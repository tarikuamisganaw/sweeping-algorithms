use std::time::Instant;
use pasture_core::{
    containers::{BorrowedBuffer, VectorBuffer},
    layout::attributes::POSITION_3D,
    nalgebra::Vector3,
    nalgebra::Point3,
    math::AABB
};
use pasture_core::containers::BorrowedBufferExt;
use pasture_core::meta::Metadata;
use pasture_io::base::{PointReader, SeekToPoint, read_all};
use pasture_io::las::LASReader;


fn main() {
    let mut reader = LASReader::from_path("/home/adam/Projects/potree/pointclouds/lion_takanawa.copc.laz", false).expect("read file");
    let point_count: usize = reader.point_count().expect("point count meta data");
    let bbox: AABB<f64> = reader.las_metadata().bounds().expect("bbox meta data");
    let points: VectorBuffer = reader.read(point_count).expect("read all points");

    if points.point_layout().has_attribute(&POSITION_3D) {
        let positions = points.view_attribute::<Vector3<f64>>(&POSITION_3D);
        let mut rbbox = AABB::from_min_max(Point3::origin(), Point3::origin());
        positions.clone().into_iter().for_each(|point| rbbox = AABB::extend_with_point(&rbbox, &point.into()));
        // yuck, probably due to rounding, the real bbox does not coincide with the meta data bbox
        
        let mut tree = Octree::new(rbbox);
        let t_construction = Instant::now(); 
        positions.into_iter().for_each(|point| tree.insert(point.into()));
        println!("inserted {point_count} in {} ms", t_construction.elapsed().as_millis());
        let first_octant = Octree::child(&tree.bounds, 0);
        let mut contained = 0;
        let t_range = Instant::now();
        tree.range_query(first_octant, &mut |_| { contained += 1; true });
        println!("Query visited {} points in first octant {:?} in {} ms", contained, first_octant, t_range.elapsed().as_millis());
        let k = 10;
        let t_knn = Instant::now();
        let topk = tree.knn(first_octant.center(), k);
        println!("{k}-NN returned {:?} around {:?} in {} µs", topk, first_octant.center(), t_knn.elapsed().as_micros());
    } else {
        panic!("Point cloud files has no positions!");
    }
}


const LEAF_CAPACITY: usize = 8;
const MAX_DEPTH: usize = 12;

enum Node {
    Leaf { points: Vec<Point3<f64>> },
    Branch { children: [Option<Box<Node>>; 8] },
}

impl Default for Node {
    fn default() -> Self {
        Node::Leaf {
            points: Vec::with_capacity(LEAF_CAPACITY),
        }
    }
}

struct Octree {
    root: Node,
    bounds: AABB<f64>,
}

impl Octree {
    fn new(bounds: AABB<f64>) -> Self {
        Self {
            root: Node::default(),
            bounds,
        }
    }

    pub fn insert(&mut self, p: Point3<f64>) {
        if !self.bounds.contains(&p) {
            panic!("Point {:?} is outside the tree bounds {:?}", p, self.bounds);
        }
        Self::insert_rec(&mut self.root, p, self.bounds, 0);
    }

    fn insert_rec(node: &mut Node, p: Point3<f64>, bounds: AABB<f64>, depth: usize) {
        match node {
            Node::Leaf { points } => {
                if points.len() < LEAF_CAPACITY || depth >= MAX_DEPTH {
                    points.push(p);
                } else {
                    // Split the leaf.
                    let mut new_children: [Option<Box<Node>>; 8] = Default::default();
                    // Re‑insert existing points into children.
                    for &old_p in points.iter() {
                        let idx = Self::child_index(bounds.center(), old_p);
                        let child_bounds = Self::child(&bounds, idx);
                        new_children[idx]
                            .get_or_insert_with(|| Box::new(Node::default()));
                        Self::insert_rec(
                            new_children[idx].as_mut().unwrap(),
                            old_p,
                            child_bounds,
                            depth + 1,
                        );
                    }
                    // Clear points and convert to branch.
                    *node = Node::Branch { children: new_children };
                    // Insert the new point.
                    Self::insert_rec(node, p, bounds, depth);
                }
            }
            Node::Branch { children } => {
                let idx = Self::child_index(bounds.center(), p);
                let child_bounds = Self::child(&bounds, idx);
                children[idx]
                    .get_or_insert_with(|| Box::new(Node::default()));
                Self::insert_rec(
                    children[idx].as_mut().unwrap(),
                    p,
                    child_bounds,
                    depth + 1,
                );
            }
        }
    }

    #[inline]
    fn child_index(c: Point3<f64>, p: Point3<f64>) -> usize {
        ((p.x >= c.x) as usize)
            | (((p.y >= c.y) as usize) << 1)
            | (((p.z >= c.z) as usize) << 2)
    }

    /// Bounding box of the `index`th child octant.
    /// Octant bit pattern: x >> 0, y >> 1, z >> 2 (LSB is x).
    fn child(bx: &AABB<f64>, index: usize) -> AABB<f64> {
        let c = bx.center();
        let (min, max) = (
            Point3::new(
                if index & 1 == 0 { bx.min().x } else { c.x },
                if index & 2 == 0 { bx.min().y } else { c.y },
                if index & 4 == 0 { bx.min().z } else { c.z },
            ),
            Point3::new(
                if index & 1 == 0 { c.x } else { bx.max().x },
                if index & 2 == 0 { c.y } else { bx.max().y },
                if index & 4 == 0 { c.z } else { bx.max().z },
            ),
        );
        AABB::from_min_max(min, max)
    }

    /// Range query: collects points whose cells intersect `query` and are themselves inside.
    pub fn range_query<F : FnMut(Point3<f64>) -> bool>(&self, query: AABB<f64>, mut f: &mut F) -> bool {
        Self::query_rec(&self.root, self.bounds, &query, &mut f)
    }

    fn query_rec<F : FnMut(Point3<f64>) -> bool>(node: &Node, bounds: AABB<f64>, query: &AABB<f64>, f: &mut F) -> bool {
        if !bounds.intersects(query) {
            return true;
        }
        match node {
            Node::Leaf { points } => {
                for &p in points {
                    if query.contains(&p) {
                        if !f(p) { return false }
                    }
                }
            }
            Node::Branch { children } => {
                for idx in 0..8 {
                    if let Some(child) = &children[idx] {
                        let child_bounds = Self::child(&bounds, idx);
                        if !Self::query_rec(child, child_bounds, query, f) { return false }
                    }
                }
            }
        }
        true
    }

    #[inline]
    fn d2(s: Point3<f64>, o: Point3<f64>) -> f64 {
        let dx = s.x - o.x;
        let dy = s.y - o.y;
        let dz = s.z - o.z;
        dx * dx + dy * dy + dz * dz
    }
    
    fn boundary_d2(bbox: &AABB<f64>, p: Point3<f64>) -> f64 {
        let dx = if p.x < bbox.min().x { bbox.min().x - p.x } 
            else if p.x > bbox.max().x { p.x - bbox.max().x } 
            else { 0.0 };
        let dy = if p.y < bbox.min().y { bbox.min().y - p.y } 
            else if p.y > bbox.max().y { p.y - bbox.max().y } 
            else { 0.0 };
        let dz = if p.z < bbox.min().z { bbox.min().z - p.z } 
            else if p.z > bbox.max().z { p.z - bbox.max().z } 
            else { 0.0 };
        dx * dx + dy * dy + dz * dz
    }

    /// k‑nearest‑neighbour search (Euclidean) using best‑first traversal.
    pub fn knn(&self, query: Point3<f64>, k: usize) -> Vec<Point3<f64>> {
        if k == 0 {
            return Vec::new();
        }
        let mut best: Vec<(f64, Point3<f64>)> = Vec::with_capacity(k);
        Self::knn_rec(&self.root, self.bounds, query, k, &mut best);
        // Sort ascending before returning.
        best.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
        best.into_iter().map(|(_, p)| p).collect()
    }

    fn knn_rec(node: &Node, bounds: AABB<f64>, query: Point3<f64>, k: usize, best: &mut Vec<(f64, Point3<f64>)>) {
        // Prune if this branch cannot contain a closer point than current worst.
        let worst_dist = if best.len() == k {
            best.last().unwrap().0
        } else {
            f64::INFINITY
        };
        let box_dist = Self::boundary_d2(&bounds, query);
        if box_dist > worst_dist {
            return; // Entire node too far away.
        }

        match node {
            Node::Leaf { points } => {
                for &p in points {
                    let d2 = Self::d2(p, query);
                    Self::try_add_candidate(best, k, d2, p);
                }
            }
            Node::Branch { children } => {
                // Compute distance for each existing child and visit nearest first.
                // Collect (dist2, idx)
                let mut order: Vec<(f64, usize)> = Vec::with_capacity(8);
                for idx in 0..8 {
                    if children[idx].is_some() {
                        let child_bounds = Self::child(&bounds, idx);
                        order.push((Self::boundary_d2(&child_bounds, query), idx));
                    }
                }
                order.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
                for &(_, idx) in &order {
                    let child_bounds = Self::child(&bounds, idx);
                    let child = children[idx].as_ref().unwrap();
                    Self::knn_rec(child, child_bounds, query, k, best);
                }
            }
        }
    }

    #[inline]
    fn try_add_candidate(best: &mut Vec<(f64, Point3<f64>)>, k: usize, dist2: f64, p: Point3<f64>) {
        // Insert while keeping `best` sorted descending (worst at end).
        let pos = best.binary_search_by(|a| a.0.partial_cmp(&dist2).unwrap_or(std::cmp::Ordering::Equal));
        let insert_idx = match pos {
            Ok(i) | Err(i) => i,
        };
        best.insert(insert_idx, (dist2, p));
        if best.len() > k {
            best.pop(); // Remove farthest.
        }
    }
}
