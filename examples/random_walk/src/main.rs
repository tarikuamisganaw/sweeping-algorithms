use pathmap::PathMap;
use rand::distr::Distribution;
use rand::prelude::StdRng;
use rand::SeedableRng;
use pathmap::fuzzer::{unbiased_descend_first_policy, DescendFirstTrieValue};
use pathmap::utils::ints::gen_int_range;
use pathmap::viz::{viz_btms, DrawConfig};
use pathmap::zipper::{ReadZipperUntracked, Zipper, ZipperAbsolutePath, ZipperForking, ZipperIteration, ZipperMoving, ZipperReadOnlyConditionalValues, ZipperReadOnlySubtries, ZipperValues, ZipperWriting};
use std::convert::Infallible;
use std::str::from_utf8;
use pathmap::morphisms::Catamorphism;
use rand;

enum PathChoice {
    Value(()),
    Path(u8),
}

fn ecan() {

    // 1) create a new pathmap instance with i32 value type
    let mut p:PathMap<i32> = PathMap::new();


    // 2) insert test values to test sampling
    p.set_val_at("hell", 10);
    p.set_val_at("hells", 18);
    p.set_val_at("h", 200);
    p.set_val_at("hello", 12);
    p.set_val_at("zo", 30);

    // 3) Get a read zipper at root 
    let mut z = p.read_zipper();

    // 4) loop until the zipper focus has no child
    while z.child_count() >= 1 {

        // 4) descend_until the first fork in the path i.e where the path splits
        if z.val().is_none() {
            z.descend_until();
        }

        // 5) returns a vec of tuple for agg of each child
        let choice_param = children_agg_w(z.clone()).unwrap();
        
        // 6) choose based on the path and rand value
        let choice = choice(choice_param, &z);

        // 7) return if value is selected else conitnue to selected path
        let byte = match choice {
            PathChoice::Value(_) => {
                println!("{:?}", String::from_utf8(z.origin_path().to_vec()).unwrap());
                return
            },
            PathChoice::Path(b) => b
        };

        // 8) descend to the path
        z.descend_to_byte(byte);
    }

    let path = z.origin_path();
    println!("{:?}", String::from_utf8(path.to_vec()).unwrap());

}


fn children_agg_w(mut path:ReadZipperUntracked<i32>)  -> Result<Vec<(i32, u8)>, Infallible> {

    // 1) create a vector to store the agg_w of child and its mask
    let mut total: Vec<(i32, u8)> = Vec::new();


    for b in path.child_mask().iter() {
        path.descend_to_byte(b);
        let child = path.fork_read_zipper();
        let ch_agg_w = node_agg_w(child).unwrap();
        total.push((ch_agg_w, b));
        path.ascend_byte();
    }
        
    Ok(total)
}

fn node_agg_w(path: ReadZipperUntracked<i32>) -> Result<i32, Infallible>{


    let total: Result<i32, Infallible> = 
        path.into_cata_jumping_side_effect_fallible(|_mask, children, _size, maybe_v, _path| {
            let from_children = children.iter().copied().sum::<i32>();
            let here = maybe_v.copied().unwrap_or(0);
            Ok(here + from_children)
        });

    total// .map(|s| s - root_val)
}


// return true if its path false if value
fn path_v_val(focus_val: &i32, choice_param: &Vec<(i32, u8)>, root_agg_w :i32) -> bool {

    let random_num = rand::random_range(0..=root_agg_w);
    let sum: i32 = choice_param.iter().map(|(i, _)| i).sum();

    if sum > *focus_val {
        if sum >= random_num {
            true
        } else {
            false 
        }
    } else {
        if *focus_val >= random_num {
            false
        } else {
            true
        }
    } 
}

// return a Path(u8) if it choses path or Value(()) if it chosses value
fn choice(mut choice_param: Vec<(i32, u8)>, path: &ReadZipperUntracked<i32>) -> PathChoice {

    // get agreagte weight of all values
    let mut root_agg_w = node_agg_w(path.fork_read_zipper()).unwrap();

    // if path as a value chose between paths and values
    if path.val().is_some() {
        let focus_val = path.val().unwrap();
        root_agg_w -= focus_val;
        if !path_v_val(focus_val, &choice_param, root_agg_w) {
            return PathChoice::Value(())
        }
    }

    let mut random_num = rand::random_range(0..=root_agg_w);

    // sort in descnding order of aggregate weights
    let mut path: u8 = 0;
    choice_param.sort_by(|a, b| b.0.cmp(&a.0));

    // chose a path
    for (i, u) in choice_param {
        if i >= random_num { 
            path = u; 
            break
        }
        random_num -= i;
    }

    PathChoice::Path(path)
        
}

fn main() {
    // small();
    // big();
    ecan();
}
