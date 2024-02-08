extern crate rand;
use rand::Rng;
type Nat = u64;

// key generation
fn key_gen() -> (Nat, Nat) {
    let sk = rand::thread_rng().gen::<Nat>();
    let pk = rand::thread_rng().gen::<Nat>();
    (sk, pk)
}

// apply function 
fn apply<F>(f: F, sk: Nat) -> Nat
where
    F: FnOnce(Nat) -> Nat,
{
    f(sk)
}

fn example_function(sk: Nat) -> Nat {
    sk + 0
}

fn main() {
    let (sk, pk) = key_gen();
    println!("Public Key (pk): {}", pk);
    let result = apply(example_function, sk);
    println!("Result: {}", result);
}

