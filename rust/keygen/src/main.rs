extern crate rand;
use rand::Rng;
type Nat = u64;

struct State {
   sk : Option<Nat>
}

impl State { 
    fn init() -> State {
        let sk = Some(rand::thread_rng().gen::<Nat>());
        State { sk }
    }
    // key generation
    fn key_gen(&mut self) -> Nat {
        let pk = rand::thread_rng().gen::<Nat>();
        pk
    }
    fn apply<F>(&self, f: F) -> Nat 
    where 
         F: FnOnce(Nat) -> Nat, {
            match self.sk {
                Some(sk) => f(sk),
                None => panic!("State not initialized"),
            }
    }
}
/*
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
*/

fn main() {
    
}
