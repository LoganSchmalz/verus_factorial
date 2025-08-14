use vstd::prelude::*;

verus! {

mod triangle_facts {
use vstd::prelude::*;

pub open spec fn triangle(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        n + triangle((n - 1) as nat)
    }
}

pub broadcast proof fn triangle_is_monotonic(i: nat, j: nat)
    ensures #![trigger triangle(i), triangle(j)]
        i <= j ==> triangle(i) <= triangle(j),
    decreases j,
{
    if j == 0 {
    }
    else {
        triangle_is_monotonic(i, (j - 1) as nat);
    }
}

}

use triangle_facts::triangle;
use triangle_facts::triangle_is_monotonic;
//broadcast use triangle_is_monotonic;

fn rec_triangle(n: u32) -> (sum: u32)
    requires
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        sum == triangle(n as nat),
    decreases n,
{
    if n == 0 {
        0
    } else {
        n + rec_triangle(n - 1)
    }
}


fn loop_triangle(n: u32) -> (sum: u32)
    requires
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        sum == triangle(n as nat),
{
    let mut sum: u32 = 0;
    let mut idx: u32 = 0;
    while idx < n
        invariant
            idx <= n,
            sum == triangle(idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
        decreases n - idx,
    {
        idx = idx + 1;
        assert(sum + idx < 0x1_0000_0000) by {
            triangle_is_monotonic(idx as nat, n as nat);
        }
        sum = sum + idx;
    }
    sum
}

// fn loop2_triangle(n: u32) -> (sum: u32)
//     requires(triangle(n as nat)) <= u32::MAX
// {
//     let mut sum: u32 = 0;
//     let mut idx: u32 = 1;
//     while idx <= n
//         invariant
//             idx <= n + 1,
//             triangle(n as nat) <= u32::MAX,
//             sum + idx <= u32::MAX,
//             idx + 1 <= u32::MAX
//         decreases n - idx
//     {
//         assert(sum + idx <= u32::MAX) by {
//             triangle_is_monotonic(idx as nat, n as nat);
//         }
//         sum = sum + idx;
//         assert(idx + 1 <= u32::MAX);
//         idx = idx + 1;
//     }
//     sum
// }

mod factorial {

    use vstd::prelude::*;

    pub open spec fn factorial(n: nat) -> nat
        decreases n,
    {
        if n <= 1 {
            1
        } else {
            n * factorial((n - 1) as nat)
        }
    }

    proof fn factorial_0_eq_1()
        ensures
            factorial(0) == factorial(1)
    {}

    proof fn factorial_1_lt_2()
        ensures
            factorial(1) < factorial(2)
    {
        assert(factorial(0) == factorial(1) < factorial(2));
    }

    pub proof fn is_monotonic(i: nat, j: nat) by (nonlinear_arith)
        ensures
            i <= j ==> factorial(i) <= factorial(j),
        decreases j,
    {
        if j == 0 {
        }
        else {
            is_monotonic(i, (j - 1) as nat);
        }
    }

    pub broadcast proof fn monotonic_step(i: nat) by (nonlinear_arith)
        requires 1 <= i
        ensures #![trigger (factorial((i-1) as nat))] factorial((i-1) as nat) <= factorial(i)
    {
    }

    pub broadcast proof fn from_prev(i: nat) by (nonlinear_arith)
        requires i >= 1
        ensures #[trigger] factorial(i) == (i * factorial((i-1) as nat))
    {}
}

fn rec_factorial(n: u32) -> (res: u32)
    requires factorial::factorial(n as nat) < u32::MAX
    ensures res == factorial::factorial(n as nat)
    decreases n
{
    if n <= 1 {
        1
    } else {
        proof { factorial::monotonic_step(n as nat) }
        // proof {
        //     factorial_is_monotonic((n-1) as nat, n as nat)
        // }
        n * rec_factorial(n-1)
    }
}



fn mut_factorial(n: u32, res: &mut u32)
    requires factorial::factorial(n as nat) <= u32::MAX
    ensures *res == factorial::factorial(n as nat)
    decreases n
{
    if n <= 1 {
        *res = 1;
    } else {
        // assert(factorial::factorial((n - 1) as nat) <= factorial::factorial(n as nat)) by {
        //     factorial::is_monotonic((n-1) as nat, n as nat);
        // }
        proof { factorial::monotonic_step(n as nat) }
        mut_factorial(n-1, res);
        *res = *res * n;
        assert(*res == n * factorial::factorial((n-1) as nat));
    }
}

fn tail_factorial(n: u32, idx: u32, sum: &mut u32)
requires
        idx <= n,
        *old(sum) == factorial::factorial(idx as nat),
        factorial::factorial(n as nat) <= u32::MAX,
    ensures
        *sum == factorial::factorial(n as nat),
    decreases n - idx,
{
    if idx < n {
        let idx = idx + 1;
        assert(*sum * idx <= u32::MAX) by {
            factorial::is_monotonic(idx as nat, n as nat);
        }
        *sum = *sum * idx;
        // assert(idx >= 1);
        // assert(idx * factorial((idx-1) as nat) == factorial(idx as nat)) by (nonlinear_arith); // WHY DOESNT THIS WORK???!
        assert(*sum == idx * factorial::factorial((idx-1) as nat) == factorial::factorial(idx as nat)) by {
            factorial::from_prev(idx as nat);
        };
        // assert(*sum == idx * factorial((idx-1) as nat) == factorial(idx as nat));
        tail_factorial(n, idx, sum);
    }
}


fn loop_factorial(n: u32) -> (res: u32)
    requires
        factorial::factorial(n as nat) <= u32::MAX,
    ensures
        res == factorial::factorial(n as nat),
{
    let mut res: u32 = 1;
    let mut i: u32 = 0;
    assert(res == factorial::factorial(0) == factorial::factorial(1));
    while i < n
        invariant
            i <= n,
            res == factorial::factorial(i as nat),
            factorial::factorial(n as nat) <= u32::MAX,
        decreases n - i,
    {
        i = i + 1;
        assert(res * i <= u32::MAX) by {
            factorial::is_monotonic(i as nat, n as nat);
        }
        res = res * i;
        // assert(i >= 1);
        // assert(i * factorial((i-1) as nat) == factorial(i as nat)) by (nonlinear_arith) requires i >= 1;
        // assert(res == i * factorial((i-1) as nat));
        // assert(res == factorial(i as nat));
        // assert(res == factorial(i as nat)) by {
        //     factorial_from_prev(i as nat);
        // };
        assert(res == i * factorial::factorial((i-1) as nat) == factorial::factorial(i as nat))
        by {
            factorial::from_prev(i as nat);
        };
    }
    res
}

#[verifier::spinoff_prover]
fn loop2_factorial(n: u32) -> (res: u32)
    requires
        factorial::factorial(n as nat) <= u32::MAX,
    ensures
        res == factorial::factorial(n as nat),
{
    let mut res: u32 = 1;
    let mut i: u32 = 1;
    while i < n
        invariant
            1 <= i <= n || n < 1,
            i <= n ==> res == factorial::factorial(i as nat),
            n < 1 ==> res == factorial::factorial(0) == factorial::factorial(1),
            factorial::factorial(n as nat) <= u32::MAX,
        decreases n - i,
    {
        // proof {
        //     factorial_facts::monotonic2(i as nat)
        // }
        i = i + 1;
        assert(res * i <= u32::MAX) by {
            factorial::is_monotonic(i as nat, n as nat);
        }
        res = res * i;
        assert(res == i * factorial::factorial((i-1) as nat) == factorial::factorial(i as nat)) by {
            factorial::from_prev(i as nat);
        };
    }
    res
}

fn main() {
    assert(factorial::factorial(3) <= u32::MAX) by (compute);
    loop_factorial(3);
}
}
