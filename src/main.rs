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

fn rec_factorial_checked(n: u32) -> (res: Option<u32>)
    ensures res matches Some(r) ==> r as nat == factorial::factorial(n as nat),
    decreases n
{
    if n <= 1 {
        Some(1)
    } else {
        n.checked_mul(rec_factorial_checked(n-1)?)
    }

}

fn loop_factorial_checked(n: u32) -> (res: Option<u32>)
    ensures
        res matches Some(r) ==> r as nat == factorial::factorial(n as nat),
{
    let mut res: u32 = 1;
    let mut i: u32 = 0;
    assert(res == factorial::factorial(0) == factorial::factorial(1));
    while i < n
        invariant
            i <= n,
            res == factorial::factorial(i as nat),
        decreases n - i,
    {
        i = i + 1;
        // assert(i >= 1);
        assert(res == factorial::factorial((i-1) as nat));
        res = res.checked_mul(i)?;
        // assert(i >= 1);
        // assert(res == i * factorial::factorial((i-1) as nat));
        proof { factorial::from_prev(i as nat) }
    }
    Some(res)
}

pub mod nats_facts {
    use vstd::prelude::*;

    pub proof fn mod_if_divides(i: nat, j: nat) by (nonlinear_arith)
        requires j != 0, exists |k: nat| k != 0 && i == #[trigger] (k * j)
        ensures i % j == 0
    {}

    pub proof fn divides_if_mod(i: nat, j: nat) by (nonlinear_arith)
        requires i != 0, j != 0, i % j == 0
        ensures exists |k: nat| i == #[trigger] (k * j) && k != 0
    {
        assert(i == (i / j) * j);
    }

    pub proof fn divide_mult_comm(i: nat, j: nat, k: nat) by (nonlinear_arith)
        requires j > 0, i % j == 0
        ensures i / j * k == k * i / j
        decreases i
    {}

    pub proof fn mod_factor(i: nat, j: nat, k: nat) by (nonlinear_arith)
        requires i != 0, j != 0, k != 0, i % j == 0, j % k == 0
        ensures i % k == 0
    {
        divides_if_mod(i, j);
        let x = i / j;
        divides_if_mod(j, k);
        let y = j / k;
        assert(i == x * y * k);
        mod_if_divides(i, k);
    }
}

pub mod factorial_division {
    use vstd::prelude::*;

    use crate::nats_facts;
    use crate::factorial::{self, factorial, from_prev, is_monotonic};

    pub proof fn non_zero(i: nat) by (nonlinear_arith)
        ensures factorial(i) != 0
    {
        is_monotonic(0, i)
    }

    pub proof fn divide(n: nat, i: nat) by (nonlinear_arith)
        requires 1 <= i <= n
        ensures i * factorial(n) / factorial(i) == factorial(n) / factorial((i-1) as nat)
    {
        non_zero(i);
    }

    pub proof fn mod_step(n: nat) by (nonlinear_arith)
        requires 1 <= n
        ensures factorial(n) % factorial((n-1) as nat) == 0
    {
        factorial::from_prev(n);
        non_zero((n-1) as nat);
        nats_facts::mod_if_divides(factorial(n), factorial((n-1) as nat));
    }

    pub proof fn lt_mod(n: nat) by (nonlinear_arith)
        ensures forall |i: nat| i <= n ==> factorial(n) % factorial(i) == 0
        decreases n
    {
        if n == 0 {}
        else {
            mod_step(n);
            lt_mod((n-1) as nat);
            assert forall |i: nat| i <= n-1 implies #[trigger] (factorial((n-1) as nat) % factorial(i)) == 0 by {
                lt_mod((n-1) as nat);
            }
            assert(factorial(n) % factorial((n-1) as nat) == 0);
            assert forall |i: nat| i <= n-1 implies #[trigger] (factorial(n) % factorial(i)) == 0 by {
                non_zero(n);
                non_zero((n-1) as nat);
                non_zero(i);
                assert(factorial(n) % factorial((n-1) as nat) == 0);
                assert(factorial((n-1) as nat) % factorial(i) == 0);
                nats_facts::mod_factor(factorial(n), factorial((n-1) as nat), factorial(i));
            }
        }
    }

    pub proof fn lt_divides(n: nat, i: nat) by (nonlinear_arith)
        requires i <= n
        ensures exists |k: nat| factorial(n) == #[trigger] (k * factorial(i))
    {
        non_zero(n);
        non_zero(i);
        lt_mod(n);
        nats_facts::divides_if_mod(factorial(n), factorial(i));
    }

    pub proof fn grouping_mult(n: nat, i: nat) by (nonlinear_arith)
        requires 1 <= i <= n
        ensures factorial(n) / factorial(i) * i == i * factorial(n) / factorial(i)
        decreases i
    {
        non_zero(i);
        lt_mod(n);
        nats_facts::divide_mult_comm(factorial(n), factorial(i), i);
    }

    pub proof fn factors(n: nat, i: nat) by (nonlinear_arith)
        requires 0 < i <= n
        ensures factorial(n) % i == 0
    {
        lt_mod(n);
        non_zero(n);
        non_zero(i);
        assert(i != 0);
        assert(factorial(i) % i == 0);
        assert(factorial(n) % factorial(i) == 0);
        nats_facts::mod_factor(factorial(n), factorial(i), i);
    }
}

fn loop_factorial_checked2(n: u32) -> (res: Option<u32>)
    ensures
        res matches Some(r) ==> r as nat == factorial::factorial(n as nat),
{
    let mut res: u32 = 1;
    let mut i: u32 = n;
    assert(factorial::factorial(n as nat) / factorial::factorial(n as nat) == 1) by (nonlinear_arith) {
        factorial_division::non_zero(n as nat)
    };
    while i > 1
        invariant
            i >= 1 ==> i <= n,
            res == factorial::factorial(n as nat) / factorial::factorial(i as nat),
        decreases i,
    {
        res = res.checked_mul(i)?;
        assert(factorial::factorial(n as nat) / factorial::factorial(i as nat) * i as nat == factorial::factorial(n as nat) / factorial::factorial((i-1) as nat)) by
        {
            factorial_division::grouping_mult(n as nat, i as nat);
            factorial_division::divide(n as nat, i as nat)
        };
        i = i - 1;
    }
    assert(res == factorial::factorial(n as nat) / 1);
    Some(res)
}

fn loop_factorial_checked3(n: u32) -> (res: Option<u32>)
    ensures
        res matches Some(r) ==> r as nat == factorial::factorial(n as nat),
{
    let mut res: u32 = 1;
    let mut i: u32 = n;
    while i > 1
        invariant
            i >= 1 ==> i <= n,
            res * factorial::factorial(i as nat) == factorial::factorial(n as nat),
        decreases i,
    {
        assert(res * (i * factorial::factorial((i-1) as nat)) == res * i * factorial::factorial((i-1) as nat)) by (nonlinear_arith);
        res = res.checked_mul(i)?;
        i = i - 1;
    }
    assert(res * 1 == factorial::factorial(n as nat));
    Some(res)
}

fn main() {
    assert(factorial::factorial(3) <= u32::MAX) by (compute);
    loop_factorial(3);
}
}
