# DA Strip-Dense Counterexample

- **ID:** da-strip-dense-counterexample
- **Stage:** 0-backlog
- **Type:** THEOREM (paper) / COUNTEREXAMPLE
- **Source:** Professor attack on Gamma-shift FE-prime moonshot, 2026-06-23
- **Statement:** Arbitrary differentially algebraic functions over `C(s)` can have dense strip-confined zero divisors, so any Gamma-zeta obstruction based on strip-confined zeros must restrict the admissible category more sharply than "DA over `C(s)<Gamma>`".

## Goal

Prevent the Gamma-zeta moonshot from quantifying over too broad a class. The candidate obstruction cannot be:

> no function differentially algebraic over `C(s)<Gamma>` has a dense strip-confined divisor.

That statement is false already over `C(s)`.

## The Counterexample

Let

`u = s exp(s)`,

and

`y = sin(u) = sin(s exp(s))`.

Then `y` is single-valued entire and differentially algebraic over `C(s)`.

Set

`a = 1 + 1/s`,

and

`E = (1/a) D_s`.

Then `E u = u`. Hence

`E y = u cos(u)`,

and

`E^2 y = E y - u^2 y`.

Therefore

`q = (E y - E^2 y)/y = u^2`,

and since `E(u^2)=2u^2`,

`E q = 2q`.

Clearing the quotient gives the algebraic differential equation

`y E(Ey-E^2y) - (Ey-E^2y) E y - 2y(Ey-E^2y) = 0`.

Since `E=(1/a)D_s` has rational coefficient `1/a=s/(s+1)`, clearing denominators gives a nonzero ADE over `C(s)`.

## Strip-Dense Zeros

Zeros of `y` satisfy

`s exp(s) = n pi`,

so

`s = W_k(n pi)`.

For large branch index `k`,

`Re W_k(n pi) ~ log(n pi) - log(2 pi |k|)`,

and

`Im W_k(n pi) ~ 2 pi k`.

Fix a vertical strip `a <= Re(s) <= b`. Then the condition becomes, to first order,

`C_a |k| <= n <= C_b |k|`.

Thus for each large `|k|` there are `asymp |k|` zeros in the strip, and up to height `T` the strip contains `asymp T^2` zeros.

## Consequence

The differential-algebraic closure of `C(s)<Gamma>` is too large for a strip-divisor obstruction. It contains single-valued entire DA functions with strip-confined zero divisors much denser than zeta's `T log T` count.

The Gamma-zeta moonshot can survive only in a narrower category, such as a parameterized Picard-Vessiot / Gamma-shift-compatible category, not arbitrary DA extensions.

## Theatre Test

This counterexample is likely not globally novel: functions like `sin(P(s,exp(s)))` are standard differential-algebraic constructions. Its value is project-local and significant because it falsifies an overbroad obstruction class before the team builds on it.

## Log

- 2026-06-23 - created after routing Haiku's moonshot and Turing's rational-part result. This counterexample narrows the live conjecture to category selection: what finite extensions are allowed, and why does zeta require a generator outside them?

## Computation

Local artifacts:

- `computations/2026-06-23-da-strip-dense-counterexample.py`
- `computations/2026-06-23-da-strip-dense-counterexample.txt`

RunPod artifacts:

- `/root/hgt-shared/computations/2026-06-23-da-strip-dense-counterexample.py`
- `/root/hgt-shared/computations/2026-06-23-da-strip-dense-counterexample-runpod.txt`

The count table for zeros `s=W_k(n*pi)` in the strip `0<=Re(s)<=1` gives:

- `kmax=10`: `count=182`, `T=61.277366`, `count/T^2=0.04846980`
- `kmax=20`: `count=706`, `T=124.100939`, `count/T^2=0.04584105`
- `kmax=40`: `count=2785`, `T=249.760618`, `count/T^2=0.04464546`
- `kmax=80`: `count=11067`, `T=501.086021`, `count/T^2=0.04407632`

This is consistent with quadratic strip density.
