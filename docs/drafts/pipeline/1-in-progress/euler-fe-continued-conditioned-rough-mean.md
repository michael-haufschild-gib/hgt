# Conditioned rough variance of the continued Euler current

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Euler–FE transport: coupling the full arithmetic mean to analytic continuation.

## Target

Under `¬AAL`, find `1/2<σ<1` below an actual exceptional abscissa such that,
for every finite smooth head probe `R(t)=Σ_S w_s s^(it)`,

`T⁻¹∫_T^(2T)|R(t)|²|ζ′/ζ(σ+it)+C_Y(σ+it)|²dt → W₀ A_Y(σ)`.

Here `C_Y(s)=Σ_{p<Y}log p/(p^s−1)`, `W₀=Σ_S|w_s|²`, and
`A_Y(σ)=Σ_{Y-rough n}Λ(n)²n^(−2σ)→0` as `Y→∞`.
Both the continued current and the infinite rough arithmetic tail are literal.
No phase-return or approximation premise may be added.

## Mechanism and obligations

1. Strengthen raw-prime passage to damping `1/T` uniformly over
   `T≤Im s≤2T`, `σ≤Re s≤1`. The complementary Gamma field has error
   `O((T⁻¹+T^(−p))(1+log(2T)))`, `p>0`; finite exceptional modes are
   `O(T⁻¹)`; one Mellin recursion bounds the continuum by `O(T^(−1/2))`.
   Scalar and polar corrections are `O((1+log(2T))/T)`.
2. Split the entire von Mangoldt current into the rough part and all powers
   of primes below `Y`. Absolute convergence at positive abscissa removes
   Gaussian damping from the latter uniformly in height.
3. Transfer the proved Gaussian mean-square identity through this uniform
   approximation. Cauchy–Schwarz and the bounded Gaussian second mean
   control the cross term.

The first obligation is a uniform two-variable statement: convergence at
damping `1/Im s` alone does not justify it. The Gaussian mean theorem uses
positive phases; conjugation of the real-coefficient rough current must
explicitly match the negative phases of `n^(−s)`. Its norm is unchanged;
the independent head weight may have complex coefficients.

## Analytic input

`../3-formalized/euler-fe-fixed-damping-dyadic-passage.md` discharges the
first obligation, with all five terminal axiom audits standard.

For the arithmetic split, a nonzero von Mangoldt coefficient is supported
on one prime power. A coefficient excluded by the rough restriction therefore
lies in the smooth monoid. The established
`RHTower.summable_smoothNumbers_log_mul_rpow_neg` admits this entire small-prime
part at every positive abscissa, including all prime powers. Dominated
convergence then removes its Gaussian damping uniformly in height.

This mean-square target still does not prove pointwise control at every
prime return, same-depth zero replication, `LinAt C`, or AAL.
