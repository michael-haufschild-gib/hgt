# Conditioned rough variance of the continued Euler current

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Euler–FE transport: coupling the full arithmetic mean to analytic continuation.

## Theorem

Under `¬AAL`, find `1/2<σ<1` below an actual exceptional abscissa such that,
for every finite smooth head probe `R(t)=Σ_S w_s s^(it)`,

`T⁻¹∫_T^(2T)|R(t)|²|ζ′/ζ(σ+it)+C_Y(σ+it)|²dt → W₀ A_Y(σ)`.

Here `C_Y(s)=Σ_{p<Y}log p/(p^s−1)`, `W₀=Σ_S|w_s|²`, and
`A_Y(σ)=Σ_{Y-rough n}Λ(n)²n^(−2σ)→0` as `Y→∞`.
Both the continued current and the infinite rough arithmetic tail are literal.
No phase-return or approximation premise may be added.

## Proof

1. Strengthen raw-prime passage to damping `1/T` uniformly over
   `T≤Im s≤2T`, `σ≤Re s≤1`. The complementary Gamma field has error
   `O((T⁻¹+T^(−p))(1+log(2T)))`, `p>0`; finite exceptional modes are
   `O(T⁻¹)`; one Mellin recursion bounds the continuum by `O(T^(−1/2))`.
   Scalar and polar corrections are `O((1+log(2T))/T)`.
2. Split the entire von Mangoldt current into the rough part and all powers
   of primes below `Y`. Absolute convergence at positive abscissa removes
   Gaussian damping from the latter uniformly in height.
3. Reindex the small-prime series by `(p,k)↦p^(k+1)`. Unique factorization
   makes this injective; its geometric sums are exactly `log p/(p^s−1)`.
4. Transfer the Gaussian mean-square identity through uniform approximation.
   The bounded Gaussian second mean controls the cross term. The actual
   finite exceptional layer supplies a zero-free line above a finite height;
   clipping below that height gives continuous functions and disappears on
   escaping dyadic windows.

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

## Formalization

`EulerFETransportTheory/TheContinuedCurrentRetainsTheRoughVariance.lean`:

- `summable_norm_smallPrimeVonMangoldtCoeff`.
- `smallPrime_gaussianDamping_uniformly_vanishes`.
- `gaussianDampedPrimeSum_eq_heightCurrent`.
- `gaussianDampedPrimeSum_eq_small_add_rough`.
- `not_asymptoticAbscissaLaw_has_regular_roughPassage`.
- `not_asymptoticAbscissaLaw_has_conditioned_seriesRoughMean`.
- `smallPrime_heightSeries_eq_eulerCurrent`.
- `not_asymptoticAbscissaLaw_has_conditioned_roughMean`.

The final theorem retains a positive height above which the same observation
line is zero-free. Direct `lake --old env lean` checking and all eight
transitive axiom audits pass with only `propext`, `Classical.choice`, and
`Quot.sound`. Low exceptional zeros can obstruct an unrestricted prefix
integral; the conclusion uses escaping dyadic windows.
