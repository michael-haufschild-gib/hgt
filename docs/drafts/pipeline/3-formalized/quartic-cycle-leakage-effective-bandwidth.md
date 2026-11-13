# Quartic cycle leakage controls effective bandwidth

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** B27 frequency-profile design.
- **Statement:** A probability density with little quartic frequency leakage must have effective bandwidth close to one half.

Let `w ≥ 0`, `∫ℝ w = 1`, `0 < E = ∫ℝ w² < ∞`, and `η=1/E`. For four independent
samples from `w(u)du`, write

\[
V(u)=|u_1-u_2|+|u_2-u_3|+|u_3-u_4|+|u_4-u_1|,
\qquad \delta=\Pr(V>2).
\]

**Stability law.** If `δ<1/8`, then

\[
\eta\le\frac1{2(1-(8\delta)^{1/4})^2}.
\]

Equivalently, `η>1/2` forces
`δ ≥ (1−1/√(2η))⁴/8`. The estimate is sharp at zero leakage:
`δ=0` exactly when `w` is essentially supported in some interval of length `1/2`;
then `η≤1/2`, with equality exactly for `w=2·1_[a,a+1/2]` almost everywhere.
No optimality claim is made for positive `δ`.

## Paper proof

The distribution function of `w(u)du` is continuous, tends to zero and one at the
two ends, and hence has every quantile. Fix `0<ε<1/2`; choose `a,b` with
`Pr(U≤a)=ε` and `Pr(U≤b)=1−ε`. Then `a<b`, the middle interval has mass
`1−2ε`, and Cauchy–Schwarz gives `(1−2ε)²≤(b−a)E`.

If `b−a>1/2`, the disjoint events
`(u₁,u₃≤a; u₂,u₄≥b)` and their reversals lie in `{V>2}`. Independence gives
each mass `ε⁴`, so `δ≥2ε⁴`. Therefore, whenever `δ<2ε⁴`, one has
`b−a≤1/2` and `2(1−2ε)²≤E`. Let `ε` decrease to `(δ/2)^(1/4)` to obtain
the displayed stability law.

For the support statement, two points of the measure's support at distance
greater than `1/2` have disjoint positive-mass neighbourhoods still separated
by more than `1/2`; the same alternating events force positive leakage.
Thus zero leakage gives support diameter at most `1/2`. A nonempty closed
bounded subset of the real line lies in an interval of that length. Conversely,
four points in such an interval satisfy `V≤4·(1/2)=2`.
Finally Cauchy–Schwarz on that interval gives `E≥2`; equality is equivalent to
`∫(w−2·1_[a,a+1/2])²=0`, hence to the asserted uniform density.

## Arithmetic consequence and limit

Profiles with `η≥5/7` retain at least `(1−√(7/10))⁴/8` of their quartic
frequency mass outside the available correlation region. This is a positive
geometric mass, not a bound on the signed arithmetic contribution. Proving six
singleton ordinates still needs a source estimate on that region; ζ target remains open.

## Lean declarations

`IncommensurableGaborPinching/QuarticCycleProfileStability.lean` proves:

- `effectiveBandwidth_le_of_quarticCycleLeakage`: stability law.
- `quarticCycleLeakage_eq_zero_iff`: half-interval support classification for atomless probability measures.
- `zero_leakage_and_energy_two_iff_uniform`: exact uniform extremizer.

The fourth root is `Real.sqrt (Real.sqrt (8 * δ))`. The current-source check
passed; each displayed theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

## Gates

- [x] Corpus novelty search found no matching cycle/effective-bandwidth stability law.
- [x] Dependency-closed paper proof.
- [x] Exact density theorem, support classification and equality case in Lean.
- [x] Transitive axiom audit of new declarations.
