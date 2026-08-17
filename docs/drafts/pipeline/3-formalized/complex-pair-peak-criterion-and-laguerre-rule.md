# Exponential-sum nonnegativity: Laguerre's rule, and the peak criterion for a complex pair

**Stage:** 3 — formalized in Lean 4 (unconditional; axioms `[propext, Classical.choice, Quot.sound]`).

## Problem

Classifying rational Beurling zeta functions reduces to deciding, for a difference of exponential
sums `F(t) = ∑ c_k e^{a_k t}`, whether `F ≥ 0` on `(0,∞)`.  When all exponents are real this is a
Descartes-type question.  When the zeta has a conjugate pair of zeros or poles at `β ± iγ` — the
RH-relevant configuration — the difference contains `2 e^{βt} cos(γ t)` and sign-change counting
breaks down.  This card settles both halves.

## Part A — Laguerre's rule with multiplicity

**Theorem.**  Let `a : Fin (m+1) → ℝ` be strictly increasing and `c i ≠ 0` for every `i`.  Then every
zero configuration of `t ↦ ∑ c i e^{a i t}` — real zeros listed with their vanishing orders — has
length at most the number of sign changes of `c`.

`GaloisForLFunctions.HTGeometry.laguerre_zeroList_length_le`

Supporting layer, all new:

| Statement | Module |
|---|---|
| Zero configurations as sorted lists with repetition; Rolle descent; counting theorem | `ZeroMultisetRolle` |
| `VanishesTo` closed under sums and under multiplication by a smooth factor | `VanishingOrderProduct` |
| Iterated derivatives, exponent shift, multiplicity bound for `expSum` | `ExponentialSumZeros` |
| Dominant term at `-∞`, eventual sign | `ExponentialSumAsymptotics` |
| Sign changes of a coefficient sequence; peeling the lowest exponent | `LaguerreSignChanges` |
| The gain-one Rolle descent and the rule | `LaguerreRule` |

The induction is the classical one, with the step that is usually left informal made explicit: when
the two lowest coefficients agree in sign, the mean value theorem forces `f'` to change sign between
the region where `f` and `f'` both carry the sign of `c 0` and the leftmost zero of `f`, and the
intermediate value theorem supplies one extra critical point strictly left of every zero.  That is
`exists_deriv_zeroList_succ`.

## Part B — The complex pair: a peak criterion, not a count

Let `R(t) = ∑ c_i e^{a_i t}` with every `c_i > 0`, and `γ > 0`.

**B1 (log-convexity).**  `log R` is convex — `R` is a Laplace transform of a positive atomic measure.
`convexOn_log_expSum`.  Consequently `R` lies above the exponential of any tangent to `log R`:
`exp_supporting_le_expSum`.

**B2 (the cap profile).**  Define
```
Φ(x) = log 2 − ½ log(1 + x²) + x · arctan x .
```
Then `Φ(x) = sup_{|u| < π/2} ( log 2 + log cos u − x u )`, attained exactly at `u = −arctan x`.
Equivalently `2 cos u ≤ e^{Φ(x)} e^{x u}` on `|u| ≤ π/2`, and `Φ(x)` is the least constant for which
this holds.  `capProfile`, `two_mul_cos_le_exp_capProfile`, `capProfile_le_of_forall`.
`Φ` is even, `Φ(0) = log 2`, `Φ' = arctan`.

**B3 (the arc criterion — the main theorem).**  For every `β, γ > 0, p`:
```
  (∀ t with |t − p| ≤ π/(2γ),  2 e^{βt} cos(γ(t−p)) ≤ R(t))
    ⟺  ∃ ν L,  (∀ t ∈ ℝ,  e^{L + (β+ν)t} ≤ R(t))  ∧  Φ(ν/γ) ≤ L + ν p .
```
`cos_arc_le_iff_exists_separating`; peak-lattice form `cos_peak_arc_le_iff` (with `p = 2πk/γ`, so
`cos(γ(t−p)) = cos(γ t)`).

So the obstruction is a **separation by a single exponential**, and the only condition on that
exponential is that its logarithm at the centre of the arc reach the Legendre profile of the cap.
Writing `Λ_R(μ) = inf_t (log R(t) − μ t)` for the concave conjugate of `log R`, the criterion is
```
  ∃ ν :  Λ_R(β + ν) + ν p  ≥  Φ(ν/γ) .
```
This is a one-dimensional convex-conjugate comparison — a large-deviation rate-function condition on
the pole data — with no reference to zero counting.

Mechanism: the ratio `2 cos(γ(t−p)) e^{βt}/R(t)` is continuous on the closed arc and vanishes at its
endpoints, so its maximum is interior; the tangency there pins `γ(t−p) = −arctan(ν/γ)`, which is
exactly the point where the cap attains `Φ(ν/γ)`.  The separating exponential is the supporting
exponential of `R` at that point, which exists because `log R` is convex.

**B4 (peak rigidity).**  If `R(t) ≥ 2 e^{βt} cos(γ t)` for all `t ∈ ℝ` and equality holds at two
distinct points of the peak lattice, then `R(t) = 2 e^{βt}` identically.
`eq_two_mul_exp_of_two_contacts`.

So the contact set on the peak lattice is a single point or the whole lattice; nothing in between.
The proof needs no analyticity: `S(t) = e^{−βt} R(t)` has `S'' = ∑ c_i (a_i−β)² e^{(a_i−β)t} ≥ 0`,
so `S'` is monotone; `S'` vanishes at each contact (a global minimum of `S − 2cos(γ·)` at a point
where `sin(γ·) = 0`), hence `S' ≡ 0` between them, hence `S'' = 0` there, and a positive combination
of exponentials has vanishing second derivative only when every exponent equals `β`.

**B5 (sign-change counting provably fails).**  The extremal function
```
  2 e^{βt} − e^{(β+iγ)t} − e^{(β−iγ)t}  =  2 e^{βt} (1 − cos γ t)
```
is nonnegative and admits zero configurations of **every** length.
`exists_zeroList_length_eq_of_complex_pair`.  Contrast Part A: a three-term sum with real exponents
has at most two zeros with multiplicity.  No Descartes-type bound survives complex exponents.

## Consequence for rational Beurling zetas

A conjugate pair of zeros at `β ± iγ` is admissible against a positive pole configuration `R` exactly
when the criterion of B3 holds at every peak `2πk/γ` in range; only finitely many peaks matter,
namely those inside the interval `{t : log R(t) − βt < log 2}`, which is bounded whenever
`min a_i < β < max a_i`.  The unique extremal configuration is `R(t) = 2 e^{βt}`: a double pole at
`β` compensating the conjugate pair, giving `F(t) = 2 e^{βt}(1 − cos γ t) ≥ 0` — the `1 − cos`
positivity that also underlies de la Vallée Poussin's zero-free region, here recovered as the unique
rigid case rather than as a chosen trigonometric identity.

## Modules

```
formal/GaloisForLFunctions/HTGeometry/ZeroMultisetRolle.lean
formal/GaloisForLFunctions/HTGeometry/VanishingOrderProduct.lean
formal/GaloisForLFunctions/HTGeometry/ExponentialSumZeros.lean
formal/GaloisForLFunctions/HTGeometry/ExponentialSumAsymptotics.lean
formal/GaloisForLFunctions/HTGeometry/LaguerreSignChanges.lean
formal/GaloisForLFunctions/HTGeometry/LaguerreRule.lean
formal/GaloisForLFunctions/HTGeometry/PositiveExpSumLogConvex.lean
formal/GaloisForLFunctions/HTGeometry/CosineCapProfile.lean
formal/GaloisForLFunctions/HTGeometry/ComplexPairArcCriterion.lean
formal/GaloisForLFunctions/HTGeometry/ComplexPairPeakRigidity.lean
```

## Open

* Several conjugate pairs at once: the comparison function is a sum of caps and is no longer
  concave on any single arc, so the separation argument does not apply verbatim.  The finiteness
  reduction (only peaks inside `{log R − βt < log 2}` matter) does survive.
* Turning the `Λ_R` inequality into an explicit decision procedure for a given rational Beurling
  datum requires evaluating the concave conjugate of a positive exponential sum — a finite convex
  program, but not yet formalized.
