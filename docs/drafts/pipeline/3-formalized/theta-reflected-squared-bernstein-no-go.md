# Theta reflected squared-profile Bernstein obstruction

- **ID:** C5-BERNSTEIN-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** `theta-center-mixed-odd-four-point-cusp.md` · C5 logistic survivor
- **Statement:** For every center `u` and Gaussian rate `a ≥ 0`, `exp(a t²) Φ(u+t)Φ(u-t) → 0`; hence the squared-displacement reflected profile has no nonzero finite positive Laplace-measure representation.

## Goal

Hostile-test the strongest generic measure route to C5.  If

```text
x ↦ Φ(u+sqrt x) Φ(u-sqrt x)
```

were a completely monotone profile, Bernstein--Widder would represent it by a finite positive
Laplace measure.  Its divided drop would then itself be a positive Laplace transform and therefore
log-convex, closing C5.  The card determines whether that generic route is available before any
theta-specific measure infrastructure is built.

## Gates

- [x] 0 → 1 in-progress: exact source-pure claim and hostile mechanism identified
- [x] 1 → 2 fully-proven: dependency-closed paper proof below
- [x] 2 → 3 formalized: exact Lean theorem and targeted build
- [ ] 3 → 4 publication-ready: standalone priority audit and exposition

## Internal frontier

- `[CORPUS]` `thetaCuspFullSource_le_envelope` gives, for `s ≥ 0`,
  `Φ(s) ≤ U exp(9s/2 - π exp(2s))` with `U>0`.
- `[CORPUS]` `thetaCuspFullSource_neg` makes `Φ` even, and
  `thetaCuspFullSource_pos_all` makes it strictly positive.
- `[CORPUS]` `thetaCuspReflectedSourceFifthRootCurvatureNumerator_eq_five_logConvexity_add_sq`
  shows ordinary log-convexity of the squared divided drop is a sufficient C5 bridge.
- Corpus search found no positive Laplace representation or global complete-monotonicity theorem
  for the squared reflected product.

## External frontier

Bernstein--Widder characterizes completely monotone functions as positive Laplace transforms.
O'Cinneide, *A Property of Completely Monotonic Functions*, J. Austral. Math. Soc. 42 (1987),
143–146, DOI `10.1017/S1446788700028160`, records the representation and its ratio consequences.
The divided-drop inheritance is immediate from Tonelli:

```text
(f(0)-f(x))/x
  = ∫ (1-exp(-xs))/x dμ(s)
  = ∫∫_[0,s] exp(-xr) dr dμ(s).
```

Search through August 2026 found no source treating the completed-theta reflected squared profile
or the super-Gaussian obstruction below.

## Conjecture and hostile verdict

`[CONJECTURE]` The squared-displacement reflected theta profile is completely monotone and hence
admits a finite positive Bernstein measure.

**Verdict: FALSE.**  Complete monotonicity is incompatible with the exact theta tail.

## Complete paper proof

Write `Φ=thetaCuspFullSource` and `P_u(t)=Φ(u+t)Φ(u-t)`.  Fix `u∈ℝ` and `a≥0`.
For `t≥|u|`, evenness and the corpus envelope give

```text
P_u(t)
 ≤ U² exp(9t - π exp(2t)(exp(2u)+exp(-2u)))
 ≤ U² exp(9t - 2π exp(2t)).
```

The last inequality uses `exp(2u)+exp(-2u)≥2`.  Since
`exp(2t)/t²→∞`, eventually

```text
2π exp(2t) ≥ (a+10)t²,
```

and for `t≥1`, `9t≤9t²`.  Therefore eventually

```text
0 ≤ exp(a t²) P_u(t) ≤ U² exp(-t²) → 0.
```

Thus `exp(a t²)P_u(t)→0` for every `a≥0`.

Now suppose a nonzero finite positive Borel measure `μ` on `[0,∞)` represented the squared profile:

```text
P_u(sqrt x)=∫ exp(-xr) dμ(r),       x≥0.
```

Because `μ` is nonzero and `[0,∞)=⋃_N[0,N]`, some finite `N` has
`c:=μ([0,N])>0`.  Positivity of the integrand gives, for `x≥0`,

```text
P_u(sqrt x) ≥ ∫_[0,N] exp(-xr)dμ(r) ≥ c exp(-Nx).
```

Set `x=t²`.  Then `exp(Nt²)P_u(t)≥c>0` for all `t≥0`, contradicting the
proved limit with `a=N`.  No such measure exists.  Since `P_u(0)=Φ(u)²>0`, the zero measure cannot
represent the profile either.

## No-go closure

- **Exact killing theorem/mechanism:** every nonzero finite positive Laplace transform retains a
  finite exponential lower tail; the squared reflected theta profile decays faster than every
  exponential in its squared variable.
- **Strongest positive survivor:** the all-center, all-Gaussian-rate decay law
  `exp(a t²)P_u(t)→0`, plus classification of every viable future measure representation as
  necessarily signed, scale-dependent, or placed before the `t↦t²` pullback.
- **New insight:** ordinary Bernstein/complete-monotonicity machinery cannot prove C5 for this
  profile.  The surviving measure route must exploit cancellation in the literal theta atom--ray
  law rather than positivity of a fixed squared-scale representing measure.
- **Status:** `[LEAN-PROVED]`.  The generic divided-drop Laplace bridge is `[REDISCOVERED]`, while
  its incompatibility with this literal source is novelty-unverified.

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.ThetaCuspReflectedSquaredBernsteinNoGo`

- `thetaCuspReflectedSourceProduct_le_superGaussianEnvelope` proves the explicit reflected
  double-exponential envelope.
- `tendsto_exp_sq_mul_thetaCuspReflectedSourceProduct_atTop_zero` proves decay after multiplication
  by every nonnegative Gaussian rate.
- `positiveLaplaceTransform_has_exponential_minorant` proves the reusable finite-positive-measure
  obstruction.
- `not_exists_finitePositiveLaplaceRepresentation_thetaCuspReflectedSquaredProduct` closes the
  literal squared-profile representation route.

Audit: direct `lake env lean` passed; targeted module build passed; all four public results use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-28 — conjectured from the C5 logistic survivor, falsified by the theta double-exponential
  tail, paper proof closed, positive survivor extracted.
- 2026-08-28 — exact no-go and positive decay survivor formalized in Lean; module wired into
  `RHTower.lean`; targeted build and axiom audit passed.
