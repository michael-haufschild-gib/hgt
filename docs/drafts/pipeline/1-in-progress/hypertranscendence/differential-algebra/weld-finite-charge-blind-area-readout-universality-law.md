# Weld finite-charge-blind area-readout universality law

Status: **Stage 3 — formalized in Lean 4**

## Discovery

Whole-corpus theorem-posting closure joined:

- `WeldChargeFaithfulness`: every homomorphism from real weld cohomology to any finite abelian
  group annihilates every class on the real weld line; and
- `WeldPolarizationDirection`: the same weld line maps injectively to alternating area forms.

The second theorem exposes a canonical two-vector scalar readout of the area form. No corpus theorem
compares this one faithful continuous readout with the complete blindness of all finite-valued
charges.

## Universal law

For a weld-line class `c`, define its area readout by

`A(c) = weldClassLineToArea(c)((1,0),(0,1))`.

Then:

1. every additive charge from ambient real weld cohomology to any finite nonempty abelian group
   sends `c` to zero; and
2. `A` is injective on the entire weld-class line.

Equivalently, no family of bounded finite charge values can distinguish even two points of the
real flux line, while one canonical oriented-plane scalar distinguishes all of them.

## Dependency-closed paper proof

1. Every `c : WeldClassLine` has a unique coordinate `θ : ℝ` with
   `c = weldClassHom.rangeRestrict θ`.
2. `weldClass_finite_charge_invisible` gives `φ(weldClassHom θ)=0` for every additive map `φ` into
   a finite nonempty abelian target. This proves finite-charge blindness for arbitrary `c`.
3. `weldClassLineToArea_apply` identifies the area form of `c` with
   `weldAreaForm θ`.
4. Evaluating at the ordered basis pair `((1,0),(0,1))` gives exactly `θ`.
5. Therefore equality of the scalar area readouts gives equality of coordinates and hence equality
   of weld classes.

No prime specialization, RH premise, computation, or choice of a noncanonical complex structure
enters.

## Formal targets

- `weldClassLine_finiteCharge_invisible`
- `weldClassAreaReadout`
- `weldClassAreaReadout_rangeRestrict`
- `weldClassAreaReadout_injective`
- `weld_finiteChargeBlind_areaReadoutUniversality`

## Novelty audit

Post-proof searches found classical adjacent literature on finite quotients of symplectic groups,
symplectic quotients, and torsion cohomology, but no statement combining:

- total blindness of every finite abelian charge on this real weld line; and
- injectivity of the canonical ordered-basis evaluation of its alternating area form.

The exact weld/area-readout conjunction remains **[NOVELTY UNVERIFIED]**:

- https://arxiv.org/abs/2004.04129
- https://arxiv.org/abs/math/0001002
- https://annals.math.princeton.edu/2015/182-3/p03

## Lean formalization

Formalized in:

`formal/GaloisForLFunctions/RHTower/WeldFiniteChargeBlindAreaReadoutUniversalityLaw.lean`

with declarations:

- `weldClassLine_finiteCharge_invisible`
- `weldClassAreaReadout`
- `weldClassAreaReadout_rangeRestrict`
- `weldClassAreaReadout_injective`
- `weld_finiteChargeBlind_areaReadoutUniversality`

Exact-file verification passed:

`lake env lean GaloisForLFunctions/RHTower/WeldFiniteChargeBlindAreaReadoutUniversalityLaw.lean`

Wired into `GaloisForLFunctions/RHTower.lean` immediately after `WeldChargeFaithfulness`.
