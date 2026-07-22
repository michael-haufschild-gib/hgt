# Suzuki global-local compound Bezoutian weld — formalization certificate

## Status

`[FORMALIZED] [SOURCE-PURE] [NO RH PREMISE] [NOVELTY UNVERIFIED]`

## Paper source

`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-global-local-compound-bezoutian-weld.md`

## Lean source

`formal/GaloisForLFunctions/RHTower/SuzukiGlobalLocalCompoundBezoutianWeld.lean`

## Formal theorem surface

- `suzukiGlobalLocalCompound_quotient`: compound quotient is the difference of local and global affine responses.
- `suzukiGlobalLocalCompound_commonGauge_invariant`: arbitrary common pointwise affine gauge cancels before division.
- `suzukiGlobalLocalCompound_relativeGauge`: independent gauges leave exactly relative gauge times compound denominator.
- `suzukiBilinearGlobalLocalWeld_classification`: common-gauge invariance and coincidence vanishing uniquely characterize the determinant weld among bidegree-`(1,1)` forms.
- `suzukiGlobalLocalCompound_bezoutCross_productRule`: exact division-free Hermitian Bezoutian product rule.
- `suzukiHermitianBezoutCross_relativeGauge`: exact relative-gauge curvature term.
- `suzukiHermitianBezoutCross_realConstantGauge_invariant`: real constant relative gauges are Pick-invisible.
- `suzukiScalarPickKernel_quotient_eq_bezoutCross`: homogeneous-to-affine Pick-kernel connector.
- `suzukiXiGlobalLocalCompound_quotient`: specialization to centered multiplier pair `(XiC', z^2 XiC)`.
- `suzukiXiGlobalLocalCompound_bezoutCross`: exact local-tensor-minus-Xi-deficit identity.
- `suzukiMarkedXiCompound_bezoutCross`: source connector using existing marked Volterra affine-secant tensor.

## Dependency audit

- Imports existing marked-secant/Volterra and jump-kernel modules.
- Uses only commutative-ring/field algebra, complex conjugation, and existing Xi definitions.
- No positivity, Herglotz realization, zero-free region, zero-location statement, estimate, numerical computation, or RH premise.
- Quotient theorems state explicit denominator hypotheses; core cross-Bezoutian theorem is division-free and unconditional.

## Scientific content

Formalization corrects the prior frontier. Local Pluecker data alone is insufficient, but affine chart ambiguity does not survive unchanged into the RH Pick kernel. Common pointwise gauge cancels exactly, and real constant relative gauge is also Pick-invisible. Canonical full-jump carrier is compound determinant

`N = Q*T - S*P`, `D = P*T`,

not local marked tensor alone. Its exact signed kernel is

`T(z)*conj(T(w))*[Q,P] - P(z)*conj(P(w))*[S,T]`.

This isolates new open core:

`SUZUKI-COMPOUND-BEZOUTIAN-GRAM` — derive positive prime--Gamma Green/Gram factorization of source-specialized compound Bezoutian on one nontrivial aperture without assuming an RH-equivalent positivity statement.

## Verification

- Direct module check: passed with `lake env lean GaloisForLFunctions/RHTower/SuzukiGlobalLocalCompoundBezoutianWeld.lean`.
- Direct SOTA check: passed with `lake env lean GaloisForLFunctions/RHTower/RiemannHypothesisSOTA2026.lean`.
- Axiom audit: only standard `propext`, `Quot.sound`, and `Classical.choice`; no project axiom or RH premise.
- Forbidden-token scan of new module: clean.
- Repository lint: new module is reachable and clean; repository gate remains red on four concurrent unrelated unreachable modules: `MobiusAdditiveTriangleSourceUniversalityLaw`, `MobiusLaplaceAdditiveTrianglePolylog`, `MobiusLaplacePolylogSharpCoefficientLaw`, and `SuzukiGlobalLocalScalarPickUniversalityLaw`.
- Targeted final build: passed with `lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` (9192 jobs).

## Novelty verdict

- Determinant/Bezoutian product law: `[BRIDGE]`.
- Exact Suzuki global-local source specialization and correction of affine-gauge frontier: `[NOVELTY UNVERIFIED]`.
- No claim of RH proof or source positivity.
