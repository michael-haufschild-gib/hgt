# SQB entire native operator

Status: operator construction formalized; 33 public exports pass targeted builds
and axiom audits. Xi occurrence and RH remain unproved.

## Proof chain and scope

Original Maass source → modular curvature and exact mass → quarter domination →
Selberg gap → independently constructed Xi occurrence → RH.

This result constructs the actual operator and domain for the entire scalar
transform from [the scalar and preimage construction](sqb-entire-casimir-transform.md).
It closes that operator-construction obligation. It supplies neither quarter
domination nor a Xi occurrence theorem. The previous
[sharp native residual](sqb-native-domain-residual.md) excludes literal native
scattering occurrence even for critical zeros; that obstruction is unchanged.

## Dependency-closed paper proof

Let `J` be the original modular value-plus-gradient embedding, already constructed,
injective, and dense. Its covariance `B = J J†` is bounded, positive,
self-adjoint, and injective. The existing energy operator is the graph inverse
`A = B⁻¹ = 1 − Δ_H`. The shift by one is retained throughout.

The existing entire function satisfies `F(1/4+w²)=cosh(8πw)`. For every real λ,
`F(λ)` is real and at least −1. On λ≥1/4 it equals
`cosh(8π√(λ−1/4))`, so it tends to positive infinity as λ tends to infinity.
Define

`g(x) = 1/(F(x⁻¹−1).re+2)` for `x>0`, and `g(x)=0` for `x≤0`.

The denominator is at least one. Therefore `0≤g≤1`, and `g(x)=0` exactly on
`x≤0`. The positive-side limit at zero is zero by the preceding growth law.
On the positive half-line continuity follows by composition; the zero extension
is continuous across zero. For positive x the exact reciprocal identity is
`g(x)⁻¹−2=F(x⁻¹−1).re`.

The required kernel-preservation theorem is proved for any bounded self-adjoint
operator `D` and any continuous real symbol `h` whose zeros on its spectrum are
confined to zero. On that compact spectrum set

`r_n(x) = x²/(1+n h(x)²)`.

These continuous functions decrease pointwise to zero. If `h(x)=0`, the
no-new-zero property gives x=0; otherwise the denominator tends to infinity.
Dini's theorem upgrades this to uniform convergence. Isometric continuous
functional calculus gives `‖r_n(D)‖→0`. If `h(D)v=0`, the exact factorization

`x²−r_n(x) = [n x² h(x)/(1+n h(x)²)] h(x)`

gives `D²v=r_n(D)v` for every n. Taking norms proves `D²v=0`.
Self-adjointness gives `‖Dv‖²=⟪D²v,v⟫=0`. Thus `h(D)` creates no new kernel
vectors. If D is injective, so is `h(D)`; self-adjointness then gives dense
range by the orthogonal-range/kernel identity. No uniform positive lower bound
for h is required. The limiting argument is a formal analytic proof, not a
numerical approximation supplied as a premise.

Apply this theorem to B and g. Positivity of B confines its real spectrum to
the nonnegative half-line, so g has no new zeros there. Thus `C=g(B)` is
positive, self-adjoint, injective, has dense range, and satisfies `‖C‖≤1`.
Define the native reciprocal-calculus realization

`T = C⁻¹−2`, with `domain(T)=range(C)`.

The existing graph-inverse theorem makes `C⁻¹` self-adjoint; the existing
bounded-shift theorem makes T self-adjoint on exactly that domain. Hence T is
closed and densely defined. For every Hilbert vector y and every domain vector x,

`T(Cy)=y−2Cy`, and `C(Tx+2x)=x`.

Consequently `T+2` is bijective from its domain to the original Hilbert space,
with bounded inverse C, and `‖x‖≤‖Tx+2x‖`. The positive-inverse Rayleigh theorem
gives `Re⟪C⁻¹x,x⟫≥‖C‖⁻¹‖x‖²≥‖x‖²`; subtracting two times the mass gives

`Re⟪Tx,x⟫≥−‖x‖²`.

The trivial-Hilbert-space case is discharged separately in Lean. No nonzero
source, form-domain, inverse, or positivity premise is added to these actual
modular conclusions.

## Lean artifacts

- `formal/GaloisForLFunctions/HTGeometry/CfcKernelPreservation.lean`:
  3 public theorems, no-new-kernel law, preserved injectivity, and dense range.
- `formal/GaloisForLFunctions/RHTower/SelbergScatteringEntireSymbol.lean`:
  8 public declarations, reciprocal symbol, bounds, zeros, growth,
  continuity including zero, and exact inverse identity.
- `formal/GaloisForLFunctions/RHTower/SelbergScatteringEntireOperator.lean`:
  22 public declarations, original covariance and energy identification,
  transformed covariance, actual graph domain, self-adjointness, closedness,
  inverse identities, resolvent, and lower bound.

## Verification and search coverage

- [x] Broad unrestricted OR corpus searches; inspect relevant proof bodies.
- [x] Check every new proof with `lake env lean` scratch files.
- [x] Build each of the three named modules separately after read-only
  `lake --no-build build` preflights; each final build compiles only its named module.
- [x] Wire every finished module exactly once into its own umbrella; no full
  or umbrella build is run.
- [x] Audit all 33 public exports using `#print axioms` in `/tmp`: only
  `propext`, `Classical.choice`, and `Quot.sound`.
- [x] Confirm all 33 public exports are indexed; proof-hole token and whitespace
  checks pass for the new modules.
- [x] Run repository formal lint. At this audit it reports three unrelated
  unfinished modules missing from their umbrella: `HTGeometry.FokasLenellsRawCubicKernel`,
  `HTGeometry.FokasLenellsRawPhase`, and `HTGeometry.FokasLenellsRawTaylorFirst`.
  Existing large-file warnings remain. These SQB modules have no lint errors.

Broad search of kernels, injectivity, functional calculus, dense range, Dini,
and uniform approximation returned 20,184 declarations across 6,090 modules.
The operator-calculus search returned 107 declarations across 50 modules.
These counts measure metadata discovery, not inspection of every returned proof.
The proofs used `CfcNormBound`, `FriedrichsFormOperator`,
`ClosedHyperplaneInverse`, `BoundedPerturbedFriedrichsOperator`, and mathlib's
Dini, continuous functional calculus, and real limit theorems.

During scratch iteration a second check was launched before collecting the
first check's completion; this breached the one-process workflow and was
reported in chat. Both ended. Subsequent compiler runs and all final module
audits were collected serially. No compiler process from this task remains.
No numerical experiment or external computation was used. Frontier map is read-only.

## Remaining mathematical obligation

The constructed T is a genuine self-adjoint receiver for the scalar transform.
The subsequent [cusp-packet construction](sqb-entire-cusp-occurrence.md) supplies
actual unit domain vectors and approximate occurrence at every transformed real
cusp frequency. At each full complex Xi target it proves an exact residual defect,
vanishing precisely on critical copies; it does not assert occurrence for all copies.
The real-preimage theorem still makes the existence of a matching real native
parameter for each actual Xi zero equivalent to that zero's critical placement.
An occurrence producer must therefore use independent original-source identities;
assuming the matching parameter would assume the missing conclusion. The scalar
classifier needs only the real transformed range `[−1,∞)`, corresponding to T's
proved lower bound. The intended entire-transform branch is therefore

`original modular covariance → g(B) → T with lower bound −1 → independent Xi occurrence → RH`.

Universal occurrence at the full transformed Xi parameter remains to be proved.
The original SQB quarter-domination inequality is still open;
the entire-transform classifier does not by itself require that stronger gap.
