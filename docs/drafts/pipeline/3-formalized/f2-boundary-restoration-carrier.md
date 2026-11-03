# F2 — an exact boundary extension of the Lewis source carrier

- **Stage:** 3-formalized
- **Parameters:** `w=2s`, `0<Re s<1/2`.
- **Purpose:** Identify the corrected first-prime operator with actual source transport, retaining the coordinate lost by completed-period restoration.

## Exact restoration

Use the evaluation functionals `α,β` and templates `A,P` from the corrected Hecke construction. Write `q=2^(−w)`, `D=1−(w+1)q≠0`. Let `Rf=f+α(f)A+β(f)P` and `V={g:2g(2)=g(1)}`.

Evaluation gives

`(Rf)(1)=(w−1)β(f)`, `2(Rf)(2)=(Rf)(1)`.

For `g∈V`, set `F(g,c)=g−cA−g(1)/(w−1)P`. The template evaluations give

`α(A)=−1`, `β(A)=0`, `β(P)=(−1+2q)/D`,

`α(P)=(1−w)(1−4q)/(2D)`,

`β(g)=−qg(1)/D`, `α(g)=(4q−1)g(1)/(2D)`.

Consequently `β(F(g,c))=g(1)/(w−1)`, `α(F(g,c))=c`, and `R(F(g,c))=g`. Conversely `F(Rf,α(f))=f`. Thus `f↦(Rf,α(f))` is an explicit linear bijection from physical functions onto `V×ℂ`. In particular `ker R=span{A}`: restoration alone loses exactly the zeta-axis direction.

## The first-prime source evaluation law

Let `W_s` consist of functions fixed on `(0,∞)` by actual modular inversion and the Lewis three-term operator. Evaluating the three-term law at `1` gives `g(1)=g(2)+qg(1/2)`. Inversion at `2` gives `qg(1/2)=g(2)`. Hence `W_s⊆V`.

The actual four-branch formula now gives

`(T₂,s g)(1)=2g(2)+2qg(1)=(1+2q)g(1)`.

This is a boundary evaluation law for every member of the source carrier, not an assumed Hecke eigenfunction equation. Existing exact inversion commutation and three-term defect transport prove `T₂,s W_s⊆W_s`.

## Corrected transport on the extended carrier

Define `D_s={f:Rf∈W_s}`. The restoration bijection restricts to `D_s≃W_s×ℂ`. Write `λ=1+2q`. Since `T₂g∈W_s` and `(T₂g)(1)=λg(1)`, direct substitution in the actual corrected operator gives

`T̂₂,s F(g,c)=F(T₂,s g,λc)`.

Equivalently, for every `f∈D_s`,

`R(T̂₂,s f)=T₂,s(Rf)`, `α(T̂₂,s f)=λα(f)`.

Thus the corrected operator preserves `D_s`; its zero-boundary channel is invariant. No source eigenlaw is assumed for general carrier elements.

The audited global core identity and recovered coefficients give `R core_s=E_s` on the positive axis and `α(core_s)=ζ(w)`. Existing global inversion and three-term identities for `E_s` therefore place every actual upper-strip core in `D_s`. At upper resonances its boundary coordinate is zero.

## Scope

The source intertwining here concerns the first-prime Hecke operator and the inversion/three-term Lewis carrier. General-prime carrier invariance, compatibility with the full Mayer transfer family, a topology on this extension, mixed-parameter physical synthesis and Krein positivity are not consequences of these algebraic identities.

## Lean

`RenormalizedIntersectionTheory/MayerScattering/BoundaryRestorationCarrier`:

- `mayerBoundaryRestore_boundary_relation`
- `mayerCoreZetaCoordinate_reconstruct`
- `mayerCoreScatteringCoordinate_reconstruct`
- `mayerBoundaryRestore_reconstruct`
- `mayerBoundaryReconstruct_restore`
- `mayerCompletedLewisCarrier_boundary_relation`
- `mayerCompletedLewisCarrier_hecke_at_one`
- `mayerCompletedLewisCarrier_heckeT2`
- `mayerPeriodCore_mem_boundaryCarrier`
- `mayerCorrectedHeckeT2_reconstruct`
- `mayerBoundaryRestore_unique_preimage`
- `mayerBoundaryRestore_kernel_iff`
- `mayerBoundaryRestore_correctedHeckeT2`
- `mayerBoundaryCoreCarrier_correctedHeckeT2`

Individual final `lake --old env lean` audit passed without warnings. All fourteen declarations have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Umbrella import wired.
