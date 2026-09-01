# HB unbounded maximal dissipative reflected forcing no-go

- **ID:** HB-MAXDISS-REFLECT
- **Stage:** 3-formalized
- **Type:** ROUTE-CLASS NO-GO THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` HB source-semantic two-leg Peierls core
- **Statement:** Closed order-maximal dissipative/antidissipative unbounded dynamics have unique nonzero forced responses in matching open half-planes, so cannot extinguish either exact source on a tilted Schwarz Xi pair.

## Goal

Kill chain `exact tilted 2s Teukolsky source -> unbounded maximal passive boundary exclusion -> universal source extinction -> HB Ward cancellation -> RH`.

## Gates

- [x] 0 → 1 in-progress: corpus chain, exact operator class, defect-extension attack fixed
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: direct Lean, targeted build, axiom audit green
- [ ] 3 → 4 publication-ready: standalone paper

## Proof [PROVED HERE]

Let `A` be closed and dissipative and let `Im z>0`. Imaginary-part expansion and
Cauchy--Schwarz give `Im(z)||x|| <= ||(A-z)x||`. Thus `A-z` is injective. The same
bound controls both coordinates of the closed graph by `(A-z)x`, so its range is closed.

If nonzero `y` is orthogonal to that range, then `y ∉ dom A`: otherwise the imaginary
part of `⟨(A-z)y,y⟩=0` contradicts dissipativity and `Im z>0`. Hence every vector in
`dom A + C y` has a unique form `x+c y`. Define
`B(x+c y)=A x+c conj(z)y`. From `y ⟂ ran(A-z)`,
`⟨A x,y⟩=conj(z)⟨x,y⟩`; consequently the two cross terms in `⟨x+c y,B(x+c y)⟩`
are conjugates. Its imaginary part is
`Im⟨x,A x⟩-|c|² Im(z)||y||² <= 0`. Thus `B` is a proper dissipative extension,
contradicting order maximality. Therefore `ran(A-z)ᗮ=0`; closedness makes the range all
space. Injectivity and the lower bound give every nonzero source a unique nonzero response.

For closed order-maximal antidissipative `A` and `Im z<0`, identical calculations reverse
both inequalities. The extension still uses eigenvalue `conj z`, whose imaginary part is
positive, and proves the lower-half-plane resolvent law.

Apply this to the corpus-proved opposite nonzero imaginary angular parameters and nonzero exact doubled-weight Teukolsky sources at `q` and `copyConj q`.

## Hostile audit

- Claims only forcing extinction no-go; nonzero responses may still have vanishing two-leg observables.
- Survivor must use non-maximal deficiency/domain exclusion, nonlinear dynamics, orientation change, or observable cancellation.
- General maximal-dissipative resolvent theorem is classical. New claim is exact reflected Xi/Teukolsky route-class closure and Lean certificate.

## No-go closure

- **Killed:** closed order-maximal unbounded linear dissipative/antidissipative source extinction.
- **Positive survivor:** a linear extinction law must expose a non-maximal range-defect/domain exclusion; otherwise use nonlinear dynamics, orientation change, or observable-level cancellation.
- **Significance:** removes the maximal-domain nonnormal passive class, not a numerical regime.

## Formalization

Module:
`GaloisForLFunctions.RHTower.ThetaCuspHawkingHBUnboundedMaximalDissipativeReflectedForcingNoGo`

Main theorem:
`d4HBUnboundedMaximalDissipativeReflectedForcingExclusionRouteKilled`

Audit: direct `lake env lean` PASS; targeted `lake build` PASS; axioms only
`propext`, `Classical.choice`, `Quot.sound`; umbrella wired. Global lint reports only pre-existing
unreachable owned modules; new module is reachable and has no forbidden declaration.

## Novelty audit through 2026-08

Corpus search found bounded dissipative forcing, unbounded self-adjoint forcing, maximal-domain
coefficient realizability, and source-fixed Peierls endpoints, but no unbounded maximal nonnormal
reflected-pair theorem. General maximal-dissipative resolvent/extension theory is classical.
Primary Teukolsky/QNM literature supplies radial dynamics and boundary conditions but no exact
Xi-source reflected forcing no-go. Novel contribution is route-specific defect classification and
Lean closure.
