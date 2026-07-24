# Von Mangoldt–Gamma Beta reflection rank-one repair no-go

- **ID:** ccm-beta-rank-one-repair-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/handover/connes.md`
- **Statement:** The cofinal factorial/Beta-reflected von Mangoldt–Gamma source has a complex two-dimensional negative subspace for every sufficiently large displacement, so no single positive rank-one boundary channel—including boundary diagonal `4`—can make it positive semidefinite.

## Goal

Decide whether the already-formalized factorial/Beta reflection can supply source-side positivity
for the fixed CCM Ward block.  The existing `2 × 2` determinant obstruction proves only one
negative direction and therefore does not exclude repair by the one boundary channel.  This card
tests the exact missing rank-one repair question.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, `lake env lean` green, axiom audit uses only standard Lean axioms
- [ ] 3 → 4  publication-ready: not a standalone paper target

## Approach

Let `A_x(i,j)=m_{i+j+1}(x)/(i+j+1)!` on orders `0,1,2,3`.  After multiplication
by `2^(x+1)`, first-prime dominance gives the entrywise limit

`L(i,j)=(log 2)^(i+j+2)/(i+j+1)!`.

Writing `ell=log 2`, the two columns

`u=(-1/2, 1/ell, 0, 0)` and
`v=(-1/120, 1/(10 ell), -1/(2 ell^2), 1/ell^3)`

compress `L` to `ell^2 * diag(-1/12, -1/100800)`.  Entrywise convergence and the
finite-dimensional perturbation lemma therefore make `span_C{u,v}` negative definite for `A_x`
eventually.  If `A_x + b b*` were positive semidefinite, the complex Krein–Langer rank-one bound
would force every negative-definite subspace of `A_x` to have dimension at most one, contradicting
this explicit plane.

## No-go closure

- **Exact killing theorem/mechanism:** `betaFactorialFourComplexGram_eventually_negDef_on_plane` gives a fixed complex two-dimensional negative plane eventually; `betaFactorialFourComplexGram_eventually_not_posSemidef_add_rankOne` excludes every positive rank-one repair.
- **Strongest positive survivor:** the Beta reflection has a canonical alternating-sign factorial chamber; its negative index, not merely determinant sign, is the invariant controlling required boundary-channel count.
- **New insight:** one scalar boundary charge cannot repair this source reflection.  Any surviving CCM construction must change the source kernel or introduce at least two independent positive channels before the singular Ward lift.
- **Status:** `[PROVED HERE]` and formalized unconditionally in `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaBetaReflectionRankOneRepairNoGo.lean`; axiom audit is `[propext, Classical.choice, Quot.sound]`; wired into `GaloisForLFunctions.RHTower`.

## Log

- 2026-07-24 — created directly in `1-in-progress` after corpus audit found only the one-negative-direction `2 × 2` theorem.
- 2026-07-24 — proved explicit two-pivot compression `diag(-1/12,-1/100800)`, transferred it to the actual cofinal source, and formalized universal rank-one unreparability.
