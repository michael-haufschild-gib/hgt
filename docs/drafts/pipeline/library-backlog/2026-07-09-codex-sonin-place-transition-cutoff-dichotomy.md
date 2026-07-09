# Library ticket: Sonin place-transition cutoff dichotomy

- **Target docs:** `docs/drafts/door/00-index.md`; `docs/drafts/door/00-status.md`;
  `docs/drafts/door/bucket-the-seam-archimedean-obstruction.md`;
  `docs/drafts/rh-monodromy-weight-mismatch/129-pinned-carrier-geometry-candidates.md`;
  `docs/drafts/rh-monodromy-weight-mismatch/130-sonin-seam-defect-commutator-nogo.md`;
  `docs/drafts/rh-monodromy-weight-mismatch/131-cross-boundary-cochain.md`
- **Source card:** `docs/drafts/pipeline/2-fully-proven/new/sonin-place-transition-cutoff-dichotomy.md`
- **Active successor:** `docs/drafts/pipeline/1-in-progress/sonin-cutoff-transversality-realization.md`
- **Formal file:** `formal/GaloisForLFunctions/RHTower/CutoffCochain.lean`

## Update needed

Record the two source-level no-gos beyond the abstract cutoff-crossing witness and the surviving
formal prolate defect:

1. Connes--Consani--Moscovici's `sigma_p` is a self-Fourier Sonin vector, not an endomorphism `U_p`
   of a fixed Sonin carrier.
2. Their place-enlargement maps canonically identify every semilocal Sonin space with the same
   entire-function carrier `B_lambda`. A cutoff transported from that carrier is intertwined by place
   transition, so its cross-boundary is zero.
3. `CutoffCochain.lean` formalizes the general theorem as
   `canonicalTransition_boundary_eq_zero` together with its transition/intertwining support API.
4. In the one-prime multiplicative coordinate the explicit place factor is
   `T_p g(u)=g(u)-p^(-1/2)g(u/p)`. Its raw support-cutoff corner is a scalar multiple of a unitary
   between the shells `(lambda/p,lambda]` and `(lambda,p lambda]`; it is noncompact and does not define
   the finite polynomial Fitting class used by the current torsion-seam interface.
5. The paper does define a first formal semilocal prolate candidate
   `W_{lambda,S}=(H+1/2)^2+lambda^2 N_S`. Remark 4.2(i) gives
   `N_S eta_S != eta_S N_infinity` for nontrivial `S`, hence the formal place-naturality defect
   `Omega_{S,lambda}=W_{lambda,S}eta_S-eta_SW_{lambda,infinity}` is nonzero for `lambda != 0`.
   The deferred items are the general-`S` Jacobi coefficients and a second metaplectic candidate, not the
   existence of this first formal candidate.
6. Therefore the abstract `2 x 2` sheared witness is not an arithmetic Sonin realization, but neither is
   the source route waiting for an invented `U_p`. The live target is the Sonin cutoff corner of
   `Omega_{S,lambda}`: prove a Schatten-class extension, construct a presentation-invariant determinant
   boundary, and compute whether its two-place cross-effect is nonzero or splits into one-prime terms.
7. `CutoffCochain.lean` now formalizes `operatorNaturalityDefect` and
   `transitionBoundary_operatorNaturalityDefect`. For cutoff-compatible transitions, the cutoff corner of
   `W_TJ-JW_S` is exactly the difference of the transported local `W`-corners. On a common carrier this
   telescopes as `b_T-b_S`, so arbitrary vertexwise gauge subtraction would kill it. The active card must
   derive the admissible gauge group; if the raw corner is not Schatten, its canonical fallback is the
   relative-resolvent identity.

## Suggested grade

THEOREM (paper) + THEOREM (Lean structural core), BRIDGE (substrate, route-closing). The canonical
place transition is killed; the raw support crossing is outside the determinant category; the formal
prolate naturality defect is the source-defined successor, with its analytic cutoff and determinant
realization still open.
