# Sonin Cutoff Transversality Realization

- **ID:** sonin-cutoff-transversality-realization
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (source-defined prolate naturality defect; two immediate shortcuts refuted)
- **Source:** `../3-formalized/new/cutoff-cross-boundary-seam-nonmember.md`;
  `../3-formalized/new/mplus-torsion-seam-extension.md`;
  Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*, arXiv:2310.18423v2,
  Section 4.3 and Remark 4.2(i)
- **Statement:** `[CONJECTURE]` The source-defined formal semilocal prolate operators

  `W_{lambda,S} = (H + 1/2)^2 + lambda^2 N_S`

  have a prime-place naturality defect on the common cyclic core

  `Omega_{S,lambda} := W_{lambda,S} eta_S - eta_S W_{lambda,infinity}
                     = lambda^2 (N_S eta_S - eta_S N_infinity)`.

  Let `Q_{lambda,infinity}` and `Q_{lambda,S}` be compatible bounded idempotents onto the
  archimedean and semilocal Sonin sectors. The live cutoff cochain is the two-space corner

  `Delta_{S,lambda} := (1 - Q_{lambda,S}) Omega_{S,lambda} Q_{lambda,infinity}`.

  If this corner extends to a stated Schatten ideal and has a presentation- and admissible-gauge-invariant
  determinant boundary, then the decisive native test is its two-place cross-effect after transport to a
  common determinant line. A nonzero nonfake cross-effect would be a genuinely mixed archimedean--prime seam;
  decomposition into one-prime terms would close this route at BRIDGE strength. A finite Fitting
  presentation, if canonically constructed, must still pass

  `X^m ∤ tr(adj(A_lambda) Delta_{S,lambda})`.

  The canonical place transition and the raw support dilation do not qualify. The formal prolate
  operator is already present in the source; its analytic corner and determinant-line realization are not.

## Goal

Deconflict from the remote-defect / finite-probe route. The question here is not how far out an
off-line zero hides from finite degree. The question is whether the actual source-defined failure of
prolate naturality crosses the Sonin sector in a way that survives a presentation-invariant determinant
boundary before any zero-location, Hankel, Markov, or Li positivity chart is evaluated.

Existing formal cards already prove the abstract algebra:

- pinned-germ scalar actions have zero cross-boundary cochain;
- commutator defects `sigma A - A sigma` have zero Fitting boundary;
- an abstract cutoff-crossing cochain can be determinant-transverse and nonfake;
- split diagonal torsion presentations are boundary-blind.

So the only possible new content is analytic and categorical realization: close the formal prolate
operator on a controlled domain, prove the corner of its place-naturality defect belongs to a trace
ideal, construct its stable determinant-line presentation, and compute the mixed-place boundary class.

## Source-realization audit

`[PROVED HERE; see ../2-fully-proven/new/sonin-place-transition-cutoff-dichotomy.md and
../2-fully-proven/new/sonin-euler-metric-corner-noncompact.md]` The source audit separates the
transition, raw dilation, Euler metric, and formal prolate objects:

1. The place-enlargement transition between semilocal Sonin spaces becomes the identity on the common
   entire-function carrier `B_lambda`. Every cutoff transported from that carrier is intertwined, hence
   its transition boundary is zero. The abstract theorem is formalized as
   `canonicalTransition_boundary_eq_zero` in `CutoffCochain.lean`.
2. In the one-prime coordinate the explicit factor is
   `T_p g(u)=g(u)-p^(-1/2)g(u/p)`. Against the raw support cutoff, its crossing corner is a scalar
   multiple of a unitary map between the shells `(lambda/p,lambda]` and `(lambda,p lambda]`; it has
   infinite multiplicity and is noncompact. It is not a finite polynomial matrix entry and has no
   adjugate trace in `FittingSeamBoundary`.
3. The source's `sigma_p` is a self-Fourier Sonin vector, not an endomorphism `U_p` of a fixed carrier.
   Replacing it by the lower-left entry of an abstract `2 x 2` sheared witness was therefore a type jump.
4. The paper nevertheless does define the first formal semilocal prolate candidate `W_{lambda,S}`.
   Its cyclic grading is genuinely place-sensitive: Remark 4.2(i) states
   `N_S eta_S != eta_S N_infinity` unless `S = {infinity}`. Thus for `lambda != 0` the formal defect
   `Omega_{S,lambda}` is nonzero. This nonvanishing is source-level SEARCH, not the desired seam class.
5. The bounded positive Euler metric on the common `B_lambda` carrier does not provide a trace-ideal
   replacement. For the pinned archimedean norm, its corner across the **actual** Sonin projection is
   noncompact for every `lambda>0` and every prime `p`. The proof constructs high-frequency shell modes
   that are asymptotically Sonin while one dilation moves the full shell across the physical cutoff.

For any cutoff-compatible place transition `J_{T,S}`, Lean now proves the exact structural identity

`(1-q_T)(W_T J_{T,S} - J_{T,S} W_S)q_S
   = crossBoundary(q_T,W_T) J_{T,S} - J_{T,S} crossBoundary(q_S,W_S)`.

On a common carrier this is a vertex difference `b_T-b_S`. Thus the raw naturality defect is a
coboundary: an obstruction theory allowing arbitrary vertexwise subtraction kills it. The determinant
construction must derive and restrict the admissible gauge group rather than declare the class nonfake.

`[OPEN CORE]` Promote `W_{lambda,S}` and `Omega_{S,lambda}` from their formal cyclic core to controlled
closed operators, construct domain-compatible Sonin idempotents, prove `Delta_{S,lambda}` is in a stated
Schatten class, and construct a presentation-invariant determinant boundary. Then compute its two-place
cross-effect. Until these steps, the low-coefficient test is not well-typed for the Sonin source.

## Gates

- [x] 0 -> 1 candidate shape: different from remote visibility; source-side cutoff action; attack listed
- [ ] 1 -> 2 fully-proven: construct the closed realization of `W_{lambda,S}`, prove the corner of
  `Omega_{S,lambda}` lies in a stated trace ideal, construct a presentation-invariant determinant
  boundary, and prove either a nonzero mixed-place cross-effect or one-prime decomposition
- [ ] 2 -> 3 formalized: Lean statement for the concrete trace-ideal datum, its stable
  finite-projective or determinant-line reduction, and the resulting boundary witness
- [ ] 3 -> 4 publication-ready

## Attack

- This is not a proof of RH. It is an attempt to locate a source-side obstruction class.
- This cannot reuse the pinned-germ prime action: that action is central at the local germ and already
  collapses.
- This cannot use the commutator `sigma A - A sigma`: formal trace cyclicity kills it for every
  presentation.
- This cannot use a split torsion presentation: the split model is boundary-blind even for a crossing
  corner.
- This cannot promote `Omega != 0`: `Omega` is an exact naturality coboundary, and arbitrary vertexwise
  gauge subtraction kills it.
- This cannot substitute the positive Euler norm-change operator for `Omega`: its actual-Sonin corner
  is noncompact, hence outside every Schatten class.
- This cannot grade success by detecting an off-line zero. The witness must be invariantly defined at
  the trace-ideal/determinant-line level; a low coefficient of `tr(adj(A) Delta)` is admissible only
  after a stable finite-projective presentation has been constructed.

## Approach

1. Put the formal `W_{lambda,S}` on a common invariant core and prove a closed or self-adjoint
   realization with explicit domain behavior under `eta_S`.
2. Construct the Sonin idempotents and prove
   `(1-Q_{lambda,S}) Omega_{S,lambda} Q_{lambda,infinity}` lies in a stated trace ideal.
3. Extract a stable determinant-line or finite-projective presentation `A_lambda`, derive its admissible
   gauge transformations, and prove the boundary is invariant under them. Only then compute the
   row-replacement determinant form

   `tr(adj(A_lambda) Delta_{p,lambda})
    = sum_i det(A_lambda with row i replaced by row_i(Delta_{p,lambda}))`.

4. Transport the determinant boundaries to a common target and compute the bi-reduced two-place
   cross-effect. Promote only one of two outcomes:

   - `[PROVED]` mixed determinant-transverse: the two-place cross-effect is nonzero, giving a native
     seam class not reconstructed from singleton primes;
   - `[PROVED]` one-prime decomposition: every boundary splits into singleton terms, closing this
     handle at BRIDGE strength.

## Log

- 2026-07-09 - created from the route deconfliction request: avoid remote/finite-probe visibility and
  push the distinct Sonin cutoff-crossing torsion seam realization instead.
- 2026-07-09 - [BRIDGE] Extracted the existential non-split witness into named Lean API in
  `formal/GaloisForLFunctions/RHTower/CutoffCochain.lean`:
  `polynomialLowerCrossing`, `polynomialLowerCrossing_eq_crossBoundary`,
  `shearTorsionPresentation`, `shearTorsionPresentation_det`,
  `fittingBoundaryTrace_shearTorsion_lowerCrossing`,
  `fittingBoundaryClass_shearTorsion_lowerCrossing_ne_zero`,
  `lowerCrossing_not_right_factor_shearTorsion_mod_X_pow`, and
  `lowerCrossing_not_left_factor_shearTorsion_mod_X_pow`.  This does not solve the arithmetic
  Sonin realization; it gives a conditional sheared normal form for any future stable
  finite-projective reduction. It does not show that the source supplies such a reduction.
- 2026-07-09 - [BRIDGE] The open arithmetic computation is now one coordinate residue in a sheared
  chart, not a full adjugate-trace calculation.  The Lean card
  `../3-formalized/new/sheared-seam-coordinate-criterion.md` proves that for
  `A_m = [[X^m,1],[0,1]]`, every defect satisfies
  `tr(adj(A_m) Delta) = Delta_00 - Delta_10 + X^m Delta_11`, so the Fitting class is exactly
  `jetClass(Delta_00 - Delta_10)`. Thus any future trace-ideal Sonin/prolate datum equipped with a
  source-built stable sheared presentation must prove either
  `X^m ∤ (Delta_{p,lambda,00} - Delta_{p,lambda,10})` or that this entry difference is always
  divisible by `X^m`. No such presentation has yet been constructed.
- 2026-07-09 - [BRIDGE] The residue criterion is now packaged as a concrete one-label
  `TorsionSeamPresentation`: `shearedTorsionSeam m Delta`.  For this object, Lean proves
  `HasDeterminantTransverseDefect` iff `X^m ∤ (Delta_00 - Delta_10)`, and residue nondivisibility
  gives both right and left nonfake defects. This remains an abstract acceptance test, conditional on
  first constructing a stable finite-projective reduction of a trace-ideal cutoff corner.
- 2026-07-09 - [RETIRED by source-realization audit] The earlier proposal to read the standard-cutoff
  calculation as an immediate Sonin target was ill-typed. Lean proves abstractly that
  `crossBoundary standardCutoff sigma = [[0,0],[sigma_10,0]]` and the sheared boundary class is
  `jetClass(-sigma_10)`, but the source's `sigma_p` is a vector, while its canonical transition has
  zero transported-cutoff boundary and its raw dilation corner is noncompact. The standard-chart
  criterion becomes relevant only after the missing trace-ideal operator and invariant reduction exist.
- 2026-07-09 - [PROVED] The bounded Euler-metric fallback is closed in the pinned archimedean
  realization. `sonin-euler-metric-corner-noncompact.md` proves that the actual Sonin projection retains
  asymptotically shell-localized high-frequency modes, so
  `(1-P_lambda)M_{|1-p^(-1/2-is)|^2}P_lambda` is noncompact for every prime and `lambda>0`.

## Source-defined construction to attack

`[SEARCH]` The nonzero operator `Omega_{S,lambda}` is an exact naturality coboundary `delta W`; its
nonvanishing alone is neither novel nor a curvature theorem. The first possible new class occurs only
after the Sonin cutoff and determinant operations: a nonzero operator can be block diagonal, a nonzero
corner can be noncompact, and a trace-class corner can still have zero determinant boundary.

`[CONJECTURE]` After analytic closure, the determinant boundary of `Delta_{S,lambda}` has a nonzero
two-place cross-effect. The kill cases are `lambda = 0`, `S = {infinity}`, a block-diagonal Sonin action,
a non-trace-ideal corner, determinant compatibility, or decomposition into one-prime terms.

`[CONJECTURE]` If the raw corner is not Schatten, the relative resolvent identity

`R_T(z) J - J R_S(z) = -R_T(z) (W_T J - J W_S) R_S(z)`

provides the source-respecting smoothing. The next test is whether this relative resolvent is trace
class and yields a canonical perturbation determinant; failure retires the smoothing variant.
