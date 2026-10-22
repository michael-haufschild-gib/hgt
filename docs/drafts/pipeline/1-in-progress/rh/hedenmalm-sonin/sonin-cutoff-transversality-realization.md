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
6. The normalized cyclic grading nevertheless has a strict source-defined low-mode sign. For every
   finite nonempty prime set `P`, `semilocal-all-even-jacobi-prolate-residue-tower.md` proves an
   alternating nonzero ground-state residue in every positive even Jacobi degree. Its first member is
   `a_0(P)^2<1/2` and

   `<e_0^P,(N_PJ_P-J_PN_infinity)e_2^infinity>
      =2(1/2-a_0(P)^2)/sqrt(3/2)>0`.

   Thus the formal naturality defect is explicitly nonzero on the normalized polynomial core. This
   does not yet imply that its exact Sonin corner is nonzero or Schatten.
7. The inverse-metric and polar-unitarization fallbacks are also closed. By
   `sonin-euler-inverse-polar-corner-noncompact.md`, noncompactness of the positive Euler metric corner
   forces noncompactness of the inverse metric and both square-root corners. Hence the exact bounded
   Sonin identification `theta_p` cannot be converted by polar decomposition into a unitary map that
   preserves the Sonin sector modulo compacts.
8. The formal domain problem has been reduced to a genuine extension problem. The card
   `semilocal-jacobi-linear-growth-prolate-domain-gate.md` proves explicit two-sided comparison
   `a_n(S)asymp a_n(infinity)asymp n`, so the parity-block prolate off-diagonals grow quadratically.
   Their reciprocal series converges. Thus the elementary Jacobi Carleman divergence criterion does
   not supply essential self-adjointness; a source-selected boundary condition is indispensable.
9. The raw determinant variant is closed independently of compactness estimates. By
   `semilocal-prolate-defect-triangular-determinant-blindness.md`, the pulled-back grading defect lowers
   the cyclic polynomial filtration strictly. Every finite truncation is nilpotent with determinant
   one; any compact extension is quasinilpotent, and any trace-class extension has Fredholm
   determinant one. Resolvent mixing is therefore essential, not optional regularization.
10. Exact Sonin compression does not erase every smoothed grading residue. The card
    `sonin-small-cutoff-ground-row-survival.md` projects the defect to the semilocal ground state and
    smooths on the right by `(N_infinity+1)^(-1)`. The result is a canonical nonzero rank-one
    trace-class corner for every sufficiently small positive cutoff. This proves local survival, but
    its pulled-back Fredholm determinant is still one. Its trace norm tends to zero as the cutoff
    tends to infinity, so it supplies no uniform cofinal large-cutoff obstruction.
11. The live prolate-resolvent corner now has an exact source factorization. By
    `sonin-relative-resolvent-sylvester-factorization.md`, after pullback through `theta_S` it is

    `R_(S,complement)(z) H_S-H_S R_(infinity,Sonin)(z)`,

    where `H_S=(1-Q_infinity)G_SQ_infinity` is the noncompact Euler cyclic-density corner. Thus
    trace-class restricted resolvents are sufficient to regularize the corner, while vanishing is
    equivalent to an exact restricted spectral intertwiner. The analytic unknowns are now the
    source-selected extensions, reduction by the Sonin spaces, resolvent Schatten class, and spectral
    separation--not the algebraic form of the corner.
12. A cofinal analytic control is now complete at one prime. The card
    `transported-prolate-relative-resolvent-corner.md` transports the unique archimedean self-adjoint
    prolate operator through `theta_p`. For every cutoff and nonreal resolvent parameter, its cyclic
    relative-resolvent Sonin corner is nonzero and trace class. Nonvanishing follows because the
    noncompact Euler corner cannot be supported on the finite positive-exception subspace of the
    Sonin spectrum, while the infinite negative Sonin spectrum is disjoint from the positive
    complementary spectrum. This proves that the analytic survival package is consistent, but the
    transported grading is `theta_pN_infinitytheta_p^(-1)`, not `N_p`; it is an isospectral control,
    not the arithmetic semilocal prolate operator.
13. The arithmetic remainder is one formal grading deformation. The card
    `semilocal-prolate-control-deformation.md` defines

    `K_p=N_p-theta_pN_infinitytheta_p^(-1)`

    gives the formal identity

    `W_(lambda,p)^cyc=W_(lambda,p)^theta+lambda^2K_p`.

    If a common closed graph realization exists, the genuine cyclic relative-resolvent corner is the
    cofinally nonzero trace-class control corner minus the single second-resolvent correction
    `lambda^2(1-Q_p)R_cycK_pR_thetaeta_pQ_infinity`.
14. No unitary transport can remove that deformation. By
    `semilocal-prolate-unitary-transport-trilemma.md`, a unitary intertwining both scaling and grading
    would preserve the ground-state scaling norm `a_0^2`, contradicting
    `a_0(p)^2<1/2=a_0(infinity)^2`. More strongly, no single unitary intertwines the two formal
    prolate families at two distinct positive parameters. The genuine semilocal realization must be a
    new extension; it cannot inherit the archimedean family by a better unitary gauge.
15. The deformation has no bounded-perturbation realization. The candidate-new theorem
    `semilocal-grading-deformation-unbounded.md` proves

    `|<p_0,[N_infinity,G_p]p_(2k)>| asymp_p k^(1/4)`.

    Metric self-adjointness of `theta_p^(-1)N_ptheta_p` then rules out every bounded operator `K`
    satisfying `theta_p^(-1)N_ptheta_p=N_infinity+K` on `Dom N_infinity`. Thus the genuine operator
    cannot be obtained from the transported control by a bounded perturbation; graph-resolvent
    control is the first remaining analytic possibility. The ground row has the sharp smoothing
    threshold `alpha>3/4` for `(N_infinity+1)^(-alpha)`.
16. The natural domains do not furnish even a perturbation core. The candidate-new theorem
    `semilocal-prolate-core-disjointness.md` proves that in canonical spectral coordinates the cyclic
    core `C[s]` and transported core `w_pC[s]` intersect only at zero. After pullback, the cyclic
    ground `G_pp_0` lies in `Dom((N+1)^alpha)` exactly for `alpha<1/4`, so it is outside the
    transported number-form domain. A new graph/boundary relation is required before the formal
    `K_p` difference or second resolvent identity is well typed.
17. The direct cyclic transport `eta_P` has a distinct common form geometry. The bridge card
    `semilocal-number-form-equivalence.md` proves

    `Dom(N_P^(1/2))=Dom(N_infinity^(1/2))`

    with explicit equivalent forms, using the distance-to-polynomial-filtration identity. Hence the
    genuine cyclic prolate forms share a canonical energy domain and a bounded self-adjoint energy
    representative. This does not produce an `L^2` self-adjoint prolate operator; it moves the open
    core to a gap/boundary theorem compatible with the exact Sonin projection.
18. Bare self-adjoint extension exists. The bridge card
    `semilocal-prolate-extension-rank-two-ambiguity.md` proves that each real parity-block Jacobi
    minimal operator has deficiency indices `(0,0)` or `(1,1)`. Hence an extension always exists, and
    changing a parity-preserving extension changes the full resolvent by rank at most two. Schatten
    membership is therefore boundary-independent up to finite rank, but determinant scalars can vary.
    The remaining extension problem is canonical Sonin-compatible selection, not existence.
19. The archimedean alternative is now exact.  The bridge card
    `archimedean-prolate-jacobi-limit-circle-transition.md` applies the exceptional double-root
    power-asymptotic classification to both explicit prolate parity matrices.  At every positive
    prolate parameter, each block is limit-circle with deficiency `(1,1)`; at parameter zero each is
    limit-point.  Thus the transported control genuinely carries two boundary angles, rather than
    inheriting essential self-adjointness from its formal Jacobi expression.  The new Lean module
    `SemilocalProlateCriticalPotential.lean` proves the exact four-radius identity

    `2R = Delta(a^2) - [(Delta a)^2+(Delta a)^2]`

    and its metaplectic-anomaly form.  This reduces the unresolved semilocal classification to the
    high-degree source asymptotics of one explicit critical potential; quadratic coefficient
    comparability alone cannot decide it.

For any cutoff-compatible place transition `J_{T,S}`, Lean now proves the exact structural identity

`(1-q_T)(W_T J_{T,S} - J_{T,S} W_S)q_S
   = crossBoundary(q_T,W_T) J_{T,S} - J_{T,S} crossBoundary(q_S,W_S)`.

On a common carrier this is a vertex difference `b_T-b_S`. Thus the raw naturality defect is a
coboundary: an obstruction theory allowing arbitrary vertexwise subtraction kills it. The determinant
construction must derive and restrict the admissible gauge group rather than declare the class nonfake.

`[OPEN CORE]` Promote `W_{lambda,S}` and `Omega_{S,lambda}` from their formal cyclic core to controlled
closed operators, construct domain-compatible Sonin idempotents, prove `Delta_{S,lambda}` is in a stated
Schatten class, and construct a presentation-invariant determinant boundary. Then compute its two-place
cross-effect. The positive degree-two-to-degree-zero polynomial-core residue is now known, so the first
unresolved map is precisely its survival under exact Sonin compression. Until that step, the
low-coefficient test is not a cofinal Sonin-sector invariant. A rank-one number-resolvent shadow now
survives exact Sonin compression at sufficiently small cutoff, so the unresolved issue is specifically
prolate-resolvent closure, determinant nontriviality, and persistence to arbitrarily large cutoffs.
The transported control now proves persistence and trace class at every cutoff for one prime, so the
remaining operator-theoretic unknown is specifically the deformation from
`theta_pN_infinitytheta_p^(-1)` to the genuine cyclic grading `N_p`.

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
- This cannot repair the norm-change operator by inversion or polar square root: those actual-Sonin
  corners are noncompact as well.
- This cannot replace `theta_p` by another unitary transport intertwining both source scaling and
  grading, or the full prolate family: strict first-Jacobi contraction forbids it.
- This cannot take an ordinary or Fredholm determinant of the raw prolate naturality defect: its
  strict filtration lowering makes every such determinant trivial whenever defined.
- This cannot grade success by detecting an off-line zero. The witness must be invariantly defined at
  the trace-ideal/determinant-line level; a low coefficient of `tr(adj(A) Delta)` is admissible only
  after a stable finite-projective presentation has been constructed.
- A chosen self-adjoint extension is not automatically source data. If a prolate parity block is
  limit-circle, Krein's resolvent formula makes changes of boundary condition rank one; the resulting
  perturbation determinant can therefore acquire an extension-dependent scalar factor. Before any
  determinant is called canonical, either prove essential self-adjointness or derive a compatible
  boundary condition from the semilocal Fourier/Sonin structure and prove invariance under the
  remaining extension freedom.

## Approach

1. Put the formal `W_{lambda,S}` on a common invariant core and prove a closed or self-adjoint
   realization with explicit domain behavior under `eta_S`. The Jacobi coefficients are now known to
   have quadratic prolate growth, but the easy Carleman criterion is unavailable.
   Determine the limit-point/limit-circle alternative for both parity blocks. Existence is automatic;
   in the limit-circle case, derive the boundary condition from source symmetries rather than selecting
   an angle.
   Equivalently, start from the closed transported control and prove relative control of
   the formal difference `K_p=N_p-theta_pN_infinitytheta_p^(-1)`. A bounded realization is now
   refuted, so the estimate must begin with a newly constructed common graph domain.
   In parallel, use the common `eta_P` energy domain and decide whether its bounded indefinite-form
   representative admits a source-selected `L^2` realization.
2. Construct the Sonin idempotents and prove
   `(1-Q_{lambda,S}) Omega_{S,lambda} Q_{lambda,infinity}` lies in a stated trace ideal.
   For the relative-resolvent variant, use the proved Sylvester factorization: establish trace-class
   restricted resolvents and rule out an intertwiner between the semilocal complementary spectrum and
   the archimedean Sonin spectrum.
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

## 2026-08-02 prime-resolved asymptotic input

`[PAPER+LEAN-PROVED]` The one-prime grading coefficient now has an exact geometric-subsequence
profile, not only `k^(-3/4)` bounds. For `k_j=c p^(2j)`, the intrinsically normalized literal
coefficient converges to

```text
F_p(c)=sum_(z in Z) sqrt(2c) p^(-z) exp(-4c p^(-2z)) > 0,
F_p(c p^2)=F_p(c).
```

This is a genuine prime-label signature. By the updated source-clock theorem it is nevertheless
local Euler data for every fixed prime or finite prime set, so it cannot itself be promoted to a
global determinant boundary. The next admissible analytic step is cofinal: propagate the
prime-resolved profiles through finite-set orthogonalization and determine whether the exact
critical potential has a source-stable limit or a nontrivial infinite-label boundary relation.
Replacing that step by one-prime scalarization would erase the source class.
