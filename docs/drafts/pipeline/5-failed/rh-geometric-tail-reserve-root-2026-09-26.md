# Strict geometric theta reserve: obstruction and boundary invariant

- **ID:** RH-GEOMETRIC-TAIL-RESERVE-ROOT-20260926
- **Owner:** root
- **Stage:** 5-failed — strict-reserve strategy retired; C11 obstruction proved
- **Type:** THEOREM (Lean), derived [BRIDGE]
- **Parents:** full theta tail kernel, geometric-deficit split, analytic locality, C10

## Frozen C11 — proved unchanged

Let Phi be the complete theta source, K its tail first-moment kernel, and

    G(x,y) = integral_(s>0) sqrt((x+s)*(y+s))*Phi(x+s)*Phi(y+s).

For every real a and epsilon>0, there are n, real nodes t_i>max(a,0), and
real coefficients b_i such that

    sum_ij b_i*b_j*(K(t_i,t_j)-epsilon*G(t_i,t_j)) < 0.

Exact Lean theorem:
`RHTower.ThetaGeometricBoundaryAudit.exists_finite_negative_geometric_tail`
in `RHTower/ThetaTailGeometricCoercivityObstruction.lean`.

This excludes a strict geometric reserve on every real tail. It does not
give a negative packet for K or decide RH. Since K=2G+D on positive nodes,
the geometric split can only succeed at the sharp boundary D>=-2G.

## Scientific and whole-route audit

- Irritant: sqrt(t)*Phi(t) has singular tangent energy at zero; K's actual
  polynomial channels have finite secant limits there.
- Theta input: Phi(0)>0, its Schwartz regularity, and the complete source's
  actual analytic L2 realization. No first-atom approximation.
- Changed viewpoint: compare finite-section energies through the boundary
  derivative, then transport negative directions by analytic totality.
- Classification: [BRIDGE], because this mechanism was visible before C11
  was frozen. It is not a claimed new universal theory or an RH proof.
- Right-problem gate: both the all-tail obstruction and the nontrivial
  positive boundary invariant were required. Both are now formalized.
- Next unresolved core: the exact sign of unsubtracted K. More strict-margin
  obstructions would not replace an actual full-source sign argument.

## Dependency-closed paper proof [PROVED HERE]

1. For f=Phi^2, extended divided differences give, for x>0, the exact
   subtraction of f(0)*log(1/x) from integral_(t>x) f(t)/t. Differentiability
   makes dslope(f,0) continuous; Schwartz decay controls the infinite tail.
2. Set v(t)=sqrt(t)*Phi(t). Its positive-argument derivative is
   `v'(t)=Phi(t)/(2*sqrt(t))+sqrt(t)*Phi'(t)`. Integration by parts gives

       integral_(t>x) v'(t)^2 = integral_(t>x) Phi(t)^2/t /4
                               -Phi(x)^2/2 + integral_(t>x) t*Phi'(t)^2.

   The coefficient of log(1/x) is Phi(0)^2/4>0, so v'^2 is not integrable
   on (0,infinity), whereas v^2 is integrable.
3. Fatou's lemma forces arbitrarily large finite v secant energies at
   arbitrarily small positive steps. Otherwise their pointwise tangent
   limit would have finite squared integral.
4. A_c(t)=(t+c)*Phi(t) is Schwartz. Strong translation convergence gives
   finite limits for the squared secants of A_1 and A_-1 on (0,infinity).
   Exact Krein algebra identifies K's secant with half their energy
   difference; G's secant is v's energy. Thus K-epsilon*G has a strict
   negative two-node form at h,0 for each epsilon>0.
5. A common translation of both nodes is exactly a moving lower integral
   cut. Integrability gives continuity in that cut. A small translation
   preserves strict negativity and puts both nodes in (0,infinity).
6. On the connected open right half-strip, sqrt(z+s)*Phi(z+s), s>0, is
   weakly L2 analytic. Its square root stays in the slit plane. The exact
   bound norm(sqrt z)<=norm(z+1) for Re(z)>=0 lets it use the existing c=1
   polynomial channel's local L2 majorant.
7. Adjoin this geometric feature to the two polynomial channels. Use the
   bounded Hermitian form (differenceForm, -2*epsilon id). Compression to
   the closed section span gives an analytic total realization whose real
   kernel is exactly 2*(K-epsilon*G).
8. Step 5 gives a negative vector of this realization. Every real tail
   above max(a,0) accumulates inside its domain. Analytic totality
   approximates that vector by finite sections on the tail while
   preserving strict negativity.
9. The kernel is real on real nodes. Complex coefficient energy splits
   into the energies of its real and imaginary coefficients. One is
   negative. Reindex its finite support by Fin n, obtaining C11 exactly.

## No-go closure: strongest positive survivors

**Boundary invariant.** The tangent decomposition in step 2 is exact, and

    integral_(t>x) v'(t)^2 / log(1/x) -> Phi(0)^2/4.

After subtracting this logarithm, the remainder tends to

    [integral_0^1 dslope(Phi^2,0,t) + integral_(t>1) Phi(t)^2/t]/4
    -Phi(0)^2/2 + integral_(t>0) t*Phi'(t)^2.

Paper proof: steps 1–2; no open dependency. Lean:
`geometricTangent_energy_eq`, `geometricTangent_energy_finitePart_tendsto`,
`geometricTangent_energy_log_ratio_tendsto` in
`RHTower/ThetaGeometricBoundaryEnergy.lean`.

**Negative-dimension invariant.** Every finite negative dimension of the
augmented analytic realization is retained on every positive real tail.
Paper proof: analytic totality applied to each finite negative subspace.
Lean: `geometric_negative_dimensions_tail_iff` in
`RHTower/ThetaTailGeometricAnalyticLocality.lean`.

**New insight.** The geometric factor creates an exact logarithmic
boundary energy absent from the finite polynomial-channel secant limits.
Analytic transport preserves its sign obstruction on distant tails,
despite eventual positivity for each fixed node pattern. This identifies
the failure of strict geometric comparison without settling K's sign.

## Lean and repository audit

All eight named leaf builds pass; their proofs were checked in scratch
before packaging. Each leaf is wired exactly once:

- `HTGeometry.MellinBoundaryFinitePart`
- `HTGeometry.SecantEnergyBoundary`
- `HTGeometry.SchwartzSecantEnergy`
- `HTGeometry.ComplexSquareRootEnvelope`
- `RHTower.ThetaGeometricBoundaryEnergy`
- `RHTower.ThetaTailGeometricReserveObstruction`
- `RHTower.ThetaTailGeometricAnalyticLocality`
- `RHTower.ThetaTailGeometricCoercivityObstruction`

All 70 public theorem axiom reports pass (51 earlier + 19 final), only
propext, Classical.choice, Quot.sound; none missing. No heartbeat/recursion
override, forbidden declaration, numerical mathematical experiment, or
git command. Only necessary dependencies and named leaves were built.

Index regeneration passes. Final global `lint --check-generated` exits 1
on exactly two unrelated unwired RHTower modules:
`ShiftedDirichletPolynomialUniqueness`, `ShiftedDirichletTarget`.
There is no own-leaf or stale-generated-file error. Global lint is not green.

Evidence: `/tmp/rh-c11-boundary-axioms.log`,
`/tmp/rh-c11-final-axioms.log`, `/tmp/rh-c11-final-axiom-names.txt`,
`/tmp/rh-c11-final-leaf-build.log`, `/tmp/rh-c11-index-alltail.log`,
`/tmp/rh-c11-lint-alltail.log`.

## Corpus audit and remaining task

Deep searches inspected declarations, candidate lemmas, source arguments
(methods), proof ideas, and ingredient sets. Final exact-sign searches:
`/tmp/rh-c12-sharp-sign-search.json` (partial: text retrieval interrupted),
`/tmp/rh-c12-quadratic-sign-search.json` (complete against available index).
Both report complete inventories; compiler evidence is predominantly
source-only and semantic coverage unmeasured. Generated proposals about
entrywise positivity or unrelated kernels do not establish matrix PSD.

The existing literal double-Laplace and two-Volterra criteria in
`ThetaTailFirstMomentDoubleLaplace.lean` remain RH-equivalent receivers.
They do not produce the missing source sign. C11 is closed; RH is not.
