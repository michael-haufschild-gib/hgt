# IRK: charged arithmetic source and projective lift

- **ID:** irk-charged-source-projective-lift-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** read-only IRK entry in `docs/reports/rh-current-frontier-map.md`
- **Statement:** [OPEN CORE] Construct a global arithmetic rotation source realization retaining the actual Xi boundary defect, with a derived integral analytic count.

## Goal

Remove a genuine source-construction obstruction in IRK. An estimate, trace coordinate receiver, or renamed RH equivalence does not qualify. This turn concerns IRK only; earlier thread attempts concerned XN and HF and were not credited as qualifying advances. The full 44-route objective remains open.

## Evidence and plan

1. Inspect current Lean source and search the corpus. No external sources or old research Markdown.
2. State and attack a precise source construction. Preserve the clock correction: the existing untwisting theorem transfers all isolated dipole charge to the removed correction.
3. Write a dependency-closed paper proof before implementing any surviving theorem.
4. Formalize without extra analytic hypotheses, axioms, computations, or heartbeat changes. Check only owned modules, one foreground Lean process at a time.
5. Audit every new public theorem's axioms, wire finished modules, run formal lint, clean owned scratch, and state the remaining gap honestly.

## Current source facts

- `PrimeRotationXiRelativeKTwo`: literal relative K2 source, exact multiplicity boundary, composition correction, and charge loss under untwisting.
- `PrimeRotationCanonicalTraceIntegrality`: integral traces of actual finite prime-Weyl matrix idempotents, without a Xi projective realization.
- `PrimeRotationXiDeterminantSource`: full source jet relation determinant has the actual Xi multiplicity and agrees with Xi in the marked tame quotient.
- `PrimeRotationXiBoundaryHomotopy`: explicit invertible boundary homotopies distinguish the two sides of the critical line; quantum transgression remains separate.
- Broad deep research returned no useful exact hit. Coverage was complete at the source inventory level, but compiler metadata was mostly pending/stale; no suggested lemma is accepted without inspecting source and checking Lean.

## Gates

- [x] Source-pure problem selected; frontier map untouched.
- [ ] Dependency-closed paper proof of a new obstacle-removing theorem.
- [ ] Formalized and audited.
- [ ] Meets user's significant-frontier-contribution criterion.

## Attack: literal completion of the arithmetic resolution

**C1 [CONDITIONAL OBSTRUCTION]:** At any hypothetical off-line Xi zero, completing the displayed finite free resolution in the closed rotation algebra does not preserve its source quotient. The scalar resolvent facts imply contraction, even with the entire Jordan block retained. This does not assert that off-line Xi zeros exist, and does not falsify IRK itself.

**Positive survivor [PAPER PROOF]:** For each actual Xi zero rho and each positive native prime clock, the literal completed relation matrix is invertible exactly when `rho.re != 1/2`. Off the line it has an explicit finite nilpotent-series inverse inside the closed rotation algebra. Its logarithmic matrix trace is full analytic multiplicity on the right and zero on the left. Thus the analytic contraction and the surviving boundary trace are distinct, concrete objects; the surviving charge cannot be the ordinary completed cokernel.

### Dependency-closed proof

Write `V` for native modulation, `m` for actual Xi multiplicity, `T` for the complete centered prime flow matrix, and `lambda = exp(-log(p)(rho-1/2))`. The literal relation on row vectors is the upper triangular matrix `B = V I - T.transpose`, with every diagonal entry `a = V-lambda`. These are actual matrix coefficients, not declared spectral data.

1. If `Re rho != 1/2`, the already constructed geometric inverses give `r a = a r = 1` in the closed rotation algebra: inside the unit circle on the right, outside on the left. Put `D=diag(a)`, `R=diag(r)`, and `N=1-R B`. `N` is strictly upper triangular.
2. Over any ring, a strictly upper triangular m-by-m matrix has `N^m=0`. More precisely `(N^k) i j=0` whenever `j<i+k`, by induction on k in the matrix multiplication formula. Hence `S=sum_{k<m} N^k` satisfies `S(1-N)=(1-N)S=1`. The explicit inverse `E=S R` satisfies `E B=B E=1`, using `B=D(1-N)`. No small-norm assumption on the nilpotent jet block is needed.
3. The same support proof gives `S i i=1`, so `E i i=r`. Therefore the canonical matrix trace of `diag(V) E` is `m*tau(Vr)`. The existing scalar geometric trace theorem gives m on the right and zero on the left. This derives the trace from the full inverse.
4. On the critical line `|lambda|=1`. The prime frequency divided by `2*pi` is the negative of the already proved irrational prime rotation parameter. The integer multiples are dense on `AddCircle (2*pi)` and hence their exponentials are dense on the unit circle. Modulation acts on coordinate vectors by these phases.
5. If `C a=1`, applying this identity to a unit coordinate vector gives `1 <= ||C||*|phase-lambda|`. Density contradicts this inequality. Thus `a` has no bounded left inverse. The first column of the upper triangular `B` has only entry `a`; a left inverse of B would provide a bounded left inverse of a from its (0,0) entry. Since m is positive at every actual Xi zero, B cannot be invertible.
6. Before completion, the existing exact free resolution and surjection onto the literal nonzero singleton clock packet prove that its relation is not surjective. After completion, row multiplication by the explicit inverse proves bijectivity off the line. Thus the loss of the original quotient is proved from source exactness, rather than inferred from a determinant.

**Scope audit:** This is an exact completion/charge classification, not the requested global charged projective lift. IRK stays open; do not count this as satisfying the user's frontier criterion without an additional construction that retains the arithmetic source and supplies the required projective charge.

## No-go closure for direct completion

- **Mechanism:** At any off-line source point, the actual relation matrix becomes a unit inside the closed rotation algebra, while its polynomial-source cokernel is nonzero. No existence of such a zero is asserted.
- **Positive survivor:** Explicit full-Jordan inverse, exact critical-line invertibility boundary, and equality of its logarithmic canonical trace with the literal source boundary winding.
- **New insight:** The surviving integer is a boundary trace of a contracting complex. It cannot be identified with the ordinary completed cokernel's projective trace.
- **Next open construction:** Retain the global Poisson complex and its clock correction in a relative construction before passing to a finite spectral quotient. A source-derived projective representative and its analytic trace still have to be constructed; neither is supplied as a premise.

## Verified partial result

- Module: `formal/GaloisForLFunctions/RHTower/PrimeRotationXiCompletedResolution.lean`.
- Exact boundary: `deningerMeyerXiCompletedRelation_isUnit_iff`.
- Constructed two-sided inverse: `deningerMeyerXiCompletedRelationInverse_mul` and `deningerMeyerXiCompletedRelationMatrix_mul_inverse`.
- Literal source comparison: `deningerMeyerXiCompletedRelationMatrix_source`.
- Source nonzero before completion: `deningerMeyerXiClockRelation_not_surjective`; completed bijectivity: `deningerMeyerXiCompletedRelation_bijective`.
- Retained trace: `deningerMeyerXiCompletedLogarithmicTrace_eq_boundary`.
- Final module check: `lake --old env lean -j 1 -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/PrimeRotationXiCompletedResolution.olean GaloisForLFunctions/RHTower/PrimeRotationXiCompletedResolution.lean`, exit 0, no warnings.
- Separate `/tmp` axiom audit: all eleven public theorems depend only on `propext`, `Classical.choice`, `Quot.sound`; exit 0.
- Wired in `RHTower.lean`; `scripts/formal_tools.py index` exited 0. Full umbrella build not run.
- Global `scripts/formal_tools.py lint --check-generated` exited 1: seventeen other modules were unreachable from their umbrellas (Archimedean anomaly, CHMD/BV, and prime graph-clock work). No error named this module; no generated-file staleness error appeared. Those concurrent work scopes were not modified.
- Scoped whitespace checks passed. The frontier map was not edited by this task; its hash changed during concurrent work, so no unchanged-worktree claim is made.
- No new axioms, admitted declarations, numerical experiments, or heartbeat changes.
- All owned scratch files removed after all owned handles terminated; no owned jobs remain.
- **Goal credit: none.** The missing global projective lift remains open; this exact completion theorem is a verified partial result.

### Late source lead

The current `PrimePositiveClockRealization` and `MobiusDivisorPrimeGraphClockRealization` source supplies Banach/graph-norm synthesis by actual primes. Its statements do not construct a rotation-algebra action, equivariant projective representative, or Chern comparison. These concurrent unfinished modules are not dependencies of the new theorem and were not treated as a solution to the missing IRK lift.

## Log

- 2026-10-17 — IRK selected. No claim that existing local boundary identities construct the missing global projective lift.
