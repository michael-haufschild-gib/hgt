# Contribution 010: faithful full-Jordan source Fredholm realization

Status: completed; **10/100** contributions audited. Baseline for this turn was
9/100: contribution 009 had removed native differentiated-mode admission and
constructed full confluent theta currents. This turn closes the actual-source
Fredholm realization; all seven leaves, 61 axiom checks, and global lint pass.

Objective remains 100 distinct structural advances, one per goal turn.
Routine consequences, estimates, receivers and RH equivalences do not count.
No web, external novelty check, old reports, numerical experiments, subagents,
commits, full builds or umbrella builds. Main constructions unconditional;
one foreground Lean process at a time; no added axioms or heartbeat increases.

Plan:
1. Recheck current map and multiple independent Lean-source obstacles with the
   documented research search. Do not assume 009's adjacent corollaries qualify.
2. Conjecture, test the exact source requirements, and record failures/positive
   survivors. Require a dependency-closed paper proof before mathematical code.
3. Formalize a substantial survivor, audit leaves and axioms, wire umbrellas,
   run formal lint, clean scratch, then update the contribution ledger.

Initial investigations, not claims:
- Literal Euler inversion: source periodization is split, but periodization
  surjectivity on actual Poisson boundaries remains unpaid. Pointwise inverse
  on Xi jets is insufficient. Inspect the exact boundary source before choosing
  a scalar interpolation or Fourier multiplier construction.
- Actual full-Jordan generator: the diagonal closed operator already exists;
  a bounded nilpotent shift alone is too routine. A source-faithful closed
  realization with a genuine resolvent/trace calculus could be substantial.
- Recheck independent prime/source trace routes and current source constraints;
  do not count positivity or signed work that remains an unproved premise.

## Selected conjecture: faithful full-Jordan source Fredholmization

Euler candidate remains unproved: Floquet boundary completeness is a Hilbert
closure result on sampled critical-line nodes; the Big-Witt strict Green
descent concerns finite prime seams. Neither provides the required smooth
periodization surjectivity on the literal Poisson boundary. No inversion claim.

The selected target combines HF's global Xi synthesis, original-source Hasse
admission and finite causal solvability, RN's unconditional endpoint Xi gap,
and TG's nonnormal Hilbert–Carleman determinant calculus. A bare diagonal
model or bounded perturbation alone will not be counted.

Target: the **closure of the actual centered Meyer generator** on the faithful
dense unweighted Hasse Hilbert realization has a compact Hilbert–Schmidt
inverse, retaining every original Jordan chain. Its entire regularized
determinant is exactly `XiC(z)/XiC(0)` on the whole complex plane.

### Dependency-closed paper proof

Write `i(u)_(rho,j)=M_u^(j)(rho)/j!`, `mu_rho=-I*(rho-1/2)`.
The existing generator identity gives
`i(G u)_(rho,j)=mu_rho*i(u)_(rho,j)-I*i(u)_(rho,j-1)` for
`G=-I*(Theta-1/2)`; the last term is zero at j=0.

1. Let N be the backward-coordinate shift in each finite Hasse block,
   zero at its initial slot. It is a coordinate permutation followed by an
   orthogonal mask, hence a contraction even with unbounded multiplicities.
2. Let D=diag(mu^-1). The endpoint source theorem gives |mu|>4, and the
   canonical full-multiplicity reciprocal-square sum is finite. Thus D is
   Hilbert–Schmidt and ||D||<=1/4. T=I*D*N is a strict contraction.
3. U=1-T is invertible. Define K=U^-1*D. This is Hilbert–Schmidt and compact;
   its coordinate equation is `mu*(K y)-I*N(K y)=y`. K is injective since D
   is injective. The source identity gives `K i(G u)=i(u)`.
4. The existing off-divisor causal division solves G v=u on the literal
   source. Hence `K i(u)=i(v)` with a unique v, by faithful admission.
   K therefore extends the actual source inverse, with no source-admission
   premise on its data. Its range is dense since it contains i(source).
5. Define the closed generator as the inverse linear partial map of K.
   Its graph is {(K y,y): y in Hilbert}, closed because K is continuous.
   Dense original source data y=i(u), with the exact v from step4, give
   graph density. Consequently this operator is precisely the graph closure
   of the original generator, not merely an extension or divisor proxy.
   Its maximal domain is exactly the square-summability domain of the
   displayed full Jordan expression.
6. The recurrence from step3, by induction on j, makes the matrix of K
   strictly lower graded triangular away from its diagonal mu^-1: every
   off-diagonal nonzero entry increases Hasse degree. In a closed path all
   degree increases must vanish. Thus every diagonal entry of every power
   is mu^(-n), retaining one entry for each multiplicity slot.
7. The trace series defining det2 therefore equals that of D. Their entire
   continuations agree. The diagonal product theorem and the unconditional
   Xi Hadamard normalization identify det2(D) with XiC(z)/XiC(0).

This supplies genuine source-defined compact resolvent and exact determinant
calculus without semisimplifying repeated zeros or changing source topology.
It opens nonnormal Fredholm/trace/finite-section methods on the actual Meyer
generator. Positive Hodge compatibility, self-adjointness, and RH remain open.

Paper status: dependency-closed. Lean status: formalized and audited.

Lean progress:
- `DeningerHasseHilbertShift`: direct leaf audit passed.
- `DeningerMeyerHasseResolvent`: direct leaf audit passed, including exact
  original-source inverse, injectivity, dense range, and Hilbert–Schmidt compactness.
- `DeningerMeyerClosedHasseGenerator`: direct leaf audit passed, including
  maximal full-Jordan domain and exact original-source graph closure.
- `HTGeometry.GradedTriangularRegularizedDeterminant`: direct leaf audit passed.
- `DeningerHasseResolventTriangular`: direct leaf audit passed, including full
  diagonal power laws without bounded multiplicity.
- `DeningerMeyerFredholmXi`: direct leaf audit passed, including the entire
  normalized Xi determinant and full algebraic multiplicity of the actual inverse.
- `PaperThetaMeyerFredholmMultiplicity`: direct leaf audit passed. The actual
  source resolvent's generalized spectral rank is exactly RN's number of
  lower admitted AC parameter orders; its rank-order mode is discontinuous
  at every interior cut. This is part of contribution 010, not a separate count.

Lean implementation corrections were type/coercion issues, not missing math:
finite-fibre permutation equality needed an explicit dependent constructor;
`lp.single` rewrites needed the explicit constant complex fibre; overloaded
`hsComp`/`hsPow` lemma names were changed to avoid namespace shadowing.
No mathematical premise or heartbeat increase was introduced.

## Final audit and frontier delta

- Seven final direct leaf audits passed with `lake --old env lean -o ... file`.
  No full or umbrella builds were run.
- All 61 public declarations passed `/tmp` `#print axioms` audit; every list
  is exactly `[propext, Classical.choice, Quot.sound]`.
- All 25 selected mathlib API checks passed in a separate `/tmp` Lean file.
  An initial API harness used unconstrained universe-polymorphic `have`
  declarations; using polymorphic examples fixed the harness without changing
  any mathematical code.
- Every leaf has exactly one appropriate umbrella import. All seven compiled
  artifacts are newer than their sources. No holes, added axioms, unsafe/opaque
  declarations, heartbeat overrides, or numerical research computations.
- `scripts/formal_tools.py lint` passed. Its warnings concern existing large
  files; this contribution's leaves have 49–171 lines. The previous turn's
  six unrelated umbrella omissions no longer occur in the current global lint.
- All ten owned `/tmp/hgt_rh010*` files removed; no owned scratch remains.
  All owned build/search sessions finished. No commits or pushes.

The obstacle removed is the gap between an artificial diagonal divisor model
and the genuine source generator's closed Fredholm calculus. The inverse is
proved to extend original-source causal inversion; graph-core equality then
identifies the unbounded operator itself. Its determinant is the entire
Hilbert–Carleman function, rather than the nowhere-zero local exponential.
The proof retains all multiplicities, even without a uniform multiplicity bound.

This enables compact-resolvent, nonnormal determinant, generalized-eigenspace,
and finite-section methods on the actual generator in its canonical Hasse
completion. Its spectral rank also determines the native RN gluing threshold.
It does not prove self-adjointness, positive Hodge compatibility, original-
Fréchet finite-packet density, unrestricted Hilbert packet admission, arithmetic
cup/trace cancellation, or RH. All routine consequences of this realization
belong to 010. Continue conjecturing toward a distinct structural obstruction;
literal Euler inversion remains an unpaid candidate, not a result.

Completed count after cleanup: **10/100**.
