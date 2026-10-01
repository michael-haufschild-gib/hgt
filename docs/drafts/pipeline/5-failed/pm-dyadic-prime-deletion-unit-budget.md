# Prime-two deletion tests the all-subset unit budget

- **ID:** pm-dyadic-prime-deletion-unit-budget
- **Stage:** 5-failed
- **Type:** CLOSED no-go with a formalized exact resolvent survivor
- **Source:** Route PM, PM-31, after the Hilbert-tangent investigation.
- **Statement tested:** Some positive damping neighborhood has canonical norm at most one for every finite prime subset.
- **Status:** Unconditional obstruction and positive survivor fully formalized and audited.

## Paper construction

Let `O_ε` be the literal Fermi sum with the even Möbius coefficients deleted.
At ε=0 the identity `μ(2n)=−μ(n)` for odd n, and zero for even n, gives

`O₀(t)−O₀(2t)=A₀(t)=H₀(t)` for t>0,

where `H₀` is Haar supported on `(0,1]`. Since every physical source vanishes
above one, iteration stops after finitely many steps at each t>0:

`O₀(t)=B(t):=Σ_{k≥0} H₀(2^k t)`.

Each Haar summand has canonical squared norm `2^(−k)`. Distinct summands
are orthogonal: the coarser Haar is constant on the finer one's support,
and the finer Haar has zero mean. Their norms are summable, so B is a
canonical L² source, with zero mean and exact squared norm

`||B||₂²=Σ_{k≥0}2^(−k)=2`.

Equivalently, the admitted self-similarity equation `B=H₀+B(2·)` gives
`||B||₂²=1+||B||₂²/2`, because the mixed term is zero. This gives a
second derivation of the same exact energy, with no numerical experiment.

The odd-prime apertures `(primes through N)\{2}` recover the odd Möbius
coefficients at every fixed physical cutoff, so their finite sources converge
pointwise to O₀. A proposed common unit norm budget at every sufficiently
small positive ε first passes to ε=0 for each finite prime subset by Fatou,
then to O₀ by Fatou again. It would imply `||B||₂≤1`, contradicting the
exact energy two. More generally, every such all-subset norm budget must
be at least `sqrt 2`.

## Positive survivor and scope

The survivor is the exact physical prime-two-deleted source, its canonical
admission, zero mean, orthogonal Haar expansion and exact energy. It solves
the dyadic resolvent equation. The stronger pointwise uniqueness needs only the difference equation and
support: iteration reaches the zero region after finitely many steps.

This excludes an all-subset unit ceiling only. Canonical full prime
apertures contain two once the cutoff reaches it, so neither a canonical
unit ceiling nor admission of the complete source is excluded. A larger
all-subset budget remains a possible RH producer.

## Existing evidence and remaining gates

- Queries 1036 and 1037: all returned candidate/source statements and chains
  reviewed, with no exact PM deleted-dyadic theorem among the hits. Coverage
  and freshness are recorded on the main PM-31 card.
- `PMPowerDampedMobiusPrimeGrowth` gives literal finite prime sources and
  budget transfer. `MobiusFinitePrimeApertureSourceConsumption` defines exact
  prime-factor coverage.
- `RHTower.moebius_two_mul` in `MertensOddWindowKnapsack` supplies the arithmetic
  splitting identity. `Sieve.CoprimeMoebiusSeries` uses the same deletion
  reindexing for its inverse-square Dirichlet series, not the physical norm.
- Completed: exact odd-source recurrence; supported Haar resolvent admission
  and energy; finite odd-prime stabilization; parameter Fatou; actual finite
  source exceedance; full Lean artifact and standard-axiom audits.

## Log

- 2026-10-01 — Candidate recorded from the actual PM coefficient and Haar
  definitions after corpus search. No numerical experiments or added premises.

- Prepared `/tmp/pm_dyadic_resolvent_1038.lean`: initial eleven-declaration
  supported-Haar package (measurability, squared-norm indicator, canonical
  admission, energy one, mean zero, and dyadic dilation terms with exact
  energies and means). It is not yet run; 1034 final audits take precedence
  under the one-compiler rule. No resolvent or odd-coefficient bridge claimed.

- Initial twenty-declaration resolvent scratch passed empty: supported-Haar
  admission/energy/mean, exact geometric L² norms of dyadic terms, their
  pointwise summability, finite-prefix norm bound and Fatou admission of the
  actual infinite sum. Added seven declarations for support, the exact
  self-similarity equation, canonical L¹ integrability, zero mean and exact
  energy two. Full 27-declaration scratch is checking.
- A shorter positive proof emerged: after canonical L² admission, compact
  carrier gives L¹. Integrating `B=H₀+B(2·)` forces the mean to zero; because
  H₀ is -1 throughout the support of B(2·), the mixed energy term integrates
  to zero. The same identity then forces `E=1+E/2`, hence E=2. No infinite
  energy or integral interchange is needed in this final exact-energy step.
  Arithmetic odd-Möbius source identification still remains.

- The exact-energy assembly exposed only interface issues (sum-zero name,
  explicit IntegrableOn annotations, dyadic shift rewriting and complex-real
  integral conversion); corrected these. Full 27-declaration scratch is
  checking again. Prepared a stronger uniqueness survivor: support above one
  plus `f(t)=H₀(t)+f(2t)` uniquely determines f on the positive ray, with no
  norm premise. Paper proof: iterate the homogeneous difference until `2^k t>1`,
  where both sources vanish. Its separate tail scratch has not yet been joined
  or compiled. The arithmetic identification can then use this exact uniqueness
  theorem rather than an infinite Möbius/series interchange.

- Full 29-declaration resolvent scratch passed empty, including exact energy
  two, canonical norm sqrt 2 and the stronger pointwise uniqueness statement.
  Promoted/wired `PMPowerDampedMobiusDyadicResolvent` (299 lines / 29
  declarations); targeted build and full audits pending. Prepared unrun
  `/tmp/pm_dyadic_deletion_1039.lean`: twelve declarations for the literal
  odd-Möbius finite prefix, exact even/odd split, reciprocal cutoff identity,
  dyadic recurrence, identification with the admitted resolvent, exact norm
  and mean. Finite odd-prime stabilization and norm-budget transfer remain.

- Resolvent leaf targeted old build passed (18 seconds); final actual leaf
  passed empty. All 29 exact bodies, exhaustive unique names, API entries and
  unique umbrella import passed. Standard-axiom reports are checking. Latest
  lint: twelve unrelated unwired modules plus concurrent LEAN_API staleness;
  no owned or proof-debt finding. Prospective combined PM-31 totals after this
  audit: fifteen leaves / 3595 lines / 226 declarations.

- Dyadic resolvent ingredient fully audited: `PMPowerDampedMobiusDyadicResolvent`
  (299 lines / 29 declarations), targeted old build 18s, final actual leaf empty,
  all standard-axiom/body/name/API/unique-import gates passed. Exact canonical
  energy 2, mean 0, norm sqrt 2 and pointwise support/recurrence uniqueness are
  certified. Combined PM-31: fifteen leaves / 3595 lines / 226 declarations.
  Odd-Möbius identification and all-subset budget obstruction remain pending;
  no closure of the prime-deletion no-go yet. Small-positive L² admission and
  RH remain open. Latest lint: twelve unrelated unwired modules and concurrent
  LEAN_API staleness; no owned or proof-debt finding.

- First twelve-declaration arithmetic check found two rewrite issues:
  repeated uninstantiated dilation rewrote the same side twice, and broad
  simp normalized `1/t` before its floor equation. Corrected with explicit
  dilation arguments and a prior floor rewrite. Other initial statements
  elaborated. Joined fourteen declarations for odd-prime coefficient coverage,
  exact finite-source stabilization, parameter continuity, two Fatou transfers
  and actual finite-subset norm exceedance of every budget below sqrt 2.
  Full 26-declaration scratch 1039 is checking; the unit-budget no-go remains
  open until its actual capstones and artifact gates pass.

- Full 26-declaration arithmetic/budget scratch passed. Removed its single
  unnecessary-simpa warning and promoted/wired `PMPowerDampedMobiusDyadicDeletion`.
  Actual finite sources exceed every budget below sqrt 2 arbitrarily near zero.
  Targeted build, actual-leaf and exhaustive artifact audits remain pending.
- Search 1040 (`prime deleted Haar resolvent norm`): reviewed all 20 candidate
  and 20 source-argument statements; no generated ingredient chains or proof
  ideas. The exact dyadic resolvent hits are our prior leaf; other hits concern
  distinct Sonin/Deninger/operator carriers. No general prime-deletion physical
  norm theorem returned. Partial=false; 63804 files, generation 1172249,
  coverage snapshot 1172245/current 1172249. Semantic coverage unmeasured
  (reporting budget), background refresh incomplete. This is a bounded search,
  not an exhaustive novelty claim.

- Closure: `PMPowerDampedMobiusDyadicDeletion` (257 lines / 26 declarations)
  passed targeted old build (7.3s), final actual leaf (empty), all 26 exact
  bodies, unique names, public API entries, unique umbrella import, and
  standard-axiom reports (`propext`, `Classical.choice`, `Quot.sound` only).
  Together with the already audited 299-line / 29-declaration resolvent leaf,
  this proves the literal odd-Mobius source has energy 2, mean 0 and norm
  sqrt 2. Every all-subset near-zero budget is at least sqrt 2; every smaller
  budget is exceeded by an admitted actual finite prime source arbitrarily
  near zero. The unit-budget route is retired with this exact positive survivor.
  PM-31 totals: sixteen leaves / 3852 lines / 252 audited declarations.
- Global lint reports twelve unrelated unwired modules; no owned proof-debt,
  generated-API or wiring issue in this leaf. Canonical complete-source
  admission and RH remain open. The larger all-subset budget conjecture now
  has its own paper argument on `pm-finite-prime-deletion-energy`.
