# EDQ exact compensation and unique finite-energy counterterm

Stage: 3-formalized. [BRIDGE], derived from existing exact identities; not a new primary conjecture.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.
Objective: identify the complete signed cancellation field and classify which scalar corrections retain finite full weighted energy.

## Frozen derived statements and paper proof

Write H_N=sum_(m<=N) mu(m)/m, M(k)=sum_(m<=k) mu(m),
R_N(n)=sum_(j<=floor(n/(N+1)))(M(floor(n/j))-M(N)), and
e_N(n)=1-F_N(n)=n H_N+R_N(n), for n>=1.

For N>=1 the Mertens-increment series
T_N=sum_(k>=N)(M(k)-M(N))/(k(k+1)) is absolutely convergent.
The existing absolutely convergent Mertens series and telescoping positive
kernel give T_N=-H_N. Therefore e_N(n) is exactly the quotient sampling
of the increment field minus n times its entire mass. This retains the
counterterm and the infinite tail in one signed discrepancy.

For every cutoff N and real c, define the corrected coordinate
q_(N,c)(n)=n c+R_N(n). Since |e_N(n)|<=N+1,
q_(N,c)(n)/n tends to c-H_N. Consequently its weighted square
q_(N,c)(n)^2/(n(n+1)) tends to (c-H_N)^2. A summable sequence tends to zero,
so finite weighted energy forces c=H_N. Conversely c=H_N gives the actual
bounded error, whose weighted squares are summable. This is a complete
classification, including N=0; it does not assert H_N is nonzero.

## Corpus and novelty audit

The basis is EulerDeletionQuotientHarmonicBound, the exact harmonic tail
identity in Sieve/MoebiusHarmonicTailIdentity, and bounded-error/step-Gram
summability in BaezDuarteMobiusPrefixApproximation. Searches for Möbius
compensation, finite-energy uniqueness, scalar summability, and exact
counterterm uniqueness found no statement of this classification. Related
CCM quadrature and signed Mertens-gradient identities concern other sources
or retain unproved variation/moment bounds; they do not give EDQ's missing
absolute ceiling. This is a corpus bridge, with no claim of external novelty.

## Boundary and positive survivor

Globally tuning a free linear counterterm is excluded: every incorrect
coefficient destroys finite weighted energy, even at one fixed cutoff.
The positive survivor is the exact, unique compensator and its absolutely
convergent increment-mass representation. The actual compensated field still
needs a cofinal polynomial-log energy/current ceiling. This result does not
prove that ceiling, falsify RH, or retire EDQ.

The statements follow by visible deductions. No numerical experiment is
justified, and no numerical evidence enters Lean.

## Lean and validation

`EulerDeletionCountertermRigidity.lean`, namespace `RHTower.DeletionCounterterm`,
contains nine public theorems and two definitions. The mass, exact quotient
compensation, asymptotic linear coefficient, limiting energy summand, actual
full energy, and complete summability classification are all proved without
an arithmetic premise. The uncompensated quotient field has finite energy
exactly when H_N=0; no unsupported nonvanishing of H_N is asserted.

The scratch proof passed `lake env lean` with no diagnostics. Final targeted
`lake build --old GaloisForLFunctions.RHTower.EulerDeletionCountertermRigidity`
built only this new leaf in 4.9 seconds; all dependencies were cached. All eleven
new public declarations were audited once through a temporary `lake env lean`
file and depend exactly on `propext`, `Classical.choice`, and `Quot.sound`.
The module is wired into `RHTower.lean`. No full or umbrella build, added axiom,
admission, numerical certificate, or numerical experiment was used.

Scoped source, whitespace, unique umbrella wiring, audit coverage, documentation
links, and stage checks passed. The search index was refreshed once. Repository
formal lint found only four concurrent unrelated unwired modules:
`CCMRestrictedWeilPolarBombieriYoshidaQuantitative`,
`FiniteDirichletMellinContinuationObstruction`, `RetainedPrimeLandauCarrier`,
and `RetainedPrimeLandauSeparation`. No lint error concerned this leaf.
All owned Lean processes exited, and the temporary proof, API, and axiom files
were removed. Validation logs remain under `/tmp/edq_counterterm.*.log`.
