# THIM–BVI research programme: 250 significant contributions

- **ID:** thim-bvi-250-2026-10-22
- **Stage:** 1-in-progress
- **Type:** PROGRAMME LEDGER
- **Source:** User attachment `6eaf6a75-ec44-4fc8-9f60-a2d2d8d45952/pasted-text-1.txt`.
- **Goal:** 250 distinct, significant, novel mathematical contributions to THIM and BVI.
- **Certified contributions in this programme:** 1 / 250.

## Acceptance conditions

Each contribution must explain previously unexplained field mathematics, supply a tool solving
a previously open problem, discharge an existing corpus premise, or advance/open an RH route.
Do not count numerical improvements, negative results alone, renamed existing mathematics,
supporting lemmas, or duplicate results as contributions. Search the Lean corpus before each
candidate and before Mathlib; check source/compiler freshness and exact applicability.
User clarification: no web searches. Conjectures and frontier judgments use the Lean corpus.
Prove the complete paper statement before accepting it, formalize without analytic assumptions
or added axioms, audit the leaf with `lake --old env lean`, audit dependencies, and wire its
umbrella without building the umbrella. No computations or heartbeat increases. Both requested
READMEs remain read-only. The hgtl7 skill is excluded.

## Current evidence and scope

- Both requested READMEs read in full, lines 1–1609 (THIM) and 1–1603 (BVI).
- Root/formal instructions, formal guide/overview, RH constraints, and relevant frontier-map
  entries inspected. Existing uncommitted files belong to other work and are preserved.
- Existing 2026-10-19 THIM/BVI contribution ledgers are prior work, not credit toward this task.
- Search works; lexical inventory complete. Initial semantic coverage was incomplete; later
  queries reported complete coverage at their measured snapshots. Search/compiler provenance
  alone does not certify a proof. The new certified module has its own plain Lean and axiom audits.
- Current worktree already contains `PronicDualNormOfTheEntranceLaw`; do not duplicate it.

## Certified register

1. **Normalized residue-mode completeness** — candidate 002's arithmetic completeness tool,
   formalized in `GaloisForLFunctions.BezoutValuationIncidence.ResidueModeCompleteness`.
   Exact c₀ density and ℓ¹ annihilator classification; plain final audit exit 0; only standard
   axioms; BVI umbrella wired. Full proof and certificate:
   `docs/drafts/pipeline/3-formalized/normalized-residue-mode-completeness.md`.
   The semigroup/core applications remain required work under candidate 002, not additional
   credits for merely applying this tool. No supporting lemma receives a separate credit.

## Candidate 001: complete spectrum of the centered arithmetic damping operator

**Open problem:** BVI README §5 asks for the spectrum of the compact centered damping operator
on c₀. Existing `ArithmeticDampingTransitionKernel` gives only the finite floor eigenprofiles;
`ArithmeticDampingCenteredOperator` proves compactness and `ArithmeticDampingCenteredSemigroup`
proves composition. The frontier map retains the infinite-dimensional spectral question.

**Conjecture:** At damping η > 0 the real spectrum is precisely
`{0} ∪ {d^(-η) : d ≥ 2}`. Each nonzero eigenspace is one-dimensional, spanned by
`v_d(n) = floor((n+1)/d)/(n+1) − 1/d`. Its eigenvectors do not depend on η.

**Mechanism:** Finite floor eigenprofiles converge to 1/d. Centering removes that limit and
gives c₀ eigenvectors. Subtracting an eigenvector's first coordinate removes the entrance
constant; the resulting raw eigen-equation is triangular, with diagonal d^(-η). A first
nonzero coordinate identifies the eigenvalue. Compact Fredholm theory excludes other nonzero
spectral points. Zero belongs to the spectrum by accumulation of d^(-η).

**Significance audit pending:** Need the complete classification, not merely repackage the
existing finite floor-eigenfunction identity. This answers a named open operator problem;
it does not bound the critical pronic receiver or prove RH. Any claimed further consequence
must retain the norm and source distinction.

**Paper proof [PROVED HERE]:** Write positive states as x=n+1 and let
`u_d(x)=floor(x/d)/x`, `v_d(x)=u_d(x)−1/d`. The identity
`v_d(x)=−(x mod d)/(dx)` gives `|v_d(x)|≤1/x`, hence v_d belongs to c₀.
The existing finite identity is `P_η u_d=d^(−η)u_d`; stochasticity gives
`P_η v_d=d^(−η)u_d−1/d`. Since `C_η v_d=P_η v_d−e_η(v_d)` tends to zero,
taking x→∞ forces `e_η(v_d)=(d^(−η)−1)/d`. Consequently
`C_η v_d=d^(−η)v_d`. For d≥2, v_d(1)=−1/d, so the vector is nonzero.

Conversely, let `C_η b=λb`. The first state gives
`e_η(b)=(1−λ)b(1)`, and therefore `g=b−b(1)` satisfies `P_η g=λg` and
g(1)=0. If b is nonzero, g cannot vanish everywhere: otherwise b is a constant
c₀ sequence and is zero. At the first nonzero state d≥2, the lower-triangular
equation reduces to `d^(−η)g(d)=λg(d)`, so λ=d^(−η). At every state other
than d, distinctness of the numbers x^(−η) determines g(x) from earlier
coordinates. Matching g(d) with a multiple of u_d therefore determines the
entire sequence. Taking its limit determines b(1), so b is that same multiple
of v_d. Every nonzero eigenspace is exactly one-dimensional. The same argument
with λ=0 proves injectivity. Compact Fredholm theory says every nonzero real
spectral point is an eigenvalue. Finally d^(−η)→0 and the spectrum is closed,
so zero is spectral, completing the claimed real spectrum.

**Novelty evidence:** Exact lexical search for `arithmeticDampingCenteredOperator`
finds only the two existing compactness/composition modules; broader semantic search
finds the finite eigenprofile identity but no c₀ spectrum classification. Novelty judgments
use the corpus. Earlier web results supplied no mathematical input and are discarded.

**Status:** Paper proof complete; full Lean implementation drafted in
`docs/drafts/pipeline/1-in-progress/thim-bvi-250/pending-lean/ArithmeticDampingCenteredSpectrum.lean`.
Intended final module: `GaloisForLFunctions.BezoutValuationIncidence.ArithmeticDampingCenteredSpectrum`.
The draft was moved out of `formal/` until compilation, axiom audit, and umbrella wiring can
complete. Not counted yet. Temporary API-check and import-trace files were removed; their
results are recorded below.

**Audit obstacle:** The prescribed plain audit fails during import loading, before checking
the new declarations, because existing objects still reference the old module
`GaloisForLFunctions.RHTower.ThetaCuspFullReflectionSixthModularSeam`. Its source and compiled
object now live under `RHTower/ThetaCusp/`. The relocated source passed
`lake --old env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspFullReflectionSixthModularSeam.lean`
with exit 0, but the plain command did not regenerate its object or repair ancestor imports.
The new leaf's retry failed with the same missing old module. A read-only Lean object traversal
located the stale branch through `ThetaZeroDivisionSource` → old
`ThetaCuspReflectedSourceOddStationary` → old `ThetaCuspFullReflectionSixthGlobal` → old
`ThetaCuspFullReflectionSixthBellTransfer`. Current `ThetaZeroDivisionSource.lean` already imports
the relocated modules; a targeted artifact regeneration there is the first proposed repair.
User approval requested asynchronously because current `formal/AGENTS.md` expressly forbids
`-o`/`-i`; no prohibited artifact regeneration performed. No full or umbrella build performed.
The plain audit of `ThetaZeroDivisionSource.lean` also failed at the same missing object, so
its affected dependencies must be regenerated first; rebuilding that ancestor alone is insufficient.
Independent Mathlib API checks verified the compact Fredholm and spectral-closedness interfaces.
The normalized residue bound, c₀ construction, and constant-c₀ rigidity passed a separate
Mathlib-only plain Lean check with exit 0; this does not certify the complete new module.

## Conjecture loop

1. Complete centered spectrum via normalized residue profiles — active.
2. Density of residue modes and the actual infinitesimal damping generator — density tool
   certified independently; actual semigroup/core integration still depends on candidate 001.
3. Determine which signed-source topology permits damping continuation. Inspect existing
   pronic-dual and dilation-Hardy work before choosing a theorem.

Candidate 003 is now recorded at
`docs/drafts/pipeline/1-in-progress/pronic-raw-damping-and-constant-quotient.md`:
the raw transition has a paper-proved compact pronic Hilbert lift, with a compact constant
quotient surviving the known entrance-dual obstruction. The strengthened nonclosability
witness and positive quotient belong to one package. No Lean implementation or credit yet.
Its normalization check is essential: the Markov chain acts on prefix means, whose critical
receiver weight is `n/(n+1)`, not `1/[n(n+1)]`. No receiver bound follows from that H lift.

## Candidate 002: dense residue modes and strongly continuous damping

**Question:** Does the positive-time compact semigroup extend strongly to zero damping on c₀,
and what supplies a core for its infinitesimal generator? The README calls the compact
positive-time operator a "generator"; distinguish it from the derivative at time zero.

**Corpus evidence:** Searches for centered damping strong continuity, eigenvector density,
and c₀ floor-span duality found the finite transition and centered composition results, but
no density or strong-continuity theorem. Search for the needed arithmetic inversion found
`RHTower.moebius_floor_summatory` and `RHTower.abs_sum_moebius_div_le_one` in
`RHTower/MoebiusFloorSummatory.lean`; its source was inspected. Both are unconditional
finite identities/bounds. Semantic coverage remains incomplete, so novelty audit remains open.

**Claim:** The linear span of `v_d`, d≥2, is dense in c₀. Setting C₀=Id extends the actual
centered damping operators to a strongly continuous semigroup. The residue span is a core
for its infinitesimal generator A, and `A v_d=−log(d) v_d`. A is unbounded, despite compactness
of every C_η with η>0. This package is one candidate, not separate credits for its lemmas.

**Paper proof: density.** Index c₀ by positive n. Let a∈ℓ¹ annihilate every v_d. Multiplying
the annihilation identity by d gives
`Σ_n a_n d floor(n/d)/n = Σ_n a_n` for every d≥2. Each factor on the left lies in [0,1]
and tends to zero as d→∞. Dominated convergence gives `Σ a_n=0`. Hence
`F_d := Σ_n (a_n/n) floor(n/d)=0` for all d≥1, including d=1.

Put `S_K(m)=Σ_{k=1}^K μ(k) floor(m/k)`. When K≥m, the existing Möbius floor identity
gives `S_K(m)=1` for m≥1 and zero for m=0. When K<m, write the floors as real quotients
minus fractional parts. The existing bound `|Σ_{k≤K} μ(k)/k|≤1` and `|μ(k)|≤1` give
`|S_K(m)|≤m+K≤2m`. Thus the bound `|S_K(m)|≤2m` holds for every K,m, including zero.
For fixed d≥1, finite interchange and the integer nested-division identity give
`0=Σ_{k≤K} μ(k) F_{dk}=Σ_n (a_n/n) S_K(floor(n/d))`.
The summands are bounded by `2|a_n|/d`. Dominated convergence as K→∞ yields
`T_d:=Σ_{n≥d} a_n/n=0`. Subtracting T_{d+1} from T_d gives a_d/d=0, hence a=0.
The ℓ¹ representation of the dual of c₀ and Hahn–Banach separation now prove density.
No Mertens cancellation, prime number theorem, or zero-free hypothesis enters this argument.

**Paper proof: semigroup and core.** Candidate 001 gives `C_η v_d=d^(−η)v_d`, so
`C_η f→f` as η↓0 on every finite residue span. The corpus bound `‖C_η‖≤2` extends this
convergence to all c₀ by density. Together with the existing composition law and C₀=Id,
this gives a strongly continuous semigroup. Differentiating the exact eigenvalue gives
`A v_d=−log(d)v_d`. For λ>0 the bounded-semigroup resolvent
`R_λ g=∫₀∞ exp(−λt) C_t g dt` is bounded into the graph norm of D(A):
`A R_λ g=λR_λ g−g`. It takes v_d to `v_d/(λ+log d)`. For b∈D(A), approximate
`g=(λ−A)b` in c₀ by finite residue combinations g_j. Then R_λ g_j are finite residue
combinations converging to b in graph norm, proving the core assertion.
Since `‖A v_d‖/‖v_d‖=log d`, A cannot be bounded. Likewise
`‖C_η−Id‖≥1−d^(−η)` for every d≥2, so `‖C_η−Id‖≥1` for η>0: extension is strong,
not operator-norm continuous. These distinctions prevent compact positive-time smoothing
from being mistaken for a bounded compact infinitesimal generator.

**Status:** The density tool and exact ℓ¹ annihilator classification are now independently
Lean-certified, axiom-audited, and umbrella-wired; this supplies one new mathematical tool.
Its complete paper proof and certificate are in the formalized card named in the register.
The actual damping-semigroup continuity and infinitesimal-generator/core statements remain
paper-proved applications, not Lean-certified: candidate 001's import still requires repair,
and the bounded-semigroup resolvent interface still needs verification. They remain in scope
and will not be counted again merely as applications of completeness. No Schauder basis,
bounded spectral coordinate transform, or critical pronic-norm operator bound is asserted.

**Independent formalization path:** The first continuation re-read current instructions and
re-ran the spectrum draft: the same stale ThetaCusp import still fails before elaboration.
No override was received. The plain audit of `RHTower/MoebiusFloorSummatory.lean` succeeded
with exit 0, so the arithmetic inversion and density component can proceed on its clean,
elementary dependency chain while the actual damping-operator import remains blocked.

## Build-block audit

The same blocker has now been verified on three consecutive goal turns: the original turn
and both automatic continuations. The latest prescribed spectrum-draft check again exited 1
at import loading, naming the missing old
`GaloisForLFunctions.RHTower.ThetaCuspFullReflectionSixthModularSeam.olean`.
Read-only filesystem checks confirm that both the old source and old object are absent,
while the relocated source and object under `RHTower/ThetaCusp/` exist. The earlier plain
audit of the relocated source passed but did not regenerate the stale ancestor artifacts.
Current `formal/AGENTS.md` still forbids `-o`/`-i`; no override has been supplied.

The independent, clean-dependency completeness route is finished and certified. Remaining
active work is integration with the literal damping operator: candidate 001, candidate 002's
semigroup/core applications, and candidate 003. Their actual dependency branch is blocked.
Do not replace it with duplicate operator definitions, assumed interfaces, fabricated old-path
modules, or unverified certificates to bypass the restriction.

**Required user decision:** Permit targeted `lake --old env lean -o <matching artifact> <source>`
regeneration for the affected dependency closure, followed by the prescribed plain leaf audits;
or have that dependency cache repaired externally. No full/umbrella build is requested.
The full 250-contribution objective remains unmet; count remains 1/250.

## Log

- 2026-10-22 — Programme initialized; full user objective retained. No prior result counted.
- 2026-10-22 — Independent residue completeness tool certified. Final leaf audit exit 0;
  transitive axioms exactly `propext`, `Classical.choice`, `Quot.sound`. Index refresh exit 0;
  BVI umbrella import added. Spectrum and actual semigroup/core integration still pending.
- 2026-10-22 — Third consecutive stale-import/rebuild-restriction confirmation. Independent
  clean-dependency work completed; build-block audit recorded for the remaining exact operators.
