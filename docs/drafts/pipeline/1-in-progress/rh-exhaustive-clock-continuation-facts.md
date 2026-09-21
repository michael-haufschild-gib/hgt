# Exhaustive clock continuation

Owner: critical-clock product task. RH and paid exhaustive continuation remain open.

## Frozen target

Construct nested prime cores exhausting every prime, with cumulative source
payments controlling all intervening original cutoffs and their complete
processing under one critical-action bound. Sparse bounded checkpoints alone
do not satisfy this target.

## Source facts and obstruction checks

- The preceding growing-depth payment uses a fixed seed, excludes prime 2,
  and only pays prescribed primes above a moving logarithmic threshold.
  Its quantified conclusion does not admit direct exhaustive iteration.
- `exists_mobiusDivisorSmallTerminalCore` processes all primes outside two
  macroscopic signed windows and has a square-root head. Taking its clock
  beyond an inherited finite core can include every old prime.
- `mobiusDivisorSuccessorEnvelope_le_terminal_density` controls the terminal
  square sum by `M * primeCounting M`, uniformly over the inherited core.
  PNT absorbs the additional logarithmic clock weight into a uniform
  quadratic endpoint bound, now proved in the source construction below.
- `MobiusDivisorWeightedTerminalHeadBarrier` already excludes completing all
  these small-head endpoints by fixed-positive-weight monotone insertions.
  That obstruction does not exclude nonmonotone bounded completion.

## Closed source construction [BRIDGE]

Module: `MobiusDivisorExhaustiveClockCheckpoints`.

- `eventually_exists_mobiusDivisorTerminalClockBudget`: there is b>=8 such
  that, eventually for every N, at `M=28*(b+1)*N` an actual prime core P
  contains every prime at most `4*b*N`, is contained in the active primes
  below M, and has `W(P,M)<=200*M^2`. Every original integer cutoff
  `M<=L<=M+M^(1/4)` has `W(P,L)<=201*L^2`. No source availability, initial
  energy, or sign premise is assumed.
- `exists_mobiusDivisorExhaustiveClockCheckpoints`: closed existence of
  strictly increasing clocks and nested actual prime cores with
  `M_(n+1)=8*M_n`, `P_n subset SelectionPrimes(M_n)`, and
  `SelectionPrimes(M_n) subset P_(n+1)`. Every prime is eventually permanently
  processed. The constants 200 and 201 hold uniformly for all stages at
  their checkpoints and collars, independently of growing core cardinality.

## Dependency-closed paper proof

1. Exact squarefree energy shows `W(P,M)<=(1+log M)*E(P,M)`.
2. For a terminal core with head at most `5*sqrt M` and residual quotients
   at most 7, the existing literal density law gives
   `E(P,M)<=((46/5)^2+(441/25)*pi(M))*M`.
3. PNT gives `(1+log M)*pi(M)<=4*M` eventually. Also `1+log M<=M` for M>=1.
   Hence `W(P,M)<=(3880/25)*M^2<=200*M^2`. This avoids exponential
   cardinality constants entirely for the constructed terminal cores.
   The core producer is used only at fixed epsilon=1; no invalid substitution
   of a moving epsilon into its eventual threshold is made.
4. The actual terminal-core producer leaves omissions only in its two signed
   windows, both above `4*b*N`. It therefore includes every prime below that
   boundary. Core-uniform cutoff transport spends one additional `M^2` on
   the fourth-root collar, yielding `201*L^2`.
5. Beyond the common threshold T, choose `N_n=(T+1)*8^n`. Since b>=8,
   the lower processed boundary at stage n+1 exceeds M_n. Any witnesses
   selected at these clocks are therefore nested and capture the entire
   previous active prime set. Strict clock growth gives prime exhaustion.

## Whole-route consequence

Prime exhaustion, nesting, and a core-uniform full weighted bound at
geometric checkpoints are now simultaneously produced. Small primes,
including 2, are eventually included. This is stronger than the former
independently chosen fixed-seed extensions. Inclusion is not a proved payment
at the old clock. Cumulative paid continuation and RH remain open.

## Unproved implications that must not be asserted

The checkpoint estimate concerns `W(P_n,M_n)`. Original-wall completion
requires control of `W(P_(n+1),M_n)` once the next core includes all primes
active at M_n. The attempted induction supplies no comparison between these
two quantities. Advancing the clock in an exhaustion argument therefore
leaves a missing estimate at the old wall. Fourth-root collars do not cover
the factor-eight gaps of the proposed checkpoint sequence. The attempted
diagonal selection has not supplied that estimate or a cumulative payment law.

The next mathematical obligation is source control of old-wall completion
and inter-checkpoint motion. Producing more independently bounded endpoints
will not establish that missing estimate.

## Audit facts

- `lake env lean /tmp/hgt-exhaustive-checkpoints.lean` passed without warnings.
  Both public theorem axiom audits contain only `propext`, `Classical.choice`,
  and `Quot.sound`.
- The leaf is wired into `RHTower.lean`. Final named audit
  `lake build GaloisForLFunctions.RHTower.MobiusDivisorExhaustiveClockCheckpoints`
  passed without new-leaf warnings. Existing dependency warnings were replayed;
  no full or umbrella build was run.
- Corpus index refreshed successfully. Repository lint returned four unrelated
  pre-existing umbrella reachability errors: `ThetaCuspHawkingBMLiteralCyclicPeierlsLowerWeylRadialDetector`,
  `ThetaCuspHawkingBMLiteralCyclicPeierlsSelfInverseSquarePhysical`,
  `ThetaCuspHawkingBMLiteralCyclicPeierlsSelfMixedCuspFlux`, and
  `XiHeatCassiniWoldJointDepthMöbiusSourceTransport`. No error concerns this leaf.
- All owned Lean, build, search, index, and lint processes exited. Scratch
  proof/name-probe files were removed after their verified proof was promoted;
  audit logs remain under `/tmp/hgt-exhaustive-checkpoints*`.
- Full-corpus deep search completed; the focused terminal/weighted search
  returned partial results. Candidate lemmas, source methods and their actual
  quantifiers were checked against source. No search result discharged an
  assumed source estimate.
- Broad 2026 searches on reservoir and dissipation led to
  [Beuria--Shukla](https://arxiv.org/abs/2608.04028). Its freely designed decay
  spectrum supplies no law for the fixed arithmetic source; no result from
  that paper is used.
