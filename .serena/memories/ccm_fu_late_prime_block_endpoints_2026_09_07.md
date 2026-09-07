# CCM-FU: actual late-prime blocks have exact endpoint control

## Goal/current boundary
RH goal ACTIVE, not solved. Full chain: completed Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → coherent prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH.
Previous turn closed PE5 independent-average refutation and actual normalized deformed mean unbounded on every tail; do not reopen or re-audit it. See mem:ccm_fu_half_selection_growth_obstruction_2026_09_07.
Current turn made POSITIVE progress for surviving PE4 via an exact actual-source block law. PE4, PE4G, SD1 and RH remain open. No arbitrary endpoint inequality is used as an RH producer.

## Source discovery
For p prime, p<M and M≤2p, the only active squarefree label below M containing p is p itself. Its retained fibre is singleton {p}, as long as p is unprocessed. Source coefficient C_p≤0 by existing unsigned positivity. Other nonempty fibres remain fixed. Write h_P = mobiusDivisorSelectionFibre M P ∅ and Q_P = mobiusDivisorSelectionEnergy M P.
Exact source updates: h_(insert p P)=h_P+C_p; Q_(insert p P)-Q_P=2*h_P*C_p.
Thus isolated late-prime processing is a scalar same-sign block. Head decreases. Energy contracts when the head before each step is nonnegative; it increases after the head becomes negative. For every intermediate subset R of an unprocessed late-prime set L, Q_(P∪R)≤max(Q_P,Q_(P∪L)). Therefore a ceiling controls every intermediate subset iff it controls the two endpoints. This holds for every ordering and every actual processed base P disjoint from L.

## New formal leaves, root namespace RHTower
`MobiusDivisorLatePrimeFibres.lean` (125 lines,5 public theorems):
- mobiusDivisorSelectionFibre_late_prime hp hpM hM P R hpP hpR: if p∈R then actual fibre equals if R={p} then C_p else0.
- mobiusDivisorDilationChannel_late_prime_nonpos hp M: C_p≤0, in fact for every prime at every M.
- mobiusDivisorSelectionFibre_insert_late_prime: exact piecewise full fibre update, only empty and singleton change.
- mobiusDivisorSelectionHead_insert_late_prime: h'=h+C_p.
- mobiusDivisorSelectionEnergy_insert_late_prime: Q'-Q=2hC_p.
Imports MobiusDivisorBernoulliPrimeEnergy and DivisorUnsignedChannelPositivity.
Private arithmetic isolation uses n∈Icc1(M−1), p∣n, M≤2p ⇒ n=p. No numerical source estimate.

`MobiusDivisorLatePrimeBlocks.lean` (162 lines,7 public theorems):
For hL:∀p∈L,p.Prime∧p<M∧M≤2p and hfree:∀p∈L,p∉P:
- mobiusDivisorSelectionHead_union_late_primes: h_(P∪L)=h_P+Σp∈L C_p.
- mobiusDivisorSelectionHead_union_late_primes_le: h_(P∪L)≤h_P.
- mobiusDivisorSelectionEnergy_union_late_primes: Q_(P∪L)=Q_P+2h_P c_L+c_L²−q_L, where c_L=ΣC_p, q_L=ΣC_p².
- mobiusDivisorSelectionEnergy_union_late_primes_le_of_head_nonneg: h_(P∪L)≥0 ⇒ Q_(P∪L)≤Q_P.
- mobiusDivisorSelectionEnergy_le_union_late_primes_of_head_nonpos: h_P≤0 ⇒ Q_P≤Q_(P∪L).
- mobiusDivisorSelectionEnergy_late_block_le_max_endpoints M P L R hL hfree hRL.
- mobiusDivisorSelectionEnergy_late_block_ceiling_iff M P L B hL hfree: (∀R⊆L,Q_(P∪R)≤B) ↔ Q_P≤B ∧ Q_(P∪L)≤B.
Block proofs use finite-set induction and exact single-prime identities. The endpoint theorem splits on head sign at P∪R; final comparison uses remaining L\R.

## Verification completed; do NOT repeat
Scratch checks, then foreground `lake env lean <leaf> -o <exact olean>` for both leaves passed without errors/warnings. Both exact oleans exist; both wired ONCE into RHTower.lean immediately after MobiusHalfSelectionGrowthObstruction.
All12 NEW public theorems axiom-audited ONCE: only propext, Classical.choice, Quot.sound. Do not re-audit these or previous leaves. No lake build, umbrella or dependency build.
Global formal lint ran once; three unrelated concurrent unwired RHTower modules: ThetaCuspEffectiveFirstAtomJets, ThetaCuspEffectiveLikelihoodCooling, ThetaCuspEffectiveSourceApproximation. Neither new CCM-FU leaf flagged. formal_tools.py index ran once,5changed0removed. git diff --check passed. New certificate relative links checked. All10 owned scratch/log files removed; no owned Lean process remains.

## Documentation
New `docs/drafts/pipeline/3-formalized/ccm-fu-late-prime-block-endpoints.md` gives paper proof, exact source formulas, all12 Lean theorems/audit and open boundary.
Updated PE4 card with formal block reduction, SD1 card, current frontier CCM-FU row and paragraph; extended universal MUST-217 with route-independent head-sign/isolated-block endpoint rule. PE5 stays failed, PE4 in progress.

## Research boundary and next useful work
Entire corpus searches for prime mergers, actual overlap control, balanced Möbius decomposition and Buchstab found no independent all-cutoff smaller-prime controller. Generic unsigned positivity/endpoint arguments already fail via positive cube; independent average already refuted. Do not add another finite graph receiver and call it a producer.
Actual late-block endpoint control leaves scheduling of smaller-prime mergers and the final signed SD1 bound. It does NOT justify putting the entire late block first or last; increasing-order head asymptotic already excludes the latter original-ceiling strategy.
Potential further exact arithmetic direction (not yet proved here): after processing small primes, larger quotient bands can become isolated scalar fibres with combined coefficients; their signs must be proved from the actual small-scale source. E.g. extending beyond M/2 requires retaining p,2p source labels and the processing status of2. Do not assume same sign in the larger band.
A possible constructive refinement within the already proved late band is greedy ordering by current head sign: explicit first-block coefficient C_p=-D(1)(sqrt M−sqrt p) would order late-prime gains by p. That public formula/sign comparison is NOT created in this turn; the older private `unsigned_channel_first_block` lives in MobiusDivisorLatePrimeCompensation. Search/reuse carefully before proving anything new.

## Lean efficiency notes
One foreground Lean process per agent, poll same handle. No full or umbrella builds. Need imports for unsigned positivity; BernoulliPrimeEnergy alone does not expose mobiusDivisorDilationChannel_eq_moebius_unsigned.
`hp.primeFactors` and `hp.squarefree` verified in scratch. `Finset.union_insert` rewrites P∪insert p L to insert p(P∪L). Finset induction: `revert hL hfree` before induction gives useful ih hL' hfree'. For arbitrary intermediate subset, prove (P∪R)∪(L\R)=P∪L by ext and hRL, not by guessing simplifier names.
