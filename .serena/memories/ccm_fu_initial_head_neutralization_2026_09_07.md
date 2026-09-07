# CCM-FU: unconditional initial head neutralization

Goal remains active; RH, SD1, PE4, PE4G and PE4C remain open. Progress: a positive source-derived initial balancing operation, not merely another conditional budget.

## Closed leaf
`formal/GaloisForLFunctions/RHTower/MobiusDivisorHeadNeutralization.lean` imports only existing NonemptyEnergy and LatePrimeInterleavingCapacity. Nine public theorems, no new definitions.
- `exists_mass_cover_with_square_reserve`: finite nonnegative weights bounded by a, total covering nonnegative h, admit L with excess delta in [0,a] and delta² <= sum_L w². Finite induction; no endpoint-energy assumption.
- `divisorUnsignedDilationChannel_eq_first_block`: 1<=d<M<=2d gives K_d(M)=(sqrt M-sqrt d) D(1).
- `divisorUnsignedDilationChannel_late_le_sqrt`: K_d(M)<=sqrt M on first quotient block, analytically from D(1)<=1.
- `exists_mobiusDivisorLatePrime_head_neutralization`: any currently unprocessed late-prime supply covering a nonnegative current head has selected L with head in [-sqrt M,0], head²<=M, E(P union L)<=V(P)=E(P)-head(P)², and EVERY R subset L has E(P union R)<=E(P). Exact nonempty block identity pays the discrete excess square from removed singleton squares; endpoint law supplies all intermediates.
- `mobiusDivisorSelectionHead_empty_eq_unit_channel`: initial head=K_1(M).
- `mobiusDivisorSelectionHead_empty_nonneg`: all M.
- `mobiusDivisorSelectionHead_empty_le_linear`: initial head<=27M, from head²<=original diagonal<=722M².
- `eventually_mobiusDivisorLatePrimeMass_covers_initial_head`: eventually N, initial head(4N)<=T(4N), using formal T(4N)/(4N)->infinity.
- `eventually_exists_mobiusDivisorInitialHeadNeutralization`: UNCONDITIONAL capstone eventually N, L subset actual activeLatePrimes(4N), head in [-sqrt(4N),0], head²<=4N, E(L)<=V(empty), every R subset L under original diagonal. Only eventual cutoffs 4N are asserted, not all M.

## Remaining mathematical boundary
This releases the ENTIRE original head square in the first block and proves source availability there. It does not establish availability or joint signed budgets after later smaller-prime mergers. A successful complete original-diagonal schedule still requires growing late/earlier-prime interleaving (prior exact fixed-block obstruction), actual retained singleton signs and nonempty mixed products. Prior universal V-contraction is false (M21 P={2} q=5), while existence of a full nonincreasing V path through32 is numerical guidance only. Do not claim this initial block proves SD1. No new diagnostics were run this turn.

## Verification completed; do not redo
API names verified in scratch. Full proof scratch passed first try; exact new leaf compiled with lake env lean -o its own olean. No umbrella/dependency/full build. New leaf wired once in RHTower.lean after NonemptyEnergyObstruction. All nine new declarations axiom-audited ONCE (standard propext, Classical.choice, Quot.sound only); no numerical premise. Global formal lint PASSED. Scoped diff check passed. Card promoted to docs/drafts/pipeline/3-formalized/ccm-fu-late-prime-head-neutralization.md; all new relative links verified. PE4, SD1, current frontier and universal STATUS updated. STATUS adds route-independent MUST-DISCRETE-CORRECTION-RESERVE. Index refreshed once (4 changed,0 removed; API/GAPS/OVERVIEW written).

All owned Lean/build/audit sessions completed; process check empty. Six owned scratch/audit files removed. Preserve unrelated concurrent working-tree changes. No commit/push. Next turn state full route chain and advance the subsequent joint control using corpus/source, not training assumptions.
