# CCM-FU: oriented initial block with arbitrary one-prime extension

Active RH goal stays open. Previous turn was progress (initial head neutralization); this turn adds an unconditional oriented initial phase controlling arbitrary one-prime interleaving. No new computations or numerical diagnostics.

## Closed new leaf
`formal/GaloisForLFunctions/RHTower/MobiusDivisorOrientedPrimeExtension.lean` (178 lines), imports previously built HeadNeutralization and Sieve.TruncatedMoebius. Seven public theorems; no new definitions.
1. `exists_mass_cover_below_with_bounded_residual`: finite nonnegative weights <=a covering h>=0 admit L with 0<=h-sum_L w<=a. If h<=a choose empty; otherwise use previous crossing selection on h-a.
2. `mobiusDivisorSelectionFibre_empty_parity_nonneg`: for all M,R, 0<=(-1)^card(R)*F(M,empty,R). Termwise squarefree Möbius parity and unsigned-source positivity.
3. `mobiusDivisorSelectionFibre_late_parity_nonneg`: same sign for every NONEMPTY retained label after any late-only set L, regardless of head sign. Exact isolated-prime recurrence removes only its singleton; preserves other nonempty fibres.
4. `mobiusDivisorSelectionEnergy_insert_le_of_parity_nonneg`: at any state P whose EVERY retained label (including empty) satisfies parity, every unprocessed prime q<M contracts E. Pair products nonpositive from opposite label parity; uses exact source merger sum.
5. `mobiusDivisorSelectionEnergy_insert_le_after_late_primes`: after any late-only L with nonnegative head, every available q contracts E.
6. `exists_mobiusDivisorInitialOrientedPrimeExtension`: explicit late-prime supply covering the initial head gives L with head in [0,sqrt(M)], head²<=M, E(L)<=V(empty)+M, and FOR EVERY R subset L: E(R)<=E(empty), and every available prime q<M has E(insert q R)<=E(R). Availability is explicit here.
7. `eventually_exists_mobiusDivisorInitialOrientedPrimeExtension`: UNCONDITIONAL capstone along every sufficiently large cutoff 4N, L subset actual activeLatePrimes(4N), all properties above. Existing formal T(4N)/(4N)->infinity discharges supply, no signed energy or RH premise.

## Meaning and boundary
The selected block is independent of q. Its bounds control every ordering of L together with ANY ONE extra prime, inserted anywhere, since every state is R or insert q R. Original head-square reserve is released up to additive M in the terminal E<=V0+M budget. Previous alternative gives negative residual head and full-square release; keep both results.
Do NOT iterate parity automatically. Existing public `mobiusDivisorSelectionFibre_twentyOne_three_gt` (NonemptyEnergyObstruction) is precisely 0.04<F(21,{2},{3}), so one small-prime merger can violate original odd parity on a nonempty label. This claim was read and verified against current source, not re-audited. Repeated smaller-prime operations need control of changed signs or restoration, plus a growing interleaving. PE4/PE4G/PE4C/SD1/RH all remain open.

## Verification done — no repeats needed
API names scratch passed; complete proof scratch passed first try. Exact leaf checked and own olean emitted via lake env lean. Wired once into RHTower.lean after HeadNeutralization. No full, umbrella, dependency or lake build. Audited ONLY seven NEW declarations ONCE: standard propext/Classical.choice/Quot.sound, no other axiom and no numerical premise. New leaf matches checked scratch bytes. Scoped git diff --check passed; unique import and new relative links checked.
Global formal lint invocation returned FIVE unrelated concurrent umbrella-wiring errors: RHTower.ThetaCuspTwoAtomExponentialAdmission; RHTower.ThetaCuspTwoAtomOddProfiles; HTGeometry.TwoAtomOddAlgebra; HTGeometry.TwoAtomOddHighReserve; HTGeometry.TwoAtomOddLowerReserve. No new-leaf error; do NOT claim global lint passed. Do not edit these unrelated active modules. Index refreshed once, 4 changed 0 removed, API/GAPS/OVERVIEW written.

Card promoted to `docs/drafts/pipeline/3-formalized/ccm-fu-oriented-initial-prime-extension.md`; PE4, SD1, current frontier and universal STATUS updated. STATUS adds route-independent MUST-PRESERVE-NEXT-STEP-ORIENTATION. Card records exact validation and remaining sign-changing iteration boundary.
All owned process handles completed (5025 names,14499 scratch,1247 leaf,18911 axioms,17562 lint,74631 index). Process snapshot found no lake env lean / owned leaf or scratch processes. Six owned /tmp files removed. No commit/push, no subagents. Preserve concurrent changes. Next turn start with full CCM-FU proof chain and pursue repeated smaller-prime control rather than retesting this leaf.
