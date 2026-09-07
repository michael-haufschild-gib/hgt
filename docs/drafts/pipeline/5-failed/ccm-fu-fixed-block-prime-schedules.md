# CCM-FU: fixed-block prime schedules

- **Stage:** 5-failed
- **Type:** unconditional fixed-block obstruction; positive capacity law formalized
- **Parent:** [adaptive original-diagonal ceiling](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Boundary:** PE4, PE4G, PE4C, SD1 and RH remain open.

## Frozen fixed-block claim and obstruction

Every unprocessed prime p with M/2<p<M contributes only its isolated nonpositive singleton coefficient. If L is a block of such primes and P its initial processed set, its positive mass is `t_L=sum_(p in L)K_p(M)` and its head drops exactly by t_L. Each head square is at most its actual retained energy. Hence, if both block endpoints have energy at most B, then

`t_L <= 2 sqrt(B)`.

For K disjoint blocks covering the late primes, summing gives `T(M)<=2K sqrt(B)`. This estimate holds for arbitrary corresponding processed sets, so it applies in particular to complete prime orders split into maximal uninterrupted late-prime blocks. It requires no monotonicity within the order and retains all actual source mass.

The closed arithmetic bounds are `Q(M)<=722M^2` and `T(4N)/(4N)->+infinity`. Consequently, for every fixed block count K and original-diagonal multiplier C, all sufficiently large cutoffs 4N defeat every such K-block schedule: at least one block endpoint exceeds `C Q(4N)`. A bounded-energy proof therefore needs an unbounded number of interleavings between late and earlier primes. Changing only the order within a fixed number of late blocks cannot suffice.

## Positive survivor and Lean closure

The single-block capacity, stronger sum of actual endpoint square roots and common-budget partition estimate are proved in Lean. A partition assigns every active late prime to one of K labels, retaining each exactly once. Intermediate processed sets remain arbitrary; only disjointness from their assigned unprocessed block is required. This includes the maximal uninterrupted late-prime blocks in an actual complete order. No energy-budget premise appears in the final unconditional obstruction: it asserts an exceeding endpoint for every admissible fixed-size decomposition.

`MobiusDivisorLatePrimeInterleavingCapacity.lean` contains one definition and nine public theorems:

- `mobiusDivisorActiveLatePrimes`, its membership conditions and exact total-mass identity remove only the terminal zero channel.
- `abs_mobiusDivisorSelectionHead_le_sqrt_energy` controls the literal retained head by complete energy.
- `mobiusDivisorLateBlock_mass_le_endpoint_roots` and `mobiusDivisorLateBlock_mass_le_of_energy_le` give the two endpoint capacity bounds.
- `sum_mobiusDivisorLatePrimePartition_mass`, `mobiusDivisorLatePrimeMass_le_partition_endpoints` and `mobiusDivisorLatePrimeMass_le_partition_capacity` retain all assigned prime mass and prove the aggregate bounds.
- `eventually_mobiusDivisorLatePrimePartition_exceeds_diagonal` proves the eventual obstruction at cutoffs 4N for every natural K and real multiplier C.

The positive survivor is quantitative: `T(M)<=2K sqrt(B)` for every admissible uniformly budgeted decomposition, and the sum of actual endpoint square roots bounds T without a common budget. Since the source has `T(4N)/(4N)->+infinity`, the number of blocks required under any fixed original-diagonal multiplier must grow without bound. The theorem supplies no upper bound or construction for a sufficient number of blocks and does not imply SD1.

Paper proof and scratch/exact-leaf checks are complete. Existing late-block laws, quadratic diagonal and late-mass growth are reused without re-audit. No numerical result enters Lean. The common-order PE4C diagnostic through cutoff 32 remains separate finite guidance.

The new leaf passed foreground `lake env lean` in scratch and then with its exact olean output. All ten new public declarations were axiom-audited once and use only `propext`, `Classical.choice` and `Quot.sound`. The leaf is wired once into `RHTower.lean`; no umbrella, full or dependency build ran. The single global `scripts/formal_tools.py lint` run passed. Formal indexes were regenerated after adding the declarations.
