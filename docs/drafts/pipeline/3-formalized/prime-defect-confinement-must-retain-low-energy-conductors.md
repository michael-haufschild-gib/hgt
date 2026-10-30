# Prime-defect confinement must retain low-energy conductors

- **ID:** prime-defect-conductor-cutoff-obstruction
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** If a finite positive conductor family omits `m`, actual unit horizon vectors have coordinate mass tending to zero on that family and eventually have prime defect at most `E_m+log 4+4+ε`. In particular, a defect-only certificate for defect budget `γ+(k+1)log 2+log 4+5` must retain conductors at least as large as `2^k`.

## Paper proof

Write `v_m,N` for the logarithmically normalized Ramanujan vector and `u_m,N=v_m,N/‖v_m,N‖`. The proved norm limit is one, so `u_m,N` is defined and has norm one eventually. Its prime residual against eigenvalue `log N-E_m` tends to zero. Pairing that residual with `u_m,N` gives `log N-〈P_Nu_m,N,u_m,N〉→E_m`.

The exact row identity gives `D_N(u)≤log N-〈P_Nu,u〉+log 4+4` for every unit vector. Hence `D_N(u_m,N)≤E_m+log 4+4+ε` eventually. For every `l≠m`, the proved Gram limit gives `〈u_m,N,v_l,N〉→0`. Summing the squares over any fixed finite family omitting `m` proves the escaping-coordinate statement.

For `m=2^k`, `k≥1`, the exact tame-different formula gives `E_m=γ+(k+1)log 2`. Take the defect slack at most one. Every cutoff `Q<2^k` omits this witness, so its coordinate mass tends to zero despite the displayed defect budget. This establishes an exponential necessary scale, without assuming anything about prime distribution beyond the already proved quasimodes.

## Scope

These witnesses are not negative complete-Weil eigenvectors. The result tests the proposed improvement of generic arithmetic compactness; it does not obstruct the whole quasi-RH route. Any useful negative-eigenvector confinement must use information beyond the prime-defect bound.

## Positive survivor

Exact conductor-sensitive necessary condition for a universal coordinate certificate: every omitted low-energy conductor supplies an actual escaping unit sequence. Paper and Lean proofs closed.

## Lean proof

`RenormalizedArithmeticPotentialTheory/PrimeDefectConfinementMustRetainLowEnergyConductors.lean`:

- `tendsto_unitRamanujanHorizonVector_primeEnergy`
- `eventually_exists_unit_vector_escaping_conductors`
- `eventually_exists_unit_vector_escaping_binary_cutoff`
- `not_eventually_defect_coordinate_capture_below_binary_cutoff`

Final `lake --old env lean` check passes. All four audited declarations use only `propext`, `Classical.choice`, `Quot.sound`.
