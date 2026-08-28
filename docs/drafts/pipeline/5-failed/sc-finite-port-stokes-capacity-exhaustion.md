# SC unbounded negative-port capacity

- Route: SC (`LAND ORIENT COMP`)
- Claim: finite-port coefficient-generated Stokes landing cannot carry all reflected source-horizontal prime packets on an off-line Xi fibre.
- Status: `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- Active exact claim: for every off-line Xi divisor copy and every finite port budget `k`, an injectively prime-labelled packet of size `k+2` has one reflected orientation whose quadratic form cannot factor as a sum of `k` one-port forms.

## Internal frontier

- `[CORPUS]` `sourceZeroHorizontalSharedReservoirMatrix_inertia_of_right` proves exact inertia `(1,m-1,0)` for every right-half packet.
- `[CORPUS]` reflection negates the matrix, so every off-line copy has one orientation with negative index `m-1`.
- `[CORPUS]` `globalWittForm_add_rankCorrection_nonneg` proves every coefficient-generated global Stokes Witt form becomes nonnegative after one rank square.
- `[CORPUS]` `sourceZeroHorizontalSharedReservoir_twoOrientation_onePort_obstruction` excludes one Stokes port when `m >= 3`.
- `[CORPUS]` `exists_sourceZeroHorizontalSharedReservoirPacket` supplies arbitrarily large injectively prime-labelled packets with every coefficient nonzero.

## External frontier

- `[LITERATURE]` Krein--Langer/Pontryagin theory treats kernels and spaces with a fixed finite number of negative squares. The dimension bound used below is the standard negative-squares mechanism.
- `[LITERATURE]` Deninger-style determinant programs and Connes-style spectral realizations do not provide the exact source-horizontal/Stokes finite-port exhaustion statement below.
- Exact priority remains unverified; repository novelty is not scientific-priority evidence.

## Conjecture loop

### C1 -- boundary annihilation

`[FALSIFIED]` Every Xi theta-source eigenmode annihilates the rank-two pinned Green boundary form.

Killing mechanism: `inner_pinnedBoundaryCLM_thetaDivisorEigenvector` computes the form as a strictly positive root energy times the transverse Xi coordinate. It vanishes exactly on the critical line and is nonzero off it.

Representation lesson: finite boundary flux is the obstruction, not an error term to discard.

### C2 -- finite-port absorption

`[FALSIFIED]` A fixed finite sum of coefficient-generated Stokes/Pontryagin ports can absorb all finite reflected prime packets.

Killing mechanism: packet negative index grows as `m-1`, while a sum of `k` one-port carriers has negative index at most `k`.

### C3 -- unbounded-port law

`[LEAN-PROVED]` For every finite `k` and every off-line Xi copy, there is an injectively prime-labelled packet of size `k+2` for which simultaneous landing of the copy and its reflection through `k` one-port carriers is impossible. The same holds for `k` copies of any coefficient-generated global Stokes Witt carrier.

## Dependency-closed paper proof

Let `S` be a real quadratic form on a finite-dimensional space `V`. Suppose

`S(x) = sum_i Q_i(f_i x)`

for `i < k`, and each port admits a linear functional `ell_i` with

`Q_i(y) + ell_i(y)^2 >= 0`.

Then

`S(x) + sum_i (ell_i(f_i x))^2 = sum_i (Q_i(f_i x) + ell_i(f_i x)^2) >= 0`.

The Krein--Langer dimension argument therefore gives `sigNeg(S) <= k`: on any negative-definite subspace, the map `x |-> (ell_i(f_i x))_i` is injective.

Now fix an off-line Xi copy `q` and a packet of size `m`. If `q` is right of the critical line, its source-horizontal shared-reservoir form has `sigNeg = m-1`. If `q` is left, its line-conjugate reflection is right and has `sigNeg = m-1`. Hence simultaneous `k`-port factorizations of both orientations imply `m-1 <= k`. They are impossible whenever `k < m-1`.

For any finite `k`, take `m=k+2`. The corpus packet-existence theorem supplies injective prime labels with all coefficients nonzero. Since `k < (k+2)-1`, the simultaneous landing is impossible. A coefficient-generated global Stokes Witt form is one-port after its explicit rank correction, so the same conclusion applies to every finite direct sum of such carriers.

No RH assumption, zero-location premise, continuity assumption, compactness assumption, or added positivity hypothesis occurs.

## Mathematical delta

The one-port SC obstruction is not repaired by taking any fixed finite number of Stokes sectors, finite direct sums, finite Pontryagin index, or larger finite matrices. Off-line source reflection forces negative-port demand to grow without bound with prime-packet size.

Strongest positive survivor: any viable literal all-prime SC object must carry genuinely unbounded/infinite negative index before its final orientation selection, or use a nonlinear/non-quadratic coupling that does not factor through finitely many one-port forms. Merely enlarging finite Stokes data cannot work.

## Lean realization

Module: `formal/GaloisForLFunctions/RHTower/SourceHorizontalFinitePortStokesCapacity.lean`

- `sigNeg_le_of_finiteOnePortSumPullback`
- `sourceZeroHorizontalSharedReservoir_twoOrientation_finitePort_obstruction`
- `GlobalPuiseuxWittFinitePort.not_both_sourceZeroHorizontal_orientations_land_in_finiteGlobalWitt`
- `GlobalPuiseuxWittFinitePort.xiOffLineFiniteGlobalWittPortExhaustion`

Targeted `lake env lean` and leaf `lake build` pass. All four capstones depend only on `[propext, Classical.choice, Quot.sound]`.
