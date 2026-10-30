# Separation reserve for actual prime packets

- **ID:** completed-arithmetic-forms-separated-reserve
- **Stage:** 3-formalized
- **Type:** THEOREM

## Statement

Let distinct integer nodes `k_i` lie in `1,…,Q−1`, with no two adjacent. Then

`Σ_i a_i² ≤ (2/Q) Σ_(i,j) a_i a_j [Q min(k_i,k_j)−k_i k_j]`.

For an actual neutral prime packet in `(P,2P]`, `P≥2`, this gives

`Σ_p a_p² ≤ 2 primePacketBilinear(S,S,a,a)`.

Neutrality means the two exact constraints `Σa_p=Σa_p log p=0`.

## Proof

Extend the coefficients by zero to every integer coordinate, obtaining `C_r`.
Separation gives `C_r C_(r+1)=0`. Both endpoint values vanish, so

`D_Q(C)=Σ_(r<Q)(C_(r+1)−C_r)²=2Σ_r C_r²=2Σ_i a_i²`.

The normalized arithmetic Schur inequality at coupling `b=C/2` becomes

`Σ_i a_i²−E_Q(C)/Q≤D_Q(C)/4=(1/2)Σ_i a_i²`.

Rearrangement proves the stated reserve. Every prime above `P≥2` is odd,
so distinct nodes in the prime block are nonadjacent. The actual first-jump
source comparison `E_Q(C)/Q≤primePacketBilinear(S,S,a,a)`, with `Q=2P+2`,
transfers the reserve to the complete prime form on its neutral domain.

## Consequence

The source coefficient reserve doubles when the arithmetic support has no
adjacent indices. This improvement uses the exact inverse variation and
retains all unequal-prime entries of the original source form.

Lean: `CompletedArithmeticForms/SeparatedPacketReserve.lean`,
`packetBridge_separated_reserve` and `primePacket_odd_coefficient_reserve`.
Kernel dependencies: `propext`, `Classical.choice`, `Quot.sound`.
