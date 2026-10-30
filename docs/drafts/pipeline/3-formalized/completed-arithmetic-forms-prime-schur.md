# Prime packet reserve and local variation payment

- **ID:** completed-arithmetic-forms-prime-schur
- **Stage:** 3-formalized
- **Type:** THEOREM

## Finite arithmetic packets

For `Q≥1`, a finite index set `S`, interior nodes `1≤k_i<Q`, and real coefficients `a_i`,
let `A_r=Σ_(i∈S,k_i=r) a_i` and `B_Q(r,s)=Q min(r,s)-rs`.
Finite summation gives

`E_Q(A)=Σ_(i,j∈S) a_i a_j B_Q(k_i,k_j)`.

Its radical consists exactly of packets with `A_r=0` at every interior node. The exact
coefficient reserve controls `(Σ_i a_i)²+Σ_r A_r²`; for distinct nodes the second term
is `Σ_i a_i²`. Collisions are therefore retained as fiber sums, not discarded.

For any coupling `b`, with zero boundary extension `b⁰`, the normalized Schur bound is

`2Σ_i a_i b(k_i) − E_Q(A)/Q ≤ D_Q(b⁰)`.

Indeed apply the exact arithmetic Schur bound to `A` and `Qb`, then divide by `Q`.
The factors cancel because `D_Q(Qb⁰)=Q²D_Q(b⁰)`.

## Actual prime source

Let `S⊂(P,2P]` be a finite prime block and let its coefficient packet have zero mass
and zero logarithmic moment. Set `Q=2P+2`. The source identity on the first-jump
window, followed by positivity of the omitted actual energy, gives

`E_Q(A)/Q ≤ primePacketBilinear(S,S,a,a)`.

Consequently, uniformly in the prime block and every real coupling `b`,

`Σ_(p∈S) a_p² ≤ 4 primePacketBilinear(S,S,a,a)`,

`2Σ_(p∈S) a_p b(p) − primePacketBilinear(S,S,a,a) ≤ D_Q(b⁰)`.

Both boundary edges belong to `D_Q`. The restricted packet domain is explicit; no
unproved sign or residual bound enters either inequality. The result controls a linear
coupling to the actual energy-centered prime source. It does not identify an arbitrary
complete Weil remainder with that coupling.

## Dependencies

- `divisorGramEnergy_coercive`, `divisorGramEnergy_eq_zero_iff`.
- `bridgeSchur_bound`, `bridgeSchurCost_mul`.
- `brownianBridge_le_primePacketBilinear`.
- Finite fiber summation.

Lean: `CompletedArithmeticForms/FinitePackets.lean` and
`CompletedArithmeticForms/PrimePacketSchur.lean`, particularly
`packetBridge_eq_zero_iff`, `packetBridge_schur_bound`,
`divisorGramEnergy_le_primePacket`, and `primePacket_schur_bound`.
Kernel dependencies: `propext`, `Classical.choice`, `Quot.sound`.
