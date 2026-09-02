# Route E Brick 148: exact coprime squarefree product-sign count

Production module:
`formal/GaloisForLFunctions/RHTower/MobiusCoprimeSquarefreeProductSignCount.lean`

Exact finite packet:
```lean
finiteCoprimeSquarefreeProductPairPacket (S : Finset (ℕ × ℕ))
```
filters an arbitrary finite pair set by `Nat.Coprime a b ∧ Squarefree a ∧ Squarefree b`, matching the paper card's two separate squarefree-factor assumptions literally.

Balanced specialization:
```lean
balancedCoprimeSquarefreeProductPairPacket (x h : ℝ)
```
uses existing native `RHTower.Sieve.balancedPairs x h`.

Six unconditional public theorems:
- `sum_moebius_finiteCoprimeSquarefreeProductPair_eq_sum_mul`
- `finiteCoprimeSquarefreeProductPair_bothSignCount_lower`
- `finiteCoprimeSquarefreeProductPair_bothProductSignCount_lower`
- `sum_moebius_balancedCoprimeSquarefreeProductPair_eq_sum_mul`
- `balancedCoprimeSquarefreeProductPair_bothSignCount_lower`
- `balancedCoprimeSquarefreeProductPair_bothProductSignCount_lower`

The sum theorems give exact Möbius multiplicativity on the packet. Factor-sign and literal product-sign versions both give simultaneous lower bounds for signs `±1`:
`(#packet - |signed imbalance|) / 2`.
The literal form uses `Σ μ(a*b)` and filters `μ(a*b)=±1`, exactly matching the card's product-sign object.

Proof derives literal factor signs from each factor's `Squarefree` filter via `CofactorParity.moebius_eq_one_or_neg_one`, applies existing finite sign extraction, then transports both sum and filtered cardinalities using coprime Möbius multiplicativity. No proposition hypotheses occur in public theorem statements.

Verification:
- source check: `lake env lean GaloisForLFunctions/RHTower/MobiusCoprimeSquarefreeProductSignCount.lean`
- targeted leaf audit: `lake build GaloisForLFunctions.RHTower.MobiusCoprimeSquarefreeProductSignCount` passed `9118/9118`
- all six theorem axiom audits: `[propext, Classical.choice, Quot.sound]`
- module wired into `formal/GaloisForLFunctions/RHTower.lean`; umbrella intentionally not built.

Card remains Stage 2: exact finite algebra does not prove full general-`h` asymptotic positive-liminf statement.