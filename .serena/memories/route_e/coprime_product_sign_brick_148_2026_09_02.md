# Route E Brick 148: exact coprime squarefree product-sign count

Production module:
`formal/GaloisForLFunctions/RHTower/MobiusCoprimeSquarefreeProductSignCount.lean`

Exact finite packet:
`finiteCoprimeSquarefreeProductPairPacket (S : Finset (ℕ × ℕ))`
filters an arbitrary finite pair set by `Nat.Coprime a b ∧ Squarefree a ∧ Squarefree b`, matching the paper card's two separate squarefree-factor assumptions literally.

Balanced specialization:
`balancedCoprimeSquarefreeProductPairPacket (x h : ℝ)`
uses native `RHTower.Sieve.balancedPairs x h`.

Nine unconditional public theorems:
- exact product Möbius/factor Möbius sum equality for arbitrary finite packet;
- simultaneous factor-sign lower count for arbitrary packet;
- simultaneous literal `μ(a*b)=±1` lower count for arbitrary packet;
- balanced-window versions of those three results;
- exact equality of balanced factor-sign filters with canonical `Sieve.coprimeSignClass x h (±1)`;
- exact equality of balanced literal product-sign filters with those canonical classes;
- terminal lower bound stated directly on `Sieve.coprimeSignClassCount x h (±1)`, the card's `R_±(x,h)`.

The canonical reverse inclusion is proved, not assumed: `μ(a)μ(b)=±1` forces each factor Möbius value nonzero; `ArithmeticFunction.moebius_ne_zero_iff_squarefree` yields the two separate squarefree predicates. Coprime multiplicativity then identifies literal product signs.

No proposition hypotheses occur in public theorem statements.

Verification:
- source check: `lake env lean GaloisForLFunctions/RHTower/MobiusCoprimeSquarefreeProductSignCount.lean`
- targeted leaf build run for `GaloisForLFunctions.RHTower.MobiusCoprimeSquarefreeProductSignCount`
- all nine theorem axiom audits: `[propext, Classical.choice, Quot.sound]`
- module wired into `formal/GaloisForLFunctions/RHTower.lean`; umbrella intentionally not built.

Card remains Stage 2: exact finite algebra now reaches canonical `R_ε`, but does not prove full general-`h` asymptotic positive-liminf statement.