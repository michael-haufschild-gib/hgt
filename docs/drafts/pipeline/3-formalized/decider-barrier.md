# T3: the invisibility barrier — whole classes of RH₂ deciders are constant

- **ID:** decider-barrier
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]` + formalized, axiom-clean
- **Source:** unifies the parity/no-go cluster (SignatureParity, DeckChargeLadder reflection blindness)
- **Statement (delivered):** `[PROVED HERE]`
  - `decider_blind_of_invariant_collision` — the barrier principle: any decider `D` factoring through an invariant `I` that collapses a pass/fail pair returns the same verdict on both. (Uses NO axioms.)
  - `deckCharge_quotient_barrier` — modulus-n instantiation: no deck-charge decider sees the discarded quotient index/n (`k` vs `k+n·q` collide).
  - `reflection_parity_barrier` — reflection instantiation: a fixed-point-free reflection pairing of off-line zeros has trivial parity (empty/RH-passing value), so no parity decider distinguishes a reflection-symmetric buckling from the empty configuration.
  - `exists_parity_blind_buckling` — a concrete two-zero buckling (σ = 1−i on Fin 2, m≡1): parity-blind yet carrying 2 > 0 off-line zeros (RH₂-failing). The barrier is not vacuous.
- **Lean:** `RHTower.decider_blind_of_invariant_collision`, `deckCharge_quotient_barrier`, `reflection_parity_barrier`, `exists_parity_blind_buckling` in `formal/GaloisForLFunctions/RHTower/DeciderBarrier.lean`. `#print axioms` = {propext, Classical.choice, Quot.sound} (principle: none). `lake build` green.

## What was new
The corpus had each no-go as a one-off "invariant X is blind to distinction Y". T3 abstracts the shared shape into a single barrier principle quantified over EVERY decider in a class, and instantiates it with two structurally different no-gos (mod-n quotient; reflection parity) plus a concrete non-vacuous collision witness. This is a barrier metatheorem — a constraint on the shape of any RH₂ proof (the rung-decider must read the discarded quotient / a quadrant-local count, never the global charge), in the spirit of complexity-theoretic barriers. The abstraction + multi-instantiation is not in the corpus.

## Log
- 2026-07-07 — created directly in 3-formalized (barrier principle + instantiations + witness + Lean).
