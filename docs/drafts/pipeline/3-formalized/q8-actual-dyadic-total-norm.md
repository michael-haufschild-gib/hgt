# Q8 actual dyadic total norm

**Claim.** For every prime `P|2` of the literal SST `Q8` field, let `Q` be its contraction to `ℚ(√5,√41)` and `E` the packaged `Q`-adic completion. There is `x∈E⊗_K N` such that

`N_{E⊗N/E}(x) · σ_E(N_{E⊗N/E}(x)) = −1`,

where `σ_E` is the completed source decomposition involution.

**Proof.** Decomposition-group equality forces the first conjugation to preserve `Q`; valuation-ring preservation gives a continuous completed involution. The Hensel norm selector supplies `x` with norm `u=(1+√5)/2`. Completion compatibility gives `σ_E(u)=1−u`, while `u²=u+1`; thus `u(1−u)=−1`.

**Lean.** `RHTower.exists_q8ActualTwoAdicTotalNorm_neg_one` in `DeningerQ8ActualTwoAdicTotalNorm.lean`; source check, leaf build, and axiom audit pass. Dependencies use only `propext`, `Classical.choice`, and `Quot.sound`.

**Boundary.** This kills dyadic norm selection. It does not identify the literal Artin/Hecke source character with local reciprocity.
