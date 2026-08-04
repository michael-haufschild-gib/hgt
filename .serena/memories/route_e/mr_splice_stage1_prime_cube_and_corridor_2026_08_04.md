# MR splice: stage 1 built; power-clean corridor certified (2026-08-04)

Card: `docs/drafts/pipeline/1-in-progress/mr-splice-wide-range-mean-square.md`.

**Built and verified** (`RHTower/Sieve/PrimeCubeSupport.lean`, wired into `RHTower.lean`,
`lake build` pass, axioms only propext/Classical.choice/Quot.sound):
- `sum_normSq_convCube_le_of_support` — cube ℓ² bound through an arbitrary coefficient support;
- `cubeFibreOn_primeSupport_card_le_nine` — triple-of-primes fibre ≤ 9 (first two coordinates lie
  among the ≤3 prime factors of the anchored product, third determined);
- `sum_normSq_convCube_le_of_prime_support` (constant 9, no `C_ε N^ε`);
- `volume_largeValues_sixth_le_of_prime_support` and `_symm_` — prime-polynomial level-set bounds.

**Key numeric certifications (sweeps on the card, exact built constants):**
1. Single product-split with `sup²·meas` on the exceptional set, and also the double split with a
   fourth-moment tail, BOTH fail below `θ = 1/2` by a positive power of `N` — under the corpus's
   Gallagher passage, because its ℓ¹ tail `M₂/(π²W)` forces `W ≍ (N/L)²`.
2. **The ℓ¹ tail is the false wall.** The Gallagher weight decays like `2/(π²w²)`
   (`norm_fourier_triC_le`); dyadic far blocks paid by the symmetric MVT give tail
   `O(L² log N)` at `W = N/L`. With `W = N/L`, prime scale `P³ ≍ W`, threshold `V = εP/log P`:
   NO `N`-power obstruction anywhere in `θ ∈ (1/4, 1)` — covering the Route E marker corridor
   `(1/2, 3/4]`. Everything remaining is a log-power fight: diagonal `log N` + exceptional
   `ε⁻⁶(log)³⁺`, to be beaten by the built `MoebiusUniformFrequency` Halász layer.
3. Below `θ = 1/4` a single prime scale cannot work (`P³ ≍ W` collides with the long diagonal);
   iterated ranges (true MR) required.

**Next Lean unit (stage 3a, frozen):** weighted Gallagher far tail — replace the ℓ¹ tail in
`GallagherSplitIntegral` by dyadic weighted MVT blocks. Corpus-owned ingredients only.
Then 3b: log-power fight (pre-certify numerically first).

Corrections to stale memories: `mr-path-gap-status`'s "no lower bound on δ" is stale —
`MoebiusUniformFrequency.lean` proves the uniform distance lower bound
`min_{|t|≤T} D(μ,χ_t)² ≥ log log z − 7 log log T − C`.
