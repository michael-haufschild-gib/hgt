# Primes in short intervals in every reduced residue class

- **ID:** A59 (review-1111 §2.1, classical inputs)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For `q ≥ 1`, `a` a unit mod `q` and `θ = 1 − 1/(16(14·10⁷ + 12))`, every interval
  `(x, x + x^θ]` with `x` large contains a prime `p ≡ a (mod q)`; the von Mangoldt mass of the class
  in the interval is `∼ x^θ/φ(q)`.

## Lean

Folder `formal/GaloisForLFunctions/ShortIntervalPrimesInProgressions/`, umbrella
`ShortIntervalPrimesInProgressions.lean`. Axioms of both headline theorems: `propext`,
`Classical.choice`, `Quot.sound`.

| Step | Module | Theorem |
|---|---|---|
| Zeros of primitive `Λ(s,χ)` in `0 < Re < 1`, Hadamard partial fraction | `TheZerosOfAPrimitiveLFunction` | `zero_re_mem`, `logDeriv_completedLFunction_eq` |
| Explicit formula | `TheExplicitFormulaForACharacter` | `explicitFormula` |
| Window of `ψ(·,χ)` by a weighted zero sum | `CharacterSumsInShortWindows` | `norm_psiChi_window_le` |
| Local zero count `O(log(|t|+3))` (Jensen) | `LocalZeroCount` | `card_zeros_near_le` |
| `k`-th derivative test for `χ(n)n^{−it}` (finite Fourier on `ZMod q`) | `CharacterPhaseBlocks` | `norm_twisted_block_le`, `norm_character_run_le` |
| `|L(σ+it,χ)| ≤ (3+4888q) log³|t|` for `σ ≥ 1 − (log log|t|)²/log|t|` | `LittlewoodGrowth` | `norm_LFunction_le_littlewood` |
| `β ≤ 1 − log log|γ|/(10⁷ log|γ|)` | `LittlewoodZeroFreeRegion` | `exists_littlewood_zero_free_region_character` |
| Mollified detection, slabs, blocks, Taylor orders | `ZeroDetectionForACharacter` | `half_le_norm_detPolyChi`, `exists_class_of_detected` |
| `N(σ,T) ≤ D(1+log T)^{11} T^{12(1−σ)}` | `ZeroDensityForACharacter` | `exists_zeroDensity_character` |
| `Σ_ρ zeroShortWeight(x, c x^{2u}, ρ) → 0`, `u < u₁/4` | `TheZeroSumVanishes` | `tendsto_tsum_zeroShortWeight` |
| Windows for every character (primitive, imprimitive, principal) | `CharacterWindows` | `tendsto_window_character`, `tendsto_window_principal` |
| Residue class asymptotic, primes | `PrimesInShortProgressions` | `tendsto_residueClass_window`, `eventually_exists_prime_short_interval_mod` |

## Proof

1. Explicit formula and window squeeze: `|Δψ(χ)| ≤ windows of ψ of length h' + 2h Σ_ρ x^{β−1}
   min(1, 8x²/(hh'|ρ||1−ρ|)) + O(log x) + O(1/h')`.
2. Zero sum at `h = x^θ`, `h' = x^{1−u₁/8}`, i.e. `8x^{2u}`, `u = 3u₁/32`: zeros with `β ≤ 3/4` or
   `|γ| > x^{u₁}` cost `O(x^{3u/2−1/4} + x^{2u−u₁/2}) Σ(|ρ||1−ρ|)^{−3/4}`; the rest are cut into
   slabs of width `1/log x`, each bounded by the density estimate, and Littlewood's region gives
   `x^{−(1−12u₁)w₁} = (u₁ log x)^{−14}` against `(log x)^{12}`.
3. Littlewood's growth: dyadic blocks `≤ exp(2L/log L)` trivially (`≤ L²`); above, the least order
   `k` with `λ_k ≤ M^{−1/2}` has `λ_k ≥ M^{−3/2}/2`, the test saves `M^{−2^{−k−1}}`, and
   `2^{k+1} ≤ 16√L`.
4. Region: de la Vallée Poussin with Landau's lemma on discs of radius `(log L)²/(16L)`; the
   principal `χ²` uses the corpus wide band of `ζ`.
5. Density: `L_X M_y − 1 = Σ χ(k)e_k k^{−s}` with `y = ⌈T⌉`, `X ≍ T⁴`; a zero gives a class (slab,
   dyadic block, Taylor order) with value `≥ 1/(12J)`; a separated subset of the fullest class is
   bounded by the discrete mean value theorem.
6. Imprimitive characters agree with their primitive character off `gcd(n,q) > 1`; a window
   `(x, x+h]`, `h ≤ x`, holds at most one power of each prime. Huxley's theorem gives the
   principal window; prime powers cost `ψ − θ ≤ 2√y log y`.
