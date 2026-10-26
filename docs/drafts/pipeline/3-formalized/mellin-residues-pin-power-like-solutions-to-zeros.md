# Mellin residues pin power-like solutions to the translated zeros

- **ID:** adr-mellin-residues
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Let `0 < ε < 1/2`, `S_ε v(n) = Σ_{j≤n} j^{−ε} v(⌊n/j⌋)`. If a complex row
  `v = Σ_{s∈F} c_s n^s + r` (finite `F`, `1/2 < Re s ≤ 1`, `s ≠ 1 − ε`, `r` of bounded pronic energy)
  satisfies the renormalized inversion law `S_ε v = c' n^{1−ε} + r'` with `r'` of bounded energy, then
  `ζ(s + ε) = 0` for every `s` with `c_s ≠ 0`. Consequently, for `1/2 < Re s < 1 − ε`: there is a
  complex row of infinite pronic energy that is an approximate eigenrow of `D₂` and `D₃` with
  exponent `s` (errors of finite energy) and satisfies the renormalized inversion law **iff**
  `ζ(s + ε) = 0`.

## Paper proof
1. **Mellin transform.** `𝓜v(w) = Σ v(n)(n^{−w} − (n+1)^{−w})`. For `r` of bounded energy the series
   converges absolutely and locally uniformly on `Re w > 1/2` (Cauchy–Schwarz against `n^{−Re w−1}`),
   so `𝓜r` is holomorphic there.
2. **Power rows.** For `Re w > Re s + 1`, telescoping gives
   `𝓜(n^s)(w) = Σ_k ((k+1)^s − k^s)(k+1)^{−w} = s ζ(w − s + 1) + E_s(w)`, with
   `E_s(w) = Σ_k e_s(k)(k+1)^{−w}`, `e_s(k) = (k+1)^s − k^s − s(k+1)^{s−1} = O(k^{Re s−2})` (second-order
   mean value), so `E_s` is holomorphic on `Re w > Re s − 1`.
3. **Fubini.** For `Re w > 2`, the pair sum `Σ_{j,n} j^{−ε} v(⌊n/j⌋) Δ_n(w)` converges absolutely
   (`|v(m)| ≪ m + 1`), and the block identity `Σ_{t<j} Δ_{mj+t}(w) = j^{−w} Δ_m(w)` gives
   `𝓜(S_ε v)(w) = ζ(w + ε) 𝓜v(w)`.
4. **Identity theorem.** `G(w) = ζ(w+ε)(Σ c_s(sζ(w−s+1) + E_s(w)) + 𝓜r(w)) −
   (c'(αζ(w−α+1) + E_α(w)) + 𝓜r'(w))` is meromorphic on the connected half plane `Re w > 1/2` and
   vanishes on `Re w > 2`, so its meromorphic order is `⊤` everywhere: `G = 0` on a punctured
   neighbourhood of each point.
5. **Residue.** Near `s₀ ∈ F` every term except `c_{s₀} s₀ ζ(w + ε) ζ(w − s₀ + 1)` is continuous
   (exponents distinct, `s₀ ≠ α`, `s₀ + ε ≠ 1`), and `(w − s₀)ζ(w − s₀ + 1) → 1`; hence
   `(w − s₀)G(w) → c_{s₀} s₀ ζ(s₀ + ε)`, which must be `0`.
6. **Dictionary.** (⇐) two dilation laws give `w = c n^s + r` (contribution "two-dilation eigenrows"),
   `c ≠ 0` since `w` has infinite energy; apply 5. (⇒) `w = n^s`: the dilation laws hold
   (`|n^s − (p⌊n/p⌋)^s| ≤ (‖s‖+1)p`), and the symbol estimate gives
   `S_ε n^s − 𝓛_s n^{1−ε} = ζ(s+ε) n^s + O(n^{(Re s−ε)/2})`, of finite energy when `ζ(s + ε) = 0`.

## Lean
`ArithmeticDefectRigidity/MellinResiduesPinPowerLikeSolutionsToZeros.lean`:
`differentiableOn_rowMellin`, `norm_powerDefect_le`, `differentiableOn_powerCorrection`,
`rowMellin_cpow_eq`, `hasSum_dil_mul_complexMellinCell`, `hasSum_cTotalCofactorSum_mul_cell`,
`tendsto_sub_mul_riemannZeta_shift`, `riemannZeta_add_eq_zero_of_powerLike_solution`.
`ArithmeticDefectRigidity/RankOneEscapeRowsAreTranslatedZeros.lean`:
`cPronicEnergy_cpow_eq_top`, `riemannZeta_add_eq_zero_iff_exists_rankOneEscapeRow`.
Standard axioms only.

## Insight
`S_ε` is unbounded on rows of finite energy, so finite-horizon symbol estimates cannot rule out that
`S_ε r` cancels a power term; the Mellin transform can, because `𝓜r` continues holomorphically to
`Re w > 1/2` while `𝓜(n^s)` has a pole at `s` whose residue survives multiplication by `ζ(w + ε)` unless
`ζ(s + ε) = 0`. Together with two-dilation tiedness this closes the rank-one source-level dictionary:
escape rows that behave like joint eigenvectors of `D₂, D₃` up to finite energy are exactly the
translated zeros. The remaining gap for exclusion is only that actual escape states need not be
joint eigenrows with `O(1)` errors.
