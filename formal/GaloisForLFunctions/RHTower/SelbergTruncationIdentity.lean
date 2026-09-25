import GaloisForLFunctions.RHTower.SelbergSeedUnfolding
import GaloisForLFunctions.RHTower.SelbergEisensteinCriticalLine
import GaloisForLFunctions.RHTower.EisensteinHoroballBound

open Complex UpperHalfPlane ModularGroup
open scoped MatrixGroups

/-!
# The truncation identity for the `Γ(N)` Eisenstein series on the modular cell

For `w ∈ 𝒟` every bottom row `(c, d)` with `c ≠ 0` has height `Im(w)/|cw+d|² ≤ 1` (`ht_le_one`), and the rows
`(0, ±1)` have height `Im w` (`ht_zero_row`). Hence for `Y ≥ 1` the only terms of `E_∞(σw, u)` of height above `Y`
are the `count₀(σ)` rows `(0, ±1)` at the cusp `σ∞`, when `Im w > Y`:
`E_∞(σw, u) = Σ_q [Im(qσw) ≤ Y] Im(qσw)^u + [Im w > Y] count₀(σ) (Im w)^u` (`truncation_identity`). The truncated
row sum `rowSumY` is a `Γ∞(N)\Γ(N)`-series with the seed `seedY`, so it unfolds (`seed_unfold`).
-/

namespace GaloisForLFunctions.RHTower.SelbergTruncationIdentity
open GaloisForLFunctions.RHTower.SelbergPoincare GaloisForLFunctions.RHTower.SelbergEisensteinCusp
  GaloisForLFunctions.RHTower.SelbergPoincareFourier GaloisForLFunctions.RHTower.SelbergEisensteinCuspConstant
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspRows

variable (N : ℕ) [NeZero N] (σ : SL(2, ℤ))

/-- The truncated seed `[Im w ≤ Y] Im(w)^u`. -/
noncomputable def seedY (u : ℂ) (Y : ℝ) (w : ℍ) : ℂ := if w.im ≤ Y then ((w.im : ℝ) : ℂ) ^ u else 0

/-- The truncated row sum `Σ_{q ∈ Γ∞(N)\Γ(N)} [Im(qz) ≤ Y] Im(qz)^u`. -/
noncomputable def rowSumY (u : ℂ) (Y : ℝ) (z : ℍ) : ℂ :=
  ∑' q : Cosets N, seedY u Y (((Quotient.out q : CongruenceSubgroup.Gamma N) : SL(2, ℤ)) • z)

/-- The height of the row `p` at `w`. -/
noncomputable def ht (w : ℍ) (p : ℤ × ℤ) : ℝ := w.im / Complex.normSq ((p.1 : ℂ) * (w : ℂ) + p.2)

omit [NeZero N] in
theorem im_out_smul (w : ℍ) (q : Cosets N) :
    (((Quotient.out q : CongruenceSubgroup.Gamma N) : SL(2, ℤ)) • σ • w).im = ht w (botσ N σ q) := by
  rw [← mul_smul, ModularGroup.im_smul_eq_div_normSq]
  unfold ht botσ
  congr 2

theorem esum_eq_ht (u : ℂ) (w : ℍ) (p : ℤ × ℤ) : esum u w p = ((ht w p : ℝ) : ℂ) ^ u := rfl

omit [NeZero N] in
theorem ht_le_one {w : ℍ} (hw : w ∈ fd) {p : ℤ × ℤ} (hp : p.1 ≠ 0) : ht w p ≤ 1 :=
  RHTower.im_div_normSq_le_one_of_mem_fd hw hp

omit [NeZero N] in
theorem ht_zero_row (w : ℍ) {d : ℤ} (hd : d = 1 ∨ d = -1) : ht w (0, d) = w.im := by
  unfold ht; rcases hd with rfl | rfl <;> simp

/-- **The truncation identity on the modular cell**: for `w ∈ 𝒟` and `Y ≥ 1`,
`E_∞(σw, u) = Σ_q [Im(qσw) ≤ Y] Im(qσw)^u + [Im w > Y] count₀(σ) (Im w)^u`. -/
theorem truncation_identity {u : ℂ} (hu : 1 < u.re) {w : ℍ} (hw : w ∈ fd) {Y : ℝ} (hY : 1 ≤ Y) :
    poincare N 0 u (σ • w) = rowSumY N u Y (σ • w) +
      if Y < w.im then (count0 N σ : ℂ) * ((w.im : ℝ) : ℂ) ^ u else 0 := by
  classical
  have hsum : Summable (fun q : Cosets N => esum u w (botσ N σ q)) :=
    (summable_termQ N 0 hu (σ • w)).of_norm.congr (fun q => termQ_smul N σ u w q)
  have hseed : ∀ q : Cosets N, seedY u Y (((Quotient.out q : CongruenceSubgroup.Gamma N) : SL(2, ℤ)) • σ • w) =
      if ht w (botσ N σ q) ≤ Y then esum u w (botσ N σ q) else 0 := by
    intro q; unfold seedY; rw [im_out_smul]; rfl
  have hsum2 : Summable (fun q : Cosets N => if ht w (botσ N σ q) ≤ Y then esum u w (botσ N σ q) else 0) := by
    refine Summable.of_norm_bounded hsum.norm (fun q => ?_)
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  have hP : poincare N 0 u (σ • w) = ∑' q : Cosets N, esum u w (botσ N σ q) := by
    unfold poincare; exact tsum_congr (fun q => termQ_smul N σ u w q)
  have hR : rowSumY N u Y (σ • w) =
      ∑' q : Cosets N, if ht w (botσ N σ q) ≤ Y then esum u w (botσ N σ q) else 0 := by
    unfold rowSumY; exact tsum_congr hseed
  rw [hP, hR, ← sub_eq_iff_eq_add', ← Summable.tsum_sub hsum hsum2]
  have hdiff : ∀ q : Cosets N, esum u w (botσ N σ q) - (if ht w (botσ N σ q) ≤ Y then esum u w (botσ N σ q) else 0) =
      (fun p => if Y < ht w p then esum u w p else 0) (botσ N σ q) := by
    intro q
    simp only
    split_ifs with h1 h2 h2
    · exfalso; linarith
    · simp
    · simp
    · exfalso; linarith [not_le.mp h1, not_lt.mp h2]
  simp_rw [hdiff]
  rw [← tsum_range (fun p => if Y < ht w p then esum u w p else 0) (botσ_injective N σ),
    tsum_subtype (Set.range (botσ N σ)) (fun p => if Y < ht w p then esum u w p else 0), range_botσ]
  have h2 : HasSum ((rowMul σ '' adm N).indicator (fun p => if Y < ht w p then esum u w p else 0))
      (∑ p ∈ ({((0 : ℤ), (1 : ℤ)), ((0 : ℤ), (-1 : ℤ))} : Finset (ℤ × ℤ)),
        (rowMul σ '' adm N).indicator (fun p => if Y < ht w p then esum u w p else 0) p) := by
    refine hasSum_sum_of_ne_finset_zero (fun p hp => ?_)
    by_cases hm : p ∈ rowMul σ '' adm N
    · rw [Set.indicator_of_mem hm]
      have hp1 : p.1 ≠ 0 := by
        intro h0
        have hc := GaloisForLFunctions.RHTower.SelbergEisensteinCuspConstant.coprime_of_mem N σ hm
        rw [h0] at hc
        rcases Int.isUnit_iff.mp (isCoprime_zero_left.mp hc) with h | h
        · apply hp; obtain ⟨a, b⟩ := p; simp only at h0 h; subst h0; subst h; simp
        · apply hp; obtain ⟨a, b⟩ := p; simp only at h0 h; subst h0; subst h; simp
      rw [if_neg (not_lt.mpr ((ht_le_one hw hp1).trans hY))]
    · exact Set.indicator_of_notMem hm _
  rw [h2.tsum_eq]
  have h3 : ∀ p ∈ ({((0 : ℤ), (1 : ℤ)), ((0 : ℤ), (-1 : ℤ))} : Finset (ℤ × ℤ)),
      (rowMul σ '' adm N).indicator (fun p => if Y < ht w p then esum u w p else 0) p =
        if ((0 : ℤ), p.2) ∈ rowMul σ '' adm N then (if Y < w.im then ((w.im : ℝ) : ℂ) ^ u else 0) else 0 := by
    intro p hp
    have hp' : p = ((0 : ℤ), (1 : ℤ)) ∨ p = ((0 : ℤ), (-1 : ℤ)) := by simpa using hp
    have hd : p.2 = 1 ∨ p.2 = -1 := by rcases hp' with rfl | rfl <;> simp
    have hp0 : p = ((0 : ℤ), p.2) := by rcases hp' with rfl | rfl <;> rfl
    rw [Set.indicator_apply]
    conv_lhs => rw [hp0]
    rw [esum_eq_ht, ht_zero_row w hd]
  rw [Finset.sum_congr rfl h3]
  rw [Finset.sum_pair (by simp)]
  simp only
  unfold count0
  rw [Finset.card_filter, Finset.sum_pair (by norm_num)]
  by_cases hY' : Y < w.im
  · by_cases h1 : ((0 : ℤ), (1 : ℤ)) ∈ rowMul σ '' adm N <;>
      by_cases h2 : ((0 : ℤ), (-1 : ℤ)) ∈ rowMul σ '' adm N <;>
      simp only [hY', h1, h2, if_true, if_false] <;> push_cast <;> ring
  · simp only [hY', if_false]; split_ifs <;> simp

end GaloisForLFunctions.RHTower.SelbergTruncationIdentity
