import GaloisForLFunctions.RHTower.Sieve.GuthMaynardCubicTermIntegral
import GaloisForLFunctions.RHTower.ChenGuptaLiHtAllOrder

/-!
# The sum `S₃` and its truncation to `|m_i| ≤ T^{1+η}/N` (Guth–Maynard (7.1))

`S₃ = Σ_{m ∈ ℤ³, m₁m₂m₃ ≠ 0} I_m` (`allNonzeroCubicSum`). For `W ⊂ [0, T]` every difference
`t − t'` has `|t − t'| ≤ T`, so Lemma 4.3 (`cglSmoothBumpHt_allOrder_fourier_decay`,
`|ξ|^n |ĥ_t(ξ)| ≤ B_n (1+|t|)^n`) gives for `k ≠ 0`

`|ĥ_{t−t'}(kN)| ≤ B_j ((1+T)/(|k|N))^j ≤ B_j ((1+T)/N)² k^{−2} ((1+T)/(RN))^{j−2}`   (`|k| ≥ R`).

Hence `|I_m| ≤ N³|W|³ B³ ((1+T)/N)⁶ ∏ m_i^{−2}`, which is summable over `ℤ³`, and outside the box
`0 < |m_i| ≤ K` one coordinate has `|m_i| ≥ K + 1` and contributes the extra factor
`((1+T)/((K+1)N))^{j−2}`. With `K = ⌊T^{1+η}/N⌋` this factor is `≤ (2T^{−η})^{j−2}`, which proves
(7.1): `S₃ = Σ_{0<|m_i|≤T^{1+η}/N} I_m + O(|W|³ T^{−A})` for every `A` (`allNonzeroCubicSum_truncation`).
-/

set_option autoImplicit false

open MeasureTheory Set

namespace RHTower.GuthMaynard

noncomputable section

/-- `S₃ = Σ_{m ∈ ℤ³, m₁m₂m₃ ≠ 0} I_m`. -/
def allNonzeroCubicSum (w : CGLSmoothBump) (W : Finset ℝ) (N : ℝ) : ℂ :=
  ∑' m : ℤ × ℤ × ℤ, if m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then cubicTerm w W N m.1 m.2.1 m.2.2 else 0

/-- The frequency box `{m ∈ ℤ³ : 0 < |m_i| ≤ K}`. -/
def nonzeroFrequencyBox (K : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-(K : ℤ)) K ×ˢ (Finset.Icc (-(K : ℤ)) K ×ˢ Finset.Icc (-(K : ℤ)) K)).filter
    fun m => m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0

theorem mem_nonzeroFrequencyBox {K : ℕ} {m : ℤ × ℤ × ℤ} :
    m ∈ nonzeroFrequencyBox K ↔ (m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0) ∧
      |m.1| ≤ K ∧ |m.2.1| ≤ K ∧ |m.2.2| ≤ K := by
  simp only [nonzeroFrequencyBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, abs_le]
  tauto

/-- The Lemma 4.3 constant: `|ξ|^n |ĥ_t(ξ)| ≤ B_n (1 + |t|)^n`. -/
def bumpDecayConstant (w : CGLSmoothBump) (n : ℕ) : ℝ :=
  cglSmoothBumpHtAllOrderBudget w n / (2 * Real.pi) ^ n

theorem bumpDecayConstant_nonneg (w : CGLSmoothBump) (n : ℕ) : 0 ≤ bumpDecayConstant w n := by
  unfold bumpDecayConstant cglSmoothBumpHtAllOrderBudget
  refine div_nonneg (Finset.sum_nonneg fun i _ => ?_) (by positivity)
  exact mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)

/-- `|ĥ_d(kN)| ≤ B_n ((1+T)/(|k|N))^n` for `|d| ≤ T`, `k ≠ 0`. -/
theorem norm_bumpFourier_int_le (w : CGLSmoothBump) {T N d : ℝ} (hN : 0 < N) (hd : |d| ≤ T)
    {k : ℤ} (hk : k ≠ 0) (n : ℕ) :
    ‖bumpFourier w d (k * N)‖ ≤ bumpDecayConstant w n * ((1 + T) / (|(k : ℝ)| * N)) ^ n := by
  have hk' : 0 < |(k : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hk)
  have hξ : 0 < |(k : ℝ)| * N := mul_pos hk' hN
  have h := cglSmoothBumpHt_allOrder_fourier_decay w n d (k * N)
  rw [abs_mul, abs_of_pos hN] at h
  rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos hξ n), mul_comm]
  calc (|(k : ℝ)| * N) ^ n * ‖bumpFourier w d (k * N)‖
      ≤ cglSmoothBumpHtAllOrderBudget w n / (2 * Real.pi) ^ n * (1 + |d|) ^ n := h
    _ ≤ bumpDecayConstant w n * (1 + T) ^ n := by
      unfold bumpDecayConstant
      gcongr
      · exact div_nonneg (by
          unfold cglSmoothBumpHtAllOrderBudget
          exact Finset.sum_nonneg fun i _ =>
            mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)) (by positivity)

/-- `|ĥ_d(kN)| ≤ B_j ((1+T)/N)² k^{−2} ((1+T)/(RN))^{j−2}` for `|d| ≤ T`, `|k| ≥ R > 0`, `j ≥ 2`. -/
theorem norm_bumpFourier_int_le_sq (w : CGLSmoothBump) {T N d : ℝ} (hT : 0 ≤ T) (hN : 0 < N)
    (hd : |d| ≤ T) {k : ℤ} (hk : k ≠ 0) {j : ℕ} (hj : 2 ≤ j) {R : ℝ} (hR : 0 < R)
    (hkR : R ≤ |(k : ℝ)|) :
    ‖bumpFourier w d (k * N)‖ ≤
      bumpDecayConstant w j * (((1 + T) / N) ^ 2 * (1 / (k : ℝ) ^ 2)) *
        ((1 + T) / (R * N)) ^ (j - 2) := by
  refine (norm_bumpFourier_int_le w hN hd hk j).trans ?_
  have hk' : 0 < |(k : ℝ)| := hR.trans_le hkR
  set y := (1 + T) / (|(k : ℝ)| * N) with hy
  have hy0 : 0 ≤ y := by positivity
  have hyR : y ≤ (1 + T) / (R * N) := by
    rw [hy]; gcongr
  have hsq : y ^ 2 = ((1 + T) / N) ^ 2 * (1 / (k : ℝ) ^ 2) := by
    rw [hy, div_pow, mul_pow, sq_abs]; field_simp
  calc bumpDecayConstant w j * y ^ j = bumpDecayConstant w j * (y ^ 2 * y ^ (j - 2)) := by
        rw [← pow_add, Nat.add_sub_cancel' hj]
    _ ≤ bumpDecayConstant w j * (y ^ 2 * ((1 + T) / (R * N)) ^ (j - 2)) := by
        have := bumpDecayConstant_nonneg w j
        gcongr
    _ = _ := by rw [hsq]; ring

/-- Product bound: if each factor `|ĥ_{t−t'}(m_iN)|` is at most `a_i`, then
`|I_m| ≤ N³ |W|³ a₁a₂a₃`. -/
theorem norm_cubicTerm_le_of_forall (w : CGLSmoothBump) (W : Finset ℝ) {N : ℝ} (hN : 0 ≤ N)
    (m₁ m₂ m₃ : ℤ) {a₁ a₂ a₃ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (h₁ : ∀ t ∈ W, ∀ t' ∈ W, ‖bumpFourier w (t - t') (m₁ * N)‖ ≤ a₁)
    (h₂ : ∀ t ∈ W, ∀ t' ∈ W, ‖bumpFourier w (t - t') (m₂ * N)‖ ≤ a₂)
    (h₃ : ∀ t ∈ W, ∀ t' ∈ W, ‖bumpFourier w (t - t') (m₃ * N)‖ ≤ a₃) :
    ‖cubicTerm w W N m₁ m₂ m₃‖ ≤ N ^ 3 * (W.card : ℝ) ^ 3 * (a₁ * a₂ * a₃) := by
  unfold cubicTerm
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hN, mul_assoc]
  gcongr
  calc ‖∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, bumpFourier w (t₁ - t₂) (m₁ * N) *
        bumpFourier w (t₂ - t₃) (m₂ * N) * bumpFourier w (t₃ - t₁) (m₃ * N)‖
      ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, a₁ * a₂ * a₃ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t₁ ht₁ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t₂ ht₂ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t₃ ht₃ => ?_)
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul (h₁ t₁ ht₁ t₂ ht₂) (h₂ t₂ ht₂ t₃ ht₃) (norm_nonneg _) ha₁)
          (h₃ t₃ ht₃ t₁ ht₁) (norm_nonneg _) (mul_nonneg ha₁ ha₂)
    _ = (W.card : ℝ) ^ 3 * (a₁ * a₂ * a₃) := by
        simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- The summable majorant `m ↦ m₁^{−2} m₂^{−2} m₃^{−2}` on `ℤ³`. -/
def inverseSquareTriple (m : ℤ × ℤ × ℤ) : ℝ :=
  1 / (m.1 : ℝ) ^ 2 * (1 / (m.2.1 : ℝ) ^ 2 * (1 / (m.2.2 : ℝ) ^ 2))

theorem inverseSquareTriple_nonneg (m : ℤ × ℤ × ℤ) : 0 ≤ inverseSquareTriple m := by
  unfold inverseSquareTriple; positivity

theorem summable_inverseSquareTriple : Summable inverseSquareTriple := by
  have h : Summable fun k : ℤ => 1 / (k : ℝ) ^ 2 := Real.summable_one_div_int_pow.mpr one_lt_two
  have h0 : 0 ≤ fun k : ℤ => 1 / (k : ℝ) ^ 2 := fun k => by positivity
  exact h.mul_of_nonneg (h.mul_of_nonneg h h0 h0) h0
    (fun p => mul_nonneg (h0 p.1) (h0 p.2))

/-- Pointwise bound on `I_m` for `W ⊂ [0, T]`, all `m_i ≠ 0`, with the extra decay factor `ρ`
whenever one coordinate satisfies `|m_i| ≥ R`. -/
theorem norm_cubicTerm_le_inverseSquare (w : CGLSmoothBump) {T N : ℝ} (hT : 0 ≤ T) (hN : 0 < N)
    {W : Finset ℝ} (hW : ∀ t ∈ W, t ∈ Icc 0 T) {j : ℕ} (hj : 2 ≤ j) {R : ℝ} (hR : 1 ≤ R)
    {m : ℤ × ℤ × ℤ} (hm : m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0)
    (hbig : R ≤ |(m.1 : ℝ)| ∨ R ≤ |(m.2.1 : ℝ)| ∨ R ≤ |(m.2.2 : ℝ)|) :
    ‖cubicTerm w W N m.1 m.2.1 m.2.2‖ ≤
      N ^ 3 * (W.card : ℝ) ^ 3 * (bumpDecayConstant w 2 + bumpDecayConstant w j) ^ 3 *
        ((1 + T) / N) ^ 6 * ((1 + T) / (R * N)) ^ (j - 2) * inverseSquareTriple m := by
  obtain ⟨h1, h2, h3⟩ := hm
  set B := bumpDecayConstant w 2 + bumpDecayConstant w j with hB
  have hB2 : bumpDecayConstant w 2 ≤ B := by
    have := bumpDecayConstant_nonneg w j; linarith
  have hBj : bumpDecayConstant w j ≤ B := by
    have := bumpDecayConstant_nonneg w 2; linarith
  have hB0 : 0 ≤ B := (bumpDecayConstant_nonneg w 2).trans hB2
  have hdiff : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T := fun t ht t' ht' => by
    have := hW t ht; have := hW t' ht'
    rw [abs_le]; constructor <;> linarith [(hW t ht).1, (hW t ht).2, (hW t' ht').1, (hW t' ht').2]
  set x : ℤ → ℝ := fun k => ((1 + T) / N) ^ 2 * (1 / (k : ℝ) ^ 2) with hx
  set ρ := ((1 + T) / (R * N)) ^ (j - 2) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hx0 : ∀ k, 0 ≤ x k := fun k => by positivity
  -- every factor: `≤ B x_k`; a factor with `|k| ≥ R`: `≤ B x_k ρ`
  have hsmall : ∀ {k : ℤ}, k ≠ 0 → ∀ t ∈ W, ∀ t' ∈ W,
      ‖bumpFourier w (t - t') (k * N)‖ ≤ B * x k := fun {k} hk t ht t' ht' => by
    have := norm_bumpFourier_int_le_sq w hT hN (hdiff t ht t' ht') hk le_rfl one_pos
      (by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk)
    simp only [Nat.sub_self, pow_zero, mul_one] at this
    exact this.trans (mul_le_mul_of_nonneg_right hB2 (hx0 k))
  have hlarge : ∀ {k : ℤ}, k ≠ 0 → R ≤ |(k : ℝ)| → ∀ t ∈ W, ∀ t' ∈ W,
      ‖bumpFourier w (t - t') (k * N)‖ ≤ B * x k * ρ := fun {k} hk hkR t ht t' ht' => by
    have := norm_bumpFourier_int_le_sq w hT hN (hdiff t ht t' ht') hk hj
      (by linarith : (0 : ℝ) < R) hkR
    exact this.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBj (hx0 k)) hρ0)
  have hprod : x m.1 * x m.2.1 * x m.2.2 = ((1 + T) / N) ^ 6 * inverseSquareTriple m := by
    simp only [hx, inverseSquareTriple]; ring
  have hfinal : ∀ a₁ a₂ a₃ : ℝ, a₁ * a₂ * a₃ = B ^ 3 * ρ * (x m.1 * x m.2.1 * x m.2.2) →
      N ^ 3 * (W.card : ℝ) ^ 3 * (a₁ * a₂ * a₃) =
        N ^ 3 * (W.card : ℝ) ^ 3 * B ^ 3 * ((1 + T) / N) ^ 6 * ρ * inverseSquareTriple m := by
    intro a₁ a₂ a₃ h; rw [h, hprod]; ring
  rcases hbig with hb | hb | hb
  · refine (norm_cubicTerm_le_of_forall w W hN.le _ _ _ (by positivity) (by positivity)
      (hlarge h1 hb) (hsmall h2) (hsmall h3)).trans (le_of_eq ?_)
    exact hfinal _ _ _ (by ring)
  · refine (norm_cubicTerm_le_of_forall w W hN.le _ _ _ (by positivity) (by positivity)
      (hsmall h1) (hlarge h2 hb) (hsmall h3)).trans (le_of_eq ?_)
    exact hfinal _ _ _ (by ring)
  · refine (norm_cubicTerm_le_of_forall w W hN.le _ _ _ (by positivity) (by positivity)
      (hsmall h1) (hsmall h2) (hlarge h3 hb)).trans (le_of_eq ?_)
    exact hfinal _ _ _ (by ring)

/-- The summand of `S₃`. -/
def allNonzeroCubicSummand (w : CGLSmoothBump) (W : Finset ℝ) (N : ℝ) (m : ℤ × ℤ × ℤ) : ℂ :=
  if m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then cubicTerm w W N m.1 m.2.1 m.2.2 else 0

/-- **Truncation of `S₃`, explicit form.** For `W ⊂ [0, T]`, `N > 0`, `j ≥ 2` and every box size `K`:
`|S₃ − Σ_{0<|m_i|≤K} I_m| ≤ C N³ |W|³ ((1+T)/N)⁶ ((1+T)/((K+1)N))^{j−2}`; the series `S₃` converges
absolutely. -/
theorem norm_allNonzeroCubicSum_sub_box_le (w : CGLSmoothBump) {j : ℕ} (hj : 2 ≤ j) :
    ∃ C, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ) (K : ℕ), 0 ≤ T → 0 < N →
      (∀ t ∈ W, t ∈ Icc 0 T) →
      ‖allNonzeroCubicSum w W N -
          ∑ m ∈ nonzeroFrequencyBox K, cubicTerm w W N m.1 m.2.1 m.2.2‖ ≤
        C * N ^ 3 * (W.card : ℝ) ^ 3 * ((1 + T) / N) ^ 6 * ((1 + T) / ((K + 1) * N)) ^ (j - 2) := by
  set B := bumpDecayConstant w 2 + bumpDecayConstant w j
  have hB0 : 0 ≤ B := add_nonneg (bumpDecayConstant_nonneg w 2) (bumpDecayConstant_nonneg w j)
  set Z := ∑' m, inverseSquareTriple m
  have hZ0 : 0 ≤ Z := tsum_nonneg inverseSquareTriple_nonneg
  refine ⟨B ^ 3 * Z, by positivity, fun T N W K hT hN hW => ?_⟩
  set f := allNonzeroCubicSummand w W N with hf
  set c := N ^ 3 * (W.card : ℝ) ^ 3 * B ^ 3 * ((1 + T) / N) ^ 6 with hc
  have hc0 : 0 ≤ c := by positivity
  set ρ := ((1 + T) / ((K + 1) * N)) ^ (j - 2) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  -- the general bound (`R = 1`, no extra decay)
  have hgen : ∀ m, ‖f m‖ ≤ c * ((1 + T) / (1 * N)) ^ (j - 2) * inverseSquareTriple m := by
    intro m
    simp only [hf, allNonzeroCubicSummand]
    split_ifs with hm
    · have h1 : (1 : ℝ) ≤ |(m.1 : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm.1
      refine (norm_cubicTerm_le_inverseSquare w hT hN hW hj le_rfl hm (Or.inl h1)).trans
        (le_of_eq ?_)
      rw [hc]
    · simp only [norm_zero]
      exact mul_nonneg (mul_nonneg hc0 (by positivity)) (inverseSquareTriple_nonneg m)
  have hfs : Summable f := Summable.of_norm_bounded
    (summable_inverseSquareTriple.mul_left _) hgen
  -- split off the box
  set fin : ℤ × ℤ × ℤ → ℂ := fun m => if m ∈ nonzeroFrequencyBox K then f m else 0 with hfin
  set fout : ℤ × ℤ × ℤ → ℂ := fun m => if m ∈ nonzeroFrequencyBox K then 0 else f m with hfout
  have hsplit : ∀ m, f m = fin m + fout m := fun m => by
    simp only [hfin, hfout]; split_ifs <;> simp
  have hfin_sum : ∑' m, fin m = ∑ m ∈ nonzeroFrequencyBox K, cubicTerm w W N m.1 m.2.1 m.2.2 := by
    rw [tsum_eq_sum (s := nonzeroFrequencyBox K) fun m hm => by simp [hfin, hm]]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := (mem_nonzeroFrequencyBox.mp hm).1
    simp [hfin, hm, hf, allNonzeroCubicSummand, hm'.1, hm'.2.1, hm'.2.2]
  have hfin_s : Summable fin := summable_of_ne_finset_zero (s := nonzeroFrequencyBox K)
    fun m hm => by simp [hfin, hm]
  have hout_bound : ∀ m, ‖fout m‖ ≤ c * ρ * inverseSquareTriple m := by
    intro m
    simp only [hfout]
    split_ifs with hbox
    · simp only [norm_zero]; exact mul_nonneg (mul_nonneg hc0 hρ0) (inverseSquareTriple_nonneg m)
    · simp only [hf, allNonzeroCubicSummand]
      split_ifs with hm
      · have hout : (K : ℝ) + 1 ≤ |(m.1 : ℝ)| ∨ (K : ℝ) + 1 ≤ |(m.2.1 : ℝ)| ∨
            (K : ℝ) + 1 ≤ |(m.2.2 : ℝ)| := by
          have : ¬ (|m.1| ≤ K ∧ |m.2.1| ≤ K ∧ |m.2.2| ≤ K) := fun h =>
            hbox (mem_nonzeroFrequencyBox.mpr ⟨hm, h⟩)
          simp only [not_and_or, not_le] at this
          rcases this with h | h | h
          · left; rw [← Int.cast_abs]; exact_mod_cast h
          · right; left; rw [← Int.cast_abs]; exact_mod_cast h
          · right; right; rw [← Int.cast_abs]; exact_mod_cast h
        refine (norm_cubicTerm_le_inverseSquare w hT hN hW hj (by linarith [K.cast_nonneg' (α := ℝ)])
          hm hout).trans (le_of_eq ?_)
        rw [hc, hρ]
      · simp only [norm_zero]
        exact mul_nonneg (mul_nonneg hc0 hρ0) (inverseSquareTriple_nonneg m)
  have hfout_s : Summable fun m => ‖fout m‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    hout_bound (summable_inverseSquareTriple.mul_left _)
  have htotal : allNonzeroCubicSum w W N = ∑' m, fin m + ∑' m, fout m := by
    rw [← (hfin_s.tsum_add (hfout_s.of_norm))]
    exact tsum_congr hsplit
  rw [htotal, hfin_sum, add_sub_cancel_left]
  calc ‖∑' m, fout m‖ ≤ ∑' m, ‖fout m‖ := norm_tsum_le_tsum_norm hfout_s
    _ ≤ ∑' m, c * ρ * inverseSquareTriple m :=
        hfout_s.tsum_le_tsum hout_bound (summable_inverseSquareTriple.mul_left _)
    _ = c * ρ * Z := tsum_mul_left
    _ = B ^ 3 * Z * N ^ 3 * (W.card : ℝ) ^ 3 * ((1 + T) / N) ^ 6 *
          ((1 + T) / ((K + 1) * N)) ^ (j - 2) := by rw [hc, hρ]; ring

/-- `S₃` is an absolutely convergent series. -/
theorem summable_allNonzeroCubicSummand (w : CGLSmoothBump) {T N : ℝ} (hT : 0 ≤ T) (hN : 0 < N)
    {W : Finset ℝ} (hW : ∀ t ∈ W, t ∈ Icc 0 T) :
    Summable fun m => ‖allNonzeroCubicSummand w W N m‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
    (summable_inverseSquareTriple.mul_left
      (N ^ 3 * (W.card : ℝ) ^ 3 * (bumpDecayConstant w 2 + bumpDecayConstant w 2) ^ 3 *
        ((1 + T) / N) ^ 6 * ((1 + T) / (1 * N)) ^ (2 - 2)))
  unfold allNonzeroCubicSummand
  split_ifs with hm
  · have h1 : (1 : ℝ) ≤ |(m.1 : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm.1
    exact norm_cubicTerm_le_inverseSquare w hT hN hW le_rfl le_rfl hm (Or.inl h1)
  · simp only [norm_zero]
    have := bumpDecayConstant_nonneg w 2
    exact mul_nonneg (by positivity) (inverseSquareTriple_nonneg m)

/-- **Guth–Maynard (7.1).** For every `η > 0` and `A` there is `C` such that for `T ≥ 1`,
`1 ≤ N`, `W ⊂ [0, T]`: `|S₃ − Σ_{0<|m_i|≤T^{1+η}/N} I_m| ≤ C |W|³ T^{−A}`. -/
theorem allNonzeroCubicSum_truncation (w : CGLSmoothBump) {η : ℝ} (hη : 0 < η) (A : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ), 1 ≤ T → 1 ≤ N → (∀ t ∈ W, t ∈ Icc 0 T) →
      ‖allNonzeroCubicSum w W N -
          ∑ m ∈ nonzeroFrequencyBox ⌊T ^ (1 + η) / N⌋₊, cubicTerm w W N m.1 m.2.1 m.2.2‖ ≤
        C * (W.card : ℝ) ^ 3 * T ^ (-A) := by
  set n : ℕ := ⌈(A + 6) / η⌉₊ with hn
  obtain ⟨C, hC, hbound⟩ := norm_allNonzeroCubicSum_sub_box_le w (j := n + 2) (by omega)
  refine ⟨C * 64 * 2 ^ n, by positivity, fun T N W hT hN hW => ?_⟩
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  set K := ⌊T ^ (1 + η) / N⌋₊
  refine (hbound T N W K hT0.le hN0 hW).trans ?_
  simp only [Nat.add_sub_cancel] at *
  -- `(1+T)/N ≤ 2T` and `(1+T)/((K+1)N) ≤ 2T^{−η}`
  have h1 : (1 + T) / N ≤ 2 * T := by
    rw [div_le_iff₀ hN0]; nlinarith
  have hKN : T ^ (1 + η) ≤ ((K : ℝ) + 1) * N := by
    have := Nat.lt_floor_add_one (T ^ (1 + η) / N)
    rw [div_lt_iff₀ hN0] at this; linarith
  have hTη : T ^ (1 + η) = T * T ^ η := by
    rw [Real.rpow_add hT0, Real.rpow_one]
  have h2 : (1 + T) / ((K + 1) * N) ≤ 2 * T ^ (-η) := by
    have hpos : 0 < ((K : ℝ) + 1) * N := by positivity
    rw [div_le_iff₀ hpos, Real.rpow_neg hT0.le]
    have hTη0 : 0 < T ^ η := Real.rpow_pos_of_pos hT0 η
    calc 1 + T ≤ 2 * T := by linarith
      _ = 2 * (T ^ η)⁻¹ * (T * T ^ η) := by field_simp
      _ ≤ 2 * (T ^ η)⁻¹ * (((K : ℝ) + 1) * N) := by rw [← hTη]; gcongr
  have hN3 : N ^ 3 * ((1 + T) / N) ^ 6 ≤ 64 * T ^ 6 := by
    have : N ^ 3 * ((1 + T) / N) ^ 6 = (1 + T) ^ 6 / N ^ 3 := by field_simp
    rw [this, div_le_iff₀ (by positivity)]
    have hN3' : 1 ≤ N ^ 3 := one_le_pow₀ hN
    have : (1 + T) ^ 6 ≤ (2 * T) ^ 6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
    nlinarith [pow_pos hT0 6]
  have hρ : ((1 + T) / ((K + 1) * N)) ^ n ≤ 2 ^ n * T ^ (-(η * n)) := by
    calc ((1 + T) / ((K + 1) * N)) ^ n ≤ (2 * T ^ (-η)) ^ n :=
          pow_le_pow_left₀ (by positivity) h2 n
      _ = 2 ^ n * T ^ (-(η * n)) := by
          rw [mul_pow, ← Real.rpow_natCast (T ^ (-η)), ← Real.rpow_mul hT0.le]; ring_nf
  -- `T^6 T^{−ηn} ≤ T^{−A}`
  have hexp : T ^ (6 : ℝ) * T ^ (-(η * n)) ≤ T ^ (-A) := by
    rw [← Real.rpow_add hT0]
    apply Real.rpow_le_rpow_of_exponent_le hT
    have := Nat.le_ceil ((A + 6) / η)
    rw [div_le_iff₀ hη] at this
    rw [← hn] at this
    linarith
  have hT6 : T ^ (6 : ℝ) = T ^ 6 := by exact_mod_cast Real.rpow_natCast T 6
  rw [hT6] at hexp
  have hW3 : (0 : ℝ) ≤ (W.card : ℝ) ^ 3 := by positivity
  calc C * N ^ 3 * (W.card : ℝ) ^ 3 * ((1 + T) / N) ^ 6 * ((1 + T) / ((K + 1) * N)) ^ n
      = C * (W.card : ℝ) ^ 3 * (N ^ 3 * ((1 + T) / N) ^ 6) *
          ((1 + T) / ((K + 1) * N)) ^ n := by ring
    _ ≤ C * (W.card : ℝ) ^ 3 * (64 * T ^ 6) * (2 ^ n * T ^ (-(η * n))) := by gcongr
    _ = C * 64 * 2 ^ n * (W.card : ℝ) ^ 3 * (T ^ 6 * T ^ (-(η * n))) := by ring
    _ ≤ C * 64 * 2 ^ n * (W.card : ℝ) ^ 3 * T ^ (-A) := by gcongr

end

end RHTower.GuthMaynard
