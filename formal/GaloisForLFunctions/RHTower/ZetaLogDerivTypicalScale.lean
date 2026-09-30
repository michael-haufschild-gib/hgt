import GaloisForLFunctions.RHTower.ZetaRightZeroWeightedCount
import GaloisForLFunctions.RHTower.SelbergVonMangoldtPolyTypical

/-!
# Exclusion windows of the right zeros at heights `[T, 2T]`

Let `x > 1`, `ℓ = log x`, `L = log T`, and `R > 0`. The exclusion windows
`|Im w − t| ≤ W(w) = 12R x^{3(Re w − ½)}` of the zeros `w` of the fixed rectangle
`selbergMidZeros T` with `Re w > ½ + R/2` have total length

`Σ 2W(w) ≤ (168/π) T A (1 + 9600/(RL)) e^{−RL/9600} + (144/π) (L + 3)² K x³`

for all large `T`, whenever `RL ≥ 4`, `R ≤ 1/2` and `6ℓ/L ≤ 1/4800`
(`exists_sum_selbergRightWindow_le`). The rectangle's heights `[T/2 − 1, 3T + 1]` are covered by
the three windows of the weighted count at `U = 2T − 8, 4T − 24, 8T − 56`
(`exists_windowZeros_weighted_le`), where the weight `e^{λ(Re w − ½) log U}` is `x^{3(Re w − ½)}`
for `λ = 3ℓ/log U`.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

open Sieve

/-- A zero of the residue unit has multiplicity at least one. -/
theorem one_le_zeroMult {w : ℂ} (hw : zetaResidueUnit w = 0) : 1 ≤ zeroMult w := by
  unfold zeroMult
  have hne := zetaResidueUnit_order_ne_top w
  have h0 : analyticOrderAt zetaResidueUnit w ≠ 0 := by
    rw [Ne, (analyticAt_zetaResidueUnit w).analyticOrderAt_eq_zero]
    exact fun h => h hw
  have h1 : (analyticOrderAt zetaResidueUnit w).toNat ≠ 0 := by
    intro h
    apply h0
    rw [← ENat.coe_toNat hne, h]
    rfl
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h1

theorem sum_union_le_of_nonneg {s₁ s₂ : Finset ℂ} {f : ℂ → ℝ} (hf : ∀ w, 0 ≤ f w) :
    ∑ w ∈ s₁ ∪ s₂, f w ≤ ∑ w ∈ s₁, f w + ∑ w ∈ s₂, f w := by
  classical
  have h := Finset.sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := f)
  have : 0 ≤ ∑ w ∈ s₁ ∩ s₂, f w := Finset.sum_nonneg fun w _ => hf w
  linarith

/-- **Three windows cover the right zeros of the fixed rectangle.** -/
theorem selbergMidZeros_right_subset {T v a₀ b₀ a₁ b₁ a₂ b₂ : ℝ} (hv : 0 ≤ v)
    (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hab₀ : a₀ ≤ b₀) (hab₁ : a₁ ≤ b₁)
    (hab₂ : a₂ ≤ b₂) (hlow : a₀ ≤ T / 2 - 1) (h01 : a₁ ≤ b₀) (h12 : a₂ ≤ b₁)
    (hhigh : 3 * T + 1 ≤ b₂) :
    (selbergMidZeros T).filter (fun w => 1 / 2 + v < w.re) ⊆
      ((windowZeros a₀ b₀).filter (fun w => 1 / 2 + v < w.re) ∪
        (windowZeros a₁ b₁).filter (fun w => 1 / 2 + v < w.re)) ∪
        (windowZeros a₂ b₂).filter (fun w => 1 / 2 + v < w.re) := by
  intro w hw
  obtain ⟨hwM, hwv⟩ := Finset.mem_filter.mp hw
  rw [selbergMidZeros, mem_zetaResidueUnitClosedRectangleZeros] at hwM
  obtain ⟨hrect, hG⟩ := hwM
  have hw1 : w ≠ 1 := by
    intro h; rw [h, zetaResidueUnit_one] at hG; exact one_ne_zero hG
  have hζ : riemannZeta w = 0 := (zetaResidueUnit_eq_zero_iff hw1).1 hG
  have hre1 : w.re < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hζ
  have him := (Complex.mem_reProdIm.mp hrect).2
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.im_ofNat, add_zero] at him
  have hTT : T / 2 - 1 ≤ 3 * T + 1 := by
    by_contra h
    push Not at h
    have : b₂ < a₀ := by linarith
    linarith
  rw [uIcc_of_le hTT] at him
  have hmem : ∀ {a b : ℝ}, 0 < a → a ≤ b → a ≤ w.im → w.im ≤ b →
      w ∈ (windowZeros a b).filter (fun w => 1 / 2 + v < w.re) := by
    intro a b ha hab h1 h2
    refine Finset.mem_filter.mpr ⟨(mem_windowZeros_iff ha hab w).2 ⟨?_, hζ⟩, hwv⟩
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · rw [uIcc_of_le (by norm_num)]
      exact ⟨by linarith, by linarith⟩
    · rw [uIcc_of_le hab]
      exact ⟨h1, h2⟩
  by_cases h0 : w.im ≤ b₀
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (hmem ha₀ hab₀ (by linarith [him.1]) h0))
  by_cases h1 : w.im ≤ b₁
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (hmem ha₁ hab₁ (by linarith) h1))
  · exact Finset.mem_union_right _ (hmem ha₂ hab₂ (by linarith) (by linarith [him.2]))

/-- One window of the weighted count, with the weight `x^{3(Re w − ½)}` and `v₀ = R/2`. -/
theorem window_sum_selbergRightWindow_le {A K U T x R T₁ T₂ : ℝ} (hA : 0 < A) (hK : 0 ≤ K)
    (hx : 1 < x) (hR : 0 < R) (hR2 : R ≤ 1 / 2) (hT : 8 ≤ T) (hTU : T ≤ U) (hU8 : U ≤ 8 * T)
    (hRL : 4 ≤ R * Real.log T) (hℓ : 6 * Real.log x / Real.log T ≤ 1 / 4800)
    (hP : ∀ lam v₀ : ℝ, 0 ≤ lam → 2 * lam ≤ 1 / 4800 → 2 / Real.log U ≤ v₀ → v₀ ≤ 1 / 4 →
      ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v₀ < w.re),
          zeroMult w * Real.exp (lam * (w.re - 1 / 2) * Real.log U) ≤
        U * A / (4 * Real.pi * v₀) * (1 + 4800 / (v₀ * Real.log U)) *
            Real.exp (-(v₀ * Real.log U / 4800)) +
          Real.log U * (K * Real.log U / (Real.pi * v₀) * Real.exp (lam * Real.log U))) :
    ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + R / 2 < w.re),
        zeroMult w * (2 * selbergRightWindow x R w) ≤
      12 * U * A / Real.pi * (1 + 9600 / (R * Real.log T)) *
          Real.exp (-(R * Real.log T / 9600)) +
        48 * (Real.log T + 3) ^ 2 * K * Real.exp (3 * Real.log x) / Real.pi := by
  have hT0 : 0 < T := by linarith
  have hU0 : 0 < U := by linarith
  set L := Real.log T with hLdef
  set LU := Real.log U with hLUdef
  have hL0 : 0 < L := by
    have := Real.log_pos (show (1 : ℝ) < T by linarith); linarith
  have hLLU : L ≤ LU := Real.log_le_log hT0 hTU
  have hLU3 : LU ≤ L + 3 := by
    have h1 : LU ≤ Real.log (8 * T) := Real.log_le_log hU0 hU8
    rw [Real.log_mul (by norm_num) hT0.ne'] at h1
    have h8 : Real.log 8 < 3 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)
      have h2 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9
      linarith
    linarith
  have hLU0 : 0 < LU := lt_of_lt_of_le hL0 hLLU
  have hl : 0 < Real.log x := Real.log_pos hx
  set lam : ℝ := 3 * Real.log x / LU with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hlam2 : 2 * lam ≤ 1 / 4800 := by
    have : 2 * lam ≤ 6 * Real.log x / L := by
      rw [hlam, show 2 * (3 * Real.log x / LU) = 6 * Real.log x / LU by ring]
      exact div_le_div_of_nonneg_left (by positivity) hL0 hLLU
    linarith
  have hv1 : 2 / LU ≤ R / 2 := by
    rw [div_le_iff₀ hLU0]
    nlinarith
  have hbound := hP lam (R / 2) hlam0 hlam2 hv1 (by linarith)
  have hweight : ∀ w : ℂ, zeroMult w * (2 * selbergRightWindow x R w) =
      24 * R * (zeroMult w * Real.exp (lam * (w.re - 1 / 2) * LU)) := by
    intro w
    unfold selbergRightWindow
    have : lam * (w.re - 1 / 2) * LU = 3 * (w.re - 1 / 2) * Real.log x := by
      rw [hlam]; field_simp
    rw [this]; ring
  simp_rw [hweight]
  rw [← Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left hbound (by positivity)).trans ?_
  have hlamLU : lam * LU = 3 * Real.log x := by rw [hlam]; field_simp
  rw [hlamLU]
  have hfac1 : 1 + 4800 / (R / 2 * LU) ≤ 1 + 9600 / (R * L) := by
    have : 4800 / (R / 2 * LU) = 9600 / (R * LU) := by field_simp; ring
    rw [this]
    have := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 9600 by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hLLU hR.le)
    linarith
  have hexp1 : Real.exp (-(R / 2 * LU / 4800)) ≤ Real.exp (-(R * L / 9600)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hLLU hR.le
    linarith
  have hLUsq : LU * LU ≤ (L + 3) ^ 2 := by nlinarith
  have hx3 : 0 ≤ Real.exp (3 * Real.log x) := (Real.exp_pos _).le
  have e1 : 24 * R * (U * A / (4 * Real.pi * (R / 2)) * (1 + 4800 / (R / 2 * LU)) *
      Real.exp (-(R / 2 * LU / 4800))) =
      12 * U * A / Real.pi * (1 + 4800 / (R / 2 * LU)) * Real.exp (-(R / 2 * LU / 4800)) := by
    field_simp; ring
  have e2 : 24 * R * (LU * (K * LU / (Real.pi * (R / 2)) * Real.exp (3 * Real.log x))) =
      48 * (LU * LU) * K * Real.exp (3 * Real.log x) / Real.pi := by
    field_simp; ring
  rw [mul_add, e1, e2]
  have hc : 0 ≤ 12 * U * A / Real.pi := by positivity
  have hA1 : 12 * U * A / Real.pi * (1 + 4800 / (R / 2 * LU)) * Real.exp (-(R / 2 * LU / 4800)) ≤
      12 * U * A / Real.pi * (1 + 9600 / (R * L)) * Real.exp (-(R * L / 9600)) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hfac1 hc) hexp1 (Real.exp_pos _).le
    exact mul_nonneg hc (by positivity)
  have hA2 : 48 * (LU * LU) * K * Real.exp (3 * Real.log x) / Real.pi ≤
      48 * (L + 3) ^ 2 * K * Real.exp (3 * Real.log x) / Real.pi := by
    apply div_le_div_of_nonneg_right _ Real.pi_pos.le
    have := mul_le_mul_of_nonneg_right hLUsq (mul_nonneg hK hx3)
    nlinarith
  linarith

/-- **Total length of the exclusion windows.** -/
theorem exists_sum_selbergRightWindow_le :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ T in atTop, ∀ x R : ℝ, 1 < x → 0 < R → R ≤ 1 / 2 →
      4 ≤ R * Real.log T → 6 * Real.log x / Real.log T ≤ 1 / 4800 →
      ∑ w ∈ (selbergMidZeros T).filter (fun w => 1 / 2 + R / 2 < w.re),
          2 * selbergRightWindow x R w ≤
        168 * T * A / Real.pi * (1 + 9600 / (R * Real.log T)) *
            Real.exp (-(R * Real.log T / 9600)) +
          144 * (Real.log T + 3) ^ 2 * K * Real.exp (3 * Real.log x) / Real.pi := by
  obtain ⟨A, K, hA, hK, hev⟩ := exists_windowZeros_weighted_le
  refine ⟨A, K, hA, hK, ?_⟩
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hev
  filter_upwards [eventually_ge_atTop (max U₀ 64)] with T hT x R hx hR hR2 hRL hℓ
  have hT64 : 64 ≤ T := le_of_max_le_right hT
  have hTU₀ : U₀ ≤ T := le_of_max_le_left hT
  obtain ⟨a₀, ha₀, b₀, hb₀, hP₀⟩ := hU₀ (2 * T - 8) (by linarith)
  obtain ⟨a₁, ha₁, b₁, hb₁, hP₁⟩ := hU₀ (4 * T - 24) (by linarith)
  obtain ⟨a₂, ha₂, b₂, hb₂, hP₂⟩ := hU₀ (8 * T - 56) (by linarith)
  have hsub := selbergMidZeros_right_subset (T := T) (v := R / 2) (a₀ := a₀) (b₀ := b₀)
    (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂) (by linarith)
    (by linarith [ha₀.1]) (by linarith [ha₁.1]) (by linarith [ha₂.1])
    (by linarith [ha₀.2, hb₀.1]) (by linarith [ha₁.2, hb₁.1]) (by linarith [ha₂.2, hb₂.1])
    (by linarith [ha₀.2]) (by linarith [ha₁.2, hb₀.1]) (by linarith [ha₂.2, hb₁.1])
    (by linarith [hb₂.1])
  have hf : ∀ w, 0 ≤ zeroMult w * (2 * selbergRightWindow x R w) := fun w =>
    mul_nonneg (zeroMult_nonneg w) (by have := selbergRightWindow_pos (x := x) hR w; positivity)
  have hmult : ∑ w ∈ (selbergMidZeros T).filter (fun w => 1 / 2 + R / 2 < w.re),
      2 * selbergRightWindow x R w ≤
      ∑ w ∈ (selbergMidZeros T).filter (fun w => 1 / 2 + R / 2 < w.re),
        zeroMult w * (2 * selbergRightWindow x R w) := by
    refine Finset.sum_le_sum fun w hw => ?_
    have hw' := (Finset.mem_filter.mp hw).1
    rw [selbergMidZeros, mem_zetaResidueUnitClosedRectangleZeros] at hw'
    have h1 := one_le_zeroMult hw'.2
    have := selbergRightWindow_pos (x := x) hR w
    nlinarith
  refine hmult.trans ((Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ => hf w).trans ?_)
  refine (sum_union_le_of_nonneg hf).trans ?_
  have h0 := window_sum_selbergRightWindow_le hA hK hx hR hR2 (by linarith) (by linarith)
    (by linarith) hRL hℓ hP₀
  have h1 := window_sum_selbergRightWindow_le hA hK hx hR hR2 (by linarith) (by linarith)
    (by linarith) hRL hℓ hP₁
  have h2 := window_sum_selbergRightWindow_le hA hK hx hR hR2 (by linarith) (by linarith)
    (by linarith) hRL hℓ hP₂
  have h01 := sum_union_le_of_nonneg (s₁ := (windowZeros a₀ b₀).filter
    (fun w => 1 / 2 + R / 2 < w.re)) (s₂ := (windowZeros a₁ b₁).filter
    (fun w => 1 / 2 + R / 2 < w.re)) hf
  have hc : 0 ≤ A / Real.pi * (1 + 9600 / (R * Real.log T)) *
      Real.exp (-(R * Real.log T / 9600)) := by
    have : 0 < R * Real.log T := by linarith
    positivity
  have e : ∀ U : ℝ, 12 * U * A / Real.pi * (1 + 9600 / (R * Real.log T)) *
      Real.exp (-(R * Real.log T / 9600)) = 12 * U * (A / Real.pi * (1 + 9600 / (R * Real.log T)) *
      Real.exp (-(R * Real.log T / 9600))) := fun U => by ring
  rw [e] at h0 h1 h2
  have e2 : 168 * T * A / Real.pi * (1 + 9600 / (R * Real.log T)) *
      Real.exp (-(R * Real.log T / 9600)) = 168 * T * (A / Real.pi * (1 + 9600 / (R * Real.log T)) *
      Real.exp (-(R * Real.log T / 9600))) := by ring
  rw [e2]
  set c := A / Real.pi * (1 + 9600 / (R * Real.log T)) * Real.exp (-(R * Real.log T / 9600))
  set E := 48 * (Real.log T + 3) ^ 2 * K * Real.exp (3 * Real.log x) / Real.pi with hE
  have hE3 : 144 * (Real.log T + 3) ^ 2 * K * Real.exp (3 * Real.log x) / Real.pi = 3 * E := by
    rw [hE]; ring
  rw [hE3]
  have hsum : 12 * (2 * T - 8) * c + 12 * (4 * T - 24) * c + 12 * (8 * T - 56) * c ≤ 168 * T * c := by
    nlinarith
  linarith

end RHTower
