import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.PeriodicShellWindows

/-!
# Complete shell rows and their polar mass

An integer window containing the entire logarithmic kernel support lies in
`[n/2,2n]`. Periodic cancellation bounds its mean-zero rows, including a
logarithmic weight, by a reciprocal-index error. The constant row has the
same continuum mass as the pole; lattice quadrature retains an error
`Oφ(G/n)`, uniformly when the shell width satisfies `wn≥1/2`.
-/

open MeasureTheory Finset Filter Topology intervalIntegral
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
noncomputable section

/-- Integer cells containing the support of a logarithmic shell row. -/
def shellWindowLower (n : ℕ) (w : ℝ) : ℕ := Nat.floor ((n : ℝ) * Real.exp (-w))
def shellWindowUpper (n : ℕ) (w : ℝ) : ℕ := Nat.floor ((n : ℝ) * Real.exp w) + 1

theorem shellWindow_geometry {n : ℕ} (hn : 4 ≤ n) {w : ℝ}
    (hw : 0 < w) (hw4 : w ≤ 1 / 4) :
    1 ≤ shellWindowLower n w ∧
    (n : ℝ) / 2 ≤ shellWindowLower n w ∧
    (shellWindowLower n w : ℝ) ≤ n * Real.exp (-w) ∧
    n * Real.exp w ≤ (shellWindowUpper n w : ℝ) ∧
    (shellWindowUpper n w : ℝ) ≤ 2 * n ∧
    shellWindowLower n w ≤ shellWindowUpper n w ∧
    ((shellWindowUpper n w - shellWindowLower n w : ℕ) : ℝ) ≤ 3 * w * n + 2 := by
  set A := shellWindowLower n w
  set B := shellWindowUpper n w
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hnR]
  have hem : 3 / 4 ≤ Real.exp (-w) := by
    have h := Real.add_one_le_exp (-w)
    linarith only [h, hw4]
  have heq : Real.exp w * Real.exp (-w) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hep : Real.exp w ≤ 4 / 3 := by
    nlinarith only [heq, hem, Real.exp_pos w]
  have hexp : Real.exp w - Real.exp (-w) ≤ 3 * w := by
    have h := Real.add_one_le_exp (-w)
    nlinarith only [h, heq, hw, hw4, Real.exp_pos w, Real.exp_pos (-w)]
  have hAle : (A : ℝ) ≤ n * Real.exp (-w) := Nat.floor_le (by positivity)
  have hAgt : (n : ℝ) * Real.exp (-w) < A + 1 := Nat.lt_floor_add_one _
  have hBle : (B : ℝ) ≤ n * Real.exp w + 1 := by
    dsimp only [B, shellWindowUpper]
    push_cast
    have h := Nat.floor_le (show 0 ≤ (n : ℝ) * Real.exp w by positivity)
    linarith only [h]
  have hBgt : (n : ℝ) * Real.exp w < B := by
    simpa only [B, shellWindowUpper, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one ((n : ℝ) * Real.exp w)
  have hAn : (n : ℝ) / 2 ≤ A := by nlinarith only [hAgt, hem, hnR]
  have hA1 : 1 ≤ A := by
    exact_mod_cast (by linarith only [hAn, hnR] : (1 : ℝ) ≤ A)
  have hB2n : (B : ℝ) ≤ 2 * n := by nlinarith only [hBle, hep, hnR]
  have hAB : A ≤ B := by
    have h1 : (n : ℝ) * Real.exp (-w) ≤ n :=
      mul_le_of_le_one_right hn0.le (Real.exp_le_one_iff.mpr (by linarith only [hw]))
    have h2 : (n : ℝ) ≤ n * Real.exp w :=
      le_mul_of_one_le_right hn0.le (Real.one_le_exp_iff.mpr hw.le)
    exact_mod_cast (hAle.trans (h1.trans (h2.trans hBgt.le)))
  refine ⟨hA1, hAn, hAle, hBgt.le, hB2n, hAB, ?_⟩
  rw [Nat.cast_sub hAB]
  nlinarith only [hAgt, hBle, hexp, hn0]

theorem shellPartnerKernel_eq_zero_off_window
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    {w : ℝ} (hw : 0 < w) {n ℓ : ℕ} (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hoff : ℓ ∉ Ico (shellWindowLower n w) (shellWindowUpper n w)) :
    shellPartnerKernel (atomDilate φ w) n ℓ = 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  rw [shellPartnerKernel, bumpCorr_atomDilate_eq_zero_of_le hφ hsupp hw, mul_zero]
  simp only [mem_Ico, not_and_or, not_le, not_lt] at hoff
  rcases hoff with hleft | hright
  · have hfloor := Nat.floor_le (show 0 ≤ (n : ℝ) * Real.exp (-w) by positivity)
    have hℓA : (ℓ : ℝ) < shellWindowLower n w := by exact_mod_cast hleft
    have h := Real.log_le_log hℓ0 (hℓA.le.trans hfloor)
    rw [Real.log_mul hn0.ne' (Real.exp_pos _).ne', Real.log_exp] at h
    rw [abs_of_nonpos (by linarith only [h, hw])]
    linarith only [h]
  · have hfloor : (n : ℝ) * Real.exp w < (shellWindowUpper n w : ℝ) := by
      simpa only [shellWindowUpper, Nat.cast_add, Nat.cast_one] using
        Nat.lt_floor_add_one ((n : ℝ) * Real.exp w)
    have hBℓ : (shellWindowUpper n w : ℝ) ≤ ℓ := by exact_mod_cast hright
    have h := Real.log_le_log (mul_pos hn0 (Real.exp_pos w)) (hfloor.le.trans hBℓ)
    rw [Real.log_mul hn0.ne' (Real.exp_pos _).ne', Real.log_exp] at h
    rw [abs_of_nonneg (by linarith only [h, hw])]
    linarith only [h]

/-- The complete row retains exactly the integer cells meeting its support. -/
theorem sum_shellPartnerKernel_eq_window
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    {w : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    {N n : ℕ} (hn : 4 ≤ n) (hnN : n ≤ N) (a : ℕ → ℝ) :
    (∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)),
      shellPartnerKernel (atomDilate φ w) n ℓ * a ℓ) =
      ∑ i ∈ range (shellWindowUpper n w - shellWindowLower n w),
        shellPartnerKernel (atomDilate φ w) n ((shellWindowLower n w : ℝ) + i) *
          a (shellWindowLower n w + i) := by
  obtain ⟨hA1, _, _, _, _, _, _⟩ := shellWindow_geometry hn hw hw4
  have hsub : Ico (shellWindowLower n w) (shellWindowUpper n w) ⊆
      Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)) := by
    intro ℓ hℓ
    obtain ⟨hleft, hright⟩ := mem_Ico.mp hℓ
    refine mem_Icc.mpr ⟨hA1.trans hleft, ?_⟩
    have hℓfloor : ℓ ≤ Nat.floor ((n : ℝ) * Real.exp w) := by
      change ℓ < Nat.floor ((n : ℝ) * Real.exp w) + 1 at hright
      omega
    have hℓR : (ℓ : ℝ) ≤ n * Real.exp w :=
      (show (ℓ : ℝ) ≤ Nat.floor ((n : ℝ) * Real.exp w) by
        exact_mod_cast hℓfloor).trans (Nat.floor_le (by positivity))
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast hnN
    exact_mod_cast (hℓR.trans
      ((mul_le_mul_of_nonneg_right hnR (Real.exp_pos w).le).trans (Nat.le_ceil _)))
  have he := Finset.sum_subset hsub (f := fun ℓ : ℕ =>
    shellPartnerKernel (atomDilate φ w) n ℓ * a ℓ) (fun ℓ hℓ hoff => by
      rw [shellPartnerKernel_eq_zero_off_window hφ hsupp hw (by omega : 1 ≤ n)
        (mem_Icc.mp hℓ).1 hoff, zero_mul])
  rw [← he, sum_Ico_eq_sum_range]
  simp only [Nat.cast_add]

/-- Logarithmic change of variables identifies the full shell-row mass with the pole moment. -/
theorem integral_shellPartnerKernel
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    {w : ℝ} (hw : 0 < w) {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ n * Real.exp (-w)) (hb : n * Real.exp w ≤ b) :
    ∫ t in a..b, shellPartnerKernel (atomDilate φ w) n t =
      Real.sqrt n * ∫ u, Real.exp (u / 2) * bumpCorr (atomDilate φ w) u := by
  set β := bumpCorr (atomDilate φ w)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hβc : Continuous β := continuous_bumpCorr_atomDilate hφ hsupp hw
  have hβ0 : ∀ u, w ≤ |u| → β u = 0 :=
    fun u hu => bumpCorr_atomDilate_eq_zero_of_le hφ hsupp hw hu
  set a' := Real.log (a / n)
  set b' := Real.log (b / n)
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have ha' : a' ≤ -w := by
    rw [← Real.log_exp (-w)]
    exact Real.log_le_log (div_pos ha hn0) (by rw [div_le_iff₀ hn0]; linarith only [hab])
  have hb' : w ≤ b' := by
    rw [← Real.log_exp w]
    exact Real.log_le_log (Real.exp_pos w) (by rw [le_div_iff₀ hn0]; linarith only [hb])
  have hab' : a' ≤ b' := by linarith only [ha', hb', hw]
  have hsub := integral_comp_mul_deriv' (a := a') (b := b') (f := fun u => n * Real.exp u)
    (f' := fun u => n * Real.exp u) (g := shellPartnerKernel (atomDilate φ w) n)
    (fun u _ => (Real.hasDerivAt_exp u).const_mul _) (by fun_prop) (by
      rintro t ⟨u, -, rfl⟩
      have ht : (0 : ℝ) < n * Real.exp u := by positivity
      refine ContinuousAt.continuousWithinAt ?_
      unfold shellPartnerKernel
      exact (Real.continuous_sqrt.continuousAt.inv₀ (Real.sqrt_pos.mpr ht).ne').mul
        (hβc.continuousAt.comp ((Real.continuousAt_log ht.ne').sub continuousAt_const)))
  have hfa : (n : ℝ) * Real.exp a' = a := by
    simp only [a']; rw [Real.exp_log (div_pos ha hn0)]; field_simp
  have hfb : (n : ℝ) * Real.exp b' = b := by
    simp only [b']; rw [Real.exp_log (div_pos hb0 hn0)]; field_simp
  rw [hfa, hfb] at hsub
  rw [← hsub]
  have hpt (u : ℝ) :
      (shellPartnerKernel (atomDilate φ w) n ∘ fun u => (n : ℝ) * Real.exp u) u *
        ((n : ℝ) * Real.exp u) = Real.sqrt n * (Real.exp (u / 2) * β u) := by
    have he : Real.sqrt (Real.exp u) = Real.exp (u / 2) := by
      rw [← Real.sqrt_sq (Real.exp_pos (u / 2)).le, sq, ← Real.exp_add, add_halves]
    have hlog : Real.log ((n : ℝ) * Real.exp u) = Real.log n + u := by
      rw [Real.log_mul hn0.ne' (Real.exp_pos u).ne', Real.log_exp]
    have hsq : Real.sqrt ((n : ℝ) * Real.exp u) = Real.sqrt n * Real.exp (u / 2) := by
      rw [Real.sqrt_mul hn0.le, he]
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have hex : Real.exp u = Real.exp (u / 2) * Real.exp (u / 2) := by
      rw [← Real.exp_add, add_halves]
    simp only [Function.comp, shellPartnerKernel, hlog, hsq, add_sub_cancel_left]
    change (Real.sqrt n * Real.exp (u / 2))⁻¹ * β u * (n * Real.exp u) = _
    rw [hex]
    field_simp
    rw [Real.sq_sqrt hn0.le]
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_of_le hab']
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_
  have hu' : w ≤ |u| := by
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
    rcases hu with hu | hu
    · rw [abs_of_neg (by linarith only [hu, ha', hw])]
      linarith only [hu, ha']
    · rw [abs_of_pos (by linarith only [hu, hb', hw])]
      linarith only [hu, hb']
  rw [hβ0 u hu', mul_zero]

/-- The shell width pays for the variation and both endpoint cells. -/
theorem poleVector_window_variation_le
    {φ : ℝ → ℝ} (hM : 0 < ∫ u, φ u ^ 2)
    {w A₁ : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4) (hA₁0 : 0 ≤ A₁)
    {n : ℕ} (hn : 2 ≤ n) (hwn : 1 / 2 ≤ w * n) (L : ℕ)
    (hlen : (L : ℝ) ≤ 3 * w * n + 2) :
    poleVector n * ((∫ u, atomDilate φ w u ^ 2) / Real.sqrt ((n : ℝ) / 2) +
      L * (((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ *
        ((∫ u, atomDilate φ w u ^ 2) + A₁))) ≤
      (2 + 28 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) *
        (∫ u, atomDilate φ w u ^ 2) / n := by
  set G := ∫ u, atomDilate φ w u ^ 2
  set M := ∫ u, φ u ^ 2
  set r := (1 / 4 : ℝ) + A₁ / M
  have hG : G = w * M := integral_atomDilate_sq hw
  have hG0 : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
  have hr0 : 0 ≤ r := add_nonneg (by norm_num) (div_nonneg hA₁0 hM.le)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hnR]
  have hs : 0 < Real.sqrt ((n : ℝ) / 2) := Real.sqrt_pos.mpr (by positivity)
  have hL : (L : ℝ) ≤ 7 * w * n := by linarith only [hlen, hwn]
  have hratio : w * (G + A₁) ≤ r * G := by
    have he : w * (G + A₁) = (w + A₁ / M) * G := by
      rw [hG]
      field_simp [hM.ne']
    rw [he]
    exact mul_le_mul_of_nonneg_right (show w + A₁ / M ≤ r by
      dsimp only [r]
      linarith only [hw4]) hG0
  have hbracket : G / Real.sqrt ((n : ℝ) / 2) +
      L * (((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ * (G + A₁)) ≤
      (1 + 14 * r) * G / Real.sqrt ((n : ℝ) / 2) := by
    have h1 := mul_le_mul_of_nonneg_right hL
      (show 0 ≤ ((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ * (G + A₁) by positivity)
    have he : (7 * w * n) *
        (((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ * (G + A₁)) =
        14 * (w * (G + A₁)) / Real.sqrt ((n : ℝ) / 2) := by
      field_simp [hn0.ne', hs.ne']
      ring
    rw [he] at h1
    have h2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 14)) hs.le
    calc
      _ ≤ G / Real.sqrt ((n : ℝ) / 2) + 14 * (r * G) / Real.sqrt ((n : ℝ) / 2) :=
        add_le_add le_rfl (h1.trans h2)
      _ = _ := by ring
  have hweight : poleVector n / Real.sqrt ((n : ℝ) / 2) ≤ 2 / n := by
    have hden : (n : ℝ) / 2 ≤ Real.sqrt n * Real.sqrt ((n : ℝ) / 2) := by
      calc
        (n : ℝ) / 2 = Real.sqrt ((n : ℝ) / 2) * Real.sqrt ((n : ℝ) / 2) :=
          (Real.mul_self_sqrt (by positivity)).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.sqrt_le_sqrt (by linarith only [hn0])) hs.le
    have hi := inv_anti₀ (show (0 : ℝ) < n / 2 by positivity) hden
    simpa only [poleVector, one_div, div_eq_mul_inv, mul_inv_rev,
      inv_div, inv_inv, one_mul, mul_comm] using hi
  calc
    _ ≤ poleVector n * ((1 + 14 * r) * G / Real.sqrt ((n : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hbracket (by unfold poleVector; positivity)
    _ = (poleVector n / Real.sqrt ((n : ℝ) / 2)) * ((1 + 14 * r) * G) := by ring
    _ ≤ (2 / n) * ((1 + 14 * r) * G) :=
      mul_le_mul_of_nonneg_right hweight (by positivity)
    _ = _ := by dsimp only [r, M, G]; ring

/-- A full periodic shell row has a uniform reciprocal-index bound. -/
theorem abs_full_periodic_shellPartnerKernel_sum_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2)
    {q : ℕ} (hq : 1 ≤ q) (ψ : ℕ → ℝ) {U : ℝ}
    (hper : ∀ j, ψ (j + q) = ψ j) (hmean : ∑ j ∈ range q, ψ j = 0)
    (hU : ∀ j, |ψ j| ≤ U) {w A₁ : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    (hA₁0 : 0 ≤ A₁) (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {N n : ℕ} (hn : 4 ≤ n) (hnN : n ≤ N) (hwn : 1 / 2 ≤ w * n) :
    |poleVector n * ∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)),
        shellPartnerKernel (atomDilate φ w) n ℓ * ψ ℓ| ≤
      (4 + 56 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) * q * U *
        (∫ u, atomDilate φ w u ^ 2) / n := by
  obtain ⟨_, hleft, _, _, hright, hAB, hlen⟩ := shellWindow_geometry hn hw hw4
  have hcells : (shellWindowLower n w : ℝ) +
      (shellWindowUpper n w - shellWindowLower n w : ℕ) = shellWindowUpper n w := by
    rw [Nat.cast_sub hAB]
    ring
  rw [sum_shellPartnerKernel_eq_window hφ hsupp hw hw4 hn hnN]
  exact abs_weighted_periodic_shellPartnerKernel_sum_le hφ hsupp hM hq ψ hper hmean hU
    hw hw4 hA₁0 hA₁ (by omega : 2 ≤ n) hwn _ _ hleft (hcells.le.trans hright) hlen

/-- The lattice reading of the constant shell row differs from its polar mass by `Oφ(G/n)`. -/
theorem abs_full_shellPartnerKernel_sum_sub_integral_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2)
    {w A₁ : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    (hA₁0 : 0 ≤ A₁) (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {N n : ℕ} (hn : 4 ≤ n) (hnN : n ≤ N) (hwn : 1 / 2 ≤ w * n) :
    |poleVector n * (∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)),
        shellPartnerKernel (atomDilate φ w) n ℓ) -
        ∫ u, Real.exp (u / 2) * bumpCorr (atomDilate φ w) u| ≤
      (2 + 28 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) *
        (∫ u, atomDilate φ w u ^ 2) / n := by
  set A := shellWindowLower n w
  set L := shellWindowUpper n w - A
  set G := ∫ u, atomDilate φ w u ^ 2
  set P := ∫ u, Real.exp (u / 2) * bumpCorr (atomDilate φ w) u
  set K := ((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ * (G + A₁)
  obtain ⟨hA1, hleft, hAexp, hBexp, hright, hAB, hlen⟩ := shellWindow_geometry hn hw hw4
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcells : (A : ℝ) + L = shellWindowUpper n w := by
    dsimp only [L]
    rw [Nat.cast_sub hAB]
    ring
  have hsub : Set.Icc (A : ℝ) (A + L) ⊆ Set.Icc ((n : ℝ) / 2) (2 * n) := by
    intro t ht
    exact ⟨hleft.trans ht.1, ht.2.trans (hcells.le.trans hright)⟩
  have hd (t : ℝ) (ht : t ∈ Set.Icc (A : ℝ) (A + L)) :=
    hasDerivAt_shellPartnerKernel hφ hsupp hw n
      (show 0 < t from (by positivity : (0 : ℝ) < n / 2).trans_le (hsub ht).1)
  have hb (t : ℝ) (ht : t ∈ Set.Icc (A : ℝ) (A + L)) :=
    abs_deriv_shellPartnerKernel_le hφ hsupp hw hA₁ (by omega : 2 ≤ n) (hsub ht)
  have hcmp := abs_sum_sub_integral_le_of_deriv hd hb
  have hint := integral_shellPartnerKernel hφ hsupp hw (by omega : 1 ≤ n)
    (a := A) (b := A + L)
    (by have h : (1 : ℝ) ≤ A := by exact_mod_cast hA1
        linarith only [h]) hAexp
    (by rw [hcells]; exact hBexp)
  rw [hint] at hcmp
  have hsum := sum_shellPartnerKernel_eq_window hφ hsupp hw hw4 hn hnN (fun _ => 1)
  simp only [mul_one] at hsum
  rw [hsum]
  have hp : poleVector n * Real.sqrt n = 1 := by
    rw [poleVector, one_div, inv_mul_cancel₀ (Real.sqrt_pos.mpr hn0).ne']
  have hrewrite : poleVector n *
      ((∑ i ∈ range L, shellPartnerKernel (atomDilate φ w) n ((A : ℝ) + i)) -
        Real.sqrt n * P) =
      poleVector n * (∑ i ∈ range L,
        shellPartnerKernel (atomDilate φ w) n ((A : ℝ) + i)) - P := by
    rw [mul_sub, ← mul_assoc, hp, one_mul]
  rw [← hrewrite, abs_mul, abs_of_nonneg (show 0 ≤ poleVector n by unfold poleVector; positivity)]
  calc
    _ ≤ poleVector n * (L * K) :=
      mul_le_mul_of_nonneg_left hcmp (by unfold poleVector; positivity)
    _ ≤ poleVector n * (G / Real.sqrt ((n : ℝ) / 2) + L * K) := by
      apply mul_le_mul_of_nonneg_left _ (by unfold poleVector; positivity)
      have hG : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
      exact le_add_of_nonneg_left (by positivity)
    _ ≤ _ := poleVector_window_variation_le hM hw hw4 hA₁0 (by omega : 2 ≤ n) hwn L hlen

/-- A logarithm on a mean-zero periodic shell row costs only one logarithm of its index. -/
theorem abs_full_periodic_rowIntegrand_sum_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2)
    {q : ℕ} (hq : 1 ≤ q) (ψ : ℕ → ℝ) {U : ℝ}
    (hper : ∀ j, ψ (j + q) = ψ j) (hmean : ∑ j ∈ range q, ψ j = 0)
    (hU : ∀ j, |ψ j| ≤ U) {w A₁ : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    (hA₁0 : 0 ≤ A₁) (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {N n : ℕ} (hn : 4 ≤ n) (hnN : n ≤ N) (hwn : 1 / 2 ≤ w * n) :
    |poleVector n * ∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)),
        rowIntegrand (atomDilate φ w) n ℓ * ψ ℓ| ≤
      (4 + 56 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) * q * U *
        (∫ u, atomDilate φ w u ^ 2) * (1 + Real.log (2 * n)) / n := by
  set A := shellWindowLower n w
  set L := shellWindowUpper n w - A
  set G := ∫ u, atomDilate φ w u ^ 2
  set D := 1 + Real.log (2 * n)
  set K := ((n : ℝ) / 2 * Real.sqrt ((n : ℝ) / 2))⁻¹ * (G + A₁)
  obtain ⟨_, hleft, _, _, hright, hAB, hlen⟩ := shellWindow_geometry hn hw hw4
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hnR]
  have hG0 : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  have hD0 : 0 ≤ D := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 2 * n by linarith only [hnR])
    dsimp only [D]
    linarith only [h]
  have hcells : (A : ℝ) + L = shellWindowUpper n w := by
    dsimp only [L]
    rw [Nat.cast_sub hAB]
    ring
  have hsub : Set.Icc (A : ℝ) (A + L) ⊆ Set.Icc ((n : ℝ) / 2) (2 * n) := by
    intro t ht
    exact ⟨hleft.trans ht.1, ht.2.trans (hcells.le.trans hright)⟩
  obtain ⟨hg, _, hgc⟩ := atomDilate_facts hφ hsupp hw
  have hF (t : ℝ) (ht : t ∈ Set.Icc (A : ℝ) (A + L)) :
      |rowIntegrand (atomDilate φ w) n t| ≤ D * G / Real.sqrt ((n : ℝ) / 2) := by
    have htI := hsub ht
    have ht1 : 1 ≤ t := by linarith only [htI.1, hnR]
    have ht0 : 0 < t := zero_lt_one.trans_le ht1
    have hlog : |Real.log t| ≤ D := by
      rw [abs_of_nonneg (Real.log_nonneg ht1)]
      have h := Real.log_le_log ht0 htI.2
      dsimp only [D]
      linarith only [h]
    have hinv : (Real.sqrt t)⁻¹ ≤ (Real.sqrt ((n : ℝ) / 2))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_le_sqrt htI.1)
    have hβ := abs_bumpCorr_le hg.continuous hgc (Real.log t - Real.log n)
    rw [rowIntegrand, abs_mul, abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg t)]
    calc
      _ ≤ (D * (Real.sqrt ((n : ℝ) / 2))⁻¹) * G :=
        mul_le_mul (mul_le_mul hlog hinv (by positivity) hD0) hβ (abs_nonneg _)
          (by positivity)
      _ = _ := by ring
  have hd (t : ℝ) (ht : t ∈ Set.Icc (A : ℝ) (A + L)) :=
    hasDerivAt_rowIntegrand hφ hsupp hw n
      (show 0 < t from (by positivity : (0 : ℝ) < n / 2).trans_le (hsub ht).1)
  have hb (t : ℝ) (ht : t ∈ Set.Icc (A : ℝ) (A + L)) :
      |((t * Real.sqrt t)⁻¹ * ((1 - Real.log t / 2) *
          bumpCorr (atomDilate φ w) (Real.log t - Real.log n) +
        Real.log t * deriv (shellAutocorr φ) ((Real.log t - Real.log n) / w)))| ≤ D * K := by
    exact (abs_deriv_rowIntegrand_le hφ hsupp hw hA₁ (by omega : 2 ≤ n) (hsub ht)).trans_eq
      (by dsimp only [D, K, G]; ring)
  have hrow := abs_periodic_lattice_sum_le_of_deriv hq ψ hper hmean hU A L hF hd hb
  have hsum := sum_shellPartnerKernel_eq_window hφ hsupp hw hw4 hn hnN
    (fun ℓ => Real.log ℓ * ψ ℓ)
  have he : (∑ ℓ ∈ Icc 1 (Nat.ceil ((N : ℝ) * Real.exp w)),
      rowIntegrand (atomDilate φ w) n ℓ * ψ ℓ) =
      ∑ i ∈ range L, rowIntegrand (atomDilate φ w) n ((A : ℝ) + i) * ψ (A + i) := by
    simpa only [rowIntegrand, shellPartnerKernel, Nat.cast_add,
      mul_assoc, mul_left_comm, mul_comm] using hsum
  rw [he, abs_mul, abs_of_nonneg (show 0 ≤ poleVector n by unfold poleVector; positivity)]
  calc
    _ ≤ poleVector n * ((2 * q * U) *
        (D * G / Real.sqrt ((n : ℝ) / 2) + L * (D * K))) :=
      mul_le_mul_of_nonneg_left hrow (by unfold poleVector; positivity)
    _ = (2 * q * U * D) *
        (poleVector n * (G / Real.sqrt ((n : ℝ) / 2) + L * K)) := by ring
    _ ≤ (2 * q * U * D) *
        ((2 + 28 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) * G / n) :=
      mul_le_mul_of_nonneg_left
        (poleVector_window_variation_le hM hw hw4 hA₁0 (by omega : 2 ≤ n) hwn L hlen)
        (by positivity)
    _ = _ := by dsimp only [D, G]; ring

#print axioms shellWindow_geometry
#print axioms sum_shellPartnerKernel_eq_window
#print axioms integral_shellPartnerKernel
#print axioms abs_full_periodic_shellPartnerKernel_sum_le
#print axioms abs_full_shellPartnerKernel_sum_sub_integral_le
#print axioms abs_full_periodic_rowIntegrand_sum_le
end
end GaloisForLFunctions.SuccessorShellArithmetic
