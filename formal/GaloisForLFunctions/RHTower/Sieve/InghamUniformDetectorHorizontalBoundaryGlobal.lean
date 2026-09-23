import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorHorizontalBoundary

open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

/-- A single horizontal-boundary constant works for every moving center. The old pointwise proof
only depends on the center through a width `W = 4 - c`, and `0 ≤ W ≤ 4` on the whole parameter
range. -/
theorem exists_inghamClassicalHorizontalBoundary_global_polylog :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {sigma : ℝ}, 7 / 10 ≤ sigma → sigma ≤ 1 →
      ∀ {X : ℕ}, 10 ≤ X →
      ∃ T₁ ∈ Ioo (-(X : ℝ)) (-(X : ℝ) + 1),
      ∃ T₂ ∈ Ioo ((X : ℝ) - 2) ((X : ℝ) - 1),
        (∀ x ∈ Icc (inghamUniformGabrielCenter sigma) 4,
          inghamDetector X ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
        (∀ x ∈ Icc (inghamUniformGabrielCenter sigma) 4,
          inghamDetector X ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
        inghamClassicalHorizontalBoundary X (inghamUniformGabrielCenter sigma) 4 T₁ T₂ ≤
          K * (1 + Real.log X) ^ (2 : ℕ) := by
  obtain ⟨K0, hK0, hselected⟩ :=
    exists_inghamDetector_two_horizontal_edges_polylog
  let B : ℝ := K0 + 2
  let K : ℝ := 32 * B
  have hB : 0 ≤ B := by dsimp only [B]; linarith
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro sigma hsigma0 hsigma1 X hX
  have hcenter699 : (699 / 1000 : ℝ) ≤ inghamUniformGabrielCenter sigma := by
    unfold inghamUniformGabrielCenter
    nlinarith
  have hcenter4 : inghamUniformGabrielCenter sigma ≤ 4 := by
    unfold inghamUniformGabrielCenter
    nlinarith
  obtain ⟨T₁, hT₁, T₂, hT₂, hbottom, htop⟩ := hselected hX
  let u : ℝ := 1 + Real.log X
  let W : ℝ := 4 - inghamUniformGabrielCenter sigma
  have hW : 0 ≤ W := by dsimp only [W]; linarith
  have hW4 : W ≤ 4 := by
    dsimp only [W]
    unfold inghamUniformGabrielCenter
    nlinarith
  have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hu1 : 1 ≤ u := by
    dsimp only [u]
    linarith [Real.log_nonneg hX1]
  have huSq0 : 0 ≤ u ^ (2 : ℕ) := sq_nonneg u
  have huSq1 : 1 ≤ u ^ (2 : ℕ) := by nlinarith
  have hT₁abs : 1 ≤ |T₁| := by
    rw [abs_of_nonpos (by linarith [hT₁.2, hXR])]
    linarith [hT₁.2]
  have hT₂abs : 1 ≤ |T₂| := by
    rw [abs_of_nonneg (by linarith [hT₂.1, hXR])]
    linarith [hT₂.1]
  have hclassical₁ : ∀ x ∈ Icc (inghamUniformGabrielCenter sigma) 4,
      ‖logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₁ : ℂ) * I)‖ ≤
        B * u ^ (2 : ℕ) := by
    intro x hx
    have hx' : x ∈ Icc (699 / 1000 : ℝ) 4 :=
      ⟨hcenter699.trans hx.1, hx.2⟩
    obtain ⟨hH, hdet⟩ := hbottom x hx'
    let s : ℂ := (x : ℂ) + (T₁ : ℂ) * I
    have hsIm : |s.im| = |T₁| := by simp [s]
    have hs1 : s ≠ 1 := by
      intro hs
      have himEq := congrArg Complex.im hs
      have hTzero : T₁ = 0 := by simpa [s] using himEq
      rw [hTzero, abs_zero] at hT₁abs
      linarith
    have htransfer := norm_logDeriv_inghamClassicalDetector_le
      X hs1 (by simpa only [s] using hH) (by rw [hsIm]; exact hT₁abs)
    have hdet' : ‖logDeriv (inghamDetector X) s‖ ≤ K0 * u ^ (2 : ℕ) := by
      simpa only [s, u] using hdet
    calc
      ‖logDeriv (inghamClassicalDetector X) s‖ ≤
          ‖logDeriv (inghamDetector X) s‖ + 2 := htransfer
      _ ≤ K0 * u ^ (2 : ℕ) + 2 := add_le_add hdet' (le_refl 2)
      _ ≤ B * u ^ (2 : ℕ) := by dsimp only [B]; nlinarith
  have hclassical₂ : ∀ x ∈ Icc (inghamUniformGabrielCenter sigma) 4,
      ‖logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₂ : ℂ) * I)‖ ≤
        B * u ^ (2 : ℕ) := by
    intro x hx
    have hx' : x ∈ Icc (699 / 1000 : ℝ) 4 :=
      ⟨hcenter699.trans hx.1, hx.2⟩
    obtain ⟨hH, hdet⟩ := htop x hx'
    let s : ℂ := (x : ℂ) + (T₂ : ℂ) * I
    have hsIm : |s.im| = |T₂| := by simp [s]
    have hs1 : s ≠ 1 := by
      intro hs
      have himEq := congrArg Complex.im hs
      have hTzero : T₂ = 0 := by simpa [s] using himEq
      rw [hTzero, abs_zero] at hT₂abs
      linarith
    have htransfer := norm_logDeriv_inghamClassicalDetector_le
      X hs1 (by simpa only [s] using hH) (by rw [hsIm]; exact hT₂abs)
    have hdet' : ‖logDeriv (inghamDetector X) s‖ ≤ K0 * u ^ (2 : ℕ) := by
      simpa only [s, u] using hdet
    calc
      ‖logDeriv (inghamClassicalDetector X) s‖ ≤
          ‖logDeriv (inghamDetector X) s‖ + 2 := htransfer
      _ ≤ K0 * u ^ (2 : ℕ) + 2 := add_le_add hdet' (le_refl 2)
      _ ≤ B * u ^ (2 : ℕ) := by dsimp only [B]; nlinarith
  let M : ℝ := W * (B * u ^ (2 : ℕ))
  have hpoint₁ : ∀ x ∈ Set.uIoc (inghamUniformGabrielCenter sigma) 4,
      ‖(x - inghamUniformGabrielCenter sigma) *
        (logDeriv (inghamClassicalDetector X)
          ((x : ℂ) + (T₁ : ℂ) * I)).im‖ ≤ M := by
    intro x hx
    rw [uIoc_of_le hcenter4] at hx
    have hxIcc : x ∈ Icc (inghamUniformGabrielCenter sigma) 4 := ⟨hx.1.le, hx.2⟩
    have himle := Complex.abs_im_le_norm
      (logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₁ : ℂ) * I))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hxIcc.1)]
    calc
      (x - inghamUniformGabrielCenter sigma) *
          |(logDeriv (inghamClassicalDetector X)
            ((x : ℂ) + (T₁ : ℂ) * I)).im| ≤
          (x - inghamUniformGabrielCenter sigma) *
            ‖logDeriv (inghamClassicalDetector X)
              ((x : ℂ) + (T₁ : ℂ) * I)‖ :=
        mul_le_mul_of_nonneg_left himle (sub_nonneg.mpr hxIcc.1)
      _ ≤ W * (B * u ^ (2 : ℕ)) := by
        apply mul_le_mul (by dsimp only [W]; linarith [hxIcc.2])
          (hclassical₁ x hxIcc) (norm_nonneg _) hW
      _ = M := rfl
  have hpoint₂ : ∀ x ∈ Set.uIoc (inghamUniformGabrielCenter sigma) 4,
      ‖(x - inghamUniformGabrielCenter sigma) *
        (logDeriv (inghamClassicalDetector X)
          ((x : ℂ) + (T₂ : ℂ) * I)).im‖ ≤ M := by
    intro x hx
    rw [uIoc_of_le hcenter4] at hx
    have hxIcc : x ∈ Icc (inghamUniformGabrielCenter sigma) 4 := ⟨hx.1.le, hx.2⟩
    have himle := Complex.abs_im_le_norm
      (logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₂ : ℂ) * I))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hxIcc.1)]
    calc
      (x - inghamUniformGabrielCenter sigma) *
          |(logDeriv (inghamClassicalDetector X)
            ((x : ℂ) + (T₂ : ℂ) * I)).im| ≤
          (x - inghamUniformGabrielCenter sigma) *
            ‖logDeriv (inghamClassicalDetector X)
              ((x : ℂ) + (T₂ : ℂ) * I)‖ :=
        mul_le_mul_of_nonneg_left himle (sub_nonneg.mpr hxIcc.1)
      _ ≤ W * (B * u ^ (2 : ℕ)) := by
        apply mul_le_mul (by dsimp only [W]; linarith [hxIcc.2])
          (hclassical₂ x hxIcc) (norm_nonneg _) hW
      _ = M := rfl
  have hint₁ : ‖∫ x in (inghamUniformGabrielCenter sigma)..4,
      (x - inghamUniformGabrielCenter sigma) *
        (logDeriv (inghamClassicalDetector X)
          ((x : ℂ) + (T₁ : ℂ) * I)).im‖ ≤ M * W := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint₁
    rw [abs_of_nonneg hW] at h
    simpa only [W] using h
  have hint₂ : ‖∫ x in (inghamUniformGabrielCenter sigma)..4,
      (x - inghamUniformGabrielCenter sigma) *
        (logDeriv (inghamClassicalDetector X)
          ((x : ℂ) + (T₂ : ℂ) * I)).im‖ ≤ M * W := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint₂
    rw [abs_of_nonneg hW] at h
    simpa only [W] using h
  have hzero₁ : ∀ x ∈ Icc (inghamUniformGabrielCenter sigma) 4,
      inghamDetector X ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx
    exact (hbottom x ⟨hcenter699.trans hx.1, hx.2⟩).1
  have hzero₂ : ∀ x ∈ Icc (inghamUniformGabrielCenter sigma) 4,
      inghamDetector X ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx
    exact (htop x ⟨hcenter699.trans hx.1, hx.2⟩).1
  refine ⟨T₁, hT₁, T₂, hT₂, hzero₁, hzero₂, ?_⟩
  dsimp only [inghamClassicalHorizontalBoundary]
  let I₁ : ℝ := ∫ x in (inghamUniformGabrielCenter sigma)..4,
      (x - inghamUniformGabrielCenter sigma) *
        (logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₁ : ℂ) * I)).im
  let I₂ : ℝ := ∫ x in (inghamUniformGabrielCenter sigma)..4,
      (x - inghamUniformGabrielCenter sigma) *
        (logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₂ : ℂ) * I)).im
  change I₁ - I₂ ≤ K * u ^ (2 : ℕ)
  have hdiff : I₁ - I₂ ≤ ‖I₁ - I₂‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  have htri : ‖I₁ - I₂‖ ≤ ‖I₁‖ + ‖I₂‖ := norm_sub_le _ _
  have hI₁ : ‖I₁‖ ≤ M * W := by simpa only [I₁] using hint₁
  have hI₂ : ‖I₂‖ ≤ M * W := by simpa only [I₂] using hint₂
  have hWsq : W ^ (2 : ℕ) ≤ 16 := by
    nlinarith [mul_self_le_mul_self hW hW4]
  calc
    I₁ - I₂ ≤ ‖I₁ - I₂‖ := hdiff
    _ ≤ ‖I₁‖ + ‖I₂‖ := htri
    _ ≤ M * W + M * W := add_le_add hI₁ hI₂
    _ = 2 * W ^ (2 : ℕ) * B * u ^ (2 : ℕ) := by dsimp only [M]; ring
    _ ≤ 2 * 16 * B * u ^ (2 : ℕ) := by gcongr
    _ = K * u ^ (2 : ℕ) := by dsimp only [K]; ring

end

end RHTower.Sieve
