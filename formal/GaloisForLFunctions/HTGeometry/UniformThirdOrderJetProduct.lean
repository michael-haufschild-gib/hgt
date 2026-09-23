import GaloisForLFunctions.HTGeometry.UniformThirdOrderJet

/-! Product calculus for parameter-uniform cubic endpoint jets. -/

namespace GaloisForLFunctions.HTGeometry
open Set Filter Topology
noncomputable section
set_option autoImplicit false

/-- Scalar multiplication preserves a cubic endpoint jet with the exact norm
scaling of its remainder constant. -/
theorem HasUniformJet3.const_mul {S : Set ℂ} {b : ℝ} {F : ℂ → ℝ → ℂ}
    {c₀ c₁ c₂ : ℂ → ℂ} {C : ℝ} (h : HasUniformJet3 S b F c₀ c₁ c₂ C) (k : ℂ) :
    HasUniformJet3 S b (fun u z => k * F u z) (fun u => k * c₀ u)
      (fun u => k * c₁ u) (fun u => k * c₂ u) (‖k‖ * C) := by
  intro u hu z hz
  calc
    ‖k * F u z - k * c₀ u - k * c₁ u * z - k * c₂ u * z ^ (2 : ℕ)‖ =
        ‖k‖ * ‖F u z - c₀ u - c₁ u * z - c₂ u * z ^ (2 : ℕ)‖ := by
          rw [← norm_mul]
          ring_nf
    _ ≤ ‖k‖ * (C * z ^ (3 : ℕ)) := mul_le_mul_of_nonneg_left (h u hu z hz) (norm_nonneg _)
    _ = (‖k‖ * C) * z ^ (3 : ℕ) := by ring

/-- Products of cubic endpoint jets remain cubic endpoint jets. The retained
coefficients are the literal degree-zero through degree-two product terms. -/
theorem HasUniformJet3.mul {S : Set ℂ} {b : ℝ} (hb1 : b ≤ 1)
    {F G : ℂ → ℝ → ℂ} {c₀ c₁ c₂ d₀ d₁ d₂ : ℂ → ℂ} {C D M : ℝ}
    (hF : HasUniformJet3 S b F c₀ c₁ c₂ C) (hG : HasUniformJet3 S b G d₀ d₁ d₂ D)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hc₀ : ∀ u ∈ S, ‖c₀ u‖ ≤ M) (hc₁ : ∀ u ∈ S, ‖c₁ u‖ ≤ M)
    (hc₂ : ∀ u ∈ S, ‖c₂ u‖ ≤ M) (hd₀ : ∀ u ∈ S, ‖d₀ u‖ ≤ M)
    (hd₁ : ∀ u ∈ S, ‖d₁ u‖ ≤ M) (hd₂ : ∀ u ∈ S, ‖d₂ u‖ ≤ M) :
    HasUniformJet3 S b (fun u z => F u z * G u z)
      (fun u => c₀ u * d₀ u)
      (fun u => c₀ u * d₁ u + c₁ u * d₀ u)
      (fun u => c₀ u * d₂ u + c₁ u * d₁ u + c₂ u * d₀ u)
      (3 * M ^ (2 : ℕ) + C * (3 * M + D) + 3 * M * D) := by
  intro u hu z hz
  have hz0 : 0 ≤ z := hz.1.le
  have hz1 : z ≤ 1 := hz.2.trans hb1
  have hz2 : z ^ (2 : ℕ) ≤ 1 := pow_le_one₀ hz0 hz1
  have hz3 : z ^ (3 : ℕ) ≤ 1 := pow_le_one₀ hz0 hz1
  have hz4 : z ^ (4 : ℕ) ≤ z ^ (3 : ℕ) := by nlinarith [mul_nonneg (pow_nonneg hz0 3) (sub_nonneg.mpr hz1)]
  set r := F u z - c₀ u - c₁ u * z - c₂ u * z ^ (2 : ℕ) with hr
  set s := G u z - d₀ u - d₁ u * z - d₂ u * z ^ (2 : ℕ) with hs
  have hrn : ‖r‖ ≤ C * z ^ (3 : ℕ) := hF u hu z hz
  have hsn : ‖s‖ ≤ D * z ^ (3 : ℕ) := hG u hu z hz
  have hFz : F u z = c₀ u + c₁ u * z + c₂ u * z ^ (2 : ℕ) + r := by rw [hr]; ring
  have hGz : G u z = d₀ u + d₁ u * z + d₂ u * z ^ (2 : ℕ) + s := by rw [hs]; ring
  have hzn : ‖(z : ℂ)‖ = z := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hz0]
  have hGb : ‖G u z‖ ≤ 3 * M + D := by
    rw [hGz]
    calc
      ‖d₀ u + d₁ u * z + d₂ u * z ^ (2 : ℕ) + s‖
          ≤ ‖d₀ u‖ + ‖d₁ u * z‖ + ‖d₂ u * z ^ (2 : ℕ)‖ + ‖s‖ := by
            calc
              _ ≤ ‖d₀ u + d₁ u * z + d₂ u * z ^ (2 : ℕ)‖ + ‖s‖ := norm_add_le _ _
              _ ≤ (‖d₀ u + d₁ u * z‖ + ‖d₂ u * z ^ (2 : ℕ)‖) + ‖s‖ := by
                gcongr
                exact norm_add_le _ _
              _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ M + M * 1 + M * 1 + D * 1 := by
        gcongr
        · exact hd₀ u hu
        · rw [norm_mul, hzn]
          exact mul_le_mul (hd₁ u hu) hz1 hz0 hM
        · rw [norm_mul, norm_pow, hzn]
          exact mul_le_mul (hd₂ u hu) hz2 (sq_nonneg z) hM
        · exact hsn.trans (mul_le_mul_of_nonneg_left hz3 hD)
      _ = 3 * M + D := by ring
  have hFb : ‖c₀ u + c₁ u * z + c₂ u * z ^ (2 : ℕ)‖ ≤ 3 * M := by
    calc
      ‖c₀ u + c₁ u * z + c₂ u * z ^ (2 : ℕ)‖
          ≤ ‖c₀ u‖ + ‖c₁ u * z‖ + ‖c₂ u * z ^ (2 : ℕ)‖ := by
            calc
              _ ≤ ‖c₀ u + c₁ u * z‖ + ‖c₂ u * z ^ (2 : ℕ)‖ := norm_add_le _ _
              _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ M + M * 1 + M * 1 := by
        gcongr
        · exact hc₀ u hu
        · rw [norm_mul, hzn]
          exact mul_le_mul (hc₁ u hu) hz1 hz0 hM
        · rw [norm_mul, norm_pow, hzn]
          exact mul_le_mul (hc₂ u hu) hz2 (sq_nonneg z) hM
      _ = 3 * M := by ring
  have hhigh3 : ‖(c₁ u * d₂ u + c₂ u * d₁ u) * (z : ℂ) ^ (3 : ℕ)‖ ≤
      2 * M ^ (2 : ℕ) * z ^ (3 : ℕ) := by
    rw [norm_mul, norm_pow, hzn]
    calc
      ‖c₁ u * d₂ u + c₂ u * d₁ u‖ * z ^ (3 : ℕ)
          ≤ (‖c₁ u * d₂ u‖ + ‖c₂ u * d₁ u‖) * z ^ (3 : ℕ) :=
            mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg hz0 _)
      _ ≤ (M * M + M * M) * z ^ (3 : ℕ) := by
        gcongr
        · rw [norm_mul]
          exact mul_le_mul (hc₁ u hu) (hd₂ u hu) (norm_nonneg _) hM
        · rw [norm_mul]
          exact mul_le_mul (hc₂ u hu) (hd₁ u hu) (norm_nonneg _) hM
      _ = 2 * M ^ (2 : ℕ) * z ^ (3 : ℕ) := by ring
  have hhigh4 : ‖c₂ u * d₂ u * (z : ℂ) ^ (4 : ℕ)‖ ≤ M ^ (2 : ℕ) * z ^ (3 : ℕ) := by
    rw [norm_mul, norm_mul, norm_pow, hzn]
    calc
      ‖c₂ u‖ * ‖d₂ u‖ * z ^ (4 : ℕ) ≤ M * M * z ^ (4 : ℕ) := by
        gcongr
        · exact hc₂ u hu
        · exact hd₂ u hu
      _ ≤ M * M * z ^ (3 : ℕ) := by gcongr
      _ = M ^ (2 : ℕ) * z ^ (3 : ℕ) := by ring
  have hkey : F u z * G u z - c₀ u * d₀ u -
      (c₀ u * d₁ u + c₁ u * d₀ u) * z -
      (c₀ u * d₂ u + c₁ u * d₁ u + c₂ u * d₀ u) * z ^ (2 : ℕ) =
      (c₁ u * d₂ u + c₂ u * d₁ u) * (z : ℂ) ^ (3 : ℕ) + c₂ u * d₂ u * (z : ℂ) ^ (4 : ℕ) +
        r * G u z + s * (c₀ u + c₁ u * z + c₂ u * z ^ (2 : ℕ)) := by
    rw [hFz]
    conv_rhs => rw [hGz]
    rw [hGz]
    ring
  rw [hkey]
  calc
    ‖(c₁ u * d₂ u + c₂ u * d₁ u) * (z : ℂ) ^ (3 : ℕ) + c₂ u * d₂ u * (z : ℂ) ^ (4 : ℕ) +
        r * G u z + s * (c₀ u + c₁ u * z + c₂ u * z ^ (2 : ℕ))‖
        ≤ ‖(c₁ u * d₂ u + c₂ u * d₁ u) * (z : ℂ) ^ (3 : ℕ)‖ +
          ‖c₂ u * d₂ u * (z : ℂ) ^ (4 : ℕ)‖ + ‖r * G u z‖ +
            ‖s * (c₀ u + c₁ u * z + c₂ u * z ^ (2 : ℕ))‖ := by
          calc
            _ ≤ ‖(c₁ u * d₂ u + c₂ u * d₁ u) * (z : ℂ) ^ (3 : ℕ) +
                c₂ u * d₂ u * (z : ℂ) ^ (4 : ℕ) + r * G u z‖ +
                  ‖s * (c₀ u + c₁ u * z + c₂ u * z ^ (2 : ℕ))‖ := norm_add_le _ _
            _ ≤ (‖(c₁ u * d₂ u + c₂ u * d₁ u) * (z : ℂ) ^ (3 : ℕ) +
                c₂ u * d₂ u * (z : ℂ) ^ (4 : ℕ)‖ + ‖r * G u z‖) +
                  ‖s * (c₀ u + c₁ u * z + c₂ u * z ^ (2 : ℕ))‖ := by
                  gcongr
                  exact norm_add_le _ _
            _ ≤ _ := by gcongr; exact norm_add_le _ _
    _ ≤ 2 * M ^ (2 : ℕ) * z ^ (3 : ℕ) + M ^ (2 : ℕ) * z ^ (3 : ℕ) +
        (C * z ^ (3 : ℕ)) * (3 * M + D) + (D * z ^ (3 : ℕ)) * (3 * M) := by
          apply add_le_add
          · apply add_le_add
            · apply add_le_add hhigh3 hhigh4
            · rw [norm_mul]
              exact mul_le_mul hrn hGb (norm_nonneg _) (by positivity)
          · rw [norm_mul]
            exact mul_le_mul hsn hFb (norm_nonneg _) (by positivity)
    _ = (3 * M ^ (2 : ℕ) + C * (3 * M + D) + 3 * M * D) * z ^ (3 : ℕ) := by ring

end
end GaloisForLFunctions.HTGeometry
