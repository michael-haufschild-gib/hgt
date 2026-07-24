import GaloisForLFunctions.RHTower.WeightedEulerMobiusRayRecovery
import GaloisForLFunctions.RHTower.WeightedEulerFECarrierSeparation

/-!
# Weighted-Euler Lambert carrier-separation universality law

A positive lower carrier wall supplies geometric decay on every positive
multiplicative ray.  Quantitative Möbius recovery therefore converts uniform
Lambert-transform decay into Fourier--Borel decay.  If that decay crosses the
upper carrier wall, two continuous functionals have the same entire
Fourier--Borel transform.
-/

noncomputable section

namespace RHTower

open Complex Set

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- **Lambert carrier-separation universality.**  On one compact carrier in a
positive real strip, uniform sampled Lambert decay beyond the upper strip
wall forces equality of two Fourier--Borel transforms. -/
theorem compactFourierBorel_eq_of_uniform_sampled_lambert_decay
    (L₁ L₂ : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    {α β σ D ρ : ℝ}
    (hα : 0 < α) (hβσ : β < σ)
    (hstrip : ∀ k, α ≤ (s k).re ∧ (s k).re ≤ β)
    (hD : 0 ≤ D) (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (hlam : ∀ x : ℝ, 0 < x → ∀ n : ℕ+,
      ‖compactCarrierLambertTransform (L₁ - L₂) s
          ((n : ℂ) * (x : ℂ))‖
        ≤ (D * Real.exp (-(σ * x))) * ρ ^ (n : ℕ)) :
    ∀ z : ℂ, compactFourierBorel L₁ s z = compactFourierBorel L₂ s z := by
  let L : C(K, ℂ) →L[ℂ] ℂ := L₁ - L₂
  have hre_upper : ∀ k, (s k).re ≤ β := fun k => (hstrip k).2
  have hdecay : ∀ x : ℝ, 0 ≤ x →
      ‖compactFourierBorel L₁ s (x : ℂ) -
          compactFourierBorel L₂ s (x : ℂ)‖
        ≤ max (4 * D * ρ) ‖L‖ * Real.exp (-(σ * x)) := by
    intro x hx
    have hsub : compactFourierBorel L₁ s (x : ℂ) -
        compactFourierBorel L₂ s (x : ℂ) =
        compactFourierBorel L s (x : ℂ) := by
      simp [L, compactFourierBorel]
    rw [hsub]
    rcases hx.eq_or_lt with rfl | hxpos
    · have hzero := norm_compactFourierBorel_le_exp L s (0 : ℂ)
      have hz : ‖compactFourierBorel L s (0 : ℂ)‖ ≤ ‖L‖ := by
        simpa using hzero
      simpa using hz.trans (le_max_right (4 * D * ρ) ‖L‖)
    · set r : ℝ := Real.exp (-(α * x)) with hr
      have hr0 : 0 ≤ r := Real.exp_nonneg _
      have hr1 : r < 1 := by
        rw [hr, Real.exp_lt_one_iff]
        nlinarith
      have hq : ∀ n : ℕ+,
          ‖compactExponentialTest s ((n : ℂ) * (x : ℂ))‖ < 1 := by
        intro n
        have hnpos : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.prop
        apply norm_compactExponentialTest_lt_one_of_re_pos s _
          ((n : ℝ) * (α * x))
        · positivity
        · intro k
          have hk := (hstrip k).1
          have hcast :
              (n : ℂ) * (x : ℂ) = (((n : ℝ) * x : ℝ) : ℂ) := by
            norm_cast
          calc
            (n : ℝ) * (α * x)
                ≤ (n : ℝ) * (x * (s k).re) := by
                  apply mul_le_mul_of_nonneg_left _ hnpos.le
                  nlinarith [mul_le_mul_of_nonneg_left hk hxpos.le]
            _ = (((n : ℂ) * (x : ℂ)) * s k).re := by
                  rw [hcast]
                  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
                  ring
      have hFB : ∀ n : ℕ+,
          ‖compactFourierBorel L s ((n : ℂ) * (x : ℂ))‖
            ≤ ‖L‖ * r ^ (n : ℕ) := by
        intro n
        have hnpos : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.prop
        have hre : ∀ k,
            (n : ℝ) * (α * x) ≤
              (((n : ℂ) * (x : ℂ)) * s k).re := by
          intro k
          have hk := (hstrip k).1
          have hcast :
              (n : ℂ) * (x : ℂ) = (((n : ℝ) * x : ℝ) : ℂ) := by
            norm_cast
          calc
            (n : ℝ) * (α * x)
                ≤ (n : ℝ) * (x * (s k).re) := by
                  apply mul_le_mul_of_nonneg_left _ hnpos.le
                  nlinarith [mul_le_mul_of_nonneg_left hk hxpos.le]
            _ = (((n : ℂ) * (x : ℂ)) * s k).re := by
                  rw [hcast]
                  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
                  ring
        have htest := norm_compactExponentialTest_le_exp_neg_of_re s
          ((n : ℂ) * (x : ℂ)) ((n : ℝ) * (α * x)) hre
        calc
          ‖compactFourierBorel L s ((n : ℂ) * (x : ℂ))‖
              ≤ ‖L‖ *
                  ‖compactExponentialTest s ((n : ℂ) * (x : ℂ))‖ := by
                exact L.le_opNorm _
          _ ≤ ‖L‖ * Real.exp (-((n : ℝ) * (α * x))) := by gcongr
          _ = ‖L‖ * r ^ (n : ℕ) := by
                congr 1
                rw [hr, show -((n : ℝ) * (α * x)) =
                    (n : ℕ) * (-(α * x)) by ring, Real.exp_nat_mul]
      have hrecover := norm_compactFourierBorel_le_of_sampled_lambert_decay
        L s (x : ℂ) hq (norm_nonneg L) hr0 hr1 hFB
        (mul_nonneg hD (Real.exp_nonneg _)) hρ0 hρhalf
        (fun n => hlam x hxpos n)
      calc
        ‖compactFourierBorel L s (x : ℂ)‖
            ≤ 4 * (D * Real.exp (-(σ * x))) * ρ := hrecover
        _ = (4 * D * ρ) * Real.exp (-(σ * x)) := by ring
        _ ≤ max (4 * D * ρ) ‖L‖ * Real.exp (-(σ * x)) := by
              exact mul_le_mul_of_nonneg_right (le_max_left _ _)
                (Real.exp_nonneg _)
  exact compactFourierBorel_sub_eq_zero_of_ray_decay
    L₁ s L₂ s hβσ hre_upper hre_upper hdecay

end RHTower
