import GaloisForLFunctions.ConjugateDiagonalGeometry.MovingSourceTail
import GaloisForLFunctions.RHTower.LorentzianZeroMass
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ZeroDensityFilteredWeilPositivityAndCoercivity

/-!
# Arithmetic control of the omitted xi reference mass

Every omitted zero lies beyond the cutoff's ordinate radius. A width-radius
Lorentzian kernel bounds its reference weight; the arithmetic logarithmic
derivative estimate then bounds the complete multiplicity-weighted tail.
-/

open Complex Filter Set
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 _root_.RHTower

/-- A width-n arithmetic resolvent controls every zero omitted by the source cutoff. -/
theorem sourceReferenceTail_le_lorentzMassW {n : ℕ} (hn : 1 ≤ n) :
    sourceReferenceTail n ≤ 2 * lorentzMassW (n : ℝ) 0 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := zero_lt_one.trans_le hn1
  have hs : Summable (fun q : XiZeroCopy => 1 / ((n : ℝ) ^ 2 + (q.1 : ℂ).im ^ 2)) := by
    simpa only [lorentzMassWTerm, zero_sub, neg_sq] using summable_lorentzMassWTerm hn1 0
  have hc := ArithmeticCastelnuovoSeveri.summable_zetaCarrier_of_xiZeroCopy
    (g := fun z : ℂ => 1 / ((n : ℝ) ^ 2 + z.im ^ 2)) (fun z => by positivity) hs
  have hp (ρ : zetaZeroConfig.carrier) :
      (1 - sourceCutoff n ρ) *
        ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) ≤
      2 * ((zetaZeroConfig.mult ρ : ℝ) * (1 / ((n : ℝ) ^ 2 + (ρ : ℂ).im ^ 2))) := by
    by_cases hχ : sourceCutoff n ρ = 1
    · rw [hχ, sub_self, zero_mul]
      positivity
    have hy : (n : ℝ) < |(ρ : ℂ).im| := by
      by_contra h
      exact hχ (sourceCutoff_eq_one_of_im_le n ρ (le_of_not_gt h))
    have hn2 : (n : ℝ) ^ 2 ≤ (ρ : ℂ).im ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hn0.le hy.le 2
    have hre : (gammaOf (ρ : ℂ)).re = (ρ : ℂ).im := by
      rw [gammaOf, Complex.div_I]
      simp
    have hgamma : (ρ : ℂ).im ^ 2 ≤ Complex.normSq (gammaOf (ρ : ℂ)) := by
      rw [Complex.normSq_apply, hre]
      nlinarith only [sq_nonneg (gammaOf (ρ : ℂ)).im]
    have hden : 1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))) ≤
        2 / ((n : ℝ) ^ 2 + (ρ : ℂ).im ^ 2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith only [hn2, hgamma]
    have hq0 : 0 ≤ (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))) := by
      positivity
    have hcut : 0 ≤ sourceCutoff n ρ := (sourceCutoff n).nonneg
    calc
      (1 - sourceCutoff n ρ) *
          ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) ≤
          (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf (ρ : ℂ))) :=
        mul_le_of_le_one_left hq0 (by linarith only [hcut])
      _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (2 / ((n : ℝ) ^ 2 + (ρ : ℂ).im ^ 2)) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg _)
      _ = _ := by ring
  calc
    sourceReferenceTail n ≤ ∑' ρ : zetaZeroConfig.carrier,
        2 * ((zetaZeroConfig.mult ρ : ℝ) * (1 / ((n : ℝ) ^ 2 + (ρ : ℂ).im ^ 2))) :=
      (summable_sourceReferenceTail n).tsum_le_tsum hp (hc.mul_left 2)
    _ = 2 * ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) * (1 / ((n : ℝ) ^ 2 + (ρ : ℂ).im ^ 2)) := tsum_mul_left
    _ = 2 * lorentzMassW (n : ℝ) 0 := by
      rw [← ArithmeticCastelnuovoSeveri.tsum_xiZeroCopy_eq_zetaCarrier hs]
      simp only [lorentzMassW, lorentzMassWTerm, zero_sub, neg_sq]

/-- The omitted spectral reference mass is bounded by xi data on the zero-free right half-plane. -/
theorem sourceReferenceTail_le_sourceLogDeriv {n : ℕ} (hn : 1 ≤ n) :
    sourceReferenceTail n ≤ (16 / (n : ℝ)) *
      (logDeriv xi (widthPoint (n : ℝ) 0)).re := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine (sourceReferenceTail_le_lorentzMassW hn).trans ?_
  have h := mul_le_mul_of_nonneg_left (lorentzMassW_le_re_logDeriv_xi hn1 0)
    (by norm_num : (0 : ℝ) ≤ 2)
  calc
    2 * lorentzMassW (n : ℝ) 0 ≤
        2 * ((8 / (n : ℝ)) * (logDeriv xi (widthPoint (n : ℝ) 0)).re) := h
    _ = _ := by ring

/-- The reference tail has a uniform arithmetic logarithm-over-radius bound. -/
theorem sourceReferenceTail_le_log_div {n : ℕ} (hn : 1 ≤ n) :
    sourceReferenceTail n ≤ (16 / (n : ℝ)) *
      (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine (sourceReferenceTail_le_lorentzMassW hn).trans ?_
  have h := mul_le_mul_of_nonneg_left (lorentzMassW_le_log hn1 0)
    (by norm_num : (0 : ℝ) ≤ 2)
  simp only [abs_zero, add_zero] at h
  calc
    2 * lorentzMassW (n : ℝ) 0 ≤
        2 * ((8 / (n : ℝ)) *
          (xiLineTwoLogDerivConstant + Real.log ((n : ℝ) + 4))) := h
    _ = _ := by ring

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.sourceReferenceTail_le_sourceLogDeriv
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.sourceReferenceTail_le_log_div
