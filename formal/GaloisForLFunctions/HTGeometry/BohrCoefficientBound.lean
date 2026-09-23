import GaloisForLFunctions.HTGeometry.BohrCauchySchwarz
import GaloisForLFunctions.HTGeometry.BohrTrigProduct

/-!
# The Bohr coefficients of a product are controlled by the two mean squares

Twisting one factor by the character costs nothing, because the character has modulus one.  So
Cauchy–Schwarz for the Bohr mean bounds every Bohr coefficient of a product:

`‖c_λ(u v)‖² ≤ M(|u|²) · M(|v|²)`.

This is the estimate that lets a mean-square approximation of the factors control the coefficients
of the product.
-/

open MeasureTheory ComplexConjugate

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

theorem conj_bohrChar (lam t : ℝ) : conj (bohrChar lam t) = bohrExp lam t := by
  have h := conj_bohrExp lam t
  rw [← h, Complex.conj_conj]

/-- **The coefficients of a product are bounded by the mean squares of the factors.** -/
theorem norm_bohrCoefficient_mul_sq_le {u v : ℝ → ℂ} (huc : Continuous u)
    (hua : IsBohrAlmostPeriodic u) (hvc : Continuous v) (hva : IsBohrAlmostPeriodic v) (lam : ℝ) :
    ‖bohrCoefficient (fun t => u t * v t) lam‖ ^ (2 : ℕ)
      ≤ (bohrMean (fun t => u t * conj (u t))).re
        * (bohrMean (fun t => v t * conj (v t))).re := by
  set k : ℝ → ℂ := fun t => conj (v t) * bohrExp lam t with hk
  have hkc : Continuous k :=
    (Complex.continuous_conj.comp hvc).mul (continuous_bohrExp lam)
  have hka : IsBohrAlmostPeriodic k :=
    isBohrAlmostPeriodic_mul (Complex.continuous_conj.comp hvc)
      (isBohrAlmostPeriodic_conj hva) (continuous_bohrExp lam)
      (isBohrAlmostPeriodic_bohrExp lam)
  -- the pairing is the Bohr coefficient of the product
  have hpair : (fun t : ℝ => u t * conj (k t)) = fun t : ℝ => (u t * v t) * bohrChar lam t := by
    funext t
    rw [hk]
    simp only [map_mul, Complex.conj_conj, conj_bohrExp]
    ring
  -- the twisted factor has the same mean square
  have hsame : (fun t : ℝ => k t * conj (k t)) = fun t : ℝ => v t * conj (v t) := by
    funext t
    rw [hk]
    simp only [map_mul, Complex.conj_conj, conj_bohrExp]
    have hchar : bohrExp lam t * bohrChar lam t = bohrChar 0 t := by
      rw [bohrExp_mul_bohrChar]
      congr 1
      ring
    calc conj (v t) * bohrExp lam t * (v t * bohrChar lam t)
        = (v t * conj (v t)) * (bohrExp lam t * bohrChar lam t) := by ring
      _ = (v t * conj (v t)) * bohrChar 0 t := by rw [hchar]
      _ = v t * conj (v t) := by
          unfold bohrChar
          norm_num
  have hcs := norm_bohrMean_mul_conj_sq_le huc hua hkc hka
  rw [hpair, hsame] at hcs
  exact hcs

end

end GaloisForLFunctions
