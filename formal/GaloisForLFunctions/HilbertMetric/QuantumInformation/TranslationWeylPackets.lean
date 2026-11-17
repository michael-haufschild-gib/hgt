import GaloisForLFunctions.HilbertMetric.QuantumInformation.TranslationWeylAverage
import GaloisForLFunctions.HilbertMetric.QuantumInformation.TranslationWeakAveragePackets

/-!
# Contractive weak averaging of Weyl and finite-rank packets

A finite sum of integer-frequency Weyl observables may be perturbed by any
explicit finite-rank Ward packet. Weak translation averaging removes the
finite-rank part and all nonzero frequencies. The retained translation
operator is bounded by the original operator norm, including cancellations
between its Weyl and finite-rank terms.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.ShiftAverage

/-- A concrete finite observable containing Weyl terms and finite-rank source terms. -/
def weylPacket {m n : ℕ} (a : Fin m → ℝ) (k : Fin m → ℤ) (c : Fin m → ℂ)
    (d : Fin n → ℂ) (x y : Fin n → Space) : Space →L[ℂ] Space :=
  integerWeylPolynomial a k c + HTGeometry.finiteRankProbe d x y

/-- All weak coefficients of a finite Weyl polynomial are integrable on the averaging interval. -/
theorem integerWeylPolynomial_coefficient_integrableOn {m : ℕ}
    (a : Fin m → ℝ) (k : Fin m → ℤ) (c : Fin m → ℂ) (u v : Space) :
    IntegrableOn (fun t : ℝ => inner ℂ (shift t u)
      (integerWeylPolynomial a k c (shift t v))) (Set.Ioc 0 1) := by
  simp only [integerWeylPolynomial, _root_.sum_apply, smul_apply,
    inner_sum, inner_smul_right]
  exact integrable_finsetSum Finset.univ (fun i _ =>
    (weylWord_coefficient_integrableOn (a i) (2 * Real.pi * (k i : ℝ)) u v).const_mul (c i))

private theorem weylPacket_coefficient_ae {m n : ℕ}
    (a : Fin m → ℝ) (k : Fin m → ℤ) (c : Fin m → ℂ)
    (d : Fin n → ℂ) (x y : Fin n → Space) (u v : Space) :
    (fun t : ℝ => inner ℂ (shift t u) (weylPacket a k c d x y (shift t v))) =ᵐ[
      volume.restrict (Set.Ioc 0 1)]
      (fun t : ℝ => inner ℂ (shift t u) (integerWeylPolynomial a k c (shift t v))) := by
  filter_upwards [ae_restrict_of_ae (finiteRankProbe_shift_ae_zero d x y v)] with t ht
  change inner ℂ (shift t u)
    (integerWeylPolynomial a k c (shift t v) + HTGeometry.finiteRankProbe d x y (shift t v)) = _
  rw [ht, Pi.zero_apply, add_zero]

/-- Finite-rank perturbations preserve weak coefficient integrability on the actual interval. -/
theorem weylPacket_coefficient_integrableOn {m n : ℕ}
    (a : Fin m → ℝ) (k : Fin m → ℤ) (c : Fin m → ℂ)
    (d : Fin n → ℂ) (x y : Fin n → Space) (u v : Space) :
    IntegrableOn (fun t : ℝ => inner ℂ (shift t u)
      (weylPacket a k c d x y (shift t v))) (Set.Ioc 0 1) :=
  (integrable_congr (weylPacket_coefficient_ae a k c d x y u v)).mpr
    (integerWeylPolynomial_coefficient_integrableOn a k c u v)

/-- The exact weak average is the zero-frequency translation operator. -/
theorem interval_average_weylPacket {m n : ℕ}
    (a : Fin m → ℝ) (k : Fin m → ℤ) (c : Fin m → ℂ)
    (d : Fin n → ℂ) (x y : Fin n → Space) (u v : Space) :
    (∫ t : ℝ in Set.Ioc 0 1,
      inner ℂ (shift t u) (weylPacket a k c d x y (shift t v))) =
        inner ℂ u (zeroFrequencyPart a k c v) := by
  rw [integral_congr_ae (weylPacket_coefficient_ae a k c d x y u v)]
  exact interval_average_integerWeylPolynomial a k c u v

private theorem shifted_coefficient_norm_le (A : Space →L[ℂ] Space) (u v : Space) (t : ℝ) :
    ‖inner ℂ (shift t u) (A (shift t v))‖ ≤ ‖u‖ * (‖A‖ * ‖v‖) := by
  calc
    _ ≤ ‖shift t u‖ * ‖A (shift t v)‖ := norm_inner_le_norm _ _
    _ ≤ ‖shift t u‖ * (‖A‖ * ‖shift t v‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
    _ = _ := by rw [norm_shift, norm_shift]

/-- Every retained pairing is bounded by the original packet norm. -/
theorem zeroFrequencyPart_pairing_norm_le {m n : ℕ}
    (a : Fin m → ℝ) (k : Fin m → ℤ) (c : Fin m → ℂ)
    (d : Fin n → ℂ) (x y : Fin n → Space) (u v : Space) :
    ‖inner ℂ u (zeroFrequencyPart a k c v)‖ ≤
      ‖u‖ * (‖weylPacket a k c d x y‖ * ‖v‖) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  rw [← interval_average_weylPacket a k c d x y u v]
  calc
    _ ≤ ∫ t : ℝ in Set.Ioc 0 1,
        ‖inner ℂ (shift t u) (weylPacket a k c d x y (shift t v))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _t : ℝ in Set.Ioc 0 1, ‖u‖ * (‖weylPacket a k c d x y‖ * ‖v‖) := by
      apply integral_mono (weylPacket_coefficient_integrableOn a k c d x y u v).norm
        (integrable_const _)
      exact shifted_coefficient_norm_le _ u v
    _ = _ := by simp

/-- Weak frequency projection contracts the norm even after arbitrary finite-rank perturbation. -/
theorem norm_zeroFrequencyPart_le_weylPacket {m n : ℕ}
    (a : Fin m → ℝ) (k : Fin m → ℤ) (c : Fin m → ℂ)
    (d : Fin n → ℂ) (x y : Fin n → Space) :
    ‖zeroFrequencyPart a k c‖ ≤ ‖weylPacket a k c d x y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  by_cases hv : zeroFrequencyPart a k c v = 0
  · rw [hv, norm_zero]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · have hb := zeroFrequencyPart_pairing_norm_le a k c d x y (zeroFrequencyPart a k c v) v
    have hs : ‖inner ℂ (zeroFrequencyPart a k c v) (zeroFrequencyPart a k c v)‖ =
        ‖zeroFrequencyPart a k c v‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      change ‖(‖zeroFrequencyPart a k c v‖ : ℂ) ^ 2‖ = ‖zeroFrequencyPart a k c v‖ ^ 2
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [hs, pow_two] at hb
    by_contra h
    exact (not_lt_of_ge hb)
      (mul_lt_mul_of_pos_left (lt_of_not_ge h) (norm_pos_iff.mpr hv))

#print axioms integerWeylPolynomial_coefficient_integrableOn
#print axioms weylPacket_coefficient_integrableOn
#print axioms interval_average_weylPacket
#print axioms zeroFrequencyPart_pairing_norm_le
#print axioms norm_zeroFrequencyPart_le_weylPacket
end GaloisForLFunctions.HilbertMetric.ShiftAverage
