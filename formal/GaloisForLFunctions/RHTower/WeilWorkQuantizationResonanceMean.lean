import GaloisForLFunctions.RHTower.WeilWorkQuantizationResonanceEnergy
import GaloisForLFunctions.HTGeometry.BohrTrigPolynomial

/-!
# Vanishing mean-square tests with fixed resonance response

The exact source energy produces finite exponential polynomials with mean
square tending to zero and height-one resonance response equal to one. Thus
unweighted mean-square approximation cannot support a continuous extension
of the normalized resonance functional.
-/

open Complex Filter Topology GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

noncomputable section
namespace RHTower.WeilSpectral

def quantizationResonancePolynomial (p : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, p n * bohrExp (-2 * Real.log n) t

theorem continuous_quantizationResonancePolynomial (p : ℕ → ℂ) (N : ℕ) :
    Continuous (quantizationResonancePolynomial p N) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_bohrExp _)

theorem isBohrAlmostPeriodic_quantizationResonancePolynomial (p : ℕ → ℂ) (N : ℕ) :
    IsBohrAlmostPeriodic (quantizationResonancePolynomial p N) :=
  isBohrAlmostPeriodic_sum _
    (fun _ _ => continuous_const.mul (continuous_bohrExp _))
    (fun _ _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_bohrExp _))

/-- The critical logarithmic frequencies are distinct, so mean square equals
coefficient square norm exactly. -/
theorem quantizationResonancePolynomial_mean (p : ℕ → ℂ) (N : ℕ) :
    bohrMean (fun t => quantizationResonancePolynomial p N t *
      conj (quantizationResonancePolynomial p N t)) =
        ((∑ n ∈ Finset.Icc 1 N, ‖p n‖ ^ 2 : ℝ) : ℂ) := by
  classical
  let P := quantizationResonancePolynomial p N
  have hc : Continuous P := continuous_quantizationResonancePolynomial p N
  have ha : IsBohrAlmostPeriodic P := isBohrAlmostPeriodic_quantizationResonancePolynomial p N
  have hcoef (j : ℕ) (hj : j ∈ Finset.Icc 1 N) :
      bohrCoefficient P (-2 * Real.log j) = p j := by
    rw [show P = fun t => ∑ n ∈ Finset.Icc 1 N,
      p n * bohrExp (-2 * Real.log n) t from rfl, bohrCoefficient_trigPoly]
    have hinj (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
        -2 * Real.log (n : ℝ) = -2 * Real.log j ↔ n = j := by
      constructor
      · intro h
        have hlog : Real.log (n : ℝ) = Real.log j := by linarith
        have he := congrArg Real.exp hlog
        rw [Real.exp_log (by exact_mod_cast (show 0 < n by have := (Finset.mem_Icc.mp hn).1; omega)),
          Real.exp_log (by exact_mod_cast (show 0 < j by have := (Finset.mem_Icc.mp hj).1; omega))] at he
        exact_mod_cast he
      · rintro rfl
        rfl
    calc
      _ = ∑ n ∈ Finset.Icc 1 N, if n = j then p n else 0 :=
        Finset.sum_congr rfl fun n hn => by simp only [hinj n hn]
      _ = p j := by simp [hj]
  have hsplit : (fun t => P t * conj (P t)) = fun t =>
      ∑ n ∈ Finset.Icc 1 N, conj (p n) * (P t * bohrChar (-2 * Real.log n) t) := by
    funext t
    change P t * conj (∑ n ∈ Finset.Icc 1 N, p n * bohrExp (-2 * Real.log n) t) = _
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [map_mul, conj_bohrExp]; ring
  change bohrMean (fun t => P t * conj (P t)) = _
  rw [hsplit, bohrMean_sum (F := fun n => fun t =>
    conj (p n) * (P t * bohrChar (-2 * Real.log n) t)) _
    (fun n _ => continuous_const.mul (hc.mul (continuous_bohrChar _)))
    (fun n _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_mul_bohrChar hc ha _))]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [bohrMean_const_mul (f := fun t => P t * bohrChar (-2 * Real.log n) t)
    _ (hc.mul (continuous_bohrChar _))
    (isBohrAlmostPeriodic_mul_bohrChar hc ha _)]
  change conj (p n) * bohrCoefficient P (-2 * Real.log n) = _
  rw [hcoef n hn, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- A sequence of actual critical resonance tests has vanishing mean square,
while its normalized source response is eventually exactly one. -/
theorem exists_quantization_resonance_discontinuity {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ p : ℕ → ℕ → ℂ,
      Tendsto (fun N => (bohrMean (fun t => quantizationResonancePolynomial (p N) N t *
        conj (quantizationResonancePolynomial (p N) N t))).re) atTop (𝓝 0) ∧
      ∀ᶠ N in atTop, (∑ n ∈ Finset.Icc 1 N,
        p N n * quantizationFrequencyResidue lam (-2 * Real.log n) 1) = 1 := by
  let E := quantizationResonanceEnergy lam 0
  let p : ℕ → ℕ → ℂ := fun N n => conj (quantizationCenteredResonance lam 0 n) / (E N : ℂ)
  have hE : Tendsto E atTop atTop := tendsto_quantization_resonance_energy hW
  have hn (N : ℕ) : (∑ n ∈ Finset.Icc 1 N, ‖p N n‖ ^ 2) = (E N)⁻¹ := by
    calc
      _ = E N / (E N) ^ 2 := by
        simp only [p, norm_div, Complex.norm_conj, Complex.norm_real,
          Real.norm_eq_abs, div_pow, sq_abs, ← Finset.sum_div]
        rfl
      _ = (E N)⁻¹ := by
        by_cases hz : E N = 0
        · simp [hz]
        · field_simp
  refine ⟨p, ?_, ?_⟩
  · simpa only [quantizationResonancePolynomial_mean, Complex.ofReal_re, hn,
      Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hE)
  · filter_upwards [hE.eventually_gt_atTop 0] with N hN
    have hne : (E N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hN
    have hz : ∀ n : ℕ, quantizationFrequencyResidue lam (-2 * Real.log n) 1 =
        quantizationCenteredResonance lam 0 n := by simp [quantizationCenteredResonance]
    simp_rw [p, hz, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [(quantization_resonance_norm_attained lam 0 N).1]
    exact div_self hne

end RHTower.WeilSpectral
