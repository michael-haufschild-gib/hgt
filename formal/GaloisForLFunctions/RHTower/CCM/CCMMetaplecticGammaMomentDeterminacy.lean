import GaloisForLFunctions.RHTower.SoninSemilocalGammaMoments
import GaloisForLFunctions.HTGeometry.GammaVerticalRatioBound
import GaloisForLFunctions.HTGeometry.GammaCriticalLineModulus
import GaloisForLFunctions.HTGeometry.HardyStieltjesDeterminacy

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace RHTower

def ccmMetaplecticGammaExponentialMajorantConstant : ℝ :=
  (2 * Real.pi) ^ (-(3 : ℝ) / 2) *
    (Real.Gamma (1 / 4) / Real.Gamma (1 / 2)) ^ 2 * (2 * Real.pi)

theorem ccmMetaplecticGammaExponentialMajorantConstant_nonneg :
    0 ≤ ccmMetaplecticGammaExponentialMajorantConstant := by
  unfold ccmMetaplecticGammaExponentialMajorantConstant
  have hG4 : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hG2 : 0 < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  positivity

theorem semilocalArchimedeanGammaDensity_le_exponentialMajorant (s : ℝ) :
    semilocalArchimedeanGammaDensity s ≤
      ccmMetaplecticGammaExponentialMajorantConstant *
        Real.exp (-((Real.pi / 2) * |s|)) := by
  let A : ℝ := ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * Complex.I)‖
  let B : ℝ := ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * Complex.I)‖
  let C : ℝ := Real.Gamma (1 / 4) / Real.Gamma (1 / 2)
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hBpos : 0 < B := by
    apply norm_pos_iff.mpr
    apply Complex.Gamma_ne_zero
    intro n hn
    have hre := congrArg Complex.re hn
    simp at hre
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    norm_num at hre
    linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hratio := HTGeometry.norm_Gamma_div_le
    (a := (1 / 4 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (s / 2)
  have hAB : A ≤ C * B := by
    calc
      A = (A / B) * B := by field_simp
      _ ≤ C * B := mul_le_mul_of_nonneg_right (by simpa [A, B, C] using hratio) hB
  have hsq : A ^ 2 ≤ C ^ 2 * B ^ 2 := by
    have hmul := mul_le_mul hAB hAB hA (mul_nonneg hC hB)
    nlinarith
  have hcrit : B ^ 2 ≤
      2 * Real.pi * Real.exp (-((Real.pi / 2) * |s|)) := by
    have h := GaloisForLFunctions.normSq_Gamma_half_add_mul_I_le (s / 2)
    have habs : |s / 2| = |s| / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [habs] at h
    have hexp : -(Real.pi * (|s| / 2)) = -((Real.pi / 2) * |s|) := by ring
    rw [hexp] at h
    simpa [B] using h
  have hnorm : (0 : ℝ) ≤ (2 * Real.pi) ^ (-(3 : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  calc
    semilocalArchimedeanGammaDensity s =
        (2 * Real.pi) ^ (-(3 : ℝ) / 2) * A ^ 2 := by
      rw [semilocalArchimedeanGammaDensity, Complex.normSq_eq_norm_sq]
      simp only [A]
      congr 2
      push_cast
      ring
    _ ≤ (2 * Real.pi) ^ (-(3 : ℝ) / 2) * (C ^ 2 * B ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hnorm
    _ ≤ (2 * Real.pi) ^ (-(3 : ℝ) / 2) *
        (C ^ 2 * (2 * Real.pi * Real.exp (-((Real.pi / 2) * |s|)))) := by
      gcongr
    _ = ccmMetaplecticGammaExponentialMajorantConstant *
        Real.exp (-((Real.pi / 2) * |s|)) := by
      simp only [ccmMetaplecticGammaExponentialMajorantConstant, C]
      ring

theorem integrable_exp_neg_mul_abs_metaplectic {d : ℝ} (hd : 0 < d) :
    Integrable (fun x : ℝ => Real.exp (-d * |x|)) := by
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-d * |x|)) (Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (a := -d) (neg_lt_zero.mpr hd) 0
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [abs_of_pos hx]
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-d * |x|)) (Iic 0) := by
    have h := integrableOn_exp_mul_Iic (a := d) hd 0
    refine h.congr_fun (fun x hx => ?_) measurableSet_Iic
    rw [abs_of_nonpos hx]
    congr 1
    ring
  simpa [Ioi_union_Iic] using hpos.union hneg

theorem integrable_exp_pi_div_four_abs_mul_semilocalArchimedeanGammaDensity :
    Integrable (fun s : ℝ =>
      Real.exp ((Real.pi / 4) * |s|) * semilocalArchimedeanGammaDensity s) := by
  have hmajor : Integrable (fun s : ℝ =>
      ccmMetaplecticGammaExponentialMajorantConstant *
        Real.exp (-(Real.pi / 4) * |s|)) :=
    (integrable_exp_neg_mul_abs_metaplectic (by positivity : (0 : ℝ) < Real.pi / 4)).const_mul _
  have hstrong : AEStronglyMeasurable (fun s : ℝ =>
      Real.exp ((Real.pi / 4) * |s|) * semilocalArchimedeanGammaDensity s) := by
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_abs)).mul
        continuous_semilocalArchimedeanGammaDensity).aestronglyMeasurable
  apply Integrable.mono' hmajor hstrong
  filter_upwards with s
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.exp_pos _).le (semilocalArchimedeanGammaDensity_nonneg s))]
  calc
    Real.exp ((Real.pi / 4) * |s|) * semilocalArchimedeanGammaDensity s ≤
        Real.exp ((Real.pi / 4) * |s|) *
          (ccmMetaplecticGammaExponentialMajorantConstant *
            Real.exp (-((Real.pi / 2) * |s|))) :=
      mul_le_mul_of_nonneg_left
        (semilocalArchimedeanGammaDensity_le_exponentialMajorant s)
        (Real.exp_pos _).le
    _ = ccmMetaplecticGammaExponentialMajorantConstant *
        Real.exp (-(Real.pi / 4) * |s|) := by
      calc
        Real.exp ((Real.pi / 4) * |s|) *
            (ccmMetaplecticGammaExponentialMajorantConstant *
              Real.exp (-((Real.pi / 2) * |s|))) =
            ccmMetaplecticGammaExponentialMajorantConstant *
              (Real.exp ((Real.pi / 4) * |s|) *
                Real.exp (-((Real.pi / 2) * |s|))) := by ring
        _ = ccmMetaplecticGammaExponentialMajorantConstant *
              Real.exp ((Real.pi / 4) * |s| - (Real.pi / 2) * |s|) := by
            rw [← Real.exp_add]
            ring_nf
        _ = _ := by congr 2 <;> ring

theorem integrable_exp_pi_div_four_abs_semilocalArchimedeanGammaMeasure :
    Integrable (fun s : ℝ => Real.exp ((Real.pi / 4) * |s|))
      semilocalArchimedeanGammaMeasure := by
  rw [semilocalArchimedeanGammaMeasure,
    integrable_withDensity_iff_integrable_smul
      continuous_semilocalArchimedeanGammaDensityNNReal.measurable]
  apply integrable_exp_pi_div_four_abs_mul_semilocalArchimedeanGammaDensity.congr
  filter_upwards with s
  simp only [semilocalArchimedeanGammaDensityNNReal]
  change Real.exp ((Real.pi / 4) * |s|) * semilocalArchimedeanGammaDensity s =
    semilocalArchimedeanGammaDensity s * Real.exp ((Real.pi / 4) * |s|)
  ring

noncomputable instance semilocalArchimedeanGammaMeasure_isProbabilityMeasure :
    IsProbabilityMeasure semilocalArchimedeanGammaMeasure := by
  constructor
  rw [semilocalArchimedeanGammaMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have hfun :
      (fun s : ℝ => (semilocalArchimedeanGammaDensityNNReal s : ℝ≥0∞)) =
        fun s : ℝ => ENNReal.ofReal (semilocalArchimedeanGammaDensity s) := by
    funext s
    rw [ENNReal.ofReal_eq_coe_nnreal
      (semilocalArchimedeanGammaDensity_nonneg s)]
    rfl
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal
    integrable_semilocalArchimedeanGammaDensity
    (Filter.Eventually.of_forall semilocalArchimedeanGammaDensity_nonneg),
    integral_semilocalArchimedeanGammaDensity_eq_one]
  norm_num

def ccmMetaplecticGammaProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨semilocalArchimedeanGammaMeasure, inferInstance⟩

def ccmMetaplecticGammaMoment (n : ℕ) : ℝ :=
  ∫ s : ℝ, s ^ n ∂semilocalArchimedeanGammaMeasure

def ccmMetaplecticGammaMomentFiber : Set (ProbabilityMeasure ℝ) :=
  {ν | ∀ n : ℕ,
    Integrable (fun s : ℝ => s ^ n) (ν : Measure ℝ) ∧
      (∫ s : ℝ, s ^ n ∂(ν : Measure ℝ)) = ccmMetaplecticGammaMoment n}

theorem integrable_pow_semilocalArchimedeanGammaMeasure (n : ℕ) :
    Integrable (fun s : ℝ => s ^ n) semilocalArchimedeanGammaMeasure := by
  rw [semilocalArchimedeanGammaMeasure,
    integrable_withDensity_iff_integrable_smul
      continuous_semilocalArchimedeanGammaDensityNNReal.measurable]
  apply (integrable_pow_mul_semilocalArchimedeanGammaDensity n).congr
  filter_upwards with s
  simp only [semilocalArchimedeanGammaDensityNNReal]
  change s ^ n * semilocalArchimedeanGammaDensity s =
    semilocalArchimedeanGammaDensity s * s ^ n
  ring

theorem ccmMetaplecticGammaProbabilityMeasure_mem_momentFiber :
    ccmMetaplecticGammaProbabilityMeasure ∈ ccmMetaplecticGammaMomentFiber := by
  intro n
  exact ⟨integrable_pow_semilocalArchimedeanGammaMeasure n, rfl⟩

theorem ccmMetaplecticGammaMomentFiber_eq_singleton :
    ccmMetaplecticGammaMomentFiber = {ccmMetaplecticGammaProbabilityMeasure} := by
  ext ν
  constructor
  · intro hν
    letI : IsProbabilityMeasure (ν : Measure ℝ) := ν.property
    have hνexp : Integrable (fun s : ℝ =>
        Real.exp ((Real.pi / 8) * |s|)) (ν : Measure ℝ) := by
      have htransfer := HTGeometry.integrable_exp_half_abs_of_even_moments_eq
        (c := Real.pi / 4) (μ := semilocalArchimedeanGammaMeasure)
        (ν := (ν : Measure ℝ)) (by positivity)
        integrable_exp_pi_div_four_abs_semilocalArchimedeanGammaMeasure
        (fun n => integrable_pow_semilocalArchimedeanGammaMeasure (2 * n))
        (fun n => (hν (2 * n)).1)
        (fun n => by simpa [ccmMetaplecticGammaMoment] using (hν (2 * n)).2.symm)
      convert htransfer using 1 <;> ring
    have hμzero : 0 ∈ interior
        (integrableExpSet id semilocalArchimedeanGammaMeasure) :=
      HTGeometry.zero_mem_interior_integrableExpSet_of_integrable_exp_abs
        (by positivity : (0 : ℝ) < Real.pi / 4)
        integrable_exp_pi_div_four_abs_semilocalArchimedeanGammaMeasure
    have hνzero : 0 ∈ interior (integrableExpSet id (ν : Measure ℝ)) :=
      HTGeometry.zero_mem_interior_integrableExpSet_of_integrable_exp_abs
        (by positivity : (0 : ℝ) < Real.pi / 8) hνexp
    have heq : (ν : Measure ℝ) = semilocalArchimedeanGammaMeasure := by
      symm
      apply HTGeometry.measure_eq_of_moments_eq_of_bilateral_exponential_window
        hμzero hνzero
      intro n
      simpa [ccmMetaplecticGammaMoment] using (hν n).2.symm
    rw [Set.mem_singleton_iff]
    apply Subtype.ext
    exact heq
  · intro hν
    rw [Set.mem_singleton_iff] at hν
    simpa [hν] using ccmMetaplecticGammaProbabilityMeasure_mem_momentFiber

end RHTower
