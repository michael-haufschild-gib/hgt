import GaloisForLFunctions.RHTower.PrimeArchThetaScoreMomentDefect
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelSource
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Actual theta raw and score measures

The raw probability and countable positive score carrier retain every positive
source row and the same raw normalizer. Natural power integrability precedes
measure-series evaluation; the score dominates the complete square-weighted raw
law. These source inequalities supply no sign conclusion for a clock history.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal
namespace RHTower
noncomputable section
local notation "R0" => thetaCuspRawEvenMoment 0
local notation "nu" => thetaCuspNormalizedEvenMoment
local notation "mu0" => (volume.restrict (Ioi (0 : ℝ)))

/-- Exact odd-Ward score defect of a theta row. -/
def liClockThetaScoreDefect (n : ℕ) (x : ℝ) : ℝ :=
  1 + 32*x*thetaCuspBornWittenSuperpotential n x - 303*x^2

/-- Full theta source, normalized to a probability on the positive half-line. -/
def liClockThetaRawSourceMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun x => ENNReal.ofReal ((2/R0)*thetaCuspFullSource x))

/-- Score carrier for actual positive row `n + 1`, with the raw normalizer. -/
def liClockThetaScoreAtomMeasure (n : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal
    ((2*Real.pi/R0)*liClockThetaScoreDefect (n+1) x *
      thetaCuspBornWittenAmplitude (n+1) x ^ 2))

/-- Complete countable sum of the actual score carriers. -/
def liClockThetaScoreMeasure : Measure ℝ :=
  Measure.sum liClockThetaScoreAtomMeasure

/-- Normalized exact score recurrence, including degree zero. -/
def liClockThetaScoreMomentGap (j : ℕ) : ℝ :=
  (32*(j:ℝ)+17)*nu j - 303*nu (j+1)

private theorem hgt_score_normalizer_pos : 0 < R0 := thetaCuspRawEvenMoment_pos 0

private theorem hgt_score_density_l1 {rho f : ℝ → ℝ}
    (hr : Measurable rho) (hn : ∀ᵐ x ∂mu0, 0 ≤ rho x)
    (hi : Integrable (fun x => rho x * f x) mu0) :
    Integrable f ((mu0).withDensity (fun x => ENNReal.ofReal (rho x))) := by
  apply (integrable_withDensity_iff_integrable_smul' hr.ennreal_ofReal
    (by simp : ∀ᵐ x ∂mu0, ENNReal.ofReal (rho x) < ∞)).2
  apply hi.congr
  filter_upwards [hn] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]

private theorem hgt_score_density_integral {rho : ℝ → ℝ}
    (hr : Measurable rho) (hn : ∀ᵐ x ∂mu0, 0 ≤ rho x) (f : ℝ → ℝ) :
    (∫ x, f x ∂(mu0).withDensity (fun x => ENNReal.ofReal (rho x))) =
      ∫ x, rho x * f x ∂mu0 := by
  rw [integral_withDensity_eq_integral_toReal_smul hr.ennreal_ofReal
    (by simp : ∀ᵐ x ∂mu0, ENNReal.ofReal (rho x) < ∞)]
  apply integral_congr_ae
  filter_upwards [hn] with x hx
  simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]

private theorem hgt_score_raw_measurable :
    Measurable (fun x : ℝ => (2/R0)*thetaCuspFullSource x) :=
  contDiff_thetaCuspFullSource.continuous.measurable.const_mul _

private theorem hgt_score_raw_nonneg :
    ∀ᵐ x ∂mu0, 0 ≤ (2/R0)*thetaCuspFullSource x := by
  have hZ := hgt_score_normalizer_pos
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (by positivity)
    (thetaCuspFullSource_pos_of_pos hx).le

private theorem hgt_score_raw_power_l1 (m : ℕ) :
    Integrable (fun x : ℝ => x^m) liClockThetaRawSourceMeasure := by
  apply hgt_score_density_l1 hgt_score_raw_measurable hgt_score_raw_nonneg
  apply ((integrableOn_thetaCuspRawMoment m).const_mul (2/R0)).congr
  filter_upwards [] with x
  ring

/-- All normalized even moments of the literal raw probability. -/
theorem liClockThetaRawSourceMeasure_moment (j : ℕ) :
  (∫ x : ℝ, x^(2*j) ∂liClockThetaRawSourceMeasure) = nu j := by
  rw [liClockThetaRawSourceMeasure,
    hgt_score_density_integral hgt_score_raw_measurable hgt_score_raw_nonneg]
  have he : (fun x : ℝ => (2/R0)*thetaCuspFullSource x*x^(2*j)) =
      (fun x : ℝ => (2/R0)*(x^(2*j)*thetaCuspFullSource x)) := by
    ext x; ring
  rw [he,integral_const_mul]
  unfold thetaCuspNormalizedEvenMoment thetaCuspRawEvenMoment
  ring

private theorem hgt_score_raw_probability : IsProbabilityMeasure liClockThetaRawSourceMeasure := by
  refine ⟨?_⟩
  rw [liClockThetaRawSourceMeasure,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,←ofReal_integral_eq_lintegral_ofReal
      ((integrableOn_thetaCuspRawMoment 0).const_mul (2/R0) |>.congr (by
        filter_upwards [] with x
        simp)) hgt_score_raw_nonneg]
  have hm := liClockThetaRawSourceMeasure_moment 0
  rw [liClockThetaRawSourceMeasure,
    hgt_score_density_integral hgt_score_raw_measurable hgt_score_raw_nonneg] at hm
  simpa only [mul_zero,pow_zero,mul_one,thetaCuspNormalizedEvenMoment_zero,ENNReal.ofReal_one] using
    congrArg ENNReal.ofReal hm

private theorem hgt_score_density_support (rho : ℝ → ℝ) :
    ((mu0).withDensity (fun x => ENNReal.ofReal (rho x))) ((Ioi 0)ᶜ) = 0 := by
  apply withDensity_absolutelyContinuous _ _
  rw [Measure.restrict_apply measurableSet_Ioi.compl,compl_inter_self]
  exact measure_empty

private theorem hgt_score_raw_null : NullSingletonClass liClockThetaRawSourceMeasure := by
  unfold liClockThetaRawSourceMeasure
  infer_instance

/-- Probability, carrier, singleton nullity and genuine natural-power integrability. -/
theorem liClockThetaRawSourceMeasure_admission :
  IsProbabilityMeasure liClockThetaRawSourceMeasure ∧
  liClockThetaRawSourceMeasure ((Ioi 0)ᶜ) = 0 ∧
  NullSingletonClass liClockThetaRawSourceMeasure ∧
  ∀ m : ℕ, Integrable (fun x : ℝ => x^m) liClockThetaRawSourceMeasure := by
  exact ⟨hgt_score_raw_probability,hgt_score_density_support _,hgt_score_raw_null,
    hgt_score_raw_power_l1⟩

private theorem hgt_score_amplitude_measurable (n : ℕ) :
    Measurable (thetaCuspBornWittenAmplitude n) := by
  unfold thetaCuspBornWittenAmplitude thetaCuspBornWittenWeight
    thetaCuspMorseSuperpotential thetaCuspMorseGroundState thetaCuspMorseZeroMode
    thetaCuspMorseScale
  fun_prop

private theorem hgt_score_defect_measurable (n : ℕ) :
    Measurable (liClockThetaScoreDefect n) := by
  unfold liClockThetaScoreDefect thetaCuspBornWittenSuperpotential
    thetaCuspBornWittenWeight thetaCuspMorseSuperpotential thetaCuspMorseScale
  fun_prop

private theorem hgt_score_defect_square {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 0≤x) :
    (x-1)^2 ≤ liClockThetaScoreDefect n x :=
  thetaCuspBornWitten_scoreDefect_ge_square hn hx

private theorem hgt_score_defect_nonneg {n : ℕ} (hn : 0<n) {x : ℝ} (hx : 0≤x) :
    0 ≤ liClockThetaScoreDefect n x := (sq_nonneg _).trans (hgt_score_defect_square hn hx)

private theorem hgt_score_atom_measurable (n : ℕ) :
    Measurable (fun x : ℝ => (2*Real.pi/R0)*liClockThetaScoreDefect (n+1) x *
      thetaCuspBornWittenAmplitude (n+1) x ^ 2) := by
  exact ((hgt_score_defect_measurable (n+1)).const_mul _).mul
    ((hgt_score_amplitude_measurable (n+1)).pow_const 2)

private theorem hgt_score_atom_nonneg (n : ℕ) :
    ∀ᵐ x ∂mu0, 0 ≤ (2*Real.pi/R0)*liClockThetaScoreDefect (n+1) x *
      thetaCuspBornWittenAmplitude (n+1) x ^ 2 := by
  have hZ := hgt_score_normalizer_pos
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (mul_nonneg (by positivity)
    (hgt_score_defect_nonneg (by omega) hx.le)) (sq_nonneg _)

private theorem hgt_score_atom_power_density_l1 (m n : ℕ) :
    Integrable (fun x : ℝ => x^m * liClockThetaScoreDefect (n+1) x *
      thetaCuspBornWittenAmplitude (n+1) x ^ 2) mu0 := by
  have h0 := integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq m
    (n:=n+1) (by omega)
  have hw := integrableOn_pow_mul_thetaCuspBornWittenSuperpotential_mul_amplitude_sq
    (m+1) (n:=n+1) (by omega)
  have h2 := integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (m+2)
    (n:=n+1) (by omega)
  apply ((h0.add (hw.const_mul 32)).sub (h2.const_mul 303)).congr
  filter_upwards [] with x
  simp only [liClockThetaScoreDefect,Pi.add_apply,Pi.sub_apply,pow_add,pow_one]
  ring

private theorem hgt_score_atom_power_l1 (m n : ℕ) :
    Integrable (fun x : ℝ => x^m) (liClockThetaScoreAtomMeasure n) := by
  apply hgt_score_density_l1 (hgt_score_atom_measurable n) (hgt_score_atom_nonneg n)
  apply ((hgt_score_atom_power_density_l1 m n).const_mul (2*Real.pi/R0)).congr
  filter_upwards [] with x
  ring

/-- Exact row Ward identity, preserving its factor `2 * pi`. -/
theorem liClockThetaScoreAtom_moment_identity (j n : ℕ) :
  (32*(j:ℝ)+17)*thetaCuspAtomRawEvenMoment j (n+1) -
    303*thetaCuspAtomRawEvenMoment (j+1) (n+1) =
  2*Real.pi * ∫ x : ℝ in Ioi 0,
    x^(2*j)*liClockThetaScoreDefect (n+1) x *
      thetaCuspBornWittenAmplitude (n+1) x ^ 2 := by
  rw [thetaCuspAtomRawEvenMoment_eq_morseBornMoment,
    thetaCuspAtomRawEvenMoment_eq_morseBornMoment]
  have h := thetaCuspMorseBornMoment_scoreGap_eq_integral j (n:=n+1) (by omega)
  dsimp only [liClockThetaScoreDefect]
  rw [←h]
  ring


private theorem hgt_score_source_tail_sum (x : ℝ) :
    (∑' n : ℕ, thetaCuspSourceTerm x (n+1)) = thetaCuspFullSource x := by
  have hs := summable_thetaCuspSourceTerm x
  have hz : thetaCuspSourceTerm x 0 = 0 := by
    simp [thetaCuspSourceTerm,thetaCuspSeed]
  have he := hs.sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one,hz,zero_add,thetaCuspFullSource] using he

private theorem hgt_score_raw_row_sum {x : ℝ} (hx : 0≤x) :
    Summable (fun n : ℕ => (2*Real.pi/R0)*
      thetaCuspBornWittenAmplitude (n+1) x^2) ∧
    (∑' n : ℕ, (2*Real.pi/R0)*thetaCuspBornWittenAmplitude (n+1) x^2) =
      (2/R0)*thetaCuspFullSource x := by
  have hs : Summable (fun n : ℕ => (2/R0)*thetaCuspSourceTerm x (n+1)) :=
    ((summable_nat_add_iff 1).2 (summable_thetaCuspSourceTerm x)).mul_left _
  have he (n : ℕ) : (2/R0)*thetaCuspSourceTerm x (n+1) =
      (2*Real.pi/R0)*thetaCuspBornWittenAmplitude (n+1) x^2 := by
    rw [thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq (by omega) hx]
    ring
  refine ⟨hs.congr he,?_⟩
  rw [←tsum_congr he,tsum_mul_left,hgt_score_source_tail_sum]

/-- Equality of full raw measures, retaining every positive theta row. -/
theorem liClockThetaRawSourceMeasure_eq_sum_atoms :
  liClockThetaRawSourceMeasure = Measure.sum (fun n : ℕ =>
    (volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal
      ((2*Real.pi/R0)*thetaCuspBornWittenAmplitude (n+1) x ^ 2))) := by
  have hm (n : ℕ) : Measurable (fun x : ℝ => ENNReal.ofReal
      ((2*Real.pi/R0)*thetaCuspBornWittenAmplitude (n+1) x^2)) :=
    (((hgt_score_amplitude_measurable (n+1)).pow_const 2).const_mul _).ennreal_ofReal
  rw [←withDensity_tsum (μ:=mu0) hm]
  apply withDensity_congr_ae
  have hZ := hgt_score_normalizer_pos
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [tsum_apply (Pi.summable.2 (fun _ => ENNReal.summable)),
    ←ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (by positivity) (sq_nonneg _))
      (hgt_score_raw_row_sum hx.le).1,(hgt_score_raw_row_sum hx.le).2]

private theorem hgt_score_atom_even_moment (j n : ℕ) :
    (∫ x : ℝ, x^(2*j) ∂liClockThetaScoreAtomMeasure n) =
      ((32*(j:ℝ)+17)*thetaCuspAtomRawEvenMoment j (n+1)-
        303*thetaCuspAtomRawEvenMoment (j+1) (n+1))/R0 := by
  rw [liClockThetaScoreAtomMeasure,hgt_score_density_integral
    (hgt_score_atom_measurable n) (hgt_score_atom_nonneg n)]
  have he : (fun x : ℝ => (2*Real.pi/R0)*liClockThetaScoreDefect (n+1) x *
      thetaCuspBornWittenAmplitude (n+1) x^2 * x^(2*j)) =
      (fun x : ℝ => (2*Real.pi/R0)*(x^(2*j)*liClockThetaScoreDefect (n+1) x *
      thetaCuspBornWittenAmplitude (n+1) x^2)) := by ext x; ring
  rw [he,integral_const_mul,liClockThetaScoreAtom_moment_identity]
  ring

private theorem hgt_score_atom_raw_summable (j : ℕ) :
    Summable (fun n : ℕ => thetaCuspAtomRawEvenMoment j n) := by
  by_contra h
  have hz := tsum_eq_zero_of_not_summable h
  have he := thetaCuspRawEvenMoment_eq_tsum_atomRawEvenMoment j
  have hp := thetaCuspRawEvenMoment_pos j
  linarith

private theorem hgt_score_atom_raw_tail_sum (j : ℕ) :
    (∑' n : ℕ, thetaCuspAtomRawEvenMoment j (n+1)) = thetaCuspRawEvenMoment j := by
  have he := (hgt_score_atom_raw_summable j).sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one,thetaCuspAtomRawEvenMoment_zero,zero_add,
    ←thetaCuspRawEvenMoment_eq_tsum_atomRawEvenMoment] using he

private theorem hgt_score_atom_even_summable (j : ℕ) :
    Summable (fun n : ℕ => ∫ x : ℝ, x^(2*j) ∂liClockThetaScoreAtomMeasure n) := by
  simp_rw [hgt_score_atom_even_moment,div_eq_mul_inv]
  exact (((summable_nat_add_iff 1).2 (hgt_score_atom_raw_summable j)).mul_left _ |>.sub
    (((summable_nat_add_iff 1).2 (hgt_score_atom_raw_summable (j+1))).mul_left _)).mul_right _

private theorem hgt_score_atom_carrier (n : ℕ) :
    ∀ᵐ x ∂liClockThetaScoreAtomMeasure n, 0<x := by
  rw [liClockThetaScoreAtomMeasure,ae_withDensity_iff
    (hgt_score_atom_measurable n).ennreal_ofReal]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx _
  exact hx

private theorem hgt_score_atom_even_norm_integral (j n : ℕ) :
    (∫ x : ℝ, ‖x^(2*j)‖ ∂liClockThetaScoreAtomMeasure n) =
      ∫ x : ℝ, x^(2*j) ∂liClockThetaScoreAtomMeasure n := by
  apply integral_congr_ae
  filter_upwards [hgt_score_atom_carrier n] with x hx
  exact Real.norm_of_nonneg (pow_nonneg hx.le _)

private theorem hgt_score_atom_power_norm_le (m n : ℕ) :
    (∫ x : ℝ, ‖x^m‖ ∂liClockThetaScoreAtomMeasure n) ≤
      (∫ x : ℝ, x^0 ∂liClockThetaScoreAtomMeasure n) +
      (∫ x : ℝ, x^(2*m) ∂liClockThetaScoreAtomMeasure n) := by
  rw [←integral_add (hgt_score_atom_power_l1 0 n) (hgt_score_atom_power_l1 (2*m) n)]
  apply integral_mono_ae (hgt_score_atom_power_l1 m n |>.norm)
    ((hgt_score_atom_power_l1 0 n).add (hgt_score_atom_power_l1 (2*m) n))
  filter_upwards [hgt_score_atom_carrier n] with x hx
  rw [Real.norm_of_nonneg (pow_nonneg hx.le _)]
  simp only [Pi.add_apply,pow_zero]
  have hp : x^(2*m) = (x^m)^2 := by rw [show 2*m=m*2 by omega,pow_mul]
  rw [hp]
  nlinarith [sq_nonneg (x^m-1)]

private theorem hgt_score_atom_power_norm_summable (m : ℕ) :
    Summable (fun n : ℕ => ∫ x : ℝ, ‖x^m‖ ∂liClockThetaScoreAtomMeasure n) := by
  apply Summable.of_nonneg_of_le
    (fun n => integral_nonneg (fun _ => norm_nonneg _))
    (fun n => hgt_score_atom_power_norm_le m n)
  exact (hgt_score_atom_even_summable 0).add (hgt_score_atom_even_summable m)

private theorem hgt_score_power_l1 (m : ℕ) :
    Integrable (fun x : ℝ => x^m) liClockThetaScoreMeasure :=
  integrable_sum_measure (hgt_score_atom_power_l1 m) (hgt_score_atom_power_norm_summable m)

private theorem hgt_score_finite : IsFiniteMeasure liClockThetaScoreMeasure := by
  apply (integrable_const_iff_isFiniteMeasure (c:=(1:ℝ)) (by norm_num)).1
  simpa only [pow_zero] using hgt_score_power_l1 0

private theorem hgt_score_support : liClockThetaScoreMeasure ((Ioi 0)ᶜ) = 0 := by
  rw [liClockThetaScoreMeasure,Measure.sum_apply _ measurableSet_Ioi.compl]
  have he (n : ℕ) : liClockThetaScoreAtomMeasure n ((Ioi 0)ᶜ) = 0 :=
    hgt_score_density_support _
  simp only [he,tsum_zero]

private theorem hgt_score_null : NullSingletonClass liClockThetaScoreMeasure := by
  refine ⟨fun x => ?_⟩
  rw [liClockThetaScoreMeasure,Measure.sum_apply _ (measurableSet_singleton x)]
  have he (n : ℕ) : liClockThetaScoreAtomMeasure n {x} = 0 := by
    unfold liClockThetaScoreAtomMeasure
    exact measure_singleton x
  simp only [he,tsum_zero]

/-- Finite full score measure, with genuine natural-power integrability. -/
theorem liClockThetaScoreMeasure_admission :
  IsFiniteMeasure liClockThetaScoreMeasure ∧
  liClockThetaScoreMeasure ((Ioi 0)ᶜ) = 0 ∧
  NullSingletonClass liClockThetaScoreMeasure ∧
  ∀ m : ℕ, Integrable (fun x : ℝ => x^m) liClockThetaScoreMeasure := by
  exact ⟨hgt_score_finite,hgt_score_support,hgt_score_null,hgt_score_power_l1⟩

/-- The complete score moment equals its normalized recurrence gap. -/
theorem liClockThetaScoreMeasure_moment (j : ℕ) :
  (∫ x : ℝ, x^(2*j) ∂liClockThetaScoreMeasure) =
    liClockThetaScoreMomentGap j := by
  rw [liClockThetaScoreMeasure,integral_sum_measure (hgt_score_power_l1 (2*j))]
  simp_rw [hgt_score_atom_even_moment,div_eq_mul_inv]
  have hj := (summable_nat_add_iff 1).2 (hgt_score_atom_raw_summable j)
  have hj1 := (summable_nat_add_iff 1).2 (hgt_score_atom_raw_summable (j+1))
  rw [tsum_mul_right,Summable.tsum_sub (hj.mul_left _) (hj1.mul_left _),
    tsum_mul_left,tsum_mul_left,hgt_score_atom_raw_tail_sum,hgt_score_atom_raw_tail_sum]
  simp only [liClockThetaScoreMomentGap,thetaCuspNormalizedEvenMoment]
  ring

private theorem hgt_score_first_square_l1 (j : ℕ) :
    Integrable (fun x : ℝ => x^(2*j)*(x-1)^2 *
      thetaCuspBornWittenAmplitude 1 x^2) mu0 := by
  have h0 := integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2*j)
    (n:=1) (by norm_num)
  have h1 := integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2*j+1)
    (n:=1) (by norm_num)
  have h2 := integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2*j+2)
    (n:=1) (by norm_num)
  apply ((h2.sub (h1.const_mul 2)).add h0).congr
  filter_upwards [] with x
  simp only [Pi.add_apply,Pi.sub_apply,pow_add,pow_one]
  ring

private theorem hgt_score_first_square_pos (j : ℕ) :
    0 < ∫ x : ℝ in Ioi 0, x^(2*j)*(x-1)^2 *
      thetaCuspBornWittenAmplitude 1 x^2 := by
  have hn : ∀ᵐ x ∂mu0, 0 ≤ x^(2*j)*(x-1)^2 *
      thetaCuspBornWittenAmplitude 1 x^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (mul_nonneg (pow_nonneg hx.le _) (sq_nonneg _)) (sq_nonneg _)
  apply (integral_pos_iff_support_of_nonneg_ae hn (hgt_score_first_square_l1 j)).2
  have hs : Ioo (2 : ℝ) 3 ⊆ Function.support (fun x : ℝ =>
      x^(2*j)*(x-1)^2 * thetaCuspBornWittenAmplitude 1 x^2) := by
    intro x hx
    change x^(2*j)*(x-1)^2 * thetaCuspBornWittenAmplitude 1 x^2 ≠ 0
    exact (mul_pos (mul_pos (pow_pos (by linarith [hx.1]) _)
      (sq_pos_of_ne_zero (by linarith [hx.1])))
      (sq_pos_of_pos (thetaCuspBornWittenAmplitude_pos (by norm_num)
        (by linarith [hx.1])))).ne'
  have he : Ioo (2 : ℝ) 3 ∩ Ioi 0 = Ioo (2 : ℝ) 3 := by
    ext x
    simp only [mem_inter_iff,mem_Ioo,mem_Ioi]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h,by linarith [h.1]⟩
  have hp : 0 < (mu0) (Ioo (2 : ℝ) 3) := by
    rw [Measure.restrict_apply measurableSet_Ioo,he]
    norm_num [Real.volume_Ioo]
  exact hp.trans_le (measure_mono hs)

private theorem hgt_score_gap_raw (j : ℕ) :
    liClockThetaScoreMomentGap j =
      ((32*(j:ℝ)+17)*thetaCuspRawEvenMoment j -
        303*thetaCuspRawEvenMoment (j+1))/R0 := by
  simp only [liClockThetaScoreMomentGap,thetaCuspNormalizedEvenMoment]
  ring

/-- Strict square reserve and finite recurrence ceiling in every even degree. -/
theorem liClockThetaScoreMomentGap_bounds (j : ℕ) :
  0 < liClockThetaScoreMomentGap j ∧
  liClockThetaScoreMomentGap j ≤ (32*(j:ℝ)+17)*nu j := by
  constructor
  · rw [hgt_score_gap_raw]
    apply div_pos _ hgt_score_normalizer_pos
    exact (mul_pos (by positivity) (hgt_score_first_square_pos j)).trans_le
      (thetaCuspRawEvenMoment_scoreGap_ge_firstAtomSquare j)
  · unfold liClockThetaScoreMomentGap
    have h := thetaCuspNormalizedEvenMoment_pos (j+1)
    linarith

private theorem hgt_score_mass :
    liClockThetaScoreMeasure.real univ = liClockThetaScoreMomentGap 0 := by
  letI := hgt_score_finite
  simpa only [mul_zero,pow_zero,integral_const,smul_eq_mul,mul_one] using
    liClockThetaScoreMeasure_moment 0

private theorem hgt_score_mass_pos : 0 < liClockThetaScoreMeasure.real univ := by
  rw [hgt_score_mass]
  exact (liClockThetaScoreMomentGap_bounds 0).1

private theorem hgt_score_raw_square_l1 :
    Integrable (fun x : ℝ => (x-1)^2) liClockThetaRawSourceMeasure := by
  apply (((hgt_score_raw_power_l1 2).sub
    ((hgt_score_raw_power_l1 1).const_mul 2)).add (hgt_score_raw_power_l1 0)).congr
  filter_upwards [] with x
  simp only [Pi.add_apply,Pi.sub_apply,pow_one,pow_zero]
  ring

private theorem hgt_score_square_measurable :
    Measurable (fun x : ℝ => ENNReal.ofReal ((x-1)^2)) := by fun_prop

private theorem hgt_score_raw_row_measurable (n : ℕ) :
    Measurable (fun x : ℝ => ENNReal.ofReal
      ((2*Real.pi/R0)*thetaCuspBornWittenAmplitude (n+1) x^2)) :=
  (((hgt_score_amplitude_measurable (n+1)).pow_const 2).const_mul _).ennreal_ofReal

private theorem hgt_score_row_square_domination (n : ℕ) :
    ((mu0).withDensity (fun x : ℝ => ENNReal.ofReal
      ((2*Real.pi/R0)*thetaCuspBornWittenAmplitude (n+1) x^2))).withDensity
      (fun x => ENNReal.ofReal ((x-1)^2)) ≤ liClockThetaScoreAtomMeasure n := by
  rw [←withDensity_mul (mu0) (hgt_score_raw_row_measurable n)
    hgt_score_square_measurable]
  apply withDensity_mono
  have hZ := hgt_score_normalizer_pos
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hc : 0 ≤ (2*Real.pi/R0)*thetaCuspBornWittenAmplitude (n+1) x^2 := by positivity
  rw [Pi.mul_apply,←ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_mono
  calc
    (2*Real.pi/R0)*thetaCuspBornWittenAmplitude (n+1) x^2 * (x-1)^2 ≤
        (2*Real.pi/R0)*thetaCuspBornWittenAmplitude (n+1) x^2 *
          liClockThetaScoreDefect (n+1) x :=
      mul_le_mul_of_nonneg_left (hgt_score_defect_square (by omega) hx.le) hc
    _ = (2*Real.pi/R0)*liClockThetaScoreDefect (n+1) x *
        thetaCuspBornWittenAmplitude (n+1) x^2 := by ring

/-- The full square-weighted raw measure is finite and dominated by the score law. -/
theorem liClockThetaScoreMeasure_square_domination :
  IsFiniteMeasure (liClockThetaRawSourceMeasure.withDensity
    (fun x => ENNReal.ofReal ((x-1)^2))) ∧
  liClockThetaRawSourceMeasure.withDensity
    (fun x => ENNReal.ofReal ((x-1)^2)) ≤ liClockThetaScoreMeasure := by
  refine ⟨isFiniteMeasure_withDensity_ofReal hgt_score_raw_square_l1.hasFiniteIntegral,?_⟩
  rw [liClockThetaRawSourceMeasure_eq_sum_atoms,withDensity_sum,
    liClockThetaScoreMeasure]
  apply Measure.le_iff.2
  intro s hs
  rw [Measure.sum_apply _ hs,Measure.sum_apply _ hs]
  exact ENNReal.tsum_le_tsum (fun n => hgt_score_row_square_domination n s)

/-- Transfer every nonnegative measurable score-integrable test to the square law. -/
theorem liClockThetaScoreMeasure_nonnegative_test (f : ℝ → ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f liClockThetaScoreMeasure) :
  Integrable (fun x => (x-1)^2*f x) liClockThetaRawSourceMeasure ∧
  (∫ x, (x-1)^2*f x ∂liClockThetaRawSourceMeasure) ≤
    ∫ x, f x ∂liClockThetaScoreMeasure := by
  have hle := liClockThetaScoreMeasure_square_domination.2
  have hi : Integrable f (liClockThetaRawSourceMeasure.withDensity
      (fun x => ENNReal.ofReal ((x-1)^2))) :=
    ⟨hf.aestronglyMeasurable,(hfi.mono_measure hle).hasFiniteIntegral⟩
  have hw := (integrable_withDensity_iff_integrable_smul'
    hgt_score_square_measurable (by simp : ∀ᵐ x ∂liClockThetaRawSourceMeasure,
      ENNReal.ofReal ((x-1)^2) < ∞)).1 hi
  have he : (fun x : ℝ => (ENNReal.ofReal ((x-1)^2)).toReal • f x) =
      (fun x : ℝ => (x-1)^2*f x) := by
    ext x
    simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]
  refine ⟨he ▸ hw,?_⟩
  have hm := integral_mono_measure hle (Filter.Eventually.of_forall hf0) hfi
  rw [integral_withDensity_eq_integral_toReal_smul hgt_score_square_measurable
    (by simp : ∀ᵐ x ∂liClockThetaRawSourceMeasure,
      ENNReal.ofReal ((x-1)^2) < ∞),he] at hm
  exact hm

end
end RHTower
