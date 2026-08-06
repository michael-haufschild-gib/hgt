import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Small-ball lower bound for a standard Gaussian coefficient vector

The one-dimensional standard Gaussian charges a centred interval of radius
`ρ ≤ 1` with at least the minimal density on that interval times its length.
Taking the product over `v` independent coordinates, a standard Gaussian vector
in `v` dimensions charges the centred cube of radius `ρ` with at least a fixed
constant times `ρ ^ v`.  This is the small-ball input behind the transverse
Gaussian lower bound on the shortcut probability, and it is the source of the
exponent `v`.
-/

open MeasureTheory Metric Real
open scoped NNReal ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- The density floor of the standard Gaussian on the unit interval. -/
noncomputable def gaussianDensityFloor : ℝ := (√(2 * π))⁻¹ * rexp (-(1 : ℝ) / 2)

theorem gaussianDensityFloor_pos : 0 < gaussianDensityFloor := by
  have h : 0 < √(2 * π) := Real.sqrt_pos.mpr (by positivity)
  unfold gaussianDensityFloor
  positivity

/-- The standard Gaussian density is bounded below on the unit interval. -/
theorem gaussianPDFReal_ge_floor {x : ℝ} (hx : |x| ≤ 1) :
    gaussianDensityFloor ≤ ProbabilityTheory.gaussianPDFReal 0 1 x := by
  have hval : ProbabilityTheory.gaussianPDFReal 0 1 x
      = (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) := by
    unfold ProbabilityTheory.gaussianPDFReal
    norm_num
  have hsq : x ^ 2 ≤ 1 := by
    rcases abs_le.mp hx with ⟨h1, h2⟩
    nlinarith
  have hexp : rexp (-(1 : ℝ) / 2) ≤ rexp (-x ^ 2 / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpos : (0 : ℝ) ≤ (√(2 * π))⁻¹ := by positivity
  rw [hval, gaussianDensityFloor]
  exact mul_le_mul_of_nonneg_left hexp hpos

/-- **One-dimensional small-ball bound.**  A centred interval of radius at most
one carries at least the density floor times its length. -/
theorem gaussianReal_Icc_lower {ρ : ℝ} (hρ1 : ρ ≤ 1) :
    ENNReal.ofReal (gaussianDensityFloor * (2 * ρ))
      ≤ ProbabilityTheory.gaussianReal 0 1 (Set.Icc (-ρ) ρ) := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero _ one_ne_zero,
    withDensity_apply _ measurableSet_Icc]
  have hfloor : ∀ x ∈ Set.Icc (-ρ) ρ,
      ENNReal.ofReal gaussianDensityFloor ≤ ProbabilityTheory.gaussianPDF 0 1 x := by
    intro x hx
    refine ENNReal.ofReal_le_ofReal (gaussianPDFReal_ge_floor ?_)
    rw [abs_le]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmono : ∫⁻ _ in Set.Icc (-ρ) ρ, ENNReal.ofReal gaussianDensityFloor
      ≤ ∫⁻ x in Set.Icc (-ρ) ρ, ProbabilityTheory.gaussianPDF 0 1 x :=
    setLIntegral_mono' measurableSet_Icc hfloor
  refine le_trans ?_ hmono
  rw [setLIntegral_const, Real.volume_Icc,
    ← ENNReal.ofReal_mul (le_of_lt gaussianDensityFloor_pos)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

/-- **Small-ball lower bound.**  A standard Gaussian vector in `v` coordinates
charges the centred cube of radius `ρ ≤ 1` with at least a fixed positive
constant times `ρ ^ v`. -/
theorem measure_pi_gaussian_closedBall_lower (v : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) :
    ENNReal.ofReal ((2 * gaussianDensityFloor) ^ v * ρ ^ v)
      ≤ (Measure.pi fun _ : Fin v => ProbabilityTheory.gaussianReal 0 1)
          (closedBall (0 : Fin v → ℝ) ρ) := by
  have hball : closedBall (0 : Fin v → ℝ) ρ
      = Set.univ.pi fun _ : Fin v => Set.Icc (-ρ) ρ := by
    rw [closedBall_pi _ hρ0]
    refine Set.pi_congr rfl fun i _ => ?_
    rw [Real.closedBall_eq_Icc]
    simp
  rw [hball, Measure.pi_pi]
  have hbase : (0 : ℝ) ≤ gaussianDensityFloor * (2 * ρ) :=
    mul_nonneg (le_of_lt gaussianDensityFloor_pos) (by linarith)
  have hstep : ∏ _i : Fin v, ENNReal.ofReal (gaussianDensityFloor * (2 * ρ))
      ≤ ∏ _i : Fin v, ProbabilityTheory.gaussianReal 0 1 (Set.Icc (-ρ) ρ) :=
    Finset.prod_le_prod' fun i _ => gaussianReal_Icc_lower hρ1
  refine le_trans (le_of_eq ?_) hstep
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow hbase]
  congr 1
  rw [← mul_pow]
  ring_nf

/-- **Transverse Gaussian shortcut mass.**  At time `t` the transverse Gaussian
ball of radius `ε / (L t)` carries at least a fixed constant times `t ^ (-v)`. -/
theorem measure_pi_gaussian_transverse_ball_lower (v : ℕ) {L ε t : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (ht : 0 < t) (hle : ε ≤ L * t) :
    ENNReal.ofReal ((2 * gaussianDensityFloor * (ε / L)) ^ v * (t ^ v)⁻¹)
      ≤ (Measure.pi fun _ : Fin v => ProbabilityTheory.gaussianReal 0 1)
          (closedBall (0 : Fin v → ℝ) (ε / (L * t))) := by
  have hLt : 0 < L * t := mul_pos hL ht
  have hρ0 : (0 : ℝ) ≤ ε / (L * t) := le_of_lt (div_pos hε hLt)
  have hρ1 : ε / (L * t) ≤ 1 := (div_le_one hLt).mpr hle
  refine le_trans (le_of_eq ?_) (measure_pi_gaussian_closedBall_lower v hρ0 hρ1)
  congr 1
  have hrw : 2 * gaussianDensityFloor * (ε / L) * t⁻¹
      = 2 * gaussianDensityFloor * (ε / (L * t)) := by
    field_simp
  rw [← inv_pow, ← mul_pow, hrw, mul_pow]

end GaloisForLFunctions.HTGeometry
