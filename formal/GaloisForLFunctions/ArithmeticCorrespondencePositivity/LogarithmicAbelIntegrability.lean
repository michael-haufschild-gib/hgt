import GaloisForLFunctions.ArithmeticCorrespondencePositivity.LogarithmicAbelMeans
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.IntegrableLogarithmicStaircasesHaveHolomorphicMellinTransforms

/-!
# Absolute Abel integrability controls the continuous normalization

For a nonnegative power exponent, replacing the integer normalization
by its continuous logarithmic counterpart only decreases the absolute
integrand. Thus absolute Abel integrability gives a holomorphic contact
transform without a pointwise bound on the normalized sequence.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open SelbergClass.DegreeOne

/-- Absolute integrability for every positive logarithmic damping. -/
def LogarithmicAbelIntegrable (f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → IntegrableOn
    (fun u => stepLaplaceIntegrand f 0 u * abelKernel 0 (ε : ℂ) u) (Ioi 0)

/-- Logarithmic Abel averaging is the positive-staircase Mellin integral
at a real parameter, including its normalization factor. -/
theorem logarithmicAbelMean_eq_oneSidedStepMellin (f : ℕ → ℝ) (ε : ℝ) :
    logarithmicAbelMean f ε = oneSidedStepMellin f (ε : ℂ) := by
  rw [logarithmicAbelMean, abelIntegral, oneSidedStepMellin]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    simp only [stepLaplaceIntegrand, abelKernel, ofReal_zero, mul_zero,
      neg_zero, Complex.exp_zero, one_mul, zero_mul, Complex.cpow_zero, neg_mul]
    ring

/-- Subpolynomial sequences have every positive absolute Abel integral. -/
theorem logarithmicAbelIntegrable_of_strictGrowth
    {f : ℕ → ℝ} (hf : _root_.HTGeometry.StrictNaturalPowerGrowth f 0) :
    LogarithmicAbelIntegrable f := fun _ hε => integrableOn_logarithmicAbelIntegrand hf hε

/-- A finite linear combination preserves absolute Abel integrability. -/
theorem LogarithmicAbelIntegrable.sub {f g : ℕ → ℝ}
    (hf : LogarithmicAbelIntegrable f) (hg : LogarithmicAbelIntegrable g) :
    LogarithmicAbelIntegrable (fun N => f N - g N) := by
  intro ε hε
  apply ((hf ε hε).sub (hg ε hε)).congr
  exact Eventually.of_forall fun u => by
    simp only [stepLaplaceIntegrand, ofReal_sub]
    ring

/-- Scalar multiplication preserves absolute Abel integrability. -/
theorem LogarithmicAbelIntegrable.const_mul {f : ℕ → ℝ}
    (hf : LogarithmicAbelIntegrable f) (c : ℝ) :
    LogarithmicAbelIntegrable (fun N => c * f N) := by
  intro ε hε
  apply ((hf ε hε).const_mul (c : ℂ)).congr
  exact Eventually.of_forall fun u => by
    simp only [stepLaplaceIntegrand, ofReal_mul]
    ring

/-- The unused zero index does not affect absolute Abel integrability. -/
theorem LogarithmicAbelIntegrable.congr_pos {f g : ℕ → ℝ}
    (hf : LogarithmicAbelIntegrable f) (he : ∀ N : ℕ, 1 ≤ N → f N = g N) :
    LogarithmicAbelIntegrable g := by
  intro ε hε
  apply (hf ε hε).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hN : 1 ≤ ⌊Real.exp u⌋₊ := Nat.le_floor
    (by simpa only [Nat.cast_one] using Real.one_le_exp (le_of_lt hu))
  simp only [stepLaplaceIntegrand, he _ hN]

/-- Continuous power normalization is dominated by integer normalization
on positive logarithmic time. -/
theorem integrableOn_stepLaplaceIntegrand_of_normalized_abel
    {f : ℕ → ℝ} {θ c : ℝ} (hθ : 0 ≤ θ)
    (hf : LogarithmicAbelIntegrable (fun N => (N : ℝ) ^ (-θ) * f N))
    (hc : θ < c) :
    IntegrableOn (stepLaplaceIntegrand f (c : ℂ)) (Ioi 0) := by
  have hint := hf (c - θ) (sub_pos.mpr hc)
  apply hint.norm.mono' (measurable_stepLaplaceIntegrand f (c : ℂ)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hN : 1 ≤ ⌊Real.exp u⌋₊ := Nat.le_floor
    (by simpa only [Nat.cast_one] using Real.one_le_exp (le_of_lt hu))
  have hNp : (0 : ℝ) < ⌊Real.exp u⌋₊ := by exact_mod_cast hN
  have hp := Real.rpow_le_rpow_of_nonpos hNp (Nat.floor_le (Real.exp_pos u).le)
    (neg_nonpos.mpr hθ)
  rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp] at hp
  rw [norm_stepLaplaceIntegrand, ofReal_re, norm_mul, norm_stepLaplaceIntegrand,
    zero_re, zero_mul, neg_zero, Real.exp_zero, one_mul,
    norm_abelKernel 0 ((c - θ : ℝ) : ℂ) hu, ofReal_re,
    abs_mul, abs_of_pos (Real.rpow_pos_of_pos hNp _)]
  calc
    _ = (Real.exp (u * -θ) * |f ⌊Real.exp u⌋₊|) * Real.exp (-(c - θ) * u) := by
      rw [mul_right_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ ((⌊Real.exp u⌋₊ : ℝ) ^ (-θ) * |f ⌊Real.exp u⌋₊|) *
        Real.exp (-(c - θ) * u) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (abs_nonneg _))
        (Real.exp_pos _).le

/-- Absolute Abel integrability of normalized contacts provides the full
open holomorphy half-plane for their literal Mellin integral. -/
theorem differentiableOn_oneSidedStepMellin_of_normalized_abel
    {f : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ)
    (hf : LogarithmicAbelIntegrable (fun N => (N : ℝ) ^ (-θ) * f N)) :
    DifferentiableOn ℂ (oneSidedStepMellin f) {s : ℂ | θ < s.re} :=
  differentiableOn_oneSidedStepMellin fun _ hc =>
    integrableOn_stepLaplaceIntegrand_of_normalized_abel hθ hf hc

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
