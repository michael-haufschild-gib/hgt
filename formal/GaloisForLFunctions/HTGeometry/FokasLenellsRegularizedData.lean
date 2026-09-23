import GaloisForLFunctions.HTGeometry.FokasLenellsScatteringContinuity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Genuine regularized scattering data for the Fokas–Lenells jump

The constructed uniformized scattering matrix gives the coefficients of
(3.32)–(3.35) in arXiv:2607.19649v1. In the corpus's jump convention the
lower parameter is minus the paper's `r₂`; the upper parameter is `r₁`.
A single explicit rescaling of each Schwartz potential keeps every matrix
entry within one quarter of the identity for all real uniformized spectra.
Both quotients are continuous and bounded by one third. Prescribed singular
time phases preserve the bounds and measurability, supplying actual data
for the inverse Cauchy equation. No nonlinear reconstruction is asserted.
-/

open Complex Matrix Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The actual uniformized scattering matrix, evaluated at the derivative profiles of the potential. -/
def regularScatteringMatrix (q : SchwartzMap ℝ ℂ) (z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  uniformizedScatteringMatrix (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) z

theorem regularScatteringMatrix_det (q : SchwartzMap ℝ ℂ) (z : ℝ) :
    (regularScatteringMatrix q z).det = 1 := uniformizedScatteringMatrix_det _ _ _ _

theorem continuous_regularScatteringMatrix (q : SchwartzMap ℝ ℂ) : Continuous (regularScatteringMatrix q) :=
  continuous_uniformizedScatteringMatrix _ _ _

/-- Every entry stays within one quarter of the identity, for all real uniformized spectra. -/
theorem globalSmall_regularScatteringMatrix_bound (q : SchwartzMap ℝ ℂ) (z : ℝ) (i j : Fin 2) :
    ‖regularScatteringMatrix (globalSmallScatteringPotential q) z i j-(1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ 1/4 := by
  exact (uniformizedScatteringMatrix_entry_displacement _ _ _ z i j).trans
    (globalSmallScatteringPotential_error q)

theorem globalSmall_regularTransmission_lower (q : SchwartzMap ℝ ℂ) (z : ℝ) :
    3/4 ≤ ‖regularScatteringMatrix (globalSmallScatteringPotential q) z 0 0‖ ∧
    3/4 ≤ ‖regularScatteringMatrix (globalSmallScatteringPotential q) z 1 1‖ := by
  have h0 := globalSmall_regularScatteringMatrix_bound q z 0 0
  have h1 := globalSmall_regularScatteringMatrix_bound q z 1 1
  simp only [Matrix.one_apply_eq] at h0 h1
  have hn0 := norm_sub_norm_le (1:ℂ) (regularScatteringMatrix (globalSmallScatteringPotential q) z 0 0)
  have hn1 := norm_sub_norm_le (1:ℂ) (regularScatteringMatrix (globalSmallScatteringPotential q) z 1 1)
  rw [norm_one, norm_sub_rev] at hn0 hn1
  constructor <;> linarith

theorem globalSmall_regularTransmission_nonzero (q : SchwartzMap ℝ ℂ) (z : ℝ) :
    regularScatteringMatrix (globalSmallScatteringPotential q) z 0 0 ≠ 0 ∧
    regularScatteringMatrix (globalSmallScatteringPotential q) z 1 1 ≠ 0 := by
  have hb := globalSmall_regularTransmission_lower q z
  constructor <;> apply norm_pos_iff.mp <;> linarith [hb.1,hb.2]

/-- The lower coefficient is minus the paper's `r₂`, matching `jump a b = !![1,b;-a,1-a*b]`. -/
def regularReflectionCoefficient (q : SchwartzMap ℝ ℂ) (z : ℝ) : ℂ :=
  regularScatteringMatrix q z 1 0/regularScatteringMatrix q z 0 0

/-- The upper coefficient is the paper's `r₁`. -/
def regularReverseReflectionCoefficient (q : SchwartzMap ℝ ℂ) (z : ℝ) : ℂ :=
  regularScatteringMatrix q z 0 1/regularScatteringMatrix q z 1 1

/-- The regularized reflection definitions agree with the gauge factors in (3.33). -/
theorem regularReflectionCoefficients_gauge (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    regularReflectionCoefficient q ((Real.exp κ)^(2 : ℕ)) =
      -(2*(Real.exp κ:ℂ))*reflectionCoefficient q κ ∧
    regularReverseReflectionCoefficient q ((Real.exp κ)^(2 : ℕ)) =
      -(reverseReflectionCoefficient q κ)/(2*(Real.exp κ:ℂ)) := by
  constructor <;> simp [regularReflectionCoefficient, regularReverseReflectionCoefficient, regularScatteringMatrix,
    uniformizedScatteringMatrix_amplitudes, ← Complex.ofReal_exp,
    reflectionCoefficient, reverseReflectionCoefficient] <;> ring

/-- The two genuine regularized reflection coefficients are uniformly small on the entire real line. -/
theorem globalSmall_regularReflection_bounds (q : SchwartzMap ℝ ℂ) (z : ℝ) :
    ‖regularReflectionCoefficient (globalSmallScatteringPotential q) z‖ ≤ 1/3 ∧
    ‖regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z‖ ≤ 1/3 := by
  have hl := globalSmall_regularTransmission_lower q z
  have h0 := globalSmall_regularScatteringMatrix_bound q z 1 0
  have h1 := globalSmall_regularScatteringMatrix_bound q z 0 1
  simp at h0 h1
  constructor
  · rw [regularReflectionCoefficient, norm_div]
    apply (div_le_iff₀ (by linarith [hl.1])).mpr
    linarith [hl.1]
  · rw [regularReverseReflectionCoefficient, norm_div]
    apply (div_le_iff₀ (by linarith [hl.2])).mpr
    linarith [hl.2]

/-- Continuity includes the uniformized origin; no transmission-zero premise is needed. -/
theorem continuous_globalSmall_regularReflection (q : SchwartzMap ℝ ℂ) :
    Continuous (regularReflectionCoefficient (globalSmallScatteringPotential q)) ∧
    Continuous (regularReverseReflectionCoefficient (globalSmallScatteringPotential q)) := by
  have hc (i j : Fin 2) : Continuous (fun z => regularScatteringMatrix (globalSmallScatteringPotential q) z i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_regularScatteringMatrix _))
  exact ⟨(hc 1 0).div (hc 0 0) (fun z => (globalSmall_regularTransmission_nonzero q z).1),
    (hc 0 1).div (hc 1 1) (fun z => (globalSmall_regularTransmission_nonzero q z).2)⟩

def regularJumpReflection (q : SchwartzMap ℝ ℂ) (t x z : ℝ) : ℂ :=
  FDNLS.staggerPhase 2 (z*x-t/(4*z))*regularReflectionCoefficient q z

def regularJumpReverseReflection (q : SchwartzMap ℝ ℂ) (t x z : ℝ) : ℂ :=
  FDNLS.staggerPhase (-2) (z*x-t/(4*z))*regularReverseReflectionCoefficient q z

theorem regularJumpReflection_norms (q : SchwartzMap ℝ ℂ) (t x z : ℝ) :
    ‖regularJumpReflection q t x z‖ = ‖regularReflectionCoefficient q z‖ ∧
    ‖regularJumpReverseReflection q t x z‖ = ‖regularReverseReflectionCoefficient q z‖ := by
  simp [regularJumpReflection, regularJumpReverseReflection, FDNLS.norm_staggerPhase]

/-- The singular time phase is still measurable, so both actual jump symbols are measurable. -/
theorem measurable_globalSmall_regularJump (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    Measurable (regularJumpReflection (globalSmallScatteringPotential q) t x) ∧
    Measurable (regularJumpReverseReflection (globalSmallScatteringPotential q) t x) := by
  have hphase (s : ℝ) : Measurable (fun z : ℝ => FDNLS.staggerPhase s (z*x-t/(4*z))) := by
    unfold FDNLS.staggerPhase
    fun_prop
  exact ⟨(hphase 2).mul (continuous_globalSmall_regularReflection q).1.measurable,
    (hphase (-2)).mul (continuous_globalSmall_regularReflection q).2.measurable⟩

theorem globalSmall_regularJump_bounds (q : SchwartzMap ℝ ℂ) (t x z : ℝ) :
    ‖regularJumpReflection (globalSmallScatteringPotential q) t x z‖ ≤ 1/3 ∧
    ‖regularJumpReverseReflection (globalSmallScatteringPotential q) t x z‖ ≤ 1/3 := by
  rw [(regularJumpReflection_norms _ t x z).1, (regularJumpReflection_norms _ t x z).2]
  exact globalSmall_regularReflection_bounds q z

/-- The jump is exactly `I+R` with `r₁ = upper` and `r₂ = -lower` in (3.32). -/
def regularJump (q : SchwartzMap ℝ ℂ) (t x z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  jump (regularJumpReflection q t x z) (regularJumpReverseReflection q t x z)

theorem regularJump_det (q : SchwartzMap ℝ ℂ) (t x z : ℝ) : (regularJump q t x z).det = 1 :=
  det_jump _ _

/-- Prescribed time propagation leaves the product of the two regularized reflection coefficients unchanged. -/
theorem regularJumpReflection_product (q : SchwartzMap ℝ ℂ) (t x z : ℝ) :
    regularJumpReflection q t x z*regularJumpReverseReflection q t x z =
      regularReflectionCoefficient q z*regularReverseReflectionCoefficient q z := by
  unfold regularJumpReflection regularJumpReverseReflection
  have hp : FDNLS.staggerPhase 2 (z*x-t/(4*z))*FDNLS.staggerPhase (-2) (z*x-t/(4*z)) = 1 := by
    simp [FDNLS.staggerPhase, ← Complex.exp_add]
  calc
    _ = (FDNLS.staggerPhase 2 (z*x-t/(4*z))*FDNLS.staggerPhase (-2) (z*x-t/(4*z)))*
      (regularReflectionCoefficient q z*regularReverseReflectionCoefficient q z) := by ring
    _ = _ := by rw [hp, one_mul]


/-- The lower regularized coefficient carries the positive time exponential in (5.4). -/
theorem regularJumpReflection_time_factor (q : SchwartzMap ℝ ℂ) (t x z : ℝ) :
    regularJumpReflection q t x z = phase (-t) z*regularJumpReflection q 0 x z := by
  unfold regularJumpReflection FDNLS.staggerPhase phase
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_ofNat, zero_div, sub_zero]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The upper regularized coefficient carries the opposite time exponential. -/
theorem regularJumpReverseReflection_time_factor (q : SchwartzMap ℝ ℂ) (t x z : ℝ) :
    regularJumpReverseReflection q t x z = phase t z*regularJumpReverseReflection q 0 x z := by
  unfold regularJumpReverseReflection FDNLS.staggerPhase phase
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_ofNat, zero_div, sub_zero]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

end
end GaloisForLFunctions.HTGeometry.FokasLenells
