import GaloisForLFunctions.RHTower.ProlateL2Operator
import GaloisForLFunctions.HTGeometry.CompactFourierIntegrableEntire

/-!
# A closed unit-interval instance of Connes--van Suijlekom Theorem 3.1

The source theorem concerns an interval convolution attached to an even real
kernel, a simple extremal eigenline, and real zeros of the Fourier transform of
the zero-extended ground state.  This module proves every datum for the fully
fixed rank-one model `h = 1` on `[0,1]`.  It does not claim the source's general
theorem for arbitrary kernels.
-/

noncomputable section

open MeasureTheory Set intervalIntegral
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower
open GaloisForLFunctions.RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- The constant even source kernel for the closed unit-interval instance. -/
def connesVanSuijlekomT31UnitSource (_t : ℝ) : ℝ := 1

/-- Its actual interval convolution kernel. -/
def connesVanSuijlekomT31UnitKernel :
    C(ClosedInterval (0 : ℝ) 1 × ClosedInterval (0 : ℝ) 1, ℝ) := 1

/-- The fixed constant ground vector in the actual interval `L²` space. -/
def connesVanSuijlekomT31UnitEigenvector : RealIntervalL2 0 1 :=
  ContinuousMap.toLp 2 volume ℝ 1

/-- The zero-extended continuous representative of the fixed ground vector. -/
def connesVanSuijlekomT31UnitZeroExtension (x : ℝ) : ℂ :=
  if x ∈ Set.Icc (0 : ℝ) 1 then 1 else 0

theorem connesVanSuijlekomT31_unitSource_continuous :
    Continuous connesVanSuijlekomT31UnitSource := continuous_const

theorem connesVanSuijlekomT31_unitSource_even :
    ∀ t : ℝ, connesVanSuijlekomT31UnitSource (-t) = connesVanSuijlekomT31UnitSource t := by
  intro t
  rfl

theorem connesVanSuijlekomT31_unitKernel_is_convolution :
    ∀ x y : ClosedInterval (0 : ℝ) 1,
      connesVanSuijlekomT31UnitKernel (x, y) = connesVanSuijlekomT31UnitSource (x - y) := by
  intro x y
  rfl

theorem connesVanSuijlekomT31_unitKernel_compact :
    IsCompactOperator (continuousKernelOperator connesVanSuijlekomT31UnitKernel) :=
  isCompactOperator_continuousKernelOperator _

theorem connesVanSuijlekomT31_unitKernel_symmetric (f g : RealIntervalL2 0 1) :
    (inner ℝ (continuousKernelOperator connesVanSuijlekomT31UnitKernel f) g : ℝ) =
      inner ℝ f (continuousKernelOperator connesVanSuijlekomT31UnitKernel g) := by
  apply continuousKernelOperator_symmetric connesVanSuijlekomT31UnitKernel
  intro x
  simp [connesVanSuijlekomT31UnitKernel]

theorem connesVanSuijlekomT31_unitKernel_apply_ae (f : RealIntervalL2 0 1) :
    (continuousKernelOperator connesVanSuijlekomT31UnitKernel f : ClosedInterval (0 : ℝ) 1 → ℝ) =ᵐ[volume]
      fun _ => ∫ y : ClosedInterval (0 : ℝ) 1, f y ∂volume := by
  filter_upwards [continuousKernelOperator_coeFn connesVanSuijlekomT31UnitKernel f] with x hx
  rw [hx]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  simp [connesVanSuijlekomT31UnitKernel]

private theorem connesVanSuijlekomT31_unit_interval_mass :
    (volume : Measure (ClosedInterval (0 : ℝ) 1)).real Set.univ = 1 := by
  change ((measureUnivNNReal (volume : Measure (ClosedInterval (0 : ℝ) 1)) : ℝ)) = 1
  simpa using measureUnivNNReal_interval (a := (0 : ℝ)) (b := 1) (by norm_num)

private theorem connesVanSuijlekomT31_unit_eigenvector_coe :
    ((ContinuousMap.toLp 2 volume ℝ (1 : C(ClosedInterval (0 : ℝ) 1, ℝ)) :
      RealIntervalL2 0 1) : ClosedInterval (0 : ℝ) 1 → ℝ) =ᵐ[volume] fun _ => 1 :=
  ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
    (μ := (volume : Measure (ClosedInterval (0 : ℝ) 1)))
    (1 : C(ClosedInterval (0 : ℝ) 1, ℝ))

theorem connesVanSuijlekomT31_unitKernel_eigen :
    continuousKernelOperator connesVanSuijlekomT31UnitKernel connesVanSuijlekomT31UnitEigenvector =
      connesVanSuijlekomT31UnitEigenvector := by
  apply Lp.ext
  filter_upwards [
    continuousKernelOperator_coeFn connesVanSuijlekomT31UnitKernel
      connesVanSuijlekomT31UnitEigenvector,
    connesVanSuijlekomT31_unit_eigenvector_coe
  ] with x hOp hx
  rw [hOp]
  change ∫ y : ClosedInterval (0 : ℝ) 1,
      connesVanSuijlekomT31UnitKernel (x, y) *
        ((ContinuousMap.toLp 2 volume ℝ (1 : C(ClosedInterval (0 : ℝ) 1, ℝ)) :
          RealIntervalL2 0 1) y) =
      ((ContinuousMap.toLp 2 volume ℝ (1 : C(ClosedInterval (0 : ℝ) 1, ℝ)) :
        RealIntervalL2 0 1) x)
  have hInt : ∫ y : ClosedInterval (0 : ℝ) 1,
      connesVanSuijlekomT31UnitKernel (x, y) *
        ((ContinuousMap.toLp 2 volume ℝ (1 : C(ClosedInterval (0 : ℝ) 1, ℝ)) :
          RealIntervalL2 0 1) y) = ∫ _ : ClosedInterval (0 : ℝ) 1, (1 : ℝ) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [connesVanSuijlekomT31_unit_eigenvector_coe] with y hy
    rw [hy]
    simp [connesVanSuijlekomT31UnitKernel]
  rw [hInt, MeasureTheory.integral_const, connesVanSuijlekomT31_unit_interval_mass, hx]
  norm_num

theorem connesVanSuijlekomT31_unitEigenvector_ne_zero :
    connesVanSuijlekomT31UnitEigenvector ≠ 0 := by
  intro hzero
  have hveczero :
      (connesVanSuijlekomT31UnitEigenvector : ClosedInterval (0 : ℝ) 1 → ℝ) =ᵐ[volume] fun _ => 0 := by
    rw [hzero]
    exact Lp.coeFn_zero ℝ 2 (volume : Measure (ClosedInterval (0 : ℝ) 1))
  have hfalse : ∀ᵐ x : ClosedInterval (0 : ℝ) 1 ∂volume, False := by
    filter_upwards [connesVanSuijlekomT31_unit_eigenvector_coe, hveczero] with x hx hzeroAt
    change ((ContinuousMap.toLp 2 volume ℝ (1 : C(ClosedInterval (0 : ℝ) 1, ℝ)) :
      RealIntervalL2 0 1) x) = 0 at hzeroAt
    rw [hx] at hzeroAt
    norm_num at hzeroAt
  have hmeasure : (volume : Measure (ClosedInterval (0 : ℝ) 1)) Set.univ = 0 := by
    simpa using ae_iff.mp hfalse
  have : (1 : ℝ) = 0 := by
    calc
      (1 : ℝ) = (volume : Measure (ClosedInterval (0 : ℝ) 1)).real Set.univ :=
        connesVanSuijlekomT31_unit_interval_mass.symm
      _ = ((volume : Measure (ClosedInterval (0 : ℝ) 1)) Set.univ).toReal :=
        MeasureTheory.measureReal_def _ _
      _ = 0 := by rw [hmeasure]; rfl
  norm_num at this

theorem connesVanSuijlekomT31_unitKernel_range (f : RealIntervalL2 0 1) :
    ∃ c : ℝ, continuousKernelOperator connesVanSuijlekomT31UnitKernel f =
      c • connesVanSuijlekomT31UnitEigenvector := by
  let c : ℝ := ∫ y : ClosedInterval (0 : ℝ) 1, f y ∂volume
  have hconst :
      (continuousKernelOperator connesVanSuijlekomT31UnitKernel f : ClosedInterval (0 : ℝ) 1 → ℝ) =ᵐ[volume]
        fun _ => c := by
    simpa [c] using connesVanSuijlekomT31_unitKernel_apply_ae f
  refine ⟨c, ?_⟩
  apply Lp.ext
  filter_upwards [hconst, Lp.coeFn_smul c connesVanSuijlekomT31UnitEigenvector,
    connesVanSuijlekomT31_unit_eigenvector_coe] with x hx hsmul hu
  rw [hsmul]
  change (continuousKernelOperator connesVanSuijlekomT31UnitKernel f :
      ClosedInterval (0 : ℝ) 1 → ℝ) x =
    c * ((ContinuousMap.toLp 2 volume ℝ (1 : C(ClosedInterval (0 : ℝ) 1, ℝ)) :
      RealIntervalL2 0 1) x)
  rw [hx, hu]
  ring

theorem connesVanSuijlekomT31_unitKernel_one_eigenspace (f : RealIntervalL2 0 1)
    (hf : continuousKernelOperator connesVanSuijlekomT31UnitKernel f = f) :
    ∃ c : ℝ, f = c • connesVanSuijlekomT31UnitEigenvector := by
  let c : ℝ := ∫ y : ClosedInterval (0 : ℝ) 1, f y ∂volume
  have hconst : (f : ClosedInterval (0 : ℝ) 1 → ℝ) =ᵐ[volume] fun _ => c := by
    rw [← hf]
    simpa [c] using connesVanSuijlekomT31_unitKernel_apply_ae f
  refine ⟨c, ?_⟩
  apply Lp.ext
  filter_upwards [hconst, Lp.coeFn_smul c connesVanSuijlekomT31UnitEigenvector,
    connesVanSuijlekomT31_unit_eigenvector_coe] with x hx hsmul hu
  rw [hsmul]
  change (f : ClosedInterval (0 : ℝ) 1 → ℝ) x =
    c * ((ContinuousMap.toLp 2 volume ℝ (1 : C(ClosedInterval (0 : ℝ) 1, ℝ)) :
      RealIntervalL2 0 1) x)
  rw [hx, hu]
  ring

theorem connesVanSuijlekomT31_unitKernel_eigenvalue_eq_zero_or_one (lam : ℝ) (f : RealIntervalL2 0 1)
    (hfne : f ≠ 0) (hEig : continuousKernelOperator connesVanSuijlekomT31UnitKernel f = lam • f) :
    lam = 0 ∨ lam = 1 := by
  by_cases hlam : lam = 0
  · exact Or.inl hlam
  right
  obtain ⟨c, hrange⟩ := connesVanSuijlekomT31_unitKernel_range f
  have hfspan : f = (lam⁻¹ * c) • connesVanSuijlekomT31UnitEigenvector := by
    calc
      f = (1 : ℝ) • f := (one_smul ℝ f).symm
      _ = (lam⁻¹ * lam) • f := by rw [inv_mul_cancel₀ hlam]
      _ = lam⁻¹ • (lam • f) := by rw [smul_smul]
      _ = lam⁻¹ • continuousKernelOperator connesVanSuijlekomT31UnitKernel f := by rw [hEig]
      _ = lam⁻¹ • (c • connesVanSuijlekomT31UnitEigenvector) := by rw [hrange]
      _ = (lam⁻¹ * c) • connesVanSuijlekomT31UnitEigenvector := by rw [smul_smul]
  have hfix : continuousKernelOperator connesVanSuijlekomT31UnitKernel f = f := by
    rw [hfspan, map_smul, connesVanSuijlekomT31_unitKernel_eigen]
  have hsub : (1 - lam) • f = 0 := by
    calc
      (1 - lam) • f = f - lam • f := by rw [sub_smul, one_smul]
      _ = continuousKernelOperator connesVanSuijlekomT31UnitKernel f - lam • f := by rw [hfix]
      _ = 0 := by rw [hEig, sub_self]
  rcases smul_eq_zero.mp hsub with hscalar | hvector
  · linarith
  · exact False.elim (hfne hvector)

theorem connesVanSuijlekomT31_unitZeroExtension_on_interval (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    connesVanSuijlekomT31UnitZeroExtension x = 1 := by
  simp [connesVanSuijlekomT31UnitZeroExtension, hx]

theorem connesVanSuijlekomT31_unitZeroExtension_compactFourier_eq_constant (z : ℂ) :
    compactFourier connesVanSuijlekomT31UnitZeroExtension 0 1 z =
      compactFourier (fun _ : ℝ => (1 : ℂ)) 0 1 z := by
  unfold compactFourier
  refine intervalIntegral.integral_congr fun x hx => ?_
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  rw [connesVanSuijlekomT31_unitZeroExtension_on_interval x hx']

theorem connesVanSuijlekomT31_unitConstant_compactFourier_zero_im {z : ℂ}
    (hz : compactFourier (fun _ : ℝ => (1 : ℂ)) 0 1 z = 0) : z.im = 0 := by
  have hcalc (hz' : z ≠ 0) :
      compactFourier (fun _ : ℝ => (1 : ℂ)) 0 1 z =
        (Complex.exp (Complex.I * z) - 1) / (Complex.I * z) := by
    rw [compactFourier]
    have hIz : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz'
    rw [show (fun x : ℝ => (1 : ℂ) * Complex.exp (Complex.I * (z * (x : ℂ)))) =
      fun x : ℝ => Complex.exp ((Complex.I * z) * (x : ℂ)) by
        funext x
        rw [one_mul, mul_assoc]]
    rw [integral_exp_mul_complex hIz]
    norm_num
  have hzne : z ≠ 0 := by
    intro hz0
    subst z
    rw [compactFourier, show (fun x : ℝ => (1 : ℂ) * Complex.exp (Complex.I * (0 * (x : ℂ)))) =
      fun _ : ℝ => (1 : ℂ) by
        funext x
        norm_num, intervalIntegral.integral_const] at hz
    norm_num at hz
  have heq : Complex.exp (Complex.I * z) = 1 := by
    have h := hcalc hzne
    rw [h] at hz
    have hden : Complex.I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hzne
    exact sub_eq_zero.mp ((div_eq_zero_iff.mp hz).resolve_right hden)
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp heq
  have hzreal : z = ((n : ℂ) * (2 * Real.pi)) := by
    calc
      z = (-Complex.I * Complex.I) * z := by simp [Complex.I_mul_I]
      _ = (-Complex.I) * (Complex.I * z) := by ring
      _ = (-Complex.I) * ((n : ℂ) * (2 * Real.pi * Complex.I)) := by rw [hn]
      _ = (n : ℂ) * (2 * Real.pi) := by
        ring_nf
        simp only [Complex.I_sq]
        ring
  rw [hzreal]
  simp

theorem connesVanSuijlekomT31_unitZeroExtension_compactFourier_zero_im {z : ℂ}
    (hz : compactFourier connesVanSuijlekomT31UnitZeroExtension 0 1 z = 0) : z.im = 0 := by
  apply connesVanSuijlekomT31_unitConstant_compactFourier_zero_im
  rw [← connesVanSuijlekomT31_unitZeroExtension_compactFourier_eq_constant]
  exact hz

/-- A fully discharged concrete instance of every analytic/eigenline datum of Theorem 3.1. -/
theorem connesVanSuijlekomT31_unitInterval_closed_instance :
    Continuous connesVanSuijlekomT31UnitSource ∧
      (∀ t : ℝ, connesVanSuijlekomT31UnitSource (-t) = connesVanSuijlekomT31UnitSource t) ∧
      (∀ x y : ClosedInterval (0 : ℝ) 1,
        connesVanSuijlekomT31UnitKernel (x, y) = connesVanSuijlekomT31UnitSource (x - y)) ∧
      IsCompactOperator (continuousKernelOperator connesVanSuijlekomT31UnitKernel) ∧
      (∀ f g : RealIntervalL2 0 1,
        (inner ℝ (continuousKernelOperator connesVanSuijlekomT31UnitKernel f) g : ℝ) =
          inner ℝ f (continuousKernelOperator connesVanSuijlekomT31UnitKernel g)) ∧
      connesVanSuijlekomT31UnitEigenvector ≠ 0 ∧
      continuousKernelOperator connesVanSuijlekomT31UnitKernel connesVanSuijlekomT31UnitEigenvector =
        connesVanSuijlekomT31UnitEigenvector ∧
      (∀ f : RealIntervalL2 0 1,
        continuousKernelOperator connesVanSuijlekomT31UnitKernel f = f →
          ∃ c : ℝ, f = c • connesVanSuijlekomT31UnitEigenvector) ∧
      (∀ (lam : ℝ) (f : RealIntervalL2 0 1), f ≠ 0 →
        continuousKernelOperator connesVanSuijlekomT31UnitKernel f = lam • f → lam = 0 ∨ lam = 1) ∧
      ∀ z : ℂ, compactFourier connesVanSuijlekomT31UnitZeroExtension 0 1 z = 0 → z.im = 0 := by
  exact ⟨connesVanSuijlekomT31_unitSource_continuous,
    connesVanSuijlekomT31_unitSource_even,
    connesVanSuijlekomT31_unitKernel_is_convolution,
    connesVanSuijlekomT31_unitKernel_compact,
    connesVanSuijlekomT31_unitKernel_symmetric,
    connesVanSuijlekomT31_unitEigenvector_ne_zero,
    connesVanSuijlekomT31_unitKernel_eigen,
    connesVanSuijlekomT31_unitKernel_one_eigenspace,
    connesVanSuijlekomT31_unitKernel_eigenvalue_eq_zero_or_one,
    fun z hz => connesVanSuijlekomT31_unitZeroExtension_compactFourier_zero_im hz⟩

end GaloisForLFunctions.HTGeometry
