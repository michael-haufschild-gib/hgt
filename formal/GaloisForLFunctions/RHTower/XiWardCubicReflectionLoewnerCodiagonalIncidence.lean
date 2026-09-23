import GaloisForLFunctions.RHTower.XiWardCubicOppositeRadialBoundarySignature
import GaloisForLFunctions.RHTower.XiWardCubicTranslationEnergySeparator

/-!
# Cubic Ward reflection-Loewner codiagonal incidence (W-H190)

The Hermitian divided difference of the completed logarithmic derivative is the
coefficient-linear replacement for scalar Bohr squaring.  At a reflected zero pair its
iterated sesquiresidue is the zero multiplicity, not its square.  Coupling this codiagonal
to the nonholomorphic horizontal/ordinate tensor feature lands the exact cubic Hellinger
self-charge.  Every strict-right zero therefore contributes at least `115 / 108`.

This module constructs and audits the zero-side codiagonal.  It does not assert the still
missing global contraction from its total residue trace to the primitive Euler source trace.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- Hermitian reflection-Loewner kernel of the completed logarithmic derivative. -/
def xiWardCubicReflectionLoewnerKernel (s t : ℂ) : ℂ :=
  (logDeriv xi s + star (logDeriv xi t)) / (s + star t - 1)

/-- Arithmetic current equal to the completed logarithmic derivative on `re > 1`. -/
def xiWardCubicCompletedArithmeticCurrent (s : ℂ) : ℂ :=
  s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s -
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s

/-- Functional-equation form: the reflection kernel is a divided difference. -/
theorem xiWardCubicReflectionLoewnerKernel_eq_dividedDifference (s t : ℂ) :
    xiWardCubicReflectionLoewnerKernel s t =
      (logDeriv xi s - logDeriv xi (1 - star t)) /
        (s - (1 - star t)) := by
  rw [xiWardCubicReflectionLoewnerKernel, logDeriv_xi_reciprocity]
  rw [show logDeriv xi (star t) = star (logDeriv xi t) by
    exact logDeriv_xi_conj_global t]
  congr 1 <;> ring

/-- The reflection-Loewner kernel is Hermitian without any RH assumption. -/
theorem xiWardCubicReflectionLoewnerKernel_hermitian (s t : ℂ) :
    star (xiWardCubicReflectionLoewnerKernel t s) =
      xiWardCubicReflectionLoewnerKernel s t := by
  simp only [xiWardCubicReflectionLoewnerKernel, Complex.star_def, map_div₀,
    map_add, map_sub, map_one, Complex.conj_conj]
  ring

/-- Exact source expression on the Euler half-plane; von Mangoldt remains linear. -/
theorem xiWardCubicReflectionLoewnerKernel_eq_arithmetic
    {s t : ℂ} (hs : 1 < s.re) (ht : 1 < t.re) :
    xiWardCubicReflectionLoewnerKernel s t =
      (xiWardCubicCompletedArithmeticCurrent s +
          star (xiWardCubicCompletedArithmeticCurrent t)) /
        (s + star t - 1) := by
  unfold xiWardCubicReflectionLoewnerKernel xiWardCubicCompletedArithmeticCurrent
  rw [logDeriv_xi_eq_arithmetic hs, logDeriv_xi_eq_arithmetic ht]

/-- Explicit left residue of the reflection-Loewner kernel at a reflected zero. -/
def xiWardCubicReflectionLoewnerLeftResidue (rho t : ℂ) : ℂ :=
  (((analyticOrderAt xi (1 - star rho)).toNat : ℂ)) / star (t - rho)

/-- First residue in the reflected variable. -/
theorem xiWardCubicReflectionLoewnerKernel_left_residue
    (rho : ℂ) {t : ℂ} (ht : t ≠ rho) :
    Tendsto
      (fun s : ℂ =>
        (s - (1 - star rho)) * xiWardCubicReflectionLoewnerKernel s t)
      (nhdsWithin (1 - star rho) ({1 - star rho}ᶜ))
      (nhds (xiWardCubicReflectionLoewnerLeftResidue rho t)) := by
  let s0 : ℂ := 1 - star rho
  have hlog := xi_normalizedLogDeriv_tendsto_order s0
  have hzero : Tendsto (fun s : ℂ => (s - s0) * star (logDeriv xi t))
      (nhdsWithin s0 ({s0}ᶜ)) (nhds 0) := by
    have hcont : ContinuousAt (fun s : ℂ =>
        (s - s0) * star (logDeriv xi t)) s0 :=
      (continuousAt_id.sub continuousAt_const).mul continuousAt_const
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hnum := hlog.add hzero
  have hden : Tendsto (fun s : ℂ => s + star t - 1)
      (nhdsWithin s0 ({s0}ᶜ)) (nhds (star (t - rho))) := by
    have hcont : ContinuousAt (fun s : ℂ => s + star t - 1) s0 :=
      (continuousAt_id.add continuousAt_const).sub continuousAt_const
    convert hcont.tendsto.mono_left nhdsWithin_le_nhds using 1
    simp [s0]
    ring
  have hstar : star (t - rho) ≠ 0 := by
    intro h
    have h' := congrArg (starRingEnd ℂ) h
    have hz : t - rho = 0 := by simpa using h'
    exact ht (sub_eq_zero.mp hz)
  have hquot := hnum.div hden hstar
  convert hquot using 1
  · funext s
    simp [xiWardCubicReflectionLoewnerKernel, s0]
    ring
  · simp [xiWardCubicReflectionLoewnerLeftResidue, s0]

/-- Iterating the sesquiresidue lands one copy of the reflected zero order. -/
theorem xiWardCubicReflectionLoewnerKernel_iterated_sesquiresidue (rho : ℂ) :
    Tendsto
      (fun t : ℂ =>
        star (t - rho) * xiWardCubicReflectionLoewnerLeftResidue rho t)
      (nhdsWithin rho ({rho}ᶜ))
      (nhds (((analyticOrderAt xi (1 - star rho)).toNat : ℂ))) := by
  have heq :
      (fun t : ℂ =>
        star (t - rho) * xiWardCubicReflectionLoewnerLeftResidue rho t) =ᶠ[
          nhdsWithin rho ({rho}ᶜ)]
      fun _ => (((analyticOrderAt xi (1 - star rho)).toNat : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hne : star (t - rho) ≠ 0 := by
      intro h
      have h' := congrArg (starRingEnd ℂ) h
      have hz : t - rho = 0 := by simpa using h'
      exact ht (sub_eq_zero.mp hz)
    rw [xiWardCubicReflectionLoewnerLeftResidue]
    field_simp [hne]
  exact tendsto_const_nhds.congr' heq.symm

/-- Horizontal Hellinger difference carried by the tensor feature. -/
def xiWardCubicTensorHorizontalDifference (s : ℂ) (r : ℝ) : ℝ :=
  Real.exp (-((s - 1 / 2).re * r)) -
    Real.exp (-((2 * (s - 1 / 2).re) * r))

/-- One radial variable carries both horizontal Hellinger split and signed ordinate phase. -/
def xiWardCubicTensorConormalFeature (s : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) * (xiWardCubicTensorHorizontalDifference s r : ℂ) *
    Complex.exp (-I * (((s - 1 / 2).im * r : ℝ) : ℂ))

/-- Opposite radial reflection preserves the horizontal Hellinger difference. -/
theorem xiWardCubicTensorHorizontalDifference_reflection_neg (s : ℂ) (r : ℝ) :
    xiWardCubicTensorHorizontalDifference (1 - star s) (-r) =
      xiWardCubicTensorHorizontalDifference s r := by
  simp [xiWardCubicTensorHorizontalDifference]
  congr 1 <;> ring

/-- Exact FE--Schwarz/opposite-radial anti-Hermitian law for the tensor feature. -/
theorem xiWardCubicTensorConormalFeature_reflection_neg (s : ℂ) (r : ℝ) :
    xiWardCubicTensorConormalFeature (1 - star s) (-r) =
      -star (xiWardCubicTensorConormalFeature s r) := by
  rw [xiWardCubicTensorConormalFeature, xiWardCubicTensorConormalFeature,
    xiWardCubicTensorHorizontalDifference_reflection_neg]
  change _ = -(starRingEnd ℂ) (_ * _ * _)
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  have him : (1 - star s - 1 / 2).im = (s - 1 / 2).im := by simp
  rw [him]
  push_cast
  ring

/-- The ordinate phase is unitary, so norm square retains exactly the cubic radial weight. -/
theorem xiWardCubicTensorConormalFeature_normSq (s : ℂ) (r : ℝ) :
    Complex.normSq (xiWardCubicTensorConormalFeature s r) =
      r ^ (2 : ℕ) * (xiWardCubicTensorHorizontalDifference s r) ^ (2 : ℕ) := by
  rw [xiWardCubicTensorConormalFeature, Complex.normSq_mul, Complex.normSq_mul]
  have hphase : Complex.normSq
      (Complex.exp (-I * (((s - 1 / 2).im * r : ℝ) : ℂ))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    norm_num [Complex.mul_re]
  rw [hphase]
  simp [Complex.normSq_apply]
  ring

/-- Radial norm-square integral is the exact cubic Hellinger horizontal kernel. -/
theorem integral_xiWardCubicTensorConormalFeature_normSq
    {s : ℂ} (hs : 1 / 2 < s.re) :
    (∫ r : ℝ in Ioi 0,
        Complex.normSq (xiWardCubicTensorConormalFeature s r)) =
      cubicLogMomentHellingerHorizontalKernel
        (s - 1 / 2).re (s - 1 / 2).re := by
  rw [show (fun r : ℝ =>
      Complex.normSq (xiWardCubicTensorConormalFeature s r)) =
      fun r : ℝ => r ^ (2 : ℕ) *
        (Real.exp (-((s - 1 / 2).re * r)) -
          Real.exp (-((2 * (s - 1 / 2).re) * r))) *
        (Real.exp (-((s - 1 / 2).re * r)) -
          Real.exp (-((2 * (s - 1 / 2).re) * r))) by
    funext r
    rw [xiWardCubicTensorConormalFeature_normSq,
      xiWardCubicTensorHorizontalDifference]
    ring]
  exact integral_cubicLogMomentHellingerHorizontalKernel
    (by norm_num at hs ⊢; linarith) (by norm_num at hs ⊢; linarith)

/-- Completed reflection-Loewner current carrying the cubic tensor feature. -/
def xiWardCubicReflectionLoewnerCurrent (s t : ℂ) (r : ℝ) : ℂ :=
  -xiWardCubicReflectionLoewnerKernel s t *
    xiWardCubicTensorConormalFeature s (-r) *
      xiWardCubicTensorConormalFeature t r

/-- Explicit left-residue column of the completed current. -/
def xiWardCubicReflectionLoewnerCurrentLeftResidue (rho t : ℂ) (r : ℝ) : ℂ :=
  -xiWardCubicReflectionLoewnerLeftResidue rho t *
    xiWardCubicTensorConormalFeature (1 - star rho) (-r) *
      xiWardCubicTensorConormalFeature t r

/-- First current residue: only the meromorphic Loewner factor is differentiated. -/
theorem xiWardCubicReflectionLoewnerCurrent_left_residue
    (rho : ℂ) {t : ℂ} (ht : t ≠ rho) (r : ℝ) :
    Tendsto
      (fun s : ℂ =>
        (s - (1 - star rho)) * xiWardCubicReflectionLoewnerCurrent s t r)
      (nhdsWithin (1 - star rho) ({1 - star rho}ᶜ))
      (nhds (xiWardCubicReflectionLoewnerCurrentLeftResidue rho t r)) := by
  have hL :=
    (xiWardCubicReflectionLoewnerKernel_left_residue rho ht).neg
  have hf : Tendsto (fun s : ℂ => xiWardCubicTensorConormalFeature s (-r))
      (nhdsWithin (1 - star rho) ({1 - star rho}ᶜ))
      (nhds (xiWardCubicTensorConormalFeature (1 - star rho) (-r))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply ContinuousAt.tendsto
    unfold xiWardCubicTensorConormalFeature xiWardCubicTensorHorizontalDifference
    fun_prop
  have h := (hL.mul hf).mul_const (xiWardCubicTensorConormalFeature t r)
  convert h using 1
  · funext s
    simp [xiWardCubicReflectionLoewnerCurrent]
    ring
  · simp [xiWardCubicReflectionLoewnerCurrentLeftResidue]

/-- Iterated current sesquiresidue lands multiplicity times feature norm square. -/
theorem xiWardCubicReflectionLoewnerCurrent_iterated_sesquiresidue
    (rho : ℂ) (r : ℝ) :
    Tendsto
      (fun t : ℂ =>
        star (t - rho) * xiWardCubicReflectionLoewnerCurrentLeftResidue rho t r)
      (nhdsWithin rho ({rho}ᶜ))
      (nhds ((((analyticOrderAt xi (1 - star rho)).toNat : ℂ)) *
        ((Complex.normSq (xiWardCubicTensorConormalFeature rho r) : ℝ) : ℂ))) := by
  have hf : Tendsto (fun t : ℂ => xiWardCubicTensorConormalFeature t r)
      (nhdsWithin rho ({rho}ᶜ))
      (nhds (xiWardCubicTensorConormalFeature rho r)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply ContinuousAt.tendsto
    unfold xiWardCubicTensorConormalFeature xiWardCubicTensorHorizontalDifference
    fun_prop
  let m : ℂ := ((analyticOrderAt xi (1 - star rho)).toNat : ℂ)
  have htarget :=
    hf.const_mul (m * star (xiWardCubicTensorConormalFeature rho r))
  have heq :
      (fun t : ℂ =>
        star (t - rho) * xiWardCubicReflectionLoewnerCurrentLeftResidue rho t r) =ᶠ[
          nhdsWithin rho ({rho}ᶜ)]
      fun t => (m * star (xiWardCubicTensorConormalFeature rho r)) *
        xiWardCubicTensorConormalFeature t r := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hne : star (t - rho) ≠ 0 := by
      intro h
      have h' := congrArg (starRingEnd ℂ) h
      have hz : t - rho = 0 := by simpa using h'
      exact ht (sub_eq_zero.mp hz)
    rw [xiWardCubicReflectionLoewnerCurrentLeftResidue,
      xiWardCubicReflectionLoewnerLeftResidue,
      xiWardCubicTensorConormalFeature_reflection_neg]
    dsimp only [m]
    field_simp [hne]
  have hfinal := htarget.congr' heq.symm
  convert hfinal using 1
  rw [Complex.normSq_eq_conj_mul_self]
  dsimp only [m]
  congr 1
  rw [show star (xiWardCubicTensorConormalFeature rho r) =
    (starRingEnd ℂ) (xiWardCubicTensorConormalFeature rho r) from rfl]
  ring

/-- Reflected order equals the intrinsic multiplicity of the support point. -/
theorem xiWardCubic_reflected_order_eq_supportMultiplicity
    (rho : XiDivisorSupport) :
    (analyticOrderAt xi (1 - star (rho : ℂ))).toNat =
      xiSupportMultiplicity rho := by
  change (analyticOrderAt xi
    (1 - (starRingEnd ℂ) (rho : ℂ))).toNat = xiSupportMultiplicity rho
  rw [← xiZeroLineConjEquiv_apply]
  rw [xi_orderAt_xiZeroLineConjEquiv]
  exact (xiSupportMultiplicity_eq_analyticOrderAt_toNat rho).symm

/-- Multiplicity-faithful codiagonal landing density. -/
def xiWardCubicReflectionLoewnerCodiagonalLanding
    (rho : XiDivisorSupport) (r : ℝ) : ℝ :=
  xiSupportMultiplicity rho *
    Complex.normSq (xiWardCubicTensorConormalFeature (rho : ℂ) r)

/-- Exact integrated codiagonal landing. -/
theorem integral_xiWardCubicReflectionLoewnerCodiagonalLanding
    (rho : XiDivisorSupport) (hrho : 1 / 2 < (rho : ℂ).re) :
    (∫ r : ℝ in Ioi 0,
        xiWardCubicReflectionLoewnerCodiagonalLanding rho r) =
      xiSupportMultiplicity rho *
        cubicLogMomentHellingerHorizontalKernel
          ((rho : ℂ) - 1 / 2).re ((rho : ℂ) - 1 / 2).re := by
  change (∫ r : ℝ in Ioi 0,
      (xiSupportMultiplicity rho : ℝ) *
        Complex.normSq (xiWardCubicTensorConormalFeature (rho : ℂ) r)) = _
  rw [MeasureTheory.integral_const_mul,
    integral_xiWardCubicTensorConormalFeature_normSq hrho]

/-- Every strict-right support point consumes at least one `115 / 108` source quantum. -/
theorem xiWardCubicReflectionLoewnerCodiagonalLanding_charge_ge_quantum
    (rho : XiDivisorSupport) (hrho : 1 / 2 < (rho : ℂ).re) :
    115 / 108 ≤ ∫ r : ℝ in Ioi 0,
      xiWardCubicReflectionLoewnerCodiagonalLanding rho r := by
  rw [integral_xiWardCubicReflectionLoewnerCodiagonalLanding rho hrho]
  have ha : 0 < ((rho : ℂ) - 1 / 2).re := by
    norm_num at hrho ⊢
    linarith
  have hhalf : ((rho : ℂ) - 1 / 2).re ≤ 1 / 2 := by
    have hstrip := xi_divisor_support_re_mem_open_unit rho
    norm_num at hstrip ⊢
    linarith
  have hk := cubicLogMomentHellingerHorizontalKernel_self_ge ha hhalf
  have hm : (1 : ℝ) ≤ xiSupportMultiplicity rho := by
    exact_mod_cast xiSupportMultiplicity_pos rho
  have hkpos : 0 ≤ cubicLogMomentHellingerHorizontalKernel
      ((rho : ℂ) - 1 / 2).re ((rho : ℂ) - 1 / 2).re :=
    (cubicLogMomentHellingerHorizontalKernel_pos ha ha).le
  calc
    115 / 108 ≤ cubicLogMomentHellingerHorizontalKernel
        ((rho : ℂ) - 1 / 2).re ((rho : ℂ) - 1 / 2).re := hk
    _ ≤ xiSupportMultiplicity rho *
        cubicLogMomentHellingerHorizontalKernel
          ((rho : ℂ) - 1 / 2).re ((rho : ℂ) - 1 / 2).re := by
      nlinarith

end
end RHTower
