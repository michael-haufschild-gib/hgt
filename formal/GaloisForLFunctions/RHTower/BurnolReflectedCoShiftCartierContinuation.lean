import GaloisForLFunctions.RHTower.BurnolDividedShiftPhysicalDissipativity
import GaloisForLFunctions.HTGeometry.L2FourierMultiplier

/-!
# Burnol reflected co-shift Cartier continuation

The physical reflected co-shift diverges when its parameter lies left of the critical line.  Its
critical-line coefficient nevertheless remains bounded.  This module constructs that bounded
Cartier continuation independently, proves coefficient-faithful uniqueness, and identifies the
continuation at `1 - rho` with the negative forward divided shift at `rho`.

For the fixed co-Poisson atom, the reflected port is therefore strictly negative.  At every actual
right-half Xi divisor, Burnol's zero-division theorem additionally places the reflected output in
the literal extended Sonin source.  The remaining Route R producer is the pre-divisor
Euler--Gamma--Stokes sewing of the forward physical reading to this constructed reflected source
reading; that sewing is named but not assumed here.
-/

noncomputable section

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace

namespace RHTower

/-! ## Independent left-half multiplier -/

/-- Critical-line coefficient of the reflected co-shift continuation. -/
def burnolReflectedCoShiftContinuationSymbol (sigma : ℂ) (t : ℝ) : ℂ :=
  (criticalLineArgument t + sigma - 1)⁻¹

/-- Reflection turns the left-half coefficient into the negative forward Cauchy coefficient. -/
theorem burnolReflectedCoShiftContinuationSymbol_eq_neg
    (sigma : ℂ) (t : ℝ) :
    burnolReflectedCoShiftContinuationSymbol sigma t =
      -burnolDividedShiftSymbol (1 - sigma) t := by
  unfold burnolReflectedCoShiftContinuationSymbol burnolDividedShiftSymbol
  rw [show criticalLineArgument t + sigma - 1 =
      -((1 - sigma) - criticalLineArgument t) by ring, inv_neg]

theorem measurable_burnolReflectedCoShiftContinuationSymbol (sigma : ℂ) :
    Measurable (burnolReflectedCoShiftContinuationSymbol sigma) := by
  unfold burnolReflectedCoShiftContinuationSymbol
  apply Measurable.inv
  unfold criticalLineArgument
  fun_prop

/-- Uniform left-half resolvent bound. -/
theorem norm_burnolReflectedCoShiftContinuationSymbol_le
    {sigma : ℂ} (h : sigma.re < 1 / 2) (t : ℝ) :
    ‖burnolReflectedCoShiftContinuationSymbol sigma t‖ ≤
      (1 / 2 - sigma.re)⁻¹ := by
  rw [burnolReflectedCoShiftContinuationSymbol_eq_neg, norm_neg]
  have hright : 1 / 2 < (1 - sigma).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  convert norm_burnolDividedShiftSymbol_le hright t using 1
  simp only [Complex.sub_re, Complex.one_re]
  ring

/-- Exact anti-Herglotz identity of the reflected coefficient. -/
theorem re_burnolReflectedCoShiftContinuationSymbol_eq
    {sigma : ℂ} (h : sigma.re < 1 / 2) (t : ℝ) :
    (burnolReflectedCoShiftContinuationSymbol sigma t).re =
      (sigma.re - 1 / 2) *
        Complex.normSq (burnolReflectedCoShiftContinuationSymbol sigma t) := by
  have hright : 1 / 2 < (1 - sigma).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  rw [burnolReflectedCoShiftContinuationSymbol_eq_neg, Complex.neg_re,
    re_burnolDividedShiftSymbol_eq hright, Complex.normSq_neg]
  simp only [Complex.sub_re, Complex.one_re]
  ring

/-- Bounded spectral continuation of the reflected co-shift in the open left half-plane. -/
def burnolSpectralReflectedCoShiftContinuation
    {sigma : ℂ} (h : sigma.re < 1 / 2) : SpectralL2 →L[ℂ] SpectralL2 :=
  lpBoundedMulCLM (p := 2) (μ := volume)
    (measurable_burnolReflectedCoShiftContinuationSymbol sigma)
    (inv_nonneg.mpr (by linarith))
    (norm_burnolReflectedCoShiftContinuationSymbol_le h)

theorem burnolSpectralReflectedCoShiftContinuation_ae
    {sigma : ℂ} (h : sigma.re < 1 / 2) (f : SpectralL2) :
    burnolSpectralReflectedCoShiftContinuation h f =ᵐ[volume]
      fun t => burnolReflectedCoShiftContinuationSymbol sigma t * f t :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := volume)
    (measurable_burnolReflectedCoShiftContinuationSymbol sigma)
    (inv_nonneg.mpr (by linarith))
    (norm_burnolReflectedCoShiftContinuationSymbol_le h) f

/-- Coefficient-faithful operator reflection on Mellin `L²`. -/
theorem burnolSpectralReflectedCoShiftContinuation_eq_neg
    {sigma : ℂ} (h : sigma.re < 1 / 2) :
    burnolSpectralReflectedCoShiftContinuation h =
      -burnolSpectralDividedShift (rho := 1 - sigma) (by
        simp only [Complex.sub_re, Complex.one_re]
        linarith) := by
  unfold burnolSpectralReflectedCoShiftContinuation burnolSpectralDividedShift
  apply MeasureTheory.lpBoundedMulCLM_neg
  exact Filter.Eventually.of_forall
    (burnolReflectedCoShiftContinuationSymbol_eq_neg sigma)

/-! ## Physical transport, uniqueness, and sign -/

/-- Mellin-unitary transport of the bounded reflected continuation to the even physical space. -/
def burnolReflectedCoShiftContinuation
    {sigma : ℂ} (h : sigma.re < 1 / 2) : evenSubspace →L[ℂ] evenSubspace :=
  unitaryPush archimedeanMellinUnitary.symm
    (burnolSpectralReflectedCoShiftContinuation h)

theorem burnolReflectedCoShiftContinuation_eq_neg
    {sigma : ℂ} (h : sigma.re < 1 / 2) :
    burnolReflectedCoShiftContinuation h =
      -burnolMellinDividedShift (rho := 1 - sigma) (by
        simp only [Complex.sub_re, Complex.one_re]
        linarith) := by
  rw [burnolReflectedCoShiftContinuation,
    burnolSpectralReflectedCoShiftContinuation_eq_neg,
    burnolMellinDividedShift]
  simpa using (unitaryPush_smul archimedeanMellinUnitary.symm (-1 : ℂ)
    (burnolSpectralDividedShift (rho := 1 - sigma) (by
      simp only [Complex.sub_re, Complex.one_re]
      linarith)))

/-- Reflection-specialized form with the forward proof parameter fixed by proof irrelevance. -/
theorem burnolReflectedCoShiftContinuation_one_sub_eq_neg
    {rho : ℂ} (h : 1 / 2 < rho.re) :
    burnolReflectedCoShiftContinuation (sigma := 1 - rho) (by
      simp only [Complex.sub_re, Complex.one_re]
      linarith) = -burnolMellinDividedShift h := by
  simpa using burnolReflectedCoShiftContinuation_eq_neg
    (sigma := 1 - rho) (by
      simp only [Complex.sub_re, Complex.one_re]
      linarith)

/-- Exact dissipative energy identity for the reflected continuation. -/
theorem re_inner_burnolReflectedCoShiftContinuation_eq
    {sigma : ℂ} (h : sigma.re < 1 / 2) (f : evenSubspace) :
    (inner ℂ f (burnolReflectedCoShiftContinuation h f)).re =
      (sigma.re - 1 / 2) * ‖burnolReflectedCoShiftContinuation h f‖ ^ 2 := by
  have hright : 1 / 2 < (1 - sigma).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  rw [burnolReflectedCoShiftContinuation_eq_neg,
    neg_apply, inner_neg_right, Complex.neg_re,
    re_inner_burnolMellinDividedShift_eq hright, norm_neg]
  simp only [Complex.sub_re, Complex.one_re]
  ring

/-- Strict negative orientation on every nonzero physical source. -/
theorem re_inner_burnolReflectedCoShiftContinuation_neg
    {sigma : ℂ} (h : sigma.re < 1 / 2) {f : evenSubspace} (hf : f ≠ 0) :
    (inner ℂ f (burnolReflectedCoShiftContinuation h f)).re < 0 := by
  have hright : 1 / 2 < (1 - sigma).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hshift : burnolMellinDividedShift hright f ≠ 0 := by
    intro hz
    exact burnolMellinDividedShift_inner_ne_zero hright hf (by
      rw [hz, inner_zero_right])
  have hreflected : burnolReflectedCoShiftContinuation h f ≠ 0 := by
    rw [burnolReflectedCoShiftContinuation_eq_neg]
    simpa only [neg_apply, neg_ne_zero] using hshift
  rw [re_inner_burnolReflectedCoShiftContinuation_eq h]
  exact mul_neg_of_neg_of_pos (by linarith)
    (sq_pos_of_pos (norm_pos_iff.mpr hreflected))

/-- A bounded physical operator with this Mellin coefficient is forced to be the constructed
continuation. -/
theorem burnolReflectedCoShiftContinuation_unique
    {sigma : ℂ} (h : sigma.re < 1 / 2)
    (T : evenSubspace →L[ℂ] evenSubspace)
    (hT : ∀ f, archimedeanMellinUnitary (T f) =
      burnolSpectralReflectedCoShiftContinuation h
        (archimedeanMellinUnitary f)) :
    T = burnolReflectedCoShiftContinuation h := by
  apply ContinuousLinearMap.ext
  intro f
  apply archimedeanMellinUnitary.injective
  rw [hT]
  simp [burnolReflectedCoShiftContinuation, unitaryPush]

/-! ## Fixed Cartier port and actual Xi-source landing -/

/-- Fixed-source port of the reflected Cartier continuation at the functional-equation mate. -/
def burnolReflectedCoShiftCartierPort
    (rho : ℂ) (h : 1 / 2 < rho.re) : ℂ :=
  inner ℂ burnolFixedSubWindowSourceAtom
    (burnolReflectedCoShiftContinuation (sigma := 1 - rho) (by
      simp only [Complex.sub_re, Complex.one_re]
      linarith) burnolFixedSubWindowSourceAtom)

/-- The reflected Cartier port is exactly the negative physical forward port. -/
theorem burnolReflectedCoShiftCartierPort_eq_neg
    {rho : ℂ} (h : 1 / 2 < rho.re) :
    burnolReflectedCoShiftCartierPort rho h =
      -burnolDividedShiftPhysicalPort rho := by
  unfold burnolReflectedCoShiftCartierPort
  rw [burnolReflectedCoShiftContinuation_one_sub_eq_neg h,
    neg_apply, inner_neg_right,
    burnolDividedShiftPhysicalPort_eq_inner_mellin h]

/-- The reflected fixed-source port is strictly negative off the critical line. -/
theorem re_burnolReflectedCoShiftCartierPort_neg
    {rho : ℂ} (h : 1 / 2 < rho.re) :
    (burnolReflectedCoShiftCartierPort rho h).re < 0 := by
  unfold burnolReflectedCoShiftCartierPort
  exact re_inner_burnolReflectedCoShiftContinuation_neg
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    burnolFixedSubWindowSourceAtom_ne_zero

/-- At an actual right-half Xi divisor, the negative reflected continuation of the fixed atom is
the literal zero-divided extended-Sonin source supplied by Burnol's division theorem. -/
theorem xiDivisor_burnolReflectedCoShiftContinuation_mem_soninExtendedSpace
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolReflectedCoShiftContinuation (sigma := 1 - (rho : ℂ)) (by
        simp only [Complex.sub_re, Complex.one_re]
        linarith) burnolFixedSubWindowSourceAtom ∈
      soninExtendedSpace (subWindowAperture (1 / 2) 1) := by
  have hxi : xi (rho : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support rho
  have hrhoOne : (rho : ℂ) ≠ 1 := by
    intro hrho
    rw [hrho, xi_one] at hxi
    norm_num at hxi
  have hzeta : riemannZeta (rho : ℂ) = 0 :=
    (xi_eq_zero_iff (by linarith) hrhoOne).mp hxi
  have hlt : (rho : ℂ).re < 1 := riemannZeta_zero_re_lt_one hzeta
  have hvalue := soninMellinEvaluation_coPoissonSubWindowSonin_eq_zero
    (c := (1 / 2 : ℝ)) (d := 1) (by norm_num) (by norm_num)
    (by linarith : 0 < (rho : ℂ).re) hzeta
  rw [soninMellinEvaluation] at hvalue
  have hraw :
      (∫ s in Ioi (0 : ℝ),
        (((coPoissonSubWindowSonin (c := (1 / 2 : ℝ)) (d := 1)
          (by norm_num) (by norm_num) :
            soninExtendedSpace (subWindowAperture (1 / 2) 1)) : evenSubspace) :
              SoninL2) s * soninMellinKernel (rho : ℂ) s) = 0 :=
    (mul_eq_zero.mp hvalue).resolve_left
      (mellinCompletionFactor_ne_zero (by linarith))
  have hmem := burnolShift_mem_soninExtendedSpace h hlt
    (subWindowAperture_pos (c := (1 / 2 : ℝ)) (d := 1) (by norm_num) (by norm_num))
    (coPoissonSubWindowSonin (c := (1 / 2 : ℝ)) (d := 1)
      (by norm_num) (by norm_num)).property hraw
  rw [burnolReflectedCoShiftContinuation_one_sub_eq_neg h]
  change -(burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) ∈
    soninExtendedSpace (subWindowAperture (1 / 2) 1)
  rw [← burnolShift_eq_burnolMellinDividedShift h]
  exact (soninExtendedSpace (subWindowAperture (1 / 2) 1)).neg_mem
    (by simpa [burnolFixedSubWindowSourceAtom, coPoissonSubWindowSonin] using hmem)

/-- The reflected continuation packaged as its actual Xi-zero-divided Sonin source lift. -/
def burnolXiReflectedCoShiftCartierSourceLift
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    soninExtendedSpace (subWindowAperture (1 / 2) 1) :=
  ⟨burnolReflectedCoShiftContinuation (sigma := 1 - (rho : ℂ)) (by
      simp only [Complex.sub_re, Complex.one_re]
      linarith) burnolFixedSubWindowSourceAtom,
    xiDivisor_burnolReflectedCoShiftContinuation_mem_soninExtendedSpace rho h⟩

@[simp] theorem coe_burnolXiReflectedCoShiftCartierSourceLift
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    ((burnolXiReflectedCoShiftCartierSourceLift rho h :
      soninExtendedSpace (subWindowAperture (1 / 2) 1)) : evenSubspace) =
      burnolReflectedCoShiftContinuation (sigma := 1 - (rho : ℂ)) (by
        simp only [Complex.sub_re, Complex.one_re]
        linarith) burnolFixedSubWindowSourceAtom := rfl

/-! ## Exact remaining producer signature -/

/-- Source-native sewing still required from pre-divisor Euler--Gamma--Stokes structure: the
forward physical reading equals the fixed reflected zero-divided source reading. -/
def BurnolXiForwardReflectedCartierStokesSewing : Prop :=
  ∀ (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re),
    burnolDividedShiftPhysicalPort (rho : ℂ) =
      inner ℂ burnolFixedSubWindowSourceAtom
        (burnolXiReflectedCoShiftCartierSourceLift rho h : evenSubspace)

/-- Forward/reflected source sewing supplies the missing nonpositive physical sign. -/
theorem burnolXiDividedShiftPhysicalDissipativity_of_forwardReflectedCartierStokesSewing
    (hsew : BurnolXiForwardReflectedCartierStokesSewing) :
    BurnolXiDividedShiftPhysicalDissipativity := by
  intro rho h
  rw [hsew rho h, coe_burnolXiReflectedCoShiftCartierSourceLift]
  exact (re_inner_burnolReflectedCoShiftContinuation_neg
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    burnolFixedSubWindowSourceAtom_ne_zero).le

/-- The constructed Cartier source makes the remaining sewing law a direct RH producer. -/
theorem riemannHypothesis_of_burnolXiForwardReflectedCartierStokesSewing
    (hsew : BurnolXiForwardReflectedCartierStokesSewing) : RiemannHypothesis :=
  riemannHypothesis_of_burnolXiDividedShiftPhysicalDissipativity
    (burnolXiDividedShiftPhysicalDissipativity_of_forwardReflectedCartierStokesSewing hsew)

end RHTower
