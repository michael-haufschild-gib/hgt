import GaloisForLFunctions.RHTower.Deninger.DeningerParametricTorus
import GaloisForLFunctions.RHTower.Deninger.DeningerCylinderModes

/-!
# Transposing the Kronecker derivative onto a character

The Kronecker vector field differentiates along the linear flow.  Integrating its action against a
character transposes it onto the character, where it acts by the frequency: this is the identity
`Y χ_a = i ℓ(a) χ_a` in its integrated form.

The proof does not differentiate the character.  Translation invariance of Haar measure moves the
flow off the function and onto the character, where it becomes the explicit one-frequency
oscillation; differentiating that scalar factor at time zero produces the frequency, while
differentiating under the integral sign produces the integral of the Kronecker derivative.

* `deningerTorusFlow_zero`, `deningerTorusFlow_neg` : the flow is a one-parameter group.
* `deningerKronecker_transpose` : the transposition identity.
* `deningerKroneckerCoeff` : the Fourier coefficient form.
-/

namespace RHTower

open UnitAddTorus MeasureTheory Set

/-- The circle is normalised to total mass one, as in the multivariate Fourier theory. -/
noncomputable local instance deningerKroneckerTransposeMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance deningerKroneckerTransposeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance deningerKroneckerTransposeIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section Transpose

variable {d : Type*} [Fintype d]

omit [Fintype d] in
@[simp] theorem deningerTorusFlow_zero (lam : d → ℝ) : deningerTorusFlow lam 0 = 0 := by
  funext i
  show ((0 * lam i : ℝ) : AddCircle (1 : ℝ)) = 0
  rw [zero_mul]
  rfl

omit [Fintype d] in
theorem deningerTorusFlow_neg (lam : d → ℝ) (t : ℝ) :
    deningerTorusFlow lam (-t) = -deningerTorusFlow lam t := by
  funext i
  show ((-t * lam i : ℝ) : AddCircle (1 : ℝ)) = -((t * lam i : ℝ) : AddCircle (1 : ℝ))
  rw [neg_mul]
  simp

/-- **The transposition identity.**  Integrating the Kronecker derivative against a character is
multiplication by the frequency of that character. -/
theorem deningerKronecker_transpose (lam : d → ℝ) (n : d → ℤ)
    {f Yf : UnitAddTorus d → ℂ} (hf : Continuous f) (hYf : Continuous Yf)
    (hderiv : ∀ (t : ℝ) (η : UnitAddTorus d),
      HasDerivAt (fun s : ℝ => f (η + deningerTorusFlow lam s))
        (Yf (η + deningerTorusFlow lam t)) t) :
    (∫ η : UnitAddTorus d, Yf η * mFourier (-n) η)
      = ((2 * Real.pi * deningerFrequency n lam : ℝ) : ℂ) * Complex.I
        * ∫ η : UnitAddTorus d, f η * mFourier (-n) η := by
  set μ := deningerFrequency n lam with hμ
  set C : ℂ := ∫ η : UnitAddTorus d, f η * mFourier (-n) η with hC
  set G : ℝ → ℂ :=
    fun t => ∫ η : UnitAddTorus d, f (η + deningerTorusFlow lam t) * mFourier (-n) η with hG
  have hflowcont := deningerTorusFlow_continuous lam
  -- the flow can be moved onto the character, where it is an explicit oscillation
  have key : ∀ t : ℝ, G t = Complex.exp (((2 * Real.pi * μ * t : ℝ) : ℂ) * Complex.I) * C := by
    intro t
    have htrans := integral_add_right_eq_self (μ := (volume : Measure (UnitAddTorus d)))
      (fun η : UnitAddTorus d => f (η + deningerTorusFlow lam t) * mFourier (-n) η)
      (-deningerTorusFlow lam t)
    have hpt : ∀ η : UnitAddTorus d,
        f (η + -deningerTorusFlow lam t + deningerTorusFlow lam t)
            * mFourier (-n) (η + -deningerTorusFlow lam t)
          = (f η * mFourier (-n) η)
            * Complex.exp (((2 * Real.pi * μ * t : ℝ) : ℂ) * Complex.I) := by
      intro η
      rw [neg_add_cancel_right, deningerMFourier_arg_add,
        show -deningerTorusFlow lam t = deningerTorusFlow lam (-t) from
          (deningerTorusFlow_neg lam t).symm,
        deningerMFourier_flow, deningerFrequency_neg,
        show (2 * Real.pi * -μ * -t : ℝ) = (2 * Real.pi * μ * t : ℝ) by rw [hμ]; ring]
      ring
    rw [hG]
    show (∫ η : UnitAddTorus d, f (η + deningerTorusFlow lam t) * mFourier (-n) η) = _
    rw [← htrans]
    show (∫ η : UnitAddTorus d,
      f (η + -deningerTorusFlow lam t + deningerTorusFlow lam t)
        * mFourier (-n) (η + -deningerTorusFlow lam t)) = _
    rw [funext hpt, integral_mul_const, ← hC, mul_comm]
  -- differentiation under the integral sign
  have hjoint : Continuous fun p : ℝ × UnitAddTorus d =>
      f (p.2 + deningerTorusFlow lam p.1) * mFourier (-n) p.2 :=
    (hf.comp (continuous_snd.add (hflowcont.comp continuous_fst))).mul
      ((mFourier (-n)).continuous.comp continuous_snd)
  have hjoint' : Continuous fun p : ℝ × UnitAddTorus d =>
      Yf (p.2 + deningerTorusFlow lam p.1) * mFourier (-n) p.2 :=
    (hYf.comp (continuous_snd.add (hflowcont.comp continuous_fst))).mul
      ((mFourier (-n)).continuous.comp continuous_snd)
  have hGderiv : HasDerivAt G
      (∫ η : UnitAddTorus d,
        Yf (η + deningerTorusFlow lam 0) * mFourier (-n) η) 0 :=
    deningerHasDerivAt_integral hjoint hjoint' (fun t η => (hderiv t η).mul_const _) 0
  -- differentiation of the explicit oscillation
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (((2 * Real.pi * μ * t : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((2 * Real.pi * μ * 0 : ℝ) : ℂ) * Complex.I)
        * (((2 * Real.pi * μ : ℝ) : ℂ) * Complex.I)) 0 := by
    have hlin : HasDerivAt (fun t : ℝ => ((2 * Real.pi * μ * t : ℝ) : ℂ) * Complex.I)
        (((2 * Real.pi * μ : ℝ) : ℂ) * Complex.I) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => (2 * Real.pi * μ * t : ℝ)) (2 * Real.pi * μ) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * Real.pi * μ)
      exact (h1.ofReal_comp).mul_const Complex.I
    exact hlin.cexp
  have hRHS : HasDerivAt (fun t : ℝ =>
      Complex.exp (((2 * Real.pi * μ * t : ℝ) : ℂ) * Complex.I) * C)
      ((((2 * Real.pi * μ : ℝ) : ℂ) * Complex.I) * C) 0 := by
    have h := hexp.mul_const C
    rw [show (2 * Real.pi * μ * 0 : ℝ) = 0 by ring] at h
    simpa using h
  have hGeq : G = fun t : ℝ =>
      Complex.exp (((2 * Real.pi * μ * t : ℝ) : ℂ) * Complex.I) * C := funext key
  rw [hGeq] at hGderiv
  have huniq := hGderiv.unique hRHS
  rw [deningerTorusFlow_zero] at huniq
  simpa using huniq

/-- **The Fourier coefficient form of the transposition identity.** -/
theorem deningerKroneckerCoeff (lam : d → ℝ) (n : d → ℤ)
    {f Yf : UnitAddTorus d → ℂ} (hf : Continuous f) (hYf : Continuous Yf)
    (hderiv : ∀ (t : ℝ) (η : UnitAddTorus d),
      HasDerivAt (fun s : ℝ => f (η + deningerTorusFlow lam s))
        (Yf (η + deningerTorusFlow lam t)) t) :
    (∫ η : UnitAddTorus d, Yf η * (starRingEnd ℂ) (mFourier n η))
      = ((2 * Real.pi * deningerFrequency n lam : ℝ) : ℂ) * Complex.I
        * ∫ η : UnitAddTorus d, f η * (starRingEnd ℂ) (mFourier n η) := by
  have hconj : ∀ η : UnitAddTorus d, (starRingEnd ℂ) (mFourier n η) = mFourier (-n) η :=
    fun η => (mFourier_neg).symm
  simp only [hconj]
  exact deningerKronecker_transpose lam n hf hYf hderiv

end Transpose

end RHTower
