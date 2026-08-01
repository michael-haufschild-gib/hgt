import GaloisForLFunctions.RHTower.DeningerKroneckerTranspose
import GaloisForLFunctions.RHTower.DeningerHarmonicUniqueness
import GaloisForLFunctions.RHTower.DeningerTorusCompleteness

/-!
# Descent of the leafwise Hodge system to the character coefficients

The character coefficients of a solution of the leafwise Hodge system solve the two-term radial
system at the frequency of that character.  The radial derivative passes through the torus
integral, and the Kronecker derivative transposes onto the character where it acts by the
frequency.

Combined with the uniqueness of the decaying solution at a fixed frequency, this says that every
coefficient of a square-integrable solution is a scalar multiple of the mode; combined with the
completeness of the characters, that a solution all of whose coefficients vanish is itself zero.

* `deningerCoeff_hasDerivAt` : the radial derivative of a coefficient.
* `deningerCoeff_solves` : the coefficients solve the radial system.
* `deningerCoeff_eq_smul_mode` : each square-integrable coefficient is a multiple of the mode.
-/

namespace RHTower

open UnitAddTorus MeasureTheory Set

/-- The circle is normalised to total mass one, as in the multivariate Fourier theory. -/
noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section Descent

variable {d : Type*} [Fintype d]

/-- The character coefficient of a function on the cylinder. -/
noncomputable def deningerCoeff (n : d → ℤ) (a : ℝ → UnitAddTorus d → ℂ) (r : ℝ) : ℂ :=
  ∫ η : UnitAddTorus d, a r η * (starRingEnd ℂ) (mFourier n η)

/-- **The radial derivative passes through the coefficient integral.** -/
theorem deningerCoeff_hasDerivAt (n : d → ℤ) {a ar' : ℝ → UnitAddTorus d → ℂ}
    (hcont : Continuous fun p : ℝ × UnitAddTorus d => a p.1 p.2)
    (hcont' : Continuous fun p : ℝ × UnitAddTorus d => ar' p.1 p.2)
    (hderiv : ∀ (r : ℝ) (η : UnitAddTorus d), HasDerivAt (fun s => a s η) (ar' r η) r)
    (r₀ : ℝ) :
    HasDerivAt (deningerCoeff n a) (deningerCoeff n ar' r₀) r₀ := by
  have hchar : Continuous fun p : ℝ × UnitAddTorus d => (starRingEnd ℂ) (mFourier n p.2) :=
    Complex.continuous_conj.comp ((mFourier n).continuous.comp continuous_snd)
  exact deningerHasDerivAt_integral (hcont.mul hchar) (hcont'.mul hchar)
    (fun r η => (hderiv r η).mul_const _) r₀

/-- **The character coefficients of a solution solve the radial system.**  The radial derivative
passes through the integral, and the Kronecker derivative transposes onto the character. -/
theorem deningerCoeff_solves (lam : d → ℝ) (n : d → ℤ)
    {a b ar' br' Ya Yb : ℝ → UnitAddTorus d → ℂ}
    (hca : Continuous fun p : ℝ × UnitAddTorus d => a p.1 p.2)
    (hcb : Continuous fun p : ℝ × UnitAddTorus d => b p.1 p.2)
    (hcar : Continuous fun p : ℝ × UnitAddTorus d => ar' p.1 p.2)
    (hcbr : Continuous fun p : ℝ × UnitAddTorus d => br' p.1 p.2)
    (hcYa : Continuous fun p : ℝ × UnitAddTorus d => Ya p.1 p.2)
    (hcYb : Continuous fun p : ℝ × UnitAddTorus d => Yb p.1 p.2)
    (hra : ∀ (r : ℝ) (η : UnitAddTorus d), HasDerivAt (fun s => a s η) (ar' r η) r)
    (hrb : ∀ (r : ℝ) (η : UnitAddTorus d), HasDerivAt (fun s => b s η) (br' r η) r)
    (hYa : ∀ (r t : ℝ) (η : UnitAddTorus d),
      HasDerivAt (fun s : ℝ => a r (η + deningerTorusFlow lam s))
        (Ya r (η + deningerTorusFlow lam t)) t)
    (hYb : ∀ (r t : ℝ) (η : UnitAddTorus d),
      HasDerivAt (fun s : ℝ => b r (η + deningerTorusFlow lam s))
        (Yb r (η + deningerTorusFlow lam t)) t)
    (hsys₁ : ∀ (r : ℝ) (η : UnitAddTorus d), ar' r η = -(Yb r η))
    (hsys₂ : ∀ (r : ℝ) (η : UnitAddTorus d), br' r η = Ya r η) (r₀ : ℝ) :
    HasDerivAt (deningerCoeff n a)
        (-(Complex.I * ((2 * Real.pi * deningerFrequency n lam : ℝ) : ℂ)
          * deningerCoeff n b r₀)) r₀
      ∧ HasDerivAt (deningerCoeff n b)
        (Complex.I * ((2 * Real.pi * deningerFrequency n lam : ℝ) : ℂ)
          * deningerCoeff n a r₀) r₀ := by
  have hslice : ∀ (c : ℝ → UnitAddTorus d → ℂ),
      (Continuous fun p : ℝ × UnitAddTorus d => c p.1 p.2) →
        ∀ r : ℝ, Continuous fun η : UnitAddTorus d => c r η :=
    fun c hc r => hc.comp (continuous_const.prodMk continuous_id)
  constructor
  · have hd := deningerCoeff_hasDerivAt n hca hcar hra r₀
    have hval : deningerCoeff n ar' r₀
        = -(Complex.I * ((2 * Real.pi * deningerFrequency n lam : ℝ) : ℂ)
          * deningerCoeff n b r₀) := by
      have htr := deningerKroneckerCoeff lam n (hslice b hcb r₀) (hslice Yb hcYb r₀)
        (fun t η => hYb r₀ t η)
      have hcong : deningerCoeff n ar' r₀ = -deningerCoeff n Yb r₀ := by
        rw [deningerCoeff, deningerCoeff, ← integral_neg]
        refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
        dsimp only
        rw [hsys₁ r₀ η]
        ring
      rw [hcong, deningerCoeff, htr, deningerCoeff]
      ring
    rw [← hval]
    exact hd
  · have hd := deningerCoeff_hasDerivAt n hcb hcbr hrb r₀
    have hval : deningerCoeff n br' r₀
        = Complex.I * ((2 * Real.pi * deningerFrequency n lam : ℝ) : ℂ)
          * deningerCoeff n a r₀ := by
      have htr := deningerKroneckerCoeff lam n (hslice a hca r₀) (hslice Ya hcYa r₀)
        (fun t η => hYa r₀ t η)
      have hcong : deningerCoeff n br' r₀ = deningerCoeff n Ya r₀ := by
        rw [deningerCoeff, deningerCoeff]
        refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
        dsimp only
        rw [hsys₂ r₀ η]
      rw [hcong, deningerCoeff, htr, deningerCoeff]
      ring
    rw [← hval]
    exact hd

/-- **Each square-integrable coefficient of a solution is a scalar multiple of the mode.**  This is
the mode decomposition of the solution space, coefficient by coefficient. -/
theorem deningerCoeff_eq_smul_mode (lam : d → ℝ) (n : d → ℤ)
    {a b ar' br' Ya Yb : ℝ → UnitAddTorus d → ℂ}
    (hca : Continuous fun p : ℝ × UnitAddTorus d => a p.1 p.2)
    (hcb : Continuous fun p : ℝ × UnitAddTorus d => b p.1 p.2)
    (hcar : Continuous fun p : ℝ × UnitAddTorus d => ar' p.1 p.2)
    (hcbr : Continuous fun p : ℝ × UnitAddTorus d => br' p.1 p.2)
    (hcYa : Continuous fun p : ℝ × UnitAddTorus d => Ya p.1 p.2)
    (hcYb : Continuous fun p : ℝ × UnitAddTorus d => Yb p.1 p.2)
    (hra : ∀ (r : ℝ) (η : UnitAddTorus d), HasDerivAt (fun s => a s η) (ar' r η) r)
    (hrb : ∀ (r : ℝ) (η : UnitAddTorus d), HasDerivAt (fun s => b s η) (br' r η) r)
    (hYa : ∀ (r t : ℝ) (η : UnitAddTorus d),
      HasDerivAt (fun s : ℝ => a r (η + deningerTorusFlow lam s))
        (Ya r (η + deningerTorusFlow lam t)) t)
    (hYb : ∀ (r t : ℝ) (η : UnitAddTorus d),
      HasDerivAt (fun s : ℝ => b r (η + deningerTorusFlow lam s))
        (Yb r (η + deningerTorusFlow lam t)) t)
    (hsys₁ : ∀ (r : ℝ) (η : UnitAddTorus d), ar' r η = -(Yb r η))
    (hsys₂ : ∀ (r : ℝ) (η : UnitAddTorus d), br' r η = Ya r η)
    (hfreq : 2 * Real.pi * deningerFrequency n lam ≠ 0)
    (hL2 : IntegrableOn
      (fun r => ‖deningerCoeff n a r‖ ^ 2 + ‖deningerCoeff n b r‖ ^ 2) (Ioi (0 : ℝ))) :
    ∃ c : ℂ, ∀ r ∈ Ioi (0 : ℝ),
      (deningerCoeff n a r, deningerCoeff n b r)
        = c • deningerMode (2 * Real.pi * deningerFrequency n lam) r := by
  refine deningerSolution_eq_smul_mode hfreq (fun r _ => ?_) (fun r _ => ?_) hL2
  · exact (deningerCoeff_solves lam n hca hcb hcar hcbr hcYa hcYb hra hrb hYa hYb
      hsys₁ hsys₂ r).1
  · exact (deningerCoeff_solves lam n hca hcb hcar hcbr hcYa hcYb hra hrb hYa hYb
      hsys₁ hsys₂ r).2

/-- **A solution invisible to every character vanishes.**  Together with the mode decomposition of
each coefficient, and the mutual orthogonality of the modes, this exhausts the square-integrable
solution space. -/
theorem deningerSolution_eq_zero_of_coeff_zero {a : ℝ → UnitAddTorus d → ℂ}
    (hcont : ∀ r : ℝ, Continuous fun η : UnitAddTorus d => a r η)
    (hzero : ∀ (n : d → ℤ) (r : ℝ), deningerCoeff n a r = 0) (r : ℝ) (η : UnitAddTorus d) :
    a r η = 0 := by
  have h : (⟨fun η => a r η, hcont r⟩ : C(UnitAddTorus d, ℂ)) = 0 :=
    deningerTorusCompleteness fun n => hzero n r
  exact DFunLike.congr_fun h η

end Descent

end RHTower
