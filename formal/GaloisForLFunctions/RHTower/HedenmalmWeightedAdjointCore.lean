import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy

/-!
# The weighted formal adjoint of the Hedenmalm pair

In the weighted space `H_k = L²(ℝ, k⁻¹ dx)` the differential expression `D = -i ∂_x` has weighted
formal adjoint

`L = k D k⁻¹ = D + i k'/k`.

On compactly supported differentiable data this is a single integration by parts: the function
`f ḡ / k` has compact support, so its derivative integrates to zero, and the three terms of that
derivative are exactly the difference of the two sides of the weighted pairing.

Multiplication by the half density `k^{1/2}` conjugates the plain derivative into the derivative
shifted by half the logarithmic derivative of the source; that identity is the pointwise calculus
at the end.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile

/-! ### The logarithmic derivative of the source -/

/-- The derivative of the theta source. -/
def sourceDeriv (x : ℝ) : ℝ := deriv thetaCuspFullSource x

theorem hasDerivAt_thetaCuspFullSource (x : ℝ) :
    HasDerivAt thetaCuspFullSource (sourceDeriv x) x :=
  (contDiff_thetaCuspFullSource.differentiable (by simp) x).hasDerivAt

theorem continuous_sourceDeriv : Continuous sourceDeriv :=
  contDiff_thetaCuspFullSource.continuous_deriv (by simp)

/-- The logarithmic derivative `a = k'/k` of the theta source. -/
def sourceLogDeriv (x : ℝ) : ℝ := sourceDeriv x / thetaCuspFullSource x

theorem continuous_sourceLogDeriv : Continuous sourceLogDeriv :=
  continuous_sourceDeriv.div contDiff_thetaCuspFullSource.continuous
    fun x => (thetaCuspFullSource_pos x).ne'

/-! ### The complexified weight -/

/-- The complexified source weight. -/
def sourceWeightC (x : ℝ) : ℂ := ((thetaCuspFullSource x : ℝ) : ℂ)

theorem sourceWeightC_ne_zero (x : ℝ) : sourceWeightC x ≠ 0 := by
  rw [sourceWeightC]
  exact_mod_cast (thetaCuspFullSource_pos x).ne'

theorem continuous_sourceWeightC : Continuous sourceWeightC :=
  Complex.continuous_ofReal.comp contDiff_thetaCuspFullSource.continuous

theorem hasDerivAt_sourceWeightC (x : ℝ) :
    HasDerivAt sourceWeightC ((sourceDeriv x : ℝ) : ℂ) x :=
  (hasDerivAt_thetaCuspFullSource x).ofReal_comp

/-! ### The weighted pairing -/

/-- **The weighted formal symmetry of the Hedenmalm pair.**  On compactly supported
differentiable data,

`⟨D f, g⟩_{H_k} = ⟨f, L g⟩_{H_k}`,  with `L = D + i k'/k`. -/
theorem integral_weighted_symmetry {f g f' g' : ℝ → ℂ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hfc : Continuous f) (hgc : Continuous g)
    (hfc' : Continuous f') (hgc' : Continuous g')
    (hfs : HasCompactSupport f) (hfs' : HasCompactSupport f') :
    (∫ x, (-Complex.I * f' x) * (starRingEnd ℂ) (g x) / sourceWeightC x)
      = ∫ x, f x * (starRingEnd ℂ) (-Complex.I * g' x
          + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * g x) / sourceWeightC x := by
  have hinv : Continuous fun x : ℝ => (sourceWeightC x)⁻¹ :=
    continuous_sourceWeightC.inv₀ sourceWeightC_ne_zero
  set F : ℝ → ℂ := fun x => f x * (starRingEnd ℂ) (g x) * (sourceWeightC x)⁻¹ with hF
  set F' : ℝ → ℂ := fun x =>
    (f' x * (starRingEnd ℂ) (g x) + f x * (starRingEnd ℂ) (g' x)) * (sourceWeightC x)⁻¹
      + f x * (starRingEnd ℂ) (g x) * (-((sourceDeriv x : ℝ) : ℂ) / sourceWeightC x ^ 2) with hF'
  have hderiv : ∀ x, HasDerivAt F (F' x) x := by
    intro x
    have h1 : HasDerivAt (fun t => f t * (starRingEnd ℂ) (g t))
        (f' x * (starRingEnd ℂ) (g x) + f x * (starRingEnd ℂ) (g' x)) x := (hf x).mul (hg x).star
    have h2 : HasDerivAt (fun t => (sourceWeightC t)⁻¹)
        (-((sourceDeriv x : ℝ) : ℂ) / sourceWeightC x ^ 2) x :=
      (hasDerivAt_sourceWeightC x).inv (sourceWeightC_ne_zero x)
    exact h1.mul h2
  have hF'cont : Continuous F' := by
    rw [hF']
    refine Continuous.add ?_ ?_
    · exact ((hfc'.mul (Complex.continuous_conj.comp hgc)).add
        (hfc.mul (Complex.continuous_conj.comp hgc'))).mul hinv
    · refine (hfc.mul (Complex.continuous_conj.comp hgc)).mul ?_
      exact (Complex.continuous_ofReal.comp continuous_sourceDeriv).neg.div
        (continuous_sourceWeightC.pow 2) fun x => pow_ne_zero 2 (sourceWeightC_ne_zero x)
  have hFs : HasCompactSupport F := by
    rw [hF]
    exact (hfs.mul_right).mul_right
  have hFeq : deriv F = F' := funext fun x => (hderiv x).deriv
  have hFs' : HasCompactSupport F' := hFeq ▸ hFs.deriv
  have hzeroInf := hFs.is_zero_at_infty
  rw [cocompact_eq_atBot_atTop] at hzeroInf
  have hzero : (∫ x, F' x) = 0 := by
    have h := MeasureTheory.integral_of_hasDerivAt_of_tendsto hderiv
      (hF'cont.integrable_of_hasCompactSupport hFs')
      (hzeroInf.mono_left le_sup_left) (hzeroInf.mono_left le_sup_right)
    simpa using h
  have hLcont : Continuous
      (fun x => (-Complex.I * f' x) * (starRingEnd ℂ) (g x) / sourceWeightC x) :=
    ((continuous_const.mul hfc').mul (Complex.continuous_conj.comp hgc)).div
      continuous_sourceWeightC sourceWeightC_ne_zero
  have hLs : HasCompactSupport
      (fun x => (-Complex.I * f' x) * (starRingEnd ℂ) (g x) / sourceWeightC x) := by
    have : HasCompactSupport (fun x => -Complex.I * f' x) := hfs'.mul_left
    exact (this.mul_right).div_right
  have hRcont : Continuous
      (fun x => f x * (starRingEnd ℂ) (-Complex.I * g' x
        + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * g x) / sourceWeightC x) := by
    refine Continuous.div (hfc.mul (Complex.continuous_conj.comp ?_)) continuous_sourceWeightC
      sourceWeightC_ne_zero
    exact (continuous_const.mul hgc').add
      ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_sourceLogDeriv)).mul hgc)
  have hRs : HasCompactSupport
      (fun x => f x * (starRingEnd ℂ) (-Complex.I * g' x
        + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * g x) / sourceWeightC x) :=
    (hfs.mul_right).div_right
  have hpt : ∀ x, (-Complex.I * f' x) * (starRingEnd ℂ) (g x) / sourceWeightC x
      - f x * (starRingEnd ℂ) (-Complex.I * g' x
          + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * g x) / sourceWeightC x
      = -Complex.I * F' x := by
    intro x
    have hK := sourceWeightC_ne_zero x
    have ha : ((sourceLogDeriv x : ℝ) : ℂ) = ((sourceDeriv x : ℝ) : ℂ) / sourceWeightC x := by
      rw [sourceLogDeriv, sourceWeightC, Complex.ofReal_div]
    have hconj : (starRingEnd ℂ) (-Complex.I * g' x
        + Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * g x)
        = Complex.I * (starRingEnd ℂ) (g' x)
          - Complex.I * ((sourceLogDeriv x : ℝ) : ℂ) * (starRingEnd ℂ) (g x) := by
      simp only [map_add, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hconj, ha, hF']
    field_simp
    ring
  have hsub := MeasureTheory.integral_sub (hLcont.integrable_of_hasCompactSupport hLs)
    (hRcont.integrable_of_hasCompactSupport hRs)
  rw [← sub_eq_zero, hsub, integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul, hzero, mul_zero]

/-! ### The half-density conjugation -/

/-- **The half-density conjugation.**  Multiplying by `k^{1/2}` turns the plain derivative into the
derivative shifted by half the logarithmic derivative of the source; equivalently
`U D U^{-1} = D - (i/2) k'/k` for the unitary `U` of multiplication by `k^{-1/2}`. -/
theorem hasDerivAt_halfDensity_mul {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (fun t => ((Real.sqrt (thetaCuspFullSource t) : ℝ) : ℂ) * f t)
      (((Real.sqrt (thetaCuspFullSource x) : ℝ) : ℂ)
        * (f' x + ((sourceLogDeriv x / 2 : ℝ) : ℂ) * f x)) x := by
  have hkpos : 0 < thetaCuspFullSource x := thetaCuspFullSource_pos x
  have hsqrtpos : 0 < Real.sqrt (thetaCuspFullSource x) := Real.sqrt_pos.mpr hkpos
  have hsq : HasDerivAt (fun t => Real.sqrt (thetaCuspFullSource t))
      (sourceDeriv x / (2 * Real.sqrt (thetaCuspFullSource x))) x := by
    have h := (Real.hasDerivAt_sqrt hkpos.ne').comp x (hasDerivAt_thetaCuspFullSource x)
    refine h.congr_deriv ?_
    field_simp
  have hsqC : HasDerivAt (fun t => ((Real.sqrt (thetaCuspFullSource t) : ℝ) : ℂ))
      (((sourceDeriv x / (2 * Real.sqrt (thetaCuspFullSource x)) : ℝ) : ℂ)) x :=
    hsq.ofReal_comp
  refine (hsqC.mul (hf x)).congr_deriv ?_
  have hsqrtne : (Real.sqrt (thetaCuspFullSource x) : ℝ) ≠ 0 := hsqrtpos.ne'
  have hsqrtsq : Real.sqrt (thetaCuspFullSource x) * Real.sqrt (thetaCuspFullSource x)
      = thetaCuspFullSource x := Real.mul_self_sqrt hkpos.le
  have hkne : (thetaCuspFullSource x : ℝ) ≠ 0 := hkpos.ne'
  have hgoal : ((sourceDeriv x / (2 * Real.sqrt (thetaCuspFullSource x)) : ℝ) : ℂ)
      = ((Real.sqrt (thetaCuspFullSource x) : ℝ) : ℂ) * ((sourceLogDeriv x / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [sourceLogDeriv, ← hsqrtsq]
    field_simp
    ring
  rw [hgoal]
  ring

end HedenmalmThetaSource

end

end RHTower
