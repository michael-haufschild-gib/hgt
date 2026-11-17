import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatEvenPotential
import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatIntegralRoot
import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatDescentNoUniformRate

/-!
# A unique critical profile without a norm error bound

The reflected flat loss gives a C¹ energy on every real L² space with
a globally contractive gradient and exactly one critical profile: zero.
On Lebesgue L², unit profiles nevertheless have arbitrarily small energy
and gradient. Removing the original flat minimizer cone therefore does
not remove the failure of residuals to control distance to the minimum.
-/

open MeasureTheory Filter
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def evenIntegralEnergy (f : Lp ℝ 2 μ) : ℝ := integralEnergy f + integralEnergy (-f)

def evenGradientLp (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  evenGradient_contraction.compLp evenGradient_zero f

theorem evenGradientLp_eq (f : Lp ℝ 2 μ) :
    evenGradientLp f = gradientLp f - gradientLp (-f) := by
  apply Lp.ext
  filter_upwards [evenGradient_contraction.coeFn_compLp evenGradient_zero f,
    gradient_contraction.coeFn_compLp gradient_zero f,
    gradient_contraction.coeFn_compLp gradient_zero (-f), Lp.coeFn_neg f,
    Lp.coeFn_sub (gradientLp f) (gradientLp (-f))] with x he hf hg hn hd
  change (evenGradient_contraction.compLp evenGradient_zero f) x = _
  rw [he, hd]
  simp only [Pi.sub_apply]
  change evenGradient (f x) = (gradient_contraction.compLp gradient_zero f) x -
    (gradient_contraction.compLp gradient_zero (-f)) x
  rw [hf, hg]
  simp only [Function.comp_apply]
  rw [hn]
  rfl

theorem evenGradientLp_contraction : LipschitzWith 1 (evenGradientLp : Lp ℝ 2 μ → Lp ℝ 2 μ) :=
  evenGradient_contraction.lipschitzWith_compLp evenGradient_zero

/-- The pointwise reflected gradient is the true Hilbert-space Fréchet gradient. -/
theorem evenIntegralEnergy_hasFDerivAt (f : Lp ℝ 2 μ) :
    HasFDerivAt evenIntegralEnergy (innerSL ℝ (evenGradientLp f)) f := by
  have hn : HasFDerivAt (fun g : Lp ℝ 2 μ => integralEnergy (-g))
      ((innerSL ℝ (gradientLp (-f))).comp
        (-(ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)))) f :=
    (integralEnergy_hasFDerivAt (-f)).comp f
      (-(ContinuousLinearMap.id ℝ (Lp ℝ 2 μ))).hasFDerivAt
  have h : HasFDerivAt evenIntegralEnergy
      (innerSL ℝ (gradientLp f) + (innerSL ℝ (gradientLp (-f))).comp
        (-(ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)))) f :=
    (integralEnergy_hasFDerivAt f).add hn
  have he : innerSL ℝ (gradientLp f) + (innerSL ℝ (gradientLp (-f))).comp
      (-(ContinuousLinearMap.id ℝ (Lp ℝ 2 μ))) = innerSL ℝ (evenGradientLp f) := by
    ext v
    change inner ℝ (gradientLp f) v + inner ℝ (gradientLp (-f)) (-v) =
      inner ℝ (evenGradientLp f) v
    rw [evenGradientLp_eq, inner_sub_left, inner_neg_right]
    ring
  rwa [he] at h

theorem evenIntegralEnergy_contDiff_one : ContDiff ℝ 1 (evenIntegralEnergy : Lp ℝ 2 μ → ℝ) :=
  integralEnergy_contDiff_one.add (integralEnergy_contDiff_one.comp contDiff_id.neg)

/-- The reflected gradient has no nonzero zero, including on infinite measure spaces. -/
theorem evenGradientLp_zero_iff (f : Lp ℝ 2 μ) : evenGradientLp f = 0 ↔ f = 0 := by
  constructor
  · intro h
    apply Lp.ext
    filter_upwards [evenGradient_contraction.coeFn_compLp evenGradient_zero f,
      Lp.coeFn_zero ℝ 2 μ] with x hx hz
    change evenGradientLp f x = evenGradient (f x) at hx
    rw [h, hz] at hx
    have hf : f x = 0 := (evenGradient_zero_iff _).mp (by
      simpa only [Pi.zero_apply] using hx.symm)
    rw [hf, hz]
    rfl
  · rintro rfl
    exact evenGradient_contraction.compLp_zero evenGradient_zero

private theorem energy_zero_profile : integralEnergy (0 : Lp ℝ 2 μ) = 0 := by
  apply (integralEnergy_zero_iff _).mpr
  filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
  simp only [hx, Pi.zero_apply, le_refl]

/-- Reflection changes the entire minimizer cone into one genuine Hilbert-space point. -/
theorem evenIntegralEnergy_zero_iff (f : Lp ℝ 2 μ) : evenIntegralEnergy f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hp : integralEnergy f = 0 := by
      unfold evenIntegralEnergy at h
      linarith only [h, (integral_energy_bounds f).1, (integral_energy_bounds (-f)).1]
    have hn : integralEnergy (-f) = 0 := by
      unfold evenIntegralEnergy at h
      linarith only [h, (integral_energy_bounds f).1, (integral_energy_bounds (-f)).1]
    apply Lp.ext
    filter_upwards [(integralEnergy_zero_iff _).mp hp, (integralEnergy_zero_iff _).mp hn,
      Lp.coeFn_neg f, Lp.coeFn_zero ℝ 2 μ] with x hp' hn' he hz
    rw [he] at hn'
    rw [hz]
    change f x = 0
    change -f x ≤ 0 at hn'
    linarith only [hp', hn']
  · rintro rfl
    rw [evenIntegralEnergy, neg_zero, energy_zero_profile, add_zero]

/-- The full Fréchet critical-point equation has exactly the zero profile as its solution. -/
theorem evenIntegralEnergy_critical_iff (f : Lp ℝ 2 μ) :
    fderiv ℝ evenIntegralEnergy f = 0 ↔ f = 0 := by
  rw [(evenIntegralEnergy_hasFDerivAt f).fderiv]
  constructor
  · intro h
    have hn := congrArg norm h
    rw [innerSL_apply_norm, norm_zero] at hn
    exact (evenGradientLp_zero_iff f).mp (norm_eq_zero.mp hn)
  · intro h
    rw [(evenGradientLp_zero_iff f).mpr h]
    exact map_zero (innerSL ℝ)

private theorem gradientLp_zero_of_nonpos (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, f x ≤ 0) :
    gradientLp f = 0 := by
  apply Lp.ext
  filter_upwards [gradient_contraction.coeFn_compLp gradient_zero f, hf,
    Lp.coeFn_zero ℝ 2 μ] with x hx hf' hz
  change (gradient_contraction.compLp gradient_zero f) x = _
  rw [hx, hz]
  exact (gradient_zero_iff _).mpr hf'

/-- A unique critical point does not make small energy and small gradient control the norm. -/
theorem evenEnergy_unit_approximate_critical_profile {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Lp ℝ 2 (volume : Measure ℝ), ‖f‖ = 1 ∧
      (0 < evenIntegralEnergy f ∧ evenIntegralEnergy f < ε) ∧
      (0 < ‖evenGradientLp f‖ ∧ ‖evenGradientLp f‖ < ε) := by
  obtain ⟨f, hn, hp, he, hg⟩ := exists_unit_approximate_critical_profile hε
  have hnonneg : ∀ᵐ x ∂volume, 0 ≤ f x := by
    filter_upwards [negativePartLp_ae f, Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with x hx hz
    rw [hp, hz] at hx
    change 0 = min (f x) 0 at hx
    have hh := min_le_left (f x) 0
    linarith only [hx, hh]
  have hneg : ∀ᵐ x ∂volume, (-f) x ≤ 0 := by
    filter_upwards [Lp.coeFn_neg f, hnonneg] with x hx hf
    rw [hx]
    exact neg_nonpos.mpr hf
  have he' : evenIntegralEnergy f = integralEnergy f := by
    rw [evenIntegralEnergy, (integralEnergy_zero_iff (-f)).mpr hneg, add_zero]
  have hg' : evenGradientLp f = gradientLp f := by
    rw [evenGradientLp_eq, gradientLp_zero_of_nonpos (-f) hneg, sub_zero]
  exact ⟨f, hn, by rwa [he'], by rwa [hg']⟩

#print axioms evenGradientLp_contraction
#print axioms evenIntegralEnergy_hasFDerivAt
#print axioms evenIntegralEnergy_contDiff_one
#print axioms evenIntegralEnergy_zero_iff
#print axioms evenIntegralEnergy_critical_iff
#print axioms evenEnergy_unit_approximate_critical_profile
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
