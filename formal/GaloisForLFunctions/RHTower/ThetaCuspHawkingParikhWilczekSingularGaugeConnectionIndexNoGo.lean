import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekSingularCarrierRescalingGaugeNoGo
import GaloisForLFunctions.HTGeometry.HillFundamentalPair
import GaloisForLFunctions.HTGeometry.HyperbolicBounds
import GaloisForLFunctions.HTGeometry.OscillatorProductMonotone

/-!
# The singular PW gauge has zero connection index and no canonical Hilbert density

In logarithmic recoil coordinate `t = log x`, the exact positive-ray Parikh--Wilczek gain is

`a(t) = exp(2 phi(t))`, where `phi(t) = sinh(t) - t/2`.

Its forced gauge connection has potential `phi'(t) = cosh(t) - 1/2 > 0`. This module classifies
all horizontal sections of both orientations: they are respectively constant multiples of
`exp(phi)` and `exp(-phi)`. The first grows on the right half-line and the second on the left, so
neither orientation has a nonzero square-integrable horizontal section. Hence the natural
kernel-imbalance/Witten index of the exact singular gauge is zero.

The weighted reflection `T f(t) = a(t) f(-t)` also fails to choose a Hilbert geometry. Every
positive pointwise density making it energy-unitary is exactly

`w(t) = a(t)⁻¹ h(t)`

for an arbitrary positive even function `h`. For every such density, `T` preserves both the
maximal finite-energy domain and total quadratic energy. Thus the singular Borel edge supplies
neither a nonzero connection index nor a source-independent normalization.

This kills the connection-index/operator-domain branch in

`PW winding -> singular FE partner -> intrinsic edge index -> partner balance -> Deninger Ward -> RH`.

A surviving PW-B route must supply an independently source-normalized measure/domain or derive
partner balance directly from source dynamics.

`[NEW] [PW-B ROUTE-CLASS NO-GO] [CONNECTION INDEX ZERO] [DENSITY CLASSIFICATION] [LEAN-PROVED]`
-/

open Real Set MeasureTheory

namespace RHTower

noncomputable section

def pwLogSingularGaugePotential (t : ℝ) : ℝ := Real.sinh t - t / 2

def pwLogSingularConnectionPotential (t : ℝ) : ℝ := Real.cosh t - 1 / 2

def pwLogSingularGauge (t : ℝ) : ℝ := Real.exp (pwLogSingularGaugePotential t)

def pwLogSingularGaugeInv (t : ℝ) : ℝ := Real.exp (-pwLogSingularGaugePotential t)

def pwLogSingularGain (t : ℝ) : ℝ := Real.exp (2 * pwLogSingularGaugePotential t)

theorem pwSingularReflectionGain_exp_eq (t : ℝ) :
    pwSingularReflectionGain (Real.exp t) = pwLogSingularGain t := by
  rw [pwSingularReflectionGain_eq (Real.exp_pos t)]
  have hinv : (Real.exp t)⁻¹ = Real.exp (-t) := (Real.exp_neg t).symm
  rw [hinv]
  simp only [pwLogSingularGain, pwLogSingularGaugePotential]
  rw [← Real.exp_add]
  congr 1
  rw [Real.sinh_eq]
  ring

theorem pwLogSingularGaugePotential_neg (t : ℝ) :
    pwLogSingularGaugePotential (-t) = -pwLogSingularGaugePotential t := by
  simp [pwLogSingularGaugePotential]
  ring

theorem pwLogSingularGain_neg (t : ℝ) :
    pwLogSingularGain (-t) = (pwLogSingularGain t)⁻¹ := by
  rw [pwLogSingularGain, pwLogSingularGain, pwLogSingularGaugePotential_neg]
  rw [show 2 * -pwLogSingularGaugePotential t = -(2 * pwLogSingularGaugePotential t) by ring]
  exact Real.exp_neg _

theorem pwLogSingularConnectionPotential_pos (t : ℝ) :
    0 < pwLogSingularConnectionPotential t := by
  rw [pwLogSingularConnectionPotential]
  linarith [Real.one_le_cosh t]

theorem hasDerivAt_pwLogSingularGaugePotential (t : ℝ) :
    HasDerivAt pwLogSingularGaugePotential (pwLogSingularConnectionPotential t) t := by
  have h := (Real.hasDerivAt_sinh t).sub ((hasDerivAt_id t).div_const 2)
  have hfun : pwLogSingularGaugePotential =
      fun u : ℝ => Real.sinh u - u / 2 := by
    funext u
    rfl
  rw [hfun]
  exact h

theorem hasDerivAt_pwLogSingularGauge (t : ℝ) :
    HasDerivAt pwLogSingularGauge
      (pwLogSingularConnectionPotential t * pwLogSingularGauge t) t := by
  have h := (Real.hasDerivAt_exp (pwLogSingularGaugePotential t)).comp t
    (hasDerivAt_pwLogSingularGaugePotential t)
  have hfun : pwLogSingularGauge =
      fun u : ℝ => Real.exp (pwLogSingularGaugePotential u) := by
    funext u
    rfl
  rw [hfun]
  exact h.congr_deriv (by ring)

theorem hasDerivAt_pwLogSingularGaugeInv (t : ℝ) :
    HasDerivAt pwLogSingularGaugeInv
      (-pwLogSingularConnectionPotential t * pwLogSingularGaugeInv t) t := by
  have hneg := (hasDerivAt_pwLogSingularGaugePotential t).neg
  have h := (Real.hasDerivAt_exp (-pwLogSingularGaugePotential t)).comp t hneg
  have hfun : pwLogSingularGaugeInv =
      fun u : ℝ => Real.exp (-pwLogSingularGaugePotential u) := by
    funext u
    rfl
  rw [hfun]
  exact h.congr_deriv (by ring)

theorem pwLogSingularGauge_mul_inv (t : ℝ) :
    pwLogSingularGauge t * pwLogSingularGaugeInv t = 1 := by
  rw [pwLogSingularGauge, pwLogSingularGaugeInv, ← Real.exp_add]
  rw [show pwLogSingularGaugePotential t + -pwLogSingularGaugePotential t = 0 by ring,
    Real.exp_zero]

theorem pwLogSingularGauge_pos (t : ℝ) : 0 < pwLogSingularGauge t := by
  exact Real.exp_pos _

theorem pwLogSingularGaugeInv_pos (t : ℝ) : 0 < pwLogSingularGaugeInv t := by
  exact Real.exp_pos _

theorem pwLogSingular_horizontal_plus_classification
    {f : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (pwLogSingularConnectionPotential t * f t) t) :
    ∃ c : ℝ, ∀ t, f t = c * pwLogSingularGauge t := by
  have hzero : ∀ t, HasDerivAt (fun u => f u * pwLogSingularGaugeInv u) 0 t := by
    intro t
    have h := (hf t).mul (hasDerivAt_pwLogSingularGaugeInv t)
    exact h.congr_deriv (by ring)
  refine ⟨f 0, fun t => ?_⟩
  have hconst := GaloisForLFunctions.HTGeometry.const_of_hasDerivAt_zero hzero t 0
  apply mul_right_cancel₀ (pwLogSingularGaugeInv_pos t).ne'
  rw [mul_assoc, pwLogSingularGauge_mul_inv, mul_one]
  simpa [pwLogSingularGaugeInv, pwLogSingularGaugePotential] using hconst

theorem pwLogSingular_horizontal_minus_classification
    {f : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (-pwLogSingularConnectionPotential t * f t) t) :
    ∃ c : ℝ, ∀ t, f t = c * pwLogSingularGaugeInv t := by
  have hzero : ∀ t, HasDerivAt (fun u => f u * pwLogSingularGauge u) 0 t := by
    intro t
    have h := (hf t).mul (hasDerivAt_pwLogSingularGauge t)
    exact h.congr_deriv (by ring)
  refine ⟨f 0, fun t => ?_⟩
  have hconst := GaloisForLFunctions.HTGeometry.const_of_hasDerivAt_zero hzero t 0
  apply mul_right_cancel₀ (pwLogSingularGauge_pos t).ne'
  rw [mul_assoc, mul_comm (pwLogSingularGaugeInv t),
    pwLogSingularGauge_mul_inv, mul_one]
  simpa [pwLogSingularGauge, pwLogSingularGaugePotential] using hconst

theorem pwLogSingularGaugePotential_ge_half {t : ℝ} (ht : 0 ≤ t) :
    t / 2 ≤ pwLogSingularGaugePotential t := by
  rw [pwLogSingularGaugePotential]
  linarith [HTGeometry.self_le_sinh_of_nonneg ht]

theorem pwLogSingularGaugePotential_le_half {t : ℝ} (ht : t ≤ 0) :
    pwLogSingularGaugePotential t ≤ t / 2 := by
  have hnonneg : 0 ≤ -t := by linarith
  have h := pwLogSingularGaugePotential_ge_half hnonneg
  rw [pwLogSingularGaugePotential_neg] at h
  linarith

theorem not_integrableOn_Iic_of_le {f : ℝ → ℝ} {a delta : ℝ} (hd : 0 < delta)
    (hf : ∀ x ∈ Iic a, delta ≤ f x) (hint : IntegrableOn f (Iic a) volume) : False := by
  have hconst : IntegrableOn (fun _ : ℝ => delta) (Iic a) volume := by
    refine Integrable.mono' hint aestronglyMeasurable_const ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    rw [Real.norm_eq_abs, abs_of_pos hd]
    exact hf x hx
  rw [integrableOn_const_iff] at hconst
  rcases hconst with h | h
  · have hz : delta = 0 := by simpa using h
    exact hd.ne' hz
  · rw [Real.volume_Iic] at h
    simp at h

theorem pwLogSingular_horizontal_plus_not_integrable
    {f : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (pwLogSingularConnectionPotential t * f t) t)
    (hL2 : Integrable (fun t => f t ^ (2 : ℕ))) :
    f = 0 := by
  rcases pwLogSingular_horizontal_plus_classification hf with ⟨c, hc⟩
  by_cases hc0 : c = 0
  · funext t
    simp [hc t, hc0]
  have hdelta : 0 < c ^ (2 : ℕ) := sq_pos_of_ne_zero hc0
  exfalso
  apply GaloisForLFunctions.HTGeometry.not_integrableOn_Ici_of_le hdelta
    (a := 0) (f := fun t => f t ^ (2 : ℕ))
  · intro u hu
    rw [hc]
    have hu0 : 0 ≤ u := hu
    have hphi : 0 ≤ pwLogSingularGaugePotential u := by
      have := pwLogSingularGaugePotential_ge_half hu0
      linarith
    have hg : 1 ≤ pwLogSingularGauge u := by
      rw [pwLogSingularGauge]
      exact Real.one_le_exp hphi
    have hgsq : 1 ≤ pwLogSingularGauge u ^ (2 : ℕ) := by nlinarith
    calc
      c ^ (2 : ℕ) ≤ c ^ (2 : ℕ) * pwLogSingularGauge u ^ (2 : ℕ) :=
        by simpa using mul_le_mul_of_nonneg_left hgsq (sq_nonneg c)
      _ = (c * pwLogSingularGauge u) ^ (2 : ℕ) := by ring
  · exact hL2.integrableOn

theorem pwLogSingular_horizontal_minus_not_integrable
    {f : ℝ → ℝ}
    (hf : ∀ t, HasDerivAt f (-pwLogSingularConnectionPotential t * f t) t)
    (hL2 : Integrable (fun t => f t ^ (2 : ℕ))) :
    f = 0 := by
  rcases pwLogSingular_horizontal_minus_classification hf with ⟨c, hc⟩
  by_cases hc0 : c = 0
  · funext t
    simp [hc t, hc0]
  have hdelta : 0 < c ^ (2 : ℕ) := sq_pos_of_ne_zero hc0
  exfalso
  apply not_integrableOn_Iic_of_le hdelta
    (a := 0) (f := fun t => f t ^ (2 : ℕ))
  · intro u hu
    rw [hc]
    have hu0 : u ≤ 0 := hu
    have hphi : 0 ≤ -pwLogSingularGaugePotential u := by
      have := pwLogSingularGaugePotential_le_half hu0
      linarith
    have hg : 1 ≤ pwLogSingularGaugeInv u := by
      rw [pwLogSingularGaugeInv]
      exact Real.one_le_exp hphi
    have hgsq : 1 ≤ pwLogSingularGaugeInv u ^ (2 : ℕ) := by nlinarith
    calc
      c ^ (2 : ℕ) ≤ c ^ (2 : ℕ) * pwLogSingularGaugeInv u ^ (2 : ℕ) :=
        by simpa using mul_le_mul_of_nonneg_left hgsq (sq_nonneg c)
      _ = (c * pwLogSingularGaugeInv u) ^ (2 : ℕ) := by ring
  · exact hL2.integrableOn

def PWLogReflectionUnitaryDensityLaw (w : ℝ → ℝ) : Prop :=
  ∀ t, w (-t) = pwLogSingularGain t ^ (2 : ℕ) * w t

def pwLogSingularDensityCore (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  pwLogSingularGain t * w t

theorem pwLogReflectionUnitaryDensityLaw_iff_even_core (w : ℝ → ℝ) :
    PWLogReflectionUnitaryDensityLaw w ↔ Function.Even (pwLogSingularDensityCore w) := by
  constructor
  · intro h t
    rw [pwLogSingularDensityCore, pwLogSingularDensityCore, pwLogSingularGain_neg, h]
    have hpos : pwLogSingularGain t ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  · intro h t
    have ht := h t
    rw [pwLogSingularDensityCore, pwLogSingularDensityCore, pwLogSingularGain_neg] at ht
    have hpos : pwLogSingularGain t ≠ 0 := (Real.exp_pos _).ne'
    apply (mul_left_cancel₀ (inv_ne_zero hpos))
    rw [ht]
    field_simp

theorem pwLogReflectionUnitaryDensity_classification (w : ℝ → ℝ) :
    ((∀ t, 0 < w t) ∧ PWLogReflectionUnitaryDensityLaw w) ↔
      ∃ h : ℝ → ℝ, (∀ t, 0 < h t) ∧ Function.Even h ∧
        ∀ t, w t = (pwLogSingularGain t)⁻¹ * h t := by
  constructor
  · rintro ⟨hwpos, hwlaw⟩
    refine ⟨pwLogSingularDensityCore w, ?_,
      (pwLogReflectionUnitaryDensityLaw_iff_even_core w).mp hwlaw, ?_⟩
    · intro t
      exact mul_pos (Real.exp_pos _) (hwpos t)
    · intro t
      rw [pwLogSingularDensityCore]
      symm
      have hgain : pwLogSingularGain t ≠ 0 := by
        rw [pwLogSingularGain]
        exact (Real.exp_pos _).ne'
      rw [← mul_assoc, inv_mul_cancel₀ hgain, one_mul]
  · rintro ⟨h, hhpos, hheven, hw⟩
    constructor
    · intro t
      rw [hw]
      exact mul_pos (inv_pos.mpr (Real.exp_pos _)) (hhpos t)
    · intro t
      rw [hw, hw, pwLogSingularGain_neg, hheven t]
      field_simp

def pwLogSingularWeightedReflection (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  pwLogSingularGain t * f (-t)

def pwLogWeightedEnergyDensity (w f : ℝ → ℝ) (t : ℝ) : ℝ :=
  w t * f t ^ (2 : ℕ)

theorem pwLogWeightedEnergyDensity_reflection_neg
    {w : ℝ → ℝ} (hw : PWLogReflectionUnitaryDensityLaw w)
    (f : ℝ → ℝ) (t : ℝ) :
    pwLogWeightedEnergyDensity w (pwLogSingularWeightedReflection f) (-t) =
      pwLogWeightedEnergyDensity w f t := by
  simp only [pwLogWeightedEnergyDensity, pwLogSingularWeightedReflection]
  rw [hw t, pwLogSingularGain_neg]
  simp only [neg_neg]
  have hgain : pwLogSingularGain t ≠ 0 := by
    rw [pwLogSingularGain]
    exact (Real.exp_pos _).ne'
  field_simp

theorem pwLogSingularWeightedReflection_integrable_energy_iff
    {w : ℝ → ℝ} (hw : PWLogReflectionUnitaryDensityLaw w)
    (f : ℝ → ℝ) :
    Integrable (pwLogWeightedEnergyDensity w (pwLogSingularWeightedReflection f)) ↔
      Integrable (pwLogWeightedEnergyDensity w f) := by
  have hcomp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_emb
    (measurableEmbedding_neg (α := ℝ))
    (g := pwLogWeightedEnergyDensity w (pwLogSingularWeightedReflection f))
  have hfun :
      pwLogWeightedEnergyDensity w (pwLogSingularWeightedReflection f) ∘ Neg.neg =
        pwLogWeightedEnergyDensity w f := by
    funext t
    exact pwLogWeightedEnergyDensity_reflection_neg hw f t
  rw [hfun] at hcomp
  exact hcomp.symm

theorem integral_pwLogWeightedEnergyDensity_reflection
    {w : ℝ → ℝ} (hw : PWLogReflectionUnitaryDensityLaw w)
    (f : ℝ → ℝ) :
    ∫ t, pwLogWeightedEnergyDensity w (pwLogSingularWeightedReflection f) t =
      ∫ t, pwLogWeightedEnergyDensity w f t := by
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    (measurableEmbedding_neg (α := ℝ))
    (pwLogWeightedEnergyDensity w (pwLogSingularWeightedReflection f))
  calc
    _ = ∫ t, pwLogWeightedEnergyDensity w (pwLogSingularWeightedReflection f) (-t) := hneg.symm
    _ = _ := by
      refine integral_congr_ae ?_
      filter_upwards with t
      exact pwLogWeightedEnergyDensity_reflection_neg hw f t

def PWSingularGaugeConnectionIndexNoGo : Prop :=
  (∀ f : ℝ → ℝ,
    (∀ t, HasDerivAt f (pwLogSingularConnectionPotential t * f t) t) →
    Integrable (fun t => f t ^ (2 : ℕ)) → f = 0) ∧
  (∀ f : ℝ → ℝ,
    (∀ t, HasDerivAt f (-pwLogSingularConnectionPotential t * f t) t) →
    Integrable (fun t => f t ^ (2 : ℕ)) → f = 0) ∧
  (∀ w : ℝ → ℝ,
    ((∀ t, 0 < w t) ∧ PWLogReflectionUnitaryDensityLaw w) ↔
      ∃ h : ℝ → ℝ, (∀ t, 0 < h t) ∧ Function.Even h ∧
        ∀ t, w t = (pwLogSingularGain t)⁻¹ * h t) ∧
  (∀ w : ℝ → ℝ, PWLogReflectionUnitaryDensityLaw w → ∀ f : ℝ → ℝ,
    Integrable (pwLogWeightedEnergyDensity w (pwLogSingularWeightedReflection f)) ↔
      Integrable (pwLogWeightedEnergyDensity w f)) ∧
  (∀ w : ℝ → ℝ, PWLogReflectionUnitaryDensityLaw w → ∀ f : ℝ → ℝ,
    ∫ t, pwLogWeightedEnergyDensity w (pwLogSingularWeightedReflection f) t =
      ∫ t, pwLogWeightedEnergyDensity w f t)

theorem pwSingularGauge_connectionIndex_noGo :
    PWSingularGaugeConnectionIndexNoGo := by
  exact ⟨fun f => pwLogSingular_horizontal_plus_not_integrable,
    fun f => pwLogSingular_horizontal_minus_not_integrable,
    pwLogReflectionUnitaryDensity_classification,
    fun _ hw f => pwLogSingularWeightedReflection_integrable_energy_iff hw f,
    fun _ hw f => integral_pwLogWeightedEnergyDensity_reflection hw f⟩

end

end RHTower
