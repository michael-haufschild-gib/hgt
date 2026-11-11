import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheAbscissaLawsOfAZeroConfiguration

/-!
# Additive functionals of the depths are mixtures of inner masses

A finite layer of off-line zeros is a finite family of depths `δ_i ∈ [0, D]` with weights `m_i`,
the multiplicities. An additive functional with profile `ψ` is `Σ m_i ψ(δ_i)`. Projection to
the line replaces every depth by `0`, so the functional drops by `Σ m_i (ψ(δ_i) − ψ(0))`.

Two functions of the level `a` describe the layer: the count `N(a) = Σ_{δ_i ≥ a} m_i` of the
zeros at depth at least `a`, and the inner mass `I(a) = Σ m_i (δ_i − a)₊`.

* `sum_profile_sub_eq_integral_count`: `Σ m_i (ψ(δ_i) − ψ(0)) = ∫₀^D ψ'(a) N(a) da`.
* `sum_profile_sub_eq_innerMass`:
  `Σ m_i (ψ(δ_i) − ψ(0)) = ψ'(0) I(0) + ∫₀^D ψ''(a) I(a) da`.
* `sum_profile_sub_nonneg`: a profile that increases with the depth drops under projection.
* `sum_profile_sub_eq_of_innerMass_eq`: two layers with the same inner mass at every level
  have the same drop of every additive functional.
* `rightZeros_profile_drop_eq_integral_count`: the first identity for the zeros of a
  configuration right of the critical line, when they are finitely many.

So an additive functional of the depths that decreases under projection is a positive mixture
of the counts, and every additive functional is a linear functional of the inner mass as a
function of the level: it carries no information beyond the inner masses.
-/

open MeasureTheory Set
open scoped Interval

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

variable {ι : Type*}

/-- The count of a layer at the level `a`: the total weight at depth at least `a`. -/
def layerCount (s : Finset ι) (m δ : ι → ℝ) (a : ℝ) : ℝ :=
  ∑ i ∈ s, m i * (if a ≤ δ i then 1 else 0)

/-- The inner mass of a layer at the level `a`: `Σ m_i (δ_i − a)₊`. -/
def layerInnerMass (s : Finset ι) (m δ : ι → ℝ) (a : ℝ) : ℝ :=
  ∑ i ∈ s, m i * max (δ i - a) 0

theorem layerCount_nonneg {s : Finset ι} {m δ : ι → ℝ} (hm : ∀ i ∈ s, 0 ≤ m i) (a : ℝ) :
    0 ≤ layerCount s m δ a :=
  Finset.sum_nonneg fun i hi => mul_nonneg (hm i hi) (by split_ifs <;> norm_num)

/-- Cutting an integrand off above `δ` cuts the integral off at `δ`. -/
theorem integral_mul_ite_le (f : ℝ → ℝ) {δ D : ℝ} (h0 : 0 ≤ δ) (hD : δ ≤ D) :
    ∫ a in (0 : ℝ)..D, f a * (if a ≤ δ then 1 else 0) = ∫ a in (0 : ℝ)..δ, f a := by
  rw [intervalIntegral.integral_of_le (h0.trans hD), intervalIntegral.integral_of_le h0]
  have hcongr : EqOn (fun a => f a * (if a ≤ δ then (1 : ℝ) else 0))
      ((Ioc (0 : ℝ) δ).indicator f) (Ioc (0 : ℝ) D) := by
    intro a ha
    simp only [Set.indicator, Set.mem_Ioc, ha.1, true_and]
    split_ifs <;> simp
  have hset : Ioc (0 : ℝ) D ∩ Ioc 0 δ = Ioc 0 δ :=
    Set.inter_eq_self_of_subset_right (Ioc_subset_Ioc_right hD)
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr, setIntegral_indicator measurableSet_Ioc,
    hset]

/-- **Additive functionals are mixtures of counts.** The drop of an additive functional with a
continuously differentiable profile is the integral of the derivative of the profile against
the count. -/
theorem sum_profile_sub_eq_integral_count (s : Finset ι) (m δ : ι → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hδ : ∀ i ∈ s, 0 ≤ δ i ∧ δ i ≤ D) {ψ ψ' : ℝ → ℝ}
    (hψ : ∀ a ∈ Icc (0 : ℝ) D, HasDerivAt ψ (ψ' a) a) (hψ' : ContinuousOn ψ' (Icc (0 : ℝ) D)) :
    ∑ i ∈ s, m i * (ψ (δ i) - ψ 0) = ∫ a in (0 : ℝ)..D, ψ' a * layerCount s m δ a := by
  have hψint : IntegrableOn ψ' (Ioc (0 : ℝ) D) :=
    hψ'.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hint : ∀ i ∈ s, IntervalIntegrable
      (fun a => m i * (ψ' a * (if a ≤ δ i then (1 : ℝ) else 0))) volume 0 D := by
    intro i _
    have hfun : (fun a => m i * (ψ' a * (if a ≤ δ i then (1 : ℝ) else 0))) =
        fun a => m i * (Set.Iic (δ i)).indicator ψ' a := by
      funext a
      simp only [Set.indicator, Set.mem_Iic]
      split_ifs <;> simp
    rw [hfun, intervalIntegrable_iff_integrableOn_Ioc_of_le hD]
    exact (hψint.indicator measurableSet_Iic).const_mul (m i)
  have hrw : (fun a => ψ' a * layerCount s m δ a) =
      fun a => ∑ i ∈ s, m i * (ψ' a * (if a ≤ δ i then (1 : ℝ) else 0)) := by
    funext a
    rw [layerCount, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hrw, intervalIntegral.integral_finsetSum hint]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨h0i, hDi⟩ := hδ i hi
  have hftc : ∫ a in (0 : ℝ)..δ i, ψ' a = ψ (δ i) - ψ 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a ha => hψ a ?_) ?_
    · rw [uIcc_of_le h0i] at ha
      exact ⟨ha.1, ha.2.trans hDi⟩
    · exact (hψ'.mono (Icc_subset_Icc_right hDi)).intervalIntegrable_of_Icc h0i
  rw [intervalIntegral.integral_const_mul, integral_mul_ite_le ψ' h0i hDi, hftc]

/-- **A profile increasing with the depth drops under projection.** -/
theorem sum_profile_sub_nonneg (s : Finset ι) (m δ : ι → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hm : ∀ i ∈ s, 0 ≤ m i) (hδ : ∀ i ∈ s, 0 ≤ δ i ∧ δ i ≤ D) {ψ ψ' : ℝ → ℝ}
    (hψ : ∀ a ∈ Icc (0 : ℝ) D, HasDerivAt ψ (ψ' a) a) (hψ' : ContinuousOn ψ' (Icc (0 : ℝ) D))
    (hpos : ∀ a ∈ Icc (0 : ℝ) D, 0 ≤ ψ' a) :
    0 ≤ ∑ i ∈ s, m i * (ψ (δ i) - ψ 0) := by
  rw [sum_profile_sub_eq_integral_count s m δ hD hδ hψ hψ']
  exact intervalIntegral.integral_nonneg hD fun a ha =>
    mul_nonneg (hpos a ha) (layerCount_nonneg hm a)

/-- **Additive functionals are linear in the inner mass.** For a twice continuously
differentiable profile the drop is `ψ'(0) I(0) + ∫₀^D ψ''(a) I(a) da`. -/
theorem sum_profile_sub_eq_innerMass (s : Finset ι) (m δ : ι → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hδ : ∀ i ∈ s, 0 ≤ δ i ∧ δ i ≤ D) {ψ ψ' ψ'' : ℝ → ℝ}
    (hψ : ∀ a ∈ Icc (0 : ℝ) D, HasDerivAt ψ (ψ' a) a)
    (hψ' : ∀ a ∈ Icc (0 : ℝ) D, HasDerivAt ψ' (ψ'' a) a)
    (hψ'' : ContinuousOn ψ'' (Icc (0 : ℝ) D)) :
    ∑ i ∈ s, m i * (ψ (δ i) - ψ 0) =
      ψ' 0 * layerInnerMass s m δ 0 + ∫ a in (0 : ℝ)..D, ψ'' a * layerInnerMass s m δ a := by
  have hint : ∀ i ∈ s, IntervalIntegrable
      (fun a => m i * (ψ'' a * max (δ i - a) 0)) volume 0 D := by
    intro i _
    refine ContinuousOn.intervalIntegrable_of_Icc hD ?_
    exact continuousOn_const.mul
      (hψ''.mul ((continuous_const.sub continuous_id).max continuous_const).continuousOn)
  have hrw : (fun a => ψ'' a * layerInnerMass s m δ a) =
      fun a => ∑ i ∈ s, m i * (ψ'' a * max (δ i - a) 0) := by
    funext a
    rw [layerInnerMass, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h0 : layerInnerMass s m δ 0 = ∑ i ∈ s, m i * δ i :=
    Finset.sum_congr rfl fun i hi => by rw [sub_zero, max_eq_left (hδ i hi).1]
  rw [hrw, intervalIntegral.integral_finsetSum hint, h0, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨h0i, hDi⟩ := hδ i hi
  have hsub : uIcc (0 : ℝ) (δ i) ⊆ Icc 0 D := by
    rw [uIcc_of_le h0i]
    exact Icc_subset_Icc_right hDi
  -- the positive part cuts the integral off at the depth
  have htrunc : ∫ a in (0 : ℝ)..D, ψ'' a * max (δ i - a) 0 =
      ∫ a in (0 : ℝ)..δ i, (δ i - a) * ψ'' a := by
    refine (intervalIntegral.integral_congr
      (g := fun a => (δ i - a) * ψ'' a * (if a ≤ δ i then 1 else 0)) fun a _ => ?_).trans
      (integral_mul_ite_le (fun a => (δ i - a) * ψ'' a) h0i hDi)
    show ψ'' a * max (δ i - a) 0 = (δ i - a) * ψ'' a * (if a ≤ δ i then 1 else 0)
    by_cases h : a ≤ δ i
    · rw [if_pos h, mul_one, max_eq_left (sub_nonneg.mpr h), mul_comm]
    · rw [if_neg h, mul_zero, max_eq_right (sub_nonpos.mpr (not_le.mp h).le), mul_zero]
  -- integration by parts against `δ − a`
  have hibp : ∫ a in (0 : ℝ)..δ i, (δ i - a) * ψ'' a = ψ (δ i) - ψ 0 - δ i * ψ' 0 := by
    have hv' : IntervalIntegrable ψ'' volume 0 (δ i) :=
      (hψ''.mono (Icc_subset_Icc_right hDi)).intervalIntegrable_of_Icc h0i
    have hψ'c : IntervalIntegrable ψ' volume 0 (δ i) :=
      ContinuousOn.intervalIntegrable_of_Icc h0i fun a ha =>
        (hψ' a ⟨ha.1, ha.2.trans hDi⟩).continuousAt.continuousWithinAt
    have h1 : ∫ a in (0 : ℝ)..δ i, (δ i - a) * ψ'' a =
        (δ i - δ i) * ψ' (δ i) - (δ i - 0) * ψ' 0 - ∫ a in (0 : ℝ)..δ i, (-1 : ℝ) * ψ' a :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun a => δ i - a)
        (u' := fun _ => (-1 : ℝ)) (v := ψ') (v' := ψ'')
        (fun x _ => (hasDerivAt_id x).const_sub (δ i)) (fun x hx => hψ' x (hsub hx))
        intervalIntegrable_const hv'
    have h2 : ∫ a in (0 : ℝ)..δ i, ψ' a = ψ (δ i) - ψ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hψ x (hsub hx)) hψ'c
    rw [h1, intervalIntegral.integral_const_mul, h2]
    ring
  rw [intervalIntegral.integral_const_mul, htrunc, hibp]
  ring

/-- **The inner masses determine every additive functional.** Two layers with the same inner
mass at every level have the same drop, for every twice continuously differentiable profile. -/
theorem sum_profile_sub_eq_of_innerMass_eq {κ : Type*} (s : Finset ι) (m δ : ι → ℝ)
    (t : Finset κ) (n ε : κ → ℝ) {D : ℝ} (hD : 0 ≤ D) (hδ : ∀ i ∈ s, 0 ≤ δ i ∧ δ i ≤ D)
    (hε : ∀ j ∈ t, 0 ≤ ε j ∧ ε j ≤ D)
    (hI : ∀ a ∈ Icc (0 : ℝ) D, layerInnerMass s m δ a = layerInnerMass t n ε a)
    {ψ ψ' ψ'' : ℝ → ℝ} (hψ : ∀ a ∈ Icc (0 : ℝ) D, HasDerivAt ψ (ψ' a) a)
    (hψ' : ∀ a ∈ Icc (0 : ℝ) D, HasDerivAt ψ' (ψ'' a) a)
    (hψ'' : ContinuousOn ψ'' (Icc (0 : ℝ) D)) :
    ∑ i ∈ s, m i * (ψ (δ i) - ψ 0) = ∑ j ∈ t, n j * (ψ (ε j) - ψ 0) := by
  rw [sum_profile_sub_eq_innerMass s m δ hD hδ hψ hψ' hψ'',
    sum_profile_sub_eq_innerMass t n ε hD hε hψ hψ' hψ'', hI 0 ⟨le_rfl, hD⟩]
  congr 1
  refine intervalIntegral.integral_congr fun a ha => ?_
  rw [uIcc_of_le hD] at ha
  show ψ'' a * layerInnerMass s m δ a = ψ'' a * layerInnerMass t n ε a
  rw [hI a ha]

/-! ### The zeros of a configuration right of the critical line -/

open Zeta23 ZeroConfigurationGeometry ZeroConfigurationGeometry.ConfigAbscissa

/-- **The drop of an additive functional of a configuration.** If a configuration has finitely
many zeros right of the critical line, the drop under projection of the additive functional
with profile `ψ` of the depth `Re ρ − ½` is the integral of `ψ'` against the count of the zeros
at depth at least `a`, over `0 ≤ a ≤ ½`. -/
theorem rightZeros_profile_drop_eq_integral_count (Z : ZeroConfig)
    (hfin : (rightOf Z 0).Finite) {ψ ψ' : ℝ → ℝ}
    (hψ : ∀ a ∈ Icc (0 : ℝ) (1 / 2), HasDerivAt ψ (ψ' a) a)
    (hψ' : ContinuousOn ψ' (Icc (0 : ℝ) (1 / 2))) :
    ∑ ρ ∈ hfin.toFinset, (Z.mult ρ : ℝ) * (ψ (ρ.re - 1 / 2) - ψ 0) =
      ∫ a in (0 : ℝ)..(1 / 2),
        ψ' a * layerCount hfin.toFinset (fun ρ => (Z.mult ρ : ℝ)) (fun ρ => ρ.re - 1 / 2) a := by
  refine sum_profile_sub_eq_integral_count _ _ _ (by norm_num) (fun ρ hρ => ?_) hψ hψ'
  have hmem : ρ ∈ rightOf Z 0 := hfin.mem_toFinset.mp hρ
  have h1 : 1 / 2 + 0 < ρ.re := hmem.2
  have h2 := (Z.strip ρ hmem.1).2
  exact ⟨by linarith only [h1], by linarith only [h2]⟩

end GaloisForLFunctions.FloorFreeArithmetic
