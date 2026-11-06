import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheAnchorFlow
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilChainIsOneScalarFlow
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilTracesHaveTheirSoftKick
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheGreenCornerReadsThePotential

/-!
# The restoring bound of the actual Weil chain

The chain has `L = artanh r`, and in integrated form `L(y) − L(x) = Ψ(y) − Ψ(x) − ∫_x^y sinh 2L`, with no regularity of `Ψ`. The restoring force needs no derivative of `Ψ`.

**Theorem** (`abs_artanh_anchorReflection_le_osc`). On a precontact interval, with `|Ψ(z) − Ψ(c)| ≤ ω` on `[c, x]`,

`|L(x)| ≤ artanh e^{−2(x−c)} + 2ω`.

The bound has no initial value, no inverse of a lower eigenvalue, no derivative of `Ψ`, and no integrability of `q`: the a priori estimate for the actual chain is a bound by the oscillation of the canonical potential over any window of aperture. It replaces `∫|q|` of the bound for smooth
potentials by the oscillation, and so applies through the soft kicks. Contact needs the potential to oscillate without bound over a shrinking window.
-/

open Set Filter Topology MeasureTheory

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
open GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
open GaloisForLFunctions.CanonicalSystemOfTheWindowTower

noncomputable section

/-- **The restoring bound in integrated form.** If `v′ = −sinh 2(v + e)` with `|e| ≤ ω`, then `|v + e|` at `x` is at most `artanh e^{−2(x−c)} + 2ω`. -/
theorem abs_le_of_integrated_flow {v e : ℝ → ℝ} {c x ω : ℝ} (hcx : c < x)
    (hv : ∀ z ∈ Icc c x, HasDerivAt v (-Real.sinh (2 * (v z + e z))) z)
    (he : ∀ z ∈ Icc c x, |e z| ≤ ω) :
    |v x + e x| ≤ coolingBound (x - c) + 2 * ω := by
  have hx := he x (right_mem_Icc.mpr hcx.le)
  have hx' := abs_le.mp hx
  have hup : v x - ω ≤ coolingBound (x - c) := by
    refine le_coolingBound_of_tanh_le (by linarith) ?_
    refine tanh_le_exp_of_deriv_le (y := fun z => v z - ω)
      (D := fun z => -Real.sinh (2 * (v z + e z))) hcx.le
      (fun z hz => (hv z hz).sub_const ω) fun z hz hy => ?_
    have h1 := abs_le.mp (he z hz)
    have h2 : 2 * (v z - ω) ≤ 2 * (v z + e z) := by linarith [h1.1]
    have h3 := Real.sinh_le_sinh.mpr h2
    linarith
  have hlo : -v x - ω ≤ coolingBound (x - c) := by
    refine le_coolingBound_of_tanh_le (by linarith) ?_
    refine tanh_le_exp_of_deriv_le (y := fun z => -v z - ω)
      (D := fun z => Real.sinh (2 * (v z + e z))) hcx.le
      (fun z hz => by simpa using ((hv z hz).neg).sub_const ω) fun z hz hy => ?_
    have h1 := abs_le.mp (he z hz)
    have h2 : 2 * (v z + e z) ≤ -(2 * (-v z - ω)) := by linarith [h1.2]
    have h3 := Real.sinh_le_sinh.mpr h2
    rw [Real.sinh_neg] at h3
    linarith
  rw [abs_le]
  constructor <;> linarith [hx'.1, hx'.2]

/-- The drift is continuous on the precontact set. -/
theorem continuousAt_precontactCanonicalDrift {a : ℝ} (ha : a ∈ precontactSet) :
    ContinuousAt precontactCanonicalDrift a := by
  have hr : ContinuousAt anchorReflection a := continuousAt_anchorReflection (toPrecontact ha)
  have hmem := anchorReflection_mem ha
  have hne : 1 - anchorReflection a ^ 2 ≠ 0 := by
    have := abs_lt.mpr ⟨hmem.1, hmem.2⟩
    have h2 := (sq_lt_one_iff_abs_lt_one _).mpr this
    linarith
  have hc : ContinuousAt (fun z => 2 * anchorReflection z / (1 - anchorReflection z ^ 2)) a :=
    (continuousAt_const.mul hr).div (continuousAt_const.sub (hr.pow 2)) hne
  refine hc.congr ?_
  filter_upwards [isOpen_precontactSet.mem_nhds ha] with z hz
  exact (precontactCanonicalDrift_eq hz).symm

/-- **The restoring bound of the actual chain.** -/
theorem abs_artanh_anchorReflection_le_osc {l h base c x ω : ℝ} (hs : Icc l h ⊆ precontactSet)
    (hb : base ∈ Icc l h) (hc : c ∈ Icc l h) (hx : x ∈ Icc l h) (hcx : c < x)
    (hω : ∀ z ∈ Icc c x, |canonicalPotential base z - canonicalPotential base c| ≤ ω) :
    |Real.artanh (anchorReflection x)| ≤ coolingBound (x - c) + 2 * ω := by
  have hsub : Icc c x ⊆ Icc l h := Icc_subset_Icc hc.1 hx.2
  set v : ℝ → ℝ := fun z => Real.artanh (anchorReflection c) - ∫ t in c..z, precontactCanonicalDrift t with hvd
  set e : ℝ → ℝ := fun z => canonicalPotential base z - canonicalPotential base c with hed
  have hL : ∀ z ∈ Icc c x, v z + e z = Real.artanh (anchorReflection z) := fun z hz => by
    have := artanh_anchorReflection_sub hs hb hc (hsub hz)
    simp only [hvd, hed]
    linarith
  have hv : ∀ z ∈ Icc c x, HasDerivAt v (-Real.sinh (2 * (v z + e z))) z := fun z hz => by
    have hzs : z ∈ precontactSet := hs (hsub hz)
    have hcont := continuousAt_precontactCanonicalDrift hzs
    have hint : IntervalIntegrable precontactCanonicalDrift volume c z :=
      intervalIntegrable_precontactCanonicalDrift hz.1 (Icc_subset_Icc_right hz.2 |>.trans (hsub.trans hs))
    have hmeas : StronglyMeasurableAtFilter precontactCanonicalDrift (𝓝 z) := by
      have hco : ContinuousOn precontactCanonicalDrift precontactSet := fun a ha =>
        (continuousAt_precontactCanonicalDrift ha).continuousWithinAt
      exact hco.stronglyMeasurableAtFilter isOpen_precontactSet z hzs
    have h1 := intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
    have h2 := h1.const_sub (Real.artanh (anchorReflection c))
    rw [hL z hz, ← precontactCanonicalDrift_eq_sinh hzs]
    exact h2
  have hB := abs_le_of_integrated_flow hcx hv hω
  rwa [hL x (right_mem_Icc.mpr hcx.le)] at hB

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
