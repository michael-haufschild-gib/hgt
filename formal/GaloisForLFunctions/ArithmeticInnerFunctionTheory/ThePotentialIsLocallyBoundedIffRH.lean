import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheRestoringBoundOfTheActualChain
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilTracesAreAbsolutelyContinuous

/-!
# RH is local boundedness of the canonical potential

Before contact the Weil chain is one scalar flow: with `r` the anchor reflection, `L = artanh r`
and `Ψ = ½ log H₁`, one has `L(y) − L(x) = Ψ(y) − Ψ(x) − ∫_x^y sinh 2L`, the anchor mass is
`cosh 2L`, and `1/(1−r²) = (cosh 2L + 1)/2`. Contact is `∫ dx/(1−r²) = ∞`, so a bounded angle `L`
excludes contact. The restoring bound `|L(x)| ≤ artanh e^{−2(x−c)} + 2 osc_{[c,x]} Ψ` bounds `L` by
the oscillation of `Ψ`, with no initial value and no regularity of `Ψ`.

* `riemannHypothesis_or_anchorAngle_unbounded`: off RH, `L` is unbounded above every base.
* `riemannHypothesis_iff_anchorAngle_locallyBounded`: RH iff `L` is bounded on every bounded
  precontact interval above a base.
* `riemannHypothesis_iff_canonicalPotential_locallyBounded`: RH iff the same holds for `Ψ`.

So the whole window tower is one local boundedness statement for one real function.
-/

open Set Filter Topology MeasureTheory
open scoped Interval

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact
open GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
open GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower SquareRootThreshold WindowVisibilityLaw Zeta23

noncomputable section

/-- The cooling bound decreases in the elapsed aperture. -/
theorem coolingBound_le_coolingBound {h h' : ℝ} (hh : 0 < h) (hle : h ≤ h') :
    coolingBound h' ≤ coolingBound h := by
  have h1 : Real.exp (-2 * h) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h2 : -1 < Real.exp (-2 * h') := by linarith [Real.exp_pos (-2 * h')]
  exact Real.artanh_le_artanh h2 h1 (Real.exp_le_exp.mpr (by linarith))

/-- A precontact base and a point between it and a precontact point span a precontact interval. -/
private theorem Icc_subset_precontactSet_of_mem {b x : ℝ} (hb : b ∈ precontactSet)
    (hx : x ∈ precontactSet) : Icc b x ⊆ precontactSet := fun _ hy =>
  ⟨hb.1.trans_le hy.1, (EReal.coe_le_coe_iff.mpr hy.2).trans_lt hx.2⟩

/-- **Off RH the angle is unbounded above every base.** At finite contact `∫ dx/(1−r²) = ∞`, and
`1/(1−r²) = (cosh 2L + 1)/2`, so `L = artanh r` cannot stay bounded up to contact. -/
theorem riemannHypothesis_or_anchorAngle_unbounded :
    RiemannHypothesis ∨ ∃ c : ℝ, (c : EReal) = onsetAperture zetaZeroConfig ∧
      ∀ (base : PrecontactAperture) (Λ : ℝ), ∃ x ∈ precontactSet, base.1.1 ≤ x ∧
        Λ < |Real.artanh (anchorReflection x)| := by
  rcases riemannHypothesis_or_integral_reflection_unbounded with hRH | ⟨a, ha, hu⟩
  · exact Or.inl hRH
  refine Or.inr ⟨a.1, ha, fun base Λ => ?_⟩
  by_contra! hΛ
  have hbp : base.1.1 ∈ precontactSet := ⟨base.1.2, base.2⟩
  set K : ℝ := (Real.cosh (2 * Λ) + 1) / 2 with hK
  obtain ⟨b, hbb, hlt⟩ := hu base (K * (a.1 - base.1.1))
  have hbp' : b.1.1 ∈ precontactSet := ⟨b.1.2, b.2⟩
  have hba : b.1.1 < a.1 := EReal.coe_lt_coe_iff.mp (b.2.trans_eq ha.symm)
  have hs := Icc_subset_precontactSet_of_mem hbp hbp'
  have hpt : ∀ x ∈ Ι base.1.1 b.1.1, ‖1 / (1 - anchorReflection x ^ 2)‖ ≤ K := fun x hx => by
    rw [uIoc_of_le hbb] at hx
    have hxp : x ∈ precontactSet := hs ⟨hx.1.le, hx.2⟩
    have hL := hΛ x hxp hx.1.le
    have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans hL
    have hpos : 0 < 1 / (1 - anchorReflection x ^ 2) := by
      rw [one_div_one_sub_sq_eq hxp, anchorMassRatio_eq_cosh hxp]
      have := Real.cosh_pos (2 * Real.artanh (anchorReflection x))
      linarith
    rw [Real.norm_of_nonneg hpos.le, one_div_one_sub_sq_eq hxp, anchorMassRatio_eq_cosh hxp, hK]
    have hc : Real.cosh (2 * Real.artanh (anchorReflection x)) ≤ Real.cosh (2 * Λ) := by
      rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_two, abs_of_nonneg hΛ0]
      linarith only [hL]
    linarith only [hc]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (sub_nonneg.mpr hbb)] at hnorm
  have hK0 : 0 ≤ K := by
    rw [hK]
    have := Real.cosh_pos (2 * Λ)
    linarith
  have hle : K * (b.1.1 - base.1.1) ≤ K * (a.1 - base.1.1) :=
    mul_le_mul_of_nonneg_left (by linarith only [hba]) hK0
  have := (Real.le_norm_self _).trans hnorm
  linarith only [this, hle, hlt]

/-- **RH is local boundedness of the angle** `L = artanh r` above any precontact base. -/
theorem riemannHypothesis_iff_anchorAngle_locallyBounded (base : PrecontactAperture) :
    RiemannHypothesis ↔ ∀ c : ℝ, ∃ Λ : ℝ, ∀ x ∈ precontactSet, base.1.1 ≤ x → x ≤ c →
      |Real.artanh (anchorReflection x)| ≤ Λ := by
  constructor
  · intro hRH c
    have htop := riemannHypothesis_iff_onsetAperture_zeta_eq_top.mp hRH
    rcases lt_or_ge c base.1.1 with hc | hc
    · exact ⟨0, fun x _ hx hxc => absurd (hx.trans hxc) (not_le.mpr hc)⟩
    have hcp : c ∈ precontactSet := ⟨base.1.2.trans_le hc, by rw [htop]; exact EReal.coe_lt_top c⟩
    have hs := Icc_subset_precontactSet_of_mem ⟨base.1.2, base.2⟩ hcp
    have hco : ContinuousOn (fun x => Real.artanh (anchorReflection x)) (Icc base.1.1 c) :=
      fun x hx => (continuousAt_artanh_anchorReflection (toPrecontact (hs hx))).continuousWithinAt
    obtain ⟨Λ, hΛ⟩ := isCompact_Icc.exists_bound_of_continuousOn hco
    exact ⟨Λ, fun x _ hx hxc => by simpa using hΛ x ⟨hx, hxc⟩⟩
  · intro h
    rcases riemannHypothesis_or_anchorAngle_unbounded with hRH | ⟨c, hc, hu⟩
    · exact hRH
    obtain ⟨Λ, hΛ⟩ := h c
    obtain ⟨x, hxp, hbx, hlt⟩ := hu base Λ
    have hxc : x < c := EReal.coe_lt_coe_iff.mp (hxp.2.trans_eq hc.symm)
    exact absurd (hΛ x hxp hbx hxc.le) (not_le.mpr hlt)

/-- **RH is local boundedness of the canonical potential.** For every precontact base, RH holds
iff `Ψ = ½ log H₁` is bounded on every bounded precontact interval above the base. Off RH the
restoring bound turns a bound `|Ψ| ≤ M` below contact into `|L| ≤ artanh e^{−2(x−m)} + 4M` past the
midpoint `m` of the base and the contact, which the unbounded angle forbids. -/
theorem riemannHypothesis_iff_canonicalPotential_locallyBounded (base : PrecontactAperture) :
    RiemannHypothesis ↔ ∀ c : ℝ, ∃ M : ℝ, ∀ x ∈ precontactSet, base.1.1 ≤ x → x ≤ c →
      |canonicalPotential base.1.1 x| ≤ M := by
  have hbp : base.1.1 ∈ precontactSet := ⟨base.1.2, base.2⟩
  constructor
  · intro hRH c
    have htop := riemannHypothesis_iff_onsetAperture_zeta_eq_top.mp hRH
    rcases lt_or_ge c base.1.1 with hc | hc
    · exact ⟨0, fun x _ hx hxc => absurd (hx.trans hxc) (not_le.mpr hc)⟩
    let a₂ : PrecontactAperture := ⟨⟨c, base.1.2.trans_le hc⟩, (EReal.coe_lt_top c).trans_eq htop.symm⟩
    have hco := (absolutelyContinuousOnInterval_canonicalPotential hbp (a₁ := base) (a₂ := a₂)
      hc).continuousOn
    rw [uIcc_of_le hc] at hco
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hco
    exact ⟨M, fun x _ hx hxc => by simpa using hM x ⟨hx, hxc⟩⟩
  · intro h
    rcases riemannHypothesis_or_anchorAngle_unbounded with hRH | ⟨c, hc, hu⟩
    · exact hRH
    have hbc : base.1.1 < c := EReal.coe_lt_coe_iff.mp (base.2.trans_eq hc.symm)
    obtain ⟨M, hM⟩ := h c
    set m : ℝ := (base.1.1 + c) / 2 with hm
    have hbm : base.1.1 < m := by rw [hm]; linarith only [hbc]
    have hmc : m < c := by rw [hm]; linarith only [hbc]
    let mA : PrecontactAperture := ⟨⟨m, base.1.2.trans hbm⟩, (EReal.coe_lt_coe_iff.mpr hmc).trans_eq hc⟩
    obtain ⟨x, hxp, hmx, hlt⟩ := hu mA (coolingBound (m - base.1.1) + 2 * (2 * M))
    have hxc : x < c := EReal.coe_lt_coe_iff.mp (hxp.2.trans_eq hc.symm)
    have hbx : base.1.1 < x := hbm.trans_le hmx
    have hs := Icc_subset_precontactSet_of_mem hbp hxp
    have hω : ∀ z ∈ Icc base.1.1 x,
        |canonicalPotential base.1.1 z - canonicalPotential base.1.1 base.1.1| ≤ 2 * M := by
      intro z hz
      have h1 := hM z (hs hz) hz.1 (hz.2.trans hxc.le)
      have h2 := hM base.1.1 hbp le_rfl hbc.le
      have := abs_sub (canonicalPotential base.1.1 z) (canonicalPotential base.1.1 base.1.1)
      linarith only [this, h1, h2]
    have hB := abs_artanh_anchorReflection_le_osc hs (left_mem_Icc.mpr hbx.le)
      (left_mem_Icc.mpr hbx.le) (right_mem_Icc.mpr hbx.le) hbx hω
    have hcool := coolingBound_le_coolingBound (sub_pos.mpr hbm) (sub_le_sub_right hmx base.1.1)
    linarith only [hB, hcool, hlt]

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
