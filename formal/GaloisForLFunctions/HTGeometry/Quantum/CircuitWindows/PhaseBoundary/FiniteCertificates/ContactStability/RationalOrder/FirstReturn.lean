import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.ContactStability.RationalOrder.PowerLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.DistanceGap

/-! # Direct and inverse leading powers at the first physical circuit contact -/

open Set Filter Topology Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.ContactStability.RationalOrder
open BudgetComparisons PrecisionReturns
noncomputable section

/-- Just above the prescribed tolerance, first contacts lie strictly before
the original date. On each shorter closed record the distance has a strictly
positive margin above the original tolerance. -/
theorem relaxed_dates {N : ℕ} (H : selfAdjoint (Square (Bits N))) (s : ℕ) (a : ℝ)
    {e : ℝ} (he : 0<e) (hout : e<orbitCircuitDistance H s a) :
    let w := firstVisit H a s
    Tendsto w (𝓝[>] e) (𝓝[<] (w e)) ∧ ∀ᶠ u in 𝓝[>] e, orbitCircuitDistance H s (w u)=u := by
  intro w
  let d := orbitCircuitDistance H s
  obtain ⟨hav,hv,hstrict⟩ := firstVisit_left_contact H s a he hout
  have band : ∀ᶠ u in 𝓝[>] e, e<u ∧ u<d a :=
    self_mem_nhdsWithin.and (nhdsWithin_le_nhds (gt_mem_nhds hout))
  have hdates : ∀ᶠ u in 𝓝[>] e, a≤w u ∧ w u<w e ∧ d (w u)=u := by
    filter_upwards [band] with u hu
    have hwu := firstVisit_isLeast H a s (he.trans hu.1)
    have hcontact := (firstVisit_left_contact H s a (he.trans hu.1) hu.2).2.1
    have hle := hwu.2 ⟨hav.le,(hasProjectiveCircuitApproximation_iff_infDist ..).mpr
      (hv.le.trans hu.1.le)⟩
    exact ⟨hwu.1.1,lt_of_le_of_ne hle (fun h => hu.1.ne
      (hv.symm.trans ((congrArg d h).symm.trans hcontact))),hcontact⟩
  refine ⟨tendsto_nhdsWithin_iff.mpr ⟨tendsto_order.mpr ⟨?_,?_⟩,
    hdates.mono fun _ h => h.2.1⟩,hdates.mono fun _ h => h.2.2⟩
  · intro t ht
    by_cases hta : t<a
    · exact hdates.mono fun _ h => hta.trans_le h.1
    have hat := le_of_not_gt hta
    obtain ⟨r,hr,hmin⟩ := isCompact_Icc.exists_isMinOn
      (show (Icc a t).Nonempty from ⟨a,le_rfl,hat⟩) (orbitCircuitDistance_lipschitz H s).continuous.continuousOn
    have her : e<d r := hr.1.eq_or_lt.elim (fun h => h ▸ hout)
      (fun h => hstrict r ⟨h,hr.2.trans_lt ht⟩)
    filter_upwards [hdates,nhdsWithin_le_nhds (gt_mem_nhds her)] with u hu hsmall
    exact lt_of_not_ge fun hle => hsmall.not_ge ((hmin ⟨hu.1,hle⟩).trans_eq hu.2.2)
  · intro t ht
    exact hdates.mono fun _ h => h.2.1.trans ht

/-- At every genuine first contact, the distance and the advance of its
date under relaxed error have reciprocal rational leading orders.
Lipschitz continuity makes the distance order at least one. -/
theorem first_return_contact_order {N : ℕ} (H : selfAdjoint (Square (Bits N))) (s : ℕ) (a : ℝ)
    {e : ℝ} (he : 0<e) (hout : e<orbitCircuitDistance H s a) :
    let d := orbitCircuitDistance H s
    let w := firstVisit H a s
    let v := w e
    ∃ q p : ℕ, 0 < q ∧ q ≤ p ∧ ∃ c>0,
      Tendsto (fun t => (d t-e)^q/(v-t)^p) (𝓝[<] v) (𝓝 c) ∧
      Tendsto (fun u => (v-w u)^p/(u-e)^q) (𝓝[>] e) (𝓝 c⁻¹) := by
  intro d w v
  obtain ⟨hav,hv,hpre⟩ := firstVisit_left_contact H s a he hout
  let f (t : ℝ) := d t-e
  let r : coefficients := ⟨fun _ => e,analyticOnNhd_const⟩
  have hconst : IsAlgebraic coefficients (fun _ : ℝ => e) := isAlgebraic_algebraMap r
  have hpos : ∀ᶠ t in 𝓝[<] v, 0<f t := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (lt_mem_nhds hav)] with t htv hat
    exact sub_pos.mpr (hpre t ⟨hat,htv⟩)
  obtain ⟨q,p,hq,hp,c,hc,hlim⟩ := algebraic_contact_order
    ((orbitCircuitDistance_lipschitz H s).continuous.sub continuous_const)
    ((algebraic_distance H s).sub hconst) v (sub_eq_zero.mpr hv) hpos
  have hqp : q ≤ p := by
    rw [←one_mul q]
    apply order_ge_of_power_bound hc hlim (hpos.mono fun _ ht => ht.le) (K:=‖(H : Square (Bits N))‖)
    filter_upwards [hpos,self_mem_nhdsWithin] with t ht htv
    have hL := (orbitCircuitDistance_lipschitz H s).dist_le_mul t v
    rw [Real.dist_eq,Real.dist_eq,hv,abs_of_pos ht,abs_sub_comm t v,abs_of_pos (sub_pos.mpr htv)] at hL
    simpa only [pow_one] using hL
  obtain ⟨hw,hd⟩ := relaxed_dates H s a he hout
  refine ⟨q,p,hq,hqp,c,hc,hlim,((hlim.comp hw).inv₀ hc.ne').congr' ?_⟩
  filter_upwards [hd] with u hu
  change ((d (w u)-e)^q/(v-w u)^p)⁻¹=_
  rw [hu,inv_div]

#print axioms first_return_contact_order
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.ContactStability.RationalOrder
