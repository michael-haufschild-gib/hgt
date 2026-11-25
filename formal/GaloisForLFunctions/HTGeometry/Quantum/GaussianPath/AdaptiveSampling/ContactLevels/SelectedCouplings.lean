import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactLevels.FirstVisits
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactLevels.VisitParameter

/-! # Prescribing the tolerance before drawing the couplings -/

open Set Filter MeasureTheory Real Topology
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels
open PrescribedTimes PrecisionReturns ExactContacts.CoarseVisits
noncomputable section

/-- At almost every prescribed coarse tolerance, rescaling the coupling
vector by the time from a measurable offset to a first entry avoids any
specified null set. The conclusion allows all outside origins at once. -/
theorem selected_couplings_avoid (n s : ℕ) (b : (PrefixIndex n → ℝ) → ℝ) (hb : Measurable b)
    (S : Set (PrefixIndex n → ℝ)) (hS : volume S=0) :
    ∀ᵐ e : ℝ ∂volume, ∀ᵐ x ∂volume, 0 < e → ∀ a : ℝ,
      e < orbitCircuitDistance (prefixGenerator n x) s a →
      (firstVisit (prefixGenerator n x) a s e-b x) • x ∉ S := by
  let X := PrefixIndex n → ℝ
  obtain ⟨B,hsub,hB,hnull⟩ := exists_measurable_superset_of_null hS
  have hrow := ae_dilations (measure_eq_zero_iff_ae_notMem.mp hnull)
  have H (q : ℚ) : ∀ᵐ e : ℝ ∂volume, ∀ᵐ x ∂volume, 0 < e →
      e < pathGateDistance n s x q → (visitParameter n s q (x,e)-b x) • x ∉ B := by
    let v := visitParameter n s (q:ℝ)
    have hv := measurable_visitParameter n s (q:ℝ)
    have hd : Measurable (fun p : X × ℝ => pathGateDistance n s p.1 q) :=
      (continuous_distance_at_time n s (q:ℝ)).measurable.comp measurable_fst
    have hm : MeasurableSet {p : X × ℝ | 0 < p.2 → p.2 < pathGateDistance n s p.1 q →
        (v p-b p.1) • p.1 ∉ B} :=
      (measurableSet_lt measurable_const measurable_snd).imp
        ((measurableSet_lt measurable_snd hd).imp
          (hB.compl.preimage ((hv.sub (hb.comp measurable_fst)).smul measurable_fst)))
    apply (Measure.ae_ae_comm (μ:=volume) (ν:=volume) hm).mp
    filter_upwards [hrow] with x hx
    let Hx := prefixGenerator n x
    filter_upwards [ae_contact_transfer hx (orbitCircuitDistance_lipschitz Hx s) (b x)] with e he hpos hout
    have hfit := firstVisit_distance Hx (q:ℝ) s hpos hout
    simpa only [v,visitParameter,if_pos hpos] using he _ hfit
  filter_upwards [ae_all_iff.mpr H] with e he
  filter_upwards [ae_all_iff.mpr he] with x hx hpos a hout
  obtain ⟨q,hq,hv⟩ := rational_visit_origin (prefixGenerator n x) a s hpos hout
  have h := hx q hpos hq
  simp only [visitParameter,if_pos hpos,hv] at h
  exact fun hh => h (hsub hh)

#print axioms selected_couplings_avoid
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactLevels
