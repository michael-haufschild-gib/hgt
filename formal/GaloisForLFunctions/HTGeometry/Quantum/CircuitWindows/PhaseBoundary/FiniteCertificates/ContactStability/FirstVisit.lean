import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.ContactStability.PowerMargin
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.DistanceGap

/-! # One-sided power-law stability of the first physical gate return at every tolerance -/

open Set Filter Topology Metric Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.ContactStability
open BudgetComparisons PrecisionReturns
noncomputable section

/-- A local power lower bound at the end of a strictly positive interval
extends to the whole interval by compactness away from the endpoint. -/
private theorem interval_margin {f : ℝ → ℝ} (hf : Continuous f) {a v : ℝ} (hav : a<v)
    (hpos : ∀ t∈Ico a v, 0<f t) (he : f v=0) {m : ℕ} (hm : 0<m) {B : ℝ} (hB : 0<B)
    (hnear : ∀ᶠ t in 𝓝 v, f t≠0 → B*|t-v|^m≤|f t|) :
    ∃ c>0, ∀ t∈Icc a v, c*(v-t)^m≤f t := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let b := max a (v-r/2)
  have hab : a≤b := le_max_left ..
  have hbv : b<v := max_lt hav (by linarith only [hr])
  obtain ⟨u,hu,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc a b).Nonempty from ⟨a,le_rfl,hab⟩) hf.continuousOn
  have hu' := hpos u ⟨hu.1,hu.2.trans_lt hbv⟩
  let c := min B (f u/(v-a)^m)
  have hpow := pow_pos (sub_pos.mpr hav) m
  refine ⟨c,lt_min hB (div_pos hu' hpow),?_⟩
  intro t ht
  rcases ht.2.lt_or_eq with hlt|rfl
  · have hvt := sub_nonneg.mpr hlt.le
    by_cases htb : t≤b
    · calc
        c*(v-t)^m ≤ (f u/(v-a)^m)*(v-t)^m :=
          mul_le_mul_of_nonneg_right (min_le_right ..) (pow_nonneg hvt _)
        _ ≤ (f u/(v-a)^m)*(v-a)^m := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hvt (sub_le_sub_left ht.1 v) m) (div_nonneg hu'.le hpow.le)
        _ = f u := div_mul_cancel₀ _ hpow.ne'
        _ ≤ f t := hmin ⟨ht.1,htb⟩
    · have hb : t∈ball v r := by
        rw [Metric.mem_ball,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hlt.le)]
        linarith only [(le_max_right a (v-r/2)).trans (le_of_not_ge htb),hr]
      have hp := hpos t ⟨ht.1,hlt⟩
      have hh := hball hb hp.ne'
      rw [abs_sub_comm,abs_of_nonneg hvt,abs_of_pos hp] at hh
      exact (mul_le_mul_of_nonneg_right (min_le_left ..) (pow_nonneg hvt _)).trans hh
  · rw [sub_self,zero_pow hm.ne',mul_zero,he]

/-- Relaxing a fixed positive tolerance advances a genuine first return
by at most a power of the error change. A single exponent and constant
work for every larger tolerance, including at a tangential first contact. -/
theorem first_visit_power_law {N : ℕ} (H : selfAdjoint (Square (Bits N))) (a : ℝ) (s : ℕ)
    {e : ℝ} (he : 0<e) : ∃ m : ℕ, 0<m ∧ ∃ c>0, ∀ e'≥e,
      let v := firstVisit H a s e
      let w := firstVisit H a s e'
      w≤v ∧ c*(v-w)^m≤e'-e := by
  let v := firstVisit H a s e
  let d := orbitCircuitDistance H s
  have hw (e' : ℝ) (h : e≤e') : let w := firstVisit H a s e'
      a≤w ∧ w≤v ∧ d w≤e' := by
    intro w
    have V := firstVisit_isLeast H a s he
    have W := firstVisit_isLeast H a s (he.trans_le h)
    exact ⟨W.1.1,W.2 ⟨V.1.1,(hasProjectiveCircuitApproximation_iff_infDist ..).mpr
      (((hasProjectiveCircuitApproximation_iff_infDist ..).mp V.1.2).trans h)⟩,
      (hasProjectiveCircuitApproximation_iff_infDist ..).mp W.1.2⟩
  by_cases ha : e<d a
  · obtain ⟨hav,hv,hpre⟩ := firstVisit_left_contact H s a he ha
    let r : coefficients := ⟨fun _ => e,analyticOnNhd_const⟩
    let f (t : ℝ) := d t-e
    have hcf : Continuous f := (orbitCircuitDistance_lipschitz H s).continuous.sub continuous_const
    have hconst : IsAlgebraic coefficients (fun _ : ℝ => e) := isAlgebraic_algebraMap r
    obtain ⟨m,hm,B,hB,hnear⟩ := algebraic_power_margin hcf ((algebraic_distance H s).sub hconst) v
    have hpos (t : ℝ) (ht : t∈Ico a v) : 0<f t := by
      rcases ht.1.eq_or_lt with heq|hlt
      · subst t; exact sub_pos.mpr ha
      · exact sub_pos.mpr (hpre t ⟨hlt,ht.2⟩)
    obtain ⟨c,hc,hbound⟩ := interval_margin hcf hav hpos (sub_eq_zero.mpr hv) hm hB hnear
    refine ⟨m,hm,c,hc,?_⟩
    intro e' hh v' w
    obtain ⟨haw,hwv,hd⟩ := hw e' hh
    exact ⟨hwv,(hbound w ⟨haw,hwv⟩).trans (sub_le_sub_right hd e)⟩
  · have hcheap := (hasProjectiveCircuitApproximation_iff_infDist ..).mpr (le_of_not_gt ha)
    have hv : v=a := le_antisymm ((firstVisit_isLeast H a s he).2 ⟨le_rfl,hcheap⟩)
      (firstVisit_isLeast H a s he).1.1
    refine ⟨1,one_pos,1,one_pos,?_⟩
    intro e' h v' w
    obtain ⟨haw,hwv,_⟩ := hw e' h
    have hwe : w=v := le_antisymm hwv (hv.trans_le haw)
    refine ⟨hwv,?_⟩
    change 1*(v-w)^1≤e'-e
    rw [hwe,sub_self,pow_one,one_mul]
    exact sub_nonneg.mpr h

#print axioms first_visit_power_law
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.ContactStability
