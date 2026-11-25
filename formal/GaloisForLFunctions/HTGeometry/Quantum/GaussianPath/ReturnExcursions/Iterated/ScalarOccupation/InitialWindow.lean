import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Iterated.Timeline
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.BudgetOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # Scalar residence in each rise is bounded by one initial occupation -/

open Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated.ScalarOccupation
open PrecisionReturns (firstVisit firstVisit_isLeast)
open SharpOccupation (visitSet)
noncomputable section

/-- Scalar dates in a rise translate, from the earliest scalar anchor,
to scalar fits at doubled error in the initial window. A harder lag
cannot fit inside the remaining part of the rise after the anchor. -/
theorem rise_mass {N : ℕ} (H : selfAdjoint (Reg N)) {P : ℕ} {r h u : ℝ} (hu : 0≤u)
    (hhard : 17/80<orbitCircuitDistance H P u)
    (hpre : ∀ t∈Icc r h, orbitCircuitDistance H P t≤9/80) :
    volume.real (visitSet H 0 (1/10) ∩ Ico r h) ≤
      volume.real (visitSet H 0 (1/5) ∩ Icc 0 u) := by
  let F := visitSet H 0 (1/5) ∩ Icc 0 u
  let p := firstVisit H r 0 (1/10)
  have hp := firstVisit_isLeast H r 0 (by norm_num : (0:ℝ)<1/10)
  have hclosed : IsClosed (visitSet H 0 (1/5)) := by
    change IsClosed {t | HasProjectiveCircuitApproximation N (1/5) 0 (unitaryEvolution H.val t)}
    simp only [hasProjectiveCircuitApproximation_iff_infDist]
    exact isClosed_le (orbitCircuitDistance_lipschitz H 0).continuous continuous_const
  have hm : MeasurableSet F := hclosed.measurableSet.inter measurableSet_Icc
  have hmp := measurePreserving_add_right volume (-p)
  rw [← hmp.measureReal_preimage (s:=F) hm.nullMeasurableSet]
  apply measureReal_mono _ (by
    rw [hmp.measure_preimage hm.nullMeasurableSet]
    exact measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  intro t ht
  obtain ⟨hfit,hrt,hth⟩ := ht
  have hpt : p≤t := hp.2 ⟨hrt,hfit⟩
  have hneg := HasProjectiveCircuitApproximation.neg_time H hp.1.2
  have hdiff := affordable_add_time H hfit hneg
  have htu : t-p<u := by
    by_contra! hlag
    have hpu : p+u∈Icc r h := ⟨hp.1.1.trans (le_add_of_nonneg_right hu),by linarith only [hlag,hth]⟩
    have hinc := (hasProjectiveCircuitApproximation_iff_infDist ..).mpr (hpre _ hpu)
    have hc := affordable_add_time H hinc hneg
    change HasProjectiveCircuitApproximation N (9/80+1/10) (P+0) (unitaryEvolution H.val ((p+u)+ -p)) at hc
    rw [show p+u+ -p=u by ring,Nat.add_zero,show (9/80+1/10:ℝ)=17/80 by norm_num] at hc
    exact hhard.not_ge ((hasProjectiveCircuitApproximation_iff_infDist ..).mp hc)
  change t+ -p∈F
  refine ⟨?_,by linarith only [hpt],by linarith only [htu]⟩
  change HasProjectiveCircuitApproximation N (1/5) 0 (unitaryEvolution H.val (t+ -p))
  exact (show (1/10+1/10:ℝ)=1/5 by norm_num) ▸ hdiff

/-- Adding the disjoint cycles charges all scalar occupation to one
copy of the initial-window mass per cycle. A terminal date has zero mass. -/
theorem scalar_record_charge {N : ℕ} (H : selfAdjoint (Reg N)) (P : ℕ) (v σ : ℕ → ℝ)
    (hmono : Monotone v) (hpre : ∀ i t, t∈Icc (v i) (σ i) → orbitCircuitDistance H P t≤9/80)
    (hpost : ∀ i t, v i≤t → t<v (i+1) → t∈visitSet H 0 (1/10) → t<σ i)
    {u : ℝ} (hu : 0≤u) (hhard : 17/80<orbitCircuitDistance H P u) (n : ℕ) :
    volume.real (visitSet H 0 (1/10) ∩ Icc (v 0) (v n)) ≤
      (n:ℝ)*volume.real (visitSet H 0 (1/5) ∩ Icc 0 u) := by
  let A := visitSet H 0 (1/10)
  let M := volume.real (visitSet H 0 (1/5) ∩ Icc 0 u)
  have step (i : ℕ) : volume.real (A ∩ Ico (v i) (v (i+1)))≤M := by
    apply (measureReal_mono _ (measure_ne_top_of_subset inter_subset_right measure_Ico_lt_top.ne)).trans
      (rise_mass H hu hhard (hpre i))
    rintro t ⟨ht,hlo,hhi⟩
    exact ⟨ht,hlo,hpost i t hlo hhi ht⟩
  have hcoe : A ∩ Ico (v 0) (v n) =ᵐ[volume] A ∩ Icc (v 0) (v n) := by
    filter_upwards [Ico_ae_eq_Icc (μ:=volume) (a:=v 0) (b:=v n)] with t ht
    exact propext (and_congr_right fun _ => iff_of_eq ht)
  rw [←measureReal_congr hcoe]
  clear hcoe
  induction n with
  | zero => simp
  | succ n ih =>
    rw [←Set.Ico_union_Ico_eq_Ico (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n)),inter_union_distrib_left]
    apply (measureReal_union_le _ _).trans
    change _≤((n+1:ℕ):ℝ)*M
    rw [Nat.cast_succ,add_mul,one_mul]
    exact add_le_add ih (step n)

#print axioms scalar_record_charge
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated.ScalarOccupation
