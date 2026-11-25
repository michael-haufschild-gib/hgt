import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.BudgetOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit

/-! # Initial occupation of differences and the first date after an observed prefix -/

open Set MeasureTheory Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines
open SharpOccupation
open PrecisionReturns (firstVisit firstVisit_isLeast)
noncomputable section

/-- Moving the first point of a compact window to zero puts the entire
translated window into its nonnegative difference set. -/
theorem translate_from_first (A B : Set ℝ) (hA : IsClosed A) (hB : MeasurableSet B)
    (hdiff : ∀ t∈A, ∀ u∈A, t-u∈B) (a T : ℝ) :
    volume.real (A∩Icc a (a+T)) ≤ volume.real (B∩Icc 0 T) := by
  let K := A∩Icc a (a+T)
  rcases K.eq_empty_or_nonempty with h|hne
  · change volume.real K≤_
    rw [h,measureReal_empty]
    exact measureReal_nonneg
  obtain ⟨p,hp,hmin⟩ := (isCompact_Icc.inter_left hA).exists_isMinOn hne continuous_id.continuousOn
  let F := B∩Icc 0 T
  have hm : MeasurableSet F := hB.inter measurableSet_Icc
  have hmp := measurePreserving_add_right volume (-p)
  rw [←hmp.measureReal_preimage (s:=F) hm.nullMeasurableSet]
  apply measureReal_mono _ (by
    rw [hmp.measure_preimage hm.nullMeasurableSet]
    exact measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  intro t ht
  change t+ -p∈F
  rw [←sub_eq_add_neg]
  exact ⟨hdiff t ht.1 p hp.1,sub_nonneg.mpr (hmin ht),by linarith only [ht.2.2,hp.2.1]⟩

/-- A limiting time density gives an identity-prefix lower bound at every
length for the set of allowed differences, including on very short records. -/
theorem density_le_prefix (A B : Set ℝ) (hA : IsClosed A) (hB : MeasurableSet B)
    (hdiff : ∀ t∈A, ∀ u∈A, t-u∈B) {p : ℝ}
    (hp : Tendsto (fun t : ℝ => volume.real (A∩Icc 0 t)/t) atTop (𝓝 p))
    (T : ℝ) (hT : 0≤T) : p*T≤volume.real (B∩Icc 0 T) := by
  rcases hT.eq_or_lt with h|h
  · rw [←h,mul_zero]; exact measureReal_nonneg
  let M := volume.real (B∩Icc 0 T)
  have tiles (n : ℕ) : volume.real (A∩Icc 0 ((n:ℝ)*T))≤(n:ℝ)*M := by
    induction n with
    | zero =>
      simp only [Nat.cast_zero,zero_mul,Icc_self]
      have hz : volume (A∩{(0:ℝ)})=0 := measure_mono_null inter_subset_right (measure_singleton _)
      simp only [Measure.real,hz,ENNReal.toReal_zero,le_refl]
    | succ n ih =>
      let u := (n:ℝ)*T
      have hu : 0≤u := mul_nonneg (Nat.cast_nonneg _) hT
      have hsplit : Icc 0 u ∪ Icc u (u+T)=Icc 0 (u+T) := by
        ext t
        constructor
        · rintro (ht|ht)
          · exact ⟨ht.1,ht.2.trans (le_add_of_nonneg_right hT)⟩
          · exact ⟨hu.trans ht.1,ht.2⟩
        · intro ht
          exact (le_total t u).elim (fun htu => Or.inl ⟨ht.1,htu⟩) (fun hut => Or.inr ⟨hut,ht.2⟩)
      rw [Nat.cast_succ,add_mul,one_mul,add_mul,one_mul,←hsplit,inter_union_distrib_left]
      exact (measureReal_union_le _ _).trans (add_le_add ih (translate_from_first A B hA hB hdiff u T))
  have ht : Tendsto (fun n : ℕ => (n:ℝ)*T) atTop atTop := by
    simpa only [mul_comm T] using tendsto_natCast_atTop_atTop.const_mul_atTop h
  apply (le_div_iff₀ h).mp
  apply le_of_tendsto (hp.comp ht)
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn
  apply (div_le_div_iff₀ (mul_pos hn' h) h).mpr
  exact (mul_le_mul_of_nonneg_right (tiles n) hT).trans_eq (by ring)

/-- The terminal visit adds zero measure. All affordable time up to the
first return was already observed by its starting date. -/
theorem first_visit_mass {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) {e a : ℝ}
    (he : 0<e) :
    volume.real (visitSet H s e∩Icc 0 (firstVisit H a s e))=volume.real (visitSet H s e∩Icc 0 a) := by
  let v := firstVisit H a s e
  have hl := firstVisit_isLeast H a s he
  have hnull : ∀ᵐ t : ℝ ∂volume, t≠v := by
    exact (measure_eq_zero_iff_ae_notMem.mp (measure_singleton v) : ∀ᵐ t ∂volume, t∉({v}:Set ℝ))
  apply measureReal_congr
  filter_upwards [hnull] with t ht
  apply propext
  constructor
  · rintro ⟨hfit,hlo,hv⟩
    exact ⟨hfit,hlo,le_of_not_gt fun h => ht (le_antisymm hv (hl.2 ⟨h.le,hfit⟩))⟩
  · exact fun h => ⟨h.1,h.2.1,h.2.2.trans hl.1.1⟩

theorem closed_visits {N : ℕ} (H : selfAdjoint (Register N)) (k : ℕ) (e : ℝ) :
    IsClosed (visitSet H k e) := by
  change IsClosed {t | HasProjectiveCircuitApproximation N e k (unitaryEvolution H.val t)}
  simp only [hasProjectiveCircuitApproximation_iff_infDist]
  exact isClosed_le (orbitCircuitDistance_lipschitz H k).continuous continuous_const

#print axioms density_le_prefix
#print axioms first_visit_mass
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrefixDeadlines
