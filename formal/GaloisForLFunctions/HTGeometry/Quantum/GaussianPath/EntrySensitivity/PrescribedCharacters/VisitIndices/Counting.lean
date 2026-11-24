import GaloisForLFunctions.HTGeometry.Quantum.IntegerClockPhaseEquidistribution
import Mathlib.Data.Nat.Nth

/-! # Mean spacing of visits to a positive-frequency target -/

open Set MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.EntrySensitivity.PrescribedCharacters.VisitIndices
noncomputable section

private theorem prefix_count {X : Type*} [MeasurableSpace X] (f : ℕ → X) (A : Set X)
    (hA : MeasurableSet A) (N : ℕ) [DecidablePred fun j => f j ∈ A] :
    (integerClockPrefixLaw f N : Measure X).real A =
      (Nat.count (fun j => f j ∈ A) (N+1):ℝ)/(N+1) := by
  classical
  rw [Measure.real,integerClockPrefixLaw,ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_of_finite _) hA]
  change ((PMF.uniformOfFintype (Fin (N+1))).toMeasure {i : Fin (N+1) | f i.val ∈ A}).toReal = _
  rw [PMF.toMeasure_uniformOfFintype_apply _ (Set.toFinite _).measurableSet,Fintype.card_fin,
    ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_natCast,Nat.cast_succ]
  congr 1
  rw [Nat.count_eq_card_fintype]
  let e : {i : Fin (N+1) // f i.val ∈ A} ≃ {n : ℕ // n<N+1 ∧ f n ∈ A} :=
    { toFun := fun i => ⟨i.val.val,i.val.isLt,i.property⟩
      invFun := fun n => ⟨⟨n.val,n.property.1⟩,n.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact_mod_cast Fintype.card_congr e

/-- For the increasing enumeration of every hit, elapsed ticks divided
by the number of returns converge to the reciprocal target frequency. -/
theorem return_index_spacing {X : Type*} [MeasurableSpace X] (f : ℕ → X) (A : Set X)
    (hA : MeasurableSet A) {p : ℝ} (hp : 0<p)
    (h : Tendsto (fun j => (integerClockPrefixLaw f j : Measure X).real A) atTop (𝓝 p)) :
    {j | f j ∈ A}.Infinite ∧ Tendsto (fun i : ℕ => (Nat.nth (fun j => f j ∈ A) i:ℝ)/i) atTop (𝓝 p⁻¹) := by
  classical
  let hit (j : ℕ) := f j ∈ A
  have hd := h.congr (prefix_count f A hA)
  have hlim : Tendsto (fun N : ℕ => (Nat.count hit N:ℝ)/N) atTop (𝓝 p) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Nat.cast_add,Nat.cast_one,hit] using hd
  have hi : (setOf hit).Infinite := by
    intro hfin
    have hz : Tendsto (fun N : ℕ => (Nat.count hit N:ℝ)/N) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => by positivity) _ (tendsto_const_div_atTop_nhds_zero_nat (hfin.toFinset.card:ℝ))
      exact fun n => div_le_div_of_nonneg_right (by exact_mod_cast Nat.count_le_card hfin n) (by positivity)
    exact hp.ne' (tendsto_nhds_unique hlim hz)
  have hn := hlim.comp (Nat.nth_strictMono hi).tendsto_atTop
  refine ⟨hi,?_⟩
  simpa only [Function.comp_def,Nat.count_nth_of_infinite hi,inv_div,hit] using hn.inv₀ hp.ne'

#print axioms return_index_spacing
end
end GaloisForLFunctions.HTGeometry.EntrySensitivity.PrescribedCharacters.VisitIndices
