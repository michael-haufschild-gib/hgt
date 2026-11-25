import GaloisForLFunctions.HTGeometry.Quantum.IntegerClockPhaseEquidistribution
import Mathlib.Data.Nat.Nth

/-! # Mean spacing of visits to a positive-frequency target -/

open Set MeasureTheory Filter Topology
open scoped Count
namespace GaloisForLFunctions.HTGeometry.EntrySensitivity.PrescribedCharacters.VisitIndices
noncomputable section

/-- The empirical mass of a measurable target counts visits up to and
including the terminal index. -/
theorem prefix_count {X : Type*} [MeasurableSpace X] (f : ℕ → X) (A : Set X)
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

/-- One hit in every block gives an infinite enumeration with a common
upper bound on every consecutive index difference. -/
theorem bounded_tick_indices (hit : ℕ → Prop) {B : ℕ}
    (h : ∀ n : ℕ, ∃ j ∈ Icc n (n+B), hit j) :
    (setOf hit).Infinite ∧ ∀ i, Nat.nth hit (i+1)≤Nat.nth hit i+(B+1) := by
  constructor
  · apply Set.infinite_of_forall_exists_gt
    intro n
    obtain ⟨j,hj,hfit⟩ := h (n+1)
    exact ⟨j,hfit,hj.1⟩
  · intro i
    obtain ⟨j,hj,hfit⟩ := h (Nat.nth hit i+1)
    have hn : Nat.nth hit (i+1)≤j := le_of_not_gt fun hv =>
      (Nat.le_nth_of_lt_nth_succ hv hfit).not_gt hj.1
    simpa only [Nat.add_assoc,Nat.add_comm 1 B] using hn.trans hj.2

/-- A prefix frequency below 1/L eventually places the ith hit at
index at least L(i+1). No limiting frequency is required. -/
theorem sparse_prefix_indices {X : Type*} [MeasurableSpace X] (f : ℕ → X) (A : Set X)
    (hA : MeasurableSet A) (hi : {j | f j∈A}.Infinite) {L : ℕ} (hL : 0<L)
    (h : ∀ᶠ M : ℕ in atTop, (integerClockPrefixLaw f M : Measure X).real A < 1/(L:ℝ)) :
    ∀ᶠ i : ℕ in atTop, L*(i+1)≤Nat.nth (fun j => f j∈A) i := by
  classical
  let hit := fun j => f j∈A
  filter_upwards [(Nat.nth_strictMono hi).tendsto_atTop.eventually h] with i hp
  rw [prefix_count _ _ hA,Nat.count_nth_succ_of_infinite hi] at hp
  have hleft : (0:ℝ)<(Nat.nth hit i:ℝ)+1 := by positivity
  have hright : (0:ℝ)<L := Nat.cast_pos.mpr hL
  have hmul := (div_lt_div_iff₀ hleft hright).mp hp
  have hnat : (i+1)*L<Nat.nth hit i+1 := by
    rw [one_mul] at hmul
    exact_mod_cast hmul
  rw [Nat.mul_comm]
  exact Nat.le_of_lt_succ hnat

/-- A uniform linear deadline on all visit indices gives the
reciprocal lower bound for their limiting frequency. -/
theorem frequency_lower_of_linear_indices {X : Type*} [MeasurableSpace X] (f : ℕ → X)
    (A : Set X) (hA : MeasurableSet A) (hi : {j | f j∈A}.Infinite) {L : ℕ} (hL : 0<L)
    (hu : ∀ i, Nat.nth (fun j => f j∈A) i<L*(i+1)) {p : ℝ}
    (h : Tendsto (fun j => (integerClockPrefixLaw f j : Measure X).real A) atTop (𝓝 p)) :
    1/(L:ℝ)≤p := by
  apply le_of_not_gt
  intro hh
  obtain ⟨i,hl⟩ := (sparse_prefix_indices f A hA hi hL (h.eventually_lt_const hh)).exists
  exact (hu i).not_ge hl

/-- A limiting affordable fraction is positive whenever consecutive
visits in its infinite enumeration have bounded gaps. -/
theorem positive_frequency_of_index_gaps {X : Type*} [MeasurableSpace X] (f : ℕ → X)
    (A : Set X) (hA : MeasurableSet A) {B : ℕ}
    (hi : {j | f j∈A}.Infinite)
    (hs : ∀ i, Nat.nth (fun j => f j∈A) (i+1)≤Nat.nth (fun j => f j∈A) i+B) {p : ℝ}
    (h : Tendsto (fun j => (integerClockPrefixLaw f j : Measure X).real A) atTop (𝓝 p)) :
    0<p := by
  classical
  let hit := fun j => f j∈A
  change ∀ i, Nat.nth hit (i+1)≤Nat.nth hit i+B at hs
  let L := Nat.nth hit 0+B+2
  have hL : 0<L := by dsimp [L]; omega
  have hu (i : ℕ) : Nat.nth hit i < L*(i+1) := by
    induction i with
    | zero =>
      simp only [Nat.zero_add,Nat.mul_one]
      dsimp only [L]
      omega
    | succ i ih =>
      have hh := hs i
      rw [Nat.mul_succ]
      dsimp only [L] at *
      omega
  exact (one_div_pos.mpr (Nat.cast_pos.mpr hL)).trans_le (frequency_lower_of_linear_indices f A hA hi hL hu h)

/-- For the increasing enumeration of every hit, elapsed ticks divided
by the number of returns converge to the reciprocal target frequency. -/
theorem return_index_spacing {X : Type*} [MeasurableSpace X] (f : ℕ → X) (A : Set X)
    (hA : MeasurableSet A) {p : ℝ} (hp : 0<p)
    (h : Tendsto (fun j => (integerClockPrefixLaw f j : Measure X).real A) atTop (𝓝 p)) :
    {j | f j ∈ A}.Infinite ∧ Tendsto (fun i : ℕ => (Nat.nth (fun j => f j ∈ A) i:ℝ)/i) atTop (𝓝 p⁻¹) := by
  classical
  let hit (j : ℕ) := f j ∈ A
  have hd := h.congr (fun N => prefix_count f A hA N)
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
