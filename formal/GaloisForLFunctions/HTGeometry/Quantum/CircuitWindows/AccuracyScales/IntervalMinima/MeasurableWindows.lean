import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.IntervalMinima.RecordHeights
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.PrescribedTolerance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability

/-! # Measurability of the best physical fit in a moving observation interval -/

open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima
open MaximumIntervals PrescribedTimes ShortWindows
noncomputable section

private def windowBelow {X : Type*} (f : X × ℝ → ℝ) (T r : ℝ) : Set (X × ℝ) :=
  ⋃ t : Icc (0:ℝ) (max T 0), {p | f (p.1,p.2+t.val)<r}

private theorem open_windowBelow {X : Type*} [TopologicalSpace X] (f : X × ℝ → ℝ)
    (hf : Continuous f) (T r : ℝ) : IsOpen (windowBelow f T r) := by
  apply isOpen_iUnion
  intro t
  exact isOpen_lt (hf.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))) continuous_const

private theorem prefix_distance (k s : ℕ) (ω : PathPauliDisorder) (t : ℝ) :
    pathGateDistance (k+1) s (prefixPoint k ω) t = orbitCircuitDistance (chainGenerator ω k) s t := by
  unfold pathGateDistance orbitCircuitDistance chainGenerator
  rw [show numberedGenerator (k+1) (prefixPoint k ω)=pathHamiltonian (pathPauliDisorderShell ω (k+1))
    from numberedGenerator_shell _]

private theorem minimum_sublevel (k s : ℕ) (ω : PathPauliDisorder) (a T r : ℝ) :
    let H := chainGenerator ω k
    orbitCircuitDistance H s (bestDate H s a T) < r ↔
      (prefixPoint k ω,a) ∈ windowBelow (fun p => pathGateDistance (k+1) s p.1 p.2) T r := by
  intro H
  let w := bestDate H s a T
  obtain ⟨hw,hmin⟩ := bestDate_spec H s a T
  change w ∈ Icc a (a+max T 0) at hw
  constructor
  · intro h
    have hd : w-a ∈ Icc (0:ℝ) (max T 0) :=
      ⟨sub_nonneg.mpr hw.1,by linarith only [hw.2]⟩
    apply mem_iUnion.mpr
    refine ⟨⟨w-a,hd⟩,?_⟩
    change pathGateDistance (k+1) s (prefixPoint k ω) (a+(w-a)) < r
    rw [show a+(w-a)=w by ring,prefix_distance]
    exact h
  · intro h
    obtain ⟨t,ht⟩ := mem_iUnion.mp h
    change pathGateDistance (k+1) s (prefixPoint k ω) (a+t.val)<r at ht
    rw [prefix_distance] at ht
    have hd : a+t.val ∈ Icc a (a+max T 0) :=
      ⟨le_add_of_nonneg_right t.property.1,add_le_add le_rfl t.property.2⟩
    exact (hmin _ hd).trans_lt ht

/-- The minimum gate distance on a fixed-duration interval is measurable
at every measurable origin. Its strict sublevels come from open unions
over all offsets in the interval. -/
theorem measurable_best_distance (k s : ℕ) (a : PathPauliDisorder → ℝ) (ha : Measurable a) (T : ℝ) :
    Measurable fun ω => let H := chainGenerator ω k
      orbitCircuitDistance H s (bestDate H s (a ω) T) := by
  let f (p : (PrefixIndex (k+1) → ℝ) × ℝ) := pathGateDistance (k+1) s p.1 p.2
  let p (ω : PathPauliDisorder) := (prefixPoint k ω,a ω)
  have hp : Measurable p := (gaussian_pauli_prefix_coordinates_law (k+1)).measurable.prodMk ha
  let m (ω : PathPauliDisorder) := orbitCircuitDistance (chainGenerator ω k) s
    (bestDate (chainGenerator ω k) s (a ω) T)
  change Measurable m
  apply measurable_of_Iio
  intro r
  have heq : m ⁻¹' Iio r = p ⁻¹' windowBelow f T r := Set.ext fun ω => minimum_sublevel k s ω (a ω) T r
  rw [heq]
  exact (open_windowBelow f (continuous_distance (k+1) s) T r).measurableSet.preimage hp

/-- Almost every error selected before drawing the chain has record
clearance in a prescribed family of moving finite intervals. -/
theorem prescribed_interval_clearance (a : ℕ → ℕ → PathPauliDisorder → ℝ)
    (ha : ∀ k i, Measurable (a k i)) (T : ℕ → ℕ → ℝ) (b : ℕ → ℕ) :
    ∀ᵐ e : ℝ ∂volume, ∀ᵐ ω ∂pathPauliDisorderLaw,
      e ∉ intervalExceptional ω (fun k i => a k i ω) T b := by
  classical
  let g ω := records ω (fun k i => a k i ω) T
  have hg (k j : ℕ) : Measurable fun ω => g ω k j := by
    by_cases h : j=0
    · simpa only [g,records,if_pos h] using (measurable_const : Measurable fun _ : PathPauliDisorder => (0:ℝ))
    · dsimp only [g,records]
      simp only [if_neg h]
      exact measurable_best_distance _ _ _ (ha ..) _
  apply gaussian_regular_for_measurable_heights (fun ω => embedRows b (g ω))
  intro n j
  by_cases h : ∃ k, b k=n
  · simp only [embedRows,dif_pos h]; exact hg _ _
  · simp only [embedRows,dif_neg h]; exact measurable_const

#print axioms prescribed_interval_clearance
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.IntervalMinima
