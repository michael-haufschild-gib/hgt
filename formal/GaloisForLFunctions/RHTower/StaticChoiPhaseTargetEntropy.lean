import GaloisForLFunctions.RHTower.UniversalPhaseCoherenceTargetMeasure

/-!
# Static Choi phase-target entropy

Translation invariance turns the existing equal-phase coherence estimate into
an entropy bound for any target contained in a translated coherence cap.  A
finite union pays only its dictionary cardinality.  This is the measure layer
needed to count low-complexity circuit targets on a static spectral torus.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Equal-weight coherence cap translated to the phase point `y`. -/
def translatedTorusCoherenceTarget {d : Type*} [Fintype d]
    (y : d → UnitAddCircle) (η : ℝ) : Set (d → UnitAddCircle) :=
  (fun x => x - y) ⁻¹' torusCoherenceTarget (d := d) η

/-- Coordinate translation preserves the Haar mass of a coherence cap. -/
theorem measureReal_translatedTorusCoherenceTarget
    {d : Type*} [Fintype d]
    (y : d → UnitAddCircle) (η : ℝ) :
    volume.real (translatedTorusCoherenceTarget y η) =
      volume.real (torusCoherenceTarget (d := d) η) := by
  rw [measureReal_def, measureReal_def]
  simp only [translatedTorusCoherenceTarget, sub_eq_add_neg]
  change ENNReal.toReal
      (volume ((fun x : d → UnitAddCircle => x + -y) ⁻¹'
        torusCoherenceTarget (d := d) η)) =
    ENNReal.toReal (volume (torusCoherenceTarget (d := d) η))
  rw [measure_preimage_add_right]

/-- A phase target is controlled at defect `η` when it lies in one translated
equal-weight coherence cap. -/
def TorusTargetControlled {d : Type*} [Fintype d]
    (A : Set (d → UnitAddCircle)) (η : ℝ) : Prop :=
  ∃ y, A ⊆ translatedTorusCoherenceTarget y η

/-- Preimage in phase space of a metric ball around an arbitrary target. -/
def torusMetricBallTarget {d : Type*} [Fintype d]
    {Y : Type*} [PseudoMetricSpace Y]
    (f : (d → UnitAddCircle) → Y) (c : Y) (δ : ℝ) :
    Set (d → UnitAddCircle) :=
  {x | dist (f x) c ≤ δ}

/-- The phase preimage of a closed metric ball is closed whenever the phase
map is continuous. -/
theorem isClosed_torusMetricBallTarget
    {d : Type*} [Fintype d]
    {Y : Type*} [PseudoMetricSpace Y]
    {f : (d → UnitAddCircle) → Y} (hf : Continuous f)
    (c : Y) (δ : ℝ) :
    IsClosed (torusMetricBallTarget f c δ) := by
  rw [torusMetricBallTarget]
  exact isClosed_le (hf.dist continuous_const) continuous_const

/-- If every pair in a radius-`δ` target ball is coherent at defect `η`, the
whole ball lies in one translated coherence cap. -/
theorem torusMetricBallTarget_controlled
    {d : Type*} [Fintype d]
    {Y : Type*} [PseudoMetricSpace Y]
    (f : (d → UnitAddCircle) → Y) (c : Y) {δ η : ℝ}
    (hpair : ∀ x y, dist (f x) (f y) ≤ 2 * δ →
      x - y ∈ torusCoherenceTarget (d := d) η) :
    TorusTargetControlled (torusMetricBallTarget f c δ) η := by
  classical
  by_cases hnonempty : (torusMetricBallTarget f c δ).Nonempty
  · obtain ⟨y, hy⟩ := hnonempty
    refine ⟨y, ?_⟩
    intro x hx
    change dist (f x) c ≤ δ at hx
    change dist (f y) c ≤ δ at hy
    have hy' : dist c (f y) ≤ δ := by simpa [dist_comm] using hy
    rw [translatedTorusCoherenceTarget, Set.mem_preimage]
    apply hpair x y
    calc
      dist (f x) (f y) ≤ dist (f x) c + dist c (f y) := dist_triangle _ _ _
      _ ≤ δ + δ := add_le_add hx hy'
      _ = 2 * δ := by ring
  · refine ⟨0, ?_⟩
    intro x hx
    exact (hnonempty ⟨x, hx⟩).elim

/-- Every controlled target inherits the optimized coherence-cap entropy
bound, with no basis-dependent constant. -/
theorem measureReal_torusTargetControlled_le
    {d : Type*} [Fintype d] [Nonempty d]
    {A : Set (d → UnitAddCircle)} {η : ℝ} (hη : 0 < η)
    (hA : TorusTargetControlled A η) :
    volume.real A ≤
      (Fintype.card d : ℝ) * Real.exp ((Fintype.card d : ℝ) / 2) *
        Real.sqrt (Real.pi * η / 2) ^ (Fintype.card d - 1) := by
  obtain ⟨y, hy⟩ := hA
  calc
    volume.real A ≤ volume.real (translatedTorusCoherenceTarget y η) :=
      measureReal_mono hy
    _ = volume.real (torusCoherenceTarget (d := d) η) :=
      measureReal_translatedTorusCoherenceTarget y η
    _ ≤ _ := measureReal_torusCoherenceTarget_le_optimized hη

/-- A finite dictionary of controlled targets pays exactly the dictionary
cardinality in the Haar upper bound. -/
theorem measureReal_iUnion_torusTargetControlled_le
    {d κ : Type*} [Fintype d] [Nonempty d] [Fintype κ]
    (A : κ → Set (d → UnitAddCircle)) {η : ℝ} (hη : 0 < η)
    (hA : ∀ k, TorusTargetControlled (A k) η) :
    volume.real (⋃ k, A k) ≤
      (Fintype.card κ : ℝ) *
        ((Fintype.card d : ℝ) * Real.exp ((Fintype.card d : ℝ) / 2) *
          Real.sqrt (Real.pi * η / 2) ^ (Fintype.card d - 1)) := by
  calc
    volume.real (⋃ k, A k) ≤ ∑ k, volume.real (A k) :=
      measureReal_iUnion_fintype_le A
    _ ≤ ∑ _k : κ,
        ((Fintype.card d : ℝ) * Real.exp ((Fintype.card d : ℝ) / 2) *
          Real.sqrt (Real.pi * η / 2) ^ (Fintype.card d - 1)) := by
      exact Finset.sum_le_sum fun k _hk =>
        measureReal_torusTargetControlled_le hη (hA k)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Fixed-length words used to pad every circuit of length at most `s` once an
identity-labelled gate is included in the alphabet. -/
def PaddedCircuitWord (gate : Type*) (s : ℕ) := Fin (s + 1) → gate

instance {gate : Type*} [Fintype gate] (s : ℕ) :
    Fintype (PaddedCircuitWord gate s) :=
  inferInstanceAs (Fintype (Fin (s + 1) → gate))

instance {gate : Type*} [Nonempty gate] (s : ℕ) :
    Nonempty (PaddedCircuitWord gate s) :=
  inferInstanceAs (Nonempty (Fin (s + 1) → gate))

instance {gate : Type*} [DecidableEq gate] (s : ℕ) :
    DecidableEq (PaddedCircuitWord gate s) :=
  inferInstanceAs (DecidableEq (Fin (s + 1) → gate))

theorem card_paddedCircuitWord (gate : Type*) [Fintype gate] (s : ℕ) :
    Fintype.card (PaddedCircuitWord gate s) = Fintype.card gate ^ (s + 1) := by
  change Fintype.card (Fin (s + 1) → gate) = Fintype.card gate ^ (s + 1)
  rw [Fintype.card_fun, Fintype.card_fin]

/-- A padded circuit dictionary pays exactly `|gate|^(s+1)` in the phase-cap
union bound.  The theorem is independent of circuit semantics: the caller
supplies the controlled target associated to each word. -/
theorem measureReal_iUnion_paddedCircuitTargets_le
    {d gate : Type*} [Fintype d] [Nonempty d] [Fintype gate]
    (s : ℕ) (A : PaddedCircuitWord gate s → Set (d → UnitAddCircle))
    {η : ℝ} (hη : 0 < η)
    (hA : ∀ w, TorusTargetControlled (A w) η) :
    volume.real (⋃ w, A w) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        ((Fintype.card d : ℝ) * Real.exp ((Fintype.card d : ℝ) / 2) *
          Real.sqrt (Real.pi * η / 2) ^ (Fintype.card d - 1)) := by
  simpa only [card_paddedCircuitWord, Nat.cast_pow] using
    (measureReal_iUnion_torusTargetControlled_le A hη hA)

end RHTower
