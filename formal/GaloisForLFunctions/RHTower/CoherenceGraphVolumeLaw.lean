import GaloisForLFunctions.RHTower.RootedForestShear
import GaloisForLFunctions.RHTower.CircleChordBall

/-!
# The forest-coordinate volume law of a weighted coherence graph

For a finite weighted graph the chord energy `Φ_a(z) = ∑_e a_e ‖z_{src e} − z_{tgt e}‖²` is
sandwiched, in the coordinates of a rooted spanning forest, between two products of circle chord
balls: forest chords of size `δ` force `Φ_a ≤ K δ²`, and `Φ_a ≤ ε²` forces every forest chord to be
at most `ε/√a_f`.

Together with the exact circle chord-ball measure bounds this gives the two-sided volume law with
the graph rank as exponent.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
omit [Fintype V] in
omit [Fintype V] in
/-- The chord energy of a finite weighted edge family on the phase torus. -/
def graphChordEnergy (src tgt : E → V) (a : E → ℝ) (x : V → UnitAddCircle) : ℝ :=
  ∑ e, a e * ‖fourier 1 (x (src e)) - fourier 1 (x (tgt e))‖ ^ 2

/-- A rooted spanning forest chart: each nonroot vertex carries its parent edge, and every graph
edge is joined by a forest walk. -/
structure ForestChart (T : RootedForest V) (src tgt : E → V) where
  /-- The graph edge realizing the parent link of a nonroot vertex. -/
  edgeAt : V → E
  /-- Its endpoints are the vertex and its parent. -/
  edgeAt_spec : ∀ v, T.depth v ≠ 0 →
    (src (edgeAt v) = v ∧ tgt (edgeAt v) = T.parent v) ∨
      (src (edgeAt v) = T.parent v ∧ tgt (edgeAt v) = v)
  /-- A forest walk joining the endpoints of every graph edge. -/
  walk : ∀ e : E, (T.forestGraph).Walk (src e) (tgt e)

/-- The forest constant `K_F = ∑_e a_e ℓ_e²`. -/
def ForestChart.constant {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) (a : E → ℝ) : ℝ :=
  ∑ e, a e * ((chart.walk e).length : ℝ) ^ 2

omit [Fintype V] in
theorem ForestChart.constant_nonneg {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e) :
    0 ≤ chart.constant a :=
  Finset.sum_nonneg fun e _ => mul_nonneg (ha e) (sq_nonneg _)

/-- The chord of a difference of phases is the chord between the phases. -/
theorem norm_fourier_sub_sub_one (p q : UnitAddCircle) :
    ‖fourier 1 (p - q) - 1‖ = ‖fourier 1 p - fourier 1 q‖ := by
  simp only [fourier_one]
  have hsub : p - q = p + (-q) := sub_eq_add_neg _ _
  rw [hsub, AddCircle.toCircle_add, AddCircle.toCircle_neg]
  change ‖(AddCircle.toCircle p : ℂ) * (AddCircle.toCircle q : ℂ)⁻¹ - 1‖ =
    ‖(AddCircle.toCircle p - AddCircle.toCircle q : ℂ)‖
  have hq : ‖(AddCircle.toCircle q : ℂ)⁻¹‖ = 1 := by
    rw [norm_inv, Circle.norm_coe, inv_one]
  calc ‖(AddCircle.toCircle p : ℂ) * (AddCircle.toCircle q : ℂ)⁻¹ - 1‖
      = ‖((AddCircle.toCircle p : ℂ) - AddCircle.toCircle q) *
          (AddCircle.toCircle q : ℂ)⁻¹‖ := by
        congr 1
        have hq0 : (AddCircle.toCircle q : ℂ) ≠ 0 := Circle.coe_ne_zero _
        field_simp
    _ = ‖(AddCircle.toCircle p : ℂ) - AddCircle.toCircle q‖ := by
        rw [norm_mul, hq, mul_one]

omit [Fintype V] in
/-- The sheared chord at a nonroot vertex is the chord to its parent. -/
theorem norm_shear_chord (T : RootedForest V) (x : V → UnitAddCircle) {v : V}
    (h : T.depth v ≠ 0) :
    ‖fourier 1 (T.shear x v) - 1‖ = ‖fourier 1 (x v) - fourier 1 (x (T.parent v))‖ := by
  rw [T.shear_of_ne x h, norm_fourier_sub_sub_one]

omit [Fintype V] [Fintype E] in
/-- Small forest chords make all graph chords small. -/
theorem norm_chord_le_of_shear_le {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) (x : V → UnitAddCircle) {δ : ℝ}
    (hshear : ∀ v, T.depth v ≠ 0 → ‖fourier 1 (T.shear x v) - 1‖ ≤ δ) (e : E) :
    ‖fourier 1 (x (src e)) - fourier 1 (x (tgt e))‖ ≤ ((chart.walk e).length : ℝ) * δ := by
  refine T.norm_sub_le_walk_length_mul (fun v => fourier 1 (x v)) ?_ (chart.walk e)
  rintro p q ⟨hne, hpq⟩
  rcases hpq with hp | hq
  · have hdp : T.depth p ≠ 0 := T.depth_ne_zero_of_parent_ne (by rw [hp]; exact hne.symm)
    have := hshear p hdp
    rwa [norm_shear_chord T x hdp, hp] at this
  · have hdq : T.depth q ≠ 0 := T.depth_ne_zero_of_parent_ne (by rw [hq]; exact hne)
    have := hshear q hdq
    rw [norm_shear_chord T x hdq, hq] at this
    rwa [norm_sub_rev]

/-- **Small forest chords give small chord energy.** -/
theorem graphChordEnergy_le_of_shear_le {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (x : V → UnitAddCircle) {δ : ℝ}
    (hshear : ∀ v, T.depth v ≠ 0 → ‖fourier 1 (T.shear x v) - 1‖ ≤ δ) :
    graphChordEnergy src tgt a x ≤ chart.constant a * δ ^ 2 := by
  rw [graphChordEnergy, ForestChart.constant, Finset.sum_mul]
  refine Finset.sum_le_sum fun e _ => ?_
  have hchord := norm_chord_le_of_shear_le chart x hshear e
  have hnn : (0 : ℝ) ≤ ‖fourier 1 (x (src e)) - fourier 1 (x (tgt e))‖ := norm_nonneg _
  have hlen : (0 : ℝ) ≤ ((chart.walk e).length : ℝ) := Nat.cast_nonneg _
  have hsq : ‖fourier 1 (x (src e)) - fourier 1 (x (tgt e))‖ ^ 2 ≤
      (((chart.walk e).length : ℝ) * δ) ^ 2 := by
    exact pow_le_pow_left₀ hnn hchord 2
  calc a e * ‖fourier 1 (x (src e)) - fourier 1 (x (tgt e))‖ ^ 2
      ≤ a e * (((chart.walk e).length : ℝ) * δ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (ha e)
    _ = a e * ((chart.walk e).length : ℝ) ^ 2 * δ ^ 2 := by ring

omit [Fintype V] in
/-- **Small chord energy forces small forest chords.** -/
theorem shear_le_of_graphChordEnergy_le {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    (x : V → UnitAddCircle) {ε : ℝ} (hε : 0 ≤ ε)
    (henergy : graphChordEnergy src tgt a x ≤ ε ^ 2)
    {v : V} (hv : T.depth v ≠ 0) (hpos : 0 < a (chart.edgeAt v)) :
    ‖fourier 1 (T.shear x v) - 1‖ ≤ ε / Real.sqrt (a (chart.edgeAt v)) := by
  set e := chart.edgeAt v with he
  have hterm : a e * ‖fourier 1 (x (src e)) - fourier 1 (x (tgt e))‖ ^ 2 ≤ ε ^ 2 := by
    refine le_trans ?_ henergy
    rw [graphChordEnergy]
    refine Finset.single_le_sum (f := fun e => a e *
      ‖fourier 1 (x (src e)) - fourier 1 (x (tgt e))‖ ^ 2) ?_ (Finset.mem_univ e)
    exact fun i _ => mul_nonneg (ha i) (sq_nonneg _)
  have hchord : ‖fourier 1 (x (src e)) - fourier 1 (x (tgt e))‖ =
      ‖fourier 1 (T.shear x v) - 1‖ := by
    rw [norm_shear_chord T x hv]
    rcases chart.edgeAt_spec v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← he] at h1 h2; rw [h1, h2]
    · rw [← he] at h1 h2; rw [h1, h2, norm_sub_rev]
  rw [hchord] at hterm
  have hsq : Real.sqrt (a e) ^ 2 = a e := Real.sq_sqrt (le_of_lt hpos)
  have hspos : 0 < Real.sqrt (a e) := Real.sqrt_pos.2 hpos
  rw [le_div_iff₀ hspos]
  have hnn : (0 : ℝ) ≤ ‖fourier 1 (T.shear x v) - 1‖ := norm_nonneg _
  nlinarith [hterm, hsq, hspos, hnn, hε]

/-! ## The two-sided volume law -/

/-- The forest-coordinate box of prescribed nonroot radii. -/
def forestBox (T : RootedForest V) (r : V → ℝ) : Set (V → UnitAddCircle) :=
  Set.univ.pi fun v => if T.depth v = 0 then Set.univ else chordBall (r v)

theorem measurableSet_forestBox (T : RootedForest V) (r : V → ℝ) :
    MeasurableSet (forestBox T r) := by
  refine MeasurableSet.univ_pi fun v => ?_
  by_cases h : T.depth v = 0
  · simp [h]
  · simpa [h] using measurableSet_chordBall (r v)

theorem volume_forestBox (T : RootedForest V) (r : V → ℝ) :
    volume (forestBox T r) =
      ∏ v : V, if T.depth v = 0 then 1 else volume (chordBall (r v)) := by
  rw [forestBox, MeasureTheory.volume_pi_pi]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases h : T.depth v = 0
  · rw [if_pos h, if_pos h, AddCircle.measure_univ]
    simp
  · rw [if_neg h, if_neg h]

omit [Fintype V] in
theorem shear_preimage_forestBox (T : RootedForest V) (r : V → ℝ) :
    (T.shear : (V → UnitAddCircle) → (V → UnitAddCircle)) ⁻¹' (forestBox T r) =
      {x | ∀ v, T.depth v ≠ 0 → ‖fourier 1 (T.shear x v) - 1‖ ≤ r v} := by
  ext x
  simp only [Set.mem_preimage, forestBox, Set.mem_univ_pi, Set.mem_setOf_eq]
  constructor
  · intro h v hv
    have := h v
    rw [if_neg hv] at this
    exact this
  · intro h v
    by_cases hv : T.depth v = 0
    · rw [if_pos hv]; trivial
    · rw [if_neg hv]; exact h v hv

theorem volume_shear_preimage (T : RootedForest V) (r : V → ℝ) :
    volume ((T.shear : (V → UnitAddCircle) → (V → UnitAddCircle)) ⁻¹' (forestBox T r)) =
      volume (forestBox T r) :=
  (T.measurePreserving_shear).measure_preimage (measurableSet_forestBox T r).nullMeasurableSet

/-- The number of nonroot vertices: the rank of the coherence graph. -/
def RootedForest.rank (T : RootedForest V) : ℕ :=
  (Finset.univ.filter fun v => T.depth v ≠ 0).card

/-- **Lower volume bound.**  Every phase vector whose forest chords are at most `δ` has chord
energy at most `K δ²`, so the sublevel set contains a product of `rank` chord balls. -/
theorem ofReal_le_volume_graphChordEnergy_le {T : RootedForest V} {src tgt : E → V}
    (chart : ForestChart T src tgt) {a : E → ℝ} (ha : ∀ e, 0 ≤ a e)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδpi : δ ≤ Real.pi) :
    ENNReal.ofReal ((δ / Real.pi) ^ T.rank) ≤
      volume {x : V → UnitAddCircle |
        graphChordEnergy src tgt a x ≤ chart.constant a * δ ^ 2} := by
  have hsub : (T.shear : (V → UnitAddCircle) → (V → UnitAddCircle)) ⁻¹'
      (forestBox T (fun _ => δ)) ⊆
      {x : V → UnitAddCircle |
        graphChordEnergy src tgt a x ≤ chart.constant a * δ ^ 2} := by
    intro x hx
    rw [shear_preimage_forestBox] at hx
    exact graphChordEnergy_le_of_shear_le chart ha x hx
  refine le_trans ?_ (measure_mono hsub)
  rw [volume_shear_preimage, volume_forestBox]
  have hbound : ∀ v : V,
      (if T.depth v = 0 then (1 : ℝ≥0∞) else ENNReal.ofReal (δ / Real.pi)) ≤
        (if T.depth v = 0 then 1 else volume (chordBall δ)) := by
    intro v
    by_cases h : T.depth v = 0
    · simp [h]
    · simp only [h, ↓reduceIte]
      exact ofReal_le_volume_chordBall hδpi
  refine le_trans (le_of_eq ?_) (Finset.prod_le_prod' (fun v _ => hbound v))
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const,
    ENNReal.ofReal_pow (by positivity)]
  rfl

end

end RHTower
