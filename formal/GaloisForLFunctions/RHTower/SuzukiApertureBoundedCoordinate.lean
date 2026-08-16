import GaloisForLFunctions.HTGeometry.BoundedCoordinateL2Expansion
import GaloisForLFunctions.HTGeometry.CoordinateMonomialTotality
import GaloisForLFunctions.RHTower.SuzukiWeilFriedrichsOperator

/-!
# The Suzuki aperture interval as a bounded coordinate

Suzuki's operator lives on `L²` of the interval carried as a subtype.  That measure space is finite
and its inclusion coordinate is bounded by the aperture, so it is an instance of the abstract
aperture, and every Taylor expansion along a bounded coordinate applies to it verbatim.

This is the identification that lets the coalescing analysis be run on the literal operator instead
of on a model of the same interval.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

theorem volume_suzukiApertureInterval_univ (a : ℝ) :
    (volume : Measure (SuzukiApertureInterval a)) Set.univ = ENNReal.ofReal (a - -a) := by
  have h : (volume : Measure (SuzukiApertureInterval a)) Set.univ
      = Measure.comap (Subtype.val) (volume : Measure ℝ) Set.univ := rfl
  rw [h, comap_subtype_coe_apply measurableSet_Icc, Subtype.coe_image_univ,
    Real.volume_Icc]

instance instIsFiniteMeasureSuzukiAperture (a : ℝ) :
    IsFiniteMeasure (volume : Measure (SuzukiApertureInterval a)) := by
  constructor
  rw [volume_suzukiApertureInterval_univ a]
  exact ENNReal.ofReal_lt_top

/-- **The Suzuki aperture interval is a bounded coordinate.** -/
def suzukiApertureCoordinate {a : ℝ} (ha : 0 ≤ a) :
    BoundedCoordinate (SuzukiApertureInterval a) volume where
  coord := Subtype.val
  bound := a
  measurable_coord := measurable_subtype_coe
  bound_nonneg := ha
  abs_coord_le := Filter.Eventually.of_forall fun t => abs_le.mpr ⟨t.2.1, t.2.2⟩

@[simp]
theorem suzukiApertureCoordinate_coord {a : ℝ} (ha : 0 ≤ a) :
    (suzukiApertureCoordinate ha).coord = Subtype.val := rfl

@[simp]
theorem suzukiApertureCoordinate_bound {a : ℝ} (ha : 0 ≤ a) :
    (suzukiApertureCoordinate ha).bound = a := rfl

/-! ## Visible degrees on the Suzuki interval -/

/-- The Suzuki aperture coordinate as a continuous map. -/
def suzukiApertureCM (a : ℝ) : C(SuzukiApertureInterval a, ℝ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem suzukiApertureCM_injective (a : ℝ) :
    Function.Injective (suzukiApertureCM a) := Subtype.val_injective

theorem toLp_coordMonomialCM_eq {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (SuzukiApertureInterval a)) ℂ
        (coordMonomialCM (suzukiApertureCM a) n)
      = (suzukiApertureCoordinate ha).monomialC n := by
  refine Lp.ext ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (𝕜 := ℂ) (p := 2)
      (volume : Measure (SuzukiApertureInterval a)) (coordMonomialCM (suzukiApertureCM a) n),
    (suzukiApertureCoordinate ha).coeFn_monomialC n] with ω h1 h2
  rw [h1, h2, coordMonomialCM_apply]
  rfl

/-- **`(2)` on Suzuki's literal interval.**  A nonzero bounded observable has a visible degree. -/
theorem exists_visible_degree_suzuki {a : ℝ} (ha : 0 ≤ a) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : SuzukiApertureIntervalL2 a →L[ℂ] E) (hP : P ≠ 0) :
    ∃ n : ℕ, P ((suzukiApertureCoordinate ha).monomialC n) ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_visible_degree (suzukiApertureCM_injective a) P hP
  exact ⟨n, by rwa [toLp_coordMonomialCM_eq ha n] at hn⟩

/-- **`(2)`, even parity.**  An observable that kills every odd monomial and is nonzero has a
visible even degree — the integer `r` of the card. -/
theorem exists_visible_evenDegree_suzuki {a : ℝ} (ha : 0 ≤ a) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : SuzukiApertureIntervalL2 a →L[ℂ] E) (hP : P ≠ 0)
    (hodd : ∀ k : ℕ, P ((suzukiApertureCoordinate ha).monomialC (2 * k + 1)) = 0) :
    ∃ k : ℕ, P ((suzukiApertureCoordinate ha).monomialC (2 * k)) ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_visible_evenDegree (suzukiApertureCM_injective a) P hP
    (fun k => by rw [toLp_coordMonomialCM_eq ha (2 * k + 1)]; exact hodd k)
  exact ⟨k, by rwa [toLp_coordMonomialCM_eq ha (2 * k)] at hk⟩

/-- **`(2)`, odd parity.**  The integer `s` of the card. -/
theorem exists_visible_oddDegree_suzuki {a : ℝ} (ha : 0 ≤ a) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : SuzukiApertureIntervalL2 a →L[ℂ] E) (hP : P ≠ 0)
    (heven : ∀ k : ℕ, P ((suzukiApertureCoordinate ha).monomialC (2 * k)) = 0) :
    ∃ k : ℕ, P ((suzukiApertureCoordinate ha).monomialC (2 * k + 1)) ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_visible_oddDegree (suzukiApertureCM_injective a) P hP
    (fun k => by rw [toLp_coordMonomialCM_eq ha (2 * k)]; exact heven k)
  exact ⟨k, by rwa [toLp_coordMonomialCM_eq ha (2 * k + 1)] at hk⟩

end RHTower
