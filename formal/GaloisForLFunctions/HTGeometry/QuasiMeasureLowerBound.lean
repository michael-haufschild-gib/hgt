import GaloisForLFunctions.HTGeometry.QuasiNodeWeightSum
import GaloisForLFunctions.HTGeometry.QuasiTightness

/-!
# A node inside a set forces mass there

The quasi measure carries the weight `w_x` at each node `x`, so any measurable set containing a node
has at least that much mass.  Combined with `λ(x) ≤ w_x` this bounds the measure of a set below by
the Christoffel limit at any node it contains.

This is the lower bound that survives the weak limit: `limsup` of the approximants against a closed
set is at most the limit's mass there.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **A set containing a node has at least that node's weight.** -/
theorem quasiMeasure_ge_of_node_mem (s : ℕ → ℝ) (n : ℕ) (t : ℝ) {A : Set ℝ}
    (hA : MeasurableSet A) {x : ℝ} (hx : x ∈ quasiNodes s n t) (hxA : x ∈ A) :
    ENNReal.ofReal (quasiWeight s n t x) ≤ quasiMeasure s n t A := by
  classical
  rw [quasiMeasure, finsetWeightedDirac_apply _ _ hA]
  have hterm : ENNReal.ofReal (quasiWeight s n t x) * A.indicator 1 x
      = ENNReal.ofReal (quasiWeight s n t x) := by
    rw [Set.indicator_of_mem hxA, Pi.one_apply, mul_one]
  rw [← hterm]
  exact Finset.single_le_sum (f := fun ξ => ENNReal.ofReal (quasiWeight s n t ξ) *
    A.indicator 1 ξ) (fun ξ _ => zero_le) hx

/-- **A set containing a node has at least the Christoffel limit there.** -/
theorem quasiMeasure_ge_ofReal_christoffelLimit (h : PositiveMomentForm s) (n : ℕ) (t : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) {x : ℝ} (hx : x ∈ quasiNodes s n t) (hxA : x ∈ A) :
    ENNReal.ofReal (christoffelLimit s x) ≤ quasiMeasure s n t A :=
  le_trans (ENNReal.ofReal_le_ofReal (christoffelLimit_le_quasiWeight h n t hx))
    (quasiMeasure_ge_of_node_mem s n t hA hx hxA)

/-- For a normalised sequence the normalised measure is the measure itself. -/
theorem quasiProb_eq_quasiMeasure (h0 : s 0 = 1) (n : ℕ) (t : ℝ) :
    quasiProb s n t = quasiMeasure s n t := by
  rw [quasiProb, h0, ENNReal.ofReal_one, inv_one, one_smul]

/-- **The normalised quasi measure of a set containing a node.** -/
theorem quasiProb_ge_ofReal_christoffelLimit (h : PositiveMomentForm s) (h0 : s 0 = 1) (n : ℕ)
    (t : ℝ) {A : Set ℝ} (hA : MeasurableSet A) {x : ℝ} (hx : x ∈ quasiNodes s n t)
    (hxA : x ∈ A) :
    ENNReal.ofReal (christoffelLimit s x) ≤ quasiProb s n t A := by
  rw [quasiProb_eq_quasiMeasure h0]
  exact quasiMeasure_ge_ofReal_christoffelLimit h n t hA hx hxA

/-- **From shrinking intervals to the atom.**  A bound valid on every small symmetric interval about
`ξ` is a bound on the mass of `{ξ}`. -/
theorem le_measure_singleton_of_forall_Icc (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ)
    {c : ENNReal} {η : ℝ} (hη : 0 < η)
    (hall : ∀ δ : ℝ, 0 < δ → δ < η → c ≤ μ (Set.Icc (ξ - δ) (ξ + δ))) :
    c ≤ μ {ξ} := by
  set A : ℕ → Set ℝ := fun m => Set.Icc (ξ - η / ((m : ℝ) + 2)) (ξ + η / ((m : ℝ) + 2)) with hA
  have hδpos : ∀ m : ℕ, 0 < η / ((m : ℝ) + 2) := fun m => div_pos hη (by positivity)
  have hδlt : ∀ m : ℕ, η / ((m : ℝ) + 2) < η := by
    intro m
    rw [div_lt_iff₀ (by positivity)]
    have : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hmeas : ∀ m, NullMeasurableSet (A m) μ :=
    fun m => measurableSet_Icc.nullMeasurableSet
  have hanti : Antitone A := by
    intro a b hab
    have hcast : ((a : ℝ) + 2) ≤ ((b : ℝ) + 2) := by
      have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      linarith
    have hle : η / ((b : ℝ) + 2) ≤ η / ((a : ℝ) + 2) :=
      div_le_div_of_nonneg_left hη.le (by positivity) hcast
    exact Set.Icc_subset_Icc (by linarith) (by linarith)
  have hinter : (⋂ m, A m) = {ξ} := by
    ext x
    simp only [Set.mem_iInter, hA, Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hne
      have hpos : 0 < |x - ξ| := abs_pos.mpr (sub_ne_zero.mpr hne)
      obtain ⟨m, hm⟩ := exists_nat_gt (η / |x - ξ|)
      have hmb : η / ((m : ℝ) + 2) < |x - ξ| := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hpos] at hm
        nlinarith [hpos, Nat.cast_nonneg (α := ℝ) m]
      have hxm := hx m
      have : |x - ξ| ≤ η / ((m : ℝ) + 2) :=
        abs_le.mpr ⟨by linarith [hxm.1], by linarith [hxm.2]⟩
      linarith
    · rintro rfl
      intro m
      exact ⟨by linarith [hδpos m], by linarith [hδpos m]⟩
  have htend := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top μ _⟩
  rw [hinter] at htend
  exact ge_of_tendsto htend (Filter.Eventually.of_forall fun m => hall _ (hδpos m) (hδlt m))

end HTGeometry
