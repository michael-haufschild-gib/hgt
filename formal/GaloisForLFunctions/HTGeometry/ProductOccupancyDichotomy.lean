import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure

/-!
# The occupancy dichotomy of an infinite product of laws on `ℕ`

Let `μ_i` be probability measures on `ℕ`, indexed by a type in bijection with `ℕ`, and let `Π` be
their Kolmogorov product on `∏_i ℕ`.  Call the `i`-th coordinate *occupied* when it is nonzero.  The
occupancy events are independent — that is the content of a product measure — and their masses are
the local masses `μ_i {0}ᶜ`.  The two Borel–Cantelli lemmas then decide the size of the occupied set
from a single scalar:

* if `∑_i μ_i {0}ᶜ < ∞`, almost every configuration occupies only finitely many coordinates;
* if `∑_i μ_i {0}ᶜ = ∞`, almost every configuration occupies infinitely many.

The two alternatives are exclusive and exhaustive, so divergence of the local occupancy masses is
*equivalent* to almost-sure infinite occupancy: the product has no intermediate regime.

Every arithmetic instance of this law has the same shape: the occupied set is the set of primes
dividing a random integer, the local mass is the probability that `p` divides, and the threshold is
divergence of the corresponding prime series.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

/-! ## Occupancy events -/

/-- The set of coordinates a configuration occupies. -/
def occupiedSet {ι : Type*} (k : ∀ _ : ι, ℕ) : Set ι := {i | k i ≠ 0}

/-- The event that the `i`-th coordinate is occupied. -/
def occupiedEvent {ι : Type*} (i : ι) : Set (∀ _ : ι, ℕ) := {k | k i ≠ 0}

theorem occupiedSet_eq_pos {ι : Type*} (k : ∀ _ : ι, ℕ) :
    occupiedSet k = {i | 0 < k i} := by
  ext i
  simp [occupiedSet, Nat.pos_iff_ne_zero]

theorem occupiedEvent_eq_pos {ι : Type*} (i : ι) :
    occupiedEvent i = {k : ∀ _ : ι, ℕ | 0 < k i} := by
  ext k
  simp [occupiedEvent, Nat.pos_iff_ne_zero]

theorem occupiedEvent_eq_preimage {ι : Type*} (i : ι) :
    occupiedEvent i = (fun k : ∀ _ : ι, ℕ => k i) ⁻¹' {n : ℕ | n ≠ 0} := rfl

theorem measurableSet_occupiedEvent {ι : Type*} (i : ι) :
    MeasurableSet (occupiedEvent (ι := ι) i) := by
  rw [occupiedEvent_eq_preimage]
  exact (measurable_pi_apply i) (by measurability)

/-- **Occupying infinitely many coordinates is the limsup of the occupancy events.**  This is the
combinatorial identity that lets both Borel–Cantelli lemmas speak about the occupied set. -/
theorem limsup_occupiedEvent {ι : Type*} (e : ℕ ≃ ι) :
    Filter.limsup (fun n : ℕ => occupiedEvent (e n)) Filter.atTop =
      {k : ∀ _ : ι, ℕ | (occupiedSet k).Infinite} := by
  ext k
  rw [Filter.mem_limsup_iff_frequently_mem, Nat.frequently_atTop_iff_infinite]
  change {n : ℕ | k (e n) ≠ 0}.Infinite ↔ (occupiedSet k).Infinite
  have himage : e '' {n : ℕ | k (e n) ≠ 0} = occupiedSet k := by
    ext i
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact hn
    · intro hi
      refine ⟨e.symm i, ?_, by simp⟩
      simpa [occupiedSet] using hi
  rw [← himage]
  exact (Set.infinite_image_iff e.injective.injOn).symm

theorem measurableSet_infiniteOccupancy {ι : Type*} (e : ℕ ≃ ι) :
    MeasurableSet {k : ∀ _ : ι, ℕ | (occupiedSet k).Infinite} := by
  rw [← limsup_occupiedEvent e]
  exact MeasurableSet.measurableSet_limsup fun n => measurableSet_occupiedEvent _

theorem finiteOccupancy_eq_compl {ι : Type*} :
    {k : ∀ _ : ι, ℕ | (occupiedSet k).Finite} =
      {k : ∀ _ : ι, ℕ | (occupiedSet k).Infinite}ᶜ := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.not_infinite]

theorem measurableSet_finiteOccupancy {ι : Type*} (e : ℕ ≃ ι) :
    MeasurableSet {k : ∀ _ : ι, ℕ | (occupiedSet k).Finite} := by
  rw [finiteOccupancy_eq_compl]
  exact (measurableSet_infiniteOccupancy e).compl

/-! ## Reading the threshold off a real family -/

/-- The occupancy threshold in real terms: a family of nonnegative local masses has finite
`ℝ≥0∞`-total exactly when it is summable. -/
theorem tsum_ofReal_ne_top_iff_summable {ι : Type*} (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑' i, ENNReal.ofReal (a i)) ≠ ∞ ↔ Summable a := by
  have hcoe : ∀ i, ENNReal.ofReal (a i) = (((a i).toNNReal : NNReal) : ENNReal) :=
    fun i => rfl
  rw [tsum_congr hcoe, ENNReal.tsum_coe_ne_top_iff_summable]
  constructor
  · intro h
    exact (NNReal.summable_coe.mpr h).congr fun i => Real.coe_toNNReal _ (ha i)
  · intro h
    exact NNReal.summable_coe.mp (h.congr fun i => (Real.coe_toNNReal _ (ha i)).symm)

/-! ## The product measure -/

section

variable {ι : Type*} (μ : ι → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]

/-- **The occupancy mass is local.**  Reading one coordinate pushes the product forward to that
coordinate's law, so the mass of an occupancy event is the local mass of a nonzero valuation. -/
theorem infinitePi_occupiedEvent (i : ι) :
    Measure.infinitePi μ (occupiedEvent i) = μ i {0}ᶜ := by
  have hpre : (fun k : ∀ _ : ι, ℕ => k i) ⁻¹' ({0}ᶜ : Set ℕ) = occupiedEvent i := by
    ext k
    simp [occupiedEvent]
  have hmap := (measurePreserving_eval_infinitePi μ i).measure_preimage
    ((measurableSet_singleton (0 : ℕ)).compl).nullMeasurableSet
  rw [hpre] at hmap
  exact hmap

/-- **The occupancy events are independent.**  This is the probabilistic content of a product
measure: the occupancy pattern is a coin-tossing process with local success probabilities. -/
theorem iIndepSet_occupiedEvent :
    ProbabilityTheory.iIndepSet (fun i : ι => occupiedEvent i) (Measure.infinitePi μ) := by
  have hind : ProbabilityTheory.iIndepFun
      (fun (i : ι) (k : ∀ _ : ι, ℕ) => k i) (Measure.infinitePi μ) :=
    ProbabilityTheory.iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id
  refine (ProbabilityTheory.iIndepSet_iff_meas_biInter
    (fun i => measurableSet_occupiedEvent i)).2 fun S => ?_
  refine hind.meas_biInter fun i _ => ?_
  rw [occupiedEvent_eq_preimage]
  exact MeasurableSet.preimage (by measurability) (comap_measurable _)

/-- The enumerated occupancy events are independent. -/
theorem iIndepSet_occupiedEvent_comp (e : ℕ ≃ ι) :
    ProbabilityTheory.iIndepSet (fun n : ℕ => occupiedEvent (e n)) (Measure.infinitePi μ) :=
  ProbabilityTheory.iIndepSet.precomp (s := fun i : ι => occupiedEvent i) (g := e)
    e.injective (iIndepSet_occupiedEvent μ)

/-- Enumerating the index type does not change the total occupancy mass. -/
theorem tsum_infinitePi_occupiedEvent_comp (e : ℕ ≃ ι) :
    (∑' n : ℕ, Measure.infinitePi μ (occupiedEvent (e n))) = ∑' i : ι, μ i {0}ᶜ := by
  rw [tsum_congr fun n => infinitePi_occupiedEvent μ (e n)]
  exact e.tsum_eq fun i => μ i {0}ᶜ

/-- **Divergent local masses force infinite occupancy.**  The second Borel–Cantelli lemma applied to
the independent occupancy events. -/
theorem measure_infiniteOccupancy_eq_one (e : ℕ ≃ ι)
    (hdiv : (∑' i : ι, μ i {0}ᶜ) = ∞) :
    Measure.infinitePi μ {k : ∀ _ : ι, ℕ | (occupiedSet k).Infinite} = 1 := by
  rw [← limsup_occupiedEvent e]
  exact ProbabilityTheory.measure_limsup_eq_one
    (fun n => measurableSet_occupiedEvent _)
    (iIndepSet_occupiedEvent_comp μ e)
    ((tsum_infinitePi_occupiedEvent_comp μ e).trans hdiv)

/-- Under summable local masses the infinite-occupancy event is null: the first Borel–Cantelli
lemma, which uses no independence. -/
theorem measure_infiniteOccupancy_eq_zero (e : ℕ ≃ ι)
    (hconv : (∑' i : ι, μ i {0}ᶜ) ≠ ∞) :
    Measure.infinitePi μ {k : ∀ _ : ι, ℕ | (occupiedSet k).Infinite} = 0 := by
  rw [← limsup_occupiedEvent e]
  refine MeasureTheory.measure_limsup_atTop_eq_zero ?_
  rw [tsum_infinitePi_occupiedEvent_comp μ e]
  exact hconv

/-- **Summable local masses force finite occupancy.** -/
theorem measure_finiteOccupancy_eq_one (e : ℕ ≃ ι)
    (hconv : (∑' i : ι, μ i {0}ᶜ) ≠ ∞) :
    Measure.infinitePi μ {k : ∀ _ : ι, ℕ | (occupiedSet k).Finite} = 1 := by
  rw [finiteOccupancy_eq_compl,
    MeasureTheory.prob_compl_eq_one_iff (measurableSet_infiniteOccupancy e)]
  exact measure_infiniteOccupancy_eq_zero μ e hconv

/-- **The occupancy dichotomy.**  One scalar decides the qualitative behaviour of the whole product:
almost-sure infinite occupancy holds exactly when the local occupancy masses diverge. -/
theorem measure_infiniteOccupancy_eq_one_iff (e : ℕ ≃ ι) :
    Measure.infinitePi μ {k : ∀ _ : ι, ℕ | (occupiedSet k).Infinite} = 1 ↔
      (∑' i : ι, μ i {0}ᶜ) = ∞ := by
  refine ⟨fun hone => ?_, measure_infiniteOccupancy_eq_one μ e⟩
  by_contra hconv
  rw [measure_infiniteOccupancy_eq_zero μ e hconv] at hone
  exact zero_ne_one hone

/-- The complementary form of the dichotomy. -/
theorem measure_finiteOccupancy_eq_one_iff (e : ℕ ≃ ι) :
    Measure.infinitePi μ {k : ∀ _ : ι, ℕ | (occupiedSet k).Finite} = 1 ↔
      (∑' i : ι, μ i {0}ᶜ) ≠ ∞ := by
  refine ⟨fun hone hdiv => ?_, measure_finiteOccupancy_eq_one μ e⟩
  rw [finiteOccupancy_eq_compl,
    MeasureTheory.prob_compl_eq_one_iff (measurableSet_infiniteOccupancy e)] at hone
  exact zero_ne_one (hone.symm.trans (measure_infiniteOccupancy_eq_one μ e hdiv))

/-! ## Almost-everywhere forms -/

theorem ae_infinite_occupiedSet (e : ℕ ≃ ι) (hdiv : (∑' i : ι, μ i {0}ᶜ) = ∞) :
    ∀ᵐ k ∂(Measure.infinitePi μ), (occupiedSet k).Infinite :=
  (MeasureTheory.mem_ae_iff_prob_eq_one (measurableSet_infiniteOccupancy e)).mpr
    (measure_infiniteOccupancy_eq_one μ e hdiv)

theorem ae_finite_occupiedSet (e : ℕ ≃ ι) (hconv : (∑' i : ι, μ i {0}ᶜ) ≠ ∞) :
    ∀ᵐ k ∂(Measure.infinitePi μ), (occupiedSet k).Finite :=
  (MeasureTheory.mem_ae_iff_prob_eq_one (measurableSet_finiteOccupancy e)).mpr
    (measure_finiteOccupancy_eq_one μ e hconv)

/-- **A finitely occupied configuration is invisible.**  When the local masses diverge, each single
configuration with a finite occupied set is null — in particular the empty one. -/
theorem measure_singleton_eq_zero_of_finite_occupiedSet (e : ℕ ≃ ι)
    (hdiv : (∑' i : ι, μ i {0}ᶜ) = ∞) {k : ∀ _ : ι, ℕ} (hk : (occupiedSet k).Finite) :
    Measure.infinitePi μ {k} = 0 := by
  have hnull : Measure.infinitePi μ
      {k : ∀ _ : ι, ℕ | (occupiedSet k).Finite} = 0 := by
    rw [finiteOccupancy_eq_compl,
      MeasureTheory.prob_compl_eq_zero_iff (measurableSet_infiniteOccupancy e)]
    exact measure_infiniteOccupancy_eq_one μ e hdiv
  refine MeasureTheory.measure_mono_null (fun x hx => ?_) hnull
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact hk

end

end GaloisForLFunctions.HTGeometry
