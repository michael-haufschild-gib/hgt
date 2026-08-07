import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure

/-!
# The hitting dichotomy of an infinite product of laws on `ℕ`

Let `μ_i` be probability measures on `ℕ`, indexed by a type in bijection with `ℕ`, let `Π` be their
Kolmogorov product on `∏_i ℕ`, and fix a local target `t_i ⊆ ℕ` at each coordinate.  The hitting
events `{k | k i ∈ t_i}` are independent — that is the content of a product measure — and their
masses are the local masses `μ_i (t_i)`.  The two Borel–Cantelli lemmas then decide the size of the
hit set `{i | k i ∈ t_i}` from a single scalar:

* if `∑_i μ_i (t_i) < ∞`, almost every configuration hits only finitely many targets;
* if `∑_i μ_i (t_i) = ∞`, almost every configuration hits infinitely many.

The two alternatives are exclusive and exhaustive, so divergence of the local masses is *equivalent*
to almost-sure infinite hitting: the product has no intermediate regime.

Occupancy — a nonzero coordinate — is the case `t_i = {0}ᶜ`, and is developed below as the named
special case.  Higher thresholds `t_i = {m, m+1, …}` are the same law read at another level, which is
what separates the simple part of a valuation vector from its higher powers.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

/-! ## Hitting events -/

/-- The set of coordinates at which a configuration hits its local target. -/
def localHitSet {ι : Type*} (t : ι → Set ℕ) (k : ∀ _ : ι, ℕ) : Set ι := {i | k i ∈ t i}

/-- The event that the `i`-th coordinate hits its local target. -/
def localEvent {ι : Type*} (t : ι → Set ℕ) (i : ι) : Set (∀ _ : ι, ℕ) :=
  (fun k => k i) ⁻¹' t i

theorem localEvent_eq_setOf {ι : Type*} (t : ι → Set ℕ) (i : ι) :
    localEvent t i = {k : ∀ _ : ι, ℕ | k i ∈ t i} := rfl

theorem measurableSet_localEvent {ι : Type*} (t : ι → Set ℕ) (i : ι) :
    MeasurableSet (localEvent t i) :=
  (measurable_pi_apply i) MeasurableSet.of_discrete

/-- **Hitting infinitely many targets is the limsup of the hitting events.**  This is the
combinatorial identity that lets both Borel–Cantelli lemmas speak about the hit set. -/
theorem limsup_localEvent {ι : Type*} (t : ι → Set ℕ) (e : ℕ ≃ ι) :
    Filter.limsup (fun n : ℕ => localEvent t (e n)) Filter.atTop =
      {k : ∀ _ : ι, ℕ | (localHitSet t k).Infinite} := by
  ext k
  rw [Filter.mem_limsup_iff_frequently_mem, Nat.frequently_atTop_iff_infinite]
  change {n : ℕ | k (e n) ∈ t (e n)}.Infinite ↔ (localHitSet t k).Infinite
  have himage : e '' {n : ℕ | k (e n) ∈ t (e n)} = localHitSet t k := by
    ext i
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact hn
    · intro hi
      refine ⟨e.symm i, ?_, by simp⟩
      simpa [localHitSet] using hi
  rw [← himage]
  exact (Set.infinite_image_iff e.injective.injOn).symm

theorem measurableSet_infiniteHit {ι : Type*} (t : ι → Set ℕ) (e : ℕ ≃ ι) :
    MeasurableSet {k : ∀ _ : ι, ℕ | (localHitSet t k).Infinite} := by
  rw [← limsup_localEvent t e]
  exact MeasurableSet.measurableSet_limsup fun n => measurableSet_localEvent t _

theorem finiteHit_eq_compl {ι : Type*} (t : ι → Set ℕ) :
    {k : ∀ _ : ι, ℕ | (localHitSet t k).Finite} =
      {k : ∀ _ : ι, ℕ | (localHitSet t k).Infinite}ᶜ := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.not_infinite]

theorem measurableSet_finiteHit {ι : Type*} (t : ι → Set ℕ) (e : ℕ ≃ ι) :
    MeasurableSet {k : ∀ _ : ι, ℕ | (localHitSet t k).Finite} := by
  rw [finiteHit_eq_compl]
  exact (measurableSet_infiniteHit t e).compl

/-! ## Reading the threshold off a real family -/

/-- The threshold in real terms: a family of nonnegative local masses has finite `ℝ≥0∞`-total
exactly when it is summable. -/
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

/-- **The hitting mass is local.**  Reading one coordinate pushes the product forward to that
coordinate's law, so the mass of a hitting event is the local mass of the target. -/
theorem infinitePi_localEvent (t : ι → Set ℕ) (i : ι) :
    Measure.infinitePi μ (localEvent t i) = μ i (t i) :=
  (measurePreserving_eval_infinitePi μ i).measure_preimage
    MeasurableSet.of_discrete.nullMeasurableSet

/-- **The hitting events are independent.**  This is the probabilistic content of a product measure:
the hitting pattern is a coin-tossing process with local success probabilities. -/
theorem iIndepSet_localEvent (t : ι → Set ℕ) :
    ProbabilityTheory.iIndepSet (fun i : ι => localEvent t i) (Measure.infinitePi μ) := by
  have hind : ProbabilityTheory.iIndepFun
      (fun (i : ι) (k : ∀ _ : ι, ℕ) => k i) (Measure.infinitePi μ) :=
    ProbabilityTheory.iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id
  refine (ProbabilityTheory.iIndepSet_iff_meas_biInter
    (fun i => measurableSet_localEvent t i)).2 fun S => ?_
  exact hind.meas_biInter fun i _ =>
    MeasurableSet.preimage MeasurableSet.of_discrete (comap_measurable _)

/-- The enumerated hitting events are independent. -/
theorem iIndepSet_localEvent_comp (t : ι → Set ℕ) (e : ℕ ≃ ι) :
    ProbabilityTheory.iIndepSet (fun n : ℕ => localEvent t (e n)) (Measure.infinitePi μ) :=
  ProbabilityTheory.iIndepSet.precomp (s := fun i : ι => localEvent t i) (g := e)
    e.injective (iIndepSet_localEvent μ t)

/-- Enumerating the index type does not change the total local mass. -/
theorem tsum_infinitePi_localEvent_comp (t : ι → Set ℕ) (e : ℕ ≃ ι) :
    (∑' n : ℕ, Measure.infinitePi μ (localEvent t (e n))) = ∑' i : ι, μ i (t i) := by
  rw [tsum_congr fun n => infinitePi_localEvent μ t (e n)]
  exact e.tsum_eq fun i => μ i (t i)

/-- **Divergent local masses force infinite hitting.**  The second Borel–Cantelli lemma applied to
the independent hitting events. -/
theorem measure_infiniteHit_eq_one (t : ι → Set ℕ) (e : ℕ ≃ ι)
    (hdiv : (∑' i : ι, μ i (t i)) = ∞) :
    Measure.infinitePi μ {k : ∀ _ : ι, ℕ | (localHitSet t k).Infinite} = 1 := by
  rw [← limsup_localEvent t e]
  exact ProbabilityTheory.measure_limsup_eq_one
    (fun n => measurableSet_localEvent t _)
    (iIndepSet_localEvent_comp μ t e)
    ((tsum_infinitePi_localEvent_comp μ t e).trans hdiv)

/-- Under summable local masses the infinite-hitting event is null: the first Borel–Cantelli lemma,
which uses no independence. -/
theorem measure_infiniteHit_eq_zero (t : ι → Set ℕ) (e : ℕ ≃ ι)
    (hconv : (∑' i : ι, μ i (t i)) ≠ ∞) :
    Measure.infinitePi μ {k : ∀ _ : ι, ℕ | (localHitSet t k).Infinite} = 0 := by
  rw [← limsup_localEvent t e]
  refine MeasureTheory.measure_limsup_atTop_eq_zero ?_
  rw [tsum_infinitePi_localEvent_comp μ t e]
  exact hconv

/-- **Summable local masses force finite hitting.** -/
theorem measure_finiteHit_eq_one (t : ι → Set ℕ) (e : ℕ ≃ ι)
    (hconv : (∑' i : ι, μ i (t i)) ≠ ∞) :
    Measure.infinitePi μ {k : ∀ _ : ι, ℕ | (localHitSet t k).Finite} = 1 := by
  rw [finiteHit_eq_compl,
    MeasureTheory.prob_compl_eq_one_iff (measurableSet_infiniteHit t e)]
  exact measure_infiniteHit_eq_zero μ t e hconv

/-- **The hitting dichotomy.**  One scalar decides the qualitative behaviour of the whole product:
almost-sure infinite hitting holds exactly when the local masses diverge. -/
theorem measure_infiniteHit_eq_one_iff (t : ι → Set ℕ) (e : ℕ ≃ ι) :
    Measure.infinitePi μ {k : ∀ _ : ι, ℕ | (localHitSet t k).Infinite} = 1 ↔
      (∑' i : ι, μ i (t i)) = ∞ := by
  refine ⟨fun hone => ?_, measure_infiniteHit_eq_one μ t e⟩
  by_contra hconv
  rw [measure_infiniteHit_eq_zero μ t e hconv] at hone
  exact zero_ne_one hone

/-- The complementary form of the dichotomy. -/
theorem measure_finiteHit_eq_one_iff (t : ι → Set ℕ) (e : ℕ ≃ ι) :
    Measure.infinitePi μ {k : ∀ _ : ι, ℕ | (localHitSet t k).Finite} = 1 ↔
      (∑' i : ι, μ i (t i)) ≠ ∞ := by
  refine ⟨fun hone hdiv => ?_, measure_finiteHit_eq_one μ t e⟩
  rw [finiteHit_eq_compl,
    MeasureTheory.prob_compl_eq_one_iff (measurableSet_infiniteHit t e)] at hone
  exact zero_ne_one (hone.symm.trans (measure_infiniteHit_eq_one μ t e hdiv))

theorem ae_infinite_localHitSet (t : ι → Set ℕ) (e : ℕ ≃ ι)
    (hdiv : (∑' i : ι, μ i (t i)) = ∞) :
    ∀ᵐ k ∂(Measure.infinitePi μ), (localHitSet t k).Infinite :=
  (MeasureTheory.mem_ae_iff_prob_eq_one (measurableSet_infiniteHit t e)).mpr
    (measure_infiniteHit_eq_one μ t e hdiv)

theorem ae_finite_localHitSet (t : ι → Set ℕ) (e : ℕ ≃ ι)
    (hconv : (∑' i : ι, μ i (t i)) ≠ ∞) :
    ∀ᵐ k ∂(Measure.infinitePi μ), (localHitSet t k).Finite :=
  (MeasureTheory.mem_ae_iff_prob_eq_one (measurableSet_finiteHit t e)).mpr
    (measure_finiteHit_eq_one μ t e hconv)

end

/-! ## Occupancy: the level-one case -/

/-- The set of coordinates a configuration occupies. -/
def occupiedSet {ι : Type*} (k : ∀ _ : ι, ℕ) : Set ι := {i | k i ≠ 0}

/-- The event that the `i`-th coordinate is occupied. -/
def occupiedEvent {ι : Type*} (i : ι) : Set (∀ _ : ι, ℕ) := {k | k i ≠ 0}

theorem occupiedSet_eq_localHitSet {ι : Type*} (k : ∀ _ : ι, ℕ) :
    occupiedSet k = localHitSet (fun _ => ({0}ᶜ : Set ℕ)) k := rfl

theorem occupiedEvent_eq_localEvent {ι : Type*} (i : ι) :
    occupiedEvent (ι := ι) i = localEvent (fun _ => ({0}ᶜ : Set ℕ)) i := rfl

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
    MeasurableSet (occupiedEvent (ι := ι) i) :=
  measurableSet_localEvent (fun _ => ({0}ᶜ : Set ℕ)) i

theorem limsup_occupiedEvent {ι : Type*} (e : ℕ ≃ ι) :
    Filter.limsup (fun n : ℕ => occupiedEvent (e n)) Filter.atTop =
      {k : ∀ _ : ι, ℕ | (occupiedSet k).Infinite} :=
  limsup_localEvent (fun _ => ({0}ᶜ : Set ℕ)) e

theorem measurableSet_infiniteOccupancy {ι : Type*} (e : ℕ ≃ ι) :
    MeasurableSet {k : ∀ _ : ι, ℕ | (occupiedSet k).Infinite} :=
  measurableSet_infiniteHit (fun _ => ({0}ᶜ : Set ℕ)) e

theorem finiteOccupancy_eq_compl {ι : Type*} :
    {k : ∀ _ : ι, ℕ | (occupiedSet k).Finite} =
      {k : ∀ _ : ι, ℕ | (occupiedSet k).Infinite}ᶜ :=
  finiteHit_eq_compl (fun _ => ({0}ᶜ : Set ℕ))

theorem measurableSet_finiteOccupancy {ι : Type*} (e : ℕ ≃ ι) :
    MeasurableSet {k : ∀ _ : ι, ℕ | (occupiedSet k).Finite} :=
  measurableSet_finiteHit (fun _ => ({0}ᶜ : Set ℕ)) e

section

variable {ι : Type*} (μ : ι → Measure ℕ) [∀ i, IsProbabilityMeasure (μ i)]

/-- The occupancy mass of a coordinate is the local mass of a nonzero valuation. -/
theorem infinitePi_occupiedEvent (i : ι) :
    Measure.infinitePi μ (occupiedEvent i) = μ i {0}ᶜ :=
  infinitePi_localEvent μ (fun _ => ({0}ᶜ : Set ℕ)) i

/-- The occupancy events are independent. -/
theorem iIndepSet_occupiedEvent :
    ProbabilityTheory.iIndepSet (fun i : ι => occupiedEvent i) (Measure.infinitePi μ) :=
  iIndepSet_localEvent μ (fun _ => ({0}ᶜ : Set ℕ))

theorem iIndepSet_occupiedEvent_comp (e : ℕ ≃ ι) :
    ProbabilityTheory.iIndepSet (fun n : ℕ => occupiedEvent (e n)) (Measure.infinitePi μ) :=
  iIndepSet_localEvent_comp μ (fun _ => ({0}ᶜ : Set ℕ)) e

theorem tsum_infinitePi_occupiedEvent_comp (e : ℕ ≃ ι) :
    (∑' n : ℕ, Measure.infinitePi μ (occupiedEvent (e n))) = ∑' i : ι, μ i {0}ᶜ :=
  tsum_infinitePi_localEvent_comp μ (fun _ => ({0}ᶜ : Set ℕ)) e

/-- **Divergent occupancy masses force infinite occupancy.** -/
theorem measure_infiniteOccupancy_eq_one (e : ℕ ≃ ι)
    (hdiv : (∑' i : ι, μ i {0}ᶜ) = ∞) :
    Measure.infinitePi μ {k : ∀ _ : ι, ℕ | (occupiedSet k).Infinite} = 1 :=
  measure_infiniteHit_eq_one μ (fun _ => ({0}ᶜ : Set ℕ)) e hdiv

/-- Under summable occupancy masses the infinite-occupancy event is null. -/
theorem measure_infiniteOccupancy_eq_zero (e : ℕ ≃ ι)
    (hconv : (∑' i : ι, μ i {0}ᶜ) ≠ ∞) :
    Measure.infinitePi μ {k : ∀ _ : ι, ℕ | (occupiedSet k).Infinite} = 0 :=
  measure_infiniteHit_eq_zero μ (fun _ => ({0}ᶜ : Set ℕ)) e hconv

/-- **Summable occupancy masses force finite occupancy.** -/
theorem measure_finiteOccupancy_eq_one (e : ℕ ≃ ι)
    (hconv : (∑' i : ι, μ i {0}ᶜ) ≠ ∞) :
    Measure.infinitePi μ {k : ∀ _ : ι, ℕ | (occupiedSet k).Finite} = 1 :=
  measure_finiteHit_eq_one μ (fun _ => ({0}ᶜ : Set ℕ)) e hconv

/-- **The occupancy dichotomy.** -/
theorem measure_infiniteOccupancy_eq_one_iff (e : ℕ ≃ ι) :
    Measure.infinitePi μ {k : ∀ _ : ι, ℕ | (occupiedSet k).Infinite} = 1 ↔
      (∑' i : ι, μ i {0}ᶜ) = ∞ :=
  measure_infiniteHit_eq_one_iff μ (fun _ => ({0}ᶜ : Set ℕ)) e

/-- The complementary form of the occupancy dichotomy. -/
theorem measure_finiteOccupancy_eq_one_iff (e : ℕ ≃ ι) :
    Measure.infinitePi μ {k : ∀ _ : ι, ℕ | (occupiedSet k).Finite} = 1 ↔
      (∑' i : ι, μ i {0}ᶜ) ≠ ∞ :=
  measure_finiteHit_eq_one_iff μ (fun _ => ({0}ᶜ : Set ℕ)) e

theorem ae_infinite_occupiedSet (e : ℕ ≃ ι) (hdiv : (∑' i : ι, μ i {0}ᶜ) = ∞) :
    ∀ᵐ k ∂(Measure.infinitePi μ), (occupiedSet k).Infinite :=
  ae_infinite_localHitSet μ (fun _ => ({0}ᶜ : Set ℕ)) e hdiv

theorem ae_finite_occupiedSet (e : ℕ ≃ ι) (hconv : (∑' i : ι, μ i {0}ᶜ) ≠ ∞) :
    ∀ᵐ k ∂(Measure.infinitePi μ), (occupiedSet k).Finite :=
  ae_finite_localHitSet μ (fun _ => ({0}ᶜ : Set ℕ)) e hconv

/-- **A finitely occupied configuration is invisible.**  When the occupancy masses diverge, each
single configuration with a finite occupied set is null — in particular the empty one. -/
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
