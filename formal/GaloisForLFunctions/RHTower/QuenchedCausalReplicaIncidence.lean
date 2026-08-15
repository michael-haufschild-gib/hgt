import GaloisForLFunctions.RHTower.CircuitTraceLaw
import GaloisForLFunctions.RHTower.CircuitSoftCausalReporter
import GaloisForLFunctions.RHTower.LocalCircuitHeapGreenReporter
import GaloisForLFunctions.HTGeometry.QuenchedReplicaLimits

/-!
# Exact quenched replica incidence for a shared circuit source

Replicating only the candidate preparations, against one shared source of endpoints, produces an
incidence event on the product of the source with independent copies of the heap law.  Conditioning
on the source makes the replicated event a product of identical causal success events, so its
probability is the replica power of the causal accessibility, and its total mass is the quenched
causal replica mass.

Calibrating the accessibility below by the geometric weight of a shortest successful heap turns the
replica mass into a bound for the source mass of every low-complexity sector; the same calibration
applies to the soft causal reporter, whose replica power is Lipschitz with constant the replica
order over the softening scale.
-/

open MeasureTheory

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

section ReplicaIncidence

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- The event that every replicated circuit heap already succeeds at the shared endpoint. -/
def replicaIncidenceEvent (independent : α → α → Prop) (S : Trace independent → Set X)
    (x : Ω → X) (r : ℕ) : Set (Ω × (Fin r → Trace independent)) :=
  {p | ∀ j, p.2 j ∈ causalSuccessEvent independent S (x p.1)}

/-- The sources at which a fixed heap already succeeds form a measurable set. -/
theorem measurableSet_causalSuccessPreimage (independent : α → α → Prop)
    {S : Trace independent → Set X} (hS : ∀ u, MeasurableSet (S u)) {x : Ω → X}
    (hx : Measurable x) (T : Trace independent) :
    MeasurableSet {H : Ω | T ∈ causalSuccessEvent independent S (x H)} := by
  have hset : {H : Ω | T ∈ causalSuccessEvent independent S (x H)} =
      x ⁻¹' (⋃ u ∈ tracePrefixSet independent T, S u) := by
    ext H
    constructor
    · rintro ⟨u, hu, hxu⟩
      exact Set.mem_biUnion (show u ∈ tracePrefixSet independent T from hu) hxu
    · intro hH
      obtain ⟨u, hu, hxu⟩ := Set.mem_iUnion₂.1 hH
      exact ⟨u, hu, hxu⟩
  rw [hset]
  exact hx (MeasurableSet.biUnion (tracePrefixSet_finite independent T).countable
    fun u _ => hS u)

/-- The replicated incidence event is measurable in the product structure. -/
theorem measurableSet_replicaIncidenceEvent (independent : α → α → Prop)
    {S : Trace independent → Set X} (hS : ∀ u, MeasurableSet (S u)) {x : Ω → X}
    (hx : Measurable x) (r : ℕ) :
    MeasurableSet (replicaIncidenceEvent independent S x r) := by
  have hEq : replicaIncidenceEvent independent S x r =
      ⋂ j : Fin r, ⋃ T : Trace independent,
        ({H : Ω | T ∈ causalSuccessEvent independent S (x H)} ×ˢ
          ((fun t : Fin r → Trace independent => t j) ⁻¹' {T})) := by
    ext p
    simp only [replicaIncidenceEvent, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion,
      Set.mem_prod, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hp j
      exact ⟨p.2 j, hp j, rfl⟩
    · intro hp j
      obtain ⟨T, h1, h2⟩ := hp j
      rw [h2]
      exact h1
  rw [hEq]
  refine MeasurableSet.iInter fun j => MeasurableSet.iUnion fun T => ?_
  exact (measurableSet_causalSuccessPreimage independent hS hx T).prod
    (measurable_pi_apply j (measurableSet_singleton T))

/-- **Exact quenched replica incidence.**  The mass of the replicated incidence event under the
source law times independent heap laws is the replica power of the causal accessibility, integrated
over the source. -/
theorem measure_replicaIncidenceEvent (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} (hS : ∀ u, MeasurableSet (S u)) {x : Ω → X}
    (hx : Measurable x) (ρ : Measure Ω) [SFinite ρ] (r : ℕ) :
    (ρ.prod (Measure.pi fun _ : Fin r => traceLaw independent z))
        (replicaIncidenceEvent independent S x r) =
      ∫⁻ H, ENNReal.ofReal (causalAccessibility independent z S (x H)) ^ r ∂ρ := by
  haveI : IsProbabilityMeasure (traceLaw independent z) :=
    isProbabilityMeasure_traceLaw independent hsymm Δ hdegree hz0 hz
  rw [Measure.prod_apply (measurableSet_replicaIncidenceEvent independent hS hx r)]
  refine lintegral_congr fun H => ?_
  have hpre : Prod.mk H ⁻¹' replicaIncidenceEvent independent S x r =
      Set.univ.pi fun _ : Fin r => causalSuccessEvent independent S (x H) := by
    ext t
    simp only [Set.mem_preimage, replicaIncidenceEvent, Set.mem_setOf_eq, Set.mem_pi,
      Set.mem_univ, forall_const]
  rw [hpre, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    traceLaw_causalSuccessEvent independent hsymm Δ hdegree hz0 hz]

/-- The causal accessibility along a measurable endpoint map is measurable. -/
theorem measurable_causalAccessibility_comp (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} (hS : ∀ u, MeasurableSet (S u)) {x : Ω → X}
    (hx : Measurable x) :
    Measurable fun H => causalAccessibility independent z S (x H) := by
  classical
  have hform : ∀ H : Ω, traceLaw independent z (causalSuccessEvent independent S (x H)) =
      ∑' T : Trace independent,
        Set.indicator {H' : Ω | T ∈ causalSuccessEvent independent S (x H')}
          (fun _ => ENNReal.ofReal (traceWeight independent z T)) H := by
    intro H
    rw [traceLaw_apply, tsum_subtype (causalSuccessEvent independent S (x H))
      fun T => ENNReal.ofReal (traceWeight independent z T)]
    refine tsum_congr fun T => ?_
    by_cases hT : T ∈ causalSuccessEvent independent S (x H)
    · rw [Set.indicator_of_mem hT, Set.indicator_of_mem (show H ∈ _ from hT)]
    · rw [Set.indicator_of_notMem hT, Set.indicator_of_notMem (show H ∉ _ from hT)]
  have hmeasENN : Measurable fun H : Ω =>
      traceLaw independent z (causalSuccessEvent independent S (x H)) := by
    rw [funext hform]
    exact Measurable.tsum fun T =>
      measurable_const.indicator (measurableSet_causalSuccessPreimage independent hS hx T)
  have hpoint : ∀ H : Ω, causalAccessibility independent z S (x H) =
      (traceLaw independent z (causalSuccessEvent independent S (x H))).toReal := by
    intro H
    rw [traceLaw_causalSuccessEvent independent hsymm Δ hdegree hz0 hz,
      ENNReal.toReal_ofReal
        (causalAccessibility_nonneg independent hsymm Δ hdegree hz0 hz S (x H))]
  rw [funext hpoint]
  exact hmeasENN.ennreal_toReal

theorem integrable_causalAccessibility_pow (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} (hS : ∀ u, MeasurableSet (S u)) {x : Ω → X}
    (hx : Measurable x) (ρ : Measure Ω) [IsFiniteMeasure ρ] (r : ℕ) :
    Integrable (fun H => causalAccessibility independent z S (x H) ^ r) ρ := by
  refine Integrable.of_bound
    ((measurable_causalAccessibility_comp independent hsymm Δ hdegree hz0 hz hS hx).pow_const
      r).aestronglyMeasurable 1 ?_
  filter_upwards with H
  rw [Real.norm_of_nonneg
    (pow_nonneg (causalAccessibility_nonneg independent hsymm Δ hdegree hz0 hz S (x H)) r)]
  exact pow_le_one₀ (causalAccessibility_nonneg independent hsymm Δ hdegree hz0 hz S (x H))
    (causalAccessibility_le_one independent hsymm Δ hdegree hz0 hz S (x H))

/-- **Exact quenched replica incidence, real form.**  The quenched causal replica mass is the
probability of the replicated incidence event. -/
theorem measureReal_replicaIncidenceEvent (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} (hS : ∀ u, MeasurableSet (S u)) {x : Ω → X}
    (hx : Measurable x) (ρ : Measure Ω) [IsProbabilityMeasure ρ] (r : ℕ) :
    (ρ.prod (Measure.pi fun _ : Fin r => traceLaw independent z)).real
        (replicaIncidenceEvent independent S x r) =
      quenchedReplicaMass ρ (fun H => causalAccessibility independent z S (x H)) r := by
  have hmeas := measure_replicaIncidenceEvent independent hsymm Δ hdegree hz0 hz hS hx ρ r
  have hpow : ∀ H : Ω,
      ENNReal.ofReal (causalAccessibility independent z S (x H)) ^ r =
        ENNReal.ofReal (causalAccessibility independent z S (x H) ^ r) := fun H =>
    (ENNReal.ofReal_pow
      (causalAccessibility_nonneg independent hsymm Δ hdegree hz0 hz S (x H)) r).symm
  rw [funext hpow] at hmeas
  rw [measureReal_def, hmeas, ← ofReal_integral_eq_lintegral_ofReal
    (integrable_causalAccessibility_pow independent hsymm Δ hdegree hz0 hz hS hx ρ r)
    (Filter.Eventually.of_forall fun H =>
      pow_nonneg (causalAccessibility_nonneg independent hsymm Δ hdegree hz0 hz S (x H)) r),
    ENNReal.toReal_ofReal (integral_nonneg fun H =>
      pow_nonneg (causalAccessibility_nonneg independent hsymm Δ hdegree hz0 hz S (x H)) r)]
  rfl

/-- **Growing-replica complete-circuit bound.**  The source mass of the sector whose endpoint is
reachable within depth `s` is at most the quenched replica mass discounted by the replicated
geometric weight of that depth. -/
theorem measureReal_heapAccessible_le_quenchedReplicaMass (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} (hS : ∀ u, MeasurableSet (S u)) {x : Ω → X}
    (hx : Measurable x) (ρ : Measure Ω) [IsProbabilityMeasure ρ] (s r : ℕ) :
    ρ.real (x ⁻¹' heapAccessible (traceLen independent) S s) ≤
      ((z ^ s)⁻¹) ^ r *
        quenchedReplicaMass ρ (fun H => causalAccessibility independent z S (x H)) r := by
  refine measureReal_le_quenchedReplicaMass ρ
    (fun H => causalAccessibility_nonneg independent hsymm Δ hdegree hz0.le hz S (x H))
    (hx (measurableSet_heapAccessible hS s)) (pow_pos hz0 s) ?_ r
    (integrable_causalAccessibility_pow independent hsymm Δ hdegree hz0.le hz hS hx ρ r)
  intro H hH
  obtain ⟨u, hu, hxu⟩ : ∃ u : Trace independent, traceLen independent u ≤ s ∧ x H ∈ S u := by
    simpa only [Set.mem_preimage, heapAccessible, Set.mem_iUnion, Set.mem_setOf_eq,
      exists_prop] using hH
  calc z ^ s ≤ z ^ traceLen independent u := pow_le_pow_of_le_one hz0.le hz1 hu
    _ ≤ causalAccessibility independent z S (x H) :=
        pow_le_causalAccessibility independent hsymm Δ hdegree hz0.le hz hxu

/-- **Certificate-exponent form.**  The complete-circuit bound is exactly the exponential of the
negative depth-`s` certificate exponent at replica order `r`. -/
theorem measureReal_heapAccessible_le_exp (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) (hz : 2 ^ Δ * z < 1)
    {S : Trace independent → Set X} (hS : ∀ u, MeasurableSet (S u)) {x : Ω → X}
    (hx : Measurable x) (ρ : Measure Ω) [IsProbabilityMeasure ρ] (s : ℕ) {r : ℕ} (hr : 0 < r)
    (hZ : 0 < quenchedReplicaMass ρ (fun H => causalAccessibility independent z S (x H)) r) :
    ρ.real (x ⁻¹' heapAccessible (traceLen independent) S s) ≤
      Real.exp (-((r : ℝ) *
        (quenchedReplicaAction ρ (fun H => causalAccessibility independent z S (x H)) r -
          (s : ℝ) * Real.log z⁻¹))) := by
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  have hbase := measureReal_heapAccessible_le_quenchedReplicaMass independent hsymm Δ hdegree
    hz0 hz1 hz hS hx ρ s r
  have haction := quenchedReplicaAction_eq ρ
    (fun H => causalAccessibility independent z S (x H)) hZ
  set Z : ℝ := quenchedReplicaMass ρ (fun H => causalAccessibility independent z S (x H)) r
    with hZdef
  have hweight : Real.exp (((r : ℝ) * (s : ℝ)) * Real.log z⁻¹) = ((z ^ s)⁻¹) ^ r := by
    rw [mul_assoc, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hz0), inv_pow]
  have hexp : Real.exp (-((r : ℝ) *
      (quenchedReplicaAction ρ (fun H => causalAccessibility independent z S (x H)) r -
        (s : ℝ) * Real.log z⁻¹))) = ((z ^ s)⁻¹) ^ r * Z := by
    rw [haction]
    rw [show -((r : ℝ) * (-((r : ℝ)⁻¹ * Real.log Z) - (s : ℝ) * Real.log z⁻¹)) =
        ((r : ℝ) * (s : ℝ)) * Real.log z⁻¹ + Real.log Z by field_simp; ring]
    rw [Real.exp_add, Real.exp_log hZ, hweight]
  rw [hexp]
  exact hbase

end ReplicaIncidence

section SoftReplica

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
variable {X Ω : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable [MeasurableSpace Ω]

/-- Unit-bounded bases make the power map Lipschitz with constant the exponent. -/
theorem abs_pow_sub_pow_le_of_unit {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (r : ℕ) : |u ^ r - v ^ r| ≤ (r : ℝ) * |u - v| := by
  induction r with
  | zero => simp
  | succ n ih =>
    have hstep : u ^ (n + 1) - v ^ (n + 1) = u ^ n * (u - v) + v * (u ^ n - v ^ n) := by ring
    have hun : |u ^ n| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hu0 n)]
      exact pow_le_one₀ hu0 hu1
    have hvn : |v| ≤ 1 := by rw [abs_of_nonneg hv0]; exact hv1
    calc |u ^ (n + 1) - v ^ (n + 1)| = |u ^ n * (u - v) + v * (u ^ n - v ^ n)| := by rw [hstep]
      _ ≤ |u ^ n * (u - v)| + |v * (u ^ n - v ^ n)| := abs_add_le _ _
      _ = |u ^ n| * |u - v| + |v| * |u ^ n - v ^ n| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * |u - v| + 1 * ((n : ℝ) * |u - v|) := by
          have hA : |u ^ n| * |u - v| ≤ 1 * |u - v| :=
            mul_le_mul_of_nonneg_right hun (abs_nonneg _)
          have hB : |v| * |u ^ n - v ^ n| ≤ 1 * ((n : ℝ) * |u - v|) :=
            mul_le_mul hvn ih (abs_nonneg _) zero_le_one
          linarith
      _ = ((n : ℝ) + 1) * |u - v| := by ring
      _ = ((n + 1 : ℕ) : ℝ) * |u - v| := by push_cast; ring

/-- The soft causal reporter is Lipschitz with constant the reciprocal softening scale. -/
theorem lipschitzWith_softCausalReporter (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) {δ : ℝ} (hδ : 0 < δ)
    (B : Trace independent → Set X) :
    LipschitzWith (Real.toNNReal δ⁻¹) (softCausalReporter independent z δ B) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  calc |softCausalReporter independent z δ B a - softCausalReporter independent z δ B b|
      ≤ dist a b / δ :=
        abs_softCausalReporter_sub_le independent hsymm Δ hdegree hz0 hz hδ B a b
    _ = δ⁻¹ * dist a b := by field_simp

theorem measurable_softCausalReporter_comp (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) {δ : ℝ} (hδ : 0 < δ)
    (B : Trace independent → Set X) {x : Ω → X} (hx : Measurable x) :
    Measurable fun H => softCausalReporter independent z δ B (x H) :=
  ((lipschitzWith_softCausalReporter independent hsymm Δ hdegree hz0 hz hδ
    B).continuous.measurable).comp hx

theorem integrable_softCausalReporter_pow (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) {δ : ℝ} (hδ : 0 < δ)
    (B : Trace independent → Set X) {x : Ω → X} (hx : Measurable x)
    (ρ : Measure Ω) [IsFiniteMeasure ρ] (r : ℕ) :
    Integrable (fun H => softCausalReporter independent z δ B (x H) ^ r) ρ := by
  refine Integrable.of_bound
    ((measurable_softCausalReporter_comp independent hsymm Δ hdegree hz0 hz hδ B
      hx).pow_const r).aestronglyMeasurable 1 ?_
  filter_upwards with H
  rw [Real.norm_of_nonneg
    (pow_nonneg (softCausalReporter_nonneg independent hsymm Δ hdegree hz0 hz δ B (x H)) r)]
  exact pow_le_one₀ (softCausalReporter_nonneg independent hsymm Δ hdegree hz0 hz δ B (x H))
    (softCausalReporter_le_one independent hsymm Δ hdegree hz0 hz hδ B (x H))

/-- **Soft growing-replica complete-circuit bound.**  The same discounted bound holds with the
soft causal reporter in place of the causal accessibility. -/
theorem measureReal_heapAccessible_le_softReplicaMass (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) (hz : 2 ^ Δ * z < 1) {δ : ℝ} (hδ : 0 < δ)
    {B : Trace independent → Set X} (hB : ∀ u, MeasurableSet (B u)) {x : Ω → X}
    (hx : Measurable x) (ρ : Measure Ω) [IsProbabilityMeasure ρ] (s r : ℕ) :
    ρ.real (x ⁻¹' heapAccessible (traceLen independent) B s) ≤
      ((z ^ s)⁻¹) ^ r *
        quenchedReplicaMass ρ (fun H => softCausalReporter independent z δ B (x H)) r := by
  refine measureReal_le_quenchedReplicaMass ρ
    (fun H => softCausalReporter_nonneg independent hsymm Δ hdegree hz0.le hz δ B (x H))
    (hx (measurableSet_heapAccessible hB s)) (pow_pos hz0 s) ?_ r
    (integrable_softCausalReporter_pow independent hsymm Δ hdegree hz0.le hz hδ B hx ρ r)
  intro H hH
  obtain ⟨u, hu, hxu⟩ : ∃ u : Trace independent, traceLen independent u ≤ s ∧ x H ∈ B u := by
    simpa only [Set.mem_preimage, heapAccessible, Set.mem_iUnion, Set.mem_setOf_eq,
      exists_prop] using hH
  calc z ^ s ≤ z ^ traceLen independent u := pow_le_pow_of_le_one hz0.le hz1 hu
    _ ≤ causalAccessibility independent z B (x H) :=
        pow_le_causalAccessibility independent hsymm Δ hdegree hz0.le hz hxu
    _ ≤ softCausalReporter independent z δ B (x H) :=
        causalAccessibility_le_softCausalReporter independent hsymm Δ hdegree hz0.le hz hδ B (x H)

/-- **Dimension-free replica regularity.**  The replica power of the soft causal reporter is
Lipschitz with constant the replica order over the softening scale. -/
theorem abs_softCausalReporter_pow_sub_le (independent : α → α → Prop)
    (hsymm : ∀ x y, independent x y → independent y x) (Δ : ℕ)
    (hdegree : ∀ a, incidentEdgeCount independent a ≤ Δ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz : 2 ^ Δ * z < 1) {δ : ℝ} (hδ : 0 < δ)
    (B : Trace independent → Set X) (r : ℕ) (a b : X) :
    |softCausalReporter independent z δ B a ^ r - softCausalReporter independent z δ B b ^ r| ≤
      (r : ℝ) * (dist a b / δ) := by
  refine le_trans (abs_pow_sub_pow_le_of_unit
    (softCausalReporter_nonneg independent hsymm Δ hdegree hz0 hz δ B a)
    (softCausalReporter_le_one independent hsymm Δ hdegree hz0 hz hδ B a)
    (softCausalReporter_nonneg independent hsymm Δ hdegree hz0 hz δ B b)
    (softCausalReporter_le_one independent hsymm Δ hdegree hz0 hz hδ B b) r) ?_
  exact mul_le_mul_of_nonneg_left
    (abs_softCausalReporter_sub_le independent hsymm Δ hdegree hz0 hz hδ B a b)
    (Nat.cast_nonneg r)

end SoftReplica

end

end GaloisForLFunctions.RHTower
