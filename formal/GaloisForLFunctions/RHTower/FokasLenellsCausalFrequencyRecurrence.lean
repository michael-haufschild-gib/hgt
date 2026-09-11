import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyProjection
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
open Complex Set Filter Topology
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section Generic
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
local instance frequencyRecurrenceGenericEndRing : NormedRing (E →L[ℂ] E) :=
  ContinuousLinearMap.toNormedRing

private theorem phase_model (T : E →L[ℂ] E) (v : I → E) (ρ : I → Circle)
    (he : ∀ i n, (T ^ n) (v i) = (ρ i : ℂ) ^ n • v i)
    {u : E} (hu : u ∈ Submodule.span ℂ (Set.range v)) :
    ∃ F : (I → Circle) → E, Continuous F ∧ F 1 = u ∧
      ∀ n : ℕ, F (ρ ^ n) = (T ^ n) u := by
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    refine ⟨fun g => (g i : ℂ) • v i,
      (continuous_subtype_val.comp (continuous_apply i)).smul continuous_const, ?_, ?_⟩
    · simp only [Pi.one_apply, Circle.coe_one, one_smul]
    · intro n
      simpa only [Pi.pow_apply, Circle.coe_pow] using (he i n).symm
  | zero =>
    exact ⟨fun _ => 0, continuous_const, rfl, fun n => ((T ^ n).map_zero).symm⟩
  | add a b ha hb ia ib =>
    obtain ⟨F, hF, hF1, hFn⟩ := ia
    obtain ⟨G, hG, hG1, hGn⟩ := ib
    refine ⟨fun g => F g + G g, hF.add hG, ?_, ?_⟩
    · change F 1 + G 1 = a + b
      rw [hF1, hG1]
    · intro n
      change F (ρ ^ n) + G (ρ ^ n) = (T ^ n) (a + b)
      rw [hFn, hGn, map_add]
  | smul c a ha ih =>
    obtain ⟨F, hF, hF1, hFn⟩ := ih
    refine ⟨fun g => c • F g, continuous_const.smul hF, ?_, ?_⟩
    · change c • F 1 = c • a
      rw [hF1]
    · intro n
      change c • F (ρ ^ n) = (T ^ n) (c • a)
      rw [hFn, map_smul]

private theorem phase_span_recurrent (T : E →L[ℂ] E) (v : I → E) (ρ : I → Circle)
    (he : ∀ i n, (T ^ n) (v i) = (ρ i : ℂ) ^ n • v i)
    {u : E} (hu : u ∈ Submodule.span ℂ (Set.range v)) :
    MapClusterPt u atTop (fun n : ℕ => (T ^ n) u) := by
  obtain ⟨F, hF, hF1, hFn⟩ := phase_model T v ρ he hu
  have h := (mapClusterPt_one_atTop_pow ρ).continuousAt_comp hF.continuousAt
  simpa only [Function.comp_def, hF1, hFn] using h

private theorem phase_span_precompact (T : E →L[ℂ] E) (v : I → E) (ρ : I → Circle)
    (he : ∀ i n, (T ^ n) (v i) = (ρ i : ℂ) ^ n • v i)
    {u : E} (hu : u ∈ Submodule.span ℂ (Set.range v)) :
    TotallyBounded (Set.range (fun n : ℕ => (T ^ n) u)) := by
  obtain ⟨F, hF, hF1, hFn⟩ := phase_model T v ρ he hu
  exact (isCompact_range hF).totallyBounded.subset (by
    rintro w ⟨n, rfl⟩
    exact ⟨ρ ^ n, hFn n⟩)

private theorem power_dist_le (T : E →L[ℂ] E)
    (ht : ∀ n u, ‖(T ^ n) u‖ ≤ ‖u‖) (n : ℕ) (u v : E) :
    dist ((T ^ n) u) ((T ^ n) v) ≤ dist u v := by
  simpa only [dist_eq_norm, ← map_sub] using ht n (u - v)

private theorem closure_recurrent (T : E →L[ℂ] E)
    (ht : ∀ n u, ‖(T ^ n) u‖ ≤ ‖u‖) (A : Set E)
    (ha : ∀ v ∈ A, MapClusterPt v atTop (fun n : ℕ => (T ^ n) v))
    {u : E} (hu : u ∈ closure A) :
    MapClusterPt u atTop (fun n : ℕ => (T ^ n) u) := by
  apply mapClusterPt_atTop_iff_forall_mem_closure.mpr
  intro N
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨v, hv, huv⟩ := Metric.mem_closure_iff.mp hu (ε / 3) (by linarith)
  have hr := mapClusterPt_atTop_iff_forall_mem_closure.mp (ha v hv) N
  obtain ⟨w, hw, hvw⟩ := Metric.mem_closure_iff.mp hr (ε / 3) (by linarith)
  obtain ⟨n, hn, hnv⟩ := hw
  refine ⟨(T ^ n) u, ⟨n, hn, rfl⟩, ?_⟩
  have hvn : dist v ((T ^ n) v) < ε / 3 := by simpa only [hnv] using hvw
  have hpow := power_dist_le T ht n v u
  have htri := dist_triangle u v ((T ^ n) u)
  have htri' := dist_triangle v ((T ^ n) v) ((T ^ n) u)
  rw [dist_comm v u] at hpow
  linarith

private theorem closure_precompact (T : E →L[ℂ] E)
    (ht : ∀ n u, ‖(T ^ n) u‖ ≤ ‖u‖) (A : Set E)
    (ha : ∀ v ∈ A, TotallyBounded (Set.range (fun n : ℕ => (T ^ n) v)))
    {u : E} (hu : u ∈ closure A) :
    TotallyBounded (Set.range (fun n : ℕ => (T ^ n) u)) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨v, hv, huv⟩ := Metric.mem_closure_iff.mp hu (ε / 2) (by linarith)
  obtain ⟨t, htfin, hcover⟩ := Metric.totallyBounded_iff.mp (ha v hv) (ε / 2) (by linarith)
  refine ⟨t, htfin, ?_⟩
  rintro w ⟨n, rfl⟩
  have hn := hcover (show (T ^ n) v ∈ Set.range (fun k : ℕ => (T ^ k) v) from ⟨n, rfl⟩)
  simp only [Set.mem_iUnion, Metric.mem_ball] at hn ⊢
  obtain ⟨y, hy, hvy⟩ := hn
  refine ⟨y, hy, ?_⟩
  have hpow := power_dist_le T ht n u v
  have htri := dist_triangle ((T ^ n) u) ((T ^ n) v) y
  linarith

private theorem recurrent_norm_preserved (T : E →L[ℂ] E)
    (ht : ∀ n u, ‖(T ^ n) u‖ ≤ ‖u‖) (u : E)
    (hu : MapClusterPt u atTop (fun n : ℕ => (T ^ n) u)) :
    ‖T u‖ = ‖u‖ := by
  apply le_antisymm
  · simpa only [pow_one] using ht 1 u
  · have hc : IsClosed {v : E | ‖v‖ ≤ ‖T u‖} := isClosed_le continuous_norm continuous_const
    apply hc.mem_of_mapClusterPt hu
    apply Filter.eventually_atTop.mpr
    refine ⟨1, ?_⟩
    intro n hn
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
    have hp : n = k + 1 := by omega
    simp only [Set.mem_setOf_eq, hp, pow_succ, mul_apply_eq_comp]
    exact ht k (T u)
end Generic
local instance frequencyRecurrenceChainComplete : CompleteSpace causalBoundedChain :=
  causalBoundedChain_complete

local instance frequencyRecurrenceActualEndRing : NormedRing
    (causalBoundedChain →L[ℂ] causalBoundedChain) := ContinuousLinearMap.toNormedRing

private def unit_phase (b ω : ℝ) : Circle :=
  ⟨(causalUnitBoundaryRate b ω).val,
    mem_sphere_zero_iff_norm.mpr (norm_causalUnitBoundaryRate b ω)⟩

private theorem core_recurrent (b : ℝ) (v : causalBoundedChain)
    (hv : v ∈ causalFrequencyCore b) :
    MapClusterPt v atTop (fun n : ℕ => (causalBoundedChainShift ^ n) v) := by
  exact phase_span_recurrent causalBoundedChainShift (causalBoundedUnitEigenchain b)
    (unit_phase b) (fun ω n => causalBoundedChainShift_pow_unitEigenchain b ω n) hv

private theorem core_precompact (b : ℝ) (v : causalBoundedChain)
    (hv : v ∈ causalFrequencyCore b) :
    TotallyBounded (Set.range (fun n : ℕ => (causalBoundedChainShift ^ n) v)) := by
  exact phase_span_precompact causalBoundedChainShift (causalBoundedUnitEigenchain b)
    (unit_phase b) (fun ω n => causalBoundedChainShift_pow_unitEigenchain b ω n) hv

/-- Every vector in the actual completed frequency span returns arbitrarily close
in bounded-chain norm at arbitrarily late integer derivative-shift times. -/
theorem causalFrequencySpace_recurrent (b : ℝ) (u : causalFrequencySpace b) :
    MapClusterPt u.val atTop (fun n : ℕ => (causalBoundedChainShift ^ n) u.val) := by
  exact closure_recurrent causalBoundedChainShift causalBoundedChainShift_pow_norm_le
    (causalFrequencyCore b : Set causalBoundedChain) (core_recurrent b) u.property

/-- The closure of every actual completed-frequency shift orbit is compact in
bounded-chain norm; no summability representation of the vector is assumed. -/
theorem causalFrequencySpace_compact_orbit (b : ℝ) (u : causalFrequencySpace b) :
    IsCompact (closure (Set.range (fun n : ℕ => (causalBoundedChainShift ^ n) u.val))) := by
  exact (closure_precompact causalBoundedChainShift causalBoundedChainShift_pow_norm_le
    (causalFrequencyCore b : Set causalBoundedChain) (core_precompact b) u.property).closure.isCompact_of_isClosed
      isClosed_closure

/-- The genuine derivative shift preserves the norm of every vector in the
actual completed frequency span exactly. -/
theorem causalBoundedChainShift_frequency_norm (b : ℝ) (u : causalFrequencySpace b) :
    ‖causalBoundedChainShift u.val‖ = ‖u‖ := by
  exact recurrent_norm_preserved causalBoundedChainShift causalBoundedChainShift_pow_norm_le
    u.val (causalFrequencySpace_recurrent b u)

end RHTower.FokasLenells
