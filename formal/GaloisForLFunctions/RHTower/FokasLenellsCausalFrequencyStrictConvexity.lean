import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyObservation
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyRecurrence
import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedHigherSpectrum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
open Complex Set Filter
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false

private theorem hilbert_unit_ball_pair_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hxy : ‖x + y‖ = 2) : x = y := by
  have hx2 : ‖x‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ (norm_nonneg x) zero_le_one).mpr hx
  have hy2 : ‖y‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ (norm_nonneg y) zero_le_one).mpr hy
  have hp := parallelogram_law_with_norm ℂ x y
  rw [hxy] at hp
  have hzero : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

private theorem orbit_constant_closure {X : Type*} [TopologicalSpace X]
    (w : ℕ → X) (g : X → ℝ) (hg : Continuous g) (c : ℝ)
    (hc : ∀ n, g (w n) = c) {p : X} (hp : p ∈ closure (Set.range w)) : g p = c := by
  apply closure_minimal ?_ (isClosed_eq hg continuous_const) hp
  rintro _ ⟨n, rfl⟩
  exact hc n

section ObservedOrbit
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
local instance frequencyStrictConvexGenericEndRing : NormedRing (E →L[ℂ] E) :=
  ContinuousLinearMap.toNormedRing

private theorem compact_observed_pair_norm_ne_two
    (T : E →L[ℂ] E) (q : E →L[ℂ] H)
    (hq : ∀ w, ‖q w‖ ≤ ‖w‖) (hiq : Function.Injective q)
    (hobs : ∀ w : E, ∀ C : ℝ, 0 ≤ C →
      (∀ n : ℕ, ‖q ((T ^ n) w)‖ ≤ C) → ‖w‖ ≤ C)
    (u v : E) (huv : u ≠ v)
    (hu : ∀ n : ℕ, ‖(T ^ n) u‖ = 1)
    (hv : ∀ n : ℕ, ‖(T ^ n) v‖ = 1)
    (hd : ∀ n : ℕ, ‖(T ^ n) u - (T ^ n) v‖ = ‖u - v‖)
    (hku : IsCompact (closure (Set.range (fun n : ℕ => (T ^ n) u))))
    (hkv : IsCompact (closure (Set.range (fun n : ℕ => (T ^ n) v)))) :
    ‖u + v‖ ≠ 2 := by
  intro heq
  let w : ℕ → E × E := fun n => ((T ^ n) u, (T ^ n) v)
  let K : Set (E × E) := closure (Set.range w)
  have hKsub : K ⊆ (closure (Set.range (fun n : ℕ => (T ^ n) u))) ×ˢ
      (closure (Set.range (fun n : ℕ => (T ^ n) v))) := by
    apply closure_minimal ?_ (hku.isClosed.prod hkv.isClosed)
    rintro _ ⟨n, rfl⟩
    exact ⟨subset_closure (Set.mem_range_self n), subset_closure (Set.mem_range_self n)⟩
  have hK : IsCompact K := (hku.prod hkv).of_isClosed_subset isClosed_closure hKsub
  have hKne : K.Nonempty := ⟨w 0, subset_closure ⟨0, rfl⟩⟩
  let f : E × E → ℝ := fun p => ‖q (p.1 + p.2)‖
  have hf : Continuous f := by fun_prop
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hKne hf.continuousOn
  have hpU : ‖p.1‖ = 1 :=
    orbit_constant_closure w (fun z => ‖z.1‖) (by fun_prop) 1 (fun n => hu n) hp
  have hpV : ‖p.2‖ = 1 :=
    orbit_constant_closure w (fun z => ‖z.2‖) (by fun_prop) 1 (fun n => hv n) hp
  have hpD : ‖p.1 - p.2‖ = ‖u - v‖ :=
    orbit_constant_closure w (fun z => ‖z.1 - z.2‖) (by fun_prop) ‖u - v‖
      (fun n => hd n) hp
  have hqU : ‖q p.1‖ ≤ 1 := (hq p.1).trans hpU.le
  have hqV : ‖q p.2‖ ≤ 1 := (hq p.2).trans hpV.le
  have hf_le : f p ≤ 2 := by
    dsimp only [f]
    rw [map_add]
    exact (norm_add_le _ _).trans (by linarith)
  have hfn : ∀ n : ℕ, ‖q ((T ^ n) (u + v))‖ ≤ f p := by
    intro n
    have hm := hmax (subset_closure (Set.mem_range_self n))
    change ‖q ((T ^ n) u + (T ^ n) v)‖ ≤ f p at hm
    simpa only [map_add] using hm
  have hsum := hobs (u + v) (f p) (norm_nonneg _) hfn
  have hf_eq : f p = 2 := le_antisymm hf_le (by simpa only [heq] using hsum)
  have hqsum : ‖q p.1 + q p.2‖ = 2 := by
    rw [← map_add]
    exact hf_eq
  have hp_eq : p.1 = p.2 := hiq (hilbert_unit_ball_pair_eq _ _ hqU hqV hqsum)
  have hz : ‖u - v‖ = 0 := by simpa only [hp_eq, sub_self, norm_zero] using hpD.symm
  exact huv (sub_eq_zero.mp (norm_eq_zero.mp hz))
end ObservedOrbit
local instance frequencyStrictConvexActualEndRing : NormedRing
    (causalBoundedChain →L[ℂ] causalBoundedChain) := ContinuousLinearMap.toNormedRing

private theorem chain_norm_from_shift_zero (u : causalBoundedChain) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, ‖causalBoundedChainCoordinate 0 ((causalBoundedChainShift ^ n) u)‖ ≤ C) :
    ‖u‖ ≤ C := by
  change ‖u.val‖ ≤ C
  apply lp.norm_le_of_forall_le hC
  intro n
  change ‖causalBoundedChainCoordinate n u‖ ≤ C
  simpa only [causalBoundedChainShift_pow_coordinate, Nat.zero_add] using h n

/-- The completed frequency carrier is strictly convex in its genuine chain
norm: distinct unit vectors cannot have a unit-norm midpoint. -/
theorem causalFrequencySpace_strictConvex (b : ℝ) :
    StrictConvexSpace ℝ (causalFrequencySpace b) := by
  apply StrictConvexSpace.of_norm_add_ne_two
  intro u v hu hv huv
  apply compact_observed_pair_norm_ne_two causalBoundedChainShift
    (causalBoundedChainCoordinate 0) (causalBoundedChainCoordinate_norm_le 0)
    causalBoundedChainCoordinate_zero_injective chain_norm_from_shift_zero
    u.val v.val (fun h => huv (Subtype.ext h))
    (fun n => (causalBoundedChainShift_pow_frequency_norm b n u).trans hu)
    (fun n => (causalBoundedChainShift_pow_frequency_norm b n v).trans hv)
    ?_ (causalFrequencySpace_compact_orbit b u) (causalFrequencySpace_compact_orbit b v)
  intro n
  have h := causalBoundedChainShift_pow_frequency_norm b n (u - v)
  change ‖(causalBoundedChainShift ^ n) (u.val - v.val)‖ = ‖u.val - v.val‖ at h
  simpa only [map_sub] using h

end RHTower.FokasLenells
