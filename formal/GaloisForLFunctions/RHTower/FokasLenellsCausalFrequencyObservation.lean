import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyShift
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Order.Field
open Complex Set Filter Topology
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section GenericObservation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
local instance frequencyObservationGenericEndRing : NormedRing (E →L[ℂ] E) :=
  ContinuousLinearMap.toNormedRing

private theorem norm_pow_isometric_restriction (T : E →L[ℂ] E) (D : Submodule ℂ E)
    (e : D ≃ₗᵢ[ℂ] D) (he : ∀ u : D, (e u).val = T u.val) (n : ℕ) (u : D) :
    ‖(T ^ n) u.val‖ = ‖u‖ := by
  induction n generalizing u with
  | zero => simp only [pow_zero]; rfl
  | succ n ih =>
    have h₁ := congrArg (fun A : E →L[ℂ] E => A u.val) (pow_succ T n)
    have h₂ := congrArg (fun v : E => (T ^ n) v) (he u).symm
    exact (congrArg norm (h₁.trans h₂)).trans ((ih (e u)).trans (e.norm_map u))

private theorem compact_finite_norming (K : Set E) (hK : IsCompact K) (δ : ℝ)
    (hδ : 0 < δ) (hlow : ∀ v ∈ K, δ ≤ ‖v‖) :
    ∃ s : Finset (E →L[ℂ] ℂ), (∀ ℓ ∈ s, ‖ℓ‖ ≤ 1) ∧
      ∀ v ∈ K, δ ^ 2 / 4 ≤ ∑ ℓ ∈ s, ‖ℓ v‖ ^ 2 := by
  classical
  let J := {ℓ : E →L[ℂ] ℂ // ‖ℓ‖ ≤ 1}
  let U : J → Set E := fun ℓ => {v | δ / 2 < ‖ℓ.val v‖}
  have hU : ∀ ℓ : J, IsOpen (U ℓ) :=
    fun ℓ => isOpen_lt continuous_const ℓ.val.continuous.norm
  have hcover : K ⊆ ⋃ ℓ : J, U ℓ := by
    intro v hv
    obtain ⟨ℓ, hℓ, hval⟩ := exists_dual_vector'' ℂ v
    refine Set.mem_iUnion.mpr ⟨⟨ℓ, hℓ⟩, ?_⟩
    change δ / 2 < ‖ℓ v‖
    simp only [hval, norm_algebraMap', norm_norm]
    linarith [hlow v hv]
  obtain ⟨t, hcover'⟩ := hK.elim_finite_subcover U hU hcover
  refine ⟨t.image (fun ℓ : J => ℓ.val), ?_, ?_⟩
  · intro ℓ hℓ
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hℓ
    exact f.property
  · intro v hv
    have hmem := hcover' hv
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨ℓ, hℓ, hobs⟩ := hmem
    have hobs' : δ / 2 < ‖ℓ.val v‖ := hobs
    have hsq : δ ^ 2 / 4 ≤ ‖ℓ.val v‖ ^ 2 := by
      have hp : 0 ≤ (‖ℓ.val v‖ - δ / 2) * (‖ℓ.val v‖ + δ / 2) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith
    exact hsq.trans (Finset.single_le_sum (fun (f : E →L[ℂ] ℂ) _ => sq_nonneg ‖f v‖)
      (Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩))

private theorem le_cesaro_of_pointwise (f : ℕ → ℝ) (r : ℝ) (hf : ∀ n, r ≤ f n)
    (N : ℕ) (hN : 0 < N) : r ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f n := by
  have hs : (∑ _n ∈ Finset.range N, r) ≤ ∑ n ∈ Finset.range N, f n :=
    Finset.sum_le_sum (fun n hn => hf n)
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (N : ℝ)⁻¹ by positivity)
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hn, one_mul] using hm

private theorem sum_observation_means (s : Finset (E →L[ℂ] ℂ)) (x : ℕ → E) (N : ℕ) :
    (∑ ℓ ∈ s, (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖ℓ (x n)‖ ^ 2) =
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ∑ ℓ ∈ s, ‖ℓ (x n)‖ ^ 2 := by
  rw [← Finset.mul_sum, Finset.sum_comm]

private theorem finite_mean_square_floor (s : Finset (E →L[ℂ] ℂ)) (x : ℕ → E) (r : ℝ)
    (hf : ∀ n, r ≤ ∑ ℓ ∈ s, ‖ℓ (x n)‖ ^ 2)
    (hm : ∀ ℓ ∈ s, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ n ∈ Finset.range N, ‖ℓ (x n)‖ ^ 2) atTop (𝓝 0)) : r ≤ 0 := by
  have hsum : Tendsto (fun N : ℕ => ∑ ℓ ∈ s, (N : ℝ)⁻¹ *
      ∑ n ∈ Finset.range N, ‖ℓ (x n)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum s hm
  apply ge_of_tendsto hsum
  apply Filter.eventually_atTop.mpr
  refine ⟨1, ?_⟩
  intro N hN
  exact (le_cesaro_of_pointwise (fun n => ∑ ℓ ∈ s, ‖ℓ (x n)‖ ^ 2)
    r hf N (by omega)).trans_eq (sum_observation_means s x N).symm

private theorem orbit_finite_norming (x : ℕ → E) (r : ℝ) (hr : 0 ≤ r)
    (hcpt : IsCompact (closure (Set.range x))) (hnorm : ∀ n, ‖x n‖ = r) :
    ∃ s : Finset (E →L[ℂ] ℂ), (∀ ℓ ∈ s, ‖ℓ‖ ≤ 1) ∧
      ∀ n : ℕ, r ^ 2 / 4 ≤ ∑ ℓ ∈ s, ‖ℓ (x n)‖ ^ 2 := by
  classical
  by_cases hz : r = 0
  · subst r
    exact ⟨∅, by simp, by simp⟩
  have hpos : 0 < r := by
    by_contra h
    exact hz (by linarith)
  have hc : IsClosed {v : E | ‖v‖ = r} := isClosed_eq continuous_norm continuous_const
  have hs : Set.range x ⊆ {v : E | ‖v‖ = r} := by
    rintro v ⟨n, rfl⟩
    exact hnorm n
  have hall := hc.closure_subset_iff.mpr hs
  obtain ⟨s, hnorm, hfloor⟩ := compact_finite_norming (closure (Set.range x)) hcpt r hpos
    (fun v hv => (hall hv).symm.le)
  exact ⟨s, hnorm, fun n => hfloor _ (subset_closure ⟨n, rfl⟩)⟩

private theorem zero_observation_mean_tendsto (T : E →L[ℂ] E) (ℓ : E →L[ℂ] ℂ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖ℓ ((T ^ n) 0)‖ ^ 2) atTop (𝓝 0) := by
  simp only [map_zero, norm_zero, pow_two, mul_zero, Finset.sum_const_zero]
  exact tendsto_const_nhds
end GenericObservation
local instance frequencyObservationActualEndRing : NormedRing
    (causalBoundedChain →L[ℂ] causalBoundedChain) := ContinuousLinearMap.toNormedRing

/-- Every actual forward derivative-shift power preserves the norm on the completed frequency space. -/
theorem causalBoundedChainShift_pow_frequency_norm (b : ℝ) (n : ℕ) (u : causalFrequencySpace b) :
    ‖(causalBoundedChainShift ^ n) u.val‖ = ‖u‖ :=
  norm_pow_isometric_restriction causalBoundedChainShift (causalFrequencySpace b)
    (causalFrequencyShift b) (causalFrequencyShift_val b) n u

/-- A finite family of bounded ambient observations detects every point of the
actual shift orbit with a uniform mean-square floor, including the zero-vector case. -/
theorem causalFrequencyOrbit_finite_norming (b : ℝ) (u : causalFrequencySpace b) :
    ∃ s : Finset (causalBoundedChain →L[ℂ] ℂ), (∀ ℓ ∈ s, ‖ℓ‖ ≤ 1) ∧
      ∀ n : ℕ, ‖u‖ ^ 2 / 4 ≤ ∑ ℓ ∈ s, ‖ℓ ((causalBoundedChainShift ^ n) u.val)‖ ^ 2 := by
  exact orbit_finite_norming (fun n : ℕ => (causalBoundedChainShift ^ n) u.val) ‖u‖
    (norm_nonneg u) (causalFrequencySpace_compact_orbit b u)
    (fun n => causalBoundedChainShift_pow_frequency_norm b n u)

/-- Literal discrete Cesaro mean square of a bounded linear observation of the
actual derivative-shift orbit. -/
def causalFrequencyObservationMeanSquare (b : ℝ) (u : causalFrequencySpace b)
    (ℓ : causalBoundedChain →L[ℂ] ℂ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖ℓ ((causalBoundedChainShift ^ n) u.val)‖ ^ 2

/-- The zero vector is exactly the vector invisible in mean square to every
bounded ambient linear observation of its actual shift orbit. -/
theorem causalFrequencyObservationMeanSquare_vanish_iff (b : ℝ) (u : causalFrequencySpace b) :
    (∀ ℓ : causalBoundedChain →L[ℂ] ℂ,
      Tendsto (causalFrequencyObservationMeanSquare b u ℓ) atTop (𝓝 0)) ↔ u = 0 := by
  constructor
  · intro hm
    by_contra hu
    obtain ⟨s, _, hf⟩ := causalFrequencyOrbit_finite_norming b u
    have h := finite_mean_square_floor s
      (fun n : ℕ => (causalBoundedChainShift ^ n) u.val) (‖u‖ ^ 2 / 4) hf
      (fun ℓ _ => hm ℓ)
    have hp : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu) 2
    linarith
  · rintro rfl ℓ
    exact zero_observation_mean_tendsto causalBoundedChainShift ℓ

end RHTower.FokasLenells
