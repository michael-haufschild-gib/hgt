import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencySparsePackets
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyShift
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Module
open Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false

private def finiteL2Coordinates : (ℕ →₀ ℂ) →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  Finsupp.linearCombination ℂ (fun i => lp.single 2 i 1)

private theorem finiteL2Coordinates_single (i : ℕ) (z : ℂ) :
    finiteL2Coordinates (Finsupp.single i z) = lp.single 2 i z := by
  simp only [finiteL2Coordinates, Finsupp.linearCombination_single]
  simpa only [smul_eq_mul, mul_one] using
    (lp.single_smul (E := fun _ : ℕ => ℂ) 2 i z 1).symm

private theorem finiteL2Coordinates_sum (c : ℕ →₀ ℂ) :
    finiteL2Coordinates c = ∑ i ∈ c.support, lp.single 2 i (c i) := by
  simp only [finiteL2Coordinates, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [smul_eq_mul, mul_one] using
    (lp.single_smul (E := fun _ : ℕ => ℂ) 2 i (c i) 1).symm

private theorem finiteL2Coordinates_norm_sq (c : ℕ →₀ ℂ) :
    ‖finiteL2Coordinates c‖ ^ 2 = ∑ i ∈ c.support, ‖c i‖ ^ 2 := by
  rw [finiteL2Coordinates_sum]
  simpa using lp.norm_sum_single (E := fun _ : ℕ => ℂ)
    (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) c c.support

private theorem finiteL2Coordinates_dense : DenseRange finiteL2Coordinates := by
  intro c
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num) c)
  apply Filter.Eventually.of_forall
  intro s
  refine ⟨∑ i ∈ s, Finsupp.single i (c i), ?_⟩
  simp only [map_sum, finiteL2Coordinates_single]

section Extension
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private def l2Synthesis [CompleteSpace E] (v : ℕ → E) : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] E :=
  (Finsupp.linearCombination ℂ v).extendOfNorm finiteL2Coordinates

private theorem finite_l2_synthesis_bound (v : ℕ → E) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hp : ∀ s : Finset ℕ, ∀ c : ℕ → ℂ,
      ‖∑ i ∈ s, c i • v i‖ ^ 2 ≤ Δ * ∑ i ∈ s, ‖c i‖ ^ 2)
    (c : ℕ →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ v c‖ ≤ Real.sqrt Δ * ‖finiteL2Coordinates c‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
  rw [mul_pow, Real.sq_sqrt hΔ, finiteL2Coordinates_norm_sq]
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using hp c.support c

private theorem l2Synthesis_norm_le [CompleteSpace E] (v : ℕ → E) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hp : ∀ s : Finset ℕ, ∀ c : ℕ → ℂ,
      ‖∑ i ∈ s, c i • v i‖ ^ 2 ≤ Δ * ∑ i ∈ s, ‖c i‖ ^ 2)
    (c : lp (fun _ : ℕ => ℂ) 2) : ‖l2Synthesis v c‖ ≤ Real.sqrt Δ * ‖c‖ :=
  LinearMap.norm_extendOfNorm_apply_le finiteL2Coordinates_dense (Real.sqrt Δ)
    (finite_l2_synthesis_bound v Δ hΔ hp) c

private theorem l2Synthesis_single [CompleteSpace E] (v : ℕ → E) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hp : ∀ s : Finset ℕ, ∀ c : ℕ → ℂ,
      ‖∑ i ∈ s, c i • v i‖ ^ 2 ≤ Δ * ∑ i ∈ s, ‖c i‖ ^ 2)
    (i : ℕ) (z : ℂ) : l2Synthesis v (lp.single 2 i z) = z • v i := by
  have h := LinearMap.extendOfNorm_eq finiteL2Coordinates_dense
    ⟨Real.sqrt Δ, finite_l2_synthesis_bound v Δ hΔ hp⟩ (Finsupp.single i z)
  simpa only [l2Synthesis, finiteL2Coordinates_single, Finsupp.linearCombination_single] using h

private theorem synthesis_hasSum_of_single
    (v : ℕ → E) (S : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] E)
    (hS : ∀ i z, S (lp.single 2 i z) = z • v i)
    (c : lp (fun _ : ℕ => ℂ) 2) : HasSum (fun i => c i • v i) (S c) := by
  simpa only [hS] using (lp.hasSum_single (by norm_num) c).mapL S

private theorem synthesis_coefficient_of_hasSum
    (v : ℕ → E) (S : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] E)
    (hS : ∀ c, HasSum (fun i => c i • v i) (S c))
    (a : ℕ → E →L[ℂ] ℂ) (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (c : lp (fun _ : ℕ => ℂ) 2) (i : ℕ) : a i (S c) = c i := by
  have h := (hS c).mapL (a i)
  calc
    a i (S c) = ∑' j, a i (c j • v j) := h.tsum_eq.symm
    _ = c i := by
      rw [tsum_eq_single i]
      · simp [map_smul, hd]
      · intro j hji
        simp [map_smul, hd, Ne.symm hji]

private theorem synthesis_norm_lower_of_bessel
    (S : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] E) (a : ℕ → E →L[ℂ] ℂ)
    (hS : ∀ c i, a i (S c) = c i)
    (hB : ∀ u : E, ∀ s : Finset ℕ, ∑ i ∈ s, ‖a i u‖ ^ 2 ≤ ‖u‖ ^ 2)
    (c : lp (fun _ : ℕ => ℂ) 2) : ‖c‖ ≤ ‖S c‖ := by
  have he : ∑' i, ‖c i‖ ^ 2 = ‖c‖ ^ 2 := by
    simpa using (lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) c).tsum_eq
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [← he]
  apply Real.tsum_le_of_sum_le (fun i => sq_nonneg _)
  intro s
  simpa only [hS] using hB (S c) s

private theorem synthesis_closed_range_of_norm_lower
    (S : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] E)
    (hS : ∀ c, ‖c‖ ≤ ‖S c‖) : IsClosed (Set.range S) := by
  have h : AntilipschitzWith 1 S :=
    S.antilipschitz_of_bound (by simpa only [NNReal.coe_one, one_mul] using hS)
  exact h.isClosed_range S.uniformContinuous

end Extension
private theorem synthesis_range_invariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : ℕ → E) (S : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] E)
    (hS : ∀ i z, S (lp.single 2 i z) = z • v i)
    (hsum : ∀ c, HasSum (fun i => c i • v i) (S c))
    (hclosed : IsClosed (Set.range S)) (T : E →L[ℂ] E) (z : ℕ → ℂ)
    (hT : ∀ i, T (v i) = z i • v i) :
    Set.MapsTo T (Set.range S) (Set.range S) := by
  rintro _ ⟨c, rfl⟩
  apply hclosed.mem_of_tendsto (T.continuous.tendsto (S c) |>.comp (hsum c))
  apply Filter.Eventually.of_forall
  intro s
  refine ⟨∑ i ∈ s, lp.single 2 i (c i * z i), ?_⟩
  simp only [Function.comp_def, map_sum, hS, map_smul, hT, smul_smul]

private theorem invariant_image_eq
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E ≃ₗᵢ[ℂ] E) (D : Set E)
    (hf : Set.MapsTo T D D) (hb : Set.MapsTo T.symm D D) : T '' D = D := by
  apply Set.Subset.antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact hf hu
  · intro u hu
    exact ⟨T.symm u, hb hu, T.apply_symm_apply u⟩
private theorem reindexed_bessel
    {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : I → E →L[ℂ] ℂ)
    (hB : ∀ u : E, ∀ s : Finset I, ∑ i ∈ s, ‖a i u‖ ^ 2 ≤ ‖u‖ ^ 2)
    (f : ℕ → I) (hf : Function.Injective f) (u : E) (s : Finset ℕ) :
    ∑ i ∈ s, ‖a (f i) u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  classical
  simpa only [Finset.sum_image (fun i _ j _ h => hf h)] using hB u (s.image f)

private theorem synthesis_full_coefficient_of_hasSum
    {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [DecidableEq I]
    (v : ℕ → E) (S : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] E)
    (hsum : ∀ c, HasSum (fun i => c i • v i) (S c))
    (a : I → E →L[ℂ] ℂ) (f : ℕ → I)
    (hd : ∀ ξ i, a ξ (v i) = if ξ = f i then 1 else 0)
    (c : lp (fun _ : ℕ => ℂ) 2) (ξ : I) :
    a ξ (S c) = ∑' i, if ξ = f i then c i else 0 := by
  have h := ((hsum c).mapL (a ξ)).tsum_eq.symm
  simpa only [map_smul, hd, smul_eq_mul, mul_ite, mul_one, mul_zero] using h

/-- Completed synthesis of arbitrary square-summable amplitudes on the fixed
sparse frequency family. -/
def causalFrequencySparseSynthesis (b : ℝ) (k : ℕ) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] causalFrequencySpace b := by
  letI : CompleteSpace (causalFrequencySpace b) := causalFrequencySpace_complete b
  exact l2Synthesis (fun i => causalFrequencyMode b (causalFrequencySparseFrequency b k i))

/-- One sparse amplitude produces its corresponding actual mode. -/
theorem causalFrequencySparseSynthesis_single (b : ℝ) (k i : ℕ) (z : ℂ) :
    causalFrequencySparseSynthesis b k (lp.single 2 i z) =
      z • causalFrequencyMode b (causalFrequencySparseFrequency b k i) := by
  letI : CompleteSpace (causalFrequencySpace b) := causalFrequencySpace_complete b
  exact l2Synthesis_single _ (1 + 1 / ((k : ℝ) + 1)) (by positivity)
    (causalFrequencySparseFrequency_packet_norm_sq_le b k) i z

/-- Every square-summable sparse family converges unconditionally in the actual
completed chain norm to its synthesized vector. -/
theorem causalFrequencySparseSynthesis_hasSum (b : ℝ) (k : ℕ)
    (c : lp (fun _ : ℕ => ℂ) 2) :
    HasSum (fun i => c i • causalFrequencyMode b (causalFrequencySparseFrequency b k i))
      (causalFrequencySparseSynthesis b k c) :=
  synthesis_hasSum_of_single _ _ (causalFrequencySparseSynthesis_single b k) c

/-- Canonical frequency extraction recovers every selected amplitude exactly. -/
theorem causalFrequencyCoefficient_sparseSynthesis_selected (b : ℝ) (k : ℕ)
    (c : lp (fun _ : ℕ => ℂ) 2) (i : ℕ) :
    causalFrequencyCoefficient b (causalFrequencySparseFrequency b k i)
      (causalFrequencySparseSynthesis b k c) = c i := by
  apply synthesis_coefficient_of_hasSum _ _ (causalFrequencySparseSynthesis_hasSum b k)
    (fun j => causalFrequencyCoefficient b (causalFrequencySparseFrequency b k j))
  intro j l
  rw [causalFrequencyCoefficient_mode]
  simp only [(causalFrequencySparseFrequency_strictMono b k).injective.eq_iff]

/-- Full canonical coefficients contain exactly the sparse amplitudes, with zero
contribution at every unselected frequency. -/
theorem causalFrequencyCoefficient_sparseSynthesis (b : ℝ) (k : ℕ)
    (c : lp (fun _ : ℕ => ℂ) 2) (ξ : ℝ) :
    causalFrequencyCoefficient b ξ (causalFrequencySparseSynthesis b k c) =
      ∑' i, if ξ = causalFrequencySparseFrequency b k i then c i else 0 := by
  classical
  exact synthesis_full_coefficient_of_hasSum _ _ (causalFrequencySparseSynthesis_hasSum b k)
    (causalFrequencyCoefficient b) _ (fun ξ i => causalFrequencyCoefficient_mode b ξ _) c ξ

/-- Sparse synthesis has distortion arbitrarily close to one as precision grows. -/
theorem causalFrequencySparseSynthesis_norm_le (b : ℝ) (k : ℕ)
    (c : lp (fun _ : ℕ => ℂ) 2) :
    ‖causalFrequencySparseSynthesis b k c‖ ≤ Real.sqrt (1 + 1 / ((k : ℝ) + 1)) * ‖c‖ := by
  letI : CompleteSpace (causalFrequencySpace b) := causalFrequencySpace_complete b
  exact l2Synthesis_norm_le _ (1 + 1 / ((k : ℝ) + 1)) (by positivity)
    (causalFrequencySparseFrequency_packet_norm_sq_le b k) c

/-- Sparse synthesis never decreases the coefficient ℓ² norm. -/
theorem causalFrequencySparseSynthesis_norm_lower (b : ℝ) (k : ℕ)
    (c : lp (fun _ : ℕ => ℂ) 2) : ‖c‖ ≤ ‖causalFrequencySparseSynthesis b k c‖ := by
  apply synthesis_norm_lower_of_bessel _
    (fun i => causalFrequencyCoefficient b (causalFrequencySparseFrequency b k i))
    (causalFrequencyCoefficient_sparseSynthesis_selected b k)
  exact reindexed_bessel (causalFrequencyCoefficient b) (causalFrequencyCoefficient_bessel b)
    (causalFrequencySparseFrequency b k) (causalFrequencySparseFrequency_strictMono b k).injective

/-- Distinct square-summable sparse data give distinct actual completed chains. -/
theorem causalFrequencySparseSynthesis_injective (b : ℝ) (k : ℕ) :
    Function.Injective (causalFrequencySparseSynthesis b k) := by
  intro c d h
  apply lp.ext
  funext i
  have he := congrArg (causalFrequencyCoefficient b (causalFrequencySparseFrequency b k i)) h
  simpa only [causalFrequencyCoefficient_sparseSynthesis_selected] using he

/-- The sparse ℓ² copy is closed in the actual frequency-space norm. -/
theorem causalFrequencySparseSynthesis_isClosed_range (b : ℝ) (k : ℕ) :
    IsClosed (Set.range (causalFrequencySparseSynthesis b k)) :=
  synthesis_closed_range_of_norm_lower _ (causalFrequencySparseSynthesis_norm_lower b k)

/-- The derivative-shift automorphism preserves the entire closed sparse ℓ² copy. -/
theorem causalFrequencySparseSynthesis_shift_image (b : ℝ) (k : ℕ) :
    causalFrequencyShift b '' Set.range (causalFrequencySparseSynthesis b k) =
      Set.range (causalFrequencySparseSynthesis b k) := by
  apply invariant_image_eq
  · exact synthesis_range_invariant _ _ (causalFrequencySparseSynthesis_single b k)
      (causalFrequencySparseSynthesis_hasSum b k) (causalFrequencySparseSynthesis_isClosed_range b k)
      (causalFrequencyShift b).toLinearIsometry.toContinuousLinearMap
      (fun i => (causalUnitBoundaryRate b (causalFrequencySparseFrequency b k i)).val)
      (fun i => causalFrequencyShift_mode b _)
  · exact synthesis_range_invariant _ _ (causalFrequencySparseSynthesis_single b k)
      (causalFrequencySparseSynthesis_hasSum b k) (causalFrequencySparseSynthesis_isClosed_range b k)
      (causalFrequencyShift b).symm.toLinearIsometry.toContinuousLinearMap
      (fun i => (causalUnitBoundaryRate b (causalFrequencySparseFrequency b k i)).val⁻¹)
      (fun i => causalFrequencyShift_symm_mode b _)

end RHTower.FokasLenells
