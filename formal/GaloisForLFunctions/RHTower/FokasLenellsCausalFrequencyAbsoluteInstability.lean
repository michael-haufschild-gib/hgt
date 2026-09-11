import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyAlmostEuclidean
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyAbsoluteSynthesis
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Complex.Basic
open Filter Topology
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false

section FinitePackets
variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem synthesis_single_of_hasSum [DecidableEq I]
    (v : I → E) (S : lp (fun _ : I => ℂ) 1 → E)
    (hS : ∀ c, HasSum (fun i => c i • v i) (S c)) (i : I) (z : ℂ) :
    S (lp.single 1 i z) = z • v i := by
  calc
    S (lp.single 1 i z) = ∑' j, (lp.single (E := fun _ : I => ℂ) 1 i z) j • v j :=
      (hS (lp.single 1 i z)).tsum_eq.symm
    _ = z • v i := by
      rw [tsum_eq_single i]
      · rw [lp.single_apply_self]
      · intro j hj
        rw [lp.single_apply_ne _ _ _ hj, zero_smul]

private theorem lp1_inverse_unbounded_from_packets [DecidableEq I]
    (v : I → E) (S : lp (fun _ : I => ℂ) 1 →L[ℂ] E)
    (hS : ∀ i, S (lp.single 1 i 1) = v i)
    (hp : ∀ N : ℕ, ∃ s : Finset I, s.card = N ∧
      ‖∑ i ∈ s, v i‖ ^ 2 ≤ 2 * (N : ℝ)) (C : ℝ) :
    ∃ c : lp (fun _ : I => ℂ) 1, C * ‖S c‖ < ‖c‖ := by
  classical
  let D : ℝ := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * D ^ 2 + 1)
  obtain ⟨s, hs, hp⟩ := hp N
  let c : lp (fun _ : I => ℂ) 1 := ∑ i ∈ s, lp.single 1 i 1
  have hc : ‖c‖ = (N : ℝ) := by
    simpa [c, hs] using (lp.norm_sum_single (E := fun _ : I => ℂ)
      (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal) (fun _ : I => (1 : ℂ)) s)
  have hSc : S c = ∑ i ∈ s, v i := by simp only [c, map_sum, hS]
  have hupper : ‖S c‖ ^ 2 ≤ 2 * (N : ℝ) := by rw [hSc]; exact hp
  refine ⟨c, ?_⟩
  by_contra h
  have hlow : (N : ℝ) ≤ D * ‖S c‖ := by
    rw [← hc]
    exact (le_of_not_gt h).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hsq : (N : ℝ) ^ 2 ≤ (D * ‖S c‖) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg N) (mul_nonneg hD (norm_nonneg _))).2 hlow
  have hscaled := mul_le_mul_of_nonneg_left hupper (sq_nonneg D)
  have hNp : (0 : ℝ) < N := by nlinarith [sq_nonneg D]
  have hlarge : 2 * D ^ 2 < (N : ℝ) := by linarith
  have hstrict := mul_lt_mul_of_pos_right hlarge hNp
  nlinarith

private theorem subtype_small_packets (D : Submodule ℂ E) (v : I → D) (w : I → E)
    (hv : ∀ i, (v i).val = w i)
    (hp : ∀ N k : ℕ, ∃ s : Finset I, s.card = N ∧ ∀ c : I → ℂ,
      (∑ i ∈ s, ‖c i‖ ^ 2 ≤ ‖∑ i ∈ s, c i • w i‖ ^ 2) ∧
      (‖∑ i ∈ s, c i • w i‖ ^ 2 ≤
        (1 + 1 / ((k : ℝ) + 1)) * ∑ i ∈ s, ‖c i‖ ^ 2)) (N : ℕ) :
    ∃ s : Finset I, s.card = N ∧ ‖∑ i ∈ s, v i‖ ^ 2 ≤ 2 * (N : ℝ) := by
  obtain ⟨s, hs, h⟩ := hp N 0
  refine ⟨s, hs, ?_⟩
  have he : (∑ i ∈ s, v i).val = ∑ i ∈ s, w i := by
    change D.subtype (∑ i ∈ s, v i) = _
    simp only [map_sum]
    exact Finset.sum_congr rfl (fun i _ => hv i)
  change ‖(∑ i ∈ s, v i).val‖ ^ 2 ≤ _
  rw [he]
  have hbound := (h (fun _ => 1)).2
  norm_num [hs] at hbound
  exact hbound
end FinitePackets

private theorem inverse_unbounded_range_not_closed
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (S : E →L[ℂ] F) (hi : Function.Injective S)
    (hu : ∀ C : ℝ, ∃ c : E, C * ‖S c‖ < ‖c‖) :
    ¬ IsClosed (Set.range S) := by
  intro hclosed
  obtain ⟨K, hK⟩ := S.antilipschitz_of_injective_of_isClosed_range hi hclosed
  obtain ⟨c, hc⟩ := hu (K : ℝ)
  have hd := hK.le_mul_dist c 0
  have hle : ‖c‖ ≤ (K : ℝ) * ‖S c‖ := by
    simpa only [map_zero, dist_zero_right] using hd
  exact not_lt_of_ge hle hc

private theorem nonclosed_range_not_surjective
    {E F : Type*} [TopologicalSpace F] (S : E → F)
    (h : ¬ IsClosed (Set.range S)) : ¬ Function.Surjective S := by
  intro hs
  apply h
  rw [Set.range_eq_univ.mpr hs]
  exact isClosed_univ


private theorem actual_small_packet (b : ℝ) (N : ℕ) :
    ∃ s : Finset ℝ, s.card = N ∧
      ‖∑ ω ∈ s, causalFrequencyMode b ω‖ ^ 2 ≤ 2 * (N : ℝ) := by
  exact subtype_small_packets (causalFrequencySpace b) (causalFrequencyMode b)
    (causalBoundedUnitEigenchain b) (fun _ => rfl)
    (causalFrequencyPacket_almost_euclidean b) N

/-- No constant bounds absolute coefficient mass by the actual synthesis norm.
The witnesses are finite packets of genuine unit frequency modes. -/
theorem causalFrequencyAbsoluteSynthesis_inverse_unbounded (b C : ℝ) :
    ∃ c : lp (fun _ : ℝ => ℂ) 1,
      C * ‖causalFrequencyAbsoluteSynthesis b c‖ < ‖c‖ := by
  apply lp1_inverse_unbounded_from_packets (causalFrequencyMode b)
    (causalFrequencyAbsoluteSynthesis b) _ (actual_small_packet b) C
  intro ω
  simpa only [one_smul] using synthesis_single_of_hasSum
    (causalFrequencyMode b) (fun c => causalFrequencyAbsoluteSynthesis b c)
    (causalFrequencyAbsoluteSynthesis_hasSum b) ω 1

/-- Absolute synthesis has a dense, nonclosed image in the actual chain norm. -/
theorem causalFrequencyAbsoluteSynthesis_not_isClosed_range (b : ℝ) :
    ¬ IsClosed (Set.range (causalFrequencyAbsoluteSynthesis b)) := by
  letI : CompleteSpace (causalFrequencySpace b) := causalFrequencySpace_complete b
  exact inverse_unbounded_range_not_closed (causalFrequencyAbsoluteSynthesis b)
    (causalFrequencyAbsoluteSynthesis_injective b)
    (causalFrequencyAbsoluteSynthesis_inverse_unbounded b)

/-- Some completed actual frequency chains have no absolutely summable mode
representation, despite the density and injectivity of absolute synthesis. -/
theorem causalFrequencyAbsoluteSynthesis_not_surjective (b : ℝ) :
    ¬ Function.Surjective (causalFrequencyAbsoluteSynthesis b) :=
  nonclosed_range_not_surjective (causalFrequencyAbsoluteSynthesis b)
    (causalFrequencyAbsoluteSynthesis_not_isClosed_range b)

end RHTower.FokasLenells
