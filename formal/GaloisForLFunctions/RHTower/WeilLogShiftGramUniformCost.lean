import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticCostControl
import GaloisForLFunctions.RHTower.WeilLogShiftGramAmplitudeCost
import GaloisForLFunctions.RHTower.WeilLogShiftGramPacketKernel
import GaloisForLFunctions.RHTower.WeilLogShiftGramBalancedVectors
import GaloisForLFunctions.RHTower.WeilLogShiftGramFiberCost

/-! Fixed nodes realize every finite coefficient target with native cost bounded
linearly in its norm. Coalescing preserves this quantitative conclusion. -/

open scoped BigOperators
open Filter Topology
attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower

theorem exists_finiteWeilGram_fixed_node_cost_control (s : Finset ℕ) :
    ∃ N : ℕ, ∃ x : Fin N → ℝ, ∃ C : ℝ, 0 < C ∧
      ∀ y : s → ℝ, ∃ u : Fin N → ℝ,
        finiteWeilGramCoefficientVector s ⟨N, x, u, 1⟩ = y ∧
          finiteWeilGramTailCost 1 ⟨N, x, u, 1⟩ ≤ C * ‖y‖ := by
  let D := finiteWeilGramCoordinates s
  let J := D.tests
  let w : J → FiniteWeilGramTest := fun j => j.1
  let a : J → NNReal := fun j => NNReal.mk (D.balance j) (D.balance_pos j).le
  let ell : J → ℝ := fun j => (((Fintype.equivFin J) j).val : ℝ)
  have hell : Function.Injective ell := by
    intro j h he
    apply (Fintype.equivFin J).injective
    apply Fin.ext
    exact Nat.cast_injective he
  have hv (j : J) : (a j : ℝ) • finiteWeilGramCoefficientVector s (w j) =
      D.coefficientBalance j := rfl
  have hlim : Tendsto (finiteWeilGramPacketKernel s w a ell) atTop
      (𝓝 (finiteWeilQuadraticDiagonal D.coefficientBalance)) := by
    simpa only [hv] using tendsto_finiteWeilGramPacketKernel s w a ell hell
  obtain ⟨A, hA, hnear⟩ := exists_eventually_controlled_finiteWeilQuadraticMap_diagonal
    D.coefficientBalance D.coefficientBalance_sum D.coefficientBalance_spans
  obtain ⟨T, hT⟩ := (hlim.eventually hnear).exists
  let I := Σ j : J, Fin (w j).1
  let x : I → ℝ := finiteWeilGramPacketNodes w ell T
  let b : I → ℝ := fun i => finiteWeilGramPacketAmplitude w a i.1 i.2
  let Γ := finiteWeilGramTailCost 1 (finiteWeilGramTestOfFinite x b 1)
  have hΓ : 0 ≤ Γ := finiteWeilGramTailCost_one_nonneg _
  refine ⟨Fintype.card I, x ∘ (Fintype.equivFin I).symm, Γ * A + 1, by positivity, ?_⟩
  intro y
  obtain ⟨t, ht, hnorm⟩ := hT y
  refine ⟨(fun i : I => t i.1 * b i) ∘ (Fintype.equivFin I).symm, ?_, ?_⟩
  · change finiteWeilGramCoefficientVector s
      (finiteWeilGramTestOfFinite x (fun i : I => t i.1 * b i) 1) = y
    rw [finiteWeilGramCoefficientVector_packet]
    exact ht
  · change finiteWeilGramTailCost 1
      (finiteWeilGramTestOfFinite x (fun i : I => t i.1 * b i) 1) ≤ (Γ * A + 1) * ‖y‖
    calc
      _ ≤ ‖t‖ ^ 2 * Γ := finiteWeilGramTailCost_amplitude_bound x b (fun i => i.1) t
      _ ≤ (A * ‖y‖) * Γ := mul_le_mul_of_nonneg_right hnorm hΓ
      _ ≤ (Γ * A + 1) * ‖y‖ := by nlinarith only [norm_nonneg y]

/-- The nodes and cost constant precede every target; only amplitudes vary. -/
theorem exists_finiteWeilGram_distinct_fixed_node_cost_control (s : Finset ℕ) :
    ∃ N : ℕ, ∃ x : Fin N → ℝ, ∃ C : ℝ, Function.Injective x ∧ 0 < C ∧
      ∀ y : s → ℝ, ∃ u : Fin N → ℝ,
        finiteWeilGramCoefficientVector s ⟨N, x, u, 1⟩ = y ∧
          finiteWeilGramTailCost 1 ⟨N, x, u, 1⟩ ≤ C * ‖y‖ := by
  obtain ⟨N, x, C, hC, hrealize⟩ := exists_finiteWeilGram_fixed_node_cost_control s
  let S := Finset.univ.image x
  let q : Fin N → S := fun i => ⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩
  refine ⟨Fintype.card S,
    (fun y : S => (y : ℝ)) ∘ (Fintype.equivFin S).symm, C, ?_, hC, ?_⟩
  · intro i j he
    apply (Fintype.equivFin S).symm.injective
    exact Subtype.ext he
  · intro y
    obtain ⟨u, hu, hcost⟩ := hrealize y
    refine ⟨finiteWeilGramFiberAmplitude q u ∘ (Fintype.equivFin S).symm, ?_, ?_⟩
    · change finiteWeilGramCoefficientVector s
        (finiteWeilGramTestOfFinite (fun y : S => (y : ℝ))
          (finiteWeilGramFiberAmplitude q u) 1) = y
      have hf := finiteWeilGramForm_fiberAmplitude s q (fun y : S => (y : ℝ)) u 1
      calc
        _ = finiteWeilGramCoefficientVector s
            (finiteWeilGramTestOfFinite ((fun y : S => (y : ℝ)) ∘ q) u 1) := by
          funext k
          exact congrArg (fun L : (s → ℝ) →ₗ[ℝ] ℝ => L (Pi.single k 1)) hf
        _ = finiteWeilGramCoefficientVector s ⟨N, x, u, 1⟩ := by
          funext k
          rw [finiteWeilGramCoefficientVector_ofFinite, finiteWeilGramCoefficientVector_apply]
          rfl
        _ = y := hu
    · change finiteWeilGramTailCost 1
        (finiteWeilGramTestOfFinite (fun y : S => (y : ℝ))
          (finiteWeilGramFiberAmplitude q u) 1) ≤ C * ‖y‖
      calc
        _ ≤ finiteWeilGramTailCost 1
            (finiteWeilGramTestOfFinite ((fun y : S => (y : ℝ)) ∘ q) u 1) :=
          finiteWeilGramTailCost_fiberAmplitude_le (by positivity) q (fun y : S => (y : ℝ)) u 1
        _ = finiteWeilGramTailCost 1 ⟨N, x, u, 1⟩ := by
          rw [finiteWeilGramTailCost_ofFinite]
          rfl
        _ ≤ C * ‖y‖ := hcost

end RHTower
