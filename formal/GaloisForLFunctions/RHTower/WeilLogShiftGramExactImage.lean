import GaloisForLFunctions.RHTower.WeilLogShiftGramPacketKernel
import GaloisForLFunctions.RHTower.WeilLogShiftGramBalancedVectors
import GaloisForLFunctions.RHTower.WeilLogShiftGramNodeCoalescing

/-! One fixed finite node configuration realizes every finite coefficient vector
by varying only its real amplitudes. Coalescing makes its nodes distinct. -/

open scoped BigOperators
open Filter Topology
attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower

theorem exists_finiteWeilGram_fixed_node_surjection (s : Finset ℕ) :
    ∃ N : ℕ, ∃ x : Fin N → ℝ,
      Function.Surjective (fun u : Fin N → ℝ =>
        finiteWeilGramCoefficientVector s ⟨N, x, u, 1⟩) := by
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
  have hnear := eventually_surjective_finiteWeilQuadraticMap_diagonal
    D.coefficientBalance D.coefficientBalance_sum D.coefficientBalance_spans
  obtain ⟨T, hT⟩ := (hlim.eventually hnear).exists
  let I := Σ j : J, Fin (w j).1
  refine ⟨Fintype.card I,
    finiteWeilGramPacketNodes w ell T ∘ (Fintype.equivFin I).symm, ?_⟩
  intro y
  obtain ⟨t, ht⟩ := hT y
  refine ⟨(fun i : I => t i.1 * finiteWeilGramPacketAmplitude w a i.1 i.2) ∘
    (Fintype.equivFin I).symm, ?_⟩
  change finiteWeilGramCoefficientVector s
    (finiteWeilGramTestOfFinite (finiteWeilGramPacketNodes w ell T)
      (fun i : I => t i.1 * finiteWeilGramPacketAmplitude w a i.1 i.2) 1) = y
  rw [finiteWeilGramCoefficientVector_packet]
  exact ht

/-- The nodes are chosen before the target vector. Only real amplitudes vary;
the outer normalization is always one. Empty coefficient supports are included. -/
theorem exists_finiteWeilGram_distinct_fixed_node_surjection (s : Finset ℕ) :
    ∃ N : ℕ, ∃ x : Fin N → ℝ, Function.Injective x ∧
      Function.Surjective (fun u : Fin N → ℝ =>
        finiteWeilGramCoefficientVector s ⟨N, x, u, 1⟩) := by
  obtain ⟨N, x, hx⟩ := exists_finiteWeilGram_fixed_node_surjection s
  let S := Finset.univ.image x
  let q : Fin N → S := fun i => ⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩
  refine ⟨Fintype.card S,
    (fun y : S => (y : ℝ)) ∘ (Fintype.equivFin S).symm, ?_, ?_⟩
  · intro i j he
    apply (Fintype.equivFin S).symm.injective
    exact Subtype.ext he
  · intro y
    obtain ⟨u, hu⟩ := hx y
    refine ⟨finiteWeilGramFiberAmplitude q u ∘ (Fintype.equivFin S).symm, ?_⟩
    change finiteWeilGramCoefficientVector s
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

theorem surjective_finiteWeilGramCoefficientVector (s : Finset ℕ) :
    Function.Surjective (finiteWeilGramCoefficientVector s) := by
  obtain ⟨N, x, hx⟩ := exists_finiteWeilGram_fixed_node_surjection s
  intro y
  obtain ⟨u, hu⟩ := hx y
  exact ⟨⟨N, x, u, 1⟩, hu⟩

end RHTower
