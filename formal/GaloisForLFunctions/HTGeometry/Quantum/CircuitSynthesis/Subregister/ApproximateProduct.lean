import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Subregister.Evolution
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.ShortWord
import GaloisForLFunctions.HTGeometry.KroneckerIdentityIsometry
import GaloisForLFunctions.HTGeometry.SiteSupportedReindex

/-! # Physical circuit error under disjoint placement -/
open Matrix
open scoped Matrix.Norms.L2Operator Kronecker
namespace GaloisForLFunctions.HTGeometry.Subregister
open DiagonalSynthesis
noncomputable section

variable {n k j : ℕ} {S T : Finset (Fin n)}

/-- Adding idle wires and renumbering the active ones preserve operator norm. -/
theorem norm_place (e : Fin k ≃ S) (A : Register k) : ‖place e A‖ = ‖A‖ := by
  let f := configurationSplitEquiv (fun _ : Fin n => Bool) S
  rw [←l2_opNorm_reindexAlgEquiv_eq f (place e A)]
  let g := Equiv.arrowCongr e (Equiv.refl Bool)
  let O := OutsideConfiguration (fun _ : Fin n => Bool) S
  have he : Matrix.reindexAlgEquiv ℂ ℂ f (place e A)=
      (Matrix.reindexAlgEquiv ℂ ℂ g A) ⊗ₖ (1 : Matrix O O ℂ) :=
    reindex_liftLocalMatrix_eq_kronecker_one S _
  rw [he,l2_opNorm_kronecker_one,l2_opNorm_reindexAlgEquiv_eq]

private theorem place_sub (e : Fin k ≃ S) (A B : Register k) :
    place e (A-B)=place e A-place e B := by
  ext x y
  by_cases h : restrictOutsideConfiguration S x=restrictOutsideConfiguration S y
    <;> simp only [place,map_sub,liftLocalMatrix,Matrix.sub_apply,h,if_true,if_false,sub_zero]

/-- A projective approximation lifts with its original number of gates and error. -/
theorem approximation_place (e : Fin k ≃ S) {A : Register k} {B : ℕ} {ε : ℝ}
    (h : HasProjectiveCircuitApproximation k ε B A) :
    HasProjectiveCircuitApproximation n ε B (place e A) := by
  obtain ⟨z,hz,C,hC,hfit⟩ := h
  refine ⟨z,hz,placeCircuit e C,hC,?_⟩
  rw [placeCircuit_eval,←place_smul,←place_sub,norm_place]
  exact hfit

private theorem place_evolution (e : Fin k ≃ S) (A : Register k) (t : ℝ) :
    place e (unitaryEvolution A t)=unitaryEvolution (place e A) t := by
  rw [place,place,unitaryEvolution_liftLocalMatrix,RHTower.unitaryEvolution_reindexAlgEquiv]

/-- The errors and gate counts of circuits on disjoint blocks add. -/
theorem disjoint_evolution_approximation (e : Fin k ≃ S) (f : Fin j ≃ T) (hST : Disjoint S T)
    (A : selfAdjoint (Register k)) (B : selfAdjoint (Register j)) (t : ℝ)
    {ε η : ℝ} {a b : ℕ}
    (ha : HasProjectiveCircuitApproximation k ε a (unitaryEvolution A.val t))
    (hb : HasProjectiveCircuitApproximation j η b (unitaryEvolution B.val t)) :
    HasProjectiveCircuitApproximation n (ε+η) (a+b) (unitaryEvolution (place e A.val+place f B.val) t) := by
  have hS : IsSiteSupported S (place e A.val) := isSiteSupported_liftLocalMatrix _ _
  have hR : IsSiteSupported T (place f B.val) := isSiteSupported_liftLocalMatrix _ _
  rw [unitaryEvolution_add_of_isSiteSupported_disjoint hST hS hR]
  have hB : IsSelfAdjoint (place f B.val) :=
    (isHermitian_liftLocalMatrix _ (isHermitian_reindex _ B.2.isHermitian)).isSelfAdjoint
  apply LocalPatches.approx_product (unitaryEvolution_mem_unitary hB t)
  · rw [←place_evolution]; exact approximation_place e ha
  · rw [←place_evolution]; exact approximation_place f hb

#print axioms disjoint_evolution_approximation
end
end GaloisForLFunctions.HTGeometry.Subregister
