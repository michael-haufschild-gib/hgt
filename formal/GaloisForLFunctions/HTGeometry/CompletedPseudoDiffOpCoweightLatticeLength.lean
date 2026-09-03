import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpUniformizerPiLength
import GaloisForLFunctions.HTGeometry.DifferentialVariationalStandardApartment

/-!
# Exact lengths of natural coweight-lattice quotients

The standard completed lattice is identified with the coordinate module over the completed
valuation ring.  Under this identification, the actual diagonal lattice at a natural coweight is
exactly the product of the corresponding uniformizer-power ideals.  Its quotient length is
therefore the sum of the coweight coordinates.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι]

/-- Integral coordinates identify the standard lattice carrier with a free integer module. -/
def standardCompletedPseudoDiffOpLatticeIntegerEquiv :
    (ι → CompletedPseudoDiffOpInteger (K := K)) ≃ₗ[CompletedPseudoDiffOpInteger (K := K)]
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)).carrier where
  toFun x := ⟨fun i => (x i : CompletedPseudoDiffOp K),
    (mem_standardCompletedPseudoDiffOpLattice_iff _).2 fun i => (x i).property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y i := ⟨y.1 i,
    (mem_standardCompletedPseudoDiffOpLattice_iff y.1).1 y.2 i⟩
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

/-- A natural coweight lattice viewed as a submodule of the standard lattice. -/
def standardCompletedPseudoDiffOpLatticeAtNatCoweightInsideStandard (n : ι → ℕ) :
    Submodule (CompletedPseudoDiffOpInteger (K := K))
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)).carrier :=
  Submodule.comap
    (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)).carrier.subtype
    (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
      (fun i => (n i : ℤ))).carrier

/-- Coercion sends an integer uniformizer power to the corresponding unit power. -/
theorem completedPseudoDiffOpUniformizerInteger_pow_coe (n : ℕ) :
    (((completedPseudoDiffOpUniformizerInteger (K := K) ^ n : CompletedPseudoDiffOpInteger (K := K)) :
        CompletedPseudoDiffOp K)) =
      (completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ) :
        (CompletedPseudoDiffOp K)ˣ) := by
  change ((completedPseudoDiffOpUniformizerInteger (K := K) :
      CompletedPseudoDiffOp K) ^ n) =
    ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ) :
      (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K)
  rw [completedPseudoDiffOpUniformizerInteger_coe, zpow_natCast]
  rfl

/-- Integral coordinates carry product power ideals onto the actual natural coweight lattice. -/
theorem map_uniformizerPowerPi_eq_standardAtNatCoweightInsideStandard (n : ι → ℕ) :
    Submodule.map (standardCompletedPseudoDiffOpLatticeIntegerEquiv (K := K) (ι := ι)).toLinearMap
        (completedPseudoDiffOpUniformizerPowerPi (K := K) n) =
      standardCompletedPseudoDiffOpLatticeAtNatCoweightInsideStandard (K := K) n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (fun i => ((x i : CompletedPseudoDiffOpInteger (K := K)) : CompletedPseudoDiffOp K)) ∈
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun i => (n i : ℤ))).carrier
    rw [mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff]
    intro i
    have hxi := hx i (Set.mem_univ i)
    change x i ∈ (CompletedPseudoDiffOpInteger (K := K)) ∙
      (completedPseudoDiffOpUniformizerInteger (K := K) ^ n i) at hxi
    rw [Submodule.mem_span_singleton] at hxi
    obtain ⟨c, hc⟩ := hxi
    rw [← hc]
    change ((c * completedPseudoDiffOpUniformizerInteger (K := K) ^ n i : CompletedPseudoDiffOpInteger (K := K)) :
        CompletedPseudoDiffOp K) *
          ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (n i : ℤ))⁻¹ :
            (CompletedPseudoDiffOp K)ˣ) ∈ CompletedPseudoDiffOpInteger (K := K)
    change ((c : CompletedPseudoDiffOp K) *
        (((completedPseudoDiffOpUniformizerInteger (K := K) ^ n i : CompletedPseudoDiffOpInteger (K := K)) :
          CompletedPseudoDiffOp K))) *
          ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (n i : ℤ))⁻¹ :
            (CompletedPseudoDiffOp K)ˣ) ∈ CompletedPseudoDiffOpInteger (K := K)
    rw [completedPseudoDiffOpUniformizerInteger_pow_coe]
    simp
  · intro hy
    change (y.1 : ι → CompletedPseudoDiffOp K) ∈
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun i => (n i : ℤ))).carrier at hy
    rw [mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff] at hy
    let x : ι → CompletedPseudoDiffOpInteger (K := K) := fun i => ⟨y.1 i, (mem_standardCompletedPseudoDiffOpLattice_iff y.1).1 y.2 i⟩
    refine ⟨x, ?_, ?_⟩
    · intro i _
      change x i ∈ (CompletedPseudoDiffOpInteger (K := K)) ∙
        (completedPseudoDiffOpUniformizerInteger (K := K) ^ n i)
      rw [Submodule.mem_span_singleton]
      let c : CompletedPseudoDiffOpInteger (K := K) := ⟨y.1 i *
        ((completedPseudoDiffOpUniformizerUnit (K := K) ^ (n i : ℤ))⁻¹ :
          (CompletedPseudoDiffOp K)ˣ), hy i⟩
      refine ⟨c, ?_⟩
      apply Subtype.ext
      change (c : CompletedPseudoDiffOp K) *
          ((completedPseudoDiffOpUniformizerInteger (K := K) ^ n i : CompletedPseudoDiffOpInteger (K := K)) :
            CompletedPseudoDiffOp K) = y.1 i
      rw [completedPseudoDiffOpUniformizerInteger_pow_coe]
      simp [c]
    · apply Subtype.ext
      rfl

/-- The natural coweight quotient is the coordinatewise uniformizer-power quotient. -/
def standardCompletedPseudoDiffOpLatticeAtNatCoweightQuotientEquiv (n : ι → ℕ) :
    ((ι → CompletedPseudoDiffOpInteger (K := K)) ⧸ completedPseudoDiffOpUniformizerPowerPi (K := K) n) ≃ₗ[CompletedPseudoDiffOpInteger (K := K)]
      ((standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)).carrier ⧸
        standardCompletedPseudoDiffOpLatticeAtNatCoweightInsideStandard (K := K) n) :=
  Submodule.Quotient.equiv _ _ (standardCompletedPseudoDiffOpLatticeIntegerEquiv (K := K) (ι := ι))
    (map_uniformizerPowerPi_eq_standardAtNatCoweightInsideStandard (K := K) n)

/-- The standard lattice modulo a natural coweight lattice has length equal to coordinate sum. -/
theorem standardCompletedPseudoDiffOpLatticeAtNatCoweightQuotient_length (n : ι → ℕ) :
    Module.length (CompletedPseudoDiffOpInteger (K := K))
      ((standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)).carrier ⧸
        standardCompletedPseudoDiffOpLatticeAtNatCoweightInsideStandard (K := K) n) = ∑ i, n i := by
  rw [← (standardCompletedPseudoDiffOpLatticeAtNatCoweightQuotientEquiv (K := K) n).length_eq]
  exact completedPseudoDiffOpUniformizerPowerPiQuotient_length (K := K) n

end


end GaloisForLFunctions.HTGeometry.DiffOp
