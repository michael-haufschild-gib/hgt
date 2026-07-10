import GaloisForLFunctions.SemilinearKaehlerDescent

/-!
# The elementary several-automorphism Ostrowski circuit

Combine three unconditional ingredients:

1. algebraic dependence gives a nonzero Kähler circuit;
2. additive base-field shifts make its relation space semilinearly stable;
3. a least-support relation descends its coefficients to the joint fixed
   field.

The result is a nonzero constant-coefficient differential relation among the
dependent additive primitives.  The remaining classical Ostrowski step is
the general characteristic-zero theorem that the kernel of the universal
derivation of a field extension is its relative algebraic closure.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The universal relative derivation of a constant-coefficient linear
combination is the same constant-coefficient combination of the universal
differentials. -/
theorem kaehlerD_constantCoefficient_linearCombination
    {kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    (x : kappa → L) (c : kappa →₀ C) :
    KaehlerDifferential.D K L
        (Finsupp.linearCombination L x
          (Finsupp.mapRange (algebraMap C L)
            (map_zero (algebraMap C L)) c)) =
      Finsupp.linearCombination L
        (fun k ↦ KaehlerDifferential.D K L (x k))
        (Finsupp.mapRange (algebraMap C L)
          (map_zero (algebraMap C L)) c) := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  rw [Finsupp.sum_mapRange_index (fun _ ↦ by simp)]
  rw [Finsupp.sum_mapRange_index (fun _ ↦ by simp)]
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro i hi
  simp only [smul_eq_mul]
  rw [IsScalarTower.algebraMap_apply C K L]
  rw [← Algebra.smul_def, Derivation.map_smul]
  simp

/-- Algebraically dependent additive primitives admit a nonzero Kähler
relation with coefficients in the declared joint constant field. -/
theorem exists_nonzero_constant_kaehler_relation_of_dependent_base_shifts
    {I kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [CharZero K]
    (SK : CommutingDifferenceDifferentialField I C K)
    (SL : CommutingDifferenceDifferentialField I C L)
    (hcomp : ∀ i k, SL.aut i (algebraMap K L k) =
      algebraMap K L (SK.aut i k))
    (hfixed : ∀ z : L, JointFixed SL z →
      ∃ c : C, algebraMap C L c = z)
    (x : kappa → L) (b : I → kappa → K)
    (hshift : ∀ i k, SL.aut i (x k) =
      x k + algebraMap K L (b i k))
    (hdep : ¬ AlgebraicIndependent K x) :
    ∃ c : kappa →₀ C, c ≠ 0 ∧
      Finsupp.linearCombination L
        (fun k ↦ KaehlerDifferential.D K L (x k))
        (Finsupp.mapRange (algebraMap C L)
          (map_zero (algebraMap C L)) c) = 0 := by
  classical
  let W : Submodule L (kappa →₀ L) :=
    LinearMap.ker (Finsupp.linearCombination L
      (fun k ↦ KaehlerDifferential.D K L (x k)))
  obtain ⟨u, hu0, hurel⟩ :=
    exists_nonzero_kaehler_relation_of_not_algebraicIndependent x hdep
  have huW : u ∈ W := by
    exact LinearMap.mem_ker.mpr hurel
  have hW0 : W ≠ ⊥ := by
    intro hbot
    have : u ∈ (⊥ : Submodule L (kappa →₀ L)) := by
      simpa [hbot] using huW
    exact hu0 (by simpa using this)
  have hWstable : ∀ i v, v ∈ W →
      finsuppMapRangeRingEquiv SL.aut i v ∈ W := by
    intro i v hv
    exact kaehler_relationSpace_stable_of_base_shifts
      SK.aut SL.aut hcomp x b hshift i v hv
  have hfixed' : ∀ z : L, (∀ i, SL.aut i z = z) →
      ∃ c : C, algebraMap C L c = z := by
    intro z hz
    exact hfixed z hz
  obtain ⟨c, hc0, hcW⟩ :=
    stable_finsupp_submodule_exists_nonzero_constant_vector
      SL.aut hfixed' W hWstable hW0
  exact ⟨c, hc0, LinearMap.mem_ker.mp hcW⟩

/-- Equivalent differential form of the preceding circuit: a nonzero
constant-coefficient linear combination of the dependent primitives lies in
the kernel of the universal relative derivation. -/
theorem exists_nonzero_constant_linearCombination_kaehlerD_eq_zero
    {I kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [CharZero K]
    (SK : CommutingDifferenceDifferentialField I C K)
    (SL : CommutingDifferenceDifferentialField I C L)
    (hcomp : ∀ i k, SL.aut i (algebraMap K L k) =
      algebraMap K L (SK.aut i k))
    (hfixed : ∀ z : L, JointFixed SL z →
      ∃ c : C, algebraMap C L c = z)
    (x : kappa → L) (b : I → kappa → K)
    (hshift : ∀ i k, SL.aut i (x k) =
      x k + algebraMap K L (b i k))
    (hdep : ¬ AlgebraicIndependent K x) :
    ∃ c : kappa →₀ C, c ≠ 0 ∧
      KaehlerDifferential.D K L
        (Finsupp.linearCombination L x
          (Finsupp.mapRange (algebraMap C L)
            (map_zero (algebraMap C L)) c)) = 0 := by
  obtain ⟨c, hc0, hrel⟩ :=
    exists_nonzero_constant_kaehler_relation_of_dependent_base_shifts
      SK SL hcomp hfixed x b hshift hdep
  refine ⟨c, hc0, ?_⟩
  rw [kaehlerD_constantCoefficient_linearCombination]
  exact hrel

end

end GaloisForLFunctions
