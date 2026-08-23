/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebra

/-!
# Twisted commutators of cyclic Galois normal forms

For a cyclic Galois algebra, the commutator of a normal form with a coefficient twisted by a
chosen Galois power is again a normal form, with a selected coefficient killed.  This is the
coefficient-reduction mechanism in the standard minimal-support proof that a nonzero cyclic
algebra is simple; crucially, it uses only normal-form spanning, not normal-form uniqueness.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)]

/-- Coefficients of the normal form obtained by the `j`-twisted commutator with `b`. -/
noncomputable def cyclicGaloisAlgebraTwistedCommutatorCoefficients
    (j : Fin (Module.finrank K L)) (b : L)
    (v : Fin (Module.finrank K L) → L) : Fin (Module.finrank K L) → L :=
  fun i ↦ v i * (((cyclicGaloisGenerator K L).toRingEquiv ^ (i : ℕ)) b -
    ((cyclicGaloisGenerator K L).toRingEquiv ^ (j : ℕ)) b)

/-- The `j`-twisted commutator of one cyclic normal-form monomial changes only its coefficient. -/
theorem cyclicGaloisAlgebraMonomial_twistedCommutator
    (a : K) (i j : Fin (Module.finrank K L)) (c b : L) :
    (cyclicGaloisAlgebraC K L a c * cyclicGaloisAlgebraX K L a ^ (i : ℕ)) *
        cyclicGaloisAlgebraC K L a b -
      cyclicGaloisAlgebraC K L a
          (((cyclicGaloisGenerator K L).toRingEquiv ^ (j : ℕ)) b) *
        (cyclicGaloisAlgebraC K L a c * cyclicGaloisAlgebraX K L a ^ (i : ℕ)) =
      cyclicGaloisAlgebraC K L a
          (c * (((cyclicGaloisGenerator K L).toRingEquiv ^ (i : ℕ)) b -
            ((cyclicGaloisGenerator K L).toRingEquiv ^ (j : ℕ)) b)) *
        cyclicGaloisAlgebraX K L a ^ (i : ℕ) := by
  rw [mul_assoc]
  rw [cyclicAlgebraX_pow_mul_C]
  rw [← mul_assoc, cyclicAlgebraC_mul]
  rw [← mul_assoc, cyclicAlgebraC_mul]
  rw [← sub_mul]
  congr 1
  change cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a)
      (c * (((cyclicGaloisGenerator K L).toRingEquiv ^ (i : ℕ)) b)) -
    cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a)
      ((((cyclicGaloisGenerator K L).toRingEquiv ^ (j : ℕ)) b) * c) =
    cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a)
      (c * (((cyclicGaloisGenerator K L).toRingEquiv ^ (i : ℕ)) b -
        ((cyclicGaloisGenerator K L).toRingEquiv ^ (j : ℕ)) b))
  rw [← map_sub]
  congr 1
  ring

/-- A `j`-twisted commutator carries a cyclic normal form to the explicitly transformed
coefficient family. -/
theorem cyclicGaloisAlgebraNormalForm_twistedCommutator
    (a : K) (j : Fin (Module.finrank K L)) (b : L)
    (v : Fin (Module.finrank K L) → L) :
    cyclicGaloisAlgebraNormalFormLinearMap K L a v * cyclicGaloisAlgebraC K L a b -
      cyclicGaloisAlgebraC K L a (((cyclicGaloisGenerator K L).toRingEquiv ^ (j : ℕ)) b) *
        cyclicGaloisAlgebraNormalFormLinearMap K L a v =
      cyclicGaloisAlgebraNormalFormLinearMap K L a
        (cyclicGaloisAlgebraTwistedCommutatorCoefficients K L j b v) := by
  classical
  have hv : v = ∑ i : Fin (Module.finrank K L), Pi.single i (v i) := by
    funext i
    simp
  have hw : cyclicGaloisAlgebraTwistedCommutatorCoefficients K L j b v =
      ∑ i : Fin (Module.finrank K L),
        Pi.single i (v i * (((cyclicGaloisGenerator K L).toRingEquiv ^ (i : ℕ)) b -
          ((cyclicGaloisGenerator K L).toRingEquiv ^ (j : ℕ)) b)) := by
    funext i
    simp [cyclicGaloisAlgebraTwistedCommutatorCoefficients]
  calc
    cyclicGaloisAlgebraNormalFormLinearMap K L a v * cyclicGaloisAlgebraC K L a b -
        cyclicGaloisAlgebraC K L a
            (((cyclicGaloisGenerator K L).toRingEquiv ^ (j : ℕ)) b) *
          cyclicGaloisAlgebraNormalFormLinearMap K L a v =
        ∑ i : Fin (Module.finrank K L),
          (cyclicGaloisAlgebraNormalFormLinearMap K L a (Pi.single i (v i)) *
              cyclicGaloisAlgebraC K L a b -
            cyclicGaloisAlgebraC K L a
                (((cyclicGaloisGenerator K L).toRingEquiv ^ (j : ℕ)) b) *
              cyclicGaloisAlgebraNormalFormLinearMap K L a (Pi.single i (v i))) := by
          conv_lhs =>
            rw [hv, map_sum, Finset.sum_mul, Finset.mul_sum]
          rw [← Finset.sum_sub_distrib]
    _ = ∑ i : Fin (Module.finrank K L),
          cyclicGaloisAlgebraNormalFormLinearMap K L a
            (Pi.single i (v i * (((cyclicGaloisGenerator K L).toRingEquiv ^ (i : ℕ)) b -
              ((cyclicGaloisGenerator K L).toRingEquiv ^ (j : ℕ)) b))) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [cyclicGaloisAlgebraNormalFormLinearMap_single,
            cyclicGaloisAlgebraNormalFormLinearMap_single]
          exact cyclicGaloisAlgebraMonomial_twistedCommutator K L a i j (v i) b
    _ = cyclicGaloisAlgebraNormalFormLinearMap K L a
          (cyclicGaloisAlgebraTwistedCommutatorCoefficients K L j b v) := by
          rw [hw, map_sum]

/-- Finite support of a bounded cyclic normal-form coefficient family. -/
noncomputable def cyclicGaloisAlgebraCoefficientSupport
    (v : Fin (Module.finrank K L) → L) : Finset (Fin (Module.finrank K L)) := by
  classical
  exact Finset.univ.filter fun i ↦ v i ≠ 0

omit [IsCyclic Gal(L/K)] in
/-- A coefficient belongs to its finite normal-form support exactly when it is nonzero. -/
theorem mem_cyclicGaloisAlgebraCoefficientSupport
    (v : Fin (Module.finrank K L) → L) (i : Fin (Module.finrank K L)) :
    i ∈ cyclicGaloisAlgebraCoefficientSupport K L v ↔ v i ≠ 0 := by
  classical
  simp [cyclicGaloisAlgebraCoefficientSupport]

/-- Twisted commutators cannot introduce a nonzero normal-form coefficient. -/
theorem cyclicGaloisAlgebraTwistedCommutatorCoefficients_support_subset
    (j : Fin (Module.finrank K L)) (b : L)
    (v : Fin (Module.finrank K L) → L) :
    cyclicGaloisAlgebraCoefficientSupport K L
        (cyclicGaloisAlgebraTwistedCommutatorCoefficients K L j b v) ⊆
      cyclicGaloisAlgebraCoefficientSupport K L v := by
  intro i hi
  rw [mem_cyclicGaloisAlgebraCoefficientSupport] at hi ⊢
  intro hzero
  apply hi
  simp [cyclicGaloisAlgebraTwistedCommutatorCoefficients, hzero]

/-- The selected coefficient is killed by its twisted commutator. -/
theorem cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_self
    (j : Fin (Module.finrank K L)) (b : L)
    (v : Fin (Module.finrank K L) → L) :
    cyclicGaloisAlgebraTwistedCommutatorCoefficients K L j b v j = 0 := by
  simp [cyclicGaloisAlgebraTwistedCommutatorCoefficients]

/-- A twisted commutator strictly reduces coefficient support when it kills a coefficient that
was present. -/
theorem cyclicGaloisAlgebraTwistedCommutatorCoefficients_support_ssubset
    (j : Fin (Module.finrank K L)) (b : L)
    (v : Fin (Module.finrank K L) → L) (hj : v j ≠ 0) :
    cyclicGaloisAlgebraCoefficientSupport K L
        (cyclicGaloisAlgebraTwistedCommutatorCoefficients K L j b v) ⊂
      cyclicGaloisAlgebraCoefficientSupport K L v := by
  refine (Finset.ssubset_iff_subset_ne).mpr ⟨
    cyclicGaloisAlgebraTwistedCommutatorCoefficients_support_subset K L j b v, ?_⟩
  intro heq
  have hjmem : j ∈ cyclicGaloisAlgebraCoefficientSupport K L v :=
    (mem_cyclicGaloisAlgebraCoefficientSupport K L v j).mpr hj
  have hjnot : j ∉ cyclicGaloisAlgebraCoefficientSupport K L
      (cyclicGaloisAlgebraTwistedCommutatorCoefficients K L j b v) := by
    rw [mem_cyclicGaloisAlgebraCoefficientSupport]
    intro h
    exact h (cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_self K L j b v)
  apply hjnot
  rw [heq]
  exact hjmem

/-- A nonzero coefficient remains nonzero after a twisted commutator whenever the two selected
Galois powers distinguish the chosen coefficient. -/
theorem cyclicGaloisAlgebraTwistedCommutatorCoefficients_apply_ne_zero
    (j i : Fin (Module.finrank K L)) (b : L)
    (v : Fin (Module.finrank K L) → L) (hvi : v i ≠ 0)
    (hijb : ((cyclicGaloisGenerator K L).toRingEquiv ^ (i : ℕ)) b ≠
      ((cyclicGaloisGenerator K L).toRingEquiv ^ (j : ℕ)) b) :
    cyclicGaloisAlgebraTwistedCommutatorCoefficients K L j b v i ≠ 0 := by
  simp only [cyclicGaloisAlgebraTwistedCommutatorCoefficients]
  exact mul_ne_zero hvi (sub_ne_zero.mpr hijb)

/-- Distinct bounded exponents of a cyclic Galois generator give distinct automorphisms. -/
theorem cyclicGaloisGenerator_pow_ne_pow_of_finrank_lt [FiniteDimensional K L] [IsGalois K L]
    (i j : Fin (Module.finrank K L)) (hij : i ≠ j) :
    ((cyclicGaloisGenerator K L).toRingEquiv ^ (i : ℕ)) ≠
      ((cyclicGaloisGenerator K L).toRingEquiv ^ (j : ℕ)) := by
  intro hpow
  have hpow' : cyclicGaloisGenerator K L ^ (i : ℕ) =
      cyclicGaloisGenerator K L ^ (j : ℕ) := by
    ext x
    simpa [AlgEquiv.coe_pow] using DFunLike.congr_fun hpow x
  have hmod : Nat.ModEq (Module.finrank K L) (i : ℕ) (j : ℕ) :=
    by simpa only [cyclicGaloisGenerator_orderOf] using pow_eq_pow_iff_modEq.mp hpow'
  apply hij
  apply Fin.ext
  exact Nat.ModEq.eq_of_lt_of_lt hmod i.isLt j.isLt

/-- Two distinct bounded Galois powers disagree on some coefficient. -/
theorem cyclicGaloisGenerator_pow_exists_apply_ne [FiniteDimensional K L] [IsGalois K L]
    (i j : Fin (Module.finrank K L)) (hij : i ≠ j) :
    ∃ b : L, ((cyclicGaloisGenerator K L).toRingEquiv ^ (i : ℕ)) b ≠
      ((cyclicGaloisGenerator K L).toRingEquiv ^ (j : ℕ)) b := by
  have hne := cyclicGaloisGenerator_pow_ne_pow_of_finrank_lt K L i j hij
  contrapose! hne
  ext b
  exact hne b

end GaloisForLFunctions.HTGeometry.ABHN
