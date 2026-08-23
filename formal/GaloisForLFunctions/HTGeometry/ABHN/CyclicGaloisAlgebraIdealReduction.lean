/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraTwistedCommutator

/-!
# Unit reduction for cyclic Galois normal forms

A bounded normal form supported at one exponent is a unit whenever its coefficient and cyclic
parameter are nonzero. This is the terminal step of the usual minimal-support proof of cyclic
algebra simplicity. The preceding twisted-commutator calculus reduces support conditionally; the
remaining arbitrary-degree open core is to ensure such reductions remain nonzero.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L]

/-- A cyclic normal form with exactly one nonzero coefficient is a unit for a nonzero parameter. -/
theorem cyclicGaloisAlgebraNormalForm_isUnit_of_coefficientSupport_card_eq_one
    (a : K) (ha : a ≠ 0) (v : Fin (Module.finrank K L) → L)
    (hcard : (cyclicGaloisAlgebraCoefficientSupport K L v).card = 1) :
    IsUnit (cyclicGaloisAlgebraNormalFormLinearMap K L a v) := by
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have hjv : v j ≠ 0 := by
    apply (mem_cyclicGaloisAlgebraCoefficientSupport K L v j).mp
    rw [hj]
    simp
  have hv : v = Pi.single j (v j) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp
    · have hinot : i ∉ cyclicGaloisAlgebraCoefficientSupport K L v := by
        rw [hj]
        simp [hij]
      have hzero : v i = 0 := by
        apply not_ne_iff.mp
        intro hne
        exact hinot ((mem_cyclicGaloisAlgebraCoefficientSupport K L v i).mpr hne)
      simp [hzero, hij]
  rw [hv, cyclicGaloisAlgebraNormalFormLinearMap_single]
  apply IsUnit.mul
  · change IsUnit (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a) (v j))
    exact IsUnit.map _ (Ne.isUnit hjv)
  · exact (cyclicGaloisAlgebraX_isUnit K L a ha).pow _

end GaloisForLFunctions.HTGeometry.ABHN
