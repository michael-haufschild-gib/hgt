import GaloisForLFunctions.RHTower.SchanuelDefectLattice

/-!
# Schanuel defect relations inside a value field

The ambient integral-independence theorem for Schanuel defects descends from an
intermediate value field by functoriality of Kähler differentials.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

open Complex
open Module

noncomputable section

/-- An integral relation among logarithmic defects already visible in an
intermediate value field is trivial. -/
theorem schanuelDefect_integer_relation_in_intermediateField
    {n : ℕ}
    (K : IntermediateField (algebraicClosure ℚ ℂ) ℂ)
    (x y : Fin n → K)
    (hy : ∀ i, (y i : ℂ) = Complex.exp (x i : ℂ))
    (hx : LinearIndependent ℚ (fun i => (x i : ℂ)))
    (m : Fin n → ℤ)
    (hdefect :
      ∑ i, m i •
        ((y i)⁻¹ • KaehlerDifferential.D (algebraicClosure ℚ ℂ) K (y i) -
          KaehlerDifferential.D (algebraicClosure ℚ ℂ) K (x i)) = 0) :
    m = 0 := by
  let A := algebraicClosure ℚ ℂ
  let Φ := KaehlerDifferential.map A A K ℂ
  have hΦ : ∀ i,
      Φ ((y i)⁻¹ • KaehlerDifferential.D A K (y i) -
          KaehlerDifferential.D A K (x i)) =
        schanuelDefect (x i : ℂ) := by
    intro i
    simp only [Φ, A, schanuelDefect, map_sub, map_smul,
      KaehlerDifferential.map_D, IntermediateField.algebraMap_apply, hy]
    have hscalar :
        (y i)⁻¹ •
            KaehlerDifferential.D A ℂ (Complex.exp (x i : ℂ)) =
          algebraMap K ℂ ((y i)⁻¹) •
            KaehlerDifferential.D A ℂ (Complex.exp (x i : ℂ)) := by
      exact (IsScalarTower.algebraMap_smul
        (A := ℂ) (M := KaehlerDifferential A ℂ) ((y i)⁻¹)
        (KaehlerDifferential.D A ℂ (Complex.exp (x i : ℂ)))).symm
    rw [hscalar, map_inv₀, IntermediateField.algebraMap_apply, hy]
  have hmap := congrArg Φ hdefect
  simp only [map_sum, map_zsmul, map_zero] at hmap
  change (∑ i, m i •
      Φ ((y i)⁻¹ • KaehlerDifferential.D A K (y i) -
        KaehlerDifferential.D A K (x i))) = 0 at hmap
  have hambient : ∑ i, m i • schanuelDefect (x i : ℂ) = 0 := by
    calc
      ∑ i, m i • schanuelDefect (x i : ℂ) =
          ∑ i, m i •
            Φ ((y i)⁻¹ • KaehlerDifferential.D A K (y i) -
              KaehlerDifferential.D A K (x i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hΦ i]
      _ = 0 := hmap
  apply schanuelDefect_integer_relation (fun i => (x i : ℂ)) hx m
  simpa only [Int.cast_smul_eq_zsmul ℂ] using hambient

end

end GaloisForLFunctions.RHTower
