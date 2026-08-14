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

/-- A slope between two numerical exponential defects descends to any rank-one intermediate
value field in which the two exponential pairs are defined. -/
theorem schanuelDefect_slope_mem_intermediateField_of_finrank_one
    (K : IntermediateField (algebraicClosure ℚ ℂ) ℂ)
    (x y : Fin 2 → K)
    (hy : ∀ i, (y i : ℂ) = Complex.exp (x i : ℂ))
    (hx : LinearIndependent ℚ (fun i => (x i : ℂ)))
    (hfinrank : Module.finrank K
      (KaehlerDifferential (algebraicClosure ℚ ℂ) K) = 1)
    (rho : ℂ)
    (hslope : schanuelDefect (x 1 : ℂ) =
      rho • schanuelDefect (x 0 : ℂ)) :
    ∃ sigma : K, (sigma : ℂ) = rho := by
  let A := algebraicClosure ℚ ℂ
  let Phi := KaehlerDifferential.map A A K ℂ
  let eta : Fin 2 → KaehlerDifferential A K := fun i =>
    (y i)⁻¹ • KaehlerDifferential.D A K (y i) -
      KaehlerDifferential.D A K (x i)
  have hPhi : ∀ i, Phi (eta i) = schanuelDefect (x i : ℂ) := by
    intro i
    simp only [Phi, eta, A, schanuelDefect, map_sub, map_smul,
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
  have hepsilon0 : schanuelDefect (x 0 : ℂ) ≠ 0 := by
    intro hzero
    let m : Fin 2 → ℤ := fun i => if i = 0 then 1 else 0
    have hm := schanuelDefect_integer_relation (fun i => (x i : ℂ)) hx m (by
      simp [m, hzero])
    have hm0 := congrFun hm 0
    norm_num [m] at hm0
  have heta0 : eta 0 ≠ 0 := by
    intro hzero
    apply hepsilon0
    rw [← hPhi 0, hzero, map_zero]
  obtain ⟨sigma, hsigma⟩ :=
    exists_smul_eq_of_finrank_eq_one hfinrank heta0 (eta 1)
  refine ⟨sigma, ?_⟩
  apply smul_left_injective ℂ hepsilon0
  have hsigmaC := congrArg Phi hsigma
  have hsigmaC' : (sigma : ℂ) • schanuelDefect (x 0 : ℂ) =
      schanuelDefect (x 1 : ℂ) := by
    have hscalar :
        sigma • schanuelDefect (x 0 : ℂ) =
          (sigma : ℂ) • schanuelDefect (x 0 : ℂ) := by
      exact (IsScalarTower.algebraMap_smul
        (A := ℂ) (M := KaehlerDifferential A ℂ) sigma
        (schanuelDefect (x 0 : ℂ))).symm
    rw [← hscalar]
    simpa only [map_smul, hPhi] using hsigmaC
  exact hsigmaC'.trans hslope

/-- A nondegenerate integral fractional-linear transform cannot make a slope descend without the
original slope descending as well. -/
theorem mobius_slope_mem_intermediateField
    (K : IntermediateField (algebraicClosure ℚ ℂ) ℂ)
    (rho : ℂ) (sigma : K) (a b c d : ℤ)
    (hdet : a * d - b * c ≠ 0)
    (hmobius :
      (sigma : ℂ) * ((a : ℂ) + (b : ℂ) * rho) =
        (c : ℂ) + (d : ℂ) * rho) :
    ∃ tau : K, (tau : ℂ) = rho := by
  have hsolve :
      ((b : ℂ) * (sigma : ℂ) - (d : ℂ)) * rho =
        (c : ℂ) - (a : ℂ) * (sigma : ℂ) := by
    calc
      ((b : ℂ) * (sigma : ℂ) - (d : ℂ)) * rho =
          (sigma : ℂ) * ((a : ℂ) + (b : ℂ) * rho) -
            (a : ℂ) * (sigma : ℂ) - (d : ℂ) * rho := by ring
      _ = ((c : ℂ) + (d : ℂ) * rho) -
            (a : ℂ) * (sigma : ℂ) - (d : ℂ) * rho := by rw [hmobius]
      _ = (c : ℂ) - (a : ℂ) * (sigma : ℂ) := by ring
  have hdenomC : (b : ℂ) * (sigma : ℂ) - (d : ℂ) ≠ 0 := by
    intro hdenom
    have hnum : (c : ℂ) - (a : ℂ) * (sigma : ℂ) = 0 := by
      rw [← hsolve, hdenom, zero_mul]
    have hd : (b : ℂ) * (sigma : ℂ) = (d : ℂ) := sub_eq_zero.mp hdenom
    have hc : (c : ℂ) = (a : ℂ) * (sigma : ℂ) := sub_eq_zero.mp hnum
    have hdetC : ((a * d - b * c : ℤ) : ℂ) = 0 := by
      push_cast
      rw [← hd, hc]
      ring
    apply hdet
    exact_mod_cast hdetC
  let tau : K :=
    ((c : K) - (a : K) * sigma) / ((b : K) * sigma - (d : K))
  refine ⟨tau, ?_⟩
  change
    ((c : ℂ) - (a : ℂ) * (sigma : ℂ)) /
      ((b : ℂ) * (sigma : ℂ) - (d : ℂ)) = rho
  rw [div_eq_iff hdenomC]
  simpa only [mul_comm] using hsolve.symm

end

end GaloisForLFunctions.RHTower
