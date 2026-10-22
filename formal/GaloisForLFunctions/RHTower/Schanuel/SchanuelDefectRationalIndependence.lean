import GaloisForLFunctions.RHTower.Schanuel.SchanuelDefectLattice

/-!
# Rational independence of numerical exponential defects

The integral defect relation theorem extends to rational coefficients by one simultaneous
denominator clearing.  This packages the exact rational coefficient floor as a standard
`LinearIndependent` theorem.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

private theorem rat_clear_one {n : ℕ} (c : Fin n → ℚ) (i : Fin n) :
    let D : ℕ := ∏ j, (c j).den
    let m : Fin n → ℤ := fun k => (c k).num * (∏ j ∈ Finset.univ.erase k, (c j).den : ℕ)
    (m i : ℚ) = (D : ℚ) * c i := by
  classical
  dsimp only
  have hprod : (∏ j : Fin n, (c j).den) =
      (c i).den * ∏ j ∈ Finset.univ.erase i, (c j).den := by
    simpa using (Finset.mul_prod_erase Finset.univ (fun j => (c j).den)
      (Finset.mem_univ i)).symm
  rw [hprod]
  push_cast
  rw [← Rat.mul_den_eq_num (c i)]
  ring

/-- Every rational relation among defects of a rationally independent tuple is trivial. -/
theorem schanuelDefect_rational_relation
    {n : ℕ} (x : Fin n → ℂ) (hx : LinearIndependent ℚ x)
    (c : Fin n → ℚ)
    (hdefect : ∑ i, c i • schanuelDefect (x i) = 0) :
    c = 0 := by
  classical
  let D : ℕ := ∏ i, (c i).den
  let m : Fin n → ℤ := fun i =>
    (c i).num * (∏ j ∈ Finset.univ.erase i, (c j).den : ℕ)
  have hDpos : 0 < D := Finset.prod_pos fun i _ => Rat.den_pos (c i)
  have hcast : ∀ i, (m i : ℚ) = (D : ℚ) * c i := rat_clear_one c
  have hmrel : ∑ i, (m i : ℂ) • schanuelDefect (x i) = 0 := by
    have hmrelZ : ∑ i, m i • schanuelDefect (x i) = 0 := by
      calc
        ∑ i, m i • schanuelDefect (x i) =
            ∑ i, (m i : ℚ) • schanuelDefect (x i) := by
          simp only [Int.cast_smul_eq_zsmul]
        _ = ∑ i, ((D : ℚ) * c i) • schanuelDefect (x i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hcast i]
        _ = (D : ℚ) • ∑ i, c i • schanuelDefect (x i) := by
          simp only [mul_smul, Finset.smul_sum]
        _ = 0 := by rw [hdefect, smul_zero]
    simpa only [Int.cast_smul_eq_zsmul] using hmrelZ
  have hm : m = 0 := schanuelDefect_integer_relation x hx m hmrel
  funext i
  have hmi : (D : ℚ) * c i = 0 := by
    rw [← hcast i, congrFun hm i]
    simp
  have hD : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hDpos)
  exact (mul_eq_zero.mp hmi).resolve_left hD

/-- **Rational exponential-defect independence.**  Defects of a rationally independent complex
tuple are linearly independent over `ℚ`. -/
theorem schanuelDefect_linearIndependent_rational
    {n : ℕ} (x : Fin n → ℂ) (hx : LinearIndependent ℚ x) :
    LinearIndependent ℚ (fun i => schanuelDefect (x i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  exact congrFun (schanuelDefect_rational_relation x hx c hc) i

/-- A scalar relating the two defects of a rationally independent pair cannot be rational. -/
theorem schanuelDefect_slope_not_rational
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x) (rho : ℂ)
    (hslope : schanuelDefect (x 1) = rho • schanuelDefect (x 0)) :
    ∀ q : ℚ, rho ≠ (q : ℂ) := by
  intro q hrho
  have hLI := schanuelDefect_linearIndependent_rational x hx
  let c : Fin 2 → ℚ := ![-q, 1]
  have hsum : ∑ i, c i • schanuelDefect (x i) = 0 := by
    rw [Fin.sum_univ_two]
    simp only [c, Matrix.cons_val_zero, neg_smul, Matrix.cons_val_one, one_smul]
    rw [hslope, hrho]
    have hsmul : (q : ℂ) • schanuelDefect (x 0) =
        q • schanuelDefect (x 0) :=
      IsScalarTower.algebraMap_smul ℂ q _
    rw [hsmul]
    abel
  have hc1 := Fintype.linearIndependent_iff.mp hLI c hsum 1
  norm_num [c] at hc1

end


end GaloisForLFunctions.RHTower
