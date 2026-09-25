import GaloisForLFunctions.RHTower.GL3HeckeOperator


/-!
# The Hecke eigenvalue of power functions (the Satake map at `p`)

The three kinds of Hecke representatives act on Iwasawa coordinates by
`y ↦ (y₁, p y₂)` (`diag(p,1,1)`), `y ↦ (p y₁, y₂/p)` (`[[1,x,0],[0,p,0],[0,0,1]]`) and
`y ↦ (y₁/p, y₂)` (`[[1,0,y],[0,1,w],[0,0,p]]`), with a unipotent change of `x` in each case
(`heckeGL_smul_1/2/3`, by the recognition principle). Summing over `1`, `p` and `p²` representatives
gives `T_p(y₁^α y₂^β) = (p^β + p·p^{α−β} + p²·p^{−α}) · y₁^α y₂^β` (`heckeOp_pwC`).

With `α = ν₁ + 2ν₂`, `β = 2ν₁ + ν₂` the normalised eigenvalue `p⁻¹ · (…)` is
`p^{2ν₁+ν₂−1} + p^{ν₂−ν₁} + p^{1−ν₁−2ν₂}`, the sum of the three Satake parameters.
-/

open Matrix

namespace GaloisForLFunctions.RHTower.GL3

variable (p : ℕ) [Fact p.Prime]

theorem p_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos

theorem heckeGL_val (i : HeckeIdx p) :
    ((heckeGL p i : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = (heckeRep p i).map (Int.castRingHom ℝ) :=
  rfl

/-- The image of `z` under `diag(p,1,1)`. -/
noncomputable def heckePt1 (z : H3) : H3 :=
  ⟨z.x1, p * z.x2, p * z.x3, z.y1, p * z.y2, z.y1_pos, mul_pos (p_pos p) z.y2_pos⟩

/-- The image of `z` under `[[1,x,0],[0,p,0],[0,0,1]]`. -/
noncomputable def heckePt2 (x : ZMod p) (z : H3) : H3 :=
  ⟨p * z.x1, (z.x2 + x.val) / p, z.x3 + x.val * z.x1, p * z.y1, z.y2 / p,
    mul_pos (p_pos p) z.y1_pos, div_pos z.y2_pos (p_pos p)⟩

/-- The image of `z` under `[[1,0,y],[0,1,w],[0,0,p]]`. -/
noncomputable def heckePt3 (y w : ZMod p) (z : H3) : H3 :=
  ⟨(z.x1 + w.val) / p, z.x2, (z.x3 + y.val) / p, z.y1 / p, z.y2,
    div_pos z.y1_pos (p_pos p), z.y2_pos⟩

theorem heckeGL_smul_1 (u : Unit) (z : H3) : heckeGL p (.inl u) • z = heckePt1 p z := by
  apply H3.smul_eq_of_mul (k := 1) (by simp) one_ne_zero
  rw [one_smul, Matrix.mul_one, heckeGL_val]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [heckeRep, heckePt1, H3.mat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem heckeGL_smul_2 (x : ZMod p) (z : H3) : heckeGL p (.inr (.inl x)) • z = heckePt2 p x z := by
  have hp := (p_pos p).ne'
  apply H3.smul_eq_of_mul (k := 1) (by simp) one_ne_zero
  rw [one_smul, Matrix.mul_one, heckeGL_val]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [heckeRep, heckePt2, H3.mat, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem heckeGL_smul_3 (y w : ZMod p) (z : H3) :
    heckeGL p (.inr (.inr (y, w))) • z = heckePt3 p y w z := by
  have hp := (p_pos p).ne'
  apply H3.smul_eq_of_mul (k := 1) (by simp) (r := p) hp
  rw [Matrix.mul_one, heckeGL_val]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [heckeRep, heckePt3, H3.mat, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

/-- The Hecke eigenvalue `p^β + p·p^{α−β} + p²·p^{−α}` of `y₁^α y₂^β`. -/
noncomputable def heckeEig (α β : ℂ) : ℂ :=
  Complex.exp (β * Real.log p) + p * Complex.exp ((α - β) * Real.log p) +
    (p : ℂ) ^ 2 * Complex.exp (-α * Real.log p)

theorem pwC_heckePt1 (α β : ℂ) (z : H3) :
    H3.pwC α β (heckePt1 p z) = Complex.exp (β * Real.log p) * H3.pwC α β z := by
  simp only [H3.pwC, heckePt1, Real.log_mul (p_pos p).ne' z.y2_pos.ne', ← Complex.exp_add]
  congr 1; push_cast; ring

theorem pwC_heckePt2 (α β : ℂ) (x : ZMod p) (z : H3) :
    H3.pwC α β (heckePt2 p x z) = Complex.exp ((α - β) * Real.log p) * H3.pwC α β z := by
  simp only [H3.pwC, heckePt2, Real.log_mul (p_pos p).ne' z.y1_pos.ne',
    Real.log_div z.y2_pos.ne' (p_pos p).ne', ← Complex.exp_add]
  congr 1; push_cast; ring

theorem pwC_heckePt3 (α β : ℂ) (y w : ZMod p) (z : H3) :
    H3.pwC α β (heckePt3 p y w z) = Complex.exp (-α * Real.log p) * H3.pwC α β z := by
  simp only [H3.pwC, heckePt3, Real.log_div z.y1_pos.ne' (p_pos p).ne', ← Complex.exp_add]
  congr 1; push_cast; ring

/-- **Power functions are Hecke eigenfunctions**:
`T_p(y₁^α y₂^β) = (p^β + p·p^{α−β} + p²·p^{−α}) · y₁^α y₂^β`. -/
theorem heckeOp_pwC (α β : ℂ) (z : H3) :
    heckeOp p (H3.pwC α β) z = heckeEig p α β * H3.pwC α β z := by
  simp only [heckeOp, Fintype.sum_sum_type, Fintype.sum_prod_type, heckeGL_smul_1,
    heckeGL_smul_2, heckeGL_smul_3, pwC_heckePt1, pwC_heckePt2, pwC_heckePt3]
  simp only [Finset.univ_unique, Finset.card_singleton, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul, heckeEig]
  push_cast
  ring

end GaloisForLFunctions.RHTower.GL3
