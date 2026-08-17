import GaloisForLFunctions.HTGeometry.HermitianSOSCounterexample

/-!
# Why the two model cases factor

`2 e^{βt}(1 - cos γ t)` and `cosh(at) - cos(bt)` are sums of Hermitian squares.  The unfolding
obstruction explains why: their unfoldings, `2 e^{βt}(1 - cos γ u)` and `cosh(at) - cos(bu)`, are
nonnegative on the whole plane, so the obstruction is vacuous for them.

The witness of the previous file sits in the same one-parameter family and crosses the threshold:
`2λ cosh(κ(t - π/γ)) - 2 cos(γ u)` is nonnegative on the plane exactly when `λ ≥ 1`, while
nonnegativity on the diagonal only needs `λ cosh(κ π/(2γ)) ≥ 1`.  The gap between those two
conditions is precisely the gap between the Hermitian-square cone and the nonnegative cone.
-/

open Finset Real

namespace GaloisForLFunctions.HTGeometry

/-! ## The one-pair extremal function is a Hermitian square -/

noncomputable def extLam (β γ : ℝ) : Fin 3 → ℂ :=
  ![(β : ℂ), (β : ℂ) + Complex.I * (γ : ℂ), (β : ℂ) - Complex.I * (γ : ℂ)]

noncomputable def extW : Fin 3 → ℂ := ![2, -1, -1]

noncomputable def extMu (β γ : ℝ) : Fin 2 → ℂ :=
  ![((β : ℂ) + Complex.I * (γ : ℂ)) / 2, ((β : ℂ) - Complex.I * (γ : ℂ)) / 2]

noncomputable def extV : Fin 1 → Fin 2 → ℂ := ![![-Complex.I, Complex.I]]

/-- `2 e^{βt}(1 - cos γ t) = |{-i}(e^{(β+iγ)t/2} - e^{(β-iγ)t/2})|²`. -/
theorem ext_isHermitianSOS (β γ : ℝ) :
    IsHermitianSOS extW (extLam β γ) extV (extMu β γ) := by
  intro t
  rw [gram_expand extV (extMu β γ) (fun a => Complex.exp (a * t))
    (fun a b => by rw [← Complex.exp_add]; congr 1; ring)
    (fun a => by rw [← Complex.exp_conj]; congr 1; simp)]
  rw [Fintype.sum_prod_type, extW, extLam, extMu, extV, Fin.sum_univ_three]
  simp only [Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  simp only [map_div₀, map_add, map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal,
    Complex.conj_ofNat]
  simp only [map_neg, Complex.conj_I, neg_neg]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The unfolding of the extremal function is nonnegative on the whole plane. -/
theorem ext_unfold (β γ : ℝ) (t u : ℝ) :
    unfoldSum extW (extLam β γ) t u
      = ((2 * Real.exp (β * t) * (1 - Real.cos (γ * u)) : ℝ) : ℂ) := by
  have e0 : unfoldChar ((β : ℂ)) t u = Complex.exp (((β * t : ℝ) : ℂ)) := by
    rw [unfoldChar]; norm_num
  have e1 : unfoldChar ((β : ℂ) + Complex.I * (γ : ℂ)) t u
      = Complex.exp (((β * t : ℝ) : ℂ) + Complex.I * ((γ * u : ℝ) : ℂ)) := by
    rw [unfoldChar]; norm_num
  have e2 : unfoldChar ((β : ℂ) - Complex.I * (γ : ℂ)) t u
      = Complex.exp (((β * t : ℝ) : ℂ) + Complex.I * (((-γ) * u : ℝ) : ℂ)) := by
    rw [unfoldChar]; norm_num
  rw [unfoldSum, Fin.sum_univ_three, extW, extLam]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [e0, e1, e2]
  have hC : Complex.exp (((β * t : ℝ) : ℂ) + Complex.I * ((γ * u : ℝ) : ℂ))
      + Complex.exp (((β * t : ℝ) : ℂ) + Complex.I * (((-γ) * u : ℝ) : ℂ))
      = Complex.exp (((β * t : ℝ) : ℂ)) * (2 * ((Real.cos (γ * u) : ℝ) : ℂ)) := by
    rw [Complex.exp_add, Complex.exp_add, Complex.ofReal_cos]
    have h2 := Complex.two_cos ((γ * u : ℝ) : ℂ)
    have hz : Complex.I * ((γ * u : ℝ) : ℂ) = ((γ * u : ℝ) : ℂ) * Complex.I := by ring
    have hz2 : Complex.I * (((-γ) * u : ℝ) : ℂ) = -((γ * u : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hz, hz2]
    linear_combination (-(Complex.exp (((β * t : ℝ) : ℂ)))) * h2
  have hRHS : ((2 * Real.exp (β * t) * (1 - Real.cos (γ * u)) : ℝ) : ℂ)
      = 2 * Complex.exp (((β * t : ℝ) : ℂ))
        - Complex.exp (((β * t : ℝ) : ℂ)) * (2 * ((Real.cos (γ * u) : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hRHS]
  linear_combination -hC

theorem ext_unfold_nonneg (β γ : ℝ) (t u : ℝ) :
    0 ≤ (unfoldSum extW (extLam β γ) t u).re := by
  rw [ext_unfold, Complex.ofReal_re]
  have h1 : Real.cos (γ * u) ≤ 1 := Real.cos_le_one _
  have h2 : (0 : ℝ) < Real.exp (β * t) := Real.exp_pos _
  nlinarith

/-! ## The threshold in the witness family -/

/-- The unfolding of `2λ cosh(κ(t - π/γ)) - 2cos(γ u)` is nonnegative on the whole plane exactly
when `λ ≥ 1`; nonnegativity on the diagonal is a strictly weaker demand. -/
theorem cex_unfold_nonneg_of_one_le {lam0 gam kap : ℝ} (hl : 1 ≤ lam0) (t u : ℝ) :
    0 ≤ (unfoldSum (cexW lam0 gam kap) (cexLam gam kap) t u).re := by
  rw [cex_unfold, Complex.ofReal_re]
  have h1 : Real.cos (gam * u) ≤ 1 := Real.cos_le_one _
  have h2 : (1 : ℝ) ≤ Real.cosh (kap * (t - π / gam)) := Real.one_le_cosh _
  nlinarith

theorem cex_unfold_neg_of_lt_one {lam0 gam kap : ℝ} (hl : lam0 < 1) :
    (unfoldSum (cexW lam0 gam kap) (cexLam gam kap) (π / gam) 0).re < 0 := by
  rw [cex_unfold, Complex.ofReal_re]
  simp only [sub_self, mul_zero, Real.cosh_zero, Real.cos_zero]
  linarith

end GaloisForLFunctions.HTGeometry
