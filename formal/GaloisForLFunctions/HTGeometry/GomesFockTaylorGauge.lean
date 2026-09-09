import GaloisForLFunctions.HTGeometry.GammaFactorialFockPolarization
import GaloisForLFunctions.HTGeometry.GomesComplexPolynomialGaugeRigidity
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Polynomial Taylor gauge representations of finite Fock jets

This applies the polynomial-versus-unitary representation distinction in Gomes,
arXiv:2607.24901, to the corpus's Gamma-factorial derivative clock. Its terminating
exponential integrates to a faithful complex additive-group representation in every
jet dimension at least two. Polynomial compact rigidity excludes a unitary real
translation family. The parameter-one action is exactly the existing Taylor operator.
-/

open scoped Matrix Matrix.Norms.Operator BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The existing derivative clock as a complex-linear map. -/
def fockShiftLinear (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun := shiftOp
  map_add' x y := by
    funext j
    exact jetExt_add x y ((j : ℕ)+1)
  map_smul' c x := by
    funext j
    change jetExt (c • x) ((j : ℕ)+1) = c * jetExt x ((j : ℕ)+1)
    exact jetExt_smul c x ((j : ℕ)+1)

/-- Matrix of the actual finite derivative clock. -/
def fockShiftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toMatrix' (fockShiftLinear N)

/-- Matrix action agrees with the source derivative operator. -/
theorem fockShiftMatrix_mulVec (N : ℕ) (x : Fin N → ℂ) :
    fockShiftMatrix N *ᵥ x = shiftOp x :=
  LinearMap.toMatrix'_mulVec (fockShiftLinear N) x

/-- Powers of the derivative matrix are the existing iterated jet shifts. -/
theorem fockShiftMatrix_pow_mulVec (N k : ℕ) (x : Fin N → ℂ) :
    (fockShiftMatrix N)^k *ᵥ x = shiftOp^[k] x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,← Matrix.mulVec_mulVec,fockShiftMatrix_mulVec,ih,Function.iterate_succ_apply]

/-- The derivative matrix is nilpotent in every finite jet dimension. -/
theorem fockShiftMatrix_nilpotent (N : ℕ) : (fockShiftMatrix N)^N = 0 := by
  apply (Matrix.toLin' : Matrix (Fin N) (Fin N) ℂ ≃ₗ[ℂ]
    ((Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ))).injective
  apply LinearMap.ext
  intro x
  change (fockShiftMatrix N)^N *ᵥ x = (0 : Matrix (Fin N) (Fin N) ℂ) *ᵥ x
  rw [fockShiftMatrix_pow_mulVec,shiftOp_iterate_eq_zero,Matrix.zero_mulVec]

/-- Translation by an arbitrary complex parameter on the finite jet space. -/
def fockTaylorMatrix (N : ℕ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  NormedSpace.exp (z • fockShiftMatrix N)

/-- The parameterized translation is an exact finite polynomial exponential, including the
zero-dimensional jet space. -/
theorem fockTaylorMatrix_finite_exp (N : ℕ) (z : ℂ) :
    fockTaylorMatrix N z = ∑ k ∈ Finset.range N,
      (z^k / (Nat.factorial k : ℂ)) • (fockShiftMatrix N)^k := by
  have htrunc : fockTaylorMatrix N z = ∑ k ∈ Finset.range N,
      (Nat.factorial k : ℂ)⁻¹ • (z • fockShiftMatrix N)^k := by
    rw [fockTaylorMatrix,NormedSpace.exp_eq_tsum ℂ]
    apply tsum_eq_sum
    intro k hk
    have hNk : N ≤ k := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk)
    rw [smul_pow,pow_eq_zero_of_le hNk (fockShiftMatrix_nilpotent N),smul_zero,smul_zero]
  rw [htrunc]
  apply Finset.sum_congr rfl
  intro k hk
  rw [smul_pow,smul_smul]
  congr 1
  ring

/-- Translation acts by the corresponding exact finite series of derivative-clock iterates. -/
theorem fockTaylorMatrix_mulVec_series (N : ℕ) (z : ℂ) (x : Fin N → ℂ) :
    fockTaylorMatrix N z *ᵥ x = ∑ k ∈ Finset.range N,
      (z^k / (Nat.factorial k : ℂ)) • shiftOp^[k] x := by
  rw [fockTaylorMatrix_finite_exp,Matrix.sum_mulVec]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Matrix.smul_mulVec,fockShiftMatrix_pow_mulVec]

/-- At parameter one, the new action is exactly the previously formalized Taylor translation. -/
theorem fockTaylorMatrix_one_mulVec (N : ℕ) (x : Fin N → ℂ) :
    fockTaylorMatrix N 1 *ᵥ x = taylorTranslate x := by
  rw [fockTaylorMatrix_mulVec_series,taylorTranslate_eq_exp_series]
  apply Finset.sum_congr rfl
  intro k hk
  simp

/-- Zero translation is the identity. -/
theorem fockTaylorMatrix_zero (N : ℕ) : fockTaylorMatrix N 0 = 1 := by
  simp [fockTaylorMatrix,NormedSpace.exp_zero]

/-- The arbitrary-parameter finite Taylor matrices form an additive-group representation. -/
theorem fockTaylorMatrix_add (N : ℕ) (z w : ℂ) :
    fockTaylorMatrix N (z+w) = fockTaylorMatrix N z * fockTaylorMatrix N w := by
  change NormedSpace.exp ((z+w) • fockShiftMatrix N) =
    NormedSpace.exp (z • fockShiftMatrix N) * NormedSpace.exp (w • fockShiftMatrix N)
  rw [add_smul]
  apply NormedSpace.exp_add_of_commute
  change (z • fockShiftMatrix N) * (w • fockShiftMatrix N) =
    (w • fockShiftMatrix N) * (z • fockShiftMatrix N)
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [mul_comm z w]

/-- Negative translation is an exact two-sided inverse. -/
theorem fockTaylorMatrix_inverse (N : ℕ) (z : ℂ) :
    fockTaylorMatrix N z * fockTaylorMatrix N (-z) = 1 ∧
      fockTaylorMatrix N (-z) * fockTaylorMatrix N z = 1 := by
  constructor <;> rw [← fockTaylorMatrix_add] <;> simp [fockTaylorMatrix_zero]

/-- The actual derivative clock integrates to a group homomorphism into invertible matrices. -/
def fockTaylorGauge (N : ℕ) : Multiplicative ℂ →*
    (Matrix (Fin N) (Fin N) ℂ)ˣ where
  toFun z :=
    { val := fockTaylorMatrix N z.toAdd
      inv := fockTaylorMatrix N (-z.toAdd)
      val_inv := (fockTaylorMatrix_inverse N z.toAdd).1
      inv_val := (fockTaylorMatrix_inverse N z.toAdd).2 }
  map_one' := by
    apply Units.ext
    exact fockTaylorMatrix_zero N
  map_mul' z w := by
    apply Units.ext
    exact fockTaylorMatrix_add N z.toAdd w.toAdd

/-- Polynomial matrix whose evaluation realizes the entire finite Taylor representation. -/
def fockTaylorPolynomial (N : ℕ) : Matrix (Fin N) (Fin N) (Polynomial ℂ) :=
  fun i j => ∑ k ∈ Finset.range N,
    Polynomial.C ((((fockShiftMatrix N)^k) i j) / (Nat.factorial k : ℂ)) * Polynomial.X^k

/-- Exact algebraic realization of the integrated derivative clock. -/
theorem fockTaylorPolynomial_eval (N : ℕ) (z : ℂ) :
    (fockTaylorPolynomial N).map (Polynomial.eval z) = fockTaylorMatrix N z := by
  rw [fockTaylorMatrix_finite_exp]
  ext i j
  simp only [fockTaylorPolynomial,Matrix.map_apply,Polynomial.eval_finsetSum,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The first nonconstant jet records the translation parameter without truncation error. -/
theorem fockTaylorMatrix_firstJet (n : ℕ) (z : ℂ) :
    fockTaylorMatrix (n+2) z *ᵥ coordVec 1 = coordVec 1 + z • coordVec 0 := by
  have hs : shiftOp (coordVec (N := n+2) 1) = coordVec 0 := by
    funext j
    change jetExt (coordVec (N := n+2) 1) (j.val+1) = _
    rw [jetExt_coordVec (by omega)]
    simp [coordVec]
  have hz (k : ℕ) (hk : 2 ≤ k) : shiftOp^[k] (coordVec (N := n+2) 1) = 0 := by
    funext j
    rw [shiftOp_iterate_apply,jetExt_coordVec (by omega),if_neg (by omega)]
    rfl
  rw [fockTaylorMatrix_mulVec_series]
  have hsum : (∑ k ∈ Finset.range (n+2),
      (z^k / (Nat.factorial k : ℂ)) • shiftOp^[k] (coordVec (N := n+2) 1)) =
      ∑ k ∈ Finset.range 2,
      (z^k / (Nat.factorial k : ℂ)) • shiftOp^[k] (coordVec (N := n+2) 1) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k hk hnot
    rw [hz k (by simpa only [Finset.mem_range,not_lt] using hnot),smul_zero]
  rw [hsum]
  simp [Finset.sum_range_succ,hs]

/-- The zeroth coordinate of the translated linear jet recovers the parameter. -/
theorem fockTaylorMatrix_parameter (n : ℕ) (z : ℂ) :
    (fockTaylorMatrix (n+2) z *ᵥ coordVec 1) 0 = z := by
  rw [fockTaylorMatrix_firstJet]
  simp [coordVec]

/-- Every jet dimension at least two gives a faithful additive-group representation. -/
theorem fockTaylorMatrix_faithful (n : ℕ) (z w : ℂ) :
    fockTaylorMatrix (n+2) z = fockTaylorMatrix (n+2) w ↔ z = w := by
  constructor
  · intro h
    have := congrArg (fun M => (M *ᵥ coordVec 1) 0) h
    simpa only [fockTaylorMatrix_parameter] using this
  · rintro rfl
    rfl

/-- Polynomial compact rigidity excludes a unitary realization of the entire real translation
family in every nontrivial jet dimension. -/
theorem fockTaylorMatrix_not_unitary_family (n : ℕ) :
    ¬ (∀ t : ℝ, fockTaylorMatrix (n+2) (t : ℂ) ∈ Matrix.unitaryGroup (Fin (n+2)) ℂ) := by
  intro h
  have hp : ∀ t : ℝ, (fun i j => (fockTaylorPolynomial (n+2) i j).eval (t : ℂ)) ∈
      Matrix.unitaryGroup (Fin (n+2)) ℂ := by
    intro t
    change (fockTaylorPolynomial (n+2)).map (Polynomial.eval (t : ℂ)) ∈ _
    rw [fockTaylorPolynomial_eval]
    exact h t
  have hc := (complex_polynomial_unitary_family_iff (fockTaylorPolynomial (n+2))).mp hp
  have heq : fockTaylorMatrix (n+2) 1 = fockTaylorMatrix (n+2) 0 := by
    rw [← fockTaylorPolynomial_eval,← fockTaylorPolynomial_eval]
    ext i j
    change (fockTaylorPolynomial (n+2) i j).eval 1 =
      (fockTaylorPolynomial (n+2) i j).eval 0
    conv_lhs => rw [hc.1 i j,Polynomial.eval_C]
  exact one_ne_zero ((fockTaylorMatrix_faithful n 1 0).mp heq)

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
