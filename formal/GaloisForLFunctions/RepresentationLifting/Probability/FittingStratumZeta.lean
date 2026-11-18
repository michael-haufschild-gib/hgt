import GaloisForLFunctions.RepresentationLifting.Probability.NilpotentMatrixCardinality
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Zeta.PolynomialCountEulerFactors

/-!
# Local zeta factors of the Fitting stratification

The ratio of the automorphism counts in two adjacent dimensions
is a polynomial in the field size. It gives the counting polynomial
of each fixed generalized zero-eigenspace stratum. Multiplication of
their local factors cancels every pole and zero except the affine-space pole.
-/

namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels
open Finset Polynomial ArithmeticCastelnuovoSeveri
noncomputable section

/-- The generalized zero-eigenspace has dimension `d`; its invertible complement
has dimension `k`. -/
def fittingPolynomial (d : ℕ) : ℕ → ℤ[X]
  | 0 => X^(d*(d-1))
  | k+1 => X^(d+k) * (X^(d+k+1)-1) * fittingPolynomial d k

private def fittingCount (F : Type*) [Field F] (d k : ℕ) :=
  Nat.card (FittingDegreeStratum F (Fin (d+k) → F) d)

private theorem fitting_cross (F : Type*) [Field F] [Finite F] (d k : ℕ) :
    fittingCount F d k * finiteFieldAutomorphismCount F d =
      finiteFieldAutomorphismCount F (d+k) * finiteFieldNilpotentCount F d := by
  let i : Fin (Module.finrank F (Fin (d+k) → F)+1) :=
    ⟨d,by simp only [Module.finrank_pi,Fintype.card_fin]; omega⟩
  exact card_fittingDegreeStratum_mul_standard_aut (K := F) (V := Fin (d+k) → F) i

private theorem fitting_count_succ (F : Type*) [Field F] [Finite F] (d k : ℕ) :
    fittingCount F d (k+1) = (Nat.card F)^(d+k) * ((Nat.card F)^(d+k+1)-1) * fittingCount F d k := by
  apply Nat.eq_of_mul_eq_mul_right (finiteFieldAutomorphismCount_pos F d)
  rw [fitting_cross,mul_assoc,fitting_cross,← Nat.add_assoc,finiteFieldAutomorphismCount_succ]
  ac_rfl

/-- Each integral polynomial evaluates to the genuine size of its matrix stratum. -/
theorem fittingPolynomial_eval (F : Type*) [Field F] [Finite F] (d k : ℕ) :
    (fittingPolynomial d k).eval (Nat.card F : ℤ) =
      (Nat.card (FittingDegreeStratum F (Fin (d+k) → F) d) : ℤ) := by
  change _ = (fittingCount F d k : ℤ)
  induction k with
  | zero =>
    have h : fittingCount F d 0 = finiteFieldNilpotentCount F d := by
      apply Nat.eq_of_mul_eq_mul_right (finiteFieldAutomorphismCount_pos F d)
      simpa only [Nat.add_zero,mul_comm] using fitting_cross F d 0
    rw [h,finiteFieldNilpotentCount_eq]
    simp [fittingPolynomial]
  | succ k ih =>
    have hp : 1 ≤ (Nat.card F)^(d+k+1) := pow_pos (Nat.card_pos (α := F)) _
    rw [fitting_count_succ]
    simp only [fittingPolynomial,eval_mul,eval_sub,eval_pow,eval_X,eval_one,
      Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hp,Nat.cast_one,ih]

/-- The extension-degree ghost coefficient is the actual Fitting-stratum count. -/
theorem fittingPointSeries_extension (F E : Type*) [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (d k : ℕ) :
    PowerSeries.coeff (Module.finrank F E) (polynomialCountSeries (fittingPolynomial d k)
      (Fintype.card F : ℂ)) = (Nat.card (FittingDegreeStratum E (Fin (d+k) → E) d) : ℂ) := by
  rw [polynomialCountSeries,PowerSeries.coeff_mk,if_neg (Module.finrank_pos (R := F) (M := E)).ne',
    ← Nat.cast_pow,← Module.card_eq_pow_finrank (K := F) (V := E)]
  have h := Polynomial.eval₂_at_apply (p := fittingPolynomial d k) (Int.castRingHom ℂ) (Nat.card E : ℤ)
  rw [fittingPolynomial_eval] at h
  simpa only [Nat.card_eq_fintype_card,Int.coe_castRingHom,Int.cast_natCast] using h

/-- The stratum polynomials sum to the affine-space polynomial in every rank. -/
theorem sum_fittingPolynomial (n : ℕ) :
    (∑ d ∈ range (n+1), fittingPolynomial d (n-d)) = X^(n*n) := by
  induction n with
  | zero => simp [fittingPolynomial]
  | succ n ih =>
    rw [sum_range_succ,Nat.sub_self,fittingPolynomial]
    have he (d : ℕ) (hd : d ∈ range (n+1)) :
        fittingPolynomial d (n+1-d) =
          X^n * (X^(n+1)-1) * fittingPolynomial d (n-d) := by
      have hd' : d ≤ n := Nat.le_of_lt_succ (mem_range.mp hd)
      rw [show n+1-d = (n-d)+1 by omega,fittingPolynomial,Nat.add_sub_of_le hd']
    rw [sum_congr rfl he,← mul_sum,ih]
    simp only [Nat.add_sub_cancel]
    have h₁ : (X:ℤ[X])^n * X^(n*n) = X^((n+1)*n) := by rw [← pow_add]; congr 1; ring
    have h₂ : (X:ℤ[X])^(n+1) * X^((n+1)*n) = X^((n+1)*(n+1)) := by rw [← pow_add]; congr 1; ring
    linear_combination (X^(n+1)-1)*h₁ + h₂

private theorem polynomialZeta_sum {α : Type*} (s : Finset α) (P : α → ℤ[X]) (q : ℂ) :
    polynomialCountZeta (∑ i ∈ s, P i) q = ∏ i ∈ s, polynomialCountZeta (P i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polynomialCountZeta]
  | insert i s h ih => rw [sum_insert h,prod_insert h,polynomialCountZeta_add,ih]

private theorem zeta_X_pow (n : ℕ) (q : ℂ) :
    polynomialCountZeta ((X : ℤ[X])^n) q = geom (q^n) := by
  symm
  apply (polynomialCountZeta_eq_iff _ _ _).mpr
  refine ⟨by simp [geom],?_⟩
  have he : polynomialCountSeries ((X : ℤ[X])^n) q = geomTail (q^n) := by
    ext m
    simp [polynomialCountSeries,geomTail,← pow_mul,Nat.mul_comm]
  rw [he]
  exact hasGhost_geom _

/-- Despite singularities of the nilpotent cone, its local zeta factor
is the single affine-space pole of its dimension. -/
theorem nilpotentCone_zeta (q : ℂ) (d : ℕ) :
    polynomialCountZeta (fittingPolynomial d 0) q = geom (q^(d*(d-1))) :=
  zeta_X_pow _ _

/-- All Fitting strata telescope to one pole for the ambient matrix space. -/
theorem fittingZeta_product (n : ℕ) (q : ℂ) :
    (∏ d ∈ range (n+1), polynomialCountZeta (fittingPolynomial d (n-d)) q) = geom (q^(n*n)) := by
  rw [← polynomialZeta_sum,sum_fittingPolynomial,zeta_X_pow]

end
end GaloisForLFunctions.RepresentationLifting.OperatorKernels
