import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryMatrix
import GaloisForLFunctions.HTGeometry.DerivationIterateLeibniz

/-!
# Component-jet transport for the full Baker auxiliary polynomial

`PolynomialAuxiliaryMatrix` uses a closed binomial expression for the additive component jet.
This module proves that expression is not merely an integral surrogate: it is exactly the value
obtained by iterating the solved constant component, together with the diagonal nonconstant
components.  It packages a canonical component-jet monomial whose shift laws are literal
derivation identities, and evaluates it at the algebraic natural samples used by the matrix.

This closes the algebraic link from full Siegel matrix rows to genuine component values.  The next
module transports kernel equations through the chosen complex embedding and the analytic curve.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

/-- Exact iterated action of the constant component on the additive generator. -/
theorem SolvedRelation.componentDerivation_none_iterate_X_pow
    (R : SolvedRelation) (c : ℤ) (a k : ℕ) :
    (R.componentDerivation c none)^[k] (MvPolynomial.X none ^ a) =
      MvPolynomial.C ((a.descFactorial k : R.CoefficientField) *
        R.integerScalar c ^ k) * MvPolynomial.X none ^ (a - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Derivation.leibniz,
        MvPolynomial.derivation_C]
      rw [(R.componentDerivation c none).leibniz_pow]
      rw [R.componentDerivation_X]
      simp only [SolvedRelation.componentVector, nsmul_eq_mul, smul_eq_mul,
        MvPolynomial.C_mul, mul_zero, add_zero]
      rw [Nat.descFactorial_succ, Nat.sub_sub, Nat.cast_mul, pow_succ]
      simp only [MvPolynomial.C_mul]
      have hcast : ((a - k : ℕ) : MvPolynomial R.Variable R.CoefficientField) =
          MvPolynomial.C ((a - k : ℕ) : R.CoefficientField) := by
        exact (map_natCast (MvPolynomial.C : R.CoefficientField →+*
          MvPolynomial R.Variable R.CoefficientField) (a - k)).symm
      rw [hcast]
      ring

/-- Exact iterated diagonal action of the constant component on an exponential monomial. -/
theorem SolvedRelation.componentDerivation_none_iterate_exponentialMonomial
    (R : SolvedRelation) (c : ℤ) {V : ℕ} (m : R.ExponentialColumn V) (q : ℕ) :
    (R.componentDerivation c none)^[q] (R.exponentialMonomial m) =
      MvPolynomial.C (R.componentEigenvalue c none m ^ q) * R.exponentialMonomial m := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Function.iterate_succ_apply', ih, Derivation.leibniz,
        MvPolynomial.derivation_C, R.componentDerivation_exponentialMonomial]
      simp only [smul_eq_mul]
      rw [pow_succ]
      rw [MvPolynomial.C_mul]
      ring

/-- The binomial lowering/diagonal formula for an iterated constant component. -/
theorem SolvedRelation.componentDerivation_none_iterate_additivePowerMonomial
    (R : SolvedRelation) (c : ℤ) {V : ℕ}
    (a r : ℕ) (m : R.ExponentialColumn V) :
    (R.componentDerivation c none)^[r]
        (MvPolynomial.X none ^ a * R.exponentialMonomial m) =
      ∑ k ∈ Finset.range (r + 1),
        MvPolynomial.C ((Nat.choose r k : R.CoefficientField) *
          (a.descFactorial k : R.CoefficientField) * R.integerScalar c ^ k *
            R.componentEigenvalue c none m ^ (r - k)) *
          (MvPolynomial.X none ^ (a - k) * R.exponentialMonomial m) := by
  rw [GaloisForLFunctions.HTGeometry.derivation_iterate_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [R.componentDerivation_none_iterate_X_pow,
    R.componentDerivation_none_iterate_exponentialMonomial]
  simp only [nsmul_eq_mul, MvPolynomial.C_mul]
  have hcast : ((Nat.choose r k : ℕ) :
      MvPolynomial R.Variable R.CoefficientField) =
      MvPolynomial.C ((Nat.choose r k : ℕ) : R.CoefficientField) := by
    exact (map_natCast (MvPolynomial.C : R.CoefficientField →+*
      MvPolynomial R.Variable R.CoefficientField) (Nat.choose r k)).symm
  rw [hcast]
  ring

/-- Algebraic point of the auxiliary curve at a natural sample. -/
noncomputable def SolvedRelation.algebraicSamplePoint
    (R : SolvedRelation) (sample : ℕ) : R.Variable → R.CoefficientField
  | none => sample
  | some i => R.baseLift i ^ sample

theorem SolvedRelation.eval_algebraicSample_exponentialMonomial
    (R : SolvedRelation) {V : ℕ} (sample : ℕ) (m : R.ExponentialColumn V) :
    MvPolynomial.eval (R.algebraicSamplePoint sample) (R.exponentialMonomial m) =
      ∏ i, R.baseLift i ^ ((m i : ℕ) * sample) := by
  simp [SolvedRelation.exponentialMonomial, SolvedRelation.algebraicSamplePoint,
    pow_mul, mul_comm]

/-- Evaluation of the iterated constant component is the closed matrix jet coefficient. -/
theorem SolvedRelation.eval_algebraicSample_none_iterate_additivePowerMonomial
    (R : SolvedRelation) (c : ℤ) {V : ℕ}
    (a r sample : ℕ) (m : R.ExponentialColumn V) :
    MvPolynomial.eval (R.algebraicSamplePoint sample)
        ((R.componentDerivation c none)^[r]
          (MvPolynomial.X none ^ a * R.exponentialMonomial m)) =
      R.constantJetCoefficient c r a sample m *
        ∏ i, R.baseLift i ^ ((m i : ℕ) * sample) := by
  rw [R.componentDerivation_none_iterate_additivePowerMonomial]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_pow,
    MvPolynomial.eval_X]
  calc
    _ = ∑ x ∈ Finset.range (r + 1),
        R.constantJetTerm c r a sample x m *
          MvPolynomial.eval (R.algebraicSamplePoint sample) (R.exponentialMonomial m) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [SolvedRelation.constantJetTerm, SolvedRelation.algebraicSamplePoint]
      ring
    _ = (∑ x ∈ Finset.range (r + 1), R.constantJetTerm c r a sample x m) *
        MvPolynomial.eval (R.algebraicSamplePoint sample) (R.exponentialMonomial m) := by
      rw [Finset.sum_mul]
    _ = _ := by
      rw [R.eval_algebraicSample_exponentialMonomial]
      rfl

/-- Canonical polynomial representing a complete solved component jet of one basis monomial. -/
noncomputable def SolvedRelation.componentJetMonomial
    (R : SolvedRelation) (c : ℤ) {V : ℕ}
    (nu : R.Direction → ℕ) (a : ℕ) (m : R.ExponentialColumn V) :
    MvPolynomial R.Variable R.CoefficientField :=
  MvPolynomial.C (R.nonconstantEigenProduct c nu m) *
    (R.componentDerivation c none)^[nu none]
      (MvPolynomial.X none ^ a * R.exponentialMonomial m)

/-- Increment one coordinate of a component multi-index. -/
def SolvedRelation.componentBump
    (R : SolvedRelation) (nu : R.Direction → ℕ) (dir : R.Direction) :
    R.Direction → ℕ :=
  fun e => if e = dir then nu e + 1 else nu e

/-- The constant component shifts its canonical jet index. -/
theorem SolvedRelation.componentDerivation_none_componentJetMonomial
    (R : SolvedRelation) (c : ℤ) {V : ℕ}
    (nu : R.Direction → ℕ) (a : ℕ) (m : R.ExponentialColumn V) :
    R.componentDerivation c none (R.componentJetMonomial c nu a m) =
      R.componentJetMonomial c (R.componentBump nu none) a m := by
  unfold SolvedRelation.componentJetMonomial SolvedRelation.componentBump
  simp only [Derivation.leibniz, MvPolynomial.derivation_C, smul_eq_mul,
    mul_zero, add_zero]
  have hiter : R.componentDerivation c none
      ((R.componentDerivation c none)^[nu none]
        (MvPolynomial.X none ^ a * R.exponentialMonomial m)) =
      (R.componentDerivation c none)^[nu none + 1]
        (MvPolynomial.X none ^ a * R.exponentialMonomial m) := by
    symm
    exact Function.iterate_succ_apply' (R.componentDerivation c none) (nu none) _
  rw [hiter]
  simp [SolvedRelation.nonconstantEigenProduct]

/-- A nonconstant component acts diagonally on an arbitrary additive-power monomial. -/
theorem SolvedRelation.componentDerivation_some_additivePowerMonomial
    (R : SolvedRelation) (c : ℤ) (j : R.NonPivot) {V : ℕ}
    (a : ℕ) (m : R.ExponentialColumn V) :
    R.componentDerivation c (some j)
      (MvPolynomial.X none ^ a * R.exponentialMonomial m) =
      MvPolynomial.C (R.componentEigenvalue c (some j) m) *
        (MvPolynomial.X none ^ a * R.exponentialMonomial m) := by
  rw [Derivation.leibniz, R.componentDerivation_exponentialMonomial]
  have hX : R.componentDerivation c (some j) (MvPolynomial.X none) = 0 := by
    rw [R.componentDerivation_X]
    simp [SolvedRelation.componentVector]
  rw [(R.componentDerivation c (some j)).leibniz_pow, hX]
  simp only [nsmul_eq_mul, smul_eq_mul, mul_zero]
  ring

/-- Constant-component iterates commute with multiplication by a scalar polynomial coefficient. -/
theorem SolvedRelation.componentDerivation_none_iterate_C_mul
    (R : SolvedRelation) (c : ℤ) (x : R.CoefficientField)
    (P : MvPolynomial R.Variable R.CoefficientField) (r : ℕ) :
    (R.componentDerivation c none)^[r] (MvPolynomial.C x * P) =
      MvPolynomial.C x * (R.componentDerivation c none)^[r] P := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, Derivation.leibniz,
        MvPolynomial.derivation_C]
      simp only [smul_eq_mul, mul_zero, add_zero]
      rw [← Function.iterate_succ_apply' (R.componentDerivation c none) r P]

/-- Incrementing a nonconstant jet coordinate inserts exactly its eigenvalue. -/
theorem SolvedRelation.nonconstantEigenProduct_bump_some
    (R : SolvedRelation) (c : ℤ) {V : ℕ}
    (nu : R.Direction → ℕ) (j : R.NonPivot) (m : R.ExponentialColumn V) :
    R.nonconstantEigenProduct c (R.componentBump nu (some j)) m =
      R.nonconstantEigenProduct c nu m * R.componentEigenvalue c (some j) m := by
  let e : R.NonPivot → R.CoefficientField :=
    fun i => R.componentEigenvalue c (some i) m
  have hrest : (∏ i ∈ (Finset.univ : Finset R.NonPivot).erase j,
      e i ^ (R.componentBump nu (some j) (some i))) =
      ∏ i ∈ (Finset.univ : Finset R.NonPivot).erase j, e i ^ nu (some i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    simp [SolvedRelation.componentBump, hij]
  unfold SolvedRelation.nonconstantEigenProduct
  change (∏ i : R.NonPivot, e i ^ R.componentBump nu (some j) (some i)) =
    (∏ i : R.NonPivot, e i ^ nu (some i)) * e j
  rw [← Finset.prod_erase_mul (Finset.univ : Finset R.NonPivot)
    (fun i => e i ^ R.componentBump nu (some j) (some i)) (Finset.mem_univ j)]
  rw [hrest]
  simp only [SolvedRelation.componentBump, if_pos]
  rw [pow_succ]
  rw [← Finset.prod_erase_mul (Finset.univ : Finset R.NonPivot)
    (fun i => e i ^ nu (some i)) (Finset.mem_univ j)]
  ring

/-- Every nonconstant component shifts its canonical jet index. -/
theorem SolvedRelation.componentDerivation_some_componentJetMonomial
    (R : SolvedRelation) (c : ℤ) (j : R.NonPivot) {V : ℕ}
    (nu : R.Direction → ℕ) (a : ℕ) (m : R.ExponentialColumn V) :
    R.componentDerivation c (some j) (R.componentJetMonomial c nu a m) =
      R.componentJetMonomial c (R.componentBump nu (some j)) a m := by
  have hcomm : Function.Commute (R.componentDerivation c (some j))
      (R.componentDerivation c none) := by
    intro P
    exact R.componentDerivation_comm c (some j) none P
  have hmove : R.componentDerivation c (some j)
      ((R.componentDerivation c none)^[nu none]
        (MvPolynomial.X none ^ a * R.exponentialMonomial m)) =
      (R.componentDerivation c none)^[nu none]
        (R.componentDerivation c (some j)
          (MvPolynomial.X none ^ a * R.exponentialMonomial m)) := by
    exact (hcomm.iterate_right (nu none)).eq
      (MvPolynomial.X none ^ a * R.exponentialMonomial m)
  have hnone : R.componentBump nu (some j) none = nu none := by
    simp [SolvedRelation.componentBump]
  unfold SolvedRelation.componentJetMonomial
  rw [Derivation.leibniz, MvPolynomial.derivation_C]
  simp only [smul_eq_mul]
  rw [hmove, R.componentDerivation_some_additivePowerMonomial,
    R.componentDerivation_none_iterate_C_mul, hnone,
    R.nonconstantEigenProduct_bump_some]
  rw [MvPolynomial.C_mul]
  ring

/-- Algebraic sample value of a canonical component jet equals its full matrix coefficient. -/
theorem SolvedRelation.eval_algebraicSample_componentJetMonomial
    (R : SolvedRelation) (c : ℤ) {V : ℕ}
    (nu : R.Direction → ℕ) (a sample : ℕ) (m : R.ExponentialColumn V) :
    MvPolynomial.eval (R.algebraicSamplePoint sample)
      (R.componentJetMonomial c nu a m) =
      R.additiveComponentJetCoefficient c nu a sample m *
        ∏ i, R.baseLift i ^ ((m i : ℕ) * sample) := by
  unfold SolvedRelation.componentJetMonomial
  rw [map_mul, MvPolynomial.eval_C,
    R.eval_algebraicSample_none_iterate_additivePowerMonomial]
  unfold SolvedRelation.additiveComponentJetCoefficient
  ring

end GaloisForLFunctions.RHTower.BakerGeneralProof
