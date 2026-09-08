import GaloisForLFunctions.HTGeometry.GomesPolynomialGaugeRigidity
import GaloisForLFunctions.HTGeometry.GomesWeakInvariantTensors

/-!
# Complex polynomial rigidity for compact gauge carriers

The additive-parameter obstruction in arXiv:2607.24901v1 extends the corpus's
real polynomial rigidity to arbitrary complex coefficients. Real-linear
coefficient extraction supplies the missing infrastructure. A constant sum of
polynomial norm squares forces every coordinate to be constant. Consequently,
exactly unitary polynomial matrix families on the entire real axis are constant,
as are families preserving the existing weak tensor menu.
-/

open scoped BigOperators ComplexConjugate Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Apply a real-linear coordinate functional to every complex polynomial coefficient. -/
def polynomialRealCoordinate (L : ℂ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) : Polynomial ℝ :=
  p.sum fun n c => Polynomial.monomial n (L c)

/-- Real-linear coefficient extraction commutes with evaluation on the real axis. -/
theorem polynomialRealCoordinate_eval (L : ℂ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) (x : ℝ) :
    (polynomialRealCoordinate L p).eval x = L (p.eval (x : ℂ)) := by
  classical
  unfold polynomialRealCoordinate
  rw [Polynomial.sum_def, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Complex.ofReal_pow, mul_comm (p.coeff n)]
  change L (p.coeff n) * x ^ n = L ((x ^ n) • p.coeff n)
  rw [map_smul, smul_eq_mul, mul_comm]

/-- Coefficient extraction is literal, including indices outside the polynomial support. -/
theorem polynomialRealCoordinate_coeff (L : ℂ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) (n : ℕ) :
    (polynomialRealCoordinate L p).coeff n = L (p.coeff n) := by
  classical
  simp only [polynomialRealCoordinate, Polynomial.sum, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Finset.sum_ite_eq', Polynomial.mem_support_iff]
  split_ifs with hn
  · rfl
  · simp at hn
    rw [hn, map_zero]

/-- Constant coordinate polynomials force a complex polynomial to be constant. -/
theorem polynomial_real_imag_constant_iff (p : Polynomial ℂ) :
    (polynomialRealCoordinate Complex.reCLM.toLinearMap p =
        Polynomial.C ((p.eval 0).re) ∧
      polynomialRealCoordinate Complex.imCLM.toLinearMap p =
        Polynomial.C ((p.eval 0).im)) ↔ p = Polynomial.C (p.eval 0) := by
  constructor
  · rintro ⟨hr,hi⟩
    ext n
    have hre := congrArg (fun q : Polynomial ℝ => q.coeff n) hr
    have him := congrArg (fun q : Polynomial ℝ => q.coeff n) hi
    rw [polynomialRealCoordinate_coeff] at hre him
    apply Complex.ext
    · by_cases hn : n = 0 <;> simpa [Polynomial.coeff_C, hn] using hre
    · by_cases hn : n = 0 <;> simpa [Polynomial.coeff_C, hn] using him
  · intro h
    constructor <;> ext n <;> rw [polynomialRealCoordinate_coeff]
    all_goals rw [h]; by_cases hn : n = 0 <;> simp [Polynomial.coeff_C, hn]

/-- A constant sum of complex polynomial norms on the real axis forces every entry to be constant. -/
theorem complex_polynomial_sum_normSq_constant_iff {ι : Type*} [Fintype ι]
    (p : ι → Polynomial ℂ) :
    (∀ x : ℝ, ∑ i, Complex.normSq ((p i).eval (x : ℂ)) =
      ∑ i, Complex.normSq ((p i).eval 0)) ↔
        ∀ i, p i = Polynomial.C ((p i).eval 0) := by
  classical
  let q : ι × Bool → Polynomial ℝ := fun ib =>
    polynomialRealCoordinate (if ib.2 then Complex.reCLM.toLinearMap else Complex.imCLM.toLinearMap) (p ib.1)
  have he (x : ℝ) : ∑ ib, ((q ib).eval x)^2 = ∑ i, Complex.normSq ((p i).eval (x : ℂ)) := by
    simp [q, Fintype.sum_prod_type, polynomialRealCoordinate_eval, Complex.normSq_apply,
      pow_two]
  constructor
  · intro h
    have hh : ∀ x : ℝ, ∑ ib, ((q ib).eval x)^2 = ∑ ib, ((q ib).eval 0)^2 := by
      intro x
      rw [he, he]
      exact h x
    have hc := (polynomial_sum_squares_constant_iff q).mp hh
    intro i
    apply (polynomial_real_imag_constant_iff (p i)).mp
    constructor
    · simpa [q, polynomialRealCoordinate_eval] using hc (i,true)
    · simpa [q, polynomialRealCoordinate_eval] using hc (i,false)
  · intro h x
    apply Finset.sum_congr rfl
    intro i hi
    have heval : (p i).eval (x : ℂ) = (p i).eval 0 := by
      conv_lhs => rw [h i, Polynomial.eval_C]
    rw [heval]

/-- Polynomial families of complex unitary matrices on the full real axis are constant. -/
theorem complex_polynomial_unitary_family_iff {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n (Polynomial ℂ)) :
    (∀ x : ℝ, (fun i j => (P i j).eval (x : ℂ)) ∈ Matrix.unitaryGroup n ℂ) ↔
      (∀ i j, P i j = Polynomial.C ((P i j).eval 0)) ∧
        (fun i j => (P i j).eval 0) ∈ Matrix.unitaryGroup n ℂ := by
  constructor
  · intro h
    have hc (j : n) (x : ℝ) : ∑ i, Complex.normSq ((P i j).eval (x : ℂ)) = 1 := by
      have hu := Matrix.mem_unitaryGroup_iff'.mp (h x)
      have hh := congrFun (congrFun hu j) j
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, ite_true] at hh
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
        Complex.ofReal_one, Complex.star_def] using hh
    refine ⟨?_, h 0⟩
    intro i j
    apply (complex_polynomial_sum_normSq_constant_iff (fun k => P k j)).mp _ i
    intro x
    exact (hc j x).trans (hc j 0).symm
  · rintro ⟨h,h0⟩ x
    have he : (fun i j => (P i j).eval (x : ℂ)) = (fun i j => (P i j).eval 0) := by
      funext i j
      conv_lhs => rw [h i j, Polynomial.eval_C]
    rw [he]
    exact h0

/-- A polynomial weak-tensor symmetry family has no nonconstant real parameter. -/
theorem weakTensorMenu_polynomial_rigidity (P : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) :
    (∀ x : ℝ,
      (∀ H K, weakHermitianContraction (Matrix.mulVec (fun i j => (P i j).eval (x : ℂ)) H)
        (Matrix.mulVec (fun i j => (P i j).eval (x : ℂ)) K) = weakHermitianContraction H K) ∧
      ∀ H K, weakVolumeContraction (Matrix.mulVec (fun i j => (P i j).eval (x : ℂ)) H)
        (Matrix.mulVec (fun i j => (P i j).eval (x : ℂ)) K) = weakVolumeContraction H K) ↔
    (∀ i j, P i j = Polynomial.C ((P i j).eval 0)) ∧
      (fun i j => (P i j).eval 0) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  simp only [weakTensorMenu_reconstructs_specialUnitary]
  constructor
  · intro h
    have hu := (complex_polynomial_unitary_family_iff P).mp
      (fun x => Matrix.specialUnitaryGroup_le_unitaryGroup (h x))
    exact ⟨hu.1, h 0⟩
  · rintro ⟨h,h0⟩ x
    have he : (fun i j => (P i j).eval (x : ℂ)) = (fun i j => (P i j).eval 0) := by
      funext i j
      conv_lhs => rw [h i j, Polynomial.eval_C]
    rw [he]
    exact h0

/-- An exact polynomial real parameterization of a unitary family exists exactly for constant families. -/
theorem unitary_family_polynomial_iff_constant {n : Type*} [Fintype n] [DecidableEq n]
    (U : ℝ → Matrix.unitaryGroup n ℂ) :
    (∃ P : Matrix n n (Polynomial ℂ), ∀ x : ℝ,
      (fun i j => (P i j).eval (x : ℂ)) = (U x : Matrix n n ℂ)) ↔
        ∀ x, U x = U 0 := by
  constructor
  · rintro ⟨P,hP⟩
    have hc := (complex_polynomial_unitary_family_iff P).mp
      (fun x => hP x ▸ (U x).property)
    intro x
    apply Subtype.ext
    ext i j
    have hx := congrFun (congrFun (hP x) i) j
    have hz := congrFun (congrFun (hP 0) i) j
    rw [hc.1 i j, Polynomial.eval_C] at hx
    exact hx.symm.trans hz
  · intro h
    refine ⟨fun i j => Polynomial.C ((U 0 : Matrix n n ℂ) i j), ?_⟩
    intro x
    rw [h x]
    ext i j
    exact Polynomial.eval_C

end GaloisForLFunctions.HTGeometry
