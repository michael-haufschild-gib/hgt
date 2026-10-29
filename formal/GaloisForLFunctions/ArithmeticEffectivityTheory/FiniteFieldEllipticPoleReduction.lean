import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticCharts

/-!
# Leading-term cancellation at the elliptic infinity place

The linear encoding `p(x)+q(x)y ↦ p(T²)+T³q(T²)` preserves pole degree.
Its two summands have degrees of opposite parity. Ordinary polynomial
leading-term cancellation therefore gives a unique constant residue at infinity.
-/

open Polynomial

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

noncomputable section

/-- A linear polynomial encoding of affine functions, with the pole weights of `x` and `y`. -/
def polePolynomial (p q : Constants[X]) : Constants[X] :=
  p.comp (X ^ 2) + q.comp (X ^ 2) * X ^ 3

private lemma degree_comp_square (p : Constants[X]) :
    (p.comp (X ^ 2)).degree = 2 • p.degree := by
  rw [degree_comp (by norm_num), degree_X_pow]
  change p.degree * 2 = 2 • p.degree
  rw [two_nsmul, mul_two]

private lemma pole_weights_ne (p q : Constants[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    2 • p.degree ≠ 2 • q.degree + 3 := by
  rw [degree_eq_natDegree hp, degree_eq_natDegree hq]
  intro h
  rw [two_nsmul, two_nsmul] at h
  have he : p.natDegree + p.natDegree = q.natDegree + q.natDegree + 3 := by
    exact_mod_cast h
  omega

/-- The polynomial encoding has exactly the actual norm pole degree. -/
lemma degree_polePolynomial (p q : Constants[X]) :
    (polePolynomial p q).degree = poleDegree (p • (1 : A) + q • yA) := by
  rw [poleDegree_basis]
  by_cases hp : p = 0
  · simp [hp, polePolynomial, degree_mul, degree_comp_square]
  by_cases hq : q = 0
  · simp [hq, polePolynomial, degree_comp_square]
  have hqdeg : (q.comp (X ^ 2) * X ^ 3).degree = 2 • q.degree + 3 := by
    rw [degree_mul, degree_comp_square, degree_X_pow]
    rfl
  rcases lt_or_gt_of_ne (pole_weights_ne p q hp hq) with hlt | hgt
  · rw [polePolynomial, degree_add_eq_right_of_degree_lt
      (by rw [degree_comp_square, hqdeg]; exact hlt), hqdeg, max_eq_right_of_lt hlt]
  · rw [polePolynomial, degree_add_eq_left_of_degree_lt
      (by rw [degree_comp_square, hqdeg]; exact hgt), degree_comp_square, max_eq_left_of_lt hgt]

lemma polePolynomial_sub (p q r s : Constants[X]) (c : Constants) :
    polePolynomial (p - C c * r) (q - C c * s) =
      polePolynomial p q - C c * polePolynomial r s := by
  simp only [polePolynomial, sub_comp, mul_comp, C_comp]
  ring

private lemma polynomial_scalar_reduction (p q : Constants[X]) (hq : q ≠ 0)
    (hdeg : p.degree ≤ q.degree) :
    ∃ c : Constants, (p - C c * q).degree < q.degree := by
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact ⟨0, by simpa using hlt⟩
  have hp : p ≠ 0 := by
    intro hp
    rw [hp, degree_zero] at heq
    exact hq (degree_eq_bot.mp heq.symm)
  let c := p.leadingCoeff / q.leadingCoeff
  have hc : c ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hp) (leadingCoeff_ne_zero.mpr hq)
  refine ⟨c, (degree_sub_lt ?_ hp ?_).trans_eq heq⟩
  · rw [degree_mul, degree_C hc, zero_add, heq]
  · rw [leadingCoeff_mul, leadingCoeff_C]
    exact (div_mul_cancel₀ p.leadingCoeff (leadingCoeff_ne_zero.mpr hq)).symm

private lemma basis_sub_scalar_mul (p q r s : Constants[X]) (c : Constants) :
    (p • (1 : A) + q • yA) - algebraMap Constants A c * (r • 1 + s • yA) =
      (p - C c * r) • (1 : A) + (q - C c * s) • yA := by
  have hc : algebraMap Constants[X] A (C c) = algebraMap Constants A c :=
    (IsScalarTower.algebraMap_apply Constants Constants[X] A c).symm
  simp only [Algebra.smul_def, map_sub, map_mul, mul_one, hc]
  ring

/-- Every infinity-regular fraction has a constant residue: subtracting it strictly lowers degree. -/
theorem exists_scalar_poleDegree_sub_lt (a b : A) (hb : b ≠ 0)
    (hab : poleDegree a ≤ poleDegree b) :
    ∃ c : Constants, poleDegree (a - algebraMap Constants A c * b) < poleDegree b := by
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
  obtain ⟨r, s, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq b
  simp only [← yA_eq] at hb hab ⊢
  have henc : polePolynomial r s ≠ 0 := by
    intro hz
    apply hb
    apply (poleDegree_eq_bot_iff _).mp
    rw [← degree_polePolynomial, hz, degree_zero]
  obtain ⟨c, hc⟩ := polynomial_scalar_reduction (polePolynomial p q) (polePolynomial r s)
    henc (by simpa only [degree_polePolynomial] using hab)
  refine ⟨c, ?_⟩
  rw [basis_sub_scalar_mul, ← degree_polePolynomial, ← degree_polePolynomial, polePolynomial_sub]
  exact hc

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
