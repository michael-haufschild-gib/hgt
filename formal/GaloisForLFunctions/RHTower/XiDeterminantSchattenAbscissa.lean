import GaloisForLFunctions.RHTower.XiDeterminantIdealConsequences

/-!
# Exact Schatten abscissa forced by an Xi determinant

Every self-adjoint Hilbert--Carleman realization of `XiC` has approximation numbers in every
Schatten class strictly above exponent one and in no positive class at or below one.  Thus its
exact Schatten abscissa is one.  The uniqueness lemma below isolates the reusable obstruction:
no operator can have two distinct positive exact Schatten abscissae.
-/

open Complex Set Filter
open HilbertSchmidt

namespace RHTower

noncomputable section

/-- A positive number `sigma` is the exact Schatten abscissa of `T` when, for every positive
exponent, membership holds exactly to the right of `sigma`. -/
def HasExactSchattenAbscissa {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (sigma : ℝ) : Prop :=
  ∀ {q : ℝ}, 0 < q → (MemSchattenClass q T ↔ sigma < q)

/-- A bounded operator has at most one positive exact Schatten abscissa. -/
theorem HasExactSchattenAbscissa.eq_of_pos
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {T : H →L[ℂ] H} {sigma tau : ℝ}
    (hsigma : HasExactSchattenAbscissa T sigma)
    (htau : HasExactSchattenAbscissa T tau)
    (hsigma_pos : 0 < sigma) (htau_pos : 0 < tau) :
    sigma = tau := by
  rcases lt_trichotomy sigma tau with hlt | heq | hgt
  · have hmem : MemSchattenClass tau T :=
      (hsigma htau_pos).2 hlt
    exact False.elim ((htau htau_pos).1 hmem |>.ne rfl)
  · exact heq
  · have hmem : MemSchattenClass sigma T :=
      (htau hsigma_pos).2 hgt
    exact False.elim ((hsigma hsigma_pos).1 hmem |>.ne rfl)

/-- Every exact self-adjoint Hilbert--Carleman realization of `XiC` has exact Schatten
abscissa one. -/
theorem exactXiDeterminant_hasExactSchattenAbscissa_one
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) :
    HasExactSchattenAbscissa (toOperator hK) 1 := by
  intro q hq
  constructor
  · intro hmem
    by_contra hnlt
    have hq_one : q ≤ 1 := le_of_not_gt hnlt
    exact exactXiDeterminant_not_memSchattenClass_one
      hK hself H hHanalytic hH hXi
      (hmem.mono hq hq_one)
  · exact exactXiDeterminant_memSchattenClass
      hK hself H hHanalytic hH hXi

/-- An exact Xi determinant carrier cannot simultaneously have any exact positive Schatten
threshold strictly larger than one. -/
theorem exactXiDeterminant_not_hasExactSchattenAbscissa
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z)
    {tau : ℝ} (htau : 1 < tau) :
    ¬ HasExactSchattenAbscissa (toOperator hK) tau := by
  intro hcarrier
  have heq : (1 : ℝ) = tau :=
    HasExactSchattenAbscissa.eq_of_pos
      (exactXiDeterminant_hasExactSchattenAbscissa_one
        hK hself H hHanalytic hH hXi) hcarrier
      (by norm_num) (lt_trans (by norm_num) htau)
  exact (ne_of_lt htau) heq

end

end RHTower
