import GaloisForLFunctions.BiarithmeticGeometry.Affine.MonomialMatrixFaithfulness
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAffineAxisFrames

/-!
# Canonical exponents and faithfulness of multivariate moment coordinates

The chain ordering enumerates distinct ordinary multivariate monomials.
Encoding their full exponent tuples connects the explicit moment matrices
to polynomial coefficient recovery: their action on physical moment vectors
determines every matrix entry.
-/

open Matrix
open scoped BigOperators
open GaloisForLFunctions.HilbertMetric

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Exponents in the coordinate order consisting of vertical, distinguished, then transverse variables. -/
def axisExponentTuple {r k : ℕ} (a : AffineAxisIndex r k) : Fin (r + 2) → ℕ :=
  Fin.cons a.2.2.val (Fin.cons (chainDegree a.2.1 - a.2.2.val) (chainExponent a.2.1))

theorem sum_axisExponentTuple {r k : ℕ} (a : AffineAxisIndex r k) :
    (∑ i, axisExponentTuple a i) = a.1.val + 1 := by
  rw [Fin.sum_univ_succ]
  simp only [axisExponentTuple, Fin.cons_zero, Fin.cons_succ]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have h := sum_chainExponent_add_degree r (a.1.val + 1) a.2.1
  have hv := a.2.2.isLt
  omega

/-- The chain labels distinguish every full exponent tuple. -/
theorem axisExponentTuple_injective (r k : ℕ) :
    Function.Injective (axisExponentTuple (r := r) (k := k)) := by
  intro a b h
  have hs : a.1.val + 1 = b.1.val + 1 := by
    rw [← sum_axisExponentTuple a, ← sum_axisExponentTuple b, h]
  rcases a with ⟨d, a, i⟩
  rcases b with ⟨e, b, j⟩
  have hde : d = e := Fin.ext (by change d.val + 1 = e.val + 1 at hs; omega)
  subst e
  have hβ : chainExponent a = chainExponent b := by
    funext l
    exact congrFun h l.succ.succ
  have hab := chainExponent_injective r (d.val + 1) hβ
  subst b
  have hij : i = j := Fin.ext (congrFun h 0)
  subst j
  rfl

/-- Every positive exponent tuple within the degree bound occurs among the moment coordinates. -/
theorem exists_axisExponentTuple (r k : ℕ) (α : Fin (r + 2) → ℕ)
    (hpos : 0 < ∑ i, α i) (hbound : ∑ i, α i ≤ k) :
    ∃ a : AffineAxisIndex r k, axisExponentTuple a = α := by
  have hsum : (∑ i, α i) = α 0 + (α (Fin.succ 0) + ∑ i : Fin r, α i.succ.succ) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  let d : Fin k := ⟨(∑ i, α i) - 1, by omega⟩
  have hd : d.val + 1 = ∑ i, α i := by dsimp only [d]; omega
  obtain ⟨a, ha⟩ := exists_chainExponent r (d.val + 1) (fun i => α i.succ.succ) (by omega)
  have hdegree : chainDegree a = α 0 + α (Fin.succ 0) := by
    have h := sum_chainExponent_add_degree r (d.val + 1) a
    rw [ha] at h
    change (∑ i : Fin r, α i.succ.succ) + chainDegree a = d.val + 1 at h
    omega
  refine ⟨⟨d, a, ⟨α 0, by omega⟩⟩, ?_⟩
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun l => ?_) j
    · change chainDegree a - α 0 = α (Fin.succ 0)
      omega
    · exact congrFun ha l

/-- Canonical exponent indices for every nonconstant monomial through degree `k`. -/
abbrev BoundedAxisExponents (r k : ℕ) :=
  {α : Fin (r + 2) → ℕ // 0 < ∑ i, α i ∧ ∑ i, α i ≤ k}

private theorem axisExponentTuple_bounds {r k : ℕ} (a : AffineAxisIndex r k) :
    0 < ∑ i, axisExponentTuple a i ∧ ∑ i, axisExponentTuple a i ≤ k := by
  rw [sum_axisExponentTuple]
  have h := a.1.isLt
  omega

/-- The chain ordering is exactly the ordinary bounded positive monomial basis. -/
def axisExponentEquiv (r k : ℕ) : AffineAxisIndex r k ≃ BoundedAxisExponents r k where
  toFun a := ⟨axisExponentTuple a, axisExponentTuple_bounds a⟩
  invFun α := Classical.choose (exists_axisExponentTuple r k α.val α.property.1 α.property.2)
  left_inv a := by
    apply axisExponentTuple_injective r k
    exact Classical.choose_spec (exists_axisExponentTuple r k (axisExponentTuple a)
      (axisExponentTuple_bounds a).1 (axisExponentTuple_bounds a).2)
  right_inv α := by
    apply Subtype.ext
    exact Classical.choose_spec (exists_axisExponentTuple r k α.val α.property.1 α.property.2)

/-- The full exponent vector as a finitely supported multivariate-polynomial index. -/
def axisMonomialExponent {r k : ℕ} (a : AffineAxisIndex r k) : Fin (r + 2) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (axisExponentTuple a)

theorem axisMonomialExponent_injective (r k : ℕ) :
    Function.Injective (axisMonomialExponent (r := r) (k := k)) := by
  intro a b h
  apply axisExponentTuple_injective r k
  funext i
  exact DFunLike.congr_fun h i

/-- Ordinary monomial evaluation agrees exactly with the explicit affine moment coordinates. -/
theorem axisMonomialFeature_eq (r k : ℕ) (a : AffineAxisIndex r k) (u : Fin (r + 2) → ℝ) :
    monomialFeature axisMonomialExponent a u =
      affineAxisMoment r k (fun i => u i.succ.succ) (u (Fin.succ 0)) (u 0) a := by
  rw [monomialFeature, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun i => pow_zero (u i)), one_mul]
  change (∏ i, u i ^ axisExponentTuple a i) = _
  rw [Fin.prod_univ_succ]
  simp only [axisExponentTuple, Fin.cons_zero, Fin.cons_succ]
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  change u 0 ^ a.2.2.val * (u (Fin.succ 0) ^ (chainDegree a.2.1 - a.2.2.val) *
    ∏ i, u i.succ.succ ^ chainExponent a.2.1 i) =
    (∏ i, u i.succ.succ ^ chainExponent a.2.1 i) *
      (u (Fin.succ 0) ^ (chainDegree a.2.1 - a.2.2.val) * u 0 ^ a.2.2.val)
  ring

/-- Agreement on the actual moment image determines the whole matrix in every dimension and degree. -/
theorem matrix_eq_of_affineAxisMoment_eq (r k : ℕ)
    (M N : Matrix (AffineAxisIndex r k) (AffineAxisIndex r k) ℝ)
    (h : ∀ (y : Fin r → ℝ) (x z : ℝ),
      M *ᵥ affineAxisMoment r k y x z = N *ᵥ affineAxisMoment r k y x z) : M = N := by
  apply matrix_eq_of_monomial_mulVec_eq axisMonomialExponent (axisMonomialExponent_injective r k)
  intro u
  simpa only [axisMonomialFeature_eq] using h (fun i => u i.succ.succ) (u (Fin.succ 0)) (u 0)

#print axioms sum_axisExponentTuple
#print axioms axisExponentTuple_injective
#print axioms exists_axisExponentTuple
#print axioms axisExponentEquiv
#print axioms axisMonomialExponent_injective
#print axioms axisMonomialFeature_eq
#print axioms matrix_eq_of_affineAxisMoment_eq

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
