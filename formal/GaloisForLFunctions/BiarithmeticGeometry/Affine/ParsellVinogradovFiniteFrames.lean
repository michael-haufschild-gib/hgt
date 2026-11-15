import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovTransport
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

/-!
# Unipotent Parsell–Vinogradov frames on finite polynomial jets

Affine shear and translation preserve total degree. On polynomials with
zero constant coefficient, the centered frame minus identity lowers the
vertical degree whenever its value is nonzero. Its `(d+1)`-st power thus
vanishes on degree-`d` jets, and its determinant is one.

This proves the finite-frame determinant mechanism of Bi–Sun,
Proposition 2.1, in every dimension and degree.
-/

open MvPolynomial
open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Substitution by affine coordinate polynomials never raises total degree. -/
theorem totalDegree_algHom_le {σ τ R : Type*} [CommRing R]
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hF : ∀ i, (F (X i)).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (F p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [monomial_eq, map_mul, algHom_C, algebraMap_eq, Finsupp.prod, map_prod]
  simp only [map_pow]
  calc
    (C (coeff e p) * ∏ i ∈ e.support, F (X i) ^ e i).totalDegree
        ≤ (∏ i ∈ e.support, F (X i) ^ e i).totalDegree := by
      simpa only [totalDegree_C, zero_add] using
        totalDegree_mul (C (coeff e p)) (∏ i ∈ e.support, F (X i) ^ e i)
    _ ≤ ∑ i ∈ e.support, (F (X i) ^ e i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ e.support, e i := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (e i) (hF i))
    _ = e.sum (fun _ n => n) := rfl
    _ ≤ p.totalDegree := le_totalDegree he

variable {ι : Type*} [Fintype ι]

/-- The total-degree filtration is invariant under the polynomial frame. -/
theorem pull_totalDegree_le (θ : ι → ℝ) (t : ℝ) (p : MvPolynomial (Option ι) ℝ) :
    (pull θ t p).totalDegree ≤ p.totalDegree := by
  have hs : (shearForm θ).totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro i _
    simpa only [totalDegree_C, totalDegree_X, zero_add] using
      totalDegree_mul (C (θ i)) (X (some i))
  apply totalDegree_algHom_le _ _ p
  intro j
  cases j with
  | none =>
      rw [pull_vertical]
      exact (totalDegree_add _ _).trans (max_le
        ((totalDegree_add _ _).trans (max_le (by simp) hs)) (by simp))
  | some i => simp only [pull_horizontal, totalDegree_X, le_refl]

/-- Removing the constant term preserves the same degree bound. -/
theorem centeredPull_totalDegree_le (θ : ι → ℝ) (t : ℝ)
    (p : MvPolynomial (Option ι) ℝ) :
    (centeredPull θ t p).totalDegree ≤ p.totalDegree := by
  exact (totalDegree_sub _ _).trans (max_le (pull_totalDegree_le θ t p) (by simp))

/-- Centered pullback as a linear map on the full polynomial space. -/
def centeredPullLinear (θ : ι → ℝ) (t : ℝ) :
    MvPolynomial (Option ι) ℝ →ₗ[ℝ] MvPolynomial (Option ι) ℝ where
  toFun := centeredPull θ t
  map_add' p q := by
    simp only [centeredPull, map_add]
    abel
  map_smul' r p := by
    simp only [centeredPull, smul_eq_C_mul, map_mul, pull_constant, eval_C, RingHom.id_apply]
    ring

/-- Polynomials of bounded total degree with zero constant coefficient. -/
def jetSpace (ι : Type*) [Fintype ι] (d : ℕ) : Submodule ℝ (MvPolynomial (Option ι) ℝ) :=
  restrictTotalDegree (Option ι) ℝ d ⊓
    LinearMap.ker (MvPolynomial.aeval (0 : Option ι → ℝ)).toLinearMap

abbrev Jet (ι : Type*) [Fintype ι] (d : ℕ) := ↥(jetSpace ι d)

instance (d : ℕ) : Module.Finite ℝ (Jet ι d) :=
  Module.Finite.of_injective
    (Submodule.inclusion (show jetSpace ι d ≤ restrictTotalDegree (Option ι) ℝ d from inf_le_left))
    (Submodule.inclusion_injective _)

/-- The finite-dimensional centered frame. -/
def frame (θ : ι → ℝ) (t : ℝ) (d : ℕ) : Module.End ℝ (Jet ι d) :=
  (centeredPullLinear θ t).restrict (fun p hp => by
    constructor
    · apply (mem_restrictTotalDegree _ _ _).mpr
      exact (centeredPull_totalDegree_le θ t p).trans ((mem_restrictTotalDegree _ _ _).mp hp.1)
    · change eval (0 : Option ι → ℝ) (centeredPull θ t p) = 0
      exact centeredPull_at_zero θ t p)

@[simp] theorem frame_coe (θ : ι → ℝ) (t : ℝ) (d : ℕ) (p : Jet ι d) :
    (frame θ t d p : MvPolynomial (Option ι) ℝ) = centeredPull θ t p.val := rfl

/-- Composition agrees with addition of frame parameters on every jet space. -/
theorem frame_comp (θ φ : ι → ℝ) (t s : ℝ) (d : ℕ) :
    (frame θ t d).comp (frame φ s d) = frame (θ + φ) (t + s) d := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  exact centeredPull_comp θ φ t s p.val

@[simp] theorem frame_zero (d : ℕ) : frame (0 : ι → ℝ) 0 d = 1 := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  have hp : eval (0 : Option ι → ℝ) p.val = 0 := p.property.2
  change centeredPull 0 0 p.val = p.val
  simp only [centeredPull, pull_zero, AlgHom.id_apply, hp, map_zero, sub_zero]

/-- Negating both parameters gives the inverse frame on every finite jet space. -/
def frameEquiv (θ : ι → ℝ) (t : ℝ) (d : ℕ) : Jet ι d ≃ₗ[ℝ] Jet ι d where
  toFun := fun p => frame θ t d p
  map_add' := (frame θ t d).map_add
  map_smul' := (frame θ t d).map_smul
  invFun := frame (-θ) (-t) d
  left_inv p := by
    have h := DFunLike.congr_fun (frame_comp (-θ) θ (-t) t d) p
    simpa only [neg_add_cancel, frame_zero, LinearMap.comp_apply, Module.End.one_apply] using h
  right_inv p := by
    have h := DFunLike.congr_fun (frame_comp θ (-θ) t (-t) d) p
    simpa only [add_neg_cancel, frame_zero, LinearMap.comp_apply, Module.End.one_apply] using h

@[simp] theorem frameEquiv_toLinearMap (θ : ι → ℝ) (t : ℝ) (d : ℕ) :
    (frameEquiv θ t d).toLinearMap = frame θ t d := rfl

/-- The affine horizontal polynomial added to the vertical variable. -/
def horizontalShift (θ : ι → ℝ) (t : ℝ) : MvPolynomial ι ℝ :=
  (∑ i, C (θ i) * X i) + C t

/-- Treating the vertical coordinate as the polynomial variable turns the frame into Taylor shift. -/
theorem optionEquivLeft_pull (θ : ι → ℝ) (t : ℝ) (p : MvPolynomial (Option ι) ℝ) :
    optionEquivLeft ℝ ι (pull θ t p) =
      Polynomial.taylor (horizontalShift θ t) (optionEquivLeft ℝ ι p) := by
  have h : (optionEquivLeft ℝ ι).toAlgHom.comp (pull θ t) =
      ((Polynomial.taylorAlgHom (horizontalShift θ t)).restrictScalars ℝ).comp
        (optionEquivLeft ℝ ι).toAlgHom := by
    ext j
    cases j with
    | none =>
        simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
          pull_vertical, map_add, optionEquivLeft_X_none, optionEquivLeft_C,
          AlgHom.restrictScalars_apply, Polynomial.taylorAlgHom_apply, Polynomial.taylor_X]
        simp only [shearForm, map_sum, map_mul, optionEquivLeft_C, optionEquivLeft_X_some,
          horizontalShift]
        simp only [map_add, map_sum, map_mul]
        abel_nf
    | some i =>
        simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
          pull_horizontal, optionEquivLeft_X_some, AlgHom.restrictScalars_apply,
          Polynomial.taylorAlgHom_apply, Polynomial.taylor_C]
  exact DFunLike.congr_fun h p

private theorem frame_difference_degree_lt (θ : ι → ℝ) (t : ℝ) (d : ℕ) (p : Jet ι d)
    (hne : (frame θ t d - 1) p ≠ 0) :
    (optionEquivLeft ℝ ι (((frame θ t d - 1) p : Jet ι d) : MvPolynomial (Option ι) ℝ)).natDegree <
      (optionEquivLeft ℝ ι p.val).natDegree := by
  let q := optionEquivLeft ℝ ι p.val
  let u := horizontalShift θ t
  have hp0 : eval (0 : Option ι → ℝ) p.val = 0 := p.property.2
  have hD : pull θ t p.val - p.val ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    apply hne
    apply Subtype.ext
    change centeredPull θ t p.val - p.val = 0
    simp only [centeredPull, he, hp0, map_zero, sub_zero, sub_self]
  have hQ : q ≠ 0 := by
    intro h
    have hp : p.val = 0 := (optionEquivLeft ℝ ι).injective (h.trans (map_zero _).symm)
    exact hD (by rw [hp, map_zero, sub_self])
  have hDQ : Polynomial.taylor u q - q ≠ 0 := by
    intro h
    apply hD
    apply (optionEquivLeft ℝ ι).injective
    simpa only [map_sub, optionEquivLeft_pull, map_zero, q, u] using h
  have hdrop : (Polynomial.taylor u q - q).degree < q.degree := by
    have h := Polynomial.degree_sub_lt (Polynomial.degree_taylor q u)
      ((Polynomial.taylor_eq_zero u q).not.mpr hQ) (Polynomial.leadingCoeff_taylor u q)
    simpa only [Polynomial.degree_taylor] using h
  have hn := Polynomial.natDegree_lt_natDegree hDQ hdrop
  have hcenter :
      optionEquivLeft ℝ ι (((frame θ t d - 1) p : Jet ι d) : MvPolynomial (Option ι) ℝ) =
        (Polynomial.taylor u q - q) -
          Polynomial.C (C (eval (0 : Option ι → ℝ) (pull θ t p.val))) := by
    change optionEquivLeft ℝ ι (centeredPull θ t p.val - p.val) = _
    simp only [centeredPull, map_sub, optionEquivLeft_pull, optionEquivLeft_C, q, u]
    abel
  rw [hcenter]
  have hb := Polynomial.natDegree_sub_le (Polynomial.taylor u q - q)
    (Polynomial.C (C (eval (0 : Option ι → ℝ) (pull θ t p.val))))
  simp only [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)] at hb
  exact hb.trans_lt hn

private theorem frame_difference_iterate_zero (θ : ι → ℝ) (t : ℝ) (d k : ℕ) (p : Jet ι d)
    (hdeg : (optionEquivLeft ℝ ι p.val).natDegree < k) :
    ((frame θ t d - 1) ^ k) p = 0 := by
  induction k generalizing p with
  | zero => exact (Nat.not_lt_zero _ hdeg).elim
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply]
      by_cases hz : (frame θ t d - 1) p = 0
      · simp only [hz, map_zero]
      · exact ih _ ((frame_difference_degree_lt θ t d p hz).trans_le
          (Nat.lt_succ_iff.mp hdeg))

/-- The nilpotence exponent depends only on degree, not on the number of variables. -/
theorem frame_difference_pow_eq_zero (θ : ι → ℝ) (t : ℝ) (d : ℕ) :
    (frame θ t d - 1) ^ (d + 1) = 0 := by
  apply LinearMap.ext
  intro p
  apply frame_difference_iterate_zero
  rw [natDegree_optionEquivLeft]
  exact Nat.lt_succ_of_le ((degreeOf_le_totalDegree p.val none).trans
    ((mem_restrictTotalDegree _ _ _).mp p.property.1))

/-- Every finite centered frame has determinant one. -/
theorem det_frame (θ : ι → ℝ) (t : ℝ) (d : ℕ) : (frame θ t d).det = 1 := by
  letI : Ring (Module.End ℝ (Jet ι d)) := Module.End.instRing
  have hN : IsNilpotent (1 - frame θ t d) := by
    refine ⟨d + 1, ?_⟩
    have he : 1 - frame θ t d = -(frame θ t d - 1) := (neg_sub (frame θ t d) 1).symm
    rw [he, neg_pow (frame θ t d - 1) (d + 1), frame_difference_pow_eq_zero, mul_zero]
  have h := congrArg (fun P : Polynomial ℝ => P.eval 1) hN.charpoly_eq_X_pow_finrank
  rw [LinearMap.eval_charpoly] at h
  have he : (algebraMap ℝ (Module.End ℝ (Jet ι d))) 1 - (1 - frame θ t d) = frame θ t d := by
    rw [map_one]
    abel
  simpa only [he, Polynomial.eval_pow, Polynomial.eval_X, one_pow] using h

#print axioms pull_totalDegree_le
#print axioms frame_comp
#print axioms frameEquiv
#print axioms optionEquivLeft_pull
#print axioms frame_difference_pow_eq_zero
#print axioms det_frame

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
