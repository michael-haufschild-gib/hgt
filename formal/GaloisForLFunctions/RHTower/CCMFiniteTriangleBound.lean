import GaloisForLFunctions.RHTower.FiniteSignedTriangleBound

/-!
# An unconditional collective bound for every finite full Weil source family

The real polarization of the literal restricted Weil form supplies a symmetric
Gram matrix. The finite triangle correction therefore applies without support,
sign, or positivity assumptions on the sources.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

theorem ccmWeilRealPolar_symm (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) :
    ccmWeilRealPolar a u v = ccmWeilRealPolar a v u := by
  rw [ccmWeilRealPolar_eq_form, ccmWeilRealPolar_eq_form]
  ring

theorem ccmWeilRealPolar_self (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmWeilRealPolar a u u = ccmRestrictedWeilSourceQuadratic a u := by
  rw [ccmWeilRealPolar_eq_form, ccmRestrictedWeilForm_self_re_eq_source]
  ring

theorem ccmWeilRealPolar_zero_left (a : SuzukiPositiveAperture) (v : CCMArchimedeanFormDomain a) :
    ccmWeilRealPolar a 0 v = 0 := by
  simp [ccmWeilRealPolar_eq_form, ccmRestrictedWeilForm]

theorem ccmWeilRealPolar_add_left (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) :
    ccmWeilRealPolar a (u + v) w = ccmWeilRealPolar a u w + ccmWeilRealPolar a v w := by
  simp only [ccmWeilRealPolar_eq_form, ccmRestrictedWeilForm, map_add,
    inner_add_left, inner_add_right, Complex.add_re]
  ring

theorem ccmWeilRealPolar_smul_real_left (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) (x : ℝ) :
    ccmWeilRealPolar a ((x : ℂ) • u) v = x * ccmWeilRealPolar a u v := by
  simp only [ccmWeilRealPolar_eq_form, ccmRestrictedWeilForm, map_smul,
    inner_smul_left (E := CCMArchimedeanFormDomain a),
    inner_smul_right (E := CCMArchimedeanFormDomain a),
    inner_smul_left (E := suzukiApertureHilbert a),
    inner_smul_right (E := suzukiApertureHilbert a),
    Complex.conj_ofReal, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

theorem ccmWeilRealPolar_smul_real_right (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) (x : ℝ) :
    ccmWeilRealPolar a u ((x : ℂ) • v) = x * ccmWeilRealPolar a u v := by
  rw [ccmWeilRealPolar_symm, ccmWeilRealPolar_smul_real_left, ccmWeilRealPolar_symm a v u]

theorem ccmWeilRealPolar_sum_left {ι : Type*} (a : SuzukiPositiveAperture)
    (s : Finset ι) (u : ι → CCMArchimedeanFormDomain a) (v : CCMArchimedeanFormDomain a) :
    ccmWeilRealPolar a (∑ i ∈ s, u i) v = ∑ i ∈ s, ccmWeilRealPolar a (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, ccmWeilRealPolar_zero_left]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, ccmWeilRealPolar_add_left, ih]

theorem ccmWeilRealPolar_sum_right {ι : Type*} (a : SuzukiPositiveAperture)
    (s : Finset ι) (u : CCMArchimedeanFormDomain a) (v : ι → CCMArchimedeanFormDomain a) :
    ccmWeilRealPolar a u (∑ i ∈ s, v i) = ∑ i ∈ s, ccmWeilRealPolar a u (v i) := by
  rw [ccmWeilRealPolar_symm, ccmWeilRealPolar_sum_left]
  exact Finset.sum_congr rfl fun i _ => ccmWeilRealPolar_symm a (v i) u

theorem ccmRestrictedWeilSourceQuadratic_real_sum {ι : Type*} [Fintype ι]
    (a : SuzukiPositiveAperture) (u : ι → CCMArchimedeanFormDomain a) (x : ι → ℝ) :
    ccmRestrictedWeilSourceQuadratic a (∑ i, (x i : ℂ) • u i) =
      finiteSignedQuadratic (fun i j => ccmWeilRealPolar a (u i) (u j)) x := by
  rw [← ccmWeilRealPolar_self]
  simp_rw [ccmWeilRealPolar_sum_left, ccmWeilRealPolar_sum_right,
    ccmWeilRealPolar_smul_real_left, ccmWeilRealPolar_smul_real_right]
  unfold finiteSignedQuadratic
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- All finite source families, with no geometric or sign premises. -/
theorem ccmRestrictedWeilSourceQuadratic_finite_triangle_lower {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : SuzukiPositiveAperture)
    (u : ι → CCMArchimedeanFormDomain a) (x : ι → ℝ) :
    finiteSignedSeparateLower (fun i j => ccmWeilRealPolar a (u i) (u j)) x +
      finiteSignedTriangleCorrection (fun i j => ccmWeilRealPolar a (u i) (u j)) x ≤
      ccmRestrictedWeilSourceQuadratic a (∑ i, (x i : ℂ) • u i) := by
  rw [ccmRestrictedWeilSourceQuadratic_real_sum]
  exact finiteSignedTriangle_lower _ (fun i j => ccmWeilRealPolar_symm a (u i) (u j)) x

end RHTower
