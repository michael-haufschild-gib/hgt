import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Homogeneous dehomogenization in an arbitrary coordinate frame

For a polynomial whose variables are indexed by `Option σ`, this module fixes the distinguished
`none` coordinate to one.  The resulting affine-chart map is faithful on every homogeneous
sector, without any finiteness assumption on `σ`.

The proof separates the distinguished variable through `MvPolynomial.optionEquivLeft`.  Its
polynomial coefficients have pairwise distinct homogeneous degrees, so evaluation at one cannot
cancel the leading nonzero coefficient.  This supplies the infinite-variable form of the
projective-chart argument used by finite Bell horizons and scale-separated pole traces.
-/

open MvPolynomial Polynomial

namespace GaloisForLFunctions

noncomputable section

/-- Dehomogenize the distinguished `none` coordinate by setting it to one. -/
def optionHeadDehomogenize {R σ : Type*} [CommSemiring R] :
    MvPolynomial (Option σ) R →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun o =>
    match o with
    | none => 1
    | some i => MvPolynomial.X i

/-- `optionHeadDehomogenize` is evaluation at one after separating the distinguished variable. -/
theorem optionHeadDehomogenize_eq_eval_optionEquivLeft
    {R σ : Type*} [CommSemiring R] (P : MvPolynomial (Option σ) R) :
    optionHeadDehomogenize P = (MvPolynomial.optionEquivLeft R σ P).eval 1 := by
  let rhs : MvPolynomial (Option σ) R →+* MvPolynomial σ R :=
    (Polynomial.evalRingHom 1).comp (MvPolynomial.optionEquivLeft R σ).toRingHom
  have h : optionHeadDehomogenize = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [optionHeadDehomogenize, rhs]
    · intro o
      rcases o with (_ | i)
      · simp [optionHeadDehomogenize, rhs]
      · simp [optionHeadDehomogenize, rhs]
  exact RingHom.congr_fun h P

/-- The coefficient of distinguished-coordinate degree `k` in a degree-`d` homogeneous
polynomial is homogeneous of complementary degree `d-k`.  Unlike the current finite Mathlib API,
this form does not require the tail index type to be finite. -/
theorem optionEquivLeft_coeff_isHomogeneous
    {R σ : Type*} [CommSemiring R]
    {d : ℕ} {P : MvPolynomial (Option σ) R}
    (hP : P.IsHomogeneous d) (k : ℕ) (hk : k ≤ d) :
    ((MvPolynomial.optionEquivLeft R σ P).coeff k).IsHomogeneous (d - k) := by
  intro m hm
  have hmSupport : m ∈ ((MvPolynomial.optionEquivLeft R σ P).coeff k).support :=
    MvPolynomial.mem_support_iff.mpr hm
  have hfull : m.optionElim k ∈ P.support :=
    (MvPolynomial.mem_support_coeff_optionEquivLeft R).mp hmSupport
  have hdegree := hP (MvPolynomial.mem_support_iff.mp hfull)
  simp only [Finsupp.weight_apply] at hdegree ⊢
  rw [Finsupp.sum_option_index_smul] at hdegree
  simp only [Finsupp.optionElim_apply_none, Finsupp.some_optionElim,
    smul_eq_mul, Pi.one_apply, mul_one] at hdegree ⊢
  omega

/-- **Homogeneous projective-chart faithfulness.**  For an arbitrary index type, setting one
distinguished coordinate of a nonzero homogeneous multivariate polynomial to one cannot annihilate
the polynomial. -/
theorem optionHeadDehomogenize_ne_zero_of_isHomogeneous
    {R σ : Type*} [CommSemiring R] [Nontrivial R]
    {d : ℕ} {P : MvPolynomial (Option σ) R}
    (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    optionHeadDehomogenize P ≠ 0 := by
  intro hzero
  let p : Polynomial (MvPolynomial σ R) := MvPolynomial.optionEquivLeft R σ P
  have hp0 : p ≠ 0 := (MvPolynomial.optionEquivLeft R σ).injective.ne hP0
  let j := p.natDegree
  have hj : p.coeff j ≠ 0 := by
    simpa [j] using Polynomial.leadingCoeff_ne_zero.mpr hp0
  have htd : P.totalDegree = d := hP.totalDegree hP0
  have hnd : p.natDegree ≤ d := by
    rw [show p = MvPolynomial.optionEquivLeft R σ P from rfl,
      MvPolynomial.natDegree_optionEquivLeft, ← htd]
    exact MvPolynomial.degreeOf_le_totalDegree P none
  have hjd : j ≤ d := (Polynomial.le_natDegree_of_ne_zero hj).trans hnd
  have heval : p.eval 1 = 0 := by
    rw [← optionHeadDehomogenize_eq_eval_optionEquivLeft]
    exact hzero
  have hevalsum : p.eval 1 = ∑ k ∈ Finset.range (d + 1), p.coeff k := by
    rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hnd (Nat.lt_succ_self d))]
    simp
  have hcomponent := congrArg (MvPolynomial.homogeneousComponent (d - j)) heval
  rw [hevalsum, map_sum, map_zero] at hcomponent
  have hsingle :
      (∑ k ∈ Finset.range (d + 1),
        MvPolynomial.homogeneousComponent (d - j) (p.coeff k)) = p.coeff j := by
    rw [Finset.sum_eq_single j]
    · have hjhom : (p.coeff j).IsHomogeneous (d - j) :=
        optionEquivLeft_coeff_isHomogeneous hP j hjd
      exact MvPolynomial.homogeneousComponent_of_mem hjhom |>.trans (if_pos rfl)
    · intro k hk hkj
      have hkd : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hkhom : (p.coeff k).IsHomogeneous (d - k) :=
        optionEquivLeft_coeff_isHomogeneous hP k hkd
      rw [MvPolynomial.homogeneousComponent_of_mem hkhom, if_neg]
      intro heq
      apply hkj
      omega
    · intro hnot
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hjd)) hnot
  rw [hsingle] at hcomponent
  exact hj hcomponent

end

end GaloisForLFunctions
