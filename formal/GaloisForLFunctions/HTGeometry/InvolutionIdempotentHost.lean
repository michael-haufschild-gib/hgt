import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Self-inverse elements and idempotents of a commutative coefficient host

Over a commutative ring `R` in which `2` is invertible, the assignments

`e ↦ 2 * e - 1`  and  `g ↦ ⅟2 * (g + 1)`

are mutually inverse bijections between the idempotents of `R` and the solutions of `g * g = 1`.

Consequences:

* if the only idempotents of `R` are `0` and `1` — in particular if `R` has no zero divisors —
  then `g * g = 1` forces `g = 1` or `g = -1`;
* every nontrivial idempotent produces a self-inverse element that is neither `1` nor `-1`, so the
  implication `g * g = 1 → g = ±1` fails over any host carrying a nontrivial idempotent, such as a
  product ring or a matrix algebra with a proper projector.

The explicit witness `(1, -1) ∈ ℂ × ℂ` is recorded at the end.
-/

namespace GaloisForLFunctions.HTGeometry

section CommRing

variable {R : Type*} [CommRing R]

/-- The self-inverse element attached to an element of a commutative ring. -/
def hostInvolutionOfIdempotent (e : R) : R := 2 * e - 1

/-- Every idempotent produces a self-inverse element. -/
theorem hostInvolutionOfIdempotent_mul_self (e : R) (he : IsIdempotentElem e) :
    hostInvolutionOfIdempotent e * hostInvolutionOfIdempotent e = 1 := by
  have h : e * e = e := he
  simp only [hostInvolutionOfIdempotent]
  linear_combination (4 : R) * h

/-- In a commutative ring without zero divisors the only idempotents are `0` and `1`. -/
theorem isIdempotentElem_eq_zero_or_one [NoZeroDivisors R] (e : R) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have h : e * (e - 1) = 0 := by
    have h' : e * e = e := he
    linear_combination h'
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (eq_of_sub_eq_zero h)

variable [Invertible (2 : R)]

/-- The idempotent attached to an element of a commutative ring in which `2` is invertible. -/
def hostIdempotentOfInvolution (g : R) : R := ⅟(2 : R) * (g + 1)

/-- Every self-inverse element produces an idempotent. -/
theorem hostIdempotentOfInvolution_isIdempotentElem (g : R) (hg : g * g = 1) :
    IsIdempotentElem (hostIdempotentOfInvolution g) := by
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
  have h : hostIdempotentOfInvolution g * hostIdempotentOfInvolution g =
      hostIdempotentOfInvolution g := by
    simp only [hostIdempotentOfInvolution]
    linear_combination (⅟(2 : R) * ⅟(2 : R)) * hg + ((g + 1) * ⅟(2 : R)) * h2
  exact h

/-- Passing from an idempotent to its self-inverse element and back is the identity. -/
theorem hostIdempotentOfInvolution_hostInvolutionOfIdempotent (e : R) :
    hostIdempotentOfInvolution (hostInvolutionOfIdempotent e) = e := by
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
  simp only [hostIdempotentOfInvolution, hostInvolutionOfIdempotent]
  linear_combination e * h2

/-- Passing from a self-inverse element to its idempotent and back is the identity. -/
theorem hostInvolutionOfIdempotent_hostIdempotentOfInvolution (g : R) :
    hostInvolutionOfIdempotent (hostIdempotentOfInvolution g) = g := by
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
  simp only [hostIdempotentOfInvolution, hostInvolutionOfIdempotent]
  linear_combination (g + 1) * h2

/-- Over a commutative ring with `2` invertible, self-inverse elements and idempotents are the
same data. -/
def involutionEquivIdempotent : {g : R // g * g = 1} ≃ {e : R // IsIdempotentElem e} where
  toFun g := ⟨hostIdempotentOfInvolution g.1, hostIdempotentOfInvolution_isIdempotentElem g.1 g.2⟩
  invFun e := ⟨hostInvolutionOfIdempotent e.1, hostInvolutionOfIdempotent_mul_self e.1 e.2⟩
  left_inv g := Subtype.ext (hostInvolutionOfIdempotent_hostIdempotentOfInvolution g.1)
  right_inv e := Subtype.ext (hostIdempotentOfInvolution_hostInvolutionOfIdempotent e.1)

/-- The attached self-inverse element is `1` exactly at the idempotent `1`. -/
theorem hostInvolutionOfIdempotent_eq_one_iff (e : R) :
    hostInvolutionOfIdempotent e = 1 ↔ e = 1 := by
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
  constructor
  · intro h
    simp only [hostInvolutionOfIdempotent] at h
    linear_combination ⅟(2 : R) * h + (1 - e) * h2
  · intro h
    subst h
    simp [hostInvolutionOfIdempotent]
    ring

/-- The attached self-inverse element is `-1` exactly at the idempotent `0`. -/
theorem hostInvolutionOfIdempotent_eq_neg_one_iff (e : R) :
    hostInvolutionOfIdempotent e = -1 ↔ e = 0 := by
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
  constructor
  · intro h
    simp only [hostInvolutionOfIdempotent] at h
    linear_combination ⅟(2 : R) * h - e * h2
  · intro h
    subst h
    simp [hostInvolutionOfIdempotent]

/-- **Connected host.** If the only idempotents of `R` are `0` and `1`, then `g * g = 1` forces
`g = 1` or `g = -1`. -/
theorem eq_one_or_neg_one_of_mul_self_eq_one
    (hidem : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1)
    (g : R) (hg : g * g = 1) : g = 1 ∨ g = -1 := by
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
  rcases hidem _ (hostIdempotentOfInvolution_isIdempotentElem g hg) with h | h
  · refine Or.inr ?_
    simp only [hostIdempotentOfInvolution] at h
    linear_combination (2 : R) * h - (g + 1) * h2
  · refine Or.inl ?_
    simp only [hostIdempotentOfInvolution] at h
    linear_combination (2 : R) * h - (g + 1) * h2

/-- **Scalar host.** Over a commutative ring without zero divisors, `g * g = 1` forces `g = ±1`. -/
theorem eq_one_or_neg_one_of_mul_self_eq_one_of_noZeroDivisors [NoZeroDivisors R]
    (g : R) (hg : g * g = 1) : g = 1 ∨ g = -1 :=
  eq_one_or_neg_one_of_mul_self_eq_one isIdempotentElem_eq_zero_or_one g hg

/-- **Host caveat.** A nontrivial idempotent produces a self-inverse element that is neither `1`
nor `-1`; the scalar dichotomy therefore fails over every host with a proper projector. -/
theorem exists_mul_self_eq_one_ne_one_ne_neg_one_of_idempotent
    (e : R) (he : IsIdempotentElem e) (he0 : e ≠ 0) (he1 : e ≠ 1) :
    ∃ g : R, g * g = 1 ∧ g ≠ 1 ∧ g ≠ -1 :=
  ⟨hostInvolutionOfIdempotent e, hostInvolutionOfIdempotent_mul_self e he,
    fun h => he1 ((hostInvolutionOfIdempotent_eq_one_iff e).mp h),
    fun h => he0 ((hostInvolutionOfIdempotent_eq_neg_one_iff e).mp h)⟩

end CommRing

section ProductWitness

/-- The product-sector projector `(1, 0)` is idempotent. -/
theorem isIdempotentElem_prod_left : IsIdempotentElem ((1, 0) : ℂ × ℂ) := by
  have h : ((1, 0) : ℂ × ℂ) * (1, 0) = (1, 0) := by
    simp
  exact h

/-- The product-sector projector is neither `0` nor `1`. -/
theorem prod_left_ne_zero : ((1, 0) : ℂ × ℂ) ≠ 0 := by
  simp

theorem prod_left_ne_one : ((1, 0) : ℂ × ℂ) ≠ 1 := by
  norm_num [Prod.ext_iff]

/-- **Explicit failure witness.** In `ℂ × ℂ` the element `(1, -1)` is self-inverse yet is neither
the global `1` nor the global `-1`. -/
theorem prod_sign_mul_self : ((1, -1) : ℂ × ℂ) * (1, -1) = 1 := by
  simp [Prod.ext_iff]

theorem prod_sign_ne_one : ((1, -1) : ℂ × ℂ) ≠ 1 := by
  norm_num [Prod.ext_iff]

theorem prod_sign_ne_neg_one : ((1, -1) : ℂ × ℂ) ≠ -1 := by
  norm_num [Prod.ext_iff]

/-- The self-inverse element `(1, -1)` is exactly the one attached to the projector `(1, 0)`. -/
theorem hostInvolutionOfIdempotent_prod_left :
    hostInvolutionOfIdempotent ((1, 0) : ℂ × ℂ) = (1, -1) := by
  simp [hostInvolutionOfIdempotent, Prod.ext_iff]
  norm_num

end ProductWitness

end GaloisForLFunctions.HTGeometry
