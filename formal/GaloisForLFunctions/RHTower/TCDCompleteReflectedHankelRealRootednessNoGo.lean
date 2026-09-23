import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import GaloisForLFunctions.HilbertMetric.ReflectionEighthJet
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Complete reflected-Hankel positivity does not force real-rootedness

This module kills the generic cofinal landing proposed after the finite TCD/S6F gate:

`strict rank-three signed reflected Hankel determinant`
`+ all-order reflected-Hankel positivity`
`+ positive entire real source`
`⇒ all zeros real`.

The counterexample is `F(z) = cosh z + cosh (2z)`. Its reflected product is a positive five-atom
moment family at every real center, so every polynomial-square Hankel form is nonnegative and the
exact rank-three TCD determinant is strictly positive. Nevertheless `F(iπ/3) = 0`.

Thus the TCD chain cannot reach RH from cofinal reflected-Hankel signs alone. Any surviving landing
must add a theta-to-Xi/source-to-divisor incidence law not encoded by these signs.
-/

open Real Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

def twoCoshRealSource (x : ℝ) : ℝ := Real.cosh x + Real.cosh (2 * x)

def twoCoshEntireSource (z : ℂ) : ℂ := Complex.cosh z + Complex.cosh (2 * z)

def twoCoshReflectedFrequency : Fin 5 → ℝ := ![0, 1, 2, 3, 4]

def twoCoshReflectedNode : Fin 5 → ℝ := ![0, 1, 4, 9, 16]

def twoCoshReflectedWeight (x : ℝ) : Fin 5 → ℝ :=
  ![(Real.cosh (2 * x) + Real.cosh (4 * x)) / 2,
    Real.cosh (3 * x), 1 / 2, Real.cosh x, 1 / 2]

def twoCoshReflectedProfile (x t : ℝ) : ℝ :=
  ∑ i : Fin 5,
    twoCoshReflectedWeight x i * Real.cosh (twoCoshReflectedFrequency i * t)

def twoCoshReflectedMoment (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin 5, twoCoshReflectedWeight x i * twoCoshReflectedNode i ^ n

theorem twoCoshReflectedWeight_pos (x : ℝ) (i : Fin 5) :
    0 < twoCoshReflectedWeight x i := by
  fin_cases i <;> simp [twoCoshReflectedWeight] <;> positivity

theorem twoCoshReflectedNode_injective : Function.Injective twoCoshReflectedNode := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [twoCoshReflectedNode]

private theorem twoCoshReflectedFrequency_sq (i : Fin 5) :
    twoCoshReflectedFrequency i ^ (2 : ℕ) = twoCoshReflectedNode i := by
  fin_cases i <;> norm_num [twoCoshReflectedFrequency, twoCoshReflectedNode]

private theorem two_mul_real_cosh_mul_cosh (a b : ℝ) :
    2 * Real.cosh a * Real.cosh b = Real.cosh (a + b) + Real.cosh (a - b) := by
  rw [Real.cosh_add, Real.cosh_sub]
  ring

theorem twoCoshReflected_product_identity (x t : ℝ) :
    twoCoshRealSource (x + t) * twoCoshRealSource (x - t) =
      twoCoshReflectedProfile x t := by
  rw [twoCoshRealSource, twoCoshRealSource]
  unfold twoCoshReflectedProfile
  simp only [Fin.sum_univ_succ]
  simp [twoCoshReflectedWeight, twoCoshReflectedFrequency]
  have h11 := two_mul_real_cosh_mul_cosh (x + t) (x - t)
  have h12 := two_mul_real_cosh_mul_cosh (x + t) (2 * (x - t))
  have h21 := two_mul_real_cosh_mul_cosh (2 * (x + t)) (x - t)
  have h22 := two_mul_real_cosh_mul_cosh (2 * (x + t)) (2 * (x - t))
  have h3x := two_mul_real_cosh_mul_cosh (3 * x) t
  have h3t := two_mul_real_cosh_mul_cosh x (3 * t)
  rw [show x + t + (x - t) = 2 * x by ring,
    show x + t - (x - t) = 2 * t by ring] at h11
  rw [show x + t + 2 * (x - t) = 3 * x - t by ring,
    show x + t - 2 * (x - t) = -(x - 3 * t) by ring,
    Real.cosh_neg] at h12
  rw [show 2 * (x + t) + (x - t) = 3 * x + t by ring,
    show 2 * (x + t) - (x - t) = x + 3 * t by ring] at h21
  rw [show 2 * (x + t) + 2 * (x - t) = 4 * x by ring,
    show 2 * (x + t) - 2 * (x - t) = 4 * t by ring] at h22
  nlinarith

private theorem iteratedDeriv_real_cosh_mul_even (a : ℝ) (m : ℕ) :
    iteratedDeriv (2 * m) (fun t : ℝ => Real.cosh (a * t)) 0 = a ^ (2 * m) := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_cosh a]
  simp

theorem twoCoshReflectedMoment_eq_evenJet (x : ℝ) (m : ℕ) :
    twoCoshReflectedMoment x m =
      iteratedDeriv (2 * m)
        (fun t : ℝ => twoCoshRealSource (x + t) * twoCoshRealSource (x - t)) 0 := by
  have hfun :
      (fun t : ℝ => twoCoshRealSource (x + t) * twoCoshRealSource (x - t)) =
        twoCoshReflectedProfile x := by
    funext t
    exact twoCoshReflected_product_identity x t
  rw [hfun]
  unfold twoCoshReflectedProfile twoCoshReflectedMoment
  have hsum :
      (fun t : ℝ => ∑ i : Fin 5,
        twoCoshReflectedWeight x i * Real.cosh (twoCoshReflectedFrequency i * t)) =
      ∑ i : Fin 5, fun t : ℝ =>
        twoCoshReflectedWeight x i * Real.cosh (twoCoshReflectedFrequency i * t) := by
    funext t
    simp
  rw [hsum, iteratedDeriv_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedDeriv_const_mul_field,
      iteratedDeriv_real_cosh_mul_even]
    rw [← twoCoshReflectedFrequency_sq i, ← pow_mul]
  · intro i hi
    fun_prop

private theorem momentFunctional_twoCoshReflectedMoment (x : ℝ) (p : Polynomial ℝ) :
    HTGeometry.momentFunctional (twoCoshReflectedMoment x) p =
      ∑ i : Fin 5, twoCoshReflectedWeight x i * p.eval (twoCoshReflectedNode i) := by
  rw [HTGeometry.momentFunctional_eq_support_sum]
  simp_rw [twoCoshReflectedMoment, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [p.eval_eq_sum]
  simp only [Polynomial.sum_def]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem twoCoshReflectedMoment_square_nonneg (x : ℝ) (p : Polynomial ℝ) :
    0 ≤ HTGeometry.momentFunctional (twoCoshReflectedMoment x) (p ^ (2 : ℕ)) := by
  rw [momentFunctional_twoCoshReflectedMoment]
  apply Finset.sum_nonneg
  intro i hi
  rw [eval_pow]
  exact mul_nonneg (twoCoshReflectedWeight_pos x i).le (sq_nonneg _)

private theorem twoCoshReflectedMoment_rankThree_quad
    (x : ℝ) (a : Fin 3 → ℝ) :
    a ⬝ᵥ (HTGeometry.momentHankelMatrix (twoCoshReflectedMoment x) 3).mulVec a =
      ∑ k : Fin 5, twoCoshReflectedWeight x k *
        ((Polynomial.ofFn 3 a).eval (twoCoshReflectedNode k)) ^ (2 : ℕ) := by
  simp only [dotProduct, Matrix.mulVec, HTGeometry.momentHankelMatrix,
    twoCoshReflectedMoment, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  calc
    (∑ i : Fin 3, a i * ∑ j : Fin 3,
      (∑ k : Fin 5, twoCoshReflectedWeight x k *
        twoCoshReflectedNode k ^ ((i : ℕ) + (j : ℕ))) * a j) =
        ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 5,
          a i * (twoCoshReflectedWeight x k *
            twoCoshReflectedNode k ^ ((i : ℕ) + (j : ℕ)) * a j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ i : Fin 3, ∑ k : Fin 5, ∑ j : Fin 3,
        a i * (twoCoshReflectedWeight x k *
          twoCoshReflectedNode k ^ ((i : ℕ) + (j : ℕ)) * a j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k : Fin 5, ∑ i : Fin 3, ∑ j : Fin 3,
        a i * (twoCoshReflectedWeight x k *
          twoCoshReflectedNode k ^ ((i : ℕ) + (j : ℕ)) * a j) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      simp_rw [pow_add, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem twoCoshReflectedMoment_rankThree_posDef (x : ℝ) :
    (HTGeometry.momentHankelMatrix (twoCoshReflectedMoment x) 3).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨HTGeometry.momentHankelMatrix_isHermitian _ _, ?_⟩
  intro a ha
  rw [star_trivial, twoCoshReflectedMoment_rankThree_quad]
  have hp : Polynomial.ofFn 3 a ≠ 0 := by
    intro h
    apply ha
    apply Polynomial.injective_ofFn 3
    rw [h, Polynomial.ofFn_zero]
  have hdeg : (Polynomial.ofFn 3 a).natDegree < Fintype.card (Fin 5) := by
    have hlt : (Polynomial.ofFn 3 a).natDegree < 3 :=
      Polynomial.ofFn_natDegree_lt (by norm_num) a
    norm_num at hlt ⊢
    omega
  have hnotall : ¬ ∀ i, (Polynomial.ofFn 3 a).eval (twoCoshReflectedNode i) = 0 := by
    intro hall
    exact hp (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (Polynomial.ofFn 3 a) twoCoshReflectedNode_injective hall hdeg)
  obtain ⟨i, hi⟩ := not_forall.mp hnotall
  have hnonneg : ∀ k, 0 ≤ twoCoshReflectedWeight x k *
      ((Polynomial.ofFn 3 a).eval (twoCoshReflectedNode k)) ^ (2 : ℕ) := by
    intro k
    exact mul_nonneg (twoCoshReflectedWeight_pos x k).le (sq_nonneg _)
  have hpos : 0 < twoCoshReflectedWeight x i *
      ((Polynomial.ofFn 3 a).eval (twoCoshReflectedNode i)) ^ (2 : ℕ) := by
    exact mul_pos (twoCoshReflectedWeight_pos x i) (sq_pos_of_ne_zero hi)
  exact hpos.trans_le
    (Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ i))

theorem twoCoshReflectedMoment_rankThree_det_pos (x : ℝ) :
    0 < (HTGeometry.momentHankelMatrix (twoCoshReflectedMoment x) 3).det :=
  (twoCoshReflectedMoment_rankThree_posDef x).det_pos

theorem twoCoshReflectedMoment_rankThree_det_eq (x : ℝ) :
    (HTGeometry.momentHankelMatrix (twoCoshReflectedMoment x) 3).det =
      HilbertMetric.signedEvenHankelThreeDet
        (twoCoshReflectedMoment x 0) (twoCoshReflectedMoment x 1)
        (twoCoshReflectedMoment x 2) (twoCoshReflectedMoment x 3)
        (twoCoshReflectedMoment x 4) := by
  rw [Matrix.det_fin_three]
  simp only [HTGeometry.momentHankelMatrix]
  unfold HilbertMetric.signedEvenHankelThreeDet
  norm_num
  ring

theorem twoCoshReflectedMoment_signedEvenHankelThreeDet_pos (x : ℝ) :
    0 < HilbertMetric.signedEvenHankelThreeDet
      (twoCoshReflectedMoment x 0) (twoCoshReflectedMoment x 1)
      (twoCoshReflectedMoment x 2) (twoCoshReflectedMoment x 3)
      (twoCoshReflectedMoment x 4) := by
  rw [← twoCoshReflectedMoment_rankThree_det_eq]
  exact twoCoshReflectedMoment_rankThree_det_pos x

theorem twoCoshEntireSource_nonreal_zero :
    twoCoshEntireSource ((Real.pi / 3 : ℝ) * Complex.I) = 0 := by
  unfold twoCoshEntireSource
  rw [show 2 * ((Real.pi / 3 : ℝ) * Complex.I) =
      ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.cosh_mul_I, Complex.cosh_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_cos]
  have htwo : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  rw [Real.cos_pi_div_three, htwo]
  norm_num

theorem twoCoshEntireSource_nonreal_zero_im_ne_zero :
    (((Real.pi / 3 : ℝ) * Complex.I : ℂ).im) ≠ 0 := by
  simp

theorem twoCoshRealSource_pos (x : ℝ) : 0 < twoCoshRealSource x := by
  unfold twoCoshRealSource
  positivity

theorem analyticAt_twoCoshEntireSource (z : ℂ) :
    AnalyticAt ℂ twoCoshEntireSource z := by
  unfold twoCoshEntireSource
  fun_prop

theorem twoCoshEntireSource_ofReal (x : ℝ) :
    twoCoshEntireSource x = twoCoshRealSource x := by
  simp [twoCoshEntireSource, twoCoshRealSource]

/-- Positive real source, all reflected Hankel squares, and strict rank three do not force
real-rootedness. This falsifies the generic cofinal landing proposed after the finite TCD gate. -/
theorem completeReflectedHankel_realRootedness_noGo :
    (∀ z, AnalyticAt ℂ twoCoshEntireSource z) ∧
    (∀ x : ℝ, twoCoshEntireSource x = twoCoshRealSource x) ∧
    (∀ x : ℝ, 0 < twoCoshRealSource x) ∧
    (∀ x : ℝ, ∀ p : Polynomial ℝ,
      0 ≤ HTGeometry.momentFunctional (twoCoshReflectedMoment x) (p ^ (2 : ℕ))) ∧
    (∀ x : ℝ,
      0 < HilbertMetric.signedEvenHankelThreeDet
        (twoCoshReflectedMoment x 0) (twoCoshReflectedMoment x 1)
        (twoCoshReflectedMoment x 2) (twoCoshReflectedMoment x 3)
        (twoCoshReflectedMoment x 4)) ∧
    ¬ (∀ z, twoCoshEntireSource z = 0 → z.im = 0) := by
  refine ⟨analyticAt_twoCoshEntireSource, twoCoshEntireSource_ofReal,
    twoCoshRealSource_pos, twoCoshReflectedMoment_square_nonneg,
    twoCoshReflectedMoment_signedEvenHankelThreeDet_pos, ?_⟩
  intro hall
  exact twoCoshEntireSource_nonreal_zero_im_ne_zero
    (hall _ twoCoshEntireSource_nonreal_zero)

end

end RHTower
