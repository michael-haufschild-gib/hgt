import GaloisForLFunctions.RHTower.Suzuki.SuzukiCauchyReporterSecantWardCapacity

/-!
# Sharp transition atlas for Suzuki reporter-secant Cauchy Gram

The previously known factor-two theorem proves negativity when the deeper lag is at least twice
the shallower lag.  This module classifies the unresolved middle band exactly.  For every nonzero
shallower lag `p`, the cross-Gram along `q = p + r`, `0 <= r <= p`, has one and only one zero.  Its
depth lies strictly between `3p/2` and `2p`; the Gram is positive before it and negative after it.

The transition is source-specific.  Multiplication by the positive attenuation `exp(-r/2)` turns
the middle-band Gram into a strictly decreasing exponential cubic.  No RH statement, numerical
input, or spectral hypothesis is used.
-/

open Set
open scoped NNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

structure SuzukiReporterSecantMiddleBand where
  shallow : ℝ≥0
  residual : ℝ≥0
  residual_le_shallow : residual ≤ shallow

def suzukiReporterSecantTransitionPolynomial (p r : ℝ) : ℝ :=
  Real.exp (-r) + (1 - Real.exp (-p / 2)) * Real.exp (-3 * r / 2) -
    Real.exp (-p / 2)

theorem SuzukiReporterSecantMiddleBand.transition_factorization
    (P : SuzukiReporterSecantMiddleBand) :
    Real.exp (-(P.residual : ℝ) / 2) *
        suzukiReporterSecantCauchyGram P.shallow (P.shallow + P.residual) =
      suzukiReporterSecantTransitionPolynomial P.shallow P.residual := by
  have hp : 0 ≤ (P.shallow : ℝ) := P.shallow.property
  have hr : 0 ≤ (P.residual : ℝ) := P.residual.property
  have hrp : (P.residual : ℝ) ≤ P.shallow := by exact_mod_cast P.residual_le_shallow
  have h1 : |(P.shallow : ℝ) - (P.shallow + P.residual : ℝ≥0)| = P.residual := by
    rw [show (P.shallow : ℝ) - (P.shallow + P.residual : ℝ≥0) = -(P.residual : ℝ) by
      push_cast; ring, abs_neg, abs_of_nonneg hr]
  have h2 : |(P.shallow : ℝ) - 2 * (P.shallow + P.residual : ℝ≥0)| =
      (P.shallow : ℝ) + 2 * P.residual := by
    rw [show (P.shallow : ℝ) - 2 * (P.shallow + P.residual : ℝ≥0) =
        -((P.shallow : ℝ) + 2 * P.residual) by push_cast; ring,
      abs_neg, abs_of_nonneg (by positivity : 0 ≤ (P.shallow : ℝ) + 2 * P.residual)]
  have h3 : |2 * (P.shallow : ℝ) - (P.shallow + P.residual : ℝ≥0)| =
      (P.shallow : ℝ) - P.residual := by
    rw [show 2 * (P.shallow : ℝ) - (P.shallow + P.residual : ℝ≥0) =
        (P.shallow : ℝ) - P.residual by push_cast; ring,
      abs_of_nonneg (sub_nonneg.mpr hrp)]
  have h4 : |2 * (P.shallow : ℝ) - 2 * (P.shallow + P.residual : ℝ≥0)| =
      2 * (P.residual : ℝ) := by
    rw [show 2 * (P.shallow : ℝ) - 2 * (P.shallow + P.residual : ℝ≥0) =
        -(2 * (P.residual : ℝ)) by push_cast; ring,
      abs_neg, abs_of_nonneg (mul_nonneg (by norm_num) hr)]
  rw [suzukiReporterSecantCauchyGram, cauchyHalfExponentialKernel,
    cauchyHalfExponentialKernel, cauchyHalfExponentialKernel,
    cauchyHalfExponentialKernel, h1, h2, h3, h4,
    suzukiReporterSecantTransitionPolynomial]
  rw [show Real.exp (-((P.shallow : ℝ) + 2 * P.residual) / 2) =
      Real.exp (-(P.shallow : ℝ) / 2) * Real.exp (-(P.residual : ℝ)) by
        rw [← Real.exp_add]; congr 1; ring]
  rw [show Real.exp (-((P.shallow : ℝ) - P.residual) / 2) =
      Real.exp (-(P.shallow : ℝ) / 2) * Real.exp ((P.residual : ℝ) / 2) by
        rw [← Real.exp_add]; congr 1; ring]
  rw [show Real.exp (-(2 * (P.residual : ℝ)) / 2) = Real.exp (-(P.residual : ℝ)) by
        congr 1; ring]
  have hAD : Real.exp (-(P.residual : ℝ) / 2) *
      Real.exp ((P.residual : ℝ) / 2) = 1 := by
    rw [← Real.exp_add]
    rw [show -(P.residual : ℝ) / 2 + P.residual / 2 = 0 by ring,
      Real.exp_zero]
  have hAA : Real.exp (-(P.residual : ℝ) / 2) *
      Real.exp (-(P.residual : ℝ) / 2) = Real.exp (-(P.residual : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hAC : Real.exp (-(P.residual : ℝ) / 2) *
      Real.exp (-(P.residual : ℝ)) = Real.exp (-3 * (P.residual : ℝ) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-(P.residual : ℝ) / 2) *
        (Real.exp (-(P.residual : ℝ) / 2) -
          Real.exp (-(P.shallow : ℝ) / 2) * Real.exp (-(P.residual : ℝ)) -
          Real.exp (-(P.shallow : ℝ) / 2) * Real.exp ((P.residual : ℝ) / 2) +
          Real.exp (-(P.residual : ℝ))) =
      Real.exp (-(P.residual : ℝ) / 2) * Real.exp (-(P.residual : ℝ) / 2) -
        Real.exp (-(P.shallow : ℝ) / 2) *
          (Real.exp (-(P.residual : ℝ) / 2) * Real.exp (-(P.residual : ℝ))) -
        Real.exp (-(P.shallow : ℝ) / 2) *
          (Real.exp (-(P.residual : ℝ) / 2) * Real.exp ((P.residual : ℝ) / 2)) +
        Real.exp (-(P.residual : ℝ) / 2) * Real.exp (-(P.residual : ℝ)) := by ring
    _ = _ := by rw [hAA, hAD, hAC]; ring

theorem continuous_suzukiReporterSecantTransitionPolynomial (p : ℝ) :
    Continuous (suzukiReporterSecantTransitionPolynomial p) := by
  unfold suzukiReporterSecantTransitionPolynomial
  fun_prop

theorem strictAnti_suzukiReporterSecantTransitionPolynomial (p : ℝ≥0) :
    StrictAnti (suzukiReporterSecantTransitionPolynomial p) := by
  intro a b hab
  have he1 : Real.exp (-b) < Real.exp (-a) := Real.exp_lt_exp.mpr (by linarith)
  have he3 : Real.exp (-3 * b / 2) < Real.exp (-3 * a / 2) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hcoef : 0 ≤ 1 - Real.exp (-p / 2) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by
      have hp : 0 ≤ (p : ℝ) := p.property
      linarith))
  have hprod :
      (1 - Real.exp (-(p : ℝ) / 2)) * Real.exp (-3 * b / 2) ≤
        (1 - Real.exp (-(p : ℝ) / 2)) * Real.exp (-3 * a / 2) :=
    mul_le_mul_of_nonneg_left he3.le hcoef
  unfold suzukiReporterSecantTransitionPolynomial
  linarith

theorem suzukiReporterSecantTransitionPolynomial_half (p : ℝ) :
    suzukiReporterSecantTransitionPolynomial p (p / 2) =
      (1 - Real.exp (-p / 2)) * Real.exp (-3 * p / 4) := by
  rw [suzukiReporterSecantTransitionPolynomial]
  ring_nf

theorem suzukiReporterSecantTransitionPolynomial_self (p : ℝ) :
    suzukiReporterSecantTransitionPolynomial p p =
      -Real.exp (-p / 2) * (1 - Real.exp (-p / 2)) ^ 2 *
        (1 + Real.exp (-p / 2)) := by
  have hsq : Real.exp (-p) = Real.exp (-p / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hcube : Real.exp (-3 * p / 2) = Real.exp (-p / 2) ^ 3 := by
    rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [suzukiReporterSecantTransitionPolynomial, hsq, hcube]
  ring

theorem existsUnique_suzukiReporterSecantTransitionResidual
    (p : {p : ℝ≥0 // p ≠ 0}) :
    ∃! r : ℝ, r ∈ Set.Ioo ((p.1 : ℝ) / 2) p.1 ∧
      suzukiReporterSecantTransitionPolynomial p.1 r = 0 := by
  have hp : 0 < (p.1 : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr p.2)
  have ha : 0 < suzukiReporterSecantTransitionPolynomial p.1 ((p.1 : ℝ) / 2) := by
    rw [suzukiReporterSecantTransitionPolynomial_half]
    exact mul_pos
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
      (Real.exp_pos _)
  have hb : suzukiReporterSecantTransitionPolynomial p.1 p.1 < 0 := by
    rw [suzukiReporterSecantTransitionPolynomial_self]
    have he : 0 < Real.exp (-(p.1 : ℝ) / 2) := Real.exp_pos _
    have hsub : 0 < 1 - Real.exp (-(p.1 : ℝ) / 2) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (neg_neg_of_pos he) (sq_pos_of_pos hsub))
      (by positivity)
  have hcont : ContinuousOn (suzukiReporterSecantTransitionPolynomial p.1)
      (Set.Icc ((p.1 : ℝ) / 2) p.1) :=
    (continuous_suzukiReporterSecantTransitionPolynomial p.1).continuousOn
  obtain ⟨r, hr, hzero⟩ := intermediate_value_Ioo'
    (show (p.1 : ℝ) / 2 ≤ p.1 by linarith) hcont ⟨hb, ha⟩
  refine ⟨r, ⟨hr, hzero⟩, fun s hs => ?_⟩
  exact (strictAnti_suzukiReporterSecantTransitionPolynomial p.1).injective
    (hs.2.trans hzero.symm)

def suzukiReporterSecantTransitionResidual
    (p : {p : ℝ≥0 // p ≠ 0}) : ℝ :=
  Classical.choose (existsUnique_suzukiReporterSecantTransitionResidual p)

theorem suzukiReporterSecantTransitionResidual_mem
    (p : {p : ℝ≥0 // p ≠ 0}) :
    suzukiReporterSecantTransitionResidual p ∈
      Set.Ioo ((p.1 : ℝ) / 2) p.1 :=
  (Classical.choose_spec (existsUnique_suzukiReporterSecantTransitionResidual p)).1.1

theorem suzukiReporterSecantTransitionPolynomial_transitionResidual
    (p : {p : ℝ≥0 // p ≠ 0}) :
    suzukiReporterSecantTransitionPolynomial p.1
      (suzukiReporterSecantTransitionResidual p) = 0 :=
  (Classical.choose_spec (existsUnique_suzukiReporterSecantTransitionResidual p)).1.2

def suzukiReporterSecantTransitionResidualNNReal
    (p : {p : ℝ≥0 // p ≠ 0}) : ℝ≥0 :=
  ⟨suzukiReporterSecantTransitionResidual p,
    (show 0 ≤ suzukiReporterSecantTransitionResidual p by
      have hr := (suzukiReporterSecantTransitionResidual_mem p).1.le
      have hp : 0 ≤ (p.1 : ℝ) / 2 := by positivity
      exact hp.trans hr)⟩

@[simp] theorem coe_suzukiReporterSecantTransitionResidualNNReal
    (p : {p : ℝ≥0 // p ≠ 0}) :
    (suzukiReporterSecantTransitionResidualNNReal p : ℝ) =
      suzukiReporterSecantTransitionResidual p := rfl

def suzukiReporterSecantTransitionDepth
    (p : {p : ℝ≥0 // p ≠ 0}) : ℝ≥0 :=
  p.1 + suzukiReporterSecantTransitionResidualNNReal p

theorem suzukiReporterSecantTransitionDepth_mem
    (p : {p : ℝ≥0 // p ≠ 0}) :
    (suzukiReporterSecantTransitionDepth p : ℝ) ∈
      Set.Ioo (3 * (p.1 : ℝ) / 2) (2 * p.1) := by
  have hr := suzukiReporterSecantTransitionResidual_mem p
  change 3 * (p.1 : ℝ) / 2 < (p.1 : ℝ) +
      suzukiReporterSecantTransitionResidual p ∧
    (p.1 : ℝ) + suzukiReporterSecantTransitionResidual p < 2 * p.1
  constructor <;> linarith [hr.1, hr.2]

theorem suzukiReporterSecantCauchyGram_transitionDepth_eq_zero
    (p : {p : ℝ≥0 // p ≠ 0}) :
    suzukiReporterSecantCauchyGram p.1
      (suzukiReporterSecantTransitionDepth p) = 0 := by
  let P : SuzukiReporterSecantMiddleBand :=
    { shallow := p.1
      residual := suzukiReporterSecantTransitionResidualNNReal p
      residual_le_shallow := by
        exact_mod_cast (suzukiReporterSecantTransitionResidual_mem p).2.le }
  have hfactor := P.transition_factorization
  have hroot := suzukiReporterSecantTransitionPolynomial_transitionResidual p
  change suzukiReporterSecantCauchyGram P.shallow (P.shallow + P.residual) = 0
  change Real.exp (-suzukiReporterSecantTransitionResidual p / 2) *
      suzukiReporterSecantCauchyGram p.1
        (p.1 + suzukiReporterSecantTransitionResidualNNReal p) =
      suzukiReporterSecantTransitionPolynomial p.1
        (suzukiReporterSecantTransitionResidual p) at hfactor
  rw [hroot] at hfactor
  exact (mul_eq_zero.mp hfactor).resolve_left (Real.exp_ne_zero _)

structure SuzukiReporterSecantStrictMiddleBand extends SuzukiReporterSecantMiddleBand where
  shallow_ne_zero : shallow ≠ 0

def SuzukiReporterSecantStrictMiddleBand.transitionResidual
    (P : SuzukiReporterSecantStrictMiddleBand) : ℝ :=
  suzukiReporterSecantTransitionResidual ⟨P.shallow, P.shallow_ne_zero⟩

theorem SuzukiReporterSecantStrictMiddleBand.transitionResidual_mem
    (P : SuzukiReporterSecantStrictMiddleBand) :
    P.transitionResidual ∈ Set.Ioo ((P.shallow : ℝ) / 2) P.shallow :=
  suzukiReporterSecantTransitionResidual_mem ⟨P.shallow, P.shallow_ne_zero⟩

theorem SuzukiReporterSecantStrictMiddleBand.gram_sign_trichotomy
    (P : SuzukiReporterSecantStrictMiddleBand) :
    ((P.residual : ℝ) < P.transitionResidual ∧
        0 < suzukiReporterSecantCauchyGram P.shallow (P.shallow + P.residual)) ∨
      ((P.residual : ℝ) = P.transitionResidual ∧
        suzukiReporterSecantCauchyGram P.shallow (P.shallow + P.residual) = 0) ∨
      (P.transitionResidual < (P.residual : ℝ) ∧
        suzukiReporterSecantCauchyGram P.shallow (P.shallow + P.residual) < 0) := by
  have hfactor := P.toSuzukiReporterSecantMiddleBand.transition_factorization
  have hroot : suzukiReporterSecantTransitionPolynomial P.shallow P.transitionResidual = 0 :=
    suzukiReporterSecantTransitionPolynomial_transitionResidual
      ⟨P.shallow, P.shallow_ne_zero⟩
  have hexp : 0 < Real.exp (-(P.residual : ℝ) / 2) := Real.exp_pos _
  rcases lt_trichotomy (P.residual : ℝ) P.transitionResidual with hlt | heq | hgt
  · left
    refine ⟨hlt, ?_⟩
    have hT : 0 < suzukiReporterSecantTransitionPolynomial P.shallow P.residual := by
      have := strictAnti_suzukiReporterSecantTransitionPolynomial P.shallow hlt
      rw [hroot] at this
      exact this
    nlinarith
  · right
    left
    refine ⟨heq, ?_⟩
    have hT : suzukiReporterSecantTransitionPolynomial P.shallow P.residual = 0 := by
      rw [heq, hroot]
    nlinarith
  · right
    right
    refine ⟨hgt, ?_⟩
    have hT : suzukiReporterSecantTransitionPolynomial P.shallow P.residual < 0 := by
      have := strictAnti_suzukiReporterSecantTransitionPolynomial P.shallow hgt
      rw [hroot] at this
      exact this
    nlinarith

structure SuzukiReporterSecantSharpNegativePair extends SuzukiReporterSecantStrictMiddleBand where
  transitionResidual_lt_residual :
    toSuzukiReporterSecantStrictMiddleBand.transitionResidual < (residual : ℝ)

theorem SuzukiReporterSecantSharpNegativePair.gram_neg
    (P : SuzukiReporterSecantSharpNegativePair) :
    suzukiReporterSecantCauchyGram P.shallow (P.shallow + P.residual) < 0 := by
  rcases P.toSuzukiReporterSecantStrictMiddleBand.gram_sign_trichotomy with h | h | h
  · exact False.elim (not_lt_of_ge P.transitionResidual_lt_residual.le h.1)
  · exfalso
    linarith [P.transitionResidual_lt_residual, h.1]
  · exact h.2

structure SuzukiReporterSecantSharpPositivePair extends SuzukiReporterSecantStrictMiddleBand where
  residual_lt_transitionResidual :
    (residual : ℝ) < toSuzukiReporterSecantStrictMiddleBand.transitionResidual

theorem SuzukiReporterSecantSharpPositivePair.gram_pos
    (P : SuzukiReporterSecantSharpPositivePair) :
    0 < suzukiReporterSecantCauchyGram P.shallow (P.shallow + P.residual) := by
  rcases P.toSuzukiReporterSecantStrictMiddleBand.gram_sign_trichotomy with h | h | h
  · exact h.2
  · exact False.elim (ne_of_lt P.residual_lt_transitionResidual h.1)
  · exact False.elim (not_lt_of_ge P.residual_lt_transitionResidual.le h.1)

end

end GaloisForLFunctions.RHTower
