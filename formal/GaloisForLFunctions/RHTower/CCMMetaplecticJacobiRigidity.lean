import GaloisForLFunctions.RHTower.CCMCyclicPairJacobiLiterature

/-!
# Metaplectic Jacobi-coefficient rigidity

This module formalizes the coefficient-rigidity clause of Connes--Consani Theorem 7.1.  Their
`sl₂` commutator relation says that the diagonal discrepancy of the cyclic Jacobi action is the
constant `i/2`.  Among nonnegative Jacobi coefficients, the complete solution set is the singleton

`aₙ = (1/2) * sqrt ((2n+1)(2n+2))`.

The endpoint `a₋₁ = 0`, recurrence, positivity-based square-root uniqueness, and singleton
classification are all explicit.  No representation-existence or moment-problem premise is left
as a hypothesis.
-/

open Complex Set

noncomputable section

namespace RHTower

def ccmMetaplecticJacobiCoefficient (n : ℕ) : NNReal :=
  Real.toNNReal ((1 / 2 : ℝ) *
    Real.sqrt ((((2 * n + 1) * (2 * n + 2) : ℕ) : ℝ)))

theorem ccmMetaplecticJacobiCoefficient_sq (n : ℕ) :
    (ccmMetaplecticJacobiCoefficient n : ℝ) ^ 2 =
      (1 / 4 : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * ((2 * n + 2 : ℕ) : ℝ) := by
  rw [ccmMetaplecticJacobiCoefficient]
  rw [Real.coe_toNNReal _ (by positivity)]
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  push_cast
  ring

def ccmMetaplecticJacobiRecurrenceSolutions : Set (ℕ → NNReal) :=
  {a | (a 0 : ℝ) ^ 2 = 1 / 2 ∧
    ∀ n : ℕ, (a (n + 1) : ℝ) ^ 2 - (a n : ℝ) ^ 2 = 2 * (n : ℝ) + 5 / 2}

theorem ccmMetaplecticJacobiCoefficient_mem_recurrenceSolutions :
    ccmMetaplecticJacobiCoefficient ∈ ccmMetaplecticJacobiRecurrenceSolutions := by
  constructor
  · rw [ccmMetaplecticJacobiCoefficient_sq]
    norm_num
  · intro n
    rw [ccmMetaplecticJacobiCoefficient_sq,
      ccmMetaplecticJacobiCoefficient_sq]
    push_cast
    ring

theorem ccmMetaplecticJacobiRecurrenceSolutions_eq_singleton :
    ccmMetaplecticJacobiRecurrenceSolutions =
      {ccmMetaplecticJacobiCoefficient} := by
  ext a
  constructor
  · intro ha
    have hsquare : ∀ n : ℕ, (a n : ℝ) ^ 2 =
        (ccmMetaplecticJacobiCoefficient n : ℝ) ^ 2 := by
      intro n
      induction n with
      | zero =>
          rw [ccmMetaplecticJacobiCoefficient_sq]
          norm_num at ha ⊢
          exact ha.1
      | succ n ih =>
          have hrec := ha.2 n
          have hexp := ccmMetaplecticJacobiCoefficient_mem_recurrenceSolutions.2 n
          nlinarith
    have hfun : a = ccmMetaplecticJacobiCoefficient := by
      funext n
      apply NNReal.eq
      nlinarith [hsquare n, (a n).coe_nonneg,
        (ccmMetaplecticJacobiCoefficient n).coe_nonneg]
    simp [hfun]
  · intro ha
    rw [Set.mem_singleton_iff] at ha
    simpa [ha] using ccmMetaplecticJacobiCoefficient_mem_recurrenceSolutions

theorem ccmCyclicDiscrepancy_eq_halfI_iff_recurrence
    (a : ℕ → NNReal) :
    (∀ n : ℕ, ccmCyclicDiscrepancy (fun j => (a j : ℂ)) n = I / 2) ↔
      a ∈ ccmMetaplecticJacobiRecurrenceSolutions := by
  constructor
  · intro h
    constructor
    · have h0 := h 0
      simp [ccmCyclicDiscrepancy, Complex.ext_iff] at h0
      simpa [pow_two] using h0
    · intro n
      have hn := h (n + 1)
      simp [ccmCyclicDiscrepancy, Complex.ext_iff] at hn
      nlinarith
  · rintro ⟨h0, hrec⟩ n
    cases n with
    | zero =>
        simp [ccmCyclicDiscrepancy, Complex.ext_iff]
        simpa [pow_two] using h0
    | succ n =>
        have hn := hrec n
        simp [ccmCyclicDiscrepancy, Complex.ext_iff]
        simp only [pow_two] at hn ⊢
        nlinarith

theorem ccmCyclicDiscrepancy_halfI_solutions_eq_singleton :
    {a : ℕ → NNReal |
      ∀ n : ℕ, ccmCyclicDiscrepancy (fun j => (a j : ℂ)) n = I / 2} =
      {ccmMetaplecticJacobiCoefficient} := by
  rw [← ccmMetaplecticJacobiRecurrenceSolutions_eq_singleton]
  ext a
  exact ccmCyclicDiscrepancy_eq_halfI_iff_recurrence a

end RHTower
