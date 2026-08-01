import GaloisForLFunctions.RHTower.MobiusExponentialGibbsBoundary

/-!
# Prime-renewal defect at the Route E large-prime boundary

The zero-minus-one-large-prime comparison factors through one universal scalar kernel.  This
module records the exact finite identity and the normalized renewal-ratio factorization.  No
estimate for the signed small-prime sum is assumed.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Finite prime-renewal defect: one base exponential minus its selected prime dilates. -/
def finitePrimeRenewalDefect (Q : Finset ℕ) (t : ℂ) : ℂ :=
  Complex.exp (-t) - ∑ q ∈ Q, Complex.exp (-(q : ℂ) * t)

/-- Ratio of the selected prime tail to the base exponential. -/
def finitePrimeRenewalRatio (Q : Finset ℕ) (t : ℂ) : ℂ :=
  ∑ q ∈ Q, Complex.exp (-((q : ℂ) - 1) * t)

/-- Exact normalized factorization of the prime-renewal defect. -/
theorem finitePrimeRenewalDefect_eq_exp_mul_ratio
    (Q : Finset ℕ) (t : ℂ) :
    finitePrimeRenewalDefect Q t =
      Complex.exp (-t) * (1 - finitePrimeRenewalRatio Q t) := by
  rw [finitePrimeRenewalDefect, finitePrimeRenewalRatio, mul_sub,
    mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro q _hq
  rw [← Complex.exp_add]
  congr 1
  ring_nf

/-- At zero scale the renewal ratio is exactly the number of selected tail primes. -/
theorem finitePrimeRenewalRatio_zero (Q : Finset ℕ) :
    finitePrimeRenewalRatio Q 0 = Q.card := by
  rw [finitePrimeRenewalRatio]
  simp

/-- Exact finite zero/one-prime factorization.  The same scalar renewal defect is tested at every
small-prime subset product; no termwise norm or probability approximation has been taken. -/
theorem finitePrimeParityPartition_sub_sum_dilations
    (P Q : Finset ℕ) (w : ℂ) :
    finitePrimeParityPartition P w -
        ∑ q ∈ Q, finitePrimeParityPartition P ((q : ℂ) * w) =
      ∑ T ∈ P.powerset,
        (-1 : ℂ) ^ T.card *
          finitePrimeRenewalDefect Q (((finitePrimeSubsetProduct T : ℕ) : ℂ) * w) := by
  rw [finitePrimeParityPartition]
  simp_rw [finitePrimeParityPartition, finitePrimeRenewalDefect, mul_sub,
    Finset.mul_sum]
  rw [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro T _hT
    congr 1
    ring_nf
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T _hT
    apply Finset.sum_congr rfl
    intro q _hq
    congr 1
    ring_nf

/-! ## Exact consumer for the all-prime zero/one boundary source -/

/-- Every strict-half estimate for the signed zero-plus-one-large-prime boundary, at some
admissible moving aperture, with no estimate assumed for either sector separately. -/
def MobiusLargePrimeBoundaryAllStrictHalf : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      ∃ z : ℕ,
        (1 / 2 : ℝ) * Real.log (1 / x) ≤ (((z ^ 2) + 1 : ℕ) : ℝ) * x ∧
        ‖mobiusZeroLargePrimeLaplaceTransform z x +
            mobiusOneLargePrimeLaplaceTransform z x‖ ≤
          C * x ^ (-(1 / 2 + ε))

/-- Unconditional consumer: the zero/one boundary law absorbs the already-critical
two-or-more-large-prime remainder and gives every strict-half Möbius--Laplace estimate. -/
theorem mobiusDiscreteLaplaceAllStrictHalfPowerDecay_of_largePrimeBoundary
    (hboundary : MobiusLargePrimeBoundaryAllStrictHalf) :
    MobiusDiscreteLaplaceAllStrictHalfPowerDecay := by
  intro b hb
  let ε : ℝ := b - 1 / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, hsource⟩ := hboundary ε hε
  rw [Asymptotics.isBigO_iff]
  refine ⟨C + 2, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx0 hx1
  have hx : 0 < x := hx0
  obtain ⟨z, hscale, hz⟩ := hsource x hx hx1.le
  have hexponent : -(1 / 2 + ε) = -b := by
    dsimp [ε]
    ring
  rw [hexponent] at hz
  have hremainder :=
    norm_mobiusTwoLargePrimeRemainderLaplaceTransform_le_critical
      z hx hx1.le hscale
  have hhalf : x ^ (-(1 / 2 : ℝ)) ≤ x ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_ge hx hx1.le (by linarith)
  rw [mobiusDiscreteLaplaceTransform_eq_largePrimeBoundary_add_remainder z hx]
  calc
    ‖mobiusZeroLargePrimeLaplaceTransform z x +
          mobiusOneLargePrimeLaplaceTransform z x +
        mobiusTwoLargePrimeRemainderLaplaceTransform z x‖ ≤
        ‖mobiusZeroLargePrimeLaplaceTransform z x +
          mobiusOneLargePrimeLaplaceTransform z x‖ +
        ‖mobiusTwoLargePrimeRemainderLaplaceTransform z x‖ := norm_add_le _ _
    _ ≤ C * x ^ (-b) + 2 * x ^ (-(1 / 2 : ℝ)) := add_le_add hz hremainder
    _ ≤ C * x ^ (-b) + 2 * x ^ (-b) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hhalf (by norm_num))
    _ = (C + 2) * x ^ (-b) := by ring
    _ = (C + 2) * ‖x ^ (-b)‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)]

/-- Proving the literal zero/one-large-prime boundary source proves RH. -/
theorem riemannHypothesis_of_mobiusLargePrimeBoundaryAllStrictHalf
    (hboundary : MobiusLargePrimeBoundaryAllStrictHalf) :
    RiemannHypothesis :=
  mobiusDiscreteLaplaceAllStrictHalfPowerDecay_implies_riemannHypothesis
    (mobiusDiscreteLaplaceAllStrictHalfPowerDecay_of_largePrimeBoundary hboundary)

end

end RHTower
