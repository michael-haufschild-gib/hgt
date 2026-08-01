import GaloisForLFunctions.HTGeometry.BohrParsevalUpper
import GaloisForLFunctions.HTGeometry.BohrMultiFejerOperator

/-!
# Parseval's identity for almost periodic functions

The mean square of an almost periodic function is the sum of the squared moduli of its Bohr
coefficients.

Both halves are already available: the error expansion of a trigonometric approximation is a
completed square, so every finite partial sum of squared coefficients is at most the mean square
(Bessel), and the mean-square approximation makes the partial sums come arbitrarily close to it.
The mean square is therefore the least upper bound of the partial sums, which for a nonnegative
family is exactly unconditional summability.
-/

open ComplexConjugate

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

/-- **Bessel's inequality.**  Every finite partial sum of squared Bohr coefficients is at most the
mean square. -/
theorem sum_normSq_bohrCoefficient_le {f : ℝ →ᵇ ℂ}
    (htb : HasTotallyBoundedOrbit fun x => f x) (S : Finset ℝ) :
    ∑ lam ∈ S, Complex.normSq (bohrCoefficient (fun x => f x) lam)
      ≤ (bohrMean (fun t => f t * conj (f t))).re := by
  classical
  have hap : HTGeometry.IsBohrAlmostPeriodic fun x => f x :=
    isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit htb
  have hcont : Continuous fun x => f x := f.continuous
  set c : ℝ → ℂ := bohrCoefficient (fun x => f x) with hc
  have hexp := bohrMean_sub_trigPoly_mul_conj hcont hap S c
  have hre : (bohrMean (fun t => ((fun x => f x) t - trigPoly S c t) *
      conj ((fun x => f x) t - trigPoly S c t))).re
      = (bohrMean (fun t => f t * conj (f t))).re
        - ∑ lam ∈ S, Complex.normSq (c lam) := by
    rw [hexp, Complex.sub_re, Complex.re_sum]
    have hterm : ∀ lam ∈ S, (conj (c lam) * c lam + c lam * conj (c lam)
        - c lam * conj (c lam)).re = Complex.normSq (c lam) := by
      intro lam _
      rw [re_pairing_eq, sub_self]
      simp
    rw [Finset.sum_congr rfl hterm]
  have hnn : 0 ≤ (bohrMean (fun t => ((fun x => f x) t - trigPoly S c t) *
      conj ((fun x => f x) t - trigPoly S c t))).re := by
    refine bohrMean_mul_conj_re_nonneg (hcont.sub (continuous_trigPoly S c)) ?_
    exact isBohrAlmostPeriodic_sub hcont hap (continuous_trigPoly S c)
      (isBohrAlmostPeriodic_trigPoly S c)
  linarith [hre ▸ hnn]

/-- **Parseval's identity.**  The squared Bohr coefficients sum to the mean square. -/
theorem hasSum_normSq_bohrCoefficient {f : ℝ →ᵇ ℂ} (hf : UniformContinuous fun x => f x)
    (htb : HasTotallyBoundedOrbit fun x => f x) :
    HasSum (fun lam : ℝ => Complex.normSq (bohrCoefficient (fun x => f x) lam))
      (bohrMean (fun t => f t * conj (f t))).re := by
  classical
  refine hasSum_of_isLUB_of_nonneg _ (fun lam => Complex.normSq_nonneg _) ⟨?_, ?_⟩
  · rintro x ⟨S, rfl⟩
    exact sum_normSq_bohrCoefficient_le htb S
  · intro y hy
    by_contra hlt
    have hylt : y < (bohrMean (fun t => f t * conj (f t))).re := by
      exact lt_of_not_ge hlt
    obtain ⟨S, hS⟩ := exists_finset_bohrMean_normSq_le hf htb
      (show (0 : ℝ) < ((bohrMean (fun t => f t * conj (f t))).re - y) / 2 by linarith)
    have hmem : (∑ lam ∈ S, Complex.normSq (bohrCoefficient (fun x => f x) lam))
        ∈ Set.range fun s : Finset ℝ =>
          ∑ lam ∈ s, Complex.normSq (bohrCoefficient (fun x => f x) lam) := ⟨S, rfl⟩
    have := hy hmem
    linarith

/-- The mean square is the supremum of the finite partial sums. -/
theorem tsum_normSq_bohrCoefficient {f : ℝ →ᵇ ℂ} (hf : UniformContinuous fun x => f x)
    (htb : HasTotallyBoundedOrbit fun x => f x) :
    ∑' lam : ℝ, Complex.normSq (bohrCoefficient (fun x => f x) lam)
      = (bohrMean (fun t => f t * conj (f t))).re :=
  (hasSum_normSq_bohrCoefficient hf htb).tsum_eq

/-- **The spectrum is countable.**  A summable nonnegative family has countable support. -/
theorem countable_bohrSpectrum {f : ℝ →ᵇ ℂ} (hf : UniformContinuous fun x => f x)
    (htb : HasTotallyBoundedOrbit fun x => f x) :
    (bohrSpectrum fun x => f x).Countable := by
  have hsum : Summable fun lam : ℝ => Complex.normSq (bohrCoefficient (fun x => f x) lam) :=
    (hasSum_normSq_bohrCoefficient hf htb).summable
  refine (hsum.countable_support).mono ?_
  intro lam hlam
  have hne : bohrCoefficient (fun x => f x) lam ≠ 0 := hlam
  simp only [Function.mem_support, ne_eq, Complex.normSq_eq_zero]
  exact hne

end

end GaloisForLFunctions
