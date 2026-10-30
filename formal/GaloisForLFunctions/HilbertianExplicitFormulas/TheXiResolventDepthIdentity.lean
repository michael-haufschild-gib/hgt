import GaloisForLFunctions.HilbertianExplicitFormulas.TheResolventHilbertianExplicitFormula
import GaloisForLFunctions.ArithmeticElectrostatics.TheExternalFieldIsAPrimeSum
import GaloisForLFunctions.RHTower.XiLogDerivRePositiveRightOfStrip

/-!
# The resolvent depth identity on the full Xi divisor

Right of the critical strip, the same-point resolvent sum is absolutely convergent.
Pairing each zero with its critical-line reflection gives
`(Re s - 1/2) S(s) - Re (ξ'/ξ)(s) = D(s)`, where `D` is the sum of the
nonnegative depth terms. The explicit part is the archimedean logarithmic derivative
minus the von Mangoldt series. Every zero retains its analytic multiplicity.
-/

open Complex RHTower ArithmeticFunction
open GaloisForLFunctions.ArithmeticCorrespondencePositivity
open GaloisForLFunctions.ArithmeticElectrostatics

namespace GaloisForLFunctions.HilbertianExplicitFormulas

noncomputable section

/-- The squared Cauchy norm on the multiplicity-exact Xi divisor. -/
def xiSamePointResolvent (s : ℂ) : ℝ :=
  ∑' q : XiZeroCopy, 1 / normSq (s - (q.1 : ℂ))

/-- The contribution of one zero copy to the reflection-symmetrized depth sum. -/
def xiResolventDepthTerm (s : ℂ) (q : XiZeroCopy) : ℝ :=
  2 * (s.re - 1 / 2) * ((q.1 : ℂ).re - 1 / 2) ^ 2 /
    (normSq (s - (q.1 : ℂ)) * normSq (s - lineReflect (q.1 : ℂ)))

/-- The full depth sum, with analytic multiplicities carried by `XiZeroCopy`. -/
def xiResolventDepth (s : ℂ) : ℝ := ∑' q : XiZeroCopy, xiResolventDepthTerm s q

private theorem summable_real_reciprocal (s : ℂ) :
    Summable (fun q : XiZeroCopy => ((s - (q.1 : ℂ))⁻¹).re) := by
  simpa only [xiRealReciprocal, Complex.ofReal_zero, add_zero] using
    xiRealReciprocal_summable s (h := 0) (by norm_num)

/-- The positive real reciprocal field dominates the squared Cauchy kernel. -/
theorem summable_xiSamePointResolvent {s : ℂ} (hs : 1 < s.re) :
    Summable (fun q : XiZeroCopy => 1 / normSq (s - (q.1 : ℂ))) := by
  refine Summable.of_nonneg_of_le (fun q => by positivity) ?_
    ((summable_real_reciprocal s).mul_left (s.re - 1)⁻¹)
  intro q
  have hβ := (xiDivisorSupport_re_mem q.1).2
  have hσ : 0 < s.re - 1 := sub_pos.mpr hs
  rw [Complex.inv_re, Complex.sub_re]
  calc
    1 / normSq (s - (q.1 : ℂ)) =
        (s.re - 1)⁻¹ * ((s.re - 1) / normSq (s - (q.1 : ℂ))) := by
      field_simp [hσ.ne']
    _ ≤ (s.re - 1)⁻¹ * ((s.re - (q.1 : ℂ).re) / normSq (s - (q.1 : ℂ))) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (by linarith only [hβ]) (normSq_nonneg _))
        (inv_nonneg.mpr hσ.le)

private theorem summable_signed_depth {s : ℂ} (hs : 1 < s.re) :
    Summable (fun q : XiZeroCopy => ((q.1 : ℂ).re - 1 / 2) /
      normSq (s - (q.1 : ℂ))) := by
  refine (((summable_xiSamePointResolvent hs).mul_left (s.re - 1 / 2)).sub
    (summable_real_reciprocal s)).congr fun q => ?_
  simpa only [div_eq_mul_inv, mul_one] using sub_inv_re_eq s (q.1 : ℂ)

private theorem normSq_sub_zero_pos {s : ℂ} (hs : 1 < s.re) (q : XiZeroCopy) :
    0 < normSq (s - (q.1 : ℂ)) := by
  apply normSq_pos.mpr
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.zero_re] at hre
  linarith only [hre, (xiDivisorSupport_re_mem q.1).2, hs]

private theorem pair_xi_signed_depth {s : ℂ} (hs : 1 < s.re) (q : XiZeroCopy) :
    ((q.1 : ℂ).re - 1 / 2) / normSq (s - (q.1 : ℂ)) +
        (((xiZeroCopyLineConjEquiv q).1 : ℂ).re - 1 / 2) /
          normSq (s - ((xiZeroCopyLineConjEquiv q).1 : ℂ)) =
      2 * xiResolventDepthTerm s q := by
  have href : ((xiZeroCopyLineConjEquiv q).1 : ℂ) = lineReflect (q.1 : ℂ) :=
    xiZero_lineConj_eq q
  have hp := pair_depth_resolvent s (q.1 : ℂ)
    (normSq_sub_zero_pos hs q).ne'
    (by rw [← href]; exact (normSq_sub_zero_pos hs (xiZeroCopyLineConjEquiv q)).ne')
  rw [href, hp, xiResolventDepthTerm]
  ring

/-- Absolute convergence of the positive depth series follows from the signed pair identity. -/
theorem summable_xiResolventDepthTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (xiResolventDepthTerm s) := by
  have h := summable_signed_depth hs
  have hr := xiZeroCopyLineConjEquiv.summable_iff.mpr h
  refine ((h.add hr).mul_left (1 / 2 : ℝ)).congr fun q => ?_
  rw [pair_xi_signed_depth hs q]
  ring

/-- The finite reflection identity extends to all Xi zeros by absolute summation. -/
theorem sub_mul_xiSamePointResolvent_sub_logDeriv {s : ℂ} (hs : 1 < s.re) :
    (s.re - 1 / 2) * xiSamePointResolvent s - (logDeriv xi s).re =
      xiResolventDepth s := by
  have h := summable_signed_depth hs
  have hr := xiZeroCopyLineConjEquiv.summable_iff.mpr h
  have hpair : 2 * (∑' q : XiZeroCopy,
      ((q.1 : ℂ).re - 1 / 2) / normSq (s - (q.1 : ℂ))) =
      2 * xiResolventDepth s := by
    calc
      _ = ∑' q : XiZeroCopy,
          (((q.1 : ℂ).re - 1 / 2) / normSq (s - (q.1 : ℂ)) +
            (((xiZeroCopyLineConjEquiv q).1 : ℂ).re - 1 / 2) /
              normSq (s - ((xiZeroCopyLineConjEquiv q).1 : ℂ))) := by
        rw [h.tsum_add hr, xiZeroCopyLineConjEquiv.tsum_eq]
        ring
      _ = ∑' q : XiZeroCopy, 2 * xiResolventDepthTerm s q :=
        tsum_congr (pair_xi_signed_depth hs)
      _ = _ := tsum_mul_left
  have hpoint : (s.re - 1 / 2) * xiSamePointResolvent s - (logDeriv xi s).re =
      ∑' q : XiZeroCopy, ((q.1 : ℂ).re - 1 / 2) / normSq (s - (q.1 : ℂ)) := by
    rw [xiSamePointResolvent, re_logDeriv_xi_eq_tsum_of_one_lt_re hs,
      ← tsum_mul_left, ← ((summable_xiSamePointResolvent hs).mul_left _).tsum_sub
        (summable_real_reciprocal s)]
    apply tsum_congr
    intro q
    simpa only [div_eq_mul_inv, mul_one] using sub_inv_re_eq s (q.1 : ℂ)
  linarith only [hpair, hpoint]

/-- Every term of the full depth series is nonnegative to the right of the critical line. -/
theorem xiResolventDepthTerm_nonneg {s : ℂ} (hs : 1 / 2 ≤ s.re) (q : XiZeroCopy) :
    0 ≤ xiResolventDepthTerm s q :=
  div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hs)) (sq_nonneg _))
    (mul_nonneg (normSq_nonneg _) (normSq_nonneg _))

theorem xiResolventDepth_nonneg {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    0 ≤ xiResolventDepth s := tsum_nonneg (xiResolventDepthTerm_nonneg hs)

/-- The exact full-divisor depth identity with its Euler and archimedean terms opened. -/
theorem xiResolventDepth_eq_samePoint_sub_arch_add_prime {s : ℂ} (hs : 1 < s.re) :
    xiResolventDepth s =
      (s.re - 1 / 2) * xiSamePointResolvent s - (logDeriv archFactor s).re +
        ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  rw [← sub_mul_xiSamePointResolvent_sub_logDeriv hs,
    (xi_ne_zero_and_logDeriv_split hs).2, Complex.add_re,
    ← re_LSeries_vonMangoldt_eq hs, re_LSeries_vonMangoldt_eq_neg hs]
  ring

end

end GaloisForLFunctions.HilbertianExplicitFormulas
