import GaloisForLFunctions.RHTower.XiLogDerivRePositiveRightOfStrip
import GaloisForLFunctions.RHTower.WeilLagFunctionHerglotz

/-!
# The sharp form of the completed positivity criterion

The line-conjugate pair law makes `Re (ξ'/ξ)(s)` nonnegative as soon as **every** zero is strictly
closer to the critical line than `s` is:

```text
(Re ρ - 1/2)^2 < (Re s - 1/2)^2   for all ρ   ⟹   0 ≤ Re (ξ'/ξ)(s) .
```

Two consequences bracket the Riemann hypothesis exactly.  Unconditionally the hypothesis holds on
`Re s ≥ 1`, since every zero satisfies `(Re ρ - 1/2)^2 < 1/4 ≤ (Re s - 1/2)^2`.  Under the Riemann
hypothesis it holds on the whole half plane `Re s > 1/2`, since then every zero has
`(Re ρ - 1/2)^2 = 0`.  The gap between the two is precisely the off-line disks.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The criterion holds wherever `s` is further from the critical line than every zero.**
No arithmetic input: the pair law makes each line-conjugate pair positive as soon as
`(Re ρ - 1/2)^2 < (Re s - 1/2)^2`. -/
theorem re_logDeriv_xi_nonneg_of_strip_bound {s : ℂ} (hs : 1 / 2 < s.re) (hxi : xi s ≠ 0)
    (hzeros : ∀ q : XiZeroCopy, (((q.1 : ℂ)).re - 1 / 2) ^ 2 < (s.re - 1 / 2) ^ 2) :
    0 ≤ (logDeriv xi s).re := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  rw [logDeriv_xi_eq_partialFraction hxi]
  refine centralPaired_tsum_re_nonneg_of_lineConj_pairs _ ?_ ?_
  · have h := XiAtlasFinitePart.summable_logDerivTerm hxi
    refine h.congr (fun q => ?_)
    show (XiAtlasFinitePart.xiZero q - 1 / 2)⁻¹ - (XiAtlasFinitePart.xiZero q - s)⁻¹ =
      ((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹
    rw [XiAtlasFinitePart.xiZero, show ((q.1 : ℂ) - s) = -(s - (q.1 : ℂ)) by ring, inv_neg]
    ring
  · intro q
    have hq := hzeros q
    have hρ' := xiZero_lineConj_eq q
    have hcenter : (((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2) =
        -((starRingEnd ℂ) ((q.1 : ℂ) - 1 / 2)) := by
      rw [hρ', map_sub, hhalf]; ring
    have hconst : ((((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2)⁻¹).re =
        -((((q.1 : ℂ)) - 1 / 2)⁻¹).re := by
      rw [hcenter, inv_neg, ← map_inv₀, Complex.neg_re, Complex.conj_re]
    have h1 : s - (q.1 : ℂ) ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      intro hcon
      rw [hcon] at hq
      exact absurd hq (lt_irrefl _)
    have h2 : s - (1 - (starRingEnd ℂ) ((q.1 : ℂ))) ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      intro hcon
      have hre : s.re = 1 - ((q.1 : ℂ)).re := by rw [hcon]; simp
      rw [hre] at hq
      nlinarith
    have hpos := re_inv_add_re_inv_lineConj_pos (s := s) (ρ := (q.1 : ℂ)) h1 h2 hs
      (by nlinarith [sq_nonneg (s.im - ((q.1 : ℂ)).im)])
    have hrw : s - (((xiZeroCopyLineConjEquiv q).1 : ℂ)) =
        s - (1 - (starRingEnd ℂ) ((q.1 : ℂ))) := by rw [hρ']
    simp only [Complex.add_re]
    rw [hconst, hrw]
    linarith [hpos]

/-- **Under the Riemann hypothesis the criterion holds on the whole right half-strip.** -/
theorem re_logDeriv_xi_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) (hxi : xi s ≠ 0) :
    0 ≤ (logDeriv xi s).re := by
  refine re_logDeriv_xi_nonneg_of_strip_bound hs hxi (fun q => ?_)
  rw [xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q]
  nlinarith

end

end RHTower
