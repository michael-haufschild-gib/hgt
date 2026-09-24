import GaloisForLFunctions.RHTower.XiLogDerivReCriterion

/-!
# Locality of the completed positivity criterion

The line-conjugate pair at a zero `ρ` is negative at `s` exactly inside the disk

```text
(Re ρ - 1/2)^2 > (Re s - 1/2)^2 + (Im s - Im ρ)^2 ,
```

so a zero obstructs only from inside its own off-line disk.  Since every zero satisfies
`(Re ρ - 1/2)^2 < 1/4`, a zero whose ordinate is at distance at least `1/2` from `Im s` can never
obstruct.

Hence the criterion `0 ≤ Re (ξ'/ξ)(s)` is **local in the ordinate**: it follows from the disk
condition restricted to the zeros in the unit ordinate window around `Im s`, of which there are
only `O(log |Im s|)`.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Sharp form of the pair criterion.**  Only the full disk condition is needed: a zero
obstructs at `s` only if it lies in the disk `(Re ρ - 1/2)^2 ≥ (Re s - 1/2)^2 + (Im s - Im ρ)^2`. -/
theorem re_logDeriv_xi_nonneg_of_disk_bound {s : ℂ} (hs : 1 / 2 < s.re) (hxi : xi s ≠ 0)
    (hzeros : ∀ q : XiZeroCopy, (((q.1 : ℂ)).re - 1 / 2) ^ 2 <
      (s.re - 1 / 2) ^ 2 + (s.im - ((q.1 : ℂ)).im) ^ 2) :
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
      simp at hq
    have h2 : s - (1 - (starRingEnd ℂ) ((q.1 : ℂ))) ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      intro hcon
      have hre : s.re = 1 - ((q.1 : ℂ)).re := by rw [hcon]; simp
      have him : s.im = ((q.1 : ℂ)).im := by rw [hcon]; simp
      rw [hre, him] at hq
      nlinarith
    have hpos := re_inv_add_re_inv_lineConj_pos (s := s) (ρ := (q.1 : ℂ)) h1 h2 hs hq
    have hrw : s - (((xiZeroCopyLineConjEquiv q).1 : ℂ)) =
        s - (1 - (starRingEnd ℂ) ((q.1 : ℂ))) := by rw [hρ']
    simp only [Complex.add_re]
    rw [hconst, hrw]
    linarith [hpos]

/-- **The criterion is local in the ordinate.**  A zero whose ordinate is at distance at least
`1/2` from `Im s` can never obstruct, because every zero satisfies `(Re ρ - 1/2)^2 < 1/4`.  So only
zeros in the unit ordinate window around `Im s` matter. -/
theorem re_logDeriv_xi_nonneg_of_near_zeros {s : ℂ} (hs : 1 / 2 < s.re) (hxi : xi s ≠ 0)
    (hnear : ∀ q : XiZeroCopy, (s.im - ((q.1 : ℂ)).im) ^ 2 < 1 / 4 →
      (((q.1 : ℂ)).re - 1 / 2) ^ 2 < (s.re - 1 / 2) ^ 2 + (s.im - ((q.1 : ℂ)).im) ^ 2) :
    0 ≤ (logDeriv xi s).re := by
  refine re_logDeriv_xi_nonneg_of_disk_bound hs hxi (fun q => ?_)
  by_cases hy : (s.im - ((q.1 : ℂ)).im) ^ 2 < 1 / 4
  · exact hnear q hy
  · have hstrip : (((q.1 : ℂ)).re - 1 / 2) ^ 2 < 1 / 4 :=
      xi_divisor_support_centered_re_sq_lt_quarter q.1
    have hx : 0 < (s.re - 1 / 2) ^ 2 := by nlinarith
    nlinarith [not_lt.mp hy]

end

end RHTower
