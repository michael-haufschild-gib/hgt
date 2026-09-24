import GaloisForLFunctions.RHTower.XiLogDerivReCriticalLine
import GaloisForLFunctions.RHTower.XiLogDerivLineOnePositive

/-!
# The strict form of the criterion

The line-conjugate pair is strictly positive whenever the zero lies strictly inside its disk
relative to `s`, and the divisor is nonempty by Hardy's theorem, so the criterion holds with
**strict** inequality wherever the disk bound is strict.

Together with `re_logDeriv_xi_eq_zero_of_re_eq_half` this pins the boundary behaviour exactly:
under the Riemann hypothesis `Re (ξ'/ξ)` is strictly positive at every point right of the critical
line and vanishes identically on it.
-/

open Complex

namespace RHTower

noncomputable section

theorem centralPaired_tsum_re_pos_of_lineConj_pairs
    (f : XiZeroCopy → ℂ) (hsum : Summable f)
    (hpair : ∀ q : XiZeroCopy, 0 ≤ (f q + f (xiZeroCopyLineConjEquiv q)).re)
    (q₀ : XiZeroCopy) (hq₀ : 0 < (f q₀ + f (xiZeroCopyLineConjEquiv q₀)).re) :
    0 < (∑' q : XiZeroCopy, f q).re := by
  have hsumJ : Summable (fun q : XiZeroCopy => f (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr hsum
  have hpairs := hsum.add hsumJ
  have hreindex : (∑' q : XiZeroCopy, f (xiZeroCopyLineConjEquiv q)) =
      ∑' q : XiZeroCopy, f q := xiZeroCopyLineConjEquiv.tsum_eq f
  have hpairsumRe' :
      (∑' q : XiZeroCopy, (f q + f (xiZeroCopyLineConjEquiv q)).re) =
        (∑' q : XiZeroCopy, f q).re + (∑' q : XiZeroCopy, f q).re := by
    calc
      (∑' q : XiZeroCopy, (f q + f (xiZeroCopyLineConjEquiv q)).re) =
          (∑' q : XiZeroCopy, (f q + f (xiZeroCopyLineConjEquiv q))).re :=
        (Complex.re_tsum hpairs).symm
      _ = ((∑' q : XiZeroCopy, f q) +
          (∑' q : XiZeroCopy, f (xiZeroCopyLineConjEquiv q))).re := by
        rw [hsum.tsum_add hsumJ]
      _ = ((∑' q : XiZeroCopy, f q) + ∑' q : XiZeroCopy, f q).re := by rw [hreindex]
      _ = (∑' q : XiZeroCopy, f q).re + (∑' q : XiZeroCopy, f q).re := by rw [Complex.add_re]
  have hsummableRe : Summable
      (fun q : XiZeroCopy => (f q + f (xiZeroCopyLineConjEquiv q)).re) :=
    hpairs.mapL Complex.reCLM
  have hpos : 0 < ∑' q : XiZeroCopy, (f q + f (xiZeroCopyLineConjEquiv q)).re :=
    Summable.tsum_pos hsummableRe hpair q₀ hq₀
  rw [hpairsumRe'] at hpos
  linarith

/-- **Strict form of the criterion.**  If every zero is strictly inside its disk relative to `s`,
the criterion holds with strict inequality: the completed logarithmic derivative has strictly
positive real part.  Strictness comes from the divisor being nonempty (Hardy). -/
theorem re_logDeriv_xi_pos_of_disk_bound {s : ℂ} (hs : 1 / 2 < s.re) (hxi : xi s ≠ 0)
    (hzeros : ∀ q : XiZeroCopy, (((q.1 : ℂ)).re - 1 / 2) ^ 2 <
      (s.re - 1 / 2) ^ 2 + (s.im - ((q.1 : ℂ)).im) ^ 2) :
    0 < (logDeriv xi s).re := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  have hpairkey : ∀ q : XiZeroCopy,
      0 < ((((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹) +
        ((((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2)⁻¹ +
          (s - (((xiZeroCopyLineConjEquiv q).1 : ℂ)))⁻¹)).re := by
    intro q
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
  rw [logDeriv_xi_eq_partialFraction hxi]
  obtain ⟨q₀⟩ := nonempty_xiZeroCopy_xiLogDerivLineOnePositive
  refine centralPaired_tsum_re_pos_of_lineConj_pairs _ ?_ (fun q => (hpairkey q).le) q₀
    (hpairkey q₀)
  have h := XiAtlasFinitePart.summable_logDerivTerm hxi
  refine h.congr (fun q => ?_)
  show (XiAtlasFinitePart.xiZero q - 1 / 2)⁻¹ - (XiAtlasFinitePart.xiZero q - s)⁻¹ =
    ((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹
  rw [XiAtlasFinitePart.xiZero, show ((q.1 : ℂ) - s) = -(s - (q.1 : ℂ)) by ring, inv_neg]
  ring

/-- **Strict criterion under RH.**  Off the critical line the margin is strictly positive; by
`re_logDeriv_xi_eq_zero_of_re_eq_half` it degenerates to equality exactly on the line. -/
theorem re_logDeriv_xi_pos_of_riemannHypothesis (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) (hxi : xi s ≠ 0) :
    0 < (logDeriv xi s).re := by
  refine re_logDeriv_xi_pos_of_disk_bound hs hxi (fun q => ?_)
  rw [xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q]
  nlinarith [sq_nonneg (s.im - ((q.1 : ℂ)).im)]

end

end RHTower
