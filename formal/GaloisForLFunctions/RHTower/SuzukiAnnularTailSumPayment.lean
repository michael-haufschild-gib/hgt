import GaloisForLFunctions.RHTower.SuzukiAnnularCriticalPayment

/-!
# The annular payment is a tail sum, and its annulus ratio is free

Fixing the number of critical-line witnesses at two is what forces the tight band
`[3h, (432/25)h]` and hence a critical-line proportion above `5/12`.  Nothing in the two exact
height estimates uses the count.

The slope gap `(τ_q - τ_r)² > 256/(625(1+h)²)` needs only `k_r ≥ 3h` and the off-line height gap;
the upper end of the band enters solely through the witness mass `a_r = 1/(1+k_r)`.  So the whole
payment condition against the atomwise charge bound `A χ_q/a_q < 29/(625(1+h)³)` is the single
scalar inequality

`∑_{r} 1/(1+k_r) ≥ 29/(256(1+h))`,

a sum over an arbitrary finite set of critical-line copies above `3h`.  Two witnesses in the
original band give `50/(432(1+h))` against `29/(256(1+h))`, which is exactly the recorded margin,
so the two-witness theorem is the two-element case.

Because the left side is now a sum, an annulus of *any* fixed ratio `K` works as soon as it carries
`(87/256)K²` witnesses — a constant.  The zero-counting input therefore drops from a proportion
above `5/12` to the existence of one fixed annulus carrying a bounded number of critical-line
ordinates at every large height.
-/

open Finset

namespace RHTower

noncomputable section

/-- **The slope gap needs only the lower end of the band.**  Any critical-line copy at least three
times as high as an off-line atom is separated from it by the sector floor. -/
theorem slope_gap_sq_gt (q r : XiZeroCopy) (hcrit : (r.1 : ℂ).re = 1 / 2)
    (hlow : 3 * (q.1 : ℂ).im ^ 2 ≤ (r.1 : ℂ).im ^ 2)
    (hheight : (141 / 2 : ℝ) < (q.1 : ℂ).im ^ 2) :
    256 / (625 * (1 + (q.1 : ℂ).im ^ 2) ^ 2)
      < (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ 2 := by
  set h : ℝ := (q.1 : ℂ).im ^ 2 with hh
  set k : ℝ := (r.1 : ℂ).im ^ 2 with hk
  have hh0 : 0 < h := by linarith
  have hk0 : 0 < k := by linarith
  obtain ⟨hmass, hslope⟩ := criticalLine_mass_and_slope r hcrit
  rw [← hk] at hmass hslope
  have hq := slope_gt_of_height q
  rw [← hh] at hq
  have hden1 : (0 : ℝ) < 1 + h := by linarith
  have hden3 : (0 : ℝ) < 1 + 3 * h := by linarith
  have hslope_r_le : xiShiftedResponseSlope 1 r ≤ 1 / (1 + 3 * h) := by
    rw [hslope]
    apply div_le_div_of_nonneg_left (by norm_num) hden3
    linarith
  have hgap : 16 / (25 * (1 + h)) < xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r := by
    have hstep : 16 / (25 * (1 + h)) ≤ 83 / (85 * (1 + h)) - 1 / (1 + 3 * h) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith [hheight, hden1, hden3]
    linarith
  have hpos : (0 : ℝ) < 16 / (25 * (1 + h)) := by positivity
  have hsq : (16 / (25 * (1 + h))) ^ 2
      < (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ 2 :=
    pow_lt_pow_left₀ hgap hpos.le (by norm_num)
  have hval : (16 / (25 * (1 + h))) ^ 2 = 256 / (625 * (1 + h) ^ 2) := by
    field_simp
    ring
  linarith [hval ▸ hsq]

/-- **`(SR-64.28)`: the tail-sum payment criterion.**  An arbitrary finite family of critical-line
copies above `3h` pays the complete-mass-normalized charge of one off-line atom as soon as its
total response mass clears `29/(256(1+h))`. -/
theorem tailSum_annular_payment (q : XiZeroCopy) {S : Finset XiZeroCopy}
    (hS : S.Nonempty)
    (hcrit : ∀ r ∈ S, (r.1 : ℂ).re = 1 / 2)
    (hlow : ∀ r ∈ S, 3 * (q.1 : ℂ).im ^ 2 ≤ (r.1 : ℂ).im ^ 2)
    (hheight : (141 / 2 : ℝ) < (q.1 : ℂ).im ^ 2)
    (hmass : 29 / (256 * (1 + (q.1 : ℂ).im ^ 2)) ≤ ∑ r ∈ S, xiShiftedResponseMass 1 r) :
    (∑' i : XiZeroCopy, xiShiftedResponseMass 1 i) * xiShiftedTransverseChargeDensity 1 q
      < xiShiftedResponseMass 1 q *
        ∑ r ∈ S, xiShiftedResponseMass 1 r
            * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ 2 := by
  set h : ℝ := (q.1 : ℂ).im ^ 2 with hh
  have hh0 : 0 < h := by linarith
  have hden1 : (0 : ℝ) < 1 + h := by linarith
  have hden3 : (0 : ℝ) < (1 + h) ^ 3 := by positivity
  have hmq : 0 < xiShiftedResponseMass 1 q := xiShiftedResponseMass_pos (by norm_num) q
  set A : ℝ := ∑' i : XiZeroCopy, xiShiftedResponseMass 1 i with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact tsum_nonneg fun i => (xiShiftedResponseMass_pos (by norm_num) i).le
  have hAlt : A < (29 / 625 : ℝ) := tsum_xiShiftedResponseMass_one_lt
  have hratio := chargeRatio_lt_inv_cube q
  rw [← hh] at hratio
  have hchi : xiShiftedTransverseChargeDensity 1 q
      < 1 / (1 + h) ^ 3 * xiShiftedResponseMass 1 q := by
    rw [div_lt_iff₀ hmq] at hratio
    exact hratio
  have hXpos : (0 : ℝ) < 1 / (1 + h) ^ 3 * xiShiftedResponseMass 1 q := by positivity
  have hchargebound : A * xiShiftedTransverseChargeDensity 1 q
      < (29 / 625 : ℝ) / (1 + h) ^ 3 * xiShiftedResponseMass 1 q := by
    calc A * xiShiftedTransverseChargeDensity 1 q
        ≤ A * (1 / (1 + h) ^ 3 * xiShiftedResponseMass 1 q) :=
          mul_le_mul_of_nonneg_left hchi.le hA0
      _ < (29 / 625 : ℝ) * (1 / (1 + h) ^ 3 * xiShiftedResponseMass 1 q) :=
          mul_lt_mul_of_pos_right hAlt hXpos
      _ = (29 / 625 : ℝ) / (1 + h) ^ 3 * xiShiftedResponseMass 1 q := by ring
  have hterm : ∀ r ∈ S,
      xiShiftedResponseMass 1 r * (256 / (625 * (1 + h) ^ 2))
        < xiShiftedResponseMass 1 r
            * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ 2 := by
    intro r hr
    have hgap := slope_gap_sq_gt q r (hcrit r hr) (hlow r hr) hheight
    rw [← hh] at hgap
    exact mul_lt_mul_of_pos_left hgap (xiShiftedResponseMass_pos (by norm_num) r)
  have hsumlt : (∑ r ∈ S, xiShiftedResponseMass 1 r) * (256 / (625 * (1 + h) ^ 2))
      < ∑ r ∈ S, xiShiftedResponseMass 1 r
          * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_lt_sum_of_nonempty hS hterm
  have hfloor : (29 / 625 : ℝ) / (1 + h) ^ 3
      ≤ (∑ r ∈ S, xiShiftedResponseMass 1 r) * (256 / (625 * (1 + h) ^ 2)) := by
    have hcoef : (0 : ℝ) < 256 / (625 * (1 + h) ^ 2) := by positivity
    have hstep := mul_le_mul_of_nonneg_right hmass hcoef.le
    refine le_trans (le_of_eq ?_) hstep
    field_simp
  calc A * xiShiftedTransverseChargeDensity 1 q
      < (29 / 625 : ℝ) / (1 + h) ^ 3 * xiShiftedResponseMass 1 q := hchargebound
    _ ≤ ((∑ r ∈ S, xiShiftedResponseMass 1 r) * (256 / (625 * (1 + h) ^ 2)))
          * xiShiftedResponseMass 1 q := by
        exact mul_le_mul_of_nonneg_right hfloor hmq.le
    _ < (∑ r ∈ S, xiShiftedResponseMass 1 r
          * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ 2)
          * xiShiftedResponseMass 1 q := mul_lt_mul_of_pos_right hsumlt hmq
    _ = xiShiftedResponseMass 1 q *
          ∑ r ∈ S, xiShiftedResponseMass 1 r
            * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ 2 := by ring

/-- **`(SR-64.29)`: a fixed annulus with a constant witness count clears the mass floor.**  The
required count depends only on the annulus ratio, not on the height. -/
theorem annulus_mass_floor (q : XiZeroCopy) {S : Finset XiZeroCopy} {K : ℝ}
    (hK : 1 ≤ K)
    (hcrit : ∀ r ∈ S, (r.1 : ℂ).re = 1 / 2)
    (hhigh : ∀ r ∈ S, (r.1 : ℂ).im ^ 2 ≤ 3 * K ^ 2 * (q.1 : ℂ).im ^ 2)
    (hcard : (87 / 256 : ℝ) * K ^ 2 ≤ (S.card : ℝ)) :
    29 / (256 * (1 + (q.1 : ℂ).im ^ 2)) ≤ ∑ r ∈ S, xiShiftedResponseMass 1 r := by
  set h : ℝ := (q.1 : ℂ).im ^ 2 with hh
  have hh0 : 0 < h := by
    have := xiZeroCopy_fortyOne_div_two_lt_im_sq q
    rw [← hh] at this
    linarith
  have hden1 : (0 : ℝ) < 1 + h := by linarith
  have hK0 : (0 : ℝ) < K := by linarith
  have hbig : (0 : ℝ) < 3 * K ^ 2 * (1 + h) := by positivity
  have hterm : ∀ r ∈ S, 1 / (3 * K ^ 2 * (1 + h)) ≤ xiShiftedResponseMass 1 r := by
    intro r hr
    obtain ⟨hmass, -⟩ := criticalLine_mass_and_slope r (hcrit r hr)
    rw [hmass]
    have hk : (r.1 : ℂ).im ^ 2 ≤ 3 * K ^ 2 * h := hhigh r hr
    have hkpos : (0 : ℝ) < 1 + (r.1 : ℂ).im ^ 2 := by
      have := xiZeroCopy_fortyOne_div_two_lt_im_sq r
      linarith
    apply div_le_div_of_nonneg_left (by norm_num) hkpos
    nlinarith [hK0, hh0]
  have hsum : (S.card : ℝ) * (1 / (3 * K ^ 2 * (1 + h)))
      ≤ ∑ r ∈ S, xiShiftedResponseMass 1 r := by
    calc (S.card : ℝ) * (1 / (3 * K ^ 2 * (1 + h)))
        = ∑ _r ∈ S, (1 / (3 * K ^ 2 * (1 + h))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ S, xiShiftedResponseMass 1 r := Finset.sum_le_sum hterm
  refine le_trans ?_ hsum
  rw [div_le_iff₀ (by positivity)]
  have hcoef : (0 : ℝ) < 1 / (3 * K ^ 2 * (1 + h)) := by positivity
  have hstep := mul_le_mul_of_nonneg_right hcard hcoef.le
  have hval : (87 / 256 : ℝ) * K ^ 2 * (1 / (3 * K ^ 2 * (1 + h)))
      = 29 / (256 * (1 + h)) := by
    field_simp
    ring
  rw [hval] at hstep
  rw [div_le_iff₀ (by positivity)] at hstep
  nlinarith [hstep, hcoef, hden1]

/-- **The fixed-annulus payment.**  A constant number of critical-line copies in an annulus of any
fixed ratio pays the complete-mass-normalized charge of one off-line atom. -/
theorem annulus_annular_payment (q : XiZeroCopy) {S : Finset XiZeroCopy} {K : ℝ}
    (hS : S.Nonempty) (hK : 1 ≤ K)
    (hcrit : ∀ r ∈ S, (r.1 : ℂ).re = 1 / 2)
    (hlow : ∀ r ∈ S, 3 * (q.1 : ℂ).im ^ 2 ≤ (r.1 : ℂ).im ^ 2)
    (hhigh : ∀ r ∈ S, (r.1 : ℂ).im ^ 2 ≤ 3 * K ^ 2 * (q.1 : ℂ).im ^ 2)
    (hheight : (141 / 2 : ℝ) < (q.1 : ℂ).im ^ 2)
    (hcard : (87 / 256 : ℝ) * K ^ 2 ≤ (S.card : ℝ)) :
    (∑' i : XiZeroCopy, xiShiftedResponseMass 1 i) * xiShiftedTransverseChargeDensity 1 q
      < xiShiftedResponseMass 1 q *
        ∑ r ∈ S, xiShiftedResponseMass 1 r
            * (xiShiftedResponseSlope 1 q - xiShiftedResponseSlope 1 r) ^ 2 :=
  tailSum_annular_payment q hS hcrit hlow hheight
    (annulus_mass_floor q hK hcrit hhigh hcard)

end

end RHTower
