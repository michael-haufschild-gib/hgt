import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewFirstGap
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# Suzuki's first-gap positivity without numerical root finding

Suzuki (2022), Theorem 4.1 states that the literal prime--Lerch function `Psi` is positive on
an interval `(0,t₀)` with `t₀ > log 2`.  The published proof locates two derivative zeros by a
computer calculation, and its displayed derivative also omits the term `-(log pi)/2` already
identified in `SuzukiScrewFirstGap`.

This module proves the full printed theorem unconditionally.  Five Lerch blocks are retained
exactly.  The remaining infinite tail is bounded by a telescoping reciprocal progression, not by
numerical quadrature.  After the substitution `y = exp(-t/2)`, a rational tangent certificate at
`y=18/25` proves positivity on the whole closed first gap.  Continuity then extends positivity
strictly past the first prime-power seam.
-/

open Filter Set Topology
open GaloisForLFunctions.RHTower
open scoped BigOperators

noncomputable section

namespace RHTower

private def reciprocalStep (N j : ℕ) : ℝ :=
  1 / (4 * (N + j) + 1 : ℕ) - 1 / (4 * (N + j + 1) + 1 : ℕ)

private theorem reciprocalStep_nonneg (N j : ℕ) : 0 ≤ reciprocalStep N j := by
  unfold reciprocalStep
  rw [sub_nonneg]
  exact one_div_le_one_div_of_le (by positivity) (by norm_cast; omega)

private theorem hasSum_reciprocalStep (N : ℕ) :
    HasSum (reciprocalStep N) (1 / (4 * N + 1 : ℕ)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (reciprocalStep_nonneg N)]
  have hden : Tendsto (fun n : ℕ => (4 : ℝ) * n + (4 * N + 1 : ℕ))
      atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 4)).atTop_add
      tendsto_const_nhds
  have hinv : Tendsto (fun n : ℕ =>
      ((4 : ℝ) * n + (4 * N + 1 : ℕ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hlim : Tendsto (fun n : ℕ =>
      (1 / (4 * N + 1 : ℕ) : ℝ) -
        ((4 : ℝ) * n + (4 * N + 1 : ℕ))⁻¹)
      atTop (𝓝 ((1 / (4 * N + 1 : ℕ) : ℝ) - 0)) :=
    tendsto_const_nhds.sub hinv
  convert hlim using 1
  · funext n
    unfold reciprocalStep
    simp only [Nat.add_assoc]
    rw [Finset.sum_range_sub' (fun j => (1 / (4 * (N + j) + 1 : ℕ) : ℝ))]
    congr 1
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  · ring

private theorem reciprocalStep_le_lerch_reciprocal_sq (N j : ℕ) :
    reciprocalStep N j ≤ 1 / (lerchExp (N + j)) ^ (2 : ℕ) := by
  have hA : (0 : ℝ) < (4 * (N + j) + 1 : ℕ) := by positivity
  have hB : (0 : ℝ) < (4 * (N + j + 1) + 1 : ℕ) := by positivity
  have hstep : reciprocalStep N j =
      4 / ((4 * (N + j) + 1 : ℕ) * (4 * (N + j + 1) + 1 : ℕ) : ℝ) := by
    unfold reciprocalStep
    field_simp
    push_cast
    ring
  have hlerch : lerchExp (N + j) = (4 * (N + j) + 1 : ℕ) / 2 := by
    simp [lerchExp]
    ring
  rw [hstep, hlerch]
  have hle : (4 * (N + j) + 1 : ℕ) ≤ 4 * (N + j + 1) + 1 := by omega
  have hden : ((4 * (N + j) + 1 : ℕ) : ℝ) ^ (2 : ℕ) ≤
      ((4 * (N + j) + 1 : ℕ) : ℝ) * (4 * (N + j + 1) + 1 : ℕ) := by
    have hleR : ((4 * (N + j) + 1 : ℕ) : ℝ) ≤
        ((4 * (N + j + 1) + 1 : ℕ) : ℝ) := by exact_mod_cast hle
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hleR hA.le
  rw [div_pow]
  norm_num
  have hone := one_div_le_one_div_of_le (by positivity) hden
  have hfour := mul_le_mul_of_nonneg_left hone (by norm_num : (0 : ℝ) ≤ 4)
  norm_num [Nat.cast_add, Nat.cast_mul, div_eq_mul_inv] at hfour ⊢
  exact hfour

private theorem lerch_difference_tail_lower (N : ℕ) {t : ℝ} (ht : 0 < t) :
    (∑ k ∈ Finset.range N,
        (1 - Real.exp (-(lerchExp k * t))) / (lerchExp k) ^ (2 : ℕ)) +
      (1 - Real.exp (-(lerchExp N * t))) / (4 * N + 1 : ℕ) ≤
        screwLerchConst - screwLerchTail t := by
  have hfull : HasSum (fun k : ℕ =>
      (1 - Real.exp (-(lerchExp k * t))) / (lerchExp k) ^ (2 : ℕ))
      (screwLerchConst - screwLerchTail t) := by
    have hzero : HasSum (fun k : ℕ => 1 / (lerchExp k) ^ (2 : ℕ)) screwLerchConst := by
      simpa [screwLerchConst, screwLerchTail] using summable_one_div_lerchExp_sq.hasSum
    have htail : HasSum (fun k : ℕ =>
        Real.exp (-(lerchExp k * t)) / (lerchExp k) ^ (2 : ℕ)) (screwLerchTail t) :=
      (summable_screwLerchTerm ht).hasSum
    apply HasSum.congr_fun (hzero.sub htail)
    intro k
    ring
  have htail := (hasSum_nat_add_iff' N).mpr hfull
  let base : ℝ := 1 - Real.exp (-(lerchExp N * t))
  have hbase : 0 ≤ base := by
    dsimp [base]
    have : Real.exp (-(lerchExp N * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [lerchExp_pos N]
    linarith
  have hmono : ∀ j : ℕ, base ≤ 1 - Real.exp (-(lerchExp (j + N) * t)) := by
    intro j
    dsimp [base]
    have hlam : lerchExp N ≤ lerchExp (j + N) := by
      simp [lerchExp]
    have hexp : Real.exp (-(lerchExp (j + N) * t)) ≤
        Real.exp (-(lerchExp N * t)) := by
      rw [Real.exp_le_exp]
      nlinarith
    linarith
  have hsmall : Summable (fun j : ℕ => base * reciprocalStep N j) :=
    (hasSum_reciprocalStep N).summable.mul_left base
  have hlarge : Summable (fun j : ℕ =>
      (1 - Real.exp (-(lerchExp (j + N) * t))) / (lerchExp (j + N)) ^ (2 : ℕ)) :=
    htail.summable
  have hpoint : ∀ j : ℕ, base * reciprocalStep N j ≤
      (1 - Real.exp (-(lerchExp (j + N) * t))) / (lerchExp (j + N)) ^ (2 : ℕ) := by
    intro j
    have hstep := reciprocalStep_le_lerch_reciprocal_sq N j
    have hstep0 := reciprocalStep_nonneg N j
    have hnum0 : 0 ≤ 1 - Real.exp (-(lerchExp (j + N) * t)) := by
      have : Real.exp (-(lerchExp (j + N) * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [lerchExp_pos (j + N)]
      linarith
    calc
      base * reciprocalStep N j ≤
          (1 - Real.exp (-(lerchExp (j + N) * t))) * reciprocalStep N j :=
        mul_le_mul_of_nonneg_right (hmono j) hstep0
      _ ≤ (1 - Real.exp (-(lerchExp (j + N) * t))) *
          (1 / (lerchExp (N + j)) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hstep hnum0
      _ = _ := by rw [Nat.add_comm]; ring
  have htails := Summable.tsum_le_tsum hpoint hsmall hlarge
  rw [tsum_mul_left] at htails
  rw [(hasSum_reciprocalStep N).tsum_eq, htail.tsum_eq] at htails
  dsimp [base] at htails
  have hadd := (le_sub_iff_add_le).mp htails
  simpa only [div_eq_mul_inv, one_mul, add_comm] using hadd

theorem lerch_difference_five_block_lower {t : ℝ} (ht : 0 < t) :
    4 * (1 - Real.exp (-(t / 2))) +
      (4 / 25) * (1 - Real.exp (-(5 * t / 2))) +
      (4 / 81) * (1 - Real.exp (-(9 * t / 2))) +
      (4 / 169) * (1 - Real.exp (-(13 * t / 2))) +
      (4 / 289) * (1 - Real.exp (-(17 * t / 2))) +
      (1 / 21) * (1 - Real.exp (-(21 * t / 2))) ≤
        screwLerchConst - screwLerchTail t := by
  have h := lerch_difference_tail_lower 5 ht
  norm_num [lerchExp, Finset.sum_range_succ] at h ⊢
  convert h using 1
  all_goals ring_nf

private def geomBlock (m : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, y ^ (j + 1)

private def geomBlockSlope (m : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, (j + 1 : ℕ) * y ^ j

private def fiveBlockPolynomial (y : ℝ) : ℝ :=
  4 - (27 / 10) * (1 + y) +
    (4 / 25) * geomBlock 5 y +
    (4 / 81) * geomBlock 9 y +
    (4 / 169) * geomBlock 13 y +
    (4 / 289) * geomBlock 17 y +
    (1 / 21) * geomBlock 21 y

private def fiveBlockPolynomialSlope (y : ℝ) : ℝ :=
  -(27 / 10) +
    (4 / 25) * geomBlockSlope 5 y +
    (4 / 81) * geomBlockSlope 9 y +
    (4 / 169) * geomBlockSlope 13 y +
    (4 / 289) * geomBlockSlope 17 y +
    (1 / 21) * geomBlockSlope 21 y

private theorem pow_tangent_eighteen_twentyfive (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (18 / 25 : ℝ) ^ (j + 1) +
      (j + 1 : ℕ) * (18 / 25 : ℝ) ^ j * (y - 18 / 25) ≤ y ^ (j + 1) := by
  let q : ℝ := 18 / 25
  have hq : 0 < q := by norm_num [q]
  have hratio0 : 0 ≤ y / q := div_nonneg hy hq.le
  have hratio : -1 ≤ y / q := by linarith
  have h := one_add_mul_sub_le_pow hratio (j + 1)
  have hscaled := mul_le_mul_of_nonneg_left h (pow_nonneg hq.le (j + 1))
  calc
    (18 / 25 : ℝ) ^ (j + 1) +
        (j + 1 : ℕ) * (18 / 25 : ℝ) ^ j * (y - 18 / 25) =
        q ^ (j + 1) * (1 + (j + 1 : ℕ) * (y / q - 1)) := by
      dsimp [q]
      field_simp
      ring
    _ ≤ q ^ (j + 1) * (y / q) ^ (j + 1) := hscaled
    _ = y ^ (j + 1) := by
      rw [← mul_pow]
      congr 1
      field_simp [hq.ne']

private theorem geomBlock_tangent_eighteen_twentyfive (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    geomBlock m (18 / 25) +
      geomBlockSlope m (18 / 25) * (y - 18 / 25) ≤ geomBlock m y := by
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.range m) =>
    pow_tangent_eighteen_twentyfive j hy
  rw [geomBlock, geomBlockSlope, geomBlock]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact hsum

private theorem fiveBlockPolynomial_tangent {y : ℝ} (hy : 0 ≤ y) :
    fiveBlockPolynomial (18 / 25) +
      fiveBlockPolynomialSlope (18 / 25) * (y - 18 / 25) ≤
        fiveBlockPolynomial y := by
  have h5 := geomBlock_tangent_eighteen_twentyfive 5 hy
  have h9 := geomBlock_tangent_eighteen_twentyfive 9 hy
  have h13 := geomBlock_tangent_eighteen_twentyfive 13 hy
  have h17 := geomBlock_tangent_eighteen_twentyfive 17 hy
  have h21 := geomBlock_tangent_eighteen_twentyfive 21 hy
  dsimp only [fiveBlockPolynomial, fiveBlockPolynomialSlope]
  nlinarith

private theorem fiveBlockPolynomial_center_pos :
    (1 / 50 : ℝ) < fiveBlockPolynomial (18 / 25) := by
  norm_num [fiveBlockPolynomial, geomBlock, Finset.sum_range_succ]

private theorem abs_fiveBlockPolynomialSlope_center_lt :
    |fiveBlockPolynomialSlope (18 / 25)| < (1 / 25 : ℝ) := by
  norm_num [fiveBlockPolynomialSlope, geomBlockSlope, Finset.sum_range_succ, abs_lt]

private theorem fiveBlockPolynomial_pos {y : ℝ} (hylo : (7 / 10 : ℝ) ≤ y)
    (hyhi : y ≤ 1) : 0 < fiveBlockPolynomial y := by
  have hy : 0 ≤ y := by linarith
  have htangent := fiveBlockPolynomial_tangent hy
  have hcenter := fiveBlockPolynomial_center_pos
  have hslope := abs_fiveBlockPolynomialSlope_center_lt
  have hdist : |y - 18 / 25| ≤ (7 / 25 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hproduct :
      |fiveBlockPolynomialSlope (18 / 25) * (y - 18 / 25)| < (7 / 625 : ℝ) := by
    rw [abs_mul]
    by_cases hzero : y - 18 / 25 = 0
    · simp [hzero]
    · calc
        |fiveBlockPolynomialSlope (18 / 25)| * |y - 18 / 25| <
            (1 / 25) * |y - 18 / 25| :=
          mul_lt_mul_of_pos_right hslope (abs_pos.mpr hzero)
        _ ≤ (1 / 25) * (7 / 25) :=
          mul_le_mul_of_nonneg_left hdist (by norm_num)
        _ = 7 / 625 := by norm_num
  have hterm : -(7 / 625 : ℝ) <
      fiveBlockPolynomialSlope (18 / 25) * (y - 18 / 25) :=
    (abs_lt.mp hproduct).1
  nlinarith

private def suzukiFirstGapLower (t : ℝ) : ℝ :=
  4 * (Real.exp (t / 2) - 1) - (27 / 10) * t +
    (4 / 25) * (1 - Real.exp (-(5 * t / 2))) +
    (4 / 81) * (1 - Real.exp (-(9 * t / 2))) +
    (4 / 169) * (1 - Real.exp (-(13 * t / 2))) +
    (4 / 289) * (1 - Real.exp (-(17 * t / 2))) +
    (1 / 21) * (1 - Real.exp (-(21 * t / 2)))

private theorem exp_neg_half_pow (m : ℕ) (t : ℝ) :
    Real.exp (-(t / 2)) ^ m = Real.exp (-((m : ℝ) * t / 2)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem suzukiFirstGapLower_pos {t : ℝ} (ht : 0 < t)
    (htlog : t ≤ Real.log 2) : 0 < suzukiFirstGapLower t := by
  let x : ℝ := Real.exp (t / 2)
  let y : ℝ := Real.exp (-(t / 2))
  have hx : 0 < x := Real.exp_pos _
  have hy : 0 < y := Real.exp_pos _
  have hxy : x * y = 1 := by
    dsimp [x, y]
    rw [← Real.exp_add]
    norm_num
  have hxdiv : x = 1 / y := by
    rw [eq_div_iff hy.ne']
    exact hxy
  have hytop : y < 1 := by
    dsimp [y]
    rw [Real.exp_lt_one_iff]
    linarith
  have hyone : y ≤ 1 := hytop.le
  have hy_sq : (1 / 2 : ℝ) ≤ y ^ (2 : ℕ) := by
    have hneg : -Real.log 2 ≤ -t := by linarith
    have hexp := Real.exp_le_exp.mpr hneg
    have hlog2 : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    have hy2 : y ^ (2 : ℕ) = Real.exp (-t) := by
      dsimp [y]
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rw [hlog2, ← hy2] at hexp
    exact hexp
  have hylo : (7 / 10 : ℝ) ≤ y := by
    by_contra h
    rw [not_le] at h
    nlinarith
  have hK : 0 < fiveBlockPolynomial y := fiveBlockPolynomial_pos hylo hyone
  have hsinh : t ≤ x - y := by
    have h := (Real.self_le_sinh_iff (x := t / 2)).mpr (by linarith)
    rw [Real.sinh_eq] at h
    dsimp [x, y]
    nlinarith
  have h5 : Real.exp (-(5 * t / 2)) = y ^ (5 : ℕ) := by
    rw [exp_neg_half_pow]
    norm_num
  have h9 : Real.exp (-(9 * t / 2)) = y ^ (9 : ℕ) := by
    rw [exp_neg_half_pow]
    norm_num
  have h13 : Real.exp (-(13 * t / 2)) = y ^ (13 : ℕ) := by
    rw [exp_neg_half_pow]
    norm_num
  have h17 : Real.exp (-(17 * t / 2)) = y ^ (17 : ℕ) := by
    rw [exp_neg_half_pow]
    norm_num
  have h21 : Real.exp (-(21 * t / 2)) = y ^ (21 : ℕ) := by
    rw [exp_neg_half_pow]
    norm_num
  have hfactor :
      4 * (x - 1) - (27 / 10) * (x - y) +
        (4 / 25) * (1 - y ^ (5 : ℕ)) +
        (4 / 81) * (1 - y ^ (9 : ℕ)) +
        (4 / 169) * (1 - y ^ (13 : ℕ)) +
        (4 / 289) * (1 - y ^ (17 : ℕ)) +
        (1 / 21) * (1 - y ^ (21 : ℕ)) =
          ((1 - y) / y) * fiveBlockPolynomial y := by
    rw [hxdiv]
    field_simp [hy.ne']
    norm_num [fiveBlockPolynomial, geomBlock, Finset.sum_range_succ]
    ring
  have hfactorPos : 0 < ((1 - y) / y) * fiveBlockPolynomial y :=
    mul_pos (div_pos (sub_pos.mpr hytop) hy) hK
  rw [← hfactor] at hfactorPos
  dsimp [suzukiFirstGapLower]
  rw [show Real.exp (t / 2) = x by rfl, h5, h9, h13, h17, h21]
  nlinarith

theorem screwPrimeSum_eq_zero_of_le_log_two {t : ℝ} (ht : t ≤ Real.log 2) :
    screwPrimeSum t = 0 := by
  rcases ht.lt_or_eq with hlt | rfl
  · exact screwPrimeSum_eq_zero_of_lt_log_two hlt
  · rw [screwPrimeSum, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num

theorem suzukiFirstGapLower_lt_suzukiPsi {t : ℝ} (ht : 0 < t)
    (htlog : t ≤ Real.log 2) : suzukiFirstGapLower t < suzukiPsi t := by
  have hprime := screwPrimeSum_eq_zero_of_le_log_two htlog
  have htail := lerch_difference_five_block_lower ht
  have hcoeff : -(27 / 10 : ℝ) < screwLinearCoeff / 2 := by
    nlinarith [neg_twentySeven_tenths_lt_screwLinearCoeff_half]
  have hlinear : -(27 / 10 : ℝ) * t < screwLinearCoeff / 2 * t :=
    mul_lt_mul_of_pos_right hcoeff ht
  have hpsi :
      suzukiPsi t =
        4 * (Real.exp (t / 2) + Real.exp (-(t / 2)) - 2) +
          screwLinearCoeff / 2 * t +
          (screwLerchConst - screwLerchTail t) := by
    rw [suzukiPsi, abs_of_pos ht, screwFn, hprime]
    ring
  rw [hpsi]
  dsimp [suzukiFirstGapLower]
  nlinarith

/-- **Suzuki 2022, Theorem 4.1, full source statement.**  There is an interval extending
strictly beyond the first prime-power seam `log 2` on which the literal prime--Lerch function
`Psi` is strictly positive.  The proof is unconditional and replaces the paper's numerical
root-finding by the exact five-block/telescoping-tail certificate above. -/
theorem suzuki_theorem_four_one :
    ∃ t0 : ℝ, Real.log 2 < t0 ∧
      ∀ t : ℝ, 0 < t → t < t0 → 0 < suzukiPsi t := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hboundary : 0 < suzukiPsi (Real.log 2) :=
    (suzukiFirstGapLower_pos hlog2 le_rfl).trans
      (suzukiFirstGapLower_lt_suzukiPsi hlog2 le_rfl)
  have hopen : IsOpen {t : ℝ | 0 < suzukiPsi t} :=
    isOpen_lt continuous_const continuous_suzukiPsi
  have hnhds : {t : ℝ | 0 < suzukiPsi t} ∈ 𝓝 (Real.log 2) :=
    hopen.mem_nhds hboundary
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε, hball⟩
  refine ⟨Real.log 2 + ε, by linarith, ?_⟩
  intro t ht htupper
  rcases le_total t (Real.log 2) with hle | hge
  · exact (suzukiFirstGapLower_pos ht hle).trans
      (suzukiFirstGapLower_lt_suzukiPsi ht hle)
  · apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith

end RHTower
