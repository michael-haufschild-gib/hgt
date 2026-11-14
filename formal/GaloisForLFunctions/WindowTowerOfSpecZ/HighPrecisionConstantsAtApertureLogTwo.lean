import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper
import GaloisForLFunctions.ArithmeticCriticalityTheory.CurvedGaugeArchimedeanBounds
import GaloisForLFunctions.RHTower.WeilLevyPoleGaussModeCancellation
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.LiouvilleOddWindowRefutationAndSelectiveFullPositivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Ring.GeomSum

/-!
# High-precision arithmetic constants and Legendre bounds at aperture `log 2`

At aperture `A = log 2`, the Weil quadratic form couples the archimedean Gamma
counterterm and Lévy jump tail `archLevyAntideriv (2 * log 2) = log 3 / 2 + arctan (1 / 2)`
to the prime-two and prime-three contacts. Certifying the even ground-energy floor
requires rational enclosures of `log 2`, `log 3`, `√2`, `√3`, `π`, `log π`,
Euler's constant `γ`, and `archLevyAntideriv (2 * log 2)` to `10⁻¹⁸`–`10⁻²⁶`
precision, together with shifted Taylor lower bounds for the exterior logarithmic
potential `log 2 - log (1 - x²) / 2` and uniform bounds on Legendre polynomials
and their first derivatives on `[-1, 1]`.
-/

noncomputable section
open Real Set Filter Topology Finset
open _root_.RHTower.WeilLevyPoleGauss
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open SelectivePositivityAndThresholdLaws

/-! ### Rational enclosures of the aperture constants -/

def logTwoLo : ℝ := 17328679513998632735430803 / 25000000000000000000000000
def logTwoHi : ℝ := 69314718055994530941723213 / 100000000000000000000000000

def logThreeLo : ℝ := 109861228866810969139524523 / 100000000000000000000000000
def logThreeHi : ℝ := 27465307216702742284881131 / 25000000000000000000000000

def sqrtTwoLo : ℝ := 17677669529663688110021109 / 12500000000000000000000000
def sqrtTwoHi : ℝ := 141421356237309504880168873 / 100000000000000000000000000

def sqrtThreeLo : ℝ := 86602540378443864676372317 / 50000000000000000000000000
def sqrtThreeHi : ℝ := 34641016151377545870548927 / 20000000000000000000000000

def piLo : ℝ := 157079632679489661923 / 50000000000000000000
def piHi : ℝ := 314159265358979323847 / 100000000000000000000

def logPiLo : ℝ := 57236494292470008707 / 50000000000000000000
def logPiHi : ℝ := 22894597716988003483 / 20000000000000000000

def eulerLo : ℝ := 28860783245076643 / 50000000000000000
def eulerHi : ℝ := 288607832450766431 / 500000000000000000

def archLevyTwoLogTwoLo : ℝ := 101295375333486096191 / 100000000000000000000
def archLevyTwoLogTwoHi : ℝ := 1582740239585720253 / 1562500000000000000

def gammaBracketZeroLo : ℝ := -335761463701604099 / 62500000000000000
def gammaBracketZeroHi : ℝ := -5372183419225665581 / 1000000000000000000

def primeThreeRatioLo : ℝ := 15849625007211561814537389 / 10000000000000000000000000
def primeThreeRatioHi : ℝ := 1584962500721156181453739 / 1000000000000000000000000

def primeThreeShiftLo : ℝ := 5849625007211561814537389 / 10000000000000000000000000
def primeThreeShiftHi : ℝ := 584962500721156181453739 / 1000000000000000000000000

def primeTwoWeightLo : ℝ := 1225322679335683989642377 / 2500000000000000000000000
def primeTwoWeightHi : ℝ := 4901290717342735958569509 / 10000000000000000000000000

def primeThreeWeightLo : ℝ := 6342841005975639771863877 / 10000000000000000000000000
def primeThreeWeightHi : ℝ := 3171420502987819885931939 / 5000000000000000000000000

/-! ### Monotone derivative helper and hyperbolic artanh enclosures -/

private theorem nonneg_of_hasDerivAt_nonneg (f f' : ℝ → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hf0 : f 0 = 0) (hd : ∀ x ∈ Icc 0 b, HasDerivAt f (f' x) x)
    (hnn : ∀ x ∈ Icc 0 b, 0 ≤ f' x) : 0 ≤ f b := by
  have hc : ContinuousOn f (Icc 0 b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 b) hc
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hnn x (interior_subset hx))
  simpa only [hf0] using hm ⟨le_rfl, hb⟩ ⟨hb, le_rfl⟩ hb

/-- Partial sum `2 ∑_{k < N} t^{2k+1} / (2k + 1)` approximating `log ((1 + t) / (1 - t))`. -/
def artanhPartialSum (N : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, (2 / (2 * (k : ℝ) + 1)) * t ^ (2 * k + 1)

private theorem hasDerivAt_artanhPartialSum (N : ℕ) (x : ℝ) :
    HasDerivAt (artanhPartialSum N) (∑ k ∈ Finset.range N, 2 * x ^ (2 * k)) x := by
  unfold artanhPartialSum
  have hd : ∀ k ∈ Finset.range N,
      HasDerivAt (fun y : ℝ => (2 / (2 * (k : ℝ) + 1)) * y ^ (2 * k + 1))
        (2 * x ^ (2 * k)) x := by
    intro k _
    have h1 := (hasDerivAt_pow (2 * k + 1) x).const_mul (2 / (2 * (k : ℝ) + 1))
    refine h1.congr_deriv ?_
    have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp [hk]
  simpa only [sum_fn] using HasDerivAt.sum hd

private theorem geom_even_remainder (N : ℕ) {x : ℝ} (hx : 1 - x ^ 2 ≠ 0) :
    2 / (1 - x ^ 2) - (∑ k ∈ Finset.range N, 2 * x ^ (2 * k)) =
      2 * x ^ (2 * N) / (1 - x ^ 2) := by
  have hg := geom_sum_mul_neg (x ^ 2) N
  have hsum : (∑ k ∈ Finset.range N, 2 * x ^ (2 * k)) =
      2 * ∑ k ∈ Finset.range N, (x ^ 2) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← pow_mul]
  rw [hsum, sub_eq_iff_eq_add]
  apply (div_eq_iff hx).mpr
  calc
    (2 : ℝ) = 2 * ((∑ k ∈ Finset.range N, (x ^ 2) ^ k) * (1 - x ^ 2) + (x ^ 2) ^ N) := by
      rw [hg]; ring
    _ = (2 * x ^ (2 * N) / (1 - x ^ 2) + 2 * ∑ k ∈ Finset.range N, (x ^ 2) ^ k) * (1 - x ^ 2) := by
      rw [← pow_mul, add_mul, div_mul_cancel₀ _ hx]; ring

/-- Truncated series lower and upper bounds for `log ((1 + t) / (1 - t))` on `[0, 1)`. -/
theorem log_one_add_div_one_sub_bounds (N : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    artanhPartialSum N t ≤ Real.log ((1 + t) / (1 - t)) ∧
      Real.log ((1 + t) / (1 - t)) ≤
        artanhPartialSum N t + (2 / ((2 * (N : ℝ) + 1) * (1 - t ^ 2))) * t ^ (2 * N + 1) := by
  have ht2 : 0 < 1 - t ^ 2 := by nlinarith
  have hd_log : ∀ x ∈ Icc 0 t,
      HasDerivAt (fun y => Real.log (1 + y) - Real.log (1 - y)) (2 / (1 - x ^ 2)) x := by
    intro x hx
    have hx1 : 0 < 1 + x := by linarith [hx.1]
    have hx2 : 0 < 1 - x := by linarith [hx.2, ht1]
    have h1 := ((hasDerivAt_id' x).const_add 1).log hx1.ne'
    have h2 := ((hasDerivAt_id' x).const_sub 1).log hx2.ne'
    refine (h1.sub h2).congr_deriv ?_
    have hne : 1 - x ^ 2 ≠ 0 := by nlinarith [hx1, hx2]
    field_simp [hx1.ne', hx2.ne', hne]
    ring
  have hval : Real.log (1 + t) - Real.log (1 - t) = Real.log ((1 + t) / (1 - t)) :=
    (Real.log_div (by linarith) (by linarith)).symm
  have h_lo : 0 ≤ (Real.log (1 + t) - Real.log (1 - t)) - artanhPartialSum N t := by
    refine nonneg_of_hasDerivAt_nonneg
      (fun y => (Real.log (1 + y) - Real.log (1 - y)) - artanhPartialSum N y)
      (fun x => 2 / (1 - x ^ 2) - ∑ k ∈ Finset.range N, 2 * x ^ (2 * k)) ht0 ?_ ?_ ?_
    · simp [artanhPartialSum, zero_pow (Nat.succ_ne_zero _)]
    · intro x hx
      exact (hd_log x hx).sub (hasDerivAt_artanhPartialSum N x)
    · intro x hx
      have hx2 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, ht1]
      rw [geom_even_remainder N hx2.ne']
      have hxn : 0 ≤ x ^ (2 * N) := pow_nonneg hx.1 _
      positivity
  have h_hi : 0 ≤ (artanhPartialSum N t +
      (2 / ((2 * (N : ℝ) + 1) * (1 - t ^ 2))) * t ^ (2 * N + 1)) -
      (Real.log (1 + t) - Real.log (1 - t)) := by
    refine nonneg_of_hasDerivAt_nonneg
      (fun y => (artanhPartialSum N y +
        (2 / ((2 * (N : ℝ) + 1) * (1 - t ^ 2))) * y ^ (2 * N + 1)) -
        (Real.log (1 + y) - Real.log (1 - y)))
      (fun x => ((∑ k ∈ Finset.range N, 2 * x ^ (2 * k)) +
        (2 / (1 - t ^ 2)) * x ^ (2 * N)) - 2 / (1 - x ^ 2)) ht0 ?_ ?_ ?_
    · simp [artanhPartialSum, zero_pow (Nat.succ_ne_zero _)]
    · intro x hx
      have hrem_d : HasDerivAt
          (fun y : ℝ => (2 / ((2 * (N : ℝ) + 1) * (1 - t ^ 2))) * y ^ (2 * N + 1))
          ((2 / (1 - t ^ 2)) * x ^ (2 * N)) x := by
        have h1 := (hasDerivAt_pow (2 * N + 1) x).const_mul
          (2 / ((2 * (N : ℝ) + 1) * (1 - t ^ 2)))
        refine h1.congr_deriv ?_
        have hN : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
        push_cast
        field_simp [hN, ht2.ne']
      exact ((hasDerivAt_artanhPartialSum N x).add hrem_d).sub (hd_log x hx)
    · intro x hx
      have hx2 : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, ht1]
      have hdiff : (∑ k ∈ Finset.range N, 2 * x ^ (2 * k)) +
          (2 / (1 - t ^ 2)) * x ^ (2 * N) - 2 / (1 - x ^ 2) =
          2 * x ^ (2 * N) * (1 / (1 - t ^ 2) - 1 / (1 - x ^ 2)) := by
        have hg := geom_even_remainder N hx2.ne'
        linarith [show 2 * x ^ (2 * N) * (1 / (1 - t ^ 2) - 1 / (1 - x ^ 2)) =
          (2 / (1 - t ^ 2)) * x ^ (2 * N) - 2 * x ^ (2 * N) / (1 - x ^ 2) by ring]
      rw [hdiff]
      have hle : 1 - t ^ 2 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
      have hinv : 0 ≤ 1 / (1 - t ^ 2) - 1 / (1 - x ^ 2) :=
        sub_nonneg.mpr (one_div_le_one_div_of_le ht2 hle)
      have hxn : 0 ≤ 2 * x ^ (2 * N) := by have := hx.1; positivity
      exact mul_nonneg hxn hinv
  rw [hval] at h_lo h_hi
  exact ⟨by linarith, by linarith⟩

/-! ### Enclosures for `log 2`, `log 3`, `√2`, `√3`, `π`, and `log π` -/

private theorem artanh_one_fifth_bounds :
    (1065029249461195969396896023675784712 / 2626685325478320010006427764892578125 : ℝ) ≤ Real.log (3 / 2) ∧ Real.log (3 / 2) ≤ (157624328920257003470740611804856872571 / 388749428170791361480951309204101562500 : ℝ) := by
  have h := log_one_add_div_one_sub_bounds 18 (t := (1 / 5 : ℝ)) (by norm_num) (by norm_num)
  rw [show ((1 : ℝ) + 1 / 5) / (1 - 1 / 5) = 3 / 2 by norm_num] at h
  have hlo : artanhPartialSum 18 (1 / 5 : ℝ) = (1065029249461195969396896023675784712 / 2626685325478320010006427764892578125 : ℝ) := by
    norm_num [artanhPartialSum, Finset.sum_range_succ]
  have hhi : artanhPartialSum 18 (1 / 5 : ℝ) +
      (2 / ((2 * (18 : ℝ) + 1) * (1 - (1 / 5 : ℝ) ^ 2))) * (1 / 5 : ℝ) ^ (2 * 18 + 1) =
      (157624328920257003470740611804856872571 / 388749428170791361480951309204101562500 : ℝ) := by
    rw [hlo]; norm_num
  exact ⟨hlo ▸ h.1, hhi ▸ h.2⟩

private theorem artanh_one_seventh_bounds :
    (19263008916537257381220349789142042 / 66959365080929663646946656377037675 : ℝ) ≤ Real.log (4 / 3) ∧ Real.log (4 / 3) ≤ (4777226211301239830542646754639040591 / 16605922540070556584442770781505343400 : ℝ) := by
  have h := log_one_add_div_one_sub_bounds 15 (t := (1 / 7 : ℝ)) (by norm_num) (by norm_num)
  rw [show ((1 : ℝ) + 1 / 7) / (1 - 1 / 7) = 4 / 3 by norm_num] at h
  have hlo : artanhPartialSum 15 (1 / 7 : ℝ) = (19263008916537257381220349789142042 / 66959365080929663646946656377037675 : ℝ) := by
    norm_num [artanhPartialSum, Finset.sum_range_succ]
  have hhi : artanhPartialSum 15 (1 / 7 : ℝ) +
      (2 / ((2 * (15 : ℝ) + 1) * (1 - (1 / 7 : ℝ) ^ 2))) * (1 / 7 : ℝ) ^ (2 * 15 + 1) =
      (4777226211301239830542646754639040591 / 16605922540070556584442770781505343400 : ℝ) := by
    rw [hlo]; norm_num
  exact ⟨hlo ▸ h.1, hhi ▸ h.2⟩

theorem log_two_bounds_d26 : logTwoLo ≤ Real.log 2 ∧ Real.log 2 ≤ logTwoHi := by
  obtain ⟨hA1, hA2⟩ := artanh_one_fifth_bounds
  obtain ⟨hB1, hB2⟩ := artanh_one_seventh_bounds
  have h2 : Real.log 2 = Real.log (3 / 2) + Real.log (4 / 3) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have c1 : logTwoLo ≤ (1065029249461195969396896023675784712 / 2626685325478320010006427764892578125 : ℝ) + (19263008916537257381220349789142042 / 66959365080929663646946656377037675 : ℝ) := by norm_num [logTwoLo]
  have c2 : (157624328920257003470740611804856872571 / 388749428170791361480951309204101562500 : ℝ) + (4777226211301239830542646754639040591 / 16605922540070556584442770781505343400 : ℝ) ≤ logTwoHi := by norm_num [logTwoHi]
  rw [h2]
  exact ⟨c1.trans (add_le_add hA1 hB1), (add_le_add hA2 hB2).trans c2⟩

theorem log_three_bounds_d26 : logThreeLo ≤ Real.log 3 ∧ Real.log 3 ≤ logThreeHi := by
  obtain ⟨hA1, hA2⟩ := artanh_one_fifth_bounds
  obtain ⟨hB1, hB2⟩ := artanh_one_seventh_bounds
  have h3 : Real.log 3 = 2 * Real.log (3 / 2) + Real.log (4 / 3) := by
    have hsq : 2 * Real.log (3 / 2) = Real.log (9 / 4) := by
      rw [show (9 / 4 : ℝ) = (3 / 2) ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
    rw [hsq, ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have c1 : logThreeLo ≤ 2 * (1065029249461195969396896023675784712 / 2626685325478320010006427764892578125 : ℝ) + (19263008916537257381220349789142042 / 66959365080929663646946656377037675 : ℝ) := by norm_num [logThreeLo]
  have c2 : 2 * (157624328920257003470740611804856872571 / 388749428170791361480951309204101562500 : ℝ) + (4777226211301239830542646754639040591 / 16605922540070556584442770781505343400 : ℝ) ≤ logThreeHi := by norm_num [logThreeHi]
  rw [h3]
  exact ⟨c1.trans (add_le_add (mul_le_mul_of_nonneg_left hA1 (by norm_num)) hB1),
    (add_le_add (mul_le_mul_of_nonneg_left hA2 (by norm_num)) hB2).trans c2⟩

theorem sqrt_two_bounds_d26 : sqrtTwoLo ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ sqrtTwoHi := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h0 := Real.sqrt_nonneg 2
  have c1 : sqrtTwoLo ^ 2 ≤ (2 : ℝ) := by norm_num [sqrtTwoLo]
  have c2 : (2 : ℝ) ≤ sqrtTwoHi ^ 2 := by norm_num [sqrtTwoHi]
  have hlo0 : (0 : ℝ) ≤ sqrtTwoLo := by norm_num [sqrtTwoLo]
  have hhi0 : (0 : ℝ) ≤ sqrtTwoHi := by norm_num [sqrtTwoHi]
  exact ⟨by nlinarith, by nlinarith⟩

theorem sqrt_three_bounds_d26 : sqrtThreeLo ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ sqrtThreeHi := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h0 := Real.sqrt_nonneg 3
  have c1 : sqrtThreeLo ^ 2 ≤ (3 : ℝ) := by norm_num [sqrtThreeLo]
  have c2 : (3 : ℝ) ≤ sqrtThreeHi ^ 2 := by norm_num [sqrtThreeHi]
  have hlo0 : (0 : ℝ) ≤ sqrtThreeLo := by norm_num [sqrtThreeLo]
  have hhi0 : (0 : ℝ) ≤ sqrtThreeHi := by norm_num [sqrtThreeHi]
  exact ⟨by nlinarith, by nlinarith⟩

theorem pi_bounds_d20 : piLo ≤ Real.pi ∧ Real.pi ≤ piHi := by
  have h1 := Real.pi_gt_d20.le
  have h2 := Real.pi_lt_d20.le
  exact ⟨le_trans (by norm_num [piLo]) h1, le_trans h2 (by norm_num [piHi])⟩

theorem log_pi_bounds_d20 : logPiLo ≤ Real.log Real.pi ∧ Real.log Real.pi ≤ logPiHi := by
  obtain ⟨hp1, hp2⟩ := pi_bounds_d20
  obtain ⟨hl3_lo, hl3_hi⟩ := log_three_bounds_d26
  let u_lo : ℝ := (piLo - 3) / (piLo + 3)
  let u_hi : ℝ := (piHi - 3) / (piHi + 3)
  have hu_lo_b := log_one_add_div_one_sub_bounds 8 (t := u_lo)
    (by norm_num [u_lo, piLo]) (by norm_num [u_lo, piLo])
  have hu_hi_b := log_one_add_div_one_sub_bounds 8 (t := u_hi)
    (by norm_num [u_hi, piHi]) (by norm_num [u_hi, piHi])
  have hrat_lo : (1 + u_lo) / (1 - u_lo) = piLo / 3 := by norm_num [u_lo, piLo]
  have hrat_hi : (1 + u_hi) / (1 - u_hi) = piHi / 3 := by norm_num [u_hi, piHi]
  rw [hrat_lo] at hu_lo_b
  rw [hrat_hi] at hu_hi_b
  have hm_lo : Real.log (piLo / 3) ≤ Real.log (Real.pi / 3) :=
    Real.log_le_log (by norm_num [piLo]) (div_le_div_of_nonneg_right hp1 (by norm_num))
  have hm_hi : Real.log (Real.pi / 3) ≤ Real.log (piHi / 3) :=
    Real.log_le_log (div_pos Real.pi_pos (by norm_num)) (div_le_div_of_nonneg_right hp2 (by norm_num))
  have hsplit : Real.log Real.pi = Real.log 3 + Real.log (Real.pi / 3) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1; ring
  have c_lo : logPiLo ≤ logThreeLo + artanhPartialSum 8 u_lo := by
    norm_num [logPiLo, logThreeLo, artanhPartialSum, Finset.sum_range_succ, u_lo, piLo]
  have c_hi : logThreeHi + (artanhPartialSum 8 u_hi +
      (2 / ((2 * (8 : ℕ) + 1) * (1 - u_hi ^ 2))) * u_hi ^ (2 * 8 + 1)) ≤ logPiHi := by
    norm_num [logPiHi, logThreeHi, artanhPartialSum, Finset.sum_range_succ, u_hi, piHi]
  rw [hsplit]
  exact ⟨c_lo.trans (add_le_add hl3_lo (hu_lo_b.1.trans hm_lo)),
    (add_le_add hl3_hi (hm_hi.trans hu_hi_b.2)).trans c_hi⟩

/-! ### Order-twelve Euler–Maclaurin enclosure for `eulerMascheroniConstant` -/

private def eulerUpperTail (x : ℝ) : ℝ :=
  -1 / (2 * x) + 1 / (12 * x ^ 2) - 1 / (120 * x ^ 4) +
    1 / (252 * x ^ 6) - 1 / (240 * x ^ 8) + 1 / (132 * x ^ 10)

private def eulerLowerTail (x : ℝ) : ℝ :=
  eulerUpperTail x - 691 / (32760 * x ^ 12)

private def eulerUpperSeq12 (n : ℕ) : ℝ :=
  Real.eulerMascheroniSeq' (n + 1) + eulerUpperTail ((n : ℝ) + 1)

private def eulerLowerSeq12 (n : ℕ) : ℝ :=
  Real.eulerMascheroniSeq' (n + 1) + eulerLowerTail ((n : ℝ) + 1)

private theorem eulerUpperTail_mul (x : ℝ) (hx : x ≠ 0) :
    x ^ 10 * eulerUpperTail x =
      -x ^ 9 / 2 + x ^ 8 / 12 - x ^ 6 / 120 + x ^ 4 / 252 - x ^ 2 / 240 + 1 / 132 := by
  unfold eulerUpperTail
  field_simp [hx]

private theorem eulerLowerTail_mul (x : ℝ) (hx : x ≠ 0) :
    x ^ 12 * eulerLowerTail x =
      x ^ 2 * (-x ^ 9 / 2 + x ^ 8 / 12 - x ^ 6 / 120 + x ^ 4 / 252 - x ^ 2 / 240 + 1 / 132) -
        691 / 32760 := by
  unfold eulerLowerTail
  have hu := eulerUpperTail_mul x hx
  have h12 : x ^ 12 * eulerUpperTail x = x ^ 2 * (x ^ 10 * eulerUpperTail x) := by ring
  rw [mul_sub, h12, hu]
  field_simp [hx]

private theorem artanhPartialSum_seven_mul (x : ℝ) (h2x : 2 * x + 1 ≠ 0) :
    (2 * x + 1) ^ 13 * artanhPartialSum 7 (1 / (2 * x + 1)) =
      2 * (2 * x + 1) ^ 12 + (2 / 3) * (2 * x + 1) ^ 10 + (2 / 5) * (2 * x + 1) ^ 8 +
        (2 / 7) * (2 * x + 1) ^ 6 + (2 / 9) * (2 * x + 1) ^ 4 + (2 / 11) * (2 * x + 1) ^ 2 +
        2 / 13 := by
  norm_num [artanhPartialSum, Finset.sum_range_succ]
  field_simp [h2x]

private theorem eulerUpperSeq12_step_pos (y : ℝ) (hy : 0 ≤ y) :
    let x := y + 1
    1 / (x + 1) + eulerUpperTail (x + 1) - eulerUpperTail x <
      artanhPartialSum 7 (1 / (2 * x + 1)) := by
  intro x
  have hx0 : 0 < x := by dsimp [x]; linarith
  have hx1 : 0 < x + 1 := by linarith
  have h2x : 0 < 2 * x + 1 := by linarith
  have hden : 0 < x ^ 10 * (x + 1) ^ 10 * (2 * x + 1) ^ 13 := by positivity
  suffices hmul : 0 < x ^ 10 * (x + 1) ^ 10 * (2 * x + 1) ^ 13 *
      (artanhPartialSum 7 (1 / (2 * x + 1)) -
        (1 / (x + 1) + eulerUpperTail (x + 1) - eulerUpperTail x)) by
    nlinarith [hmul, hden]
  have hp := artanhPartialSum_seven_mul x h2x.ne'
  have hu0 := eulerUpperTail_mul x hx0.ne'
  have hu1 := eulerUpperTail_mul (x + 1) hx1.ne'
  have h1 : x ^ 10 * (x + 1) ^ 10 * (2 * x + 1) ^ 13 * (1 / (x + 1)) =
      x ^ 10 * (x + 1) ^ 9 * (2 * x + 1) ^ 13 := by field_simp [hx1.ne']
  have halg : x ^ 10 * (x + 1) ^ 10 * (2 * x + 1) ^ 13 *
      (artanhPartialSum 7 (1 / (2 * x + 1)) -
        (1 / (x + 1) + eulerUpperTail (x + 1) - eulerUpperTail x)) =
      x ^ 10 * (x + 1) ^ 10 * ((2 * x + 1) ^ 13 * artanhPartialSum 7 (1 / (2 * x + 1))) -
      (x ^ 10 * (x + 1) ^ 10 * (2 * x + 1) ^ 13 * (1 / (x + 1)) +
        x ^ 10 * (2 * x + 1) ^ 13 * ((x + 1) ^ 10 * eulerUpperTail (x + 1)) -
        (x + 1) ^ 10 * (2 * x + 1) ^ 13 * (x ^ 10 * eulerUpperTail x)) := by ring
  rw [halg, hp, h1, hu1, hu0]
  have hpoly : x ^ 10 * (x + 1) ^ 10 *
      (2 * (2 * x + 1) ^ 12 + (2 / 3) * (2 * x + 1) ^ 10 + (2 / 5) * (2 * x + 1) ^ 8 +
        (2 / 7) * (2 * x + 1) ^ 6 + (2 / 9) * (2 * x + 1) ^ 4 + (2 / 11) * (2 * x + 1) ^ 2 +
        2 / 13) -
      (x ^ 10 * (x + 1) ^ 9 * (2 * x + 1) ^ 13 +
        x ^ 10 * (2 * x + 1) ^ 13 *
          (-(x + 1) ^ 9 / 2 + (x + 1) ^ 8 / 12 - (x + 1) ^ 6 / 120 + (x + 1) ^ 4 / 252 -
            (x + 1) ^ 2 / 240 + 1 / 132) -
        (x + 1) ^ 10 * (2 * x + 1) ^ 13 *
          (-x ^ 9 / 2 + x ^ 8 / 12 - x ^ 6 / 120 + x ^ 4 / 252 - x ^ 2 / 240 + 1 / 132)) =
      (84307561801 / 10010 : ℝ) + (2205420730857 / 20020 : ℝ) * y + (10970944134925 / 16016 : ℝ) * y ^ 2 +
      (161714396369989 / 60060 : ℝ) * y ^ 3 + (5407956313979501 / 720720 : ℝ) * y ^ 4 + (4412551312777 / 280 : ℝ) * y ^ 5 +
      (1165850180811697 / 45045 : ℝ) * y ^ 6 + (170361703988451 / 5005 : ℝ) * y ^ 7 + (728873495272431 / 20020 : ℝ) * y ^ 8 +
      (160077458065887 / 5005 : ℝ) * y ^ 9 + (71467434426321 / 3080 : ℝ) * y ^ 10 + (19915236674199 / 1430 : ℝ) * y ^ 11 +
      (276402164547237 / 40040 : ℝ) * y ^ 12 + (5115165483301 / 1820 : ℝ) * y ^ 13 + (5081687421943 / 5460 : ℝ) * y ^ 14 +
      (25917246112 / 105 : ℝ) * y ^ 15 + (167721593425 / 3276 : ℝ) * y ^ 16 + (208113231 / 26 : ℝ) * y ^ 17 +
      (1453572451 / 1638 : ℝ) * y ^ 18 + (5660672 / 91 : ℝ) * y ^ 19 + (2830336 / 1365 : ℝ) * y ^ 20 := by
    dsimp [x]
    ring
  rw [hpoly]
  positivity

private theorem eulerLowerSeq12_step_pos (y : ℝ) (hy : 0 ≤ y) :
    let x := y + 1
    let t := 1 / (2 * x + 1)
    artanhPartialSum 7 t + (2 / (15 * (1 - t ^ 2))) * t ^ 15 <
      1 / (x + 1) + eulerLowerTail (x + 1) - eulerLowerTail x := by
  intro x t
  have hx0 : 0 < x := by dsimp [x]; linarith
  have hx1 : 0 < x + 1 := by linarith
  have h2x : 0 < 2 * x + 1 := by linarith
  have hden : 0 < 4 * x ^ 12 * (x + 1) ^ 12 * (2 * x + 1) ^ 13 := by positivity
  suffices hmul : 0 < 4 * x ^ 12 * (x + 1) ^ 12 * (2 * x + 1) ^ 13 *
      ((1 / (x + 1) + eulerLowerTail (x + 1) - eulerLowerTail x) -
        (artanhPartialSum 7 t + (2 / (15 * (1 - t ^ 2))) * t ^ 15)) by
    nlinarith [hmul, hden]
  have hp := artanhPartialSum_seven_mul x h2x.ne'
  have hl0 := eulerLowerTail_mul x hx0.ne'
  have hl1 := eulerLowerTail_mul (x + 1) hx1.ne'
  have h1 : x ^ 12 * (x + 1) ^ 12 * (2 * x + 1) ^ 13 * (1 / (x + 1)) =
      x ^ 12 * (x + 1) ^ 11 * (2 * x + 1) ^ 13 := by field_simp [hx1.ne']
  have hrem : 4 * x ^ 12 * (x + 1) ^ 12 * (2 * x + 1) ^ 13 *
      ((2 / (15 * (1 - t ^ 2))) * t ^ 15) = (2 / 15) * x ^ 11 * (x + 1) ^ 11 := by
    dsimp [t]
    have h1mt : 1 - (1 / (2 * x + 1)) ^ 2 = 4 * x * (x + 1) / (2 * x + 1) ^ 2 := by
      field_simp [h2x.ne']; ring
    rw [h1mt]
    field_simp [hx0.ne', hx1.ne', h2x.ne']
  have halg : 4 * x ^ 12 * (x + 1) ^ 12 * (2 * x + 1) ^ 13 *
      ((1 / (x + 1) + eulerLowerTail (x + 1) - eulerLowerTail x) -
        (artanhPartialSum 7 t + (2 / (15 * (1 - t ^ 2))) * t ^ 15)) =
      4 * (x ^ 12 * (x + 1) ^ 12 * (2 * x + 1) ^ 13 * (1 / (x + 1)) +
        x ^ 12 * (2 * x + 1) ^ 13 * ((x + 1) ^ 12 * eulerLowerTail (x + 1)) -
        (x + 1) ^ 12 * (2 * x + 1) ^ 13 * (x ^ 12 * eulerLowerTail x)) -
      (4 * x ^ 12 * (x + 1) ^ 12 * ((2 * x + 1) ^ 13 * artanhPartialSum 7 t) +
        4 * x ^ 12 * (x + 1) ^ 12 * (2 * x + 1) ^ 13 * ((2 / (15 * (1 - t ^ 2))) * t ^ 15)) := by
    ring
  rw [halg, h1, hl1, hl0, hp, hrem]
  have hpoly : 4 * (x ^ 12 * (x + 1) ^ 11 * (2 * x + 1) ^ 13 +
        x ^ 12 * (2 * x + 1) ^ 13 *
          ((x + 1) ^ 2 * (-(x + 1) ^ 9 / 2 + (x + 1) ^ 8 / 12 - (x + 1) ^ 6 / 120 +
            (x + 1) ^ 4 / 252 - (x + 1) ^ 2 / 240 + 1 / 132) - 691 / 32760) -
        (x + 1) ^ 12 * (2 * x + 1) ^ 13 *
          (x ^ 2 * (-x ^ 9 / 2 + x ^ 8 / 12 - x ^ 6 / 120 + x ^ 4 / 252 -
            x ^ 2 / 240 + 1 / 132) - 691 / 32760)) -
      (4 * x ^ 12 * (x + 1) ^ 12 *
        (2 * (2 * x + 1) ^ 12 + (2 / 3) * (2 * x + 1) ^ 10 + (2 / 5) * (2 * x + 1) ^ 8 +
          (2 / 7) * (2 * x + 1) ^ 6 + (2 / 9) * (2 * x + 1) ^ 4 + (2 / 11) * (2 * x + 1) ^ 2 +
          2 / 13) + (2 / 15) * x ^ 11 * (x + 1) ^ 11) =
      (2498982377251 / 6006 : ℝ) + (29586098800189 / 5005 : ℝ) * y + (17215266255854 / 429 : ℝ) * y ^ 2 +
      (2600116205890844 / 15015 : ℝ) * y ^ 3 + (8732006411718071 / 16380 : ℝ) * y ^ 4 + (2493221164863801 / 2002 : ℝ) * y ^ 5 +
      (481482647328191 / 210 : ℝ) * y ^ 6 + (310300247159332 / 91 : ℝ) * y ^ 7 + (22745730735204101 / 5460 : ℝ) * y ^ 8 +
      (11543709273298183 / 2730 : ℝ) * y ^ 9 + (14709945404434636 / 4095 : ℝ) * y ^ 10 + (2567247876386766 / 1001 : ℝ) * y ^ 11 +
      (15425503868268353 / 10010 : ℝ) * y ^ 12 + (42802708991553 / 55 : ℝ) * y ^ 13 + (126657381787547 / 385 : ℝ) * y ^ 14 +
      (133478087817812 / 1155 : ℝ) * y ^ 15 + (33023654243483 / 990 : ℝ) * y ^ 16 + (272319753249 / 35 : ℝ) * y ^ 17 +
      (50077175402 / 35 : ℝ) * y ^ 18 + (199753246 : ℝ) * y ^ 19 + (298573583 / 15 : ℝ) * y ^ 20 +
      (1261568 : ℝ) * y ^ 21 + (114688 / 3 : ℝ) * y ^ 22 := by
    dsimp [x]
    ring
  rw [hpoly]
  positivity

private theorem strictAnti_eulerUpperSeq12 : StrictAnti eulerUpperSeq12 := by
  refine strictAnti_nat_of_succ_lt fun n => ?_
  let x : ℝ := (n : ℝ) + 1
  have hx0 : 0 < x := by positivity
  have hx1 : 0 < x + 1 := by positivity
  have ht_b := log_one_add_div_one_sub_bounds 7 (t := 1 / (2 * x + 1))
    (by positivity) (by rw [div_lt_one (by positivity)]; linarith)
  have hrat : (1 + 1 / (2 * x + 1)) / (1 - 1 / (2 * x + 1)) = (x + 1) / x := by
    field_simp [hx0.ne', (show 2 * x + 1 ≠ 0 by positivity)]; ring
  rw [hrat, Real.log_div hx1.ne' hx0.ne'] at ht_b
  have hstep := eulerUpperSeq12_step_pos (n : ℝ) (Nat.cast_nonneg n)
  unfold eulerUpperSeq12 Real.eulerMascheroniSeq'
  simp only [Nat.succ_ne_zero, if_false]
  rw [harmonic_succ (n + 1)]
  push_cast
  dsimp [x] at ht_b hstep
  rw [inv_eq_one_div]
  linarith [ht_b.1, hstep]

private theorem strictMono_eulerLowerSeq12 : StrictMono eulerLowerSeq12 := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  let x : ℝ := (n : ℝ) + 1
  have hx0 : 0 < x := by positivity
  have hx1 : 0 < x + 1 := by positivity
  have ht_b := log_one_add_div_one_sub_bounds 7 (t := 1 / (2 * x + 1))
    (by positivity) (by rw [div_lt_one (by positivity)]; linarith)
  have hrat : (1 + 1 / (2 * x + 1)) / (1 - 1 / (2 * x + 1)) = (x + 1) / x := by
    field_simp [hx0.ne', (show 2 * x + 1 ≠ 0 by positivity)]; ring
  rw [hrat, Real.log_div hx1.ne' hx0.ne'] at ht_b
  have hstep := eulerLowerSeq12_step_pos (n : ℝ) (Nat.cast_nonneg n)
  norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat] at ht_b
  unfold eulerLowerSeq12 Real.eulerMascheroniSeq'
  simp only [Nat.succ_ne_zero, if_false]
  rw [harmonic_succ (n + 1)]
  push_cast
  dsimp only [x] at ht_b hstep
  rw [inv_eq_one_div]
  linarith [ht_b.2, hstep]

private theorem tendsto_inv_pow_add_one (k : ℕ) (hk : 1 ≤ k) (c : ℝ) :
    Tendsto (fun n : ℕ => c / ((n : ℝ) + 1) ^ k) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    ((tendsto_pow_atTop (by omega : k ≠ 0)).comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))

private theorem tendsto_eulerUpperTail :
    Tendsto (fun n : ℕ => eulerUpperTail ((n : ℝ) + 1)) atTop (𝓝 0) := by
  unfold eulerUpperTail
  have h1 : Tendsto (fun n : ℕ => (-1 / 2 : ℝ) / ((n : ℝ) + 1) ^ 1) atTop (𝓝 0) :=
    tendsto_inv_pow_add_one 1 le_rfl _
  have h2 := tendsto_inv_pow_add_one 2 (by norm_num) (1 / 12)
  have h4 := tendsto_inv_pow_add_one 4 (by norm_num) (-1 / 120)
  have h6 := tendsto_inv_pow_add_one 6 (by norm_num) (1 / 252)
  have h8 := tendsto_inv_pow_add_one 8 (by norm_num) (-1 / 240)
  have h10 := tendsto_inv_pow_add_one 10 (by norm_num) (1 / 132)
  have hs := (((((h1.add h2).add h4).add h6).add h8).add h10)
  rw [show (0 : ℝ) + 0 + 0 + 0 + 0 + 0 = 0 by norm_num] at hs
  refine hs.congr fun n => ?_
  have hx : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hx]
  ring

theorem eulerMascheroniConstant_bounds_d18 :
    eulerLo ≤ Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant ≤ eulerHi := by
  have hseq := Real.tendsto_eulerMascheroniSeq'.comp (tendsto_add_atTop_nat 1)
  have hlimU : Tendsto eulerUpperSeq12 atTop (𝓝 Real.eulerMascheroniConstant) := by
    unfold eulerUpperSeq12
    simpa only [Function.comp_apply, add_zero] using hseq.add tendsto_eulerUpperTail
  have hlimL : Tendsto eulerLowerSeq12 atTop (𝓝 Real.eulerMascheroniConstant) := by
    have h12 := tendsto_inv_pow_add_one 12 (by norm_num) (-691 / 32760)
    have htL : Tendsto (fun n : ℕ => eulerLowerTail ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have hs := tendsto_eulerUpperTail.add h12
      rw [add_zero] at hs
      refine hs.congr fun n => ?_
      unfold eulerLowerTail
      have hx : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp [hx]
      ring
    unfold eulerLowerSeq12
    simpa only [Function.comp_apply, add_zero] using hseq.add htL
  have h_le_U : Real.eulerMascheroniConstant ≤ eulerUpperSeq12 23 :=
    strictAnti_eulerUpperSeq12.antitone.le_of_tendsto hlimU 23
  have h_ge_L : eulerLowerSeq12 23 ≤ Real.eulerMascheroniConstant :=
    strictMono_eulerLowerSeq12.monotone.ge_of_tendsto hlimL 23
  have hH24 : ((harmonic 24 : ℚ) : ℝ) = (1347822955 / 356948592 : ℝ) := by
    rw [show (24 : ℕ) = 12 + 12 from rfl, _root_.RHTower.harmonic_add_eq_add_sum]
    norm_num [harmonic, Finset.sum_range_succ]
  have hlog24 : Real.log (24 : ℝ) = 3 * Real.log 2 + Real.log 3 := by
    rw [show (24 : ℝ) = 2 ^ (3 : ℕ) * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  obtain ⟨hl2_lo, hl2_hi⟩ := log_two_bounds_d26
  obtain ⟨hl3_lo, hl3_hi⟩ := log_three_bounds_d26
  unfold eulerUpperSeq12 Real.eulerMascheroniSeq' at h_le_U
  unfold eulerLowerSeq12 Real.eulerMascheroniSeq' at h_ge_L
  norm_num only [Nat.reduceAdd, Nat.succ_ne_zero, if_false] at h_le_U h_ge_L
  rw [hH24, hlog24] at h_le_U h_ge_L
  have cL : eulerLo ≤ (1347822955 / 356948592 : ℝ) - (3 * logTwoHi + logThreeHi) + eulerLowerTail 24 := by
    norm_num [eulerLo, logTwoHi, logThreeHi, eulerLowerTail, eulerUpperTail]
  have cU : (1347822955 / 356948592 : ℝ) - (3 * logTwoLo + logThreeLo) + eulerUpperTail 24 ≤ eulerHi := by
    norm_num [eulerHi, logTwoLo, logThreeLo, eulerUpperTail]
  exact ⟨cL.trans (by linarith), (by linarith : Real.eulerMascheroniConstant ≤ _).trans cU⟩

/-! ### Closed form and enclosure of `archLevyAntideriv (2 * log 2)` -/

/-- At diameter `2 * log 2`, the archimedean Lévy tail equals `log 3 / 2 + arctan (1 / 2)`. -/
theorem archLevyAntideriv_two_mul_log_two :
    archLevyAntideriv (2 * Real.log 2) = Real.log 3 / 2 + Real.arctan (1 / 2) := by
  have hpos : 0 < 2 * Real.log 2 := by positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hexp : Real.exp (-(2 * Real.log 2) / 2) = (1 / 2 : ℝ) := by
    rw [show -(2 * Real.log 2) / 2 = -Real.log 2 by ring, Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [archLevyAntideriv_eq_log_div hpos, hexp]
  norm_num
  ring

private def levyQuarticPartialSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 16, (2 / (4 * (n : ℝ) + 1)) * x ^ (4 * n + 1)

private theorem hasDerivAt_levyQuarticPartialSum (x : ℝ) :
    HasDerivAt levyQuarticPartialSum (∑ n ∈ Finset.range 16, 2 * x ^ (4 * n)) x := by
  unfold levyQuarticPartialSum
  have hd : ∀ n ∈ Finset.range 16,
      HasDerivAt (fun y : ℝ => (2 / (4 * (n : ℝ) + 1)) * y ^ (4 * n + 1))
        (2 * x ^ (4 * n)) x := by
    intro n _
    have h1 := (hasDerivAt_pow (4 * n + 1) x).const_mul (2 / (4 * (n : ℝ) + 1))
    refine h1.congr_deriv ?_
    have hn : (4 * (n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp [hn]
  simpa only [sum_fn] using HasDerivAt.sum hd

private theorem geom_quartic_remainder {x : ℝ} (hx : 1 - x ^ 4 ≠ 0) :
    2 / (1 - x ^ 4) - (∑ n ∈ Finset.range 16, 2 * x ^ (4 * n)) =
      2 * x ^ 64 / (1 - x ^ 4) := by
  have hg := geom_sum_mul_neg (x ^ 4) 16
  have hsum : (∑ n ∈ Finset.range 16, 2 * x ^ (4 * n)) =
      2 * ∑ n ∈ Finset.range 16, (x ^ 4) ^ n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← pow_mul]
  rw [hsum, sub_eq_iff_eq_add]
  apply (div_eq_iff hx).mpr
  calc
    (2 : ℝ) = 2 * ((∑ n ∈ Finset.range 16, (x ^ 4) ^ n) * (1 - x ^ 4) + (x ^ 4) ^ 16) := by
      rw [hg]; ring
    _ = (2 * x ^ 64 / (1 - x ^ 4) + 2 * ∑ n ∈ Finset.range 16, (x ^ 4) ^ n) * (1 - x ^ 4) := by
      rw [show ((x ^ 4) ^ 16 : ℝ) = x ^ 64 by ring, add_mul, div_mul_cancel₀ _ hx]; ring

theorem archLevyAntideriv_two_mul_log_two_bounds :
    archLevyTwoLogTwoLo ≤ archLevyAntideriv (2 * Real.log 2) ∧
      archLevyAntideriv (2 * Real.log 2) ≤ archLevyTwoLogTwoHi := by
  rw [archLevyAntideriv_two_mul_log_two]
  let f : ℝ → ℝ := fun x => (Real.log (1 + x) - Real.log (1 - x)) / 2 + Real.arctan x
  have hf_half : f (1 / 2) = Real.log 3 / 2 + Real.arctan (1 / 2) := by
    dsimp [f]
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have hd_f : ∀ x ∈ Icc (0 : ℝ) (1 / 2), HasDerivAt f (2 / (1 - x ^ 4)) x := by
    intro x hx
    have hx1 : 0 < 1 + x := by linarith [hx.1]
    have hx2 : 0 < 1 - x := by linarith [hx.2]
    have h1 := ((hasDerivAt_id' x).const_add 1).log hx1.ne'
    have h2 := ((hasDerivAt_id' x).const_sub 1).log hx2.ne'
    have h3 := Real.hasDerivAt_arctan x
    refine (((h1.sub h2).div_const 2).add h3).congr_deriv ?_
    have hne4 : 1 - x ^ 4 ≠ 0 := by
      have : x ^ 4 ≤ (1 / 2 : ℝ) ^ 4 := pow_le_pow_left₀ hx.1 hx.2 4
      linarith [show ((1 / 2 : ℝ) ^ 4) = 1 / 16 by norm_num]
    have hne2 : 1 + x ^ 2 ≠ 0 := by positivity
    field_simp [hx1.ne', hx2.ne', hne2, hne4]
    ring
  have h_lo : 0 ≤ f (1 / 2) - levyQuarticPartialSum (1 / 2) := by
    refine nonneg_of_hasDerivAt_nonneg
      (fun y => f y - levyQuarticPartialSum y)
      (fun x => 2 / (1 - x ^ 4) - ∑ n ∈ Finset.range 16, 2 * x ^ (4 * n))
      (by norm_num) ?_ ?_ ?_
    · simp [f, levyQuarticPartialSum, zero_pow (Nat.succ_ne_zero _)]
    · intro x hx
      exact (hd_f x hx).sub (hasDerivAt_levyQuarticPartialSum x)
    · intro x hx
      have hx4 : 0 < 1 - x ^ 4 := by
        have : x ^ 4 ≤ (1 / 2 : ℝ) ^ 4 := pow_le_pow_left₀ hx.1 hx.2 4
        linarith [show ((1 / 2 : ℝ) ^ 4) = 1 / 16 by norm_num]
      rw [geom_quartic_remainder hx4.ne']
      have h64 : 0 ≤ x ^ 64 := pow_nonneg hx.1 64
      positivity
  have h_hi : 0 ≤ (levyQuarticPartialSum (1 / 2) + (32 / (15 * 65)) * (1 / 2 : ℝ) ^ 65) -
      f (1 / 2) := by
    refine nonneg_of_hasDerivAt_nonneg
      (fun y => (levyQuarticPartialSum y + (32 / (15 * 65)) * y ^ 65) - f y)
      (fun x => ((∑ n ∈ Finset.range 16, 2 * x ^ (4 * n)) + (32 / 15) * x ^ 64) - 2 / (1 - x ^ 4))
      (by norm_num) ?_ ?_ ?_
    · simp [f, levyQuarticPartialSum, zero_pow (Nat.succ_ne_zero _)]
    · intro x hx
      have hrem_d : HasDerivAt (fun y : ℝ => (32 / (15 * 65)) * y ^ 65)
          ((32 / 15) * x ^ 64) x := by
        exact ((hasDerivAt_pow 65 x).const_mul (32 / (15 * 65))).congr_deriv (by norm_num; ring)
      exact ((hasDerivAt_levyQuarticPartialSum x).add hrem_d).sub (hd_f x hx)
    · intro x hx
      have hx4_le : x ^ 4 ≤ 1 / 16 :=
        (pow_le_pow_left₀ hx.1 hx.2 4).trans (by norm_num)
      have hx4 : 0 < 1 - x ^ 4 := by linarith
      have hdiff : (∑ n ∈ Finset.range 16, 2 * x ^ (4 * n)) + (32 / 15) * x ^ 64 -
          2 / (1 - x ^ 4) = 2 * x ^ 64 * (16 / 15 - 1 / (1 - x ^ 4)) := by
        have hg := geom_quartic_remainder hx4.ne'
        linarith [show 2 * x ^ 64 * (16 / 15 - 1 / (1 - x ^ 4)) =
          (32 / 15) * x ^ 64 - 2 * x ^ 64 / (1 - x ^ 4) by ring]
      rw [hdiff]
      have hinv : 1 / (1 - x ^ 4) ≤ 16 / 15 := by
        rw [div_le_iff₀ hx4]; linarith
      have h64 : 0 ≤ 2 * x ^ 64 := by have := hx.1; positivity
      exact mul_nonneg h64 (by linarith)
  rw [hf_half] at h_lo h_hi
  have c_lo : archLevyTwoLogTwoLo ≤ levyQuarticPartialSum (1 / 2) := by
    norm_num [archLevyTwoLogTwoLo, levyQuarticPartialSum, Finset.sum_range_succ]
  have c_hi : levyQuarticPartialSum (1 / 2) + (32 / (15 * 65)) * (1 / 2 : ℝ) ^ 65 ≤
      archLevyTwoLogTwoHi := by
    norm_num [archLevyTwoLogTwoHi, levyQuarticPartialSum, Finset.sum_range_succ]
  exact ⟨c_lo.trans (sub_nonneg.mp h_lo), (sub_nonneg.mp h_hi).trans c_hi⟩

/-! ### Derived enclosures for `gammaBracket 0` and prime weights and shifts -/

theorem gammaBracket_zero_bounds :
    gammaBracketZeroLo ≤ Zeta23.EF.gammaBracket 0 ∧
      Zeta23.EF.gammaBracket 0 ≤ gammaBracketZeroHi := by
  have hbr := _root_.RHTower.WeilLevyPoleGauss.neg_gammaBracket_zero_eq
  obtain ⟨hlp1, hlp2⟩ := log_pi_bounds_d20
  obtain ⟨hl21, hl22⟩ := log_two_bounds_d26
  obtain ⟨heu1, heu2⟩ := eulerMascheroniConstant_bounds_d18
  obtain ⟨hpi1, hpi2⟩ := pi_bounds_d20
  have c1 : gammaBracketZeroLo ≤ -(logPiHi + 3 * logTwoHi + eulerHi + piHi / 2) := by
    norm_num [gammaBracketZeroLo, logPiHi, logTwoHi, eulerHi, piHi]
  have c2 : -(logPiLo + 3 * logTwoLo + eulerLo + piLo / 2) ≤ gammaBracketZeroHi := by
    norm_num [gammaBracketZeroHi, logPiLo, logTwoLo, eulerLo, piLo]
  have hb1 : -(logPiHi + 3 * logTwoHi + eulerHi + piHi / 2) ≤ Zeta23.EF.gammaBracket 0 := by
    linarith [hbr, hlp2, hl22, heu2, hpi2]
  have hb2 : Zeta23.EF.gammaBracket 0 ≤ -(logPiLo + 3 * logTwoLo + eulerLo + piLo / 2) := by
    linarith [hbr, hlp1, hl21, heu1, hpi1]
  exact ⟨c1.trans hb1, hb2.trans c2⟩

theorem primeThreeRatio_bounds :
    primeThreeRatioLo ≤ Real.log 3 / Real.log 2 ∧
      Real.log 3 / Real.log 2 ≤ primeThreeRatioHi := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  obtain ⟨h3l, h3u⟩ := log_three_bounds_d26
  have h2p : 0 < Real.log 2 := by linarith [show (0 : ℝ) < logTwoLo by norm_num [logTwoLo]]
  constructor
  · rw [le_div_iff₀ h2p]
    have c : primeThreeRatioLo * logTwoHi ≤ logThreeLo := by
      norm_num [primeThreeRatioLo, logTwoHi, logThreeLo]
    have hmul := mul_le_mul_of_nonneg_left h2u (by norm_num [primeThreeRatioLo] : 0 ≤ primeThreeRatioLo)
    linarith
  · rw [div_le_iff₀ h2p]
    have c : logThreeHi ≤ primeThreeRatioHi * logTwoLo := by
      norm_num [primeThreeRatioHi, logTwoLo, logThreeHi]
    have hmul := mul_le_mul_of_nonneg_left h2l (by norm_num [primeThreeRatioHi] : 0 ≤ primeThreeRatioHi)
    linarith

theorem primeThreeShift_bounds :
    primeThreeShiftLo ≤ Real.log 3 / Real.log 2 - 1 ∧
      Real.log 3 / Real.log 2 - 1 ≤ primeThreeShiftHi := by
  obtain ⟨h1, h2⟩ := primeThreeRatio_bounds
  have c1 : primeThreeShiftLo = primeThreeRatioLo - 1 := by
    norm_num [primeThreeShiftLo, primeThreeRatioLo]
  have c2 : primeThreeShiftHi = primeThreeRatioHi - 1 := by
    norm_num [primeThreeShiftHi, primeThreeRatioHi]
  exact ⟨by linarith, by linarith⟩

theorem primeTwoWeight_bounds :
    primeTwoWeightLo ≤ Real.log 2 / Real.sqrt 2 ∧
      Real.log 2 / Real.sqrt 2 ≤ primeTwoWeightHi := by
  obtain ⟨h2l, h2u⟩ := log_two_bounds_d26
  obtain ⟨hsl, hsu⟩ := sqrt_two_bounds_d26
  have hsp : 0 < Real.sqrt 2 := by linarith [show (0 : ℝ) < sqrtTwoLo by norm_num [sqrtTwoLo]]
  constructor
  · rw [le_div_iff₀ hsp]
    have c : primeTwoWeightLo * sqrtTwoHi ≤ logTwoLo := by
      norm_num [primeTwoWeightLo, sqrtTwoHi, logTwoLo]
    have hmul := mul_le_mul_of_nonneg_left hsu (by norm_num [primeTwoWeightLo] : 0 ≤ primeTwoWeightLo)
    linarith
  · rw [div_le_iff₀ hsp]
    have c : logTwoHi ≤ primeTwoWeightHi * sqrtTwoLo := by
      norm_num [primeTwoWeightHi, sqrtTwoLo, logTwoHi]
    have hmul := mul_le_mul_of_nonneg_left hsl (by norm_num [primeTwoWeightHi] : 0 ≤ primeTwoWeightHi)
    linarith

theorem primeThreeWeight_bounds :
    primeThreeWeightLo ≤ Real.log 3 / Real.sqrt 3 ∧
      Real.log 3 / Real.sqrt 3 ≤ primeThreeWeightHi := by
  obtain ⟨h3l, h3u⟩ := log_three_bounds_d26
  obtain ⟨hsl, hsu⟩ := sqrt_three_bounds_d26
  have hsp : 0 < Real.sqrt 3 := by linarith [show (0 : ℝ) < sqrtThreeLo by norm_num [sqrtThreeLo]]
  constructor
  · rw [le_div_iff₀ hsp]
    have c : primeThreeWeightLo * sqrtThreeHi ≤ logThreeLo := by
      norm_num [primeThreeWeightLo, sqrtThreeHi, logThreeLo]
    have hmul := mul_le_mul_of_nonneg_left hsu (by norm_num [primeThreeWeightLo] : 0 ≤ primeThreeWeightLo)
    linarith
  · rw [div_le_iff₀ hsp]
    have c : logThreeHi ≤ primeThreeWeightHi * sqrtThreeLo := by
      norm_num [primeThreeWeightHi, sqrtThreeLo, logThreeHi]
    have hmul := mul_le_mul_of_nonneg_left hsl (by norm_num [primeThreeWeightHi] : 0 ≤ primeThreeWeightHi)
    linarith

/-! ### Shifted `(2, 3)`-smooth Taylor lower bound for `log 2 - log (1 - x²) / 2` -/

private theorem neg_log_one_sub_ge_sum (r : ℕ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    (∑ m ∈ Finset.Icc 1 r, z ^ m / (2 * (m : ℝ))) ≤ -Real.log (1 - z) / 2 := by
  have hsum_eq : (∑ m ∈ Finset.Icc 1 r, z ^ m / (2 * (m : ℝ))) =
      (∑ k ∈ Finset.range r, z ^ (k + 1) / ((k : ℝ) + 1)) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_bij (fun m _ => m - 1) ?_ ?_ ?_ ?_
    · intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_range]
      omega
    · intro m1 hm1 m2 hm2 heq
      rw [Finset.mem_Icc] at hm1 hm2
      omega
    · intro k hk
      rw [Finset.mem_range] at hk
      exact ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro m hm
      rw [Finset.mem_Icc] at hm
      have hm1 : m - 1 + 1 = m := by omega
      rw [hm1]
      have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hm1
      rw [hcast]
      ring
  rw [hsum_eq]
  suffices h : 0 ≤ -Real.log (1 - z) - ∑ k ∈ Finset.range r, z ^ (k + 1) / ((k : ℝ) + 1) by
    linarith
  refine nonneg_of_hasDerivAt_nonneg
    (fun y => -Real.log (1 - y) - ∑ k ∈ Finset.range r, y ^ (k + 1) / ((k : ℝ) + 1))
    (fun x => 1 / (1 - x) - ∑ k ∈ Finset.range r, x ^ k) hz0 ?_ ?_ ?_
  · simp [zero_pow (Nat.succ_ne_zero _)]
  · intro x hx
    have hx1 : 0 < 1 - x := by linarith [hx.2, hz1]
    have hd1 : HasDerivAt (fun y => -Real.log (1 - y)) (1 / (1 - x)) x := by
      have h := (((hasDerivAt_id' x).const_sub 1).log hx1.ne').neg
      exact h.congr_deriv (by ring)
    have hd2 : HasDerivAt (fun y : ℝ => ∑ k ∈ Finset.range r, y ^ (k + 1) / ((k : ℝ) + 1))
        (∑ k ∈ Finset.range r, x ^ k) x := by
      have hk : ∀ k ∈ Finset.range r,
          HasDerivAt (fun y : ℝ => y ^ (k + 1) / ((k : ℝ) + 1)) (x ^ k) x := by
        intro k _
        have h := (hasDerivAt_pow (k + 1) x).div_const ((k : ℝ) + 1)
        refine h.congr_deriv ?_
        have hne : ((k : ℝ) + 1) ≠ 0 := by positivity
        push_cast; field_simp [hne]
      simpa only [sum_fn] using HasDerivAt.sum hk
    exact hd1.sub hd2
  · intro x hx
    have hx1 : 0 < 1 - x := by linarith [hx.2, hz1]
    have hg := geom_sum_mul_neg x r
    have hrem : 1 / (1 - x) - (∑ k ∈ Finset.range r, x ^ k) = x ^ r / (1 - x) := by
      rw [sub_eq_iff_eq_add]
      apply (div_eq_iff hx1.ne').mpr
      calc
        (1 : ℝ) = (∑ k ∈ Finset.range r, x ^ k) * (1 - x) + x ^ r := by rw [hg]; ring
        _ = (x ^ r / (1 - x) + ∑ k ∈ Finset.range r, x ^ k) * (1 - x) := by
          rw [add_mul, div_mul_cancel₀ _ hx1.ne']; ring
    rw [hrem]
    have hxr : 0 ≤ x ^ r := pow_nonneg hx.1 r
    positivity

/-- Shifted Taylor lower bound for `log 2 - log (1 - x²) / 2` anchored at `1 - t0 = 2^p * 3^q`. -/
theorem exterior_log_potential_ge_shifted_taylor (p q : ℤ) (t0 om base : ℝ) (r : ℕ)
    (hom : om = (2 : ℝ) ^ p * (3 : ℝ) ^ q) (ht0 : t0 = 1 - om)
    (hbase : base ≤ Real.log 2 - ((p : ℝ) * Real.log 2 + (q : ℝ) * Real.log 3) / 2)
    {x : ℝ} (hxmin : t0 ≤ x ^ 2) (hxmax : x ^ 2 < 1) :
    base + (∑ m ∈ Finset.Icc 1 r, ((x ^ 2 - t0) / om) ^ m / (2 * (m : ℝ))) ≤
      Real.log 2 - Real.log (1 - x ^ 2) / 2 := by
  have hom_pos : 0 < om := by rw [hom]; positivity
  let z := (x ^ 2 - t0) / om
  have hz0 : 0 ≤ z := div_nonneg (by linarith) hom_pos.le
  have hz1 : z < 1 := by
    dsimp [z]
    rw [div_lt_one hom_pos]
    linarith
  have h1mx2 : 1 - x ^ 2 = om * (1 - z) := by
    dsimp [z]
    rw [ht0]
    field_simp [hom_pos.ne']
    ring
  have hlog_om : Real.log om = (p : ℝ) * Real.log 2 + (q : ℝ) * Real.log 3 := by
    rw [hom, Real.log_mul (by positivity) (by positivity), Real.log_zpow, Real.log_zpow]
  have hlog_split : Real.log (1 - x ^ 2) = Real.log om + Real.log (1 - z) := by
    rw [h1mx2, Real.log_mul hom_pos.ne' (by linarith)]
  have hsum := neg_log_one_sub_ge_sum r hz0 hz1
  rw [hlog_split, hlog_om]
  linarith

/-! ### Uniform Legendre polynomial and derivative bounds on `[-1, 1]` -/

private theorem legP'_step_identities :
    ∀ (n : ℕ) (u : ℝ),
      legP' (n + 1) u = ((n : ℝ) + 1) * legP n u + u * legP' n u ∧
        u * legP' (n + 1) u - legP' n u = ((n : ℝ) + 1) * legP (n + 1) u := by
  intro n
  induction n with
  | zero =>
    intro u
    simp [legP, legP']
  | succ n ih =>
    intro u
    obtain ⟨ih1, _⟩ := ih u
    have hbonnet := legP_bonnet n u
    have hp' : legP' (n + 2) u = (2 * (n : ℝ) + 3) * legP (n + 1) u + legP' n u := rfl
    push_cast
    constructor
    · rw [hp']; linarith
    · rw [hp']; linarith [hbonnet, congrArg (u * ·) ih1]

private theorem legP_envelope_le_one {u : ℝ} (hu : u ^ 2 ≤ 1) :
    ∀ n : ℕ, legP (n + 1) u ^ 2 + (1 - u ^ 2) * legP' (n + 1) u ^ 2 / ((n : ℝ) + 1) ^ 2 ≤ 1 := by
  intro n
  induction n with
  | zero =>
    simp only [legP, legP', Nat.cast_zero, zero_add]
    ring_nf; exact le_rfl
  | succ n ih =>
    obtain ⟨h1, h2⟩ := legP'_step_identities (n + 1) u
    have halg : (((n : ℝ) + 1) + 1) ^ 2 * legP (n + 2) u ^ 2 +
        (1 - u ^ 2) * legP' (n + 2) u ^ 2 =
        (((n : ℝ) + 1) + 1) ^ 2 * legP (n + 1) u ^ 2 +
          (1 - u ^ 2) * legP' (n + 1) u ^ 2 := by
      have hs1 : (legP' (n + 2) u - u * legP' (n + 1) u) ^ 2 =
          ((((n : ℝ) + 1) + 1) * legP (n + 1) u) ^ 2 := by
        congr 1; push_cast at h1 ⊢; linarith
      have hs2 : (u * legP' (n + 2) u - legP' (n + 1) u) ^ 2 =
          ((((n : ℝ) + 1) + 1) * legP (n + 2) u) ^ 2 := by
        congr 1; push_cast at h2 ⊢; exact h2
      linarith [show (legP' (n + 2) u - u * legP' (n + 1) u) ^ 2 -
          (u * legP' (n + 2) u - legP' (n + 1) u) ^ 2 =
          (1 - u ^ 2) * legP' (n + 2) u ^ 2 - (1 - u ^ 2) * legP' (n + 1) u ^ 2 by ring,
        hs1, hs2]
    have hpos2 : (0 : ℝ) < (((n : ℝ) + 1) + 1) ^ 2 := by positivity
    have hpos1 : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    have heq : legP (n + 2) u ^ 2 +
        (1 - u ^ 2) * legP' (n + 2) u ^ 2 / ((n + 1 : ℕ) + 1 : ℝ) ^ 2 =
        legP (n + 1) u ^ 2 +
          (1 - u ^ 2) * legP' (n + 1) u ^ 2 / ((n + 1 : ℕ) + 1 : ℝ) ^ 2 := by
      push_cast
      have hL : (legP (n + 2) u ^ 2 + (1 - u ^ 2) * legP' (n + 2) u ^ 2 / (((n : ℝ) + 1) + 1) ^ 2) =
          ((((n : ℝ) + 1) + 1) ^ 2 * legP (n + 2) u ^ 2 + (1 - u ^ 2) * legP' (n + 2) u ^ 2) /
            (((n : ℝ) + 1) + 1) ^ 2 := by field_simp [hpos2.ne']
      have hR : (legP (n + 1) u ^ 2 + (1 - u ^ 2) * legP' (n + 1) u ^ 2 / (((n : ℝ) + 1) + 1) ^ 2) =
          ((((n : ℝ) + 1) + 1) ^ 2 * legP (n + 1) u ^ 2 + (1 - u ^ 2) * legP' (n + 1) u ^ 2) /
            (((n : ℝ) + 1) + 1) ^ 2 := by field_simp [hpos2.ne']
      rw [hL, hR, halg]
    have hnn : 0 ≤ (1 - u ^ 2) * legP' (n + 1) u ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have hpos2' : (0 : ℝ) < ((n + 1 : ℕ) + 1 : ℝ) ^ 2 := by positivity
    have hdiv_le : (1 - u ^ 2) * legP' (n + 1) u ^ 2 / ((n + 1 : ℕ) + 1 : ℝ) ^ 2 ≤
        (1 - u ^ 2) * legP' (n + 1) u ^ 2 / ((n : ℝ) + 1) ^ 2 := by
      rw [div_le_div_iff₀ hpos2' hpos1]
      have hden_le : ((n : ℝ) + 1) ^ 2 ≤ ((n + 1 : ℕ) + 1 : ℝ) ^ 2 := by
        push_cast; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      exact mul_le_mul_of_nonneg_left hden_le hnn
    linarith

/-- Every Legendre polynomial satisfies `|legP n u| ≤ 1` on `[-1, 1]`. -/
theorem abs_legP_le_one {u : ℝ} (hu : |u| ≤ 1) (n : ℕ) : |legP n u| ≤ 1 := by
  have hu2 : u ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg u) hu 2
    simpa only [sq_abs, one_pow] using h
  rcases n with _ | n
  · simp [legP]
  · have henv := legP_envelope_le_one hu2 n
    have hrem : 0 ≤ (1 - u ^ 2) * legP' (n + 1) u ^ 2 / ((n : ℝ) + 1) ^ 2 :=
      div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by positivity)
    have hsq : |legP (n + 1) u| ^ 2 ≤ 1 := by rw [sq_abs]; linarith
    nlinarith [abs_nonneg (legP (n + 1) u)]

/-- Markov–Legendre derivative bound `|legP' n u| ≤ n(n + 1) / 2` on `[-1, 1]`. -/
theorem abs_legP'_le {u : ℝ} (hu : |u| ≤ 1) :
    ∀ n : ℕ, |legP' n u| ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp [legP']
    · simp [legP']
    · have hp : legP' (n + 2) u = (2 * (n : ℝ) + 3) * legP (n + 1) u + legP' n u := rfl
      rw [hp]
      have h1 := abs_legP_le_one hu (n + 1)
      have h0 := ih n (by omega)
      have habs : |(2 * (n : ℝ) + 3) * legP (n + 1) u + legP' n u| ≤
          (2 * (n : ℝ) + 3) * |legP (n + 1) u| + |legP' n u| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * (n : ℝ) + 3)]
      have hm := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) + 3)
      push_cast
      linarith

#print axioms log_two_bounds_d26
#print axioms log_three_bounds_d26
#print axioms eulerMascheroniConstant_bounds_d18
#print axioms archLevyAntideriv_two_mul_log_two
#print axioms archLevyAntideriv_two_mul_log_two_bounds
#print axioms gammaBracket_zero_bounds
#print axioms exterior_log_potential_ge_shifted_taylor
#print axioms abs_legP_le_one
#print axioms abs_legP'_le

end GaloisForLFunctions.WindowTowerOfSpecZ
