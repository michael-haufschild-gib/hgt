import GaloisForLFunctions.RHTower.LiClockPairedEtaPositiveCompletion
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Exact first-prefix Gamma packet bounds and sharp central slope

The full shifted Gamma reciprocal ladder defines an entire-clock hyperbolic
packet. Its complete Taylor/atom interchange retains every source index and
odd factorial. A telescoping majorant gives square mass strictly between zero
and `9/25`, sharp complex growth envelope, and strict real positive bounds.
The genuine derivative at zero equals the full square mass; the quotient
limit uses the positive punctured approach. Identification with the literal
finite eta source is supplied by the separate classification leaf.
-/

open Complex Filter Topology Set Metric GaloisForLFunctions
namespace RHTower
noncomputable section

/-- Exact shifted Gamma pole clock, with every atom retained. -/
def liClockPairedEtaFirstPrefixGammaClock (t : ℂ) : ℂ :=
  ∑' n : ℕ, Complex.sinh (t / (2 * (n : ℂ) + 5 / 2)) / (2 * (n : ℂ) + 5 / 2)

/-- Reciprocal-square mass of the shifted Gamma ladder. -/
def liClockPairedEtaFirstPrefixGammaSquareMass : ℝ :=
  ∑' n : ℕ, 1 / (2 * (n : ℝ) + 5 / 2) ^ 2

private def gammaHeight (n : ℕ) : ℝ := 2 * (n : ℝ) + 5 / 2
private def gammaReciprocal (n : ℕ) : ℂ := (gammaHeight n : ℂ)⁻¹

private theorem gammaHeight_pos (n : ℕ) : 0 < gammaHeight n := by
  unfold gammaHeight
  positivity

private theorem gammaHeight_ge (n : ℕ) : 5 / 2 ≤ gammaHeight n := by
  unfold gammaHeight
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

private theorem hasSum_gammaHeight_telescoper :
    HasSum (fun n : ℕ => 1 / (gammaHeight n * (gammaHeight n + 2))) (1 / 5) := by
  have hh := (hasSum_one_div_shift_mul_succ (σ := 5 / 4) (by norm_num)).mul_left (1 / 4 : ℝ)
  have heq (n : ℕ) : (1 / 4 : ℝ) * (1 / ((5 / 4 + (n : ℝ)) * (5 / 4 + (n : ℝ) + 1))) =
      1 / (gammaHeight n * (gammaHeight n + 2)) := by
    dsimp [gammaHeight]
    field_simp
    ring
  have hh2 := hh.congr_fun (fun n => (heq n).symm)
  have hv : (1 / 4 : ℝ) * (1 / (5 / 4)) = 1 / 5 := by norm_num
  rw [hv] at hh2
  exact hh2

private theorem gammaHeight_square_le_telescoper (n : ℕ) :
    1 / gammaHeight n ^ 2 ≤ (9 / 5) / (gammaHeight n * (gammaHeight n + 2)) := by
  have hp := gammaHeight_pos n
  have hg := gammaHeight_ge n
  rw [div_le_div_iff₀ (by positivity : 0 < gammaHeight n ^ 2) (by positivity)]
  have hh := mul_le_mul_of_nonneg_left hg hp.le
  nlinarith

private theorem summable_gammaHeight_square : Summable (fun n : ℕ => 1 / gammaHeight n ^ 2) :=
  Summable.of_nonneg_of_le (fun n => by positivity)
    gammaHeight_square_le_telescoper (by
      simpa only [div_eq_mul_inv, one_mul] using hasSum_gammaHeight_telescoper.summable.mul_left (9 / 5 : ℝ))

theorem summable_liClockPairedEtaFirstPrefixGammaSquareMass :
    Summable (fun n : ℕ => 1 / (2 * (n : ℝ) + 5 / 2) ^ 2) :=
  summable_gammaHeight_square

theorem liClockPairedEtaFirstPrefixGammaSquareMass_pos :
    0 < liClockPairedEtaFirstPrefixGammaSquareMass := by
  exact summable_gammaHeight_square.tsum_pos (fun n => by positivity) 0 (by norm_num [gammaHeight])

theorem liClockPairedEtaFirstPrefixGammaSquareMass_lt_nine_div_twenty_five :
    liClockPairedEtaFirstPrefixGammaSquareMass < 9 / 25 := by
  have hg : Summable (fun n : ℕ => (9 / 5) / (gammaHeight n * (gammaHeight n + 2))) := by
    simpa only [div_eq_mul_inv, one_mul] using hasSum_gammaHeight_telescoper.summable.mul_left (9 / 5 : ℝ)
  have hstrict := summable_gammaHeight_square.tsum_lt_tsum gammaHeight_square_le_telescoper
    (by norm_num [gammaHeight] : 1 / gammaHeight 1 ^ 2 < (9 / 5) / (gammaHeight 1 * (gammaHeight 1 + 2))) hg
  have heq : (∑' n : ℕ, (9 / 5) / (gammaHeight n * (gammaHeight n + 2))) = 9 / 25 := by
    calc
      _ = (9 / 5) * ∑' n : ℕ, 1 / (gammaHeight n * (gammaHeight n + 2)) := by
        rw [← tsum_mul_left]
        exact tsum_congr (fun n => by ring)
      _ = _ := by rw [hasSum_gammaHeight_telescoper.tsum_eq]; norm_num
  exact hstrict.trans_eq heq

private theorem sinh_contract_le {a x : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 ≤ x) :
    Real.sinh (a * x) ≤ a * Real.sinh x := by
  have hs := (Real.hasSum_sinh (a * x)).summable
  have hg := (Real.hasSum_sinh x).summable.mul_left a
  have hterm (j : ℕ) : (a * x) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) ≤
      a * (x ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) := by
    have hp := pow_le_one₀ (n := 2 * j) ha ha1
    rw [mul_pow, pow_succ]
    have hm := mul_le_mul_of_nonneg_right hp
      (by positivity : 0 ≤ a * (x ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)))
    convert! hm using 1 <;> first | rfl | ring
  simpa only [(Real.hasSum_sinh (a * x)).tsum_eq, tsum_mul_left, (Real.hasSum_sinh x).tsum_eq] using
    hs.tsum_le_tsum hterm hg

private theorem sinh_contract_lt {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x) :
    Real.sinh (a * x) < a * Real.sinh x := by
  have hs := (Real.hasSum_sinh (a * x)).summable
  have hg := (Real.hasSum_sinh x).summable.mul_left a
  have hterm (j : ℕ) : (a * x) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) ≤
      a * (x ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) := by
    have hp := pow_le_one₀ (n := 2 * j) ha.le ha1.le
    rw [mul_pow, pow_succ]
    have hm := mul_le_mul_of_nonneg_right hp
      (by positivity : 0 ≤ a * (x ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)))
    convert! hm using 1 <;> first | rfl | ring
  have ha2 : a ^ 2 < 1 := by
    simpa using pow_lt_pow_left₀ ha1 ha.le (by norm_num : (2 : ℕ) ≠ 0)
  have ha3 : a ^ 3 < a := by
    have hh := mul_lt_mul_of_pos_right ha2 ha
    nlinarith
  have hstrict : (a * x) ^ (2 * 1 + 1) / ((2 * 1 + 1).factorial : ℝ) <
      a * (x ^ (2 * 1 + 1) / ((2 * 1 + 1).factorial : ℝ)) := by
    have hh := mul_lt_mul_of_pos_right ha3 (by positivity : 0 < x ^ 3)
    norm_num
    rw [mul_pow]
    nlinarith
  simpa only [(Real.hasSum_sinh (a * x)).tsum_eq, tsum_mul_left, (Real.hasSum_sinh x).tsum_eq] using
    hs.tsum_lt_tsum hterm hstrict hg

private theorem norm_gammaReciprocal (n : ℕ) : ‖gammaReciprocal n‖ = 1 / gammaHeight n := by
  simp [gammaReciprocal, Complex.norm_real, abs_of_pos (gammaHeight_pos n), one_div]

private theorem summable_gammaReciprocal_square : Summable (fun n : ℕ => ‖gammaReciprocal n‖ ^ 2) := by
  simpa only [norm_gammaReciprocal, div_pow, one_pow] using summable_gammaHeight_square

private theorem norm_gammaReciprocal_le (n : ℕ) : ‖gammaReciprocal n‖ ≤ 2 / 5 := by
  rw [norm_gammaReciprocal]
  have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5 / 2) (gammaHeight_ge n)
  norm_num at hh
  simpa only [one_div] using hh

private theorem gammaHeight_cast (n : ℕ) : (gammaHeight n : ℂ) = 2 * (n : ℂ) + 5 / 2 := by
  unfold gammaHeight
  push_cast
  ring

private theorem gammaClock_eq_atoms (t : ℂ) :
    liClockPairedEtaFirstPrefixGammaClock t = ∑' n : ℕ, gammaReciprocal n * Complex.sinh (t * gammaReciprocal n) := by
  apply tsum_congr
  intro n
  simp only [gammaReciprocal, gammaHeight_cast, div_eq_mul_inv]
  ring

private theorem gammaAtom_ofReal (t : ℝ) (n : ℕ) :
    gammaReciprocal n * Complex.sinh ((t : ℂ) * gammaReciprocal n) =
      (Real.sinh (t / gammaHeight n) / gammaHeight n : ℝ) := by
  simp only [gammaReciprocal, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_sinh]
  ring

theorem summable_norm_liClockPairedEtaFirstPrefixGammaClock (t : ℂ) :
    Summable (fun n : ℕ => ‖Complex.sinh (t / (2 * (n : ℂ) + 5 / 2)) / (2 * (n : ℂ) + 5 / 2)‖) := by
  have hh := summable_norm_liClockCompletionHyperbolicAtom gammaReciprocal
    summable_gammaReciprocal_square (fun n => (norm_gammaReciprocal_le n).trans (by norm_num)) t
  convert hh using 1
  funext n
  congr 1
  simp only [gammaReciprocal, gammaHeight_cast, div_eq_mul_inv]
  ring

theorem summable_norm_liClockPairedEtaFirstPrefixGammaTaylorTerm (t : ℂ) :
    Summable (fun p : ℕ × ℕ => ‖(2 * (p.1 : ℂ) + 5 / 2) ^ (-((2 * p.2 + 2 : ℕ) : ℤ)) *
      t ^ (2 * p.2 + 1) / ((2 * p.2 + 1).factorial : ℂ)‖) := by
  have hh := summable_norm_liClockCompletionHyperbolicTaylorTerm gammaReciprocal
    summable_gammaReciprocal_square (fun n => (norm_gammaReciprocal_le n).trans (by norm_num)) t
  simpa only [liClockCompletionHyperbolicTaylorTerm, gammaReciprocal, gammaHeight,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_natCast, zpow_neg, zpow_natCast, inv_pow] using hh

theorem liClockPairedEtaFirstPrefixGammaClock_eq_tsum_odd (t : ℂ) :
    liClockPairedEtaFirstPrefixGammaClock t =
      ∑' j : ℕ, (∑' n : ℕ, (2 * (n : ℂ) + 5 / 2) ^ (-((2 * j + 2 : ℕ) : ℤ))) *
        t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℂ) := by
  rw [gammaClock_eq_atoms, ← liClockCompletionHyperbolic_tsum_eq gammaReciprocal
    summable_gammaReciprocal_square (fun n => (norm_gammaReciprocal_le n).trans (by norm_num)) t]
  simp only [gammaReciprocal, gammaHeight_cast, zpow_neg, zpow_natCast, inv_pow]

theorem liClockPairedEtaFirstPrefixGammaClock_ofReal (t : ℝ) :
    liClockPairedEtaFirstPrefixGammaClock (t : ℂ) =
      (∑' n : ℕ, Real.sinh (t / (2 * (n : ℝ) + 5 / 2)) / (2 * (n : ℝ) + 5 / 2) : ℝ) := by
  rw [gammaClock_eq_atoms, Complex.ofReal_tsum]
  exact tsum_congr (gammaAtom_ofReal t)

theorem liClockPairedEtaFirstPrefixGammaClock_im_ofReal (t : ℝ) :
    (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).im = 0 := by
  rw [liClockPairedEtaFirstPrefixGammaClock_ofReal]
  rfl

private theorem gammaClock_re_eq (t : ℝ) :
    (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re =
      ∑' n : ℕ, Real.sinh (t / gammaHeight n) / gammaHeight n := by
  rw [liClockPairedEtaFirstPrefixGammaClock_ofReal]
  rfl

private theorem summable_gammaRealAtom (t : ℝ) :
    Summable (fun n : ℕ => Real.sinh (t / gammaHeight n) / gammaHeight n) := by
  apply Complex.summable_ofReal.mp
  have hh := (summable_norm_liClockCompletionHyperbolicAtom gammaReciprocal
    summable_gammaReciprocal_square (fun n => (norm_gammaReciprocal_le n).trans (by norm_num)) (t : ℂ)).of_norm
  exact hh.congr (gammaAtom_ofReal t)

private theorem gammaRealAtom_scale_le {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (n : ℕ)
    (hh : 1 / gammaHeight n ≤ b) :
    Real.sinh (t / gammaHeight n) / gammaHeight n ≤
      (1 / gammaHeight n ^ 2) * (Real.sinh (b * t) / b) := by
  have hp := gammaHeight_pos n
  have ha : 0 ≤ (1 / gammaHeight n) / b := by positivity
  have ha1 : (1 / gammaHeight n) / b ≤ 1 := (div_le_one hb).mpr hh
  have hs := sinh_contract_le ha ha1 (mul_nonneg hb.le ht)
  rw [show (1 / gammaHeight n / b) * (b * t) = t / gammaHeight n by field_simp] at hs
  calc
    _ ≤ (((1 / gammaHeight n) / b) * Real.sinh (b * t)) / gammaHeight n :=
      div_le_div_of_nonneg_right hs hp.le
    _ = _ := by ring

private theorem gammaRealAtom_scale_lt {t b : ℝ} (ht : 0 < t) (hb : 0 < b) (n : ℕ)
    (hh : 1 / gammaHeight n < b) :
    Real.sinh (t / gammaHeight n) / gammaHeight n <
      (1 / gammaHeight n ^ 2) * (Real.sinh (b * t) / b) := by
  have hp := gammaHeight_pos n
  have ha : 0 < (1 / gammaHeight n) / b := by positivity
  have ha1 : (1 / gammaHeight n) / b < 1 := (div_lt_one hb).mpr hh
  have hs := sinh_contract_lt ha ha1 (mul_pos hb ht)
  rw [show (1 / gammaHeight n / b) * (b * t) = t / gammaHeight n by field_simp] at hs
  calc
    _ < (((1 / gammaHeight n) / b) * Real.sinh (b * t)) / gammaHeight n :=
      (div_lt_div_iff_of_pos_right hp).mpr hs
    _ = _ := by ring

private theorem gammaClock_re_scale_lt {t b : ℝ} (ht : 0 < t) (hb : 0 < b)
    (hh : ∀ n : ℕ, 1 / gammaHeight n ≤ b) {i : ℕ} (hi : 1 / gammaHeight i < b) :
    (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re <
      liClockPairedEtaFirstPrefixGammaSquareMass * (Real.sinh (b * t) / b) := by
  rw [gammaClock_re_eq]
  have hs := summable_gammaRealAtom t
  have hg := summable_gammaHeight_square.mul_right (Real.sinh (b * t) / b)
  have hh2 := hs.tsum_lt_tsum (fun n => gammaRealAtom_scale_le ht.le hb n (hh n))
    (gammaRealAtom_scale_lt ht hb i hi) hg
  simpa only [tsum_mul_right, liClockPairedEtaFirstPrefixGammaSquareMass, gammaHeight] using hh2

theorem liClockPairedEtaFirstPrefixGammaClock_re_gt_firstAtom {t : ℝ} (ht : 0 < t) :
    (2 / 5) * Real.sinh ((2 / 5) * t) <
      (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re := by
  rw [gammaClock_re_eq, (summable_gammaRealAtom t).tsum_eq_zero_add]
  have hs : Summable (fun n : ℕ => Real.sinh (t / gammaHeight (n + 1)) / gammaHeight (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_gammaRealAtom t)
  have hpos := hs.tsum_pos (fun n => by
    have hp := gammaHeight_pos (n + 1)
    exact div_nonneg (Real.sinh_nonneg_iff.mpr (div_nonneg ht.le hp.le)) hp.le) 0
    (by exact div_pos (Real.sinh_pos_iff.mpr (div_pos ht (gammaHeight_pos _))) (gammaHeight_pos _))
  have hzero : Real.sinh (t / gammaHeight 0) / gammaHeight 0 =
      (2 / 5) * Real.sinh ((2 / 5) * t) := by
    norm_num [gammaHeight, div_eq_mul_inv, mul_comm]
  rw [hzero]
  linarith

theorem liClockPairedEtaFirstPrefixGammaClock_re_pos {t : ℝ} (ht : 0 < t) :
    0 < (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re := by
  have hs : 0 < (2 / 5 : ℝ) * Real.sinh ((2 / 5) * t) := by
    exact mul_pos (by norm_num) (Real.sinh_pos_iff.mpr (by positivity))
  exact hs.trans (liClockPairedEtaFirstPrefixGammaClock_re_gt_firstAtom ht)

theorem liClockPairedEtaFirstPrefixGammaClock_re_lt_mass_envelope {t : ℝ} (ht : 0 < t) :
    (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re <
      (5 * liClockPairedEtaFirstPrefixGammaSquareMass / 2) * Real.sinh ((2 / 5) * t) := by
  have hh := gammaClock_re_scale_lt ht (by norm_num : (0 : ℝ) < 2 / 5)
    (fun n => by simpa only [norm_gammaReciprocal] using norm_gammaReciprocal_le n)
    (by norm_num [gammaHeight] : 1 / gammaHeight 1 < (2 / 5 : ℝ))
  convert! hh using 1
  first | rfl | ring

theorem liClockPairedEtaFirstPrefixGammaClock_re_lt_nine_tenths {t : ℝ} (ht : 0 < t) :
    (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re < (9 / 10) * Real.sinh ((2 / 5) * t) := by
  have hs := Real.sinh_pos_iff.mpr (by positivity : 0 < (2 / 5 : ℝ) * t)
  have hm := liClockPairedEtaFirstPrefixGammaSquareMass_lt_nine_div_twenty_five
  have hb : (5 * liClockPairedEtaFirstPrefixGammaSquareMass / 2) < (9 / 10 : ℝ) := by linarith
  exact (liClockPairedEtaFirstPrefixGammaClock_re_lt_mass_envelope ht).trans
    (mul_lt_mul_of_pos_right hb hs)

theorem liClockPairedEtaFirstPrefixGammaClock_re_lt_two_sinh_mass {t : ℝ} (ht : 0 < t) :
    (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re <
      (liClockPairedEtaFirstPrefixGammaSquareMass / 2) * Real.sinh (2 * t) := by
  have hh := gammaClock_re_scale_lt ht (by norm_num : (0 : ℝ) < 2)
    (fun n => by rw [← norm_gammaReciprocal]; exact (norm_gammaReciprocal_le n).trans (by norm_num : (2 / 5 : ℝ) ≤ 2))
    (by norm_num [norm_gammaReciprocal, gammaHeight] : 1 / gammaHeight 0 < (2 : ℝ))
  convert! hh using 1
  first | rfl | ring

theorem liClockPairedEtaFirstPrefixGammaClock_re_lt_nine_fiftieths {t : ℝ} (ht : 0 < t) :
    (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re < (9 / 50) * Real.sinh (2 * t) := by
  have hs := Real.sinh_pos_iff.mpr (by positivity : 0 < 2 * t)
  have hm := liClockPairedEtaFirstPrefixGammaSquareMass_lt_nine_div_twenty_five
  have hb : liClockPairedEtaFirstPrefixGammaSquareMass / 2 < (9 / 50 : ℝ) := by linarith
  exact (liClockPairedEtaFirstPrefixGammaClock_re_lt_two_sinh_mass ht).trans
    (mul_lt_mul_of_pos_right hb hs)

/-- The complete complex packet obeys its sharp reciprocal-square envelope. -/
theorem norm_liClockPairedEtaFirstPrefixGammaClock_le (t : ℂ) :
    ‖liClockPairedEtaFirstPrefixGammaClock t‖ ≤
      (5 * liClockPairedEtaFirstPrefixGammaSquareMass / 2) * Real.sinh ((2 / 5) * ‖t‖) := by
  let q : ℕ → ℂ := fun n => (5 / 2) * gammaReciprocal n
  have hn (n : ℕ) : ‖q n‖ = (5 / 2) * ‖gammaReciprocal n‖ := by
    simp only [q, norm_mul]
    norm_num
  have hq : Summable (fun n : ℕ => ‖q n‖ ^ 2) := by
    have hh := summable_gammaReciprocal_square.mul_left (25 / 4 : ℝ)
    exact hh.congr (fun n => by rw [hn]; ring)
  have hq1 (n : ℕ) : ‖q n‖ ≤ 1 := by
    rw [hn]
    nlinarith [norm_gammaReciprocal_le n]
  have ht : ‖(2 / 5 : ℂ) * t‖ ≤ (2 / 5 : ℝ) * ‖t‖ := by
    simp only [norm_mul]
    norm_num
  have hh := norm_liClockCompletionHyperbolic_tsum_le q hq hq1
    ((2 / 5 : ℂ) * t) ht
  have heq : liClockPairedEtaFirstPrefixGammaClock t =
      (2 / 5 : ℂ) * ∑' n : ℕ, q n * Complex.sinh (((2 / 5 : ℂ) * t) * q n) := by
    rw [gammaClock_eq_atoms, ← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp only [q]
    rw [show ((2 / 5 : ℂ) * t) * ((5 / 2) * gammaReciprocal n) = t * gammaReciprocal n by ring]
    ring
  have hmass : (∑' n : ℕ, ‖q n‖ ^ 2) = (25 / 4) * liClockPairedEtaFirstPrefixGammaSquareMass := by
    calc
      _ = (25 / 4) * ∑' n : ℕ, 1 / gammaHeight n ^ 2 := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        rw [hn, norm_gammaReciprocal]
        ring
      _ = _ := rfl
  rw [heq, norm_mul]
  norm_num only [norm_div, norm_ofNat]
  have hh2 := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2 / 5)
  rw [hmass] at hh2
  convert! hh2 using 1
  first | rfl | ring

/-- One summable source envelope works on every closed complex clock disk. -/
theorem norm_liClockPairedEtaFirstPrefixGammaClock_le_on_disk {T : ℝ}
    {t : ℂ} (ht : ‖t‖ ≤ T) :
    ‖liClockPairedEtaFirstPrefixGammaClock t‖ ≤
      (5 * liClockPairedEtaFirstPrefixGammaSquareMass / 2) * Real.sinh ((2 / 5) * T) := by
  exact (norm_liClockPairedEtaFirstPrefixGammaClock_le t).trans
    (mul_le_mul_of_nonneg_left (Real.sinh_le_sinh.mpr (by linarith))
      (by positivity [liClockPairedEtaFirstPrefixGammaSquareMass_pos]))

@[simp] theorem liClockPairedEtaFirstPrefixGammaClock_zero :
    liClockPairedEtaFirstPrefixGammaClock 0 = 0 := by
  simp [liClockPairedEtaFirstPrefixGammaClock]

private theorem gammaAtom_hasDerivAt (n : ℕ) (t : ℂ) :
    HasDerivAt (fun z : ℂ => gammaReciprocal n * Complex.sinh (z * gammaReciprocal n))
      (gammaReciprocal n ^ 2 * Complex.cosh (t * gammaReciprocal n)) t := by
  have hh := ((Complex.hasDerivAt_sinh (t * gammaReciprocal n)).comp t
    ((hasDerivAt_id t).mul_const (gammaReciprocal n))).const_mul (gammaReciprocal n)
  convert! hh using 1
  first | rfl | ring

/-- Genuine complex derivative at zero: exactly the full positive square mass. -/
theorem hasDerivAt_liClockPairedEtaFirstPrefixGammaClock_zero :
    HasDerivAt liClockPairedEtaFirstPrefixGammaClock
      (liClockPairedEtaFirstPrefixGammaSquareMass : ℂ) 0 := by
  have hu : Summable (fun n : ℕ => ‖gammaReciprocal n‖ ^ 2 * Real.cosh 1) :=
    summable_gammaReciprocal_square.mul_right (Real.cosh 1)
  have hbound (n : ℕ) (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      ‖gammaReciprocal n ^ 2 * Complex.cosh (z * gammaReciprocal n)‖ ≤
        ‖gammaReciprocal n‖ ^ 2 * Real.cosh 1 := by
    have hzn : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
    have hprod : ‖z * gammaReciprocal n‖ ≤ 1 := by
      rw [norm_mul]
      calc
        ‖z‖ * ‖gammaReciprocal n‖ ≤ 1 * (2 / 5 : ℝ) := by gcongr; exact norm_gammaReciprocal_le n
        _ ≤ 1 := by norm_num
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left
      ((norm_cosh_le_cosh_norm _).trans (Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg (norm_nonneg _), abs_one] using hprod))) (by positivity)
  have hd := hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
    (fun n z _ => gammaAtom_hasDerivAt n z) hbound
    (by simp : (0 : ℂ) ∈ ball (0 : ℂ) 1)
    (by simp : Summable (fun n : ℕ => gammaReciprocal n * Complex.sinh (0 * gammaReciprocal n)))
    (by simp : (0 : ℂ) ∈ ball (0 : ℂ) 1)
  have hsum : (∑' n : ℕ, gammaReciprocal n ^ 2 * Complex.cosh (0 * gammaReciprocal n)) =
      (liClockPairedEtaFirstPrefixGammaSquareMass : ℂ) := by
    simp only [zero_mul, Complex.cosh_zero, mul_one]
    rw [liClockPairedEtaFirstPrefixGammaSquareMass, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    simp [gammaReciprocal, gammaHeight, inv_pow]
  rw [hsum] at hd
  have hf : liClockPairedEtaFirstPrefixGammaClock =
      (fun t : ℂ => ∑' n : ℕ, gammaReciprocal n * Complex.sinh (t * gammaReciprocal n)) :=
    funext gammaClock_eq_atoms
  rw [hf]
  exact hd

/-- The real packet derivative, with no totalized quotient limit at the center. -/
theorem hasDerivAt_liClockPairedEtaFirstPrefixGammaClock_re_zero :
    HasDerivAt (fun t : ℝ => (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re)
      liClockPairedEtaFirstPrefixGammaSquareMass 0 := by
  exact hasDerivAt_liClockPairedEtaFirstPrefixGammaClock_zero.real_of_complex

/-- The sharp slope uses the positive punctured approach, excluding the totalized quotient at zero. -/
theorem liClockPairedEtaFirstPrefixGammaClock_re_div_tendsto_zero_right :
    Tendsto (fun t : ℝ => (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re / t)
      (nhdsWithin 0 (Ioi 0)) (𝓝 liClockPairedEtaFirstPrefixGammaSquareMass) := by
  have hh := hasDerivAt_liClockPairedEtaFirstPrefixGammaClock_re_zero.tendsto_slope_zero
  have hm : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhdsWithin 0 ({0}ᶜ) :=
    nhdsWithin_mono 0 (by intro x hx; simp only [mem_compl_iff, mem_singleton_iff]; exact ne_of_gt hx)
  simpa only [zero_add, Complex.ofReal_zero, liClockPairedEtaFirstPrefixGammaClock_zero,
    Complex.zero_re, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh.mono_left hm

/-- Uniform absolute Taylor envelope on a closed complex clock disk. -/
theorem norm_liClockPairedEtaFirstPrefixGammaTaylorTerm_le_on_disk
    {T : ℝ} {t : ℂ} (ht : ‖t‖ ≤ T) (n j : ℕ) :
    ‖(2 * (n : ℂ) + 5 / 2) ^ (-((2 * j + 2 : ℕ) : ℤ)) *
      t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℂ)‖ ≤
      (1 / (2 * (n : ℝ) + 5 / 2) ^ 2) *
        (T ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) := by
  have hh := norm_liClockCompletionHyperbolicTaylorTerm_le gammaReciprocal t n j
    ((norm_gammaReciprocal_le n).trans (by norm_num)) ht
  simp only [norm_gammaReciprocal] at hh
  simp only [liClockCompletionHyperbolicTaylorTerm, gammaReciprocal, gammaHeight_cast,
    inv_pow] at hh
  simpa only [zpow_neg, zpow_natCast, div_pow, one_pow, gammaHeight] using hh

/-- The compact envelope sums over the entire source-by-order product. -/
theorem summable_liClockPairedEtaFirstPrefixGammaTaylorEnvelope
    (T : ℝ) (hT : 0 ≤ T) :
    Summable (fun p : ℕ × ℕ => (1 / (2 * (p.1 : ℝ) + 5 / 2) ^ 2) *
      (T ^ (2 * p.2 + 1) / ((2 * p.2 + 1).factorial : ℝ))) := by
  exact summable_liClockPairedEtaFirstPrefixGammaSquareMass.mul_of_nonneg
    (Real.hasSum_sinh T).summable (fun n => by positivity) (fun j => by positivity)

/-- The packet stays strictly below the removed first-prefix pole at every positive clock. -/
theorem liClockPairedEtaFirstPrefixGammaClock_re_lt_two_sinh {t : ℝ} (ht : 0 < t) :
    (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re < 2 * Real.sinh (2 * t) := by
  exact (liClockPairedEtaFirstPrefixGammaClock_re_lt_nine_fiftieths ht).trans
    (mul_lt_mul_of_pos_right (by norm_num : (9 / 50 : ℝ) < 2)
      (Real.sinh_pos_iff.mpr (by positivity)))

private theorem sinh_div_tendsto_zero_right (a : ℝ) :
    Tendsto (fun t : ℝ => Real.sinh (a * t) / t)
      (nhdsWithin 0 (Ioi 0)) (𝓝 a) := by
  have hd : HasDerivAt (fun t : ℝ => Real.sinh (a * t)) a 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).const_mul a).sinh using 1
    simp
  have hm : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhdsWithin 0 ({0}ᶜ) :=
    nhdsWithin_mono 0 (by intro x hx; simp only [mem_compl_iff, mem_singleton_iff]; exact ne_of_gt hx)
  simpa only [zero_add, mul_zero, Real.sinh_zero, sub_zero, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero.mono_left hm

/-- The complex growth coefficient is forced by the genuine zero-clock slope. -/
theorem liClockPairedEtaFirstPrefixGammaClock_sharp_norm_coefficient {B : ℝ}
    (hB : ∀ t : ℂ, ‖liClockPairedEtaFirstPrefixGammaClock t‖ ≤ B * Real.sinh ((2 / 5) * ‖t‖)) :
    5 * liClockPairedEtaFirstPrefixGammaSquareMass / 2 ≤ B := by
  have hl := liClockPairedEtaFirstPrefixGammaClock_re_div_tendsto_zero_right
  have hr := (sinh_div_tendsto_zero_right (2 / 5)).const_mul B
  have he : (fun t : ℝ => (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re / t) ≤ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun t => B * (Real.sinh ((2 / 5) * t) / t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have hh := (Complex.re_le_norm (liClockPairedEtaFirstPrefixGammaClock (t : ℂ))).trans (hB (t : ℂ))
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at hh
    have hd := div_le_div_of_nonneg_right hh ht.le
    convert! hd using 1
    first | rfl | ring
  have hh := le_of_tendsto_of_tendsto hl hr he
  linarith

/-- The two-sinh comparison coefficient is likewise forced by the right-hand slope. -/
theorem liClockPairedEtaFirstPrefixGammaClock_sharp_two_sinh_coefficient {B : ℝ}
    (hB : ∀ t : ℝ, 0 < t → (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re ≤ B * Real.sinh (2 * t)) :
    liClockPairedEtaFirstPrefixGammaSquareMass / 2 ≤ B := by
  have hl := liClockPairedEtaFirstPrefixGammaClock_re_div_tendsto_zero_right
  have hr := (sinh_div_tendsto_zero_right 2).const_mul B
  have he : (fun t : ℝ => (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re / t) ≤ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun t => B * (Real.sinh (2 * t) / t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have hd := div_le_div_of_nonneg_right (hB t ht) ht.le
    convert! hd using 1
    first | rfl | ring
  have hh := le_of_tendsto_of_tendsto hl hr he
  linarith

/-- The strict positive-clock envelope chain, including both calibrated mass fences. -/
theorem liClockPairedEtaFirstPrefixGammaClock_re_bounds {t : ℝ} (ht : 0 < t) :
    ((2 / 5) * Real.sinh ((2 / 5) * t) < (liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re) ∧
    ((liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re <
      (5 * liClockPairedEtaFirstPrefixGammaSquareMass / 2) * Real.sinh ((2 / 5) * t)) ∧
    ((5 * liClockPairedEtaFirstPrefixGammaSquareMass / 2) * Real.sinh ((2 / 5) * t) <
      (9 / 10) * Real.sinh ((2 / 5) * t)) ∧
    ((liClockPairedEtaFirstPrefixGammaClock (t : ℂ)).re <
      (liClockPairedEtaFirstPrefixGammaSquareMass / 2) * Real.sinh (2 * t)) ∧
    ((liClockPairedEtaFirstPrefixGammaSquareMass / 2) * Real.sinh (2 * t) <
      (9 / 50) * Real.sinh (2 * t)) := by
  have hm := liClockPairedEtaFirstPrefixGammaSquareMass_lt_nine_div_twenty_five
  refine ⟨liClockPairedEtaFirstPrefixGammaClock_re_gt_firstAtom ht,
    liClockPairedEtaFirstPrefixGammaClock_re_lt_mass_envelope ht, ?_,
    liClockPairedEtaFirstPrefixGammaClock_re_lt_two_sinh_mass ht, ?_⟩
  · exact mul_lt_mul_of_pos_right (by linarith)
      (Real.sinh_pos_iff.mpr (by positivity))
  · exact mul_lt_mul_of_pos_right (by linarith)
      (Real.sinh_pos_iff.mpr (by positivity))

end
end RHTower
