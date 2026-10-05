import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitive
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockTopFrequency
import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius
import GaloisForLFunctions.RHTower.XiDivisorDiagonalTraceClass

/-!
# The maximal imaginary reciprocal frequency of the actual Xi clock

Let `w_q = 1/α_q` run over all multiplicity copies of the centered Xi zeros, `u_q = |Re w_q|`,
`v_q = |Im w_q|`, and `β = sup_q v_q`.

* `Σ_q |w_q|² = A > 0`, `|w_q|² < 1/150`, `v_q < 1/300` and `u_q > v_q`, `u_q > 0`;
* `0 ≤ β < 1/300`, and `β = 0` iff RH; if `β > 0` it is attained on a finite nonempty packet with a
  strict gap below `β` for every other copy;
* `P(t) = Σ_q [1 - cos(u_q t) cosh(v_q t)]` and `|P(t)| ≤ (A/2) t² e^{βt}` for `t ≥ 0`.
-/

open Set Filter Topology Complex

noncomputable section

namespace RHTower

local notation "v" => liEvenCrossActualClockReciprocalGrowthRate

/-- `u_q = |Re w_q|`. -/
def liEvenCrossActualClockReciprocalFrequency (q : XiZeroCopy) : ℝ :=
  |((xiSpectralPoint q)⁻¹).re|

local notation "u" => liEvenCrossActualClockReciprocalFrequency

/-! ## Atom geometry -/

theorem liEvenCrossActualClockReciprocalGrowthRate_lt (q : XiZeroCopy) : v q < 1 / 300 :=
  abs_im_inv_xiSpectralPoint_lt_one_div_threeHundred q

theorem norm_inv_xiSpectralPoint_sq_lt (q : XiZeroCopy) :
    ‖(xiSpectralPoint q)⁻¹‖ ^ 2 < 1 / 150 := by
  have h := norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q
  have e : ‖xiZeroCopyReciprocalSquare q‖ = ‖(xiSpectralPoint q)⁻¹‖ ^ 2 := by
    simp [xiZeroCopyReciprocalSquare, norm_pow]
  rwa [e] at h

/-- `u_q > v_q`: the real reciprocal coordinate dominates the imaginary one. -/
theorem liEvenCrossActualClockReciprocalGrowthRate_lt_frequency (q : XiZeroCopy) : v q < u q := by
  set α := xiSpectralPoint q
  have hre := fiveHundredNinetyNine_fourths_lt_xiSpectralPoint_re_sq q
  have him := xiSpectralPoint_im_mem_openHalf q
  have hα : α ≠ 0 := by
    intro h; rw [show xiSpectralPoint q = α from rfl, h] at hre; simp at hre; linarith
  have hn : 0 < Complex.normSq α := Complex.normSq_pos.2 hα
  unfold liEvenCrossActualClockReciprocalGrowthRate liEvenCrossActualClockReciprocalFrequency
  rw [Complex.inv_re, Complex.inv_im, abs_div, abs_div, abs_neg, abs_of_pos hn]
  refine div_lt_div_of_pos_right ?_ hn
  have h1 : |α.im| < 1 / 2 := abs_lt.2 ⟨by linarith [him.1], him.2⟩
  have h2 : (1 / 2 : ℝ) ^ 2 < α.re ^ 2 := by nlinarith
  have h3 : (1 / 2 : ℝ) < |α.re| := by
    rw [← sq_lt_sq₀ (by norm_num) (abs_nonneg _), sq_abs]; exact h2
  linarith

theorem liEvenCrossActualClockReciprocalFrequency_pos (q : XiZeroCopy) : 0 < u q :=
  (liEvenCrossActualClockReciprocalGrowthRate_nonneg q).trans_lt
    (liEvenCrossActualClockReciprocalGrowthRate_lt_frequency q)

private theorem re_cos_add_mul_I (a b : ℝ) :
    (Complex.cos ((a : ℂ) + (b : ℂ) * Complex.I)).re = Real.cos a * Real.cosh b := by
  rw [Complex.cos_add_mul_I]
  simp [Complex.cos_ofReal_re, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_sin]

/-- `Re(1 - cos(t w)) = 1 - cos(u t) cosh(v t)`. -/
theorem re_liEvenCrossActualClockCosineAtom (t : ℝ) (q : XiZeroCopy) :
    (liEvenCrossActualClockCosineAtom t q).re =
      1 - Real.cos (u q * t) * Real.cosh (v q * t) := by
  unfold liEvenCrossActualClockCosineAtom liEvenCrossActualClockReciprocalFrequency
    liEvenCrossActualClockReciprocalGrowthRate
  set w := (xiSpectralPoint q)⁻¹
  have e : (t : ℂ) * w = ((t * w.re : ℝ) : ℂ) + ((t * w.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [Complex.sub_re, Complex.one_re, e, re_cos_add_mul_I]
  congr 2
  · rw [← Real.cos_abs, abs_mul, mul_comm, ← Real.cos_abs (|w.re| * t), abs_mul, abs_abs]
  · rw [← Real.cosh_abs, abs_mul, mul_comm, ← Real.cosh_abs (|w.im| * t), abs_mul, abs_abs]

/-- **Full cosine–cosh decomposition (I1).** -/
theorem liEvenCrossActualClockPrimitive_eq_tsum_coshCos (t : ℝ) :
    liEvenCrossActualClockPrimitive t =
      ∑' q : XiZeroCopy, (1 - Real.cos (u q * t) * Real.cosh (v q * t)) := by
  have h := congrArg Complex.re (liEvenCrossActualClockPrimitive_ofReal_eq_tsum_cosine t)
  rw [Complex.ofReal_re, Complex.re_tsum (summable_norm_liEvenCrossActualClockCosineAtom t).of_norm] at h
  rw [h]
  exact tsum_congr fun q => re_liEvenCrossActualClockCosineAtom t q

/-! ## The maximal growth rate -/

theorem bddAbove_liEvenCrossActualClockReciprocalGrowthRate : BddAbove (range v) :=
  ⟨1 / 300, by rintro _ ⟨q, rfl⟩; exact (liEvenCrossActualClockReciprocalGrowthRate_lt q).le⟩

/-- `β = sup_q v_q`. -/
def liEvenCrossActualClockMaxGrowthRate : ℝ := ⨆ q : XiZeroCopy, v q

local notation "β" => liEvenCrossActualClockMaxGrowthRate

theorem liEvenCrossActualClockReciprocalGrowthRate_le_max (q : XiZeroCopy) : v q ≤ β :=
  le_ciSup bddAbove_liEvenCrossActualClockReciprocalGrowthRate q

theorem liEvenCrossActualClockMaxGrowthRate_nonneg : 0 ≤ β :=
  (liEvenCrossActualClockReciprocalGrowthRate_nonneg (Classical.choice nonempty_xiZeroCopy)).trans
    (liEvenCrossActualClockReciprocalGrowthRate_le_max _)

theorem liEvenCrossActualClockReciprocalGrowthRate_eq_zero_of_rh (hRH : RiemannHypothesis)
    (q : XiZeroCopy) : v q = 0 := by
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  unfold liEvenCrossActualClockReciprocalGrowthRate
  rw [ht, ← Complex.ofReal_inv, Complex.ofReal_im, abs_zero]

/-- **Top packet (I3).**  If `β > 0`, it is attained on a finite nonempty packet and every other
copy lies at most at some `β₂ < β`. -/
theorem liEvenCrossActualClockMaxGrowthRate_top_of_not_rh (hnot : ¬RiemannHypothesis) :
    0 < β ∧ (liEvenCrossActualClockTopPacket β).Finite ∧
      (liEvenCrossActualClockTopPacket β).Nonempty ∧
      ∃ b₂ : ℝ, 0 ≤ b₂ ∧ b₂ < β ∧ ∀ q, q ∉ liEvenCrossActualClockTopPacket β → v q ≤ b₂ := by
  obtain ⟨b, hb, hfin, hne, hle, b₂, hb₂, hb₂b, hgap⟩ :=
    exists_liEvenCrossActualClockTopPacket_of_not_rh hnot
  have hβ : β = b := by
    apply le_antisymm (ciSup_le hle)
    obtain ⟨q, hq⟩ := hne
    rw [← show v q = b from hq]
    exact liEvenCrossActualClockReciprocalGrowthRate_le_max q
  rw [hβ]
  exact ⟨hb, hfin, hne, b₂, hb₂, hb₂b, hgap⟩

/-- `β = 0` iff RH. -/
theorem liEvenCrossActualClockMaxGrowthRate_eq_zero_iff : β = 0 ↔ RiemannHypothesis := by
  constructor
  · intro h
    by_contra hnot
    have := (liEvenCrossActualClockMaxGrowthRate_top_of_not_rh hnot).1
    linarith
  · intro hRH
    apply le_antisymm _ liEvenCrossActualClockMaxGrowthRate_nonneg
    exact ciSup_le fun q => (liEvenCrossActualClockReciprocalGrowthRate_eq_zero_of_rh hRH q).le

/-- `β < 1/300`. -/
theorem liEvenCrossActualClockMaxGrowthRate_lt : β < 1 / 300 := by
  by_cases hRH : RiemannHypothesis
  · rw [liEvenCrossActualClockMaxGrowthRate_eq_zero_iff.2 hRH]; norm_num
  · obtain ⟨_, _, ⟨q, hq⟩, _⟩ := liEvenCrossActualClockMaxGrowthRate_top_of_not_rh hRH
    rw [← show v q = β from hq]
    exact liEvenCrossActualClockReciprocalGrowthRate_lt q

theorem liEvenCrossActualClockMaxGrowthRate_lt_of_lt {p : ℝ} (hp : 1 / 300 < p) : β < p :=
  liEvenCrossActualClockMaxGrowthRate_lt.trans hp

/-! ## The sharpened quadratic envelope -/

theorem tsum_norm_inv_xiSpectralPoint_sq :
    ∑' q : XiZeroCopy, ‖(xiSpectralPoint q)⁻¹‖ ^ 2 = xiShiftAbsoluteMass 0 := by
  simp [xiShiftAbsoluteMass, xiZeroCopyReciprocalSquare, norm_pow]

/-- **Sharpened envelope (I4).**  `|P(t)| ≤ (A/2) t² e^{βt}` for `t ≥ 0`. -/
theorem abs_liEvenCrossActualClockPrimitive_le_max {t : ℝ} (ht : 0 ≤ t) :
    |liEvenCrossActualClockPrimitive t| ≤ xiShiftAbsoluteMass 0 * t ^ 2 / 2 * Real.exp (β * t) := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, liEvenCrossActualClockPrimitive_ofReal_eq_tsum_cosine]
  have hb (q : XiZeroCopy) : ‖liEvenCrossActualClockCosineAtom t q‖ ≤
      ‖(xiSpectralPoint q)⁻¹‖ ^ 2 * (t ^ 2 / 2 * Real.exp (β * t)) := by
    have h := liClock_norm_one_sub_cos_le_imaginary_exp t (xiSpectralPoint q)⁻¹
    have he : Real.exp (|t| * |((xiSpectralPoint q)⁻¹).im|) ≤ Real.exp (β * t) := by
      rw [abs_of_nonneg ht, mul_comm]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
        (liEvenCrossActualClockReciprocalGrowthRate_le_max q) ht)
    exact h.trans ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring))
  calc ‖∑' q : XiZeroCopy, liEvenCrossActualClockCosineAtom t q‖ ≤
      ∑' q : XiZeroCopy, ‖liEvenCrossActualClockCosineAtom t q‖ :=
        norm_tsum_le_tsum_norm (summable_norm_liEvenCrossActualClockCosineAtom t)
    _ ≤ ∑' q : XiZeroCopy, ‖(xiSpectralPoint q)⁻¹‖ ^ 2 * (t ^ 2 / 2 * Real.exp (β * t)) :=
        (summable_norm_liEvenCrossActualClockCosineAtom t).tsum_le_tsum hb
          (summable_norm_inv_xiSpectralPoint_sq.mul_right _)
    _ = _ := by rw [tsum_mul_right, tsum_norm_inv_xiSpectralPoint_sq]; ring

end RHTower
