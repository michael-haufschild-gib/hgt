import GaloisForLFunctions.RHTower.Suzuki.SuzukiCorFourSix
import GaloisForLFunctions.RHTower.XiOrdinateCosineMass

/-!
# Removing damping from the Li tails

The exponentially damped Laguerre tail has transform
`1-(1-1/(ρ+ε))^n` at a zero `ρ`. Its reflected product is dominated,
uniformly in the real damping parameter, by a summable inverse-square
ordinate weight. Removing damping therefore recovers the paired Li coefficient.
-/

open Complex Filter Topology
open _root_.RHTower

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

/-- The Laguerre tail with additional exponential damping. -/
def dampedLiTestFun (n : ℕ) (ε x : ℝ) : ℂ :=
  suzukiLiTestFun n x * Complex.exp (-((ε : ℂ) * (x : ℂ)))

/-- Exponential damping shifts the Fourier variable vertically. -/
theorem suzukiEntireFourier_dampedLiTestFun_shift (n : ℕ) (ε : ℝ) (z : ℂ) :
    suzukiEntireFourier (dampedLiTestFun n ε) z =
      suzukiEntireFourier (suzukiLiTestFun n) (z + (ε : ℂ) * I) := by
  unfold suzukiEntireFourier dampedLiTestFun
  apply MeasureTheory.integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring_nf
    simp only [Complex.I_sq]
    ring

/-- The damped tail has the shifted Li resolvent as its transform. -/
theorem suzukiEntireFourier_dampedLiTestFun (n : ℕ) (ε : ℝ) {z : ℂ}
    (hz : -(1 / 2 : ℝ) < z.im + ε) :
    suzukiEntireFourier (dampedLiTestFun n ε) z =
      1 - (1 - 1 / (1 / 2 - I * z + (ε : ℂ))) ^ n := by
  rw [suzukiEntireFourier_dampedLiTestFun_shift,
    suzukiEntireFourier_liTestFun n (by simpa using hz)]
  have he : (1 : ℂ) / 2 - I * (z + (ε : ℂ) * I) = 1 / 2 - I * z + (ε : ℂ) := by
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [he]

/-- The zero summand of an exponentially damped Laguerre tail. -/
def dampedLiZeroTerm (n : ℕ) (ε : ℝ) (q : XiZeroCopy) : ℂ :=
  (1 - (1 - 1 / ((q.1 : ℂ) + (ε : ℂ))) ^ n) *
    (1 - (1 - 1 / (1 - (q.1 : ℂ) + (ε : ℂ))) ^ n)

/-- The spectral form of the damped Li tail. -/
def dampedLiWeilForm (n : ℕ) (ε : ℝ) : ℂ := ∑' q, dampedLiZeroTerm n ε q

/-- The rational summand is the actual reflected Fourier product of the damped tail. -/
theorem dampedLiZeroTerm_eq_fourier (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (q : XiZeroCopy) :
    dampedLiZeroTerm n ε q =
      suzukiEntireFourier (dampedLiTestFun n ε) (-xiSpectralPoint q) *
        (starRingEnd ℂ) (suzukiEntireFourier (dampedLiTestFun n ε)
          ((starRingEnd ℂ) (-xiSpectralPoint q))) := by
  obtain ⟨hlo, hhi⟩ := abs_im_xiSpectralPointSupport_lt q.1
  rw [xiSpectralPoint_eq_support]
  have hfirst : -(1 / 2 : ℝ) < (-xiSpectralPointSupport q.1).im + ε := by
    rw [Complex.neg_im]
    linarith only [hhi, hε]
  have hsecond : -(1 / 2 : ℝ) <
      ((starRingEnd ℂ) (-xiSpectralPointSupport q.1)).im + ε := by
    rw [Complex.conj_im, Complex.neg_im, neg_neg]
    linarith only [hlo, hε]
  rw [suzukiEntireFourier_dampedLiTestFun n ε hfirst,
    suzukiEntireFourier_dampedLiTestFun n ε hsecond,
    half_sub_I_mul_neg_spectral q.1,
    map_sub, map_one, map_pow, map_sub, map_one, map_div₀, map_one, map_add,
    conj_half_sub_I_mul_conj_neg_spectral q.1, Complex.conj_ofReal]
  rfl

private theorem norm_liFactor_le {s : ℂ} (hs : 1 ≤ ‖s‖) (n : ℕ) :
    ‖1 - (1 - 1 / s) ^ n‖ ≤ ((2 : ℝ) ^ n - 1) / ‖s‖ := by
  have hs0 : 0 < ‖s‖ := zero_lt_one.trans_le hs
  have hw : ‖1 - 1 / s‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (1 / s)
    rw [norm_one, norm_div, norm_one] at h
    have hi : 1 / ‖s‖ ≤ 1 := (div_le_one hs0).mpr hs
    linarith only [h, hi]
  induction n with
  | zero => simp
  | succ n ih =>
    have he : 1 - (1 - 1 / s) ^ (n + 1) =
        (1 - (1 - 1 / s) ^ n) + (1 - 1 / s) ^ n / s := by
      rw [pow_succ]
      ring
    rw [he]
    calc
      _ ≤ ‖1 - (1 - 1 / s) ^ n‖ + ‖(1 - 1 / s) ^ n / s‖ := norm_add_le _ _
      _ ≤ ((2 : ℝ) ^ n - 1) / ‖s‖ + (2 : ℝ) ^ n / ‖s‖ := by
        apply add_le_add ih
        rw [norm_div, norm_pow]
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw n) hs0.le
      _ = _ := by rw [pow_succ]; ring

/-- Inverse-square ordinate domination is uniform in the damping. -/
theorem norm_dampedLiZeroTerm_le (n : ℕ) (ε : ℝ) (q : XiZeroCopy) :
    ‖dampedLiZeroTerm n ε q‖ ≤
      ((2 : ℝ) ^ n - 1) ^ 2 * (1 / xiCopyOrdinate q ^ 2) := by
  have hγ := four_lt_abs_xiCopyOrdinate q
  have hγ0 : 0 < |xiCopyOrdinate q| := by linarith only [hγ]
  have hγ1 : 1 ≤ |xiCopyOrdinate q| := by linarith only [hγ]
  have hC : 0 ≤ (2 : ℝ) ^ n - 1 := sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  have hnorm (s : ℂ) (hs : |s.im| = |xiCopyOrdinate q|) :
      ‖1 - (1 - 1 / s) ^ n‖ ≤ ((2 : ℝ) ^ n - 1) / |xiCopyOrdinate q| := by
    have hg : |xiCopyOrdinate q| ≤ ‖s‖ := hs ▸ Complex.abs_im_le_norm s
    exact (norm_liFactor_le (hγ1.trans hg) n).trans
      (div_le_div_of_nonneg_left hC hγ0 hg)
  have hleft := hnorm ((q.1 : ℂ) + (ε : ℂ)) (by simp [xiCopyOrdinate])
  have hright := hnorm (1 - (q.1 : ℂ) + (ε : ℂ)) (by simp [xiCopyOrdinate])
  rw [dampedLiZeroTerm, norm_mul]
  refine (mul_le_mul hleft hright (norm_nonneg _) (by positivity)).trans_eq ?_
  rw [← sq, div_pow, sq_abs]
  ring

theorem summable_dampedLiZeroTerm (n : ℕ) (ε : ℝ) :
    Summable (dampedLiZeroTerm n ε) :=
  Summable.of_norm_bounded
    (summable_inv_sq_xiCopyOrdinate.mul_left (((2 : ℝ) ^ n - 1) ^ 2))
    (norm_dampedLiZeroTerm_le n ε)

/-- Each damped summand varies continuously with its real parameter. -/
theorem continuous_dampedLiZeroTerm (n : ℕ) (q : XiZeroCopy) :
    Continuous (fun ε : ℝ => dampedLiZeroTerm n ε q) := by
  have hleft (ε : ℝ) : (q.1 : ℂ) + (ε : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    exact xiCopyOrdinate_ne_zero q (by simpa [xiCopyOrdinate] using hi)
  have hright (ε : ℝ) : 1 - (q.1 : ℂ) + (ε : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    exact xiCopyOrdinate_ne_zero q (by simpa [xiCopyOrdinate] using hi)
  exact (continuous_const.sub ((continuous_const.sub
      (continuous_const.div (continuous_const.add Complex.continuous_ofReal) hleft)).pow n)).mul
    (continuous_const.sub ((continuous_const.sub
      (continuous_const.div (continuous_const.add Complex.continuous_ofReal) hright)).pow n))

/-- At zero damping the summand is exactly the paired Li summand. -/
theorem dampedLiZeroTerm_zero (n : ℕ) (q : XiZeroCopy) :
    dampedLiZeroTerm n 0 q = liTerm (xiRootW (q.1 : ℂ)) n := by
  have h0 : (q.1 : ℂ) ≠ 0 := by
    intro h
    exact xiCopyOrdinate_ne_zero q (by simp [xiCopyOrdinate, h])
  have h1 : (q.1 : ℂ) ≠ 1 := by
    intro h
    exact xiCopyOrdinate_ne_zero q (by simp [xiCopyOrdinate, h])
  have hw : xiRootW (q.1 : ℂ) ≠ 0 := xiRootW_ne_zero h0 h1
  have hc : xiRootW (q.1 : ℂ) ^ n * (xiRootW (q.1 : ℂ))⁻¹ ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hw, one_pow]
  simp only [dampedLiZeroTerm, Complex.ofReal_zero, add_zero]
  change (1 - xiRootW (q.1 : ℂ) ^ n) * (1 - xiRootW (1 - (q.1 : ℂ)) ^ n) = _
  rw [xiRootW_one_sub h0 h1, liTerm]
  linear_combination hc

/-- The spectral form at zero damping is the paired Li coefficient. -/
theorem dampedLiWeilForm_zero (n : ℕ) : dampedLiWeilForm n 0 = xiLiPaired n := by
  simp only [dampedLiWeilForm, dampedLiZeroTerm_zero]
  exact (hasSum_liTerm_xiZeroCopy n).tsum_eq

/-- Removing exponential damping recovers the paired Li coefficient. -/
theorem tendsto_dampedLiWeilForm (n : ℕ) :
    Tendsto (dampedLiWeilForm n) (𝓝 0) (𝓝 (xiLiPaired n)) := by
  rw [← dampedLiWeilForm_zero n]
  exact tendsto_tsum_of_dominated_convergence
    (summable_inv_sq_xiCopyOrdinate.mul_left (((2 : ℝ) ^ n - 1) ^ 2))
    (fun q => (continuous_dampedLiZeroTerm n q).tendsto 0)
    (Eventually.of_forall fun ε q => norm_dampedLiZeroTerm_le n ε q)

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
