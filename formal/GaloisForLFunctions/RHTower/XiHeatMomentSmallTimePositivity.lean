import GaloisForLFunctions.RHTower.XiGaussianHeatArchPrimeHankel
import GaloisForLFunctions.RHTower.LorentzianZeroMass
import GaloisForLFunctions.RHTower.XiLogDerivLineOneWindowLower
import GaloisForLFunctions.RHTower.XiHedenmalmMultiplicityChain
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLinearWindow
import GaloisForLFunctions.RHTower.XiOrdinateCosineMass
import GaloisForLFunctions.HTGeometry.GammaVerticalSharpBound

/-!
# Complete monotonicity of the zero heat trace at small heat time

**Theorem** (`exists_heatMoment_re_pos_small_time`).  There is `a₀ > 0` such that every heat moment
`M_n(a) = Σ_q w_q^n e^{−a w_q}` is positive for `0 < a ≤ a₀` and all `n ≥ 0`.  Equivalently the real
zero heat trace `ν(a) = Σ_q e^{−a w_q}` is completely monotone on `(0, a₀]`, with no hypothesis on
the zeros.  Complete monotonicity on `(0, ∞)` is RH
(`riemannHypothesis_iff_completelyMonotoneOn_xiGaussianHeatTraceReal`), so the moment criterion
carries no information at small heat time.

Mechanism (phase locking).  For a copy `z = t + iδ` with `w = z²`,
`Re(w^n e^{−aw}) = |w|^n e^{−a Re w} cos θ` with `θ = 2n arctan(δ/t) − 2atδ`.  At the peak
`t₀ = √(n/a)` of the profile `t^{2n} e^{−at²}` the two parts of `θ` cancel to first order:
`|θ| ≤ |n/t − at| + n/(8t³)` and `n/t − at = a(t₀² − t²)/t` (`abs_heatPhase_le`).  An off-line copy is
therefore positive on the whole window `|t − t₀| ≤ 1/(4a)`, whatever its depth.  Outside it the
profile is Gaussian small (`pow_mul_exp_le_peak`).

* The window `(t₀ − h, t₀ + h]` holds at least `log t₀` copies (Riemann–von Mangoldt,
  `exists_xiZeroCount_window_ge_log`), each contributing at least half the peak value
  (`peak_le_pow_mul_exp`).
* Far copies are weighed by the Lorentzian zero mass `Σ_ρ 1/(1 + (t₀ − γ)²) ≤ 8(A + log(t₀ + 4))`
  (`lorentzMass_le_log`); their Gaussian factor is `O(a)`.
* Low copies (`|γ| < 4n`, or `|γ| < t₀/2` when `n ≳ 1/a`) are smaller than the peak by `e^{−n/4}`,
  resp. `e^{−n/16}`.
* `n = 0` is the order-one case of the linear window (`heatMomentDet_pos_of_mul_le`).
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Arctangent and the heat phase -/

/-- `x − x³/2 ≤ arctan x` for `x ≥ 0`: `arctan x ≥ sin(arctan x) = x/√(1+x²)`. -/
theorem sub_cube_div_two_le_arctan {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 2 ≤ Real.arctan x := by
  have hs : Real.sin (Real.arctan x) ≤ Real.arctan x := Real.sin_le (Real.arctan_nonneg.2 hx)
  rw [Real.sin_arctan] at hs
  have hsq : Real.sqrt (1 + x ^ 2) ≤ 1 + x ^ 2 / 2 :=
    (Real.sqrt_le_left (by positivity)).2 (by nlinarith [sq_nonneg (x ^ 2)])
  have hpos : 0 < Real.sqrt (1 + x ^ 2) := by positivity
  have h1 : x / (1 + x ^ 2 / 2) ≤ x / Real.sqrt (1 + x ^ 2) :=
    div_le_div_of_nonneg_left hx hpos hsq
  have h2 : x - x ^ 3 / 2 ≤ x / (1 + x ^ 2 / 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_nonneg hx 5]
  linarith

theorem abs_sub_arctan_le (x : ℝ) : |x - Real.arctan x| ≤ |x| ^ 3 / 2 := by
  rcases le_total 0 x with hx | hx
  · have h1 := GaloisForLFunctions.HTGeometry.arctan_le_self_of_nonneg hx
    have h2 := sub_cube_div_two_le_arctan hx
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hx]
    linarith
  · have hx' : 0 ≤ -x := by linarith
    have h1 := GaloisForLFunctions.HTGeometry.arctan_le_self_of_nonneg hx'
    have h2 := sub_cube_div_two_le_arctan hx'
    rw [Real.arctan_neg] at h1 h2
    rw [abs_of_nonpos (by linarith), abs_of_nonpos hx]
    linarith

/-- **The heat phase is locked at the peak.**  For `t > 0` and `|δ| ≤ 1/2`,
`|2n arctan(δ/t) − 2atδ| ≤ |n/t − at| + n/(8t³)`. -/
theorem abs_heatPhase_le {t δ a : ℝ} (n : ℕ) (ht : 0 < t) (hδ : |δ| ≤ 1 / 2) :
    |2 * n * Real.arctan (δ / t) - 2 * a * t * δ| ≤ |n / t - a * t| + n / (8 * t ^ 3) := by
  have hx := abs_sub_arctan_le (δ / t)
  have key : 2 * n * Real.arctan (δ / t) - 2 * a * t * δ =
      2 * δ * (n / t - a * t) - 2 * n * (δ / t - Real.arctan (δ / t)) := by
    field_simp
    ring
  rw [key]
  have h1 : |2 * δ * (n / t - a * t)| ≤ |n / t - a * t| := by
    rw [abs_mul, abs_mul, abs_two]
    have := abs_nonneg (n / t - a * t)
    nlinarith
  have hcube : |δ / t| ^ 3 ≤ 1 / (8 * t ^ 3) := by
    rw [abs_div, abs_of_pos ht, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 := abs_nonneg δ
    have : |δ| ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ h0 hδ 3
    nlinarith [pow_pos ht 3]
  have h2 : |2 * n * (δ / t - Real.arctan (δ / t))| ≤ n / (8 * t ^ 3) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * n)]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc 2 * n * |δ / t - Real.arctan (δ / t)| ≤ 2 * n * (|δ / t| ^ 3 / 2) :=
          mul_le_mul_of_nonneg_left hx (by positivity)
      _ = n * |δ / t| ^ 3 := by ring
      _ ≤ n * (1 / (8 * t ^ 3)) := mul_le_mul_of_nonneg_left hcube hn
      _ = n / (8 * t ^ 3) := by ring
  calc |2 * δ * (n / t - a * t) - 2 * n * (δ / t - Real.arctan (δ / t))|
      ≤ |2 * δ * (n / t - a * t)| + |2 * n * (δ / t - Real.arctan (δ / t))| := abs_sub _ _
    _ ≤ |n / t - a * t| + n / (8 * t ^ 3) := add_le_add h1 h2

/-! ## Polar form of a heat term -/

theorem norm_sq_pow_mul_exp (z : ℂ) (a : ℝ) (n : ℕ) :
    ‖(z ^ 2) ^ n * Complex.exp (-(a : ℂ) * z ^ 2)‖ =
      ‖z‖ ^ (2 * n) * Real.exp (-(a * (z ^ 2).re)) := by
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_exp, ← pow_mul]
  congr 2
  simp

theorem re_sq_pow_mul_exp (z : ℂ) (a : ℝ) (n : ℕ) :
    ((z ^ 2) ^ n * Complex.exp (-(a : ℂ) * z ^ 2)).re =
      ‖z‖ ^ (2 * n) * Real.exp (-(a * (z ^ 2).re)) *
        Real.cos (2 * n * Complex.arg z - a * (z ^ 2).im) := by
  have h1 : (z ^ 2) ^ n =
      ((‖z‖ ^ (2 * n) : ℝ) : ℂ) * Complex.exp (((2 * n * Complex.arg z : ℝ) : ℂ) * I) := by
    rw [← pow_mul]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have h2 : Complex.exp (-(a : ℂ) * z ^ 2) =
      ((Real.exp (-(a * (z ^ 2).re)) : ℝ) : ℂ) *
        Complex.exp (((-(a * (z ^ 2).im) : ℝ) : ℂ) * I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;> simp
  rw [h1, h2]
  have h3 : ((‖z‖ ^ (2 * n) : ℝ) : ℂ) * Complex.exp (((2 * n * Complex.arg z : ℝ) : ℂ) * I) *
      (((Real.exp (-(a * (z ^ 2).re)) : ℝ) : ℂ) *
        Complex.exp (((-(a * (z ^ 2).im) : ℝ) : ℂ) * I)) =
      ((‖z‖ ^ (2 * n) * Real.exp (-(a * (z ^ 2).re)) : ℝ) : ℂ) *
        Complex.exp (((2 * n * Complex.arg z - a * (z ^ 2).im : ℝ) : ℂ) * I) := by
    rw [show ((2 * n * Complex.arg z - a * (z ^ 2).im : ℝ) : ℂ) * I =
        ((2 * n * Complex.arg z : ℝ) : ℂ) * I + ((-(a * (z ^ 2).im) : ℝ) : ℂ) * I by
          push_cast; ring, Complex.exp_add]
    push_cast
    ring
  rw [h3, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- **Polar form with the locked phase.**  For `Re z > 0`, the heat term is its modulus times
`cos(2n arctan(δ/t) − 2atδ)` with `t = Re z`, `δ = Im z`. -/
theorem re_sq_pow_mul_exp_of_re_pos {z : ℂ} (hz : 0 < z.re) (a : ℝ) (n : ℕ) :
    ((z ^ 2) ^ n * Complex.exp (-(a : ℂ) * z ^ 2)).re =
      ‖(z ^ 2) ^ n * Complex.exp (-(a : ℂ) * z ^ 2)‖ *
        Real.cos (2 * n * Real.arctan (z.im / z.re) - 2 * a * z.re * z.im) := by
  rw [re_sq_pow_mul_exp, norm_sq_pow_mul_exp, arg_eq_arctan_of_re_pos hz]
  congr 2
  have : (z ^ 2).im = 2 * z.re * z.im := by rw [pow_two, Complex.mul_im]; ring
  rw [this]
  ring

/-! ## The peak profile -/

/-- **Gaussian decay away from the peak.**  If `a t₀² = n` with `t₀ > 0`, then for `u ≥ 0`,
`u^n e^{−au} ≤ t₀^{2n} e^{−n} e^{−a(√u − t₀)²}`. -/
theorem pow_mul_exp_le_peak {a t₀ u : ℝ} {n : ℕ} (ht₀ : 0 < t₀) (hn : a * t₀ ^ 2 = n)
    (hu : 0 ≤ u) :
    u ^ n * Real.exp (-(a * u)) ≤
      (t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) * Real.exp (-(a * (Real.sqrt u - t₀) ^ 2)) := by
  obtain ⟨v, hv0, hvu⟩ : ∃ v : ℝ, 0 ≤ v ∧ u = v ^ 2 :=
    ⟨Real.sqrt u, Real.sqrt_nonneg u, (Real.sq_sqrt hu).symm⟩
  rw [hvu, Real.sqrt_sq hv0]
  have hs : v / t₀ ≤ Real.exp (v / t₀ - 1) := by
    have := Real.add_one_le_exp (v / t₀ - 1)
    linarith
  have hs0 : 0 ≤ v / t₀ := div_nonneg hv0 ht₀.le
  have hpow : ((v / t₀) ^ 2) ^ n ≤ (Real.exp (v / t₀ - 1) ^ 2) ^ n :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hs0 hs 2) n
  have hexp : (Real.exp (v / t₀ - 1) ^ 2) ^ n = Real.exp (2 * a * t₀ * v - 2 * n) := by
    rw [← pow_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    rw [← hn]
    field_simp
  have hsplit : (v ^ 2) ^ n = (t₀ ^ 2) ^ n * ((v / t₀) ^ 2) ^ n := by
    rw [← mul_pow, div_pow, mul_div_cancel₀ _ (by positivity)]
  rw [hsplit]
  calc (t₀ ^ 2) ^ n * ((v / t₀) ^ 2) ^ n * Real.exp (-(a * v ^ 2))
      ≤ (t₀ ^ 2) ^ n * Real.exp (2 * a * t₀ * v - 2 * n) * Real.exp (-(a * v ^ 2)) := by
        rw [← hexp]
        gcongr
    _ = (t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) * Real.exp (-(a * (v - t₀) ^ 2)) := by
        rw [mul_assoc ((t₀ ^ 2) ^ n), mul_assoc ((t₀ ^ 2) ^ n), ← Real.exp_add, ← Real.exp_add]
        congr 2
        rw [← hn]
        ring

/-- **The profile near the peak.**  If `a t₀² = n` with `t₀ > 0`, then for `t > 0`,
`t₀^{2n} e^{−n} e^{−a(t² − t₀²)²/t²} ≤ t^{2n} e^{−at²}`. -/
theorem peak_le_pow_mul_exp {a t₀ t : ℝ} {n : ℕ} (ht₀ : 0 < t₀) (hn : a * t₀ ^ 2 = n)
    (ht : 0 < t) :
    (t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) * Real.exp (-(a * (t ^ 2 - t₀ ^ 2) ^ 2 / t ^ 2)) ≤
      (t ^ 2) ^ n * Real.exp (-(a * t ^ 2)) := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = t ^ 2 / t₀ ^ 2 := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; positivity
  have ht2 : t ^ 2 = t₀ ^ 2 * y := by rw [hy]; field_simp
  -- `e^{1 − 1/y} ≤ y`
  have hkey : Real.exp (1 - 1 / y) ≤ y := by
    have h := Real.add_one_le_exp (1 / y - 1)
    have hpos : 0 < Real.exp (1 / y - 1) := Real.exp_pos _
    have h' : 1 / y ≤ Real.exp (1 / y - 1) := by linarith
    have hinv : Real.exp (1 - 1 / y) = (Real.exp (1 / y - 1))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [hinv, inv_le_comm₀ hpos hy0, ← one_div]
    exact h'
  have hpow : Real.exp (1 - 1 / y) ^ n ≤ y ^ n := pow_le_pow_left₀ (Real.exp_pos _).le hkey n
  rw [← Real.exp_nat_mul] at hpow
  have hlhs : Real.exp (-(n : ℝ)) * Real.exp (-(a * (t ^ 2 - t₀ ^ 2) ^ 2 / t ^ 2)) =
      Real.exp (n * (1 - 1 / y)) * Real.exp (-(a * t ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [ht2, ← hn]
    field_simp
    ring
  rw [mul_assoc, hlhs, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [ht2, mul_pow]
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-! ## Heat terms of zero copies -/

/-- The heat term `w_q^n e^{−a w_q}` of a zero copy. -/
def xiHeatTerm (n : ℕ) (a : ℝ) (q : XiZeroCopy) : ℂ :=
  xiHeatFrequency q ^ n * Complex.exp (-(a : ℂ) * xiHeatFrequency q)

theorem xiSpectralPoint_re_eq_ordinate (q : XiZeroCopy) :
    (xiSpectralPoint q).re = xiCopyOrdinate q := by
  simp [xiSpectralPoint, xiCopyOrdinate, Complex.mul_re]

theorem abs_xiSpectralPoint_im_le (q : XiZeroCopy) : |(xiSpectralPoint q).im| ≤ 1 / 2 := by
  have h := xiSpectralPoint_im_sq_lt_quarter q
  have h' : (xiSpectralPoint q).im ^ 2 ≤ (1 / 2) ^ 2 := by linarith
  exact abs_le.2 (abs_le_of_sq_le_sq' h' (by norm_num))

theorem norm_xiHeatTerm (n : ℕ) (a : ℝ) (q : XiZeroCopy) :
    ‖xiHeatTerm n a q‖ = (xiCopyOrdinate q ^ 2 + (xiSpectralPoint q).im ^ 2) ^ n *
      Real.exp (-(a * (xiCopyOrdinate q ^ 2 - (xiSpectralPoint q).im ^ 2))) := by
  rw [xiHeatTerm, xiHeatFrequency, norm_sq_pow_mul_exp, pow_mul, Complex.sq_norm,
    Complex.normSq_apply, ← xiSpectralPoint_re_eq_ordinate]
  congr 2
  · ring
  · rw [pow_two, Complex.mul_re]
    ring

/-- **Polar form of a copy's heat term**, with the ordinate oriented to be positive. -/
theorem exists_xiHeatTerm_re_eq (n : ℕ) (a : ℝ) (q : XiZeroCopy) :
    ∃ δ : ℝ, |δ| ≤ 1 / 2 ∧ (xiHeatTerm n a q).re = ‖xiHeatTerm n a q‖ *
      Real.cos (2 * n * Real.arctan (δ / |xiCopyOrdinate q|) -
        2 * a * |xiCopyOrdinate q| * δ) := by
  have hre : (xiSpectralPoint q).re ≠ 0 := by
    rw [xiSpectralPoint_re_eq_ordinate]
    exact xiSupport_im_ne_zero q.1
  obtain ⟨z', hsq, hre', him'⟩ : ∃ z' : ℂ, z' ^ 2 = xiSpectralPoint q ^ 2 ∧
      z'.re = |(xiSpectralPoint q).re| ∧ |z'.im| = |(xiSpectralPoint q).im| := by
    rcases lt_or_gt_of_ne hre with h | h
    · exact ⟨-xiSpectralPoint q, by ring, by simp [abs_of_neg h], by simp⟩
    · exact ⟨xiSpectralPoint q, rfl, by simp [abs_of_pos h], rfl⟩
  have hpos : 0 < z'.re := by rw [hre']; exact abs_pos.2 hre
  refine ⟨z'.im, by rw [him']; exact abs_xiSpectralPoint_im_le q, ?_⟩
  have hT : xiHeatTerm n a q = (z' ^ 2) ^ n * Complex.exp (-(a : ℂ) * z' ^ 2) := by
    rw [xiHeatTerm, xiHeatFrequency, hsq]
  rw [hT, re_sq_pow_mul_exp_of_re_pos hpos, hre', xiSpectralPoint_re_eq_ordinate]

/-- The modulus of a heat term is at most the peak value times a Gaussian in `√(γ² + ¼) − t₀`. -/
theorem norm_xiHeatTerm_le_peak {n : ℕ} {a t₀ : ℝ} (ha : 0 < a) (ht₀ : 0 < t₀)
    (hn : a * t₀ ^ 2 = n) (q : XiZeroCopy) :
    ‖xiHeatTerm n a q‖ ≤ Real.exp (a / 2) * ((t₀ ^ 2) ^ n * Real.exp (-(n : ℝ))) *
      Real.exp (-(a * (Real.sqrt (xiCopyOrdinate q ^ 2 + 1 / 4) - t₀) ^ 2)) := by
  rw [norm_xiHeatTerm]
  set γ := xiCopyOrdinate q
  set ε := (xiSpectralPoint q).im
  have hε : ε ^ 2 ≤ 1 / 4 := (xiSpectralPoint_im_sq_lt_quarter q).le
  have h1 : (γ ^ 2 + ε ^ 2) ^ n ≤ (γ ^ 2 + 1 / 4) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  have h2 : Real.exp (-(a * (γ ^ 2 - ε ^ 2))) ≤
      Real.exp (a / 2) * Real.exp (-(a * (γ ^ 2 + 1 / 4))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  have hpk := pow_mul_exp_le_peak ht₀ hn (u := γ ^ 2 + 1 / 4) (by positivity)
  calc (γ ^ 2 + ε ^ 2) ^ n * Real.exp (-(a * (γ ^ 2 - ε ^ 2)))
      ≤ (γ ^ 2 + 1 / 4) ^ n * (Real.exp (a / 2) * Real.exp (-(a * (γ ^ 2 + 1 / 4)))) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    _ = Real.exp (a / 2) * ((γ ^ 2 + 1 / 4) ^ n * Real.exp (-(a * (γ ^ 2 + 1 / 4)))) := by ring
    _ ≤ Real.exp (a / 2) * ((t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) *
          Real.exp (-(a * (Real.sqrt (γ ^ 2 + 1 / 4) - t₀) ^ 2))) :=
        mul_le_mul_of_nonneg_left hpk (Real.exp_pos _).le
    _ = _ := by ring

theorem sqrt_sq_add_quarter_bounds (γ : ℝ) :
    |γ| ≤ Real.sqrt (γ ^ 2 + 1 / 4) ∧ Real.sqrt (γ ^ 2 + 1 / 4) ≤ |γ| + 1 / 2 := by
  constructor
  · rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  · rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs γ, abs_nonneg γ]

/-- The Lorentzian masses at `±t₀` together dominate `1/(1 + (|γ| − t₀)²)`. -/
theorem one_div_le_lorentzMassTerm_add (t₀ : ℝ) (q : XiZeroCopy) :
    1 / (1 + (|xiCopyOrdinate q| - t₀) ^ 2) ≤
      lorentzMassTerm t₀ q + lorentzMassTerm (-t₀) q := by
  have h1 := lorentzMassTerm_nonneg t₀ q
  have h2 := lorentzMassTerm_nonneg (-t₀) q
  have hγ' : ((q.1 : ℂ)).im = xiCopyOrdinate q := rfl
  unfold lorentzMassTerm at h1 h2 ⊢
  rw [hγ'] at h1 h2 ⊢
  rcases le_or_gt 0 (xiCopyOrdinate q) with hγ | hγ
  · rw [abs_of_nonneg hγ]
    have : (xiCopyOrdinate q - t₀) ^ 2 = (t₀ - xiCopyOrdinate q) ^ 2 := by ring
    rw [this]
    linarith
  · rw [abs_of_neg hγ]
    have : (-xiCopyOrdinate q - t₀) ^ 2 = (-t₀ - xiCopyOrdinate q) ^ 2 := by ring
    rw [this]
    linarith

/-! ## The four regimes of a heat term -/

/-- **Window copies.**  A copy with ordinate in `(t₀ − h, t₀ + h]` contributes at least half the
peak value. -/
theorem xiHeatTerm_re_ge_half_peak {n : ℕ} {a t₀ h : ℝ} (ha : 0 < a) (ht₀ : 0 < t₀)
    (hn : a * t₀ ^ 2 = n) (hh : 0 ≤ h) (ht₀h : 4 * h ≤ t₀) (ht₀1 : 1 ≤ t₀)
    (hph : 3 * a * h + a ≤ 1 / 2) (hgauss : 18 * a * h ^ 2 ≤ 1) {q : XiZeroCopy}
    (hq1 : t₀ - h < xiCopyOrdinate q) (hq2 : xiCopyOrdinate q ≤ t₀ + h) :
    (t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) / 2 ≤ (xiHeatTerm n a q).re := by
  set γ := xiCopyOrdinate q with hγdef
  have hγpos : 0 < γ := by linarith
  have hγhalf : t₀ / 2 ≤ γ := by linarith
  have hdist : |t₀ - γ| ≤ h := abs_le.2 ⟨by linarith, by linarith⟩
  obtain ⟨δ, hδ, hre⟩ := exists_xiHeatTerm_re_eq n a q
  rw [← hγdef, abs_of_pos hγpos] at hre
  have hphase : |2 * n * Real.arctan (δ / γ) - 2 * a * γ * δ| ≤ 1 / 2 := by
    refine (abs_heatPhase_le (a := a) n hγpos hδ).trans ?_
    have h1 : |(n : ℝ) / γ - a * γ| ≤ 3 * a * h := by
      rw [← hn, show a * t₀ ^ 2 / γ - a * γ = a * (t₀ - γ) * (t₀ + γ) / γ by
        field_simp; ring]
      rw [abs_div, abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hγpos,
        abs_of_pos (by linarith : 0 < t₀ + γ), div_le_iff₀ hγpos]
      have h3 : t₀ + γ ≤ 3 * γ := by linarith
      calc a * |t₀ - γ| * (t₀ + γ) ≤ a * h * (3 * γ) := by gcongr
        _ = 3 * a * h * γ := by ring
    have h2 : (n : ℝ) / (8 * γ ^ 3) ≤ a := by
      rw [← hn, div_le_iff₀ (by positivity)]
      have h8 : t₀ ^ 3 ≤ 8 * γ ^ 3 := by
        have := pow_le_pow_left₀ (by positivity) hγhalf 3
        nlinarith
      have h9 : t₀ ^ 2 ≤ t₀ ^ 3 := by nlinarith
      nlinarith
    linarith
  have hcos : 7 / 8 ≤ Real.cos (2 * n * Real.arctan (δ / γ) - 2 * a * γ * δ) := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := 2 * n * Real.arctan (δ / γ) - 2 * a * γ * δ)
    have hsq : (2 * n * Real.arctan (δ / γ) - 2 * a * γ * δ) ^ 2 ≤ 1 / 4 := by
      rw [← sq_abs]
      have := abs_nonneg (2 * n * Real.arctan (δ / γ) - 2 * a * γ * δ)
      nlinarith
    linarith
  have hnorm : (t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) * Real.exp (-(1 / 2)) ≤
      ‖xiHeatTerm n a q‖ := by
    rw [norm_xiHeatTerm, ← hγdef]
    set ε := (xiSpectralPoint q).im
    have hpk := peak_le_pow_mul_exp ht₀ hn hγpos
    have hg : (γ ^ 2 - t₀ ^ 2) ^ 2 / γ ^ 2 ≤ 9 * h ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have h3 : (γ + t₀) ^ 2 ≤ (3 * γ) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      have h4 : (γ - t₀) ^ 2 ≤ h ^ 2 := by
        rw [← sq_abs, abs_sub_comm]
        exact pow_le_pow_left₀ (abs_nonneg _) hdist 2
      have : (γ ^ 2 - t₀ ^ 2) ^ 2 = (γ - t₀) ^ 2 * (γ + t₀) ^ 2 := by ring
      rw [this]
      calc (γ - t₀) ^ 2 * (γ + t₀) ^ 2 ≤ h ^ 2 * (3 * γ) ^ 2 :=
            mul_le_mul h4 h3 (sq_nonneg _) (sq_nonneg _)
        _ = 9 * h ^ 2 * γ ^ 2 := by ring
    have hexp : Real.exp (-(1 / 2)) ≤ Real.exp (-(a * (γ ^ 2 - t₀ ^ 2) ^ 2 / γ ^ 2)) := by
      apply Real.exp_le_exp.2
      rw [mul_div_assoc]
      nlinarith
    have hlow : (γ ^ 2) ^ n * Real.exp (-(a * γ ^ 2)) ≤
        (γ ^ 2 + ε ^ 2) ^ n * Real.exp (-(a * (γ ^ 2 - ε ^ 2))) := by
      apply mul_le_mul (pow_le_pow_left₀ (by positivity) (by nlinarith) n)
        (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le (by positivity)
    calc (t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) * Real.exp (-(1 / 2))
        ≤ (t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) *
            Real.exp (-(a * (γ ^ 2 - t₀ ^ 2) ^ 2 / γ ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ _ := hpk.trans hlow
  have hhalf : 4 / 7 ≤ Real.exp (-(1 / 2)) := by
    have he : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have he1 := Real.exp_one_lt_d9
    have hpos := Real.exp_pos (1 / 2)
    have hlt : Real.exp (1 / 2) ≤ 7 / 4 := by nlinarith
    rw [Real.exp_neg, le_inv_comm₀ (by norm_num) hpos]
    linarith
  rw [hre]
  have hF : 0 ≤ (t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) := by positivity
  have hN := norm_nonneg (xiHeatTerm n a q)
  nlinarith

/-- **Near copies are nonnegative.**  If `|γ| ≥ t₀/2` and `||γ| − t₀| ≤ 1/(4a)`, the locked phase
stays in `[−1, 1]`. -/
theorem xiHeatTerm_re_nonneg_of_near {n : ℕ} {a t₀ : ℝ} (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (ht₀ : 1 ≤ t₀) (hn : a * t₀ ^ 2 = n) {q : XiZeroCopy}
    (h1 : t₀ / 2 ≤ |xiCopyOrdinate q|) (h2 : |(|xiCopyOrdinate q| - t₀)| ≤ 1 / (4 * a)) :
    0 ≤ (xiHeatTerm n a q).re := by
  set t := |xiCopyOrdinate q| with htdef
  have htpos : 0 < t := by linarith
  obtain ⟨δ, hδ, hre⟩ := exists_xiHeatTerm_re_eq n a q
  rw [← htdef] at hre
  have hphase : |2 * n * Real.arctan (δ / t) - 2 * a * t * δ| ≤ 1 := by
    refine (abs_heatPhase_le (a := a) n htpos hδ).trans ?_
    have hA : |(n : ℝ) / t - a * t| ≤ 3 / 4 := by
      rw [← hn, show a * t₀ ^ 2 / t - a * t = a * (t₀ - t) * (t₀ + t) / t by field_simp; ring]
      rw [abs_div, abs_mul, abs_mul, abs_of_pos ha, abs_of_pos htpos,
        abs_of_pos (by linarith : 0 < t₀ + t), div_le_iff₀ htpos]
      have h3 : t₀ + t ≤ 3 * t := by linarith
      have h4 : |t₀ - t| ≤ 1 / (4 * a) := by rw [abs_sub_comm]; exact h2
      have h5 : a * |t₀ - t| ≤ 1 / 4 := by
        calc a * |t₀ - t| ≤ a * (1 / (4 * a)) := mul_le_mul_of_nonneg_left h4 ha.le
          _ = 1 / 4 := by field_simp
      calc a * |t₀ - t| * (t₀ + t) ≤ (1 / 4) * (3 * t) :=
            mul_le_mul h5 h3 (by linarith) (by norm_num)
        _ = 3 / 4 * t := by ring
    have hB : (n : ℝ) / (8 * t ^ 3) ≤ 1 / 4 := by
      rw [← hn, div_le_iff₀ (by positivity)]
      have h8 : t₀ ^ 3 ≤ 8 * t ^ 3 := by
        have := pow_le_pow_left₀ (by positivity) h1 3
        nlinarith
      have h9 : t₀ ^ 2 ≤ t₀ ^ 3 := by nlinarith
      nlinarith
    linarith
  rw [hre]
  exact mul_nonneg (norm_nonneg _) (Real.cos_pos_of_le_one hphase).le

/-- **Middle copies are nonnegative** when `64an ≤ 1`: for `4n ≤ |γ| ≤ t₀` the phase is at most
`1/4 + 1/8 + 1/512`. -/
theorem xiHeatTerm_re_nonneg_of_mid {n : ℕ} {a t₀ : ℝ} (ha : 0 < a)
    (hn : a * t₀ ^ 2 = n) (hsmall : 64 * a * n ≤ 1) (hn1 : 1 ≤ n) {q : XiZeroCopy}
    (h1 : 4 * (n : ℝ) ≤ |xiCopyOrdinate q|) (h2 : |xiCopyOrdinate q| ≤ t₀) :
    0 ≤ (xiHeatTerm n a q).re := by
  set t := |xiCopyOrdinate q| with htdef
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have htpos : 0 < t := by linarith
  obtain ⟨δ, hδ, hre⟩ := exists_xiHeatTerm_re_eq n a q
  rw [← htdef] at hre
  have hat₀ : a * t₀ ≤ 1 / 8 := by
    have hsq : (a * t₀) ^ 2 ≤ (1 / 8) ^ 2 := by
      have : (a * t₀) ^ 2 = a * (a * t₀ ^ 2) := by ring
      rw [this, hn]
      nlinarith
    exact abs_le_of_sq_le_sq' hsq (by norm_num) |>.2
  have hphase : |2 * n * Real.arctan (δ / t) - 2 * a * t * δ| ≤ 1 := by
    refine (abs_heatPhase_le (a := a) n htpos hδ).trans ?_
    have hA : |(n : ℝ) / t - a * t| ≤ 1 / 4 + 1 / 8 := by
      have hnt : (n : ℝ) / t ≤ 1 / 4 := by
        rw [div_le_iff₀ htpos]; linarith
      have hat : a * t ≤ 1 / 8 := le_trans (mul_le_mul_of_nonneg_left h2 ha.le) hat₀
      have hnt0 : 0 ≤ (n : ℝ) / t := by positivity
      have hat0 : 0 ≤ a * t := by positivity
      rw [abs_le]
      constructor <;> linarith
    have hB : (n : ℝ) / (8 * t ^ 3) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by positivity)]
      have h64 : 64 * (n : ℝ) ^ 3 ≤ t ^ 3 := by
        have := pow_le_pow_left₀ (by positivity) h1 3
        nlinarith
      have hn3' : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
        simpa using pow_le_pow_right₀ hn1' (show 1 ≤ 3 by norm_num)
      have hn3 : (n : ℝ) ≤ 64 * (n : ℝ) ^ 3 := by nlinarith
      linarith
    linarith
  rw [hre]
  exact mul_nonneg (norm_nonneg _) (Real.cos_pos_of_le_one hphase).le

/-- **Far copies.**  If `||γ| − t₀| > 1/(4a)` with `a ≤ 1/4`, the heat term is at most
`262144 a` times the peak value times the Lorentzian masses at `±t₀`. -/
theorem norm_xiHeatTerm_le_far {n : ℕ} {a t₀ : ℝ} (ha : 0 < a) (ha4 : a ≤ 1 / 4) (ht₀ : 0 < t₀)
    (hn : a * t₀ ^ 2 = n) {q : XiZeroCopy}
    (hfar : 1 / (4 * a) < |(|xiCopyOrdinate q| - t₀)|) :
    ‖xiHeatTerm n a q‖ ≤ Real.exp (a / 2) * ((t₀ ^ 2) ^ n * Real.exp (-(n : ℝ))) *
      (262144 * a * (lorentzMassTerm t₀ q + lorentzMassTerm (-t₀) q)) := by
  refine (norm_xiHeatTerm_le_peak ha ht₀ hn q).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  set γ := xiCopyOrdinate q
  set s := |(|γ| - t₀)| with hsdef
  have h4a : 1 ≤ 1 / (4 * a) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hs1 : 1 ≤ s := by linarith
  have h4as : 1 ≤ 4 * a * s := by
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * a)).1 hfar
    linarith
  obtain ⟨hb1, hb2⟩ := sqrt_sq_add_quarter_bounds γ
  have hdist : s / 2 ≤ |Real.sqrt (γ ^ 2 + 1 / 4) - t₀| := by
    have h := abs_sub_abs_le_abs_sub (|γ| - t₀) (Real.sqrt (γ ^ 2 + 1 / 4) - t₀)
    rw [show |γ| - t₀ - (Real.sqrt (γ ^ 2 + 1 / 4) - t₀) = |γ| - Real.sqrt (γ ^ 2 + 1 / 4) by
      ring, ← hsdef] at h
    have hsm : abs (|γ| - Real.sqrt (γ ^ 2 + 1 / 4)) ≤ 1 / 2 :=
      abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hgauss : Real.exp (-(a * (Real.sqrt (γ ^ 2 + 1 / 4) - t₀) ^ 2)) ≤
      Real.exp (-(a * s ^ 2 / 4)) := by
    apply Real.exp_le_exp.2
    have hsq : (s / 2) ^ 2 ≤ (Real.sqrt (γ ^ 2 + 1 / 4) - t₀) ^ 2 := by
      rw [← sq_abs (Real.sqrt _ - t₀)]
      exact pow_le_pow_left₀ (by positivity) hdist 2
    nlinarith
  have htail : (1 + s ^ 2) * Real.exp (-(a * s ^ 2 / 4)) ≤ 262144 * a := by
    have hy := Real.pow_div_factorial_le_exp (a * s ^ 2 / 4) (by positivity) 3
    have hfac : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [hfac] at hy
    have hpos : 0 < Real.exp (a * s ^ 2 / 4) := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
    have h256 : 1 ≤ 256 * a ^ 4 * s ^ 4 := by
      have := pow_le_pow_left₀ (by norm_num) h4as 4
      nlinarith
    have hs2 : 1 ≤ s ^ 2 := by nlinarith
    have hkey : 384 * (1 + s ^ 2) ≤ 262144 * a ^ 4 * s ^ 6 := by nlinarith
    calc 1 + s ^ 2 ≤ 262144 * a * ((a * s ^ 2 / 4) ^ 3 / 6) := by nlinarith
      _ ≤ 262144 * a * Real.exp (a * s ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left hy (by positivity)
  have hL := one_div_le_lorentzMassTerm_add t₀ q
  have hs2 : s ^ 2 = (|γ| - t₀) ^ 2 := by rw [hsdef, sq_abs]
  rw [← hs2] at hL
  calc Real.exp (-(a * (Real.sqrt (γ ^ 2 + 1 / 4) - t₀) ^ 2))
      ≤ Real.exp (-(a * s ^ 2 / 4)) := hgauss
    _ = (1 + s ^ 2) * Real.exp (-(a * s ^ 2 / 4)) * (1 / (1 + s ^ 2)) := by
        field_simp
    _ ≤ 262144 * a * (lorentzMassTerm t₀ q + lorentzMassTerm (-t₀) q) :=
        mul_le_mul htail hL (by positivity) (by positivity)

/-- **Low copies, small degree.**  If `8n ≤ t₀`, `2 ≤ t₀` and `|γ| < 4n`, the heat term is at most
`8192` times the peak value times the Lorentzian mass at `0`. -/
theorem norm_xiHeatTerm_le_low_small {n : ℕ} {a t₀ : ℝ} (ha : 0 < a) (ht₀ : 0 < t₀)
    (hn : a * t₀ ^ 2 = n) (ht₀n : 8 * (n : ℝ) ≤ t₀) (ht₀2 : 2 ≤ t₀) {q : XiZeroCopy}
    (hlow : |xiCopyOrdinate q| < 4 * n) :
    ‖xiHeatTerm n a q‖ ≤ Real.exp (a / 2) * ((t₀ ^ 2) ^ n * Real.exp (-(n : ℝ))) *
      (8192 * lorentzMassTerm 0 q) := by
  refine (norm_xiHeatTerm_le_peak ha ht₀ hn q).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  set γ := xiCopyOrdinate q
  obtain ⟨-, hb2⟩ := sqrt_sq_add_quarter_bounds γ
  have hdist : t₀ / 4 ≤ t₀ - Real.sqrt (γ ^ 2 + 1 / 4) := by linarith
  have hgauss : Real.exp (-(a * (Real.sqrt (γ ^ 2 + 1 / 4) - t₀) ^ 2)) ≤
      Real.exp (-((n : ℝ) / 16)) := by
    apply Real.exp_le_exp.2
    have hsq : (t₀ / 4) ^ 2 ≤ (Real.sqrt (γ ^ 2 + 1 / 4) - t₀) ^ 2 := by
      rw [show (Real.sqrt (γ ^ 2 + 1 / 4) - t₀) ^ 2 = (t₀ - Real.sqrt (γ ^ 2 + 1 / 4)) ^ 2 by
        ring]
      exact pow_le_pow_left₀ (by positivity) hdist 2
    rw [← hn]
    nlinarith
  have hq := Real.quadratic_le_exp_of_nonneg (x := (n : ℝ) / 16) (by positivity)
  have hL : 1 / (1 + 16 * (n : ℝ) ^ 2) ≤ lorentzMassTerm 0 q := by
    unfold lorentzMassTerm
    apply one_div_le_one_div_of_le (by positivity)
    show 1 + (0 - γ) ^ 2 ≤ 1 + 16 * (n : ℝ) ^ 2
    have : (0 - γ) ^ 2 = |γ| ^ 2 := by rw [sq_abs]; ring
    rw [this]
    have h0 := abs_nonneg γ
    nlinarith
  calc Real.exp (-(a * (Real.sqrt (γ ^ 2 + 1 / 4) - t₀) ^ 2))
      ≤ Real.exp (-((n : ℝ) / 16)) := hgauss
    _ ≤ 8192 * (1 / (1 + 16 * (n : ℝ) ^ 2)) := by
        rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
        rw [show 8192 * (1 / (1 + 16 * (n : ℝ) ^ 2)) * Real.exp ((n : ℝ) / 16) =
          8192 * Real.exp ((n : ℝ) / 16) / (1 + 16 * (n : ℝ) ^ 2) by ring,
          le_div_iff₀ (by positivity)]
        nlinarith
    _ ≤ 8192 * lorentzMassTerm 0 q := mul_le_mul_of_nonneg_left hL (by norm_num)

/-- **Low copies, large degree.**  If `64an > 1`, `2 ≤ t₀` and `|γ| < t₀/2`, the heat term is at
most `1597440/n` times the peak value times the Lorentzian masses at `±t₀`. -/
theorem norm_xiHeatTerm_le_low_large {n : ℕ} {a t₀ : ℝ} (ha : 0 < a) (ht₀ : 0 < t₀)
    (hn : a * t₀ ^ 2 = n) (hlarge : 1 < 64 * a * n) (ht₀2 : 2 ≤ t₀) (hn1 : 1 ≤ n)
    {q : XiZeroCopy} (hlow : |xiCopyOrdinate q| < t₀ / 2) :
    ‖xiHeatTerm n a q‖ ≤ Real.exp (a / 2) * ((t₀ ^ 2) ^ n * Real.exp (-(n : ℝ))) *
      (1597440 / n * (lorentzMassTerm t₀ q + lorentzMassTerm (-t₀) q)) := by
  refine (norm_xiHeatTerm_le_peak ha ht₀ hn q).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  set γ := xiCopyOrdinate q
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  obtain ⟨-, hb2⟩ := sqrt_sq_add_quarter_bounds γ
  have hdist : t₀ / 4 ≤ t₀ - Real.sqrt (γ ^ 2 + 1 / 4) := by linarith
  have hgauss : Real.exp (-(a * (Real.sqrt (γ ^ 2 + 1 / 4) - t₀) ^ 2)) ≤
      Real.exp (-((n : ℝ) / 16)) := by
    apply Real.exp_le_exp.2
    have hsq : (t₀ / 4) ^ 2 ≤ (Real.sqrt (γ ^ 2 + 1 / 4) - t₀) ^ 2 := by
      rw [show (Real.sqrt (γ ^ 2 + 1 / 4) - t₀) ^ 2 = (t₀ - Real.sqrt (γ ^ 2 + 1 / 4)) ^ 2 by
        ring]
      exact pow_le_pow_left₀ (by positivity) hdist 2
    rw [← hn]
    nlinarith
  have hcube := Real.pow_div_factorial_le_exp ((n : ℝ) / 16) (by positivity) 3
  have hfac : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfac] at hcube
  -- `1 + t₀² ≤ 65 n²`
  have ht₀sq : 1 + t₀ ^ 2 ≤ 65 * (n : ℝ) ^ 2 := by
    have h64 : t₀ ^ 2 < 64 * (n : ℝ) ^ 2 := by
      have hlt : a * t₀ ^ 2 < a * (64 * (n : ℝ) ^ 2) := by
        rw [hn]; nlinarith
      exact lt_of_mul_lt_mul_left hlt ha.le
    nlinarith
  have hL : 1 / (1 + t₀ ^ 2) ≤ lorentzMassTerm t₀ q + lorentzMassTerm (-t₀) q := by
    refine le_trans ?_ (one_div_le_lorentzMassTerm_add t₀ q)
    apply one_div_le_one_div_of_le (by positivity)
    have h0 := abs_nonneg γ
    nlinarith
  calc Real.exp (-(a * (Real.sqrt (γ ^ 2 + 1 / 4) - t₀) ^ 2))
      ≤ Real.exp (-((n : ℝ) / 16)) := hgauss
    _ ≤ 1597440 / n * (1 / (1 + t₀ ^ 2)) := by
        rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
        rw [show 1597440 / (n : ℝ) * (1 / (1 + t₀ ^ 2)) * Real.exp ((n : ℝ) / 16) =
          1597440 * Real.exp ((n : ℝ) / 16) / ((n : ℝ) * (1 + t₀ ^ 2)) by
            field_simp, le_div_iff₀ (by positivity)]
        have : (n : ℝ) * (1 + t₀ ^ 2) ≤ 65 * (n : ℝ) ^ 3 := by nlinarith
        nlinarith
    _ ≤ 1597440 / n * (lorentzMassTerm t₀ q + lorentzMassTerm (-t₀) q) :=
        mul_le_mul_of_nonneg_left hL (by positivity)

/-! ## Window copies from the zero count -/

/-- The copies with ordinate in `(T − h, T + h]` number `N(T + h) − N(T − h)`. -/
theorem exists_finset_xiZeroCopy_window {T h : ℝ} (hTh : 0 ≤ T - h) (hh : 0 ≤ h) :
    ∃ P : Finset XiZeroCopy, (∀ q ∈ P, T - h < xiCopyOrdinate q ∧ xiCopyOrdinate q ≤ T + h) ∧
      ((xiZeroCount (T + h) : ℝ) - xiZeroCount (T - h)) ≤ P.card := by
  classical
  have hsub : xiSupportsPos (T - h) ⊆ xiSupportsPos (T + h) := by
    intro ρ hρ
    rw [mem_xiSupportsPos] at hρ ⊢
    exact ⟨by linarith [hρ.1], hρ.2⟩
  refine ⟨(xiSupportsPos (T + h) \ xiSupportsPos (T - h)).sigma fun ρ =>
    (Finset.univ : Finset (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))))),
    ?_, ?_⟩
  · intro q hq
    rw [Finset.mem_sigma] at hq
    obtain ⟨hq1, -⟩ := hq
    rw [Finset.mem_sdiff, mem_xiSupportsPos, mem_xiSupportsPos] at hq1
    obtain ⟨⟨h1, h2⟩, h3⟩ := hq1
    refine ⟨?_, (le_abs_self _).trans h1⟩
    by_contra hle
    exact h3 ⟨by rw [abs_of_pos h2]; exact (not_lt.1 hle), h2⟩
  · rw [Finset.card_sigma]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [xiZeroCount_eq_pos_sum (by linarith), xiZeroCount_eq_pos_sum hTh]
    push_cast
    rw [← Finset.sum_sdiff_eq_sub hsub]
    exact le_of_eq (Finset.sum_congr rfl fun ρ _ => by simp [xiSupportMultiplicity])

/-! ## Assembly -/

theorem xiHeatMoment_re_eq_tsum {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (xiHeatMoment n a).re = ∑' q, (xiHeatTerm n a q).re :=
  Complex.re_tsum (summable_pow_mul_exp_xiHeatFrequency ha n)

/-- **The pointwise budget.**  Every heat term is at least its window credit `g_q` minus its far
and low debt `b_q`. -/
theorem xiHeatTerm_re_ge_credit_sub_debt {n : ℕ} (hn1 : 1 ≤ n) {a t₀ h : ℝ} (ha : 0 < a)
    (ha4 : a ≤ 1 / 4) (ht₀ : 8 ≤ t₀) (hn : a * t₀ ^ 2 = n) (hh : 0 ≤ h) (ht₀h : 4 * h ≤ t₀)
    (hph : 3 * a * h + a ≤ 1 / 2) (hgauss : 18 * a * h ^ 2 ≤ 1) {P : Finset XiZeroCopy}
    (hP : ∀ q ∈ P, t₀ - h < xiCopyOrdinate q ∧ xiCopyOrdinate q ≤ t₀ + h) (q : XiZeroCopy) :
    (if q ∈ P then (t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) / 2 else 0) -
        Real.exp (a / 2) * ((t₀ ^ 2) ^ n * Real.exp (-(n : ℝ))) *
          (262144 * a * (lorentzMassTerm t₀ q + lorentzMassTerm (-t₀) q) +
            (if 64 * a * n ≤ 1 then 8192 * lorentzMassTerm 0 q
              else 1597440 / n * (lorentzMassTerm t₀ q + lorentzMassTerm (-t₀) q))) ≤
      (xiHeatTerm n a q).re := by
  set E := Real.exp (a / 2) * ((t₀ ^ 2) ^ n * Real.exp (-(n : ℝ))) with hE
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hLp := lorentzMassTerm_nonneg t₀ q
  have hLm := lorentzMassTerm_nonneg (-t₀) q
  have hL₀ := lorentzMassTerm_nonneg 0 q
  have hlam : 0 ≤ (if 64 * a * n ≤ 1 then 8192 * lorentzMassTerm 0 q
      else 1597440 / n * (lorentzMassTerm t₀ q + lorentzMassTerm (-t₀) q)) := by
    split_ifs <;> positivity
  have hE0 : 0 ≤ E := by positivity
  have hb : 0 ≤ E * (262144 * a * (lorentzMassTerm t₀ q + lorentzMassTerm (-t₀) q) +
      (if 64 * a * n ≤ 1 then 8192 * lorentzMassTerm 0 q
        else 1597440 / n * (lorentzMassTerm t₀ q + lorentzMassTerm (-t₀) q))) := by positivity
  by_cases hqP : q ∈ P
  · rw [if_pos hqP]
    have := xiHeatTerm_re_ge_half_peak ha (by linarith) hn hh ht₀h (by linarith) hph hgauss
      (hP q hqP).1 (hP q hqP).2
    linarith
  rw [if_neg hqP, zero_sub]
  by_cases hre : 0 ≤ (xiHeatTerm n a q).re
  · linarith
  have hre' : (xiHeatTerm n a q).re < 0 := not_le.1 hre
  have hnorm : ‖xiHeatTerm n a q‖ ≤ E * (262144 * a * (lorentzMassTerm t₀ q +
      lorentzMassTerm (-t₀) q) + (if 64 * a * n ≤ 1 then 8192 * lorentzMassTerm 0 q
        else 1597440 / n * (lorentzMassTerm t₀ q + lorentzMassTerm (-t₀) q))) := by
    by_cases hfar : 1 / (4 * a) < |(|xiCopyOrdinate q| - t₀)|
    · refine (norm_xiHeatTerm_le_far ha ha4 (by linarith) hn hfar).trans ?_
      rw [← hE]
      exact mul_le_mul_of_nonneg_left (by linarith) hE0
    have hnear := not_lt.1 hfar
    by_cases hS : 64 * a * n ≤ 1
    · rw [if_pos hS]
      have ht₀n : 8 * (n : ℝ) ≤ t₀ := by
        have hsq : (8 * (n : ℝ)) ^ 2 ≤ t₀ ^ 2 := by
          have : a * (8 * (n : ℝ)) ^ 2 ≤ a * t₀ ^ 2 := by rw [hn]; nlinarith
          exact le_of_mul_le_mul_left this ha
        exact abs_le_of_sq_le_sq' hsq (by linarith) |>.2
      by_cases hlow : |xiCopyOrdinate q| < 4 * n
      · refine (norm_xiHeatTerm_le_low_small ha (by linarith) hn ht₀n (by linarith) hlow).trans ?_
        rw [← hE]
        exact mul_le_mul_of_nonneg_left (by nlinarith) hE0
      · exfalso
        rcases le_or_gt (|xiCopyOrdinate q|) t₀ with hle | hgt
        · exact hre (xiHeatTerm_re_nonneg_of_mid ha hn hS hn1 (not_lt.1 hlow) hle)
        · exact hre (xiHeatTerm_re_nonneg_of_near ha ha4 (by linarith) hn (by linarith) hnear)
    · rw [if_neg hS]
      have hL' : 1 < 64 * a * n := not_le.1 hS
      by_cases hlow : |xiCopyOrdinate q| < t₀ / 2
      · refine (norm_xiHeatTerm_le_low_large ha (by linarith) hn hL' (by linarith) hn1
          hlow).trans ?_
        rw [← hE]
        exact mul_le_mul_of_nonneg_left (by nlinarith) hE0
      · exfalso
        exact hre (xiHeatTerm_re_nonneg_of_near ha ha4 (by linarith) hn (not_lt.1 hlow) hnear)
  have := (abs_le.1 (Complex.abs_re_le_norm (xiHeatTerm n a q))).1
  linarith

theorem lorentzMass_nonneg' (t : ℝ) : 0 ≤ lorentzMass t := by
  unfold lorentzMass
  exact tsum_nonneg (lorentzMassTerm_nonneg t)

/-- **The summed budget.**  `Re M_n(a) ≥ |P| F₀/2 − e^{a/2} F₀ (262144 a (M(t₀) + M(−t₀)) + Λ)`
with `F₀ = t₀^{2n} e^{−n}` the peak value, `M` the Lorentzian mass and `Λ` the low debt. -/
theorem heatMoment_re_ge_budget {n : ℕ} (hn1 : 1 ≤ n) {a t₀ h : ℝ} (ha : 0 < a)
    (ha4 : a ≤ 1 / 4) (ht₀ : 8 ≤ t₀) (hn : a * t₀ ^ 2 = n) (hh : 0 ≤ h) (ht₀h : 4 * h ≤ t₀)
    (hph : 3 * a * h + a ≤ 1 / 2) (hgauss : 18 * a * h ^ 2 ≤ 1) {P : Finset XiZeroCopy}
    (hP : ∀ q ∈ P, t₀ - h < xiCopyOrdinate q ∧ xiCopyOrdinate q ≤ t₀ + h) :
    (P.card : ℝ) * ((t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) / 2) -
        Real.exp (a / 2) * ((t₀ ^ 2) ^ n * Real.exp (-(n : ℝ))) *
          (262144 * a * (lorentzMass t₀ + lorentzMass (-t₀)) +
            (if 64 * a * n ≤ 1 then 8192 * lorentzMass 0
              else 1597440 / n * (lorentzMass t₀ + lorentzMass (-t₀)))) ≤
      (xiHeatMoment n a).re := by
  classical
  have hsp := summable_lorentzMassTerm t₀
  have hsmn := summable_lorentzMassTerm (-t₀)
  have hs0 := summable_lorentzMassTerm 0
  have hlam : HasSum (fun q => if 64 * a * n ≤ 1 then 8192 * lorentzMassTerm 0 q
      else 1597440 / n * (lorentzMassTerm t₀ q + lorentzMassTerm (-t₀) q))
      (if 64 * a * n ≤ 1 then 8192 * lorentzMass 0
        else 1597440 / n * (lorentzMass t₀ + lorentzMass (-t₀))) := by
    by_cases hS : 64 * a * n ≤ 1
    · simp only [if_pos hS]
      exact hs0.hasSum.mul_left 8192
    · simp only [if_neg hS]
      exact (hsp.hasSum.add hsmn.hasSum).mul_left _
  have hp : HasSum (lorentzMassTerm t₀) (lorentzMass t₀) := hsp.hasSum
  have hm : HasSum (lorentzMassTerm (-t₀)) (lorentzMass (-t₀)) := hsmn.hasSum
  have hdebt := (((hp.add hm).mul_left (262144 * a)).add hlam).mul_left
    (Real.exp (a / 2) * ((t₀ ^ 2) ^ n * Real.exp (-(n : ℝ))))
  have hcredit : HasSum (fun q => if q ∈ P then (t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) / 2 else 0)
      ((P.card : ℝ) * ((t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) / 2)) := by
    have : HasSum (fun q => if q ∈ P then (t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) / 2 else 0)
        (∑ q ∈ P, if q ∈ P then (t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) / 2 else 0) :=
      hasSum_sum_of_ne_finset_zero (fun q hq => if_neg hq)
    rwa [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul] at this
  have hsumRe : Summable fun q => (xiHeatTerm n a q).re :=
    Complex.reCLM.summable (summable_pow_mul_exp_xiHeatFrequency ha n)
  have hdiff := hcredit.sub hdebt
  rw [xiHeatMoment_re_eq_tsum ha n, ← hdiff.tsum_eq]
  exact Summable.tsum_le_tsum
    (fun q => xiHeatTerm_re_ge_credit_sub_debt hn1 ha ha4 ht₀ hn hh ht₀h hph hgauss hP q)
    hdiff.summable hsumRe

/-- **Positivity of one heat moment from a populated window.** -/
theorem heatMoment_re_pos_of_window {n : ℕ} (hn1 : 1 ≤ n) {a t₀ h A : ℝ} (ha : 0 < a)
    (ha4 : a ≤ 1 / 4) (ht₀ : 8 ≤ t₀) (hn : a * t₀ ^ 2 = n) (hh : 0 ≤ h) (ht₀h : 4 * h ≤ t₀)
    (hph : 3 * a * h + a ≤ 1 / 2) (hgauss : 18 * a * h ^ 2 ≤ 1) {P : Finset XiZeroCopy}
    (hP : ∀ q ∈ P, t₀ - h < xiCopyOrdinate q ∧ xiCopyOrdinate q ≤ t₀ + h)
    (hPcard : Real.log t₀ ≤ P.card) (hA : |xiLineTwoLogDerivConstant| ≤ A)
    (hfar : 100663296 * a * (A + 2) ≤ 1)
    (hsmall : 64 * a * n ≤ 1 → 1572864 * (A + 3) ≤ Real.log t₀)
    (hlarge : 1 < 64 * a * n → 613416960 * (A + 2) ≤ n) :
    0 < (xiHeatMoment n a).re := by
  have hbudget := heatMoment_re_ge_budget hn1 ha ha4 ht₀ hn hh ht₀h hph hgauss hP
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F = (t₀ ^ 2) ^ n * Real.exp (-(n : ℝ)) := ⟨_, rfl⟩
  have hF0 : 0 < F := by rw [hF]; positivity
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log t₀ := ⟨_, rfl⟩
  rw [← hℓ] at hPcard hsmall
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = (if 64 * a * n ≤ 1 then 8192 * lorentzMass 0
      else 1597440 / n * (lorentzMass t₀ + lorentzMass (-t₀))) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = 262144 * a * (lorentzMass t₀ + lorentzMass (-t₀)) + Λ :=
    ⟨_, rfl⟩
  rw [← hF, ← hΛ, ← hY] at hbudget
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hexp3 : Real.exp (a / 2) ≤ 3 := by
    have := Real.exp_le_exp.2 (show a / 2 ≤ 1 by linarith)
    linarith [Real.exp_one_lt_d9]
  -- the Lorentzian masses
  have hlog4 : Real.log (t₀ + 4) ≤ 1 + ℓ := by
    have h2 : Real.log (t₀ + 4) ≤ Real.log (2 * t₀) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith), ← hℓ] at h2
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hAc := le_abs_self xiLineTwoLogDerivConstant
  have hMp : lorentzMass t₀ ≤ 8 * (A + (1 + ℓ)) := by
    refine (lorentzMass_le_log t₀).trans ?_
    rw [abs_of_pos (by linarith)]
    linarith
  have hMm : lorentzMass (-t₀) ≤ 8 * (A + (1 + ℓ)) := by
    refine (lorentzMass_le_log (-t₀)).trans ?_
    rw [abs_neg, abs_of_pos (by linarith)]
    linarith
  have hM0 : lorentzMass 0 ≤ 8 * (A + 3) := by
    refine (lorentzMass_le_log 0).trans ?_
    rw [abs_zero, zero_add]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hMM : lorentzMass t₀ + lorentzMass (-t₀) ≤ 16 * (A + 2) * ℓ := by nlinarith
  have hMpos : 0 ≤ lorentzMass t₀ + lorentzMass (-t₀) :=
    add_nonneg (lorentzMass_nonneg' t₀) (lorentzMass_nonneg' (-t₀))
  -- the far debt
  have hfarpart : 262144 * a * (lorentzMass t₀ + lorentzMass (-t₀)) ≤ ℓ / 24 := by
    have h1 : 262144 * a * (lorentzMass t₀ + lorentzMass (-t₀)) ≤
        262144 * a * (16 * (A + 2) * ℓ) := mul_le_mul_of_nonneg_left hMM (by positivity)
    nlinarith
  -- the low debt
  have hΛle : Λ ≤ ℓ / 24 := by
    rw [hΛ]
    by_cases hS : 64 * a * n ≤ 1
    · rw [if_pos hS]
      have := hsmall hS
      nlinarith
    · rw [if_neg hS, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have hnbig := hlarge (not_le.1 hS)
      have h1 : 1597440 * (lorentzMass t₀ + lorentzMass (-t₀)) ≤
          1597440 * (16 * (A + 2) * ℓ) := mul_le_mul_of_nonneg_left hMM (by norm_num)
      nlinarith
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ]
    split_ifs
    · exact mul_nonneg (by norm_num) (lorentzMass_nonneg' 0)
    · exact mul_nonneg (by positivity) hMpos
  have hYle : Y ≤ ℓ / 12 := by rw [hY]; linarith
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hEY : Real.exp (a / 2) * F * Y ≤ 3 * F * (ℓ / 12) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hexp3 hF0.le) hYle hY0 (by positivity)
  have hcard : ℓ * (F / 2) ≤ P.card * (F / 2) :=
    mul_le_mul_of_nonneg_right hPcard (by positivity)
  have hpos : 0 < ℓ * F := by positivity
  linarith

/-- **Complete monotonicity of the zero heat trace at small heat time.**  There is `a₀ > 0` such
that every heat moment `M_n(a) = Σ_q w_q^n e^{−a w_q}` is positive for `0 < a ≤ a₀` and all `n`. -/
theorem exists_heatMoment_re_pos_small_time :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ → ∀ n : ℕ, 0 < (xiHeatMoment n a).re := by
  obtain ⟨h, hh, T₁, hT₁, hwin⟩ := exists_xiZeroCount_window_ge_log
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = |xiLineTwoLogDerivConstant| := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := hA ▸ abs_nonneg _
  have hκ := routeUCompletedPrimeGammaAperture_pos
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 4 + 18 * h ^ 2 + (6 * h + 2) + 39258685440 * (A + 3) +
      (T₁ + 4 * h + 8) ^ 2 + Real.exp (3145728 * (A + 3)) := ⟨_, rfl⟩
  have hexp0 := Real.exp_pos (3145728 * (A + 3))
  have hD0 : 0 < D := by rw [hD]; positivity
  refine ⟨min routeUCompletedPrimeGammaAperture (1 / D), lt_min hκ (by positivity),
    fun a ha haD n => ?_⟩
  have haκ : a ≤ routeUCompletedPrimeGammaAperture := haD.trans (min_le_left _ _)
  have haD' : a * D ≤ 1 := by
    have := haD.trans (min_le_right _ _)
    rwa [le_div_iff₀ hD0] at this
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · have h1 := heatMomentDet_pos_of_mul_le ha (N := 1) (by simpa using haκ)
    rw [Matrix.det_fin_one] at h1
    simpa [GaloisForLFunctions.HTGeometry.leadingMatrix, heatMomentArray] using h1
  have hn1 : 1 ≤ n := hnpos
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  -- consequences of `a D ≤ 1`
  have hterm : ∀ x : ℝ, 0 ≤ x → x ≤ D → a * x ≤ 1 := fun x hx hxD =>
    (mul_le_mul_of_nonneg_left hxD ha.le).trans haD'
  have hh2 : 0 ≤ 18 * h ^ 2 := by positivity
  have hDge : ∀ x : ℝ, 0 ≤ x → x ≤ D - 0 → x ≤ D := fun x _ hx => by linarith
  have hexpD : Real.exp (3145728 * (A + 3)) ≤ D := by rw [hD]; nlinarith [sq_nonneg (T₁ + 4 * h + 8)]
  have hsqD : (T₁ + 4 * h + 8) ^ 2 ≤ D := by rw [hD]; nlinarith
  have hbigD : 39258685440 * (A + 3) ≤ D := by rw [hD]; nlinarith [sq_nonneg (T₁ + 4 * h + 8)]
  have ha4 : a ≤ 1 / 4 := by
    have := hterm 4 (by norm_num) (by rw [hD]; nlinarith [sq_nonneg (T₁ + 4 * h + 8)])
    linarith
  have hgauss : 18 * a * h ^ 2 ≤ 1 := by
    have := hterm (18 * h ^ 2) hh2 (by rw [hD]; nlinarith [sq_nonneg (T₁ + 4 * h + 8)])
    linarith
  have hph : 3 * a * h + a ≤ 1 / 2 := by
    have := hterm (6 * h + 2) (by positivity) (by rw [hD]; nlinarith [sq_nonneg (T₁ + 4 * h + 8)])
    linarith
  have hfar : 100663296 * a * (A + 2) ≤ 1 := by
    have := hterm (39258685440 * (A + 3)) (by positivity) hbigD
    nlinarith
  -- the peak
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = Real.sqrt (n / a) := ⟨_, rfl⟩
  have hna : 0 ≤ (n : ℝ) / a := by positivity
  have ht₀sq : t₀ ^ 2 = n / a := by rw [ht₀, Real.sq_sqrt hna]
  have hn : a * t₀ ^ 2 = n := by rw [ht₀sq]; field_simp
  have hDt : D ≤ t₀ ^ 2 := by
    rw [ht₀sq, le_div_iff₀ ha]
    nlinarith
  have ht₀big : T₁ + 4 * h + 8 ≤ t₀ := by
    rw [ht₀, Real.le_sqrt (by linarith) hna, ← ht₀sq]
    linarith
  have ht₀8 : 8 ≤ t₀ := by linarith
  -- the window
  obtain ⟨P, hP, hPcard⟩ := exists_finset_xiZeroCopy_window (T := t₀) (h := h) (by linarith) hh.le
  have hwin' := hwin t₀ (by linarith)
  refine heatMoment_re_pos_of_window hn1 ha ha4 ht₀8 hn hh.le (by linarith) hph hgauss hP
    (hwin'.trans hPcard) hA.ge hfar (fun _ => ?_) (fun hL => ?_)
  · -- `log t₀ ≥ 1572864 (A + 3)` from `t₀² ≥ e^{3145728(A+3)}`
    have h1 : Real.exp (3145728 * (A + 3)) ≤ t₀ ^ 2 := hexpD.trans hDt
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp, Real.log_pow] at h2
    push_cast at h2
    linarith
  · -- `n ≥ 613416960 (A + 2)` from `64 a n > 1`
    have h1 : D < 64 * n := by
      have : a * D < a * (64 * n) := by nlinarith
      exact lt_of_mul_lt_mul_left this ha.le
    nlinarith

end

end RHTower
