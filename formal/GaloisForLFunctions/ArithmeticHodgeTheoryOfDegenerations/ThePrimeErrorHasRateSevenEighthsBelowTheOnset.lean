import GaloisForLFunctions.ZeroConfigurationGeometry.TheOneOffsAreFiniteOscillationsOfThePrimeError
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePoleSelfEnergyIsSharpBelowTheOnset

/-!
# The prime error has rate `7/8` below the onset

The window explicit formula squeezes `ψ(x)` between two averages of width `H`; each zero contributes
at most `16 x^{β}(x/H)^θ/(|ρ||1−ρ|^θ)` (`norm_lagWindowZeroTerm_le_interpolated`). Splitting the
zeros at a height `T` (`norm_tsum_window_le_split`), the zeros below `T` with `β ≤ ¾` give
`x^{3/4}` and those above give `x · T^{−θ/2}` (`tsum_zeroWeight_above_le`). With `θ = 1`,
`H = x^{7/8}`, `T = √x`:

* **Conditional rate** (`exists_abs_psi_sub_self_le_seven_eighths`):
  `|ψ(x) − x| ≤ C x^{7/8}` whenever every zero of height `≤ √x` has `β ≤ ¾`.
* **Below the onset** (`exists_abs_reciprocalMangoldtError_add_euler_le_of_zetaWindowPositive`):
  window positivity at `a` gives `|Σ_{n ≤ e^t} Λ(n)/n − t + γ| ≤ C e^{−t/8}` for `K(t + 2) ≤ a`.
-/

noncomputable section
set_option autoImplicit false

open Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open _root_.Zeta23 _root_.RHTower GaloisForLFunctions.ZeroConfigurationGeometry
  GaloisForLFunctions.SquareRootThreshold

/-! ### 1. Zero weights above a height -/

/-- `1/(|ρ||1−ρ|^θ) ≤ |γ|^{−(1+θ)}`. -/
private theorem zeroWeight_le_abs_im_inv_rpow {θ : ℝ} (hθ : 0 < θ) (q : XiZeroCopy) :
    zeroWeight θ q ≤ |(q.1 : ℂ).im|⁻¹ ^ (1 + θ) := by
  have him : 0 < |(q.1 : ℂ).im| := abs_pos.mpr (xiSupport_im_ne_zero q.1)
  have h1 : |(q.1 : ℂ).im| ≤ ‖(q.1 : ℂ)‖ := Complex.abs_im_le_norm _
  have h2 : |(q.1 : ℂ).im| ≤ ‖1 - (q.1 : ℂ)‖ := by
    have := Complex.abs_im_le_norm (1 - (q.1 : ℂ))
    simpa using this
  rw [zeroWeight, Real.rpow_add (inv_pos.mpr him), Real.rpow_one, Real.inv_rpow him.le]
  exact mul_le_mul (inv_anti₀ him h1)
    (inv_anti₀ (Real.rpow_pos_of_pos him _) (Real.rpow_le_rpow him.le h2 hθ.le))
    (inv_nonneg.mpr (Real.rpow_nonneg (norm_nonneg _) _)) (inv_nonneg.mpr him.le)

/-- The zeros above height `T` carry zero weight `O(T^{−θ/2})`. -/
theorem tsum_zeroWeight_above_le {θ T : ℝ} (hθ : 0 < θ) (hT : 0 < T) :
    ∑' q : XiZeroCopy, (if T < |(q.1 : ℂ).im| then zeroWeight θ q else 0) ≤
      T ^ (-(θ / 2)) * ∑' q : XiZeroCopy, |(q.1 : ℂ).im|⁻¹ ^ (1 + θ / 2) := by
  have hs := summable_abs_im_inv_rpow (p := 1 + θ / 2) (by linarith)
  have hle : ∀ q : XiZeroCopy, (if T < |(q.1 : ℂ).im| then zeroWeight θ q else 0) ≤
      T ^ (-(θ / 2)) * |(q.1 : ℂ).im|⁻¹ ^ (1 + θ / 2) := by
    intro q
    split_ifs with h
    · have him : 0 < |(q.1 : ℂ).im| := hT.trans h
      have hinv : 0 < |(q.1 : ℂ).im|⁻¹ := inv_pos.mpr him
      have hsplit : |(q.1 : ℂ).im|⁻¹ ^ (1 + θ) =
          |(q.1 : ℂ).im|⁻¹ ^ (θ / 2) * |(q.1 : ℂ).im|⁻¹ ^ (1 + θ / 2) := by
        rw [← Real.rpow_add hinv]; ring_nf
      have hTpow : |(q.1 : ℂ).im|⁻¹ ^ (θ / 2) ≤ T ^ (-(θ / 2)) := by
        rw [Real.rpow_neg hT.le, ← Real.inv_rpow hT.le]
        exact Real.rpow_le_rpow hinv.le (inv_anti₀ hT h.le) (by linarith)
      calc zeroWeight θ q ≤ |(q.1 : ℂ).im|⁻¹ ^ (1 + θ) := zeroWeight_le_abs_im_inv_rpow hθ q
        _ = _ := hsplit
        _ ≤ T ^ (-(θ / 2)) * |(q.1 : ℂ).im|⁻¹ ^ (1 + θ / 2) :=
          mul_le_mul_of_nonneg_right hTpow (Real.rpow_nonneg hinv.le _)
    · exact mul_nonneg (Real.rpow_nonneg hT.le _) (Real.rpow_nonneg (inv_nonneg.mpr (abs_nonneg _)) _)
  have hsl : Summable fun q : XiZeroCopy =>
      (if T < |(q.1 : ℂ).im| then zeroWeight θ q else 0) :=
    Summable.of_nonneg_of_le (fun q => by split_ifs <;> simp [zeroWeight_nonneg]) hle
      (hs.mul_left _)
  rw [← tsum_mul_left]
  exact hsl.tsum_le_tsum hle (hs.mul_left _)

/-! ### 2. The window zero sum split at a height -/

/-- **Split window bound.** If every zero of height `≤ T` has `β ≤ ¾`, the zero sum of a window of
width `H` near `x` is at most `16 (x/H)^θ (x^{3/4} Σ w_θ + x Σ_{|γ|>T} w_θ)`. -/
theorem norm_tsum_window_le_split {T θ x H a b : ℝ}
    (hlow : ∀ q : XiZeroCopy, |(q.1 : ℂ).im| ≤ T → (q.1 : ℂ).re ≤ 3 / 4)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hx : 1 ≤ x) (hH : 0 < H) (hxa : x / 2 ≤ a) (ha : 1 ≤ a)
    (hab : b - a = H) (hb : b ≤ 2 * x) :
    ‖∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a b‖ ≤
      16 * (x / H) ^ θ * (x ^ (3 / 4 : ℝ) * ∑' q, zeroWeight θ q +
        x * ∑' q : XiZeroCopy, (if T < |(q.1 : ℂ).im| then zeroWeight θ q else 0)) := by
  have hablt : a < b := by linarith
  set P : ℝ := 16 * (x / H) ^ θ with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  set e : XiZeroCopy → ℝ := fun q =>
    P * x ^ (3 / 4 : ℝ) * zeroWeight θ q +
      P * x * (if T < |(q.1 : ℂ).im| then zeroWeight θ q else 0) with he
  have hind : Summable fun q : XiZeroCopy =>
      (if T < |(q.1 : ℂ).im| then zeroWeight θ q else 0) :=
    Summable.of_nonneg_of_le (fun q => by split_ifs <;> simp [zeroWeight_nonneg])
      (fun q => by split_ifs <;> simp [zeroWeight_nonneg]) (summable_zeroWeight hθ0)
  have hes : Summable e :=
    ((summable_zeroWeight hθ0).mul_left _).add (hind.mul_left _)
  have hbd : ∀ q : XiZeroCopy, ‖lagWindowZeroTerm (q.1 : ℂ) a b‖ ≤ e q := by
    intro q
    have hq0 := xiZeroCopy_re_pos q
    have hq1 := xiZeroCopy_re_lt_one q
    have hw := zeroWeight_nonneg θ q
    by_cases hT : T < |(q.1 : ℂ).im|
    · have h := norm_lagWindowZeroTerm_le_interpolated hx hH hxa hab hb hθ0.le hθ1 hq0 hq1
        (β₁ := 1) hq1.le
      rw [Real.rpow_one] at h
      change _ ≤ 16 * x * (x / H) ^ θ * zeroWeight θ q at h
      simp only [he, if_pos hT]
      have : 0 ≤ P * x ^ (3 / 4 : ℝ) * zeroWeight θ q := by positivity
      nlinarith
    · have h := norm_lagWindowZeroTerm_le_interpolated hx hH hxa hab hb hθ0.le hθ1 hq0 hq1
        (β₁ := 3 / 4) (hlow q (not_lt.mp hT))
      change _ ≤ 16 * x ^ (3 / 4 : ℝ) * (x / H) ^ θ * zeroWeight θ q at h
      simp only [he, if_neg hT, mul_zero, add_zero]
      nlinarith
  have hsn := summable_norm_lagWindowZeroTerm ha hablt
  have hsum : ∑' q, e q = P * (x ^ (3 / 4 : ℝ) * ∑' q, zeroWeight θ q +
      x * ∑' q : XiZeroCopy, (if T < |(q.1 : ℂ).im| then zeroWeight θ q else 0)) := by
    rw [((summable_zeroWeight hθ0).mul_left _).tsum_add (hind.mul_left _), tsum_mul_left,
      tsum_mul_left]
    ring
  calc ‖∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a b‖
      ≤ ∑' q : XiZeroCopy, ‖lagWindowZeroTerm (q.1 : ℂ) a b‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' q, e q := hsn.tsum_le_tsum hbd hes
    _ = _ := hsum

/-! ### 3. The two-sided squeeze -/

/-- **Squeeze.** If both window zero sums at `x` have norm at most `E`, then
`|ψ(x) − x| ≤ H + 1 + log 2π + E`. -/
theorem abs_psi_sub_self_le_of_windows {x H E : ℝ} (hx : 4 ≤ x) (hH1 : 1 ≤ H) (hHx : H ≤ x / 2)
    (hU : ‖∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) x (x + H)‖ ≤ E)
    (hL : ‖∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) (x - H) x‖ ≤ E) :
    |Chebyshev.psi x - x| ≤ H + 1 + Real.log (2 * Real.pi) + E := by
  have hH : 0 < H := by linarith
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hwU : 0 < 1 / x - 1 / (x + H) := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt hx0 (by linarith)
  have hψU : Chebyshev.psi x ≤ chebyshevLagWindow x (x + H) / (1 / x - 1 / (x + H)) := by
    rw [le_div_iff₀ hwU]
    exact (chebyshevLagWindow_bounds hx0 (by linarith)).1
  rw [chebyshevLagWindow_div_eq (by linarith) (by linarith)] at hψU
  have hLU : Real.log ((x + H) / x) / (1 / x - 1 / (x + H)) ≤ x + H := by
    rw [div_le_iff₀ hwU]
    exact (log_div_le_mul_inv_sub hx0 (by linarith)).2
  have hEU := trivialWindowTerm_le (show 2 ≤ x by linarith) hH (by linarith)
  have hE1 : 4 / (x * H) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hReU : (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) x (x + H)).re ≤ E :=
    (Complex.re_le_norm _).trans hU
  have ha0 : 0 < x - H := by linarith
  have hwL : 0 < 1 / (x - H) - 1 / x := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha0 (by linarith)
  have hψL : chebyshevLagWindow (x - H) x / (1 / (x - H) - 1 / x) ≤ Chebyshev.psi x := by
    rw [div_le_iff₀ hwL]
    exact (chebyshevLagWindow_bounds ha0 (by linarith)).2
  rw [chebyshevLagWindow_div_eq (by linarith) (by linarith)] at hψL
  have hLL : x - H ≤ Real.log (x / (x - H)) / (1 / (x - H) - 1 / x) := by
    rw [le_div_iff₀ hwL]
    exact (log_div_le_mul_inv_sub ha0 (by linarith)).1
  have hEL : 0 ≤ (trivialZeroSeriesReal (x - H) / (x - H) - trivialZeroSeriesReal x / x)
      / (1 / (x - H) - 1 / x) :=
    div_nonneg (sub_nonneg.mpr (trivialZeroSeriesReal_div_anti (by linarith) (by linarith))) hwL.le
  have hReL : -E ≤ (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) (x - H) x).re :=
    neg_le_of_abs_le ((Complex.abs_re_le_norm _).trans hL)
  rw [abs_le]
  constructor <;> linarith

/-! ### 4. The rate `7/8` -/

/-- `x^{7/8} ≤ x/2` for `x ≥ 256`. -/
private theorem rpow_seven_eighths_le_half {x : ℝ} (hx : 256 ≤ x) :
    x ^ (7 / 8 : ℝ) ≤ x / 2 := by
  have hx0 : 0 < x := by linarith
  have h8 : (2 : ℝ) ≤ x ^ (1 / 8 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num) hx (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have h256 : (256 : ℝ) ^ (1 / 8 : ℝ) = 2 := by
      rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, show (1 / 8 : ℝ) = ((8 : ℕ) : ℝ)⁻¹ by norm_num,
        Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
    linarith
  have hsplit : x = x ^ (7 / 8 : ℝ) * x ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hp := Real.rpow_pos_of_pos hx0 (7 / 8 : ℝ)
  nlinarith

/-- **Conditional prime error at rate `7/8`.** There is `C ≥ 0` such that `|ψ(x) − x| ≤ C x^{7/8}`
for every `x ≥ 256` for which all zeros of height `≤ √x` have real part `≤ ¾`. -/
theorem exists_abs_psi_sub_self_le_seven_eighths :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 256 ≤ x →
      (∀ q : XiZeroCopy, |(q.1 : ℂ).im| ≤ Real.sqrt x → (q.1 : ℂ).re ≤ 3 / 4) →
        |Chebyshev.psi x - x| ≤ C * x ^ (7 / 8 : ℝ) := by
  set W : ℝ := ∑' q, zeroWeight 1 q
  set V : ℝ := ∑' q : XiZeroCopy, |(q.1 : ℂ).im|⁻¹ ^ (1 + 1 / 2 : ℝ)
  have hW : 0 ≤ W := tsum_nonneg (zeroWeight_nonneg 1)
  have hV : 0 ≤ V := tsum_nonneg fun q => Real.rpow_nonneg (inv_nonneg.mpr (abs_nonneg _)) _
  refine ⟨4 + 16 * (W + V), by positivity, fun x hx hlow => ?_⟩
  have hx0 : 0 < x := by linarith
  set H : ℝ := x ^ (7 / 8 : ℝ)
  have hH1 : 1 ≤ H := Real.one_le_rpow (by linarith) (by norm_num)
  have hHx : H ≤ x / 2 := rpow_seven_eighths_le_half hx
  have hH0 : 0 < H := by linarith
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  -- exponent bookkeeping
  have hxH : x / H = x ^ (1 / 8 : ℝ) := by
    rw [div_eq_iff hH0.ne', ← Real.rpow_add hx0]; norm_num
  have htail : Real.sqrt x ^ (-(1 / 2 : ℝ)) = x ^ (-(1 / 4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]; norm_num
  have hlowpow : x ^ (1 / 8 : ℝ) * x ^ (3 / 4 : ℝ) = x ^ (7 / 8 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hhighpow : x ^ (1 / 8 : ℝ) * (x * x ^ (-(1 / 4 : ℝ))) = x ^ (7 / 8 : ℝ) := by
    conv_lhs => rw [show x * x ^ (-(1 / 4 : ℝ)) = x ^ (1 : ℝ) * x ^ (-(1 / 4 : ℝ)) by
      rw [Real.rpow_one]]
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
  have hE : ∀ a b : ℝ, x / 2 ≤ a → 1 ≤ a → b - a = H → b ≤ 2 * x →
      ‖∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a b‖ ≤
        16 * (W + V) * x ^ (7 / 8 : ℝ) := by
    intro a b hxa ha hab hb
    have h := norm_tsum_window_le_split (T := Real.sqrt x) hlow one_pos le_rfl (by linarith) hH0
      hxa ha hab hb
    have hab1 := tsum_zeroWeight_above_le (θ := 1) one_pos hsq
    rw [Real.rpow_one, hxH] at h
    have hx8 := Real.rpow_pos_of_pos hx0 (1 / 8 : ℝ)
    have hx34 := Real.rpow_pos_of_pos hx0 (3 / 4 : ℝ)
    have htail' : ∑' q : XiZeroCopy, (if Real.sqrt x < |(q.1 : ℂ).im| then zeroWeight 1 q else 0)
        ≤ x ^ (-(1 / 4 : ℝ)) * V := by
      rw [← htail]; exact hab1
    have hx14 := Real.rpow_pos_of_pos hx0 (-(1 / 4 : ℝ))
    calc _ ≤ 16 * x ^ (1 / 8 : ℝ) * (x ^ (3 / 4 : ℝ) * W +
          x * ∑' q : XiZeroCopy, (if Real.sqrt x < |(q.1 : ℂ).im| then zeroWeight 1 q else 0)) := h
      _ ≤ 16 * x ^ (1 / 8 : ℝ) * (x ^ (3 / 4 : ℝ) * W + x * (x ^ (-(1 / 4 : ℝ)) * V)) := by
          gcongr
      _ = 16 * (W * (x ^ (1 / 8 : ℝ) * x ^ (3 / 4 : ℝ)) +
            V * (x ^ (1 / 8 : ℝ) * (x * x ^ (-(1 / 4 : ℝ))))) := by ring
      _ = 16 * (W + V) * x ^ (7 / 8 : ℝ) := by rw [hlowpow, hhighpow]; ring
  have hU := hE x (x + H) (by linarith) (by linarith) (by ring) (by linarith)
  have hL := hE (x - H) x (by linarith) (by linarith) (by ring) (by linarith)
  have hψ := abs_psi_sub_self_le_of_windows (by linarith) hH1 hHx hU hL
  have hlog2 : Real.log (2 * Real.pi) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h1 := Real.pi_lt_d2
    have h2 : (7.38 : ℝ) ≤ Real.exp 2 := by
      have := Real.exp_one_gt_d9
      have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    linarith
  nlinarith

/-! ### 5. The reciprocal-Mangoldt error below the onset -/

/-- `log(|γ| + 3) ≤ L + 2` when `|γ| ≤ e^L`, `L ≥ 0`. -/
private theorem log_abs_add_three_le' {γ L : ℝ} (hL : 0 ≤ L) (hγ : |γ| ≤ Real.exp L) :
    Real.log (|γ| + 3) ≤ L + 2 := by
  have he1 : 1 ≤ Real.exp L := Real.one_le_exp hL
  have hle : |γ| + 3 ≤ 4 * Real.exp L := by linarith
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  calc Real.log (|γ| + 3) ≤ Real.log (4 * Real.exp L) :=
        Real.log_le_log (by positivity) hle
    _ = Real.log 4 + L := by rw [Real.log_mul (by norm_num) (Real.exp_pos L).ne', Real.log_exp]
    _ ≤ L + 2 := by linarith

/-- **The reciprocal-Mangoldt error is exponentially small below the onset.** There are `K > 0`,
`a₁`, `C ≥ 0` such that window positivity at `a ≥ a₁` gives `|E_M(t) + γ| ≤ C e^{−t/8}` for every
`t > 0` with `K(t + 2) ≤ a`, where `E_M(t) = Σ_{n ≤ e^t} Λ(n)/n − t`. -/
theorem exists_abs_reciprocalMangoldtError_add_euler_le_of_zetaWindowPositive :
    ∃ K a₁ C : ℝ, 0 < K ∧ 0 ≤ C ∧ ∀ a : ℝ, a₁ ≤ a → ZetaWindowPositive a →
      ∀ t : ℝ, 0 < t → K * (t + 2) ≤ a →
        |reciprocalMangoldtError t + Real.eulerMascheroniConstant| ≤
          C * Real.exp (-(t / 8)) := by
  obtain ⟨K₁, a₁, C₁, hK₁, hC₁, hv⟩ := exists_abs_mertensLagPrimitive_le_of_zetaWindowPositive
  obtain ⟨K₂, a₂, hK₂, hzero⟩ := exists_abs_re_sub_half_lt_quarter_of_hodgeIndex
  obtain ⟨Cψ, hCψ, hψ⟩ := exists_abs_psi_sub_self_le_seven_eighths
  have hL4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨K₁ + K₂, max a₁ a₂, C₁ + Cψ + 2 * (Real.log 4 + 5), by positivity, by positivity,
    fun a ha hW t ht hKt => ?_⟩
  have hK1t : K₁ * (t + 2) ≤ a := by nlinarith
  have hvt := hv a (le_trans (le_max_left _ _) ha) hW t ht hK1t
  have hid := mertensLagPrimitive_eq_reciprocalMangoldtError ht.le
  have hE := Real.exp_pos t
  have hsplit : reciprocalMangoldtError t + Real.eulerMascheroniConstant =
      mertensLagPrimitive t + (Chebyshev.psi (Real.exp t) - Real.exp t) / Real.exp t := by
    rw [hid]; ring
  have hdec : Real.exp (-(t / 4)) ≤ Real.exp (-(t / 8)) := Real.exp_le_exp.mpr (by linarith)
  have hpsi_err : |(Chebyshev.psi (Real.exp t) - Real.exp t) / Real.exp t| ≤
      (Cψ + 2 * (Real.log 4 + 5)) * Real.exp (-(t / 8)) := by
    rw [abs_div, abs_of_pos hE, div_le_iff₀ hE]
    rcases le_or_gt (Real.log 256) t with hbig | hsmall
    · -- large `t`: the zero-location input
      have hx : (256 : ℝ) ≤ Real.exp t := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 256)]; exact Real.exp_le_exp.mpr hbig
      have hH := hodgeIndexAtLevel_of_zetaWindowPositive hW
      have hlow : ∀ q : XiZeroCopy, |(q.1 : ℂ).im| ≤ Real.sqrt (Real.exp t) →
          (q.1 : ℂ).re ≤ 3 / 4 := by
        intro q hq
        rw [Real.sqrt_eq_rpow, ← Real.exp_mul] at hq
        have hlog := log_abs_add_three_le' (L := t * (1 / 2)) (by positivity) hq
        have hsz : K₂ * Real.log (|(q.1 : ℂ).im| + 3) ≤ a := by
          have : K₂ * Real.log (|(q.1 : ℂ).im| + 3) ≤ K₂ * (t * (1 / 2) + 2) :=
            mul_le_mul_of_nonneg_left (by linarith) hK₂.le
          nlinarith
        have h := hzero a (le_trans (le_max_right _ _) ha) hH _
          (xiZeroCopy_mem_zetaZeroConfig_carrier q) hsz
        linarith [(abs_lt.mp h).2]
      have hb := hψ _ hx hlow
      have hpow : Real.exp t ^ (7 / 8 : ℝ) = Real.exp (-(t / 8)) * Real.exp t := by
        rw [← Real.exp_mul, ← Real.exp_add]; ring_nf
      rw [hpow] at hb
      have : 0 ≤ 2 * (Real.log 4 + 5) * Real.exp (-(t / 8)) * Real.exp t := by positivity
      nlinarith
    · -- small `t`: Chebyshev's bound
      have hψle := Chebyshev.psi_le_const_mul_self (Real.exp_pos t).le
      have hψ0 := Chebyshev.psi_nonneg (Real.exp t)
      have h8 : 1 / 2 ≤ Real.exp (-(t / 8)) := by
        have hl : Real.log 256 = 8 * Real.log 2 := by
          rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
        have hlt : -(t / 8) > -Real.log 2 := by linarith
        have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
          rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
        linarith [Real.exp_lt_exp.mpr hlt]
      have habs : |Chebyshev.psi (Real.exp t) - Real.exp t| ≤ (Real.log 4 + 5) * Real.exp t := by
        rw [abs_le]; constructor <;> nlinarith
      have : (Real.log 4 + 5) * Real.exp t ≤
          2 * (Real.log 4 + 5) * Real.exp (-(t / 8)) * Real.exp t := by
        nlinarith
      nlinarith [mul_nonneg hCψ (mul_nonneg (Real.exp_pos (-(t / 8))).le hE.le)]
  rw [hsplit]
  have h1 : |mertensLagPrimitive t| ≤ C₁ * Real.exp (-(t / 8)) :=
    hvt.trans (mul_le_mul_of_nonneg_left hdec hC₁)
  calc _ ≤ |mertensLagPrimitive t| + |(Chebyshev.psi (Real.exp t) - Real.exp t) / Real.exp t| :=
        abs_add_le _ _
    _ ≤ C₁ * Real.exp (-(t / 8)) + (Cψ + 2 * (Real.log 4 + 5)) * Real.exp (-(t / 8)) :=
        add_le_add h1 hpsi_err
    _ = (C₁ + Cψ + 2 * (Real.log 4 + 5)) * Real.exp (-(t / 8)) := by ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
