import GaloisForLFunctions.RHTower.ZetaZeroDensitySeparatedSelection
import GaloisForLFunctions.RHTower.Sieve.WidthEnvelopeBounds
import GaloisForLFunctions.RHTower.Sieve.RouteTWidthUpper
import GaloisForLFunctions.RHTower.Sieve.RouteTZetaZeroFree

/-!
# The Route-T zero-free region on height boxes

The Route-T zero-free region excludes zeros of `ζ` with `β > 1 - W(γ)` above a fixed height, and its
width dominates the explicit polylogarithmic surrogate `w(τ)` with `τ = 2(γ - 1)/3`.  Since `w` is
antitone in `|τ|`, every zero of `ξ` in the box `T ≤ γ ≤ 2T` has `β ≤ 1 - w(4T/3)`.

For `x` with `L = log x ≥ 6` and `X = x^{2u}` (`0 ≤ u ≤ 1/2`), the explicit form of `w` gives

`x^{-δ w(4X/3)} ≤ exp(-(δ/(4C)) L^{1/10}/(1 + log 4L)²)`,

where `C = 10 · routeTZeroFreeDeltaEnvelopeConstant A`.
-/

namespace RHTower

noncomputable section

open Complex RHTower.Sieve

/-- **Zero-free boxes.** -/
theorem exists_zeroHeightBox_zeroFree :
    ∃ A T₁ : ℝ, 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T → ∀ σ : ℝ, (zeroHeightBox σ T).Nonempty →
      σ ≤ 1 - routeTWidthPolylogLower A (4 * T / 3) := by
  obtain ⟨A, hZF⟩ := exists_routeT_zero_free_region
  set N : ℕ := routeTBandDepthRootThreshold ^ 10 with hN
  refine ⟨A, max 100000 ((2 : ℝ) ^ N), le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro T hT σ ⟨q, hσ, hγ1, hγ2⟩
  set β := (q.1 : ℂ).re with hβ
  set γ := (q.1 : ℂ).im with hγ
  have hT1 : 100000 ≤ T := le_trans (le_max_left _ _) hT
  have hT2 : (2 : ℝ) ^ N ≤ T := le_trans (le_max_right _ _) hT
  have hγ0 : 100000 ≤ γ := le_trans hT1 hγ1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbin : N ≤ routeTBinaryHeight γ := by
    have h1 := log_div_log_two_le_binaryHeight (t := γ) (by linarith)
    have h2 : (N : ℝ) ≤ Real.log γ / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      have := Real.log_le_log (by positivity) (le_trans hT2 hγ1)
      rwa [Real.log_pow] at this
    exact_mod_cast le_trans h2 h1
  have hβ1 : β ≤ 1 := (xiZeroCopy_re_lt_one q).le
  have hζ : riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) = 0 := by
    rw [hβ, hγ, Complex.re_add_im]
    exact riemannZeta_eq_zero_of_xiZeroCopy q
  -- the width at `γ` dominates the surrogate at `4T/3`
  set τ : ℝ := 2 * (γ - 1) / 3 with hτ
  have hτ0 : 0 ≤ τ := by rw [hτ]; linarith
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hτπ : 16 * Real.pi / 3 ≤ |τ| := by rw [abs_of_nonneg hτ0, hτ]; nlinarith
  have hW := routeTWidthPolylogLower_le (A := A) hτπ
  rw [abs_of_nonneg hτ0, show 3 * τ / 2 + 1 = γ by rw [hτ]; ring] at hW
  have hanti : routeTWidthPolylogLower A (4 * T / 3) ≤ routeTWidthPolylogLower A τ := by
    refine routeTWidthPolylogLower_antitone ?_
    rw [abs_of_nonneg hτ0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 4 * T / 3), hτ]
    linarith
  by_contra hcon
  push Not at hcon
  exact hZF β γ hγ0 hbin hβ1 (by linarith) hζ

/-- **The zero-free saving in logarithmic form.** -/
theorem rpow_neg_width_le_exp {A x u δ : ℝ} (hx1 : 1 ≤ x) (hx : 6 ≤ Real.log x) (hu0 : 0 ≤ u)
    (hu : u ≤ 1 / 2) (hδ : 0 ≤ δ) :
    x ^ (-(δ * routeTWidthPolylogLower A (4 * x ^ (2 * u) / 3)))
      ≤ Real.exp (-(δ / (4 * (10 * routeTZeroFreeDeltaEnvelopeConstant A)))
          * (Real.log x ^ (1 / 10 : ℝ) / (1 + Real.log (4 * Real.log x)) ^ 2)) := by
  set L := Real.log x with hL
  have hx0 : 0 < x := by linarith
  set X := x ^ (2 * u) with hX
  have hX1 : 1 ≤ X := Real.one_le_rpow hx1 (by linarith)
  have hlogX : Real.log X = 2 * u * L := by rw [hX, Real.log_rpow hx0]
  set C := 10 * routeTZeroFreeDeltaEnvelopeConstant A with hC
  have hC0 : 0 < C := by rw [hC]; have := routeTZeroFreeDeltaEnvelopeConstant_pos A; positivity
  set τ : ℝ := 4 * X / 3 with hτ
  have hτ1 : 1 ≤ |τ| := by rw [abs_of_nonneg (by positivity), hτ]; linarith
  -- the log-height envelope is at most `4L`
  have hlog43 : Real.log (4 / 3) ≤ 1 / 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    linarith
  have henv : routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)) ≤ 4 * L := by
    refine le_trans (routeTLogHeightEnvelope_le hτ1) ?_
    rw [abs_of_nonneg (by positivity), hτ,
      show 4 * X / 3 = (4 / 3) * X by ring,
      Real.log_mul (by norm_num) (by positivity), hlogX]
    nlinarith
  have hw := routeTWidthPolylogLower_ge (A := A) hτ1 henv (by linarith)
  rw [← hC] at hw
  set Q := (1 + Real.log (4 * L)) ^ 2 with hQ
  have hQ0 : 0 < Q := by
    have : 0 ≤ Real.log (4 * L) := Real.log_nonneg (by linarith)
    rw [hQ]; positivity
  have hL0 : 0 < L := by linarith
  -- `(4L)^{9/10} ≤ 4 L^{9/10}`
  have h49 : (4 * L) ^ (9 / 10 : ℝ) ≤ 4 * L ^ (9 / 10 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hL0.le]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hL0.le _)
    calc (4 : ℝ) ^ (9 / 10 : ℝ) ≤ 4 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := Real.rpow_one 4
  have hwlow : 1 / (4 * C * L ^ (9 / 10 : ℝ) * Q) ≤ routeTWidthPolylogLower A τ := by
    refine le_trans ?_ hw
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : C * (4 * L) ^ (9 / 10 : ℝ) * Q ≤ C * (4 * L ^ (9 / 10 : ℝ)) * Q := by gcongr
    linarith
  -- convert to the exponential
  have hsplit : L = L ^ (1 / 10 : ℝ) * L ^ (9 / 10 : ℝ) := by
    rw [← Real.rpow_add hL0]
    norm_num
  rw [Real.rpow_def_of_pos hx0, ← hL, Real.exp_le_exp]
  have hL910 : 0 < L ^ (9 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hkey : δ / (4 * C) * (L ^ (1 / 10 : ℝ) / Q) ≤ δ * routeTWidthPolylogLower A τ * L := by
    have h1 : δ / (4 * C) * (L ^ (1 / 10 : ℝ) / Q) = δ * (1 / (4 * C * L ^ (9 / 10 : ℝ) * Q)) * L := by
      have e : δ * (1 / (4 * C * L ^ (9 / 10 : ℝ) * Q)) * L
          = δ * (1 / (4 * C * L ^ (9 / 10 : ℝ) * Q)) * (L ^ (1 / 10 : ℝ) * L ^ (9 / 10 : ℝ)) := by
        rw [← hsplit]
      rw [e]
      field_simp
    rw [h1]
    gcongr
  nlinarith

end

end RHTower
