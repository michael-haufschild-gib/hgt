import GaloisForLFunctions.FloorFreeArithmetic.MomentsOnWindowsAmplifyTheDepth
import GaloisForLFunctions.SurfaceOfSpecZ.TheGapMethodIterates

/-!
# The primes attain the top rate on every window

Uniform attainment of a finite top layer holds already at the prime logarithms. Every point of
a late window has a prime within the gap `x^{2/3}` below it, and the trace of a configuration
of width `b` moves by at most `e^{(b − 1/3)u}` over such a gap, which is of smaller order than
the rate `e^{bu}`. So every late window of every positive length contains a prime `p` with
`|2 Re S(log p)| ≥ c p^b`.

Contrapositively, for `ζ`: arbitrarily late windows of one fixed length on which the trace at
every prime is `o(p^b)` give the asymptotic abscissa law. The hypothesis reads only the primes
of a window of bounded ratio and compares the trace with its own rate.

* `finite_top_seen_at_primes_on_every_window`: uniform attainment at the primes.
* `asymptoticAbscissaLaw_of_prime_window_nonAttainment`: the receiver.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open SquareRootThreshold Zeta23 SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality

/-- **Uniform attainment at the primes.** A finite nonempty active top layer at depth `b ≥ 0`
of a configuration of width `b` gives, in every late window of every length `L > 0`, a prime `p`
with `c p^b ≤ |2 Re S(log p)|`. -/
theorem finite_top_seen_at_primes_on_every_window {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {b L : ℝ} (hb : 0 ≤ b) (htop : TopDepth Z b) (hL : 0 < L) (S : Finset ℂ)
    (hS : ∀ z, z ∈ S ↔ z ∈ positiveTopSupport Z b) (hne : S.Nonempty)
    (hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0)
    (hwid : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + b) :
    ∃ c U : ℝ, 0 < c ∧ ∀ T : ℝ, U ≤ T → ∃ p : ℕ, p.Prime ∧ Real.log p ∈ Icc T (T + L) ∧
      c * (p : ℝ) ^ b ≤ |2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re| := by
  obtain ⟨c₀, U₁, hc₀, hwin⟩ :=
    finite_top_seen_on_every_window hZ htop (half_pos hL) S hS hne hreal
  obtain ⟨G, U₀, hG, -, hnear⟩ := exists_log_degree_near (θ := (2 : ℝ) / 3)
    (by norm_num) (powGaps_primes (by norm_num) (by norm_num))
  set Lam : ℝ := ∑' z : ℂ, ‖lagCoeff Z (boxSpline 1 3) z‖ * ‖z‖ with hLam
  have hLam0 : 0 ≤ Lam := tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  -- beyond some point the prime gap is short and costs less than half of the attained size
  have hexp : Tendsto (fun u : ℝ => Real.exp (((2 : ℝ) / 3 - 1) * u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (2 : ℝ) / 3 - 1 < 0))
  have hgap1 : Tendsto (fun u : ℝ => 2 * G * Real.exp (((2 : ℝ) / 3 - 1) * u)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hexp.const_mul (2 * G)
  have hgap2 : Tendsto (fun u : ℝ => 4 * Lam * G * Real.exp (((2 : ℝ) / 3 - 1) * u)) atTop
      (𝓝 0) := by
    simpa only [mul_zero] using hexp.const_mul (4 * Lam * G)
  obtain ⟨U₂, hU₂⟩ := eventually_atTop.mp
    ((hgap1.eventually_le_const (half_pos hL)).and
      ((hgap2.eventually_le_const (half_pos hc₀)).and (eventually_ge_atTop 0)))
  refine ⟨c₀ / 2, max U₁ (max U₀ U₂), half_pos hc₀, fun T hT => ?_⟩
  have hT₁ : U₁ ≤ T := (le_max_left _ _).trans hT
  have hT₀ : U₀ ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hT₂ : U₂ ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  obtain ⟨u₀, hu₀, hbig⟩ := hwin (T + L / 2) (by linarith only [hT₁, hL])
  have hTu : T ≤ u₀ := by linarith only [hu₀.1, hL]
  obtain ⟨hshort, hcost, hu0⟩ := hU₂ u₀ (hT₂.trans hTu)
  obtain ⟨p, hp, -, hlog0, hlogu, hgap⟩ := hnear u₀ (hT₀.trans hTu)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hp : p.Prime).pos
  refine ⟨p, hp, ⟨by linarith only [hgap, hshort, hu₀.1], by linarith only [hlogu, hu₀.2]⟩, ?_⟩
  have hE : 0 < Real.exp (b * u₀) := Real.exp_pos _
  -- the trace at `u₀` has its full rate
  have hfull : c₀ * Real.exp (b * u₀) ≤ |2 * (lagStructure Z (boxSpline 1 3) u₀).re| := by
    rw [two_re_lagStructure_eq_normTrace_mul Z b u₀, abs_mul, abs_of_pos hE]
    exact mul_le_mul_of_nonneg_right hbig hE.le
  -- the gap to the prime costs less than half of it
  have hlip := abs_two_re_lagStructure_sub_le_of_width hZ hb hwid hlog0 hlogu
  have hmove : |2 * (lagStructure Z (boxSpline 1 3) u₀).re -
      2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re| ≤ c₀ / 2 * Real.exp (b * u₀) := by
    have h1 : 2 * Lam * (u₀ - Real.log p) ≤
        4 * Lam * G * Real.exp (((2 : ℝ) / 3 - 1) * u₀) := by
      have := mul_le_mul_of_nonneg_left hgap (mul_nonneg zero_le_two hLam0)
      linarith only [this]
    exact hlip.trans (mul_le_mul_of_nonneg_right (h1.trans hcost) hE.le)
  have htri := abs_sub_abs_le_abs_sub (2 * (lagStructure Z (boxSpline 1 3) u₀).re)
    (2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re)
  have hpow : (p : ℝ) ^ b ≤ Real.exp (b * u₀) := by
    rw [Real.rpow_def_of_pos hp0]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hlogu hb
    linarith only [this, mul_comm (Real.log p) b]
  have hhalf : c₀ / 2 * (p : ℝ) ^ b ≤ c₀ / 2 * Real.exp (b * u₀) :=
    mul_le_mul_of_nonneg_left hpow (half_pos hc₀).le
  linarith only [hfull, hmove, htri, hhalf]

/-- **Non-attainment at the primes gives the abscissa law.** Suppose that for every depth
`b > 0` bounding all zeros there is a length `L > 0` and arbitrarily late windows of length `L`
in which every prime `p` has `|2 Re S(log p)| ≤ ε p^b`, for every `ε > 0`. Then the asymptotic
abscissa law holds. -/
theorem asymptoticAbscissaLaw_of_prime_window_nonAttainment
    (h : ∀ b : ℝ, 0 < b → TopDepth zetaZeroConfig b → ∃ L : ℝ, 0 < L ∧
      ∀ ε : ℝ, 0 < ε → ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
        Real.log p ∈ Icc T (T + L) →
        |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re| ≤ ε * (p : ℝ) ^ b) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  obtain ⟨b, hb, htop, S, hS, hne⟩ := exists_finite_top_of_not_abscissaLaw hnot
  have hwid : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + b := by
    intro ρ hρ
    by_cases hre : 1 / 2 < ρ.re
    · have hx := htop (ρ - 1 / 2) (evenCoeff_spline_sees hρ hre)
      have he : (ρ - 1 / 2).re = ρ.re - 1 / 2 := by simp
      rw [he] at hx
      linarith only [hx]
    · linarith only [le_of_not_gt hre, hb]
  obtain ⟨L, hL, hsmall⟩ := h b hb htop
  obtain ⟨c, U, hc, hbig⟩ := finite_top_seen_at_primes_on_every_window
    temperedConfig_zetaZeroConfig hb.le htop hL S hS hne
    (fun z hz _ => evenCoeff_spline_real hz) hwid
  obtain ⟨T, hT, hle⟩ := hsmall (c / 2) (half_pos hc) U
  obtain ⟨p, hp, hwin, hge⟩ := hbig T hT
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpb : 0 < (p : ℝ) ^ b := Real.rpow_pos_of_pos hp0 b
  have := hle p hp hwin
  nlinarith only [hge, this, hpb, hc]

end GaloisForLFunctions.FloorFreeArithmetic
