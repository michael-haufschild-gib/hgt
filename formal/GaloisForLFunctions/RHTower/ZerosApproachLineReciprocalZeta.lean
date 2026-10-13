import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse
import GaloisForLFunctions.RHTower.InvZetaAbscissaSubpolynomial
import GaloisForLFunctions.HTGeometry.LogDerivativeBound

/-!
# Zeros approaching the line give subpolynomial reciprocal zeta at large heights

**Theorem** (`exists_norm_riemannZeta_ge_rpow_of_zerosApproachLine`).  If the zeros of `ζ` approach
the critical line, then for every `0 < κ < ½` and `ε > 0` there are `c > 0` and `T` with
`|ζ(s)| ≥ c (2 + |Im s|)^{−ε}` whenever `Re s ≥ ½ + κ` and `|Im s| ≥ T`.

Only finitely many zeros lie right of `½ + κ/2`, so above their heights `ζ` is zero-free right of
`½ + κ/2` (`exists_zeta_ne_zero_above_of_zerosApproachLine`).  The three-circles argument centred
at `4 + it` only sees heights within `4` of `t`
(`exists_zeta_lower_bound_subpolynomial_of_zeroFree_above`).

With `lindelofCriticalLine_of_zerosApproachLine`, the zeros approaching the line control `ζ` from
both sides right of the line at large heights: `|ζ(s)| = |t|^{o(1)}` uniformly on `Re s ≥ ½ + κ`.
A global zero-free half-plane is not needed, only one above some height.

**Corollary** (`exists_norm_logDeriv_riemannZeta_le_of_zerosApproachLine`).  Under ZAL,
`|ζ'/ζ(s)| ≤ ε log|Im s|` on `Re s ≥ ½ + κ` at large heights, for every `ε > 0`: the logarithmic
derivative is `o(log t)` right of the line, as under RH (Littlewood).
-/

open Complex Set Metric

namespace RHTower

noncomputable section

open BacklundConverse LindelofSparse

/-- **Under ZAL, `ζ` is zero-free right of `½ + h` above some height.** -/
theorem exists_zeta_ne_zero_above_of_zerosApproachLine (hZ : ZerosApproachLine) {h : ℝ}
    (hh : 0 < h) :
    ∃ T₀ : ℝ, ∀ z : ℂ, 1 / 2 + h < z.re → T₀ ≤ |z.im| → riemannZeta z ≠ 0 := by
  obtain ⟨M, hM⟩ := ((finite_re_gt_of_zerosApproachLine hZ hh).image
    fun q : XiZeroCopy => |((q.1 : ℂ)).im|).bddAbove
  refine ⟨M + 1, fun z hz hzT h0 => ?_⟩
  by_cases h1 : z.re < 1
  · obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip h0 (by linarith) h1
    have hmem : q ∈ {q : XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re} := by
      simp only [mem_setOf_eq, hq]; exact hz
    have := hM ⟨q, hmem, rfl⟩
    simp only [hq] at this
    linarith
  · exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h1) h0

/-- **Under ZAL, `1/ζ` is subpolynomial right of the line at large heights.** -/
theorem exists_norm_riemannZeta_ge_rpow_of_zerosApproachLine (hZ : ZerosApproachLine) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ c T : ℝ, 0 < c ∧ ∀ s : ℂ, 1 / 2 + κ ≤ s.re → T ≤ |s.im| →
      c * (2 + |s.im|) ^ (-ε) ≤ ‖riemannZeta s‖ := by
  obtain ⟨T₀, hT₀⟩ := exists_zeta_ne_zero_above_of_zerosApproachLine hZ (h := κ / 2)
    (by linarith)
  obtain ⟨c, hc, hbd⟩ := exists_zeta_lower_bound_subpolynomial_of_zeroFree_above
    (Θ := 1 / 2 + κ / 2) (T₀ := T₀) (by linarith) (by linarith) hT₀ (δ := κ / 2)
    (by linarith) (by linarith) hε
  exact ⟨c, max 6 (T₀ + 4), hc, fun s hs hT => hbd s (by linarith)
    ((le_max_left _ _).trans hT) ((le_max_right _ _).trans hT)⟩

/-- **Under ZAL, `ζ'/ζ = o(log t)` right of the line at large heights.**  On the disc of radius
`κ/2` about `s` the function `ζ` is zero-free, bounded by `C|t|^{ε₁}` (Lindelöf, from ZAL), and at
the centre it is at least `c|t|^{−ε₁}`; the zero-free log-derivative bound
(`GaloisForLFunctions.HTGeometry.norm_logDeriv_le`) gives `‖ζ'/ζ(s)‖ ≤ (8/κ)(log(M/m) + 1)`. -/
theorem exists_norm_logDeriv_riemannZeta_le_of_zerosApproachLine (hZ : ZerosApproachLine)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ s : ℂ, 1 / 2 + κ ≤ s.re → T ≤ |s.im| →
      ‖logDeriv riemannZeta s‖ ≤ ε * Real.log |s.im| := by
  set ε₁ : ℝ := ε * κ / 32 with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨C₁, hC₁, hup⟩ :=
    lindelofHalfPlane_of_criticalLine (lindelofCriticalLine_of_zerosApproachLine hZ) ε₁ hε₁0
  obtain ⟨c₂, T₂, hc₂, hlow⟩ := exists_norm_riemannZeta_ge_rpow_of_zerosApproachLine hZ hκ hκ1 hε₁0
  obtain ⟨T₀, hT₀⟩ := exists_zeta_ne_zero_above_of_zerosApproachLine hZ (h := κ / 4) (by positivity)
  set K' : ℝ := ε / 2 * Real.log 2 + 8 / κ * (|Real.log (C₁ / c₂)| + 1) with hK'
  refine ⟨max (max T₂ (T₀ + 1)) (max 2 (Real.exp (2 * K' / ε))), fun s hs hT => ?_⟩
  set t : ℝ := s.im with ht
  have hT₂ : T₂ ≤ |t| := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hT₀' : T₀ + 1 ≤ |t| := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have ht2 : 2 ≤ |t| := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have htE : Real.exp (2 * K' / ε) ≤ |t| := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  -- the disc of radius `κ/2` about `s`
  have hball_re : ∀ z ∈ ball s (κ / 2), 1 / 2 + κ / 2 < z.re := by
    intro z hz
    have hd := mem_ball_iff_norm.mp hz
    have := (abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm (z - s)) hd)).1
    rw [Complex.sub_re] at this
    linarith
  have hball_im : ∀ z ∈ ball s (κ / 2), |t| - 1 ≤ |z.im| ∧ |z.im| ≤ |t| + 1 := by
    intro z hz
    have hd := mem_ball_iff_norm.mp hz
    have him := (Complex.abs_im_le_norm (z - s)).trans hd.le
    rw [Complex.sub_im] at him
    have h1 := abs_sub_abs_le_abs_sub t z.im
    have h2 := abs_sub_abs_le_abs_sub z.im t
    rw [abs_sub_comm] at h1
    constructor <;> linarith
  have hne1 : ∀ z ∈ ball s (κ / 2), z ≠ 1 := by
    intro z hz h1
    have := (hball_im z hz).1
    rw [h1, Complex.one_im, abs_zero] at this
    linarith
  have hdiff : DifferentiableOn ℂ riemannZeta (ball s (κ / 2)) := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  have hnz : ∀ z ∈ ball s (κ / 2), riemannZeta z ≠ 0 := fun z hz =>
    hT₀ z (by linarith [hball_re z hz]) (by linarith [(hball_im z hz).1])
  set M : ℝ := C₁ * (|t| + 1) ^ ε₁ with hM
  have hMb : ∀ z ∈ ball s (κ / 2), ‖riemannZeta z‖ ≤ M := by
    intro z hz
    have hi := hball_im z hz
    refine (hup z (by linarith [hball_re z hz]) (by linarith [hi.1])).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hi.2 hε₁0.le) (by linarith)
  set m : ℝ := c₂ * (2 + |t|) ^ (-ε₁) with hm
  have hm0 : 0 < m := by positivity
  have hms : m ≤ ‖riemannZeta s‖ := hlow s hs hT₂
  have hbd := GaloisForLFunctions.HTGeometry.norm_logDeriv_le (f := riemannZeta) (c := s)
    (R := κ / 2) (r := κ / 4) (ρ := 0) le_rfl (by positivity) (by linarith) hdiff hnz hMb hm0
    hms (z := s) (by simp)
  rw [logDeriv_apply]
  -- simplify the bound
  have hsimp : 2 * (Real.log (M / m) + 1) * (κ / 4) / (κ / 2 - κ / 4) / (κ / 4 - 0) =
      8 / κ * (Real.log (M / m) + 1) := by
    have hκne : κ ≠ 0 := hκ.ne'
    rw [show κ / 2 - κ / 4 = κ / 4 by ring, sub_zero]
    field_simp
    ring
  rw [hsimp] at hbd
  -- `log(M/m) ≤ log(C₁/c₂) + 2ε₁ log(2 + |t|)`
  have ht1 : (0 : ℝ) < |t| + 1 := by positivity
  have ht2' : (0 : ℝ) < 2 + |t| := by positivity
  have hMm : M / m = C₁ / c₂ * ((|t| + 1) ^ ε₁ * (2 + |t|) ^ ε₁) := by
    rw [hM, hm, Real.rpow_neg ht2'.le]
    field_simp
  have hlogMm : Real.log (M / m) ≤ |Real.log (C₁ / c₂)| + 2 * ε₁ * Real.log (2 + |t|) := by
    rw [hMm, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow ht1, Real.log_rpow ht2']
    have h1 : Real.log (|t| + 1) ≤ Real.log (2 + |t|) := Real.log_le_log ht1 (by linarith)
    have h2 := le_abs_self (Real.log (C₁ / c₂))
    nlinarith
  have hlog2t : Real.log (2 + |t|) ≤ Real.log 2 + Real.log |t| := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log ht2' (by linarith)
  have hKt : K' ≤ ε / 2 * Real.log |t| := by
    have := Real.log_le_log (Real.exp_pos _) htE
    rw [Real.log_exp] at this
    rw [div_le_iff₀ hε] at this
    linarith
  calc ‖deriv riemannZeta s / riemannZeta s‖
      ≤ 8 / κ * (Real.log (M / m) + 1) := hbd
    _ ≤ 8 / κ * (|Real.log (C₁ / c₂)| + 2 * ε₁ * (Real.log 2 + Real.log |t|) + 1) := by
        gcongr
        have : 2 * ε₁ * Real.log (2 + |t|) ≤ 2 * ε₁ * (Real.log 2 + Real.log |t|) :=
          mul_le_mul_of_nonneg_left hlog2t (by positivity)
        linarith
    _ = 8 / κ * (|Real.log (C₁ / c₂)| + 1) + ε / 2 * Real.log 2 + ε / 2 * Real.log |t| := by
        rw [hε₁]; field_simp; ring
    _ ≤ ε * Real.log |t| := by rw [hK'] at hKt; linarith

end

end RHTower
