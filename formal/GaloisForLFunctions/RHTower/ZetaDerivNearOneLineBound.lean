import GaloisForLFunctions.RHTower.ZetaNearOneLineBound
import GaloisForLFunctions.RHTower.Sieve.ZetaDerivBound

/-!
# The derivative of `ζ` near the one-line

Cauchy's estimate on the disc of radius `1/(2 log|t|)` centred at a point of the one-line turns the
strip growth bound `|ζ| ≤ 8 log|t| + 39` into `|ζ'| ≤ 110 (log|t|)²`.  The radius is chosen so that
the disc stays inside the region where the strip bound applies: it reaches left only to
`1 − 1/(2 log|t|)`, and every point `w` of the disc has `log|w.im| ≤ 2 log|t|`, so the strip
hypothesis `1 − 1/log|w.im| ≤ w.re` holds throughout.

This is the estimate that lets a three-four-one lower bound at one abscissa be slid to every smaller
abscissa, which is how the `δ`-free lower bound for `ζ` on the closed half-plane `σ ≥ 1` is obtained.
-/

namespace RHTower

open Complex Metric

noncomputable section

/-- **The derivative bound near the one-line.**  `|ζ'(σ+it)| ≤ 110 (log|t|)²` for `1 ≤ σ ≤ 3/2`
and `|t| ≥ 9`. -/
theorem norm_deriv_riemannZeta_le_log_sq {s : ℂ}
    (hσ1 : 1 ≤ s.re) (hσ2 : s.re ≤ 3 / 2) (ht : 9 ≤ |s.im|) :
    ‖deriv riemannZeta s‖ ≤ 110 * (Real.log |s.im|) ^ 2 := by
  have ht8 : (8 : ℝ) ≤ |s.im| := by linarith
  have htpos : (0 : ℝ) < |s.im| := by linarith
  set L : ℝ := Real.log |s.im| with hLdef
  have hL2 : (2 : ℝ) ≤ L := two_le_log_of_eight_le ht8
  have hL0 : (0 : ℝ) < L := by linarith
  set R : ℝ := 1 / (2 * L) with hRdef
  have hR0 : (0 : ℝ) < R := by rw [hRdef]; positivity
  have hRle : R ≤ 1 / 4 := by
    rw [hRdef]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- every point of the closed disc has large imaginary part
  have him : ∀ w : ℂ, ‖w - s‖ ≤ R → |s.im| - R ≤ |w.im| ∧ |w.im| ≤ |s.im| + R := by
    intro w hw
    have hd : |w.im - s.im| ≤ R := by
      have h := Complex.abs_im_le_norm (w - s)
      rw [Complex.sub_im] at h
      linarith
    constructor
    · have := abs_sub_abs_le_abs_sub s.im w.im
      rw [show s.im - w.im = -(w.im - s.im) by ring, abs_neg] at this
      linarith
    · have := abs_sub_abs_le_abs_sub w.im s.im
      linarith
  have hre : ∀ w : ℂ, ‖w - s‖ ≤ R → s.re - R ≤ w.re ∧ w.re ≤ s.re + R := by
    intro w hw
    have hd : |w.re - s.re| ≤ R := by
      have h := Complex.abs_re_le_norm (w - s)
      rw [Complex.sub_re] at h
      linarith
    have := abs_le.mp hd
    constructor <;> linarith [this.1, this.2]
  -- `ζ` is holomorphic on the closed disc
  have hne : ∀ w ∈ closedBall s R, w ≠ (1 : ℂ) := by
    intro w hw hcon
    have hws : ‖w - s‖ ≤ R := by
      rw [← dist_eq_norm]
      exact mem_closedBall.mp hw
    have hlow := (him w hws).1
    rw [hcon] at hlow
    simp only [Complex.one_im, abs_zero] at hlow
    linarith
  -- the boundary bound
  have hbound : ∀ w ∈ sphere s R, ‖riemannZeta w‖ ≤ 16 * L + 39 := by
    intro w hw
    have hws : ‖w - s‖ = R := mem_sphere_iff_norm.mp hw
    have hwsle : ‖w - s‖ ≤ R := le_of_eq hws
    obtain ⟨hlow, hhigh⟩ := him w hwsle
    obtain ⟨hrelow, hrehigh⟩ := hre w hwsle
    have hw8 : (8 : ℝ) ≤ |w.im| := by linarith
    have hwpos : (0 : ℝ) < |w.im| := by linarith
    have hwlog2 : Real.log |w.im| ≤ 2 * L := by
      have hsq : |w.im| ≤ |s.im| ^ (2 : ℕ) := by nlinarith [ht, hRle]
      have h2 : Real.log |w.im| ≤ Real.log (|s.im| ^ (2 : ℕ)) :=
        Real.log_le_log hwpos hsq
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith
    have hwlog0 : (0 : ℝ) < Real.log |w.im| := by
      have := two_le_log_of_eight_le hw8
      linarith
    have hstrip : 1 - 1 / Real.log |w.im| ≤ w.re := by
      have hinv : 1 / (2 * L) ≤ 1 / Real.log |w.im| :=
        div_le_div_of_nonneg_left (by norm_num) hwlog0 hwlog2
      have : s.re - R ≤ w.re := hrelow
      rw [hRdef] at this
      linarith
    have hstrip2 : w.re ≤ 2 := by linarith
    have hzeta := norm_riemannZeta_le_log_near_one hstrip hstrip2 hw8
    linarith
  -- Cauchy's estimate
  have hcauchy := Sieve.norm_deriv_riemannZeta_le (c := s) (R := R) (C := 16 * L + 39)
    hR0 hne hbound
  have hval : (16 * L + 39) / R = (16 * L + 39) * (2 * L) := by
    rw [hRdef]
    field_simp
  rw [hval] at hcauchy
  nlinarith [hcauchy, hL2, hL0]

end

end RHTower
