import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The non-archimedean principal value of Connes' Appendix II, Lemma 2

Formalization of the computational core of Lemma 2 of Appendix II of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Connes compares his own principal value `∫'` (fixed by the requirement that the Fourier transform
of the regularizing distribution vanish at `1`, Theorem V.3) with Weil's `Pfw`.  In the
non-archimedean case the two differ by a multiple of `h(1)`, and the multiple is shown to vanish by
computing `⟨log |·| , 1̂_Y⟩ = A + B` with (Appendix II (29))

  `A = -(1/q) ∫_{π⁻¹R*} α(x) (log q) dx`,   `B = (1 - 1/q) ∫_R log|x| dx`,

and checking `A + B = 0`.

Two hypothesis-free bricks are proved here.

* `integral_eq_zero_of_translationCharacter` — the orthogonality principle behind `A`.  On a
  translation-invariant measure, a function satisfying `χ(x+t) = χ(t)χ(x)` and taking some value
  `≠ 1` integrates to zero (no integrability hypothesis is needed).  Applied to `y ↦ α(π⁻¹ y)` on `R` (which is
  nontrivial exactly because `α` is ramified at level `π⁻¹R`), this gives `∫_R α(π⁻¹y) dy = 0`,
  whence Connes' `A = (1/q) log q`.
* `connes_shellLogSeries` — the shell series behind `B`.  Since `vol(πⁿR*) = q^{-n}(1 - 1/q)` and
  `log|x| = -n log q` on `πⁿR*`, one has
  `B = (1-1/q)² ∑_{n≥0} (-n log q) q^{-n} = -q⁻¹ log q`.
* `connes_nonArch_A_add_B_eq_zero` — the conclusion `A + B = 0` of Appendix II (29).
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory

/-- **Character orthogonality on a translation-invariant measure.**  If `χ` is integrable and
satisfies the twisted translation law `χ (x + t) = χ t * χ x`, and if `χ t ≠ 1` for some `t`, then
`χ` integrates to zero.  This is the engine of Connes' Appendix II (29), step `A`. -/
theorem integral_eq_zero_of_translationCharacter {G : Type*} [MeasurableSpace G]
    [AddGroup G] [MeasurableAdd G] {μ : Measure G} [μ.IsAddRightInvariant]
    {χ : G → ℂ}
    (hmul : ∀ x t : G, χ (x + t) = χ t * χ x) {t : G} (ht : χ t ≠ 1) :
    ∫ x, χ x ∂μ = 0 := by
  have hstep : ∫ x, χ x ∂μ = χ t * ∫ x, χ x ∂μ := by
    calc ∫ x, χ x ∂μ = ∫ x, χ (x + t) ∂μ := (integral_add_right_eq_self χ t).symm
      _ = ∫ x, χ t * χ x ∂μ := by simp_rw [hmul]
      _ = χ t * ∫ x, χ x ∂μ := integral_const_mul _ _
  have : (1 - χ t) * ∫ x, χ x ∂μ = 0 := by rw [sub_mul, one_mul, ← hstep]; ring
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (by linear_combination -h : χ t = 1) ht
  · exact h

/-- **Appendix II (29), term `B`.**  The shell series of the non-archimedean logarithm. -/
theorem connes_shellLogSeries (q : ℝ) (hq : 1 < q) :
    (1 - 1 / q) ^ 2 * ∑' n : ℕ, (-(n : ℝ) * Real.log q) * (1 / q) ^ n
      = -(Real.log q) / q := by
  have hq0 : (0:ℝ) < q := lt_trans one_pos hq
  have ht : ‖(1 / q : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [div_lt_one hq0]; exact hq
  have hgeo : ∑' n : ℕ, (n : ℝ) * (1 / q) ^ n = (1 / q) / (1 - 1 / q) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one ht
  have hne : (1 - 1 / q : ℝ) ≠ 0 := by
    have : (1:ℝ) / q < 1 := by rw [div_lt_one hq0]; exact hq
    linarith
  have hrw : ∀ n : ℕ, (-(n : ℝ) * Real.log q) * (1 / q) ^ n
      = (-Real.log q) * ((n : ℝ) * (1 / q) ^ n) := by intro n; ring
  have hq1 : (q - 1 : ℝ) ≠ 0 := by linarith
  rw [tsum_congr hrw, tsum_mul_left, hgeo]
  field_simp

/-- **Appendix II (29).**  `A + B = 0`: Connes' principal value `∫'` agrees with Weil's `Pfw` at a
non-archimedean place with unramified basic character. -/
theorem connes_nonArch_A_add_B_eq_zero (q : ℝ) (hq : 1 < q) :
    (1 / q) * Real.log q
        + (1 - 1 / q) ^ 2 * ∑' n : ℕ, (-(n : ℝ) * Real.log q) * (1 / q) ^ n = 0 := by
  have hq0 : (0:ℝ) < q := lt_trans one_pos hq
  rw [connes_shellLogSeries q hq]
  field_simp
  ring

end GaloisForLFunctions.RHTower
