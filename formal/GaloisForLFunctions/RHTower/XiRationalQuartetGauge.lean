/-
An explicit rational-gauge countermodel to divisor recovery from the elementary
completed-xi symmetries.

For real `a, b`, the centered even polynomial

  Q_{a,b}(s) = (((s - 1/2) - a)^2 + b^2) (((s - 1/2) + a)^2 + b^2)

commutes with `s ↦ 1-s` and complex conjugation.  If `a ≠ 0` and `b > 0`,
then `Q_{a,b} * xi` is entire, satisfies the same two symmetries as `xi`, is
nonzero on the real segment `(0,1)`, and has the explicit off-critical zero
`1/2 + a + b i`.

This file formalizes only that concrete analytic countermodel.  It does not
formalize the separate differential-field theorem that multiplication by a
base-field unit preserves translate-generated differential fields.
-/
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.RHTower.XiRealAnchorPositive

namespace RHTower

open Complex

/-- The centered real-even quartic gauge with zero quartet
`1/2 ± a ± b i`. -/
noncomputable def centeredQuartetGauge (a b : ℝ) (s : ℂ) : ℂ :=
  ((((s - (1 / 2 : ℂ)) - (a : ℂ)) ^ 2 + (b : ℂ) ^ 2) *
    (((s - (1 / 2 : ℂ)) + (a : ℂ)) ^ 2 + (b : ℂ) ^ 2))

/-- Completed xi multiplied by the centered quartic gauge. -/
noncomputable def quartetGaugedXi (a b : ℝ) (s : ℂ) : ℂ :=
  centeredQuartetGauge a b s * xi s

/-- The upper-right member of the gauge's zero quartet. -/
noncomputable def quartetPoint (a b : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I

/-- The centered quartic gauge respects the completed functional equation. -/
theorem centeredQuartetGauge_one_sub (a b : ℝ) (s : ℂ) :
    centeredQuartetGauge a b (1 - s) = centeredQuartetGauge a b s := by
  simp only [centeredQuartetGauge]
  ring

/-- The centered quartic gauge has real coefficients. -/
theorem centeredQuartetGauge_conj (a b : ℝ) (s : ℂ) :
    centeredQuartetGauge a b ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (centeredQuartetGauge a b s) := by
  simp only [centeredQuartetGauge, map_mul, map_add, map_sub, map_pow,
    Complex.conj_ofReal]
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  rw [hhalf]

/-- The displayed upper-right quartet point is a gauge zero. -/
theorem centeredQuartetGauge_quartetPoint (a b : ℝ) :
    centeredQuartetGauge a b (quartetPoint a b) = 0 := by
  simp only [centeredQuartetGauge, quartetPoint]
  rw [show
    (((1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I - 1 / 2 - (a : ℂ)) ^ 2 + (b : ℂ) ^ 2) = 0 by
      rw [show (1 / 2 : ℂ) + (a : ℂ) + (b : ℂ) * I - 1 / 2 - (a : ℂ) = (b : ℂ) * I by ring]
      rw [mul_pow, Complex.I_sq]
      ring]
  exact zero_mul _

/-- If `a ≠ 0`, the displayed gauge zero is not on the critical line. -/
theorem quartetPoint_off_critical {a b : ℝ} (ha : a ≠ 0) :
    (quartetPoint a b).re ≠ 1 / 2 := by
  simp only [quartetPoint, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im]
  intro h
  apply ha
  norm_num at h ⊢
  linarith

/-- The gauged completed xi has the explicit quartet zero. -/
theorem quartetGaugedXi_quartetPoint (a b : ℝ) :
    quartetGaugedXi a b (quartetPoint a b) = 0 := by
  rw [quartetGaugedXi, centeredQuartetGauge_quartetPoint, zero_mul]

/-- The gauged completed xi is entire. -/
theorem quartetGaugedXi_analyticAt (a b : ℝ) (s : ℂ) :
    AnalyticAt ℂ (quartetGaugedXi a b) s := by
  apply AnalyticAt.mul
  · unfold centeredQuartetGauge
    fun_prop
  · exact xi_analyticOnNhd_univ s (Set.mem_univ s)

/-- The gauged completed xi satisfies the same functional equation as xi. -/
theorem quartetGaugedXi_one_sub (a b : ℝ) (s : ℂ) :
    quartetGaugedXi a b (1 - s) = quartetGaugedXi a b s := by
  rw [quartetGaugedXi, quartetGaugedXi, centeredQuartetGauge_one_sub, xi_one_sub]

/-- The gauged completed xi satisfies the same Schwarz symmetry as xi. -/
theorem quartetGaugedXi_conj (a b : ℝ) (s : ℂ) :
    quartetGaugedXi a b ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (quartetGaugedXi a b s) := by
  rw [quartetGaugedXi, quartetGaugedXi, centeredQuartetGauge_conj, xi_conj, map_mul]

/-- On the real axis the gauge is the positive real product of two sums of squares. -/
theorem centeredQuartetGauge_ofReal (a b σ : ℝ) :
    centeredQuartetGauge a b (σ : ℂ) =
      ((((σ - 1 / 2) - a) ^ 2 + b ^ 2) * (((σ - 1 / 2) + a) ^ 2 + b ^ 2) : ℝ) := by
  simp only [centeredQuartetGauge]
  push_cast
  ring

/-- A nonreal quartet (`b > 0`) gives a strictly positive gauge on the real axis. -/
theorem centeredQuartetGauge_real_pos {a b σ : ℝ} (hb : 0 < b) :
    0 < (centeredQuartetGauge a b (σ : ℂ)).re := by
  rw [centeredQuartetGauge_ofReal, Complex.ofReal_re]
  exact mul_pos
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hb))
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hb))

/-- The gauged xi remains nonzero on the real segment `(0,1)`. -/
theorem quartetGaugedXi_real_anchor_ne_zero {a b σ : ℝ}
    (hb : 0 < b) (h0 : 0 < σ) (h1 : σ < 1) :
    quartetGaugedXi a b (σ : ℂ) ≠ 0 := by
  apply mul_ne_zero
  · intro hzero
    have hre := congrArg Complex.re hzero
    rw [Complex.zero_re] at hre
    exact (ne_of_gt (centeredQuartetGauge_real_pos (a := a) (σ := σ) hb)) hre
  · intro hzero
    have hre := congrArg Complex.re hzero
    rw [Complex.zero_re] at hre
    exact (ne_of_gt (xi_pos_on_real_anchor h0 h1)) hre

/-- Fully explicit unconditional countermodel: the gauged xi is entire, has both xi
symmetries, is nonzero on `(0,1)`, and has an off-critical zero. -/
theorem exists_xi_symmetric_entire_offcritical_countermodel :
    ∃ F : ℂ → ℂ, ∃ ρ : ℂ,
      (∀ s, AnalyticAt ℂ F s) ∧
      (∀ s, F (1 - s) = F s) ∧
      (∀ s, F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (F s)) ∧
      (∀ σ : ℝ, 0 < σ → σ < 1 → F (σ : ℂ) ≠ 0) ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re ≠ 1 / 2 ∧ F ρ = 0 := by
  refine ⟨quartetGaugedXi (1 / 4) 1, quartetPoint (1 / 4) 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact quartetGaugedXi_analyticAt (1 / 4) 1
  · exact quartetGaugedXi_one_sub (1 / 4) 1
  · exact quartetGaugedXi_conj (1 / 4) 1
  · intro σ h0 h1
    exact quartetGaugedXi_real_anchor_ne_zero (by norm_num) h0 h1
  · norm_num [quartetPoint]
  · norm_num [quartetPoint]
  · exact quartetPoint_off_critical (by norm_num)
  · exact quartetGaugedXi_quartetPoint (1 / 4) 1

/-! ## Exact-source marking

The symmetric gauge preserves the elementary completed-function data above, but it does not
preserve the exact logarithmic source.  At the safe real anchor `s = 0`, its logarithmic derivative
is the explicit nonzero rational number `-608/425`.  Thus an orbit-sensitive source--divisor
incidence can distinguish the countermodel even though FE, Schwarz reality, entire order, and the
DA-gauge-invariant data cannot. -/

/-- Exact derivative of the concrete centered quartet gauge at the real anchor `s = 0`. -/
theorem centeredQuartetGauge_concrete_hasDerivAt_zero :
    HasDerivAt (centeredQuartetGauge (1 / 4) 1) (-19 / 8 : ℂ) 0 := by
  have hfun : centeredQuartetGauge (1 / 4) 1 =
      fun s : ℂ => ((s - 3 / 4) ^ 2 + 1) * ((s - 1 / 4) ^ 2 + 1) := by
    funext s
    norm_num [centeredQuartetGauge]
    ring
  rw [hfun]
  convert
    ((((hasDerivAt_id (𝕜 := ℂ) 0).sub_const (3 / 4)).pow 2).add_const 1).mul
      ((((hasDerivAt_id (𝕜 := ℂ) 0).sub_const (1 / 4)).pow 2).add_const 1)
    using 1
  all_goals norm_num

/-- The concrete orbit-insertion gauge has a nonzero exact logarithmic-source charge at `s = 0`. -/
theorem centeredQuartetGauge_concrete_logDeriv_zero :
    logDeriv (centeredQuartetGauge (1 / 4) 1) 0 = (-608 / 425 : ℂ) := by
  rw [logDeriv_apply, centeredQuartetGauge_concrete_hasDerivAt_zero.deriv]
  norm_num [centeredQuartetGauge]

/-- The logarithmic source of the gauged xi differs from that of xi by the explicit gauge charge. -/
theorem quartetGaugedXi_concrete_logDeriv_zero :
    logDeriv (quartetGaugedXi (1 / 4) 1) 0 =
      (-608 / 425 : ℂ) + logDeriv xi 0 := by
  change logDeriv (fun z => centeredQuartetGauge (1 / 4) 1 z * xi z) 0 = _
  rw [logDeriv_mul 0]
  · rw [centeredQuartetGauge_concrete_logDeriv_zero]
  · norm_num [centeredQuartetGauge]
  · rw [xi_zero]
    norm_num
  · unfold centeredQuartetGauge
    fun_prop
  · exact xi_differentiable 0

/-- **Exact source marking breaks the quartet gauge.**  Although the concrete gauged xi has the
same FE, Schwarz symmetry, entire regularity, and real-anchor nonvanishing as xi, their exact
logarithmic sources already differ at `s = 0`. -/
theorem quartetGaugedXi_concrete_logDeriv_ne :
    logDeriv (quartetGaugedXi (1 / 4) 1) 0 ≠ logDeriv xi 0 := by
  rw [quartetGaugedXi_concrete_logDeriv_zero]
  intro h
  have hc : (-608 / 425 : ℂ) = 0 := by
    calc
      (-608 / 425 : ℂ) =
          ((-608 / 425 : ℂ) + logDeriv xi 0) - logDeriv xi 0 := by ring
      _ = logDeriv xi 0 - logDeriv xi 0 := by rw [h]
      _ = 0 := sub_self _
  norm_num at hc

end RHTower
