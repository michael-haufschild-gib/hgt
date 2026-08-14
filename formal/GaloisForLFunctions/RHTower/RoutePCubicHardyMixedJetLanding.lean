import GaloisForLFunctions.RHTower.MobiusCriticalComplexPhaseHardyBoundarySaturation
import GaloisForLFunctions.RHTower.XiWardCubicLogMomentHellingerCauchySeparator

/-!
# Route P: cubic Hardy mixed-jet landing

The cubic horizontal Hellinger separator is the mixed source jet of a half-weighted difference of
the universal Route-P Hardy columns.  The factor `1 / 2` is forced by the doubled-node chain rule.
This identifies the cubic receiver's horizontal kernel with P-G160's critical Hardy source Gram
before any Euler--Gamma trace estimate is imposed.  It does not identify the growing projective
nodes with P-G167's finite-`sigma` full-Euler overlap.
-/

open Complex Filter Set
open scoped Topology

namespace RHTower

noncomputable section

/-- Projective Hardy node whose boundary carrier has real decay `R * a`. -/
def routePProjectiveHardyNode (R a : ℝ) : ℂ :=
  ((R * a - 1 / 2 : ℝ) : ℂ)

@[simp] theorem routePProjectiveHardyNode_re (R a : ℝ) :
    (routePProjectiveHardyNode R a).re = R * a - 1 / 2 := by
  simp [routePProjectiveHardyNode]

/-- Projective nodes are admissible inward Hardy nodes at sufficiently large scale. -/
theorem routePProjectiveHardyNode_re_nonneg
    {R a : ℝ} (h : 1 / 2 ≤ R * a) :
    0 ≤ (routePProjectiveHardyNode R a).re := by
  rw [routePProjectiveHardyNode_re]
  linarith

/-- No fixed projective scale keeps every strict-right zeta displacement in the arithmetic inward
Hardy chart.  The scale must diverge as the displacement approaches the critical line. -/
theorem exists_strictRightDepth_routePProjectiveHardyNode_re_neg (R : ℝ) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧
      (routePProjectiveHardyNode R a).re < 0 := by
  by_cases hR : 0 < R
  · by_cases hRhalf : 1 / 2 ≤ R
    · refine ⟨1 / (4 * R), by positivity, ?_, ?_⟩
      · rw [div_le_iff₀ (by positivity : 0 < 4 * R)]
        nlinarith
      · rw [routePProjectiveHardyNode_re]
        field_simp [hR.ne']
        norm_num
    · refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
      rw [routePProjectiveHardyNode_re]
      have hRlt : R < 1 / 2 := lt_of_not_ge hRhalf
      nlinarith
  · refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
    rw [routePProjectiveHardyNode_re]
    have hRnonpos : R ≤ 0 := le_of_not_gt hR
    nlinarith

/-- Exact projective rescaling of the universal Route-P Hardy kernel. -/
theorem routeP_scaled_projectiveHardyKernel
    {R a b : ℝ} (hR : R ≠ 0) (hab : a + b ≠ 0) :
    (R : ℂ) *
        mobiusCriticalUniversalHardyKernel
          (routePProjectiveHardyNode R a)
          (routePProjectiveHardyNode R b) =
      ((1 / (a + b) : ℝ) : ℂ) := by
  simp only [mobiusCriticalUniversalHardyKernel,
    routePProjectiveHardyNode, map_sub, map_mul, map_div₀, map_one,
    map_ofNat, RCLike.star_def, Complex.conj_ofReal]
  push_cast
  field_simp [hR, hab]
  ring

/-- Half-weighted two-scale Hardy difference kernel.  The half weight compensates for the
doubled-node chain rule. -/
def routePHalfWeightedHellingerCauchyKernel (a b : ℝ) : ℝ :=
  1 / (a + b) -
    (1 / 2) * (1 / (a + 2 * b)) -
    (1 / 2) * (1 / (2 * a + b)) +
    (1 / 4) * (1 / (2 * a + 2 * b))

/-- The half-weighted kernel is the exact polarization of projectively rescaled Route-P Hardy
columns at scales `a` and `2a`. -/
theorem routePHalfWeightedHellingerCauchyKernel_eq_projectiveHardy
    {R a b : ℝ} (hR : R ≠ 0) (hab : a + b ≠ 0) (ha2b : a + 2 * b ≠ 0)
    (h2ab : 2 * a + b ≠ 0) :
    (routePHalfWeightedHellingerCauchyKernel a b : ℂ) =
      (R : ℂ) * mobiusCriticalUniversalHardyKernel
          (routePProjectiveHardyNode R a)
          (routePProjectiveHardyNode R b) -
        (1 / 2 : ℂ) *
          ((R : ℂ) * mobiusCriticalUniversalHardyKernel
            (routePProjectiveHardyNode R a)
            (routePProjectiveHardyNode R (2 * b))) -
        (1 / 2 : ℂ) *
          ((R : ℂ) * mobiusCriticalUniversalHardyKernel
            (routePProjectiveHardyNode R (2 * a))
            (routePProjectiveHardyNode R b)) +
        (1 / 4 : ℂ) *
          ((R : ℂ) * mobiusCriticalUniversalHardyKernel
            (routePProjectiveHardyNode R (2 * a))
            (routePProjectiveHardyNode R (2 * b))) := by
  have h2a2b : 2 * a + 2 * b ≠ 0 := by
    intro h
    apply hab
    linarith
  rw [routeP_scaled_projectiveHardyKernel hR hab,
    routeP_scaled_projectiveHardyKernel hR ha2b,
    routeP_scaled_projectiveHardyKernel hR h2ab,
    routeP_scaled_projectiveHardyKernel hR h2a2b]
  simp only [routePHalfWeightedHellingerCauchyKernel]
  push_cast

/-- First horizontal jet of the half-weighted Hardy difference. -/
def routePHalfWeightedHellingerCauchyFirstJet (a b : ℝ) : ℝ :=
  -1 / (a + b) ^ 2 +
    (1 / 2) * (1 / (a + 2 * b) ^ 2) +
    1 / (2 * a + b) ^ 2 -
    (1 / 2) * (1 / (2 * a + 2 * b) ^ 2)

private theorem hasDerivAt_one_div_affine
    {alpha beta x : ℝ} (h : alpha * x + beta ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / (alpha * y + beta))
      (-alpha / (alpha * x + beta) ^ 2) x := by
  have hbase : HasDerivAt (fun y : ℝ => alpha * y + beta) alpha x :=
    ((hasDerivAt_id x).const_mul alpha).add_const beta
  convert hbase.inv h using 1
  · funext y
    simp only [one_div]
  · simp only [one_div, neg_div, inv_pow]
    ring

private theorem hasDerivAt_one_div_affine_sq
    {alpha beta x : ℝ} (h : alpha * x + beta ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / (alpha * y + beta) ^ 2)
      (-2 * alpha / (alpha * x + beta) ^ 3) x := by
  have hinv := hasDerivAt_one_div_affine (alpha := alpha) (beta := beta) (x := x) h
  have hmul := hinv.mul hinv
  convert hmul using 1
  · funext y
    simp only [one_div, inv_pow]
    ring
  · field_simp [h]
    ring

/-- Differentiating the first Hardy node gives the forced half-weighted first jet. -/
theorem hasDerivAt_routePHalfWeightedHellingerCauchyKernel
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun x : ℝ => routePHalfWeightedHellingerCauchyKernel x b)
      (routePHalfWeightedHellingerCauchyFirstJet a b) a := by
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  have ha2b : a + 2 * b ≠ 0 := (add_pos ha (mul_pos two_pos hb)).ne'
  have h2ab : 2 * a + b ≠ 0 := (add_pos (mul_pos two_pos ha) hb).ne'
  have h2a2b : 2 * a + 2 * b ≠ 0 :=
    (add_pos (mul_pos two_pos ha) (mul_pos two_pos hb)).ne'
  have h1 := hasDerivAt_one_div_affine (alpha := 1) (beta := b) (x := a) (by simpa using hab)
  have h2 := hasDerivAt_one_div_affine
    (alpha := 1) (beta := 2 * b) (x := a) (by simpa using ha2b)
  have h3 := hasDerivAt_one_div_affine
    (alpha := 2) (beta := b) (x := a) (by simpa using h2ab)
  have h4 := hasDerivAt_one_div_affine
    (alpha := 2) (beta := 2 * b) (x := a) (by simpa using h2a2b)
  simpa [routePHalfWeightedHellingerCauchyKernel,
    routePHalfWeightedHellingerCauchyFirstJet] using
    (((h1.sub (h2.const_mul (1 / 2))).sub (h3.const_mul (1 / 2))).add
      (h4.const_mul (1 / 4)))

/-- Differentiating the first jet in the second Hardy node produces the four cubic Laplace terms. -/
theorem hasDerivAt_routePHalfWeightedHellingerCauchyFirstJet
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun y : ℝ => routePHalfWeightedHellingerCauchyFirstJet a y)
      (2 / (a + b) ^ 3 - 2 / (a + 2 * b) ^ 3 -
        2 / (2 * a + b) ^ 3 + 2 / (2 * a + 2 * b) ^ 3) b := by
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  have ha2b : a + 2 * b ≠ 0 := (add_pos ha (mul_pos two_pos hb)).ne'
  have h2ab : 2 * a + b ≠ 0 := (add_pos (mul_pos two_pos ha) hb).ne'
  have h2a2b : 2 * a + 2 * b ≠ 0 :=
    (add_pos (mul_pos two_pos ha) (mul_pos two_pos hb)).ne'
  have h1 := hasDerivAt_one_div_affine_sq
    (alpha := 1) (beta := a) (x := b) (by simpa [add_comm] using hab)
  have h2 := hasDerivAt_one_div_affine_sq
    (alpha := 2) (beta := a) (x := b) (by simpa [add_comm] using ha2b)
  have h3 := hasDerivAt_one_div_affine_sq
    (alpha := 1) (beta := 2 * a) (x := b) (by simpa [add_comm] using h2ab)
  have h4 := hasDerivAt_one_div_affine_sq
    (alpha := 2) (beta := 2 * a) (x := b) (by simpa [add_comm] using h2a2b)
  simpa [routePHalfWeightedHellingerCauchyFirstJet] using
    (((h1.neg.add (h2.const_mul (1 / 2))).add h3).sub
      (h4.const_mul (1 / 2)))

/-- **Cubic Hardy landing.**  The mixed source jet of the projective half-weighted Route-P Hardy
packet is exactly the cubic log-moment horizontal separator. -/
theorem routePHalfWeightedHellingerCauchyKernel_mixedDeriv
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    deriv
        (fun y : ℝ =>
          deriv (fun x : ℝ => routePHalfWeightedHellingerCauchyKernel x y) a)
        b =
      cubicLogMomentHellingerHorizontalKernel a b := by
  have heq :
      (fun y : ℝ =>
        deriv (fun x : ℝ => routePHalfWeightedHellingerCauchyKernel x y) a) =ᶠ[nhds b]
      fun y : ℝ => routePHalfWeightedHellingerCauchyFirstJet a y := by
    filter_upwards [isOpen_Ioi.mem_nhds hb] with y hy
    exact (hasDerivAt_routePHalfWeightedHellingerCauchyKernel ha hy).deriv
  rw [heq.deriv_eq,
    (hasDerivAt_routePHalfWeightedHellingerCauchyFirstJet ha hb).deriv]
  exact (cubicLogMomentHellingerHorizontalKernel_eq_laplace ha hb).symm

end

end RHTower
