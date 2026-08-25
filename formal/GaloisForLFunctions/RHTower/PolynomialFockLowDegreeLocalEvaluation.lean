import GaloisForLFunctions.RHTower.PolynomialFockLocalEvaluation
import GaloisForLFunctions.HTGeometry.RpowConcavity

/-!
# Low-degree local evaluation for polynomial moment-Fock carriers

For `2 ≤ m ≤ 4`, concavity of the derivative of `t ↦ t^(m/2)` gives a uniform quadratic
Bregman bound at the exact tangent scale. This supplies weighted submean control and a sharp
real-axis diagonal-kernel upper bound throughout the subquartic range.
-/

open Set MeasureTheory Filter Topology
open scoped Real

namespace RHTower

noncomputable section

theorem rpow_anti_of_nonpos
    {L u e : ℝ} (hL : 0 < L) (hLu : L ≤ u) (he : e ≤ 0) :
    u ^ e ≤ L ^ e := by
  have hu : 0 ≤ u := hL.le.trans hLu
  have hpow : L ^ (-e) ≤ u ^ (-e) :=
    Real.rpow_le_rpow hL.le hLu (neg_nonneg.mpr he)
  have hLpow : 0 < L ^ (-e) := Real.rpow_pos_of_pos hL _
  rw [show e = -(-e) by ring, Real.rpow_neg hu, Real.rpow_neg hL.le]
  exact inv_anti₀ hLpow hpow

theorem abs_rpow_sub_rpow_le_of_lower
    {L u v β : ℝ} (hL : 0 < L) (hLu : L ≤ u) (hLv : L ≤ v)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    |u ^ β - v ^ β| ≤ L ^ (β - 1) * |u - v| := by
  have hu : 0 < u := hL.trans_le hLu
  have hv : 0 < v := hL.trans_le hLv
  have he : β - 1 ≤ 0 := by linarith
  rcases le_total u v with huv | hvu
  · have hmono : u ^ β ≤ v ^ β := Real.rpow_le_rpow hu.le huv hβ0
    have hbase := GaloisForLFunctions.HTGeometry.rpow_sub_rpow_le
      (A := v) (c := v - u) (β := β) hβ1 (sub_nonneg.mpr huv) (by simpa)
    have hpow : u ^ (β - 1) ≤ L ^ (β - 1) :=
      rpow_anti_of_nonpos hL hLu he
    have hgap : 0 ≤ v - u := sub_nonneg.mpr huv
    have hbase' : v ^ β - u ^ β ≤ (v - u) * u ^ (β - 1) := by
      convert hbase using 1 <;> ring
    rw [abs_of_nonpos (sub_nonpos.mpr hmono), abs_of_nonpos (sub_nonpos.mpr huv)]
    have hmul := mul_le_mul_of_nonneg_left hpow hgap
    simpa [mul_comm] using hbase'.trans hmul
  · have hmono : v ^ β ≤ u ^ β := Real.rpow_le_rpow hv.le hvu hβ0
    have hbase := GaloisForLFunctions.HTGeometry.rpow_sub_rpow_le
      (A := u) (c := u - v) (β := β) hβ1 (sub_nonneg.mpr hvu) (by simpa)
    have hpow : v ^ (β - 1) ≤ L ^ (β - 1) :=
      rpow_anti_of_nonpos hL hLv he
    have hgap : 0 ≤ u - v := sub_nonneg.mpr hvu
    have hbase' : u ^ β - v ^ β ≤ (u - v) * v ^ (β - 1) := by
      convert hbase using 1 <;> ring
    rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonneg (sub_nonneg.mpr hvu)]
    have hmul := mul_le_mul_of_nonneg_left hpow hgap
    simpa [mul_comm] using hbase'.trans hmul

theorem rpow_bregman_upper_lowDegree
    {L A B α : ℝ} (hL : 0 < L) (hLA : L ≤ A) (hLB : L ≤ B)
    (hα1 : 1 ≤ α) (hα2 : α ≤ 2) :
    B ^ α - A ^ α - α * A ^ (α - 1) * (B - A) ≤
      α * L ^ (α - 2) * (B - A) ^ 2 := by
  have hA : 0 < A := hL.trans_le hLA
  have hB : 0 < B := hL.trans_le hLB
  have hα0 : 0 ≤ α := zero_le_one.trans hα1
  have hβ0 : 0 ≤ α - 1 := sub_nonneg.mpr hα1
  have hβ1 : α - 1 ≤ 1 := by linarith
  have hmono :
      0 ≤ (B ^ (α - 1) - A ^ (α - 1)) * (B - A) := by
    rcases le_total A B with hAB | hBA
    · exact mul_nonneg
        (sub_nonneg.mpr (Real.rpow_le_rpow hA.le hAB hβ0))
        (sub_nonneg.mpr hAB)
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (Real.rpow_le_rpow hB.le hBA hβ0))
        (sub_nonpos.mpr hBA)
  have ht := rpow_tangent_lower hB hA.le hα1
  have hlip := abs_rpow_sub_rpow_le_of_lower
    hL hLA hLB hβ0 hβ1
  have habsprod :
      (B ^ (α - 1) - A ^ (α - 1)) * (B - A) =
        |B ^ (α - 1) - A ^ (α - 1)| * |B - A| := by
    rw [← abs_mul, abs_of_nonneg hmono]
  have hprod :
      (B ^ (α - 1) - A ^ (α - 1)) * (B - A) ≤
        L ^ (α - 2) * (B - A) ^ 2 := by
    rw [habsprod]
    calc
      |B ^ (α - 1) - A ^ (α - 1)| * |B - A| ≤
          (L ^ ((α - 1) - 1) * |B - A|) * |B - A| := by
        gcongr
        simpa [abs_sub_comm] using hlip
      _ = L ^ (α - 2) * (B - A) ^ 2 := by
        rw [show α - 1 - 1 = α - 2 by ring]
        calc
          L ^ (α - 2) * |B - A| * |B - A| =
              L ^ (α - 2) * |B - A| ^ 2 := by ring
          _ = L ^ (α - 2) * (B - A) ^ 2 := by rw [sq_abs]
  have hstep := mul_le_mul_of_nonneg_left hprod hα0
  nlinarith [ht, hstep]

/-- Low-degree local curvature constant. -/
def polynomialFockLowDegreeBregmanConstant (m : ℝ) : ℝ :=
  m / 2 + 6 * (m / 2) * 3 ^ (2 - m / 2)

theorem polynomialFockLowDegreeBregmanConstant_pos
    {m : ℝ} (hm : 2 ≤ m) :
    0 < polynomialFockLowDegreeBregmanConstant m := by
  unfold polynomialFockLowDegreeBregmanConstant
  positivity

theorem polynomialFockPotential_bregman_upper_unit_lowDegree
    {m x : ℝ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) (hx : 0 ≤ x)
    (w : ℂ) (hw : ‖w‖ ≤ 1) :
    polynomialFockPotential m ‖(x : ℂ) + w‖ ≤
      polynomialFockPotential m x + polynomialFockRadialSlope m x * w.re +
        polynomialFockLowDegreeBregmanConstant m *
          (1 + x ^ 2) ^ (m / 2 - 1) * ‖w‖ ^ 2 := by
  let α : ℝ := m / 2
  let A : ℝ := 1 + x ^ 2
  let B : ℝ := 1 + ‖(x : ℂ) + w‖ ^ 2
  let L : ℝ := A / 3
  have hα1 : 1 ≤ α := by dsimp [α]; linarith
  have hα2 : α ≤ 2 := by dsimp [α]; linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hL : 0 < L := div_pos hA (by norm_num)
  have hLA : L ≤ A := by dsimp [L]; linarith
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hnorm : x ≤ ‖(x : ℂ) + w‖ + ‖w‖ := by
    calc
      x = ‖(x : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hx]
      _ = ‖((x : ℂ) + w) - w‖ := by ring_nf
      _ ≤ ‖(x : ℂ) + w‖ + ‖w‖ := norm_sub_le _ _
  have hnorm1 : x ≤ ‖(x : ℂ) + w‖ + 1 :=
    hnorm.trans (add_le_add le_rfl hw)
  have hLB : L ≤ B := by
    dsimp [L, A, B]
    nlinarith [sq_nonneg (‖(x : ℂ) + w‖ - 1)]
  have hBA : B - A = 2 * x * w.re + ‖w‖ ^ 2 := by
    have hnormw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    dsimp [B, A]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    rw [hnormw]
    ring
  have hre : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have hgapAbs : |B - A| ≤ (2 * x + 1) * ‖w‖ := by
    rw [hBA]
    have habsmul : |2 * x * w.re| = 2 * x * |w.re| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
        abs_of_nonneg hx]
    have habssq : |‖w‖ ^ 2| = ‖w‖ ^ 2 := abs_of_nonneg (sq_nonneg _)
    calc
      |2 * x * w.re + ‖w‖ ^ 2| ≤ |2 * x * w.re| + |‖w‖ ^ 2| := abs_add_le _ _
      _ = 2 * x * |w.re| + ‖w‖ ^ 2 := by rw [habsmul, habssq]
      _ ≤ 2 * x * ‖w‖ + ‖w‖ ^ 2 := by gcongr
      _ ≤ (2 * x + 1) * ‖w‖ := by nlinarith
  have hlin0 : 0 ≤ (2 * x + 1) * ‖w‖ := by positivity
  have hgapSq0 : (B - A) ^ 2 ≤ ((2 * x + 1) * ‖w‖) ^ 2 := by
    rw [← sq_abs (B - A)]
    exact (sq_le_sq₀ (abs_nonneg _) hlin0).2 hgapAbs
  have hcoefSq : (2 * x + 1) ^ 2 ≤ 6 * A := by
    dsimp [A]
    nlinarith [sq_nonneg (x - 1)]
  have hgapSq : (B - A) ^ 2 ≤ 6 * A * ‖w‖ ^ 2 := by
    calc
      (B - A) ^ 2 ≤ ((2 * x + 1) * ‖w‖) ^ 2 := hgapSq0
      _ = (2 * x + 1) ^ 2 * ‖w‖ ^ 2 := by ring
      _ ≤ (6 * A) * ‖w‖ ^ 2 := by gcongr
  have hbreg := rpow_bregman_upper_lowDegree hL hLA hLB hα1 hα2
  have hLpow : L ^ (α - 2) = 3 ^ (2 - α) * A ^ (α - 2) := by
    dsimp [L]
    rw [Real.div_rpow hA.le (by norm_num : (0 : ℝ) ≤ 3)]
    rw [show (3 : ℝ) ^ (α - 2) = (3 ^ (2 - α))⁻¹ by
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring]
    field_simp
  have hApow : A ^ (α - 2) * A = A ^ (α - 1) := by
    calc
      A ^ (α - 2) * A = A ^ (α - 2) * A ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = A ^ ((α - 2) + 1) := (Real.rpow_add hA (α - 2) 1).symm
      _ = A ^ (α - 1) := by ring_nf
  have hrem :
      α * L ^ (α - 2) * (B - A) ^ 2 ≤
        6 * α * 3 ^ (2 - α) * A ^ (α - 1) * ‖w‖ ^ 2 := by
    rw [hLpow]
    have hfac : 0 ≤ α * (3 ^ (2 - α) * A ^ (α - 2)) := by positivity
    calc
      α * (3 ^ (2 - α) * A ^ (α - 2)) * (B - A) ^ 2 ≤
          α * (3 ^ (2 - α) * A ^ (α - 2)) * (6 * A * ‖w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hgapSq hfac
      _ = 6 * α * 3 ^ (2 - α) * A ^ (α - 1) * ‖w‖ ^ 2 := by
        rw [← hApow]
        ring
  have hAone : 1 ≤ A ^ (α - 1) :=
    Real.one_le_rpow (by dsimp [A]; nlinarith [sq_nonneg x]) (by linarith)
  unfold polynomialFockPotential polynomialFockRadialSlope
    polynomialFockLowDegreeBregmanConstant
  change B ^ α ≤ A ^ α + m * x * A ^ (α - 1) * w.re +
    (m / 2 + 6 * (m / 2) * 3 ^ (2 - m / 2)) *
      A ^ (m / 2 - 1) * ‖w‖ ^ 2
  have hmain := hbreg.trans hrem
  calc
    B ^ α ≤ A ^ α + α * A ^ (α - 1) * (B - A) +
        6 * α * 3 ^ (2 - α) * A ^ (α - 1) * ‖w‖ ^ 2 := by
      linarith
    _ = A ^ α + m * x * A ^ (α - 1) * w.re +
        (m / 2 + 6 * (m / 2) * 3 ^ (2 - m / 2)) *
          A ^ (m / 2 - 1) * ‖w‖ ^ 2 := by
      rw [hBA]
      dsimp [α]
      ring

theorem polynomialFockTangentRadius_le_one
    {m x : ℝ} (hm : 2 ≤ m) :
    polynomialFockTangentRadius m x ≤ 1 := by
  have hA : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hexp : 0 ≤ m / 2 - 1 := by linarith
  have hpow : 1 ≤ (1 + x ^ 2) ^ (m / 2 - 1) := Real.one_le_rpow hA hexp
  have hc : 1 ≤ m * (1 + x ^ 2) ^ (m / 2 - 1) := by nlinarith
  have hsqrt : 1 ≤ Real.sqrt (m * (1 + x ^ 2) ^ (m / 2 - 1)) := by
    have := Real.sqrt_le_sqrt hc
    simpa using this
  unfold polynomialFockTangentRadius
  simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hsqrt

theorem polynomialFockPotential_bregman_upper_tangentRadius_lowDegree
    {m x : ℝ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) (hx : 0 ≤ x) {w : ℂ}
    (hw : ‖w‖ ≤ polynomialFockTangentRadius m x) :
    polynomialFockPotential m ‖(x : ℂ) + w‖ - polynomialFockPotential m x -
        polynomialFockRadialSlope m x * w.re ≤
      polynomialFockLowDegreeBregmanConstant m / m := by
  have hm0 : 0 < m := by linarith
  have hunit : ‖w‖ ≤ 1 := hw.trans (polynomialFockTangentRadius_le_one hm2)
  have hlocal := polynomialFockPotential_bregman_upper_unit_lowDegree
    hm2 hm4 hx w hunit
  have hsquare : ‖w‖ ^ 2 ≤ polynomialFockTangentRadius m x ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (polynomialFockTangentRadius_pos hm0).le).2 hw
  rw [polynomialFockTangentRadius_sq hm0] at hsquare
  let A : ℝ := 1 + x ^ 2
  let α : ℝ := m / 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hAp : 0 < A ^ (α - 1) := Real.rpow_pos_of_pos hA _
  have hscaled : A ^ (α - 1) * ‖w‖ ^ 2 ≤ 1 / m := by
    calc
      A ^ (α - 1) * ‖w‖ ^ 2 ≤
          A ^ (α - 1) * (m * A ^ (α - 1))⁻¹ :=
        mul_le_mul_of_nonneg_left (by simpa [A, α] using hsquare) hAp.le
      _ = 1 / m := by field_simp
  have hC := (polynomialFockLowDegreeBregmanConstant_pos hm2).le
  have hbreg :
      polynomialFockPotential m ‖(x : ℂ) + w‖ - polynomialFockPotential m x -
          polynomialFockRadialSlope m x * w.re ≤
        polynomialFockLowDegreeBregmanConstant m *
          ((1 + x ^ 2) ^ (m / 2 - 1) * ‖w‖ ^ 2) := by
    linarith
  calc
    polynomialFockPotential m ‖(x : ℂ) + w‖ - polynomialFockPotential m x -
          polynomialFockRadialSlope m x * w.re ≤
        polynomialFockLowDegreeBregmanConstant m *
          (A ^ (α - 1) * ‖w‖ ^ 2) := by simpa [A, α] using hbreg
    _ ≤ polynomialFockLowDegreeBregmanConstant m * (1 / m) :=
      mul_le_mul_of_nonneg_left hscaled hC
    _ = polynomialFockLowDegreeBregmanConstant m / m := by ring

theorem polynomialFockPotential_bregman_upper_tangentRadius_lowDegree'
    {m x : ℝ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) (hx : 0 ≤ x) {z : ℂ}
    (hz : z ∈ Metric.ball (x : ℂ) (polynomialFockTangentRadius m x)) :
    polynomialFockPotential m ‖z‖ ≤
      polynomialFockPotential m x + polynomialFockRadialSlope m x * (z.re - x) +
        polynomialFockLowDegreeBregmanConstant m / m := by
  let w : ℂ := z - x
  have hw : ‖w‖ ≤ polynomialFockTangentRadius m x :=
    le_of_lt (by simpa [w, Metric.mem_ball, dist_eq_norm] using hz)
  have h := polynomialFockPotential_bregman_upper_tangentRadius_lowDegree
    hm2 hm4 hx hw
  have hzadd : (x : ℂ) + w = z := by dsimp [w]; abel
  have hwre : w.re = z.re - x := by simp [w]
  rw [hzadd, hwre] at h
  linarith

theorem normSq_polynomialFockTangentGauge_le_weighted_tangentRadius_lowDegree
    {m x : ℝ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) (hx : 0 ≤ x)
    (F : ℂ → ℂ) (z : ℂ)
    (hz : z ∈ Metric.ball (x : ℂ) (polynomialFockTangentRadius m x)) :
    ‖polynomialFockTangentGauge m x F z‖ ^ 2 ≤
      Real.exp (2 * polynomialFockPotential m x +
          2 * (polynomialFockLowDegreeBregmanConstant m / m)) *
        (‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockPotential m ‖z‖)) := by
  have hphi := polynomialFockPotential_bregman_upper_tangentRadius_lowDegree'
    hm2 hm4 hx hz
  have hexp :
      -2 * polynomialFockRadialSlope m x * (z.re - x) ≤
        2 * polynomialFockPotential m x +
          2 * (polynomialFockLowDegreeBregmanConstant m / m) -
            2 * polynomialFockPotential m ‖z‖ := by
    linarith
  rw [normSq_polynomialFockTangentGauge]
  calc
    ‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockRadialSlope m x * (z.re - x)) ≤
        ‖F z‖ ^ 2 * Real.exp
          (2 * polynomialFockPotential m x +
            2 * (polynomialFockLowDegreeBregmanConstant m / m) -
              2 * polynomialFockPotential m ‖z‖) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (sq_nonneg _)
    _ = Real.exp (2 * polynomialFockPotential m x +
          2 * (polynomialFockLowDegreeBregmanConstant m / m)) *
        (‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockPotential m ‖z‖)) := by
      rw [show 2 * polynomialFockPotential m x +
          2 * (polynomialFockLowDegreeBregmanConstant m / m) -
            2 * polynomialFockPotential m ‖z‖ =
        (2 * polynomialFockPotential m x +
          2 * (polynomialFockLowDegreeBregmanConstant m / m)) +
            (-2 * polynomialFockPotential m ‖z‖) by ring, Real.exp_add]
      ring

theorem polynomialFock_tangentRadius_weighted_mean_lowDegree
    {m x : ℝ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) (hx : 0 ≤ x)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    Real.pi * polynomialFockTangentRadius m x ^ 2 * ‖F (x : ℂ)‖ ^ 2 ≤
      Real.exp (2 * polynomialFockPotential m x +
        2 * (polynomialFockLowDegreeBregmanConstant m / m)) *
        ∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x),
          ‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockPotential m ‖z‖) := by
  let G : ℂ → ℂ := polynomialFockTangentGauge m x F
  have hG := differentiable_polynomialFockTangentGauge m x F hF
  have hmean := GaloisForLFunctions.HTGeometry.normSq_value_mul_area_le_integral_ball
    (R := polynomialFockTangentRadius m x) G hG (x : ℂ)
      (polynomialFockTangentRadius_pos (by linarith))
  have hGx : G (x : ℂ) = F (x : ℂ) := by simp [G, polynomialFockTangentGauge]
  rw [hGx] at hmean
  let W : ℂ → ℝ := fun z =>
    Real.exp (2 * polynomialFockPotential m x +
      2 * (polynomialFockLowDegreeBregmanConstant m / m)) *
      (‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockPotential m ‖z‖))
  have hGint : IntegrableOn (fun z => ‖G z‖ ^ 2)
      (Metric.ball (x : ℂ) (polynomialFockTangentRadius m x)) := by
    apply ((hG.continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (x : ℂ) (polynomialFockTangentRadius m x))).mono_set
    exact Metric.ball_subset_closedBall
  have hWcont : Continuous W := by
    unfold W
    exact continuous_const.mul ((hF.continuous.norm.pow 2).mul
      (Real.continuous_exp.comp
        (continuous_const.mul
          ((continuous_polynomialFockPotential m).comp continuous_norm))))
  have hWint : IntegrableOn W
      (Metric.ball (x : ℂ) (polynomialFockTangentRadius m x)) := by
    apply (hWcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (x : ℂ) (polynomialFockTangentRadius m x))).mono_set
    exact Metric.ball_subset_closedBall
  have hint :
      (∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x), ‖G z‖ ^ 2) ≤
        ∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x), W z := by
    change Integrable (fun z => ‖G z‖ ^ 2)
      (volume.restrict (Metric.ball (x : ℂ) (polynomialFockTangentRadius m x))) at hGint
    change Integrable W
      (volume.restrict (Metric.ball (x : ℂ) (polynomialFockTangentRadius m x))) at hWint
    apply MeasureTheory.integral_mono_ae hGint hWint
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact normSq_polynomialFockTangentGauge_le_weighted_tangentRadius_lowDegree
      hm2 hm4 hx F z hz
  calc
    Real.pi * polynomialFockTangentRadius m x ^ 2 * ‖F (x : ℂ)‖ ^ 2 ≤
        ∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x), ‖G z‖ ^ 2 := hmean
    _ ≤ ∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x), W z := hint
    _ = Real.exp (2 * polynomialFockPotential m x +
        2 * (polynomialFockLowDegreeBregmanConstant m / m)) *
        ∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x),
          ‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockPotential m ‖z‖) := by
      rw [MeasureTheory.integral_const_mul]

theorem normSq_polynomialMomentFockKernel_mul_tangentArea_le_lowDegree
    {m x : ℝ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) (hx : 0 ≤ x) :
    Real.pi * polynomialFockTangentRadius m x ^ 2 *
        ‖momentFockKernel (polynomialMomentFockData m hm2) (x : ℂ)‖ ^ 2 ≤
      Real.exp (2 * polynomialFockPotential m x +
        2 * (polynomialFockLowDegreeBregmanConstant m / m)) := by
  let d : MomentFockData := polynomialMomentFockData m hm2
  let k : MomentFock := momentFockKernel d (x : ℂ)
  let K : ℝ := ‖k‖ ^ 2
  have hK : 0 < K := by
    dsimp [K, k]
    exact sq_pos_of_pos (norm_pos_iff.mpr (momentFockKernel_ne_zero d (x : ℂ)))
  have hmean := polynomialFock_tangentRadius_weighted_mean_lowDegree
    hm2 hm4 hx (polynomialMomentFockFunction m hm2 k)
    (differentiable_polynomialMomentFockFunction m hm2 k)
  have hdensity : (fun z =>
      ‖polynomialMomentFockFunction m hm2 k z‖ ^ 2 *
        Real.exp (-2 * polynomialFockPotential m ‖z‖)) =
      polynomialMomentFockWeightedNormSq m hm2 k := by rfl
  rw [hdensity] at hmean
  have hlocal :
      (∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x),
        polynomialMomentFockWeightedNormSq m hm2 k z) ≤ K := by
    dsimp [K]
    rw [← integral_polynomialMomentFockWeightedNormSq m hm2 k]
    exact MeasureTheory.setIntegral_le_integral
      (integrable_polynomialMomentFockWeightedNormSq m hm2 k)
      (Filter.Eventually.of_forall
        (polynomialMomentFockWeightedNormSq_nonneg m hm2 k))
  have heval :
      ‖polynomialMomentFockFunction m hm2 k (x : ℂ)‖ ^ 2 = K ^ 2 := by
    rw [polynomialMomentFockFunction_eq_evaluation]
    change ‖momentFockEvaluation d (x : ℂ) k‖ ^ 2 = K ^ 2
    rw [momentFockEvaluation_apply]
    dsimp [k, K]
    rw [inner_self_eq_norm_sq_to_K, norm_pow]
    norm_num
  have hmain :
      Real.pi * polynomialFockTangentRadius m x ^ 2 * K ^ 2 ≤
        Real.exp (2 * polynomialFockPotential m x +
          2 * (polynomialFockLowDegreeBregmanConstant m / m)) * K := by
    rw [heval] at hmean
    exact hmean.trans (mul_le_mul_of_nonneg_left hlocal (Real.exp_nonneg _))
  have hcancel :
      (Real.pi * polynomialFockTangentRadius m x ^ 2 * K) * K ≤
        Real.exp (2 * polynomialFockPotential m x +
          2 * (polynomialFockLowDegreeBregmanConstant m / m)) * K := by
    simpa [pow_two, mul_assoc] using hmain
  have h := le_of_mul_le_mul_right hcancel hK
  simpa [K, k, d] using h

/-- Sharp real-axis diagonal-kernel upper bound throughout the low-degree range. -/
theorem normSq_polynomialMomentFockKernel_le_lowDegree
    {m x : ℝ} (hm2 : 2 ≤ m) (hm4 : m ≤ 4) (hx : 0 ≤ x) :
    ‖momentFockKernel (polynomialMomentFockData m hm2) (x : ℂ)‖ ^ 2 ≤
      Real.exp (2 * polynomialFockPotential m x +
          2 * (polynomialFockLowDegreeBregmanConstant m / m)) *
        (m * (1 + x ^ 2) ^ (m / 2 - 1) / Real.pi) := by
  let c : ℝ := m * (1 + x ^ 2) ^ (m / 2 - 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have h := normSq_polynomialMomentFockKernel_mul_tangentArea_le_lowDegree hm2 hm4 hx
  rw [polynomialFockTangentRadius_sq (by linarith)] at h
  have h' : Real.pi * c⁻¹ *
      ‖momentFockKernel (polynomialMomentFockData m hm2) (x : ℂ)‖ ^ 2 ≤
      Real.exp (2 * polynomialFockPotential m x +
        2 * (polynomialFockLowDegreeBregmanConstant m / m)) := by
    simpa [c, mul_assoc] using h
  calc
    ‖momentFockKernel (polynomialMomentFockData m hm2) (x : ℂ)‖ ^ 2 =
        (Real.pi * c⁻¹ *
          ‖momentFockKernel (polynomialMomentFockData m hm2) (x : ℂ)‖ ^ 2) *
          (c / Real.pi) := by field_simp
    _ ≤ Real.exp (2 * polynomialFockPotential m x +
          2 * (polynomialFockLowDegreeBregmanConstant m / m)) *
        (c / Real.pi) :=
      mul_le_mul_of_nonneg_right h' (div_nonneg hc.le hpi.le)
    _ = _ := by rfl

end

end RHTower
