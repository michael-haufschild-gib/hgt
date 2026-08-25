import GaloisForLFunctions.RHTower.PolynomialFockPotentialGeometry

/-!
# Local upper Bregman geometry for polynomial Fock weights

The global tangent lower bound also controls the local upper remainder.  A scalar `rpow`
Lipschitz estimate derived from tangent inequalities gives an explicit quadratic majorant on every
unit ball centered on the nonnegative real axis.
-/

open Set
open scoped Real

namespace RHTower

noncomputable section

/-- `rpow` is Lipschitz on a positive compact interval, with the endpoint derivative bound. -/
theorem abs_rpow_sub_rpow_le_of_le
    {u v M β : ℝ} (hu : 0 < u) (hv : 0 < v) (huM : u ≤ M) (hvM : v ≤ M)
    (hβ : 1 ≤ β) :
    |u ^ β - v ^ β| ≤ β * M ^ (β - 1) * |u - v| := by
  have hM : 0 < M := hu.trans_le huM
  have hβ0 : 0 ≤ β := by linarith
  have hβm : 0 ≤ β - 1 := by linarith
  have hcoef : 0 ≤ β * M ^ (β - 1) := by positivity
  rcases le_total u v with huv | hvu
  · have ht := rpow_tangent_lower hv hu.le hβ
    have hpow : v ^ (β - 1) ≤ M ^ (β - 1) :=
      Real.rpow_le_rpow hv.le hvM hβm
    have hgap : 0 ≤ v - u := sub_nonneg.mpr huv
    have hstep : β * v ^ (β - 1) * (v - u) ≤
        β * M ^ (β - 1) * (v - u) := by gcongr
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.rpow_le_rpow hu.le huv hβ0)),
      abs_of_nonpos (sub_nonpos.mpr huv)]
    nlinarith [ht, hstep]
  · have ht := rpow_tangent_lower hu hv.le hβ
    have hpow : u ^ (β - 1) ≤ M ^ (β - 1) :=
      Real.rpow_le_rpow hu.le huM hβm
    have hgap : 0 ≤ u - v := sub_nonneg.mpr hvu
    have hstep : β * u ^ (β - 1) * (u - v) ≤
        β * M ^ (β - 1) * (u - v) := by gcongr
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hv.le hvu hβ0)),
      abs_of_nonneg (sub_nonneg.mpr hvu)]
    nlinarith [ht, hstep]

/-- Quadratic upper Bregman remainder for `rpow` on a bounded positive interval. -/
theorem rpow_bregman_upper_of_le
    {A B M α : ℝ} (hA : 0 < A) (hB : 0 < B) (hAM : A ≤ M) (hBM : B ≤ M)
    (hα : 2 ≤ α) :
    B ^ α - A ^ α - α * A ^ (α - 1) * (B - A) ≤
      α * (α - 1) * M ^ (α - 2) * (B - A) ^ 2 := by
  have hα1 : 1 ≤ α := hα.trans' (by norm_num)
  have hβ : 1 ≤ α - 1 := by linarith
  have hα0 : 0 ≤ α := by linarith
  have hmono :
      0 ≤ (B ^ (α - 1) - A ^ (α - 1)) * (B - A) := by
    rcases le_total A B with hAB | hBA
    · exact mul_nonneg
        (sub_nonneg.mpr (Real.rpow_le_rpow hA.le hAB (by linarith)))
        (sub_nonneg.mpr hAB)
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (Real.rpow_le_rpow hB.le hBA (by linarith)))
        (sub_nonpos.mpr hBA)
  have ht := rpow_tangent_lower hB hA.le hα1
  have hlip := abs_rpow_sub_rpow_le_of_le hA hB hAM hBM hβ
  have habsprod :
      (B ^ (α - 1) - A ^ (α - 1)) * (B - A) =
        |B ^ (α - 1) - A ^ (α - 1)| * |B - A| := by
    rw [← abs_mul, abs_of_nonneg hmono]
  have hprod :
      (B ^ (α - 1) - A ^ (α - 1)) * (B - A) ≤
        (α - 1) * M ^ (α - 2) * (B - A) ^ 2 := by
    rw [habsprod]
    calc
      |B ^ (α - 1) - A ^ (α - 1)| * |B - A| ≤
          ((α - 1) * M ^ ((α - 1) - 1) * |B - A|) * |B - A| := by
        gcongr
        simpa [abs_sub_comm] using hlip
      _ = (α - 1) * M ^ (α - 2) * (B - A) ^ 2 := by
        rw [show α - 1 - 1 = α - 2 by ring]
        have habssq : |B - A| * |B - A| = (B - A) ^ 2 := by
          rw [← pow_two, sq_abs]
        calc
          (α - 1) * M ^ (α - 2) * |B - A| * |B - A| =
              ((α - 1) * M ^ (α - 2)) * (|B - A| * |B - A|) := by ring
          _ = _ := by rw [habssq]
  have hstep :
      α * ((B ^ (α - 1) - A ^ (α - 1)) * (B - A)) ≤
        α * ((α - 1) * M ^ (α - 2) * (B - A) ^ 2) :=
    mul_le_mul_of_nonneg_left hprod hα0
  nlinarith [ht, hstep]

/-- Degree-dependent local curvature constant for the polynomial Fock potential. -/
def polynomialFockLocalBregmanConstant (m : ℝ) : ℝ :=
  m / 2 + 6 * (m / 2) * (m / 2 - 1) * 3 ^ (m / 2 - 2)

theorem polynomialFockLocalBregmanConstant_pos
    {m : ℝ} (hm : 4 ≤ m) : 0 < polynomialFockLocalBregmanConstant m := by
  unfold polynomialFockLocalBregmanConstant
  have hhalf : 0 < m / 2 := by linarith
  have hminus : 0 ≤ m / 2 - 1 := by linarith
  have hterm : 0 ≤ 6 * (m / 2) * (m / 2 - 1) * 3 ^ (m / 2 - 2) := by
    positivity
  linarith

/-- Explicit local tangent-paraboloid upper bound on each real-axis unit ball. -/
theorem polynomialFockPotential_bregman_upper_unit
    {m x : ℝ} (hm : 4 ≤ m) (hx : 0 ≤ x) (w : ℂ) (hw : ‖w‖ ≤ 1) :
    polynomialFockPotential m ‖(x : ℂ) + w‖ ≤
      polynomialFockPotential m x + polynomialFockRadialSlope m x * w.re +
        polynomialFockLocalBregmanConstant m *
          (1 + x ^ 2) ^ (m / 2 - 1) * ‖w‖ ^ 2 := by
  let α : ℝ := m / 2
  let A : ℝ := 1 + x ^ 2
  let B : ℝ := 1 + ‖(x : ℂ) + w‖ ^ 2
  let M : ℝ := 3 * A
  have hα : 2 ≤ α := by dsimp [α]; linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hnorm : ‖(x : ℂ) + w‖ ≤ x + ‖w‖ := by
    calc
      ‖(x : ℂ) + w‖ ≤ ‖(x : ℂ)‖ + ‖w‖ := norm_add_le _ _
      _ = x + ‖w‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hx]
  have hw2 : ‖w‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - ‖w‖)]
  have hnormSq : ‖(x : ℂ) + w‖ ^ 2 ≤ (x + ‖w‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
  have hBM : B ≤ M := by
    dsimp [B, M, A]
    nlinarith [sq_nonneg (x - 1), mul_nonneg hx hw0]
  have hAM : A ≤ M := by dsimp [M]; nlinarith [hA.le]
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
  have hbreg := rpow_bregman_upper_of_le hA hB hAM hBM hα
  have hMpow : M ^ (α - 2) = 3 ^ (α - 2) * A ^ (α - 2) := by
    dsimp [M]
    rw [Real.mul_rpow (by norm_num) hA.le]
  have hApow : A ^ (α - 2) * A = A ^ (α - 1) := by
    calc
      A ^ (α - 2) * A = A ^ (α - 2) * A ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = A ^ ((α - 2) + 1) := (Real.rpow_add hA (α - 2) 1).symm
      _ = A ^ (α - 1) := by ring_nf
  have hrem :
      α * (α - 1) * M ^ (α - 2) * (B - A) ^ 2 ≤
        6 * α * (α - 1) * 3 ^ (α - 2) * A ^ (α - 1) * ‖w‖ ^ 2 := by
    rw [hMpow]
    have hfac : 0 ≤ α * (α - 1) * (3 ^ (α - 2) * A ^ (α - 2)) := by
      have : 0 ≤ α - 1 := by linarith
      positivity
    calc
      α * (α - 1) * (3 ^ (α - 2) * A ^ (α - 2)) * (B - A) ^ 2 ≤
          α * (α - 1) * (3 ^ (α - 2) * A ^ (α - 2)) *
            (6 * A * ‖w‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hgapSq hfac
      _ = 6 * α * (α - 1) * 3 ^ (α - 2) *
          A ^ (α - 1) * ‖w‖ ^ 2 := by rw [← hApow]; ring
  unfold polynomialFockPotential polynomialFockRadialSlope
    polynomialFockLocalBregmanConstant
  change B ^ α ≤ A ^ α + m * x * A ^ (α - 1) * w.re +
    (m / 2 + 6 * (m / 2) * (m / 2 - 1) * 3 ^ (m / 2 - 2)) *
      A ^ (m / 2 - 1) * ‖w‖ ^ 2
  have hmain := hbreg.trans hrem
  calc
    B ^ α ≤ A ^ α + α * A ^ (α - 1) * (B - A) +
        6 * α * (α - 1) * 3 ^ (α - 2) * A ^ (α - 1) * ‖w‖ ^ 2 := by
      linarith
    _ = A ^ α + m * x * A ^ (α - 1) * w.re +
        (m / 2 + 6 * (m / 2) * (m / 2 - 1) * 3 ^ (m / 2 - 2)) *
          A ^ (m / 2 - 1) * ‖w‖ ^ 2 := by
      rw [hBA]
      dsimp [α]
      ring

end

end RHTower
