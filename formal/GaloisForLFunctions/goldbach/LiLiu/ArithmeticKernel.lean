import GaloisForLFunctions.goldbach.LiLiu.CharacterHalfPlane
import GaloisForLFunctions.goldbach.LiLiu.DensityEuler
import GaloisForLFunctions.goldbach.LiLiu.SingularDensity
import GaloisForLFunctions.goldbach.GammaFactorBoundary
import GaloisForLFunctions.HTGeometry.RealDirichletSeries

/-!
# The arithmetic kernels on the Goldbach strip

The odd-character term is a finite Gram sum of logarithmic derivatives.
The diagonal has nonnegative Dirichlet coefficients, and the continued
off-diagonal model uses the singular series, the Euler correction and
the signed-Beta Gamma quotients.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex Finset ArithmeticFunction
open scoped Classical
noncomputable section

def characterFeature {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  logDeriv χ.LFunction (1 / 2 + s)

/-- Both arguments are strip coordinates. Conjugation is in the second slot. -/
def characterKernel (N : ℕ) [NeZero N] (s z : ℂ) : ℂ :=
  (2 / (N.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ N with χ.Odd,
    characterFeature χ s * star (characterFeature χ z)

def diagonalCoefficient (N n : ℕ) : ℂ := if n.Coprime N then (Λ n : ℂ) ^ 2 else 0

def diagonalSeries (N : ℕ) (w : ℂ) : ℂ := LSeries (diagonalCoefficient N) (1 + w)

/-- Continued Beta model (2.12), in holomorphic coordinates. -/
def betaModel (N : ℕ) (s z : ℂ) : ℂ :=
  singularSeries N * ((Real.pi / N : ℝ) : ℂ) ^ (s + z) * densityEuler N (s + z) *
    riemannZeta (1 - (s + z)) * signedBetaGammaFactor s * signedBetaGammaFactor z

/-- Arithmetic residual in Hermitian coordinates before the Hardy denominators. -/
def residualKernel (N : ℕ) [NeZero N] (s z : ℂ) : ℂ :=
  characterKernel N s z - diagonalSeries N (s + star z) - betaModel N s (star z)

theorem characterFeature_analyticAt {n : ℕ} (h : modulusGRH (n + 1))
    {χ : DirichletCharacter ℂ (n + 1)} (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (characterFeature χ) s := by
  have ha : (1 / 2 : ℝ) < (1 / 2 + s : ℂ).re := by
    norm_num [Complex.add_re]
    exact hs
  exact (h.logDeriv_analyticAt hχ ha).comp (analyticAt_const.add analyticAt_id)

theorem diagonalCoefficient_zero (N : ℕ) : diagonalCoefficient N 0 = 0 := by
  simp [diagonalCoefficient]

/-- Absolute convergence of the exact, coprime diagonal on Re w > 0. -/
theorem diagonalSeries_summable (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (diagonalCoefficient N) s := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ (HTGeometry.summable_vonMangoldt_logMul_rpow hs)
  intro n
  rw [LSeries.term_def₀ (diagonalCoefficient_zero N), norm_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [diagonalCoefficient]
  rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  unfold diagonalCoefficient
  split_ifs
  · rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg, pow_two]
    exact mul_le_mul_of_nonneg_right vonMangoldt_le_log vonMangoldt_nonneg
  · rw [norm_zero]
    exact mul_nonneg (Real.log_natCast_nonneg n) vonMangoldt_nonneg

theorem diagonalSeries_differentiableAt (N : ℕ) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (diagonalSeries N) w := by
  have hb : LSeries.abscissaOfAbsConv (diagonalCoefficient N) ≤ ((1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      diagonalSeries_summable N (by simpa using hy)
  have hr : (1 : ℝ) < (1 + w).re := by simpa using hw
  exact (LSeries_hasDerivAt (hb.trans_lt (by exact_mod_cast hr))).differentiableAt.comp w
    (differentiableAt_const _ |>.add differentiableAt_id)

#print axioms characterFeature_analyticAt
#print axioms diagonalSeries_differentiableAt
end
end GaloisForLFunctions.Goldbach.LiLiu
