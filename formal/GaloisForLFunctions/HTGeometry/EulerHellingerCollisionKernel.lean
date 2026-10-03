import GaloisForLFunctions.HTGeometry.EulerHellingerThetaLift
import GaloisForLFunctions.RHTower.RoutePPrimitiveCollisionTraceBudget
import GaloisForLFunctions.RHTower.EulerLogPrimePowerLaplace

/-!
# The Hellinger Gram is the primitive Euler collision kernel

The Hellinger column `√s_i f_{λ_i}` is `√(Λ(n_i)/n_i) t (e^{-λ_i t} - e^{-2λ_i t})` (**(EHGM.9)**), and
`⟨f_λ, f_μ⟩ = (864/115)(λμ)^{3/2} [2/(λ+μ)³ - 2/(λ+2μ)³ - 2/(2λ+μ)³ + 2/(2λ+2μ)³]`.  Hence every
finite compression of `K = W_H^*W_H` is the full critical collision kernel on the primitive Euler
carrier at `R = 1`, `κ = 0` (**(EHGM.10)**).

Its trace is the cubic Laplace moment of the von Mangoldt current:
`Tr K = (115/1728) ∫_0^∞ t² (-ζ'/ζ)(1+t) dt = Σ_i s_i` (**(EHGM.1)**), since
`-ζ'/ζ(1+t) = Σ_{p,k} Λ(p^{k+1}) p^{-(k+1)} e^{-t(k+1)log p}` and `∫ t² e^{-λt} = 2/λ³`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower
open GaloisForLFunctions.RHTower (eulerLogPrimePowerTime eulerLogPrimePowerWeight
  eulerLogPrimePowerTime_pos eulerLogPrimePowerWeight_pos
  tsum_eulerLogPrimePower_logPositionLaplace_eq_zetaLogDeriv)

local notation "ℓ²E" => lp (fun _ : EulerLabel => ℂ) 2

theorem integral_sq_mul_exp_neg {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), t ^ 2 * Real.exp (-(a * t)) = 2 / a ^ 3 :=
  (integral_exp_neg_moments ha).2.2

theorem integrableOn_sq_mul_exp_neg {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-(a * t))) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_sq_mul_exp_neg ha]
  positivity

/-- The real collision kernel `2/(λ+μ)³ - 2/(λ+2μ)³ - 2/(2λ+μ)³ + 2/(2λ+2μ)³`. -/
def collisionKernelReal (lam mu : ℝ) : ℝ :=
  2 / (lam + mu) ^ 3 - 2 / (lam + 2 * mu) ^ 3 - 2 / (2 * lam + mu) ^ 3 + 2 / (2 * lam + 2 * mu) ^ 3

theorem integral_hellingerProfile_mul {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) :
    ∫ t in Ioi (0 : ℝ), hellingerProfile lam t * hellingerProfile mu t =
      864 / 115 * (lam ^ (3 / 2 : ℝ) * mu ^ (3 / 2 : ℝ)) * collisionKernelReal lam mu := by
  have hfun : (fun t => hellingerProfile lam t * hellingerProfile mu t) = fun t =>
      864 / 115 * (lam ^ (3 / 2 : ℝ) * mu ^ (3 / 2 : ℝ)) *
        (t ^ 2 * Real.exp (-((lam + mu) * t)) - t ^ 2 * Real.exp (-((lam + 2 * mu) * t)) -
          t ^ 2 * Real.exp (-((2 * lam + mu) * t)) + t ^ 2 * Real.exp (-((2 * lam + 2 * mu) * t))) := by
    funext t
    unfold hellingerProfile
    have h864 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 864 / 115 by norm_num)
    have e : ∀ x y : ℝ, Real.exp (-(x * t)) * Real.exp (-(y * t)) = Real.exp (-((x + y) * t)) :=
      fun x y => by rw [← Real.exp_add]; ring_nf
    have e1 := e lam mu
    have e2 := e lam (2 * mu)
    have e3 := e (2 * lam) mu
    have e4 := e (2 * lam) (2 * mu)
    rw [show -(2 * lam * t) = -((2 * lam) * t) by ring, show -(2 * mu * t) = -((2 * mu) * t) by ring]
    linear_combination (lam ^ (3 / 2 : ℝ) * mu ^ (3 / 2 : ℝ) * t ^ 2 *
      (Real.exp (-(lam * t)) - Real.exp (-((2 * lam) * t))) *
        (Real.exp (-(mu * t)) - Real.exp (-((2 * mu) * t)))) * h864 +
      864 / 115 * (lam ^ (3 / 2 : ℝ) * mu ^ (3 / 2 : ℝ)) * t ^ 2 * (e1 - e2 - e3 + e4)
  have i1 := integrableOn_sq_mul_exp_neg (by positivity : 0 < lam + mu)
  have i2 := integrableOn_sq_mul_exp_neg (by positivity : 0 < lam + 2 * mu)
  have i3 := integrableOn_sq_mul_exp_neg (by positivity : 0 < 2 * lam + mu)
  have i4 := integrableOn_sq_mul_exp_neg (by positivity : 0 < 2 * lam + 2 * mu)
  have j12 : IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-((lam + mu) * t)) -
      t ^ 2 * Real.exp (-((lam + 2 * mu) * t))) (Ioi 0) := i1.sub i2
  have j123 : IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-((lam + mu) * t)) -
      t ^ 2 * Real.exp (-((lam + 2 * mu) * t)) - t ^ 2 * Real.exp (-((2 * lam + mu) * t))) (Ioi 0) :=
    j12.sub i3
  rw [hfun, integral_const_mul, integral_add j123 i4, integral_sub j12 i3, integral_sub i1 i2, integral_sq_mul_exp_neg (by positivity), integral_sq_mul_exp_neg (by positivity),
    integral_sq_mul_exp_neg (by positivity), integral_sq_mul_exp_neg (by positivity), collisionKernelReal]

/-- `⟨f_λ, f_μ⟩ = (864/115)(λμ)^{3/2} [collision kernel]`. -/
theorem inner_hellingerVector {lam mu : ℝ} (hl : 0 < lam) (hm : 0 < mu) :
    ⟪hellingerVector hl, hellingerVector hm⟫_ℂ =
      ((864 / 115 * (lam ^ (3 / 2 : ℝ) * mu ^ (3 / 2 : ℝ)) * collisionKernelReal lam mu : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def, ← integral_hellingerProfile_mul hl hm, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [hellingerVector_ae hl, hellingerVector_ae hm] with t h1 h2
  rw [h1, h2, RCLike.inner_apply, Complex.conj_ofReal]
  push_cast
  ring

/-- The von Mangoldt amplitude is `√(log p)/√n` on a prime power. -/
theorem vonMangoldt_eulerValuation (i : EulerLabel) :
    Λ (xiGammaEulerValuationNat i) = Real.log (i.1 : ℝ) := by
  rw [xiGammaEulerValuationNat, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
    ArithmeticFunction.vonMangoldt_apply_prime i.1.property]

/-- **(EHGM.9)** `√s_i · √(864/115) λ_i^{3/2} = √(Λ(n_i)/n_i)`. -/
theorem sqrt_weight_mul_hellinger_amplitude (i : EulerLabel) :
    Real.sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight i) *
        (Real.sqrt (864 / 115) * xiGammaEulerPrimitiveLogFrequency i ^ (3 / 2 : ℝ)) =
      Real.sqrt (Λ (xiGammaEulerValuationNat i) / (xiGammaEulerValuationNat i : ℝ)) := by
  have hlam := xiGammaEulerPrimitiveLogFrequency_pos i
  have hn := eulerValuation_pos i
  have hl := primeClock_pos i.1
  rw [vonMangoldt_eulerValuation, sqrt_xiGammaEulerPrimitiveCubicLogMomentWeight,
    Real.sqrt_div' _ hn.le]
  have hsl : 0 < Real.sqrt (xiGammaEulerPrimitiveLogFrequency i) := Real.sqrt_pos.2 hlam
  have h32 : xiGammaEulerPrimitiveLogFrequency i ^ (3 / 2 : ℝ) =
      Real.sqrt (xiGammaEulerPrimitiveLogFrequency i) ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    norm_num
  rw [h32]
  have hc : Real.sqrt (115 / 864) * Real.sqrt (864 / 115) = 1 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  have hsn := Real.sqrt_pos.2 hn
  field_simp
  linear_combination hc

/-- **(EHGM.10)** `K(i,j) = √(Λ(n_i)/n_i) √(Λ(n_j)/n_j) [collision kernel](λ_i, λ_j)`. -/
theorem inner_single_hellingerGram_eq_collision (i j : EulerLabel) :
    ⟪(lp.single 2 i (1 : ℂ) : ℓ²E), hellingerGram (lp.single 2 j 1)⟫_ℂ =
      ((Real.sqrt (Λ (xiGammaEulerValuationNat i) / (xiGammaEulerValuationNat i : ℝ)) *
        Real.sqrt (Λ (xiGammaEulerValuationNat j) / (xiGammaEulerValuationNat j : ℝ)) *
          collisionKernelReal (xiGammaEulerPrimitiveLogFrequency i)
            (xiGammaEulerPrimitiveLogFrequency j) : ℝ) : ℂ) := by
  rw [inner_single_hellingerGram, hellingerFrame, hellingerFrame, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, inner_hellingerVector, ← sqrt_weight_mul_hellinger_amplitude,
    ← sqrt_weight_mul_hellinger_amplitude]
  have h864 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 864 / 115 by norm_num)
  simp only [← Complex.ofReal_mul]
  congr 1
  linear_combination (-(Real.sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight i) *
    Real.sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight j) *
      (xiGammaEulerPrimitiveLogFrequency i ^ (3 / 2 : ℝ) *
        xiGammaEulerPrimitiveLogFrequency j ^ (3 / 2 : ℝ)) *
      collisionKernelReal (xiGammaEulerPrimitiveLogFrequency i) (xiGammaEulerPrimitiveLogFrequency j))) *
    h864

theorem routePCollisionCubicKernel_one_zero (a b : ℝ) :
    routePCollisionCubicKernel 1 a b 0 = (collisionKernelReal a b : ℂ) := by
  unfold routePCollisionCubicKernel routePCollisionPairFrequency collisionKernelReal
  push_cast
  ring

/-- **(EHGM.10) The Hellinger Gram is the primitive Euler collision kernel.**  Every finite
compression of `K` to a packet of Euler labels is the corpus collision kernel matrix at
`R = 1`, `κ = 0`. -/
theorem hellingerGram_compression_eq_collisionKernelMatrix {N : ℕ} (pe : Fin N → EulerLabel)
    (a b : Fin N) :
    ⟪(lp.single 2 (pe a) (1 : ℂ) : ℓ²E), hellingerGram (lp.single 2 (pe b) 1)⟫_ℂ =
      routePPrimitiveCollisionCubicKernelMatrix 1 pe (fun _ => 0) a b := by
  rw [inner_single_hellingerGram_eq_collision, routePPrimitiveCollisionCubicKernelMatrix,
    routePPrimitiveCollisionScalingMatrix, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, routePCollisionCubicKernelMatrix]
  simp only [sub_self, routePCollisionCubicKernel_one_zero, finiteVonMangoldtDepthOneAmplitude,
    Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
  push_cast
  ring

/-! ## The trace as a cubic moment of `-ζ'/ζ` -/

/-- The cubic Laplace-moment integrand `t² · λ w e^{-tλ}` of one Euler prime power, where
`λ = (k+1) log p` and `w = 1/((k+1)p^{k+1})`. -/
def eulerZetaMomentIntegrand (x : EulerLabel) (t : ℝ) : ℝ :=
  t ^ 2 * (eulerLogPrimePowerTime x.1 x.2 * eulerLogPrimePowerWeight x.1 x.2 *
    Real.exp (-t * eulerLogPrimePowerTime x.1 x.2))

theorem eulerZetaMomentIntegrand_nonneg (x : EulerLabel) (t : ℝ) :
    0 ≤ eulerZetaMomentIntegrand x t := by
  unfold eulerZetaMomentIntegrand
  have := eulerLogPrimePowerTime_pos x.1 x.2
  have := eulerLogPrimePowerWeight_pos x.1 x.2
  positivity

/-- `∫_0^∞ t² λ w e^{-tλ} dt = 2w/λ² = (1728/115) s_i`. -/
theorem integral_eulerZetaMomentIntegrand (x : EulerLabel) :
    ∫ t in Ioi (0 : ℝ), eulerZetaMomentIntegrand x t =
      1728 / 115 * xiGammaEulerPrimitiveCubicLogMomentWeight x := by
  have hT := eulerLogPrimePowerTime_pos x.1 x.2
  have hfun : (fun t => eulerZetaMomentIntegrand x t) = fun t =>
      (eulerLogPrimePowerTime x.1 x.2 * eulerLogPrimePowerWeight x.1 x.2) *
        (t ^ 2 * Real.exp (-(eulerLogPrimePowerTime x.1 x.2 * t))) := by
    funext t
    unfold eulerZetaMomentIntegrand
    have h : -t * eulerLogPrimePowerTime x.1 x.2 = -(eulerLogPrimePowerTime x.1 x.2 * t) := by ring
    rw [h]
    ring
  rw [hfun, integral_const_mul, integral_sq_mul_exp_neg hT]
  unfold eulerLogPrimePowerTime eulerLogPrimePowerWeight xiGammaEulerPrimitiveCubicLogMomentWeight
    invNatLogSq
  have hp : 0 < (x.1 : ℝ) := by exact_mod_cast x.1.property.pos
  have hl := primeClock_pos x.1
  push_cast
  rw [inv_pow]
  field_simp
  ring

theorem integrable_eulerZetaMomentIntegrand (x : EulerLabel) :
    Integrable (eulerZetaMomentIntegrand x) (volume.restrict (Ioi 0)) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_eulerZetaMomentIntegrand]
  have hp : 0 < (x.1 : ℝ) := by exact_mod_cast x.1.property.pos
  have hl := primeClock_pos x.1
  unfold xiGammaEulerPrimitiveCubicLogMomentWeight invNatLogSq
  positivity

/-- **(EHGM.1)** `(115/1728) ∫_0^∞ t² (-ζ'/ζ)(1+t) dt` is the primitive collision budget. -/
theorem integral_sq_mul_zetaLogDeriv :
    (115 / 1728 : ℂ) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ 2 *
      (-deriv riemannZeta ((1 + t : ℝ) : ℂ) / riemannZeta ((1 + t : ℝ) : ℂ)) =
      (routePPrimitiveCollisionCubicTraceBudget : ℂ) := by
  have hint : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ 2 *
      (-deriv riemannZeta ((1 + t : ℝ) : ℂ) / riemannZeta ((1 + t : ℝ) : ℂ)) =
      ((∫ t in Ioi (0 : ℝ), ∑' x : EulerLabel, eulerZetaMomentIntegrand x t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [eulerZetaMomentIntegrand]
    rw [tsum_mul_left, Complex.ofReal_mul,
      tsum_eulerLogPrimePower_logPositionLaplace_eq_zetaLogDeriv (show (0 : ℝ) < t from ht)]
    push_cast
    ring
  have hsum : ∑' x : EulerLabel, ∫ t in Ioi (0 : ℝ), eulerZetaMomentIntegrand x t =
      ∫ t in Ioi (0 : ℝ), ∑' x : EulerLabel, eulerZetaMomentIntegrand x t := by
    refine integral_tsum_of_summable_integral_norm integrable_eulerZetaMomentIntegrand ?_
    simp_rw [Real.norm_of_nonneg (eulerZetaMomentIntegrand_nonneg _ _),
      integral_eulerZetaMomentIntegrand]
    exact summable_xiGammaEulerPrimitiveCubicLogMomentWeight.mul_left _
  rw [hint, ← hsum]
  simp_rw [integral_eulerZetaMomentIntegrand]
  rw [tsum_mul_left, routePPrimitiveCollisionCubicTraceBudget]
  push_cast
  ring

/-- **(EHGM.1)** `Tr K = (115/1728) ∫_0^∞ t² (-ζ'/ζ)(1+t) dt = ` the primitive collision budget. -/
theorem hellingerGram_opTrace_eq_zeta_moment :
    hellingerGram.opTrace = (115 / 1728 : ℂ) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ 2 *
        (-deriv riemannZeta ((1 + t : ℝ) : ℂ) / riemannZeta ((1 + t : ℝ) : ℂ)) ∧
      (115 / 1728 : ℂ) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ 2 *
        (-deriv riemannZeta ((1 + t : ℝ) : ℂ) / riemannZeta ((1 + t : ℝ) : ℂ)) =
      (routePPrimitiveCollisionCubicTraceBudget : ℂ) :=
  ⟨hellingerGram_traceClass.2.2.1.trans integral_sq_mul_zetaLogDeriv.symm,
    integral_sq_mul_zetaLogDeriv⟩

end GaloisForLFunctions.HTGeometry
