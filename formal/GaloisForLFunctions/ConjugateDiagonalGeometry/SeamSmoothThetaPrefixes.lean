import GaloisForLFunctions.ConjugateDiagonalGeometry.ThetaPrefixCuspAndSectoriality
import GaloisForLFunctions.ConjugateDiagonalGeometry.ThetaPrefixIndexTransition
import GaloisForLFunctions.RHTower.FiniteZeroSubquadraticRigidity
import GaloisForLFunctions.RHTower.XiGaussianHeatSourceSmoothing
import GaloisForLFunctions.HTGeometry.LaguerrePolyaClass
import GaloisForLFunctions.HTGeometry.SlitPlaneQuotientDiscZeroFree
import GaloisForLFunctions.HTGeometry.BesselOrderLaplaceAsymptotic

/-!
# Seam-smooth theta prefixes, super-polynomial strip decay, and off-line zero persistence

This module investigates whether eliminating the `x = 0` seam derivative jump of the reflected
finite Jacobi-theta prefix `reflectedFiniteThetaSource (N + 1)` (`x ↦ P_{N+1}(|x|)`) restores
vertical-strip decay and Schur–Cohn / Hermite–Biehler / Laguerre–Pólya critical-line purity at
finite `N`:

1. **Subquadratic Hadamard obstruction & infinitude of off-line zeros of `finiteThetaAmplitude N`**:
   Every finite prefix `finiteThetaAmplitude N` satisfies a global order-`3 / 2` bound
   `‖finiteThetaAmplitude N z‖ ≤ exp (C_N (1 + ‖z‖)^(3 / 2))` on `ℂ` while growing faster than
   every single exponential along `(0, ∞)`. By subquadratic Hadamard rigidity
   (`zeroSet_infinite_of_subquadratic_superlinear_ray`), `{z | finiteThetaAmplitude N z = 0}` is
   infinite, whereas `{z | |z.re - 1 / 2| ≤ R ∧ finiteThetaAmplitude N z = 0}` is finite for every
   `R`; hence `{z | finiteThetaAmplitude N z = 0 ∧ R < |z.re - 1 / 2|}` is infinite for every `N`
   and `R`, and `z ↦ finiteThetaAmplitude N (1 / 2 + I * z)` never lies in `LaguerrePolya`.
2. **`x`-space Gaussian seam-mollification (`gaussMollifiedThetaSource N a`, `a > 0`)**:
   Convolving `reflectedFiniteThetaSource (N + 1)` with `gaussHeatKernel a` produces a strictly
   positive, `C^∞`-even source on `ℝ` with `iteratedDeriv (2 * k + 1) ... 0 = 0` for all `k : ℕ`.
   Its bilateral Laplace transform equals
   `gaussMollifiedThetaAmplitude N a z = exp ((a / 2) * (z - 1 / 2)^2) * finiteThetaAmplitude N z`,
   restoring Gaussian super-polynomial vertical-strip decay of all orders `K : ℕ`, while preserving
   the exact complex zero divisor (hence infinitely many off-line zeros) and leaving all window
   contour power sums, Newton difference polynomials, Zhukovsky loops, and Wiener–Hopf collision
   operators identically gauge-invariant whenever `finiteThetaAmplitude N` avoids `∂R_{T,n}`.
3. **Non-multiplicative `C^∞`-even Gaussian-partitioned Poisson–Jacobi prefixes
   (`partitionSymThetaSource N κ`, `κ > 0`)**:
   Weighting the analytic shell prefix `thetaCuspFiniteShellPrefix (N + 1)` across `±x` by the
   `C^∞` error-function partition of unity
   `gaussianPartitionSwitch κ x + gaussianPartitionSwitch κ (-x) = 1` produces a `C^∞`-even source
   annihilating all odd seam jets `iteratedDeriv (2 * k + 1) ... 0 = 0`, whose bilateral Laplace
   transform `partitionSymThetaAmplitude N κ` enjoys all-order super-polynomial vertical-strip decay
   at every finite `N`. At any fixed `κ > 0`, Jacobi's modular reflection
   `thetaCuspFullSource (-x) = thetaCuspFullSource x` cancels the partition switch in the `N → ∞`
   limit so `partitionSymThetaAmplitude N κ → xi`, `-partitionSymThetaFirstMoment N κ → deriv xi`
   uniformly on vertical strips, and `partitionSymCollisionOperator T n N κ` stabilizes to
   `(xiHorizontalCollisionCharge T : ℤ)`. Conversely, as `κ → ∞` at fixed `N`, uniform strip
   convergence to `finiteThetaAmplitude N` transfers arbitrarily many (`M`) distinct off-line zeros
   outside `|z.re - 1 / 2| ≤ R` via symmetric Rouché, ruling out Laguerre–Pólya critical-line purity.
-/

set_option autoImplicit false

open Complex MeasureTheory Filter Set Metric intervalIntegral Polynomial
open scoped BigOperators Topology Classical Real ContDiff Convolution

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-! ## §1 Subquadratic Hadamard obstruction and infinitude of off-line zeros -/

/-- Explicit half-Gaussian envelope constant for `thetaCuspSeed` on `[0, ∞)`. -/
private def thetaCuspSeedHalfGaussConst : ℝ :=
  4 * Real.pi ^ 2 * Real.exp (8 / Real.pi) + 6 * Real.pi * Real.exp (2 / Real.pi)

private lemma thetaCuspSeedHalfGaussConst_pos : 0 < thetaCuspSeedHalfGaussConst := by
  unfold thetaCuspSeedHalfGaussConst
  positivity

/-- Half-Gaussian bound `|thetaCuspSeed u| ≤ C * exp (-(π / 2) u²)` valid for all `u ≥ 0`. -/
private lemma abs_thetaCuspSeed_le_halfGauss {u : ℝ} (hu : 0 ≤ u) :
    |_root_.RHTower.thetaCuspSeed u| ≤
      thetaCuspSeedHalfGaussConst * Real.exp (-(Real.pi / 2) * u ^ 2) := by
  have h4 := _root_.RHTower.pow_mul_exp_neg_half_pi_sq_le 4 hu
  have h2 := _root_.RHTower.pow_mul_exp_neg_half_pi_sq_le 2 hu
  have h4' : u ^ 4 * Real.exp (-(Real.pi / 2) * u ^ 2) ≤ Real.exp (8 / Real.pi) := by
    refine h4.trans (Real.exp_le_exp.mpr ?_)
    apply le_of_eq; norm_num; ring
  have h2' : u ^ 2 * Real.exp (-(Real.pi / 2) * u ^ 2) ≤ Real.exp (2 / Real.pi) := by
    refine h2.trans (Real.exp_le_exp.mpr ?_)
    apply le_of_eq; norm_num; ring
  have hsplit : Real.exp (-Real.pi * u ^ 2) =
      Real.exp (-(Real.pi / 2) * u ^ 2) * Real.exp (-(Real.pi / 2) * u ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold _root_.RHTower.thetaCuspSeed thetaCuspSeedHalfGaussConst
  have hsub : |2 * Real.pi * u ^ 4 - 3 * u ^ 2| ≤ 2 * Real.pi * u ^ 4 + 3 * u ^ 2 := by
    have htri := abs_sub (2 * Real.pi * u ^ 4) (3 * u ^ 2)
    have hp1 : 0 ≤ 2 * Real.pi * u ^ 4 := by positivity
    have hp2 : 0 ≤ 3 * u ^ 2 := by positivity
    rw [abs_of_nonneg hp1, abs_of_nonneg hp2] at htri
    exact htri
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi),
    abs_of_pos (Real.exp_pos _), hsplit]
  calc 2 * Real.pi * |2 * Real.pi * u ^ 4 - 3 * u ^ 2| *
          (Real.exp (-(Real.pi / 2) * u ^ 2) * Real.exp (-(Real.pi / 2) * u ^ 2))
      ≤ 2 * Real.pi * (2 * Real.pi * u ^ 4 + 3 * u ^ 2) *
          (Real.exp (-(Real.pi / 2) * u ^ 2) * Real.exp (-(Real.pi / 2) * u ^ 2)) := by
        gcongr
    _ = (4 * Real.pi ^ 2 * (u ^ 4 * Real.exp (-(Real.pi / 2) * u ^ 2)) +
          6 * Real.pi * (u ^ 2 * Real.exp (-(Real.pi / 2) * u ^ 2))) *
          Real.exp (-(Real.pi / 2) * u ^ 2) := by ring
    _ ≤ (4 * Real.pi ^ 2 * Real.exp (8 / Real.pi) +
          6 * Real.pi * Real.exp (2 / Real.pi)) *
          Real.exp (-(Real.pi / 2) * u ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact add_le_add
          (mul_le_mul_of_nonneg_left h4' (by positivity))
          (mul_le_mul_of_nonneg_left h2' (by positivity))

/-- Explicit polynomial evaluation bound on `ℝ[X]` over its finite support. -/
private lemma abs_eval_le_sum_support (Q : ℝ[X]) (y : ℝ) :
    |Q.eval y| ≤ ∑ k ∈ Q.support, |Q.coeff k| * |y| ^ k := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun k _ => by rw [abs_mul, abs_pow])

private lemma iteratedDeriv_thetaCuspFiniteShellPrefix (N r : ℕ) :
    iteratedDeriv r (_root_.RHTower.thetaCuspFiniteShellPrefix N) =
      _root_.RHTower.thetaFiniteShellJet N r := by
  induction r with
  | zero =>
    rw [iteratedDeriv_zero, _root_.RHTower.thetaFiniteShellJet_zero_eq]
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (_root_.RHTower.hasDerivAt_thetaFiniteShellJet N r x).deriv

private lemma contDiff_thetaCuspFiniteShellPrefix (N : ℕ) :
    ContDiff ℝ ∞ (_root_.RHTower.thetaCuspFiniteShellPrefix N) := by
  rw [contDiff_infty]
  intro n
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _ x
  rw [iteratedDeriv_thetaCuspFiniteShellPrefix N m]
  exact (_root_.RHTower.hasDerivAt_thetaFiniteShellJet N m x).differentiableAt

private lemma reflectedFiniteThetaSource_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ _root_.RHTower.reflectedFiniteThetaSource N x := by
  unfold _root_.RHTower.reflectedFiniteThetaSource _root_.RHTower.thetaCuspFiniteShellPrefix
  exact Finset.sum_nonneg fun m _ =>
    _root_.RHTower.thetaCuspSourceTerm_nonneg_on_halfLine (abs_nonneg x) m

private lemma continuous_reflectedFiniteThetaSource (N : ℕ) :
    Continuous (_root_.RHTower.reflectedFiniteThetaSource N) :=
  (contDiff_thetaCuspFiniteShellPrefix N).continuous.comp continuous_abs

private lemma integrable_reflectedFiniteThetaSource (N : ℕ) :
    Integrable (_root_.RHTower.reflectedFiniteThetaSource (N + 1)) := by
  have hc := _root_.RHTower.integrable_bilateralLaplace (_root_.RHTower.finiteThetaTiltSource N) 0
  refine (Complex.reCLM.integrable_comp hc).congr (Eventually.of_forall fun x => ?_)
  simp [_root_.RHTower.finiteThetaTiltSource]

private lemma integrable_id_mul_reflectedFiniteThetaSource (N : ℕ) :
    Integrable (fun t : ℝ => (t : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) t : ℂ)) := by
  have hc := (_root_.RHTower.finiteThetaTiltSource N).integrable_mul_exp 0 1
  refine hc.congr (Eventually.of_forall fun t => ?_)
  simp [_root_.RHTower.finiteThetaTiltSource]

/-- Cubic exponential decay of `reflectedFiniteThetaSource (N + 1)` across `ℝ`. -/
private lemma reflectedFiniteThetaSource_le_cubic_exp (N : ℕ) (x : ℝ) :
    _root_.RHTower.reflectedFiniteThetaSource (N + 1) x ≤
      ((N + 1 : ℕ) : ℝ) * thetaCuspSeedHalfGaussConst * Real.exp 6 *
        Real.exp (-|x| - (2 / 9 : ℝ) * |x| ^ 3) := by
  set t := |x|
  have ht : 0 ≤ t := abs_nonneg x
  have hcube_exp : (8 / 27 : ℝ) * t ^ 3 ≤ Real.exp (2 * t) := by
    have h1 : (2 / 3 : ℝ) * t ≤ Real.exp (2 * t / 3) := by
      linarith [Real.add_one_le_exp (2 * t / 3)]
    have h3 : ((2 / 3 : ℝ) * t) ^ 3 ≤ (Real.exp (2 * t / 3)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h1 3
    have hexp3 : (Real.exp (2 * t / 3)) ^ 3 = Real.exp (2 * t) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    linarith [h3, hexp3]
  have hpoly_t : t / 2 - (4 / 9 : ℝ) * t ^ 3 ≤ 6 - t - (2 / 9 : ℝ) * t ^ 3 := by
    rcases le_or_gt t 3 with hle | hgt
    · have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht 3
      linarith
    · have hc : 0 ≤ t * (t - 3) ^ 2 := mul_nonneg ht (sq_nonneg _)
      have hexpnd : t * (t - 3) ^ 2 = t ^ 3 - 6 * t ^ 2 + 9 * t := by ring
      have ht2 : 3 * t ≤ t ^ 2 := by nlinarith
      linarith
  have hterm : ∀ m ∈ Finset.range (N + 2),
      _root_.RHTower.thetaCuspSourceTerm t m ≤
        (if m = 0 then 0 else
          thetaCuspSeedHalfGaussConst * Real.exp 6 *
            Real.exp (-t - (2 / 9 : ℝ) * t ^ 3)) := by
    intro m _
    rcases m with _ | m
    · simp [_root_.RHTower.thetaCuspSourceTerm, _root_.RHTower.thetaCuspSeed]
    · simp only [Nat.succ_ne_zero, ↓reduceIte]
      set u := ((m + 1 : ℕ) : ℝ) * Real.exp t
      have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
      have hu0 : 0 ≤ u := by positivity
      have hu2 : Real.exp (2 * t) ≤ u ^ 2 := by
        have hsq : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
        have he2 : (Real.exp t) ^ 2 = Real.exp (2 * t) := by
          rw [← Real.exp_nat_mul]; push_cast; rfl
        calc Real.exp (2 * t) = 1 * (Real.exp t) ^ 2 := by rw [one_mul, he2]
          _ ≤ ((m + 1 : ℕ) : ℝ) ^ 2 * (Real.exp t) ^ 2 :=
              mul_le_mul_of_nonneg_right hsq (by positivity)
          _ = u ^ 2 := by dsimp [u]; ring
      have hpi_u : (4 / 9 : ℝ) * t ^ 3 ≤ (Real.pi / 2) * u ^ 2 := by
        have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
        nlinarith
      have hseed := abs_thetaCuspSeed_le_halfGauss hu0
      have hle_abs := le_abs_self (_root_.RHTower.thetaCuspSeed u)
      calc _root_.RHTower.thetaCuspSourceTerm t (m + 1)
          = Real.exp (t / 2) * _root_.RHTower.thetaCuspSeed u := rfl
        _ ≤ Real.exp (t / 2) *
              (thetaCuspSeedHalfGaussConst * Real.exp (-(Real.pi / 2) * u ^ 2)) :=
            mul_le_mul_of_nonneg_left (hle_abs.trans hseed) (Real.exp_pos _).le
        _ = thetaCuspSeedHalfGaussConst * Real.exp (t / 2 - (Real.pi / 2) * u ^ 2) := by
            calc Real.exp (t / 2) *
                    (thetaCuspSeedHalfGaussConst * Real.exp (-(Real.pi / 2) * u ^ 2))
                = thetaCuspSeedHalfGaussConst *
                    (Real.exp (t / 2) * Real.exp (-(Real.pi / 2) * u ^ 2)) := by ring
              _ = thetaCuspSeedHalfGaussConst * Real.exp (t / 2 - (Real.pi / 2) * u ^ 2) := by
                  rw [← Real.exp_add]; congr 1; congr 1; ring
        _ ≤ thetaCuspSeedHalfGaussConst * Real.exp (6 - t - (2 / 9 : ℝ) * t ^ 3) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
              thetaCuspSeedHalfGaussConst_pos.le
            linarith
        _ = thetaCuspSeedHalfGaussConst * Real.exp 6 *
              Real.exp (-t - (2 / 9 : ℝ) * t ^ 3) := by
            rw [mul_assoc, ← Real.exp_add]; congr 1; congr 1; ring
  unfold _root_.RHTower.reflectedFiniteThetaSource _root_.RHTower.thetaCuspFiniteShellPrefix
  calc (∑ m ∈ Finset.range (N + 2), _root_.RHTower.thetaCuspSourceTerm t m)
      ≤ ∑ m ∈ Finset.range (N + 2),
          (if m = 0 then (0 : ℝ) else
            thetaCuspSeedHalfGaussConst * Real.exp 6 *
              Real.exp (-t - (2 / 9 : ℝ) * t ^ 3)) := Finset.sum_le_sum hterm
    _ = ((N + 1 : ℕ) : ℝ) * thetaCuspSeedHalfGaussConst * Real.exp 6 *
          Real.exp (-t - (2 / 9 : ℝ) * t ^ 3) := by
        rw [Finset.sum_range_succ' _ (N + 1)]
        simp only [Nat.succ_ne_zero, ↓reduceIte, add_zero, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        ring

/-- **Subquadratic order-`3 / 2` growth bound for `finiteThetaAmplitude N`.**
Every finite integer-theta bilateral Laplace amplitude has order at most `3 / 2 < 2` on `ℂ`. -/
theorem finiteThetaAmplitude_subquadratic_growth (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖_root_.RHTower.finiteThetaAmplitude N z‖ ≤
        Real.exp (C * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
  let B : ℝ := 2 * (((N + 1 : ℕ) : ℝ) * thetaCuspSeedHalfGaussConst * Real.exp 6)
  have hB_pos : 0 < B := by
    dsimp [B]
    have hN : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
    positivity [thetaCuspSeedHalfGaussConst_pos]
  let C : ℝ := |Real.log B| + 3
  have hC_nn : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC_nn, fun z => ?_⟩
  set s : ℝ := Real.sqrt (1 + ‖z‖)
  have h1z_pos : 0 < 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hs_pos : 0 < s := Real.sqrt_pos.mpr h1z_pos
  have hs_sq : s ^ 2 = 1 + ‖z‖ := Real.sq_sqrt h1z_pos.le
  have hs_cube : s ^ 3 = (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
    rw [show s = (1 + ‖z‖) ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow (1 + ‖z‖),
      ← Real.rpow_natCast ((1 + ‖z‖) ^ (1 / 2 : ℝ)) 3, ← Real.rpow_mul h1z_pos.le]
    norm_num
  have hint : Integrable (fun x : ℝ =>
      (_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
    simpa only [_root_.RHTower.finiteThetaTiltSource] using
      _root_.RHTower.integrable_bilateralLaplace
        (_root_.RHTower.finiteThetaTiltSource N) ((1 / 2 : ℂ) - z)
  have hpt : ∀ x : ℝ,
      ‖(_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
        (((N + 1 : ℕ) : ℝ) * thetaCuspSeedHalfGaussConst * Real.exp 6 *
          Real.exp (3 * s ^ 3)) * Real.exp (-|x|) := by
    intro x
    have hsrc_nn : 0 ≤ _root_.RHTower.reflectedFiniteThetaSource (N + 1) x :=
      reflectedFiniteThetaSource_nonneg (N + 1) x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsrc_nn, Complex.norm_exp]
    have hre : (((1 / 2 : ℂ) - z) * (x : ℂ)).re ≤ s ^ 2 * |x| := by
      have heq : (((1 / 2 : ℂ) - z) * (x : ℂ)).re = (1 / 2 - z.re) * x := by simp
      have habs : |1 / 2 - z.re| ≤ s ^ 2 := by
        rw [hs_sq]
        have hre_le := Complex.abs_re_le_norm z
        obtain ⟨h1, h2⟩ := abs_le.mp hre_le
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      calc (((1 / 2 : ℂ) - z) * (x : ℂ)).re
          ≤ |(1 / 2 - z.re) * x| := by rw [heq]; exact le_abs_self _
        _ = |1 / 2 - z.re| * |x| := abs_mul _ _
        _ ≤ s ^ 2 * |x| := mul_le_mul_of_nonneg_right habs (abs_nonneg x)
    have hyoung : s ^ 2 * |x| - (2 / 9 : ℝ) * |x| ^ 3 ≤ 3 * s ^ 3 := by
      rcases le_or_gt |x| (3 * s) with hle | hgt
      · have h1 : s ^ 2 * |x| ≤ s ^ 2 * (3 * s) := mul_le_mul_of_nonneg_left hle (sq_nonneg s)
        have h2 : s ^ 2 * (3 * s) = 3 * s ^ 3 := by ring
        have h3 : 0 ≤ |x| ^ 3 := pow_nonneg (abs_nonneg x) 3
        linarith
      · have h1 : 9 * s ^ 2 ≤ |x| ^ 2 := by nlinarith [abs_nonneg x, hs_pos]
        have h2 : (9 * s ^ 2) * |x| ≤ |x| ^ 2 * |x| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg x)
        have h3 : |x| ^ 2 * |x| = |x| ^ 3 := by ring
        have h4 : 0 ≤ s ^ 3 := pow_nonneg hs_pos.le 3
        have h5 : 0 ≤ s ^ 2 * |x| := mul_nonneg (sq_nonneg s) (abs_nonneg x)
        linarith
    have hcoeff_nn : 0 ≤ ((N + 1 : ℕ) : ℝ) * thetaCuspSeedHalfGaussConst * Real.exp 6 *
        Real.exp (-|x| - (2 / 9 : ℝ) * |x| ^ 3) := by
      positivity [thetaCuspSeedHalfGaussConst_pos]
    calc _root_.RHTower.reflectedFiniteThetaSource (N + 1) x *
            Real.exp (((1 / 2 : ℂ) - z) * (x : ℂ)).re
        ≤ (((N + 1 : ℕ) : ℝ) * thetaCuspSeedHalfGaussConst * Real.exp 6 *
            Real.exp (-|x| - (2 / 9 : ℝ) * |x| ^ 3)) * Real.exp (s ^ 2 * |x|) :=
          mul_le_mul (reflectedFiniteThetaSource_le_cubic_exp N x)
            (Real.exp_le_exp.mpr hre) (Real.exp_pos _).le hcoeff_nn
      _ = ((N + 1 : ℕ) : ℝ) * thetaCuspSeedHalfGaussConst * Real.exp 6 *
            Real.exp ((s ^ 2 * |x| - (2 / 9 : ℝ) * |x| ^ 3) - |x|) := by
          rw [mul_assoc _ (Real.exp _), ← Real.exp_add]; congr 1; congr 1; ring
      _ ≤ ((N + 1 : ℕ) : ℝ) * thetaCuspSeedHalfGaussConst * Real.exp 6 *
            Real.exp (3 * s ^ 3 - |x|) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
            (by positivity [thetaCuspSeedHalfGaussConst_pos])
      _ = (((N + 1 : ℕ) : ℝ) * thetaCuspSeedHalfGaussConst * Real.exp 6 *
            Real.exp (3 * s ^ 3)) * Real.exp (-|x|) := by
          rw [sub_eq_add_neg, Real.exp_add, ← mul_assoc]
  have hint_abs : (∫ x : ℝ, Real.exp (-|x|)) = 2 := by
    have heven : ∀ x : ℝ, Real.exp (-|-x|) = Real.exp (-|x|) := fun x => by simp
    have hsplit := HTGeometry.integral_even_eq_two_mul
      _root_.RHTower.integrable_thetaAmplitudeProfile heven
    have hIoi : (∫ x in Ioi (0 : ℝ), Real.exp (-|x|)) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-x) :=
      setIntegral_congr_fun measurableSet_Ioi fun x hx => by
        rw [abs_of_pos (mem_Ioi.mp hx)]
    rw [hsplit, hIoi, integral_exp_neg_Ioi_zero]
    ring
  have h1_le_pow : 1 ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [norm_nonneg z]) (by norm_num)
  calc ‖_root_.RHTower.finiteThetaAmplitude N z‖
      ≤ ∫ x : ℝ, ‖(_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, (((N + 1 : ℕ) : ℝ) * thetaCuspSeedHalfGaussConst * Real.exp 6 *
          Real.exp (3 * s ^ 3)) * Real.exp (-|x|) :=
        integral_mono hint.norm
          (_root_.RHTower.integrable_thetaAmplitudeProfile.const_mul _) hpt
    _ = B * Real.exp (3 * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
        rw [MeasureTheory.integral_const_mul, hint_abs, hs_cube]
        dsimp [B]; ring
    _ = Real.exp (Real.log B + 3 * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
        rw [Real.exp_add, Real.exp_log hB_pos]
    _ ≤ Real.exp (C * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        dsimp [C]
        have hlog : Real.log B ≤ |Real.log B| := le_abs_self _
        nlinarith [abs_nonneg (Real.log B)]

/-- **Superlinear logarithmic growth of `finiteThetaAmplitude N` along the positive real ray.** -/
theorem finiteThetaAmplitude_superlinear_real_ray (N : ℕ) (A : ℝ) :
    ∃ sigma : ℝ, 1 ≤ sigma ∧
      A * sigma < Real.log ‖_root_.RHTower.finiteThetaAmplitude N (sigma : ℂ)‖ := by
  let x₀ : ℝ := max 1 (|A| + 2)
  have hx₀_ge1 : 1 ≤ x₀ := le_max_left _ _
  have hx₀_gtA : A + 1 < x₀ := by
    have h := le_max_right 1 (|A| + 2)
    linarith [le_abs_self A]
  let κ : ℝ := 18 * Real.exp (-Real.pi * Real.exp (2 * (x₀ + 1)) - x₀ / 2)
  have hκ_pos : 0 < κ := by dsimp [κ]; positivity
  let sigma : ℝ := max 1 (|Real.log κ| + 1)
  have hsigma1 : 1 ≤ sigma := le_max_left _ _
  refine ⟨sigma, hsigma1, ?_⟩
  have hreal_int : Integrable (fun x : ℝ =>
      _root_.RHTower.reflectedFiniteThetaSource (N + 1) x *
        Real.exp ((1 / 2 - sigma) * x)) := by
    have hc : Integrable (fun x : ℝ =>
        (_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
          Complex.exp (((1 / 2 : ℂ) - (sigma : ℂ)) * (x : ℂ))) := by
      simpa only [_root_.RHTower.finiteThetaTiltSource] using
        _root_.RHTower.integrable_bilateralLaplace
          (_root_.RHTower.finiteThetaTiltSource N) ((1 / 2 : ℂ) - (sigma : ℂ))
    refine (Complex.reCLM.integrable_comp hc).congr (Eventually.of_forall fun x => ?_)
    dsimp only [Function.comp_apply, Complex.reCLM_apply]
    have hexp : Complex.exp (((1 / 2 : ℂ) - (sigma : ℂ)) * (x : ℂ)) =
        (Real.exp ((1 / 2 - sigma) * x) : ℂ) := by
      rw [Complex.ofReal_exp]; congr 1; push_cast; ring
    rw [hexp, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hamp_eq : _root_.RHTower.finiteThetaAmplitude N (sigma : ℂ) =
      ((∫ x : ℝ, _root_.RHTower.reflectedFiniteThetaSource (N + 1) x *
        Real.exp ((1 / 2 - sigma) * x) : ℝ) : ℂ) := by
    unfold _root_.RHTower.finiteThetaAmplitude
    rw [← integral_complex_ofReal]
    congr 1; funext x
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2; push_cast; ring
  have hnonneg : ∀ x : ℝ,
      0 ≤ _root_.RHTower.reflectedFiniteThetaSource (N + 1) x *
        Real.exp ((1 / 2 - sigma) * x) := fun x =>
    mul_nonneg (reflectedFiniteThetaSource_nonneg (N + 1) x) (Real.exp_pos _).le
  have hset_le : (∫ x in Icc (-(x₀ + 1)) (-x₀),
        _root_.RHTower.reflectedFiniteThetaSource (N + 1) x *
          Real.exp ((1 / 2 - sigma) * x)) ≤
      ∫ x : ℝ, _root_.RHTower.reflectedFiniteThetaSource (N + 1) x *
        Real.exp ((1 / 2 - sigma) * x) :=
    setIntegral_le_integral hreal_int (Eventually.of_forall hnonneg)
  have hpt_lower : ∀ x ∈ Icc (-(x₀ + 1)) (-x₀),
      κ * Real.exp (x₀ * sigma) ≤
        _root_.RHTower.reflectedFiniteThetaSource (N + 1) x *
          Real.exp ((1 / 2 - sigma) * x) := by
    intro x hx
    set y := -x
    have hy_lo : x₀ ≤ y := by dsimp [y]; linarith [hx.2]
    have hy_hi : y ≤ x₀ + 1 := by dsimp [y]; linarith [hx.1]
    have hy1 : 1 ≤ y := hx₀_ge1.trans hy_lo
    have habs : |x| = y := abs_of_neg (by linarith [hx.2, hx₀_ge1])
    have hm1_mem : (1 : ℕ) ∈ Finset.range (N + 2) := Finset.mem_range.mpr (by omega)
    have hsrc_ge : _root_.RHTower.thetaCuspSourceTerm y 1 ≤
        _root_.RHTower.reflectedFiniteThetaSource (N + 1) x := by
      unfold _root_.RHTower.reflectedFiniteThetaSource _root_.RHTower.thetaCuspFiniteShellPrefix
      rw [habs]
      exact Finset.single_le_sum
        (fun m _ => _root_.RHTower.thetaCuspSourceTerm_nonneg_on_halfLine (by linarith) m) hm1_mem
    have he2 : 1 ≤ Real.exp (2 * y) := Real.one_le_exp (by linarith)
    have he4 : Real.exp (2 * y) ≤ Real.exp (4 * y) := Real.exp_le_exp.mpr (by linarith)
    have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hpoly_ge : 3 ≤ 2 * Real.pi * (1 * Real.exp y) ^ 4 - 3 * (1 * Real.exp y) ^ 2 := by
      have hp4 : (1 * Real.exp y) ^ 4 = Real.exp (4 * y) := by
        rw [one_mul, ← Real.exp_nat_mul]; push_cast; rfl
      have hp2 : (1 * Real.exp y) ^ 2 = Real.exp (2 * y) := by
        rw [one_mul, ← Real.exp_nat_mul]; push_cast; rfl
      rw [hp4, hp2]
      nlinarith
    have hgauss_ge : Real.exp (-Real.pi * Real.exp (2 * (x₀ + 1))) ≤
        Real.exp (-Real.pi * (1 * Real.exp y) ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hp2 : (1 * Real.exp y) ^ 2 = Real.exp (2 * y) := by
        rw [one_mul, ← Real.exp_nat_mul]; push_cast; rfl
      rw [hp2]
      have hexp_le : Real.exp (2 * y) ≤ Real.exp (2 * (x₀ + 1)) :=
        Real.exp_le_exp.mpr (by linarith)
      nlinarith [Real.pi_pos]
    have hyhalf : 1 ≤ Real.exp (y / 2) := Real.one_le_exp (by linarith)
    have hterm_ge : 18 * Real.exp (-Real.pi * Real.exp (2 * (x₀ + 1))) ≤
        _root_.RHTower.thetaCuspSourceTerm y 1 := by
      unfold _root_.RHTower.thetaCuspSourceTerm _root_.RHTower.thetaCuspSeed
      simp only [Nat.cast_one]
      have hseed_ge : 18 * Real.exp (-Real.pi * Real.exp (2 * (x₀ + 1))) ≤
          2 * Real.pi * (2 * Real.pi * (1 * Real.exp y) ^ 4 - 3 * (1 * Real.exp y) ^ 2) *
            Real.exp (-Real.pi * (1 * Real.exp y) ^ 2) := by
        calc 18 * Real.exp (-Real.pi * Real.exp (2 * (x₀ + 1)))
            ≤ (2 * Real.pi * (2 * Real.pi * (1 * Real.exp y) ^ 4 - 3 * (1 * Real.exp y) ^ 2)) *
                Real.exp (-Real.pi * Real.exp (2 * (x₀ + 1))) :=
              mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le
          _ ≤ (2 * Real.pi * (2 * Real.pi * (1 * Real.exp y) ^ 4 - 3 * (1 * Real.exp y) ^ 2)) *
                Real.exp (-Real.pi * (1 * Real.exp y) ^ 2) :=
              mul_le_mul_of_nonneg_left hgauss_ge (by positivity)
      exact (le_mul_of_one_le_left (by positivity) hyhalf).trans
        (mul_le_mul_of_nonneg_left hseed_ge (Real.exp_pos _).le)
    have hexp_ge : Real.exp (x₀ * sigma - x₀ / 2) ≤ Real.exp ((1 / 2 - sigma) * x) := by
      apply Real.exp_le_exp.mpr
      have h1 : (1 / 2 - sigma) * x = (sigma - 1 / 2) * y := by dsimp [y]; ring
      rw [h1]
      nlinarith [hsigma1, hy_lo]
    calc κ * Real.exp (x₀ * sigma)
        = (18 * Real.exp (-Real.pi * Real.exp (2 * (x₀ + 1)))) *
            Real.exp (x₀ * sigma - x₀ / 2) := by
          dsimp [κ]
          rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
          congr 1; congr 1; ring
      _ ≤ _root_.RHTower.reflectedFiniteThetaSource (N + 1) x *
            Real.exp ((1 / 2 - sigma) * x) :=
          mul_le_mul (hterm_ge.trans hsrc_ge) hexp_ge (Real.exp_pos _).le
            (le_trans (by positivity) (hterm_ge.trans hsrc_ge))
  have hconst_le : κ * Real.exp (x₀ * sigma) ≤
      ∫ x in Icc (-(x₀ + 1)) (-x₀),
        _root_.RHTower.reflectedFiniteThetaSource (N + 1) x *
          Real.exp ((1 / 2 - sigma) * x) := by
    have hmono := setIntegral_mono_on
      (integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      hreal_int.integrableOn measurableSet_Icc hpt_lower
    rw [setIntegral_const, Measure.real_def, Real.volume_Icc,
      show -x₀ - -(x₀ + 1) = (1 : ℝ) by ring, ENNReal.toReal_ofReal zero_le_one, one_smul] at hmono
    exact hmono
  have htotal_ge : κ * Real.exp (x₀ * sigma) ≤
      ‖_root_.RHTower.finiteThetaAmplitude N (sigma : ℂ)‖ := by
    rw [hamp_eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (by positivity) (hconst_le.trans hset_le))]
    exact hconst_le.trans hset_le
  have hnorm_pos : 0 < ‖_root_.RHTower.finiteThetaAmplitude N (sigma : ℂ)‖ :=
    lt_of_lt_of_le (by positivity) htotal_ge
  rw [Real.lt_log_iff_exp_lt hnorm_pos]
  have hsigma_log : |Real.log κ| + 1 ≤ sigma := le_max_right _ _
  have hexp_lt : Real.exp (A * sigma) < κ * Real.exp (x₀ * sigma) := by
    rw [show κ * Real.exp (x₀ * sigma) = Real.exp (Real.log κ + x₀ * sigma) by
      rw [Real.exp_add, Real.exp_log hκ_pos]]
    apply Real.exp_lt_exp.mpr
    have hlog_ge : -|Real.log κ| ≤ Real.log κ := neg_abs_le _
    nlinarith [hx₀_gtA, hsigma1, hsigma_log, abs_nonneg (Real.log κ)]
  exact hexp_lt.trans_le htotal_ge

/-- **Complex zero infinitude of every finite integer theta prefix `finiteThetaAmplitude N`.** -/
theorem finiteThetaAmplitude_zeros_infinite (N : ℕ) :
    {z : ℂ | _root_.RHTower.finiteThetaAmplitude N z = 0}.Infinite := by
  obtain ⟨C, hC, hgrow⟩ := finiteThetaAmplitude_subquadratic_growth N
  exact _root_.RHTower.zeroSet_infinite_of_subquadratic_superlinear_ray
    (_root_.RHTower.differentiable_finiteThetaAmplitude N)
    (by norm_num : (0 : ℝ) ≤ 3 / 2) (by norm_num : (3 / 2 : ℝ) < 2) hC hgrow
    (finiteThetaAmplitude_superlinear_real_ray N)

/-- **Unconditional infinitude of off-line zeros outside every vertical strip.**
For every prefix `N : ℕ` and every strip half-width `R : ℝ`, `finiteThetaAmplitude N` has
infinitely many complex zeros satisfying `R < |z.re - 1 / 2|`. -/
theorem finiteThetaAmplitude_offline_zeros_outside_strip_infinite (N : ℕ) (R : ℝ) :
    {z : ℂ | _root_.RHTower.finiteThetaAmplitude N z = 0 ∧ R < |z.re - 1 / 2|}.Infinite := by
  have hinf := (finiteThetaAmplitude_zeros_infinite N).sdiff
    (finiteThetaAmplitude_strip_zeros_finite N R)
  refine hinf.mono fun z hz => ?_
  refine ⟨hz.1, ?_⟩
  by_contra hle
  exact hz.2 ⟨not_lt.mp hle, hz.1⟩

/-- **Failure of Laguerre–Pólya / Hermite–Biehler critical-line purity for every finite prefix.**
For every `N : ℕ`, the critical-line pullback `z ↦ finiteThetaAmplitude N (1 / 2 + I * z)` is not
in `HTGeometry.LaguerrePolya`. -/
theorem not_laguerrePolya_finiteThetaAmplitude_criticalLine (N : ℕ) :
    ¬ HTGeometry.LaguerrePolya
      (fun z : ℂ => _root_.RHTower.finiteThetaAmplitude N ((1 / 2 : ℂ) + I * z)) := by
  intro hLP
  obtain ⟨w, hw_mem⟩ := (finiteThetaAmplitude_offline_zeros_outside_strip_infinite N 0).nonempty
  set z₀ : ℂ := -I * (w - (1 / 2 : ℂ))
  have hw_eq : (1 / 2 : ℂ) + I * z₀ = w := by
    dsimp [z₀]; rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul, add_sub_cancel]
  have hz₀_zero : _root_.RHTower.finiteThetaAmplitude N ((1 / 2 : ℂ) + I * z₀) = 0 := by
    rw [hw_eq]; exact hw_mem.1
  have h0_ne : _root_.RHTower.finiteThetaAmplitude N ((1 / 2 : ℂ) + I * 0) ≠ 0 := by
    rw [mul_zero, add_zero]
    have hre := finiteThetaAmplitude_re_ge_lowWindow N (z := (1 / 2 : ℂ))
      (by norm_num) (by norm_num)
    intro h0
    rw [h0, Complex.zero_re] at hre
    have hpos : (0 : ℝ) < (5026 / 16875) * Real.exp (-Real.pi) := by positivity
    linarith
  have him0 := HTGeometry.im_eq_zero_of_laguerrePolya hLP h0_ne hz₀_zero
  have hz₀_im : z₀.im = -(w.re - 1 / 2) := by
    dsimp [z₀]
    simp [Complex.mul_im, Complex.sub_re]
  rw [hz₀_im] at him0
  have hre_eq : |w.re - 1 / 2| = 0 := by
    rw [abs_eq_zero]; linarith
  linarith [hw_mem.2]

/-! ## §2 `x`-space Gaussian seam-mollification and exact collision-operator gauge invariance -/

/-- General odd-origin-jet vanishing for any `ℝ → ℝ` even function. -/
private lemma iteratedDeriv_odd_zero_of_even_real {f : ℝ → ℝ} (heven : ∀ x : ℝ, f (-x) = f x)
    (k : ℕ) :
    iteratedDeriv (2 * k + 1) f 0 = 0 := by
  have hfun : (fun x : ℝ => f (-x)) = f := funext heven
  have hcomp := iteratedDeriv_comp_neg (2 * k + 1) f 0
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  rw [hfun, neg_zero, hodd.neg_one_pow] at hcomp
  simp only [neg_one_smul] at hcomp
  linarith

/-- Parity of `iteratedDeriv K f` for an even function `f : ℝ → ℝ`: `|f^{(K)}(-x)| = |f^{(K)}(x)|`. -/
private lemma abs_iteratedDeriv_neg_eq_of_even_real {f : ℝ → ℝ} (heven : ∀ x : ℝ, f (-x) = f x)
    (K : ℕ) (x : ℝ) :
    |iteratedDeriv K f (-x)| = |iteratedDeriv K f x| := by
  have hfun : (fun y : ℝ => f (-y)) = f := funext heven
  have hcomp := iteratedDeriv_comp_neg K f (-x)
  rw [hfun, neg_neg, smul_eq_mul] at hcomp
  rw [hcomp, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- Iterated polynomial factors for derivatives of `gaussPolyFun 1 β`. -/
private def iterGaussPoly (β : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | m + 1 => GaloisForLFunctions.gaussPolyDerivPoly (iterGaussPoly β m) β

private lemma hasDerivAt_iterGaussPoly (β : ℝ) (m : ℕ) (y : ℝ) :
    HasDerivAt (GaloisForLFunctions.gaussPolyFun (iterGaussPoly β m) β)
      (GaloisForLFunctions.gaussPolyFun (iterGaussPoly β (m + 1)) β y) y :=
  GaloisForLFunctions.hasDerivAt_gaussPolyFun (iterGaussPoly β m) β y

private lemma iteratedDeriv_gaussPolyFun_one (β : ℝ) (m : ℕ) :
    iteratedDeriv m (GaloisForLFunctions.gaussPolyFun 1 β) =
      GaloisForLFunctions.gaussPolyFun (iterGaussPoly β m) β := by
  induction m with
  | zero => simp [iterGaussPoly]
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    exact (hasDerivAt_iterGaussPoly β m y).deriv

/-- Explicit half-Gaussian decay bound for any polynomial–Gaussian `gaussPolyFun Q β` (`β > 0`). -/
private lemma abs_gaussPolyFun_le_halfGauss (Q : ℝ[X]) {β : ℝ} (hβ : 0 < β) (y : ℝ) :
    |GaloisForLFunctions.gaussPolyFun Q β y| ≤
      (∑ k ∈ Q.support, |Q.coeff k| * Real.exp ((k : ℝ) ^ 2 / (2 * β))) *
        Real.exp (-(β / 2) * y ^ 2) := by
  have heval : |Q.eval y| ≤ ∑ k ∈ Q.support, |Q.coeff k| * |y| ^ k :=
    abs_eval_le_sum_support Q y
  have hsplit : Real.exp (-(β * y ^ 2)) =
      Real.exp (-(β / 2) * y ^ 2) * Real.exp (-(β / 2) * y ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpow : ∀ k : ℕ,
      |y| ^ k * Real.exp (-(β / 2) * y ^ 2) ≤ Real.exp ((k : ℝ) ^ 2 / (2 * β)) := by
    intro k
    have hy_exp : |y| ≤ Real.exp |y| := by linarith [Real.add_one_le_exp |y|]
    have hpow_exp : |y| ^ k ≤ Real.exp ((k : ℝ) * |y|) := by
      calc |y| ^ k ≤ (Real.exp |y|) ^ k := pow_le_pow_left₀ (abs_nonneg y) hy_exp k
        _ = Real.exp ((k : ℝ) * |y|) := (Real.exp_nat_mul |y| k).symm
    have hquad : (k : ℝ) * |y| - (β / 2) * y ^ 2 ≤ (k : ℝ) ^ 2 / (2 * β) := by
      rw [le_div_iff₀ (by positivity), ← sq_abs y]
      have hid : (k : ℝ) ^ 2 - ((k : ℝ) * |y| - (β / 2) * |y| ^ 2) * (2 * β) =
          (β * |y| - (k : ℝ)) ^ 2 := by ring
      linarith [sq_nonneg (β * |y| - (k : ℝ))]
    calc |y| ^ k * Real.exp (-(β / 2) * y ^ 2)
        ≤ Real.exp ((k : ℝ) * |y|) * Real.exp (-(β / 2) * y ^ 2) :=
          mul_le_mul_of_nonneg_right hpow_exp (Real.exp_pos _).le
      _ = Real.exp ((k : ℝ) * |y| - (β / 2) * y ^ 2) := by
          rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((k : ℝ) ^ 2 / (2 * β)) := Real.exp_le_exp.mpr hquad
  unfold GaloisForLFunctions.gaussPolyFun
  rw [abs_mul, abs_of_pos (Real.exp_pos _), hsplit]
  calc |Q.eval y| * (Real.exp (-(β / 2) * y ^ 2) * Real.exp (-(β / 2) * y ^ 2))
      ≤ (∑ k ∈ Q.support, |Q.coeff k| * |y| ^ k) *
          (Real.exp (-(β / 2) * y ^ 2) * Real.exp (-(β / 2) * y ^ 2)) :=
        mul_le_mul_of_nonneg_right heval (by positivity)
    _ = (∑ k ∈ Q.support, |Q.coeff k| * (|y| ^ k * Real.exp (-(β / 2) * y ^ 2))) *
          Real.exp (-(β / 2) * y ^ 2) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => by ring
    _ ≤ (∑ k ∈ Q.support, |Q.coeff k| * Real.exp ((k : ℝ) ^ 2 / (2 * β))) *
          Real.exp (-(β / 2) * y ^ 2) := by
        refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun k _ => ?_) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left (hpow k) (abs_nonneg _)

/-- `x`-space Gaussian-mollified finite Jacobi-theta source `(P_{N+1}(|·|) * G_a)(x)`. -/
def gaussMollifiedThetaSource (N : ℕ) (a x : ℝ) : ℝ :=
  _root_.RHTower.heatSmooth a (_root_.RHTower.reflectedFiniteThetaSource (N + 1)) x

/-- Evenness of `gaussMollifiedThetaSource N a` across `x = 0`. -/
theorem gaussMollifiedThetaSource_even (N : ℕ) (a x : ℝ) :
    gaussMollifiedThetaSource N a (-x) = gaussMollifiedThetaSource N a x := by
  unfold gaussMollifiedThetaSource _root_.RHTower.heatSmooth
  rw [← MeasureTheory.integral_neg_eq_self (fun t =>
    _root_.RHTower.reflectedFiniteThetaSource (N + 1) t * _root_.RHTower.gaussHeatKernel a (-x - t))]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [_root_.RHTower.reflectedFiniteThetaSource_even (N + 1) t]
  congr 1
  unfold _root_.RHTower.gaussHeatKernel
  congr 2
  ring

/-- Strict positivity of `gaussMollifiedThetaSource N a` on `ℝ` for every `a > 0`. -/
theorem gaussMollifiedThetaSource_pos (N : ℕ) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    0 < gaussMollifiedThetaSource N a x := by
  unfold gaussMollifiedThetaSource _root_.RHTower.heatSmooth
  have hsrc_int : Integrable (_root_.RHTower.reflectedFiniteThetaSource (N + 1)) :=
    integrable_reflectedFiniteThetaSource N
  have hker_le : ∀ t : ℝ, |_root_.RHTower.gaussHeatKernel a (x - t)| ≤
      (2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) := by
    intro t
    unfold _root_.RHTower.gaussHeatKernel
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _), abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
  have hint' : Integrable (fun t : ℝ =>
      _root_.RHTower.reflectedFiniteThetaSource (N + 1) t *
        _root_.RHTower.gaussHeatKernel a (x - t)) := by
    have haesm : AEStronglyMeasurable (fun t : ℝ => _root_.RHTower.gaussHeatKernel a (x - t)) := by
      unfold _root_.RHTower.gaussHeatKernel
      exact (continuous_const.mul (Real.continuous_exp.comp
        (((continuous_const.sub continuous_id).pow 2).div_const (2 * a)).neg)).aestronglyMeasurable
    have h := Integrable.bdd_mul hsrc_int haesm
      (Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using hker_le t)
    exact h.congr (Eventually.of_forall fun t => mul_comm _ _)
  have hnn : ∀ t : ℝ, 0 ≤ _root_.RHTower.reflectedFiniteThetaSource (N + 1) t *
      _root_.RHTower.gaussHeatKernel a (x - t) := by
    intro t
    refine mul_nonneg (reflectedFiniteThetaSource_nonneg (N + 1) t) ?_
    unfold _root_.RHTower.gaussHeatKernel; positivity
  have hset_le := setIntegral_le_integral hint' (Eventually.of_forall hnn) (s := Icc (0 : ℝ) 1)
  have hcont : Continuous (fun t : ℝ =>
      _root_.RHTower.reflectedFiniteThetaSource (N + 1) t *
        _root_.RHTower.gaussHeatKernel a (x - t)) := by
    refine (continuous_reflectedFiniteThetaSource (N + 1)).mul ?_
    unfold _root_.RHTower.gaussHeatKernel
    exact continuous_const.mul (Real.continuous_exp.comp
      (((continuous_const.sub continuous_id).pow 2).div_const (2 * a)).neg)
  obtain ⟨t₀, _, ht₀_min⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hcont.continuousOn
  set c := _root_.RHTower.reflectedFiniteThetaSource (N + 1) t₀ *
    _root_.RHTower.gaussHeatKernel a (x - t₀)
  have hc_pos : 0 < c := by
    dsimp [c]
    have hm1 : (1 : ℕ) ∈ Finset.range (N + 2) := Finset.mem_range.mpr (by omega)
    have ht1_pos : 0 < _root_.RHTower.thetaCuspSourceTerm |t₀| 1 := by
      rcases (abs_nonneg t₀).eq_or_lt with h0 | hpos
      · rw [← h0]; exact _root_.RHTower.thetaCuspSourceTerm_zero_pos Nat.one_pos
      · unfold _root_.RHTower.thetaCuspSourceTerm _root_.RHTower.thetaCuspSeed
        simp only [Nat.cast_one, one_mul]
        have he2 : 1 ≤ Real.exp |t₀| ^ 2 := one_le_pow₀ (Real.one_le_exp hpos.le)
        have he4 : Real.exp |t₀| ^ 2 ≤ Real.exp |t₀| ^ 4 := by
          nlinarith [Real.one_le_exp hpos.le]
        have hpi := Real.pi_gt_three
        exact mul_pos (Real.exp_pos _) (mul_pos (mul_pos (by positivity) (by nlinarith))
          (Real.exp_pos _))
    have hsrc_pos : 0 < _root_.RHTower.reflectedFiniteThetaSource (N + 1) t₀ := by
      unfold _root_.RHTower.reflectedFiniteThetaSource _root_.RHTower.thetaCuspFiniteShellPrefix
      exact lt_of_lt_of_le ht1_pos (Finset.single_le_sum
        (fun m _ => _root_.RHTower.thetaCuspSourceTerm_nonneg_on_halfLine (abs_nonneg t₀) m) hm1)
    have hker_pos : 0 < _root_.RHTower.gaussHeatKernel a (x - t₀) := by
      unfold _root_.RHTower.gaussHeatKernel; positivity
    exact mul_pos hsrc_pos hker_pos
  have hmono := setIntegral_mono_on
    (integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    hint'.integrableOn measurableSet_Icc (fun t ht => isMinOn_iff.mp ht₀_min t ht)
  rw [setIntegral_const, Measure.real_def, Real.volume_Icc, sub_zero,
    ENNReal.toReal_ofReal zero_le_one, one_smul] at hmono
  exact lt_of_lt_of_le hc_pos (hmono.trans hset_le)

/-- Stepwise differentiation under the integral for `gaussMollifiedThetaSource N a`. -/
private lemma hasDerivAt_gaussMollifiedKernelIntegral (N m : ℕ) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ t : ℝ, _root_.RHTower.reflectedFiniteThetaSource (N + 1) t *
        GaloisForLFunctions.gaussPolyFun (iterGaussPoly (1 / (2 * a)) m) (1 / (2 * a)) (y - t))
      (∫ t : ℝ, _root_.RHTower.reflectedFiniteThetaSource (N + 1) t *
        GaloisForLFunctions.gaussPolyFun (iterGaussPoly (1 / (2 * a)) (m + 1)) (1 / (2 * a))
          (x - t)) x := by
  have hβ : 0 < 1 / (2 * a) := by positivity
  have hsrc_int : Integrable (_root_.RHTower.reflectedFiniteThetaSource (N + 1)) :=
    integrable_reflectedFiniteThetaSource N
  let K_bd : ℝ := ∑ k ∈ (iterGaussPoly (1 / (2 * a)) (m + 1)).support,
    |(iterGaussPoly (1 / (2 * a)) (m + 1)).coeff k| *
      Real.exp ((k : ℝ) ^ 2 / (2 * (1 / (2 * a))))
  let K_m : ℝ := ∑ k ∈ (iterGaussPoly (1 / (2 * a)) m).support,
    |(iterGaussPoly (1 / (2 * a)) m).coeff k| *
      Real.exp ((k : ℝ) ^ 2 / (2 * (1 / (2 * a))))
  have hpt_m : ∀ (y t : ℝ),
      |GaloisForLFunctions.gaussPolyFun (iterGaussPoly (1 / (2 * a)) m) (1 / (2 * a)) (y - t)| ≤
        K_m := by
    intro y t
    refine (abs_gaussPolyFun_le_halfGauss _ hβ (y - t)).trans ?_
    exact mul_le_of_le_one_right
      (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
      (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (y - t)]))
  have hpt_bd : ∀ (y t : ℝ),
      |GaloisForLFunctions.gaussPolyFun (iterGaussPoly (1 / (2 * a)) (m + 1)) (1 / (2 * a))
          (y - t)| ≤ K_bd := by
    intro y t
    refine (abs_gaussPolyFun_le_halfGauss _ hβ (y - t)).trans ?_
    exact mul_le_of_le_one_right
      (Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
      (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (y - t)]))
  have hint_y : ∀ y : ℝ, Integrable (fun t : ℝ =>
      _root_.RHTower.reflectedFiniteThetaSource (N + 1) t *
        GaloisForLFunctions.gaussPolyFun (iterGaussPoly (1 / (2 * a)) m) (1 / (2 * a))
          (y - t)) := by
    intro y
    have hcont_g : Continuous (fun t : ℝ =>
        GaloisForLFunctions.gaussPolyFun (iterGaussPoly (1 / (2 * a)) m) (1 / (2 * a)) (y - t)) :=
      (GaloisForLFunctions.continuous_gaussPolyFun _ _).comp (continuous_const.sub continuous_id)
    have h := Integrable.bdd_mul hsrc_int hcont_g.aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hpt_m y t)
    exact h.congr (Eventually.of_forall fun t => mul_comm _ _)
  have hF'_cont : Continuous (fun t : ℝ =>
      _root_.RHTower.reflectedFiniteThetaSource (N + 1) t *
        GaloisForLFunctions.gaussPolyFun (iterGaussPoly (1 / (2 * a)) (m + 1)) (1 / (2 * a))
          (x - t)) :=
    (continuous_reflectedFiniteThetaSource (N + 1)).mul
      ((GaloisForLFunctions.continuous_gaussPolyFun _ _).comp (continuous_const.sub continuous_id))
  refine (_root_.hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (F' := fun y t =>
      _root_.RHTower.reflectedFiniteThetaSource (N + 1) t *
        GaloisForLFunctions.gaussPolyFun (iterGaussPoly (1 / (2 * a)) (m + 1)) (1 / (2 * a))
          (y - t))
    (bound := fun t => K_bd * |_root_.RHTower.reflectedFiniteThetaSource (N + 1) t|)
    univ_mem
    (Eventually.of_forall fun y => (hint_y y).aestronglyMeasurable)
    (hint_y x)
    hF'_cont.aestronglyMeasurable
    (Eventually.of_forall fun t y _ => ?_)
    (hsrc_int.norm.const_mul K_bd)
    (Eventually.of_forall fun t y _ => ?_)).2
  · rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hpt_bd y t) (abs_nonneg _)
  · have hd := (hasDerivAt_iterGaussPoly (1 / (2 * a)) m (y - t)).comp y
      ((hasDerivAt_id y).sub_const t)
    refine (hd.const_mul (_root_.RHTower.reflectedFiniteThetaSource (N + 1) t)).congr_deriv ?_
    ring

private lemma iteratedDeriv_gaussMollifiedThetaSource_eq (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ m : ℕ, iteratedDeriv m (gaussMollifiedThetaSource N a) = fun x : ℝ =>
      (2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) *
        ∫ t : ℝ, _root_.RHTower.reflectedFiniteThetaSource (N + 1) t *
          GaloisForLFunctions.gaussPolyFun (iterGaussPoly (1 / (2 * a)) m) (1 / (2 * a)) (x - t) := by
  intro m
  induction m with
  | zero =>
    rw [iteratedDeriv_zero]
    funext x
    unfold gaussMollifiedThetaSource _root_.RHTower.heatSmooth
    rw [← MeasureTheory.integral_const_mul]
    congr 1; funext t
    unfold _root_.RHTower.gaussHeatKernel GaloisForLFunctions.gaussPolyFun iterGaussPoly
    rw [Polynomial.eval_one, one_mul]
    have hexp : -((x - t) ^ 2 / (2 * a)) = -(1 / (2 * a) * (x - t) ^ 2) := by ring
    rw [hexp]; ring
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact ((hasDerivAt_gaussMollifiedKernelIntegral N m ha x).const_mul
      ((2 * Real.pi * a) ^ (-(1 / 2 : ℝ)))).deriv

/-- **`C^∞` smoothness of `gaussMollifiedThetaSource N a` across the entire real line (`a > 0`).** -/
theorem contDiff_gaussMollifiedThetaSource (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ ∞ (gaussMollifiedThetaSource N a) := by
  rw [contDiff_infty]
  intro n
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _ x
  rw [iteratedDeriv_gaussMollifiedThetaSource_eq N ha m]
  exact ((hasDerivAt_gaussMollifiedKernelIntegral N m ha x).const_mul _).differentiableAt

/-- **All-order seam-cusp elimination under Gaussian mollification:** every odd origin derivative
vanishes identically. -/
theorem iteratedDeriv_odd_gaussMollifiedThetaSource_zero (N : ℕ) (a : ℝ) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (gaussMollifiedThetaSource N a) 0 = 0 :=
  iteratedDeriv_odd_zero_of_even_real (gaussMollifiedThetaSource_even N a) k

/-- Bilateral Laplace amplitude of `gaussMollifiedThetaSource N a`. -/
def gaussMollifiedThetaAmplitude (N : ℕ) (a : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (gaussMollifiedThetaSource N a x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))

/-- **Exact Gaussian factor identity for `gaussMollifiedThetaAmplitude N a`.**
`x`-space Gaussian convolution multiplies `finiteThetaAmplitude N z` by the zero-free entire unit
`exp ((a / 2) * (z - 1 / 2)²)`. -/
theorem gaussMollifiedThetaAmplitude_eq (N : ℕ) {a : ℝ} (ha : 0 < a) (z : ℂ) :
    gaussMollifiedThetaAmplitude N a z =
      Complex.exp (((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2) *
        _root_.RHTower.finiteThetaAmplitude N z := by
  set w : ℂ := -I * ((1 / 2 : ℂ) - z)
  have hIw : I * w = (1 / 2 : ℂ) - z := by
    dsimp [w]; rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
  set f : ℝ → ℂ := fun t =>
    (_root_.RHTower.reflectedFiniteThetaSource (N + 1) t : ℂ) *
      Complex.exp (((1 / 2 : ℂ) - z) * (t : ℂ))
  set g : ℝ → ℂ := fun y =>
    (_root_.RHTower.gaussHeatKernel a y : ℂ) * Complex.exp (I * w * y)
  have hfi : Integrable f := by
    simpa only [f, _root_.RHTower.finiteThetaTiltSource] using
      _root_.RHTower.integrable_bilateralLaplace
        (_root_.RHTower.finiteThetaTiltSource N) ((1 / 2 : ℂ) - z)
  have hgi : Integrable g := _root_.RHTower.integrable_heatKernel_mul_cexp ha w
  have hconv : ∀ x : ℝ,
      (gaussMollifiedThetaSource N a x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) =
        (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) x := by
    intro x
    rw [convolution_def, gaussMollifiedThetaSource, _root_.RHTower.heatSmooth,
      ← integral_complex_ofReal, ← MeasureTheory.integral_mul_const]
    congr 1; funext t
    simp only [f, g, ContinuousLinearMap.mul_apply']
    have hexp : Complex.exp (((1 / 2 : ℂ) - z) * (t : ℂ)) *
          Complex.exp (I * w * ((x - t : ℝ) : ℂ)) =
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) := by
      have hw_mul : I * w * ((x - t : ℝ) : ℂ) = ((1 / 2 : ℂ) - z) * ((x - t : ℝ) : ℂ) := by
        rw [hIw]
      rw [hw_mul, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [Complex.ofReal_mul, ← hexp]
    ring
  unfold gaussMollifiedThetaAmplitude
  simp_rw [hconv]
  rw [integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hfi hgi,
    ContinuousLinearMap.mul_apply', mul_comm]
  have hker := _root_.RHTower.heatStripTransform_heatKernel ha w
  unfold _root_.RHTower.heatStripTransform at hker
  have hg_int : (∫ y : ℝ, g y) = Complex.exp (((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2) := by
    have hsq : -(a : ℂ) * w ^ 2 / 2 = ((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2 := by
      dsimp [w]
      have hI2 : (-I) ^ 2 = (-1 : ℂ) := by rw [neg_sq, I_sq]
      calc -(a : ℂ) * (-I * ((1 / 2 : ℂ) - z)) ^ 2 / 2
          = -(a : ℂ) * ((-I) ^ 2 * ((1 / 2 : ℂ) - z) ^ 2) / 2 := by rw [mul_pow]
        _ = ((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2 := by rw [hI2]; ring
    simpa only [g, mul_assoc, hsq] using hker
  rw [hg_int]
  rfl

theorem differentiable_gaussMollifiedThetaAmplitude (N : ℕ) {a : ℝ} (ha : 0 < a) :
    Differentiable ℂ (gaussMollifiedThetaAmplitude N a) := by
  have heq : gaussMollifiedThetaAmplitude N a = fun z : ℂ =>
      Complex.exp (((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2) *
        _root_.RHTower.finiteThetaAmplitude N z :=
    funext (gaussMollifiedThetaAmplitude_eq N ha)
  rw [heq]
  exact (((differentiable_id.sub_const (1 / 2 : ℂ)).pow 2).const_mul ((a : ℂ) / 2)).cexp.mul
    (_root_.RHTower.differentiable_finiteThetaAmplitude N)

/-- **Super-polynomial (Gaussian) vertical-strip decay of `gaussMollifiedThetaAmplitude N a` at
every finite `N`.** -/
theorem gaussMollifiedThetaAmplitude_superpolynomial_strip_decay (N : ℕ) {a : ℝ} (ha : 0 < a)
    {R : ℝ} (hR : 0 ≤ R) (K : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, |z.re - 1 / 2| ≤ R →
      ‖z - (1 / 2 : ℂ)‖ ^ K * ‖gaussMollifiedThetaAmplitude N a z‖ ≤
        B * Real.exp (-(a / 4) * z.im ^ 2) := by
  let M_amp : ℝ := max 1 (_root_.RHTower.thetaAmplitudeEnvelope (R + 1))
  let B : ℝ := M_amp * Real.exp ((a / 2) * R ^ 2 + (K : ℝ) * R + (K : ℝ) ^ 2 / a)
  refine ⟨B, by dsimp [B, M_amp]; positivity, fun z hz => ?_⟩
  rw [gaussMollifiedThetaAmplitude_eq N ha z, norm_mul, Complex.norm_exp]
  have hz_re : |z.re| ≤ R + 1 := by
    obtain ⟨h1, h2⟩ := abs_le.mp hz
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hamp_le : ‖_root_.RHTower.finiteThetaAmplitude N z‖ ≤ M_amp := by
    have h1 := _root_.RHTower.norm_finiteThetaAmplitude_le_strip N (by linarith : 0 ≤ R + 1) hz_re
    exact h1.trans (le_max_right 1 _)
  have hexp_re : (((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2).re ≤
      (a / 2) * R ^ 2 - (a / 2) * z.im ^ 2 := by
    have hre_calc : (((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2).re =
        (a / 2) * ((z.re - 1 / 2) ^ 2 - z.im ^ 2) := by
      simp only [sq, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
        Complex.one_re, Complex.one_im]
      ring
    rw [hre_calc]
    have hsq : (z.re - 1 / 2) ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs (z.re - 1 / 2)]
      exact pow_le_pow_left₀ (abs_nonneg _) hz 2
    nlinarith
  have hnorm_sub : ‖z - (1 / 2 : ℂ)‖ ≤ R + |z.im| := by
    have h1 : ‖z - (1 / 2 : ℂ)‖ ≤ |(z - (1 / 2 : ℂ)).re| + |(z - (1 / 2 : ℂ)).im| :=
      Complex.norm_le_abs_re_add_abs_im (z - (1 / 2 : ℂ))
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_im, zero_div, sub_zero] at h1
    linarith
  have hpow_le : ‖z - (1 / 2 : ℂ)‖ ^ K ≤
      Real.exp ((K : ℝ) * R + (K : ℝ) * |z.im|) := by
    have ht_exp : R + |z.im| ≤ Real.exp (R + |z.im|) := by
      linarith [Real.add_one_le_exp (R + |z.im|)]
    calc ‖z - (1 / 2 : ℂ)‖ ^ K
        ≤ (R + |z.im|) ^ K := pow_le_pow_left₀ (norm_nonneg _) hnorm_sub K
      _ ≤ (Real.exp (R + |z.im|)) ^ K :=
          pow_le_pow_left₀ (by positivity) ht_exp K
      _ = Real.exp ((K : ℝ) * R + (K : ℝ) * |z.im|) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
  have hquad : (K : ℝ) * |z.im| - (a / 4) * z.im ^ 2 ≤ (K : ℝ) ^ 2 / a := by
    rw [le_div_iff₀ ha, ← sq_abs z.im]
    have hid : (K : ℝ) ^ 2 - ((K : ℝ) * |z.im| - (a / 4) * |z.im| ^ 2) * a =
        ((a / 2) * |z.im| - (K : ℝ)) ^ 2 := by ring
    linarith [sq_nonneg ((a / 2) * |z.im| - (K : ℝ))]
  calc ‖z - (1 / 2 : ℂ)‖ ^ K *
          (Real.exp (((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2).re *
            ‖_root_.RHTower.finiteThetaAmplitude N z‖)
      ≤ Real.exp ((K : ℝ) * R + (K : ℝ) * |z.im|) *
          (Real.exp ((a / 2) * R ^ 2 - (a / 2) * z.im ^ 2) * M_amp) := by
        refine mul_le_mul hpow_le
          (mul_le_mul (Real.exp_le_exp.mpr hexp_re) hamp_le (norm_nonneg _) (Real.exp_pos _).le)
          (by positivity) (Real.exp_pos _).le
    _ = M_amp * Real.exp ((a / 2) * R ^ 2 + (K : ℝ) * R +
          ((K : ℝ) * |z.im| - (a / 4) * z.im ^ 2) - (a / 4) * z.im ^ 2) := by
        have hcomb : Real.exp ((K : ℝ) * R + (K : ℝ) * |z.im|) *
              Real.exp ((a / 2) * R ^ 2 - (a / 2) * z.im ^ 2) =
            Real.exp ((a / 2) * R ^ 2 + (K : ℝ) * R +
              ((K : ℝ) * |z.im| - (a / 4) * z.im ^ 2) - (a / 4) * z.im ^ 2) := by
          rw [← Real.exp_add]; congr 1; ring
        calc Real.exp ((K : ℝ) * R + (K : ℝ) * |z.im|) *
                (Real.exp ((a / 2) * R ^ 2 - (a / 2) * z.im ^ 2) * M_amp)
            = M_amp * (Real.exp ((K : ℝ) * R + (K : ℝ) * |z.im|) *
                Real.exp ((a / 2) * R ^ 2 - (a / 2) * z.im ^ 2)) := by ring
          _ = _ := by rw [hcomb]
    _ ≤ M_amp * Real.exp ((a / 2) * R ^ 2 + (K : ℝ) * R + (K : ℝ) ^ 2 / a -
          (a / 4) * z.im ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
          (le_trans zero_le_one (le_max_left 1 _))
    _ = B * Real.exp (-(a / 4) * z.im ^ 2) := by
        dsimp [B]; rw [mul_assoc, ← Real.exp_add]; congr 1; congr 1; ring

/-- **Exact zero-set preservation under Gaussian seam mollification.** -/
theorem gaussMollifiedThetaAmplitude_zero_iff (N : ℕ) {a : ℝ} (ha : 0 < a) (z : ℂ) :
    gaussMollifiedThetaAmplitude N a z = 0 ↔ _root_.RHTower.finiteThetaAmplitude N z = 0 := by
  rw [gaussMollifiedThetaAmplitude_eq N ha z, mul_eq_zero]
  simp [Complex.exp_ne_zero]

/-- **Infinitely many off-line zeros survive Gaussian seam mollification.** -/
theorem gaussMollifiedThetaAmplitude_offline_zeros_outside_strip_infinite (N : ℕ) {a : ℝ}
    (ha : 0 < a) (R : ℝ) :
    {z : ℂ | gaussMollifiedThetaAmplitude N a z = 0 ∧ R < |z.re - 1 / 2|}.Infinite := by
  refine (finiteThetaAmplitude_offline_zeros_outside_strip_infinite N R).mono fun z hz => ?_
  exact ⟨(gaussMollifiedThetaAmplitude_zero_iff N ha z).mpr hz.1, hz.2⟩

/-- **Failure of Laguerre–Pólya critical-line purity for Gaussian-mollified prefixes.** -/
theorem not_laguerrePolya_gaussMollified_criticalLine (N : ℕ) {a : ℝ} (ha : 0 < a) :
    ¬ HTGeometry.LaguerrePolya
      (fun z : ℂ => gaussMollifiedThetaAmplitude N a ((1 / 2 : ℂ) + I * z)) := by
  intro hLP
  obtain ⟨w, hw_mem⟩ :=
    (gaussMollifiedThetaAmplitude_offline_zeros_outside_strip_infinite N ha 0).nonempty
  set z₀ : ℂ := -I * (w - (1 / 2 : ℂ))
  have hw_eq : (1 / 2 : ℂ) + I * z₀ = w := by
    dsimp [z₀]; rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul, add_sub_cancel]
  have hz₀_zero : gaussMollifiedThetaAmplitude N a ((1 / 2 : ℂ) + I * z₀) = 0 := by
    rw [hw_eq]; exact hw_mem.1
  have h0_ne : gaussMollifiedThetaAmplitude N a ((1 / 2 : ℂ) + I * 0) ≠ 0 := by
    rw [mul_zero, add_zero]
    intro h0
    have hf0 := (gaussMollifiedThetaAmplitude_zero_iff N ha (1 / 2 : ℂ)).mp h0
    have hre := finiteThetaAmplitude_re_ge_lowWindow N (z := (1 / 2 : ℂ))
      (by norm_num) (by norm_num)
    rw [hf0, Complex.zero_re] at hre
    have hpos : (0 : ℝ) < (5026 / 16875) * Real.exp (-Real.pi) := by positivity
    linarith
  have him0 := HTGeometry.im_eq_zero_of_laguerrePolya hLP h0_ne hz₀_zero
  have hz₀_im : z₀.im = -(w.re - 1 / 2) := by
    dsimp [z₀]; simp [Complex.mul_im, Complex.sub_re]
  rw [hz₀_im] at him0
  have hre_eq : |w.re - 1 / 2| = 0 := by rw [abs_eq_zero]; linarith
  linarith [hw_mem.2]

/-- Bilateral first moment of `gaussMollifiedThetaSource N a`. -/
def gaussMollifiedThetaFirstMoment (N : ℕ) (a : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (x : ℂ) * (gaussMollifiedThetaSource N a x : ℂ) *
    Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))

/-- Exact derivative and gauge-shift formula for `gaussMollifiedThetaFirstMoment N a`. -/
theorem gaussMollifiedThetaFirstMoment_eq (N : ℕ) {a : ℝ} (ha : 0 < a) (z : ℂ) :
    gaussMollifiedThetaFirstMoment N a z =
      -(a : ℂ) * (z - (1 / 2 : ℂ)) * gaussMollifiedThetaAmplitude N a z +
        Complex.exp (((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2) *
          _root_.RHTower.finiteThetaFirstMoment N z := by
  set w : ℂ := -I * ((1 / 2 : ℂ) - z)
  have hIw : I * w = (1 / 2 : ℂ) - z := by
    dsimp [w]; rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
  have hIw_mul : ∀ c : ℂ, I * w * c = ((1 / 2 : ℂ) - z) * c := fun c => by
    rw [hIw]
  set f₀ : ℝ → ℂ := fun t =>
    (_root_.RHTower.reflectedFiniteThetaSource (N + 1) t : ℂ) *
      Complex.exp (((1 / 2 : ℂ) - z) * (t : ℂ))
  set f₁ : ℝ → ℂ := fun t =>
    (t : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) t : ℂ) *
      Complex.exp (((1 / 2 : ℂ) - z) * (t : ℂ))
  set g₀ : ℝ → ℂ := fun y =>
    (_root_.RHTower.gaussHeatKernel a y : ℂ) * Complex.exp (I * w * y)
  set g₁ : ℝ → ℂ := fun y =>
    (y : ℂ) * (_root_.RHTower.gaussHeatKernel a y : ℂ) * Complex.exp (I * w * y)
  have hf₀ : Integrable f₀ := by
    simpa only [f₀, _root_.RHTower.finiteThetaTiltSource] using
      _root_.RHTower.integrable_bilateralLaplace
        (_root_.RHTower.finiteThetaTiltSource N) ((1 / 2 : ℂ) - z)
  have hf₁ : Integrable f₁ := by
    simpa only [f₁, pow_one, _root_.RHTower.finiteThetaTiltSource] using
      (_root_.RHTower.finiteThetaTiltSource N).integrable_mul_exp ((1 / 2 : ℂ) - z) 1
  have hg₀ : Integrable g₀ := _root_.RHTower.integrable_heatKernel_mul_cexp ha w
  have hb : 0 < 1 / (2 * a) := by positivity
  -- Bound `g₀` and `g₁` uniformly by integrable Gaussians on `ℝ`.
  have hg₀_dom : ∀ y : ℝ, ‖g₀ y‖ ≤
      (2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) *
        Real.exp (a * |(1 / 2 - z.re)| ^ 2) * Real.exp (-y ^ 2 / (4 * a)) := by
    intro y
    dsimp only [g₀]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, _root_.RHTower.gaussHeatKernel,
      abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _),
      abs_of_pos (Real.exp_pos _), Complex.norm_exp]
    have hre_Iw : (I * w * (y : ℂ)).re ≤ |(1 / 2 - z.re)| * |y| := by
      rw [hIw_mul]
      have he : (((1 / 2 : ℂ) - z) * (y : ℂ)).re = (1 / 2 - z.re) * y := by simp
      rw [he]
      exact (le_abs_self _).trans (by rw [abs_mul])
    have hquad : -(y ^ 2 / (2 * a)) + |(1 / 2 - z.re)| * |y| ≤
        a * |(1 / 2 - z.re)| ^ 2 - y ^ 2 / (4 * a) := by
      have h4a : 0 < 4 * a := by positivity
      suffices h : (-(y ^ 2 / (2 * a)) + |(1 / 2 - z.re)| * |y|) * (4 * a) ≤
          (a * |(1 / 2 - z.re)| ^ 2 - y ^ 2 / (4 * a)) * (4 * a) by
        exact le_of_mul_le_mul_right h h4a
      rw [← sq_abs y]
      have hid : (a * |(1 / 2 - z.re)| ^ 2 - |y| ^ 2 / (4 * a)) * (4 * a) -
          (-(|y| ^ 2 / (2 * a)) + |(1 / 2 - z.re)| * |y|) * (4 * a) =
          (|y| - 2 * a * |(1 / 2 - z.re)|) ^ 2 := by
        field_simp [ha.ne']; ring
      linarith [sq_nonneg (|y| - 2 * a * |(1 / 2 - z.re)|)]
    calc (2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) * Real.exp (-(y ^ 2 / (2 * a))) *
            Real.exp (I * w * (y : ℂ)).re
        ≤ (2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) * Real.exp (-(y ^ 2 / (2 * a))) *
            Real.exp (|(1 / 2 - z.re)| * |y|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hre_Iw) (by positivity)
      _ = (2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) *
            Real.exp (-(y ^ 2 / (2 * a)) + |(1 / 2 - z.re)| * |y|) := by
          rw [mul_assoc, ← Real.exp_add]
      _ ≤ (2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) *
            Real.exp (a * |(1 / 2 - z.re)| ^ 2 - y ^ 2 / (4 * a)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hquad) (by positivity)
      _ = _ := by
          rw [mul_assoc ((2 * Real.pi * a) ^ (-(1 / 2 : ℝ))), ← Real.exp_add]
          congr 2; ring
  have hg₁ : Integrable g₁ := by
    let C₁ : ℝ := (2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) *
      Real.exp (a * |(1 / 2 - z.re)| ^ 2 + 2 * a)
    have hgauss8 : Integrable (fun y : ℝ => Real.exp (-(1 / (8 * a)) * y ^ 2)) :=
      integrable_exp_neg_mul_sq (by positivity)
    have hg₁_cont : Continuous g₁ := by
      dsimp [g₁]
      unfold _root_.RHTower.gaussHeatKernel
      exact (Complex.continuous_ofReal.mul
        (Complex.continuous_ofReal.comp
          (continuous_const.mul (Real.continuous_exp.comp
            (((continuous_pow 2).div_const (2 * a)).neg))))).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    refine Integrable.mono (hgauss8.const_mul C₁) hg₁_cont.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    have hg₁_eq : ‖g₁ y‖ = |y| * ‖g₀ y‖ := by
      dsimp only [g₁, g₀]; rw [ mul_assoc, norm_mul, Complex.norm_real, Real.norm_eq_abs ]
    have hy_exp : |y| ≤ Real.exp |y| := by linarith [Real.add_one_le_exp |y|]
    have hq8 : |y| - y ^ 2 / (8 * a) ≤ 2 * a := by
      have h8a : 0 < 8 * a := by positivity
      suffices h : (|y| - y ^ 2 / (8 * a)) * (8 * a) ≤ (2 * a) * (8 * a) by
        exact le_of_mul_le_mul_right h h8a
      rw [← sq_abs y]
      have hid : (2 * a) * (8 * a) - (|y| - |y| ^ 2 / (8 * a)) * (8 * a) =
          (|y| - 4 * a) ^ 2 := by field_simp [ha.ne']; ring
      linarith [sq_nonneg (|y| - 4 * a)]
    have hC₁_pos : 0 < C₁ := by dsimp [C₁]; positivity
    have hrhs_norm : ‖C₁ * Real.exp (-(1 / (8 * a)) * y ^ 2)‖ =
        C₁ * Real.exp (-(1 / (8 * a)) * y ^ 2) := by
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos hC₁_pos (Real.exp_pos _))]
    rw [hg₁_eq, hrhs_norm]
    calc |y| * ‖g₀ y‖
        ≤ Real.exp |y| * ((2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) *
            Real.exp (a * |(1 / 2 - z.re)| ^ 2) * Real.exp (-y ^ 2 / (4 * a))) :=
          mul_le_mul hy_exp (hg₀_dom y) (norm_nonneg _) (Real.exp_pos _).le
      _ = (2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) *
            Real.exp (a * |(1 / 2 - z.re)| ^ 2 + (|y| - y ^ 2 / (8 * a))) *
            Real.exp (-(1 / (8 * a)) * y ^ 2) := by
          calc Real.exp |y| * ((2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) *
                  Real.exp (a * |(1 / 2 - z.re)| ^ 2) * Real.exp (-y ^ 2 / (4 * a)))
              = (2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) *
                  (Real.exp |y| * Real.exp (a * |(1 / 2 - z.re)| ^ 2) *
                    Real.exp (-y ^ 2 / (4 * a))) := by ring
            _ = _ := by
                rw [← Real.exp_add, ← Real.exp_add, mul_assoc ((2 * Real.pi * a) ^ (-(1 / 2 : ℝ))),
                  ← Real.exp_add]
                congr 2; ring
      _ ≤ C₁ * Real.exp (-(1 / (8 * a)) * y ^ 2) := by
          dsimp [C₁]
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity))
            (Real.exp_pos _).le
  -- Evaluate `∫ y, g₁ y` via whole-line FTC on `g₀`.
  have hg₁_int : (∫ y : ℝ, g₁ y) =
      -(a : ℂ) * (z - (1 / 2 : ℂ)) *
        Complex.exp (((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2) := by
    have hderiv_g₀ : ∀ y : ℝ, HasDerivAt g₀
        ((-(1 / (a : ℂ))) * g₁ y + ((1 / 2 : ℂ) - z) * g₀ y) y := by
      intro y
      have hk : HasDerivAt (fun u : ℝ => (_root_.RHTower.gaussHeatKernel a u : ℂ))
          (((-y / a : ℝ) : ℂ) * (_root_.RHTower.gaussHeatKernel a y : ℂ)) y := by
        unfold _root_.RHTower.gaussHeatKernel
        have hr : HasDerivAt (fun u : ℝ =>
            (2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) * Real.exp (-(u ^ 2 / (2 * a))))
            ((-y / a) * ((2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) *
              Real.exp (-(y ^ 2 / (2 * a))))) y := by
          have h1 : HasDerivAt (fun u : ℝ => -(u ^ 2 / (2 * a))) (-(2 * y / (2 * a))) y :=
            ((hasDerivAt_pow 2 y).div_const (2 * a)).neg
          refine (h1.exp.const_mul ((2 * Real.pi * a) ^ (-(1 / 2 : ℝ)))).congr_deriv ?_
          field_simp [ha.ne']
        simpa only [Complex.ofReal_mul] using hr.ofReal_comp
      have he : HasDerivAt (fun u : ℝ => Complex.exp (I * w * (u : ℂ)))
          (((1 / 2 : ℂ) - z) * Complex.exp (I * w * (y : ℂ))) y := by
        have hlin : HasDerivAt (fun u : ℝ => I * w * (u : ℂ)) (I * w) y := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul (I * w)
        refine hlin.cexp.congr_deriv ?_
        rw [hIw, mul_comm]
      refine (hk.mul he).congr_deriv ?_
      dsimp only [g₀, g₁]
      push_cast; field_simp [ha.ne']
    have hexp0 : Tendsto (fun u : ℝ => Real.exp (-u ^ 2 / (4 * a))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      have h1 : Tendsto (fun u : ℝ => u ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
      have h2 : Tendsto (fun u : ℝ => -(u / (4 * a))) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (by positivity))
      exact (h2.comp h1).congr fun u => by dsimp only [Function.comp_apply]; ring
    have hg₀_tendsto_top : Tendsto g₀ atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have htend : Tendsto (fun y : ℝ =>
          (2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) *
            Real.exp (a * |(1 / 2 - z.re)| ^ 2) * Real.exp (-y ^ 2 / (4 * a))) atTop (𝓝 0) := by
        simpa only [mul_zero] using hexp0.const_mul _
      exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall hg₀_dom) htend
    have hg₀_tendsto_bot : Tendsto g₀ atBot (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have htend : Tendsto (fun y : ℝ =>
          (2 * Real.pi * a) ^ (-(1 / 2 : ℝ)) *
            Real.exp (a * |(1 / 2 - z.re)| ^ 2) * Real.exp (-y ^ 2 / (4 * a))) atBot (𝓝 0) := by
        have hcomp : Tendsto (fun y : ℝ => Real.exp (-(-y) ^ 2 / (4 * a))) atBot (𝓝 0) :=
          hexp0.comp tendsto_neg_atBot_atTop
        have h1 : Tendsto (fun y : ℝ => Real.exp (-y ^ 2 / (4 * a))) atBot (𝓝 0) :=
          hcomp.congr fun y => by rw [neg_sq]
        simpa only [mul_zero] using h1.const_mul _
      exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall hg₀_dom) htend
    have hftc := integral_of_hasDerivAt_of_tendsto hderiv_g₀
      ((hg₁.const_mul (-(1 / (a : ℂ)))).add (hg₀.const_mul ((1 / 2 : ℂ) - z)))
      hg₀_tendsto_bot hg₀_tendsto_top
    rw [integral_add (hg₁.const_mul _) (hg₀.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, sub_self] at hftc
    have ha_ne : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    set E_gauss : ℂ := Complex.exp (((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2)
    have hg₀_val : (∫ y : ℝ, g₀ y) = E_gauss := by
      have hker := _root_.RHTower.heatStripTransform_heatKernel ha w
      unfold _root_.RHTower.heatStripTransform at hker
      have hsq : -(a : ℂ) * w ^ 2 / 2 = ((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2 := by
        dsimp [w]
        have hI2 : (-I) ^ 2 = (-1 : ℂ) := by rw [neg_sq, I_sq]
        rw [mul_pow, hI2]; ring
      simpa only [g₀, E_gauss, mul_assoc, hsq] using hker
    rw [hg₀_val] at hftc
    have hlin : (∫ y : ℝ, g₁ y) = (a : ℂ) * (((1 / 2 : ℂ) - z) * E_gauss) := by
      have ha_inv : (a : ℂ) * (-(1 / (a : ℂ))) = -1 := by field_simp [ha_ne]
      linear_combination -(a : ℂ) * hftc + (∫ y : ℝ, g₁ y) * ha_inv
    rw [hlin]; ring
  -- Split `(x : ℂ) = (t : ℂ) + ((x - t : ℝ) : ℂ)` inside the convolution.
  have hconv_pt : ∀ x : ℝ,
      (x : ℂ) * (gaussMollifiedThetaSource N a x : ℂ) *
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) =
        (f₁ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g₀) x +
          (f₀ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g₁) x := by
    intro x
    have hsrc_int : Integrable (_root_.RHTower.reflectedFiniteThetaSource (N + 1)) :=
      integrable_reflectedFiniteThetaSource N
    have hker_int : Integrable (fun t : ℝ =>
        _root_.RHTower.reflectedFiniteThetaSource (N + 1) t *
          _root_.RHTower.gaussHeatKernel a (x - t)) := by
      have haesm : AEStronglyMeasurable (fun t : ℝ => _root_.RHTower.gaussHeatKernel a (x - t)) := by
        unfold _root_.RHTower.gaussHeatKernel
        exact (continuous_const.mul (Real.continuous_exp.comp
          (((continuous_const.sub continuous_id).pow 2).div_const (2 * a)).neg)).aestronglyMeasurable
      have h := Integrable.bdd_mul hsrc_int haesm
        (Eventually.of_forall fun t => by
          rw [Real.norm_eq_abs, _root_.RHTower.gaussHeatKernel, abs_mul,
            abs_of_pos (Real.rpow_pos_of_pos (by positivity) _), abs_of_pos (Real.exp_pos _)]
          exact mul_le_of_le_one_right (by positivity)
            (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))))
      exact h.congr (Eventually.of_forall fun t => mul_comm _ _)
    have hc1 : Integrable (fun t : ℝ => f₁ t * g₀ (x - t)) := by
      have hexp_eq : ∀ t : ℝ, f₁ t * g₀ (x - t) =
          (t : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) t : ℂ) *
            (_root_.RHTower.gaussHeatKernel a (x - t) : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) := by
        intro t
        simp only [f₁, g₀]
        have he : Complex.exp (((1 / 2 : ℂ) - z) * (t : ℂ)) *
              Complex.exp (I * w * ((x - t : ℝ) : ℂ)) =
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) := by
          rw [hIw_mul, ← Complex.exp_add]; congr 1; push_cast; ring
        calc (t : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) t : ℂ) *
                Complex.exp (((1 / 2 : ℂ) - z) * (t : ℂ)) *
                ((_root_.RHTower.gaussHeatKernel a (x - t) : ℂ) *
                  Complex.exp (I * w * ((x - t : ℝ) : ℂ)))
            = (t : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) t : ℂ) *
                (_root_.RHTower.gaussHeatKernel a (x - t) : ℂ) *
                (Complex.exp (((1 / 2 : ℂ) - z) * (t : ℂ)) *
                  Complex.exp (I * w * ((x - t : ℝ) : ℂ))) := by ring
          _ = _ := by rw [he]
      have hsrc1 : Integrable (fun t : ℝ =>
          (t : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) t : ℂ)) :=
        integrable_id_mul_reflectedFiniteThetaSource N
      have haesm1 : AEStronglyMeasurable
          (fun t : ℝ => (_root_.RHTower.gaussHeatKernel a (x - t) : ℂ)) := by
        unfold _root_.RHTower.gaussHeatKernel
        exact (Complex.continuous_ofReal.comp
          (continuous_const.mul (Real.continuous_exp.comp
            (((continuous_const.sub continuous_id).pow 2).div_const (2 * a)).neg))).aestronglyMeasurable
      have hbdd : Integrable (fun t : ℝ =>
          (_root_.RHTower.gaussHeatKernel a (x - t) : ℂ) *
            ((t : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) t : ℂ))) :=
        Integrable.bdd_mul hsrc1 haesm1
          (Eventually.of_forall fun t => by
            rw [Complex.norm_real, Real.norm_eq_abs, _root_.RHTower.gaussHeatKernel,
              abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _),
              abs_of_pos (Real.exp_pos _)]
            exact mul_le_of_le_one_right (by positivity)
              (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))))
      refine (hbdd.mul_const (Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))).congr
        (Eventually.of_forall fun t => ?_)
      dsimp only
      rw [hexp_eq t]; ring
    have hc2 : Integrable (fun t : ℝ => f₀ t * g₁ (x - t)) := by
      have hdiff_eq : ∀ t : ℝ, f₀ t * g₁ (x - t) =
          (x : ℂ) * (((_root_.RHTower.reflectedFiniteThetaSource (N + 1) t *
              _root_.RHTower.gaussHeatKernel a (x - t) : ℝ) : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) -
            f₁ t * g₀ (x - t) := by
        intro t
        simp only [f₀, f₁, g₀, g₁]
        have he : Complex.exp (((1 / 2 : ℂ) - z) * (t : ℂ)) *
              Complex.exp (I * w * ((x - t : ℝ) : ℂ)) =
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) := by
          rw [hIw_mul, ← Complex.exp_add]; congr 1; push_cast; ring
        calc (_root_.RHTower.reflectedFiniteThetaSource (N + 1) t : ℂ) *
                Complex.exp (((1 / 2 : ℂ) - z) * (t : ℂ)) *
                (((x - t : ℝ) : ℂ) * (_root_.RHTower.gaussHeatKernel a (x - t) : ℂ) *
                  Complex.exp (I * w * ((x - t : ℝ) : ℂ)))
            = ((x - t : ℝ) : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) t : ℂ) *
                (_root_.RHTower.gaussHeatKernel a (x - t) : ℂ) *
                (Complex.exp (((1 / 2 : ℂ) - z) * (t : ℂ)) *
                  Complex.exp (I * w * ((x - t : ℝ) : ℂ))) := by ring
          _ = (x : ℂ) * (((_root_.RHTower.reflectedFiniteThetaSource (N + 1) t *
                _root_.RHTower.gaussHeatKernel a (x - t) : ℝ) : ℂ) *
                Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) -
              (t : ℂ) * (_root_.RHTower.reflectedFiniteThetaSource (N + 1) t : ℂ) *
                (_root_.RHTower.gaussHeatKernel a (x - t) : ℂ) *
                (Complex.exp (((1 / 2 : ℂ) - z) * (t : ℂ)) *
                  Complex.exp (I * w * ((x - t : ℝ) : ℂ))) := by
            rw [he]; push_cast; ring
          _ = _ := by ring
      have htot : Integrable (fun t : ℝ =>
          (x : ℂ) * (((_root_.RHTower.reflectedFiniteThetaSource (N + 1) t *
              _root_.RHTower.gaussHeatKernel a (x - t) : ℝ) : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))) :=
        ((Complex.ofRealCLM.integrable_comp hker_int).mul_const _).const_mul (x : ℂ)
      exact (htot.sub hc1).congr (Eventually.of_forall fun t => (hdiff_eq t).symm)
    rw [convolution_def, convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    rw [← integral_add hc1 hc2, gaussMollifiedThetaSource, _root_.RHTower.heatSmooth,
      ← integral_complex_ofReal, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_mul_const]
    congr 1; funext t
    simp only [f₀, f₁, g₀, g₁]
    have he : Complex.exp (((1 / 2 : ℂ) - z) * (t : ℂ)) *
          Complex.exp (I * w * ((x - t : ℝ) : ℂ)) =
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) := by
      rw [hIw_mul, ← Complex.exp_add]; congr 1; push_cast; ring
    rw [Complex.ofReal_mul]
    calc (x : ℂ) * ((_root_.RHTower.reflectedFiniteThetaSource (N + 1) t : ℂ) *
            (_root_.RHTower.gaussHeatKernel a (x - t) : ℂ)) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))
        = ((t : ℂ) + ((x - t : ℝ) : ℂ)) *
            (_root_.RHTower.reflectedFiniteThetaSource (N + 1) t : ℂ) *
            (_root_.RHTower.gaussHeatKernel a (x - t) : ℂ) *
            (Complex.exp (((1 / 2 : ℂ) - z) * (t : ℂ)) *
              Complex.exp (I * w * ((x - t : ℝ) : ℂ))) := by
          rw [he]; push_cast; ring
      _ = _ := by ring
  unfold gaussMollifiedThetaFirstMoment
  simp_rw [hconv_pt]
  have hint_conv1 := hf₁.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg₀
  have hint_conv2 := hf₀.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg₁
  rw [integral_add hint_conv1 hint_conv2,
    integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hf₁ hg₀,
    integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hf₀ hg₁,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.mul_apply', hg₁_int]
  have hg₀_val : (∫ y : ℝ, g₀ y) =
      Complex.exp (((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2) := by
    have hker := _root_.RHTower.heatStripTransform_heatKernel ha w
    unfold _root_.RHTower.heatStripTransform at hker
    have hsq : -(a : ℂ) * w ^ 2 / 2 = ((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2 := by
      dsimp [w]
      have hI2 : (-I) ^ 2 = (-1 : ℂ) := by rw [neg_sq, I_sq]
      rw [mul_pow, hI2]; ring
    simpa only [g₀, mul_assoc, hsq] using hker
  rw [hg₀_val, gaussMollifiedThetaAmplitude_eq N ha z]
  change _root_.RHTower.finiteThetaFirstMoment N z *
      Complex.exp (((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2) +
    _root_.RHTower.finiteThetaAmplitude N z *
      (-(a : ℂ) * (z - (1 / 2 : ℂ)) *
        Complex.exp (((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2)) = _
  ring

/-- Window contour power sums of the Gaussian-mollified prefix `(N, a)`. -/
def gaussMollifiedWindowPowerSum (T : ℝ) (n N : ℕ) (a : ℝ) (r : ℕ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    _root_.RHTower.rectIntegral
      (fun z => z ^ r *
        (-gaussMollifiedThetaFirstMoment N a z / gaussMollifiedThetaAmplitude N a z))
      (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)

/-- Window degree of the Gaussian-mollified prefix `(N, a)`. -/
def gaussMollifiedWindowDegree (T : ℝ) (n N : ℕ) (a : ℝ) : ℕ :=
  Nat.floor ((gaussMollifiedWindowPowerSum T n N a 0).re + 1 / 2)

/-- Newton–Girard pair-difference polynomial of the Gaussian-mollified prefix `(N, a)`. -/
def gaussMollifiedDifferencePoly (T : ℝ) (n N : ℕ) (a : ℝ) : Polynomial ℂ :=
  pairDiffPoly (gaussMollifiedWindowDegree T n N a) (gaussMollifiedWindowPowerSum T n N a)

/-- Base circle loop of the Gaussian-mollified prefix `(N, a)`. -/
def gaussMollifiedBaseLoop (T : ℝ) (n N : ℕ) (a : ℝ) : C(HTGeometry.UnitCircle, ℂ) where
  toFun u := (gaussMollifiedDifferencePoly T n N a).eval (zhukovskyLoop n u)
  continuous_toFun :=
    (gaussMollifiedDifferencePoly T n N a).continuous.comp (zhukovskyLoop n).continuous

/-- Squared Zhukovsky Laurent loop of the Gaussian-mollified prefix `(N, a)`. -/
def gaussMollifiedLaurentLoop (T : ℝ) (n N : ℕ) (a : ℝ) : C(HTGeometry.UnitCircle, ℂ) :=
  gaussMollifiedBaseLoop T n N a ^ 2

/-- Unimodular circle symbol of the Gaussian-mollified prefix `(N, a)`. -/
def gaussMollifiedCollisionSymbol (T : ℝ) (n N : ℕ) (a : ℝ) : C(HTGeometry.UnitCircle, ℂ) :=
  unitNormalizeSymbol (gaussMollifiedLaurentLoop T n N a)

/-- Wiener–Hopf collision operator on `L²(ℝ)` attached to the Gaussian-mollified prefix `(N, a)`. -/
def gaussMollifiedCollisionOperator (T : ℝ) (n N : ℕ) (a : ℝ) :
    HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real :=
  HTGeometry.wienerHopfLift (gaussMollifiedCollisionSymbol T n N a)

private lemma exists_boundaryPath_of_edge {z₁ z₂ z : ℂ}
    (hre : z₁.re ≤ z₂.re) (him : z₁.im ≤ z₂.im)
    (hx : z₁.re ≤ z.re ∧ z.re ≤ z₂.re) (hy : z₁.im ≤ z.im ∧ z.im ≤ z₂.im)
    (hedge : z.re = z₁.re ∨ z.re = z₂.re ∨ z.im = z₁.im ∨ z.im = z₂.im) :
    ∃ t : ℝ, _root_.RHTower.rectangleBoundaryPath z₁ z₂ t = z := by
  by_cases hy1 : z.im = z₁.im
  · rcases eq_or_lt_of_le hre with hxeq | hxlt
    · refine ⟨0, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_zero, _root_.RHTower.rectangleEdgePath_zero]
      exact Complex.ext (by linarith [hx.1, hx.2]) hy1.symm
    · set τ : ℝ := (z.re - z₁.re) / (4 * (z₂.re - z₁.re))
      have hdx : 0 < z₂.re - z₁.re := sub_pos.mpr hxlt
      have hτ0 : 0 ≤ τ := div_nonneg (sub_nonneg.mpr hx.1) (by positivity)
      have hτ4 : τ ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith [hx.2]
      refine ⟨τ, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨hτ0, by linarith⟩,
        _root_.RHTower.rectangleEdgePath, if_pos hτ4]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero]
        dsimp [τ]; field_simp [hdx.ne']; ring
      · simp [hy1]
  · have hy1_lt : z₁.im < z.im := lt_of_le_of_ne hy.1 (Ne.symm hy1)
    have him_lt : z₁.im < z₂.im := hy1_lt.trans_le hy.2
    have hdy : 0 < z₂.im - z₁.im := sub_pos.mpr him_lt
    by_cases hx2 : z.re = z₂.re
    · set τ : ℝ := 1 / 4 + (z.im - z₁.im) / (4 * (z₂.im - z₁.im))
      have hτ_gt : 1 / 4 < τ := by
        dsimp [τ]
        linarith [div_pos (sub_pos.mpr hy1_lt) (by positivity : 0 < 4 * (z₂.im - z₁.im))]
      have hτ_le : τ ≤ 1 / 2 := by
        dsimp [τ]
        have h1 : (z.im - z₁.im) / (4 * (z₂.im - z₁.im)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith [hy.2]
        linarith
      refine ⟨τ, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath,
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
        _root_.RHTower.rectangleEdgePath, if_neg (not_le.mpr hτ_gt), if_pos hτ_le]
      apply Complex.ext
      · simp [hx2]
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.ofReal_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
        dsimp [τ]; field_simp [hdy.ne']; ring
    · by_cases hy2 : z.im = z₂.im
      · rcases eq_or_lt_of_le hre with hxeq | hxlt
        · exact absurd (by linarith [hx.1, hx.2, hxeq] : z.re = z₂.re) hx2
        · have hdx : 0 < z₂.re - z₁.re := sub_pos.mpr hxlt
          have hx2_lt : z.re < z₂.re := lt_of_le_of_ne hx.2 hx2
          set τ : ℝ := 1 / 2 + (z₂.re - z.re) / (4 * (z₂.re - z₁.re))
          have hτ_gt : 1 / 2 < τ := by
            dsimp [τ]
            linarith [div_pos (sub_pos.mpr hx2_lt) (by positivity : 0 < 4 * (z₂.re - z₁.re))]
          have hτ_le : τ ≤ 3 / 4 := by
            dsimp [τ]
            have h1 : (z₂.re - z.re) / (4 * (z₂.re - z₁.re)) ≤ 1 / 4 := by
              rw [div_le_div_iff₀ (by positivity) (by norm_num)]
              linarith [hx.1]
            linarith
          refine ⟨τ, ?_⟩
          rw [_root_.RHTower.rectangleBoundaryPath,
            Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
            _root_.RHTower.rectangleEdgePath, if_neg (by linarith), if_neg (not_le.mpr hτ_gt),
            if_pos hτ_le]
          apply Complex.ext
          · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
              Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, add_zero]
            dsimp [τ]
            have h4 : 4 * (z₂.re - z₁.re) ≠ 0 := by positivity
            calc z₂.re - (4 * (1 / 2 + (z₂.re - z.re) / (4 * (z₂.re - z₁.re))) - 2) *
                    (z₂.re - z₁.re)
                = z₂.re - (4 * (z₂.re - z₁.re)) *
                    ((z₂.re - z.re) / (4 * (z₂.re - z₁.re))) := by ring
              _ = z₂.re - (z₂.re - z.re) := by rw [mul_div_cancel₀ _ h4]
              _ = z.re := by ring
          · simp [hy2]
      · have hx1 : z.re = z₁.re := by
          rcases hedge with h | h | h | h
          · exact h
          · exact absurd h hx2
          · exact absurd h hy1
          · exact absurd h hy2
        have hy2_lt : z.im < z₂.im := lt_of_le_of_ne hy.2 hy2
        set τ : ℝ := 3 / 4 + (z₂.im - z.im) / (4 * (z₂.im - z₁.im))
        have hτ_gt : 3 / 4 < τ := by
          dsimp [τ]
          linarith [div_pos (sub_pos.mpr hy2_lt) (by positivity : 0 < 4 * (z₂.im - z₁.im))]
        have hτ_lt1 : τ < 1 := by
          dsimp [τ]
          have h1 : (z₂.im - z.im) / (4 * (z₂.im - z₁.im)) < 1 / 4 := by
            rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
            linarith [hy1_lt]
          linarith
        refine ⟨τ, ?_⟩
        rw [_root_.RHTower.rectangleBoundaryPath,
          Int.fract_eq_self.mpr ⟨by linarith, hτ_lt1⟩,
          _root_.RHTower.rectangleEdgePath, if_neg (by linarith), if_neg (by linarith),
          if_neg (not_le.mpr hτ_gt)]
        apply Complex.ext
        · simp [hx1]
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
            Complex.ofReal_re, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
          dsimp [τ]
          have h4 : 4 * (z₂.im - z₁.im) ≠ 0 := by positivity
          calc z₂.im - (4 * (3 / 4 + (z₂.im - z.im) / (4 * (z₂.im - z₁.im))) - 3) *
                  (z₂.im - z₁.im)
              = z₂.im - (4 * (z₂.im - z₁.im)) *
                  ((z₂.im - z.im) / (4 * (z₂.im - z₁.im))) := by ring
            _ = z₂.im - (z₂.im - z.im) := by rw [mul_div_cancel₀ _ h4]
            _ = z.im := by ring

/-- **Exact gauge invariance of all window contour power sums, degrees, difference polynomials,
Zhukovsky loops, and Wiener–Hopf collision operators under `x`-space Gaussian mollification.** -/
theorem gaussMollifiedWindowPowerSum_eq (T : ℝ) (n N : ℕ) {a : ℝ} (ha : 0 < a)
    (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0)
    (r : ℕ) :
    gaussMollifiedWindowPowerSum T n N a r = integerThetaWindowPowerSum T n N r := by
  set z₁ := thetaWindowLowerLeft n
  set z₂ := thetaWindowUpperRight T n
  have hre_le : z₁.re ≤ z₂.re := thetaWindow_re_le T n
  have him_le : z₁.im ≤ z₂.im := thetaWindow_im_le T n
  set g₀ : ℂ → ℂ := fun z =>
    z ^ r * (-_root_.RHTower.finiteThetaFirstMoment N z / _root_.RHTower.finiteThetaAmplitude N z)
  set g_gauge : ℂ → ℂ := fun z => z ^ r * ((a : ℂ) * (z - (1 / 2 : ℂ)))
  set g_moll : ℂ → ℂ := fun z =>
    z ^ r * (-gaussMollifiedThetaFirstMoment N a z / gaussMollifiedThetaAmplitude N a z)
  have hedge_nz : ∀ z : ℂ,
      (z₁.re ≤ z.re ∧ z.re ≤ z₂.re) → (z₁.im ≤ z.im ∧ z.im ≤ z₂.im) →
      (z.re = z₁.re ∨ z.re = z₂.re ∨ z.im = z₁.im ∨ z.im = z₂.im) →
      _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := by
    intro z hx hy hedge
    obtain ⟨t, rfl⟩ := exists_boundaryPath_of_edge hre_le him_le hx hy hedge
    exact hbdry t
  have hpt_eq : ∀ z : ℂ, _root_.RHTower.finiteThetaAmplitude N z ≠ 0 →
      g_moll z = g₀ z + g_gauge z := by
    intro z hnz
    dsimp only [g_moll, g₀, g_gauge]
    rw [gaussMollifiedThetaFirstMoment_eq N ha z, gaussMollifiedThetaAmplitude_eq N ha z]
    have hexp_ne : Complex.exp (((a : ℂ) / 2) * (z - (1 / 2 : ℂ)) ^ 2) ≠ 0 :=
      Complex.exp_ne_zero _
    field_simp [hnz, hexp_ne]
    ring
  have hcont_mom : Continuous (fun z : ℂ => -_root_.RHTower.finiteThetaFirstMoment N z) := by
    have h : (fun z : ℂ => -_root_.RHTower.finiteThetaFirstMoment N z) =
        deriv (_root_.RHTower.finiteThetaAmplitude N) :=
      funext fun z => (_root_.RHTower.deriv_finiteThetaAmplitude N z).symm
    rw [h]
    exact continuous_iff_continuousAt.mpr fun z =>
      (((_root_.RHTower.differentiable_finiteThetaAmplitude N).differentiableOn.analyticOnNhd
        isOpen_univ) z (Set.mem_univ z)).deriv.continuousAt
  have hcont_amp : Continuous (_root_.RHTower.finiteThetaAmplitude N) :=
    (_root_.RHTower.differentiable_finiteThetaAmplitude N).continuous
  have hcont_gauge : Continuous g_gauge := by
    dsimp [g_gauge]
    exact (continuous_pow r).mul (continuous_const.mul (continuous_id.sub continuous_const))
  have hg₀_bot : ContinuousOn (fun x : ℝ => g₀ ((x : ℂ) + z₁.im * I)) (uIcc z₁.re z₂.re) := by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.div
      (hcont_mom.comp (by fun_prop)).continuousOn
      (hcont_amp.comp (by fun_prop)).continuousOn fun x hx => ?_)
    rw [uIcc_of_le hre_le] at hx
    exact hedge_nz _ ⟨by simpa using hx.1, by simpa using hx.2⟩
      ⟨by simp, by simpa using him_le⟩ (Or.inr (Or.inr (Or.inl (by simp))))
  have hg₀_top : ContinuousOn (fun x : ℝ => g₀ ((x : ℂ) + z₂.im * I)) (uIcc z₁.re z₂.re) := by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.div
      (hcont_mom.comp (by fun_prop)).continuousOn
      (hcont_amp.comp (by fun_prop)).continuousOn fun x hx => ?_)
    rw [uIcc_of_le hre_le] at hx
    exact hedge_nz _ ⟨by simpa using hx.1, by simpa using hx.2⟩
      ⟨by simpa using him_le, by simp⟩ (Or.inr (Or.inr (Or.inr (by simp))))
  have hg₀_right : ContinuousOn (fun y : ℝ => g₀ ((z₂.re : ℂ) + (y : ℂ) * I)) (uIcc z₁.im z₂.im) := by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.div
      (hcont_mom.comp (by fun_prop)).continuousOn
      (hcont_amp.comp (by fun_prop)).continuousOn fun y hy => ?_)
    rw [uIcc_of_le him_le] at hy
    exact hedge_nz _ ⟨by simpa using hre_le, by simp⟩
      ⟨by simpa using hy.1, by simpa using hy.2⟩ (Or.inr (Or.inl (by simp)))
  have hg₀_left : ContinuousOn (fun y : ℝ => g₀ ((z₁.re : ℂ) + (y : ℂ) * I)) (uIcc z₁.im z₂.im) := by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.div
      (hcont_mom.comp (by fun_prop)).continuousOn
      (hcont_amp.comp (by fun_prop)).continuousOn fun y hy => ?_)
    rw [uIcc_of_le him_le] at hy
    exact hedge_nz _ ⟨by simp, by simpa using hre_le⟩
      ⟨by simpa using hy.1, by simpa using hy.2⟩ (Or.inl (by simp))
  have hrect_eq : _root_.RHTower.rectIntegral g_moll z₁ z₂ =
      _root_.RHTower.rectIntegral (fun z => g₀ z + g_gauge z) z₁ z₂ := by
    unfold _root_.RHTower.rectIntegral
    have he1 : ∫ x in z₁.re..z₂.re, g_moll ((x : ℂ) + z₁.im * I) =
        ∫ x in z₁.re..z₂.re, (g₀ ((x : ℂ) + z₁.im * I) + g_gauge ((x : ℂ) + z₁.im * I)) := by
      refine intervalIntegral.integral_congr fun x hx => hpt_eq _ ?_
      rw [uIcc_of_le hre_le] at hx
      exact hedge_nz _ ⟨by simpa using hx.1, by simpa using hx.2⟩
        ⟨by simp, by simpa using him_le⟩ (Or.inr (Or.inr (Or.inl (by simp))))
    have he2 : ∫ x in z₁.re..z₂.re, g_moll ((x : ℂ) + z₂.im * I) =
        ∫ x in z₁.re..z₂.re, (g₀ ((x : ℂ) + z₂.im * I) + g_gauge ((x : ℂ) + z₂.im * I)) := by
      refine intervalIntegral.integral_congr fun x hx => hpt_eq _ ?_
      rw [uIcc_of_le hre_le] at hx
      exact hedge_nz _ ⟨by simpa using hx.1, by simpa using hx.2⟩
        ⟨by simpa using him_le, by simp⟩ (Or.inr (Or.inr (Or.inr (by simp))))
    have he3 : ∫ y in z₁.im..z₂.im, g_moll ((z₂.re : ℂ) + (y : ℂ) * I) =
        ∫ y in z₁.im..z₂.im,
          (g₀ ((z₂.re : ℂ) + (y : ℂ) * I) + g_gauge ((z₂.re : ℂ) + (y : ℂ) * I)) := by
      refine intervalIntegral.integral_congr fun y hy => hpt_eq _ ?_
      rw [uIcc_of_le him_le] at hy
      exact hedge_nz _ ⟨by simpa using hre_le, by simp⟩
        ⟨by simpa using hy.1, by simpa using hy.2⟩ (Or.inr (Or.inl (by simp)))
    have he4 : ∫ y in z₁.im..z₂.im, g_moll ((z₁.re : ℂ) + (y : ℂ) * I) =
        ∫ y in z₁.im..z₂.im,
          (g₀ ((z₁.re : ℂ) + (y : ℂ) * I) + g_gauge ((z₁.re : ℂ) + (y : ℂ) * I)) := by
      refine intervalIntegral.integral_congr fun y hy => hpt_eq _ ?_
      rw [uIcc_of_le him_le] at hy
      exact hedge_nz _ ⟨by simp, by simpa using hre_le⟩
        ⟨by simpa using hy.1, by simpa using hy.2⟩ (Or.inl (by simp))
    rw [he1, he2, he3, he4]
  have hgauge_zero : _root_.RHTower.rectIntegral g_gauge z₁ z₂ = 0 := by
    refine _root_.RHTower.rectIntegral_eq_zero_of_analyticOnNhd (Set.subset_univ _) ?_
    have hdiff : Differentiable ℂ g_gauge := by
      dsimp [g_gauge]
      exact (differentiable_id.pow r).mul (differentiable_const _ |>.mul
        (differentiable_id.sub_const _))
    exact hdiff.differentiableOn.analyticOnNhd isOpen_univ
  unfold gaussMollifiedWindowPowerSum integerThetaWindowPowerSum
  change (2 * Real.pi * I)⁻¹ * _root_.RHTower.rectIntegral g_moll z₁ z₂ =
    (2 * Real.pi * I)⁻¹ * _root_.RHTower.rectIntegral g₀ z₁ z₂
  rw [hrect_eq, _root_.RHTower.rectIntegral_add
    hg₀_bot.intervalIntegrable ((hcont_gauge.comp (by fun_prop)).intervalIntegrable _ _)
    hg₀_top.intervalIntegrable ((hcont_gauge.comp (by fun_prop)).intervalIntegrable _ _)
    hg₀_right.intervalIntegrable ((hcont_gauge.comp (by fun_prop)).intervalIntegrable _ _)
    hg₀_left.intervalIntegrable ((hcont_gauge.comp (by fun_prop)).intervalIntegrable _ _),
    hgauge_zero, add_zero]

/-- **Complete collision-operator gauge invariance under `x`-space Gaussian mollification.**
Whenever `finiteThetaAmplitude N` avoids `∂R_{T,n}`, Gaussian seam mollification leaves the window
degree, Newton difference polynomial, Zhukovsky Laurent loop, and Wiener–Hopf operator identically
invariant. -/
theorem gaussMollifiedCollisionOperator_eq (T : ℝ) (n N : ℕ) {a : ℝ} (ha : 0 < a)
    (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0) :
    gaussMollifiedWindowDegree T n N a = integerThetaWindowDegree T n N ∧
    gaussMollifiedDifferencePoly T n N a = integerThetaDifferencePoly T n N ∧
    gaussMollifiedLaurentLoop T n N a = integerThetaLaurentLoop T n N ∧
    gaussMollifiedCollisionOperator T n N a = integerThetaCollisionOperator T n N := by
  have hps : gaussMollifiedWindowPowerSum T n N a = integerThetaWindowPowerSum T n N :=
    funext (gaussMollifiedWindowPowerSum_eq T n N ha hbdry)
  have hdeg : gaussMollifiedWindowDegree T n N a = integerThetaWindowDegree T n N := by
    unfold gaussMollifiedWindowDegree integerThetaWindowDegree
    rw [hps]
  have hpoly : gaussMollifiedDifferencePoly T n N a = integerThetaDifferencePoly T n N := by
    unfold gaussMollifiedDifferencePoly integerThetaDifferencePoly
    rw [hdeg, hps]
  have hbase : gaussMollifiedBaseLoop T n N a = integerThetaBaseLoop T n N := by
    ext u
    change (gaussMollifiedDifferencePoly T n N a).eval (zhukovskyLoop n u) =
      (integerThetaDifferencePoly T n N).eval (zhukovskyLoop n u)
    rw [hpoly]
  have hloop : gaussMollifiedLaurentLoop T n N a = integerThetaLaurentLoop T n N := by
    unfold gaussMollifiedLaurentLoop integerThetaLaurentLoop
    rw [hbase]
  have hop : gaussMollifiedCollisionOperator T n N a = integerThetaCollisionOperator T n N := by
    unfold gaussMollifiedCollisionOperator integerThetaCollisionOperator
      gaussMollifiedCollisionSymbol integerThetaCollisionSymbol
    rw [hloop]
  exact ⟨hdeg, hpoly, hloop, hop⟩

/-! ## §3 Non-multiplicative `C^∞`-even Gaussian-partitioned Poisson–Jacobi prefixes -/

/-- `C^∞` error-function partition switch `1 / 2 + √(κ / π) ∫_0^x e^{-κ u²} du`. -/
def gaussianPartitionSwitch (κ x : ℝ) : ℝ :=
  1 / 2 + Real.sqrt (κ / Real.pi) * ∫ u in (0 : ℝ)..x, Real.exp (-κ * u ^ 2)

/-- Exact partition-of-unity law across `x ↔ -x`. -/
theorem gaussianPartitionSwitch_add_neg (κ x : ℝ) :
    gaussianPartitionSwitch κ x + gaussianPartitionSwitch κ (-x) = 1 := by
  unfold gaussianPartitionSwitch
  have hneg : (∫ u in (0 : ℝ)..(-x), Real.exp (-κ * u ^ 2)) =
      -(∫ u in (0 : ℝ)..x, Real.exp (-κ * u ^ 2)) := by
    have hcomp := intervalIntegral.integral_comp_neg (f := fun u => Real.exp (-κ * u ^ 2))
      (a := 0) (b := x)
    simp only [neg_zero, neg_sq] at hcomp
    rw [intervalIntegral.integral_symm (-x) 0, ← hcomp]
  rw [hneg]
  ring

/-- Complementary Gaussian tail identity for `gaussianPartitionSwitch κ (-x)` on `x ≥ 0`. -/
private lemma gaussianPartitionSwitch_neg_eq_Ioi {κ : ℝ} (hκ : 0 < κ) {x : ℝ} (hx : 0 ≤ x) :
    gaussianPartitionSwitch κ (-x) =
      Real.sqrt (κ / Real.pi) * ∫ u in Ioi x, Real.exp (-κ * u ^ 2) := by
  have hint : Integrable (fun u : ℝ => Real.exp (-κ * u ^ 2)) := integrable_exp_neg_mul_sq hκ
  have hsplit : (∫ u in Ioi (0 : ℝ), Real.exp (-κ * u ^ 2)) =
      (∫ u in Ioc 0 x, Real.exp (-κ * u ^ 2)) + ∫ u in Ioi x, Real.exp (-κ * u ^ 2) := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hint.integrableOn hint.integrableOn, Ioc_union_Ioi_eq_Ioi hx]
  have hhalf : Real.sqrt (κ / Real.pi) * (∫ u in Ioi (0 : ℝ), Real.exp (-κ * u ^ 2)) = 1 / 2 := by
    rw [HTGeometry.integral_Ioi_gaussian hκ]
    have hmul : Real.sqrt (κ / Real.pi) * Real.sqrt (Real.pi / κ) = 1 := by
      rw [← Real.sqrt_mul (by positivity),
        show (κ / Real.pi) * (Real.pi / κ) = 1 by field_simp [hκ.ne', Real.pi_ne_zero],
        Real.sqrt_one]
    calc Real.sqrt (κ / Real.pi) * (Real.sqrt (Real.pi / κ) / 2)
        = (Real.sqrt (κ / Real.pi) * Real.sqrt (Real.pi / κ)) / 2 := by ring
      _ = 1 / 2 := by rw [hmul]
  have hx_eq : gaussianPartitionSwitch κ x =
      1 / 2 + Real.sqrt (κ / Real.pi) * ∫ u in Ioc 0 x, Real.exp (-κ * u ^ 2) := by
    unfold gaussianPartitionSwitch
    rw [intervalIntegral.integral_of_le hx]
  have hsum := gaussianPartitionSwitch_add_neg κ x
  linarith [hsum, hx_eq, hhalf, congrArg (Real.sqrt (κ / Real.pi) * ·) hsplit]

/-- Strict positivity and Gaussian tail bound `0 < χ_κ(-x) ≤ (1 / 2) e^{-κ x²}` for `x ≥ 0`. -/
theorem gaussianPartitionSwitch_neg_bounds {κ : ℝ} (hκ : 0 < κ) {x : ℝ} (hx : 0 ≤ x) :
    0 < gaussianPartitionSwitch κ (-x) ∧
      gaussianPartitionSwitch κ (-x) ≤ (1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) := by
  rw [gaussianPartitionSwitch_neg_eq_Ioi hκ hx]
  have hint : Integrable (fun v : ℝ => Real.exp (-κ * v ^ 2)) := integrable_exp_neg_mul_sq hκ
  have hsqrt_pos : 0 < Real.sqrt (κ / Real.pi) := Real.sqrt_pos.mpr (by positivity)
  constructor
  · have hsub : Ioc x (x + 1) ⊆ Ioi x := fun u hu => hu.1
    have hnn : ∀ u : ℝ, 0 ≤ Real.exp (-κ * u ^ 2) := fun _ => (Real.exp_pos _).le
    have hle1 : (∫ u in Ioc x (x + 1), Real.exp (-κ * u ^ 2)) ≤
        ∫ u in Ioi x, Real.exp (-κ * u ^ 2) :=
      setIntegral_mono_set hint.integrableOn (Eventually.of_forall hnn)
        (Eventually.of_forall hsub)
    have hlo : ∀ u ∈ Ioc x (x + 1),
        Real.exp (-κ * (x + 1) ^ 2) ≤ Real.exp (-κ * u ^ 2) := by
      intro u hu
      apply Real.exp_le_exp.mpr
      have hu2 : u ^ 2 ≤ (x + 1) ^ 2 := by nlinarith [hx, hu.1, hu.2]
      nlinarith
    have hmono := setIntegral_mono_on
      (integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
      hint.integrableOn measurableSet_Ioc hlo
    rw [setIntegral_const, Measure.real_def, Real.volume_Ioc, show x + 1 - x = (1 : ℝ) by ring,
      ENNReal.toReal_ofReal zero_le_one, one_smul] at hmono
    exact mul_pos hsqrt_pos (lt_of_lt_of_le (Real.exp_pos _) (hmono.trans hle1))
  · have hshift : (∫ u in Ioi x, Real.exp (-κ * u ^ 2)) =
        ∫ v in Ioi (0 : ℝ), Real.exp (-κ * (v + x) ^ 2) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
        ← MeasureTheory.integral_indicator measurableSet_Ioi,
        ← MeasureTheory.integral_add_right_eq_self
          (fun u => (Ioi x).indicator (fun w => Real.exp (-κ * w ^ 2)) u) x]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      dsimp only
      by_cases hv : 0 < v
      · have hvx : x < v + x := by linarith
        rw [Set.indicator_of_mem hvx, Set.indicator_of_mem hv]
      · have hvx : ¬ (x < v + x) := by linarith
        rw [Set.indicator_of_notMem hvx, Set.indicator_of_notMem hv]
    rw [hshift]
    have hpt : ∀ v ∈ Ioi (0 : ℝ),
        Real.exp (-κ * (v + x) ^ 2) ≤ Real.exp (-κ * x ^ 2) * Real.exp (-κ * v ^ 2) := by
      intro v hv
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hv0 : 0 < v := mem_Ioi.mp hv
      have hvx : 0 ≤ 2 * κ * v * x := by positivity
      linarith [show -κ * (v + x) ^ 2 = -κ * x ^ 2 + -κ * v ^ 2 - 2 * κ * v * x by ring, hvx]
    have hint_vx : IntegrableOn (fun v : ℝ => Real.exp (-κ * (v + x) ^ 2)) (Ioi (0 : ℝ)) := by
      refine Integrable.mono (hint.integrableOn.const_mul (Real.exp (-κ * x ^ 2)))
        (Real.continuous_exp.comp
          (continuous_const.mul ((continuous_id.add continuous_const).pow 2))).aestronglyMeasurable.restrict
        ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_pos (by positivity)]
      exact hpt v hv
    have hmono := setIntegral_mono_on hint_vx
      (hint.integrableOn.const_mul (Real.exp (-κ * x ^ 2))) measurableSet_Ioi hpt
    rw [MeasureTheory.integral_const_mul, HTGeometry.integral_Ioi_gaussian hκ] at hmono
    have hmul : Real.sqrt (κ / Real.pi) * (Real.sqrt (Real.pi / κ) / 2) = 1 / 2 := by
      have h1 : Real.sqrt (κ / Real.pi) * Real.sqrt (Real.pi / κ) = 1 := by
        rw [← Real.sqrt_mul (by positivity),
          show (κ / Real.pi) * (Real.pi / κ) = 1 by field_simp [hκ.ne', Real.pi_ne_zero],
          Real.sqrt_one]
      calc Real.sqrt (κ / Real.pi) * (Real.sqrt (Real.pi / κ) / 2)
          = (Real.sqrt (κ / Real.pi) * Real.sqrt (Real.pi / κ)) / 2 := by ring
        _ = 1 / 2 := by rw [h1]
    calc Real.sqrt (κ / Real.pi) * ∫ v in Ioi (0 : ℝ), Real.exp (-κ * (v + x) ^ 2)
        ≤ Real.sqrt (κ / Real.pi) *
            (Real.exp (-κ * x ^ 2) * (Real.sqrt (Real.pi / κ) / 2)) :=
          mul_le_mul_of_nonneg_left hmono hsqrt_pos.le
      _ = (Real.sqrt (κ / Real.pi) * (Real.sqrt (Real.pi / κ) / 2)) *
            Real.exp (-κ * x ^ 2) := by ring
      _ = (1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) := by rw [hmul]

theorem gaussianPartitionSwitch_mem_Ioo {κ : ℝ} (hκ : 0 < κ) (x : ℝ) :
    0 < gaussianPartitionSwitch κ x ∧ gaussianPartitionSwitch κ x < 1 := by
  rcases le_or_gt 0 x with hx | hx
  · have hb := (gaussianPartitionSwitch_neg_bounds hκ hx).1
    have hle := (gaussianPartitionSwitch_neg_bounds hκ hx).2.trans
      (mul_le_of_le_one_right (by norm_num) (Real.exp_le_one_iff.mpr (by nlinarith)))
    have hsum := gaussianPartitionSwitch_add_neg κ x
    exact ⟨by linarith, by linarith⟩
  · have hx' : 0 ≤ -x := by linarith
    have hb := (gaussianPartitionSwitch_neg_bounds hκ hx').1
    have hle := (gaussianPartitionSwitch_neg_bounds hκ hx').2.trans
      (mul_le_of_le_one_right (by norm_num) (Real.exp_le_one_iff.mpr (by nlinarith)))
    rw [neg_neg] at hb hle
    exact ⟨hb, by linarith⟩

private lemma hasDerivAt_gaussianPartitionSwitch (κ x : ℝ) :
    HasDerivAt (gaussianPartitionSwitch κ)
      (Real.sqrt (κ / Real.pi) * GaloisForLFunctions.gaussPolyFun 1 κ x) x := by
  unfold gaussianPartitionSwitch
  have hcont : Continuous (fun u : ℝ => Real.exp (-κ * u ^ 2)) := by fun_prop
  have hint := intervalIntegral.integral_hasStrictDerivAt_right
    (hcont.intervalIntegrable 0 x) (hcont.stronglyMeasurableAtFilter volume (𝓝 x))
    (hcont.continuousAt)
  refine ((hasDerivAt_const x (1 / 2 : ℝ)).add
    (hint.hasDerivAt.const_mul (Real.sqrt (κ / Real.pi)))).congr_deriv ?_
  unfold GaloisForLFunctions.gaussPolyFun
  rw [Polynomial.eval_one, one_mul, zero_add]
  congr 2; ring

private lemma iteratedDeriv_succ_gaussianPartitionSwitch (κ : ℝ) (j : ℕ) :
    iteratedDeriv (j + 1) (gaussianPartitionSwitch κ) =
      fun x : ℝ => Real.sqrt (κ / Real.pi) *
        GaloisForLFunctions.gaussPolyFun (iterGaussPoly κ j) κ x := by
  induction j with
  | zero =>
    rw [zero_add, iteratedDeriv_one]
    funext x
    exact (hasDerivAt_gaussianPartitionSwitch κ x).deriv
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact ((hasDerivAt_iterGaussPoly κ j x).const_mul (Real.sqrt (κ / Real.pi))).deriv

theorem contDiff_gaussianPartitionSwitch (κ : ℝ) :
    ContDiff ℝ ∞ (gaussianPartitionSwitch κ) := by
  rw [contDiff_infty]
  intro n
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _ x
  rcases m with _ | j
  · rw [iteratedDeriv_zero]
    exact (hasDerivAt_gaussianPartitionSwitch κ x).differentiableAt
  · rw [iteratedDeriv_succ_gaussianPartitionSwitch κ j]
    exact ((hasDerivAt_iterGaussPoly κ j x).const_mul _).differentiableAt

/-- **Non-multiplicative Gaussian-partitioned Poisson–Jacobi prefix source.**
Weights the genuine analytic shell prefix `thetaCuspFiniteShellPrefix (N + 1)` across `±x` via the
`C^∞` partition of unity `gaussianPartitionSwitch κ`. -/
def partitionSymThetaSource (N : ℕ) (κ x : ℝ) : ℝ :=
  gaussianPartitionSwitch κ x * _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) x +
    gaussianPartitionSwitch κ (-x) * _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) (-x)

/-- Exact evenness of `partitionSymThetaSource N κ` on `ℝ`. -/
theorem partitionSymThetaSource_even (N : ℕ) (κ x : ℝ) :
    partitionSymThetaSource N κ (-x) = partitionSymThetaSource N κ x := by
  unfold partitionSymThetaSource
  rw [neg_neg, add_comm]

/-- **`C^∞` smoothness of `partitionSymThetaSource N κ` across `ℝ` (including `x = 0`).** -/
theorem contDiff_partitionSymThetaSource (N : ℕ) (κ : ℝ) :
    ContDiff ℝ ∞ (partitionSymThetaSource N κ) := by
  unfold partitionSymThetaSource
  exact ((contDiff_gaussianPartitionSwitch κ).mul
    (contDiff_thetaCuspFiniteShellPrefix (N + 1))).add
    (((contDiff_gaussianPartitionSwitch κ).comp contDiff_neg).mul
      ((contDiff_thetaCuspFiniteShellPrefix (N + 1)).comp contDiff_neg))

/-- **All-order seam-cusp elimination for `partitionSymThetaSource N κ`:** every odd derivative at
`x = 0` vanishes identically. -/
theorem iteratedDeriv_odd_partitionSymThetaSource_zero (N : ℕ) (κ : ℝ) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (partitionSymThetaSource N κ) 0 = 0 :=
  iteratedDeriv_odd_zero_of_even_real (partitionSymThetaSource_even N κ) k

/-- Uniform boundedness of `thetaFiniteShellJet (N + 1) r (-x)` across `x ≥ 0`. -/
private lemma abs_thetaFiniteShellJet_neg_le_of_nonneg (N r : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {x : ℝ}, 0 ≤ x →
      |_root_.RHTower.thetaFiniteShellJet (N + 1) r (-x)| ≤ B := by
  set P := _root_.RHTower.thetaCuspLogDerivativePolynomial r
  let B_atom : ℕ → ℝ := fun m =>
    ∑ k ∈ P.support, |P.coeff k| * ((m + 1 : ℕ) : ℝ) ^ k
  refine ⟨∑ m ∈ Finset.range (N + 1), B_atom m,
    Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun k _ => by positivity, ?_⟩
  intro x hx
  unfold _root_.RHTower.thetaFiniteShellJet
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  unfold _root_.RHTower.thetaCuspPolynomialAtom
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  have hexp_half : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexp_gauss : Real.exp (-Real.pi * (((m + 1 : ℕ) : ℝ) * Real.exp (-x)) ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg (((m + 1 : ℕ) : ℝ) * Real.exp (-x))])
  set u := ((m + 1 : ℕ) : ℝ) * Real.exp (-x)
  have hu0 : 0 ≤ u := by positivity
  have hu_le : u ≤ ((m + 1 : ℕ) : ℝ) :=
    mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by linarith))
  have heval : |P.eval u| ≤ B_atom m := by
    refine (abs_eval_le_sum_support P u).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_of_nonneg hu0]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu0 hu_le k) (abs_nonneg _)
  calc Real.exp (-x / 2) * |P.eval u| * Real.exp (-Real.pi * u ^ 2)
      ≤ 1 * B_atom m * 1 := by
        refine mul_le_mul (mul_le_mul hexp_half heval (abs_nonneg _) zero_le_one)
          hexp_gauss (Real.exp_pos _).le (by dsimp [B_atom]; positivity)
    _ = B_atom m := by ring

/-- **All-order super-exponential decay of `partitionSymThetaSource N κ` (`κ > 0`) on `ℝ`.** -/
theorem abs_iteratedDeriv_partitionSymThetaSource_le_exp (N K : ℕ) {κ : ℝ} (hκ : 0 < κ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      |iteratedDeriv K (partitionSymThetaSource N κ) x| ≤ C * Real.exp (-M * |x|) := by
  let q : ℕ := Nat.ceil (max 0 M) + 1
  have hM_le_q : M ≤ (q : ℝ) := by
    dsimp [q]
    have h1 : M ≤ max 0 M := le_max_right 0 M
    have h2 : max 0 M ≤ (Nat.ceil (max 0 M) : ℝ) := Nat.le_ceil _
    push_cast; linarith
  -- Bound on `x ≥ 0` first via Leibniz's rule on the two smooth summands, then reflect to `ℝ`.
  let f₁ : ℝ → ℝ := fun y =>
    gaussianPartitionSwitch κ y * _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) y
  let f₂ : ℝ → ℝ := fun y =>
    gaussianPartitionSwitch κ (-y) * _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) (-y)
  have hf₁_cd : ContDiff ℝ ∞ f₁ :=
    (contDiff_gaussianPartitionSwitch κ).mul (contDiff_thetaCuspFiniteShellPrefix (N + 1))
  have hf₂_cd : ContDiff ℝ ∞ f₂ :=
    ((contDiff_gaussianPartitionSwitch κ).comp contDiff_neg).mul
      ((contDiff_thetaCuspFiniteShellPrefix (N + 1)).comp contDiff_neg)
  -- Uniform Gaussian-to-exponential conversion `e^{-(κ / 2) x²} ≤ e^{q² / (2 κ)} e^{-q x}` (`x ≥ 0`).
  have hgauss_to_exp : ∀ {x : ℝ}, 0 ≤ x →
      Real.exp (-(κ / 2) * x ^ 2) ≤
        Real.exp ((q : ℝ) ^ 2 / (2 * κ)) * Real.exp (-(q : ℝ) * x) := by
    intro x _
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hdiv : -(κ / 2) * x ^ 2 + (q : ℝ) * x ≤ (q : ℝ) ^ 2 / (2 * κ) := by
      rw [le_div_iff₀ (by positivity)]
      have hid : (q : ℝ) ^ 2 - (-(κ / 2) * x ^ 2 + (q : ℝ) * x) * (2 * κ) =
          (κ * x - (q : ℝ)) ^ 2 := by ring
      linarith [sq_nonneg (κ * x - (q : ℝ))]
    linarith
  -- Termwise bound on `|iteratedDeriv i (gaussianPartitionSwitch κ) x|` and `(-x)` for `x ≥ 0`.
  let C_sw : ℕ → ℝ := fun i =>
    match i with
    | 0 => 1
    | j + 1 => Real.sqrt (κ / Real.pi) *
        (∑ k ∈ (iterGaussPoly κ j).support,
          |(iterGaussPoly κ j).coeff k| * Real.exp ((k : ℝ) ^ 2 / (2 * κ)))
  have hC_sw_nn : ∀ i, 0 ≤ C_sw i := by
    intro i; rcases i with _ | j
    · norm_num [C_sw]
    · dsimp [C_sw]
      exact mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun _ _ => by positivity)
  let C_jet_pos : ℕ → ℝ := fun r =>
    ((N + 1 : ℕ) : ℝ) *
      _root_.RHTower.thetaCuspGaussianConstant
        (_root_.RHTower.thetaCuspWeightedPolynomial
          (_root_.RHTower.thetaCuspLogDerivativePolynomial r) (q + 1))
  let C_jet_neg : ℕ → ℝ := fun r => (abs_thetaFiniteShellJet_neg_le_of_nonneg N r).choose
  let termBound : ℕ → ℝ := fun i =>
    (Nat.choose K i : ℝ) *
      ((if i = 0 then C_jet_pos K
        else C_sw i * Real.exp ((q : ℝ) ^ 2 / (2 * κ)) * C_jet_pos (K - i)) +
       C_sw i * Real.exp ((q : ℝ) ^ 2 / (2 * κ)) * C_jet_neg (K - i))
  let C_tot : ℝ := 1 + ∑ i ∈ Finset.range (K + 1), termBound i
  have hterm_nn : ∀ i, 0 ≤ termBound i := by
    intro i
    dsimp [termBound]
    refine mul_nonneg (Nat.cast_nonneg _) (add_nonneg ?_ ?_)
    · split_ifs
      · dsimp [C_jet_pos]
        exact mul_nonneg (Nat.cast_nonneg _) (_root_.RHTower.thetaCuspGaussianConstant_nonneg _)
      · refine mul_nonneg (mul_nonneg (hC_sw_nn i) (Real.exp_pos _).le) ?_
        dsimp [C_jet_pos]
        exact mul_nonneg (Nat.cast_nonneg _) (_root_.RHTower.thetaCuspGaussianConstant_nonneg _)
    · exact mul_nonneg (mul_nonneg (hC_sw_nn i) (Real.exp_pos _).le)
        (abs_thetaFiniteShellJet_neg_le_of_nonneg N (K - i)).choose_spec.1
  have hC_pos : 0 < C_tot := by
    dsimp [C_tot]
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range (K + 1)) => hterm_nn i]
  have hpos_bound : ∀ {x : ℝ}, 0 ≤ x →
      |iteratedDeriv K (partitionSymThetaSource N κ) x| ≤
        C_tot * Real.exp (-(q : ℝ) * x) := by
    intro x hx
    have hfun_eq : partitionSymThetaSource N κ = f₁ + f₂ := rfl
    have hadd_der : iteratedDeriv K (partitionSymThetaSource N κ) x =
        iteratedDeriv K f₁ x + iteratedDeriv K f₂ x := by
      rw [hfun_eq]
      exact iteratedDeriv_add
        ((contDiff_infty.mp hf₁_cd K).contDiffAt)
        ((contDiff_infty.mp hf₂_cd K).contDiffAt)
    have hm1 : iteratedDeriv K f₁ x = ∑ i ∈ Finset.range (K + 1),
        (Nat.choose K i : ℝ) * iteratedDeriv i (gaussianPartitionSwitch κ) x *
          iteratedDeriv (K - i) (_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1)) x := by
      have hf₁_eq : f₁ = gaussianPartitionSwitch κ *
          _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) := rfl
      rw [hf₁_eq, iteratedDeriv_mul
        ((contDiff_infty.mp (contDiff_gaussianPartitionSwitch κ) K).contDiffAt)
        ((contDiff_infty.mp (contDiff_thetaCuspFiniteShellPrefix (N + 1)) K).contDiffAt)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [nsmul_eq_mul]; ring
    have hm2 : iteratedDeriv K f₂ x = ∑ i ∈ Finset.range (K + 1),
        (Nat.choose K i : ℝ) * iteratedDeriv i (fun y => gaussianPartitionSwitch κ (-y)) x *
          iteratedDeriv (K - i)
            (fun y => _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) (-y)) x := by
      let g₁ : ℝ → ℝ := fun y => gaussianPartitionSwitch κ (-y)
      let g₂ : ℝ → ℝ := fun y => _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) (-y)
      have hf₂_eq : f₂ = g₁ * g₂ := rfl
      have hg₁_cd : ContDiffAt ℝ K g₁ x :=
        (contDiff_infty.mp ((contDiff_gaussianPartitionSwitch κ).comp contDiff_neg) K).contDiffAt
      have hg₂_cd : ContDiffAt ℝ K g₂ x :=
        (contDiff_infty.mp ((contDiff_thetaCuspFiniteShellPrefix (N + 1)).comp contDiff_neg) K).contDiffAt
      rw [hf₂_eq, iteratedDeriv_mul hg₁_cd hg₂_cd]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [nsmul_eq_mul]; ring
    rw [hadd_der, hm1, hm2, ← Finset.sum_add_distrib]
    have hsum_le : |∑ i ∈ Finset.range (K + 1),
          ((Nat.choose K i : ℝ) * iteratedDeriv i (gaussianPartitionSwitch κ) x *
              iteratedDeriv (K - i) (_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1)) x +
            (Nat.choose K i : ℝ) * iteratedDeriv i (fun y => gaussianPartitionSwitch κ (-y)) x *
              iteratedDeriv (K - i)
                (fun y => _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) (-y)) x)| ≤
        ∑ i ∈ Finset.range (K + 1), termBound i * Real.exp (-(q : ℝ) * x) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      have hi_le : i ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      -- Bound first summand at `i`.
      have hp1 : |(Nat.choose K i : ℝ) * iteratedDeriv i (gaussianPartitionSwitch κ) x *
            iteratedDeriv (K - i) (_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1)) x| ≤
          (Nat.choose K i : ℝ) *
            (if i = 0 then C_jet_pos K
             else C_sw i * Real.exp ((q : ℝ) ^ 2 / (2 * κ)) * C_jet_pos (K - i)) *
            Real.exp (-(q : ℝ) * x) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
          iteratedDeriv_thetaCuspFiniteShellPrefix]
        rcases i with _ | j
        · simp only [↓reduceIte, Nat.sub_zero, iteratedDeriv_zero]
          have hsw_lt := gaussianPartitionSwitch_mem_Ioo hκ x
          have hsw_abs : |gaussianPartitionSwitch κ x| ≤ 1 :=
            abs_le.mpr ⟨by linarith [hsw_lt.1], hsw_lt.2.le⟩
          have hjet := exp_mul_abs_thetaFiniteShellJet_le N K q hx
          have hjet' : |_root_.RHTower.thetaFiniteShellJet (N + 1) K x| ≤
              C_jet_pos K * Real.exp (-(q : ℝ) * x) := by
            have hmul := mul_le_mul_of_nonneg_left hjet (Real.exp_pos (-(q : ℝ) * x)).le
            rw [← mul_assoc, ← Real.exp_add,
              show -(q : ℝ) * x + (q : ℝ) * x = 0 by ring, Real.exp_zero, one_mul] at hmul
            refine hmul.trans ?_
            have hex1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
            dsimp [C_jet_pos]
            calc Real.exp (-(q : ℝ) * x) *
                    (((N + 1 : ℕ) : ℝ) * _root_.RHTower.thetaCuspGaussianConstant _ * Real.exp (-x))
                ≤ Real.exp (-(q : ℝ) * x) *
                    (((N + 1 : ℕ) : ℝ) * _root_.RHTower.thetaCuspGaussianConstant _ * 1) := by
                  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
                  exact mul_le_mul_of_nonneg_left hex1
                    (mul_nonneg (Nat.cast_nonneg _)
                      (_root_.RHTower.thetaCuspGaussianConstant_nonneg _))
              _ = _ := by ring
          calc (Nat.choose K 0 : ℝ) * |gaussianPartitionSwitch κ x| *
                  |_root_.RHTower.thetaFiniteShellJet (N + 1) K x|
              ≤ (Nat.choose K 0 : ℝ) * 1 * (C_jet_pos K * Real.exp (-(q : ℝ) * x)) := by
                refine mul_le_mul (mul_le_mul_of_nonneg_left hsw_abs (Nat.cast_nonneg _))
                  hjet' (abs_nonneg _) (by positivity)
            _ = _ := by ring
        · simp only [Nat.succ_ne_zero, ↓reduceIte, iteratedDeriv_succ_gaussianPartitionSwitch]
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          have hsw_bd : Real.sqrt (κ / Real.pi) *
                |GaloisForLFunctions.gaussPolyFun (iterGaussPoly κ j) κ x| ≤
              C_sw (j + 1) * Real.exp ((q : ℝ) ^ 2 / (2 * κ)) * Real.exp (-(q : ℝ) * x) := by
            have h1 := mul_le_mul_of_nonneg_left
              (abs_gaussPolyFun_le_halfGauss (iterGaussPoly κ j) hκ x) (Real.sqrt_nonneg _)
            change Real.sqrt (κ / Real.pi) * _ ≤
              Real.sqrt (κ / Real.pi) * (_ * Real.exp (-(κ / 2) * x ^ 2)) at h1
            refine h1.trans ?_
            have h2 := mul_le_mul_of_nonneg_left (hgauss_to_exp hx) (hC_sw_nn (j + 1))
            simpa only [C_sw, mul_assoc] using h2
          have hjet := exp_mul_abs_thetaFiniteShellJet_le N (K - (j + 1)) q hx
          have hjet_le : |_root_.RHTower.thetaFiniteShellJet (N + 1) (K - (j + 1)) x| ≤
              C_jet_pos (K - (j + 1)) := by
            have hexp1 : 1 ≤ Real.exp ((q : ℝ) * x) := Real.one_le_exp (by positivity)
            have hex_neg : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
            calc |_root_.RHTower.thetaFiniteShellJet (N + 1) (K - (j + 1)) x|
                ≤ Real.exp ((q : ℝ) * x) *
                    |_root_.RHTower.thetaFiniteShellJet (N + 1) (K - (j + 1)) x| :=
                  le_mul_of_one_le_left (abs_nonneg _) hexp1
              _ ≤ C_jet_pos (K - (j + 1)) * Real.exp (-x) := hjet
              _ ≤ C_jet_pos (K - (j + 1)) :=
                  mul_le_of_le_one_right
                    (mul_nonneg (Nat.cast_nonneg _)
                      (_root_.RHTower.thetaCuspGaussianConstant_nonneg _)) hex_neg
          calc (Nat.choose K (j + 1) : ℝ) *
                  (Real.sqrt (κ / Real.pi) *
                    |GaloisForLFunctions.gaussPolyFun (iterGaussPoly κ j) κ x|) *
                  |_root_.RHTower.thetaFiniteShellJet (N + 1) (K - (j + 1)) x|
              ≤ (Nat.choose K (j + 1) : ℝ) *
                  (C_sw (j + 1) * Real.exp ((q : ℝ) ^ 2 / (2 * κ)) * Real.exp (-(q : ℝ) * x)) *
                  C_jet_pos (K - (j + 1)) := by
                refine mul_le_mul (mul_le_mul_of_nonneg_left hsw_bd (Nat.cast_nonneg _))
                  hjet_le (abs_nonneg _)
                  (mul_nonneg (Nat.cast_nonneg _)
                    (mul_nonneg (mul_nonneg (hC_sw_nn (j + 1)) (Real.exp_pos _).le)
                      (Real.exp_pos _).le))
            _ = _ := by ring
      -- Bound second summand at `i`.
      have hp2 : |(Nat.choose K i : ℝ) * iteratedDeriv i (fun y => gaussianPartitionSwitch κ (-y)) x *
            iteratedDeriv (K - i)
              (fun y => _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) (-y)) x| ≤
          (Nat.choose K i : ℝ) *
            (C_sw i * Real.exp ((q : ℝ) ^ 2 / (2 * κ)) * C_jet_neg (K - i)) *
            Real.exp (-(q : ℝ) * x) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
          iteratedDeriv_comp_neg i (gaussianPartitionSwitch κ) x,
          iteratedDeriv_comp_neg (K - i) (_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1)) x,
          smul_eq_mul, smul_eq_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_neg, abs_one]
        simp only [one_pow, one_mul, iteratedDeriv_thetaCuspFiniteShellPrefix]
        have hjet_neg := (abs_thetaFiniteShellJet_neg_le_of_nonneg N (K - i)).choose_spec.2 hx
        have hsw_neg : |iteratedDeriv i (gaussianPartitionSwitch κ) (-x)| ≤
            C_sw i * Real.exp ((q : ℝ) ^ 2 / (2 * κ)) * Real.exp (-(q : ℝ) * x) := by
          rcases i with _ | j
          · rw [iteratedDeriv_zero]
            have hb := gaussianPartitionSwitch_neg_bounds hκ hx
            rw [abs_of_pos hb.1]
            have hexp_le : (1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) ≤ Real.exp (-(κ / 2) * x ^ 2) := by
              calc (1 / 2 : ℝ) * Real.exp (-κ * x ^ 2)
                  ≤ 1 * Real.exp (-(κ / 2) * x ^ 2) :=
                    mul_le_mul (by norm_num)
                      (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x]))
                      (Real.exp_pos _).le zero_le_one
                _ = Real.exp (-(κ / 2) * x ^ 2) := one_mul _
            simpa only [C_sw, one_mul] using hb.2.trans (hexp_le.trans (hgauss_to_exp hx))
          · rw [iteratedDeriv_succ_gaussianPartitionSwitch, abs_mul,
              abs_of_nonneg (Real.sqrt_nonneg _)]
            have h1 := mul_le_mul_of_nonneg_left
              (abs_gaussPolyFun_le_halfGauss (iterGaussPoly κ j) hκ (-x)) (Real.sqrt_nonneg _)
            rw [neg_sq] at h1
            refine h1.trans ?_
            have h2 := mul_le_mul_of_nonneg_left (hgauss_to_exp hx) (hC_sw_nn (j + 1))
            simpa only [C_sw, mul_assoc] using h2
        calc (Nat.choose K i : ℝ) * |iteratedDeriv i (gaussianPartitionSwitch κ) (-x)| *
                |_root_.RHTower.thetaFiniteShellJet (N + 1) (K - i) (-x)|
            ≤ (Nat.choose K i : ℝ) *
                (C_sw i * Real.exp ((q : ℝ) ^ 2 / (2 * κ)) * Real.exp (-(q : ℝ) * x)) *
                C_jet_neg (K - i) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hsw_neg (Nat.cast_nonneg _))
                hjet_neg (abs_nonneg _)
                (mul_nonneg (Nat.cast_nonneg _)
                  (mul_nonneg (mul_nonneg (hC_sw_nn i) (Real.exp_pos _).le) (Real.exp_pos _).le))
          _ = _ := by ring
      refine (abs_add_le _ _).trans ?_
      calc _ ≤ (Nat.choose K i : ℝ) *
                (if i = 0 then C_jet_pos K
                 else C_sw i * Real.exp ((q : ℝ) ^ 2 / (2 * κ)) * C_jet_pos (K - i)) *
                Real.exp (-(q : ℝ) * x) +
              (Nat.choose K i : ℝ) *
                (C_sw i * Real.exp ((q : ℝ) ^ 2 / (2 * κ)) * C_jet_neg (K - i)) *
                Real.exp (-(q : ℝ) * x) := add_le_add hp1 hp2
        _ = termBound i * Real.exp (-(q : ℝ) * x) := by dsimp [termBound]; ring
    rw [← Finset.sum_mul] at hsum_le
    refine hsum_le.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    dsimp [C_tot]; linarith
  refine ⟨C_tot, hC_pos, fun x => ?_⟩
  have heven_abs : |iteratedDeriv K (partitionSymThetaSource N κ) x| =
      |iteratedDeriv K (partitionSymThetaSource N κ) (|x|)| := by
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg hx, abs_iteratedDeriv_neg_eq_of_even_real (partitionSymThetaSource_even N κ)]
  rw [heven_abs]
  refine (hpos_bound (abs_nonneg x)).trans (mul_le_mul_of_nonneg_left ?_ hC_pos.le)
  exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg x, hM_le_q])

/-- Bilateral Laplace amplitude of `partitionSymThetaSource N κ`. -/
def partitionSymThetaAmplitude (N : ℕ) (κ : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (partitionSymThetaSource N κ x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))

/-- Bilateral first moment of `partitionSymThetaSource N κ`. -/
def partitionSymThetaFirstMoment (N : ℕ) (κ : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, (x : ℂ) * (partitionSymThetaSource N κ x : ℂ) *
    Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))

private lemma integrable_iteratedDeriv_partitionSym_mul_cexp (N K : ℕ) {κ : ℝ} (hκ : 0 < κ)
    (r : ℕ) (z : ℂ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ r *
      ((iteratedDeriv K (partitionSymThetaSource N κ) x : ℝ) : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
  obtain ⟨C, hC_pos, hbd⟩ := abs_iteratedDeriv_partitionSymThetaSource_le_exp N K hκ
    (|1 / 2 - z.re| + (r : ℝ) + 2)
  have hcont : Continuous (fun x : ℝ => (x : ℂ) ^ r *
      ((iteratedDeriv K (partitionSymThetaSource N κ) x : ℝ) : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
    have hK_cont : Continuous (iteratedDeriv K (partitionSymThetaSource N κ)) :=
      (contDiff_infty.mp (contDiff_partitionSymThetaSource N κ) (K + 1)).continuous_iteratedDeriv K
        (by norm_cast; omega)
    exact ((Complex.continuous_ofReal.pow r).mul
      (Complex.continuous_ofReal.comp hK_cont)).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  refine Integrable.mono (_root_.RHTower.integrable_thetaAmplitudeProfile.const_mul C)
    hcont.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Complex.norm_exp,
    Real.norm_eq_abs, abs_of_pos (mul_pos hC_pos (Real.exp_pos _))]
  have hpow : |x| ^ r ≤ Real.exp ((r : ℝ) * |x|) := by
    have h1 : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
    calc |x| ^ r ≤ (Real.exp |x|) ^ r := pow_le_pow_left₀ (abs_nonneg x) h1 r
      _ = Real.exp ((r : ℝ) * |x|) := (Real.exp_nat_mul |x| r).symm
  have hre : (((1 / 2 : ℂ) - z) * (x : ℂ)).re ≤ |1 / 2 - z.re| * |x| := by
    have he : (((1 / 2 : ℂ) - z) * (x : ℂ)).re = (1 / 2 - z.re) * x := by simp
    rw [he]; exact (le_abs_self _).trans (by rw [abs_mul])
  calc |x| ^ r * |iteratedDeriv K (partitionSymThetaSource N κ) x| *
          Real.exp (((1 / 2 : ℂ) - z) * (x : ℂ)).re
      ≤ Real.exp ((r : ℝ) * |x|) *
          (C * Real.exp (-(|1 / 2 - z.re| + (r : ℝ) + 2) * |x|)) *
          Real.exp (|1 / 2 - z.re| * |x|) := by
        refine mul_le_mul (mul_le_mul hpow (hbd x) (abs_nonneg _) (Real.exp_pos _).le)
          (Real.exp_le_exp.mpr hre) (Real.exp_pos _).le (by positivity)
    _ = C * Real.exp (-2 * |x|) := by
        calc Real.exp ((r : ℝ) * |x|) *
                (C * Real.exp (-(|1 / 2 - z.re| + (r : ℝ) + 2) * |x|)) *
                Real.exp (|1 / 2 - z.re| * |x|)
            = C * (Real.exp ((r : ℝ) * |x|) *
                Real.exp (-(|1 / 2 - z.re| + (r : ℝ) + 2) * |x|) *
                Real.exp (|1 / 2 - z.re| * |x|)) := by ring
          _ = C * Real.exp (-2 * |x|) := by
              rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
    _ ≤ C * Real.exp (-|x|) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [abs_nonneg x])) hC_pos.le

/-- Holomorphy and first-moment derivative law for `partitionSymThetaAmplitude N κ`. -/
theorem hasDerivAt_partitionSymThetaAmplitude (N : ℕ) {κ : ℝ} (hκ : 0 < κ) (z : ℂ) :
    HasDerivAt (partitionSymThetaAmplitude N κ) (-partitionSymThetaFirstMoment N κ z) z := by
  let R₀ : ℝ := ‖z‖ + 2
  obtain ⟨C, hC_pos, hbd⟩ := abs_iteratedDeriv_partitionSymThetaSource_le_exp N 0 hκ (R₀ + 3)
  rw [iteratedDeriv_zero] at hbd
  have hmem : Metric.ball z 1 ∈ 𝓝 z := Metric.ball_mem_nhds z zero_lt_one
  have hint_w : ∀ w : ℂ, Integrable (fun x : ℝ =>
      (partitionSymThetaSource N κ x : ℂ) * Complex.exp (((1 / 2 : ℂ) - w) * (x : ℂ))) := by
    intro w
    simpa only [pow_zero, one_mul, iteratedDeriv_zero] using
      integrable_iteratedDeriv_partitionSym_mul_cexp N 0 hκ 0 w
  have hderiv_pt : ∀ (x : ℝ) (w : ℂ),
      HasDerivAt (fun ζ : ℂ =>
        (partitionSymThetaSource N κ x : ℂ) * Complex.exp (((1 / 2 : ℂ) - ζ) * (x : ℂ)))
        (-(x : ℂ) * (partitionSymThetaSource N κ x : ℂ) *
          Complex.exp (((1 / 2 : ℂ) - w) * (x : ℂ))) w := by
    intro x w
    have hlin : HasDerivAt (fun ζ : ℂ => ((1 / 2 : ℂ) - ζ) * (x : ℂ)) (-(x : ℂ)) w := by
      simpa using ((hasDerivAt_const w (1 / 2 : ℂ)).sub (hasDerivAt_id w)).mul_const (x : ℂ)
    refine (hlin.cexp.const_mul (partitionSymThetaSource N κ x : ℂ)).congr_deriv ?_
    ring
  have hres := (_root_.hasDerivAt_integral_of_dominated_loc_of_deriv_le hmem
    (Eventually.of_forall fun w => (hint_w w).aestronglyMeasurable)
    (hint_w z)
    (by
      have h := integrable_iteratedDeriv_partitionSym_mul_cexp N 0 hκ 1 z
      simp only [pow_one, iteratedDeriv_zero] at h
      exact h.neg.aestronglyMeasurable.congr (Eventually.of_forall fun x => by ring))
    (Eventually.of_forall fun x w hw => ?_)
    (_root_.RHTower.integrable_thetaAmplitudeProfile.const_mul C)
    (Eventually.of_forall fun x w _ => hderiv_pt x w)).2
  · refine hres.congr_deriv ?_
    unfold partitionSymThetaFirstMoment
    rw [← MeasureTheory.integral_neg]
    congr 1; funext x; ring
  · rw [Metric.mem_ball, dist_eq_norm] at hw
    have hw_norm : ‖w‖ ≤ R₀ - 1 := by
      have htri := norm_sub_norm_le w z
      dsimp [R₀]; linarith
    have hre : (((1 / 2 : ℂ) - w) * (x : ℂ)).re ≤ R₀ * |x| := by
      have he : (((1 / 2 : ℂ) - w) * (x : ℂ)).re = (1 / 2 - w.re) * x := by simp
      have habs : |1 / 2 - w.re| ≤ R₀ := by
        have ht := abs_sub (1 / 2 : ℝ) w.re
        have hr := Complex.abs_re_le_norm w
        norm_num at ht; dsimp [R₀] at hw_norm ⊢; linarith
      rw [he]
      exact (le_abs_self _).trans ((abs_mul _ _).trans_le
        (mul_le_mul_of_nonneg_right habs (abs_nonneg x)))
    have hx_exp : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, Complex.norm_exp]
    calc |x| * |partitionSymThetaSource N κ x| * Real.exp (((1 / 2 : ℂ) - w) * (x : ℂ)).re
        ≤ Real.exp |x| * (C * Real.exp (-(R₀ + 3) * |x|)) * Real.exp (R₀ * |x|) := by
          refine mul_le_mul (mul_le_mul hx_exp (hbd x) (abs_nonneg _) (Real.exp_pos _).le)
            (Real.exp_le_exp.mpr hre) (Real.exp_pos _).le (by positivity)
      _ = C * Real.exp (-2 * |x|) := by
          calc Real.exp |x| * (C * Real.exp (-(R₀ + 3) * |x|)) * Real.exp (R₀ * |x|)
              = C * (Real.exp |x| * Real.exp (-(R₀ + 3) * |x|) * Real.exp (R₀ * |x|)) := by ring
            _ = C * Real.exp (-2 * |x|) := by rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
      _ ≤ C * Real.exp (-|x|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [abs_nonneg x])) hC_pos.le

theorem differentiable_partitionSymThetaAmplitude (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Differentiable ℂ (partitionSymThetaAmplitude N κ) :=
  fun z => (hasDerivAt_partitionSymThetaAmplitude N hκ z).differentiableAt

/-- Functional symmetry `z ↔ 1 - z` of `partitionSymThetaAmplitude N κ`. -/
theorem partitionSymThetaAmplitude_one_sub (N : ℕ) (κ : ℝ) (z : ℂ) :
    partitionSymThetaAmplitude N κ (1 - z) = partitionSymThetaAmplitude N κ z := by
  unfold partitionSymThetaAmplitude
  rw [← MeasureTheory.integral_neg_eq_self (fun x =>
    (partitionSymThetaSource N κ x : ℂ) * Complex.exp (((1 / 2 : ℂ) - (1 - z)) * (x : ℂ)))]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [partitionSymThetaSource_even N κ x]
  congr 1; congr 1; push_cast; ring

/-- **All-order bilateral integration by parts for `partitionSymThetaAmplitude N κ` (`κ > 0`)**:
because `partitionSymThetaSource N κ` is `C^∞` across `x = 0`, every boundary/seam jump vanishes. -/
theorem pow_mul_partitionSymThetaAmplitude_eq_integral_iteratedDeriv (N K : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (z : ℂ) :
    (z - (1 / 2 : ℂ)) ^ K * partitionSymThetaAmplitude N κ z =
      ∫ x : ℝ, ((iteratedDeriv K (partitionSymThetaSource N κ) x : ℝ) : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) := by
  induction K with
  | zero => simp [partitionSymThetaAmplitude]
  | succ K ih =>
    rw [pow_succ', mul_assoc, ih]
    set gK : ℝ → ℝ := iteratedDeriv K (partitionSymThetaSource N κ)
    set gK1 : ℝ → ℝ := iteratedDeriv (K + 1) (partitionSymThetaSource N κ)
    let F : ℝ → ℂ := fun x => (gK x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))
    have hderiv_F : ∀ x : ℝ, HasDerivAt F
        ((gK1 x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) -
          (z - (1 / 2 : ℂ)) * ((gK x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))) x := by
      intro x
      have hg : HasDerivAt gK (gK1 x) x := by
        have hcd : DifferentiableAt ℝ gK x :=
          ((contDiff_infty.mp (contDiff_partitionSymThetaSource N κ) (K + 1)).differentiable_iteratedDeriv K
            (by norm_cast; omega)) x
        have hd_eq : deriv gK x = gK1 x := by
          dsimp [gK, gK1]; rw [iteratedDeriv_succ]
        rw [← hd_eq]
        exact hcd.hasDerivAt
      have he : HasDerivAt (fun u : ℝ => Complex.exp (((1 / 2 : ℂ) - z) * (u : ℂ)))
          (((1 / 2 : ℂ) - z) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) x := by
        have hlin : HasDerivAt (fun u : ℝ => ((1 / 2 : ℂ) - z) * (u : ℂ))
            ((1 / 2 : ℂ) - z) x := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul ((1 / 2 : ℂ) - z)
        exact hlin.cexp.congr_deriv (mul_comm _ _)
      refine (hg.ofReal_comp.mul he).congr_deriv ?_
      ring
    have hint1 : Integrable (fun x : ℝ =>
        (gK1 x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
      simpa only [pow_zero, one_mul] using
        integrable_iteratedDeriv_partitionSym_mul_cexp N (K + 1) hκ 0 z
    have hint0 : Integrable (fun x : ℝ =>
        (gK x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
      simpa only [pow_zero, one_mul] using
        integrable_iteratedDeriv_partitionSym_mul_cexp N K hκ 0 z
    obtain ⟨C, hC_pos, hbd⟩ := abs_iteratedDeriv_partitionSymThetaSource_le_exp N K hκ
      (|1 / 2 - z.re| + 1)
    have hF_norm : ∀ x : ℝ, ‖F x‖ ≤ C * Real.exp (-|x|) := by
      intro x
      dsimp only [F, gK]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      have hre : (((1 / 2 : ℂ) - z) * (x : ℂ)).re ≤ |1 / 2 - z.re| * |x| := by
        have he : (((1 / 2 : ℂ) - z) * (x : ℂ)).re = (1 / 2 - z.re) * x := by simp
        rw [he]; exact (le_abs_self _).trans (by rw [abs_mul])
      calc |iteratedDeriv K (partitionSymThetaSource N κ) x| *
              Real.exp (((1 / 2 : ℂ) - z) * (x : ℂ)).re
          ≤ (C * Real.exp (-(|1 / 2 - z.re| + 1) * |x|)) *
              Real.exp (|1 / 2 - z.re| * |x|) :=
            mul_le_mul (hbd x) (Real.exp_le_exp.mpr hre) (Real.exp_pos _).le (by positivity)
        _ = C * Real.exp (-|x|) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    have htop : Tendsto F atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall hF_norm) ?_
      have h1 : Tendsto (fun x : ℝ => C * Real.exp (-x)) atTop (𝓝 0) := by
        simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
      exact h1.congr' (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx; rw [abs_of_nonneg hx])
    have hbot : Tendsto F atBot (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall hF_norm) ?_
      have h1 : Tendsto (fun x : ℝ => C * Real.exp (-(-x))) atBot (𝓝 0) := by
        simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_neg_atBot_atTop).const_mul C
      exact h1.congr' (by filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx; rw [abs_of_nonpos hx])
    have hftc := integral_of_hasDerivAt_of_tendsto hderiv_F
      (hint1.sub (hint0.const_mul (z - (1 / 2 : ℂ)))) hbot htop
    rw [integral_sub hint1 (hint0.const_mul _), MeasureTheory.integral_const_mul, sub_self] at hftc
    exact (sub_eq_zero.mp hftc).symm

/-- **All-order super-polynomial vertical-strip decay of `partitionSymThetaAmplitude N κ` at every
finite `N` (`κ > 0`).** -/
theorem partitionSymThetaAmplitude_superpolynomial_strip_decay (N K : ℕ) {κ : ℝ} (hκ : 0 < κ)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, |z.re - 1 / 2| ≤ R →
      ‖z - (1 / 2 : ℂ)‖ ^ K * ‖partitionSymThetaAmplitude N κ z‖ ≤ B := by
  obtain ⟨C, hC_pos, hbd⟩ := abs_iteratedDeriv_partitionSymThetaSource_le_exp N K hκ (R + 1)
  refine ⟨2 * C, by positivity, fun z hz => ?_⟩
  rw [← norm_pow, ← norm_mul, pow_mul_partitionSymThetaAmplitude_eq_integral_iteratedDeriv N K hκ z]
  have hint : Integrable (fun x : ℝ =>
      ((iteratedDeriv K (partitionSymThetaSource N κ) x : ℝ) : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
    simpa only [pow_zero, one_mul] using
      integrable_iteratedDeriv_partitionSym_mul_cexp N K hκ 0 z
  have hpt : ∀ x : ℝ,
      ‖((iteratedDeriv K (partitionSymThetaSource N κ) x : ℝ) : ℂ) *
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤ C * Real.exp (-|x|) := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (((1 / 2 : ℂ) - z) * (x : ℂ)).re ≤ R * |x| := by
      have he : (((1 / 2 : ℂ) - z) * (x : ℂ)).re = (1 / 2 - z.re) * x := by simp
      have habs : |1 / 2 - z.re| ≤ R := by rwa [abs_sub_comm]
      rw [he]
      exact (le_abs_self _).trans ((abs_mul _ _).trans_le
        (mul_le_mul_of_nonneg_right habs (abs_nonneg x)))
    calc |iteratedDeriv K (partitionSymThetaSource N κ) x| *
            Real.exp (((1 / 2 : ℂ) - z) * (x : ℂ)).re
        ≤ (C * Real.exp (-(R + 1) * |x|)) * Real.exp (R * |x|) :=
          mul_le_mul (hbd x) (Real.exp_le_exp.mpr hre) (Real.exp_pos _).le (by positivity)
      _ = C * Real.exp (-|x|) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hint_abs : (∫ x : ℝ, Real.exp (-|x|)) = 2 := by
    have heven : ∀ x : ℝ, Real.exp (-|-x|) = Real.exp (-|x|) := fun x => by simp
    have hsplit := HTGeometry.integral_even_eq_two_mul
      _root_.RHTower.integrable_thetaAmplitudeProfile heven
    have hIoi : (∫ x in Ioi (0 : ℝ), Real.exp (-|x|)) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-x) :=
      setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [abs_of_pos (mem_Ioi.mp hx)]
    rw [hsplit, hIoi, integral_exp_neg_Ioi_zero]; ring
  calc ‖∫ x : ℝ, ((iteratedDeriv K (partitionSymThetaSource N κ) x : ℝ) : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖
      ≤ ∫ x : ℝ, ‖((iteratedDeriv K (partitionSymThetaSource N κ) x : ℝ) : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, C * Real.exp (-|x|) :=
        integral_mono hint.norm (_root_.RHTower.integrable_thetaAmplitudeProfile.const_mul C) hpt
    _ = 2 * C := by rw [MeasureTheory.integral_const_mul, hint_abs]; ring

/-- Geometric bound `∑' n : ℕ, |thetaCuspSourceTerm (-x) n| ≤ C * exp (2 * x)` on `x ≥ 0`. -/
private lemma tsum_abs_thetaCuspSourceTerm_neg_le_exp_two {x : ℝ} (hx : 0 ≤ x) :
    (∑' n : ℕ, |_root_.RHTower.thetaCuspSourceTerm (-x) n|) ≤
      (2 * Real.exp 2 * thetaCuspSeedHalfGaussConst / Real.pi) * Real.exp (2 * x) := by
  set α : ℝ := (Real.pi / 2) * Real.exp (-2 * x)
  have hα_pos : 0 < α := by dsimp [α]; positivity
  have hα_le2 : α ≤ 2 := by
    dsimp [α]
    have hex1 : Real.exp (-2 * x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    nlinarith [Real.pi_pos]
  set r : ℝ := Real.exp (-α)
  have hr_nn : 0 ≤ r := (Real.exp_pos _).le
  have hr_lt1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1_sub_r : α * Real.exp (-2) ≤ 1 - r := by
    have h1 : α + 1 ≤ Real.exp α := Real.add_one_le_exp α
    have h2 : (α + 1) * Real.exp (-α) ≤ Real.exp α * Real.exp (-α) :=
      mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
    have h3 : Real.exp (-2) ≤ Real.exp (-α) := Real.exp_le_exp.mpr (by linarith)
    have h4 : α * Real.exp (-2) ≤ α * Real.exp (-α) :=
      mul_le_mul_of_nonneg_left h3 hα_pos.le
    dsimp [r]; linarith
  have hterm : ∀ n : ℕ, |_root_.RHTower.thetaCuspSourceTerm (-x) n| ≤
      (if n = 0 then 0 else thetaCuspSeedHalfGaussConst * r ^ n) := by
    intro n
    rcases n with _ | m
    · simp [_root_.RHTower.thetaCuspSourceTerm, _root_.RHTower.thetaCuspSeed]
    · simp only [Nat.succ_ne_zero, ↓reduceIte]
      unfold _root_.RHTower.thetaCuspSourceTerm
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      have hex_half : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      set u := ((m + 1 : ℕ) : ℝ) * Real.exp (-x)
      have hu0 : 0 ≤ u := by positivity
      have hseed := abs_thetaCuspSeed_le_halfGauss hu0
      have hm_le_sq : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
        have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
        nlinarith
      have hgauss_le : Real.exp (-(Real.pi / 2) * u ^ 2) ≤ r ^ (m + 1) := by
        dsimp [r]
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have hu2 : u ^ 2 = ((m + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-2 * x) := by
          dsimp [u]
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2; ring
        rw [hu2]
        dsimp [α]
        nlinarith [Real.pi_pos, Real.exp_pos (-2 * x)]
      calc Real.exp (-x / 2) * |_root_.RHTower.thetaCuspSeed u|
          ≤ 1 * (thetaCuspSeedHalfGaussConst * Real.exp (-(Real.pi / 2) * u ^ 2)) :=
            mul_le_mul hex_half hseed (abs_nonneg _) zero_le_one
        _ ≤ thetaCuspSeedHalfGaussConst * r ^ (m + 1) := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_left hgauss_le thetaCuspSeedHalfGaussConst_pos.le
  have hsum_maj : Summable (fun n : ℕ =>
      if n = 0 then (0 : ℝ) else thetaCuspSeedHalfGaussConst * r ^ n) := by
    refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity [thetaCuspSeedHalfGaussConst_pos])
      (fun n => ?_) ((summable_geometric_of_lt_one hr_nn hr_lt1).mul_left thetaCuspSeedHalfGaussConst)
    split_ifs
    · positivity [thetaCuspSeedHalfGaussConst_pos]
    · exact le_rfl
  have htsum_le := (_root_.RHTower.summable_thetaCuspSourceTerm (-x)).abs.tsum_le_tsum hterm hsum_maj
  have hgeom : (∑' n : ℕ, if n = 0 then (0 : ℝ) else thetaCuspSeedHalfGaussConst * r ^ n) ≤
      thetaCuspSeedHalfGaussConst * (1 - r)⁻¹ := by
    calc (∑' n : ℕ, if n = 0 then (0 : ℝ) else thetaCuspSeedHalfGaussConst * r ^ n)
        ≤ ∑' n : ℕ, thetaCuspSeedHalfGaussConst * r ^ n := by
          refine hsum_maj.tsum_le_tsum (fun n => ?_)
            ((summable_geometric_of_lt_one hr_nn hr_lt1).mul_left _)
          split_ifs
          · positivity [thetaCuspSeedHalfGaussConst_pos]
          · exact le_rfl
      _ = thetaCuspSeedHalfGaussConst * (1 - r)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr_nn hr_lt1]
  have hinv_le : (1 - r)⁻¹ ≤ (2 * Real.exp 2 / Real.pi) * Real.exp (2 * x) := by
    have hpos_lhs : 0 < α * Real.exp (-2) := by positivity
    have h1 := inv_anti₀ hpos_lhs h1_sub_r
    refine h1.trans (le_of_eq ?_)
    calc (α * Real.exp (-2))⁻¹
        = (Real.pi / 2)⁻¹ * Real.exp (-(-2 * x)) * Real.exp (-(-2 : ℝ)) := by
          dsimp [α]; rw [mul_inv, mul_inv, ← Real.exp_neg, ← Real.exp_neg]
      _ = (Real.pi / 2)⁻¹ * Real.exp (2 * x) * Real.exp 2 := by
          rw [show -(-2 * x) = 2 * x by ring, show -(-2 : ℝ) = 2 by ring]
      _ = (2 * Real.exp 2 / Real.pi) * Real.exp (2 * x) := by
          rw [inv_div]; ring
  calc (∑' n : ℕ, |_root_.RHTower.thetaCuspSourceTerm (-x) n|)
      ≤ thetaCuspSeedHalfGaussConst * (1 - r)⁻¹ := htsum_le.trans hgeom
    _ ≤ thetaCuspSeedHalfGaussConst * ((2 * Real.exp 2 / Real.pi) * Real.exp (2 * x)) :=
        mul_le_mul_of_nonneg_left hinv_le thetaCuspSeedHalfGaussConst_pos.le
    _ = (2 * Real.exp 2 * thetaCuspSeedHalfGaussConst / Real.pi) * Real.exp (2 * x) := by ring

/-- Pointwise convergence and `N`-independent `L¹` domination of `partitionSymThetaSource N κ →
thetaCuspFullSource` at fixed `κ > 0`. -/
private lemma tendsto_partitionSymStripIntegral (r : ℕ) {κ : ℝ} (hκ : 0 < κ) {R : ℝ}
    (_hR : 0 ≤ R) :
    (∀ N : ℕ, Integrable (fun x : ℝ =>
      |x| ^ r * |partitionSymThetaSource N κ x - _root_.RHTower.thetaCuspFullSource x| *
        Real.exp ((R + 1 / 2) * |x|))) ∧
    Tendsto (fun N : ℕ => ∫ x : ℝ,
      |x| ^ r * |partitionSymThetaSource N κ x - _root_.RHTower.thetaCuspFullSource x| *
        Real.exp ((R + 1 / 2) * |x|)) atTop (𝓝 0) := by
  let C_neg : ℝ := 2 * Real.exp 2 * thetaCuspSeedHalfGaussConst / Real.pi
  let bound : ℝ → ℝ := fun x =>
    |x| ^ r *
      (2 * _root_.RHTower.thetaCuspFullSource x +
        (1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) * (C_neg * Real.exp (2 * |x|))) *
      Real.exp ((R + 1 / 2) * |x|)
  -- Pointwise convergence as `N → ∞`: Jacobi reflection `Φ(-x) = Φ(x)` cancels the partition!
  have hpt_tendsto : ∀ x : ℝ, Tendsto (fun N : ℕ =>
      |x| ^ r * |partitionSymThetaSource N κ x - _root_.RHTower.thetaCuspFullSource x| *
        Real.exp ((R + 1 / 2) * |x|)) atTop (𝓝 0) := by
    intro x
    have hpos : Tendsto (fun N : ℕ => _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) x)
        atTop (𝓝 (_root_.RHTower.thetaCuspFullSource x)) := by
      have hs := (_root_.RHTower.summable_thetaCuspSourceTerm x).hasSum.tendsto_sum_nat
      exact hs.comp (tendsto_add_atTop_nat 2)
    have hneg : Tendsto (fun N : ℕ => _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) (-x))
        atTop (𝓝 (_root_.RHTower.thetaCuspFullSource (-x))) := by
      have hs := (_root_.RHTower.summable_thetaCuspSourceTerm (-x)).hasSum.tendsto_sum_nat
      exact hs.comp (tendsto_add_atTop_nat 2)
    have hsrc : Tendsto (fun N : ℕ => partitionSymThetaSource N κ x)
        atTop (𝓝 (_root_.RHTower.thetaCuspFullSource x)) := by
      have hcomb := (hpos.const_mul (gaussianPartitionSwitch κ x)).add
        (hneg.const_mul (gaussianPartitionSwitch κ (-x)))
      have hlim : gaussianPartitionSwitch κ x * _root_.RHTower.thetaCuspFullSource x +
          gaussianPartitionSwitch κ (-x) * _root_.RHTower.thetaCuspFullSource (-x) =
          _root_.RHTower.thetaCuspFullSource x := by
        rw [_root_.RHTower.thetaCuspFullSource_neg, ← add_mul,
          gaussianPartitionSwitch_add_neg, one_mul]
      rw [hlim] at hcomb
      exact hcomb
    have habs0 : Tendsto (fun N : ℕ =>
        |partitionSymThetaSource N κ x - _root_.RHTower.thetaCuspFullSource x|) atTop (𝓝 0) := by
      simpa only [sub_self, abs_zero] using
        (hsrc.sub (tendsto_const_nhds (x := _root_.RHTower.thetaCuspFullSource x))).abs
    simpa only [mul_zero, zero_mul] using
      (habs0.const_mul (|x| ^ r)).mul_const (Real.exp ((R + 1 / 2) * |x|))
  -- Pointwise domination across all `N` and `x : ℝ` (using evenness of both functions).
  have hpt_dom : ∀ (N : ℕ) (x : ℝ),
      ‖|x| ^ r * |partitionSymThetaSource N κ x - _root_.RHTower.thetaCuspFullSource x| *
          Real.exp ((R + 1 / 2) * |x|)‖ ≤ bound x := by
    intro N x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have heven_diff : |partitionSymThetaSource N κ x - _root_.RHTower.thetaCuspFullSource x| =
        |partitionSymThetaSource N κ (|x|) - _root_.RHTower.thetaCuspFullSource (|x|)| := by
      rcases le_or_gt 0 x with hx | hx
      · rw [abs_of_nonneg hx]
      · rw [abs_of_neg hx, partitionSymThetaSource_even, _root_.RHTower.thetaCuspFullSource_neg]
    set y := |x|
    have hy : 0 ≤ y := abs_nonneg x
    have hid : partitionSymThetaSource N κ y - _root_.RHTower.thetaCuspFullSource y =
        gaussianPartitionSwitch κ y *
          (_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) y -
            _root_.RHTower.thetaCuspFullSource y) +
        gaussianPartitionSwitch κ (-y) *
          (_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) (-y) -
            _root_.RHTower.thetaCuspFullSource (-y)) := by
      unfold partitionSymThetaSource
      have h1 := gaussianPartitionSwitch_add_neg κ y
      have h2 := _root_.RHTower.thetaCuspFullSource_neg y
      nlinarith
    have hsw_y := gaussianPartitionSwitch_mem_Ioo hκ y
    have hsw_negy := gaussianPartitionSwitch_neg_bounds hκ hy
    have htail_pos : |_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) y -
          _root_.RHTower.thetaCuspFullSource y| ≤ _root_.RHTower.thetaCuspFullSource y := by
      have hrel := (_root_.RHTower.thetaCuspFiniteShellPrefix_relative_tail (N + 1) hy).1
      have hpref_nn : 0 ≤ _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) y :=
        Finset.sum_nonneg fun m _ => _root_.RHTower.thetaCuspSourceTerm_nonneg_on_halfLine hy m
      rw [abs_sub_comm, abs_of_nonneg hrel]
      linarith
    have htail_neg : |_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) (-y) -
          _root_.RHTower.thetaCuspFullSource (-y)| ≤
        _root_.RHTower.thetaCuspFullSource y + C_neg * Real.exp (2 * y) := by
      have hpref_le : |_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) (-y)| ≤
          C_neg * Real.exp (2 * y) := by
        unfold _root_.RHTower.thetaCuspFiniteShellPrefix
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact ((_root_.RHTower.summable_thetaCuspSourceTerm (-y)).abs.sum_le_tsum
          (Finset.range (N + 2)) (fun _ _ => abs_nonneg _)).trans
          (tsum_abs_thetaCuspSourceTerm_neg_le_exp_two hy)
      have hfull_nn : 0 ≤ _root_.RHTower.thetaCuspFullSource y :=
        (_root_.RHTower.thetaCuspFullSource_pos_all y).le
      rw [_root_.RHTower.thetaCuspFullSource_neg]
      have htri := abs_sub (_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) (-y))
        (_root_.RHTower.thetaCuspFullSource y)
      rw [abs_of_nonneg hfull_nn] at htri
      linarith
    have hdiff_le : |partitionSymThetaSource N κ y - _root_.RHTower.thetaCuspFullSource y| ≤
        2 * _root_.RHTower.thetaCuspFullSource x +
          (1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) * (C_neg * Real.exp (2 * y)) := by
      rw [hid]
      have h1 : |gaussianPartitionSwitch κ y *
            (_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) y -
              _root_.RHTower.thetaCuspFullSource y)| ≤
          _root_.RHTower.thetaCuspFullSource y := by
        rw [abs_mul, abs_of_pos hsw_y.1]
        exact (mul_le_mul hsw_y.2.le htail_pos (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      have h2 : |gaussianPartitionSwitch κ (-y) *
            (_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) (-y) -
              _root_.RHTower.thetaCuspFullSource (-y))| ≤
          _root_.RHTower.thetaCuspFullSource y +
            (1 / 2 : ℝ) * Real.exp (-κ * y ^ 2) * (C_neg * Real.exp (2 * y)) := by
        rw [abs_mul, abs_of_pos hsw_negy.1]
        have hmul := mul_le_mul hsw_negy.2 htail_neg (abs_nonneg _)
          (by positivity)
        have hfull_nn : 0 ≤ _root_.RHTower.thetaCuspFullSource y :=
          (_root_.RHTower.thetaCuspFullSource_pos_all y).le
        have hex_le1 : (1 / 2 : ℝ) * Real.exp (-κ * y ^ 2) ≤ 1 :=
          (mul_le_of_le_one_right (by norm_num) (Real.exp_le_one_iff.mpr (by nlinarith))).trans
            (by norm_num)
        nlinarith [Real.exp_pos (2 * y), thetaCuspSeedHalfGaussConst_pos]
      have hy_sq : y ^ 2 = x ^ 2 := sq_abs x
      have hfull_abs : _root_.RHTower.thetaCuspFullSource y =
          _root_.RHTower.thetaCuspFullSource x := _root_.RHTower.thetaCuspFullSource_abs x
      linarith [abs_add_le
        (gaussianPartitionSwitch κ y *
          (_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) y -
            _root_.RHTower.thetaCuspFullSource y))
        (gaussianPartitionSwitch κ (-y) *
          (_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) (-y) -
            _root_.RHTower.thetaCuspFullSource (-y))), hy_sq, hfull_abs]
    rw [heven_diff]
    dsimp [bound, y] at hdiff_le ⊢
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdiff_le (by positivity)) (Real.exp_pos _).le
  -- Integrability of `bound`.
  have hbound_int : Integrable bound := by
    let C₁ : ℝ := 2 * _root_.RHTower.thetaCuspTiltDecayConstant (R + (r : ℝ) + 5 / 2)
    let C₂ : ℝ := (1 / 2 : ℝ) * C_neg *
      Real.exp ((R + (r : ℝ) + 7 / 2) ^ 2 / (4 * κ))
    have hcont_b : Continuous bound := by
      dsimp [bound]
      refine ((continuous_abs.pow r).mul ?_).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_abs))
      exact (continuous_const.mul _root_.RHTower.contDiff_thetaCuspFullSource.continuous).add
        ((continuous_const.mul (Real.continuous_exp.comp
          (continuous_const.mul (continuous_pow 2)))).mul
          (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_abs))))
    refine Integrable.mono (_root_.RHTower.integrable_thetaAmplitudeProfile.const_mul (C₁ + C₂))
      hcont_b.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    have hpow : |x| ^ r ≤ Real.exp ((r : ℝ) * |x|) := by
      have h1 : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
      calc |x| ^ r ≤ (Real.exp |x|) ^ r := pow_le_pow_left₀ (abs_nonneg x) h1 r
        _ = Real.exp ((r : ℝ) * |x|) := (Real.exp_nat_mul |x| r).symm
    have hfull_le := _root_.RHTower.thetaCuspFullSource_le_tiltDecayConstant
      (R + (r : ℝ) + 5 / 2) x
    have hfull_nn := (_root_.RHTower.thetaCuspFullSource_pos_all x).le
    have hC_neg_nn : 0 ≤ C_neg := by dsimp [C_neg]; positivity [thetaCuspSeedHalfGaussConst_pos]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by dsimp [bound]; positivity)]
    have hp1 : |x| ^ r * (2 * _root_.RHTower.thetaCuspFullSource x) *
          Real.exp ((R + 1 / 2) * |x|) ≤ C₁ * Real.exp (-|x|) := by
      calc |x| ^ r * (2 * _root_.RHTower.thetaCuspFullSource x) * Real.exp ((R + 1 / 2) * |x|)
          ≤ Real.exp ((r : ℝ) * |x|) *
              (2 * (_root_.RHTower.thetaCuspTiltDecayConstant (R + (r : ℝ) + 5 / 2) *
                Real.exp (-((R + (r : ℝ) + 5 / 2) * |x|)))) *
              Real.exp ((R + 1 / 2) * |x|) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul hpow (mul_le_mul_of_nonneg_left hfull_le zero_le_two)
                (by positivity) (Real.exp_pos _).le)
              (Real.exp_pos _).le
        _ = C₁ * Real.exp (-2 * |x|) := by
            dsimp [C₁]
            calc Real.exp ((r : ℝ) * |x|) *
                    (2 * (_root_.RHTower.thetaCuspTiltDecayConstant (R + (r : ℝ) + 5 / 2) *
                      Real.exp (-((R + (r : ℝ) + 5 / 2) * |x|)))) *
                    Real.exp ((R + 1 / 2) * |x|)
                = 2 * _root_.RHTower.thetaCuspTiltDecayConstant (R + (r : ℝ) + 5 / 2) *
                    (Real.exp ((r : ℝ) * |x|) *
                      Real.exp (-((R + (r : ℝ) + 5 / 2) * |x|)) *
                      Real.exp ((R + 1 / 2) * |x|)) := by ring
              _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
        _ ≤ C₁ * Real.exp (-|x|) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [abs_nonneg x]))
              (mul_nonneg zero_le_two (_root_.RHTower.thetaCuspTiltDecayConstant_pos _).le)
    have hp2 : |x| ^ r * ((1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) * (C_neg * Real.exp (2 * |x|))) *
          Real.exp ((R + 1 / 2) * |x|) ≤ C₂ * Real.exp (-|x|) := by
      have hquad : -κ * x ^ 2 + (R + (r : ℝ) + 7 / 2) * |x| ≤
          (R + (r : ℝ) + 7 / 2) ^ 2 / (4 * κ) := by
        rw [le_div_iff₀ (by positivity), ← sq_abs x]
        have hid : (R + (r : ℝ) + 7 / 2) ^ 2 -
            (-κ * |x| ^ 2 + (R + (r : ℝ) + 7 / 2) * |x|) * (4 * κ) =
            (2 * κ * |x| - (R + (r : ℝ) + 7 / 2)) ^ 2 := by ring
        linarith [sq_nonneg (2 * κ * |x| - (R + (r : ℝ) + 7 / 2))]
      calc |x| ^ r * ((1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) * (C_neg * Real.exp (2 * |x|))) *
              Real.exp ((R + 1 / 2) * |x|)
          ≤ Real.exp ((r : ℝ) * |x|) *
              ((1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) * (C_neg * Real.exp (2 * |x|))) *
              Real.exp ((R + 1 / 2) * |x|) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hpow (by positivity)) (Real.exp_pos _).le
        _ = (1 / 2 : ℝ) * C_neg *
              Real.exp ((-κ * x ^ 2 + (R + (r : ℝ) + 7 / 2) * |x|) - |x|) := by
            calc Real.exp ((r : ℝ) * |x|) *
                    ((1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) * (C_neg * Real.exp (2 * |x|))) *
                    Real.exp ((R + 1 / 2) * |x|)
                = (1 / 2 : ℝ) * C_neg *
                    (Real.exp ((r : ℝ) * |x|) * Real.exp (-κ * x ^ 2) *
                      Real.exp (2 * |x|) * Real.exp ((R + 1 / 2) * |x|)) := by ring
              _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
        _ ≤ (1 / 2 : ℝ) * C_neg *
              Real.exp ((R + (r : ℝ) + 7 / 2) ^ 2 / (4 * κ) - |x|) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
        _ = C₂ * Real.exp (-|x|) := by
            dsimp [C₂]; rw [mul_assoc _ (Real.exp _), ← Real.exp_add]; congr 2; ring
    have hb_eq : bound x =
        |x| ^ r * (2 * _root_.RHTower.thetaCuspFullSource x) * Real.exp ((R + 1 / 2) * |x|) +
          |x| ^ r * ((1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) * (C_neg * Real.exp (2 * |x|))) *
            Real.exp ((R + 1 / 2) * |x|) := by dsimp [bound]; ring
    have habs_rhs : |(C₁ + C₂) * Real.exp (-|x|)| = (C₁ + C₂) * Real.exp (-|x|) :=
      abs_of_nonneg (mul_nonneg
        (add_nonneg (mul_nonneg zero_le_two (_root_.RHTower.thetaCuspTiltDecayConstant_pos _).le)
          (by dsimp [C₂]; positivity)) (Real.exp_pos _).le)
    rw [habs_rhs, hb_eq, add_mul]
    exact add_le_add hp1 hp2
  have haesm : ∀ N : ℕ, AEStronglyMeasurable (fun x : ℝ =>
      |x| ^ r * |partitionSymThetaSource N κ x - _root_.RHTower.thetaCuspFullSource x| *
        Real.exp ((R + 1 / 2) * |x|)) := fun N =>
    (((continuous_abs.pow r).mul
      (((contDiff_partitionSymThetaSource N κ).continuous.sub
        _root_.RHTower.contDiff_thetaCuspFullSource.continuous).abs)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs))).aestronglyMeasurable
  refine ⟨fun N => Integrable.mono' hbound_int (haesm N) (Eventually.of_forall (hpt_dom N)), ?_⟩
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence bound haesm hbound_int hpt_dom
      (Eventually.of_forall hpt_tendsto)

/-- **Uniform vertical-strip convergence of `partitionSymThetaAmplitude N κ → xi` and
`-partitionSymThetaFirstMoment N κ → deriv xi` at any fixed `κ > 0`.** -/
theorem tendsto_partitionSymThetaAmplitude_xi_strip {κ : ℝ} (hκ : 0 < κ) {R : ℝ} (hR : 0 ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℂ, |z.re| ≤ R →
      ‖partitionSymThetaAmplitude N κ z - _root_.RHTower.xi z‖ < ε ∧
      ‖-partitionSymThetaFirstMoment N κ z - deriv _root_.RHTower.xi z‖ < ε := by
  obtain ⟨hint0, htend0⟩ := tendsto_partitionSymStripIntegral 0 hκ hR
  obtain ⟨hint1, htend1⟩ := tendsto_partitionSymStripIntegral 1 hκ hR
  filter_upwards [htend0.eventually (gt_mem_nhds hε), htend1.eventually (gt_mem_nhds hε)]
    with N hN0 hN1 z hz
  have hre : ∀ x : ℝ, ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
      Real.exp ((R + 1 / 2) * |x|) := by
    intro x
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have he : (((1 / 2 : ℂ) - z) * (x : ℂ)).re = (1 / 2 - z.re) * x := by simp
    have h1 : |1 / 2 - z.re| ≤ R + 1 / 2 := by
      have ha := abs_sub (1 / 2 : ℝ) z.re
      norm_num at ha; linarith [abs_le.mp hz]
    rw [he]
    exact (le_abs_self _).trans ((abs_mul _ _).trans_le
      (mul_le_mul_of_nonneg_right h1 (abs_nonneg x)))
  constructor
  · rw [← bilateral_fullTheta_eq_xi]
    have hpj : Integrable (fun x : ℝ =>
        (partitionSymThetaSource N κ x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
      simpa only [pow_zero, one_mul, iteratedDeriv_zero] using
        integrable_iteratedDeriv_partitionSym_mul_cexp N 0 hκ 0 z
    have hfull : Integrable (fun x : ℝ =>
        (_root_.RHTower.thetaCuspFullSource x : ℂ) *
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
      simpa only [_root_.RHTower.thetaCuspTiltSource_k] using
        _root_.RHTower.integrable_bilateralLaplace
          _root_.RHTower.thetaCuspTiltSource ((1 / 2 : ℂ) - z)
    unfold partitionSymThetaAmplitude _root_.RHTower.bilateralLaplace
    simp only [_root_.RHTower.thetaCuspTiltSource_k]
    rw [← integral_sub hpj hfull]
    have hpt : ∀ x : ℝ,
        ‖(partitionSymThetaSource N κ x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) -
            (_root_.RHTower.thetaCuspFullSource x : ℂ) *
              Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
          |x| ^ 0 * |partitionSymThetaSource N κ x - _root_.RHTower.thetaCuspFullSource x| *
            Real.exp ((R + 1 / 2) * |x|) := by
      intro x
      have hf : (partitionSymThetaSource N κ x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) -
          (_root_.RHTower.thetaCuspFullSource x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) =
          ((partitionSymThetaSource N κ x - _root_.RHTower.thetaCuspFullSource x : ℝ) : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) := by push_cast; ring
      rw [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, pow_zero, one_mul]
      exact mul_le_mul_of_nonneg_left (hre x) (abs_nonneg _)
    exact (MeasureTheory.norm_integral_le_integral_norm _).trans_lt
      ((integral_mono (hpj.sub hfull).norm (hint0 N) hpt).trans_lt hN0)
  · have hrew : -partitionSymThetaFirstMoment N κ z - deriv _root_.RHTower.xi z =
        thetaSourceFirstMoment z - partitionSymThetaFirstMoment N κ z := by
      rw [thetaSourceFirstMoment_eq_neg_deriv_xi]; ring
    rw [hrew, thetaSourceFirstMoment, partitionSymThetaFirstMoment]
    have hfull1 : Integrable (fun x : ℝ =>
        (x : ℂ) * (_root_.RHTower.thetaCuspFullSource x : ℂ) *
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
      simpa only [pow_one, _root_.RHTower.thetaCuspTiltSource_k] using
        _root_.RHTower.thetaCuspTiltSource.integrable_mul_exp ((1 / 2 : ℂ) - z) 1
    have hpj1 : Integrable (fun x : ℝ =>
        (x : ℂ) * (partitionSymThetaSource N κ x : ℂ) *
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
      simpa only [pow_one, iteratedDeriv_zero] using
        integrable_iteratedDeriv_partitionSym_mul_cexp N 0 hκ 1 z
    rw [← integral_sub hfull1 hpj1]
    have hpt1 : ∀ x : ℝ,
        ‖(x : ℂ) * (_root_.RHTower.thetaCuspFullSource x : ℂ) *
              Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) -
            (x : ℂ) * (partitionSymThetaSource N κ x : ℂ) *
              Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
          |x| ^ 1 * |partitionSymThetaSource N κ x - _root_.RHTower.thetaCuspFullSource x| *
            Real.exp ((R + 1 / 2) * |x|) := by
      intro x
      have hf : (x : ℂ) * (_root_.RHTower.thetaCuspFullSource x : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) -
          (x : ℂ) * (partitionSymThetaSource N κ x : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) =
          (x : ℂ) *
            ((_root_.RHTower.thetaCuspFullSource x - partitionSymThetaSource N κ x : ℝ) : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) := by push_cast; ring
      rw [hf, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm, pow_one]
      exact mul_le_mul_of_nonneg_left (hre x) (by positivity)
    exact (MeasureTheory.norm_integral_le_integral_norm _).trans_lt
      ((integral_mono (hfull1.sub hpj1).norm (hint1 N) hpt1).trans_lt hN1)

/-- Window contour power sums of the Gaussian-partitioned Poisson–Jacobi prefix `(N, κ)`. -/
def partitionSymWindowPowerSum (T : ℝ) (n N : ℕ) (κ : ℝ) (r : ℕ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    _root_.RHTower.rectIntegral
      (fun z => z ^ r *
        (-partitionSymThetaFirstMoment N κ z / partitionSymThetaAmplitude N κ z))
      (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)

/-- Window degree of the Gaussian-partitioned Poisson–Jacobi prefix `(N, κ)`. -/
def partitionSymWindowDegree (T : ℝ) (n N : ℕ) (κ : ℝ) : ℕ :=
  Nat.floor ((partitionSymWindowPowerSum T n N κ 0).re + 1 / 2)

/-- Newton–Girard pair-difference polynomial of the Gaussian-partitioned prefix `(N, κ)`. -/
def partitionSymDifferencePoly (T : ℝ) (n N : ℕ) (κ : ℝ) : Polynomial ℂ :=
  pairDiffPoly (partitionSymWindowDegree T n N κ) (partitionSymWindowPowerSum T n N κ)

/-- Base circle loop of the Gaussian-partitioned prefix `(N, κ)`. -/
def partitionSymBaseLoop (T : ℝ) (n N : ℕ) (κ : ℝ) : C(HTGeometry.UnitCircle, ℂ) where
  toFun u := (partitionSymDifferencePoly T n N κ).eval (zhukovskyLoop n u)
  continuous_toFun :=
    (partitionSymDifferencePoly T n N κ).continuous.comp (zhukovskyLoop n).continuous

/-- Squared Zhukovsky Laurent loop of the Gaussian-partitioned prefix `(N, κ)`. -/
def partitionSymLaurentLoop (T : ℝ) (n N : ℕ) (κ : ℝ) : C(HTGeometry.UnitCircle, ℂ) :=
  partitionSymBaseLoop T n N κ ^ 2

/-- Unimodular circle symbol of the Gaussian-partitioned prefix `(N, κ)`. -/
def partitionSymCollisionSymbol (T : ℝ) (n N : ℕ) (κ : ℝ) : C(HTGeometry.UnitCircle, ℂ) :=
  unitNormalizeSymbol (partitionSymLaurentLoop T n N κ)

/-- Wiener–Hopf collision operator on `L²(ℝ)` attached to `(N, κ)`. -/
def partitionSymCollisionOperator (T : ℝ) (n N : ℕ) (κ : ℝ) :
    HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real :=
  HTGeometry.wienerHopfLift (partitionSymCollisionSymbol T n N κ)

private lemma partitionSymWindowPowerSum_zero_is_int (T : ℝ) (n N : ℕ) {κ : ℝ} (hκ : 0 < κ)
    (hne : ∀ t : ℝ, partitionSymThetaAmplitude N κ
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0) :
    ∃ k : ℤ, partitionSymWindowPowerSum T n N κ 0 = (k : ℂ) := by
  let D : _root_.RHTower.RectangleArgumentDatum :=
    { F := partitionSymThetaAmplitude N κ
      z₁ := thetaWindowLowerLeft n
      z₂ := thetaWindowUpperRight T n
      U := Set.univ
      isOpen := isOpen_univ
      differentiableOn := (differentiable_partitionSymThetaAmplitude N hκ).differentiableOn
      path_mem := fun _ => Set.mem_univ _
      ne_zero := hne }
  obtain ⟨k, hk⟩ := D.toPhase.windingNumber_eq_intCast
  refine ⟨k, ?_⟩
  rw [D.windingNumber_toPhase] at hk
  have hfun : (fun z : ℂ => z ^ 0 *
        (-partitionSymThetaFirstMoment N κ z / partitionSymThetaAmplitude N κ z)) =
      logDeriv (partitionSymThetaAmplitude N κ) := by
    funext z
    rw [pow_zero, one_mul, logDeriv_apply, (hasDerivAt_partitionSymThetaAmplitude N hκ z).deriv]
  unfold partitionSymWindowPowerSum
  rw [hfun]
  simpa [D] using hk

private lemma continuous_neg_partitionSymThetaFirstMoment (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Continuous (fun z : ℂ => -partitionSymThetaFirstMoment N κ z) := by
  have heq : (fun z : ℂ => -partitionSymThetaFirstMoment N κ z) =
      deriv (partitionSymThetaAmplitude N κ) :=
    funext fun z => ((hasDerivAt_partitionSymThetaAmplitude N hκ z).deriv).symm
  rw [heq]
  exact continuous_iff_continuousAt.mpr fun z =>
    (((differentiable_partitionSymThetaAmplitude N hκ).differentiableOn.analyticOnNhd
      isOpen_univ) z (Set.mem_univ z)).deriv.continuousAt

private lemma boundary_re_abs_le_two (T : ℝ) (n : ℕ) (t : ℝ) :
    |(_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t).re| ≤ 2 := by
  have hmem := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
    (thetaWindow_re_le T n) (thetaWindow_im_le T n) t
  rw [uIcc_of_le (thetaWindow_re_le T n), Complex.mem_reProdIm,
    thetaWindowLowerLeft_re, thetaWindowUpperRight_re] at hmem
  exact abs_le.mpr ⟨by linarith [hmem.1.1], by linarith [hmem.1.2]⟩

private lemma boundaryPath_on_edges (z₁ z₂ : ℂ) (t : ℝ) :
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t).re = z₁.re ∨
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t).re = z₂.re ∨
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t).im = z₁.im ∨
    (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t).im = z₂.im := by
  unfold _root_.RHTower.rectangleBoundaryPath _root_.RHTower.rectangleEdgePath
  split_ifs
  · right; right; left; simp
  · right; left; simp
  · right; right; right; simp
  · left; simp

private lemma boundary_xi_ne_zero {T : ℝ} {n : ℕ} (hn : thetaWindowScale T ≤ n) (t : ℝ) :
    _root_.RHTower.xi
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 := by
  intro hz0
  set γt := _root_.RHTower.rectangleBoundaryPath
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t
  have hmemRect := _root_.RHTower.rectangleBoundaryPath_mem_reProdIm
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
    (thetaWindow_re_le T n) (thetaWindow_im_le T n) t
  have hmemBox : γt ∈ thetaWindowOpenBox T n := thetaWindowRect_subset_openBox T n hmemRect
  have hmemZ := xi_zero_in_openBox_mem_stripZeros hn hmemBox hz0
  obtain ⟨h1, h2, h3, h4⟩ := stripZeros_strictly_inside_thetaWindow hn hmemZ
  rcases boundaryPath_on_edges (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t
      with h | h | h | h
  · exact h1.ne' h
  · exact h2.ne h
  · exact h3.ne' h
  · exact h4.ne h

/-- Convergence `N → ∞` of `partitionSymWindowPowerSum T n N κ r` to the exact `xi` power sum at
any fixed `κ > 0`. -/
theorem tendsto_partitionSymWindowPowerSum (T : ℝ) {n : ℕ} (hn : thetaWindowScale T ≤ n)
    {κ : ℝ} (hκ : 0 < κ) (r : ℕ) :
    Tendsto (fun N : ℕ => partitionSymWindowPowerSum T n N κ r) atTop
      (𝓝 (∑ w ∈ (_root_.RHTower.stripZeros_finite T).toFinset,
        ((analyticOrderAt _root_.RHTower.xi w).toNat : ℂ) * w ^ r)) := by
  rw [← xi_rectIntegral_powerSum_eq_stripZeros_sum T hn r]
  unfold partitionSymWindowPowerSum
  refine Tendsto.const_mul _ ?_
  set z₁ := thetaWindowLowerLeft n
  set z₂ := thetaWindowUpperRight T n
  set γ := _root_.RHTower.rectangleBoundaryPath z₁ z₂
  set vel := _root_.RHTower.rectangleBoundaryVelocity z₁ z₂
  have hγ_cont : Continuous γ := _root_.RHTower.continuous_rectangleBoundaryPath z₁ z₂
  have hxi_cont : Continuous (fun t : ℝ => ‖_root_.RHTower.xi (γ t)‖) :=
    (_root_.RHTower.xi_differentiable.continuous.comp hγ_cont).norm
  obtain ⟨t₀, _, ht₀⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)) hxi_cont.continuousOn
  set μ : ℝ := ‖_root_.RHTower.xi (γ t₀)‖
  have hμ : 0 < μ := norm_pos_iff.mpr (boundary_xi_ne_zero hn t₀)
  have hmin : ∀ t : ℝ, μ ≤ ‖_root_.RHTower.xi (γ t)‖ := by
    intro t
    have hper : γ (Int.fract t) = γ t := by
      simp [γ, _root_.RHTower.rectangleBoundaryPath, Int.fract_fract]
    rw [← hper]
    exact isMinOn_iff.mp ht₀ (Int.fract t) ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hxi_deriv_cont : Continuous (deriv _root_.RHTower.xi) :=
    continuousOn_univ.mp
      ((_root_.RHTower.xi_differentiable.differentiableOn.deriv isOpen_univ).continuousOn)
  obtain ⟨B_pow, hB_pow⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hγ_cont.pow r).continuousOn
  obtain ⟨B_xi, hB_xi⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (_root_.RHTower.xi_differentiable.continuous.comp hγ_cont).continuousOn
  obtain ⟨B_dxi, hB_dxi⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hxi_deriv_cont.comp hγ_cont).continuousOn
  set M_pow : ℝ := max 1 B_pow
  set M_xi : ℝ := max 1 B_xi
  set M_dxi : ℝ := max 1 B_dxi
  set L_vel : ℝ := 4 * (|z₂.re - z₁.re| + |z₂.im - z₁.im|)
  have hM_pow_pos : 0 < M_pow := lt_of_lt_of_le zero_lt_one (le_max_left 1 B_pow)
  have hM_dxi_pos : 0 < M_dxi := lt_of_lt_of_le zero_lt_one (le_max_left 1 B_dxi)
  have hL_vel_nonneg : 0 ≤ L_vel := by positivity
  have hxi_logDeriv_cont : Continuous (fun t : ℝ => (γ t) ^ r * logDeriv _root_.RHTower.xi (γ t)) :=
    (hγ_cont.pow r).mul
      ((hxi_deriv_cont.comp hγ_cont).div
        (_root_.RHTower.xi_differentiable.continuous.comp hγ_cont)
        (boundary_xi_ne_zero hn))
  rw [← _root_.RHTower.integral_rectangleBoundary_eq_rectIntegral z₁ z₂ _ hxi_logDeriv_cont,
    Metric.tendsto_atTop]
  intro ε hε
  set K_lip : ℝ := M_pow * ((M_xi + M_dxi + μ) / (μ ^ 2 / 2)) * (L_vel + 1)
  have hK_lip_pos : 0 < K_lip := by positivity
  set δ_err : ℝ := min (μ / 2) (ε / (2 * K_lip))
  have hδ_pos : 0 < δ_err := lt_min (half_pos hμ) (by positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (tendsto_partitionSymThetaAmplitude_xi_strip hκ (by norm_num : (0 : ℝ) ≤ 2) hδ_pos)
  refine ⟨N₀, fun N hN => ?_⟩
  have hbd_all := fun t : ℝ => hN₀ N hN (γ t) (boundary_re_abs_le_two T n t)
  have hamp_lower : ∀ t : ℝ, μ / 2 ≤ ‖partitionSymThetaAmplitude N κ (γ t)‖ := by
    intro t
    have h1 := hmin t
    have h2 := (hbd_all t).1.trans_le (min_le_left _ _)
    have htri := norm_sub_norm_le (_root_.RHTower.xi (γ t)) (partitionSymThetaAmplitude N κ (γ t))
    rw [norm_sub_rev] at htri
    linarith
  have hamp_nz : ∀ t : ℝ, partitionSymThetaAmplitude N κ (γ t) ≠ 0 := by
    intro t h0; have h := hamp_lower t; rw [h0, norm_zero] at h; linarith
  let gN : ℂ → ℂ := fun z => z ^ r *
    (-partitionSymThetaFirstMoment N κ z / partitionSymThetaAmplitude N κ z)
  have hgN_cont : Continuous (fun t : ℝ => gN (γ t)) :=
    (hγ_cont.pow r).mul
      (((continuous_neg_partitionSymThetaFirstMoment N hκ).comp hγ_cont).div
        (((differentiable_partitionSymThetaAmplitude N hκ).continuous).comp hγ_cont)
        hamp_nz)
  rw [← _root_.RHTower.integral_rectangleBoundary_eq_rectIntegral z₁ z₂ gN hgN_cont,
    dist_eq_norm]
  have hIntN := _root_.RHTower.intervalIntegrable_mul_rectangleBoundaryVelocity z₁ z₂ hgN_cont 0 1
  have hIntXi := _root_.RHTower.intervalIntegrable_mul_rectangleBoundaryVelocity
    z₁ z₂ hxi_logDeriv_cont 0 1
  rw [← intervalIntegral.integral_sub hIntN hIntXi]
  have hpt : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖gN (γ t) * vel t - ((γ t) ^ r * logDeriv _root_.RHTower.xi (γ t)) * vel t‖ ≤
        K_lip * δ_err := by
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 :=
      Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at ht)
    have hxi_nz : _root_.RHTower.xi (γ t) ≠ 0 := boundary_xi_ne_zero hn t
    have hpow_le : ‖(γ t) ^ r‖ ≤ M_pow := (hB_pow t htIcc).trans (le_max_right 1 B_pow)
    have hxi_le : ‖_root_.RHTower.xi (γ t)‖ ≤ M_xi :=
      (hB_xi t htIcc).trans (le_max_right 1 B_xi)
    have hdxi_le : ‖deriv _root_.RHTower.xi (γ t)‖ ≤ M_dxi :=
      (hB_dxi t htIcc).trans (le_max_right 1 B_dxi)
    have hvel_le : ‖vel t‖ ≤ L_vel + 1 :=
      (_root_.RHTower.norm_rectangleBoundaryVelocity_le z₁ z₂ t).trans (by linarith)
    set A_N := -partitionSymThetaFirstMoment N κ (γ t)
    set B_N := partitionSymThetaAmplitude N κ (γ t)
    set A := deriv _root_.RHTower.xi (γ t)
    set B := _root_.RHTower.xi (γ t)
    have hquot : A_N / B_N - A / B = ((A_N - A) * B + A * (B - B_N)) / (B_N * B) := by
      rw [div_sub_div _ _ (hamp_nz t) hxi_nz]; congr 1; ring
    have hdenom_pos : 0 < μ ^ 2 / 2 := by positivity
    have hdenom_le : μ ^ 2 / 2 ≤ ‖B_N * B‖ := by
      rw [norm_mul]
      calc μ ^ 2 / 2 = (μ / 2) * μ := by ring
        _ ≤ ‖B_N‖ * ‖B‖ := mul_le_mul (hamp_lower t) (hmin t) (by positivity) (norm_nonneg _)
    have hnum_le : ‖(A_N - A) * B + A * (B - B_N)‖ ≤ (M_xi + M_dxi + μ) * δ_err := by
      calc ‖(A_N - A) * B + A * (B - B_N)‖
          ≤ ‖A_N - A‖ * ‖B‖ + ‖A‖ * ‖B_N - B‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_sub_rev B B_N]
        _ ≤ δ_err * M_xi + M_dxi * δ_err :=
            add_le_add
              (mul_le_mul (hbd_all t).2.le hxi_le (norm_nonneg _) hδ_pos.le)
              (mul_le_mul hdxi_le (hbd_all t).1.le (norm_nonneg _) hM_dxi_pos.le)
        _ ≤ (M_xi + M_dxi + μ) * δ_err := by nlinarith
    have hquot_le : ‖A_N / B_N - logDeriv _root_.RHTower.xi (γ t)‖ ≤
        ((M_xi + M_dxi + μ) / (μ ^ 2 / 2)) * δ_err := by
      rw [logDeriv_apply, hquot, norm_div]
      calc ‖(A_N - A) * B + A * (B - B_N)‖ / ‖B_N * B‖
          ≤ ((M_xi + M_dxi + μ) * δ_err) / (μ ^ 2 / 2) := by
            have hBB_pos : 0 < ‖B_N * B‖ := lt_of_lt_of_le hdenom_pos hdenom_le
            rw [div_le_div_iff₀ hBB_pos hdenom_pos]
            exact mul_le_mul hnum_le hdenom_le hdenom_pos.le (by positivity)
        _ = ((M_xi + M_dxi + μ) / (μ ^ 2 / 2)) * δ_err := by ring
    have halg : gN (γ t) * vel t - ((γ t) ^ r * logDeriv _root_.RHTower.xi (γ t)) * vel t =
        (γ t) ^ r * (A_N / B_N - logDeriv _root_.RHTower.xi (γ t)) * vel t := by
      dsimp [gN]; ring
    rw [halg, norm_mul, norm_mul]
    calc ‖(γ t) ^ r‖ * ‖A_N / B_N - logDeriv _root_.RHTower.xi (γ t)‖ * ‖vel t‖
        ≤ (M_pow * (((M_xi + M_dxi + μ) / (μ ^ 2 / 2)) * δ_err)) * (L_vel + 1) := by
          refine mul_le_mul (mul_le_mul hpow_le hquot_le (norm_nonneg _) hM_pow_pos.le)
            hvel_le (norm_nonneg _) (by positivity)
      _ = K_lip * δ_err := by dsimp [K_lip]; ring
  have hint_le := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [show |(1 : ℝ) - 0| = 1 by norm_num, mul_one] at hint_le
  have hlt_eps : K_lip * δ_err < ε := by
    have hle : δ_err ≤ ε / (2 * K_lip) := min_le_right _ _
    calc K_lip * δ_err ≤ K_lip * (ε / (2 * K_lip)) :=
          mul_le_mul_of_nonneg_left hle hK_lip_pos.le
      _ = ε / 2 := by field_simp [hK_lip_pos.ne']
      _ < ε := half_lt_self hε
  exact hint_le.trans_lt hlt_eps

/-- **Asymptotic collision-operator stabilization (`N → ∞`) of the seam-smooth Poisson–Jacobi
prefix at any fixed `κ > 0`.** -/
theorem partitionSymCollisionOperator_eventually_eq_charge (T : ℝ) {n : ℕ}
    (hn : thetaWindowScale T ≤ n) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in atTop,
      partitionSymWindowPowerSum T n N κ 0 = (_root_.RHTower.xiStripWindowTotalOrder T : ℂ) ∧
      partitionSymWindowDegree T n N κ = _root_.RHTower.xiStripWindowTotalOrder T ∧
      (∀ u : HTGeometry.UnitCircle, partitionSymLaurentLoop T n N κ u ≠ 0) ∧
      _root_.RHTower.windingNumber
        (fun θ => partitionSymLaurentLoop T n N κ (HTGeometry.circleExp θ)) 0 (2 * Real.pi) =
        (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) ∧
      HTGeometry.fredholmIndex (partitionSymCollisionOperator T n N κ) =
        (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) := by
  -- Boundary nonvanishing and degree stabilization.
  set γ := _root_.RHTower.rectangleBoundaryPath
    (thetaWindowLowerLeft n) (thetaWindowUpperRight T n)
  have hγ_cont : Continuous γ := _root_.RHTower.continuous_rectangleBoundaryPath _ _
  obtain ⟨t₀, _, ht₀⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1))
    ((_root_.RHTower.xi_differentiable.continuous.comp hγ_cont).norm).continuousOn
  set μ_b : ℝ := ‖_root_.RHTower.xi (γ t₀)‖
  have hμ_b : 0 < μ_b := norm_pos_iff.mpr (boundary_xi_ne_zero hn t₀)
  have hev_nz : ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, partitionSymThetaAmplitude N κ (γ t) ≠ 0 := by
    filter_upwards [tendsto_partitionSymThetaAmplitude_xi_strip hκ (by norm_num : (0 : ℝ) ≤ 2)
      (half_pos hμ_b)] with N hN t h0
    have hbd := (hN (γ t) (boundary_re_abs_le_two T n t)).1
    rw [h0, zero_sub, norm_neg] at hbd
    have hper : γ (Int.fract t) = γ t := by
      simp [γ, _root_.RHTower.rectangleBoundaryPath, Int.fract_fract]
    have hmin_t : μ_b ≤ ‖_root_.RHTower.xi (γ t)‖ := by
      rw [← hper]
      exact isMinOn_iff.mp ht₀ (Int.fract t) ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
    linarith
  have hsum0 : (∑ w ∈ (_root_.RHTower.stripZeros_finite T).toFinset,
      ((analyticOrderAt _root_.RHTower.xi w).toNat : ℂ) * w ^ 0) =
      (_root_.RHTower.xiStripWindowTotalOrder T : ℂ) := by
    simp [_root_.RHTower.xiStripWindowTotalOrder]
  have htend0 := tendsto_partitionSymWindowPowerSum T hn hκ 0
  rw [hsum0] at htend0
  have hev_deg : ∀ᶠ N : ℕ in atTop,
      partitionSymWindowPowerSum T n N κ 0 = (_root_.RHTower.xiStripWindowTotalOrder T : ℂ) ∧
        partitionSymWindowDegree T n N κ = _root_.RHTower.xiStripWindowTotalOrder T := by
    filter_upwards [hev_nz, (Metric.tendsto_nhds.mp htend0) (1 / 2 : ℝ) (by norm_num)]
      with N hnz hdist
    obtain ⟨k, hk⟩ := partitionSymWindowPowerSum_zero_is_int T n N hκ hnz
    rw [hk, dist_eq_norm] at hdist
    have hcast : (k : ℂ) - (_root_.RHTower.xiStripWindowTotalOrder T : ℂ) =
        (((k - (_root_.RHTower.xiStripWindowTotalOrder T : ℤ)) : ℤ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_intCast] at hdist
    have habs : |(k : ℝ) - (_root_.RHTower.xiStripWindowTotalOrder T : ℝ)| < 1 / 2 := by
      exact_mod_cast hdist
    obtain ⟨h1, h2⟩ := abs_lt.mp habs
    have hlt : ((k - (_root_.RHTower.xiStripWindowTotalOrder T : ℤ) : ℤ) : ℝ) < 1 := by
      push_cast; linarith
    have hgt : (-1 : ℝ) < ((k - (_root_.RHTower.xiStripWindowTotalOrder T : ℤ) : ℤ) : ℝ) := by
      push_cast; linarith
    have hk_eq : k = (_root_.RHTower.xiStripWindowTotalOrder T : ℤ) := by
      have hlt' : k - (_root_.RHTower.xiStripWindowTotalOrder T : ℤ) < 1 := by exact_mod_cast hlt
      have hgt' : -1 < k - (_root_.RHTower.xiStripWindowTotalOrder T : ℤ) := by exact_mod_cast hgt
      omega
    have hp0 : partitionSymWindowPowerSum T n N κ 0 =
        (_root_.RHTower.xiStripWindowTotalOrder T : ℂ) := by
      rw [hk, hk_eq]; norm_cast
    refine ⟨hp0, ?_⟩
    unfold partitionSymWindowDegree
    rw [hp0, Complex.natCast_re]
    exact (Nat.floor_eq_iff (by positivity)).mpr ⟨by linarith, by linarith⟩
  -- Newton–Girard continuity on `zhukovskyLoop n`.
  obtain ⟨hQ_nz, hQ_wind⟩ := exactWindowDifferencePoly_winding T hn
  obtain ⟨u₀, _, hu₀⟩ := isCompact_univ.exists_isMinOn
    ⟨HTGeometry.circleExp 0, Set.mem_univ _⟩
    (((exactWindowDifferencePoly T).continuous.comp (zhukovskyLoop n).continuous).norm).continuousOn
  set η : ℝ := ‖(exactWindowDifferencePoly T).eval (zhukovskyLoop n u₀)‖
  have hη_pos : 0 < η := norm_pos_iff.mpr (hQ_nz u₀)
  have hη_le : ∀ u : HTGeometry.UnitCircle,
      η ≤ ‖(exactWindowDifferencePoly T).eval (zhukovskyLoop n u)‖ :=
    fun u => isMinOn_iff.mp hu₀ u (Set.mem_univ u)
  set M_ord := _root_.RHTower.xiStripWindowTotalOrder T
  let s₀ : ℕ → ℂ := fun r => ∑ w ∈ (_root_.RHTower.stripZeros_finite T).toFinset,
    ((analyticOrderAt _root_.RHTower.xi w).toNat : ℂ) * w ^ r
  have htend_ps : ∀ K : ℕ, Tendsto
      (fun N => pairDiffPowerSum M_ord (partitionSymWindowPowerSum T n N κ) K) atTop
      (𝓝 (pairDiffPowerSum M_ord s₀ K)) := by
    intro K
    unfold pairDiffPowerSum; dsimp only
    refine tendsto_finsetSum _ fun r _ => ?_
    have h1 : Tendsto (fun N => if r = 0 then (M_ord : ℂ) else
        partitionSymWindowPowerSum T n N κ r) atTop
        (𝓝 (if r = 0 then (M_ord : ℂ) else s₀ r)) := by
      by_cases hr : r = 0
      · simp [hr]
      · simpa [hr] using tendsto_partitionSymWindowPowerSum T hn hκ r
    have h2 : Tendsto (fun N => if K - r = 0 then (M_ord : ℂ) else
        partitionSymWindowPowerSum T n N κ (K - r)) atTop
        (𝓝 (if K - r = 0 then (M_ord : ℂ) else s₀ (K - r))) := by
      by_cases hKr : K - r = 0
      · simp [hKr]
      · simpa [hKr] using tendsto_partitionSymWindowPowerSum T hn hκ (K - r)
    exact (h1.const_mul _).mul h2
  have htend_elem : ∀ k : ℕ, Tendsto
      (fun N => newtonElem (pairDiffPowerSum M_ord (partitionSymWindowPowerSum T n N κ)) k) atTop
      (𝓝 (newtonElem (pairDiffPowerSum M_ord s₀) k)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      rcases k with _ | k
      · simp only [newtonElem, tendsto_const_nhds]
      · simp only [newtonElem]
        refine Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ => ?_)
        exact ((ih (k - j) (by omega)).const_mul ((-1 : ℂ) ^ j)).mul (htend_ps (j + 1))
  have hsum_tendsto : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range (M_ord ^ 2 + 1),
        ‖newtonElem (pairDiffPowerSum M_ord (partitionSymWindowPowerSum T n N κ)) k -
          newtonElem (pairDiffPowerSum M_ord s₀) k‖ * 2 ^ (M_ord ^ 2 - k))
      atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ _k ∈ Finset.range (M_ord ^ 2 + 1), (0 : ℝ) by simp]
    refine tendsto_finsetSum _ fun k _ => ?_
    have hnorm : Tendsto
        (fun N : ℕ =>
          ‖newtonElem (pairDiffPowerSum M_ord (partitionSymWindowPowerSum T n N κ)) k -
            newtonElem (pairDiffPowerSum M_ord s₀) k‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero] using
        ((htend_elem k).sub (tendsto_const_nhds (x := newtonElem (pairDiffPowerSum M_ord s₀) k))).norm
    simpa only [zero_mul] using hnorm.mul_const (2 ^ (M_ord ^ 2 - k))
  filter_upwards [hev_deg, hsum_tendsto.eventually (gt_mem_nhds hη_pos)] with N hdeg hsum_lt
  have happrox : ∀ u : HTGeometry.UnitCircle,
      ‖(partitionSymDifferencePoly T n N κ).eval (zhukovskyLoop n u) -
          (exactWindowDifferencePoly T).eval (zhukovskyLoop n u)‖ <
        ‖(exactWindowDifferencePoly T).eval (zhukovskyLoop n u)‖ := by
    intro u
    have hpoly_eq : partitionSymDifferencePoly T n N κ =
        newtonPoly (M_ord ^ 2) (pairDiffPowerSum M_ord (partitionSymWindowPowerSum T n N κ)) := by
      unfold partitionSymDifferencePoly pairDiffPoly
      rw [hdeg.2]
    rw [hpoly_eq]
    have hle_sum : ‖(newtonPoly (M_ord ^ 2)
          (pairDiffPowerSum M_ord (partitionSymWindowPowerSum T n N κ))).eval (zhukovskyLoop n u) -
        (exactWindowDifferencePoly T).eval (zhukovskyLoop n u)‖ ≤
        ∑ k ∈ Finset.range (M_ord ^ 2 + 1),
          ‖newtonElem (pairDiffPowerSum M_ord (partitionSymWindowPowerSum T n N κ)) k -
            newtonElem (pairDiffPowerSum M_ord s₀) k‖ * 2 ^ (M_ord ^ 2 - k) := by
      unfold exactWindowDifferencePoly pairDiffPoly newtonPoly
      rw [Polynomial.eval_finsetSum, Polynomial.eval_finsetSum, ← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      have hdiff : (-1 : ℂ) ^ k *
          newtonElem (pairDiffPowerSum M_ord (partitionSymWindowPowerSum T n N κ)) k *
          (zhukovskyLoop n u) ^ (M_ord ^ 2 - k) -
          (-1 : ℂ) ^ k * newtonElem (pairDiffPowerSum M_ord s₀) k *
          (zhukovskyLoop n u) ^ (M_ord ^ 2 - k) =
          (-1 : ℂ) ^ k *
            (newtonElem (pairDiffPowerSum M_ord (partitionSymWindowPowerSum T n N κ)) k -
              newtonElem (pairDiffPowerSum M_ord s₀) k) *
            (zhukovskyLoop n u) ^ (M_ord ^ 2 - k) := by ring
      have hzhuk_le2 : ‖zhukovskyLoop n u‖ ≤ 2 := by
        have h1 := norm_zhukovskyLoop_sub_half_le n u
        have ha := (zhukovskyMajorAxis_lt_half n).le
        have hb := zhukovskyMinorAxis_le_sixth n
        have htri : ‖zhukovskyLoop n u‖ ≤ ‖zhukovskyLoop n u - (1 / 2 : ℂ)‖ + ‖(1 / 2 : ℂ)‖ := by
          simpa using norm_add_le (zhukovskyLoop n u - (1 / 2 : ℂ)) (1 / 2 : ℂ)
        have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
        linarith
      rw [hdiff, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hzhuk_le2 (M_ord ^ 2 - k)) (norm_nonneg _)
    exact hle_sum.trans_lt (hsum_lt.trans_le (hη_le u))
  obtain ⟨hL_nz, hL_wind⟩ := windingNumber_zhukovsky_poly_sq_of_approx n
    (partitionSymDifferencePoly T n N κ) (exactWindowDifferencePoly T) hQ_nz happrox
  have hL_nz' : ∀ u : HTGeometry.UnitCircle, partitionSymLaurentLoop T n N κ u ≠ 0 := hL_nz
  have hwind_eq : _root_.RHTower.windingNumber
      (fun θ => partitionSymLaurentLoop T n N κ (HTGeometry.circleExp θ)) 0 (2 * Real.pi) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) := by
    change _root_.RHTower.windingNumber
      (fun θ => ((partitionSymDifferencePoly T n N κ).eval
        (zhukovskyLoop n (HTGeometry.circleExp θ))) ^ 2) 0 (2 * Real.pi) = _
    rw [hL_wind, hQ_wind]
  have hfred : HTGeometry.fredholmIndex (partitionSymCollisionOperator T n N κ) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) := by
    unfold partitionSymCollisionOperator partitionSymCollisionSymbol
    rw [fredholmIndex_wienerHopfLift_unitNormalizeSymbol,
      circleWinding_unitNormalizeSymbol_of_ne_zero hL_nz', hwind_eq]
  exact ⟨hdeg.1, hdeg.2, hL_nz', hwind_eq, hfred⟩

/-! ### `κ → ∞` persistence of arbitrarily many off-line zeros -/

/-- Explicit `O(κ^{-1/2})` uniform vertical-strip convergence of `partitionSymThetaAmplitude N κ`
to `finiteThetaAmplitude N` as `κ → ∞` at fixed `N`. -/
theorem norm_partitionSymThetaAmplitude_sub_finite_le_strip (N : ℕ) {R : ℝ} (hR : 0 ≤ R)
    {κ : ℝ} (hκ : max 1 ((R + 2) ^ 2) ≤ κ) {z : ℂ} (hz : |z.re - 1 / 2| ≤ R) :
    ‖partitionSymThetaAmplitude N κ z - _root_.RHTower.finiteThetaAmplitude N z‖ ≤
      ((Real.exp 3 * thetaCuspSeedHalfGaussConst / Real.pi) +
        (1 / 2 : ℝ) * _root_.RHTower.thetaCuspTiltDecayConstant (R + 1)) *
        Real.sqrt (2 * Real.pi / κ) := by
  have hκ_pos : 0 < κ := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hκ)
  have hκ_sq : (R + 2) ^ 2 ≤ κ := (le_max_right _ _).trans hκ
  let C_neg : ℝ := 2 * Real.exp 2 * thetaCuspSeedHalfGaussConst / Real.pi
  let K_c : ℝ := (Real.exp 3 * thetaCuspSeedHalfGaussConst / Real.pi) +
    (1 / 2 : ℝ) * _root_.RHTower.thetaCuspTiltDecayConstant (R + 1)
  have hK_c_pos : 0 < K_c := by
    dsimp [K_c]
    have h1 : 0 < Real.exp 3 * thetaCuspSeedHalfGaussConst / Real.pi := by
      positivity [thetaCuspSeedHalfGaussConst_pos]
    have h2 : 0 < _root_.RHTower.thetaCuspTiltDecayConstant (R + 1) :=
      _root_.RHTower.thetaCuspTiltDecayConstant_pos _
    linarith
  have hpj : Integrable (fun x : ℝ =>
      (partitionSymThetaSource N κ x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
    simpa only [pow_zero, one_mul, iteratedDeriv_zero] using
      integrable_iteratedDeriv_partitionSym_mul_cexp N 0 hκ_pos 0 z
  have hfin : Integrable (fun x : ℝ =>
      (_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
    simpa only [_root_.RHTower.finiteThetaTiltSource] using
      _root_.RHTower.integrable_bilateralLaplace
        (_root_.RHTower.finiteThetaTiltSource N) ((1 / 2 : ℂ) - z)
  have hgauss_int : Integrable (fun x : ℝ => Real.exp (-(κ / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hgauss_val : (∫ x : ℝ, Real.exp (-(κ / 2) * x ^ 2)) = Real.sqrt (2 * Real.pi / κ) := by
    have heven : ∀ x : ℝ, Real.exp (-(κ / 2) * (-x) ^ 2) = Real.exp (-(κ / 2) * x ^ 2) :=
      fun x => by rw [neg_sq]
    rw [HTGeometry.integral_even_eq_two_mul hgauss_int heven,
      HTGeometry.integral_Ioi_gaussian (by positivity : 0 < κ / 2)]
    have hdiv : Real.pi / (κ / 2) = 2 * Real.pi / κ := by rw [div_div_eq_mul_div]; ring
    rw [hdiv]; ring
  have hpt : ∀ x : ℝ,
      ‖(partitionSymThetaSource N κ x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) -
          (_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤
        K_c * Real.exp (-(κ / 2) * x ^ 2) := by
    intro x
    have hf : (partitionSymThetaSource N κ x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) -
        (_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) =
        ((partitionSymThetaSource N κ x - _root_.RHTower.reflectedFiniteThetaSource (N + 1) x :
          ℝ) : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) := by push_cast; ring
    rw [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    set y := |x|
    have hy : 0 ≤ y := abs_nonneg x
    have hy_sq : y ^ 2 = x ^ 2 := sq_abs x
    have heven_diff :
        |partitionSymThetaSource N κ x - _root_.RHTower.reflectedFiniteThetaSource (N + 1) x| =
        |partitionSymThetaSource N κ y - _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) y| := by
      have href : _root_.RHTower.reflectedFiniteThetaSource (N + 1) x =
          _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) y := rfl
      rw [href]
      rcases le_or_gt 0 x with hx | hx
      · rw [show y = x from abs_of_nonneg hx]
      · rw [show y = -x from abs_of_neg hx, partitionSymThetaSource_even]
    have hid : partitionSymThetaSource N κ y -
          _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) y =
        gaussianPartitionSwitch κ (-y) *
          (_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) (-y) -
            _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) y) := by
      unfold partitionSymThetaSource
      have hsw' : gaussianPartitionSwitch κ y = 1 - gaussianPartitionSwitch κ (-y) := by
        linarith [gaussianPartitionSwitch_add_neg κ y]
      rw [hsw']; ring
    have hsw_bd := gaussianPartitionSwitch_neg_bounds hκ_pos hy
    have hneg_le : |_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) (-y)| ≤
        C_neg * Real.exp (2 * y) := by
      unfold _root_.RHTower.thetaCuspFiniteShellPrefix
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      exact ((_root_.RHTower.summable_thetaCuspSourceTerm (-y)).abs.sum_le_tsum
        (Finset.range (N + 2)) (fun _ _ => abs_nonneg _)).trans
        (tsum_abs_thetaCuspSourceTerm_neg_le_exp_two hy)
    have hpos_le : |_root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) y| ≤
        _root_.RHTower.thetaCuspFullSource y := by
      have hnn : 0 ≤ _root_.RHTower.thetaCuspFiniteShellPrefix (N + 1) y :=
        Finset.sum_nonneg fun m _ => _root_.RHTower.thetaCuspSourceTerm_nonneg_on_halfLine hy m
      have hrel := (_root_.RHTower.thetaCuspFiniteShellPrefix_relative_tail (N + 1) hy).1
      rw [abs_of_nonneg hnn]
      linarith
    have hdiff_le :
        |partitionSymThetaSource N κ x - _root_.RHTower.reflectedFiniteThetaSource (N + 1) x| ≤
          (1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) *
            (C_neg * Real.exp (2 * y) + _root_.RHTower.thetaCuspFullSource y) := by
      rw [heven_diff, hid, abs_mul, abs_of_pos hsw_bd.1, ← hy_sq]
      refine mul_le_mul hsw_bd.2 ?_ (abs_nonneg _) (by positivity)
      exact (abs_sub _ _).trans (add_le_add hneg_le hpos_le)
    have hre : (((1 / 2 : ℂ) - z) * (x : ℂ)).re ≤ R * y := by
      have he : (((1 / 2 : ℂ) - z) * (x : ℂ)).re = (1 / 2 - z.re) * x := by simp
      have habs : |1 / 2 - z.re| ≤ R := by rwa [abs_sub_comm]
      rw [he]
      exact (le_abs_self _).trans ((abs_mul _ _).trans_le
        (mul_le_mul_of_nonneg_right habs hy))
    have hp1 : (1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) * (C_neg * Real.exp (2 * y)) *
          Real.exp (R * y) ≤
        (Real.exp 3 * thetaCuspSeedHalfGaussConst / Real.pi) *
          Real.exp (-(κ / 2) * x ^ 2) := by
      have hquad : -(κ / 2) * x ^ 2 + (R + 2) * y ≤ 1 := by
        have h1 : -(κ / 2) * x ^ 2 + (R + 2) * y ≤ (R + 2) ^ 2 / (2 * κ) := by
          rw [le_div_iff₀ (by positivity), ← hy_sq]
          have hid : (R + 2) ^ 2 - (-(κ / 2) * y ^ 2 + (R + 2) * y) * (2 * κ) =
              (κ * y - (R + 2)) ^ 2 := by ring
          linarith [sq_nonneg (κ * y - (R + 2))]
        have h2 : (R + 2) ^ 2 / (2 * κ) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith [hκ_sq, hκ_pos]
        exact h1.trans h2
      have hcomb : Real.exp (-κ * x ^ 2) * Real.exp (2 * y) * Real.exp (R * y) ≤
          Real.exp 1 * Real.exp (-(κ / 2) * x ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      calc (1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) * (C_neg * Real.exp (2 * y)) * Real.exp (R * y)
          = ((1 / 2 : ℝ) * C_neg) *
              (Real.exp (-κ * x ^ 2) * Real.exp (2 * y) * Real.exp (R * y)) := by ring
        _ ≤ ((1 / 2 : ℝ) * C_neg) * (Real.exp 1 * Real.exp (-(κ / 2) * x ^ 2)) :=
            mul_le_mul_of_nonneg_left hcomb (by dsimp [C_neg]; positivity [thetaCuspSeedHalfGaussConst_pos])
        _ = (Real.exp 3 * thetaCuspSeedHalfGaussConst / Real.pi) *
              Real.exp (-(κ / 2) * x ^ 2) := by
            dsimp [C_neg]
            have he3 : Real.exp 2 * Real.exp 1 = Real.exp 3 := by
              rw [← Real.exp_add]; norm_num
            calc (1 / 2 : ℝ) * (2 * Real.exp 2 * thetaCuspSeedHalfGaussConst / Real.pi) *
                    (Real.exp 1 * Real.exp (-(κ / 2) * x ^ 2))
                = ((Real.exp 2 * Real.exp 1) * thetaCuspSeedHalfGaussConst / Real.pi) *
                    Real.exp (-(κ / 2) * x ^ 2) := by ring
              _ = _ := by rw [he3]
    have hp2 : (1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) * _root_.RHTower.thetaCuspFullSource y *
          Real.exp (R * y) ≤
        (1 / 2 : ℝ) * _root_.RHTower.thetaCuspTiltDecayConstant (R + 1) *
          Real.exp (-(κ / 2) * x ^ 2) := by
      have hfull_le := _root_.RHTower.thetaCuspFullSource_le_tiltDecayConstant (R + 1) y
      have habs_y : |y| = y := abs_of_nonneg hy
      rw [habs_y] at hfull_le
      have hprod_le : _root_.RHTower.thetaCuspFullSource y * Real.exp (R * y) ≤
          _root_.RHTower.thetaCuspTiltDecayConstant (R + 1) := by
        calc _root_.RHTower.thetaCuspFullSource y * Real.exp (R * y)
            ≤ (_root_.RHTower.thetaCuspTiltDecayConstant (R + 1) *
                Real.exp (-((R + 1) * y))) * Real.exp (R * y) :=
              mul_le_mul_of_nonneg_right hfull_le (Real.exp_pos _).le
          _ = _root_.RHTower.thetaCuspTiltDecayConstant (R + 1) * Real.exp (-y) := by
              rw [mul_assoc, ← Real.exp_add]; congr 2; ring
          _ ≤ _root_.RHTower.thetaCuspTiltDecayConstant (R + 1) :=
              mul_le_of_le_one_right (_root_.RHTower.thetaCuspTiltDecayConstant_pos _).le
                (Real.exp_le_one_iff.mpr (by linarith))
      have hex_le : Real.exp (-κ * x ^ 2) ≤ Real.exp (-(κ / 2) * x ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
      calc (1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) * _root_.RHTower.thetaCuspFullSource y *
              Real.exp (R * y)
          = (1 / 2 : ℝ) * (_root_.RHTower.thetaCuspFullSource y * Real.exp (R * y)) *
              Real.exp (-κ * x ^ 2) := by ring
        _ ≤ (1 / 2 : ℝ) * _root_.RHTower.thetaCuspTiltDecayConstant (R + 1) *
              Real.exp (-(κ / 2) * x ^ 2) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hprod_le (by norm_num)) hex_le
              (Real.exp_pos _).le
              (mul_nonneg (by norm_num) (_root_.RHTower.thetaCuspTiltDecayConstant_pos _).le)
    have hsum_nn : 0 ≤ (1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) *
        (C_neg * Real.exp (2 * y) + _root_.RHTower.thetaCuspFullSource y) :=
      mul_nonneg (by positivity)
        (add_nonneg
          (mul_nonneg (by dsimp [C_neg]; positivity [thetaCuspSeedHalfGaussConst_pos])
            (Real.exp_pos _).le)
          (_root_.RHTower.thetaCuspFullSource_pos_all y).le)
    calc |partitionSymThetaSource N κ x - _root_.RHTower.reflectedFiniteThetaSource (N + 1) x| *
            Real.exp (((1 / 2 : ℂ) - z) * (x : ℂ)).re
        ≤ ((1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) *
            (C_neg * Real.exp (2 * y) + _root_.RHTower.thetaCuspFullSource y)) *
            Real.exp (R * y) :=
          mul_le_mul hdiff_le (Real.exp_le_exp.mpr hre) (Real.exp_pos _).le hsum_nn
      _ = (1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) * (C_neg * Real.exp (2 * y)) * Real.exp (R * y) +
            (1 / 2 : ℝ) * Real.exp (-κ * x ^ 2) * _root_.RHTower.thetaCuspFullSource y *
              Real.exp (R * y) := by ring
      _ ≤ K_c * Real.exp (-(κ / 2) * x ^ 2) := by
          dsimp [K_c]; rw [add_mul]; exact add_le_add hp1 hp2
  unfold partitionSymThetaAmplitude _root_.RHTower.finiteThetaAmplitude
  rw [← integral_sub hpj hfin]
  calc ‖∫ x : ℝ, ((partitionSymThetaSource N κ x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) -
          (_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))‖
      ≤ ∫ x : ℝ, K_c * Real.exp (-(κ / 2) * x ^ 2) :=
        (MeasureTheory.norm_integral_le_integral_norm _).trans
          (integral_mono (hpj.sub hfin).norm (hgauss_int.const_mul K_c) hpt)
    _ = K_c * Real.sqrt (2 * Real.pi / κ) := by
        rw [MeasureTheory.integral_const_mul, hgauss_val]

/-- Contrapositive Hurwitz/Rouché root-capture lemma on a disc: if `G w = 0`, `G ≠ 0` on
`sphere w δ`, and `‖F ζ - G ζ‖ < ‖G ζ‖ / 2` on `sphere w δ`, then `F` has at least one zero inside
`ball w δ`. -/
private lemma exists_zero_in_ball_of_sphere_half_bound {F G : ℂ → ℂ} {w : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hGw : G w = 0)
    (hG_sph : ∀ ζ ∈ Metric.sphere w δ, G ζ ≠ 0)
    (happrox : ∀ ζ ∈ Metric.sphere w δ, ‖F ζ - G ζ‖ < ‖G ζ‖ / 2) :
    ∃ z ∈ Metric.ball w δ, F z = 0 := by
  by_contra hno_ex
  have hno : ∀ z ∈ Metric.ball w δ, F z ≠ 0 := fun z hz h0 => hno_ex ⟨z, hz, h0⟩
  have hF_sph : ∀ ζ ∈ Metric.sphere w δ, ‖G ζ‖ / 2 < ‖F ζ‖ := by
    intro ζ hζ
    have h1 := happrox ζ hζ
    have htri := norm_sub_norm_le (G ζ) (F ζ)
    rw [norm_sub_rev] at htri
    linarith
  have hF_cb : ∀ z ∈ Metric.closedBall w δ, F z ≠ 0 := by
    intro z hz
    rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with hlt | heq
    · exact hno z (Metric.mem_ball.mpr hlt)
    · have hpos : 0 < ‖G z‖ / 2 := half_pos (norm_pos_iff.mpr (hG_sph z (Metric.mem_sphere.mpr heq)))
      exact norm_pos_iff.mp (hpos.trans (hF_sph z (Metric.mem_sphere.mpr heq)))
  have hslit : ∀ ζ ∈ Metric.sphere w δ, G ζ / F ζ ∈ Complex.slitPlane := by
    intro ζ hζ
    have hFz_pos : 0 < ‖F ζ‖ :=
      (half_pos (norm_pos_iff.mpr (hG_sph ζ hζ))).trans (hF_sph ζ hζ)
    have hFz_ne : F ζ ≠ 0 := norm_pos_iff.mp hFz_pos
    have hq : G ζ / F ζ - 1 = (G ζ - F ζ) / F ζ := by field_simp [hFz_ne]
    have hq_lt : ‖G ζ / F ζ - 1‖ < 1 := by
      rw [hq, norm_div, div_lt_one hFz_pos, norm_sub_rev]
      exact (happrox ζ hζ).trans (hF_sph ζ hζ)
    have hre_lt : |(G ζ / F ζ - 1).re| < 1 := (Complex.abs_re_le_norm _).trans_lt hq_lt
    rw [Complex.sub_re, Complex.one_re] at hre_lt
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [(abs_lt.mp hre_lt).1]))
  have hGw_ne := HTGeometry.zeroFree_ball_of_quotient_mem_slitPlane hδ (by linarith : δ < 2 * δ)
    isOpen_univ (Set.subset_univ _) hG.differentiableOn hF.differentiableOn hF_cb hslit
    w (Metric.mem_ball_self hδ)
  exact hGw_ne hGw

/-- **Persistence of arbitrarily many off-line zeros for `C^∞`-even super-polynomially decaying
theta prefixes.**
For every finite shell cutoff `N : ℕ`, every target cardinality `M : ℕ`, and every strip half-width
`R : ℝ`, there exists `κ₀ > 0` such that for all `κ ≥ κ₀`, `partitionSymThetaAmplitude N κ` has at
least `M` distinct complex zeros strictly outside `|z.re - 1 / 2| ≤ R`. -/
theorem exists_kappa_offline_zeros_partitionSym (N M : ℕ) (R : ℝ) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ {κ : ℝ}, κ₀ ≤ κ →
      ∃ S : Finset ℂ, S.card = M ∧
        ∀ z ∈ S, partitionSymThetaAmplitude N κ z = 0 ∧ R < |z.re - 1 / 2| := by
  rcases Nat.eq_zero_or_pos M with rfl | hM_pos
  · exact ⟨1, zero_lt_one, fun _ => ⟨∅, Finset.card_empty, fun _ h => absurd h (Finset.notMem_empty _)⟩⟩
  set R₀ : ℝ := max 0 R
  obtain ⟨W, hW_sub, hW_card⟩ :=
    (finiteThetaAmplitude_offline_zeros_outside_strip_infinite N R₀).exists_subset_card_eq M
  have hW_ne : W.Nonempty := Finset.card_pos.mp (hW_card ▸ hM_pos)
  let B_rad : ℝ := W.sup' hW_ne (fun w => ‖w‖) + 2
  let Z_all : Finset ℂ := (finiteThetaAmplitude_zeros_closedBall_finite N 0 B_rad).toFinset
  let P_pairs : Finset (ℂ × ℂ) := (Z_all ×ˢ Z_all).filter (fun p => p.1 ≠ p.2)
  let δ₁ : ℝ := if h : P_pairs.Nonempty then (P_pairs.inf' h (fun p => dist p.1 p.2)) / 3 else 1
  let δ₂ : ℝ := (W.inf' hW_ne (fun w => |w.re - 1 / 2| - R₀)) / 2
  let δ : ℝ := min (1 / 2) (min δ₁ δ₂)
  have hδ₁_pos : 0 < δ₁ := by
    dsimp [δ₁]
    split_ifs with h
    · refine div_pos ?_ (by norm_num)
      obtain ⟨p, hp, hp_eq⟩ := Finset.exists_mem_eq_inf' h (fun p => dist p.1 p.2)
      rw [hp_eq]
      exact dist_pos.mpr (Finset.mem_filter.mp hp).2
    · exact zero_lt_one
  have hδ₂_pos : 0 < δ₂ := by
    dsimp [δ₂]
    refine div_pos ?_ (by norm_num)
    obtain ⟨w, hw, hw_eq⟩ := Finset.exists_mem_eq_inf' hW_ne (fun w => |w.re - 1 / 2| - R₀)
    rw [hw_eq]
    exact sub_pos.mpr (hW_sub hw).2
  have hδ_pos : 0 < δ := lt_min (by norm_num) (lt_min hδ₁_pos hδ₂_pos)
  have hδ_le_half : δ ≤ 1 / 2 := min_le_left _ _
  have hδ_le_δ₁ : δ ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ_le_δ₂ : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_right _ _)
  have hw_mem_Zall : ∀ w ∈ W, w ∈ Z_all := by
    intro w hw
    apply (finiteThetaAmplitude_zeros_closedBall_finite N 0 B_rad).mem_toFinset.mpr
    refine ⟨?_, (hW_sub hw).1⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsup := Finset.le_sup' (fun u => ‖u‖) hw
    dsimp [B_rad]; linarith
  have hG_sph_nz : ∀ w ∈ W, ∀ ζ ∈ Metric.sphere w δ,
      _root_.RHTower.finiteThetaAmplitude N ζ ≠ 0 := by
    intro w hw ζ hζ h0
    have hζ_Z : ζ ∈ Z_all := by
      apply (finiteThetaAmplitude_zeros_closedBall_finite N 0 B_rad).mem_toFinset.mpr
      refine ⟨?_, h0⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have htri : ‖ζ‖ ≤ ‖w‖ + dist ζ w := by
        simpa [dist_eq_norm] using norm_add_le w (ζ - w)
      have hsup := Finset.le_sup' (fun u => ‖u‖) hw
      rw [Metric.mem_sphere.mp hζ] at htri
      dsimp [B_rad]; linarith
    have hne : ζ ≠ w := by
      intro heq
      rw [heq, Metric.mem_sphere, dist_self] at hζ
      exact hδ_pos.ne hζ.symm
    have hp_mem : (ζ, w) ∈ P_pairs :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hζ_Z, hw_mem_Zall w hw⟩, hne⟩
    have hinf_le : δ₁ ≤ dist ζ w / 3 := by
      dsimp [δ₁]; rw [dif_pos ⟨(ζ, w), hp_mem⟩]
      exact div_le_div_of_nonneg_right (Finset.inf'_le (fun p => dist p.1 p.2) hp_mem) (by norm_num)
    rw [Metric.mem_sphere.mp hζ] at hinf_le
    linarith
  -- Compact union of spheres `⋃ w ∈ W, sphere w δ`.
  let K_sph : Set ℂ := ⋃ w ∈ (W : Set ℂ), Metric.sphere w δ
  have hK_comp : IsCompact K_sph :=
    W.finite_toSet.isCompact_biUnion fun w _ => isCompact_sphere w δ
  obtain ⟨w₀, hw₀⟩ := hW_ne
  have hK_ne : K_sph.Nonempty := by
    refine ⟨w₀ + (δ : ℂ), Set.mem_iUnion₂.mpr ⟨w₀, hw₀, ?_⟩⟩
    rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hδ_pos]
  obtain ⟨ζ₀, hζ₀_mem, hζ₀_min⟩ := hK_comp.exists_isMinOn hK_ne
    (_root_.RHTower.differentiable_finiteThetaAmplitude N).continuous.norm.continuousOn
  set μ : ℝ := ‖_root_.RHTower.finiteThetaAmplitude N ζ₀‖
  have hμ_pos : 0 < μ := by
    obtain ⟨w, hw, hsph⟩ := Set.mem_iUnion₂.mp hζ₀_mem
    exact norm_pos_iff.mpr (hG_sph_nz w hw ζ₀ hsph)
  let R₁ : ℝ := B_rad + 2
  have hR₁_nn : 0 ≤ R₁ := by
    dsimp [R₁, B_rad]
    linarith [norm_nonneg w₀, Finset.le_sup' (fun u => ‖u‖) hw₀]
  have hK_strip : ∀ ζ ∈ K_sph, |ζ.re - 1 / 2| ≤ R₁ := by
    intro ζ hζ
    obtain ⟨w, hw, hsph⟩ := Set.mem_iUnion₂.mp hζ
    have htri : ‖ζ‖ ≤ ‖w‖ + δ := by
      rw [← Metric.mem_sphere.mp hsph]
      simpa [dist_eq_norm] using norm_add_le w (ζ - w)
    have hsup := Finset.le_sup' (fun u => ‖u‖) hw
    have hre := Complex.abs_re_le_norm ζ
    have hsub := abs_sub ζ.re (1 / 2 : ℝ)
    norm_num at hsub
    dsimp [R₁, B_rad]; linarith
  let K_c : ℝ := (Real.exp 3 * thetaCuspSeedHalfGaussConst / Real.pi) +
    (1 / 2 : ℝ) * _root_.RHTower.thetaCuspTiltDecayConstant (R₁ + 1)
  have hK_c_pos : 0 < K_c := by
    dsimp [K_c]
    have h1 : 0 < Real.exp 3 * thetaCuspSeedHalfGaussConst / Real.pi := by
      positivity [thetaCuspSeedHalfGaussConst_pos]
    have h2 : 0 < _root_.RHTower.thetaCuspTiltDecayConstant (R₁ + 1) :=
      _root_.RHTower.thetaCuspTiltDecayConstant_pos _
    linarith
  let κ₀ : ℝ := max (max 1 ((R₁ + 2) ^ 2)) (2 * Real.pi * (2 * K_c / μ + 1) ^ 2)
  have hκ₀_pos : 0 < κ₀ := lt_of_lt_of_le zero_lt_one
    ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨κ₀, hκ₀_pos, fun {κ} hκ => ?_⟩
  have hκ_pos : 0 < κ := hκ₀_pos.trans_le hκ
  have hκ_strip : max 1 ((R₁ + 2) ^ 2) ≤ κ := (le_max_left _ _).trans hκ
  have hκ_err : K_c * Real.sqrt (2 * Real.pi / κ) < μ / 2 := by
    have hκ_ge : 2 * Real.pi * (2 * K_c / μ + 1) ^ 2 ≤ κ := (le_max_right _ _).trans hκ
    have hdiv_le : 2 * Real.pi / κ ≤ 1 / (2 * K_c / μ + 1) ^ 2 := by
      rw [div_le_div_iff₀ hκ_pos (by positivity)]
      linarith
    have hsqrt_le : Real.sqrt (2 * Real.pi / κ) ≤ 1 / (2 * K_c / μ + 1) := by
      have h1 := Real.sqrt_le_sqrt hdiv_le
      rwa [Real.sqrt_div zero_le_one, Real.sqrt_one, Real.sqrt_sq (by positivity)] at h1
    have hlt_inv : 1 / (2 * K_c / μ + 1) < μ / (2 * K_c) := by
      have h1 : 1 / (2 * K_c / μ + 1) < 1 / (2 * K_c / μ) :=
        one_div_lt_one_div_of_lt (by positivity) (by linarith)
      rwa [one_div_div] at h1
    calc K_c * Real.sqrt (2 * Real.pi / κ)
        ≤ K_c * (1 / (2 * K_c / μ + 1)) := mul_le_mul_of_nonneg_left hsqrt_le hK_c_pos.le
      _ < K_c * (μ / (2 * K_c)) := mul_lt_mul_of_pos_left hlt_inv hK_c_pos
      _ = μ / 2 := by field_simp [hK_c_pos.ne']
  -- Capture one root of `partitionSymThetaAmplitude N κ` inside each disjoint disc `ball w δ`.
  have hcapture : ∀ w ∈ W, ∃ z ∈ Metric.ball w δ, partitionSymThetaAmplitude N κ z = 0 := by
    intro w hw
    refine exists_zero_in_ball_of_sphere_half_bound hδ_pos
      (differentiable_partitionSymThetaAmplitude N hκ_pos)
      (_root_.RHTower.differentiable_finiteThetaAmplitude N)
      (hW_sub hw).1 (hG_sph_nz w hw) fun ζ hζ => ?_
    have hζ_mem : ζ ∈ K_sph := Set.mem_iUnion₂.mpr ⟨w, hw, hζ⟩
    have hmin_ζ : μ ≤ ‖_root_.RHTower.finiteThetaAmplitude N ζ‖ :=
      isMinOn_iff.mp hζ₀_min ζ hζ_mem
    have hbd := norm_partitionSymThetaAmplitude_sub_finite_le_strip N hR₁_nn hκ_strip
      (hK_strip ζ hζ_mem)
    exact (hbd.trans_lt hκ_err).trans_le (by linarith)
  let pick : ℂ → ℂ := fun w => if hw : w ∈ W then (hcapture w hw).choose else 0
  have hpick_spec : ∀ w ∈ W,
      pick w ∈ Metric.ball w δ ∧ partitionSymThetaAmplitude N κ (pick w) = 0 := by
    intro w hw
    dsimp [pick]; rw [dif_pos hw]
    exact (hcapture w hw).choose_spec
  have hpick_inj : Set.InjOn pick W := by
    intro w₁ hw₁ w₂ hw₂ heq
    by_contra hne
    have hp_mem : (w₁, w₂) ∈ P_pairs :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hw_mem_Zall w₁ hw₁, hw_mem_Zall w₂ hw₂⟩, hne⟩
    have hsep : 3 * δ₁ ≤ dist w₁ w₂ := by
      have h1 : δ₁ ≤ dist w₁ w₂ / 3 := by
        dsimp [δ₁]; rw [dif_pos ⟨(w₁, w₂), hp_mem⟩]
        exact div_le_div_of_nonneg_right
          (Finset.inf'_le (fun p => dist p.1 p.2) hp_mem) (by norm_num)
      linarith
    have hb₁ : dist (pick w₁) w₁ < δ := Metric.mem_ball.mp (hpick_spec w₁ hw₁).1
    have hb₂ : dist (pick w₂) w₂ < δ := Metric.mem_ball.mp (hpick_spec w₂ hw₂).1
    rw [heq] at hb₁
    have htri := dist_triangle_left w₁ w₂ (pick w₂)
    linarith [hδ_le_δ₁]
  refine ⟨W.image pick, (Finset.card_image_of_injOn hpick_inj).trans hW_card, fun z hz => ?_⟩
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
  refine ⟨(hpick_spec w hw).2, ?_⟩
  have hb : dist (pick w) w < δ := Metric.mem_ball.mp (hpick_spec w hw).1
  have hre_diff : |(pick w).re - w.re| < δ := by
    rw [dist_eq_norm] at hb
    exact lt_of_le_of_lt (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (pick w - w)) hb
  have hw_out : 2 * δ₂ ≤ |w.re - 1 / 2| - R₀ := by
    have hinf := Finset.inf'_le (fun u => |u.re - 1 / 2| - R₀) hw
    dsimp [δ₂]; linarith
  have htri_re : |w.re - 1 / 2| - |(pick w).re - w.re| ≤ |(pick w).re - 1 / 2| := by
    have h1 := abs_add_le ((pick w).re - 1 / 2) (w.re - (pick w).re)
    have h2 : ((pick w).re - 1 / 2) + (w.re - (pick w).re) = w.re - 1 / 2 := by ring
    have h3 : |w.re - (pick w).re| = |(pick w).re - w.re| := abs_sub_comm _ _
    rw [h2, h3] at h1; linarith
  have hR_le_R₀ : R ≤ R₀ := le_max_right 0 R
  linarith [hδ_le_δ₂, hδ_pos]

/-- **Failure of Laguerre–Pólya / Hermite–Biehler critical-line purity for `C^∞`-even
Gaussian-partitioned Poisson–Jacobi prefixes (`κ ≥ κ₁`).** -/
theorem exists_kappa_not_laguerrePolya_partitionSym (N : ℕ) :
    ∃ κ₁ : ℝ, 0 < κ₁ ∧ ∀ {κ : ℝ}, κ₁ ≤ κ →
      ¬ HTGeometry.LaguerrePolya
        (fun z : ℂ => partitionSymThetaAmplitude N κ ((1 / 2 : ℂ) + I * z)) := by
  obtain ⟨κ₀, hκ₀_pos, hcap⟩ := exists_kappa_offline_zeros_partitionSym N 1 0
  let c₀ : ℝ := (5026 / 16875) * Real.exp (-Real.pi)
  have hc₀_pos : 0 < c₀ := by dsimp [c₀]; positivity
  let K_0 : ℝ := (Real.exp 3 * thetaCuspSeedHalfGaussConst / Real.pi) +
    (1 / 2 : ℝ) * _root_.RHTower.thetaCuspTiltDecayConstant 1
  have hK_0_pos : 0 < K_0 := by
    dsimp [K_0]
    have h1 : 0 < Real.exp 3 * thetaCuspSeedHalfGaussConst / Real.pi := by
      positivity [thetaCuspSeedHalfGaussConst_pos]
    have h2 : 0 < _root_.RHTower.thetaCuspTiltDecayConstant 1 :=
      _root_.RHTower.thetaCuspTiltDecayConstant_pos 1
    linarith
  let κ₁ : ℝ := max κ₀ (max 4 (2 * Real.pi * (2 * K_0 / c₀ + 1) ^ 2))
  have hκ₁_pos : 0 < κ₁ := hκ₀_pos.trans_le (le_max_left _ _)
  refine ⟨κ₁, hκ₁_pos, fun {κ} hκ hLP => ?_⟩
  have hκ_pos : 0 < κ := hκ₁_pos.trans_le hκ
  obtain ⟨S, hS_card, hS_spec⟩ := hcap ((le_max_left _ _).trans hκ)
  obtain ⟨w, hw_S⟩ := Finset.card_pos.mp (hS_card ▸ Nat.one_pos)
  obtain ⟨hw_zero, hw_off⟩ := hS_spec w hw_S
  -- Show `partitionSymThetaAmplitude N κ (1 / 2) ≠ 0` so the function is not identically zero.
  have hhalf_ne : partitionSymThetaAmplitude N κ ((1 / 2 : ℂ) + I * 0) ≠ 0 := by
    rw [mul_zero, add_zero]
    intro h0
    have hfin_ge : c₀ ≤ ‖_root_.RHTower.finiteThetaAmplitude N (1 / 2 : ℂ)‖ := by
      have hre := finiteThetaAmplitude_re_ge_lowWindow N (z := (1 / 2 : ℂ))
        (by simp; norm_num) (by simp; norm_num)
      exact hre.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    have hκ4 : max 1 ((0 + 2 : ℝ) ^ 2) ≤ κ := by
      have h4 : (4 : ℝ) ≤ κ := (le_max_left _ _).trans ((le_max_right _ _).trans hκ)
      norm_num; exact h4
    have hbd := norm_partitionSymThetaAmplitude_sub_finite_le_strip N (le_rfl : (0 : ℝ) ≤ 0) hκ4
      (z := (1 / 2 : ℂ)) (by simp)
    rw [zero_add] at hbd
    have hκ_ge : 2 * Real.pi * (2 * K_0 / c₀ + 1) ^ 2 ≤ κ :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hκ)
    have hdiv_le : 2 * Real.pi / κ ≤ 1 / (2 * K_0 / c₀ + 1) ^ 2 := by
      rw [div_le_div_iff₀ hκ_pos (by positivity)]; linarith
    have hsqrt_le : Real.sqrt (2 * Real.pi / κ) ≤ 1 / (2 * K_0 / c₀ + 1) := by
      have h1 := Real.sqrt_le_sqrt hdiv_le
      rwa [Real.sqrt_div zero_le_one, Real.sqrt_one, Real.sqrt_sq (by positivity)] at h1
    have hlt_inv : 1 / (2 * K_0 / c₀ + 1) < c₀ / (2 * K_0) := by
      have h1 : 1 / (2 * K_0 / c₀ + 1) < 1 / (2 * K_0 / c₀) :=
        one_div_lt_one_div_of_lt (by positivity) (by linarith)
      rwa [one_div_div] at h1
    have herr_lt : K_0 * Real.sqrt (2 * Real.pi / κ) < c₀ / 2 := by
      calc K_0 * Real.sqrt (2 * Real.pi / κ)
          ≤ K_0 * (1 / (2 * K_0 / c₀ + 1)) := mul_le_mul_of_nonneg_left hsqrt_le hK_0_pos.le
        _ < K_0 * (c₀ / (2 * K_0)) := mul_lt_mul_of_pos_left hlt_inv hK_0_pos
        _ = c₀ / 2 := by field_simp [hK_0_pos.ne']
    rw [h0, zero_sub, norm_neg] at hbd
    linarith [hbd.trans_lt herr_lt]
  set z₀ : ℂ := -I * (w - (1 / 2 : ℂ))
  have hw_eq : (1 / 2 : ℂ) + I * z₀ = w := by
    dsimp [z₀]; rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul, add_sub_cancel]
  have hz₀_zero : partitionSymThetaAmplitude N κ ((1 / 2 : ℂ) + I * z₀) = 0 := by
    rw [hw_eq]; exact hw_zero
  have him0 := HTGeometry.im_eq_zero_of_laguerrePolya hLP hhalf_ne hz₀_zero
  have hz₀_im : z₀.im = -(w.re - 1 / 2) := by
    dsimp [z₀]; simp [Complex.mul_im, Complex.sub_re]
  rw [hz₀_im] at him0
  have hre0 : |w.re - 1 / 2| = 0 := by rw [abs_eq_zero]; linarith
  linarith [hw_off]

end GaloisForLFunctions.ConjugateDiagonalGeometry

end

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.finiteThetaAmplitude_offline_zeros_outside_strip_infinite
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.not_laguerrePolya_finiteThetaAmplitude_criticalLine
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.gaussMollifiedThetaAmplitude_eq
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.gaussMollifiedThetaAmplitude_superpolynomial_strip_decay
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.gaussMollifiedCollisionOperator_eq
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.iteratedDeriv_odd_partitionSymThetaSource_zero
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.partitionSymThetaAmplitude_superpolynomial_strip_decay
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.partitionSymCollisionOperator_eventually_eq_charge
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_kappa_offline_zeros_partitionSym
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_kappa_not_laguerrePolya_partitionSym



