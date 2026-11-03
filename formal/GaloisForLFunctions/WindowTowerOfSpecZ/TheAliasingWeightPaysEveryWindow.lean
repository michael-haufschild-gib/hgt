import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheWindowDatum
import GaloisForLFunctions.HTGeometry.RealDirichletSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# An aperture-independent weighted floor for Weil's form

On the negative half-line, the weight `exp(-p u)` makes a shift by `t ≥ 0`
cost at most `exp(-p t/2)`. For `p > 1` the resulting prime series converges
and both pole moments are bounded. The nonnegative archimedean jump energy
then gives a lower bound independent of the length of the window.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole

/-- The exponential mass read by the aliasing form. -/
def exponentialMass (p : ℝ) (H : ℝ → ℝ) : ℝ :=
  ∫ u, Real.exp (-(p * u)) * H u ^ 2

theorem exponentialMass_nonneg (p : ℝ) (H : ℝ → ℝ) :
    0 ≤ exponentialMass p H := integral_nonneg fun _ => by positivity

variable {A p t : ℝ} {H : ℝ → ℝ}

theorem integrable_exponentialMass (hH : IsWindowTest A H) (p : ℝ) :
    Integrable fun u => Real.exp (-(p * u)) * H u ^ 2 := by
  have hHc := hH.continuous
  have hc : Continuous fun u => Real.exp (-(p * u)) * H u ^ 2 := by
    fun_prop
  exact hc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -A) (b := 0))
      fun u hu => by simp [hH.vanish u hu])

theorem integral_sq_le_exponentialMass (hH : IsWindowTest A H) (hp : 0 ≤ p) :
    (∫ u, H u ^ 2) ≤ exponentialMass p H := by
  apply integral_mono (integrable_sq hH.continuous hH.hasCompactSupport)
    (integrable_exponentialMass hH p)
  intro u
  by_cases hu : u ∈ Icc (-A) 0
  · have he : 1 ≤ Real.exp (-(p * u)) := Real.one_le_exp (by nlinarith only [hp, hu.2])
    exact le_mul_of_one_le_left (sq_nonneg _) he
  · simp [hH.vanish u hu]

private theorem exp_sq (x : ℝ) : Real.exp x ^ 2 = Real.exp (2 * x) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- Conjugating a shift by the exponential weight gives decay in its length. -/
theorem abs_correlation_le_exponentialMass (hH : IsWindowTest A H) (hp : 0 ≤ p)
    (_ht : 0 ≤ t) :
    |∫ u, H u * H (u + t)| ≤ Real.exp (-(p * t) / 2) * exponentialMass p H := by
  have hpt : ∀ u, 2 * |H u * H (u + t)| ≤ Real.exp (-(p * t) / 2) *
      (Real.exp (-(p * u)) * H u ^ 2 +
        Real.exp (-(p * (u + t))) * H (u + t) ^ 2) := by
    intro u
    by_cases hz : H u * H (u + t) = 0
    · rw [hz, abs_zero, mul_zero]
      positivity
    have hut : u + t ≤ 0 := by
      by_contra h
      have hv := hH.vanish (u + t) (fun hm => h hm.2)
      exact hz (by rw [hv, mul_zero])
    have hu : u ≤ -t := by linarith only [hut]
    have he1 : Real.exp (p * t / 2) ≤
        Real.exp (-(p * t) / 2) * Real.exp (-(p * u)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hp (sub_nonneg.mpr hu)]
    have he2 : Real.exp (-(p * t) / 2) ≤
        Real.exp (-(p * t) / 2) * Real.exp (-(p * (u + t))) := by
      apply le_mul_of_one_le_right (Real.exp_pos _).le
      exact Real.one_le_exp (by nlinarith only [hp, hut])
    have hs := sq_nonneg
      (Real.exp (p * t / 4) * |H u| - Real.exp (-(p * t) / 4) * |H (u + t)|)
    have he : Real.exp (p * t / 4) * Real.exp (-(p * t) / 4) = 1 := by
      rw [← Real.exp_add, show p * t / 4 + -(p * t) / 4 = 0 by ring, Real.exp_zero]
    have hsq1 : Real.exp (p * t / 4) ^ 2 = Real.exp (p * t / 2) := by
      rw [exp_sq]; congr 1; ring
    have hsq2 : Real.exp (-(p * t) / 4) ^ 2 = Real.exp (-(p * t) / 2) := by
      rw [exp_sq]; congr 1; ring
    have hyoung : 2 * |H u * H (u + t)| ≤
        Real.exp (p * t / 2) * H u ^ 2 + Real.exp (-(p * t) / 2) * H (u + t) ^ 2 := by
      rw [abs_mul]
      rw [sub_sq, mul_pow, mul_pow, hsq1, hsq2, sq_abs, sq_abs] at hs
      have hc : 2 * (Real.exp (p * t / 4) * |H u|) *
          (Real.exp (-(p * t) / 4) * |H (u + t)|) = 2 * |H u| * |H (u + t)| := by
        linear_combination (2 * |H u| * |H (u + t)|) * he
      linarith only [hs, hc]
    have h1 := mul_le_mul_of_nonneg_right he1 (sq_nonneg (H u))
    have h2 := mul_le_mul_of_nonneg_right he2 (sq_nonneg (H (u + t)))
    nlinarith only [hyoung, h1, h2]
  have iE := integrable_exponentialMass hH p
  have iEt : Integrable fun u => Real.exp (-(p * (u + t))) * H (u + t) ^ 2 :=
    iE.comp_add_right t
  have hi := integral_mono ((integrable_mul_shift hH.continuous hH.hasCompactSupport t).abs.const_mul 2)
    ((iE.add iEt).const_mul (Real.exp (-(p * t) / 2))) hpt
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_const_mul, integral_add iE iEt,
    integral_add_right_eq_self (fun u => Real.exp (-(p * u)) * H u ^ 2) t] at hi
  calc |∫ u, H u * H (u + t)| ≤ ∫ u, |H u * H (u + t)| := abs_integral_le_integral_abs
    _ ≤ Real.exp (-(p * t) / 2) * exponentialMass p H := by
      unfold exponentialMass
      linarith only [hi]

/-- Weighted Cauchy–Schwarz for a Laplace moment on the negative half-line. -/
theorem laplaceMoment_sq_le_exponentialMass (hH : IsWindowTest A H) {q : ℝ}
    (hpq : 0 < p + 2 * q) :
    (∫ u, H u * Real.exp (q * u)) ^ 2 ≤ exponentialMass p H / (p + 2 * q) := by
  let G : ℝ → ℝ := fun u => Real.exp (-(p * u) / 2) * H u
  let B : ℝ → ℝ := (Iic (0 : ℝ)).indicator fun u => Real.exp ((p + 2 * q) * u / 2)
  have hG : ∀ u, G u ^ 2 = Real.exp (-(p * u)) * H u ^ 2 := by
    intro u
    dsimp only [G]
    rw [mul_pow, exp_sq, show 2 * (-(p * u) / 2) = -(p * u) by ring]
  have hB : ∀ u, B u ^ 2 = (Iic (0 : ℝ)).indicator
      (fun u => Real.exp ((p + 2 * q) * u)) u := by
    intro u
    by_cases hu : u ∈ Iic (0 : ℝ)
    · simp only [B, indicator_of_mem hu]
      rw [exp_sq]
      congr 1
      ring
    · simp [B, hu]
  have hGB : ∀ u, G u * B u = H u * Real.exp (q * u) := by
    intro u
    by_cases hu : u ∈ Iic (0 : ℝ)
    · simp only [G, B, indicator_of_mem hu]
      rw [mul_right_comm, ← Real.exp_add, mul_comm]
      congr 1
      congr 1
      ring
    · have hv : H u = 0 := hH.vanish u (fun hm => hu hm.2)
      simp [G, B, hu, hv]
  have iG : Integrable fun u => G u ^ 2 := by
    simpa only [hG] using integrable_exponentialMass hH p
  have iB : Integrable fun u => B u ^ 2 := by
    simp_rw [hB]
    exact (integrable_indicator_iff measurableSet_Iic).mpr (integrableOn_exp_mul_Iic hpq 0)
  have iGB : Integrable fun u => G u * B u := by
    simp_rw [hGB]
    exact (hH.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      hH.hasCompactSupport.mul_right
  have hnormB : (∫ u, B u ^ 2) = 1 / (p + 2 * q) := by
    simp_rw [hB]
    rw [integral_indicator measurableSet_Iic, integral_exp_mul_Iic hpq 0]
    simp only [mul_zero, Real.exp_zero]
  have hcs := abs_integral_mul_le iG iB iGB
  have hs := pow_le_pow_left₀ (abs_nonneg _) hcs 2
  rw [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg fun u => sq_nonneg (G u)),
    Real.sq_sqrt (integral_nonneg fun u => sq_nonneg (B u)), hnormB] at hs
  simpa only [hGB, hG, exponentialMass, div_eq_mul_inv, one_mul] using hs

/-- Both pole moments have an aperture-independent weighted bound. -/
theorem pole_ge_neg_exponentialMass (hH : IsWindowTest A H) (hp : 1 < p) :
    -((1 / (p + 1) + 1 / (p - 1)) * exponentialMass p H) ≤
      coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2 := by
  have hplus := laplaceMoment_sq_le_exponentialMass (p := p) hH
    (q := 1 / 2) (by linarith)
  have hminus := laplaceMoment_sq_le_exponentialMass (p := p) hH
    (q := -(1 / 2)) (by linarith)
  have ep : (fun u : ℝ => H u * Real.exp (1 / 2 * u)) = fun u => H u * Real.exp (u / 2) := by
    funext u; congr 2; ring
  have em : (fun u : ℝ => H u * Real.exp (-(1 / 2) * u)) = fun u => H u * Real.exp (-u / 2) := by
    funext u; congr 2; ring
  rw [ep, show p + 2 * (1 / 2) = p + 1 by ring] at hplus
  rw [em, show p + 2 * (-(1 / 2)) = p - 1 by ring] at hminus
  rw [← pole_eq_pairings H hH.continuous hH.hasCompactSupport]
  have hs := sq_nonneg ((∫ u, H u * Real.exp (u / 2)) + ∫ u, H u * Real.exp (-u / 2))
  simp only [div_eq_mul_inv] at hs hplus hminus ⊢
  nlinarith only [hs, hplus, hminus]

/-- The prime mass after conjugating by the aliasing weight. -/
def exponentialPrimeMass (p : ℝ) : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-((p + 1) / 2))

theorem exponentialPrimeMass_nonneg (p : ℝ) : 0 ≤ exponentialPrimeMass p :=
  tsum_nonneg fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

private theorem primeJumpWeight_mul_exp (p : ℝ) {n : ℕ} (hn : 0 < n) :
    primeJumpWeight n * Real.exp (-(p * Real.log n) / 2) =
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-((p + 1) / 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [primeJumpWeight, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0,
    Real.rpow_def_of_pos hn0, div_eq_mul_inv, ← Real.exp_neg,
    mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The full prime debit is bounded independently of the window level. -/
theorem prime_correlation_sum_le_exponentialMass (hH : IsWindowTest A H) (hp : 1 < p)
    (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, primeJumpWeight n * (∫ u, H u * H (u + Real.log n))) ≤
      exponentialPrimeMass p * exponentialMass p H := by
  have hterm : ∀ n ∈ Finset.Icc 2 N,
      primeJumpWeight n * (∫ u, H u * H (u + Real.log n)) ≤
        ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-((p + 1) / 2))) *
          exponentialMass p H := by
    intro n hn
    have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hn).1
    have h := abs_correlation_le_exponentialMass hH (by linarith) (Real.log_natCast_nonneg n)
    calc primeJumpWeight n * (∫ u, H u * H (u + Real.log n)) ≤
          primeJumpWeight n * |∫ u, H u * H (u + Real.log n)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (primeJumpWeight_nonneg n)
      _ ≤ primeJumpWeight n * (Real.exp (-(p * Real.log n) / 2) * exponentialMass p H) :=
        mul_le_mul_of_nonneg_left h (primeJumpWeight_nonneg n)
      _ = _ := by rw [← mul_assoc, primeJumpWeight_mul_exp p hn0]
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum
  have hs := HTGeometry.summable_vonMangoldt_rpow (σ := (p + 1) / 2) (by linarith)
  have hle : (∑ n ∈ Finset.Icc 2 N,
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-((p + 1) / 2))) ≤
      exponentialPrimeMass p := by
    exact hs.sum_le_tsum (Finset.Icc 2 N) fun n _ =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  exact hsum.trans (mul_le_mul_of_nonneg_right hle (exponentialMass_nonneg p H))

/-- A finite Markov form consists of its diagonal, its nonnegative archimedean
jumps, and the signed prime correlations. -/
private theorem markovForm_eq_correlations (hH : IsWindowTest A H) (N : ℕ) :
    markovForm N H = EF.gammaBracket 0 * (∫ u, H u ^ 2) + levyJump H -
      2 * ∑ n ∈ Finset.Icc 2 N, primeJumpWeight n * (∫ u, H u * H (u + Real.log n)) := by
  have h0 : RHTower.ArchimedeanAnomaly.autocorr H 0 = ∫ u, H u ^ 2 := by
    unfold RHTower.ArchimedeanAnomaly.autocorr
    congr 1
    funext u
    rw [add_zero, sq]
  have hprime : ∀ n, primeJumpWeight n * ∫ u, (H u - H (u + Real.log n)) ^ 2 =
      (2 * primeJumpWeight n) * (∫ u, H u ^ 2) -
        2 * (primeJumpWeight n * ∫ u, H u * H (u + Real.log n)) := by
    intro n
    rw [RHTower.ArchimedeanAnomaly.integral_sub_shift_sq hH.hasCompactSupport hH.continuous, h0]
    unfold RHTower.ArchimedeanAnomaly.autocorr
    ring
  rw [markovForm, creationPotential, primeJump]
  simp_rw [hprime]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- An explicit floor constant, independent of the aperture. -/
def exponentialWeilFloor (p : ℝ) : ℝ :=
  |EF.gammaBracket 0| + 2 * exponentialPrimeMass p + 1 / (p + 1) + 1 / (p - 1)

theorem exponentialWeilFloor_pos (hp : 1 < p) : 0 < exponentialWeilFloor p := by
  have hs := exponentialPrimeMass_nonneg p
  unfold exponentialWeilFloor
  have hp1 : 0 < p - 1 := by linarith
  have hp2 : 0 < p + 1 := by linarith
  positivity

/-- **Aperture-independent weighted Weil floor.** For every `p > 1`, the same
constant bounds the complete form on every window of the negative half-line. -/
theorem weilQuad_ge_neg_exponentialMass (hH : IsWindowTest A H) (hp : 1 < p) :
    -(exponentialWeilFloor p * exponentialMass p H) ≤ weilQuad H := by
  have hmass := integral_sq_le_exponentialMass hH (by linarith : 0 ≤ p)
  have hdiag : -(|EF.gammaBracket 0| * exponentialMass p H) ≤
      EF.gammaBracket 0 * (∫ u, H u ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_right (neg_abs_le (EF.gammaBracket 0))
      (integral_nonneg (μ := volume) fun u => sq_nonneg (H u))
    have h2 := mul_le_mul_of_nonneg_left hmass (abs_nonneg (EF.gammaBracket 0))
    linarith only [h1, h2]
  have hprime := prime_correlation_sum_le_exponentialMass hH hp (windowLevel A)
  have hpole := pole_ge_neg_exponentialMass hH hp
  have hjump : 0 ≤ levyJump H := ENNReal.toReal_nonneg
  rw [weilQuad_eq_markovForm_windowLevel hH, markovForm_eq_correlations hH, exponentialWeilFloor]
  nlinarith only [hdiag, hprime, hpole, hjump]

/-- One weighted pencil is positive on every aperture when its coefficient
strictly exceeds the same fixed floor. -/
theorem weighted_pencil_ge (hH : IsWindowTest A H) (hp : 1 < p) {κ c : ℝ} (hκ : 0 ≤ κ) :
    (c - κ * exponentialWeilFloor p) * exponentialMass p H ≤
      κ * weilQuad H + c * exponentialMass p H := by
  have h := mul_le_mul_of_nonneg_left (weilQuad_ge_neg_exponentialMass hH hp) hκ
  linarith only [h]

end GaloisForLFunctions.WindowTowerOfSpecZ
