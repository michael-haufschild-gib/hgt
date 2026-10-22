import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeSource
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Joint shell-frequency boundary layer of the literal theta source

The squared shell index is the natural frequency scale. In the exact
incomplete-Gamma coordinate `v = (n+1)^2 + u`, the normalized amplitude and
phase converge to `2π² exp(-πu)` and `u/2`. Polynomial domination transfers
every fixed frequency jet. This is the analytic input for the moving-cutoff
first-Laguerre transition; it does not assert that transition by itself.
-/

open Real Complex MeasureTheory Set Filter Topology

namespace RHTower
noncomputable section

def thetaMovingShellScale (n : ℕ) : ℝ := ((n : ℝ) + 1)^2

def thetaMovingShellGammaPhase (n : ℕ) (u : ℝ) : ℝ :=
  thetaMovingShellScale n * Real.log (1 + u / thetaMovingShellScale n) / 2

def thetaMovingShellGammaAmplitude (n : ℕ) (u : ℝ) : ℝ :=
  Real.pi * Real.exp (Real.log (1 + u / thetaMovingShellScale n) / 4) *
    (2 * Real.pi * (1 + u / thetaMovingShellScale n) - 3 / thetaMovingShellScale n) *
      Real.exp (-Real.pi * u)

def thetaMovingShellGammaJetIntegrand (n k : ℕ) (lambda u : ℝ) : ℂ :=
  (thetaMovingShellGammaAmplitude n u : ℂ) *
    (Complex.I * (thetaMovingShellGammaPhase n u : ℂ))^k *
      Complex.exp (Complex.I * (lambda : ℂ) * (thetaMovingShellGammaPhase n u : ℂ))

def thetaMovingShellGammaJet (n k : ℕ) (lambda : ℝ) : ℂ :=
  ∫ u : ℝ in Ioi 0, thetaMovingShellGammaJetIntegrand n k lambda u

theorem one_le_thetaMovingShellScale (n : ℕ) : 1 ≤ thetaMovingShellScale n := by
  unfold thetaMovingShellScale
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem thetaMovingShellScale_pos (n : ℕ) : 0 < thetaMovingShellScale n :=
  lt_of_lt_of_le zero_lt_one (one_le_thetaMovingShellScale n)

theorem tendsto_thetaMovingShellScale :
    Tendsto thetaMovingShellScale atTop atTop := by
  exact (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem tendsto_thetaMovingShellGammaPhase (u : ℝ) :
    Tendsto (fun n => thetaMovingShellGammaPhase n u) atTop (𝓝 (u / 2)) := by
  exact (Real.tendsto_mul_log_one_add_div_atTop u).comp
    tendsto_thetaMovingShellScale |>.div_const 2

theorem tendsto_thetaMovingShellGammaAmplitude (u : ℝ) :
    Tendsto (fun n => thetaMovingShellGammaAmplitude n u) atTop
      (𝓝 (2 * Real.pi^2 * Real.exp (-Real.pi * u))) := by
  have hu : Tendsto (fun n => u / thetaMovingShellScale n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_thetaMovingShellScale
  have hthree : Tendsto (fun n => 3 / thetaMovingShellScale n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_thetaMovingShellScale
  have hbase : Tendsto (fun n => 1 + u / thetaMovingShellScale n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hu
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp
    ((hbase.log (by exact one_ne_zero)).div_const 4)
  have hpoly := (hbase.const_mul (2 * Real.pi)).sub hthree
  have hlim := ((hexp.const_mul Real.pi).mul hpoly).mul_const (Real.exp (-Real.pi*u))
  convert hlim using 1
  · rfl
  · simp
    ring

theorem thetaMovingShellGammaPhase_nonneg (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ thetaMovingShellGammaPhase n u := by
  unfold thetaMovingShellGammaPhase
  have ha := thetaMovingShellScale_pos n
  have hlog : 0 ≤ Real.log (1 + u / thetaMovingShellScale n) :=
    Real.log_nonneg (le_add_of_nonneg_right (div_nonneg hu ha.le))
  positivity

theorem thetaMovingShellGammaPhase_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    thetaMovingShellGammaPhase n u ≤ u / 2 := by
  have ha := thetaMovingShellScale_pos n
  have hlog := Real.log_le_sub_one_of_pos
    (show 0 < 1 + u / thetaMovingShellScale n by positivity)
  have hb : Real.log (1 + u / thetaMovingShellScale n) ≤ u / thetaMovingShellScale n := by
    linarith
  unfold thetaMovingShellGammaPhase
  have hm := mul_le_mul_of_nonneg_left hb ha.le
  rw [mul_div_cancel₀ _ ha.ne'] at hm
  linarith

theorem abs_thetaMovingShellGammaAmplitude_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |thetaMovingShellGammaAmplitude n u| ≤
      (Real.pi * (2 * Real.pi + 3)) * (1 + u)^2 * Real.exp (-Real.pi*u) := by
  have ha := thetaMovingShellScale_pos n
  have ha1 := one_le_thetaMovingShellScale n
  have hr0 : 0 ≤ u / thetaMovingShellScale n := div_nonneg hu ha.le
  have hr : 1 + u / thetaMovingShellScale n ≤ 1 + u := by
    have := (div_le_self hu ha1)
    linarith
  have hrpos : 0 < 1 + u / thetaMovingShellScale n := by positivity
  have hlog := Real.log_nonneg (le_add_of_nonneg_right hr0)
  have hexp : Real.exp (Real.log (1 + u / thetaMovingShellScale n) / 4) ≤ 1 + u := by
    calc
      Real.exp (Real.log (1 + u / thetaMovingShellScale n) / 4)
        ≤ Real.exp (Real.log (1 + u / thetaMovingShellScale n)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 + u / thetaMovingShellScale n := Real.exp_log hrpos
      _ ≤ 1 + u := hr
  have hthree : 3 / thetaMovingShellScale n ≤ 3 := div_le_self (by positivity) ha1
  have hpoly0 : 0 ≤ 2 * Real.pi * (1 + u / thetaMovingShellScale n) -
      3 / thetaMovingShellScale n := by
    nlinarith [Real.pi_gt_three]
  have hpoly : 2 * Real.pi * (1 + u / thetaMovingShellScale n) -
      3 / thetaMovingShellScale n ≤ (2 * Real.pi + 3) * (1 + u) := by
    have := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2 * Real.pi)
    nlinarith [div_nonneg (by positivity : (0 : ℝ) ≤ 3) ha.le]
  unfold thetaMovingShellGammaAmplitude
  rw [abs_of_nonneg (by positivity)]
  have hprod := mul_le_mul hexp hpoly hpoly0 (by positivity : 0 ≤ 1 + u)
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hprod Real.pi_pos.le) (Real.exp_pos (-Real.pi*u)).le
  convert hscaled using 1 <;> first | rfl | ring

theorem norm_thetaMovingShellGammaJetIntegrand_le (n k : ℕ) (lambda : ℝ)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖thetaMovingShellGammaJetIntegrand n k lambda u‖ ≤
      (Real.pi * (2 * Real.pi + 3)) * (1 + u)^(k+2) * Real.exp (-Real.pi*u) := by
  have hphase0 := thetaMovingShellGammaPhase_nonneg n hu
  have hphase := thetaMovingShellGammaPhase_le n hu
  have hphase1 : thetaMovingShellGammaPhase n u ≤ 1 + u := by linarith
  have hpow := pow_le_pow_left₀ hphase0 hphase1 k
  have hnorm : ‖thetaMovingShellGammaJetIntegrand n k lambda u‖ =
      |thetaMovingShellGammaAmplitude n u| * (thetaMovingShellGammaPhase n u)^k := by
    simp [thetaMovingShellGammaJetIntegrand, norm_pow, Complex.norm_exp,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hphase0]
  rw [hnorm]
  have hprod := mul_le_mul (abs_thetaMovingShellGammaAmplitude_le n hu) hpow
    (pow_nonneg hphase0 k) (by positivity : 0 ≤
      (Real.pi * (2 * Real.pi + 3)) * (1 + u)^2 * Real.exp (-Real.pi*u))
  convert hprod using 1 <;> first | rfl | (rw [pow_add]; ring)

private theorem integrableOn_boundaryMajorant (k : ℕ) :
    IntegrableOn (fun u : ℝ => (Real.pi * (2 * Real.pi + 3)) *
      (1 + u)^(k+2) * Real.exp (-Real.pi*u)) (Ioi 0) := by
  have hmono (j : ℕ) : IntegrableOn (fun u : ℝ => u^j * Real.exp (-Real.pi*u))
      (Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (j : ℝ))
        (by linarith [Nat.cast_nonneg (α := ℝ) j]) (le_refl 1) Real.pi_pos)
  have hsum := integrable_finsetSum (Finset.range (k+2+1)) (fun j _ =>
    (hmono j).const_mul ((k+2).choose j : ℝ))
  have hpoly : IntegrableOn (fun u : ℝ => (1+u)^(k+2) * Real.exp (-Real.pi*u))
      (Ioi 0) := by
    rw [show (fun u : ℝ => (1+u)^(k+2) * Real.exp (-Real.pi*u)) =
      (fun u : ℝ => ∑ j ∈ Finset.range (k+2+1),
        ((k+2).choose j : ℝ) * (u^j * Real.exp (-Real.pi*u))) by
        funext u
        rw [add_comm 1 u, add_pow, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        simp only [one_pow]
        ring]
    exact hsum
  change Integrable _ (volume.restrict (Ioi (0 : ℝ)))
  simpa only [mul_assoc] using hpoly.const_mul (Real.pi * (2 * Real.pi + 3))

def thetaMovingShellJetBound (k : ℕ) : ℝ :=
  ∫ u : ℝ in Ioi 0, (Real.pi * (2 * Real.pi + 3)) *
    (1+u)^(k+2) * Real.exp (-Real.pi*u)

theorem thetaMovingShellJetBound_nonneg (k : ℕ) : 0 ≤ thetaMovingShellJetBound k := by
  unfold thetaMovingShellJetBound
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := hu.le
  positivity

theorem norm_thetaMovingShellGammaJet_le (n k : ℕ) (lambda : ℝ) :
    ‖thetaMovingShellGammaJet n k lambda‖ ≤ thetaMovingShellJetBound k := by
  apply norm_integral_le_of_norm_le (integrableOn_boundaryMajorant k)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact norm_thetaMovingShellGammaJetIntegrand_le n k lambda hu.le

theorem tendsto_thetaMovingShellGammaJetIntegrand (k : ℕ) (lambda u : ℝ) :
    Tendsto (fun n => thetaMovingShellGammaJetIntegrand n k lambda u) atTop
      (𝓝 (((2 * Real.pi^2 * Real.exp (-Real.pi*u) : ℝ) : ℂ) *
        (Complex.I * ((u/2 : ℝ) : ℂ))^k *
          Complex.exp (Complex.I * (lambda : ℂ) * ((u/2 : ℝ) : ℂ)))) := by
  have hA := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_thetaMovingShellGammaAmplitude u)
  have hq := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_thetaMovingShellGammaPhase u)
  have hpow := (hq.const_mul Complex.I).pow k
  have he := Complex.continuous_exp.continuousAt.tendsto.comp
    (hq.const_mul (Complex.I * (lambda : ℂ)))
  simpa only [thetaMovingShellGammaJetIntegrand, Function.comp_apply, mul_assoc] using
    (hA.mul hpow).mul he

theorem tendsto_thetaMovingShellGammaJet_integral (k : ℕ) (lambda : ℝ) :
    Tendsto (fun n => thetaMovingShellGammaJet n k lambda) atTop
      (𝓝 (∫ u : ℝ in Ioi 0,
        ((2 * Real.pi^2 * Real.exp (-Real.pi*u) : ℝ) : ℂ) *
          (Complex.I * ((u/2 : ℝ) : ℂ))^k *
            Complex.exp (Complex.I * (lambda : ℂ) * ((u/2 : ℝ) : ℂ)))) := by
  apply tendsto_integral_of_dominated_convergence
    (fun u : ℝ => (Real.pi * (2 * Real.pi + 3)) *
      (1+u)^(k+2) * Real.exp (-Real.pi*u))
  · intro n
    have hm : Measurable (thetaMovingShellGammaJetIntegrand n k lambda) := by
      unfold thetaMovingShellGammaJetIntegrand thetaMovingShellGammaAmplitude
        thetaMovingShellGammaPhase
      fun_prop
    exact hm.aestronglyMeasurable.restrict
  · exact integrableOn_boundaryMajorant k
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_thetaMovingShellGammaJetIntegrand_le n k lambda hu.le
  · exact Eventually.of_forall (tendsto_thetaMovingShellGammaJetIntegrand k lambda)

/-- All fixed frequency jets have one explicit rational boundary-layer limit. -/
theorem tendsto_thetaMovingShellGammaJet (k : ℕ) (lambda : ℝ) :
    Tendsto (fun n => thetaMovingShellGammaJet n k lambda) atTop
      (𝓝 (((2 * Real.pi^2 : ℝ) : ℂ) * (Complex.I / 2)^k *
        ((k.factorial : ℂ) / ((Real.pi : ℂ) - Complex.I * (lambda : ℂ) / 2)^(k+1)))) := by
  let c : ℂ := (Real.pi : ℂ) - Complex.I * (lambda : ℂ) / 2
  have hc : 0 < c.re := by simpa [c] using Real.pi_pos
  have hfun :
      (fun u : ℝ => ((2 * Real.pi^2 * Real.exp (-Real.pi*u) : ℝ) : ℂ) *
          (Complex.I * ((u/2 : ℝ) : ℂ))^k *
            Complex.exp (Complex.I * (lambda : ℂ) * ((u/2 : ℝ) : ℂ))) =
      (fun u : ℝ => (((2 * Real.pi^2 : ℝ) : ℂ) * (Complex.I / 2)^k) *
        ((u : ℂ)^k * Complex.exp (-(c * (u : ℂ))))) := by
    funext u
    have he : (Real.exp (-Real.pi*u) : ℂ) *
        Complex.exp (Complex.I * (lambda : ℂ) * ((u/2 : ℝ) : ℂ)) =
        Complex.exp (-(c * (u : ℂ))) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      dsimp [c]
      push_cast
      ring
    calc
      _ = (((2 * Real.pi^2 : ℝ) : ℂ) * (Complex.I / 2)^k) *
        ((u : ℂ)^k * ((Real.exp (-Real.pi*u) : ℂ) *
          Complex.exp (Complex.I * (lambda : ℂ) * ((u/2 : ℝ) : ℂ)))) := by
            push_cast
            simp only [mul_pow, div_pow]
            ring
      _ = _ := by rw [he]
  have hlim := tendsto_thetaMovingShellGammaJet_integral k lambda
  rw [hfun, integral_const_mul,
    GaloisForLFunctions.HTGeometry.integral_Ioi_pow_mul_cexp hc k] at hlim
  simpa only [c, mul_assoc] using hlim

end
end RHTower
