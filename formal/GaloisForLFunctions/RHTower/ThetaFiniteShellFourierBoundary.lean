import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFiniteShellSeamCancellation
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailDensityAtoms
import GaloisForLFunctions.HTGeometry.JuliaDefectLevyKhintchine
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullDerivativeExponentialMoments
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartz

/-!
# Exact Fourier boundary cancellation across finite theta shell cutoffs

Write `C_f(b) = integral_{x>0} f(x) cos(b*x) dx`. For every nonempty canonical
prefix `P_N` of the actual theta density, this module proves

* `b^(2 : ℕ) C_(P_N)(b) -> -P_N'(0) < 0`;
* `b^(2 : ℕ) C_(Phi)(b) -> 0`;
* `b^(2 : ℕ) C_(Phi-P_N)(b) -> P_N'(0) > 0`.

Thus the omitted arithmetic tail contributes the full opposite leading Fourier
term at every fixed cutoff. The proof uses exact source derivatives, Gaussian
integrability, two integrations by parts, reflection, and Riemann--Lebesgue.
No numerical moment or eigenvalue enters the proof.

These are Fourier asymptotics, not a proof of the all-degree logarithmic Hankel
inequality. In particular, a negative cosine value is not itself a negative
Hankel-form witness.
-/

open Real Set Filter Topology MeasureTheory Polynomial
open scoped BigOperators
namespace RHTower
noncomputable section

/-- Exact derivative jets of the first `N` positive integer theta shells. -/
def thetaFiniteShellJet (N k : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial k) (n+1) x

theorem hasDerivAt_thetaFiniteShellJet (N k : ℕ) (x : ℝ) :
    HasDerivAt (thetaFiniteShellJet N k) (thetaFiniteShellJet N (k+1) x) x := by
  convert HasDerivAt.sum (u := Finset.range N) (fun n _ =>
      hasDerivAt_thetaCuspPolynomialAtom (thetaCuspLogDerivativePolynomial k) (n+1) x) using 1
  all_goals first | rfl | (ext y; simp [thetaFiniteShellJet])

theorem integrableOn_thetaFiniteShellJet (N k : ℕ) :
    IntegrableOn (thetaFiniteShellJet N k) (Ioi 0) := by
  exact integrable_finsetSum _ (fun n _ =>
    integrableOn_thetaCuspPolynomialAtom_Ioi_of_pos
      (thetaCuspLogDerivativePolynomial k) (Nat.succ_pos n))

theorem thetaFiniteShellJet_tendsto_atTop_zero (N k : ℕ) :
    Tendsto (thetaFiniteShellJet N k) atTop (𝓝 0) := by
  convert tendsto_finsetSum (Finset.range N) (fun n _ =>
      thetaCuspPolynomialAtom_tendsto_atTop_zero_of_pos
        (thetaCuspLogDerivativePolynomial k) (Nat.succ_pos n)) using 1
  all_goals first | rfl | simp

theorem thetaFiniteShellJet_zero_eq (N : ℕ) :
    thetaFiniteShellJet N 0 = thetaCuspFiniteShellPrefix N := by
  funext x
  unfold thetaCuspFiniteShellPrefix
  rw [Finset.sum_range_succ']
  have hz : thetaCuspSourceTerm x 0 = 0 := by
    simp [thetaCuspSourceTerm, thetaCuspSeed]
  rw [hz, add_zero]
  unfold thetaFiniteShellJet
  apply Finset.sum_congr rfl
  intro n hn
  have h := congrFun (iteratedDeriv_thetaCuspSourceTerm_eq_polynomialAtom 0 (n+1)) x
  simpa using h.symm

theorem thetaFiniteShellJet_one_zero_pos (N : ℕ) :
    0 < thetaFiniteShellJet (N+1) 1 0 := by
  have h := (hasDerivAt_thetaFiniteShellJet (N+1) 0 0).deriv
  rw [thetaFiniteShellJet_zero_eq] at h
  rw [← h]
  exact deriv_thetaCuspFiniteShellPrefix_zero_pos (by omega)

private theorem halfLineCosine_secondIntegrationByParts
    (J : ℕ → ℝ → ℝ)
    (hD : ∀ k x, HasDerivAt (J k) (J (k+1) x) x)
    (hI : ∀ k, IntegrableOn (J k) (Ioi 0))
    (hT : ∀ k, Tendsto (J k) atTop (𝓝 0)) (b : ℝ) :
    b ^ (2 : ℕ) * (∫ x : ℝ in Ioi 0,
      (J 0) x * Real.cos (b * x)) =
      -(J 1) 0 -
        ∫ x : ℝ in Ioi 0,
          (J 2) x * Real.cos (b * x) := by
  have hcos (x : ℝ) : HasDerivAt (fun y : ℝ => Real.cos (b * y))
      (-b * Real.sin (b * x)) x := by
    have h := (Real.hasDerivAt_cos (b * x)).comp x
      ((hasDerivAt_id x).const_mul b)
    convert h using 1
    all_goals try rfl
    ring
  have hsin (x : ℝ) : HasDerivAt (fun y : ℝ => -b * Real.sin (b * y))
      (-b ^ (2 : ℕ) * Real.cos (b * x)) x := by
    have h := ((Real.hasDerivAt_sin (b * x)).comp x
      ((hasDerivAt_id x).const_mul b)).const_mul (-b)
    convert h using 1
    all_goals try rfl
    ring
  have hcosCurv : IntegrableOn (fun x : ℝ =>
      Real.cos (b * x) * (J 2) x) (Ioi 0) := by
    apply Integrable.bdd_mul (hI 2)
    · exact (by fun_prop : Continuous (fun x : ℝ => Real.cos (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs]
      exact abs_cos_le_one _
  have hsinSlope : IntegrableOn (fun x : ℝ =>
      (-b * Real.sin (b * x)) * (J 1) x) (Ioi 0) := by
    apply Integrable.bdd_mul (hI 1)
    · exact (by fun_prop : Continuous (fun x : ℝ => -b * Real.sin (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg b) (abs_sin_le_one _)
  have hcosSlopeZero : Tendsto (fun x : ℝ =>
      Real.cos (b * x) * (J 1) x)
      (𝓝[>] 0) (nhds ((J 1) 0)) := by
    have hright : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) := inf_le_left
    have hc : Tendsto (fun x : ℝ => Real.cos (b * x)) (𝓝[>] 0) (nhds 1) := by
      have hcont : Continuous (fun x : ℝ => Real.cos (b * x)) := by fun_prop
      have hzero : Tendsto (fun x : ℝ => Real.cos (b * x))
          (𝓝 (0 : ℝ)) (nhds (Real.cos (b * 0))) := hcont.continuousAt
      simpa only [mul_zero, Real.cos_zero] using hzero.mono_left hright
    have hs : Tendsto (J 1) (𝓝[>] 0)
        (nhds ((J 1) 0)) :=
      ((hD 1) 0).continuousAt.tendsto.mono_left hright
    simpa using hc.mul hs
  have hcosSlopeInf : Tendsto (fun x : ℝ =>
      Real.cos (b * x) * (J 1) x) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
      (Eventually.of_forall fun x => ?_) (by simpa using (hT 1).norm)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (by rw [Real.norm_eq_abs]; exact abs_cos_le_one _)
  have hsinAmpZero : Tendsto (fun x : ℝ =>
      (-b * Real.sin (b * x)) * (J 0) x)
      (𝓝[>] 0) (nhds 0) := by
    have hright : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) := inf_le_left
    have hs : Tendsto (fun x : ℝ => -b * Real.sin (b * x)) (𝓝[>] 0) (nhds 0) := by
      have hcont : Continuous (fun x : ℝ => -b * Real.sin (b * x)) := by fun_prop
      have hzero : Tendsto (fun x : ℝ => -b * Real.sin (b * x))
          (𝓝 (0 : ℝ)) (nhds (-b * Real.sin (b * 0))) := hcont.continuousAt
      simpa only [mul_zero, Real.sin_zero, mul_zero, neg_zero] using
        hzero.mono_left hright
    have ha : Tendsto (J 0) (𝓝[>] 0)
        (nhds ((J 0) 0)) :=
      ((hD 0) 0).continuousAt.tendsto.mono_left hright
    simpa using hs.mul ha
  have hsinAmpInf : Tendsto (fun x : ℝ =>
      (-b * Real.sin (b * x)) * (J 0) x) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
      (Eventually.of_forall fun x => ?_)
      (by simpa using (hT 0).norm.const_mul |b|)
    rw [norm_mul]
    calc
      ‖-b * Real.sin (b * x)‖ * ‖(J 0) x‖
          ≤ |b| * ‖(J 0) x‖ := by
            gcongr
            rw [Real.norm_eq_abs, abs_mul, abs_neg]
            exact mul_le_of_le_one_right (abs_nonneg b) (abs_sin_le_one _)
      _ = _ := rfl
  have hsinAmp : IntegrableOn (fun x : ℝ =>
      (-b * Real.sin (b * x)) * (J 0) x) (Ioi 0) := by
    apply Integrable.bdd_mul (hI 0)
    · exact (by fun_prop : Continuous (fun x : ℝ => -b * Real.sin (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg b) (abs_sin_le_one _)
  have hcosAmp : IntegrableOn (fun x : ℝ =>
      (-b ^ (2 : ℕ) * Real.cos (b * x)) * (J 0) x) (Ioi 0) := by
    apply Integrable.bdd_mul (hI 0)
    · exact (by fun_prop : Continuous (fun x : ℝ => -b ^ (2 : ℕ) * Real.cos (b * x))).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg (b ^ (2 : ℕ))) (abs_cos_le_one _)
  have hfirst := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := fun x => Real.cos (b * x))
    (u' := fun x => -b * Real.sin (b * x))
    (v := (J 1))
    (v' := (J 2))
    (fun x _ => hcos x) (fun x _ => (hD 1) x)
    hcosCurv hsinSlope hcosSlopeZero hcosSlopeInf
  have hsecond := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (u := fun x => -b * Real.sin (b * x))
    (u' := fun x => -b ^ (2 : ℕ) * Real.cos (b * x))
    (v := (J 0))
    (v' := (J 1))
    (fun x _ => hsin x) (fun x _ => (hD 0) x)
    hsinSlope hcosAmp hsinAmpZero hsinAmpInf
  rw [show (∫ x : ℝ in Ioi 0,
      Real.cos (b * x) * (J 2) x) =
      ∫ x : ℝ in Ioi 0,
        (J 2) x * Real.cos (b * x) by
      apply integral_congr_ae
      filter_upwards with x
      ring] at hfirst
  rw [show (∫ x : ℝ in Ioi 0,
      (-b * Real.sin (b * x)) * (J 1) x) =
      ∫ x : ℝ in Ioi 0,
        (J 1) x * (-b * Real.sin (b * x)) by
      apply integral_congr_ae
      filter_upwards with x
      ring] at hfirst
  rw [show (∫ x : ℝ in Ioi 0,
      (-b * Real.sin (b * x)) * (J 1) x) =
      ∫ x : ℝ in Ioi 0,
        (J 1) x * (-b * Real.sin (b * x)) by
      apply integral_congr_ae
      filter_upwards with x
      ring] at hsecond
  rw [show (∫ x : ℝ in Ioi 0,
      (-b ^ (2 : ℕ) * Real.cos (b * x)) * (J 0) x) =
      -b ^ (2 : ℕ) * ∫ x : ℝ in Ioi 0,
        (J 0) x * Real.cos (b * x) by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring] at hsecond
  linarith

theorem thetaFiniteShellCosine_secondIntegrationByParts (N : ℕ) (b : ℝ) :
    b^(2 : ℕ) * (∫ x : ℝ in Ioi 0, thetaFiniteShellJet N 0 x * Real.cos (b*x)) =
      -thetaFiniteShellJet N 1 0 -
        ∫ x : ℝ in Ioi 0, thetaFiniteShellJet N 2 x * Real.cos (b*x) :=
  halfLineCosine_secondIntegrationByParts (thetaFiniteShellJet N)
    (hasDerivAt_thetaFiniteShellJet N) (integrableOn_thetaFiniteShellJet N)
    (thetaFiniteShellJet_tendsto_atTop_zero N) b

theorem tendsto_thetaFiniteShellCosine_mul_sq (N : ℕ) :
    Tendsto (fun b : ℝ => b^(2 : ℕ) * ∫ x : ℝ in Ioi 0,
      thetaCuspFiniteShellPrefix N x * Real.cos (b*x)) atTop
      (𝓝 (-thetaFiniteShellJet N 1 0)) := by
  have hr := HTGeometry.tendsto_setIntegral_mul_cos_atTop
    (integrableOn_thetaFiniteShellJet N 2)
  have heq (b : ℝ) :
      b^(2 : ℕ) * (∫ x : ℝ in Ioi 0, thetaCuspFiniteShellPrefix N x * Real.cos (b*x)) =
      -thetaFiniteShellJet N 1 0 -
        ∫ x : ℝ in Ioi 0, Real.cos (x*b) * thetaFiniteShellJet N 2 x := by
    rw [← thetaFiniteShellJet_zero_eq, thetaFiniteShellCosine_secondIntegrationByParts]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    rw [mul_comm x b, mul_comm]
  simpa only [heq, sub_zero] using tendsto_const_nhds.sub hr

/-- Every nonempty finite shell prefix has a negative cosine transform at all
sufficiently large real frequencies. The full source's reflection cancellation
is absent from each such prefix. -/
theorem eventually_thetaFiniteShellCosine_neg (N : ℕ) :
    ∀ᶠ b : ℝ in atTop,
      (∫ x : ℝ in Ioi 0, thetaCuspFiniteShellPrefix (N+1) x * Real.cos (b*x)) < 0 := by
  have h := (tendsto_thetaFiniteShellCosine_mul_sq (N+1)).eventually
    (gt_mem_nhds (neg_neg_of_pos (thetaFiniteShellJet_one_zero_pos N)))
  filter_upwards [h] with b hb
  exact neg_of_mul_neg_right hb (sq_nonneg b)

private theorem fullJet_integrable (k : ℕ) :
    IntegrableOn (thetaCuspFullDerivative k) (Ioi 0) := by
  have h := integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource k 0
  simp only [zero_mul, Real.exp_zero, one_mul] at h
  have hc : Continuous (iteratedDeriv k thetaCuspFullSource) := by
    rw [iteratedDeriv_thetaCuspFullSource]
    exact continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_thetaCuspFullDerivative k x).continuousAt
  have hi : Integrable (iteratedDeriv k thetaCuspFullSource) := by
    exact (integrable_norm_iff hc.aestronglyMeasurable).mp h
  rw [iteratedDeriv_thetaCuspFullSource] at hi
  exact hi.integrableOn

private theorem fullJet_tendsto_zero (k : ℕ) :
    Tendsto (thetaCuspFullDerivative k) atTop (𝓝 0) := by
  rw [← iteratedDeriv_thetaCuspFullSource, tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun x : ℝ => thetaCuspDerivativeExpConstant k * Real.exp (-x))
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
      (thetaCuspDerivativeExpConstant k))
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ ht
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg k hx

/-- Reflection cancels the quadratic-frequency boundary anomaly in the exact
completed theta source. -/
theorem tendsto_thetaFullCosine_mul_sq_zero :
    Tendsto (fun b : ℝ => b^(2 : ℕ) * ∫ x : ℝ in Ioi 0,
      thetaCuspFullSource x * Real.cos (b*x)) atTop (𝓝 0) := by
  have hzero : thetaCuspFullDerivative 0 = thetaCuspFullSource := by
    rw [← iteratedDeriv_thetaCuspFullSource]
    simp
  have hseam : thetaCuspFullDerivative 1 0 = 0 :=
    tsum_iteratedDeriv_one_thetaCuspSourceTerm_zero_eq_zero
  have hr := HTGeometry.tendsto_setIntegral_mul_cos_atTop (fullJet_integrable 2)
  have heq (b : ℝ) :
      b^(2 : ℕ) * (∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (b*x)) =
      -(∫ x : ℝ in Ioi 0, Real.cos (x*b) * thetaCuspFullDerivative 2 x) := by
    rw [← hzero, halfLineCosine_secondIntegrationByParts thetaCuspFullDerivative
      hasDerivAt_thetaCuspFullDerivative fullJet_integrable fullJet_tendsto_zero,
      hseam, neg_zero, zero_sub]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    rw [mul_comm x b, mul_comm]
  simpa only [heq, neg_zero] using hr.neg

/-- The omitted infinite arithmetic tail restores exactly the leading Fourier
boundary term lost by every finite shell prefix. -/
theorem tendsto_thetaShellRemainderCosine_mul_sq (N : ℕ) :
    Tendsto (fun b : ℝ => b^(2 : ℕ) * ∫ x : ℝ in Ioi 0,
      (thetaCuspFullSource x - thetaCuspFiniteShellPrefix N x) * Real.cos (b*x))
      atTop (𝓝 (thetaFiniteShellJet N 1 0)) := by
  have h := tendsto_thetaFullCosine_mul_sq_zero.sub (tendsto_thetaFiniteShellCosine_mul_sq N)
  have hi : IntegrableOn thetaCuspFullSource (Ioi 0) := by
    have h0 := fullJet_integrable 0
    simpa only [← iteratedDeriv_thetaCuspFullSource, iteratedDeriv_zero] using h0
  have hj : IntegrableOn (thetaCuspFiniteShellPrefix N) (Ioi 0) := by
    rw [← thetaFiniteShellJet_zero_eq]
    exact integrableOn_thetaFiniteShellJet N 0
  have hc (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0)) (b : ℝ) :
      IntegrableOn (fun x : ℝ => f x * Real.cos (b*x)) (Ioi 0) := by
    have hmul := Integrable.bdd_mul hf
      (by fun_prop : Continuous (fun x : ℝ => Real.cos (b*x))).aestronglyMeasurable.restrict
      (ae_of_all _ fun x => (show ‖Real.cos (b*x)‖ ≤ 1 by
        simpa only [Real.norm_eq_abs] using abs_cos_le_one (b*x)))
    exact hmul.congr (ae_of_all _ fun x => mul_comm _ _)
  have heq (b : ℝ) :
      b^(2 : ℕ) * (∫ x : ℝ in Ioi 0,
        (thetaCuspFullSource x - thetaCuspFiniteShellPrefix N x) * Real.cos (b*x)) =
      b^(2 : ℕ) * (∫ x : ℝ in Ioi 0, thetaCuspFullSource x * Real.cos (b*x)) -
      b^(2 : ℕ) * (∫ x : ℝ in Ioi 0, thetaCuspFiniteShellPrefix N x * Real.cos (b*x)) := by
    simp_rw [sub_mul]
    rw [integral_sub (hc _ hi b) (hc _ hj b), mul_sub]
  simpa only [heq, sub_neg_eq_add, zero_add] using h

/-- The exact omitted tail has eventually positive cosine transform, even
though its raw mass can be extremely small. -/
theorem eventually_thetaShellRemainderCosine_pos (N : ℕ) :
    ∀ᶠ b : ℝ in atTop,
      (∫ x : ℝ in Ioi 0,
        (thetaCuspFullSource x - thetaCuspFiniteShellPrefix (N+1) x) * Real.cos (b*x)) > 0 := by
  have h := (tendsto_thetaShellRemainderCosine_mul_sq (N+1)).eventually
    (lt_mem_nhds (thetaFiniteShellJet_one_zero_pos N))
  filter_upwards [h] with b hb
  exact pos_of_mul_pos_right hb (sq_nonneg b)

end
end RHTower
