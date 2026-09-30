import GaloisForLFunctions.RHTower.LiClockPairedEtaFiniteFilledDeflation
import Mathlib.Probability.Moments.Tilted
import GaloisForLFunctions.RHTower.LiClockPairedEtaCompletionMoments
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import GaloisForLFunctions.RHTower.LiClockCentralTraceSineContinuity
/-!
# The actual finite partition clock and its symmetrized Volterra law

The complete finite logarithmic interval union is tilted at one half. Its independent
product is normalized by the square of the literal partition value. The difference
measure has positive moments at every even degree and retains both integration variables.

Parity of its entire moment-generating function gives the exact cumulant recurrence.
The beta integral and compact absolute series interchange yield the literal partition
clock equation with symmetrization factor two. Positive Borel degree escapes every finite
prefix, forcing its positive-part clock area to diverge and positive clocks to occur on
all tails. The contour hypotheses require a nonzero partition on the full closed source
disk; the actual centered phase strip supplies such a radius for every nonempty prefix.
-/

open Complex Filter Set Metric Topology MeasureTheory ProbabilityTheory RiemannGaussian
open scoped BigOperators ComplexConjugate
namespace RHTower
noncomputable section


/-- The literal positive half-tilt normalizer of the complete finite interval union. -/
def liClockPairedEtaPartitionNormalizer (N : ℕ) : ℝ :=
  ∫u:ℝ, Real.exp (-u/2) ∂pairedEtaFiniteLogMeasure N

/-- The full normalized product half-tilt, before taking the difference of its coordinates. -/
def liClockPairedEtaSymmetrizedMeasure (N : ℕ) : Measure (ℝ×ℝ) :=
  ((pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)).tilted
    (fun p:ℝ×ℝ=>-(p.1+p.2)/2)

/-- Every even raw difference moment retains the full tilted product measure. -/
def liClockPairedEtaSymmetrizedEvenMoment (N j : ℕ) : ℝ :=
  ∫p:ℝ×ℝ, (p.1-p.2)^(2*j) ∂liClockPairedEtaSymmetrizedMeasure N

private lemma normalizer_eq (N : ℕ) : pairedEtaFiniteLaplacePartition N (1/2:ℂ) =
    (liClockPairedEtaPartitionNormalizer N : ℂ) := by
  rw [pairedEtaFiniteLaplacePartition_eq_integral_logMeasure]
  calc
    _ = ∫u:ℝ, (Real.exp (-u/2):ℂ) ∂pairedEtaFiniteLogMeasure N := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    _ = _ := integral_complex_ofReal
private lemma normalizer_pos {N : ℕ} (hN : 0<N) : 0<liClockPairedEtaPartitionNormalizer N := by
  have hp := pairedEtaFiniteCenteredTiltedCosineMoment_pos_of_phase_le_pi hN (1/2) 0 (by simp; exact Real.pi_pos.le)
  rw [pairedEtaFiniteCenteredTiltedCosineMoment_eq_rotation] at hp
  simp only [zero_mul, Real.cos_zero, one_mul, Real.sin_zero, zero_mul, add_zero] at hp
  have hc := congrArg Complex.re (pairedEtaFiniteLaplacePartition_eq_cosine_sub_I_sine N (1/2) 0)
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_zero, zero_mul, add_zero] at hc
  rw [normalizer_eq] at hc
  simp only [Complex.ofReal_re, zero_mul, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero] at hc
  exact hc.symm ▸ hp
private lemma joint_weight_factor (p : ℝ×ℝ) :
    Real.exp (-(p.1+p.2)/2)=Real.exp (-p.1/2)*Real.exp (-p.2/2) := by
  rw [← Real.exp_add]
  congr 1
  ring
private lemma joint_weight_integrable (N : ℕ) : Integrable (fun p:ℝ×ℝ=>Real.exp (-(p.1+p.2)/2))
    ((pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)) := by
  have h := (integrable_rexp_neg_mul_pairedEtaFiniteLogMeasure N (1/2)).mul_prod
    (integrable_rexp_neg_mul_pairedEtaFiniteLogMeasure N (1/2))
  convert h using 1
  funext p
  rw [joint_weight_factor]
  congr 1 <;> congr 1 <;> ring
private lemma joint_weight_integral (N : ℕ) :
    (∫p:ℝ×ℝ, Real.exp (-(p.1+p.2)/2) ∂(pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)) =
    (liClockPairedEtaPartitionNormalizer N)^2 := by
  simp_rw [joint_weight_factor]
  simpa only [liClockPairedEtaPartitionNormalizer, pow_two] using
    integral_prod_mul (μ:=pairedEtaFiniteLogMeasure N) (ν:=pairedEtaFiniteLogMeasure N)
      (fun u : ℝ => Real.exp (-u/2)) (fun v : ℝ => Real.exp (-v/2))
private lemma sym_measure_probability {N : ℕ} (hN : 0<N) :
    IsProbabilityMeasure (liClockPairedEtaSymmetrizedMeasure N) := by
  have hn : NeZero ((pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)) := by
    constructor
    intro hz
    have hp : 0<(∫p:ℝ×ℝ, Real.exp (-(p.1+p.2)/2) ∂(pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)) := by
      rw [joint_weight_integral]
      exact sq_pos_of_pos (normalizer_pos hN)
    rw [hz, integral_zero_measure] at hp
    exact (lt_irrefl _ hp)
  exact isProbabilityMeasure_tilted (joint_weight_integrable N)
private lemma sym_exp_integrable (N : ℕ) (v : ℝ) :
    Integrable (fun p:ℝ×ℝ=>Real.exp (v*(p.1-p.2))) (liClockPairedEtaSymmetrizedMeasure N) := by
  rw [liClockPairedEtaSymmetrizedMeasure, integrable_tilted_iff (joint_weight_integrable N)]
  have h := (integrable_rexp_neg_mul_pairedEtaFiniteLogMeasure N (1/2-v)).mul_prod
    (integrable_rexp_neg_mul_pairedEtaFiniteLogMeasure N (1/2+v))
  convert h using 1
  funext p
  simp only [smul_eq_mul]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring
private lemma sym_interior (N : ℕ) (z : ℂ) :
    z.re∈interior (integrableExpSet (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaSymmetrizedMeasure N)) := by
  have hu : (integrableExpSet (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaSymmetrizedMeasure N))=univ := by
    ext v
    simp only [mem_univ, iff_true]
    exact sym_exp_integrable N v
  rw [hu, interior_univ]
  trivial
private lemma sym_complexMGF_eq (N : ℕ) (z : ℂ) :
    complexMGF (fun p : ℝ×ℝ=>p.1-p.2) (liClockPairedEtaSymmetrizedMeasure N) z =
      pairedEtaFiniteLaplacePartition N (1/2-z)*pairedEtaFiniteLaplacePartition N (1/2+z) /
        (pairedEtaFiniteLaplacePartition N (1/2))^2 := by
  rw [complexMGF, liClockPairedEtaSymmetrizedMeasure, integral_tilted, joint_weight_integral]
  have heq : (fun p : ℝ×ℝ => (Real.exp (-(p.1+p.2)/2) / liClockPairedEtaPartitionNormalizer N^2) •
      Complex.exp (z * ((p.1-p.2:ℝ):ℂ))) =
    (fun p : ℝ×ℝ => (Complex.exp (-(1/2-z)*(p.1:ℂ))*Complex.exp (-(1/2+z)*(p.2:ℂ))) /
      ((liClockPairedEtaPartitionNormalizer N : ℂ)^2)) := by
    funext p
    rw [RCLike.real_smul_eq_coe_mul]
    simp only [RCLike.ofReal_eq_complex_ofReal]
    simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_sub,
      Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_exp]
    rw [div_mul_eq_mul_div]
    congr 1
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [heq, integral_div, normalizer_eq]
  congr 1
  rw [pairedEtaFiniteLaplacePartition_eq_integral_logMeasure,
    pairedEtaFiniteLaplacePartition_eq_integral_logMeasure]
  exact integral_prod_mul (fun u : ℝ=>Complex.exp (-(1/2-z)*(u:ℂ)))
    (fun v : ℝ=>Complex.exp (-(1/2+z)*(v:ℂ)))
private lemma sym_even_deriv (N j : ℕ) :
    iteratedDeriv (2*j) (complexMGF (fun p : ℝ×ℝ=>p.1-p.2) (liClockPairedEtaSymmetrizedMeasure N)) 0 =
      (liClockPairedEtaSymmetrizedEvenMoment N j : ℂ) := by
  rw [iteratedDeriv_complexMGF (sym_interior N 0)]
  simp only [zero_mul, Complex.exp_zero, mul_one]
  rw [liClockPairedEtaSymmetrizedEvenMoment, ← integral_complex_ofReal (μ:=liClockPairedEtaSymmetrizedMeasure N) (f:=fun p : ℝ×ℝ=>(p.1-p.2)^(2*j))]
  apply integral_congr_ae
  filter_upwards [] with p
  push_cast
  rfl
private lemma sym_moment_zero {N : ℕ} (hN : 0<N) :
    liClockPairedEtaSymmetrizedEvenMoment N 0 = 1 := by
  letI := sym_measure_probability hN
  simp [liClockPairedEtaSymmetrizedEvenMoment]
private lemma logMeasure_support (N : ℕ) :
    ∀ᵐu ∂pairedEtaFiniteLogMeasure N, 0 ≤ u ∧ u ≤ Real.log (2*(N:ℝ)) := by
  unfold pairedEtaFiniteLogMeasure
  rw [ae_finsetSum_measure_iff]
  intro n hn
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hlo : 0 ≤ Real.log (2*(n:ℝ)+1) := Real.log_nonneg (by linarith [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n])
  have hhi : Real.log (2*(n:ℝ)+2)  ≤  Real.log (2*(N:ℝ)) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show 2*n+2  ≤  2*N by have := Finset.mem_range.mp hn; omega)
  exact ⟨hlo.trans hu.1.le, hu.2.trans hhi⟩
private lemma sym_support (N : ℕ) :
    ∀ᵐp ∂liClockPairedEtaSymmetrizedMeasure N, |p.1-p.2| ≤ Real.log (2*(N:ℝ)) := by
  apply Measure.AbsolutelyContinuous.ae_le (tilted_absolutelyContinuous _ _)
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [logMeasure_support N] with u hu
  filter_upwards [logMeasure_support N] with v hv
  rw [abs_le]
  constructor <;> linarith
private lemma sym_moment_integrable (N j : ℕ) :
    Integrable (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)) (liClockPairedEtaSymmetrizedMeasure N) := by
  have h := integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (by simpa only [Complex.zero_re] using sym_interior N (0:ℂ)) (2*j)
  simpa only [zero_mul, Real.exp_zero, mul_one] using h
private lemma sym_moment_bound {N : ℕ} (hN : 0<N) (j : ℕ) :
    liClockPairedEtaSymmetrizedEvenMoment N j  ≤  Real.log (2*(N:ℝ))^(2*j) := by
  letI := sym_measure_probability hN
  have hle : ∀ᵐp ∂liClockPairedEtaSymmetrizedMeasure N,
      (p.1-p.2)^(2*j)  ≤  Real.log (2*(N:ℝ))^(2*j) := by
    filter_upwards [sym_support N] with p hp
    calc
      _  ≤  |p.1-p.2|^(2*j) := le_abs_self _ |>.trans_eq (abs_pow _ _)
      _  ≤  _ := pow_le_pow_left₀ (abs_nonneg _) hp _
  have hm := integral_mono_ae (sym_moment_integrable N j) (integrable_const _) hle
  simpa only [liClockPairedEtaSymmetrizedEvenMoment, integral_const, probReal_univ,
    one_smul] using hm
private lemma first_interval_le {N : ℕ} (hN : 0<N) :
    volume.restrict (Ioc (0:ℝ) (Real.log 2))  ≤  pairedEtaFiniteLogMeasure N := by
  have hh := Finset.single_le_sum (f:=fun n:ℕ=>volume.restrict
      (Ioc (Real.log (2*(n:ℝ)+1)) (Real.log (2*(n:ℝ)+2))))
    (fun n _ => bot_le) (Finset.mem_range.mpr hN)
  simpa only [pairedEtaFiniteLogMeasure, Nat.cast_zero, mul_zero, zero_add, Real.log_one] using hh
private lemma sym_moment_pos {N : ℕ} (hN : 0<N) (j : ℕ) :
    0<liClockPairedEtaSymmetrizedEvenMoment N j := by
  by_cases hj : j=0
  · rw [hj, sym_moment_zero hN]
    norm_num
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  let a : Set ℝ := Ioc 0 (Real.log 2/3)
  let b : Set ℝ := Ioc (2*Real.log 2/3) (Real.log 2)
  let rect : Set (ℝ×ℝ) := a ×ˢ b
  have ha : a⊆Ioc 0 (Real.log 2) := by intro x hx; exact ⟨hx.1, hx.2.trans (by linarith)⟩
  have hb : b⊆Ioc 0 (Real.log 2) := by intro x hx; exact ⟨by linarith [hx.1],hx.2⟩
  have hfirsta : (volume.restrict (Ioc 0 (Real.log 2))) a = ENNReal.ofReal (Real.log 2/3) := by
    rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr ha, Real.volume_Ioc]
    simp
  have hfirstb : (volume.restrict (Ioc 0 (Real.log 2))) b = ENNReal.ofReal (Real.log 2/3) := by
    rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr hb, Real.volume_Ioc]
    congr 1
    ring
  have hrawpos : 0<((pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)) rect := by
    have hh := (Measure.prod_mono (first_interval_le hN) (first_interval_le hN)) rect
    rw [Measure.prod_prod, hfirsta, hfirstb] at hh
    have hpos : 0<ENNReal.ofReal (Real.log 2/3)*ENNReal.ofReal (Real.log 2/3) := by positivity
    exact hpos.trans_le hh
  have htiltpos : 0<(liClockPairedEtaSymmetrizedMeasure N) rect := by
    apply bot_lt_iff_ne_bot.mpr
    intro hz
    have hrawzero := absolutelyContinuous_tilted (joint_weight_integrable N) hz
    exact hrawpos.ne' hrawzero
  have hsub : rect⊆Function.support (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j)) := by
    intro p hp
    have huv : p.1<p.2 := by
      have hu := hp.1.2
      have hv := hp.2.1
      linarith
    exact pow_ne_zero _ (sub_ne_zero.mpr (ne_of_lt huv))
  have hspos : 0<(liClockPairedEtaSymmetrizedMeasure N)
      (Function.support (fun p:ℝ×ℝ=>(p.1-p.2)^(2*j))) := htiltpos.trans_le (measure_mono hsub)
  apply (integral_pos_iff_support_of_nonneg (fun p=>by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) j) (sym_moment_integrable N j)).2 hspos


private def symLaplace (N : ℕ) (z : ℂ) : ℂ :=
  pairedEtaFiniteLaplacePartition N (1/2-z) *
  pairedEtaFiniteLaplacePartition N (1/2+z) /
  (pairedEtaFiniteLaplacePartition N (1/2))^2
private def symSlope (N : ℕ) (z : ℂ) : ℂ :=
  logDeriv (pairedEtaFiniteLaplacePartition N) (1/2+z) -
  logDeriv (pairedEtaFiniteLaplacePartition N) (1/2-z)
private lemma analytic_sym (N : ℕ) (z : ℂ) : AnalyticAt ℂ (symLaplace N) z := by
  exact (((analyticAt_liClockPairedEtaFiniteLaplacePartition_entire N (1/2-z)).comp
      (f := fun z : ℂ => 1/2-z) (analyticAt_const.sub analyticAt_id)).mul
    ((analyticAt_liClockPairedEtaFiniteLaplacePartition_entire N (1/2+z)).comp
      (f := fun z : ℂ => 1/2+z) (analyticAt_const.add analyticAt_id))).div_const
private lemma sym_even (N : ℕ) (z : ℂ) : symLaplace N (-z) = symLaplace N z := by
  simp only [symLaplace, sub_neg_eq_add, ← sub_eq_add_neg]
  rw [mul_comm]
private lemma sym_odd_zero (N j : ℕ) : iteratedDeriv (2*j+1) (symLaplace N) 0 = 0 := by
  have heq : (fun z : ℂ => symLaplace N (-z)) = symLaplace N := funext (sym_even N)
  have h := iteratedDeriv_comp_neg (2*j+1) (symLaplace N) (0:ℂ)
  rw [heq] at h
  simp only [neg_zero, smul_eq_mul, pow_add, pow_mul, neg_one_sq, one_pow, one_mul,
    pow_one] at h
  linear_combination (1/2:ℂ)*h
private lemma analytic_q {N : ℕ} (hN : 0 < N) :
    AnalyticAt ℂ (logDeriv (pairedEtaFiniteLaplacePartition N)) (1/2:ℂ) := by
  have ha := analyticAt_liClockPairedEtaFiniteLaplacePartition_entire N (1/2:ℂ)
  exact ha.deriv.div ha (liClockPairedEtaFiniteLaplacePartition_ne_zero hN (by norm_num; exact Real.pi_pos.le))
private lemma slope_jet {N : ℕ} (hN : 0 < N) (n : ℕ) :
    iteratedDeriv n (symSlope N) 0 =
      (1 - (-1:ℂ)^n) * iteratedDeriv n (logDeriv (pairedEtaFiniteLaplacePartition N)) (1/2) := by
  have hq := analytic_q hN
  have hplus : AnalyticAt ℂ (fun z : ℂ => logDeriv (pairedEtaFiniteLaplacePartition N) (1/2+z)) 0 :=
    by
    have hq' : AnalyticAt ℂ (logDeriv (pairedEtaFiniteLaplacePartition N)) ((fun z : ℂ => 1/2+z) 0) := by simpa only [add_zero] using hq
    exact hq'.comp (f := fun z : ℂ => 1/2+z) (analyticAt_const.add analyticAt_id)
  have hminus : AnalyticAt ℂ (fun z : ℂ => logDeriv (pairedEtaFiniteLaplacePartition N) (1/2-z)) 0 :=
    by
    have hq' : AnalyticAt ℂ (logDeriv (pairedEtaFiniteLaplacePartition N)) ((fun z : ℂ => 1/2-z) 0) := by simpa only [sub_zero] using hq
    exact hq'.comp (f := fun z : ℂ => 1/2-z) (analyticAt_const.sub analyticAt_id)
  change iteratedDeriv n ((fun z => logDeriv (pairedEtaFiniteLaplacePartition N) (1/2+z)) -
    (fun z => logDeriv (pairedEtaFiniteLaplacePartition N) (1/2-z))) 0 = _
  rw [iteratedDeriv_sub hplus.contDiffAt hminus.contDiffAt]
  rw [iteratedDeriv_comp_const_add, iteratedDeriv_comp_const_sub]
  simp only [add_zero, sub_zero, smul_eq_mul]
  ring
private lemma sym_deriv_eq {N : ℕ} (hN : 0 < N) :
    deriv (symLaplace N) =ᶠ[𝓝 (0:ℂ)] fun z => symSlope N z * symLaplace N z := by
  have h0 : pairedEtaFiniteLaplacePartition N (1/2:ℂ) ≠ 0 :=
    liClockPairedEtaFiniteLaplacePartition_ne_zero hN (by norm_num; exact Real.pi_pos.le)
  have hcA : Continuous (pairedEtaFiniteLaplacePartition N) :=
    continuous_iff_continuousAt.mpr fun w => (analyticAt_liClockPairedEtaFiniteLaplacePartition_entire N w).continuousAt
  have hcplus : ContinuousAt (fun z : ℂ => pairedEtaFiniteLaplacePartition N (1/2+z)) 0 :=
    (hcA.comp (continuous_const.add continuous_id)).continuousAt
  have hcminus : ContinuousAt (fun z : ℂ => pairedEtaFiniteLaplacePartition N (1/2-z)) 0 :=
    (hcA.comp (continuous_const.sub continuous_id)).continuousAt
  have hplus : ∀ᶠ z : ℂ in 𝓝 0, pairedEtaFiniteLaplacePartition N (1/2+z) ≠ 0 :=
    hcplus.eventually_ne (by simpa only [add_zero] using h0)
  have hminus : ∀ᶠ z : ℂ in 𝓝 0, pairedEtaFiniteLaplacePartition N (1/2-z) ≠ 0 :=
    hcminus.eventually_ne (by simpa only [sub_zero] using h0)
  filter_upwards [hplus, hminus] with z hp hm
  have hdminus := ((analyticAt_liClockPairedEtaFiniteLaplacePartition_entire N (1/2-z)).differentiableAt.hasDerivAt).comp z
    ((hasDerivAt_const z (1/2:ℂ)).sub (hasDerivAt_id z))
  have hdplus := ((analyticAt_liClockPairedEtaFiniteLaplacePartition_entire N (1/2+z)).differentiableAt.hasDerivAt).comp z
    ((hasDerivAt_const z (1/2:ℂ)).add (hasDerivAt_id z))
  have hd := (hdminus.mul hdplus).div_const ((pairedEtaFiniteLaplacePartition N (1/2))^2)
  change deriv (fun z : ℂ => pairedEtaFiniteLaplacePartition N (1/2-z) *
    pairedEtaFiniteLaplacePartition N (1/2+z) / (pairedEtaFiniteLaplacePartition N (1/2))^2) z = _
  have he : deriv (symLaplace N) z =
      (-deriv (pairedEtaFiniteLaplacePartition N) (1/2-z)*pairedEtaFiniteLaplacePartition N (1/2+z) +
        pairedEtaFiniteLaplacePartition N (1/2-z)*deriv (pairedEtaFiniteLaplacePartition N) (1/2+z)) /
        (pairedEtaFiniteLaplacePartition N (1/2))^2 := by
    change deriv (fun w : ℂ => pairedEtaFiniteLaplacePartition N (1/2-w)*pairedEtaFiniteLaplacePartition N (1/2+w) / (pairedEtaFiniteLaplacePartition N (1/2))^2) z = _
    simpa only [Function.comp_def, Pi.mul_apply, zero_sub, zero_add,
      mul_neg_one, mul_one] using hd.deriv
  change deriv (symLaplace N) z = _
  rw [he]
  have hhplus : deriv (pairedEtaFiniteLaplacePartition N) (1/2+z) /
      pairedEtaFiniteLaplacePartition N (1/2+z) *
      (pairedEtaFiniteLaplacePartition N (1/2-z)*pairedEtaFiniteLaplacePartition N (1/2+z)) =
      pairedEtaFiniteLaplacePartition N (1/2-z)*deriv (pairedEtaFiniteLaplacePartition N) (1/2+z) := by
    rw [div_eq_mul_inv]
    calc
      _ = pairedEtaFiniteLaplacePartition N (1/2-z)*deriv (pairedEtaFiniteLaplacePartition N) (1/2+z)*
          ((pairedEtaFiniteLaplacePartition N (1/2+z))⁻¹*pairedEtaFiniteLaplacePartition N (1/2+z)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hp,mul_one]
  have hhminus : deriv (pairedEtaFiniteLaplacePartition N) (1/2-z) /
      pairedEtaFiniteLaplacePartition N (1/2-z) *
      (pairedEtaFiniteLaplacePartition N (1/2-z)*pairedEtaFiniteLaplacePartition N (1/2+z)) =
      deriv (pairedEtaFiniteLaplacePartition N) (1/2-z)*pairedEtaFiniteLaplacePartition N (1/2+z) := by
    rw [div_eq_mul_inv]
    calc
      _ = deriv (pairedEtaFiniteLaplacePartition N) (1/2-z)*pairedEtaFiniteLaplacePartition N (1/2+z)*
          ((pairedEtaFiniteLaplacePartition N (1/2-z))⁻¹*pairedEtaFiniteLaplacePartition N (1/2-z)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hm,mul_one]
  simp only [symSlope, symLaplace, logDeriv, Pi.div_apply]
  rw [←mul_div_assoc,sub_mul,hhplus,hhminus]
  ring
private lemma slope_analytic {N : ℕ} (hN : 0 < N) : AnalyticAt ℂ (symSlope N) 0 := by
  have hq := analytic_q hN
  have hplus : AnalyticAt ℂ (fun z : ℂ => logDeriv (pairedEtaFiniteLaplacePartition N) (1/2+z)) 0 := by
    have hq' : AnalyticAt ℂ (logDeriv (pairedEtaFiniteLaplacePartition N)) ((fun z : ℂ => 1/2+z) 0) := by simpa only [add_zero] using hq
    exact hq'.comp (f := fun z : ℂ => 1/2+z) (analyticAt_const.add analyticAt_id)
  have hminus : AnalyticAt ℂ (fun z : ℂ => logDeriv (pairedEtaFiniteLaplacePartition N) (1/2-z)) 0 := by
    have hq' : AnalyticAt ℂ (logDeriv (pairedEtaFiniteLaplacePartition N)) ((fun z : ℂ => 1/2-z) 0) := by simpa only [sub_zero] using hq
    exact hq'.comp (f := fun z : ℂ => 1/2-z) (analyticAt_const.sub analyticAt_id)
  exact hplus.sub hminus
private lemma sum_range_two (f : ℕ → ℂ) (n : ℕ) :
    ∑ i ∈ Finset.range (2*n), f i = ∑ j ∈ Finset.range n, (f (2*j) + f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring
private lemma sym_recurrence {N : ℕ} (hN : 0 < N) (n : ℕ) :
    iteratedDeriv (2*n+2) (symLaplace N) 0 =
      ∑ j ∈ Finset.range (n+1),
        ((2*n+1).choose (2*j+1):ℂ) * 2 *
          iteratedDeriv (2*j+1) (logDeriv (pairedEtaFiniteLaplacePartition N)) (1/2) *
          iteratedDeriv (2*(n-j)) (symLaplace N) 0 := by
  have h := (sym_deriv_eq hN).iteratedDeriv_eq (2*n+1)
  rw [← iteratedDeriv_succ'] at h
  rw [iteratedDeriv_fun_mul (slope_analytic hN).contDiffAt (analytic_sym N 0).contDiffAt,
    show 2*n+1+1=2*(n+1) by omega, sum_range_two] at h
  rw [show 2*n+2=2*(n+1) by omega, h]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j  ≤  n := by simpa using Finset.mem_range.mp hj
  rw [slope_jet hN, slope_jet hN]
  simp only [pow_mul, pow_add, neg_one_sq, one_pow, pow_one]
  rw [show 2*n+1-(2*j+1)=2*(n-j) by omega]
  ring

private def gTerm (c : ℕ → ℝ) (t : ℝ) (j : ℕ) := c j*t^(2*j)
private def gKernel (c : ℕ → ℝ) (t : ℝ) := ∑' j, gTerm c t j
private def gWeighted (c : ℕ → ℝ) (t : ℝ) := ∑' j : ℕ, (2*j:ℝ)*gTerm c t j
private def gPrefix (c : ℕ → ℝ) (K : ℕ) (t : ℝ) := ∑ j ∈ Finset.range K, gTerm c t j
variable {c : ℕ → ℝ} {R : ℝ}
private lemma gTerm_nonneg (hc : ∀j, 0<c j) (t : ℝ) (j : ℕ) : 0 ≤ gTerm c t j := by
  rw [gTerm, pow_mul]
  exact mul_nonneg (hc j).le (pow_nonneg (sq_nonneg t) j)
private lemma norm_gTerm_le (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) {t T : ℝ} (ht : |t| ≤ T) (j : ℕ) :
    ‖gTerm c t j‖  ≤  (R*T^2)^j/(j.factorial:ℝ) := by
  rw [gTerm, norm_mul, Real.norm_eq_abs, abs_of_pos (hc j), norm_pow, Real.norm_eq_abs]
  calc
    c j*|t|^(2*j)  ≤  (R^j/(j.factorial:ℝ))*T^(2*j) :=
      mul_le_mul (hbound j) (pow_le_pow_left₀ (abs_nonneg t) ht _)
        (pow_nonneg (abs_nonneg t) _) (by positivity)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring
private lemma summable_gTerm (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) (t : ℝ) : Summable (gTerm c t) :=
  (Real.summable_pow_div_factorial (R*|t|^2)).of_norm_bounded
    (fun j => norm_gTerm_le hc hR hbound (le_refl |t|) j)
private lemma summable_degree_pow (r : ℝ) :
    Summable (fun j : ℕ => (2*j:ℝ)*r^j/(j.factorial:ℝ)) := by
  apply (summable_nat_add_iff 1).1
  have h := (Real.summable_pow_div_factorial r).mul_left (2*r)
  apply h.congr
  intro j
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have hf : (j.factorial:ℝ) ≠ 0 := by positivity
  have hj : (j+1:ℝ) ≠ 0 := by positivity
  field_simp
private lemma summable_gWeighted (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) (t : ℝ) :
    Summable (fun j : ℕ => (2*j:ℝ)*gTerm c t j) := by
  apply (summable_degree_pow (R*|t|^2)).of_norm_bounded
  intro j
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*j)]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
    (norm_gTerm_le hc hR hbound (le_refl |t|) j) (show (0:ℝ) ≤ 2*j by positivity)
private lemma gTerm_le_kernel (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) (t : ℝ) (j : ℕ) :
    gTerm c t j  ≤  gKernel c t :=
  (summable_gTerm hc hR hbound t).le_tsum j (fun i _ => gTerm_nonneg hc t i)
private lemma gKernel_pos (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) (t : ℝ) : 0<gKernel c t := by
  have h := gTerm_le_kernel hc hR hbound t 0
  simp only [gTerm, Nat.mul_zero, pow_zero, mul_one] at h
  exact (hc 0).trans_le h
private lemma gKernel_mono (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    gKernel c a  ≤  gKernel c b := by
  apply (summable_gTerm hc hR hbound a).tsum_le_tsum _ (summable_gTerm hc hR hbound b)
  intro j
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab _) (hc j).le
private lemma continuous_gTerm (j : ℕ) : Continuous (fun t : ℝ => gTerm c t j) := by
  unfold gTerm
  fun_prop
private lemma continuous_gKernel (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) : Continuous (gKernel c) := by
  rw [continuous_iff_continuousAt]
  intro x
  let T : ℝ := |x|+1
  have hcT : ContinuousOn (gKernel c) (Metric.ball 0 T) := by
    apply continuousOn_tsum (fun j => (continuous_gTerm j).continuousOn)
      (Real.summable_pow_div_factorial (R*T^2))
    intro j t ht
    apply norm_gTerm_le hc hR hbound
    exact le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using ht)
  exact hcT.continuousAt (Metric.isOpen_ball.mem_nhds (by simp [Metric.mem_ball, T]))
private def gDerivTerm (c : ℕ → ℝ) (t : ℝ) (j : ℕ) := c j*(2*j:ℝ)*t^(2*j-1)
private lemma norm_gDerivTerm_le (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) {t T : ℝ} (hT : 1 ≤ T) (ht : |t| ≤ T) (j : ℕ) :
    ‖gDerivTerm c t j‖  ≤  (2*j:ℝ)*(R*T^2)^j/(j.factorial:ℝ) := by
  have hpow : |t|^(2*j-1)  ≤  T^(2*j) :=
    (pow_le_pow_left₀ (abs_nonneg t) ht _).trans (pow_le_pow_right₀ hT (Nat.sub_le _ _))
  rw [gDerivTerm, norm_mul, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (hc j), abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*j), Real.norm_eq_abs]
  calc
    c j*(2*j:ℝ)*|t|^(2*j-1)  ≤  (R^j/(j.factorial:ℝ))*(2*j:ℝ)*T^(2*j) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (hbound j) (by positivity)
      · exact hpow
      · positivity
      · positivity
    _ = _ := by rw [mul_pow, ← pow_mul]; ring
private lemma hasDerivAt_gKernel (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) (t : ℝ) :
    HasDerivAt (gKernel c) (∑'j, gDerivTerm c t j) t := by
  let T : ℝ := |t|+1
  have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hg (j : ℕ) (y : ℝ) (_ : y∈Metric.ball 0 T) :
      HasDerivAt (fun z => gTerm c z j) (gDerivTerm c y j) y := by
    simpa only [gTerm, gDerivTerm, Pi.pow_apply, id_eq, mul_one, Nat.cast_mul,
      Nat.cast_ofNat, mul_assoc] using ((hasDerivAt_id y).pow (2*j)).const_mul (c j)
  exact hasDerivAt_tsum_of_isPreconnected (summable_degree_pow (R*T^2))
    Metric.isOpen_ball (convex_ball (0:ℝ) T).isPreconnected hg
    (fun j y hy => norm_gDerivTerm_le hc hR hbound hT
      (le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hy)) j)
    (by simp [Metric.mem_ball, T]; positivity)
    (summable_gTerm hc hR hbound 0) (by simp [Metric.mem_ball, T])
private lemma gKernel_mul_deriv (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) (t : ℝ) :
    t*deriv (gKernel c) t = gWeighted c t := by
  rw [(hasDerivAt_gKernel hc hR hbound t).deriv, gWeighted, ← tsum_mul_left]
  apply tsum_congr
  intro j
  by_cases hj : j=0
  · simp [hj, gTerm, gDerivTerm]
  · have hdegree : 1 ≤ 2*j := by omega
    have hp : t*t^(2*j-1)=t^(2*j) := by rw [← pow_succ', Nat.sub_add_cancel hdegree]
    dsimp only [gDerivTerm, gTerm]
    calc
      t*(c j*(2*j:ℝ)*t^(2*j-1)) = (2*j:ℝ)*c j*(t*t^(2*j-1)) := by ring
      _ = _ := by rw [hp]; ring
private lemma gPrefix_nonneg (hc : ∀j, 0<c j) (K : ℕ) (t : ℝ) : 0 ≤ gPrefix c K t :=
  Finset.sum_nonneg (fun j _ => gTerm_nonneg hc t j)
private lemma gPrefix_le_power (hc : ∀j, 0<c j) (K : ℕ) (hK : 0<K) {t : ℝ} (ht : 1 ≤ t) :
    gPrefix c K t  ≤  (∑j∈Finset.range K, c j)*t^(2*(K-1)) := by
  rw [gPrefix, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ ht (by have := Finset.mem_range.mp hj; omega)) (hc j).le
private lemma gPrefix_div_kernel_tendsto (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) (K : ℕ) :
    Tendsto (fun t : ℝ => gPrefix c K t/gKernel c t) atTop (𝓝 0) := by
  by_cases hK : K=0
  · simp [hK, gPrefix]
  have hKpos : 0<K := Nat.pos_of_ne_zero hK
  let A : ℝ := ∑j∈Finset.range K, c j
  let b : ℝ := c K
  have hb : 0<b := hc K
  have hlim : Tendsto (fun t : ℝ => (A/b)/t^2) atTop (𝓝 0) :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).const_div_atTop (A/b)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Eventually.of_forall (fun t => div_nonneg (gPrefix_nonneg hc K t)
      (gKernel_pos hc hR hbound t).le)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have htpos : 0<t := lt_of_lt_of_le zero_lt_one ht
    have hlower : b*t^(2*K)  ≤  gKernel c t := gTerm_le_kernel hc hR hbound t K
    calc
      gPrefix c K t/gKernel c t  ≤  gPrefix c K t/(b*t^(2*K)) :=
        div_le_div_of_nonneg_left (gPrefix_nonneg hc K t) (by positivity) hlower
      _  ≤  (A*t^(2*(K-1)))/(b*t^(2*K)) :=
        div_le_div_of_nonneg_right (gPrefix_le_power hc K hKpos ht) (by positivity)
      _ = (A/b)/t^2 := by
        rw [show 2*K=2*(K-1)+2 by omega, pow_add]
        have hp : t^(2*(K-1)) ≠ 0 := pow_ne_zero _ htpos.ne'
        field_simp
private lemma gWeighted_prefix_lower (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) (K : ℕ) (t : ℝ) :
    (2*K:ℝ)*(gKernel c t-gPrefix c K t)  ≤  gWeighted c t := by
  have hf := summable_gTerm hc hR hbound t
  have hg := summable_gWeighted hc hR hbound t
  have htail : (2*K:ℝ)*(∑'j, gTerm c t (j+K))  ≤
      ∑'j:ℕ, (2*(j+K):ℝ)*gTerm c t (j+K) := by
    rw [← tsum_mul_left]
    have hgs := (summable_nat_add_iff K).2 hg
    simp only [Nat.cast_add] at hgs
    apply Summable.tsum_le_tsum _ (((summable_nat_add_iff K).2 hf).mul_left (2*K:ℝ)) hgs
    intro j
    exact mul_le_mul_of_nonneg_right (by linarith) (gTerm_nonneg hc t (j+K))
  have hhead : 0 ≤ ∑j∈Finset.range K, (2*j:ℝ)*gTerm c t j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (gTerm_nonneg hc t j))
  have heqf := hf.sum_add_tsum_nat_add K
  have heqg := hg.sum_add_tsum_nat_add K
  simp only [Nat.cast_add] at heqg
  change (2*K:ℝ)*((∑'j, gTerm c t j)-(∑j∈Finset.range K, gTerm c t j))  ≤
    ∑'j:ℕ, (2*j:ℝ)*gTerm c t j
  rw [← heqf]
  simp only [add_sub_cancel_left]
  linarith
private lemma gWeighted_div_prefix_lower (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) (K : ℕ) (t : ℝ) :
    (2*K:ℝ)*(1-gPrefix c K t/gKernel c t)  ≤  gWeighted c t/gKernel c t := by
  have hp := gKernel_pos hc hR hbound t
  calc
    (2*K:ℝ)*(1-gPrefix c K t/gKernel c t) = ((2*K:ℝ)*(gKernel c t-gPrefix c K t))/gKernel c t := by field_simp
    _  ≤  _ := div_le_div_of_nonneg_right (gWeighted_prefix_lower hc hR hbound K t) hp.le
private lemma gWeighted_div_kernel_tendsto (hc : ∀j, 0<c j) (hR : 0 ≤ R)
    (hbound : ∀j, c j  ≤  R^j/(j.factorial:ℝ)) :
    Tendsto (fun t : ℝ => gWeighted c t/gKernel c t) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro L
  obtain ⟨K,hK⟩ := exists_nat_gt (max L 0)
  have hKL : L<(K:ℝ) := lt_of_le_of_lt (le_max_left _ _) hK
  have hKpos : 0<(K:ℝ) := lt_of_le_of_lt (le_max_right _ _) hK
  have hsmall : ∀ᶠt:ℝ in atTop, gPrefix c K t/gKernel c t<1/2 :=
    (gPrefix_div_kernel_tendsto hc hR hbound K).eventually_lt_const (by norm_num)
  filter_upwards [hsmall] with t ht
  have hlower := gWeighted_div_prefix_lower hc hR hbound K t
  nlinarith
private def gPositiveArea (F : ℝ→ℝ) (t : ℝ) : ℝ := ∫s in (0:ℝ)..t, max (F s) 0
private lemma positiveArea_lower {F B : ℝ→ℝ} (hF : Continuous F) (hB : Continuous B)
    (hBpos : ∀t, 0<B t) (hBmono : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → B a ≤ B b)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫s in (0:ℝ)..t, F s*B (t - s))/B t  ≤  gPositiveArea F t := by
  have hc : Continuous (fun s : ℝ=>B (t - s)) := hB.comp (continuous_const.sub continuous_id)
  have hm : Continuous (fun s=>max (F s) 0) := hF.max continuous_const
  have hle := intervalIntegral.integral_mono_on (μ:=volume) ht
    ((hF.mul hc).intervalIntegrable 0 t) ((hm.mul_const (B t)).intervalIntegrable 0 t)
    (fun s hs => calc
      F s*B (t - s)  ≤  max (F s) 0 * B (t - s) := mul_le_mul_of_nonneg_right (le_max_left _ _) (hBpos _).le
      _  ≤  max (F s) 0 * B t := mul_le_mul_of_nonneg_left (hBmono (by linarith [hs.2]) (by linarith [hs.1])) (le_max_right _ _))
  rw [intervalIntegral.integral_mul_const] at hle
  exact (div_le_iff₀ (hBpos t)).mpr (by simpa [gPositiveArea, mul_comm] using hle)
private lemma exists_pos_gt_of_positiveArea_tendsto {F : ℝ→ℝ} (hF : Continuous F)
    (harea : Tendsto (gPositiveArea F) atTop atTop) (T0 : ℝ) : ∃t>T0, 0<F t := by
  by_contra h
  have hnonpos : ∀t>T0, F t ≤ 0 := by simpa only [not_exists, not_and, not_lt] using h
  let T : ℝ := max T0 0 + 1
  have hTT0 : T0<T := by dsimp [T]; linarith [le_max_left T0 0]
  have hconst : ∀ᶠt:ℝ in atTop, gPositiveArea F t=gPositiveArea F T := by
    filter_upwards [eventually_ge_atTop T] with t ht
    have hc : Continuous (fun s=>max (F s) 0) := hF.max continuous_const
    have hz : (∫s in T..t, max (F s) 0)=0 := by
      calc
        _ = ∫s in T..t, (0:ℝ) := intervalIntegral.integral_congr (fun s hs => by
          have hst : T ≤ s := (Set.uIcc_of_le ht ▸ hs).1
          rw [max_eq_right (hnonpos s (hTT0.trans_le hst))])
        _ = 0 := by simp
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ:=volume) 0 T) (hc.intervalIntegrable (μ:=volume) T t)
    dsimp only [gPositiveArea]
    linarith
  have habove := harea.eventually_gt_atTop (gPositiveArea F T)
  obtain ⟨t,ht,hgt⟩ := (hconst.and habove).exists
  exact (ne_of_gt hgt) ht
private def dividedPower (n : ℕ) (t : ℝ) : ℝ := t^n/(n.factorial:ℝ)
@[fun_prop] private theorem continuous_dividedPower (n : ℕ) : Continuous (dividedPower n) := by
  unfold dividedPower
  fun_prop
private theorem dividedPower_deriv (n : ℕ) (t : ℝ) :
    HasDerivAt (dividedPower (n+1)) (dividedPower n t) t := by
  have h := ((hasDerivAt_id t).pow (n+1)).div_const ((n+1).factorial:ℝ)
  convert h using 1 <;> try rfl
  simp only [dividedPower, id_eq, Nat.add_sub_cancel, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_one]
  field_simp
private theorem integral_dividedPower_convolution (p q : ℕ) (t : ℝ) :
    ∫ s in 0..t, dividedPower p s * dividedPower q (t-s) =
      dividedPower (p+q+1) t := by
  induction q generalizing p with
  | zero =>
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a:=0) (b:=t) (fun x _ => dividedPower_deriv p x)
      (by exact (by fun_prop : Continuous (dividedPower p)).intervalIntegrable 0 t)
    simpa [dividedPower] using h
  | succ q ih =>
    have hu : ∀ x, HasDerivAt (fun s => dividedPower (q+1) (t-s))
        (-dividedPower q (t-x)) x := by
      intro x
      simpa only [Function.comp_def, zero_sub, mul_neg_one] using
        (dividedPower_deriv q (t-x)).comp x
          ((hasDerivAt_const x t).sub (hasDerivAt_id x))
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a:=0) (b:=t)
      (u:=fun s => dividedPower (q+1) (t-s)) (v:=dividedPower (p+1))
      (u':=fun s => -dividedPower q (t-s)) (v':=dividedPower p)
      (by fun_prop) (by fun_prop) (fun x _ => hu x)
      (fun x _ => dividedPower_deriv p x)
      ((by fun_prop : Continuous fun s => -dividedPower q (t-s)).intervalIntegrable 0 t)
      ((by fun_prop : Continuous (dividedPower p)).intervalIntegrable 0 t)
    simp only [dividedPower, sub_self, zero_pow (Nat.succ_ne_zero _), zero_div,
      zero_mul, mul_zero, sub_zero, zero_sub] at h
    have hn : (fun x : ℝ => -(dividedPower q (t-x)) * dividedPower (p+1) x) =
        (fun x => -(dividedPower q (t-x) * dividedPower (p+1) x)) := by
      funext x
      ring
    change (∫x in 0..t, dividedPower (q+1) (t-x)*dividedPower p x) =
      -(∫x in 0..t, -(dividedPower q (t-x))*dividedPower (p+1) x) at h
    rw [hn, intervalIntegral.integral_neg, neg_neg] at h
    calc
      (∫s in 0..t, dividedPower p s * dividedPower (q+1) (t-s)) =
          ∫s in 0..t, dividedPower (q+1) (t-s)*dividedPower p s := by
        congr 1
        funext s
        ring
      _ = ∫s in 0..t, dividedPower q (t-s)*dividedPower (p+1) s := h
      _ = ∫s in 0..t, dividedPower (p+1) s * dividedPower q (t-s) := by
        congr 1
        funext s
        ring
      _ = dividedPower (p+q+1+1) t := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (p+1)

private def pTerm (p : ℕ→ℝ) (t : ℝ) (j : ℕ) : ℝ := p j*t^(2*j+1)
private def pResponse (p : ℕ→ℝ) (t : ℝ) : ℝ := ∑'j, pTerm p t j
private def pBlock (p c : ℕ→ℝ) (t s : ℝ) (n : ℕ) : ℝ :=
  ∑j∈Finset.range (n+1), pTerm p s j*gTerm c (t-s) (n-j)
private lemma pTerm_bound {p : ℕ→ℝ} {s T : ℝ} (hT : 0 ≤ T) (hs : |s| ≤ T) (j : ℕ) :
    ‖pTerm p s j‖  ≤  ‖pTerm p T j‖ := by
  simp only [pTerm, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hT]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg s) hs _) (abs_nonneg _)
private lemma pBlock_hasSum {p c : ℕ→ℝ} (hp : ∀t, Summable (fun j=>‖pTerm p t j‖))
    (hc : ∀j, 0<c j) {R : ℝ} (hR : 0 ≤ R) (hbound : ∀j, c j ≤ R^j/(j.factorial:ℝ)) (t s : ℝ) :
    HasSum (pBlock p c t s) (pResponse p s*gKernel c (t-s)) :=
  hasSum_sum_range_mul_of_summable_norm (hp s) (summable_gTerm hc hR hbound (t-s)).norm
private lemma integral_pTerm_mul_gTerm (p c : ℕ→ℝ) (j k : ℕ) (t : ℝ) :
    (∫s in (0:ℝ)..t, pTerm p s j*gTerm c (t-s) k) =
      p j*c k*((2*j+1).factorial:ℝ)*((2*k).factorial:ℝ)*dividedPower (2*j+2*k+2) t := by
  have heq : (fun s : ℝ=>pTerm p s j*gTerm c (t-s) k) =
      (fun s : ℝ=> (p j*c k*((2*j+1).factorial:ℝ)*((2*k).factorial:ℝ))*
        (dividedPower (2*j+1) s*dividedPower (2*k) (t-s))) := by
    funext s
    dsimp only [pTerm,gTerm,dividedPower]
    have hf : ((2*j+1).factorial:ℝ) ≠ 0 := by positivity
    have hg : ((2*k).factorial:ℝ) ≠ 0 := by positivity
    field_simp
  rw [heq, intervalIntegral.integral_const_mul, integral_dividedPower_convolution]
  congr 1
  congr 1
  omega
private lemma integral_pBlock {p c : ℕ→ℝ}
    (hrec : ∀n, 2*(∑j∈Finset.range (n+1), p j*c (n-j)*((2*j+1).factorial:ℝ)*((2*(n-j)).factorial:ℝ)) =
      (2*n+2:ℝ)*c (n+1)*((2*n+2).factorial:ℝ)) (n : ℕ) (t : ℝ) :
    2*(∫s in (0:ℝ)..t, pBlock p c t s n) = (2*(n+1):ℝ)*gTerm c t (n+1) := by
  unfold pBlock
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [integral_pTerm_mul_gTerm]
    have heq : ∑j∈Finset.range (n+1),
        p j*c (n-j)*((2*j+1).factorial:ℝ)*((2*(n-j)).factorial:ℝ)*dividedPower (2*j+2*(n-j)+2) t =
      (∑j∈Finset.range (n+1), p j*c (n-j)*((2*j+1).factorial:ℝ)*((2*(n-j)).factorial:ℝ))*dividedPower (2*n+2) t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show 2*j+2*(n-j)+2=2*n+2 by have := Finset.mem_range.mp hj; omega]
    rw [heq, ← mul_assoc, hrec]
    dsimp only [dividedPower,gTerm]
    rw [show 2*(n+1)=2*n+2 by omega]
    have hf : ((2*n+2).factorial:ℝ) ≠ 0 := by positivity
    field_simp
  · intro j hj
    apply Continuous.intervalIntegrable
    unfold pTerm gTerm
    fun_prop
private lemma pResponse_volterra {p c : ℕ→ℝ} (hp : ∀t, Summable (fun j=>‖pTerm p t j‖))
    (hc : ∀j, 0<c j) {R : ℝ} (hR : 0 ≤ R) (hbound : ∀j, c j ≤ R^j/(j.factorial:ℝ))
    (hrec : ∀n, 2*(∑j∈Finset.range (n+1), p j*c (n-j)*((2*j+1).factorial:ℝ)*((2*(n-j)).factorial:ℝ)) =
      (2*n+2:ℝ)*c (n+1)*((2*n+2).factorial:ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    2*(∫s in (0:ℝ)..t, pResponse p s*gKernel c (t-s))=gWeighted c t := by
  let Q (n : ℕ) : ℝ := ∑j∈Finset.range (n+1), ‖pTerm p t j‖*((R*t^2)^(n-j)/((n-j).factorial:ℝ))
  have hQ : Summable Q := (hasSum_sum_range_mul_of_summable_norm
    (hp t).norm (Real.summable_pow_div_factorial (R*t^2)).norm).summable
  have hboundBlock (n : ℕ) : ∀ᵐs:ℝ, s∈Set.uIoc (0:ℝ) t → ‖pBlock p c t s n‖ ≤ Q n := by
    filter_upwards [] with s hs
    have hs0 : 0 ≤ s := (Set.uIoc_of_le ht ▸ hs).1.le
    have hst : s ≤ t := (Set.uIoc_of_le ht ▸ hs).2
    have hsa : |s| ≤ t := by rw [abs_of_nonneg hs0]; exact hst
    have htsa : |t-s| ≤ t := by rw [abs_of_nonneg (by linarith)]; linarith
    dsimp only [pBlock,Q]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_mul]
    exact mul_le_mul (pTerm_bound ht hsa j) (norm_gTerm_le hc hR hbound htsa (n-j))
      (norm_nonneg _) (norm_nonneg _)
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a:=0) (b:=t) (μ:=volume) (F:=fun n s=>pBlock p c t s n)
    (f:=fun s=>pResponse p s*gKernel c (t-s)) (fun n _=>Q n)
    (fun n=> (by unfold pBlock pTerm gTerm; fun_prop : Continuous (fun s=>pBlock p c t s n)).aestronglyMeasurable)
    hboundBlock (Eventually.of_forall (fun _ _=>hQ)) intervalIntegrable_const
    (Eventually.of_forall (fun s _=>pBlock_hasSum hp hc hR hbound t s))
  have hsum2 := hsum.mul_left 2
  have heq := hsum2.congr_fun (fun n=>(integral_pBlock hrec n t).symm)
  have hw := summable_gWeighted hc hR hbound t
  have hseries := hw.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_mul, zero_add] at hseries
  change _ = ∑'j:ℕ, (2*j:ℝ)*gTerm c t j
  rw [← hseries]
  simpa only [Nat.cast_add,Nat.cast_one] using heq.tsum_eq.symm
private lemma symLaplace_even_deriv (N j : ℕ) :
    iteratedDeriv (2*j) (symLaplace N) 0 = (liClockPairedEtaSymmetrizedEvenMoment N j : ℂ) := by
  have hfun : complexMGF (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaSymmetrizedMeasure N) = symLaplace N :=
    funext (sym_complexMGF_eq N)
  rw [← hfun]
  exact sym_even_deriv N j
/-- Raw even cumulant of order `2*j+2` selected from the actual partition logarithmic derivative. -/
def liClockPairedEtaPartitionEvenCumulant (N j : ℕ) : ℝ :=
  (iteratedDeriv (2*j+1) (logDeriv (pairedEtaFiniteLaplacePartition N)) (1/2:ℂ)).re
private lemma moment_recurrence {N : ℕ} (hN : 0<N) (n : ℕ) :
    liClockPairedEtaSymmetrizedEvenMoment N (n+1) =
      ∑j∈Finset.range (n+1), ((2*n+1).choose (2*j+1):ℝ)*2*liClockPairedEtaPartitionEvenCumulant N j*
        liClockPairedEtaSymmetrizedEvenMoment N (n-j) := by
  have h := sym_recurrence hN n
  rw [show 2*n+2=2*(n+1) by omega, symLaplace_even_deriv] at h
  simp_rw [symLaplace_even_deriv] at h
  have hre := congrArg Complex.re h
  simpa [Complex.mul_re,liClockPairedEtaPartitionEvenCumulant] using hre
/-- Exact coefficient with both raw odd factorials in the literal partition clock. -/
def liClockPairedEtaPartitionClockCoefficient (N j : ℕ) : ℝ :=
  liClockPairedEtaPartitionEvenCumulant N j/((2*j+1).factorial:ℝ)^2
/-- Exact normalized difference-moment coefficient with both even factorials. -/
def liClockPairedEtaPartitionBorelCoefficient (N j : ℕ) : ℝ :=
  liClockPairedEtaSymmetrizedEvenMoment N j/((2*j).factorial:ℝ)^2
private lemma liClockPairedEtaPartitionBorelCoefficient_pos {N : ℕ} (hN : 0<N) (j : ℕ) :
    0<liClockPairedEtaPartitionBorelCoefficient N j := div_pos (sym_moment_pos hN j) (by positivity)
private lemma liClockPairedEtaPartitionBorelCoefficient_bound {N : ℕ} (hN : 0<N) (j : ℕ) :
    liClockPairedEtaPartitionBorelCoefficient N j  ≤  (Real.log (2*(N:ℝ))^2)^j/(j.factorial:ℝ) := by
  have hf : (j.factorial:ℝ)  ≤  ((2*j).factorial:ℝ)^2 := by
    have h1 : (j.factorial:ℝ)  ≤  ((2*j).factorial:ℝ) := by exact_mod_cast Nat.factorial_le (show j ≤ 2*j by omega)
    have h2 : (1:ℝ) ≤ ((2*j).factorial:ℝ) := by exact_mod_cast Nat.factorial_le (Nat.zero_le (2*j))
    nlinarith
  unfold liClockPairedEtaPartitionBorelCoefficient
  calc
    liClockPairedEtaSymmetrizedEvenMoment N j/((2*j).factorial:ℝ)^2  ≤
        Real.log (2*(N:ℝ))^(2*j)/((2*j).factorial:ℝ)^2 :=
      div_le_div_of_nonneg_right (sym_moment_bound hN j) (sq_nonneg _)
    _  ≤  Real.log (2*(N:ℝ))^(2*j)/(j.factorial:ℝ) :=
      div_le_div_of_nonneg_left (by rw [pow_mul]; positivity) (by positivity) hf
    _ = _ := by rw [pow_mul]
private lemma partitionCoefficient_recurrence {N : ℕ} (hN : 0<N) (n : ℕ) :
    2*(∑j∈Finset.range (n+1), liClockPairedEtaPartitionClockCoefficient N j*liClockPairedEtaPartitionBorelCoefficient N (n-j)*
      ((2*j+1).factorial:ℝ)*((2*(n-j)).factorial:ℝ)) =
      (2*n+2:ℝ)*liClockPairedEtaPartitionBorelCoefficient N (n+1)*((2*n+2).factorial:ℝ) := by
  have hfact : ((2*n+1).factorial:ℝ) ≠ 0 := by positivity
  have hs : 2*(∑j∈Finset.range (n+1), liClockPairedEtaPartitionClockCoefficient N j*liClockPairedEtaPartitionBorelCoefficient N (n-j)*
      ((2*j+1).factorial:ℝ)*((2*(n-j)).factorial:ℝ)) =
    (∑j∈Finset.range (n+1), ((2*n+1).choose (2*j+1):ℝ)*2*liClockPairedEtaPartitionEvenCumulant N j*
      liClockPairedEtaSymmetrizedEvenMoment N (n-j))/((2*n+1).factorial:ℝ) := by
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
    have hh := Nat.choose_mul_factorial_mul_factorial (show 2*j+1 ≤ 2*n+1 by omega)
    rw [show 2*n+1-(2*j+1)=2*(n-j) by omega] at hh
    have hc : ((2*n+1).choose (2*j+1):ℝ)*((2*j+1).factorial:ℝ)*((2*(n-j)).factorial:ℝ) =
        ((2*n+1).factorial:ℝ) := by exact_mod_cast hh
    have hchoose : ((2*n+1).choose (2*j+1):ℝ) ≠ 0 := by
      intro hz
      rw [hz,zero_mul,zero_mul] at hc
      exact hfact hc.symm
    rw [← hc]
    dsimp only [liClockPairedEtaPartitionClockCoefficient,liClockPairedEtaPartitionBorelCoefficient]
    have hf : ((2*j+1).factorial:ℝ) ≠ 0 := by positivity
    have hg : ((2*(n-j)).factorial:ℝ) ≠ 0 := by positivity
    field_simp
  rw [hs, ← moment_recurrence hN]
  have hfnext : ((2*n+2).factorial:ℝ)=(2*n+2:ℝ)*((2*n+1).factorial:ℝ) := by
    rw [show 2*n+2=(2*n+1)+1 by omega,Nat.factorial_succ]
    push_cast
    ring
  dsimp only [liClockPairedEtaPartitionBorelCoefficient]
  rw [show 2*(n+1)=2*n+2 by omega,hfnext]
  have hdegree : (2*n+2:ℝ) ≠ 0 := by positivity
  field_simp
private lemma partitionTrace_odd (N j : ℕ) :
    iteratedDeriv (2*j+1) (liClockPairedEtaPartitionSourceTrace N) 0 =
      (-1:ℂ)^(j+1)*iteratedDeriv (2*j+1) (logDeriv (pairedEtaFiniteLaplacePartition N)) (1/2) := by
  unfold liClockPairedEtaPartitionSourceTrace
  have hc : (fun z : ℂ=>logDeriv (pairedEtaFiniteLaplacePartition N) (1/2+z*I)) =
      (fun z=>logDeriv (pairedEtaFiniteLaplacePartition N) (I*z+1/2)) := by funext z; congr 1; ring
  rw [iteratedDeriv_const_mul_field,hc, GaloisForLFunctions.liClock_iteratedDeriv_comp_affine]
  simp only [mul_zero,zero_add]
  have hi : (I:ℂ)*(I:ℂ)^(2*j+1)=(-1:ℂ)^(j+1) := by
    rw [← pow_succ',show 2*j+1+1=2*(j+1) by omega,pow_mul,Complex.I_sq]
  rw [← mul_assoc,hi]
/-- Literal complete partition-source odd derivative at every complex clock. -/
def liClockPairedEtaPartitionClockSeriesTerm (N : ℕ) (t : ℂ) (j : ℕ) : ℂ :=
  iteratedDeriv (2*j+1) (logDeriv (pairedEtaFiniteLaplacePartition N)) (1/2)*t^(2*j+1)/((2*j+1).factorial:ℂ)^2
private lemma liClockPairedEtaPartitionClockSeriesTerm_eq_neg (N : ℕ) (t : ℂ) (j : ℕ) :
    liClockPairedEtaPartitionClockSeriesTerm N t j = -liClockCentralTraceSineContourTerm (liClockPairedEtaPartitionSourceTrace N) t j := by
  unfold liClockPairedEtaPartitionClockSeriesTerm liClockCentralTraceSineContourTerm
  rw [partitionTrace_odd]
  have hs : (-1:ℂ)^j*(-1:ℂ)^(j+1)= -1 := by
    rw [← pow_add,show j+(j+1)=2*j+1 by omega,pow_add,pow_mul]
    norm_num
  rw [← mul_assoc,hs]
  ring
private lemma partition_real_term (N : ℕ) (t : ℝ) (j : ℕ) :
    (liClockPairedEtaPartitionClockSeriesTerm N (t:ℂ) j).re=pTerm (liClockPairedEtaPartitionClockCoefficient N) t j := by
  unfold liClockPairedEtaPartitionClockSeriesTerm pTerm liClockPairedEtaPartitionClockCoefficient liClockPairedEtaPartitionEvenCumulant
  have hd : (((((2*j+1).factorial:ℝ)^2):ℝ):ℂ)=((2*j+1).factorial:ℂ)^2 := by norm_cast
  rw [←hd,←Complex.ofReal_pow,Complex.div_ofReal_re]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  ring
private lemma partitionTrace_analytic {N : ℕ} {z : ℂ}
    (hn : pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0) :
    AnalyticAt ℂ (liClockPairedEtaPartitionSourceTrace N) z := by
  have ha := analyticAt_liClockPairedEtaFiniteLaplacePartition_entire N (1/2+z*I)
  exact analyticAt_const.mul ((ha.deriv.div ha hn).comp (f:=fun z : ℂ=>1/2+z*I)
    (analyticAt_const.add (analyticAt_id.mul analyticAt_const)))
private lemma partitionTrace_diffCont {N : ℕ} {r : ℝ}
    (hclosed : ∀z∈closedBall (0:ℂ) r, pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0) :
    DiffContOnCl ℂ (liClockPairedEtaPartitionSourceTrace N) (ball (0:ℂ) r) := by
  have ha : AnalyticOnNhd ℂ (liClockPairedEtaPartitionSourceTrace N) (closedBall (0:ℂ) r) :=
    fun z hz=>partitionTrace_analytic (hclosed z hz)
  exact ha.differentiableOn.diffContOnCl_ball (Subset.refl _)
private lemma liClockPairedEtaPartitionClockSeriesTerm_summable {N : ℕ} {r : ℝ} (hr : 0<r)
    (hclosed : ∀z∈closedBall (0:ℂ) r, pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0) (t : ℂ) :
    Summable (fun j=>‖liClockPairedEtaPartitionClockSeriesTerm N t j‖) := by
  apply (summable_norm_liClockCentralTraceSineContourTerm hr (partitionTrace_diffCont hclosed) t).congr
  intro j
  rw [liClockPairedEtaPartitionClockSeriesTerm_eq_neg,norm_neg]
private lemma partitionPterm_summable {N : ℕ} {r : ℝ} (hr : 0<r)
    (hclosed : ∀z∈closedBall (0:ℂ) r, pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0) (t : ℝ) :
    Summable (fun j=>‖pTerm (liClockPairedEtaPartitionClockCoefficient N) t j‖) := by
  apply (liClockPairedEtaPartitionClockSeriesTerm_summable hr hclosed (t:ℂ)).of_nonneg_of_le
  · intro j
    exact norm_nonneg _
  · intro j
    rw [← partition_real_term]
    exact Complex.abs_re_le_norm _
private lemma partitionClock_eq_series {N : ℕ} {r : ℝ} (hr : 0<r)
    (hclosed : ∀z∈closedBall (0:ℂ) r, pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0) (t : ℝ) :
    (liClockPairedEtaPartitionClockResponse N r (t:ℂ)).re=pResponse (liClockPairedEtaPartitionClockCoefficient N) t := by
  rw [liClockPairedEtaPartitionClockResponse,liClockCentralTraceSineContour_eq_neg_tsum hr (partitionTrace_diffCont hclosed)]
  have heq : -(∑'j, liClockCentralTraceSineContourTerm (liClockPairedEtaPartitionSourceTrace N) (t:ℂ) j) =
      ∑'j,liClockPairedEtaPartitionClockSeriesTerm N (t:ℂ) j := by
    rw [← tsum_neg]
    exact tsum_congr (fun j=>(liClockPairedEtaPartitionClockSeriesTerm_eq_neg N (t:ℂ) j).symm)
  rw [heq,Complex.re_tsum (liClockPairedEtaPartitionClockSeriesTerm_summable hr hclosed (t:ℂ)).of_norm]
  exact tsum_congr (partition_real_term N t)
private lemma partition_conj (N : ℕ) (s : ℂ) :
    pairedEtaFiniteLaplacePartition N (conj s)=conj (pairedEtaFiniteLaplacePartition N s) := by
  rw [pairedEtaFiniteLaplacePartition_eq_integral_logMeasure,
    pairedEtaFiniteLaplacePartition_eq_integral_logMeasure,←integral_conj]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [←Complex.exp_conj,map_neg,map_mul,Complex.conj_ofReal]
private lemma partition_deriv_conj (N : ℕ) (s : ℂ) :
    deriv (pairedEtaFiniteLaplacePartition N) (conj s)=conj (deriv (pairedEtaFiniteLaplacePartition N) s) := by
  have hf : (conj ∘ pairedEtaFiniteLaplacePartition N ∘ conj)=pairedEtaFiniteLaplacePartition N := by
    funext z
    simp only [Function.comp_def,partition_conj,Complex.conj_conj]
  have hd := deriv_conj_conj (f:=pairedEtaFiniteLaplacePartition N)
  rw [hf] at hd
  simpa only [Function.comp_def,Complex.conj_conj] using congrFun hd (conj s)
private lemma partition_logDeriv_conj (N : ℕ) (s : ℂ) :
    logDeriv (pairedEtaFiniteLaplacePartition N) (conj s)=conj (logDeriv (pairedEtaFiniteLaplacePartition N) s) := by
  simp only [logDeriv,Pi.div_apply,partition_deriv_conj,partition_conj,map_div₀]
private lemma partitionTrace_neg_conj (N : ℕ) (z : ℂ) :
    liClockPairedEtaPartitionSourceTrace N (-conj z) = -conj (liClockPairedEtaPartitionSourceTrace N z) := by
  have hs : (1/2:ℂ)+ -conj z*I=conj (1/2+z*I) := by
    simp only [map_add,map_mul,map_div₀,map_one,map_ofNat,Complex.conj_I]
    ring
  unfold liClockPairedEtaPartitionSourceTrace
  rw [hs,partition_logDeriv_conj]
  simp only [map_mul,Complex.conj_I]
  ring
/-- The Borel kernel of the complete normalized finite interval-union difference measure. -/
def liClockPairedEtaPartitionBorelKernel (N : ℕ) (t : ℝ) : ℝ :=
  gKernel (liClockPairedEtaPartitionBorelCoefficient N) t
/-- Exact even degree weighted over the full finite-source Borel series. -/
def liClockPairedEtaPartitionBorelWeighted (N : ℕ) (t : ℝ) : ℝ :=
  gWeighted (liClockPairedEtaPartitionBorelCoefficient N) t
/-- The real literal partition contour at a real clock. -/
def liClockPairedEtaPartitionClockResponseReal (N : ℕ) (r t : ℝ) : ℝ :=
  (liClockPairedEtaPartitionClockResponse N r (t:ℂ)).re
/-- Integrated positive part of the literal partition clock. -/
def liClockPairedEtaPartitionPositivePartArea (N : ℕ) (r t : ℝ) : ℝ :=
  gPositiveArea (liClockPairedEtaPartitionClockResponseReal N r) t

theorem liClockPairedEtaPartitionNormalizer_pos {N : ℕ} (hN : 0<N) :
    0<liClockPairedEtaPartitionNormalizer N := normalizer_pos hN

theorem liClockPairedEtaSymmetrizedMeasure_isProbability {N : ℕ} (hN : 0<N) :
    IsProbabilityMeasure (liClockPairedEtaSymmetrizedMeasure N) := sym_measure_probability hN

theorem liClockPairedEtaSymmetrizedEvenMoment_zero {N : ℕ} (hN : 0<N) :
    liClockPairedEtaSymmetrizedEvenMoment N 0=1 := sym_moment_zero hN

theorem liClockPairedEtaSymmetrizedEvenMoment_pos {N : ℕ} (hN : 0<N) (j : ℕ) :
    0<liClockPairedEtaSymmetrizedEvenMoment N j := sym_moment_pos hN j

theorem liClockPairedEtaSymmetrizedEvenMoment_le_log_power {N : ℕ} (hN : 0<N) (j : ℕ) :
    liClockPairedEtaSymmetrizedEvenMoment N j ≤ Real.log (2*(N:ℝ))^(2*j) := sym_moment_bound hN j

theorem liClockPairedEtaSymmetrizedEvenMoment_eq_double_integral (N j : ℕ) :
    liClockPairedEtaSymmetrizedEvenMoment N j =
      (∫p:ℝ×ℝ, (p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2)
        ∂(pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)) /
        liClockPairedEtaPartitionNormalizer N^2 := by
  rw [liClockPairedEtaSymmetrizedEvenMoment,liClockPairedEtaSymmetrizedMeasure,
    integral_tilted,joint_weight_integral]
  simp only [smul_eq_mul]
  have heq : (fun p:ℝ×ℝ=>Real.exp (-(p.1+p.2)/2)/liClockPairedEtaPartitionNormalizer N^2 *
      (p.1-p.2)^(2*j)) =
    (fun p:ℝ×ℝ=>((p.1-p.2)^(2*j)*Real.exp (-(p.1+p.2)/2))/liClockPairedEtaPartitionNormalizer N^2) := by
    funext p
    ring
  rw [heq,integral_div]

theorem liClockPairedEtaSymmetrizedMeasure_complexMGF_eq_source (N : ℕ) (z : ℂ) :
    complexMGF (fun p:ℝ×ℝ=>p.1-p.2) (liClockPairedEtaSymmetrizedMeasure N) z =
      pairedEtaFiniteLaplacePartition N (1/2-z)*pairedEtaFiniteLaplacePartition N (1/2+z) /
        (liClockPairedEtaPartitionNormalizer N:ℂ)^2 := by
  rw [sym_complexMGF_eq,normalizer_eq]

theorem liClockPairedEtaPartitionSourceTrace_diffContOnCl {N : ℕ} {r : ℝ}
    (hclosed : ∀z∈closedBall (0:ℂ) r, pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0) :
    DiffContOnCl ℂ (liClockPairedEtaPartitionSourceTrace N) (ball (0:ℂ) r) := partitionTrace_diffCont hclosed

theorem liClockPairedEtaPartitionSourceTrace_neg_conj (N : ℕ) (z : ℂ) :
    liClockPairedEtaPartitionSourceTrace N (-conj z) = -conj (liClockPairedEtaPartitionSourceTrace N z) :=
  partitionTrace_neg_conj N z

theorem liClockPairedEtaPartitionClockResponse_im_ofReal_eq_zero {N : ℕ} {r : ℝ} (hr : 0<r)
    (hclosed : ∀z∈closedBall (0:ℂ) r, pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0) (t : ℝ) :
    (liClockPairedEtaPartitionClockResponse N r (t:ℂ)).im=0 :=
  liClockCentralTraceSineContour_im_ofReal_eq_zero hr (partitionTrace_diffCont hclosed)
    (partitionTrace_neg_conj N) t

theorem continuous_liClockPairedEtaPartitionClockResponseReal {N : ℕ} {r : ℝ} (hr : 0<r)
    (hclosed : ∀z∈closedBall (0:ℂ) r, pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0) :
    Continuous (liClockPairedEtaPartitionClockResponseReal N r) := by
  have hc := continuous_liClockCentralTraceSineContour hr
    ((partitionTrace_diffCont hclosed).continuousOn_ball.mono sphere_subset_closedBall)
  exact Complex.continuous_re.comp (hc.comp Complex.continuous_ofReal)

theorem liClockPairedEtaPartitionBorelKernel_pos {N : ℕ} (hN : 0<N) (t : ℝ) :
    0<liClockPairedEtaPartitionBorelKernel N t :=
  gKernel_pos (liClockPairedEtaPartitionBorelCoefficient_pos hN) (sq_nonneg _) (liClockPairedEtaPartitionBorelCoefficient_bound hN) t

theorem liClockPairedEtaPartitionBorelKernel_mono {N : ℕ} (hN : 0<N) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    liClockPairedEtaPartitionBorelKernel N a ≤ liClockPairedEtaPartitionBorelKernel N b :=
  gKernel_mono (liClockPairedEtaPartitionBorelCoefficient_pos hN) (sq_nonneg _) (liClockPairedEtaPartitionBorelCoefficient_bound hN) ha hab

theorem continuous_liClockPairedEtaPartitionBorelKernel {N : ℕ} (hN : 0<N) :
    Continuous (liClockPairedEtaPartitionBorelKernel N) :=
  continuous_gKernel (liClockPairedEtaPartitionBorelCoefficient_pos hN) (sq_nonneg _) (liClockPairedEtaPartitionBorelCoefficient_bound hN)

theorem liClockPairedEtaPartitionBorel_mul_deriv {N : ℕ} (hN : 0<N) (t : ℝ) :
    t*deriv (liClockPairedEtaPartitionBorelKernel N) t = liClockPairedEtaPartitionBorelWeighted N t :=
  gKernel_mul_deriv (liClockPairedEtaPartitionBorelCoefficient_pos hN) (sq_nonneg _) (liClockPairedEtaPartitionBorelCoefficient_bound hN) t

/-- The literal finite partition clock has exactly twice the symmetrized source cumulant response. -/
theorem liClockPairedEtaPartitionClockResponse_volterra {N : ℕ} (hN : 0<N) {r : ℝ} (hr : 0<r)
    (hclosed : ∀z∈closedBall (0:ℂ) r, pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    2*(∫s in (0:ℝ)..t, liClockPairedEtaPartitionClockResponseReal N r s*
      liClockPairedEtaPartitionBorelKernel N (t-s)) =
      t*deriv (liClockPairedEtaPartitionBorelKernel N) t := by
  rw [liClockPairedEtaPartitionBorel_mul_deriv hN]
  have h := pResponse_volterra (partitionPterm_summable hr hclosed)
    (liClockPairedEtaPartitionBorelCoefficient_pos hN) (sq_nonneg _) (liClockPairedEtaPartitionBorelCoefficient_bound hN)
    (partitionCoefficient_recurrence hN) ht
  have heq : liClockPairedEtaPartitionClockResponseReal N r=pResponse (liClockPairedEtaPartitionClockCoefficient N) :=
    funext (partitionClock_eq_series hr hclosed)
  rw [heq]
  exact h

/-- Every finite source prefix becomes negligible against a positive higher even degree. -/
theorem liClockPairedEtaPartitionBorelWeighted_div_kernel_tendsto_atTop {N : ℕ} (hN : 0<N) :
    Tendsto (fun t:ℝ=>liClockPairedEtaPartitionBorelWeighted N t/liClockPairedEtaPartitionBorelKernel N t)
      atTop atTop :=
  gWeighted_div_kernel_tendsto (liClockPairedEtaPartitionBorelCoefficient_pos hN) (sq_nonneg _) (liClockPairedEtaPartitionBorelCoefficient_bound hN)

/-- Exact quantitative positive-part area lower bound; the symmetrization contributes factor two. -/
theorem liClockPairedEtaPartitionPositivePartArea_lower {N : ℕ} (hN : 0<N) {r : ℝ} (hr : 0<r)
    (hclosed : ∀z∈closedBall (0:ℂ) r, pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    t*deriv (liClockPairedEtaPartitionBorelKernel N) t/(2*liClockPairedEtaPartitionBorelKernel N t)  ≤
      liClockPairedEtaPartitionPositivePartArea N r t := by
  have hle := positiveArea_lower (continuous_liClockPairedEtaPartitionClockResponseReal hr hclosed)
    (continuous_liClockPairedEtaPartitionBorelKernel hN) (liClockPairedEtaPartitionBorelKernel_pos hN)
    (fun ha hab=>liClockPairedEtaPartitionBorelKernel_mono hN ha hab) ht
  have hconv := liClockPairedEtaPartitionClockResponse_volterra hN hr hclosed ht
  have heq : (∫s in (0:ℝ)..t, liClockPairedEtaPartitionClockResponseReal N r s*
      liClockPairedEtaPartitionBorelKernel N (t-s)) = t*deriv (liClockPairedEtaPartitionBorelKernel N) t/2 := by linarith
  rw [heq] at hle
  simpa only [div_div,mul_comm,liClockPairedEtaPartitionPositivePartArea] using hle

/-- Complete positive-part area diverges on the actual finite union at every regular source radius. -/
theorem liClockPairedEtaPartitionClockResponse_positivePartArea_tendsto_atTop {N : ℕ} (hN : 0<N)
    {r : ℝ} (hr : 0<r)
    (hclosed : ∀z∈closedBall (0:ℂ) r, pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0) :
    Tendsto (liClockPairedEtaPartitionPositivePartArea N r) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro L
  have hdegree := (liClockPairedEtaPartitionBorelWeighted_div_kernel_tendsto_atTop hN).eventually_ge_atTop (2*L)
  filter_upwards [hdegree,eventually_ge_atTop (0:ℝ)] with t hdeg ht
  have harea := liClockPairedEtaPartitionPositivePartArea_lower hN hr hclosed ht
  rw [liClockPairedEtaPartitionBorel_mul_deriv hN] at harea
  have hb := liClockPairedEtaPartitionBorelKernel_pos hN t
  have hdiv : liClockPairedEtaPartitionBorelWeighted N t/(2*liClockPairedEtaPartitionBorelKernel N t)=
      (liClockPairedEtaPartitionBorelWeighted N t/liClockPairedEtaPartitionBorelKernel N t)/2 := by field_simp
  rw [hdiv] at harea
  linarith

/-- Positive literal partition clocks occur on every tail, without a completion compensation premise. -/
theorem liClockPairedEtaPartitionClockResponse_exists_pos_gt {N : ℕ} (hN : 0<N) {r : ℝ} (hr : 0<r)
    (hclosed : ∀z∈closedBall (0:ℂ) r, pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0) (T0 : ℝ) :
    ∃t>T0, 0<(liClockPairedEtaPartitionClockResponse N r (t:ℂ)).re :=
  exists_pos_gt_of_positiveArea_tendsto (continuous_liClockPairedEtaPartitionClockResponseReal hr hclosed)
    (liClockPairedEtaPartitionClockResponse_positivePartArea_tendsto_atTop hN hr hclosed) T0


/-- The complete finite source retains both raw odd factorials in every clock coefficient. -/
theorem liClockPairedEtaPartitionClockResponse_eq_tsum {N : ℕ} {r : ℝ} (hr : 0 < r)
    (hclosed : ∀ z ∈ closedBall (0 : ℂ) r, pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0) (t : ℂ) :
    liClockPairedEtaPartitionClockResponse N r t = ∑' j, liClockPairedEtaPartitionClockSeriesTerm N t j := by
  rw [liClockPairedEtaPartitionClockResponse,liClockCentralTraceSineContour_eq_neg_tsum hr (partitionTrace_diffCont hclosed),←tsum_neg]
  exact tsum_congr (fun j => (liClockPairedEtaPartitionClockSeriesTerm_eq_neg N t j).symm)

theorem summable_norm_liClockPairedEtaPartitionClockSeriesTerm {N : ℕ} {r : ℝ} (hr : 0 < r)
    (hclosed : ∀ z ∈ closedBall (0 : ℂ) r, pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0) (t : ℂ) :
    Summable (fun j => ‖liClockPairedEtaPartitionClockSeriesTerm N t j‖) :=
  liClockPairedEtaPartitionClockSeriesTerm_summable hr hclosed t

/-- Exact finite normalized cumulant coefficient recurrence, with the symmetrization factor two. -/
theorem liClockPairedEtaPartition_cumulantConvolution {N : ℕ} (hN : 0 < N) (n : ℕ) :
    2*(∑ j ∈ Finset.range (n+1), liClockPairedEtaPartitionClockCoefficient N j*
      liClockPairedEtaPartitionBorelCoefficient N (n-j)*
      ((2*j+1).factorial : ℝ)*((2*(n-j)).factorial : ℝ)) =
      (2*n+2 : ℝ)*liClockPairedEtaPartitionBorelCoefficient N (n+1)*((2*n+2).factorial : ℝ) :=
  partitionCoefficient_recurrence hN n

theorem liClockPairedEtaPartitionBorelKernel_eq_tsum (N : ℕ) (t : ℝ) :
    liClockPairedEtaPartitionBorelKernel N t = ∑' j,
      liClockPairedEtaSymmetrizedEvenMoment N j*t^(2*j)/((2*j).factorial : ℝ)^2 := by
  unfold liClockPairedEtaPartitionBorelKernel gKernel
  apply tsum_congr
  intro j
  unfold gTerm liClockPairedEtaPartitionBorelCoefficient
  ring

theorem summable_liClockPairedEtaPartitionBorelTerm {N : ℕ} (hN : 0 < N) (t : ℝ) :
    Summable (fun j => liClockPairedEtaSymmetrizedEvenMoment N j*t^(2*j)/((2*j).factorial : ℝ)^2) := by
  apply (summable_gTerm (liClockPairedEtaPartitionBorelCoefficient_pos hN) (sq_nonneg _)
    (liClockPairedEtaPartitionBorelCoefficient_bound hN) t).congr
  intro j
  unfold gTerm liClockPairedEtaPartitionBorelCoefficient
  ring

theorem hasDerivAt_liClockPairedEtaPartitionBorelKernel {N : ℕ} (hN : 0 < N) (t : ℝ) :
    HasDerivAt (liClockPairedEtaPartitionBorelKernel N)
      (∑' j, liClockPairedEtaPartitionBorelCoefficient N j*(2*j : ℝ)*t^(2*j-1)) t :=
  hasDerivAt_gKernel (liClockPairedEtaPartitionBorelCoefficient_pos hN) (sq_nonneg _)
    (liClockPairedEtaPartitionBorelCoefficient_bound hN) t

/-- The centered phase strip gives a regular closed source disk at every positive prefix length. -/
theorem liClockPairedEtaPartition_regularDisk_of_phase {N : ℕ} (hN : 0 < N) {r : ℝ}
    (hphase : r*Real.log (2*(N : ℝ)) < Real.pi) :
    ∀ z ∈ closedBall (0 : ℂ) r, pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0 := by
  intro z hz
  have hl : 0 ≤ Real.log (2*(N : ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*N by omega))
  have hzn : ‖z‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hz
  have him : (1/2+z*I).im=z.re := by norm_num [Complex.mul_im]
  apply liClockPairedEtaFiniteLaplacePartition_ne_zero hN
  rw [him]
  exact (mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm z).trans hzn) hl).trans hphase.le

/-- Every actual positive finite prefix admits a regular central contour. -/
theorem liClockPairedEtaPartition_exists_regular_radius {N : ℕ} (hN : 0 < N) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ closedBall (0 : ℂ) r,
      pairedEtaFiniteLaplacePartition N (1/2+z*I) ≠ 0 := by
  have hl : 0 ≤ Real.log (2*(N : ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*N by omega))
  let r : ℝ := Real.pi/(2*(Real.log (2*(N : ℝ))+1))
  have hr : 0 < r := div_pos Real.pi_pos (by positivity)
  have hp : r*Real.log (2*(N : ℝ)) < Real.pi := by
    dsimp only [r]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(Real.log (2*(N : ℝ))+1))).2
    nlinarith [mul_nonneg Real.pi_pos.le hl, Real.pi_pos]
  exact ⟨r,hr,liClockPairedEtaPartition_regularDisk_of_phase hN hp⟩

/-- Cofinal positive partition clocks are unconditional for every actual nonempty finite union. -/
theorem liClockPairedEtaPartition_exists_regular_positive_clock_cofinally {N : ℕ} (hN : 0 < N) :
    ∃ r : ℝ, 0 < r ∧ ∀ T0 : ℝ, ∃ t > T0,
      0 < (liClockPairedEtaPartitionClockResponse N r (t : ℂ)).re := by
  obtain ⟨r,hr,hclosed⟩ := liClockPairedEtaPartition_exists_regular_radius hN
  exact ⟨r,hr,liClockPairedEtaPartitionClockResponse_exists_pos_gt hN hr hclosed⟩
end
end RHTower
