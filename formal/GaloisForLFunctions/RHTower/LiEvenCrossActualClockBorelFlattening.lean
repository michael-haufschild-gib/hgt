import GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelCorrection
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelGrowth
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Fixed-shift flattening of the actual theta Borel kernel

The full actual-source kernel and its derivative have vanishing logarithmic
slopes and unit ratios under every fixed bounded shift. Their weighted degrees
still escape. Every ordinary derivative is admitted from compact complete
factorial envelopes before the limits or finite-interval FTC are used.
-/

open Filter Topology Set
namespace RHTower
noncomputable section
local notation "B" => liEvenCrossActualClockBorelKernel
local notation "K" => deriv liEvenCrossActualClockBorelKernel

private def tfTerm (m j : ℕ) (t : ℝ) : ℝ :=
  liEvenCrossActualClockBorelCoefficient j * ((2*j).descFactorial m : ℝ) *
    t^(2*j-m)

private def tfSeries (m : ℕ) (t : ℝ) : ℝ := ∑' j, tfTerm m j t

private theorem tf_coefficient_le_inverse_factorial (j : ℕ) :
    liEvenCrossActualClockBorelCoefficient j ≤ ((j.factorial : ℝ))⁻¹ := by
  have hp : (32/303 : ℝ)^j ≤ 1 := by
    simpa using pow_le_pow_left₀ (by norm_num : 0 ≤ (32/303 : ℝ))
      (by norm_num : (32/303 : ℝ) ≤ 1) j
  calc
    liEvenCrossActualClockBorelCoefficient j ≤
        (32/303 : ℝ)^j/(j.factorial : ℝ) := liEvenCrossActualClockBorelCoefficient_le j
    _ ≤ 1/(j.factorial : ℝ) :=
      div_le_div_of_nonneg_right hp (by positivity)
    _ = _ := one_div _

private theorem tf_term_bound (m j : ℕ) {t T : ℝ}
    (hT : 1 ≤ T) (ht : |t| ≤ T) :
    ‖tfTerm m j t‖ ≤ (2:ℝ)^m*(j:ℝ)^m*
      liEvenCrossActualClockBorelCoefficient j*T^(2*j) := by
  have hd : ((2*j).descFactorial m : ℝ) ≤ (2:ℝ)^m*(j:ℝ)^m := by
    calc
      ((2*j).descFactorial m : ℝ) ≤ (((2*j : ℕ) : ℝ))^m := by
        exact_mod_cast Nat.descFactorial_le_pow (2*j) m
      _ = _ := by push_cast; rw [mul_pow]
  have hp : |t|^(2*j-m) ≤ T^(2*j) :=
    (pow_le_pow_left₀ (abs_nonneg t) ht _).trans
      (pow_le_pow_right₀ hT (Nat.sub_le _ _))
  have hc := (liEvenCrossActualClockBorelCoefficient_pos j).le
  rw [tfTerm, norm_mul, norm_mul, Real.norm_eq_abs,
    abs_of_pos (liEvenCrossActualClockBorelCoefficient_pos j),
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), norm_pow, Real.norm_eq_abs]
  calc
    liEvenCrossActualClockBorelCoefficient j * ((2*j).descFactorial m : ℝ) *
        |t|^(2*j-m) ≤
      (liEvenCrossActualClockBorelCoefficient j*((2:ℝ)^m*(j:ℝ)^m))*T^(2*j) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd
        (liEvenCrossActualClockBorelCoefficient_pos j).le) hp
        (by positivity) (by positivity)
    _ = _ := by ring

private theorem tf_envelope_summable (m : ℕ) {T : ℝ} (_hT : 0 ≤ T) :
    Summable (fun j : ℕ => (2:ℝ)^m*(j:ℝ)^m*
      liEvenCrossActualClockBorelCoefficient j*T^(2*j)) := by
  have hc (j : ℕ) : ‖(liEvenCrossActualClockBorelCoefficient j : ℂ)‖ ≤
      ((j.factorial : ℝ))⁻¹ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (liEvenCrossActualClockBorelCoefficient_pos j)]
      using tf_coefficient_le_inverse_factorial j
  have hs := GaloisForLFunctions.HTGeometry.summable_pow_mul_of_factorial_decay
    hc m (sq_nonneg T)
  have he : (fun j : ℕ => (2:ℝ)^m*((j:ℝ)^m*
        (‖(liEvenCrossActualClockBorelCoefficient j : ℂ)‖*(T^2)^j))) =
      (fun j : ℕ => (2:ℝ)^m*(j:ℝ)^m*
        liEvenCrossActualClockBorelCoefficient j*T^(2*j)) := by
    funext j
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (liEvenCrossActualClockBorelCoefficient_pos j), ← pow_mul]
    ring
  rw [← he]
  exact hs.mul_left _

private theorem tf_norm_summable (m : ℕ) (t : ℝ) :
    Summable (fun j => ‖tfTerm m j t‖) := by
  let T := |t|+1
  have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => tf_term_bound m j hT (by dsimp [T]; linarith))
    (tf_envelope_summable m (by linarith))

private theorem tf_summable (m : ℕ) (t : ℝ) : Summable (fun j => tfTerm m j t) :=
  (tf_norm_summable m t).of_norm

private theorem tf_term_hasDerivAt (m j : ℕ) (t : ℝ) :
    HasDerivAt (tfTerm m j) (tfTerm (m+1) j t) t := by
  have he : 2*j-(m+1) = 2*j-m-1 := by omega
  convert (((hasDerivAt_id t).pow (2*j-m)).const_mul
    (liEvenCrossActualClockBorelCoefficient j*((2*j).descFactorial m : ℝ))) using 1 <;>
    first | rfl | (simp only [tfTerm, Nat.descFactorial_succ, Nat.cast_mul,
      id_eq, mul_one, he]; ring)

private theorem tf_series_hasDerivAt (m : ℕ) (t : ℝ) :
    HasDerivAt (tfSeries m) (tfSeries (m+1) t) t := by
  let T := |t|+1
  have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  exact hasDerivAt_tsum_of_isPreconnected
    (tf_envelope_summable (m+1) (by linarith)) Metric.isOpen_ball
    (convex_ball (0:ℝ) T).isPreconnected
    (fun j y _ => tf_term_hasDerivAt m j y)
    (fun j y hy => tf_term_bound (m+1) j hT
      (le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hy)))
    (by simp [Metric.mem_ball, T]; positivity) (tf_summable m 0)
    (by simp [Metric.mem_ball, T])

private theorem tf_series_zero : tfSeries 0 = liEvenCrossActualClockBorelKernel := by
  funext t
  unfold tfSeries liEvenCrossActualClockBorelKernel
  apply tsum_congr
  intro j
  simp [tfTerm, liEvenCrossActualClockBorelTerm_eq_coefficient_mul]

private theorem tf_iteratedDeriv (m : ℕ) :
    iteratedDeriv m liEvenCrossActualClockBorelKernel = tfSeries m := by
  induction m with
  | zero => simpa using tf_series_zero.symm
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (tf_series_hasDerivAt m t).deriv

private theorem tf_first_deriv : deriv liEvenCrossActualClockBorelKernel = tfSeries 1 := by
  rw [← iteratedDeriv_one, tf_iteratedDeriv]

private theorem tf_hasDerivAt_iterated (m : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv m B) (iteratedDeriv (m+1) B t) t := by
  rw [tf_iteratedDeriv m, tf_iteratedDeriv (m+1)]
  exact tf_series_hasDerivAt m t

private theorem tf_continuous_iterated (m : ℕ) : Continuous (iteratedDeriv m B) :=
  continuous_iff_continuousAt.mpr (fun t => (tf_hasDerivAt_iterated m t).continuousAt)

/-- The literal complete actual-source kernel has genuine derivatives at every order. -/
theorem contDiff_liEvenCrossActualClockBorelKernel :
    ContDiff ℝ (⊤ : ℕ∞) liEvenCrossActualClockBorelKernel := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  exact fun t => (tf_hasDerivAt_iterated m t).differentiableAt

private theorem tf_hasDerivAt_K (t : ℝ) :
    HasDerivAt K (iteratedDeriv 2 B t) t := by
  simpa only [iteratedDeriv_one] using tf_hasDerivAt_iterated 1 t

private theorem tf_hasDerivAt_B (t : ℝ) : HasDerivAt B (K t) t := by
  simpa only [Nat.zero_add, iteratedDeriv_zero, iteratedDeriv_one] using tf_hasDerivAt_iterated 0 t

private theorem tf_continuous_K : Continuous K := by
  simpa only [iteratedDeriv_one] using tf_continuous_iterated 1

private theorem tf_nonneg (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ iteratedDeriv m B t := by
  rw [tf_iteratedDeriv]
  exact tsum_nonneg (fun j => by
    unfold tfTerm
    exact mul_nonneg (mul_nonneg (liEvenCrossActualClockBorelCoefficient_pos j).le
      (Nat.cast_nonneg _)) (pow_nonneg ht _))

private theorem tf_K_lower {t : ℝ} (ht : 0 ≤ t) :
    (2*liEvenCrossActualClockBorelCoefficient 1)*t ≤ K t := by
  have hs := (liEvenCrossActualClockBorel_deriv_series t).2
  have h := hs.summable.le_tsum 0 (fun r _ => by
    have hc := (liEvenCrossActualClockBorelCoefficient_pos (r+1)).le
    positivity)
  simpa only [Nat.zero_add, Nat.mul_zero, Nat.cast_zero, zero_add, mul_one, pow_one] using h.trans_eq hs.tsum_eq

private theorem tf_K_tendsto : Tendsto K atTop atTop := by
  have hc : 0 < 2*liEvenCrossActualClockBorelCoefficient 1 :=
    mul_pos (by norm_num) (liEvenCrossActualClockBorelCoefficient_pos 1)
  exact tendsto_atTop_mono' atTop
    ((eventually_ge_atTop (0:ℝ)).mono (fun t ht => tf_K_lower ht))
    (tendsto_id.const_mul_atTop hc)

/-- The second derivative of the actual positive first-derivative profile is negligible. -/
theorem tendsto_liEvenCrossActualClockBorel_third_div_deriv_zero :
    Tendsto (fun t : ℝ => iteratedDeriv 3 B t / K t) atTop (𝓝 (0 : ℝ)) := by
  have hlim : Tendsto (fun t : ℝ =>
      (liEvenCrossActualClockBorelCorrection t/K t)/3) atTop (𝓝 (0:ℝ)) := by
    simpa using tendsto_liEvenCrossActualClockBorelCorrection_div_deriv.div_const 3
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact div_nonneg (tf_nonneg 3 ht.le) (liEvenCrossActualClockBorel_deriv_pos ht).le
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    have hK := liEvenCrossActualClockBorel_deriv_pos ht
    have hD : 3*iteratedDeriv 3 B t ≤ liEvenCrossActualClockBorelCorrection t := by
      rw [liEvenCrossActualClockBorelCorrection_eq_derivatives]
      exact le_add_of_nonneg_right (mul_nonneg ht.le (tf_nonneg 4 ht.le))
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<3)).mpr
    have h := div_le_div_of_nonneg_right hD hK.le
    rw [mul_div_assoc] at h
    simpa only [mul_comm] using h

/-- The clock-weighted third derivative of the positive derivative profile is negligible. -/
theorem tendsto_liEvenCrossActualClockBorel_clock_fourth_div_deriv_zero :
    Tendsto (fun t : ℝ => t*iteratedDeriv 4 B t/K t) atTop (𝓝 (0:ℝ)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_liEvenCrossActualClockBorelCorrection_div_deriv
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact div_nonneg (mul_nonneg ht.le (tf_nonneg 4 ht.le))
      (liEvenCrossActualClockBorel_deriv_pos ht).le
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    apply div_le_div_of_nonneg_right _ (liEvenCrossActualClockBorel_deriv_pos ht).le
    rw [liEvenCrossActualClockBorelCorrection_eq_derivatives]
    exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (tf_nonneg 3 ht.le))

private theorem tf_energy_bound {η T t : ℝ} (hT : 0 < T) (ht : T ≤ t)
    (hcurv : ∀ u : ℝ, T ≤ u → iteratedDeriv 3 B u ≤ η^2*K u) :
    (iteratedDeriv 2 B t)^2-η^2*(K t)^2 ≤
      (iteratedDeriv 2 B T)^2-η^2*(K T)^2 := by
  let E := fun u : ℝ => (iteratedDeriv 2 B u)^2-η^2*(K u)^2
  have hd (u : ℝ) : HasDerivAt E
      (2*iteratedDeriv 2 B u*(iteratedDeriv 3 B u-η^2*K u)) u := by
    convert ((tf_hasDerivAt_iterated 2 u).pow 2).sub
      (((tf_hasDerivAt_K u).pow 2).const_mul (η^2)) using 1 <;>
      first | rfl | ring
  have hc : Continuous E :=
    ((tf_continuous_iterated 2).pow 2).sub (continuous_const.mul (tf_continuous_K.pow 2))
  have ha : AntitoneOn E (Ici T) := antitoneOn_of_deriv_nonpos (convex_Ici T)
    hc.continuousOn (fun u _ => (hd u).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [(hd u).deriv]
      have hTu : T ≤ u := interior_subset hu
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by norm_num) (tf_nonneg 2 (hT.le.trans hTu)))
        (sub_nonpos.mpr (hcurv u hTu)))
  exact ha (by simp) ht ht

/-- Energy control turns the actual curvature limit into a vanishing logarithmic slope. -/
theorem tendsto_liEvenCrossActualClockBorel_second_div_deriv_zero :
    Tendsto (fun t : ℝ => iteratedDeriv 2 B t/K t) atTop (𝓝 (0:ℝ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε/2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨T0,hT0⟩ := eventually_atTop.mp
    (tendsto_liEvenCrossActualClockBorel_third_div_deriv_zero.eventually_lt_const
      (show 0 < η^2 by positivity))
  let T := max T0 1
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hcurv (u : ℝ) (hu : T ≤ u) : iteratedDeriv 3 B u ≤ η^2*K u := by
    have hu0 : T0 ≤ u := (le_max_left _ _).trans hu
    have hKu := liEvenCrossActualClockBorel_deriv_pos (hT.trans_le hu)
    exact (div_le_iff₀ hKu).mp (hT0 u hu0).le
  let C := max ((iteratedDeriv 2 B T)^2-η^2*(K T)^2) 0
  have hp : Tendsto (fun t : ℝ => (K t)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).comp tf_K_tendsto
  have hdecay : Tendsto (fun t : ℝ => C/(K t)^2) atTop (𝓝 (0:ℝ)) := hp.const_div_atTop C
  filter_upwards [eventually_ge_atTop T,
    hdecay.eventually_lt_const (show 0 < 3*ε^2/4 by positivity)] with t ht hsmall
  have htpos := hT.trans_le ht
  have hK := liEvenCrossActualClockBorel_deriv_pos htpos
  have hnn := div_nonneg (tf_nonneg 2 htpos.le) hK.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  by_contra hbad
  have hmul : ε*K t ≤ iteratedDeriv 2 B t := (le_div_iff₀ hK).mp (le_of_not_gt hbad)
  have hsq := pow_le_pow_left₀ (mul_nonneg hε.le hK.le) hmul 2
  have hE := tf_energy_bound hT ht hcurv
  have hEC : (iteratedDeriv 2 B T)^2-η^2*(K T)^2 ≤ C := le_max_left _ _
  have hsmall' : C < (3*ε^2/4)*(K t)^2 := (div_lt_iff₀ (sq_pos_of_pos hK)).mp hsmall
  dsimp [η] at hE hEC
  nlinarith

private theorem tf_log_shift_bound {f fp : ℝ → ℝ} {t S η : ℝ}
    (hS : 0 ≤ S) (hη : 0 ≤ η)
    (hf : ContinuousOn f (Icc (t-S) (t+S)))
    (hfp : ContinuousOn fp (Icc (t-S) (t+S)))
    (hpos : ∀ u ∈ Icc (t-S) (t+S), 0 < f u)
    (hd : ∀ u ∈ Icc (t-S) (t+S), HasDerivAt f (fp u) u)
    (hb : ∀ u ∈ Icc (t-S) (t+S), |fp u/f u| ≤ η)
    {s : ℝ} (hs : s ∈ Icc (-S) S) :
    |Real.log (f (t+s))-Real.log (f t)| ≤ S*η := by
  have hsub : uIcc t (t+s) ⊆ Icc (t-S) (t+S) := by
    intro u hu
    change min t (t+s) ≤ u ∧ u ≤ max t (t+s) at hu
    exact ⟨(le_min (by linarith) (by linarith [hs.1])).trans hu.1,
      hu.2.trans (max_le (by linarith) (by linarith [hs.2]))⟩
  have hcont : ContinuousOn (fun u => fp u/f u) (uIcc t (t+s)) :=
    (hfp.mono hsub).div (hf.mono hsub) (fun u hu => (hpos u (hsub hu)).ne')
  have hi : IntervalIntegrable (fun u => fp u/f u) MeasureTheory.volume t (t+s) :=
    hcont.intervalIntegrable
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => (hd u (hsub hu)).log (hpos u (hsub hu)).ne') hi
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := t+s) (f := fun u => fp u/f u) (C := η) (fun u hu => by
      have hu' : u ∈ uIcc t (t+s) := ⟨hu.1.le,hu.2⟩
      simpa only [Real.norm_eq_abs] using hb u (hsub hu'))
  rw [he,Real.norm_eq_abs] at hn
  rw [add_sub_cancel_left] at hn
  exact hn.trans ((mul_le_mul_of_nonneg_left (abs_le.mpr hs) hη).trans_eq (mul_comm η S))

private theorem tf_exp_abs_sub_one (y : ℝ) :
    |Real.exp y-1| ≤ Real.exp |y|-1 := by
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy, abs_of_nonneg (sub_nonneg.mpr
      (by simpa using Real.exp_le_exp.mpr hy))]
  · have hy' : y ≤ 0 := le_of_not_ge hy
    have he : Real.exp y ≤ 1 := by simpa using Real.exp_le_exp.mpr hy'
    rw [abs_of_nonpos (sub_nonpos.mpr he), abs_of_nonpos hy']
    have hn : 1 ≤ Real.exp (-y) := by simpa using Real.exp_le_exp.mpr (neg_nonneg.mpr hy')
    have hi : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr he)]

private theorem tf_uniform_shift {f fp : ℝ → ℝ}
    (hf : Continuous f) (hfp : Continuous fp)
    (hd : ∀ t : ℝ, HasDerivAt f (fp t) t)
    (hpos : ∀ t : ℝ, 0 < t → 0 < f t)
    (hq : Tendsto (fun t : ℝ => fp t/f t) atTop (𝓝 (0:ℝ)))
    {S : ℝ} (hS : 0 ≤ S) :
    TendstoUniformlyOn (fun t : ℝ => fun s : ℝ => f (t+s)/f t)
      (fun _ : ℝ => (1:ℝ)) atTop (Icc (-S) S) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let η := Real.log (1+ε)/(S+1)
  have hη : 0 < η := div_pos (Real.log_pos (by linarith)) (by linarith)
  have hηeq : η*(S+1) = Real.log (1+ε) := div_mul_cancel₀ _ (by linarith : S+1≠0)
  have hsmall : Real.exp (S*η)-1 < ε := by
    have he := Real.exp_lt_exp.mpr (show S*η < Real.log (1+ε) by nlinarith)
    rw [Real.exp_log (by linarith : 0 < 1+ε)] at he
    linarith
  obtain ⟨T,hT⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hq) η hη)
  filter_upwards [eventually_ge_atTop (max T 1+S)] with t ht
  intro s hs
  have hlu (u : ℝ) (hu : u ∈ Icc (t-S) (t+S)) : T ≤ u ∧ 0 < u := by
    have h1 := le_max_left T 1
    have h2 := le_max_right T 1
    constructor <;> linarith [hu.1]
  have hP : ∀ u ∈ Icc (t-S) (t+S), 0 < f u :=
    fun u hu => hpos u (hlu u hu).2
  have hbound : ∀ u ∈ Icc (t-S) (t+S), |fp u/f u| ≤ η := by
    intro u hu
    have hh := hT u (hlu u hu).1
    simpa only [Real.dist_eq,sub_zero] using hh.le
  have hlog := tf_log_shift_bound hS hη.le hf.continuousOn hfp.continuousOn
    hP (fun u _ => hd u) hbound hs
  have htmem : t ∈ Icc (t-S) (t+S) := by constructor <;> linarith
  have htsmem : t+s ∈ Icc (t-S) (t+S) := by constructor <;> linarith [hs.1,hs.2]
  have heq : f (t+s)/f t = Real.exp (Real.log (f (t+s))-Real.log (f t)) := by
    rw [Real.exp_sub,Real.exp_log (hP _ htsmem),Real.exp_log (hP _ htmem)]
  rw [Real.dist_eq,abs_sub_comm,heq]
  exact ((tf_exp_abs_sub_one _).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr hlog) 1)).trans_lt hsmall

/-- Every fixed compact interval of shifts has a uniform unit ratio for the actual derivative. -/
theorem tendstoUniformlyOn_liEvenCrossActualClockBorel_deriv_shift_ratio
    {S : ℝ} (hS : 0 ≤ S) :
    TendstoUniformlyOn
      (fun t : ℝ => fun s : ℝ =>
        deriv liEvenCrossActualClockBorelKernel (t+s)/
          deriv liEvenCrossActualClockBorelKernel t)
      (fun _ : ℝ => (1:ℝ)) atTop (Icc (-S) S) :=
  tf_uniform_shift tf_continuous_K (tf_continuous_iterated 2) tf_hasDerivAt_K
    (fun _ ht => liEvenCrossActualClockBorel_deriv_pos ht)
    tendsto_liEvenCrossActualClockBorel_second_div_deriv_zero hS

private theorem tf_primitive (t : ℝ) : B t = 1+∫ u in 0..t, K u := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := t) (f := B) (f' := K)
    (fun u _ => tf_hasDerivAt_B u) (tf_continuous_K.intervalIntegrable 0 t)
  rw [liEvenCrossActualClockBorelKernel_zero] at he
  linarith

private theorem tf_last_interval {L t : ℝ} (hL : 0 < L) (ht : L ≤ t) :
    (∫ v in 0..L, K (t-v)/K t) ≤ B t/K t := by
  have hK := liEvenCrossActualClockBorel_deriv_pos (hL.trans_le ht)
  have h0 : IntervalIntegrable K MeasureTheory.volume 0 (t-L) :=
    tf_continuous_K.intervalIntegrable 0 (t-L)
  have h1 : IntervalIntegrable K MeasureTheory.volume (t-L) t :=
    tf_continuous_K.intervalIntegrable (t-L) t
  have hs := intervalIntegral.integral_add_adjacent_intervals h0 h1
  have hn : 0 ≤ ∫ u in 0..(t-L), K u :=
    intervalIntegral.integral_nonneg (by linarith) (fun u hu => by
      simpa only [iteratedDeriv_one] using tf_nonneg 1 hu.1)
  have hb : (∫ u in (t-L)..t, K u) ≤ B t := by
    rw [tf_primitive]
    linarith
  rw [intervalIntegral.integral_div]
  have hc : (∫ v in 0..L, K (t-v)) = ∫ u in (t-L)..t, K u := by
    simpa only [sub_zero] using
      (intervalIntegral.integral_comp_sub_left (a := 0) (b := L) K t)
  rw [hc]
  exact div_le_div_of_nonneg_right hb hK.le

private theorem tf_kernel_div_deriv_atTop :
    Tendsto (fun t : ℝ => B t/K t) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  let L := 2*max M 0+2
  have hL : 0 < L := by dsimp [L]; positivity
  have hML : M < L/2 := by dsimp [L]; linarith [le_max_left M 0]
  have hu := (Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_liEvenCrossActualClockBorel_deriv_shift_ratio hL.le))
    (1/2) (by norm_num)
  filter_upwards [hu,eventually_ge_atTop L] with t hut ht
  have hp : ∀ v ∈ Icc (0:ℝ) L, (1/2:ℝ) ≤ K (t-v)/K t := by
    intro v hv
    have hh := hut (-v) (by constructor <;> linarith [hv.1,hv.2])
    rw [Real.dist_eq] at hh
    have hh' := (abs_lt.mp hh).2
    simpa only [sub_eq_add_neg] using (show (1/2:ℝ) ≤ K (t+ -v)/K t by linarith)
  have hc : Continuous (fun v : ℝ => K (t-v)/K t) :=
    (tf_continuous_K.comp (continuous_const.sub continuous_id)).div_const _
  have hi := intervalIntegral.integral_mono_on hL.le
    (continuous_const.intervalIntegrable 0 L :
      IntervalIntegrable (fun _ : ℝ => (1/2:ℝ)) MeasureTheory.volume 0 L)
    (hc.intervalIntegrable 0 L) hp
  have hi' : L/2 ≤ ∫ v in 0..L, K (t-v)/K t := by
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one_div] using hi
  exact (hML.trans_le (hi'.trans (tf_last_interval hL ht))).le

/-- The genuine logarithmic slope of the full actual kernel tends to zero. -/
theorem tendsto_liEvenCrossActualClockBorel_deriv_div_kernel_zero :
    Tendsto (fun t : ℝ => deriv B t/B t) atTop (𝓝 (0:ℝ)) := by
  simpa only [Function.comp_def, inv_div] using tendsto_inv_atTop_zero.comp tf_kernel_div_deriv_atTop

/-- Every fixed compact interval of shifts has a uniform unit ratio for the actual kernel. -/
theorem tendstoUniformlyOn_liEvenCrossActualClockBorel_kernel_shift_ratio
    {S : ℝ} (hS : 0 ≤ S) :
    TendstoUniformlyOn
      (fun t : ℝ => fun s : ℝ =>
        liEvenCrossActualClockBorelKernel (t+s)/liEvenCrossActualClockBorelKernel t)
      (fun _ : ℝ => (1:ℝ)) atTop (Icc (-S) S) :=
  tf_uniform_shift continuous_liEvenCrossActualClockBorelKernel tf_continuous_K
    tf_hasDerivAt_B (fun t _ => liEvenCrossActualClockBorelKernel_pos t)
    tendsto_liEvenCrossActualClockBorel_deriv_div_kernel_zero hS

private def tfB (r : ℕ) : ℝ :=
  (2*(r+1):ℝ)*liEvenCrossActualClockBorelCoefficient (r+1)

private def tfKTerm (r : ℕ) (t : ℝ) : ℝ := tfB r*t^(2*r+1)

private def tfKPrefix (k : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.range k, tfKTerm r t

private theorem tfB_pos (r : ℕ) : 0 < tfB r := by
  unfold tfB
  exact mul_pos (by positivity) (liEvenCrossActualClockBorelCoefficient_pos (r+1))

private theorem tfKTerm_nonneg (r : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ tfKTerm r t := mul_nonneg (tfB_pos r).le (pow_nonneg ht _)

private theorem tfK_hasSum (t : ℝ) : HasSum (fun r => tfKTerm r t) (K t) := by
  exact (liEvenCrossActualClockBorel_deriv_series t).2

private theorem tfKPrefix_nonneg (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ tfKPrefix k t :=
  Finset.sum_nonneg (fun r _ => tfKTerm_nonneg r ht)

private theorem tfKPrefix_le_power (k : ℕ) (hk : 0 < k) {t : ℝ} (ht : 1 ≤ t) :
    tfKPrefix k t ≤ (∑ r ∈ Finset.range k, tfB r)*t^(2*(k-1)+1) := by
  rw [tfKPrefix, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r hr
  unfold tfKTerm
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ ht (by have := Finset.mem_range.mp hr; omega)) (tfB_pos r).le

private theorem tfKPrefix_div_tendsto (k : ℕ) :
    Tendsto (fun t : ℝ => tfKPrefix k t/K t) atTop (𝓝 (0:ℝ)) := by
  by_cases hk : k = 0
  · simp [hk, tfKPrefix]
  have hkpos := Nat.pos_of_ne_zero hk
  let A : ℝ := ∑ r ∈ Finset.range k, tfB r
  let b := tfB k
  have hb : 0 < b := tfB_pos k
  have hlim : Tendsto (fun t : ℝ => (A/b)/t^2) atTop (𝓝 (0:ℝ)) :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).const_div_atTop (A/b)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact div_nonneg (tfKPrefix_nonneg k ht.le) (liEvenCrossActualClockBorel_deriv_pos ht).le
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have htpos : 0 < t := zero_lt_one.trans_le ht
    have hlower : b*t^(2*k+1) ≤ K t := by
      have hh := (tfK_hasSum t).summable.le_tsum k (fun r _ => tfKTerm_nonneg r htpos.le)
      exact hh.trans_eq (tfK_hasSum t).tsum_eq
    calc
      tfKPrefix k t/K t ≤ tfKPrefix k t/(b*t^(2*k+1)) :=
        div_le_div_of_nonneg_left (tfKPrefix_nonneg k htpos.le) (by positivity) hlower
      _ ≤ (A*t^(2*(k-1)+1))/(b*t^(2*k+1)) :=
        div_le_div_of_nonneg_right (tfKPrefix_le_power k hkpos ht) (by positivity)
      _ = (A/b)/t^2 := by
        rw [show 2*k+1=(2*(k-1)+1)+2 by omega, pow_add]
        have hp : t^(2*(k-1)+1)≠0 := pow_ne_zero _ htpos.ne'
        field_simp
        simp only [pow_add, pow_one]
        ring

private theorem tf_shifted_hasSum {f : ℕ → ℝ} (hf : Summable f) (k : ℕ)
    (hz : ∀ j, j < k → f j = 0) : HasSum (fun r => f (r+k)) (∑' j, f j) := by
  have hh : ∑ j ∈ Finset.range k, f j = 0 :=
    Finset.sum_eq_zero (fun j hj => hz j (Finset.mem_range.mp hj))
  have he := hf.sum_add_tsum_nat_add k
  rw [hh, zero_add] at he
  rw [← he]
  exact ((summable_nat_add_iff k).mpr hf).hasSum

private theorem tfK_weighted_hasSum (t : ℝ) :
    HasSum (fun r : ℕ => (2*r+1:ℝ)*tfKTerm r t) (t*iteratedDeriv 2 B t) := by
  have hs := (tf_shifted_hasSum (tf_summable 2 t) 1
    (fun j hj => by
      have hj0 : j = 0 := by omega
      simp [hj0, tfTerm])).mul_left t
  have he (r : ℕ) : t*tfTerm 2 (r+1) t = (2*r+1:ℝ)*tfKTerm r t := by
    have hn : 2*(r+1)-2 = 2*r := by omega
    have hpow : t*t^(2*r) = t^(2*r+1) := by rw [pow_succ]; ring
    have hd : (((2*(r+1)).descFactorial 2 : ℕ) : ℝ) =
        (2*(r+1):ℝ)*(2*r+1:ℝ) := by
      rw [Nat.descFactorial_succ, Nat.descFactorial_one, Nat.cast_mul,
        Nat.cast_sub (by omega : 1 ≤ 2*(r+1))]
      push_cast
      ring
    simp only [tfTerm, tfKTerm, tfB, hn, hd]
    rw [← hpow]
    ring
  have hh := hs.congr_fun (fun r => (he r).symm)
  simpa only [tf_iteratedDeriv, tfSeries] using hh

private theorem tfK_prefix_lower (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (2*k+1:ℝ)*(K t-tfKPrefix k t) ≤ t*iteratedDeriv 2 B t := by
  have hf := (tfK_hasSum t).summable
  have hg := (tfK_weighted_hasSum t).summable
  have htail : (2*k+1:ℝ)*(∑' r, tfKTerm (r+k) t) ≤
      ∑' r : ℕ, (2*(r+k)+1:ℝ)*tfKTerm (r+k) t := by
    rw [← tsum_mul_left]
    have hgs := (summable_nat_add_iff k).mpr hg
    simp only [Nat.cast_add] at hgs
    apply Summable.tsum_le_tsum _
      (((summable_nat_add_iff k).mpr hf).mul_left _)
      hgs
    intro r
    exact mul_le_mul_of_nonneg_right (by
      have hr : (0:ℝ) ≤ r := Nat.cast_nonneg r
      linarith) (tfKTerm_nonneg _ ht)
  have hhead : 0 ≤ ∑ r ∈ Finset.range k, (2*r+1:ℝ)*tfKTerm r t :=
    Finset.sum_nonneg (fun r _ => mul_nonneg (by positivity) (tfKTerm_nonneg r ht))
  have heqf := hf.sum_add_tsum_nat_add k
  have heqg := hg.sum_add_tsum_nat_add k
  rw [(tfK_hasSum t).tsum_eq] at heqf
  rw [(tfK_weighted_hasSum t).tsum_eq] at heqg
  simp only [Nat.cast_add] at heqg
  change (2*k+1:ℝ)*(K t-(∑ r ∈ Finset.range k, tfKTerm r t)) ≤ _
  rw [← heqf]
  simp only [add_sub_cancel_left]
  linarith

/-- The actual derivative profile still escapes every finite degree despite its vanishing slope. -/
theorem tendsto_liEvenCrossActualClockBorel_deriv_logarithmicDegree_atTop :
    Tendsto (fun t : ℝ => t*iteratedDeriv 2 liEvenCrossActualClockBorelKernel t/
      deriv liEvenCrossActualClockBorelKernel t) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  obtain ⟨k,hk⟩ := exists_nat_gt (max M 0)
  have hMk : M < (k:ℝ) := (le_max_left _ _).trans_lt hk
  have hkpos : 0 < (k:ℝ) := (le_max_right _ _).trans_lt hk
  have hsmall := (tfKPrefix_div_tendsto k).eventually_lt_const (by norm_num : (0:ℝ)<1/2)
  filter_upwards [hsmall,eventually_gt_atTop (0:ℝ)] with t ht htpos
  have hK := liEvenCrossActualClockBorel_deriv_pos htpos
  have hlower := div_le_div_of_nonneg_right (tfK_prefix_lower k htpos.le) hK.le
  have he : ((2*k+1:ℝ)*(K t-tfKPrefix k t))/K t =
      (2*k+1:ℝ)*(1-tfKPrefix k t/K t) := by field_simp
  rw [he] at hlower
  nlinarith


private theorem tf_Kprime_lower {t : ℝ} (ht : 0 ≤ t) :
    2*liEvenCrossActualClockBorelCoefficient 1 ≤ iteratedDeriv 2 B t := by
  have h := (tf_summable 2 t).le_tsum 1 (fun j _ => by
    unfold tfTerm
    exact mul_nonneg (mul_nonneg (liEvenCrossActualClockBorelCoefficient_pos j).le
      (Nat.cast_nonneg _)) (pow_nonneg ht _))
  have he : tfTerm 2 1 t = 2*liEvenCrossActualClockBorelCoefficient 1 := by
    norm_num [tfTerm, Nat.descFactorial_succ]
    ring
  rw [he] at h
  simpa only [tf_iteratedDeriv, tfSeries] using h

end
end RHTower
