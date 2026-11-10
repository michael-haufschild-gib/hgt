import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.ComplexNormalSummability
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.JointTangentRealization

/-!
# The joint Euler normal form of a pole-preserving gauge family

Complex normal prime summability constructs the joint Euler logarithm on
a parameter disk times a half-plane left of one. Its exponential times
the zeta residue factor is the unique actual joint pole germ. Together
with necessity, this characterizes bounded holomorphic gauge families
that admit a joint pole regularization.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- Change in one Euler logarithm relative to the untwisted prime coordinate. -/
def jointEulerChange (u : Nat.Primes → ℂ → ℂ) (p : Nat.Primes) (q : ℂ × ℂ) : ℂ :=
  Complex.log (1 - Complex.exp (-(q.2 * (primeFrequency p : ℂ)))) -
    Complex.log (1 - u p q.1 * Complex.exp (-(q.2 * (primeFrequency p : ℂ))))

/-- The normally convergent joint Euler logarithm difference. -/
def jointDeformationExponent (u : Nat.Primes → ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  ∑' p, jointEulerChange u p q

/-- The canonical pole regularization associated to the prime-coordinate family. -/
def jointGaugeRegularization (u : Nat.Primes → ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  zetaResidueFactor q.2 * Complex.exp (jointDeformationExponent u q)

/-- The closed-disk deviation is a genuine nonnegative supremum inside the holomorphy disk. -/
theorem primeDiskDeviation_bounds {u : Nat.Primes → ℂ → ℂ} {r R M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hb : ∀ p z, z ∈ ball (0 : ℂ) R → ‖u p z‖ ≤ M) (p : Nat.Primes) :
    0 ≤ primeDiskDeviation u r p ∧
      ∀ z : ℂ, ‖z‖ ≤ r → ‖u p z - 1‖ ≤ primeDiskDeviation u r p := by
  have hbound : BddAbove ((fun z : ℂ => ‖u p z - 1‖) '' closedBall 0 r) := by
    refine ⟨M + 1, ?_⟩
    rintro v ⟨z, hz, rfl⟩
    have hzR : z ∈ ball (0 : ℂ) R := closedBall_subset_ball hrR hz
    exact (norm_sub_le _ _).trans (by
      rw [norm_one]
      linarith only [hb p z hzR])
  have hzero : (0 : ℂ) ∈ closedBall 0 r := mem_closedBall_self hr
  refine ⟨(norm_nonneg (u p 0 - 1)).trans (le_csSup hbound ⟨0, hzero, rfl⟩), ?_⟩
  intro z hz
  exact le_csSup hbound ⟨z, by simpa only [mem_closedBall, dist_zero_right] using hz, rfl⟩

private theorem exists_prime_phase_small_disk {u : Nat.Primes → ℂ → ℂ} {R r M : ℝ}
    (hR : 0 < R) (hr : 0 < r)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hb : ∀ p z, z ∈ ball (0 : ℂ) R → ‖u p z‖ ≤ M)
    (hu0 : ∀ p, ‖u p 0‖ ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ ρ < R ∧
      ∀ p z, ‖z‖ < ρ → ‖u p z‖ ≤ 5 / 4 := by
  let B := |M| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hMb : M ≤ B := by dsimp [B]; linarith only [le_abs_self M]
  let ρ := min (r / 2) (min (R / 4) (R / (8 * B)))
  have hρ : 0 < ρ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hρr : ρ ≤ r / 2 := min_le_left _ _
  have hρR : ρ ≤ R / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hρB : ρ ≤ R / (8 * B) := (min_le_right _ _).trans (min_le_right _ _)
  have hL : 0 ≤ 2 * B / R := by positivity
  have hLρ : (2 * B / R) * ρ ≤ 1 / 4 := by
    have hh := (le_div_iff₀ (show 0 < 8 * B by positivity)).mp hρB
    rw [show (2 * B / R) * ρ = (2 * B * ρ) / R by ring, div_le_iff₀ hR]
    nlinarith only [hh]
  refine ⟨ρ, hρ, by linarith only [hρr, hr], by linarith only [hρR, hR], ?_⟩
  intro p z hz
  have hzhalf : z ∈ ball (0 : ℂ) (R / 2) := by
    rw [mem_ball, dist_zero_right]
    linarith only [hz, hρR, hR]
  have hh := Bottcher.norm_sub_le_of_bounded_on_ball hR (hu p)
    (fun w hw => (hb p w hw).trans hMb) hzhalf (mem_ball_self (by positivity))
  rw [sub_zero] at hh
  have hdiff : ‖u p z - u p 0‖ ≤ 1 / 4 :=
    hh.trans ((mul_le_mul_of_nonneg_left hz.le hL).trans hLρ)
  have ht := norm_add_le (u p z - u p 0) (u p 0)
  rw [sub_add_cancel] at ht
  linarith only [ht, hdiff, hu0 p]

private theorem primeDamping_le_three_quarters {σ : ℝ} (hσ : 1 / 2 < σ) (p : Nat.Primes) :
    primeDamping σ p ≤ 3 / 4 := by
  have h := norm_eulerVar_le (norm_twist_prime (0 : GaugeTorus)) p.2
    (s := (σ : ℂ)) hσ
  rw [norm_eulerVar (norm_twist_prime (0 : GaugeTorus)) p.2, ofReal_re] at h
  exact h

/-- Each Euler logarithm change is jointly analytic where both factors stay in the slit plane. -/
private theorem analyticAt_jointEulerChange {u : Nat.Primes → ℂ → ℂ} (p : Nat.Primes)
    {q : ℂ × ℂ} (hu : AnalyticAt ℂ (u p) q.1)
    (hd : ‖Complex.exp (-(q.2 * (primeFrequency p : ℂ)))‖ < 1)
    (hp : ‖u p q.1 * Complex.exp (-(q.2 * (primeFrequency p : ℂ)))‖ < 1) :
    AnalyticAt ℂ (jointEulerChange u p) q := by
  have hda : AnalyticAt ℂ (fun v : ℂ × ℂ =>
      Complex.exp (-(v.2 * (primeFrequency p : ℂ)))) q :=
    (((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt q).mul analyticAt_const).neg.cexp
  have hua : AnalyticAt ℂ (fun v : ℂ × ℂ => u p v.1) q :=
    hu.comp ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt q)
  exact ((analyticAt_const.sub hda).clog (one_sub_mem_slitPlane hd)).sub
    ((analyticAt_const.sub (hua.mul hda)).clog (one_sub_mem_slitPlane hp))

/-- One summable majorant controls the Euler change on the full product domain. -/
theorem jointEulerChange_normal_bound {u : Nat.Primes → ℂ → ℂ} {R r M σ : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hrR : r < R) (hσ : 1 / 2 < σ)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hb : ∀ p z, z ∈ ball (0 : ℂ) R → ‖u p z‖ ≤ M)
    (hu0 : ∀ p, ‖u p 0‖ ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ ∀ (p : Nat.Primes) (q : ℂ × ℂ), ‖q.1‖ < ρ → σ < q.2.re →
      AnalyticAt ℂ (jointEulerChange u p) q ∧
      ‖jointEulerChange u p q‖ ≤ 16 * (primeDiskDeviation u r p * (p : ℝ) ^ (-σ)) := by
  obtain ⟨ρ, hρ, hρr, hρR, hsmall⟩ := exists_prime_phase_small_disk hR hr hu hb hu0
  refine ⟨ρ, hρ, hρr, ?_⟩
  intro p q hq hqs
  have hbd := (primeDiskDeviation_bounds hr.le hrR hb p).2 q.1 (hq.le.trans hρr.le)
  have hbn := (primeDiskDeviation_bounds hr.le hrR hb p).1
  have hud := hsmall p q.1 hq
  have hdσ := norm_prime_decay_le hqs.le p
  have hdq : ‖Complex.exp (-(q.2 * (primeFrequency p : ℂ)))‖ ≤ 3 / 4 :=
    hdσ.trans (primeDamping_le_three_quarters hσ p)
  have hprod : ‖u p q.1 * Complex.exp (-(q.2 * (primeFrequency p : ℂ)))‖ ≤ 15 / 16 := by
    rw [norm_mul]
    exact (mul_le_mul hud hdq (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hua : AnalyticAt ℂ (u p) q.1 :=
    (hu p).analyticAt (isOpen_ball.mem_nhds (by
      simpa only [mem_ball, dist_zero_right] using hq.trans hρR))
  refine ⟨analyticAt_jointEulerChange p hua (hdq.trans_lt (by norm_num))
    (hprod.trans_lt (by norm_num)), ?_⟩
  have hh := norm_log_euler_change_le (by norm_num : (1 : ℝ) ≤ 5 / 4) hud hdq
    (by norm_num : (5 / 4 : ℝ) * (3 / 4) < 1)
  norm_num only at hh
  change ‖jointEulerChange u p q‖ ≤ 16 * ‖u p q.1 - 1‖ *
    ‖Complex.exp (-(q.2 * (primeFrequency p : ℂ)))‖ at hh
  exact hh.trans (by
    change 16 * ‖u p q.1 - 1‖ * ‖Complex.exp (-(q.2 * (primeFrequency p : ℂ)))‖ ≤
      16 * (primeDiskDeviation u r p * primeDamping σ p)
    rw [← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hbd (by norm_num)) hdσ (norm_nonneg _)
      (mul_nonneg (by norm_num) hbn))

/-- Product domain of the joint Euler logarithm. -/
def jointEulerDomain (ρ σ : ℝ) : Set (ℂ × ℂ) :=
  {q | ‖q.1‖ < ρ ∧ σ < q.2.re}

private theorem isOpen_jointEulerDomain (ρ σ : ℝ) : IsOpen (jointEulerDomain ρ σ) :=
  (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
    (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd))

/-- Normal prime summability constructs the jointly holomorphic Euler normal form. -/
theorem exists_jointEuler_normal_form {u : Nat.Primes → ℂ → ℂ} {R r M σ : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hrR : r < R) (hσ : 1 / 2 < σ)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hb : ∀ p z, z ∈ ball (0 : ℂ) R → ‖u p z‖ ≤ M)
    (hu0 : ∀ p, ‖u p 0‖ ≤ 1)
    (hs : Summable (fun p => primeDiskDeviation u r p * (p : ℝ) ^ (-σ))) :
    ∃ (ρ : ℝ) (b : Nat.Primes → ℝ), 0 < ρ ∧ ρ < r ∧ Summable b ∧
      (∀ p q, q ∈ jointEulerDomain ρ σ → ‖jointEulerChange u p q‖ ≤ b p) ∧
      AnalyticOnNhd ℂ (jointDeformationExponent u) (jointEulerDomain ρ σ) ∧
      AnalyticOnNhd ℂ (jointGaugeRegularization u) (jointEulerDomain ρ σ) := by
  obtain ⟨ρ, hρ, hρr, hterm⟩ := jointEulerChange_normal_bound hR hr hrR hσ hu hb hu0
  let b : Nat.Primes → ℝ := fun p => 16 * (primeDiskDeviation u r p * (p : ℝ) ^ (-σ))
  have hbs : Summable b := hs.mul_left 16
  -- One majorant works on the entire product, hence on every local product ball.
  have hH : AnalyticOnNhd ℂ (jointDeformationExponent u) (jointEulerDomain ρ σ) := by
    intro q hq
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_jointEulerDomain ρ σ) q hq
    exact analyticAt_tsum_prod_ball hε
      (fun p v hv => (hterm p v (hball hv).1 (hball hv).2).1) hbs
      (fun p v hv => (hterm p v (hball hv).1 (hball hv).2).2)
  refine ⟨ρ, b, hρ, hρr, hbs, fun p q hq => (hterm p q hq.1 hq.2).2, hH, ?_⟩
  intro q hq
  exact ((differentiable_zetaResidueFactor.analyticAt q.2).comp
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt q)).mul (hH q hq).cexp

/-- Normalization of every prime coordinate fixes the whole central spectral slice. -/
theorem jointDeformationExponent_zero {u : Nat.Primes → ℂ → ℂ}
    (hu0 : ∀ p, u p 0 = 1) (s : ℂ) : jointDeformationExponent u (0, s) = 0 := by
  simp only [jointDeformationExponent, jointEulerChange, hu0, one_mul, sub_self, tsum_zero]

theorem jointGaugeRegularization_zero {u : Nat.Primes → ℂ → ℂ}
    (hu0 : ∀ p, u p 0 = 1) (s : ℂ) : jointGaugeRegularization u (0, s) = zetaResidueFactor s := by
  rw [jointGaugeRegularization, jointDeformationExponent_zero hu0, Complex.exp_zero, mul_one]

private theorem summable_fibreEulerLog (x : GaugeTorus) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => -Complex.log (1 - eulerVar s (twist x) p)) := by
  have h := (summable_eulerVar (norm_twist_prime x) hs).add
    (summable_localRem (s := s) (norm_twist_prime x) (by linarith only [hs]))
  refine h.congr (fun p => ?_)
  dsimp only [localRem]
  ring

private theorem exp_tsum_fibreEulerLog (x : GaugeTorus) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - eulerVar s (twist x) p)) =
      gaugeFibre x s := by
  rw [← exp_tsum_eq_gaugeFibre x hs, hullRem,
    ← (summable_eulerVar (norm_twist_prime x) hs).tsum_add
      (summable_localRem (s := s) (norm_twist_prime x) (by linarith only [hs]))]
  congr 1
  apply tsum_congr
  intro p
  dsimp only [localRem]
  ring

/-- The joint Euler logarithm gives the actual fibre throughout the complex Euler half-plane. -/
theorem zeta_mul_exp_jointDeformationExponent {u : Nat.Primes → ℂ → ℂ}
    {t : ℂ} {x : GaugeTorus} (hphase : ∀ p, u p t = twist x p)
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * Complex.exp (jointDeformationExponent u (t, s)) = gaugeFibre x s := by
  let A : Nat.Primes → ℂ := fun p => -Complex.log (1 - eulerVar s (twist x) p)
  let B : Nat.Primes → ℂ := fun p => -Complex.log (1 - eulerVar s (twist 0) p)
  have hA : Summable A := summable_fibreEulerLog x hs
  have hB : Summable B := summable_fibreEulerLog 0 hs
  have he (p : Nat.Primes) : jointEulerChange u p (t, s) = A p - B p := by
    dsimp only [jointEulerChange, A, B, eulerVar, powCoeff]
    rw [prime_cexp_decay, hphase p, twist_trivial]
    simp only [mul_one, mul_comm]
    ring
  have hsum : jointDeformationExponent u (t, s) = (∑' p, A p) - ∑' p, B p := by
    rw [jointDeformationExponent, tsum_congr he, hA.tsum_sub hB]
  have hAe : Complex.exp (∑' p, A p) = gaugeFibre x s := exp_tsum_fibreEulerLog x hs
  have hBe : Complex.exp (∑' p, B p) = riemannZeta s := by
    rw [exp_tsum_fibreEulerLog 0 hs, gaugeFibre_trivial hs]
  rw [← hBe, hsum, ← Complex.exp_add]
  convert hAe using 1
  congr 1
  ring

/-- The canonical regularization agrees with the actual Euler fibre. -/
theorem jointGaugeRegularization_eq_gaugeFibre {u : Nat.Primes → ℂ → ℂ}
    {t : ℂ} {x : GaugeTorus} (hphase : ∀ p, u p t = twist x p)
    {s : ℂ} (hs : 1 < s.re) :
    jointGaugeRegularization u (t, s) = (s - 1) * gaugeFibre x s := by
  have hs1 : s ≠ 1 := by intro h; simp only [h, Complex.one_re, lt_self_iff_false] at hs
  rw [jointGaugeRegularization, zetaResidueFactor_of_ne hs1, mul_assoc,
    zeta_mul_exp_jointDeformationExponent hphase hs]

#print axioms exists_jointEuler_normal_form
#print axioms jointGaugeRegularization_eq_gaugeFibre

/-- A real diameter is an identity set for a holomorphic function on a disk. -/
private theorem eqOn_of_real_diameter {f g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball 0 r)) (hg : AnalyticOnNhd ℂ g (ball 0 r))
    (he : ∀ t : ℝ, |t| < r → f (t : ℂ) = g (t : ℂ)) :
    EqOn f g (ball 0 r) := by
  have htend : Tendsto (fun n : ℕ => (r / 2) / (n + 1 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, div_eq_mul_inv, one_mul] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (r / 2)
  have hbase : Tendsto (fun n : ℕ => (((r / 2) / (n + 1 : ℝ) : ℝ) : ℂ)) atTop
      (𝓝 (0 : ℂ)) := by
    simpa only [Complex.ofReal_zero, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp htend
  have hpunc : Tendsto (fun n : ℕ => (((r / 2) / (n + 1 : ℝ) : ℝ) : ℂ)) atTop
      (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hbase ?_
    filter_upwards with n
    simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_eq_zero]
    positivity
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, f z - g z = 0 := by
    apply hpunc.frequently
    apply Filter.Frequently.of_forall
    intro n
    apply sub_eq_zero.mpr (he _ ?_)
    have hp : 0 < (r / 2) / (n + 1 : ℝ) := by positivity
    rw [abs_of_pos hp]
    have hn : (0 : ℝ) ≤ n := by positivity
    have hh : (r / 2) / (n + 1 : ℝ) ≤ r / 2 :=
      div_le_self (by positivity) (by linarith only [hn])
    linarith only [hh, hr]
  have hz := (hf.sub hg).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball (0 : ℂ) r).isPreconnected (mem_ball_self hr) hfreq
  intro z hz'
  exact sub_eq_zero.mp (hz hz')

/-- Real-parameter Euler agreement determines a joint holomorphic germ. -/
theorem joint_germ_eq_of_real_euler_agreement {F G : ℂ × ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hF : AnalyticAt ℂ F (0, 1)) (hG : AnalyticAt ℂ G (0, 1))
    (he : ∀ t : ℝ, |t| < R → ∀ s ∈ ball (1 : ℂ) R, 1 < s.re →
      F ((t : ℂ), s) = G ((t : ℂ), s)) : F =ᶠ[𝓝 ((0 : ℂ), (1 : ℂ))] G := by
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp (hF.eventually_analyticAt.and hG.eventually_analyticAt)
  let r := min (ε / 2) (R / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith only [hε])
  have hrR : r < R := lt_of_le_of_lt (min_le_right _ _) (by linarith only [hR])
  have hpair (z : ℂ) (hz : z ∈ ball 0 r) (s : ℂ) (hs : s ∈ ball 1 r) :
      (z, s) ∈ ball ((0 : ℂ), (1 : ℂ)) ε := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_ball.mp hz).trans hrε, (mem_ball.mp hs).trans hrε⟩
  -- First continue each real-parameter slice through the spectral disk.
  have hreal (t : ℝ) (ht : |t| < r) :
      EqOn (fun s => F ((t : ℂ), s)) (fun s => G ((t : ℂ), s)) (ball 1 r) := by
    have htball : (t : ℂ) ∈ ball (0 : ℂ) r := by
      simpa only [mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs] using ht
    have hf : AnalyticOnNhd ℂ (fun s => F ((t : ℂ), s)) (ball 1 r) := fun s hs =>
      (hb (hpair (t : ℂ) htball s hs)).1.comp
        (f := fun z : ℂ => ((t : ℂ), z)) (analyticAt_const.prod analyticAt_id)
    have hg : AnalyticOnNhd ℂ (fun s => G ((t : ℂ), s)) (ball 1 r) := fun s hs =>
      (hb (hpair (t : ℂ) htball s hs)).2.comp
        (f := fun z : ℂ => ((t : ℂ), z)) (analyticAt_const.prod analyticAt_id)
    let a : ℂ := 1 + ((r / 2 : ℝ) : ℂ)
    have ha : a ∈ ball (1 : ℂ) r := by
      dsimp only [a]
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r / 2)]
      linarith only [hr]
    have hare : 1 < a.re := by
      dsimp only [a]
      simp only [add_re, one_re, ofReal_re]
      linarith only [hr]
    apply hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_ball (1 : ℂ) r).isPreconnected ha
    filter_upwards [isOpen_ball.mem_nhds ha,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hare] with s hs hse
    exact he t (ht.trans hrR) s (ball_subset_ball hrR.le hs) hse
  -- The real parameter interval then determines every complex parameter slice.
  have hfull (s : ℂ) (hs : s ∈ ball (1 : ℂ) r) :
      EqOn (fun z => F (z, s)) (fun z => G (z, s)) (ball 0 r) := by
    apply eqOn_of_real_diameter hr
      (fun z hz => (hb (hpair z hz s hs)).1.comp
        (f := fun w : ℂ => (w, s)) (analyticAt_id.prod analyticAt_const))
      (fun z hz => (hb (hpair z hz s hs)).2.comp
        (f := fun w : ℂ => (w, s)) (analyticAt_id.prod analyticAt_const))
    exact fun t ht => hreal t ht hs
  filter_upwards [ball_mem_nhds ((0 : ℂ), (1 : ℂ)) hr] with q hq
  have hp : q.1 ∈ ball (0 : ℂ) r ∧ q.2 ∈ ball (1 : ℂ) r := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using hq
  exact hfull q.2 hp.2 hp.1


/-- A joint pole germ exists exactly for normally summable prime-coordinate perturbations. -/
theorem joint_pole_regularization_iff_normal_summability {x : ℝ → GaugeTorus}
    {u : Nat.Primes → ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hu0 : ∀ p, u p 0 = 1)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hb : ∀ p z, z ∈ ball (0 : ℂ) R → ‖u p z‖ ≤ M)
    (hphase : ∀ t : ℝ, |t| < R → ∀ p, u p (t : ℂ) = twist (x t) p) :
    (∃ (ε : ℝ) (U : ℂ × ℂ → ℂ), 0 < ε ∧ ε < R ∧ AnalyticAt ℂ U (0, 1) ∧
      ∀ t : ℝ, |t| < ε → ∀ s ∈ ball (1 : ℂ) ε, 1 < s.re →
        U ((t : ℂ), s) = (s - 1) * gaugeFibre (x t) s) ↔
    ∃ r σ : ℝ, 0 < r ∧ r < R ∧ 1 / 2 < σ ∧ σ < 1 ∧
      Summable (fun p => primeDiskDeviation u r p * (p : ℝ) ^ (-σ)) := by
  constructor
  · rintro ⟨ε, U, hε, hεR, hU, he⟩
    obtain ⟨r, σ, hr, hrε, hσ, hσ1, hs⟩ := joint_gauge_complex_normal_summability hε hu0
      (fun p => (hu p).mono (ball_subset_ball hεR.le))
      (fun p z hz => hb p z (ball_subset_ball hεR.le hz))
      (fun t ht => hphase t (ht.trans hεR)) hU he
    exact ⟨r, σ, hr, hrε.trans hεR, hσ, hσ1, hs⟩
  · rintro ⟨r, σ, hr, hrR, hσ, hσ1, hs⟩
    obtain ⟨ρ, b, hρ, hρr, _, _, _, hW⟩ :=
      exists_jointEuler_normal_form hR hr hrR hσ hu hb (fun p => by rw [hu0 p, norm_one]) hs
    have hW0 : AnalyticAt ℂ (jointGaugeRegularization u) (0, 1) :=
      hW (0, 1) ⟨by simpa only [norm_zero] using hρ, hσ1⟩
    refine ⟨ρ / 2, jointGaugeRegularization u, by positivity,
      by linarith only [hρr, hrR, hρ], hW0, ?_⟩
    intro t ht s _ hse
    exact jointGaugeRegularization_eq_gaugeFibre
      (hphase t (by linarith only [ht, hρr, hrR, hρ])) hse

/-- Every actual joint pole germ extends by the same normally convergent Euler normal form. -/
theorem joint_pole_germ_normal_form {x : ℝ → GaugeTorus}
    {u : Nat.Primes → ℂ → ℂ} {U : ℂ × ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hu0 : ∀ p, u p 0 = 1)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hb : ∀ p z, z ∈ ball (0 : ℂ) R → ‖u p z‖ ≤ M)
    (hphase : ∀ t : ℝ, |t| < R → ∀ p, u p (t : ℂ) = twist (x t) p)
    (hU : AnalyticAt ℂ U (0, 1))
    (he : ∀ t : ℝ, |t| < R → ∀ s ∈ ball (1 : ℂ) R, 1 < s.re →
      U ((t : ℂ), s) = (s - 1) * gaugeFibre (x t) s) :
    ∃ (ρ σ : ℝ) (b : Nat.Primes → ℝ),
      0 < ρ ∧ ρ < R ∧ 1 / 2 < σ ∧ σ < 1 ∧ Summable b ∧
      (∀ p q, q ∈ jointEulerDomain ρ σ → ‖jointEulerChange u p q‖ ≤ b p) ∧
      AnalyticOnNhd ℂ (jointDeformationExponent u) (jointEulerDomain ρ σ) ∧
      AnalyticOnNhd ℂ (jointGaugeRegularization u) (jointEulerDomain ρ σ) ∧
      U =ᶠ[𝓝 ((0 : ℂ), (1 : ℂ))] jointGaugeRegularization u := by
  obtain ⟨r, σ, hr, hrR, hσ, hσ1, hs⟩ :=
    joint_gauge_complex_normal_summability hR hu0 hu hb hphase hU he
  obtain ⟨ρ, b, hρ, hρr, hbs, hterm, hH, hW⟩ :=
    exists_jointEuler_normal_form hR hr hrR hσ hu hb (fun p => by rw [hu0 p, norm_one]) hs
  have hW0 : AnalyticAt ℂ (jointGaugeRegularization u) (0, 1) :=
    hW (0, 1) ⟨by simpa only [norm_zero] using hρ, hσ1⟩
  refine ⟨ρ, σ, b, hρ, hρr.trans hrR, hσ, hσ1, hbs, hterm, hH, hW, ?_⟩
  apply joint_germ_eq_of_real_euler_agreement hR hU hW0
  intro t ht s hs hse
  exact (he t ht s hs hse).trans (jointGaugeRegularization_eq_gaugeFibre (hphase t ht) hse).symm

#print axioms joint_germ_eq_of_real_euler_agreement
#print axioms joint_pole_regularization_iff_normal_summability
#print axioms joint_pole_germ_normal_form
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
