import GaloisForLFunctions.ArithmeticCompensationTheory.ThePrimeCombIsATranslation

/-!
# At the horizon the prime comb is an exponential resolvent

`ThePrimeCombIsATranslation` shows that on slowly varying tests the normalized prime comb is a
translation by the horizon. This file identifies the comb on *every* test. Measured from the
horizon, the comb primes sit at the depths `u_p = 2r − log p ≥ 0`, and their normalized weights
converge to the exponential **horizon law** of density `½ e^{−u/2}` on `(0, ∞)`:

* `eventually_abs_combTail_sub_le`: the comb tail `D_r(u) = S_{r−u/2}/S_r`, the fraction of the
  comb mass at depth at least `u`, tends to `e^{−u/2}` uniformly in `u ≥ 0`;
* `eventually_abs_combAverage_sub_horizonIntegral_le`: hence every bounded uniformly continuous
  statistic of the depths converges to its horizon-law integral, uniformly over its translates
  (a Riemann–Stieltjes comparison on shells of depth `h`, with the tails cut at depth `Kh`);
* `tendsto_combEnergy_div_combMass_sq_horizonEnergy` — **the comb resolvent law**: for every
  continuous compactly supported test `F`,

  `E_r(F)/S_r² → J(F) = ∫_{v>0} ∫_{u>0} A_F(u − v) ½e^{−u/2} ½e^{−v/2} du dv`,

  so `E_r(F) ∼ 4 J(F) e^{2r}` (`tendsto_combEnergy_div_exp_horizonEnergy`), with
  `0 ≤ J(F) ≤ A_F(0)`.

Since `log q − log p = u_p − u_q`, the comb energy reads only depth differences, and in the limit
the comb acts as `S_r` times the translation to the horizon composed with the one-sided exponential
smoothing `F ↦ ∫_{u>0} ½e^{−u/2} F(· − u) du`, the resolvent of `1 + 2∂`. On the slowly varying
family the smoothing is the identity to leading order (`J → A_f(0)`), which is the translation
theorem; on a fixed test it is a genuine resolvent, and the raw comb energy grows like `e^{2r}` on
every test with `J(F) > 0`.
-/

open Filter Topology Finset MeasureTheory Set
open GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticIncidencePositivity

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## The depth law below the horizon -/

/-- The depth of a comb prime below the horizon, `u_p = 2r − log p`. -/
def combDepth (r : ℝ) (p : ℕ) : ℝ := 2 * r - Real.log p

/-- The comb tail `D_r(u) = S_{r−u/2}/S_r`: the fraction of comb mass at depth at least `u`. -/
def combTail (r u : ℝ) : ℝ := combMass (r - u / 2) / combMass r

theorem combMass_mono : Monotone combMass := fun _ _ h =>
  sum_le_sum_of_subset_of_nonneg (combPrimes_mono h) fun p _ _ => combWeight_nonneg p

/-- A comb prime lies in the sub-comb at depth `u` exactly when its depth is at least `u`. -/
theorem mem_combPrimes_sub_iff {r u : ℝ} {p : ℕ} (hp : p ∈ combPrimes r) :
    p ∈ combPrimes (r - u / 2) ↔ u ≤ combDepth r p := by
  obtain ⟨hpr, _⟩ := mem_combPrimes.mp hp
  have h0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
  rw [mem_combPrimes, combDepth]
  constructor
  · rintro ⟨_, hle⟩
    have := Real.log_le_log h0 hle
    rw [Real.log_exp] at this
    linarith
  · intro hu
    refine ⟨hpr, ?_⟩
    calc (p : ℝ) = Real.exp (Real.log p) := (Real.exp_log h0).symm
      _ ≤ Real.exp (2 * (r - u / 2)) := Real.exp_le_exp.mpr (by linarith)

theorem combDepth_sub_combDepth (r : ℝ) (p q : ℕ) :
    combDepth r p - combDepth r q = Real.log q - Real.log p := by
  simp only [combDepth]; ring

theorem combTail_nonneg (r u : ℝ) : 0 ≤ combTail r u :=
  div_nonneg (combMass_nonneg _) (combMass_nonneg _)

theorem combTail_anti {r : ℝ} (hr : 0 < combMass r) {u v : ℝ} (huv : u ≤ v) :
    combTail r v ≤ combTail r u :=
  div_le_div_of_nonneg_right (combMass_mono (by linarith)) hr.le

/-- **The depth law, uniformly.** `sup_{u ≥ 0} |D_r(u) − e^{−u/2}| → 0`. -/
theorem eventually_abs_combTail_sub_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in atTop, ∀ u : ℝ, 0 ≤ u → |combTail r u - Real.exp (-u / 2)| ≤ ε := by
  set δ := min (ε / 4) 1 with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) one_pos
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (tendsto_combMass_div_exp.eventually
    (Metric.closedBall_mem_nhds (2 : ℝ) hδ0))
  have ha : ∀ y, Y ≤ y → |combMass y / Real.exp y - 2| ≤ δ := fun y hy => by
    simpa only [Metric.mem_closedBall, Real.dist_eq] using hY y hy
  set U := max 0 (2 * Real.log (4 / ε)) with hUdef
  have hU0 : 0 ≤ U := le_max_left _ _
  have hUexp : Real.exp (-U / 2) ≤ ε / 4 := by
    have hlog : Real.log (4 / ε) ≤ U / 2 := by
      have := le_max_right 0 (2 * Real.log (4 / ε)); linarith
    calc Real.exp (-U / 2) ≤ Real.exp (-Real.log (4 / ε)) := Real.exp_le_exp.mpr (by linarith)
      _ = ε / 4 := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  filter_upwards [eventually_ge_atTop (Y + U / 2)] with r hr
  have har := ha r (by linarith)
  have har1 : 1 ≤ combMass r / Real.exp r := by linarith [(abs_le.mp har).1]
  have hSr : 0 < combMass r := by
    have h2 : 0 < combMass r / Real.exp r := by linarith
    exact (div_pos_iff_of_pos_right (Real.exp_pos r)).mp h2
  -- the near range `u ≤ U`
  have hnear : ∀ u, 0 ≤ u → u ≤ U → |combTail r u - Real.exp (-u / 2)| ≤ ε / 2 := by
    intro u hu0 huU
    have hay := ha (r - u / 2) (by linarith)
    set ay := combMass (r - u / 2) / Real.exp (r - u / 2)
    set ar := combMass r / Real.exp r
    have hsplit : combTail r u = ay / ar * Real.exp (-u / 2) := by
      simp only [combTail, ay, ar]
      have he : Real.exp (r - u / 2) = Real.exp r * Real.exp (-u / 2) := by
        rw [← Real.exp_add]; ring_nf
      rw [he]
      field_simp
    rw [hsplit]
    have hexp1 : Real.exp (-u / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hexp0 := Real.exp_pos (-u / 2)
    have hdiff : |ay / ar - 1| ≤ 2 * δ := by
      have har0 : (0 : ℝ) < ar := by linarith
      rw [div_sub_one har0.ne', abs_div, abs_of_pos har0, div_le_iff₀ har0]
      have h1 : |ay - ar| ≤ 2 * δ := by
        calc |ay - ar| = |(ay - 2) - (ar - 2)| := by ring_nf
          _ ≤ |ay - 2| + |ar - 2| := abs_sub _ _
          _ ≤ 2 * δ := by linarith
      nlinarith
    calc |ay / ar * Real.exp (-u / 2) - Real.exp (-u / 2)|
        = |ay / ar - 1| * Real.exp (-u / 2) := by
          rw [← sub_one_mul, abs_mul, abs_of_pos hexp0]
      _ ≤ 2 * δ * 1 := mul_le_mul hdiff hexp1 hexp0.le (by positivity)
      _ ≤ ε / 2 := by linarith
  intro u hu
  rcases le_or_gt u U with huU | huU
  · linarith [hnear u hu huU]
  · have hU' := (abs_le.mp (hnear U hU0 le_rfl)).2
    have hmono := combTail_anti hSr huU.le
    have hT0 := combTail_nonneg r u
    have he0 := Real.exp_pos (-u / 2)
    have heU : Real.exp (-u / 2) ≤ Real.exp (-U / 2) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_le]
    constructor <;> linarith

/-! ## Shells of depth: the discrete side -/

/-- The comb mass at depths in `[kh, (k+1)h)`. -/
def combShellMass (r h : ℝ) (k : ℕ) : ℝ :=
  combMass (r - k * h / 2) - combMass (r - (k + 1) * h / 2)

/-- The weighted depth statistic of the sub-comb at depth at least `t`. -/
def combDepthSum (g : ℝ → ℝ) (r t : ℝ) : ℝ :=
  ∑ p ∈ combPrimes (r - t / 2), combWeight p * g (combDepth r p)

/-- **Shell comparison, discrete side.** If `g` is bounded by `M` and varies by at most `ω` over
distances `h`, the depth statistic of the comb differs from its shell sum by at most
`ω S_r + M S_{r − Kh/2}`. -/
theorem abs_combDepthSum_sub_shells_le {g : ℝ → ℝ} {M h ω : ℝ} (hg : ∀ t, |g t| ≤ M)
    (hω : ∀ x y, |x - y| ≤ h → |g x - g y| ≤ ω) (hh : 0 ≤ h) (r : ℝ) (K : ℕ) :
    |combDepthSum g r 0 - ∑ k ∈ range K, g (k * h) * combShellMass r h k| ≤
      ω * combMass r + M * combMass (r - K * h / 2) := by
  have hω0 : 0 ≤ ω := (abs_nonneg _).trans (hω 0 0 (by simpa using hh))
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hg 0)
  have hclaim : ∀ K : ℕ, |combDepthSum g r 0 - ∑ k ∈ range K, g (k * h) * combShellMass r h k -
      combDepthSum g r (K * h)| ≤ ω * (combMass r - combMass (r - K * h / 2)) := by
    intro K
    induction K with
    | zero => simp [combDepthSum]
    | succ K ih =>
        have hsub : combPrimes (r - (K + 1) * h / 2) ⊆ combPrimes (r - K * h / 2) :=
          combPrimes_mono (by nlinarith)
        have hsplit : combDepthSum g r (K * h) =
            (∑ p ∈ combPrimes (r - K * h / 2) \ combPrimes (r - (K + 1) * h / 2),
              combWeight p * g (combDepth r p)) + combDepthSum g r ((K + 1) * h) := by
          simp only [combDepthSum]
          rw [sum_sdiff hsub]
        have hmass : combShellMass r h K =
            ∑ p ∈ combPrimes (r - K * h / 2) \ combPrimes (r - (K + 1) * h / 2), combWeight p := by
          simp only [combShellMass, combMass]
          rw [← sum_sdiff hsub]
          ring
        have hshell : |(∑ p ∈ combPrimes (r - K * h / 2) \ combPrimes (r - (K + 1) * h / 2),
            combWeight p * g (combDepth r p)) - g (K * h) * combShellMass r h K| ≤
            ω * combShellMass r h K := by
          rw [hmass, mul_sum, mul_sum, ← sum_sub_distrib]
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp => ?_)
          obtain ⟨hp1, hp2⟩ := mem_sdiff.mp hp
          have hKh0 : (0 : ℝ) ≤ K * h := by positivity
          have hpr : p ∈ combPrimes r := combPrimes_mono (by linarith) hp1
          have hlo := (mem_combPrimes_sub_iff hpr).mp hp1
          have hhi : ¬ ((K + 1) * h ≤ combDepth r p) := fun h' =>
            hp2 ((mem_combPrimes_sub_iff hpr).mpr h')
          push Not at hhi
          have hclose : |combDepth r p - K * h| ≤ h := by
            rw [abs_le]; constructor <;> nlinarith
          rw [show combWeight p * g (combDepth r p) - g (K * h) * combWeight p =
              combWeight p * (g (combDepth r p) - g (K * h)) by ring, abs_mul,
            abs_of_nonneg (combWeight_nonneg p), mul_comm ω]
          exact mul_le_mul_of_nonneg_left (hω _ _ hclose) (combWeight_nonneg p)
        rw [Finset.sum_range_succ]
        push_cast
        calc |combDepthSum g r 0 - (∑ k ∈ range K, g (k * h) * combShellMass r h k +
              g (K * h) * combShellMass r h K) - combDepthSum g r ((K + 1) * h)|
            = |(combDepthSum g r 0 - ∑ k ∈ range K, g (k * h) * combShellMass r h k -
                combDepthSum g r (K * h)) +
              ((∑ p ∈ combPrimes (r - K * h / 2) \ combPrimes (r - (K + 1) * h / 2),
                combWeight p * g (combDepth r p)) - g (K * h) * combShellMass r h K)| := by
              congr 1; rw [hsplit]; ring
          _ ≤ ω * (combMass r - combMass (r - K * h / 2)) + ω * combShellMass r h K :=
              (abs_add_le _ _).trans (add_le_add ih hshell)
          _ = ω * (combMass r - combMass (r - (K + 1) * h / 2)) := by
              simp only [combShellMass]; ring
  have hK := hclaim K
  have htail : |combDepthSum g r (K * h)| ≤ M * combMass (r - K * h / 2) := by
    simp only [combDepthSum, combMass]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun p _ => ?_
    rw [abs_mul, abs_of_nonneg (combWeight_nonneg p), mul_comm M]
    exact mul_le_mul_of_nonneg_left (hg _) (combWeight_nonneg p)
  have hS0 := combMass_nonneg (r - K * h / 2)
  calc |combDepthSum g r 0 - ∑ k ∈ range K, g (k * h) * combShellMass r h k|
      = |(combDepthSum g r 0 - ∑ k ∈ range K, g (k * h) * combShellMass r h k -
          combDepthSum g r (K * h)) + combDepthSum g r (K * h)| := by congr 1; ring
    _ ≤ ω * (combMass r - combMass (r - K * h / 2)) + M * combMass (r - K * h / 2) :=
        (abs_add_le _ _).trans (add_le_add hK htail)
    _ ≤ ω * combMass r + M * combMass (r - K * h / 2) := by nlinarith

/-! ## The horizon law: the continuous side -/

/-- The density `½ e^{−u/2}` of the horizon law. -/
def horizonDensity (u : ℝ) : ℝ := Real.exp (-u / 2) / 2

/-- The horizon-law integral `∫_{u>0} g(u) ½e^{−u/2} du`. -/
def horizonIntegral (g : ℝ → ℝ) : ℝ := ∫ u in Ioi 0, g u * horizonDensity u

/-- The horizon-law mass of the shell `[kh, (k+1)h)`. -/
def expShellMass (h : ℝ) (k : ℕ) : ℝ := Real.exp (-(k * h) / 2) - Real.exp (-((k + 1) * h) / 2)

theorem horizonDensity_nonneg (u : ℝ) : 0 ≤ horizonDensity u := by
  unfold horizonDensity; positivity

theorem continuous_horizonDensity : Continuous horizonDensity := by
  unfold horizonDensity; fun_prop

theorem hasDerivAt_neg_exp_half (u : ℝ) :
    HasDerivAt (fun x => -Real.exp (-x / 2)) (horizonDensity u) u := by
  refine ((((hasDerivAt_neg u).div_const 2).exp).neg).congr_deriv ?_
  simp only [horizonDensity]
  ring

theorem integral_horizonDensity (a b : ℝ) :
    ∫ u in a..b, horizonDensity u = Real.exp (-a / 2) - Real.exp (-b / 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_neg_exp_half x)
    (continuous_horizonDensity.intervalIntegrable _ _)]
  ring

theorem integrableOn_horizonDensity (c : ℝ) : IntegrableOn horizonDensity (Ioi c) := by
  have h := (exp_neg_integrableOn_Ioi c (by norm_num : (0 : ℝ) < 1 / 2)).div_const 2
  refine IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
  simp only [horizonDensity]
  ring_nf

theorem integral_Ioi_horizonDensity (c : ℝ) : ∫ u in Ioi c, horizonDensity u = Real.exp (-c / 2) := by
  have h := integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) c
  have heq : (fun u => horizonDensity u) = fun u => Real.exp (-1 / 2 * u) / 2 := by
    funext u; simp only [horizonDensity]; ring_nf
  rw [heq, integral_div, h]
  ring_nf

theorem integrableOn_mul_horizonDensity {g : ℝ → ℝ} {M : ℝ} (hgc : Continuous g)
    (hg : ∀ t, |g t| ≤ M) (c : ℝ) : IntegrableOn (fun u => g u * horizonDensity u) (Ioi c) :=
  (integrableOn_horizonDensity c).bdd_mul hgc.aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hg u)

/-- `|∫_{Ioi c} g ½e^{−u/2}| ≤ M e^{−c/2}` when `|g| ≤ M`. -/
theorem abs_integral_Ioi_mul_horizonDensity_le {g : ℝ → ℝ} {M : ℝ}
    (hg : ∀ t, |g t| ≤ M) (c : ℝ) :
    |∫ u in Ioi c, g u * horizonDensity u| ≤ M * Real.exp (-c / 2) := by
  have hint : IntegrableOn (fun u => M * horizonDensity u) (Ioi c) :=
    (integrableOn_horizonDensity c).const_mul M
  have h := norm_integral_le_of_norm_le (f := fun u => g u * horizonDensity u) hint
    (Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (horizonDensity_nonneg u)]
    exact mul_le_mul_of_nonneg_right (hg u) (horizonDensity_nonneg u))
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_horizonDensity] at h
  exact h

/-- The horizon law has total mass one, so `|I(g)| ≤ M`. -/
theorem abs_horizonIntegral_le {g : ℝ → ℝ} {M : ℝ} (hg : ∀ t, |g t| ≤ M) :
    |horizonIntegral g| ≤ M := by
  have h := abs_integral_Ioi_mul_horizonDensity_le hg 0
  simpa [horizonIntegral] using h

theorem horizonIntegral_sub {g₁ g₂ : ℝ → ℝ} {M₁ M₂ : ℝ} (hc₁ : Continuous g₁) (hc₂ : Continuous g₂)
    (h₁ : ∀ t, |g₁ t| ≤ M₁) (h₂ : ∀ t, |g₂ t| ≤ M₂) :
    horizonIntegral g₁ - horizonIntegral g₂ = horizonIntegral (fun u => g₁ u - g₂ u) := by
  simp only [horizonIntegral, sub_mul]
  rw [integral_sub (integrableOn_mul_horizonDensity hc₁ h₁ 0)
    (integrableOn_mul_horizonDensity hc₂ h₂ 0)]

/-- The horizon-law shell masses telescope: `Σ_{k<K} = 1 − e^{−Kh/2}`. -/
theorem sum_expShellMass (h : ℝ) (K : ℕ) :
    ∑ k ∈ range K, expShellMass h k = 1 - Real.exp (-(K * h) / 2) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, expShellMass]
      push_cast
      ring

/-- **Shell comparison, continuous side.** `|I(g) − Σ_{k<K} g(kh)(e^{−kh/2} − e^{−(k+1)h/2})| ≤
ω + M e^{−Kh/2}`. -/
theorem abs_horizonIntegral_sub_shells_le {g : ℝ → ℝ} {M h ω : ℝ} (hgc : Continuous g)
    (hg : ∀ t, |g t| ≤ M) (hω : ∀ x y, |x - y| ≤ h → |g x - g y| ≤ ω) (hh : 0 ≤ h) (K : ℕ) :
    |horizonIntegral g - ∑ k ∈ range K, g (k * h) * expShellMass h k| ≤
      ω + M * Real.exp (-(K * h) / 2) := by
  have hω0 : 0 ≤ ω := (abs_nonneg _).trans (hω 0 0 (by simpa using hh))
  have hKh : (0 : ℝ) ≤ K * h := by positivity
  set f : ℝ → ℝ := fun u => g u * horizonDensity u
  have hfc : Continuous f := hgc.mul continuous_horizonDensity
  -- split `(0, ∞) = (0, Kh] ∪ (Kh, ∞)`
  have hsplit : horizonIntegral g = (∫ u in (0 : ℝ)..K * h, f u) + ∫ u in Ioi (K * h), f u := by
    rw [horizonIntegral, ← Ioc_union_Ioi_eq_Ioi hKh,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hfc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        (integrableOn_mul_horizonDensity hgc hg _),
      intervalIntegral.integral_of_le hKh]
  have hshells : (∫ u in (0 : ℝ)..K * h, f u) =
      ∑ k ∈ range K, ∫ u in (k * h : ℝ)..((k + 1 : ℕ) : ℝ) * h, f u := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
      (a := fun k : ℕ => (k : ℝ) * h) (n := K) (fun k _ => hfc.intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_mul] at h
    rw [← h]
  have hone : ∀ k : ℕ, |(∫ u in (k * h : ℝ)..((k + 1 : ℕ) : ℝ) * h, f u) -
      g (k * h) * expShellMass h k| ≤ ω * expShellMass h k := by
    intro k
    have hle : (k : ℝ) * h ≤ ((k + 1 : ℕ) : ℝ) * h := by push_cast; nlinarith
    have hmass : (∫ u in (k * h : ℝ)..((k + 1 : ℕ) : ℝ) * h, horizonDensity u) =
        expShellMass h k := by
      rw [integral_horizonDensity, expShellMass]; push_cast; ring_nf
    have hdiff : (∫ u in (k * h : ℝ)..((k + 1 : ℕ) : ℝ) * h, f u) - g (k * h) * expShellMass h k =
        ∫ u in (k * h : ℝ)..((k + 1 : ℕ) : ℝ) * h, (g u - g (k * h)) * horizonDensity u := by
      rw [← hmass, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
        (hfc.intervalIntegrable _ _)
        ((continuous_horizonDensity.const_mul _).intervalIntegrable _ _)]
      congr 1; ext u; simp only [f]; ring
    rw [hdiff, ← hmass, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.abs_integral_le_integral_abs hle |>.trans ?_
    have hc1 : Continuous fun u => |(g u - g (k * h)) * horizonDensity u| :=
      ((hgc.sub continuous_const).mul continuous_horizonDensity).abs
    refine intervalIntegral.integral_mono_on hle (hc1.intervalIntegrable _ _)
      ((continuous_horizonDensity.const_mul ω).intervalIntegrable _ _) fun u hu => ?_
    rw [abs_mul, abs_of_nonneg (horizonDensity_nonneg u)]
    refine mul_le_mul_of_nonneg_right (hω _ _ ?_) (horizonDensity_nonneg u)
    obtain ⟨hu1, hu2⟩ := hu
    push_cast at hu2
    rw [abs_le]; constructor <;> nlinarith
  have hsum_exp := sum_expShellMass h K
  have htail := abs_integral_Ioi_mul_horizonDensity_le hg (K * h)
  have hexp0 := Real.exp_pos (-(K * h) / 2)
  rw [hsplit, hshells]
  calc |(∑ k ∈ range K, ∫ u in (k * h : ℝ)..((k + 1 : ℕ) : ℝ) * h, f u) +
        (∫ u in Ioi (K * h), f u) - ∑ k ∈ range K, g (k * h) * expShellMass h k|
      = |(∑ k ∈ range K, ((∫ u in (k * h : ℝ)..((k + 1 : ℕ) : ℝ) * h, f u) -
          g (k * h) * expShellMass h k)) + ∫ u in Ioi (K * h), f u| := by
        congr 1; rw [sum_sub_distrib]; ring
    _ ≤ (∑ k ∈ range K, ω * expShellMass h k) + M * Real.exp (-(K * h) / 2) :=
        (abs_add_le _ _).trans (add_le_add ((abs_sum_le_sum_abs _ _).trans
          (sum_le_sum fun k _ => hone k)) htail)
    _ = ω * (1 - Real.exp (-(K * h) / 2)) + M * Real.exp (-(K * h) / 2) := by
        rw [← mul_sum, hsum_exp]
    _ ≤ ω + M * Real.exp (-(K * h) / 2) := by nlinarith

/-! ## Convergence of depth statistics, uniformly over translates -/

/-- The normalized shell masses are differences of the comb tail. -/
theorem combShellMass_div (r h : ℝ) (k : ℕ) :
    combShellMass r h k / combMass r = combTail r (k * h) - combTail r ((k + 1) * h) := by
  simp only [combShellMass, combTail, sub_div]

/-- **Depth statistics converge to the horizon law.** For `φ` bounded and uniformly continuous,
`S_r^{−1} Σ_p w_p φ(u_p − v) → ∫_{u>0} φ(u − v) ½e^{−u/2} du`, uniformly in the translate `v`. -/
theorem eventually_abs_combAverage_sub_horizonIntegral_le {φ : ℝ → ℝ} {M : ℝ}
    (hφ : Continuous φ) (hφM : ∀ t, |φ t| ≤ M) (hφu : UniformContinuous φ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in atTop, ∀ v : ℝ,
      |combDepthSum (fun u => φ (u - v)) r 0 / combMass r -
        horizonIntegral (fun u => φ (u - v))| ≤ ε := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hφM 0)
  -- the mesh from uniform continuity
  obtain ⟨δ, hδ, hδφ⟩ := Metric.uniformContinuous_iff.mp hφu (ε / 8) (by positivity)
  set h := δ / 2 with hhdef
  have hh : 0 < h := by positivity
  have hω : ∀ v x y : ℝ, |x - y| ≤ h → |φ (x - v) - φ (y - v)| ≤ ε / 8 := by
    intro v x y hxy
    have : dist (x - v) (y - v) < δ := by
      rw [Real.dist_eq, show x - v - (y - v) = x - y by ring]; linarith
    exact (hδφ this).le
  -- the cutoff depth `Kh`
  have hcut : Tendsto (fun K : ℕ => (M + 1) * Real.exp (-(K * h) / 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun K : ℕ => (K : ℝ) * h / 2) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_mul_const hh).atTop_div_const (by norm_num)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (M + 1)
    rw [mul_zero] at h2
    refine h2.congr fun K => ?_
    simp only [Function.comp_apply]; ring_nf
  obtain ⟨K, hK⟩ := (hcut.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 16 by positivity))).exists
  have hKexp : M * Real.exp (-(K * h) / 2) ≤ ε / 16 := by
    have := Real.exp_pos (-(K * h) / 2); nlinarith
  set η := ε / (16 * ((K : ℝ) + 1) * (M + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hηK : 2 * K * M * η ≤ ε / 8 := by
    rw [hηdef]
    have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have hM1 : (0 : ℝ) < M + 1 := by positivity
    rw [show 2 * (K : ℝ) * M * (ε / (16 * ((K : ℝ) + 1) * (M + 1))) =
      ε / 8 * ((K / ((K : ℝ) + 1)) * (M / (M + 1))) by field_simp; ring]
    have h1 : (K : ℝ) / ((K : ℝ) + 1) ≤ 1 := by rw [div_le_one hK1]; linarith
    have h2 : M / (M + 1) ≤ 1 := by rw [div_le_one hM1]; linarith
    have h4 : 0 ≤ M / (M + 1) := by positivity
    calc ε / 8 * ((K / ((K : ℝ) + 1)) * (M / (M + 1))) ≤ ε / 8 * 1 :=
          mul_le_mul_of_nonneg_left (mul_le_one₀ h1 h4 h2) (by positivity)
      _ = ε / 8 := mul_one _
  have hMη : M * η ≤ ε / 16 := by
    rw [hηdef]
    have hK1 : (1 : ℝ) ≤ 16 * ((K : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) K; linarith
    rw [show M * (ε / (16 * ((K : ℝ) + 1) * (M + 1))) =
      ε / (16 * ((K : ℝ) + 1)) * (M / (M + 1)) by field_simp]
    have h2 : M / (M + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have h3 : ε / (16 * ((K : ℝ) + 1)) ≤ ε / 16 := by
      apply div_le_div_of_nonneg_left hε.le (by norm_num); linarith
    have h4 : 0 ≤ M / (M + 1) := by positivity
    nlinarith
  filter_upwards [eventually_abs_combTail_sub_le hη, eventually_combMass_pos] with r hT hS
  intro v
  set g : ℝ → ℝ := fun u => φ (u - v)
  have hgc : Continuous g := hφ.comp' (continuous_sub_right _)
  have hgM : ∀ t, |g t| ≤ M := fun t => hφM _
  have hgω : ∀ x y, |x - y| ≤ h → |g x - g y| ≤ ε / 8 := hω v
  -- the two shell comparisons
  have hdisc := abs_combDepthSum_sub_shells_le hgM hgω hh.le r K
  have hcont := abs_horizonIntegral_sub_shells_le hgc hgM hgω hh.le K
  -- the shell masses agree up to `2η` each
  have hmid : |∑ k ∈ range K, g (k * h) * (combShellMass r h k / combMass r) -
      ∑ k ∈ range K, g (k * h) * expShellMass h k| ≤ 2 * K * M * η := by
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ range K, |g (k * h) * (combShellMass r h k / combMass r) -
        g (k * h) * expShellMass h k| ≤ M * (2 * η) := by
      intro k _
      rw [← mul_sub, abs_mul, combShellMass_div, expShellMass]
      refine mul_le_mul (hgM _) ?_ (abs_nonneg _) hM0
      have h1 := hT (k * h) (by positivity)
      have h2 := hT ((k + 1) * h) (by positivity)
      rw [show -(((k : ℝ) + 1) * h) / 2 = -((k + 1) * h) / 2 by ring] at h2
      calc |combTail r (k * h) - combTail r ((k + 1) * h) -
            (Real.exp (-(k * h) / 2) - Real.exp (-((k + 1) * h) / 2))|
          = |(combTail r (k * h) - Real.exp (-(k * h) / 2)) -
              (combTail r ((k + 1) * h) - Real.exp (-((k + 1) * h) / 2))| := by ring_nf
        _ ≤ |combTail r (k * h) - Real.exp (-(k * h) / 2)| +
              |combTail r ((k + 1) * h) - Real.exp (-((k + 1) * h) / 2)| := abs_sub _ _
        _ ≤ 2 * η := by
            have e1 : -(k * h) / 2 = -((k : ℝ) * h) / 2 := rfl
            linarith
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, card_range, nsmul_eq_mul]
    nlinarith
  -- the tail at the cutoff
  have htail : combTail r (K * h) ≤ Real.exp (-(K * h) / 2) + η := by
    have := hT (K * h) (by positivity)
    linarith [(abs_le.mp this).2]
  have hdisc' : |combDepthSum g r 0 / combMass r -
      ∑ k ∈ range K, g (k * h) * (combShellMass r h k / combMass r)| ≤
      ε / 8 + M * combTail r (K * h) := by
    have heq : combDepthSum g r 0 / combMass r -
        ∑ k ∈ range K, g (k * h) * (combShellMass r h k / combMass r) =
        (combDepthSum g r 0 - ∑ k ∈ range K, g (k * h) * combShellMass r h k) / combMass r := by
      rw [sub_div, sum_div]; congr 1; exact sum_congr rfl fun k _ => by ring
    rw [heq, abs_div, abs_of_pos hS, div_le_iff₀ hS, combTail]
    calc |combDepthSum g r 0 - ∑ k ∈ range K, g (k * h) * combShellMass r h k|
        ≤ ε / 8 * combMass r + M * combMass (r - K * h / 2) := hdisc
      _ = (ε / 8 + M * (combMass (r - K * h / 2) / combMass r)) * combMass r := by
          field_simp
  have hMtail : M * combTail r (K * h) ≤ ε / 16 + ε / 16 := by
    have := mul_le_mul_of_nonneg_left htail hM0
    nlinarith
  calc |combDepthSum g r 0 / combMass r - horizonIntegral g|
      = |(combDepthSum g r 0 / combMass r -
            ∑ k ∈ range K, g (k * h) * (combShellMass r h k / combMass r)) +
          (∑ k ∈ range K, g (k * h) * (combShellMass r h k / combMass r) -
            ∑ k ∈ range K, g (k * h) * expShellMass h k) +
          (∑ k ∈ range K, g (k * h) * expShellMass h k - horizonIntegral g)| := by
        congr 1; ring
    _ ≤ (ε / 8 + M * combTail r (K * h)) + 2 * K * M * η +
          (ε / 8 + M * Real.exp (-(K * h) / 2)) := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add hdisc' hmid)) ?_)
        rw [abs_sub_comm]; exact hcont
    _ ≤ ε := by linarith

/-! ## The comb resolvent law -/

/-- The **horizon energy** `J(F) = ∫_{v>0} ∫_{u>0} A_F(u − v) ½e^{−u/2} ½e^{−v/2} du dv`. -/
def horizonEnergy (F : ℝ → ℝ) : ℝ :=
  horizonIntegral (fun v => horizonIntegral (fun u => autoCorr F (u - v)))

variable {F : ℝ → ℝ}

/-- The autocorrelation of a continuous compactly supported test has compact support. -/
theorem hasCompactSupport_autoCorr (hFc : HasCompactSupport F) :
    HasCompactSupport (autoCorr F) := by
  obtain ⟨B, hB⟩ := hFc.isCompact.isBounded.subset_closedBall 0
  have hsupp : ∀ x, B < |x| → F x = 0 := fun x hx => by
    by_contra hne
    have := hB (subset_tsupport F (Function.mem_support.mpr hne))
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * B + 1)) fun t ht => ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at ht
  exact autoCorr_eq_zero_of_support hsupp (by linarith)

/-- The translated horizon integral of the autocorrelation, `G(v) = ∫_{u>0} A_F(u − v) dμ(u)`. -/
def horizonAutoCorr (F : ℝ → ℝ) (v : ℝ) : ℝ := horizonIntegral (fun u => autoCorr F (u - v))

theorem abs_horizonAutoCorr_le (hF : Continuous F) (hFc : HasCompactSupport F) (v : ℝ) :
    |horizonAutoCorr F v| ≤ autoCorr F 0 :=
  abs_horizonIntegral_le fun _ => abs_autoCorr_le_autoCorr_zero hF hFc _

theorem uniformContinuous_horizonAutoCorr (hF : Continuous F) (hFc : HasCompactSupport F) :
    UniformContinuous (horizonAutoCorr F) := by
  have hA := (hasCompactSupport_autoCorr hFc).uniformContinuous_of_continuous
    (continuous_autoCorr hF hFc)
  rw [Metric.uniformContinuous_iff] at hA ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδA⟩ := hA (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun {a b} hab => ?_⟩
  have hcA := continuous_autoCorr hF hFc
  have hbound := fun t => abs_autoCorr_le_autoCorr_zero hF hFc t
  rw [Real.dist_eq, horizonAutoCorr, horizonAutoCorr,
    horizonIntegral_sub (hcA.comp' (continuous_sub_right _))
      (hcA.comp' (continuous_sub_right _)) (fun t => hbound _) (fun t => hbound _)]
  have hpt : ∀ u, |autoCorr F (u - a) - autoCorr F (u - b)| ≤ ε / 2 := fun u => by
    have : dist (u - a) (u - b) < δ := by
      rw [Real.dist_eq, show u - a - (u - b) = b - a by ring, abs_sub_comm]
      rwa [Real.dist_eq] at hab
    exact (hδA this).le
  exact (abs_horizonIntegral_le hpt).trans_lt (by linarith)

/-- The comb energy reads only depth differences. -/
theorem combEnergy_eq_depthSum (r : ℝ) :
    combEnergy F (combPrimes r) combWeight =
      ∑ q ∈ combPrimes r, combWeight q *
        combDepthSum (fun u => autoCorr F (u - combDepth r q)) r 0 := by
  rw [combEnergy, sum_comm]
  refine sum_congr rfl fun q _ => ?_
  simp only [combDepthSum, show r - 0 / 2 = r by ring, mul_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [combDepth_sub_combDepth]
  ring

/-- **The comb resolvent law.** For every continuous compactly supported test,
`E_r(F)/S_r² → J(F)`. -/
theorem tendsto_combEnergy_div_combMass_sq_horizonEnergy (hF : Continuous F)
    (hFc : HasCompactSupport F) :
    Tendsto (fun r => combEnergy F (combPrimes r) combWeight / combMass r ^ 2) atTop
      (𝓝 (horizonEnergy F)) := by
  have hcA := continuous_autoCorr hF hFc
  have huA := (hasCompactSupport_autoCorr hFc).uniformContinuous_of_continuous hcA
  have hbA := fun t => abs_autoCorr_le_autoCorr_zero hF hFc t
  have hcG : Continuous (horizonAutoCorr F) := (uniformContinuous_horizonAutoCorr hF hFc).continuous
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have h1 := eventually_abs_combAverage_sub_horizonIntegral_le hcA hbA huA hε3
  have h2 := eventually_abs_combAverage_sub_horizonIntegral_le hcG (abs_horizonAutoCorr_le hF hFc)
    (uniformContinuous_horizonAutoCorr hF hFc) hε3
  obtain ⟨R, hR⟩ := eventually_atTop.mp ((h1.and h2).and eventually_combMass_pos)
  refine ⟨R, fun r hr => ?_⟩
  obtain ⟨⟨hin, hout⟩, hS⟩ := hR r hr
  have hout0 := hout 0
  simp only [sub_zero] at hout0
  have hJ : horizonEnergy F = horizonIntegral (horizonAutoCorr F) := rfl
  -- inner averages are uniformly close to `G`
  have hinner : |combEnergy F (combPrimes r) combWeight / combMass r ^ 2 -
      combDepthSum (horizonAutoCorr F) r 0 / combMass r| ≤ ε / 3 := by
    have hD : combDepthSum (horizonAutoCorr F) r 0 =
        ∑ q ∈ combPrimes r, combWeight q * horizonAutoCorr F (combDepth r q) := by
      simp only [combDepthSum, show r - 0 / 2 = r by ring]
    have e1 : ∑ q ∈ combPrimes r, combWeight q *
        (combDepthSum (fun u => autoCorr F (u - combDepth r q)) r 0 / combMass r -
          horizonAutoCorr F (combDepth r q)) =
        (∑ q ∈ combPrimes r, combWeight q *
          combDepthSum (fun u => autoCorr F (u - combDepth r q)) r 0) / combMass r -
        ∑ q ∈ combPrimes r, combWeight q * horizonAutoCorr F (combDepth r q) := by
      rw [sum_div, ← sum_sub_distrib]
      exact sum_congr rfl fun q _ => by ring
    have heq : combEnergy F (combPrimes r) combWeight / combMass r ^ 2 -
        combDepthSum (horizonAutoCorr F) r 0 / combMass r =
        (∑ q ∈ combPrimes r, combWeight q *
          (combDepthSum (fun u => autoCorr F (u - combDepth r q)) r 0 / combMass r -
            horizonAutoCorr F (combDepth r q))) / combMass r := by
      rw [e1, combEnergy_eq_depthSum, hD]
      field_simp
    rw [heq, abs_div, abs_of_pos hS, div_le_iff₀ hS]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ q ∈ combPrimes r, |combWeight q *
          (combDepthSum (fun u => autoCorr F (u - combDepth r q)) r 0 / combMass r -
            horizonAutoCorr F (combDepth r q))|
        ≤ ∑ q ∈ combPrimes r, combWeight q * (ε / 3) := by
          refine sum_le_sum fun q _ => ?_
          rw [abs_mul, abs_of_nonneg (combWeight_nonneg q)]
          exact mul_le_mul_of_nonneg_left (hin (combDepth r q)) (combWeight_nonneg q)
      _ = ε / 3 * combMass r := by rw [← sum_mul, mul_comm]; rfl
  rw [Real.dist_eq, hJ]
  have houter : |combDepthSum (horizonAutoCorr F) r 0 / combMass r -
      horizonIntegral (horizonAutoCorr F)| ≤ ε / 3 := by
    simpa [sub_zero] using hout0
  calc |combEnergy F (combPrimes r) combWeight / combMass r ^ 2 - horizonIntegral (horizonAutoCorr F)|
      ≤ |combEnergy F (combPrimes r) combWeight / combMass r ^ 2 -
          combDepthSum (horizonAutoCorr F) r 0 / combMass r| +
        |combDepthSum (horizonAutoCorr F) r 0 / combMass r -
          horizonIntegral (horizonAutoCorr F)| := abs_sub_le _ _ _
    _ ≤ ε / 3 + ε / 3 := add_le_add hinner houter
    _ < ε := by linarith

theorem horizonEnergy_nonneg (hF : Continuous F) (hFc : HasCompactSupport F) :
    0 ≤ horizonEnergy F := by
  refine ge_of_tendsto (tendsto_combEnergy_div_combMass_sq_horizonEnergy hF hFc)
    (Eventually.of_forall fun r => div_nonneg ?_ (sq_nonneg _))
  rw [combEnergy_eq_testPairing ⟨hF, hFc⟩]
  exact testPairing_self_nonneg _

theorem horizonEnergy_le (hF : Continuous F) (hFc : HasCompactSupport F) :
    horizonEnergy F ≤ autoCorr F 0 := by
  refine le_of_tendsto (tendsto_combEnergy_div_combMass_sq_horizonEnergy hF hFc) ?_
  filter_upwards [eventually_combMass_pos] with r hr
  rw [div_le_iff₀ (by positivity)]
  have := combEnergy_le_combMass_sq_mul hF hFc r
  linarith

/-- **The raw comb energy on a fixed test is `4 J(F) e^{2r}`.** -/
theorem tendsto_combEnergy_div_exp_horizonEnergy (hF : Continuous F) (hFc : HasCompactSupport F) :
    Tendsto (fun r => combEnergy F (combPrimes r) combWeight / Real.exp (2 * r)) atTop
      (𝓝 (4 * horizonEnergy F)) := by
  have h := (tendsto_combEnergy_div_combMass_sq_horizonEnergy hF hFc).mul
    (tendsto_combMass_div_exp.pow 2)
  rw [show horizonEnergy F * 2 ^ 2 = 4 * horizonEnergy F by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_combMass_pos] with r hr
  have he : Real.exp (2 * r) = Real.exp r ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  rw [he, div_pow]
  field_simp

/-! ## The horizon energy is positive on every nonzero test -/

/-- **The probe bound.** Pairing the comb against the translate of the test to depth `v` gives
`G(v)² ≤ A_F(0) J(F)`, where `G(v) = ∫_{u>0} A_F(u − v) dμ(u)`. -/
theorem sq_horizonAutoCorr_le (hF : Continuous F) (hFc : HasCompactSupport F) (v : ℝ) :
    horizonAutoCorr F v ^ 2 ≤ autoCorr F 0 * horizonEnergy F := by
  have hN : ContCompact F := ⟨hF, hFc⟩
  have hcA := continuous_autoCorr hF hFc
  have huA := (hasCompactSupport_autoCorr hFc).uniformContinuous_of_continuous hcA
  have hbA := fun t => abs_autoCorr_le_autoCorr_zero hF hFc t
  -- the probe pairing, normalized, converges to `G(v)`
  have hprobe : Tendsto (fun r => combDepthSum (fun u => autoCorr F (u - v)) r 0 / combMass r)
      atTop (𝓝 (horizonAutoCorr F v)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨R, hR⟩ := eventually_atTop.mp
      (eventually_abs_combAverage_sub_horizonIntegral_le hcA hbA huA (half_pos hε))
    exact ⟨R, fun r hr => by
      rw [Real.dist_eq]; exact (hR r hr v).trans_lt (half_lt_self hε)⟩
  have hlim := (hprobe.pow 2)
  have hupper := (tendsto_combEnergy_div_combMass_sq_horizonEnergy hF hFc).const_mul (autoCorr F 0)
  refine le_of_tendsto_of_tendsto' hlim hupper fun r => ?_
  -- Cauchy–Schwarz between the comb and the translate
  rcases (combMass_nonneg r).eq_or_lt with hS | hS
  · rw [← hS]; simp
  have hC : ContCompact (primeComb F (combPrimes r) combWeight) := by
    rw [primeComb]; exact contCompact_finsetComb hN _ _ _
  have hY : ContCompact (fun x => F (x + (2 * r - v))) := hN.translate _
  have hcs := testPairing_cauchy_schwarz hC hY
  have hpair : testPairing (primeComb F (combPrimes r) combWeight) (fun x => F (x + (2 * r - v))) =
      combDepthSum (fun u => autoCorr F (u - v)) r 0 := by
    rw [testPairing_comm, primeComb, testPairing_single_finsetComb hN, combDepthSum]
    simp only [show r - 0 / 2 = r by ring]
    refine sum_congr rfl fun p _ => ?_
    rw [← autoCorr_neg]
    congr 1; congr 1; simp only [combDepth]; ring
  rw [hpair, ← combEnergy_eq_testPairing hN, testPairing_translate F F, testPairing_self_eq_autoCorr_zero] at hcs
  rw [div_pow, div_le_iff₀ (by positivity)]
  calc combDepthSum (fun u => autoCorr F (u - v)) r 0 ^ 2
      ≤ combEnergy F (combPrimes r) combWeight * autoCorr F 0 := hcs
    _ = autoCorr F 0 * (combEnergy F (combPrimes r) combWeight / combMass r ^ 2) * combMass r ^ 2 := by
        field_simp

/-- Translating a half-line integral: `∫_{u>0} ψ(u − v) du = ∫_{s>−v} ψ(s) ds`. -/
theorem integral_Ioi_zero_comp_sub (ψ : ℝ → ℝ) (v : ℝ) :
    ∫ u in Ioi 0, ψ (u - v) = ∫ s in Ioi (-v), ψ s := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_sub_right_eq_self (fun s => (Ioi (-v)).indicator ψ s) v]
  congr 1
  ext u
  simp only [Set.indicator, Set.mem_Ioi]
  by_cases hu : 0 < u
  · rw [if_pos hu, if_pos (by linarith)]
  · rw [if_neg hu, if_neg (by linarith)]

/-- `G(v) = ½e^{−v/2} ∫_{s>−v} A_F(s) e^{−s/2} ds`. -/
theorem horizonAutoCorr_eq (v : ℝ) :
    horizonAutoCorr F v =
      Real.exp (-v / 2) / 2 * ∫ s in Ioi (-v), autoCorr F s * Real.exp (-s / 2) := by
  rw [horizonAutoCorr, horizonIntegral, ← integral_Ioi_zero_comp_sub, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [horizonDensity]
  rw [show -(u - v) / 2 = -u / 2 + v / 2 by ring, Real.exp_add]
  have h : Real.exp (-v / 2) * Real.exp (v / 2) = 1 := by
    rw [← Real.exp_add, show -v / 2 + v / 2 = 0 by ring, Real.exp_zero]
  calc autoCorr F (u - v) * (Real.exp (-u / 2) / 2)
      = autoCorr F (u - v) * (Real.exp (-u / 2) / 2) * (Real.exp (-v / 2) * Real.exp (v / 2)) := by
        rw [h, mul_one]
    _ = _ := by ring

/-- **The horizon energy is positive on every nonzero test.** -/
theorem horizonEnergy_pos (hF : Continuous F) (hFc : HasCompactSupport F) {x₀ : ℝ}
    (hx₀ : F x₀ ≠ 0) : 0 < horizonEnergy F := by
  have hA0 : 0 < autoCorr F 0 := by
    have hcont : Continuous fun x => F x * F x := hF.mul hF
    have h := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume)
      hFc.mul_left (fun x => mul_self_nonneg _) (mul_self_ne_zero.mpr hx₀)
    simpa [autoCorr] using h
  rcases (horizonEnergy_nonneg hF hFc).eq_or_lt with hJ | hJ
  swap; · exact hJ
  exfalso
  -- `J = 0` forces `G ≡ 0`, hence `∫_{s>w} A_F e^{−s/2} = 0` for every `w`
  set ψ : ℝ → ℝ := fun s => autoCorr F s * Real.exp (-s / 2)
  have hψc : Continuous ψ := (continuous_autoCorr hF hFc).mul (by fun_prop)
  have hψs : HasCompactSupport ψ := (hasCompactSupport_autoCorr hFc).mul_right
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  have hG : ∀ w, ∫ s in Ioi w, ψ s = 0 := by
    intro w
    have h := sq_horizonAutoCorr_le hF hFc (-w)
    rw [← hJ, mul_zero] at h
    have h0 : horizonAutoCorr F (-w) = 0 := by nlinarith [sq_nonneg (horizonAutoCorr F (-w))]
    rw [horizonAutoCorr_eq, neg_neg] at h0
    have hc : Real.exp (w / 2) / 2 ≠ 0 := by positivity
    exact (mul_eq_zero.mp h0).resolve_left hc
  -- every interval integral of `ψ` vanishes, so `ψ ≡ 0`
  have hint : ∀ b, ∫ s in (0 : ℝ)..b, ψ s = 0 := fun b => by
    rw [← intervalIntegral.integral_Ioi_sub_Ioi' hψi.integrableOn hψi.integrableOn, hG, hG, sub_self]
  have hψ0 : ψ 0 = 0 := by
    have hd := (hψc.integral_hasStrictDerivAt 0 0).hasDerivAt
    have hconst : (fun u => ∫ s in (0 : ℝ)..u, ψ s) = fun _ => (0 : ℝ) := funext hint
    rw [hconst] at hd
    exact (hasDerivAt_const 0 (0 : ℝ)).unique hd |>.symm
  have : ψ 0 = autoCorr F 0 := by simp [ψ]
  linarith

/-- **The raw comb energy is exponentially large on every nonzero test**: `E_r(F) ∼ 4 J(F) e^{2r}`
with `J(F) > 0`. -/
theorem exists_pos_tendsto_combEnergy_div_exp (hF : Continuous F) (hFc : HasCompactSupport F)
    {x₀ : ℝ} (hx₀ : F x₀ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun r => combEnergy F (combPrimes r) combWeight / Real.exp (2 * r))
      atTop (𝓝 c) :=
  ⟨4 * horizonEnergy F, by linarith [horizonEnergy_pos hF hFc hx₀],
    tendsto_combEnergy_div_exp_horizonEnergy hF hFc⟩

end GaloisForLFunctions.ArithmeticCompensationTheory
