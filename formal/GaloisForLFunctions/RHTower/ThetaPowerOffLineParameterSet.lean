import GaloisForLFunctions.RHTower.ThetaPowerTranscendentalOffLineZero
import GaloisForLFunctions.RHTower.ThetaPowerChiEightLFunction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargeHardyRigidity
import GaloisForLFunctions.RHTower.ThetaPowerChiTwelveLFunction

/-!
# The off-line parameter set of the theta-power family is open with countable complement

Let `O = {a ∈ (0, 1/2) : Λ_a has a zero with 0 < Im w < 1/2}`.

* `O` is open.  On the axis `|F_a| = |θ₃| |h|^{a/4}`, so for `a ∈ [a₁, a₂]` the tail `T_a(x) = e^{x/2}F_a(ie^{2x})/2`
  is dominated by `|T_{a₁}| + |T_{a₂}|`, which decays like `e^{-|x|³-|x|}`.  Dominated convergence gives
  `sup_{|Im w| ≤ ρ} |Λ_a(w) - Λ_{a₀}(w)| ≤ ∫ e^{ρ|x|}|T_a - T_{a₀}| → 0` as `a → a₀`.  `Λ_{a₀}(0) = ∫ T_{a₀} > 0`, so
  zeros of `Λ_{a₀}` are isolated, and a zero isolated by a sphere inside the open half-strip persists
  (sphere domination).
* `(0, 1/2) ∖ O` consists of algebraic numbers (transcendental parameters lie in `O`), hence is countable; it is
  closed in `(0, 1/2)`.
-/

open Complex Real Filter Topology MeasureTheory Set Metric

namespace RHTower

open Bottcher

noncomputable section

variable {a : ℝ}

/-- `x^s ≤ x^{s₁} + x^{s₂}` for `x ≥ 0` and `0 < s₁ ≤ s ≤ s₂`. -/
private theorem rpow_le_add_of_mem_Icc {x s s₁ s₂ : ℝ} (hx : 0 ≤ x) (h0 : 0 < s₁) (h₁ : s₁ ≤ s)
    (h₂ : s ≤ s₂) : x ^ s ≤ x ^ s₁ + x ^ s₂ := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [Real.zero_rpow (by linarith), Real.zero_rpow h0.ne', Real.zero_rpow (by linarith)]
    norm_num
  · have := rpow_neg_le_add (x := x) (s := -s) (s₁ := -s₂) (s₂ := -s₁) hx (by linarith)
      (by linarith)
    simpa [neg_neg, add_comm] using this

/-- **Domination in the parameter.** `|F_a| ≤ |F_{a₁}| + |F_{a₂}|` for `0 < a₁ ≤ a ≤ a₂`. -/
theorem norm_thetaPowerForm_le_add {a₁ a₂ : ℝ} (h0 : 0 < a₁) (h₁ : a₁ ≤ a) (h₂ : a ≤ a₂) {τ : ℂ}
    (hτ : 0 < τ.im) :
    ‖thetaPowerForm a τ‖ ≤ ‖thetaPowerForm a₁ τ‖ + ‖thetaPowerForm a₂ τ‖ := by
  rw [norm_thetaPowerForm hτ, norm_thetaPowerForm hτ, norm_thetaPowerForm hτ, ← mul_add]
  exact mul_le_mul_of_nonneg_left (rpow_le_add_of_mem_Icc (norm_nonneg _) (by positivity)
    (by linarith) (by linarith)) (norm_nonneg _)

theorem norm_modTail_thetaPowerForm (a x : ℝ) :
    ‖modTail (thetaPowerForm a) 0 x‖ = Real.exp (x / 2) * ‖thetaPowerForm a (modAxisPoint x)‖ / 2 := by
  unfold modTail
  rw [sub_zero, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_two]

theorem norm_modTail_thetaPowerForm_le_add {a₁ a₂ : ℝ} (h0 : 0 < a₁) (h₁ : a₁ ≤ a) (h₂ : a ≤ a₂)
    (x : ℝ) :
    ‖modTail (thetaPowerForm a) 0 x‖ ≤
      ‖modTail (thetaPowerForm a₁) 0 x‖ + ‖modTail (thetaPowerForm a₂) 0 x‖ := by
  rw [norm_modTail_thetaPowerForm, norm_modTail_thetaPowerForm, norm_modTail_thetaPowerForm]
  have h := norm_thetaPowerForm_le_add h0 h₁ h₂ (modAxisPoint_mem x)
  have he := Real.exp_pos (x / 2)
  nlinarith

theorem continuous_modTail_thetaPowerForm_param (x : ℝ) :
    Continuous fun a : ℝ => modTail (thetaPowerForm a) 0 x := by
  unfold modTail thetaPowerForm
  fun_prop

/-- The integrand bound `e^{ρ|x|} e^{-|x|³-|x|} ≤ e^{(1+ρ)^{3/2}} e^{-|x|}`. -/
theorem exp_mul_abs_mul_cubic_le {ρ : ℝ} (hρ : 0 ≤ ρ) (x : ℝ) :
    Real.exp (ρ * |x|) * Real.exp (-|x| ^ 3 - |x|) ≤
      Real.exp ((1 + ρ) ^ (3 / 2 : ℝ)) * Real.exp (-(1 * |x|)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  have h := linear_sub_cube_le_rpow hρ (abs_nonneg x)
  exact Real.exp_le_exp.mpr (by linarith)

theorem integrable_exp_mul_abs_mul_norm_modTail (ha : 0 < a) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Integrable fun x : ℝ => Real.exp (ρ * |x|) * ‖modTail (thetaPowerForm a) 0 x‖ := by
  obtain ⟨K, hK0, hT⟩ := exists_thetaPowerTail_cubic ha
  refine Integrable.mono' ((integrable_exp_neg_mul_abs' one_pos).const_mul
    (K * Real.exp ((1 + ρ) ^ (3 / 2 : ℝ)))) ?_ (Eventually.of_forall fun x => ?_)
  · exact ((by fun_prop : Continuous fun x : ℝ => Real.exp (ρ * |x|)).mul
      (continuous_modTail_thetaPowerForm a).norm).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    calc Real.exp (ρ * |x|) * ‖modTail (thetaPowerForm a) 0 x‖
        ≤ Real.exp (ρ * |x|) * (K * Real.exp (-|x| ^ 3 - |x|)) :=
          mul_le_mul_of_nonneg_left (hT x) (Real.exp_pos _).le
      _ = K * (Real.exp (ρ * |x|) * Real.exp (-|x| ^ 3 - |x|)) := by ring
      _ ≤ K * (Real.exp ((1 + ρ) ^ (3 / 2 : ℝ)) * Real.exp (-(1 * |x|))) :=
          mul_le_mul_of_nonneg_left (exp_mul_abs_mul_cubic_le hρ x) hK0
      _ = _ := by ring

theorem integrable_thetaPowerXiC_integrand (ha : 0 < a) (w : ℂ) :
    Integrable fun x : ℝ => Complex.exp (-Complex.I * w * x) * modTail (thetaPowerForm a) 0 x := by
  refine Integrable.mono' (integrable_exp_mul_abs_mul_norm_modTail ha (abs_nonneg w.im)) ?_
    (Eventually.of_forall fun x => ?_)
  · exact ((by fun_prop : Continuous fun x : ℝ => Complex.exp (-Complex.I * w * x)).mul
      (continuous_modTail_thetaPowerForm a)).aestronglyMeasurable
  · rw [norm_mul, norm_cexp_neg_I_mul_mul]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    calc w.im * x ≤ |w.im * x| := le_abs_self _
      _ = |w.im| * |x| := abs_mul _ _

/-- **Uniform comparison.** `|Λ_a(w) - Λ_b(w)| ≤ ∫ e^{ρ|x|} |T_a - T_b|` on `|Im w| ≤ ρ`. -/
theorem norm_thetaPowerXiC_sub_le {a b ρ : ℝ} (ha : 0 < a) (hb : 0 < b) (hρ : 0 ≤ ρ) {w : ℂ}
    (hw : |w.im| ≤ ρ) :
    ‖thetaPowerXiC a w - thetaPowerXiC b w‖ ≤
      ∫ x : ℝ, Real.exp (ρ * |x|) *
        ‖modTail (thetaPowerForm a) 0 x - modTail (thetaPowerForm b) 0 x‖ := by
  unfold thetaPowerXiC
  rw [← integral_sub (integrable_thetaPowerXiC_integrand ha w) (integrable_thetaPowerXiC_integrand hb w)]
  refine norm_integral_le_of_norm_le ?_ (Eventually.of_forall fun x => ?_)
  · refine Integrable.mono' ((integrable_exp_mul_abs_mul_norm_modTail ha hρ).add
      (integrable_exp_mul_abs_mul_norm_modTail hb hρ)) ?_ (Eventually.of_forall fun x => ?_)
    · exact ((by fun_prop : Continuous fun x : ℝ => Real.exp (ρ * |x|)).mul
        ((continuous_modTail_thetaPowerForm a).sub
          (continuous_modTail_thetaPowerForm b)).norm).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity), Pi.add_apply, ← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_pos _).le
  · rw [← mul_sub, norm_mul, norm_cexp_neg_I_mul_mul]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    calc w.im * x ≤ |w.im * x| := le_abs_self _
      _ = |w.im| * |x| := abs_mul _ _
      _ ≤ ρ * |x| := mul_le_mul_of_nonneg_right hw (abs_nonneg x)

/-- **Continuity of the tail in the parameter**, in the weighted `L¹` norm. -/
theorem tendsto_integral_modTail_sub (ha : 0 < a) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Tendsto (fun b : ℝ => ∫ x : ℝ, Real.exp (ρ * |x|) *
        ‖modTail (thetaPowerForm b) 0 x - modTail (thetaPowerForm a) 0 x‖) (𝓝 a) (𝓝 0) := by
  have hmem : Icc (a / 2) (2 * a) ∈ 𝓝 a := Icc_mem_nhds (by linarith) (by linarith)
  set bound : ℝ → ℝ := fun x => Real.exp (ρ * |x|) * ‖modTail (thetaPowerForm (a / 2)) 0 x‖ +
    Real.exp (ρ * |x|) * ‖modTail (thetaPowerForm (2 * a)) 0 x‖ +
    Real.exp (ρ * |x|) * ‖modTail (thetaPowerForm a) 0 x‖ with hbound
  have hbi : Integrable bound :=
    ((integrable_exp_mul_abs_mul_norm_modTail (by linarith) hρ).add
      (integrable_exp_mul_abs_mul_norm_modTail (by linarith) hρ)).add
      (integrable_exp_mul_abs_mul_norm_modTail ha hρ)
  have h := tendsto_integral_filter_of_dominated_convergence (f := fun _ : ℝ => (0 : ℝ))
    (F := fun b x => Real.exp (ρ * |x|) *
      ‖modTail (thetaPowerForm b) 0 x - modTail (thetaPowerForm a) 0 x‖) bound
    (Eventually.of_forall fun b => ((by fun_prop : Continuous fun x : ℝ => Real.exp (ρ * |x|)).mul
      ((continuous_modTail_thetaPowerForm b).sub
        (continuous_modTail_thetaPowerForm a)).norm).aestronglyMeasurable)
    (Filter.eventually_of_mem hmem fun b hb => Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (by positivity), hbound]
      have h1 := norm_modTail_thetaPowerForm_le_add (a := b) (by linarith) hb.1 hb.2 x
      have h2 := norm_sub_le (modTail (thetaPowerForm b) 0 x) (modTail (thetaPowerForm a) 0 x)
      have he := (Real.exp_pos (ρ * |x|)).le
      nlinarith [mul_le_mul_of_nonneg_left h2 he, mul_le_mul_of_nonneg_left h1 he])
    hbi (Eventually.of_forall fun x => by
      have hc : Tendsto (fun b : ℝ => modTail (thetaPowerForm b) 0 x) (𝓝 a)
          (𝓝 (modTail (thetaPowerForm a) 0 x)) :=
        (continuous_modTail_thetaPowerForm_param x).tendsto a
      have := ((hc.sub_const (modTail (thetaPowerForm a) 0 x)).norm).const_mul (Real.exp (ρ * |x|))
      rwa [sub_self, norm_zero, mul_zero] at this)
  simpa using h

/-- **Uniform convergence in the parameter** on every horizontal strip `|Im w| ≤ ρ`. -/
theorem tendstoUniformlyOn_thetaPowerXiC (ha : 0 < a) {ρ : ℝ} (hρ : 0 ≤ ρ) {S : Set ℂ}
    (hS : ∀ w ∈ S, |w.im| ≤ ρ) :
    TendstoUniformlyOn (fun b w => thetaPowerXiC b w) (thetaPowerXiC a) (𝓝 a) S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hpos : ∀ᶠ b in 𝓝 a, 0 < b := eventually_gt_nhds ha
  filter_upwards [hpos, (tendsto_order.1 (tendsto_integral_modTail_sub ha hρ)).2 ε hε] with b hb hI
  intro w hw
  rw [dist_eq_norm, norm_sub_rev]
  exact (norm_thetaPowerXiC_sub_le hb ha hρ (hS w hw)).trans_lt hI

/-- `F_a` is positive on the imaginary axis. -/
theorem thetaPowerForm_I_mul_re_pos (a : ℝ) {y : ℝ} (hy : 0 < y) :
    0 < (thetaPowerForm a (I * (y : ℂ))).re := by
  have h3 : thetaThree (I * (y : ℂ)) = ((thetaThree (I * (y : ℂ))).re : ℂ) :=
    theta_I_mul_real_eq_re thetaThree_conj y
  have hL : hauptmodulLog (I * (y : ℂ)) = ((hauptmodulLog (I * (y : ℂ))).re : ℂ) := by
    apply Complex.ext <;> simp [hauptmodulLog_I_mul_im hy]
  unfold thetaPowerForm
  rw [h3, hL, ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_pos (thetaThree_I_mul_re_pos hy) (Real.exp_pos _)

/-- `Λ_a(0) ≠ 0`: it is the integral of the positive tail. -/
theorem thetaPowerXiC_zero_ne_zero (ha : 0 < a) : thetaPowerXiC a 0 ≠ 0 := by
  have hint := integrable_thetaPowerXiC_integrand ha 0
  have hre : (thetaPowerXiC a 0).re = ∫ x : ℝ, (modTail (thetaPowerForm a) 0 x).re := by
    unfold thetaPowerXiC
    have h := Complex.reCLM.integral_comp_comm hint
    simp only [Complex.reCLM_apply] at h
    rw [← h]
    congr 1
    funext x
    simp
  have hposT : ∀ x : ℝ, 0 < (modTail (thetaPowerForm a) 0 x).re := by
    intro x
    unfold modTail modAxisPoint
    rw [sub_zero, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re,
      Complex.re_ofReal_mul]
    exact div_pos (mul_pos (Real.exp_pos _) (thetaPowerForm_I_mul_re_pos a (Real.exp_pos _)))
      (by norm_num)
  have hreInt : Integrable fun x : ℝ => (modTail (thetaPowerForm a) 0 x).re := by
    have := hint.re
    simpa using this
  have hpos : 0 < ∫ x : ℝ, (modTail (thetaPowerForm a) 0 x).re := by
    rw [integral_pos_iff_support_of_nonneg (fun x => (hposT x).le) hreInt]
    have : Function.support (fun x : ℝ => (modTail (thetaPowerForm a) 0 x).re) = univ :=
      Set.eq_univ_of_forall fun x => Function.mem_support.2 (hposT x).ne'
    rw [this, Real.volume_univ]
    exact ENNReal.zero_lt_top
  intro h
  rw [h, Complex.zero_re] at hre
  linarith

/-- A zero isolated by a sphere persists under uniform convergence on the sphere (any filter). -/
theorem eventually_exists_zero_closedBall_of_tendstoUniformlyOn_sphere {ι : Type*} {l : Filter ι}
    {F : ℂ → ℂ} {G : ι → ℂ → ℂ} (hF : Differentiable ℂ F) (hG : ∀ᶠ i in l, Differentiable ℂ (G i))
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : F z = 0) (hsphere : ∀ w ∈ sphere z r, F w ≠ 0)
    (hconv : TendstoUniformlyOn G F l (sphere z r)) :
    ∀ᶠ i in l, ∃ w ∈ closedBall z r, G i w = 0 := by
  obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_sphere z r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hF.continuous.continuousOn.norm
  have hm : 0 < ‖F w₀‖ := norm_pos_iff.mpr (hsphere w₀ hw₀)
  filter_upwards [hG, (Metric.tendstoUniformlyOn_iff.mp hconv) (‖F w₀‖ / 3) (by positivity)] with i hGi hi
  by_cases hiz : G i z = 0
  · exact ⟨z, mem_closedBall_self hr.le, hiz⟩
  obtain ⟨w, hw, hw0⟩ := exists_zero_of_sphere_domination (g := fun w => G i w - F w) (h := F) hr
    (hGi.sub hF).diffContOnCl hF.diffContOnCl hz (by simpa [hz] using hiz) (fun w hw => by
      have h1 := hi w hw
      have h2 := hmin hw
      simp only [mem_setOf_eq] at h2
      rw [dist_eq_norm, norm_sub_rev] at h1
      linarith)
  exact ⟨w, hw, by simpa using hw0⟩

/-- The off-line parameter set `O`. -/
def thetaPowerOffLineSet : Set ℝ :=
  {a : ℝ | 0 < a ∧ a < 1 / 2 ∧ ∃ w : ℂ, 0 < w.im ∧ w.im < 1 / 2 ∧ thetaPowerXiC a w = 0}

/-- **`O` is open.** -/
theorem isOpen_thetaPowerOffLineSet : IsOpen thetaPowerOffLineSet := by
  rw [isOpen_iff_mem_nhds]
  rintro a₀ ⟨ha0, ha1, w₀, hw0, hw1, hz⟩
  have hD := differentiable_thetaPowerXiC ha0
  -- isolated zero
  have hiso : ∀ᶠ w in 𝓝[≠] w₀, thetaPowerXiC a₀ w ≠ 0 := by
    rcases (hD.analyticAt w₀).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have hall := (hD.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (mem_univ w₀) h (mem_univ 0)
      exact thetaPowerXiC_zero_ne_zero ha0 hall
    · exact h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hiso)
  set r : ℝ := min (ε / 2) (min (w₀.im / 2) ((1 / 2 - w₀.im) / 2)) with hr
  have hr0 : 0 < r := by rw [hr]; exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hrε : r < ε := by rw [hr]; exact (min_le_left _ _).trans_lt (by linarith)
  have hr1 : r ≤ w₀.im / 2 := by rw [hr]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hr2 : r ≤ (1 / 2 - w₀.im) / 2 := by rw [hr]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hsphere : ∀ w ∈ sphere w₀ r, thetaPowerXiC a₀ w ≠ 0 := by
    intro w hw
    have hd : dist w w₀ = r := mem_sphere.mp hw
    refine hball (by rw [hd]; exact hrε) ?_
    intro h
    rw [h, dist_self] at hd
    linarith
  have him : ∀ w ∈ closedBall w₀ r, |w.im - w₀.im| ≤ r := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have := Complex.abs_im_le_norm (w - w₀)
    rw [Complex.sub_im] at this
    linarith
  have hconv : TendstoUniformlyOn (fun b w => thetaPowerXiC b w) (thetaPowerXiC a₀) (𝓝 a₀)
      (sphere w₀ r) :=
    tendstoUniformlyOn_thetaPowerXiC ha0 (ρ := 1) zero_le_one fun w hw => by
      have h := him w (sphere_subset_closedBall hw)
      rw [abs_le] at h ⊢
      constructor <;> linarith [h.1, h.2]
  have hev := eventually_exists_zero_closedBall_of_tendstoUniformlyOn_sphere hD
    ((eventually_gt_nhds ha0).mono fun b hb => differentiable_thetaPowerXiC hb) hr0 hz hsphere hconv
  have hpos : ∀ᶠ b in 𝓝 a₀, 0 < b ∧ b < 1 / 2 := Filter.eventually_of_mem (Ioo_mem_nhds ha0 ha1) fun b hb => hb
  filter_upwards [hev, hpos] with b hb hbI
  obtain ⟨w, hw, hwz⟩ := hb
  have h := abs_le.mp (him w hw)
  exact ⟨hbI.1, hbI.2, w, by linarith [h.1], by linarith [h.2], hwz⟩

/-- **The RH-exceptional parameters are countable and algebraic.** Every `a ∈ (0, 1/2)` outside the open set
`O` is algebraic; in particular `(0, 1/2) ∖ O` is countable and closed in `(0, 1/2)`. -/
theorem thetaPower_exceptional_algebraic {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (ha : a ∉ thetaPowerOffLineSet) : IsAlgebraic ℚ a := by
  by_contra htr
  obtain ⟨w, hw0, hw1, hz⟩ := thetaPowerXiC_offline_zero_of_transcendental ha0 ha1 htr
  exact ha ⟨ha0, ha1, w, hw0, hw1, hz⟩

theorem countable_thetaPower_exceptional :
    (Ioo (0 : ℝ) (1 / 2) \ thetaPowerOffLineSet).Countable :=
  (Algebraic.countable ℚ ℝ).mono fun _ ha => thetaPower_exceptional_algebraic ha.1.1 ha.1.2 ha.2

theorem isClosed_thetaPower_exceptional_in_interval :
    IsClosed ((Subtype.val : Ioo (0 : ℝ) (1 / 2) → ℝ) ⁻¹' thetaPowerOffLineSetᶜ) :=
  (isOpen_thetaPowerOffLineSet.isClosed_compl).preimage continuous_subtype_val

/-- **C7 for all interior parameters refutes GRH for `χ₁₂`.** If every `a ∈ (0, 1/2)` gave `Λ_a` an off-line zero
with `|Im w| < 1`, then at `a = 1/3` (where `Λ_{1/3}` is the completed `L(s, χ₁₂)`) the completed `L`-function of
`χ₁₂` would vanish off the critical line inside `|Re s - 1/2| < 1`. -/
theorem thetaPower_allInterior_offline_imp_chiTwelve_offline
    (h : ∀ a : ℝ, 0 < a → a < 1 / 2 → ∃ w : ℂ, w.im ≠ 0 ∧ |w.im| < 1 ∧ thetaPowerXiC a w = 0) :
    ∃ s : ℂ, s.re ≠ 1 / 2 ∧ |s.re - 1 / 2| < 1 ∧
      DirichletCharacter.completedLFunction dirichletChiTwelve s = 0 :=
  thetaPowerXiC_third_offline_zero_iff.mp (h (1 / 3) (by norm_num) (by norm_num))

/-- **Holomorphy at every cusp does not force RH.** For every `a ∈ (0, 1/2)` outside a countable set of algebraic
numbers, `Λ_a` has infinitely many zeros with `0 < Im w < 1/2`; the parameters with such a zero form an open set. -/
theorem thetaPower_cuspHolomorphy_not_RH :
    IsOpen thetaPowerOffLineSet ∧ (Ioo (0 : ℝ) (1 / 2) \ thetaPowerOffLineSet).Countable ∧
      ∀ a : ℝ, 0 < a → a < 1 / 2 → Transcendental ℚ a →
        {w : ℂ | 0 < w.im ∧ w.im < 1 / 2 ∧ thetaPowerXiC a w = 0}.Infinite :=
  ⟨isOpen_thetaPowerOffLineSet, countable_thetaPower_exceptional,
    fun _ ha0 ha1 htr => thetaPowerXiC_offline_zeros_infinite_of_transcendental ha0 ha1 htr⟩

end

end RHTower
