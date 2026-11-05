import GaloisForLFunctions.FiniteFreeProbability.XiMomentsOnALine
import GaloisForLFunctions.FiniteFreeProbability.DirichletPiecesAreNeverRealRooted
import GaloisForLFunctions.FiniteFreeProbability.ZeroFreeHalfPlaneStability
import GaloisForLFunctions.HTGeometry.VitaliConvergence

/-!
# The Cauchy limit law for the Jensen roots of `ξ`

Let `x` run over the roots of `R_d(ξ(σ + i·))`, `ℓ_d = ½ log d`, and let

`G_d(z) = (1/d) Σ_x 1/(z − x/ℓ_d)`

be the Cauchy transform of the empirical law of the roots at scale `ℓ_d`.

**Theorem.**

* For every `σ ≥ 1/2` and `θ > 0`, unconditionally, `G_d(iθ) → 1/(iθ + i)`.
* If all the roots lie in `Im x ≤ 0` (always for `σ ≥ 1`; at `σ = 1/2` this is RH), then
  `G_d(z) → 1/(z + i)` for every `z` in the upper half-plane.

Since `1/(z + i)` is the Cauchy transform of the standard Cauchy law `dλ/(π(1 + λ²))`, the bulk of the
Jensen roots of `ξ` follows a Cauchy law of scale `½ log d`, on every line. This is the finite free
central limit behaviour of `ξ`: the `R`-transform of the rank-one pieces `R_d(1 − w/a_q)` sums to
`−ξ'/ξ`, Stirling makes it `∓i ½ log d`, and a constant `R`-transform `∓i` is the Cauchy law.

The scale `½ log d` comes from the Gamma factor alone, and the limit does not depend on `σ`. So the bulk
is universal and cannot see the zeros: at `σ = 1/2`, the law on the imaginary axis holds whether or not
RH does. All arithmetic sits in the `o(d)` outliers `x ≈ d/z_q`.

Mechanism on the imaginary axis: `R_d(it) = i^d m_d(t)` with `m_d(t) = E (t + V)^d`, the moments of a
positive measure, and `R_d' = d R_{d−1}` give `G_d(iθ) = −i ℓ_d m_{d−1}(θℓ_d)/m_d(θℓ_d)`; then the ratio
law. Off the axis: `|G_d(z)| ≤ 1/Im z` on stable lines, and Vitali.
-/

open Polynomial Filter Topology Complex Metric
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

/-- The reversed Jensen polynomial of `w ↦ ξ(σ + iw)`. -/
abbrev xiJensen (σ : ℝ) (d : ℕ) : ℂ[X] := jensenRev d (PowerSeries.mk (xiShiftCoeff σ))

/-- `R_d(it) = i^d m_d(t)`. -/
theorem eval_xiJensen_I_mul (σ : ℝ) (d : ℕ) (t : ℝ) :
    (xiJensen σ d).eval (I * t) = I ^ d * (jensenMass (xiMoment σ) d t : ℂ) := by
  rw [xiJensen, jensenRev_eq_sum, eval_finsetSum, jensenMass]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [eval_mul, eval_C, eval_pow, eval_X, PowerSeries.coeff_mk, xiShiftCoeff_eq_moment]
  have hdesc : (d.descFactorial k : ℂ) = (d.choose k : ℂ) * (k.factorial : ℂ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hId : I ^ d = I ^ k * I ^ (d - k) := by rw [← pow_add, Nat.add_sub_cancel' hk']
  rw [hdesc, mul_pow, hId]
  field_simp

theorem multiset_sum_one_div_eq {q : ℂ[X]} {z : ℂ} (hz : q.eval z ≠ 0) :
    (q.roots.map fun x => 1 / (z - x)).sum = q.derivative.eval z / q.eval z := by
  rw [(IsAlgClosed.splits q).eval_derivative_eq_eval_mul_sum hz]
  field_simp

/-- The Cauchy transform `G_d(z) = (1/d) Σ_x 1/(z − x/ℓ_d)` of the roots at scale `ℓ_d = ½ log d`, in
the form `(ℓ_d/d) Σ_x 1/(ℓ_d z − x)`. -/
def jensenCauchy (σ : ℝ) (d : ℕ) (z : ℂ) : ℂ :=
  ((cauchyScale d / d : ℝ) : ℂ) * ((xiJensen σ d).roots.map fun x => 1 / ((cauchyScale d : ℂ) * z - x)).sum

/-- On the imaginary axis, `G_{d+1}(iθ) = −i ℓ m_d(θℓ)/m_{d+1}(θℓ)`. -/
theorem jensenCauchy_imag {σ : ℝ} (d : ℕ) (θ : ℝ)
    (hm : jensenMass (xiMoment σ) (d + 1) (θ * cauchyScale (d + 1)) ≠ 0) :
    jensenCauchy σ (d + 1) (I * θ) = -I * ((cauchyScale (d + 1) *
      jensenMass (xiMoment σ) d (θ * cauchyScale (d + 1)) /
        jensenMass (xiMoment σ) (d + 1) (θ * cauchyScale (d + 1)) : ℝ) : ℂ) := by
  set ℓ := cauchyScale (d + 1)
  set t : ℝ := θ * ℓ
  have harg : (ℓ : ℂ) * (I * θ) = I * (t : ℂ) := by
    simp only [t]
    push_cast
    ring
  have hval := eval_xiJensen_I_mul σ (d + 1) t
  have hval' := eval_xiJensen_I_mul σ d t
  have hmC : (jensenMass (xiMoment σ) (d + 1) t : ℂ) ≠ 0 := ofReal_ne_zero.2 hm
  have hI : I ^ d ≠ 0 := pow_ne_zero _ I_ne_zero
  have hne : (xiJensen σ (d + 1)).eval (I * (t : ℂ)) ≠ 0 := by
    rw [hval]
    exact mul_ne_zero (pow_ne_zero _ I_ne_zero) hmC
  have hdR : ((d + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero d)
  rw [jensenCauchy, harg, multiset_sum_one_div_eq hne, xiJensen, derivative_jensenRev, eval_mul,
    eval_C, ← xiJensen, ← xiJensen, hval, hval', pow_succ]
  push_cast at hdR ⊢
  have hI2 : I * -I = 1 := by rw [mul_neg, I_mul_I, neg_neg]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **The Cauchy law on the imaginary axis (unconditional).** For `σ ≥ 1/2` and `θ > 0`:
`G_d(iθ) → 1/(iθ + i)`. -/
theorem tendsto_jensenCauchy_imag {σ : ℝ} (hσ : 1 / 2 ≤ σ) {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun d => jensenCauchy σ d (I * θ)) atTop (𝓝 (1 / (I * θ + I))) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hr := tendsto_cauchy_ratio hσ hθ
  have hc := ((continuous_ofReal.tendsto _).comp hr).const_mul (-I)
  have h1θ : ((1 : ℂ) + θ) ≠ 0 := by
    have : ((1 + θ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (by linarith)
    simpa using this
  have hlim : -I * ((1 / (1 + θ) : ℝ) : ℂ) = 1 / (I * θ + I) := by
    have hfac : I * (θ : ℂ) + I = I * (1 + θ) := by ring
    rw [hfac]
    push_cast
    field_simp
    rw [mul_comm, I_mul_I]
    ring
  rw [hlim] at hc
  refine hc.congr' ?_
  have hev : ∀ᶠ d : ℕ in atTop, 1 ≤ θ * cauchyScale (d + 1) := by
    have h := (tendsto_add_atTop_nat 1).eventually (tendsto_cauchyScale.eventually_ge_atTop (1 / θ))
    filter_upwards [h] with d hd
    rw [div_le_iff₀ hθ] at hd
    linarith
  filter_upwards [hev] with d hd
  exact (jensenCauchy_imag d θ (jensenMass_pos hσ _ hd).ne').symm

/-! ## The upper half-plane on stable lines -/

theorem norm_multiset_sum_map_le (M : Multiset ℂ) (f : ℂ → ℂ) {B : ℝ}
    (h : ∀ x ∈ M, ‖f x‖ ≤ B) : ‖(M.map f).sum‖ ≤ Multiset.card M * B := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    have h1 := h a (Multiset.mem_cons_self a M)
    have h2 := ih fun x hx => h x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    push_cast
    calc ‖f a + (M.map f).sum‖ ≤ ‖f a‖ + ‖(M.map f).sum‖ := norm_add_le _ _
      _ ≤ B + Multiset.card M * B := add_le_add h1 h2
      _ = _ := by ring

theorem cauchyScale_nonneg (d : ℕ) : 0 ≤ cauchyScale d :=
  div_nonneg (Real.log_natCast_nonneg d) (by norm_num)

variable {σ : ℝ}

/-- `|G_d(z)| ≤ 1/Im z` when all the roots lie in `Im x ≤ 0`. -/
theorem norm_jensenCauchy_le (hstab : ∀ d x, (xiJensen σ d).IsRoot x → x.im ≤ 0) (d : ℕ) {z : ℂ}
    (hz : 0 < z.im) : ‖jensenCauchy σ d z‖ ≤ 1 / z.im := by
  rcases (cauchyScale_nonneg d).eq_or_lt with h0 | hℓ
  · simp [jensenCauchy, ← h0]
    positivity
  set ℓ := cauchyScale d
  have hd0 : (d : ℝ) ≠ 0 := by
    intro h
    have hd : d = 0 := by exact_mod_cast h
    simp [ℓ, cauchyScale, hd] at hℓ
  have hdpos : (0 : ℝ) < d := lt_of_le_of_ne (Nat.cast_nonneg d) hd0.symm
  have hterm : ∀ x ∈ (xiJensen σ d).roots, ‖1 / ((ℓ : ℂ) * z - x)‖ ≤ 1 / (ℓ * z.im) := fun x hx => by
    have hxim := hstab d x (isRoot_of_mem_roots hx)
    have him : ℓ * z.im ≤ ((ℓ : ℂ) * z - x).im := by
      simp only [sub_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
      linarith
    have hnorm : ℓ * z.im ≤ ‖(ℓ : ℂ) * z - x‖ :=
      him.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by positivity) hnorm
  have hsum := norm_multiset_sum_map_le _ _ hterm
  have hcard : (Multiset.card (xiJensen σ d).roots : ℝ) ≤ d := by
    exact_mod_cast (card_roots' _).trans (natDegree_jensenRev_le _ _)
  have hB : 0 ≤ 1 / (ℓ * z.im) := by positivity
  rw [jensenCauchy, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hℓ.le hdpos.le)]
  calc ℓ / d * ‖((xiJensen σ d).roots.map fun x => 1 / ((ℓ : ℂ) * z - x)).sum‖
      ≤ ℓ / d * ((d : ℝ) * (1 / (ℓ * z.im))) :=
        mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_right hcard hB))
          (div_nonneg hℓ.le hdpos.le)
    _ = 1 / z.im := by field_simp

theorem differentiableOn_multiset_sum {ℓ : ℝ} (hℓ : 0 < ℓ) (M : Multiset ℂ)
    (hM : ∀ x ∈ M, x.im ≤ 0) :
    DifferentiableOn ℂ (fun z : ℂ => (M.map fun x => 1 / ((ℓ : ℂ) * z - x)).sum) {z | 0 < z.im} := by
  induction M using Multiset.induction_on with
  | empty => simpa using differentiableOn_const 0
  | cons a M ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    refine DifferentiableOn.add ?_ (ih fun x hx => hM x (Multiset.mem_cons_of_mem hx))
    refine DifferentiableOn.div (differentiableOn_const _) (by fun_prop) fun z hz h0 => ?_
    have him := congrArg Complex.im h0
    simp only [sub_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, zero_im] at him
    have ha := hM a (Multiset.mem_cons_self a M)
    have : 0 < ℓ * z.im := mul_pos hℓ hz
    linarith

theorem differentiableOn_jensenCauchy (hstab : ∀ d x, (xiJensen σ d).IsRoot x → x.im ≤ 0) (d : ℕ) :
    DifferentiableOn ℂ (jensenCauchy σ d) {z | 0 < z.im} := by
  rcases (cauchyScale_nonneg d).eq_or_lt with h0 | hℓ
  · have : jensenCauchy σ d = fun _ => 0 := funext fun z => by simp [jensenCauchy, ← h0]
    rw [this]
    exact differentiableOn_const 0
  · exact (differentiableOn_multiset_sum hℓ _ fun x hx =>
      hstab d x (isRoot_of_mem_roots hx)).const_mul _

/-- **The Cauchy law on stable lines.** If all the roots of all `R_d(ξ(σ + i·))` lie in `Im x ≤ 0`, the
Cauchy transforms converge on the upper half-plane to `1/(z + i)`, the Cauchy transform of the
standard Cauchy law. -/
theorem tendsto_jensenCauchy_of_stable (hσ : 1 / 2 ≤ σ)
    (hstab : ∀ d x, (xiJensen σ d).IsRoot x → x.im ≤ 0) {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun d => jensenCauchy σ d z) atTop (𝓝 (1 / (z + I))) := by
  set U : Set ℂ := {z | 0 < z.im}
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_im
  have hUc : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected
  have hIU : I ∈ U := by simp [U]
  set Y : Set ℂ := {w | ∃ θ : ℝ, 0 < θ ∧ w = I * θ}
  have hYlim : ∀ w ∈ Y, Tendsto (fun d => jensenCauchy σ d w) atTop (𝓝 (1 / (w + I))) := by
    rintro w ⟨θ, hθ, rfl⟩
    exact tendsto_jensenCauchy_imag hσ hθ
  have hacc : ∃ᶠ w in 𝓝[≠] I, w ∈ Y := by
    set u : ℕ → ℂ := fun n => I * ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
    have hu : Tendsto u atTop (𝓝[≠] I) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n h => ?_⟩
      · have h1 : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        have h2 := ((continuous_ofReal.tendsto _).comp h1).const_mul I
        simpa [u, Function.comp_def] using h2
      · have h3 : ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) = 1 := by
          have h4 : I * ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) = I * 1 := by
            rw [mul_one]
            exact h
          exact mul_left_cancel₀ I_ne_zero h4
        have h5 : 1 + 1 / ((n : ℝ) + 1) = 1 := by exact_mod_cast h3
        have h6 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    refine hu.frequently (Frequently.of_forall fun n => ⟨1 + 1 / ((n : ℝ) + 1), by positivity, rfl⟩)
  have hloc : ∀ w ∈ U, ∃ R : ℝ, 0 < R ∧ ball w R ⊆ U ∧ ∃ C : ℝ,
      ∀ n, ∀ v ∈ ball w R, ‖jensenCauchy σ n v‖ ≤ C := fun w hw => by
    have hw' : 0 < w.im := hw
    have hsub : ∀ v ∈ ball w (w.im / 2), w.im / 2 ≤ v.im := fun v hv => by
      rw [mem_ball, dist_eq_norm] at hv
      have := (abs_le.1 ((Complex.abs_im_le_norm (v - w)).trans hv.le)).1
      rw [sub_im] at this
      linarith
    refine ⟨w.im / 2, by positivity, fun v hv => ?_, 1 / (w.im / 2), fun n v hv => ?_⟩
    · have := hsub v hv
      show 0 < v.im
      linarith
    · have hv' := hsub v hv
      have hvpos : 0 < v.im := by linarith
      exact (norm_jensenCauchy_le hstab n hvpos).trans
        (one_div_le_one_div_of_le (by positivity) hv')
  obtain ⟨G, hGd, hG⟩ := vitali_tendstoLocallyUniformlyOn_of_isPreconnected hUc
    (differentiableOn_jensenCauchy hstab) hloc hIU hacc (fun w hw => ⟨_, hYlim w hw⟩)
  have hne : ∀ w ∈ U, w + I ≠ 0 := fun w hw h => by
    have him := congrArg Complex.im h
    simp only [add_im, I_im, zero_im] at him
    have hw' : 0 < w.im := hw
    linarith
  have hg : DifferentiableOn ℂ (fun w => 1 / (w + I)) U :=
    DifferentiableOn.div (differentiableOn_const _) (by fun_prop) hne
  have hYU : ∀ w ∈ Y, w ∈ U := by
    rintro w ⟨θ, hθ, rfl⟩
    simpa [U] using hθ
  have heq := (hGd.analyticOnNhd hUo).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd hUo) hUc hIU (hacc.mono fun w hw =>
      tendsto_nhds_unique (hG.tendsto_at (hYU w hw)) (hYlim w hw))
  have hfinal := hG.tendsto_at (show z ∈ U from hz)
  rwa [heq (show z ∈ U from hz)] at hfinal

/-- **The Cauchy limit law, unconditional at `Re s ≥ 1`.** -/
theorem tendsto_jensenCauchy_of_one_le (hσ : 1 ≤ σ) {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun d => jensenCauchy σ d z) atTop (𝓝 (1 / (z + I))) :=
  tendsto_jensenCauchy_of_stable (by linarith) (fun d _ hx => im_le_zero_of_one_le hσ d hx) hz

/-- **The Cauchy limit law right of all zeros.** At `σ = 1/2` the hypothesis is RH. -/
theorem tendsto_jensenCauchy_of_zeroFree (hσ : 1 / 2 ≤ σ) (hzf : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ σ)
    {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun d => jensenCauchy σ d z) atTop (𝓝 (1 / (z + I))) :=
  tendsto_jensenCauchy_of_stable hσ (fun d _ hx => im_le_zero_of_zeroFree hzf d hx) hz

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.tendsto_jensenCauchy_imag
#print axioms FiniteFreeProbability.tendsto_jensenCauchy_of_one_le
#print axioms FiniteFreeProbability.tendsto_jensenCauchy_of_zeroFree
