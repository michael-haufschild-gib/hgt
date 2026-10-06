import GaloisForLFunctions.RHTower.VerticalProgressionLatticeSums
import GaloisForLFunctions.RHTower.ZetaSquareDiagonalHarmonic
import GaloisForLFunctions.RHTower.HighBlockCutoffMonotone

/-!
# Lattice sums of the Gaussian cutoff along a vertical progression

Let `ψ ∈ C^∞` be supported in `[1, 2]`, `α > 0`, `2|β| ≤ αT`, and write `t_ℓ = αℓ + β` and
`V = smoothAFECutoff`. For `c > 0` this file bounds

`Σ_{ℓ ∈ ℤ} ψ(ℓ/T) V(c/t_ℓ) e(ℓu)`.

* **Trivial bounds** (`norm_latticeSum_cutoff_le_trivial`, `norm_latticeSum_cutoff_le_decay`):
  `≤ (T + 1) Ψ₀` and `≤ (T + 1) Ψ₀ K_A (3αT/c)^A` for every `A > 0`, from `|V| ≤ 1` and the power
  decay of `V`.
* **Oscillation** (`exists_norm_latticeSum_cutoff_le`): if `u` is at distance `≥ δ > 0` from `ℤ`,
  then `≤ C_k T² / (c T^k δ^k)`, uniformly in `c`.

**Proof of the oscillation bound.** On the line `Re w = 1`,
`V(c/t) = (1/2π) ∫ c^{−w} t^w e^{w²}/w dv`, so the sum is `(1/2π) ∫ c^{−w} e^{w²}/w Σ_ℓ g_w(ℓ) e(ℓu)`
with `g_w(x) = ψ(x/T)(αx + β)^w`. By Leibniz and
`∂^i (αx + β)^w = α^i w(w − 1)⋯(w − i + 1)(αx + β)^{w − i}`, with `αx + β ∈ [αT/2, 3αT]` on the
support, `‖g_w^{(k)}‖ ≤ C (‖w‖ + k)^k · 3αT / T^k`; the lattice bound
`‖Σ g(ℓ)e(ℓu)‖ ≤ (len + k + 1)‖g^{(k)}‖/(4δ)^k` and the Gaussian decay of `e^{w²}` finish.
-/

open Complex MeasureTheory Set Filter

namespace RHTower.VerticalAP

noncomputable section

/-! ## Powers of an affine function -/

theorem hasDerivAt_affine_cpow {α β : ℝ} (c : ℂ) {x : ℝ} (hx : 0 < α * x + β) :
    HasDerivAt (fun y : ℝ => (((α * y + β : ℝ)) : ℂ) ^ c)
      (c * (((α * x + β : ℝ)) : ℂ) ^ (c - 1) * α) x := by
  have hslit : (((α * x + β : ℝ)) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  have hf : HasDerivAt (fun z : ℂ => z ^ c) (c * (((α * x + β : ℝ)) : ℂ) ^ (c - 1))
      (((α * x + β : ℝ)) : ℂ) := (hasStrictDerivAt_cpow_const hslit).hasDerivAt
  have hg : HasDerivAt (fun y : ℝ => (((α * y + β : ℝ)) : ℂ)) (α : ℂ) x := by
    have : HasDerivAt (fun y : ℝ => α * y + β) α x := by
      simpa using ((hasDerivAt_id x).const_mul α).add_const β
    exact this.ofReal_comp
  exact hf.comp x hg

/-- `∂^n (αx + β)^c = α^n c(c − 1)⋯(c − n + 1)(αx + β)^{c − n}` where `αx + β > 0`. -/
theorem iteratedDeriv_affine_cpow (n : ℕ) {α β : ℝ} (c : ℂ) {x : ℝ} (hx : 0 < α * x + β) :
    iteratedDeriv n (fun y : ℝ => (((α * y + β : ℝ)) : ℂ) ^ c) x =
      (α : ℂ) ^ n * (descPochhammer ℂ n).eval c * (((α * x + β : ℝ)) : ℂ) ^ (c - n) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hpos : ∀ᶠ y in nhds x, 0 < α * y + β :=
      (show ContinuousAt (fun y : ℝ => α * y + β) x by fun_prop).eventually
        (eventually_gt_nhds hx)
    have heq : iteratedDeriv n (fun y : ℝ => (((α * y + β : ℝ)) : ℂ) ^ c) =ᶠ[nhds x]
        fun y => (α : ℂ) ^ n * (descPochhammer ℂ n).eval c * (((α * y + β : ℝ)) : ℂ) ^ (c - n) := by
      filter_upwards [hpos] with y hy
      exact ih hy
    rw [heq.deriv_eq, ((hasDerivAt_affine_cpow (c - n) hx).const_mul
      ((α : ℂ) ^ n * (descPochhammer ℂ n).eval c)).deriv, descPochhammer_succ_eval]
    push_cast
    rw [show c - n - 1 = c - (n + 1) by ring]
    ring

theorem contDiffAt_affine_cpow {α β : ℝ} (c : ℂ) {x : ℝ} (hx : 0 < α * x + β) (n : ℕ) :
    ContDiffAt ℝ n (fun y : ℝ => (((α * y + β : ℝ)) : ℂ) ^ c) x := by
  have hpos : ∀ᶠ y in nhds x, 0 < α * y + β :=
    (show ContinuousAt (fun y : ℝ => α * y + β) x by fun_prop).eventually (eventually_gt_nhds hx)
  have heq : (fun y : ℝ => (((α * y + β : ℝ)) : ℂ) ^ c) =ᶠ[nhds x]
      fun y => Complex.exp (c * ((Real.log (α * y + β) : ℝ) : ℂ)) := by
    filter_upwards [hpos] with y hy
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), ← Complex.ofReal_log hy.le]
    ring_nf
  refine ContDiffAt.congr_of_eventuallyEq ?_ heq
  have hlog : ContDiffAt ℝ n (fun y : ℝ => Real.log (α * y + β)) x :=
    (Real.contDiffAt_log.mpr hx.ne').comp x
      ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffAt
  have hofReal : ContDiffAt ℝ n (fun y : ℝ => ((Real.log (α * y + β) : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hlog
  exact (contDiffAt_const.mul hofReal).cexp

theorem norm_descPochhammer_eval_le (n : ℕ) (c : ℂ) :
    ‖(descPochhammer ℂ n).eval c‖ ≤ (‖c‖ + n) ^ n := by
  rw [descPochhammer_eval_eq_prod_range, norm_prod]
  calc ∏ j ∈ Finset.range n, ‖c - j‖ ≤ ∏ _j ∈ Finset.range n, (‖c‖ + n) := by
        refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j hj => ?_
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_natCast]
        have := Finset.mem_range.mp hj
        have : (j : ℝ) ≤ n := by exact_mod_cast this.le
        linarith
    _ = (‖c‖ + n) ^ n := by rw [Finset.prod_const, Finset.card_range]

/-! ## The cutoff-power weight -/

/-- `g_w(x) = ψ(x/T)(αx + β)^w`. -/
def cutoffPowerWeight (ψ : ℝ → ℂ) (T α β : ℝ) (w : ℂ) (x : ℝ) : ℂ :=
  ψ (x / T) * (((α * x + β : ℝ)) : ℂ) ^ w

theorem support_cutoff_subset {ψ : ℝ → ℂ} (hsupp : Function.support ψ ⊆ Icc 1 2) {T : ℝ}
    (hT : 0 < T) (F : ℝ → ℂ) :
    Function.support (fun x => ψ (x / T) * F x) ⊆ Icc T (2 * T) := by
  intro x hx
  have h1 : ψ (x / T) ≠ 0 := left_ne_zero_of_mul hx
  obtain ⟨h21, h22⟩ := hsupp h1
  rw [le_div_iff₀ hT] at h21
  rw [div_le_iff₀ hT] at h22
  exact ⟨by linarith, by linarith⟩

/-- The weight vanishes near every point outside `[T, 2T]`. -/
theorem cutoff_eventually_zero {ψ : ℝ → ℂ} (hsupp : Function.support ψ ⊆ Icc 1 2) {T : ℝ}
    (hT : 0 < T) (F : ℝ → ℂ) {x : ℝ} (hx : x < T ∨ 2 * T < x) :
    (fun y => ψ (y / T) * F y) =ᶠ[nhds x] fun _ => 0 := by
  have hopen : IsOpen {y : ℝ | y < T ∨ 2 * T < y} :=
    (isOpen_gt' T).union (isOpen_lt' (2 * T))
  filter_upwards [hopen.mem_nhds hx] with y hy
  have : ψ (y / T) = 0 := by
    by_contra h
    obtain ⟨h21, h22⟩ := hsupp h
    rw [le_div_iff₀ hT] at h21
    rw [div_le_iff₀ hT] at h22
    rcases hy with hy | hy <;> linarith
  simp [this]

theorem support_cutoffPowerWeight {ψ : ℝ → ℂ} (hsupp : Function.support ψ ⊆ Icc 1 2) {T : ℝ}
    (hT : 0 < T) (α β : ℝ) (w : ℂ) :
    Function.support (cutoffPowerWeight ψ T α β w) ⊆ Icc T (2 * T) :=
  support_cutoff_subset hsupp hT _

theorem contDiff_cutoffPowerWeight {ψ : ℝ → ℂ} (hψ : ∀ k : ℕ, ContDiff ℝ k ψ)
    (hsupp : Function.support ψ ⊆ Icc 1 2) {T α β : ℝ} (hT : 0 < T) (hα : 0 < α)
    (hβ : 2 * |β| ≤ α * T) (w : ℂ) (k : ℕ) :
    ContDiff ℝ k (cutoffPowerWeight ψ T α β w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : T ≤ x ∧ x ≤ 2 * T
  · have hpos : 0 < α * x + β := by
      have := neg_abs_le β
      nlinarith
    have h1 : ContDiffAt ℝ k (fun y => ψ (y / T)) x :=
      ((hψ k).comp (contDiff_id.div_const T)).contDiffAt
    exact h1.mul (contDiffAt_affine_cpow w hpos k)
  · have hx' : x < T ∨ 2 * T < x := by
      rcases not_and_or.mp hx with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
    exact contDiffAt_const.congr_of_eventuallyEq
      (cutoff_eventually_zero hsupp hT (fun y => (((α * y + β : ℝ)) : ℂ) ^ w) hx')

/-- **Derivative bound for the cutoff-power weight.** With `‖ψ^{(j)}‖ ≤ Ψ_j` and `Re w ≥ 0`,
`‖g_w^{(k)}‖ ≤ (Σ_j C(k,j) 2^{k−j} Ψ_j) (‖w‖ + k)^k (3αT)^{Re w} / T^k`. -/
theorem norm_iteratedDeriv_cutoffPowerWeight_le {ψ : ℝ → ℂ} (hψ : ∀ k : ℕ, ContDiff ℝ k ψ)
    (hsupp : Function.support ψ ⊆ Icc 1 2) {Ψ : ℕ → ℝ} (hΨ : ∀ j y, ‖iteratedDeriv j ψ y‖ ≤ Ψ j)
    {T α β : ℝ} (hT : 0 < T) (hα : 0 < α) (hβ : 2 * |β| ≤ α * T) {w : ℂ} (hw : 0 ≤ w.re)
    (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k (cutoffPowerWeight ψ T α β w) x‖ ≤
      (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * 2 ^ (k - j) * Ψ j) *
        (‖w‖ + k) ^ k * (3 * α * T) ^ w.re / T ^ k := by
  have hΨ0 : ∀ j, 0 ≤ Ψ j := fun j => (norm_nonneg _).trans (hΨ j 0)
  have hR : 0 ≤ (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * 2 ^ (k - j) * Ψ j) *
      (‖w‖ + k) ^ k * (3 * α * T) ^ w.re / T ^ k := by
    have : 0 ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * 2 ^ (k - j) * Ψ j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hΨ0 j)
    positivity
  by_cases hx : T ≤ x ∧ x ≤ 2 * T
  · have hlow : α * T / 2 ≤ α * x + β := by
      have := neg_abs_le β
      nlinarith
    have hhigh : α * x + β ≤ 3 * α * T := by
      have := le_abs_self β
      nlinarith
    have hpos : 0 < α * x + β := lt_of_lt_of_le (by positivity) hlow
    have h1 : ∀ n : ℕ, ContDiffAt ℝ n (fun y => ψ (y / T)) x := fun n =>
      ((hψ n).comp (contDiff_id.div_const T)).contDiffAt
    have hmul : iteratedDeriv k (cutoffPowerWeight ψ T α β w) x =
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℂ) *
          iteratedDeriv i (fun y => ψ (y / T)) x *
          iteratedDeriv (k - i) (fun y : ℝ => (((α * y + β : ℝ)) : ℂ) ^ w) x := by
      have hdef : cutoffPowerWeight ψ T α β w =
          (fun y => ψ (y / T)) * fun y : ℝ => (((α * y + β : ℝ)) : ℂ) ^ w := rfl
      rw [hdef]
      exact iteratedDeriv_mul (h1 k) (contDiffAt_affine_cpow w hpos k)
    rw [hmul]
    refine (norm_sum_le _ _).trans ?_
    have hscale : ∀ i, iteratedDeriv i (fun y => ψ (y / T)) x =
        (T⁻¹) ^ i • iteratedDeriv i ψ (T⁻¹ * x) := by
      intro i
      have := iteratedDeriv_comp_const_smul (hψ i) T⁻¹
      have hfun : (fun y => ψ (y / T)) = fun y => ψ (T⁻¹ * y) := by
        funext y; rw [div_eq_inv_mul]
      rw [hfun, this]
    have hterm : ∀ i ∈ Finset.range (k + 1),
        ‖(k.choose i : ℂ) * iteratedDeriv i (fun y => ψ (y / T)) x *
          iteratedDeriv (k - i) (fun y : ℝ => (((α * y + β : ℝ)) : ℂ) ^ w) x‖ ≤
        (k.choose i : ℝ) * 2 ^ (k - i) * Ψ i * (‖w‖ + k) ^ k * (3 * α * T) ^ w.re / T ^ k := by
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [norm_mul, norm_mul, Complex.norm_natCast, hscale, norm_smul, norm_pow, norm_inv,
        Real.norm_eq_abs, abs_of_pos hT, iteratedDeriv_affine_cpow (k - i) w hpos, norm_mul,
        norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα,
        Complex.norm_cpow_eq_rpow_re_of_pos hpos]
      have hpoch := norm_descPochhammer_eval_le (k - i) w
      have hre : (w - ((k - i : ℕ) : ℂ)).re = w.re - (k - i : ℕ) := by simp
      rw [hre]
      have hψi := hΨ i (T⁻¹ * x)
      -- `(αx+β)^{Re w − (k−i)} ≤ (3αT)^{Re w} (2/(αT))^{k−i}`
      have hpow : (α * x + β) ^ (w.re - (k - i : ℕ)) ≤
          (3 * α * T) ^ w.re * (2 / (α * T)) ^ (k - i) := by
        rw [Real.rpow_sub hpos, Real.rpow_natCast]
        rw [div_eq_mul_inv]
        refine mul_le_mul (Real.rpow_le_rpow hpos.le hhigh hw) ?_ (by positivity) (by positivity)
        rw [← inv_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ _
        rw [inv_le_comm₀ hpos (by positivity), inv_div]
        exact hlow
      have hbase : (‖w‖ + (k - i : ℕ)) ^ (k - i) ≤ (‖w‖ + k) ^ k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0; simp
        · have h1k : 1 ≤ ‖w‖ + k := by
            have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
            linarith [norm_nonneg w]
          calc (‖w‖ + (k - i : ℕ)) ^ (k - i) ≤ (‖w‖ + k) ^ (k - i) := by
                refine pow_le_pow_left₀ (by positivity) ?_ _
                have : ((k - i : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k i
                linarith
            _ ≤ (‖w‖ + k) ^ k := pow_le_pow_right₀ h1k (Nat.sub_le k i)
      have hTk : (T⁻¹) ^ i * (α ^ (k - i) * (2 / (α * T)) ^ (k - i)) = 2 ^ (k - i) / T ^ k := by
        have e1 : α ^ (k - i) * (2 / (α * T)) ^ (k - i) = (2 / T) ^ (k - i) := by
          rw [← mul_pow]
          congr 1
          field_simp
        rw [e1, div_pow, inv_pow, ← Nat.add_sub_cancel' hik, pow_add, Nat.add_sub_cancel_left]
        field_simp
      calc (k.choose i : ℝ) * ((T⁻¹) ^ i * ‖iteratedDeriv i ψ (T⁻¹ * x)‖) *
            (α ^ (k - i) * ‖(descPochhammer ℂ (k - i)).eval w‖ *
              (α * x + β) ^ (w.re - (k - i : ℕ)))
          ≤ (k.choose i : ℝ) * ((T⁻¹) ^ i * Ψ i) *
            (α ^ (k - i) * (‖w‖ + k) ^ k *
              ((3 * α * T) ^ w.re * (2 / (α * T)) ^ (k - i))) := by
            gcongr
            all_goals first
              | exact hψi
              | exact hpoch.trans hbase
              | exact hpow
              | exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) (hΨ0 i))
        _ = (k.choose i : ℝ) * Ψ i * (‖w‖ + k) ^ k * (3 * α * T) ^ w.re *
              ((T⁻¹) ^ i * (α ^ (k - i) * (2 / (α * T)) ^ (k - i))) := by ring
        _ = (k.choose i : ℝ) * 2 ^ (k - i) * Ψ i * (‖w‖ + k) ^ k * (3 * α * T) ^ w.re /
              T ^ k := by
            rw [hTk]; ring
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_div]
  · have hx' : x < T ∨ 2 * T < x := by
      rcases not_and_or.mp hx with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
    have h0 := (cutoff_eventually_zero hsupp hT
      (fun y => (((α * y + β : ℝ)) : ℂ) ^ w) hx').iteratedDeriv_eq k
    have hdef : cutoffPowerWeight ψ T α β w = fun y => ψ (y / T) * (((α * y + β : ℝ)) : ℂ) ^ w := rfl
    rw [hdef, h0]
    simpa using hR

/-! ## The Gaussian cutoff along the progression -/

theorem ofReal_div_cpow_neg {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (w : ℂ) :
    (((c / t : ℝ)) : ℂ) ^ (-w) = (c : ℂ) ^ (-w) * (t : ℂ) ^ w := by
  rw [ZetaNotch.ofReal_cpow_eq_exp (div_pos hc ht), ZetaNotch.ofReal_cpow_eq_exp hc,
    ZetaNotch.ofReal_cpow_eq_exp ht, ← Complex.exp_add, Real.log_div hc.ne' ht.ne']
  congr 1
  push_cast
  ring

/-- Mellin form on `Re w = 1`: `V(c/t) = (1/2π) ∫ c^{−w} t^{w} e^{w²}/w dv`. -/
theorem smoothAFECutoff_div_eq_integral {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    smoothAFECutoff (c / t) = (1 / (2 * Real.pi) : ℂ) *
      ∫ v : ℝ, (c : ℂ) ^ (-(((1 : ℝ) : ℂ) + (v : ℂ) * I)) * (t : ℂ) ^ (((1 : ℝ) : ℂ) + (v : ℂ) * I) *
        smoothAFEGaussianKernel (((1 : ℝ) : ℂ) + (v : ℂ) * I) := by
  have hcut : smoothAFECutoff (c / t) = (1 / (2 * Real.pi) : ℂ) *
      ∫ v : ℝ, smoothAFEMellinIntegrand (c / t) (((1 : ℝ) : ℂ) + (v : ℂ) * I) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.real_smul]
    rfl
  rw [hcut]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smoothAFEMellinIntegrand]
  rw [ofReal_div_cpow_neg hc ht]

theorem norm_smoothAFECutoff_le_one' {y : ℝ} (hy : 0 < y) : ‖smoothAFECutoff y‖ ≤ 1 := by
  have hre : smoothAFECutoff y = (((smoothAFECutoff y).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [smoothAFECutoff_im_eq_zero hy])
  rw [hre, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (smoothAFECutoff_re_nonneg hy)]
  exact smoothAFECutoff_re_le_one hy

/-- **Trivial bound.** `‖Σ ψ(ℓ/T) V(c/t_ℓ) e(ℓu)‖ ≤ (T + 1) Ψ₀`. -/
theorem norm_latticeSum_cutoff_le_trivial {ψ : ℝ → ℂ} (hsupp : Function.support ψ ⊆ Icc 1 2)
    {Ψ₀ : ℝ} (hΨ₀ : ∀ y, ‖ψ y‖ ≤ Ψ₀) {α β T : ℝ} (hα : 0 < α) (hT : 0 < T)
    (hβ : 2 * |β| ≤ α * T) {c : ℝ} (hc : 0 < c) (u : ℝ) :
    ‖latticeSum (fun x => ψ (x / T) * smoothAFECutoff (c / (α * x + β))) u‖ ≤ (T + 1) * Ψ₀ := by
  have h := norm_latticeSum_le_of_bound
    (h := fun x => ψ (x / T) * smoothAFECutoff (c / (α * x + β))) (A := T) (B := 2 * T)
    (M := Ψ₀) (by linarith)
    (support_cutoff_subset hsupp hT (fun x => smoothAFECutoff (c / (α * x + β)))) (fun x => ?_) u
  · simpa [show 2 * T - T + 1 = T + 1 by ring] using h
  by_cases hx : ψ (x / T) = 0
  · simp only [hx, zero_mul, norm_zero]; exact (norm_nonneg _).trans (hΨ₀ 0)
  · obtain ⟨h21, _⟩ := hsupp hx
    rw [le_div_iff₀ hT] at h21
    have hpos : 0 < α * x + β := by
      have := neg_abs_le β
      nlinarith
    rw [norm_mul]
    calc ‖ψ (x / T)‖ * ‖smoothAFECutoff (c / (α * x + β))‖ ≤ Ψ₀ * 1 :=
          mul_le_mul (hΨ₀ _) (norm_smoothAFECutoff_le_one' (div_pos hc hpos)) (norm_nonneg _)
            ((norm_nonneg _).trans (hΨ₀ 0))
      _ = Ψ₀ := mul_one _

/-- **Decay bound.** For `A > 0` there is `K` with
`‖Σ ψ(ℓ/T) V(c/t_ℓ) e(ℓu)‖ ≤ (T + 1) Ψ₀ K (3αT/c)^A`. -/
theorem exists_norm_latticeSum_cutoff_le_decay {A : ℝ} (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ψ : ℝ → ℂ}, Function.support ψ ⊆ Icc 1 2 → ∀ {Ψ₀ : ℝ},
      (∀ y, ‖ψ y‖ ≤ Ψ₀) → ∀ {α β T : ℝ}, 0 < α → 0 < T → 2 * |β| ≤ α * T →
      ∀ {c : ℝ}, 0 < c → ∀ u : ℝ,
      ‖latticeSum (fun x => ψ (x / T) * smoothAFECutoff (c / (α * x + β))) u‖ ≤
        (T + 1) * (Ψ₀ * (K * (3 * α * T / c) ^ A)) := by
  obtain ⟨K, hK, hKb⟩ := exists_norm_smoothAFECutoff_le_neg_rpow hA
  refine ⟨K, hK, fun {ψ} hsupp {Ψ₀} hΨ₀ {α β T} hα hT hβ {c} hc u => ?_⟩
  have hΨ0 : 0 ≤ Ψ₀ := (norm_nonneg _).trans (hΨ₀ 0)
  have h := norm_latticeSum_le_of_bound
    (h := fun x => ψ (x / T) * smoothAFECutoff (c / (α * x + β))) (A := T) (B := 2 * T)
    (M := Ψ₀ * (K * (3 * α * T / c) ^ A)) (by linarith)
    (support_cutoff_subset hsupp hT (fun x => smoothAFECutoff (c / (α * x + β))))
    (fun x => ?_) u
  · simpa [show 2 * T - T + 1 = T + 1 by ring] using h
  by_cases hx : ψ (x / T) = 0
  · simp only [hx, zero_mul, norm_zero]; positivity
  · obtain ⟨h21, h22⟩ := hsupp hx
    rw [le_div_iff₀ hT] at h21
    rw [div_le_iff₀ hT] at h22
    have hpos : 0 < α * x + β := by
      have := neg_abs_le β
      nlinarith
    have hhigh : α * x + β ≤ 3 * α * T := by
      have := le_abs_self β
      nlinarith
    rw [norm_mul]
    refine mul_le_mul (hΨ₀ _) ?_ (norm_nonneg _) hΨ0
    refine (hKb (div_pos hc hpos)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hK
    rw [Real.rpow_neg (div_pos hc hpos).le, ← Real.inv_rpow (div_pos hc hpos).le, inv_div]
    exact Real.rpow_le_rpow (div_pos hpos hc).le (div_le_div_of_nonneg_right hhigh hc.le) hA.le

/-- **Oscillation bound.** If `u` is at distance `≥ δ > 0` from `ℤ`, then
`‖Σ ψ(ℓ/T) V(c/t_ℓ) e(ℓu)‖ ≤ C T² / (c T^k δ^k)`, uniformly in `c > 0` and `T ≥ 1`. -/
theorem exists_norm_latticeSum_cutoff_le {ψ : ℝ → ℂ} (hψ : ∀ k : ℕ, ContDiff ℝ k ψ)
    (hsupp : Function.support ψ ⊆ Icc 1 2) {Ψ : ℕ → ℝ} (hΨ : ∀ j y, ‖iteratedDeriv j ψ y‖ ≤ Ψ j)
    {α β : ℝ} (hα : 0 < α) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → 2 * |β| ≤ α * T → ∀ c : ℝ, 0 < c → ∀ u δ : ℝ, 0 < δ →
      (∀ j : ℤ, δ ≤ |u - j|) →
      ‖latticeSum (fun x => ψ (x / T) * smoothAFECutoff (c / (α * x + β))) u‖ ≤
        C * T ^ 2 / (c * T ^ k * δ ^ k) := by
  have hΨ0 : ∀ j, 0 ≤ Ψ j := fun j => (norm_nonneg _).trans (hΨ j 0)
  set Ak : ℝ := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * 2 ^ (k - j) * Ψ j with hAk
  have hAk0 : 0 ≤ Ak := Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hΨ0 j)
  set wl : ℝ → ℂ := fun v => ((1 : ℝ) : ℂ) + (v : ℂ) * I with hwl
  set bnd : ℝ → ℝ := fun v => ‖smoothAFEGaussianKernel (wl v)‖ * (‖wl v‖ + k) ^ k with hbnd
  have hbnd_int : Integrable bnd := by
    have hmaj : Integrable (fun v : ℝ =>
        Real.exp 1 * (k + 2) ^ k * ((1 + |v|) ^ k * Real.exp (-(v ^ 2)))) :=
      (ZetaNotch.integrable_one_add_abs_pow_mul_exp_neg_sq k).const_mul _
    refine hmaj.mono' ?_ (Eventually.of_forall fun v => ?_)
    · have hc1 : Continuous wl := by fun_prop
      have hc2 : Continuous fun v => smoothAFEGaussianKernel (wl v) := by
        unfold smoothAFEGaussianKernel
        refine Continuous.div (by fun_prop) hc1 fun v => ?_
        intro h; have := congrArg Complex.re h; simp [hwl] at this
      exact (hc2.norm.mul ((hc1.norm.add continuous_const).pow k)).aestronglyMeasurable
    · have hK := norm_smoothAFEGaussianKernel_vertical_le one_pos v
      have hw : ‖wl v‖ ≤ 1 + |v| := by
        refine (norm_add_le _ _).trans ?_
        simp
      have hpow : (‖wl v‖ + k) ^ k ≤ (k + 2) ^ k * (1 + |v|) ^ k := by
        rw [← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ k
        nlinarith [abs_nonneg v]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖smoothAFEGaussianKernel (wl v)‖ * (‖wl v‖ + k) ^ k
          ≤ (Real.exp (1 ^ 2) / 1 * Real.exp (-(v ^ 2))) * ((k + 2) ^ k * (1 + |v|) ^ k) :=
            mul_le_mul (by simpa [hwl] using hK) hpow (by positivity) (by positivity)
        _ = Real.exp 1 * (k + 2) ^ k * ((1 + |v|) ^ k * Real.exp (-(v ^ 2))) := by ring_nf
  set Ik : ℝ := ∫ v, bnd v with hIk
  have hIk0 : 0 ≤ Ik := integral_nonneg fun v => by positivity
  refine ⟨1 / (2 * Real.pi) * ((k + 2) * (3 * α) * Ak * Ik / 4 ^ k), by positivity, ?_⟩
  intro T hT1 hβ c hc u δ hδ hu
  have hT : 0 < T := by linarith
  -- rewrite the lattice sum through the Mellin integral
  have hsum := latticeSum_eq_sum (support_cutoff_subset hsupp hT
    (fun x => smoothAFECutoff (c / (α * x + β)))) u
  have hrange : ∀ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋, 0 < α * (ℓ : ℝ) + β := by
    intro ℓ hℓ
    have h1 : T ≤ ℓ := Int.ceil_le.mp (Finset.mem_Icc.mp hℓ).1
    have := neg_abs_le β
    nlinarith
  have hint : ∀ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋, Integrable (fun v : ℝ =>
      ψ ((ℓ : ℝ) / T) * unitExp (ℓ * u) * ((c : ℂ) ^ (-wl v) * (((α * ℓ + β : ℝ)) : ℂ) ^ wl v *
        smoothAFEGaussianKernel (wl v))) := by
    intro ℓ hℓ
    refine Integrable.const_mul ?_ _
    have := ZetaNotch.integrable_smoothAFEMellinIntegrand_line one_ne_zero
      (div_pos hc (hrange ℓ hℓ))
    refine this.congr (Eventually.of_forall fun v => ?_)
    simp only [smoothAFEMellinIntegrand, hwl]
    rw [ofReal_div_cpow_neg hc (hrange ℓ hℓ)]
  have hmellin : latticeSum (fun x => ψ (x / T) * smoothAFECutoff (c / (α * x + β))) u =
      (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, (c : ℂ) ^ (-wl v) * smoothAFEGaussianKernel (wl v) *
        latticeSum (cutoffPowerWeight ψ T α β (wl v)) u := by
    rw [hsum]
    have hterm : ∀ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋,
        ψ ((ℓ : ℝ) / T) * smoothAFECutoff (c / (α * ℓ + β)) * unitExp (ℓ * u) =
        (1 / (2 * Real.pi) : ℂ) * ∫ v : ℝ, ψ ((ℓ : ℝ) / T) * unitExp (ℓ * u) *
          ((c : ℂ) ^ (-wl v) * (((α * ℓ + β : ℝ)) : ℂ) ^ wl v * smoothAFEGaussianKernel (wl v)) := by
      intro ℓ hℓ
      rw [smoothAFECutoff_div_eq_integral hc (hrange ℓ hℓ), integral_const_mul]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← integral_finsetSum _ hint]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [latticeSum_eq_sum (support_cutoffPowerWeight hsupp hT α β (wl v)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp only [cutoffPowerWeight]
    ring
  rw [hmellin, norm_mul]
  have hnorm2pi : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnorm2pi]
  -- pointwise bound on the Mellin integrand
  have hpt : ∀ v : ℝ, ‖(c : ℂ) ^ (-wl v) * smoothAFEGaussianKernel (wl v) *
      latticeSum (cutoffPowerWeight ψ T α β (wl v)) u‖ ≤
      (c⁻¹ * ((T + k + 1) * (Ak * (3 * α * T) / T ^ k) / (4 * δ) ^ k)) * bnd v := by
    intro v
    have hre : (wl v).re = 1 := by simp [hwl]
    have hlat := norm_latticeSum_le (k := k) (A := T) (B := 2 * T) (by linarith)
      (contDiff_cutoffPowerWeight hψ hsupp hT hα hβ (wl v) k)
      (support_cutoffPowerWeight hsupp hT α β (wl v))
      (norm_iteratedDeriv_cutoffPowerWeight_le hψ hsupp hΨ hT hα hβ (by rw [hre]; norm_num) k)
      hδ hu
    rw [hre, Real.rpow_one] at hlat
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hc]
    have hcre : (-wl v).re = -1 := by simp [hwl]
    rw [hcre, Real.rpow_neg_one]
    have hlat' : ‖latticeSum (cutoffPowerWeight ψ T α β (wl v)) u‖ ≤
        (T + k + 1) * (Ak * (3 * α * T) / T ^ k) / (4 * δ) ^ k * (‖wl v‖ + k) ^ k := by
      refine hlat.trans (le_of_eq ?_)
      rw [hAk]
      ring
    calc c⁻¹ * ‖smoothAFEGaussianKernel (wl v)‖ * ‖latticeSum (cutoffPowerWeight ψ T α β (wl v)) u‖
        ≤ c⁻¹ * ‖smoothAFEGaussianKernel (wl v)‖ *
            ((T + k + 1) * (Ak * (3 * α * T) / T ^ k) / (4 * δ) ^ k * (‖wl v‖ + k) ^ k) :=
          mul_le_mul_of_nonneg_left hlat' (by positivity)
      _ = (c⁻¹ * ((T + k + 1) * (Ak * (3 * α * T) / T ^ k) / (4 * δ) ^ k)) * bnd v := by
          simp only [hbnd]; ring
  have hI := norm_integral_le_of_norm_le (hbnd_int.const_mul _) (Eventually.of_forall hpt)
  rw [integral_const_mul, ← hIk] at hI
  have hTk : T + k + 1 ≤ (k + 2) * T := by nlinarith
  calc 1 / (2 * Real.pi) * ‖∫ v : ℝ, (c : ℂ) ^ (-wl v) * smoothAFEGaussianKernel (wl v) *
        latticeSum (cutoffPowerWeight ψ T α β (wl v)) u‖
      ≤ 1 / (2 * Real.pi) *
          ((c⁻¹ * ((T + k + 1) * (Ak * (3 * α * T) / T ^ k) / (4 * δ) ^ k)) * Ik) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ ≤ 1 / (2 * Real.pi) *
          ((c⁻¹ * (((k + 2) * T) * (Ak * (3 * α * T) / T ^ k) / (4 * δ) ^ k)) * Ik) := by
        gcongr
    _ = 1 / (2 * Real.pi) * ((k + 2) * (3 * α) * Ak * Ik / 4 ^ k) * T ^ 2 /
          (c * T ^ k * δ ^ k) := by
        field_simp
        ring

end

end RHTower.VerticalAP
