import GaloisForLFunctions.RHTower.SalemFermiModeIntegral
import GaloisForLFunctions.RHTower.ChronologicalBoseDilateCompleteness

/-!
# Stretched Bose defects and their Mellin transforms

For `a > 0` let `f_a(t) = e^{-t^a}`, `I_a = ∫_0^∞ f_a = Γ(1/a + 1)` and

`D_a(t) = I_a / t - Σ_{n ≥ 1} f_a(n t)`        (`t > 0`).

For `a = 1` this is the Bose defect `1/t - 1/(e^t - 1)`.

* `defect_nonneg`, `defect_le_one`, `defect_le_mass_div`: `0 ≤ D_a ≤ min(1, I_a/t)`.  The bounds
  compare the sum with the integral of the decreasing function `x ↦ f_a(xt)`.
* `fermi_eq_two_mul_defect_sub`: `2 D_a(2t) - D_a(t) = Σ_{n ≥ 1} (-1)^{n+1} f_a(n t)`; the `1/t`
  terms cancel.
* `mellin_defect`: `𝓜 D_a(s) = -ζ(s) Γ(s/a)/a` on `0 < Re s < 1`.  The alternating sum has
  Mellin transform `(1 - 2^{1-s}) ζ(s) Γ(s/a)/a` on `Re s > 0`, `s ≠ 1`: the Mellin–Dirichlet
  interchange after `u = t^a` gives it on `Re s > 1`, and holomorphy continues it.  The dyadic
  identity divides out `2^{1-s} - 1`.
-/

open MeasureTheory Set Filter Complex Asymptotics
open scoped Topology

noncomputable section

namespace RHTower.StretchedBose

open GaloisForLFunctions.HTGeometry

/-- `f_a(t) = e^{-t^a}`. -/
def kernel (a t : ℝ) : ℝ := Real.exp (-(t ^ a))

/-- `I_a = Γ(1/a + 1) = ∫_0^∞ e^{-t^a} dt`. -/
def mass (a : ℝ) : ℝ := Real.Gamma (1 / a + 1)

/-- `Σ_{n ≥ 1} f_a(n t)`. -/
def bulk (a t : ℝ) : ℝ := ∑' n : ℕ, kernel a (((n : ℝ) + 1) * t)

/-- The stretched Bose defect `D_a(t) = I_a/t - Σ_{n ≥ 1} f_a(nt)` for `t > 0`, and `0` otherwise. -/
def defect (a t : ℝ) : ℝ := if 0 < t then mass a / t - bulk a t else 0

/-- The alternating sum `Σ_{n ≥ 1} (-1)^{n+1} f_a(nt)`. -/
def fermi (a t : ℝ) : ℝ := ∑' n : ℕ, (-1 : ℝ) ^ n * kernel a (((n : ℝ) + 1) * t)

/-- `F_a(s) = Γ(s/a)/a`, the Mellin transform of `f_a`. -/
def mellinFactor (a : ℝ) (s : ℂ) : ℂ := Complex.Gamma (s / a) / a

variable {a : ℝ}

theorem kernel_pos (a t : ℝ) : 0 < kernel a t := Real.exp_pos _

theorem kernel_le_one {t : ℝ} (ht : 0 ≤ t) : kernel a t ≤ 1 := by
  unfold kernel
  rw [Real.exp_le_one_iff, neg_nonpos]
  exact Real.rpow_nonneg ht a

theorem kernel_antitoneOn (ha : 0 < a) : AntitoneOn (kernel a) (Ici 0) := by
  intro x hx y hy hxy
  unfold kernel
  exact Real.exp_le_exp.mpr (neg_le_neg (Real.rpow_le_rpow hx hxy ha.le))

theorem continuous_kernel (ha : 0 < a) : Continuous (kernel a) := by
  unfold kernel
  exact Real.continuous_exp.comp (continuous_neg.comp (continuous_id.rpow_const fun _ => Or.inr ha.le))

theorem integrableOn_kernel (ha : 0 < a) : IntegrableOn (kernel a) (Ioi 0) := by
  have hsub : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (1 / a - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by positivity)
  have hc := (integrableOn_Ioi_comp_rpow_iff
    (fun u : ℝ => Real.exp (-u) * u ^ (1 / a - 1)) (p := a) ha.ne').mpr hsub
  have hc' : IntegrableOn (fun x : ℝ => a⁻¹ * ((|a| * x ^ (a - 1)) •
      (Real.exp (-x ^ a) * (x ^ a) ^ (1 / a - 1)))) (Ioi 0) := hc.const_mul a⁻¹
  refine IntegrableOn.congr_fun hc' (fun x hx => ?_) measurableSet_Ioi
  have hx0 : 0 < x := hx
  simp only [smul_eq_mul, kernel]
  rw [← Real.rpow_mul hx0.le, show a * (1 / a - 1) = 1 - a by field_simp, abs_of_pos ha,
    Real.rpow_sub hx0, Real.rpow_one, Real.rpow_sub hx0, Real.rpow_one]
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx0 a
  field_simp

theorem integral_kernel (ha : 0 < a) : ∫ x in Ioi (0 : ℝ), kernel a x = mass a := by
  simpa [kernel, mass] using integral_exp_neg_rpow ha

theorem integrableOn_kernel_comp_mul (ha : 0 < a) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x => kernel a (x * t)) (Ioi 0) := by
  rw [integrableOn_Ioi_comp_mul_right_iff _ 0 ht, zero_mul]
  exact integrableOn_kernel ha

theorem integral_kernel_comp_mul (ha : 0 < a) {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), kernel a (x * t) = mass a / t := by
  rw [integral_comp_mul_right_Ioi _ 0 ht, zero_mul, integral_kernel ha, smul_eq_mul]
  field_simp

/-- `Σ_{n < N} f_a((n+1)t) ≤ I_a / t`. -/
theorem sum_kernel_le (ha : 0 < a) {t : ℝ} (ht : 0 < t) (N : ℕ) :
    ∑ n ∈ Finset.range N, kernel a (((n : ℝ) + 1) * t) ≤ mass a / t := by
  have hanti : AntitoneOn (fun x => kernel a (x * t)) (Icc 0 (0 + (N : ℝ))) := by
    intro x hx y hy hxy
    exact kernel_antitoneOn ha (mul_nonneg hx.1 ht.le) (mul_nonneg hy.1 ht.le)
      (mul_le_mul_of_nonneg_right hxy ht.le)
  have h1 := hanti.sum_le_integral
  have hint := integrableOn_kernel_comp_mul ha ht
  have h2 : ∫ x in (0 : ℝ)..0 + (N : ℝ), kernel a (x * t) ≤ ∫ x in Ioi (0 : ℝ), kernel a (x * t) := by
    rw [zero_add, intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
    exact setIntegral_mono_set hint (Eventually.of_forall fun x => (kernel_pos a _).le)
      (Eventually.of_forall Ioc_subset_Ioi_self)
  rw [integral_kernel_comp_mul ha ht] at h2
  refine le_trans (le_of_eq ?_) (h1.trans h2)
  refine Finset.sum_congr rfl fun _ _ => ?_
  push_cast; ring_nf

theorem summable_kernel (ha : 0 < a) {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ => kernel a (((n : ℝ) + 1) * t) :=
  summable_of_sum_range_le (fun _ => (kernel_pos a _).le) (sum_kernel_le ha ht)

theorem bulk_nonneg (a t : ℝ) : 0 ≤ bulk a t :=
  tsum_nonneg fun _ => (kernel_pos a _).le

theorem bulk_le (ha : 0 < a) {t : ℝ} (ht : 0 < t) : bulk a t ≤ mass a / t :=
  (summable_kernel ha ht).tsum_le_of_sum_range_le (sum_kernel_le ha ht)

/-- `Σ_{n ≥ 1} f_a(nt) ≥ I_a/t - 1`. -/
theorem mass_div_sub_one_le_bulk (ha : 0 < a) {t : ℝ} (ht : 0 < t) : mass a / t - 1 ≤ bulk a t := by
  have hint := integrableOn_kernel_comp_mul ha ht
  have hint1 : IntegrableOn (fun x => kernel a (x * t)) (Ioi 1) := hint.mono_set (Ioi_subset_Ioi zero_le_one)
  -- `∫_1^{1+N} ≤` partial sums `≤ bulk`
  have hstep : ∀ N : ℕ, ∫ x in (1 : ℝ)..1 + (N : ℝ), kernel a (x * t) ≤ bulk a t := by
    intro N
    have hanti : AntitoneOn (fun x => kernel a (x * t)) (Icc 1 (1 + (N : ℝ))) := by
      intro x hx y hy hxy
      exact kernel_antitoneOn ha (mul_nonneg (by linarith [hx.1]) ht.le)
        (mul_nonneg (by linarith [hy.1]) ht.le) (mul_le_mul_of_nonneg_right hxy ht.le)
    refine hanti.integral_le_sum.trans ?_
    refine le_trans (le_of_eq ?_) ((summable_kernel ha ht).sum_le_tsum (Finset.range N)
      (fun n _ => (kernel_pos a _).le))
    refine Finset.sum_congr rfl fun _ _ => ?_
    ring_nf
  have hlim := intervalIntegral_tendsto_integral_Ioi (f := fun x => kernel a (x * t)) 1 hint1
    (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hIoi : ∫ x in Ioi (1 : ℝ), kernel a (x * t) ≤ bulk a t :=
    le_of_tendsto' hlim hstep
  -- `∫_{Ioi 1} = I/t - ∫_0^1 ≥ I/t - 1`
  have hsplit : ∫ x in Ioi (0 : ℝ), kernel a (x * t) =
      (∫ x in (0 : ℝ)..1, kernel a (x * t)) + ∫ x in Ioi (1 : ℝ), kernel a (x * t) := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hint.mono_set Ioc_subset_Ioi_self) hint1, Ioc_union_Ioi_eq_Ioi zero_le_one]
  have h01 : ∫ x in (0 : ℝ)..1, kernel a (x * t) ≤ 1 := by
    have := intervalIntegral.integral_mono_on zero_le_one
      (((continuous_kernel ha).comp (continuous_id.mul continuous_const)).intervalIntegrable
        (μ := volume) 0 1)
      (intervalIntegrable_const (μ := volume) (c := (1 : ℝ)))
      (fun x hx => kernel_le_one (mul_nonneg hx.1 ht.le))
    simpa using this
  rw [integral_kernel_comp_mul ha ht] at hsplit
  linarith

theorem defect_of_pos {t : ℝ} (ht : 0 < t) : defect a t = mass a / t - bulk a t := by
  simp [defect, ht]

theorem defect_of_nonpos {t : ℝ} (ht : t ≤ 0) : defect a t = 0 := by
  simp [defect, not_lt.mpr ht]

theorem defect_nonneg (ha : 0 < a) (t : ℝ) : 0 ≤ defect a t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [defect_of_nonpos ht]
  · rw [defect_of_pos ht]; linarith [bulk_le ha ht]

theorem defect_le_one (ha : 0 < a) (t : ℝ) : defect a t ≤ 1 := by
  rcases le_or_gt t 0 with ht | ht
  · rw [defect_of_nonpos ht]; norm_num
  · rw [defect_of_pos ht]; linarith [mass_div_sub_one_le_bulk ha ht]

theorem defect_le_mass_div {t : ℝ} (ht : 0 < t) : defect a t ≤ mass a / t := by
  rw [defect_of_pos ht]; linarith [bulk_nonneg a t]

theorem mass_pos (ha : 0 < a) : 0 < mass a := Real.Gamma_pos_of_pos (by positivity)


theorem continuousOn_bulk (ha : 0 < a) : ContinuousOn (bulk a) (Ioi 0) := by
  intro t₀ ht₀
  have ht₀' : (0 : ℝ) < t₀ := ht₀
  have hδ : (0 : ℝ) < t₀ / 2 := by linarith
  have hcont : ContinuousOn (bulk a) (Ioi (t₀ / 2)) := by
    refine continuousOn_tsum (u := fun n : ℕ => kernel a (((n : ℝ) + 1) * (t₀ / 2)))
      (fun n => ?_) (summable_kernel ha hδ) (fun n t ht => ?_)
    · exact ((continuous_kernel ha).comp (continuous_const.mul continuous_id)).continuousOn
    · rw [Real.norm_eq_abs, abs_of_pos (kernel_pos a _)]
      have ht' : t₀ / 2 < t := ht
      have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      exact kernel_antitoneOn ha (show (0 : ℝ) ≤ ((n : ℝ) + 1) * (t₀ / 2) by positivity)
        (show (0 : ℝ) ≤ ((n : ℝ) + 1) * t by nlinarith)
        (mul_le_mul_of_nonneg_left ht'.le hn)
  exact (hcont.continuousAt (Ioi_mem_nhds (by linarith : t₀ / 2 < t₀))).continuousWithinAt

theorem continuousOn_defect (ha : 0 < a) : ContinuousOn (defect a) (Ioi 0) := by
  have hc : ContinuousOn (fun t : ℝ => mass a / t - bulk a t) (Ioi 0) :=
    (continuousOn_const.div continuousOn_id fun t ht => ne_of_gt ht).sub (continuousOn_bulk ha)
  exact hc.congr fun t ht => defect_of_pos ht

theorem fermi_eq_bulk_sub (ha : 0 < a) {t : ℝ} (ht : 0 < t) :
    fermi a t = bulk a t - 2 * bulk a (2 * t) := by
  set g : ℕ → ℝ := fun n => kernel a (((n : ℝ) + 1) * t) with hg
  have hgs : Summable g := summable_kernel ha ht
  set h : ℕ → ℝ := fun n => (-1 : ℝ) ^ n * g n with hh
  have hhs : Summable h := by
    refine Summable.of_norm_bounded hgs fun n => ?_
    simp [hh, abs_of_pos (kernel_pos a _), hg]
  have he : Summable fun k => h (2 * k) := hhs.comp_injective fun x y hxy => by omega
  have ho : Summable fun k => h (2 * k + 1) := hhs.comp_injective fun x y hxy => by omega
  have hge : Summable fun k => g (2 * k) := hgs.comp_injective fun x y hxy => by omega
  have hgo : Summable fun k => g (2 * k + 1) := hgs.comp_injective fun x y hxy => by omega
  have h1 := tsum_even_add_odd he ho
  have h2 := tsum_even_add_odd hge hgo
  have hev : ∀ k : ℕ, h (2 * k) = g (2 * k) := fun k => by simp [hh, pow_mul]
  have hod : ∀ k : ℕ, h (2 * k + 1) = -g (2 * k + 1) := fun k => by simp [hh, pow_succ, pow_mul]
  have hodd : ∑' k : ℕ, g (2 * k + 1) = bulk a (2 * t) := by
    unfold bulk
    refine tsum_congr fun k => ?_
    simp only [hg]
    congr 1
    push_cast; ring
  have hfermi : fermi a t = ∑' n, h n := rfl
  have hbulk : bulk a t = ∑' n, g n := rfl
  rw [hfermi, hbulk, ← h1, ← h2, tsum_congr hev, tsum_congr hod, tsum_neg, hodd]
  ring

theorem fermi_eq_two_mul_defect_sub (ha : 0 < a) {t : ℝ} (ht : 0 < t) :
    fermi a t = 2 * defect a (2 * t) - defect a t := by
  rw [fermi_eq_bulk_sub ha ht, defect_of_pos ht, defect_of_pos (by positivity : (0 : ℝ) < 2 * t)]
  field_simp
  ring

theorem bulk_le_exp_mul_kernel (ha : 0 < a) {t : ℝ} (ht : 1 ≤ t) :
    bulk a t ≤ Real.exp 1 * bulk a 1 * kernel a t := by
  have hterm : ∀ n : ℕ, kernel a (((n : ℝ) + 1) * t) ≤
      Real.exp 1 * kernel a (((n : ℝ) + 1) * 1) * kernel a t := by
    intro n
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    unfold kernel
    simp only [mul_one]
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp,
      Real.mul_rpow (by positivity) (by linarith)]
    have h1 : 1 ≤ ((n : ℝ) + 1) ^ a := Real.one_le_rpow hn ha.le
    have h2 : 1 ≤ t ^ a := Real.one_le_rpow ht ha.le
    nlinarith
  calc bulk a t ≤ ∑' n : ℕ, Real.exp 1 * kernel a (((n : ℝ) + 1) * 1) * kernel a t :=
        Summable.tsum_le_tsum hterm (summable_kernel ha (by linarith))
          (((summable_kernel ha one_pos).mul_left _).mul_right _)
    _ = Real.exp 1 * bulk a 1 * kernel a t := by
        rw [tsum_mul_right, tsum_mul_left]; rfl

theorem kernel_isBigO_rpow (ha : 0 < a) (A : ℝ) :
    kernel a =O[atTop] fun t : ℝ => t ^ (-A) := by
  have h1 : Tendsto (fun t : ℝ => (t ^ a) ^ (A / a) * Real.exp (-1 * t ^ a)) atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / a) 1 one_pos).comp (tendsto_rpow_atTop ha)
  have h2 : Tendsto (fun t : ℝ => t ^ A * kernel a t) atTop (𝓝 0) := by
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [kernel]
    rw [← Real.rpow_mul ht.le, mul_div_cancel₀ _ ha.ne', neg_one_mul]
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [h2.eventually (Iio_mem_nhds one_pos), eventually_gt_atTop 0] with t ht ht0
  have hA : 0 < t ^ A := Real.rpow_pos_of_pos ht0 A
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (kernel_pos a t),
    abs_of_pos (Real.rpow_pos_of_pos ht0 _), one_mul, Real.rpow_neg ht0.le]
  rw [← one_div, le_div_iff₀ hA]
  linarith [ht]

theorem abs_fermi_le (ha : 0 < a) {t : ℝ} (ht : 0 < t) : |fermi a t| ≤ 3 := by
  rw [fermi_eq_two_mul_defect_sub ha ht]
  have h1 := defect_nonneg ha (2 * t)
  have h2 := defect_le_one ha (2 * t)
  have h3 := defect_nonneg ha t
  have h4 := defect_le_one ha t
  rw [abs_le]; constructor <;> linarith

theorem abs_fermi_le_kernel (ha : 0 < a) {t : ℝ} (ht : 1 ≤ t) :
    |fermi a t| ≤ 3 * (Real.exp 1 * bulk a 1) * kernel a t := by
  rw [fermi_eq_bulk_sub ha (by linarith)]
  have hb1 := bulk_le_exp_mul_kernel ha ht
  have hb2 := bulk_le_exp_mul_kernel ha (show (1 : ℝ) ≤ 2 * t by linarith)
  have hk : kernel a (2 * t) ≤ kernel a t :=
    kernel_antitoneOn ha (show (0 : ℝ) ≤ t by linarith) (show (0 : ℝ) ≤ 2 * t by linarith)
      (by linarith)
  have hn1 := bulk_nonneg a t
  have hn2 := bulk_nonneg a (2 * t)
  have hc : 0 ≤ Real.exp 1 * bulk a 1 := by positivity [bulk_nonneg a 1]
  have hb2' : bulk a (2 * t) ≤ Real.exp 1 * bulk a 1 * kernel a t :=
    hb2.trans (mul_le_mul_of_nonneg_left hk hc)
  rw [abs_le]; constructor <;> nlinarith [kernel_pos a t]

theorem continuousOn_fermi (ha : 0 < a) : ContinuousOn (fermi a) (Ioi 0) := by
  have hc : ContinuousOn (fun t => 2 * defect a (2 * t) - defect a t) (Ioi 0) := by
    refine ((continuousOn_const.mul ((continuousOn_defect ha).comp
      (continuousOn_const.mul continuousOn_id) fun t ht => ?_)).sub (continuousOn_defect ha))
    show (0 : ℝ) < 2 * t
    have : (0 : ℝ) < t := ht
    linarith
  exact hc.congr fun t ht => fermi_eq_two_mul_defect_sub ha ht


/-! ## Mellin transforms -/

/-- `((n+1)^a)^{s/a} = (n+1)^s` as complex powers. -/
theorem ofReal_rpow_cpow_div {x : ℝ} (hx : 0 < x) (ha : 0 < a) (s : ℂ) :
    (((x ^ a : ℝ) : ℂ)) ^ (s / (a : ℂ)) = (x : ℂ) ^ s := by
  rw [Complex.ofReal_cpow hx.le, ← Complex.cpow_mul]
  · congr 1; exact mul_div_cancel₀ s (Complex.ofReal_ne_zero.mpr ha.ne')
  · rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_mul, Complex.ofReal_im]
    linarith [Real.pi_pos]
  · rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_mul, Complex.ofReal_im]
    exact Real.pi_pos.le

theorem mellin_kernel (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t => (kernel a t : ℂ)) s = mellinFactor a s := by
  have h := mellin_comp_rpow (fun u : ℝ => ((Real.exp (-u) : ℝ) : ℂ)) s a
  have he : (fun t => (kernel a t : ℂ)) = fun t => ((Real.exp (-(t ^ a)) : ℝ) : ℂ) := rfl
  rw [he, h, ← Complex.GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral
    (by rw [Complex.div_ofReal_re]; positivity), abs_of_pos ha, mellinFactor, Complex.real_smul]
  push_cast
  field_simp

theorem mellin_fermi_of_one_lt_re (ha : 0 < a) {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t => (fermi a t : ℂ)) s = mellinFactor a s * etaPair s := by
  set G : ℝ → ℂ := fun u =>
    ((∑' n : ℕ, (-1 : ℝ) ^ n * Real.exp (-(((n : ℝ) + 1) ^ a) * u) : ℝ) : ℂ) with hG
  have hcongr : mellin (fun t => (fermi a t : ℂ)) s = mellin (fun t => G (t ^ a)) s := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    refine congrArg (fun z : ℂ => (t : ℂ) ^ (s - 1) • z) ?_
    simp only [hG, fermi, kernel]
    congr 1
    refine tsum_congr fun n => ?_
    rw [Real.mul_rpow (by positivity) ht0.le]; ring_nf
  have hs0 : 0 < s.re := by linarith
  have hw : 0 < (s / (a : ℂ)).re := by rw [Complex.div_ofReal_re]; positivity
  have hsumw : Summable fun n : ℕ => ‖(-1 : ℂ) ^ n‖ / (((n : ℝ) + 1) ^ a) ^ (s / (a : ℂ)).re := by
    have h := (Real.summable_one_div_nat_add_rpow 1 s.re).mpr hs
    refine h.congr fun n => ?_
    rw [norm_pow, norm_neg, norm_one, one_pow, Complex.div_ofReal_re,
      ← Real.rpow_mul (by positivity), mul_div_cancel₀ _ ha.ne',
      abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
  have hHas := hasSum_mellin (a := fun n : ℕ => (-1 : ℂ) ^ n)
    (p := fun n : ℕ => ((n : ℝ) + 1) ^ a) (F := G) (s := s / (a : ℂ))
    (fun n => Or.inr (by positivity)) hw (fun u hu => ?_) hsumw
  · rw [hcongr, mellin_comp_rpow, abs_of_pos ha, ← hHas.tsum_eq, Complex.real_smul,
      ← tsum_salemAlternating_eq_etaPair hs, mellinFactor, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [ofReal_rpow_cpow_div (by positivity : (0 : ℝ) < (n : ℝ) + 1) ha]
    push_cast
    field_simp
  · have hu0 : (0 : ℝ) < u := hu
    have hsr : Summable fun n : ℕ => (-1 : ℝ) ^ n * Real.exp (-(((n : ℝ) + 1) ^ a) * u) := by
      have hk := summable_kernel ha (Real.rpow_pos_of_pos hu0 (1 / a))
      refine Summable.of_norm_bounded hk fun n => ?_
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), kernel, Real.mul_rpow (by positivity)
        (Real.rpow_nonneg hu0.le _), ← Real.rpow_mul hu0.le, one_div_mul_cancel ha.ne',
        Real.rpow_one, neg_mul]
    have := (hsr.hasSum).map Complex.ofRealHom Complex.continuous_ofReal
    simpa [hG, Function.comp_def, neg_mul] using this

theorem locallyIntegrableOn_fermi (ha : 0 < a) :
    LocallyIntegrableOn (fun t => (fermi a t : ℂ)) (Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn (continuousOn_fermi ha)).locallyIntegrableOn
    measurableSet_Ioi

theorem fermi_isBigO_rpow (ha : 0 < a) (A : ℝ) :
    (fun t => (fermi a t : ℂ)) =O[atTop] fun t : ℝ => t ^ (-A) := by
  have hk := kernel_isBigO_rpow ha A
  have hb : (fun t => (fermi a t : ℂ)) =O[atTop] kernel a := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨3 * (Real.exp 1 * bulk a 1), ?_⟩
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (kernel_pos a t)]
    exact abs_fermi_le_kernel ha ht
  exact hb.trans hk

theorem fermi_isBigO_one (ha : 0 < a) :
    (fun t => (fermi a t : ℂ)) =O[𝓝[>] 0] fun t : ℝ => t ^ (-(0 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨3, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Complex.norm_real, Real.norm_eq_abs, neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact abs_fermi_le ha ht

theorem analyticOnNhd_mellin_fermi (ha : 0 < a) :
    AnalyticOnNhd ℂ (mellin fun t => (fermi a t : ℂ)) {s : ℂ | 0 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  exact (mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0)
    (locallyIntegrableOn_fermi ha) (fermi_isBigO_rpow ha _) (by linarith)
    (fermi_isBigO_one ha) hs).differentiableWithinAt

theorem analyticAt_mellinFactor (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (mellinFactor a) s := by
  have hG : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (z / a)) s :=
    (HTGeometry.analyticAt_Gamma_of_re_pos (by rw [Complex.div_ofReal_re]; positivity)).comp
      ((analyticAt_id).div analyticAt_const (by exact_mod_cast ha.ne'))
  exact hG.div analyticAt_const (by exact_mod_cast ha.ne')

theorem mellin_fermi (ha : 0 < a) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    mellin (fun t => (fermi a t : ℂ)) s =
      mellinFactor a s * ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
  let U : Set ℂ := {z : ℂ | 0 < z.re} \ {1}
  let H : ℂ → ℂ := fun z => mellinFactor a z * ((1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z)
  have hleft : AnalyticOnNhd ℂ (mellin fun t => (fermi a t : ℂ)) U :=
    (analyticOnNhd_mellin_fermi ha).mono Set.sdiff_subset
  have hright : AnalyticOnNhd ℂ H U := by
    intro z hz
    have hdyadic : AnalyticAt ℂ (fun w : ℂ => 1 - (2 : ℂ) ^ (1 - w)) z := by
      have hd : Differentiable ℂ (fun w : ℂ => 1 - (2 : ℂ) ^ (1 - w)) := by
        apply Differentiable.sub (differentiable_const _)
        exact Differentiable.const_cpow
          ((differentiable_const 1).sub differentiable_id) (Or.inl two_ne_zero)
      exact (hd.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)
    have hzeta : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z (by simpa using hz.2)
    exact (analyticAt_mellinFactor ha hz.1).mul (hdyadic.mul hzeta)
  have htwo : (2 : ℂ) ∈ U := ⟨by norm_num, by simp⟩
  have hevent : (mellin fun t => (fermi a t : ℂ)) =ᶠ[𝓝 (2 : ℂ)] H := by
    have hgt : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hgt] with z hz
    have hz1 : z ≠ 1 := by intro h; subst h; norm_num at hz
    rw [mellin_fermi_of_one_lt_re ha hz, etaPair_eq z (by linarith) hz1]
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright isPreconnected_halfplane_punctured
    htwo hevent ⟨hs0, by simpa using hs1⟩


theorem locallyIntegrableOn_defect (ha : 0 < a) :
    LocallyIntegrableOn (fun t => (defect a t : ℂ)) (Ioi 0) :=
  (Complex.continuous_ofReal.comp_continuousOn (continuousOn_defect ha)).locallyIntegrableOn
    measurableSet_Ioi

theorem defect_isBigO_inv (ha : 0 < a) :
    (fun t => (defect a t : ℂ)) =O[atTop] fun t : ℝ => t ^ (-(1 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨mass a, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (defect_nonneg ha t), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht _), Real.rpow_neg_one, ← div_eq_mul_inv]
  exact defect_le_mass_div ht

theorem defect_isBigO_one (ha : 0 < a) :
    (fun t => (defect a t : ℂ)) =O[𝓝[>] 0] fun t : ℝ => t ^ (-(0 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (defect_nonneg ha t), neg_zero,
    Real.rpow_zero, norm_one, mul_one]
  exact defect_le_one ha t

theorem mellinConvergent_defect (ha : 0 < a) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (fun t => (defect a t : ℂ)) s :=
  mellinConvergent_of_isBigO_rpow (locallyIntegrableOn_defect ha) (defect_isBigO_inv ha) hs1
    (defect_isBigO_one ha) hs0

/-- **The Mellin transform of the stretched Bose defect:** `𝓜 D_a(s) = -ζ(s) Γ(s/a)/a`
on `0 < Re s < 1`. -/
theorem mellin_defect (ha : 0 < a) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun t => (defect a t : ℂ)) s = -(mellinFactor a s * riemannZeta s) := by
  have hc := mellinConvergent_defect ha hs0 hs1
  have hc2 : MellinConvergent (fun t => (defect a (2 * t) : ℂ)) s :=
    (MellinConvergent.comp_mul_left (by positivity : (0 : ℝ) < 2)).mpr hc
  have hsub := (hasMellin_sub (hc2.const_smul (2 : ℂ)) hc).2
  have hleft : mellin (fun t => (2 : ℂ) • (defect a (2 * t) : ℂ) - (defect a t : ℂ)) s =
      mellin (fun t => (fermi a t : ℂ)) s := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    refine congrArg (fun z : ℂ => (t : ℂ) ^ (s - 1) • z) ?_
    show (2 : ℂ) • ((defect a (2 * t) : ℝ) : ℂ) - ((defect a t : ℝ) : ℂ) = ((fermi a t : ℝ) : ℂ)
    rw [fermi_eq_two_mul_defect_sub ha ht, smul_eq_mul]
    push_cast; ring
  have hs1' : s ≠ 1 := by intro h; rw [h, Complex.one_re] at hs1; exact lt_irrefl _ hs1
  rw [hleft, mellin_const_smul, mellin_comp_mul_left (fun t => (defect a t : ℂ)) s
    (by positivity : (0 : ℝ) < 2), mellin_fermi ha hs0 hs1'] at hsub
  have hpow : (2 : ℂ) * ((2 : ℝ) : ℂ) ^ (-s) = (2 : ℂ) ^ (1 - s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]; push_cast; ring
  have hcoef : 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := by
    intro h
    have h' : (2 : ℂ) ^ (1 - s) = 1 := (sub_eq_zero.mp h).symm
    have hn := congrArg norm h'
    rw [norm_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)] at hn
    have hre : 0 < (1 - s).re := by simp; linarith
    have : (1 : ℝ) < 2 ^ (1 - s).re := Real.one_lt_rpow (by norm_num) hre
    linarith
  simp only [smul_eq_mul] at hsub
  have hprod : (1 - (2 : ℂ) ^ (1 - s)) * mellin (fun t => (defect a t : ℂ)) s =
      (1 - (2 : ℂ) ^ (1 - s)) * -(mellinFactor a s * riemannZeta s) := by
    rw [← hpow] at hsub ⊢
    linear_combination hsub
  exact mul_left_cancel₀ hcoef hprod

/-- `t ↦ D_a(kt)`, complex valued. -/
def defectDilate (a : ℝ) (k : ℕ) (t : ℝ) : ℂ := (defect a ((k : ℝ) * t) : ℂ)

theorem mellin_defectDilate (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) :
    mellin (defectDilate a k) s = -((k : ℂ) ^ (-s) * mellinFactor a s * riemannZeta s) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := mellin_comp_mul_left (fun t => (defect a t : ℂ)) s hk0
  have he : defectDilate a k = fun t => (defect a ((k : ℝ) * t) : ℂ) := rfl
  rw [he, h, mellin_defect ha hs0 hs1, smul_eq_mul]
  push_cast
  ring


/-! ## `L²` vectors and their images under the Mellin unitary -/

theorem defect_sq_le (ha : 0 < a) (t : ℝ) : defect a t ^ 2 ≤ (1 + mass a ^ 2) * (1 + t ^ 2)⁻¹ := by
  have h0 := defect_nonneg ha t
  have h1 := defect_le_one ha t
  have h2 : defect a t * |t| ≤ mass a := by
    rcases le_or_gt t 0 with ht | ht
    · rw [defect_of_nonpos ht, zero_mul]; exact (mass_pos ha).le
    · rw [abs_of_pos ht]; exact (le_div_iff₀ ht).mp (defect_le_mass_div ht)
  have hn : 0 ≤ defect a t * |t| := mul_nonneg h0 (abs_nonneg t)
  have hsq : (defect a t * |t|) ^ 2 ≤ mass a ^ 2 := pow_le_pow_left₀ hn h2 2
  rw [mul_pow, sq_abs] at hsq
  rw [le_mul_inv_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)]
  nlinarith

theorem memLp_defect (ha : 0 < a) : MemLp (defect a) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hm : AEStronglyMeasurable (defect a) (volume.restrict (Ioi (0 : ℝ))) :=
    (continuousOn_defect ha).aestronglyMeasurable measurableSet_Ioi
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (integrable_inv_one_add_sq.const_mul (1 + mass a ^ 2)).integrableOn.mono' (hm.pow 2)
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact defect_sq_le ha t

theorem memLp_defectDilate (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) :
    MemLp (defectDilate a k) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (RHTower.chronological_memLp_dilate (memLp_defect ha) (continuousOn_defect ha)
    (d := (k : ℝ)) (by exact_mod_cast hk)).ofReal

/-- `D_a((k+1)·)` as a vector of `L²((0,∞))`. -/
def defectDilateL2 (ha : 0 < a) (k : ℕ) : HalfLineL2 :=
  (memLp_defectDilate ha (Nat.le_add_left 1 k)).toLp (defectDilate a (k + 1))

theorem memLp_kernel (ha : 0 < a) :
    MemLp (fun t => (kernel a t : ℂ)) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hm : AEStronglyMeasurable (kernel a) (volume.restrict (Ioi (0 : ℝ))) :=
    (continuous_kernel ha).aestronglyMeasurable
  refine MemLp.ofReal ?_
  apply (memLp_two_iff_integrable_sq hm).mpr
  refine (integrableOn_kernel ha).mono' (hm.pow 2) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
  exact mul_le_of_le_one_left (kernel_pos a t).le (kernel_le_one ht0)

/-- `f_a` as a vector of `L²((0,∞))`. -/
def kernelL2 (ha : 0 < a) : HalfLineL2 := (memLp_kernel ha).toLp fun t => (kernel a t : ℂ)

theorem norm_halfDensityPullback_defectDilate_le (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    ‖halfDensityPullback (defectDilate a k) x‖ ≤
      (1 + mass a) * Real.exp (-(1 / 2 * |x|)) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0 : ℝ) < (k : ℝ) * Real.exp x := mul_pos (by linarith) (Real.exp_pos x)
  have h0 := defect_nonneg ha ((k : ℝ) * Real.exp x)
  have h1 := defect_le_one ha ((k : ℝ) * Real.exp x)
  have h2 := defect_le_mass_div (a := a) hpos
  have hm := mass_pos ha
  have hsq : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; ring_nf
  unfold halfDensityPullback defectDilate
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg h0, hsq]
  rcases le_total x 0 with hx | hx
  · rw [abs_of_nonpos hx]
    calc Real.exp (x / 2) * defect a ((k : ℝ) * Real.exp x)
        ≤ Real.exp (x / 2) * (1 + mass a) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = (1 + mass a) * Real.exp (-(1 / 2 * -x)) := by ring_nf
  · rw [abs_of_nonneg hx]
    have hkx : Real.exp x ≤ (k : ℝ) * Real.exp x := by nlinarith [Real.exp_pos x]
    calc Real.exp (x / 2) * defect a ((k : ℝ) * Real.exp x)
        ≤ Real.exp (x / 2) * (mass a / ((k : ℝ) * Real.exp x)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ ≤ Real.exp (x / 2) * (mass a / Real.exp x) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hm.le (Real.exp_pos x) hkx)
            (Real.exp_pos _).le
      _ = mass a * Real.exp (-(1 / 2 * x)) := by
          rw [mul_div_assoc', mul_comm (Real.exp (x / 2)) (mass a), mul_div_assoc,
            ← Real.exp_sub]
          ring_nf
      _ ≤ (1 + mass a) * Real.exp (-(1 / 2 * x)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

theorem integrable_exp_neg_half_abs : Integrable fun x : ℝ => Real.exp (-(1 / 2 * |x|)) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 8)
    (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2 * |x|)
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hpos : 0 < 1 + x ^ 2 := by positivity
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  rw [show 8 * (1 + x ^ 2)⁻¹ * Real.exp (1 / 2 * |x|) =
    8 * Real.exp (1 / 2 * |x|) / (1 + x ^ 2) by field_simp]
  rw [le_div_iff₀ hpos]
  nlinarith [abs_nonneg x]

theorem integrable_halfDensityPullback_defectDilate (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (halfDensityPullback (defectDilate a k)) := by
  have hcont : Continuous (halfDensityPullback (defectDilate a k)) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hin : Continuous fun x : ℝ => defect a ((k : ℝ) * Real.exp x) := by
      rw [continuous_iff_continuousAt]
      intro x
      have hpos : (0 : ℝ) < (k : ℝ) * Real.exp x := mul_pos hk0 (Real.exp_pos x)
      exact ContinuousAt.comp (f := fun y : ℝ => (k : ℝ) * Real.exp y)
        ((continuousOn_defect ha).continuousAt (Ioi_mem_nhds hpos))
        (continuous_const.mul Real.continuous_exp).continuousAt
    unfold halfDensityPullback defectDilate
    exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp Real.continuous_exp)).mul
      (Complex.continuous_ofReal.comp hin)
  exact (integrable_exp_neg_half_abs.const_mul (1 + mass a)).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall (norm_halfDensityPullback_defectDilate_le ha hk))

theorem kernel_le_exp_neg (ha : 0 < a) (x : ℝ) :
    kernel a (Real.exp x) ≤ Real.exp (1 / (2 * a ^ 2)) * Real.exp (-x) := by
  rcases le_total x 0 with hx | hx
  · calc kernel a (Real.exp x) ≤ 1 := kernel_le_one (Real.exp_pos x).le
      _ ≤ Real.exp (1 / (2 * a ^ 2)) * Real.exp (-x) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by have : 0 ≤ 1 / (2 * a ^ 2) := by positivity
                                    linarith)
  · unfold kernel
    rw [← Real.exp_add, Real.exp_le_exp, ← Real.exp_mul]
    have hax : 0 ≤ x * a := mul_nonneg hx ha.le
    have h1 : (x * a) ^ 2 / 2 ≤ Real.exp (x * a) := by
      have := Real.quadratic_le_exp_of_nonneg hax; nlinarith
    have h2 : x - (x * a) ^ 2 / 2 ≤ 1 / (2 * a ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (a ^ 2 * x - 1)]
    linarith

theorem integrable_halfDensityPullback_kernel (ha : 0 < a) :
    Integrable (halfDensityPullback fun t => (kernel a t : ℂ)) := by
  have hcont : Continuous (halfDensityPullback fun t => (kernel a t : ℂ)) := by
    unfold halfDensityPullback
    exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp Real.continuous_exp)).mul
      (Complex.continuous_ofReal.comp ((continuous_kernel ha).comp Real.continuous_exp))
  refine (integrable_exp_neg_half_abs.const_mul (Real.exp (1 / (2 * a ^ 2)))).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hsq : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; ring_nf
  unfold halfDensityPullback
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (kernel_pos a _), hsq]
  have hC : 1 ≤ Real.exp (1 / (2 * a ^ 2)) := Real.one_le_exp (by positivity)
  rcases le_total x 0 with hx | hx
  · rw [abs_of_nonpos hx]
    calc Real.exp (x / 2) * kernel a (Real.exp x) ≤ Real.exp (x / 2) * 1 :=
          mul_le_mul_of_nonneg_left (kernel_le_one (Real.exp_pos x).le) (Real.exp_pos _).le
      _ = 1 * Real.exp (-(1 / 2 * -x)) := by ring_nf
      _ ≤ Real.exp (1 / (2 * a ^ 2)) * Real.exp (-(1 / 2 * -x)) :=
          mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
  · rw [abs_of_nonneg hx]
    calc Real.exp (x / 2) * kernel a (Real.exp x)
        ≤ Real.exp (x / 2) * (Real.exp (1 / (2 * a ^ 2)) * Real.exp (-x)) :=
          mul_le_mul_of_nonneg_left (kernel_le_exp_neg ha x) (Real.exp_pos _).le
      _ = Real.exp (1 / (2 * a ^ 2)) * Real.exp (-(1 / 2 * x)) := by
          rw [mul_left_comm, ← Real.exp_add]; ring_nf

theorem halfLineMellinUnitary_defectDilateL2 (ha : 0 < a) (k : ℕ) :
    (halfLineMellinUnitary (defectDilateL2 ha k) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => -(((k + 1 : ℕ) : ℂ) ^ (-mellinLinePoint ξ) *
        mellinFactor a (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)) := by
  have hk : 1 ≤ k + 1 := Nat.le_add_left 1 k
  have h := halfLineMellinUnitary_ae_eq_mellin (defectDilateL2 ha k) (defectDilate a (k + 1))
    (MemLp.coeFn_toLp _) (integrable_halfDensityPullback_defectDilate ha hk)
  filter_upwards [h] with ξ hξ
  rw [hξ]
  exact mellin_defectDilate ha hk (s := mellinLinePoint ξ) (by rw [mellinLinePoint_re]; norm_num)
    (by rw [mellinLinePoint_re]; norm_num)

theorem halfLineMellinUnitary_kernelL2 (ha : 0 < a) :
    (halfLineMellinUnitary (kernelL2 ha) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => mellinFactor a (mellinLinePoint ξ) := by
  have h := halfLineMellinUnitary_ae_eq_mellin (kernelL2 ha) (fun t => (kernel a t : ℂ))
    (MemLp.coeFn_toLp _) (integrable_halfDensityPullback_kernel ha)
  filter_upwards [h] with ξ hξ
  rw [hξ]
  exact mellin_kernel ha (s := mellinLinePoint ξ) (by rw [mellinLinePoint_re]; norm_num)


end RHTower.StretchedBose
