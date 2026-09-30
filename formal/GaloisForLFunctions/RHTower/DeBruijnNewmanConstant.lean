import GaloisForLFunctions.RHTower.DeBruijnNewmanHalfBound

/-!
# The de Bruijn–Newman constant on the nonnegative heat axis

Let `H_t(z) = ∫ Φ(x) e^{t x²} e^{izx} dx` (`riemannHeat`) and let `S` be the set of heat times
`t ≥ 0` at which every zero of `H_t` is real. Put `Λ₊ = inf S` (`newmanConstant`).

* `S` is an upper set: real zeros stay real along the flow (the strip contraction with width `0`).
* `S` is closed: the transforms depend locally uniformly on `t`, and the Hurwitz closed-locus
  transfer keeps the zeros on the real axis in the limit.
* Hence `S = [Λ₊, ∞)` (`mem_realRootedTimes_iff`), and `Λ₊ ≤ 1/8` (de Bruijn,
  `newmanConstant_le`).
* The Riemann hypothesis is `Λ₊ = 0` (`riemannHypothesis_iff_newmanConstant_eq_zero`).

All statements are unconditional. `Λ₊` is the classical constant `Λ` truncated at `0` and
rescaled: in Newman's normalization the heat time is `4t`, so `Λ₊ ≤ 1/8` is `Λ ≤ 1/2`.
Rodgers–Tao (`Λ ≥ 0`) is not used and not formalized here.
-/

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower.DeBruijn

noncomputable section

/-- Heat times `t ≥ 0` at which all zeros of `H_t` are real. -/
def realRootedTimes : Set ℝ := {t | 0 ≤ t ∧ ∀ z, riemannHeat t z = 0 → z.im = 0}

/-- The de Bruijn–Newman constant restricted to the nonnegative heat axis. -/
def newmanConstant : ℝ := sInf realRootedTimes

theorem riemannHeat_kernel (t : ℝ) (ht : 0 ≤ t) :
    SuperExpKernel (fun x => riemannKernelReal x * Real.exp (t * x ^ 2)) :=
  riemannKernel_superExp.mul_exp_sq ht

theorem eighth_mem_realRootedTimes {t : ℝ} (ht : 1 / 8 ≤ t) : t ∈ realRootedTimes :=
  ⟨by linarith, fun _ hz => riemannHeat_zeros_real ht hz⟩

theorem realRootedTimes_nonempty : realRootedTimes.Nonempty := ⟨1 / 8, eighth_mem_realRootedTimes le_rfl⟩

theorem realRootedTimes_bddBelow : BddBelow realRootedTimes := ⟨0, fun _ ht => ht.1⟩

/-- **Real zeros persist along the flow.** -/
theorem realRootedTimes_upper {s t : ℝ} (hs : s ∈ realRootedTimes) (hst : s ≤ t) :
    t ∈ realRootedTimes := by
  refine ⟨le_trans hs.1 hst, fun z hz => ?_⟩
  rcases hst.eq_or_lt with heq | hlt
  · subst heq; exact hs.2 z hz
  have hk := riemannHeat_kernel s hs.1
  have hzeros : ∀ w, cosTransform (fun x => riemannKernelReal x * Real.exp (s * x ^ 2)) w = 0 →
      w.im ^ 2 ≤ 0 := fun w hw => by
    rw [hs.2 w hw]; norm_num
  have hfun : (fun x => riemannKernelReal x * Real.exp (s * x ^ 2) * Real.exp ((t - s) * x ^ 2)) =
      fun x => riemannKernelReal x * Real.exp (t * x ^ 2) := by
    funext x
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  have h := cosTransform_heat_zeros_real hk hzeros (by linarith) (sub_pos.mpr hlt) z
  rw [hfun] at h
  exact h hz

theorem newmanConstant_nonneg : 0 ≤ newmanConstant :=
  le_csInf realRootedTimes_nonempty fun _ ht => ht.1

/-- **de Bruijn's bound.** -/
theorem newmanConstant_le : newmanConstant ≤ 1 / 8 :=
  csInf_le realRootedTimes_bddBelow (eighth_mem_realRootedTimes le_rfl)

/-- The heat transforms depend locally uniformly on the heat time from the right. -/
theorem tendstoLocallyUniformly_riemannHeat {t : ℝ} (ht : 0 ≤ t) :
    TendstoLocallyUniformly (fun n : ℕ => riemannHeat (t + 1 / (n + 1)))
      (riemannHeat t) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  set R' := max R 0
  have hdom := (riemannHeat_kernel (t + 1) (by linarith)).integrable_mul_exp R'
  set Φ := riemannKernelReal
  have hΦ := riemannKernel_superExp
  set ε : ℕ → ℝ := fun n =>
    ∫ x, (Φ x * Real.exp ((t + 1 / (n + 1)) * x ^ 2) - Φ x * Real.exp (t * x ^ 2)) *
      Real.exp (R' * |x|)
  have hmono : ∀ (n : ℕ) (x : ℝ), Φ x * Real.exp (t * x ^ 2) ≤
      Φ x * Real.exp ((t + 1 / (n + 1)) * x ^ 2) ∧
      Φ x * Real.exp ((t + 1 / (n + 1)) * x ^ 2) ≤ Φ x * Real.exp ((t + 1) * x ^ 2) := by
    intro n x
    have hn : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    constructor
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x]))
        (hΦ.nonneg x)
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x]))
        (hΦ.nonneg x)
  have hε : Tendsto ε atTop (𝓝 0) := by
    have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun x =>
        (Φ x * Real.exp ((t + 1 / (n + 1)) * x ^ 2) - Φ x * Real.exp (t * x ^ 2)) *
          Real.exp (R' * |x|)) volume := fun n =>
      (((riemannHeat_kernel _ (by positivity)).continuous.sub
        (riemannHeat_kernel t ht).continuous).mul (by fun_prop)).aestronglyMeasurable
    have hle : ∀ n : ℕ, ∀ᵐ x ∂volume, ‖(Φ x * Real.exp ((t + 1 / (n + 1)) * x ^ 2) -
        Φ x * Real.exp (t * x ^ 2)) * Real.exp (R' * |x|)‖ ≤
          Φ x * Real.exp ((t + 1) * x ^ 2) * Real.exp (R' * |x|) :=
      fun n => Eventually.of_forall fun x => by
        obtain ⟨h1, h2⟩ := hmono n x
        have h0 : 0 ≤ Φ x * Real.exp (t * x ^ 2) := mul_nonneg (hΦ.nonneg x) (Real.exp_pos _).le
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr h1) (Real.exp_pos _).le)]
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    have hlim : ∀ᵐ x ∂volume, Tendsto (fun n : ℕ => (Φ x * Real.exp ((t + 1 / (n + 1)) * x ^ 2) -
        Φ x * Real.exp (t * x ^ 2)) * Real.exp (R' * |x|)) atTop (𝓝 0) :=
      Eventually.of_forall fun x => by
        have h1 : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) atTop (𝓝 (t + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        rw [add_zero] at h1
        have h2 : Tendsto (fun n : ℕ => Φ x * Real.exp ((t + 1 / ((n : ℝ) + 1)) * x ^ 2)) atTop
            (𝓝 (Φ x * Real.exp (t * x ^ 2))) :=
          ((Real.continuous_exp.tendsto _).comp (h1.mul_const _)).const_mul _
        have h3 := (h2.sub_const (Φ x * Real.exp (t * x ^ 2))).mul_const (Real.exp (R' * |x|))
        simpa using h3
    have := tendsto_integral_of_dominated_convergence
      (F := fun (n : ℕ) x => (Φ x * Real.exp ((t + 1 / (n + 1)) * x ^ 2) -
        Φ x * Real.exp (t * x ^ 2)) * Real.exp (R' * |x|)) (f := fun _ => (0 : ℝ))
      (fun x => Φ x * Real.exp ((t + 1) * x ^ 2) * Real.exp (R' * |x|)) hmeas hdom hle hlim
    rw [integral_zero] at this
    exact this
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  filter_upwards [hε.eventually (gt_mem_nhds hδ)] with n hn z hz
  have hzR : |z.im| ≤ R' := (Complex.abs_im_le_norm z).trans ((hR z hz).trans (le_max_left _ _))
  have hkn := riemannHeat_kernel (t + 1 / (n + 1)) (by positivity)
  have hkt := riemannHeat_kernel t ht
  rw [dist_eq_norm]
  unfold riemannHeat cosTransform
  rw [← integral_sub (hkt.integrable z) (hkn.integrable z)]
  refine lt_of_le_of_lt ((norm_integral_le_integral_norm _).trans ?_) hn
  have hint : Integrable (fun x => (Φ x * Real.exp ((t + 1 / (n + 1)) * x ^ 2) -
      Φ x * Real.exp (t * x ^ 2)) * Real.exp (R' * |x|)) :=
    ((hkn.integrable_mul_exp R').sub (hkt.integrable_mul_exp R')).congr
      (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hint ?_
  refine Eventually.of_forall fun x => ?_
  beta_reduce
  obtain ⟨h1, -⟩ := hmono n x
  rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h1)]
  refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr h1)
  apply Real.exp_le_exp.mpr
  have : (I * z * x).re = -(z.im * x) := by simp [Complex.mul_re]
  rw [this]
  calc -(z.im * x) ≤ |z.im| * |x| := by rw [← abs_mul]; exact neg_le_abs _
    _ ≤ R' * |x| := mul_le_mul_of_nonneg_right hzR (abs_nonneg x)

/-- **Closedness from the right.** -/
theorem mem_realRootedTimes_of_forall_gt {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ n : ℕ, t + 1 / ((n : ℝ) + 1) ∈ realRootedTimes) : t ∈ realRootedTimes := by
  refine ⟨ht, fun z hz => ?_⟩
  have hk := riemannHeat_kernel t ht
  have hS : IsClosed {v : ℂ | v.im = 0} := isClosed_eq Complex.continuous_im continuous_const
  have hmem := GaloisForLFunctions.HTGeometry.zero_mem_closed_of_tendstoLocallyUniformly
    (tendstoLocallyUniformly_riemannHeat ht)
    (hk.differentiable.differentiableOn.analyticOnNhd isOpen_univ)
    (Eventually.of_forall fun n => (riemannHeat_kernel _ (by positivity)).differentiable) hS
    (Eventually.of_forall fun n v hv => (h n).2 v hv) hk.cosTransform_zero_ne hz
  exact hmem

/-- **The real-rootedness set is `[Λ₊, ∞)`.** -/
theorem mem_realRootedTimes_iff {t : ℝ} (ht : 0 ≤ t) :
    t ∈ realRootedTimes ↔ newmanConstant ≤ t := by
  constructor
  · intro h; exact csInf_le realRootedTimes_bddBelow h
  · intro hle
    -- every `t + 1/(n+1)` exceeds the infimum, hence lies in the set
    have hgt : ∀ n : ℕ, t + 1 / ((n : ℝ) + 1) ∈ realRootedTimes := by
      intro n
      have hlt : newmanConstant < t + 1 / ((n : ℝ) + 1) := by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      obtain ⟨s, hs, hslt⟩ := exists_lt_of_csInf_lt realRootedTimes_nonempty hlt
      exact realRootedTimes_upper hs hslt.le
    exact mem_realRootedTimes_of_forall_gt ht hgt

/-- **The Riemann hypothesis is `Λ₊ = 0`.** -/
theorem riemannHypothesis_iff_newmanConstant_eq_zero :
    RiemannHypothesis ↔ newmanConstant = 0 := by
  rw [riemannHypothesis_iff_riemannHeat_zero_real]
  constructor
  · intro h
    exact le_antisymm (csInf_le realRootedTimes_bddBelow ⟨le_rfl, h⟩) newmanConstant_nonneg
  · intro h
    have hmem := (mem_realRootedTimes_iff le_rfl).mpr h.le
    exact hmem.2

end

end RHTower.DeBruijn
