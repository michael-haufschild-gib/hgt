import GaloisForLFunctions.MultiplicativePositivityGeometry.DecayMassLaw

/-!
# Beurling's threshold from the half capacity

A Beurling generalized-prime system with integer count `N(t) = At + R(t)` has zeta function
`ζ_P(s) = s ∫_1^∞ N(t) t^{−s−1} dt = As/(s − 1) + s ∫_0^∞ r(v) e^{−(s−1)v} dv`, where
`r(v) = R(e^v) e^{−v}` is the normalized count error. Writing `s = 1 + w`, the model is
`beurlingZetaModel A r w = A(1 + w)/w + (1 + w) ∫_0^∞ r(v) e^{−wv} dv`.

**Regularity gives decay** (`norm_beurlingZetaModel_sub_le`). If `∫ |r(v)| (1 + v)^θ dv < ∞` for some
`0 ≤ θ ≤ 1`, then near a boundary point `1 + it₀`, `t₀ ≠ 0`,
`|Z(1 + x + it₀) − Z(1 + it₀)| ≤ K x^θ` for `0 < x ≤ 1`, because
`|e^{−xv} − 1| ≤ (xv)^θ`. A count error `|R(t)| ≤ C t (log t)^{−γ}` makes `|r(v)| ≲ (1 + v)^{−γ}`,
which has these moments for every `θ < γ − 1` (`moment_of_power_decay`).

**The threshold** (`beurling_zero_count`, `beurling_no_boundary_zero`). If `log |Z|` has
nonnegative log-coefficients (an Euler product over generalized primes), the decay-exponent mass law
applies with growth exponent `1` at the pole: a set of `n` positive zero heights needs
`n θ₀ ≤ 1/2`. So a count error `O(t/log^γ t)` with `γ > 3/2` leaves no zero on `Re s = 1`, and
`1 < γ ≤ 3/2` leaves at most `1/(2(γ − 1))` zero heights. Beurling's exponent `3/2` is
`1 + 1/2`: one for the Mellin integral, one half for the capacity of a simple pole. The half-zero
datum `ζ(s)/√(ζ(s+i)ζ(s−i))` sits exactly at the capacity.
-/

open Finset Filter Topology Complex MeasureTheory Set

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- The Laplace transform `∫_0^∞ r(v) e^{−wv} dv` of the normalized count error. -/
noncomputable def countLaplace (r : ℝ → ℝ) (w : ℂ) : ℂ :=
  ∫ v in Ioi (0 : ℝ), (r v : ℂ) * cexp (-(w * v))

/-- The Beurling zeta at `s = 1 + w`: `A(1 + w)/w + (1 + w) ∫_0^∞ r(v) e^{−wv} dv`. -/
noncomputable def beurlingZetaModel (A : ℝ) (r : ℝ → ℝ) (w : ℂ) : ℂ :=
  A * (1 + w) / w + (1 + w) * countLaplace r w

/-- `1 − e^{−y} ≤ y^θ` for `y ≥ 0` and `0 ≤ θ ≤ 1`. -/
theorem one_sub_exp_neg_le_rpow {y θ : ℝ} (hy : 0 ≤ y) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    1 - Real.exp (-y) ≤ y ^ θ := by
  have h1 : 1 - Real.exp (-y) ≤ 1 := by linarith [Real.exp_pos (-y)]
  have h2 : 1 - Real.exp (-y) ≤ y := by linarith [Real.add_one_le_exp (-y)]
  rcases le_or_gt y 1 with hy1 | hy1
  · calc 1 - Real.exp (-y) ≤ y := h2
      _ = y ^ (1 : ℝ) := (Real.rpow_one y).symm
      _ ≤ y ^ θ := Real.rpow_le_rpow_of_exponent_ge' hy hy1 hθ0 hθ1
  · exact h1.trans (Real.one_le_rpow hy1.le hθ0)

theorem norm_cexp_neg_mul_le {w : ℂ} (hw : 0 ≤ w.re) {v : ℝ} (hv : 0 ≤ v) :
    ‖cexp (-(w * v))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  refine Real.exp_le_one_iff.mpr ?_
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  nlinarith

theorem integrableOn_countLaplace_integrand {r : ℝ → ℝ} (hr : IntegrableOn r (Ioi 0))
    {w : ℂ} (hw : 0 ≤ w.re) :
    IntegrableOn (fun v : ℝ => (r v : ℂ) * cexp (-(w * v))) (Ioi 0) := by
  refine (hr.ofReal (𝕜 := ℂ)).mul_of_top_left ?_
  refine memLp_top_of_bound (C := 1) ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
    exact norm_cexp_neg_mul_le hw (le_of_lt hv)

/-- The count Laplace transform is bounded on `Re w ≥ 0` by the total mass of `|r|`. -/
theorem norm_countLaplace_le {r : ℝ → ℝ} (hr : IntegrableOn r (Ioi 0)) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖countLaplace r w‖ ≤ ∫ v in Ioi (0 : ℝ), |r v| := by
  unfold countLaplace
  refine norm_integral_le_of_norm_le hr.abs ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (norm_cexp_neg_mul_le hw (le_of_lt hv))

/-- **Regularity of the Laplace transform up to the line.** -/
theorem norm_countLaplace_sub_le {r : ℝ → ℝ} (hr : IntegrableOn r (Ioi 0)) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hmom : IntegrableOn (fun v => |r v| * (1 + v) ^ θ) (Ioi 0))
    {x t₀ : ℝ} (hx : 0 ≤ x) :
    ‖countLaplace r (x + t₀ * I) - countLaplace r (t₀ * I)‖ ≤
      x ^ θ * ∫ v in Ioi (0 : ℝ), |r v| * (1 + v) ^ θ := by
  unfold countLaplace
  rw [← integral_sub (integrableOn_countLaplace_integrand hr (by simpa using hx))
    (integrableOn_countLaplace_integrand hr (by simp)), ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hmom.const_mul _) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
  have hv0 : 0 ≤ v := le_of_lt hv
  have hsplit : (r v : ℂ) * cexp (-((↑x + ↑t₀ * I) * ↑v)) - (r v : ℂ) * cexp (-(↑t₀ * I * ↑v)) =
      (r v : ℂ) * cexp (-(↑t₀ * I * ↑v)) * ((Real.exp (-(x * v)) : ℂ) - 1) := by
    rw [Complex.ofReal_exp]
    push_cast
    rw [show -((↑x + ↑t₀ * I) * (↑v : ℂ)) = -(↑t₀ * I * ↑v) + -(↑x * ↑v) by ring, Complex.exp_add]
    ring
  have hunit : ‖cexp (-(↑t₀ * I * (↑v : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hexp : ‖((Real.exp (-(x * v)) : ℂ) - 1)‖ = 1 - Real.exp (-(x * v)) := by
    rw [show ((Real.exp (-(x * v)) : ℂ) - 1) = ((Real.exp (-(x * v)) - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by
        linarith [Real.exp_le_one_iff.mpr (by nlinarith : -(x * v) ≤ 0)])]
    ring
  rw [hsplit, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hunit, mul_one, hexp]
  have h1 := one_sub_exp_neg_le_rpow (mul_nonneg hx hv0) hθ0 hθ1
  have h2 : (x * v) ^ θ ≤ x ^ θ * (1 + v) ^ θ := by
    rw [Real.mul_rpow hx hv0]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hv0 (by linarith) hθ0)
      (Real.rpow_nonneg hx _)
  calc |r v| * (1 - Real.exp (-(x * v))) ≤ |r v| * (x ^ θ * (1 + v) ^ θ) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg _)
    _ = x ^ θ * (|r v| * (1 + v) ^ θ) := by ring

theorem norm_ofReal_add_mul_I_ge (x t : ℝ) : |t| ≤ ‖(x : ℂ) + t * I‖ := by
  have := Complex.abs_im_le_norm ((x : ℂ) + t * I)
  simpa using this

theorem norm_one_add_le (x t : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ‖(1 : ℂ) + ((x : ℂ) + t * I)‖ ≤ 2 + |t| := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [add_re, one_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, add_im, one_im, mul_im, zero_add]
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- **Regularity gives decay.** Near a boundary point `1 + it₀`, `t₀ ≠ 0`, the model moves by at
most `K x^θ`. -/
theorem norm_beurlingZetaModel_sub_le {A : ℝ} (hA : 0 ≤ A) {r : ℝ → ℝ}
    (hr : IntegrableOn r (Ioi 0)) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hmom : IntegrableOn (fun v => |r v| * (1 + v) ^ θ) (Ioi 0)) {t₀ : ℝ} (ht₀ : t₀ ≠ 0)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ‖beurlingZetaModel A r (x + t₀ * I) - beurlingZetaModel A r (t₀ * I)‖ ≤
      (A / t₀ ^ 2 + (∫ v in Ioi (0 : ℝ), |r v|) +
        (2 + |t₀|) * ∫ v in Ioi (0 : ℝ), |r v| * (1 + v) ^ θ) * x ^ θ := by
  set M₀ := ∫ v in Ioi (0 : ℝ), |r v|
  set Mθ := ∫ v in Ioi (0 : ℝ), |r v| * (1 + v) ^ θ
  set w : ℂ := x + t₀ * I
  set w₀ : ℂ := t₀ * I
  have hw0 : w ≠ 0 := fun h => ht₀ (by simpa [w] using congrArg Complex.im h)
  have hw₀0 : w₀ ≠ 0 := by simp [w₀, ht₀]
  have hnw : |t₀| ≤ ‖w‖ := norm_ofReal_add_mul_I_ge x t₀
  have hnw₀ : ‖w₀‖ = |t₀| := by simp [w₀]
  have ht2 : 0 < t₀ ^ 2 := by positivity
  have hM₀ : 0 ≤ M₀ := setIntegral_nonneg measurableSet_Ioi fun v _ => abs_nonneg _
  have hMθ : 0 ≤ Mθ := setIntegral_nonneg measurableSet_Ioi fun v hv =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by linarith [(mem_Ioi.mp hv)]) _)
  -- The pole part moves by `A x / (|w| |w₀|)`.
  have hpole : ‖A * (1 + w) / w - A * (1 + w₀) / w₀‖ ≤ A / t₀ ^ 2 * x := by
    have e : A * (1 + w) / w - A * (1 + w₀) / w₀ = -(A * x) / (w * w₀) := by
      field_simp
      simp only [w, w₀]
      ring
    rw [e, norm_div, norm_neg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hA, abs_of_pos hx0, hnw₀]
    rw [div_le_iff₀ (by positivity)]
    have : t₀ ^ 2 ≤ ‖w‖ * |t₀| := by
      rw [← sq_abs]; nlinarith [abs_nonneg t₀]
    calc A * x = A / t₀ ^ 2 * x * t₀ ^ 2 := by field_simp
      _ ≤ A / t₀ ^ 2 * x * (‖w‖ * |t₀|) :=
        mul_le_mul_of_nonneg_left this (by positivity)
  -- The Laplace part.
  have hI := norm_countLaplace_le hr (w := w) (by simp [w]; linarith)
  have hΔ := norm_countLaplace_sub_le hr hθ0 hθ1 hmom (t₀ := t₀) hx0.le
  have hlap : ‖(1 + w) * countLaplace r w - (1 + w₀) * countLaplace r w₀‖ ≤
      M₀ * x + (2 + |t₀|) * (x ^ θ * Mθ) := by
    have e : (1 + w) * countLaplace r w - (1 + w₀) * countLaplace r w₀ =
        (x : ℂ) * countLaplace r w + (1 + w₀) * (countLaplace r w - countLaplace r w₀) := by
      simp only [w, w₀]; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, mul_comm]
      exact mul_le_mul_of_nonneg_right hI hx0.le
    · rw [norm_mul]
      have h1w : ‖1 + w₀‖ ≤ 2 + |t₀| := by
        have := norm_one_add_le 0 t₀ le_rfl zero_le_one
        simpa [w₀] using this
      exact mul_le_mul h1w hΔ (norm_nonneg _) (by positivity)
  have hxθ : x ≤ x ^ θ := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ θ := Real.rpow_le_rpow_of_exponent_ge' hx0.le hx1 hθ0 hθ1
  have hsplit : beurlingZetaModel A r w - beurlingZetaModel A r w₀ =
      (A * (1 + w) / w - A * (1 + w₀) / w₀) +
        ((1 + w) * countLaplace r w - (1 + w₀) * countLaplace r w₀) := by
    unfold beurlingZetaModel; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hxθ0 : 0 ≤ x ^ θ := Real.rpow_nonneg hx0.le _
  nlinarith [hpole, hlap, mul_le_mul_of_nonneg_left hxθ (by positivity : (0 : ℝ) ≤ A / t₀ ^ 2),
    mul_le_mul_of_nonneg_left hxθ hM₀]

/-! ### Power decay of the count error gives the moments -/

theorem continuousOn_one_add_rpow (a : ℝ) {s : Set ℝ} (hs : ∀ v ∈ s, 0 ≤ v) :
    ContinuousOn (fun v : ℝ => (1 + v) ^ a) s :=
  (Continuous.continuousOn (by fun_prop : Continuous fun v : ℝ => 1 + v)).rpow_const
    fun v hv => Or.inl (ne_of_gt (by linarith [hs v hv]))

theorem integrableOn_one_add_rpow {a : ℝ} (ha : a < -1) :
    IntegrableOn (fun v : ℝ => (1 + v) ^ a) (Ioi 0) := by
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · exact ((continuousOn_one_add_rpow a fun v hv => hv.1).integrableOn_Icc).mono_set
      Set.Ioc_subset_Icc_self
  · refine (integrableOn_Ioi_rpow_of_lt ha zero_lt_one).mono' ?_ ?_
    · exact (continuousOn_one_add_rpow a fun v hv => le_of_lt (lt_trans zero_lt_one hv)).aestronglyMeasurable
        measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
      have hv1 : 1 < v := hv
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)

/-- **Count regularity gives moments.** If `|r(v)| ≤ C(1 + v)^{−γ}`, then
`∫ |r(v)| (1 + v)^θ dv < ∞` for every `θ < γ − 1`. -/
theorem moment_of_power_decay {r : ℝ → ℝ} (hrm : AEStronglyMeasurable r (volume.restrict (Ioi 0)))
    {C γ : ℝ} (hrb : ∀ v, 0 < v → |r v| ≤ C * (1 + v) ^ (-γ)) {θ : ℝ} (hθ : θ < γ - 1) :
    IntegrableOn (fun v => |r v| * (1 + v) ^ θ) (Ioi 0) := by
  refine ((integrableOn_one_add_rpow (a := θ - γ) (by linarith)).const_mul C).mono' ?_ ?_
  · exact (continuous_abs.comp_aestronglyMeasurable hrm).mul
      ((continuousOn_one_add_rpow θ fun v hv => le_of_lt hv).aestronglyMeasurable
        measurableSet_Ioi)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
    have hv0 : 0 < v := hv
    have h1 : 0 < 1 + v := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg h1.le _))]
    calc |r v| * (1 + v) ^ θ ≤ C * (1 + v) ^ (-γ) * (1 + v) ^ θ :=
          mul_le_mul_of_nonneg_right (hrb v hv0) (Real.rpow_nonneg h1.le _)
      _ = C * (1 + v) ^ (θ - γ) := by
          rw [mul_assoc, ← Real.rpow_add h1]; ring_nf

/-! ### The threshold -/

/-- `log f ≤ (−c + ε) log(1/x)` eventually, from `0 < f x ≤ K x^c`. -/
theorem eventually_log_le_of_le_rpow {f : ℝ → ℝ} {K c : ℝ} (hK : 0 < K)
    (hf : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < f x ∧ f x ≤ K * x ^ c) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), Real.log (f x) ≤ (-c + ε) * -Real.log x := by
  have hL : Tendsto (fun x : ℝ => -Real.log x) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  filter_upwards [hf, hL.eventually (eventually_ge_atTop (Real.log K / ε)),
    self_mem_nhdsWithin] with x hfx hLx hx
  have hx0 : 0 < x := hx
  have h1 : Real.log (f x) ≤ Real.log (K * x ^ c) := Real.log_le_log hfx.1 hfx.2
  rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hx0 c).ne', Real.log_rpow hx0] at h1
  have h2 : Real.log K ≤ ε * -Real.log x := by
    rw [div_le_iff₀ hε] at hLx; linarith
  nlinarith

/-- **Beurling's zero count.** Let `Z(1 + w) = A(1 + w)/w + (1 + w) ∫ r(v) e^{−wv} dv` on
`Re w ≥ 0`, `w ≠ 0`, with `Z ≠ 0` on `Re s > 1` and `u ↦ log |Z(1 + x + iu)|` positive definite
for every `x > 0` (nonnegative log-coefficients). If `∫ |r|(1 + v)^θ < ∞` with `0 ≤ θ ≤ 1`, then
`n` positive zero heights on `Re s = 1` satisfy `n θ ≤ 1/2`. -/
theorem beurling_zero_count {Z : ℂ → ℂ} {A : ℝ} (hA : 0 ≤ A) {r : ℝ → ℝ}
    (hr : IntegrableOn r (Ioi 0)) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hmom : IntegrableOn (fun v => |r v| * (1 + v) ^ θ) (Ioi 0))
    (hZ : ∀ w : ℂ, 0 ≤ w.re → w ≠ 0 → Z (1 + w) = beurlingZetaModel A r w)
    (hne : ∀ x : ℝ, 0 < x → ∀ u : ℝ, Z (1 + (x + u * I)) ≠ 0)
    (hpd : ∀ x : ℝ, 0 < x → IsEvenPosDef fun u : ℝ => Real.log ‖Z (1 + (x + u * I))‖)
    {Zs : Finset ℝ} (hZs : ∀ t ∈ Zs, 0 < t) (hzero : ∀ t ∈ Zs, Z (1 + t * I) = 0) :
    (Zs.card : ℝ) * θ ≤ 1 / 2 := by
  set M₀ := ∫ v in Ioi (0 : ℝ), |r v|
  have hM₀ : 0 ≤ M₀ := setIntegral_nonneg measurableSet_Ioi fun v _ => abs_nonneg _
  have hL : Tendsto (fun x : ℝ => -Real.log x) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hsmall : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x ∧ x ≤ 1 :=
    Filter.eventually_of_mem (Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))
      fun x hx => ⟨hx.1, hx.2⟩
  have hval : ∀ x : ℝ, 0 < x → ∀ u : ℝ, Z (1 + (x + u * I)) = beurlingZetaModel A r (x + u * I) :=
    fun x hx u => hZ _ (by simp [hx.le]) (fun h => by
      have := congrArg Complex.re h; simp at this; linarith)
  -- Bound at height `u` for `0 < x ≤ 1`.
  have hbound : ∀ u : ℝ, u ≠ 0 → ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖Z (1 + (x + u * I))‖ ≤ (A / |u| + M₀) * (2 + |u|) := by
    intro u hu x hx0 hx1
    rw [hval x hx0 u]
    unfold beurlingZetaModel
    have hw : |u| ≤ ‖(x : ℂ) + u * I‖ := norm_ofReal_add_mul_I_ge x u
    have hu0 : 0 < |u| := abs_pos.mpr hu
    have h1w := norm_one_add_le x u hx0.le hx1
    have hI := norm_countLaplace_le hr (w := (x : ℂ) + u * I) (by simp [hx0.le])
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
    have ha : A * ‖1 + ((x : ℂ) + u * I)‖ / ‖(x : ℂ) + u * I‖ ≤ A / |u| * (2 + |u|) := by
      rw [div_le_iff₀ (hu0.trans_le hw)]
      calc A * ‖1 + ((x : ℂ) + u * I)‖ ≤ A * (2 + |u|) := mul_le_mul_of_nonneg_left h1w hA
        _ = A / |u| * (2 + |u|) * |u| := by field_simp
        _ ≤ A / |u| * (2 + |u|) * ‖(x : ℂ) + u * I‖ :=
            mul_le_mul_of_nonneg_left hw (by positivity)
    have hb : ‖1 + ((x : ℂ) + u * I)‖ * ‖countLaplace r ((x : ℂ) + u * I)‖ ≤ (2 + |u|) * M₀ :=
      mul_le_mul h1w hI (norm_nonneg _) (by positivity)
    nlinarith
  -- The pole bound.
  have hpole : ∀ x : ℝ, 0 < x → x ≤ 1 → ‖Z (1 + (x + (0 : ℝ) * I))‖ ≤ (2 * A + 2 * M₀ + 1) * x ^ (-1 : ℝ) := by
    intro x hx0 hx1
    rw [hval x hx0 0, Real.rpow_neg_one]
    unfold beurlingZetaModel
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    have hI := norm_countLaplace_le hr (w := (x : ℂ)) (by simp [hx0.le])
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hA, abs_of_pos hx0]
    have h1x : ‖(1 : ℂ) + x‖ ≤ 2 := by
      rw [show (1 : ℂ) + x = ((1 + x : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    have hxinv : 1 ≤ x⁻¹ := one_le_inv₀ hx0 |>.mpr hx1
    have e1 : A * ‖(1 : ℂ) + x‖ / x ≤ 2 * A * x⁻¹ := by
      rw [div_eq_mul_inv]
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1x hA) (inv_pos.mpr hx0).le
      linarith
    have e2 : ‖(1 : ℂ) + x‖ * ‖countLaplace r x‖ ≤ 2 * M₀ * x⁻¹ := by
      nlinarith [norm_nonneg ((1 : ℂ) + x), norm_nonneg (countLaplace r x)]
    nlinarith [inv_pos.mpr hx0]
  have h0' : ∀ ε > 0, ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      Real.log ‖Z (1 + ((x : ℂ) + ((0 : ℝ) : ℂ) * I))‖ ≤ (1 + ε) * -Real.log x := by
    intro ε hε
    have := eventually_log_le_of_le_rpow (f := fun x : ℝ => ‖Z (1 + ((x : ℂ) + ((0 : ℝ) : ℂ) * I))‖)
      (K := 2 * A + 2 * M₀ + 1) (c := -1) (by positivity)
      ((hsmall).mono fun x hx => ⟨norm_pos_iff.mpr (hne x hx.1 0), hpole x hx.1 hx.2⟩) ε hε
    filter_upwards [this] with x hx
    simpa using hx
  have hoff' : ∀ v : ℝ, v ≠ 0 → ∀ ε > 0, ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      Real.log ‖Z (1 + ((x : ℂ) + (v : ℂ) * I))‖ ≤ ε * -Real.log x := by
    intro v hv ε hε
    have := eventually_log_le_of_le_rpow (f := fun x : ℝ => ‖Z (1 + ((x : ℂ) + (v : ℂ) * I))‖)
      (K := (A / |v| + M₀) * (2 + |v|) + 1) (c := 0) (by positivity)
      ((hsmall).mono fun x hx => ⟨norm_pos_iff.mpr (hne x hx.1 v), by
        rw [Real.rpow_zero, mul_one]; linarith [hbound v hv x hx.1 hx.2]⟩) ε hε
    filter_upwards [this] with x hx
    simpa using hx
  have hz' : ∀ t ∈ Zs, ∀ ε > 0, ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      Real.log ‖Z (1 + ((x : ℂ) + (t : ℂ) * I))‖ ≤ (-θ + ε) * -Real.log x := by
    intro t ht ε hε
    have hzt := hzero t ht
    have ht0 : t ≠ 0 := (hZs t ht).ne'
    have hline : Z (1 + t * I) = beurlingZetaModel A r (t * I) :=
      hZ _ (by simp) (by simp [ht0])
    set K := A / t ^ 2 + M₀ + (2 + |t|) * ∫ v in Ioi (0 : ℝ), |r v| * (1 + v) ^ θ
    have hK0 : 0 ≤ K := by
      have : 0 ≤ ∫ v in Ioi (0 : ℝ), |r v| * (1 + v) ^ θ :=
        setIntegral_nonneg measurableSet_Ioi fun v hv =>
          mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by linarith [mem_Ioi.mp hv]) _)
      positivity
    have := eventually_log_le_of_le_rpow (f := fun x : ℝ => ‖Z (1 + ((x : ℂ) + (t : ℂ) * I))‖)
      (K := K + 1) (c := θ) (by positivity)
      ((hsmall).mono fun x hx => ⟨norm_pos_iff.mpr (hne x hx.1 t), by
        rw [hval x hx.1 t]
        have h := norm_beurlingZetaModel_sub_le hA hr hθ0 hθ1 hmom ht0 hx.1 hx.2
        rw [← hline, hzt, sub_zero] at h
        nlinarith [Real.rpow_nonneg hx.1.le θ]⟩) ε hε
    filter_upwards [this] with x hx
    simpa using hx
  have key := decay_mass_law (T := fun (x u : ℝ) => Real.log ‖Z (1 + ((x : ℂ) + (u : ℂ) * I))‖)
    hpd hL (k := 1)
    h0' hoff' hZs (α := fun _ => θ) (fun _ _ => hθ0) hz'
  simpa [Finset.sum_const, nsmul_eq_mul] using key

end GaloisForLFunctions.MultiplicativePositivityGeometry
