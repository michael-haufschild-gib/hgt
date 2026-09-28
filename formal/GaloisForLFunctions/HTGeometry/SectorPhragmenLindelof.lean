import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Liouville

/-!
# Phragmén–Lindelöf in sectors, and a Liouville criterion from rays

Through `w ↦ e^w`, a sector `|arg z| < α < π/2` becomes the strip `|Im w| < α`, where mathlib's
strip principle applies to entire functions of order-one growth since `1 < π/(2α)`. Damping by
`e^{-ηz}` turns ray bounds `A e^{η r cos α}` into sector bounds `A e^{η Re z}`; on the positive
real axis these feed the right half-plane principle, and letting `η → 0` bounds the function by
its supremum on the imaginary axis. Together with the same data for `z ↦ f(-z)`, Liouville's
theorem makes `f` constant.
-/

open Complex Filter Topology Set Asymptotics

namespace HTGeometry

noncomputable section

/-- The order-one weight is dominated by any power `max(1, r)^{1+ε}`. -/
theorem orderOne_le_rpow {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) {r : ℝ} (hr : 0 ≤ r) :
    K * (1 + r) * Real.log (2 + r) ≤ K * 3 ^ (1 + ε) / ε * max 1 r ^ (1 + ε) := by
  have h1 : Real.log (2 + r) ≤ (2 + r) ^ ε / ε := Real.log_le_rpow_div (by linarith) hε
  have h2 : (1 + r) * (2 + r) ^ ε ≤ (2 + r) ^ (1 + ε) := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h3 : (2 + r) ^ (1 + ε) ≤ (3 * max 1 r) ^ (1 + ε) :=
    Real.rpow_le_rpow (by linarith) (by linarith [le_max_left 1 r, le_max_right 1 r])
      (by linarith)
  rw [Real.mul_rpow (by norm_num) (by positivity)] at h3
  calc K * (1 + r) * Real.log (2 + r) ≤ K * (1 + r) * ((2 + r) ^ ε / ε) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = K / ε * ((1 + r) * (2 + r) ^ ε) := by ring
    _ ≤ K / ε * (2 + r) ^ (1 + ε) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ K / ε * (3 ^ (1 + ε) * max 1 r ^ (1 + ε)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

theorem max_one_exp_rpow_le (x c : ℝ) (hc : 0 ≤ c) :
    max 1 (Real.exp x) ^ c ≤ Real.exp (c * |x|) := by
  have h : max 1 (Real.exp x) ≤ Real.exp |x| :=
    max_le (Real.one_le_exp (abs_nonneg x)) (Real.exp_le_exp.mpr (le_abs_self x))
  calc max 1 (Real.exp x) ^ c ≤ Real.exp |x| ^ c :=
        Real.rpow_le_rpow (by positivity) h hc
    _ = Real.exp (c * |x|) := by rw [← Real.exp_mul, mul_comm]

/-- **Phragmén–Lindelöf in a sector of opening `2α < π`.** An entire function of order-one growth
that is bounded by `C` on the two rays `arg z = ±α` is bounded by `C` on the closed sector. -/
theorem norm_le_of_sector {f : ℂ → ℂ} (hf : Differentiable ℂ f) {α K C : ℝ} (hα0 : 0 < α)
    (hα : α < Real.pi / 2) (hK : 0 ≤ K)
    (hgrowth : ∀ z, ‖f z‖ ≤ Real.exp (K * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hup : ∀ r : ℝ, 0 ≤ r → ‖f (r * cexp (α * I))‖ ≤ C)
    (hdown : ∀ r : ℝ, 0 ≤ r → ‖f (r * cexp (-α * I))‖ ≤ C)
    {z : ℂ} (hz : |z.arg| ≤ α) : ‖f z‖ ≤ C := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simpa using hup 0 le_rfl
  have hg : Differentiable ℂ (fun w => f (cexp w)) := hf.comp differentiable_exp
  have hπα : 1 < Real.pi / (α - -α) := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  set ε := (Real.pi / (α - -α) - 1) / 2 with hεdef
  have hε : 0 < ε := by linarith
  have hc : 1 + ε < Real.pi / (α - -α) := by linarith
  have hray : ∀ w : ℂ, cexp w = (Real.exp w.re : ℂ) * cexp (w.im * I) := by
    intro w
    conv_lhs => rw [← Complex.re_add_im w]
    rw [Complex.exp_add, ← Complex.ofReal_exp]
  have key := PhragmenLindelof.horizontal_strip (f := fun w => f (cexp w)) (a := -α) (b := α)
    (C := C) (z := Complex.log z) hg.diffContOnCl
    ⟨1 + ε, hc, K * 3 ^ (1 + ε) / ε, ?_⟩ ?_ ?_ ?_ ?_
  · simpa [Complex.exp_log hz0] using key
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun w => ?_)
    rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    refine (hgrowth _).trans (Real.exp_le_exp.mpr ?_)
    rw [Complex.norm_exp]
    refine (orderOne_le_rpow hK hε (Real.exp_pos _).le).trans ?_
    exact mul_le_mul_of_nonneg_left (max_one_exp_rpow_le _ _ (by linarith)) (by positivity)
  · intro w hw
    have := hdown (Real.exp w.re) (Real.exp_pos _).le
    rwa [hray w, hw, show ((-α : ℝ) : ℂ) = -(α : ℂ) by push_cast; ring]
  · intro w hw
    have := hup (Real.exp w.re) (Real.exp_pos _).le
    rwa [hray w, hw]
  · rw [Complex.log_im]; linarith [(abs_le.mp hz).1]
  · rw [Complex.log_im]; linarith [(abs_le.mp hz).2]

theorem norm_mul_exp_neg (f : ℂ → ℂ) (η : ℝ) (z : ℂ) :
    ‖f z * cexp (-(η : ℂ) * z)‖ = ‖f z‖ * Real.exp (-η * z.re) := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

theorem orderOne_add_linear_le {K η : ℝ} (hη : 0 ≤ η) (z : ℂ) :
    K * (1 + ‖z‖) * Real.log (2 + ‖z‖) + η * ‖z‖ ≤
      (K + η / Real.log 2) * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log (2 + ‖z‖) := Real.log_le_log (by norm_num) (by linarith [norm_nonneg z])
  have h : η * ‖z‖ ≤ η / Real.log 2 * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hl2]
    have h1 : ‖z‖ * Real.log 2 ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
      mul_le_mul (by linarith) hl hl2.le (by linarith [norm_nonneg z])
    nlinarith [mul_le_mul_of_nonneg_left h1 hη]
  nlinarith

/-- **Damped sector bound.** If `‖f(r e^{±iα})‖ ≤ A e^{η r cos α}` on both rays, then
`‖f z‖ ≤ A e^{η Re z}` throughout the sector `|arg z| ≤ α`. -/
theorem norm_le_mul_exp_of_sector {f : ℂ → ℂ} (hf : Differentiable ℂ f) {α K A η : ℝ}
    (hα0 : 0 < α) (hα : α < Real.pi / 2) (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hgrowth : ∀ z, ‖f z‖ ≤ Real.exp (K * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hup : ∀ r : ℝ, 0 ≤ r → ‖f (r * cexp (α * I))‖ ≤ A * Real.exp (η * r * Real.cos α))
    (hdown : ∀ r : ℝ, 0 ≤ r → ‖f (r * cexp (-α * I))‖ ≤ A * Real.exp (η * r * Real.cos α))
    {z : ℂ} (hz : |z.arg| ≤ α) : ‖f z‖ ≤ A * Real.exp (η * z.re) := by
  have hre : ∀ r : ℝ, ∀ β : ℝ, ((r : ℂ) * cexp (β * I)).re = r * Real.cos β := by
    intro r β
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hK' : 0 ≤ K + η / Real.log 2 := add_nonneg hK (div_nonneg hη (Real.log_pos (by norm_num)).le)
  have hgr : ∀ z, ‖f z * cexp (-(η : ℂ) * z)‖ ≤
      Real.exp ((K + η / Real.log 2) * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
    intro z
    rw [norm_mul_exp_neg]
    have h1 : Real.exp (-η * z.re) ≤ Real.exp (η * ‖z‖) := by
      refine Real.exp_le_exp.mpr ?_
      have := Complex.abs_re_le_norm z
      nlinarith [abs_le.mp this, neg_abs_le z.re]
    calc ‖f z‖ * Real.exp (-η * z.re) ≤ Real.exp (K * (1 + ‖z‖) * Real.log (2 + ‖z‖)) *
          Real.exp (η * ‖z‖) := mul_le_mul (hgrowth z) h1 (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (K * (1 + ‖z‖) * Real.log (2 + ‖z‖) + η * ‖z‖) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (orderOne_add_linear_le hη z)
  have hray : ∀ r : ℝ, ∀ β : ℝ, Real.cos β = Real.cos α →
      ‖f (r * cexp (β * I))‖ ≤ A * Real.exp (η * r * Real.cos α) →
      ‖f (r * cexp (β * I)) * cexp (-(η : ℂ) * (r * cexp (β * I)))‖ ≤ A := by
    intro r β hβ h
    rw [norm_mul_exp_neg, hre, hβ]
    calc ‖f (r * cexp (β * I))‖ * Real.exp (-η * (r * Real.cos α)) ≤
          A * Real.exp (η * r * Real.cos α) * Real.exp (-η * (r * Real.cos α)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = A := by rw [mul_assoc, ← Real.exp_add]; ring_nf; simp
  have h := norm_le_of_sector (f := fun z => f z * cexp (-(η : ℂ) * z))
    (hf.mul (differentiable_exp.comp (differentiable_id.const_mul _))) hα0 hα hK' (C := A) hgr
    (fun r hr => hray r α rfl (hup r hr))
    (fun r hr => by
      have := hray r (-α) (Real.cos_neg α) (by simpa using hdown r hr)
      simpa using this) hz
  rw [norm_mul_exp_neg] at h
  have hpos := Real.exp_pos (-η * z.re)
  calc ‖f z‖ = ‖f z‖ * Real.exp (-η * z.re) * Real.exp (η * z.re) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf; simp
    _ ≤ A * Real.exp (η * z.re) := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- **Phragmén–Lindelöf in the right half-plane from sector rays.** An entire function of
order-one growth, bounded by `C` on the imaginary axis, whose rays `arg z = ±α` satisfy
`‖f(r e^{±iα})‖ ≤ A e^{η r cos α}` for arbitrarily small `η > 0` (with `α, A` depending on `η`), is
bounded by `C` on the closed right half-plane. -/
theorem norm_le_of_imag_of_rays {f : ℂ → ℂ} (hf : Differentiable ℂ f) {K C : ℝ} (hK : 0 ≤ K)
    (hgrowth : ∀ z, ‖f z‖ ≤ Real.exp (K * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (him : ∀ y : ℝ, ‖f (y * I)‖ ≤ C)
    (hrays : ∀ η > 0, ∃ α ∈ Ioo 0 (Real.pi / 2), ∃ A : ℝ, ∀ r : ℝ, 0 ≤ r →
      ‖f (r * cexp (α * I))‖ ≤ A * Real.exp (η * r * Real.cos α) ∧
        ‖f (r * cexp (-α * I))‖ ≤ A * Real.exp (η * r * Real.cos α))
    {z : ℂ} (hz : 0 ≤ z.re) : ‖f z‖ ≤ C := by
  have key : ∀ η > 0, ‖f z‖ ≤ C * Real.exp (2 * η * z.re) := by
    intro η hη
    obtain ⟨α, ⟨hα0, hα⟩, A, hA⟩ := hrays η hη
    have hreal : ∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ A * Real.exp (η * x) := by
      intro x hx
      have := norm_le_mul_exp_of_sector hf hα0 hα hK hη.le hgrowth (fun r hr => (hA r hr).1)
        (fun r hr => (hA r hr).2) (z := (x : ℂ)) (by rw [Complex.arg_ofReal_of_nonneg hx, abs_zero]; exact hα0.le)
      simpa using this
    set K' := K + 2 * η / Real.log 2
    have hK' : 0 ≤ K' := add_nonneg hK (div_nonneg (by linarith) (Real.log_pos (by norm_num)).le)
    have hgr : ∀ w, ‖f w * cexp (-((2 * η : ℝ) : ℂ) * w)‖ ≤
        Real.exp (K' * (1 + ‖w‖) * Real.log (2 + ‖w‖)) := by
      intro w
      rw [norm_mul_exp_neg]
      have h1 : Real.exp (-(2 * η) * w.re) ≤ Real.exp (2 * η * ‖w‖) := by
        refine Real.exp_le_exp.mpr ?_
        have := Complex.abs_re_le_norm w
        nlinarith [abs_le.mp this, neg_abs_le w.re]
      calc ‖f w‖ * Real.exp (-(2 * η) * w.re) ≤ Real.exp (K * (1 + ‖w‖) * Real.log (2 + ‖w‖)) *
            Real.exp (2 * η * ‖w‖) := mul_le_mul (hgrowth w) h1 (Real.exp_pos _).le (Real.exp_pos _).le
        _ = Real.exp (K * (1 + ‖w‖) * Real.log (2 + ‖w‖) + 2 * η * ‖w‖) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (orderOne_add_linear_le (by linarith) w)
    have hPL := PhragmenLindelof.right_half_plane_of_bounded_on_real
      (f := fun w => f w * cexp (-((2 * η : ℝ) : ℂ) * w)) (C := C) (z := z)
      ((hf.mul (differentiable_exp.comp (differentiable_id.const_mul _))).diffContOnCl) ?_ ?_ ?_ hz
    · rw [norm_mul_exp_neg] at hPL
      calc ‖f z‖ = ‖f z‖ * Real.exp (-(2 * η) * z.re) * Real.exp (2 * η * z.re) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf; simp
        _ ≤ C * Real.exp (2 * η * z.re) := mul_le_mul_of_nonneg_right hPL (Real.exp_pos _).le
    · refine ⟨3 / 2, by norm_num, K' * 3 ^ (1 + (1 / 2 : ℝ)) / (1 / 2), ?_⟩
      refine IsBigO.of_bound 1 ?_
      have hev : ∀ᶠ w in Bornology.cobounded ℂ ⊓ 𝓟 {w : ℂ | 0 < w.re}, 1 ≤ ‖w‖ :=
        ((tendsto_norm_cobounded_atTop).eventually (eventually_ge_atTop 1)).filter_mono inf_le_left
      filter_upwards [hev] with w hw
      rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      refine (hgr w).trans (Real.exp_le_exp.mpr ?_)
      have := orderOne_le_rpow hK' (by norm_num : (0 : ℝ) < 1 / 2) (norm_nonneg w)
      rw [max_eq_right hw] at this
      norm_num at this ⊢
      exact this
    · refine isBoundedUnder_of_eventually_le (a := A) ?_
      filter_upwards [eventually_ge_atTop 0] with x hx
      rw [norm_mul_exp_neg, Complex.ofReal_re]
      calc ‖f x‖ * Real.exp (-(2 * η) * x) ≤ A * Real.exp (η * x) * Real.exp (-(2 * η) * x) :=
            mul_le_mul_of_nonneg_right (hreal x hx) (Real.exp_pos _).le
        _ = A * Real.exp (-(η * x)) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
        _ ≤ A := by
            have hA0 : 0 ≤ A := (norm_nonneg _).trans ((hA 0 le_rfl).1.trans (by simp))
            exact mul_le_of_le_one_right hA0 (Real.exp_le_one_iff.mpr (by nlinarith))
    · intro y
      rw [norm_mul_exp_neg]
      simpa using him y
  have hlim : Tendsto (fun η : ℝ => C * Real.exp (2 * η * z.re)) (𝓝[>] 0) (𝓝 C) := by
    have : Tendsto (fun η : ℝ => C * Real.exp (2 * η * z.re)) (𝓝 0) (𝓝 (C * Real.exp (2 * 0 * z.re))) :=
      (continuous_const.mul (Real.continuous_exp.comp (by fun_prop))).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun η hη => key η hη)

/-- **Liouville from the imaginary axis and four sector rays.** If `f` and `z ↦ f (-z)` both satisfy
the hypotheses of `norm_le_of_imag_of_rays`, then `f` is constant. -/
theorem eq_const_of_imag_of_rays {f : ℂ → ℂ} (hf : Differentiable ℂ f) {K C : ℝ} (hK : 0 ≤ K)
    (hgrowth : ∀ z, ‖f z‖ ≤ Real.exp (K * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (him : ∀ y : ℝ, ‖f (y * I)‖ ≤ C)
    (hrays : ∀ η > 0, ∃ α ∈ Ioo 0 (Real.pi / 2), ∃ A : ℝ, ∀ r : ℝ, 0 ≤ r →
      ‖f (r * cexp (α * I))‖ ≤ A * Real.exp (η * r * Real.cos α) ∧
        ‖f (r * cexp (-α * I))‖ ≤ A * Real.exp (η * r * Real.cos α) ∧
        ‖f (-(r * cexp (α * I)))‖ ≤ A * Real.exp (η * r * Real.cos α) ∧
        ‖f (-(r * cexp (-α * I)))‖ ≤ A * Real.exp (η * r * Real.cos α)) (z : ℂ) :
    f z = f 0 := by
  have hbound : ∀ w, ‖f w‖ ≤ C := by
    intro w
    rcases le_total 0 w.re with h | h
    · exact norm_le_of_imag_of_rays hf hK hgrowth him (fun η hη => by
        obtain ⟨α, hα, A, hA⟩ := hrays η hη
        exact ⟨α, hα, A, fun r hr => ⟨(hA r hr).1, (hA r hr).2.1⟩⟩) h
    · have := norm_le_of_imag_of_rays (f := fun w => f (-w)) (hf.comp differentiable_neg) hK
        (fun w => by simpa using hgrowth (-w)) (fun y => by
          have := him (-y); simpa [neg_mul] using this)
        (fun η hη => by
          obtain ⟨α, hα, A, hA⟩ := hrays η hη
          exact ⟨α, hα, A, fun r hr => ⟨(hA r hr).2.2.1, (hA r hr).2.2.2⟩⟩)
        (z := -w) (by simp; linarith)
      simpa using this
  refine Differentiable.apply_eq_apply_of_bounded hf ?_ z 0
  rw [Metric.isBounded_iff_subset_closedBall 0]
  exact ⟨C, by rintro _ ⟨w, rfl⟩; simpa using hbound w⟩

end

end HTGeometry
