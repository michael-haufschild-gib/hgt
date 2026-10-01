import GaloisForLFunctions.HTGeometry.DecayingStripVerticalShift
import GaloisForLFunctions.HTGeometry.MellinLinePlancherel

/-!
# Mellin-regular functions on a vertical strip

`MellinRegularStrip Ψ α β`: holomorphic on `α < Re s < β`, with decay faster than every power of
`|Im s|` uniformly on closed substrips. For such `Ψ`:

* on every line inside the strip, `t ↦ Ψ(c+it)` is continuous, integrable and square integrable;
* `Mellin⁻¹_c Ψ` does not depend on `c ∈ (α, β)` (vertical contour shift);
* `s ↦ s Ψ(s)` is again regular;
* `d/dx Mellin⁻¹_c Ψ (x) = x⁻¹ Mellin⁻¹_c (-s Ψ)(x)` for `c ≠ 0` (differentiation under the
  integral with a local dominating function).

With Mellin–Plancherel these give the weighted `L²` norms of `Mellin⁻¹ Ψ` and of its derivative
as line integrals of `Ψ`.
-/

open Complex MeasureTheory Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- `Ψ` is holomorphic on the open strip `α < Re s < β` and decays faster than every power of
`|Im s|`, uniformly on closed substrips. -/
structure MellinRegularStrip (Ψ : ℂ → ℂ) (α β : ℝ) : Prop where
  diff : ∀ s : ℂ, α < s.re → s.re < β → DifferentiableAt ℂ Ψ s
  decay : ∀ a b : ℝ, α < a → b < β → ∀ K : ℕ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
    ‖Ψ s‖ ≤ C / (1 + s.im ^ 2) ^ K

namespace MellinRegularStrip

variable {Ψ : ℂ → ℂ} {α β : ℝ}

/-- On a line inside the strip, `t ↦ Ψ(c + it)` is continuous. -/
theorem continuous_line (hΨ : MellinRegularStrip Ψ α β) {c : ℝ} (hc : α < c) (hc' : c < β) :
    Continuous fun t : ℝ => Ψ ((c : ℂ) + t * I) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hΨ.diff _ (by simpa using hc) (by simpa using hc')).continuousAt.comp (by fun_prop)

/-- On a line inside the strip, `|Ψ(c + it)| ≤ C (1 + t²)^{-K}` for every `K`. -/
theorem line_bound (hΨ : MellinRegularStrip Ψ α β) {c : ℝ} (hc : α < c) (hc' : c < β) (K : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, ‖Ψ ((c : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2) ^ K := by
  obtain ⟨C, hC⟩ := hΨ.decay c c hc hc' K
  exact ⟨C, fun t => by simpa using hC ((c : ℂ) + t * I) (by simp) (by simp)⟩

/-- Integrability on a line inside the strip. -/
theorem integrable_line (hΨ : MellinRegularStrip Ψ α β) {c : ℝ} (hc : α < c) (hc' : c < β) :
    Integrable fun t : ℝ => Ψ ((c : ℂ) + t * I) := by
  obtain ⟨C, hC⟩ := hΨ.line_bound hc hc' 1
  refine (integrable_inv_one_add_sq.const_mul C).mono' (hΨ.continuous_line hc hc').aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have := hC t
  simpa [div_eq_mul_inv] using this

/-- Square integrability on a line inside the strip. -/
theorem memLp_two_line (hΨ : MellinRegularStrip Ψ α β) {c : ℝ} (hc : α < c) (hc' : c < β) :
    MemLp (fun t : ℝ => Ψ ((c : ℂ) + t * I)) 2 := by
  obtain ⟨C, hC⟩ := hΨ.line_bound hc hc' 1
  have hcont := hΨ.continuous_line hc hc'
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (by simpa using hC 0)
  refine (integrable_inv_one_add_sq.const_mul (C ^ 2)).mono' (hcont.norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have h1 := hC t
  rw [pow_one] at h1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hden : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  calc ‖Ψ ((c : ℂ) + t * I)‖ ^ 2 ≤ (C / (1 + t ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = C ^ 2 / (1 + t ^ 2) / (1 + t ^ 2) := by ring
    _ ≤ C ^ 2 / (1 + t ^ 2) := div_le_self (by positivity) hden
    _ = C ^ 2 * (1 + t ^ 2)⁻¹ := by ring

private theorem norm_cpow_neg_le' {x : ℝ} (hx : 0 < x) {c₁ c₂ : ℝ} {s : ℂ} (hs : s.re ∈ uIcc c₁ c₂) :
    ‖(x : ℂ) ^ (-s)‖ ≤ x ^ (-c₁) + x ^ (-c₂) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, neg_re]
  rw [Set.mem_uIcc] at hs
  have h1 : 0 ≤ x ^ (-c₁) := Real.rpow_nonneg hx.le _
  have h2 : 0 ≤ x ^ (-c₂) := Real.rpow_nonneg hx.le _
  rcases le_or_gt x 1 with hx1 | hx1
  · rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have := Real.rpow_le_rpow_of_exponent_ge hx hx1 (show -s.re ≥ -c₂ by linarith)
      linarith
    · have := Real.rpow_le_rpow_of_exponent_ge hx hx1 (show -s.re ≥ -c₁ by linarith)
      linarith
  · rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have := Real.rpow_le_rpow_of_exponent_le hx1.le (show -s.re ≤ -c₁ by linarith)
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le hx1.le (show -s.re ≤ -c₂ by linarith)
      linarith

/-- The inverse Mellin transform of a regular function does not depend on the abscissa inside the
strip. -/
theorem mellinInv_eq (hΨ : MellinRegularStrip Ψ α β) {c₁ c₂ : ℝ}
    (h1 : α < c₁) (h1' : c₁ < β) (h2 : α < c₂) (h2' : c₂ < β) {x : ℝ} (hx : 0 < x) :
    mellinInv c₁ Ψ x = mellinInv c₂ Ψ x := by
  unfold mellinInv
  congr 1
  obtain ⟨C, hC⟩ := hΨ.decay (min c₁ c₂) (max c₁ c₂) (lt_min h1 h2) (max_lt h1' h2') 1
  have hstrip : ∀ s : ℂ, s.re ∈ uIcc c₁ c₂ → α < s.re ∧ s.re < β := by
    intro s hs
    rw [Set.mem_uIcc] at hs
    rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> constructor <;> linarith
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have key := integral_vertical_line_shift_of_decay
    (Φ := fun s : ℂ => (x : ℂ) ^ (-s) * Ψ s) (c₁ := c₁) (c₂ := c₂)
    (C := (x ^ (-c₁) + x ^ (-c₂)) * C)
    (fun s hs => by
      obtain ⟨hs0, hs1⟩ := hstrip s hs
      exact ((differentiableAt_id.neg).const_cpow (Or.inl hx0)).mul (hΨ.diff s hs0 hs1))
    (fun s hs => by
      have hs' := hs
      rw [Set.mem_uIcc] at hs'
      have hmin : min c₁ c₂ ≤ s.re := by
        rcases hs' with ⟨ha, _⟩ | ⟨ha, _⟩
        · exact min_le_iff.mpr (Or.inl ha)
        · exact min_le_iff.mpr (Or.inr ha)
      have hmax : s.re ≤ max c₁ c₂ := by
        rcases hs' with ⟨_, hb⟩ | ⟨_, hb⟩
        · exact le_max_iff.mpr (Or.inr hb)
        · exact le_max_iff.mpr (Or.inl hb)
      have hb := hC s hmin hmax
      rw [pow_one] at hb
      rw [norm_mul]
      calc ‖(x : ℂ) ^ (-s)‖ * ‖Ψ s‖ ≤ (x ^ (-c₁) + x ^ (-c₂)) * (C / (1 + s.im ^ 2)) :=
            mul_le_mul (norm_cpow_neg_le' hx hs) hb (norm_nonneg _) (by positivity)
        _ = (x ^ (-c₁) + x ^ (-c₂)) * C / (1 + s.im ^ 2) := by ring)
  simpa [smul_eq_mul] using key

/-- Multiplying by `s` preserves regularity. -/
theorem mul_id (hΨ : MellinRegularStrip Ψ α β) : MellinRegularStrip (fun s => s * Ψ s) α β := by
  refine ⟨fun s h1 h2 => differentiableAt_id.mul (hΨ.diff s h1 h2), fun a b ha hb K => ?_⟩
  obtain ⟨C, hC⟩ := hΨ.decay a b ha hb (K + 1)
  refine ⟨(|a| + |b| + 1) * max C 0, fun s hsa hsb => ?_⟩
  have hden : 0 < (1 + s.im ^ 2) ^ K := by positivity
  have hs : ‖s‖ ≤ (|a| + |b| + 1) * Real.sqrt (1 + s.im ^ 2) := by
    have hre : |s.re| ≤ |a| + |b| := by
      rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ (|a| + |b|) * Real.sqrt (1 + s.im ^ 2) + 1 * Real.sqrt (1 + s.im ^ 2) := by
        have h1 : 1 ≤ Real.sqrt (1 + s.im ^ 2) := by
          rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [sq_nonneg s.im]
        have h2 : |s.im| ≤ Real.sqrt (1 + s.im ^ 2) := by
          rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
        nlinarith [abs_nonneg s.re, abs_nonneg a, abs_nonneg b]
      _ = _ := by ring
  have hΨb : ‖Ψ s‖ ≤ max C 0 / (1 + s.im ^ 2) ^ (K + 1) :=
    (hC s hsa hsb).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  rw [norm_mul]
  have hsq : Real.sqrt (1 + s.im ^ 2) ≤ 1 + s.im ^ 2 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_nonneg s.im]
  calc ‖s‖ * ‖Ψ s‖ ≤ ((|a| + |b| + 1) * Real.sqrt (1 + s.im ^ 2)) *
        (max C 0 / (1 + s.im ^ 2) ^ (K + 1)) := mul_le_mul hs hΨb (norm_nonneg _) (by positivity)
    _ ≤ ((|a| + |b| + 1) * (1 + s.im ^ 2)) * (max C 0 / (1 + s.im ^ 2) ^ (K + 1)) := by
        gcongr
    _ = (|a| + |b| + 1) * max C 0 / (1 + s.im ^ 2) ^ K := by
        rw [pow_succ]; field_simp; ring

/-- **Differentiation of the inverse Mellin transform.** For `x₀ > 0` and a line `c ≠ 0` inside the
strip, `d/dx Mellin⁻¹_c Ψ (x) = x⁻¹ Mellin⁻¹_c (s ↦ -s Ψ(s)) (x)`. -/
theorem hasDerivAt_mellinInv (hΨ : MellinRegularStrip Ψ α β) {c : ℝ} (hc : α < c) (hc' : c < β)
    (hc0 : c ≠ 0) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    HasDerivAt (fun x : ℝ => mellinInv c Ψ x)
      (((x₀ : ℂ))⁻¹ * mellinInv c (fun s => -s * Ψ s) x₀) x₀ := by
  set L : ℝ → ℂ := fun t => (c : ℂ) + t * I with hL
  have hLre : ∀ t : ℝ, (L t).re = c := fun t => by simp [hL]
  have hL0 : ∀ t : ℝ, -(L t) ≠ 0 := by
    intro t h
    have := congrArg Complex.re h
    rw [neg_re, hLre, zero_re] at this
    exact hc0 (by linarith)
  set Fx : ℝ → ℝ → ℂ := fun x t => (x : ℂ) ^ (-(L t)) * Ψ (L t) with hFx
  set Fd : ℝ → ℝ → ℂ := fun x t => -(L t) * (x : ℂ) ^ (-(L t) - 1) * Ψ (L t) with hFd
  have hs : Icc (x₀ / 2) (2 * x₀) ∈ 𝓝 x₀ := Icc_mem_nhds (by linarith) (by linarith)
  have hpos : ∀ x ∈ Icc (x₀ / 2) (2 * x₀), 0 < x := fun x hx => lt_of_lt_of_le (by linarith) hx.1
  set M : ℝ := (x₀ / 2) ^ (-c - 1) + (2 * x₀) ^ (-c - 1) with hM
  have hcontΨ : Continuous fun t : ℝ => Ψ (L t) := hΨ.continuous_line hc hc'
  have hmulInt : Integrable fun t : ℝ => L t * Ψ (L t) := (hΨ.mul_id).integrable_line hc hc'
  have hΨint : Integrable fun t : ℝ => Ψ (L t) := hΨ.integrable_line hc hc'
  have hcpow : ∀ x : ℝ, 0 < x → ∀ e : ℂ → ℂ, Continuous (fun t : ℝ => e (L t)) →
      Continuous fun t : ℝ => (x : ℂ) ^ (e (L t)) := by
    intro x hx e he
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    exact Continuous.const_cpow he (Or.inl hx0)
  have hLcont : Continuous L := by simp only [hL]; fun_prop
  have hderiv : ∀ t : ℝ, ∀ x ∈ Icc (x₀ / 2) (2 * x₀), HasDerivAt (fun x => Fx x t) (Fd x t) x := by
    intro t x hx
    have h := (hasDerivAt_ofReal_cpow_const (hpos x hx).ne' (hL0 t)).mul_const (Ψ (L t))
    simpa [hFx, hFd] using h
  have hxM : ∀ x ∈ Icc (x₀ / 2) (2 * x₀), x ^ (-c - 1) ≤ M := by
    intro x hx
    have hxp := hpos x hx
    have h1 : 0 ≤ (x₀ / 2) ^ (-c - 1) := Real.rpow_nonneg (by linarith) _
    have h2 : 0 ≤ (2 * x₀) ^ (-c - 1) := Real.rpow_nonneg (by linarith) _
    rcases le_or_gt 0 (-c - 1) with he | he
    · have := Real.rpow_le_rpow hxp.le hx.2 he; linarith
    · have := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < x₀ / 2) hx.1 he.le; linarith
  have hbound : ∀ t : ℝ, ∀ x ∈ Icc (x₀ / 2) (2 * x₀), ‖Fd x t‖ ≤ M * ‖L t * Ψ (L t)‖ := by
    intro t x hx
    have hxp := hpos x hx
    simp only [hFd]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hxp, norm_mul]
    have hre : (-(L t) - 1).re = -c - 1 := by simp [hLre]
    rw [hre]
    have hM0 := hxM x hx
    have h0 : 0 ≤ ‖L t‖ * ‖Ψ (L t)‖ := by positivity
    nlinarith [Real.rpow_nonneg hxp.le (-c - 1), norm_nonneg (L t), norm_nonneg (Ψ (L t))]
  have hmeasF : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (Fx x) volume := by
    filter_upwards [Ioi_mem_nhds hx₀] with x hx
    exact ((hcpow x hx (fun z => -z) (hLcont.neg)).mul hcontΨ).aestronglyMeasurable
  have hFint : Integrable (Fx x₀) := by
    refine (hΨint.norm.const_mul (x₀ ^ (-c))).mono'
      ((hcpow x₀ hx₀ (fun z => -z) hLcont.neg).mul hcontΨ).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    simp only [hFx]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx₀, neg_re, hLre]
  have hFdmeas : AEStronglyMeasurable (Fd x₀) volume :=
    ((hLcont.neg.mul (hcpow x₀ hx₀ (fun z => -z - 1) (hLcont.neg.sub continuous_const))).mul
      hcontΨ).aestronglyMeasurable
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := Fx)
    (F' := Fd) (bound := fun t => M * ‖L t * Ψ (L t)‖) hs hmeasF hFint hFdmeas
    (Eventually.of_forall fun t x hx => hbound t x hx) (hmulInt.norm.const_mul M)
    (Eventually.of_forall fun t x hx => hderiv t x hx)
  have h2 := hmain.2.const_smul (1 / (2 * Real.pi) : ℝ)
  have hfun : (fun x : ℝ => mellinInv c Ψ x) = fun x => (1 / (2 * Real.pi) : ℝ) • ∫ t, Fx x t := by
    funext x; simp [mellinInv, hFx, hL, smul_eq_mul]
  rw [hfun]
  have h3 : HasDerivAt (fun x : ℝ => (1 / (2 * Real.pi) : ℝ) • ∫ t, Fx x t)
      ((1 / (2 * Real.pi) : ℝ) • ∫ t, Fd x₀ t) x₀ := h2
  refine h3.congr_deriv ?_
  have hx0 : (x₀ : ℂ) ≠ 0 := by exact_mod_cast hx₀.ne'
  have hint_eq : ∫ t, Fd x₀ t = ((x₀ : ℂ))⁻¹ * ∫ t, (x₀ : ℂ) ^ (-(L t)) * (-(L t) * Ψ (L t)) := by
    rw [← integral_const_mul]
    congr 1; funext t
    simp only [hFd]
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
    field_simp
  rw [hint_eq]
  simp [mellinInv, hL, smul_eq_mul]
  ring

end MellinRegularStrip

end GaloisForLFunctions.HTGeometry
