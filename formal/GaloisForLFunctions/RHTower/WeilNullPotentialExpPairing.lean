import GaloisForLFunctions.RHTower.WeilNullPotentialSpectralPairing
import GaloisForLFunctions.RHTower.StripHorizontalShift

/-!
# The spectral pairing of a null potential against exponentially decaying transforms

Let `u : ℕ → ℝ` with `u 0 = 0`, and let `ψ_u` be its null potential. If
`−ψ_u = charFun σ` for a finite measure `σ`, then for every continuous integrable `g` whose transform
decays like `e^{−b|v|}` with `0 < b < 2` (`nullPotential_pairing_exp`):

`Σ_n u(n) (𝓕(Ξ²g)(log n) + 𝓕(Ξ²g)(−log n)) = −∫ g(t/2π) dσ(t)`,

provided `Σ_n |u(n)| n^{−b} < ∞`. The kernel smoothing `∫ K(v − c)|𝓕g(v)| dv ≤ C e^{−b|c|}`
(`integral_riemannAutocorr_mul_le_exp`) carries the decay of `𝓕g` to the sample points `±log n`,
from `K(y) ≤ C₁ e^{−2|y|}` and `e^{−b|v|} ≤ e^{−b|c|} e^{b|v − c|}`. Compared with polynomial
decay, the summability required of `u` drops from `(1 + log n)^{−J}` to `n^{−b}`.

The same holds for transforms with linear-exponential decay `(1 + |v|) e^{−b|v|}` under
`Σ_n |u(n)| (1 + log n) n^{−b} < ∞` (`nullPotential_pairing_eq_integral_linexp`); both are
instances of `nullPotential_pairing_eq_integral_of_smoothing`.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate

namespace RHTower.WeilRegular

open RHTower.WeilExcess

noncomputable section

variable {u : ℕ → ℝ}

/-- The exponential moment `∫ e^{−k|w|} dw`. -/
def expAbsMoment (k : ℝ) : ℝ := ∫ x : ℝ, Real.exp (-(k * |x|))

theorem expAbsMoment_nonneg (k : ℝ) : 0 ≤ expAbsMoment k :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- **Kernel smoothing of exponential decay**: if `P(v) ≤ C_P e^{−b|v|}` with `0 ≤ b < 2`, then
`∫ K(v − c) P(v) dv ≤ C₁ C_P E e^{−b|c|}` with `E = ∫ e^{−(2−b)|w|} dw`. -/
theorem integral_riemannAutocorr_mul_le_exp {C₁ : ℝ}
    (hC₁ : ∀ y, riemannAutocorr y ≤ C₁ * Real.exp (-(2 * |y|))) {P : ℝ → ℝ}
    (hP0 : ∀ v, 0 ≤ P v) {b CP : ℝ} (hb0 : 0 ≤ b) (hb : b < 2)
    (hP : ∀ v, P v ≤ CP * Real.exp (-(b * |v|))) (c : ℝ) :
    ∫ v, riemannAutocorr (v - c) * P v ≤ C₁ * CP * expAbsMoment (2 - b) * Real.exp (-(b * |c|)) := by
  have hCP : 0 ≤ CP := by
    have h := (hP0 0).trans (hP 0)
    simp only [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    exact h
  have hC₁0 : 0 ≤ C₁ := by
    have := (riemannAutocorr_nonneg 0).trans (hC₁ 0)
    simp at this
    exact this
  set M : ℝ → ℝ := fun v => C₁ * CP * Real.exp (-(b * |c|)) * Real.exp (-((2 - b) * |v - c|))
    with hM
  have hMi : Integrable M :=
    ((integrable_exp_neg_mul_abs' (by linarith : (0 : ℝ) < 2 - b)).comp_sub_right c).const_mul _
  have hpt : ∀ v, riemannAutocorr (v - c) * P v ≤ M v := by
    intro v
    have htri : |c| ≤ |v| + |v - c| := by
      have := abs_sub v (v - c)
      rwa [sub_sub_cancel] at this
    have hexp : Real.exp (-(2 * |v - c|)) * Real.exp (-(b * |v|)) ≤
        Real.exp (-(b * |c|)) * Real.exp (-((2 - b) * |v - c|)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [abs_nonneg v, abs_nonneg (v - c)]
    calc riemannAutocorr (v - c) * P v
        ≤ (C₁ * Real.exp (-(2 * |v - c|))) * (CP * Real.exp (-(b * |v|))) :=
          mul_le_mul (hC₁ _) (hP v) (hP0 v) (by positivity)
      _ = C₁ * CP * (Real.exp (-(2 * |v - c|)) * Real.exp (-(b * |v|))) := by ring
      _ ≤ C₁ * CP * (Real.exp (-(b * |c|)) * Real.exp (-((2 - b) * |v - c|))) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hC₁0 hCP)
      _ = M v := by rw [hM]; ring
  calc ∫ v, riemannAutocorr (v - c) * P v ≤ ∫ v, M v :=
        integral_mono_of_nonneg (Eventually.of_forall fun v =>
          mul_nonneg (riemannAutocorr_nonneg _) (hP0 v)) hMi (Eventually.of_forall hpt)
    _ = C₁ * CP * Real.exp (-(b * |c|)) * expAbsMoment (2 - b) := by
        rw [hM, integral_const_mul]
        congr 1
        exact integral_sub_right_eq_self (fun w => Real.exp (-((2 - b) * |w|))) c
    _ = C₁ * CP * expAbsMoment (2 - b) * Real.exp (-(b * |c|)) := by ring

theorem integrable_fourier_of_exp_decay {g : ℝ → ℂ} (hg : Integrable g) {b : ℝ} (hb : 0 < b)
    {Cg : ℝ} (hdec : ∀ v, ‖𝓕 g v‖ ≤ Cg * Real.exp (-(b * |v|))) : Integrable (𝓕 g) :=
  ((integrable_exp_neg_mul_abs' hb).const_mul Cg).mono'
    (continuous_fourier_integrable hg).aestronglyMeasurable (Eventually.of_forall hdec)

theorem exp_neg_mul_abs_log (b : ℝ) {n : ℕ} (hn : n ≠ 0) :
    Real.exp (-(b * |Real.log n|)) = (n : ℝ) ^ (-b) := by
  rw [abs_of_nonneg (Real.log_natCast_nonneg n),
    Real.rpow_def_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn)]
  ring_nf

/-- `(1 + s) e^{−as} ≤ (1 + 2/a) e^{−as/2}` for `a > 0`, `s ≥ 0`. -/
theorem one_add_mul_exp_neg_le {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    (1 + s) * Real.exp (-(a * s)) ≤ (1 + 2 / a) * Real.exp (-(a / 2 * s)) := by
  have he := Real.add_one_le_exp (a / 2 * s)
  have hE : 1 ≤ Real.exp (a / 2 * s) := Real.one_le_exp (by positivity)
  have h1 : 1 + s ≤ (1 + 2 / a) * Real.exp (a / 2 * s) := by
    have hs' : s ≤ 2 / a * Real.exp (a / 2 * s) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      nlinarith
    nlinarith
  have e : Real.exp (-(a * s)) = Real.exp (-(a / 2 * s)) * (Real.exp (a / 2 * s))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  rw [e]
  have hpos := Real.exp_pos (a / 2 * s)
  calc (1 + s) * (Real.exp (-(a / 2 * s)) * (Real.exp (a / 2 * s))⁻¹)
      = (1 + s) * (Real.exp (a / 2 * s))⁻¹ * Real.exp (-(a / 2 * s)) := by ring
    _ ≤ (1 + 2 / a) * Real.exp (-(a / 2 * s)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        rw [← div_eq_mul_inv, div_le_iff₀ hpos]
        exact h1

/-- **Kernel smoothing of linear-exponential decay**: if `P(v) ≤ C_P (1 + |v|) e^{−b|v|}` with
`0 ≤ b < 2`, then `∫ K(v − c) P(v) dv ≤ C₁ C_P (1 + 2/(2−b)) E (1 + |c|) e^{−b|c|}` with
`E = ∫ e^{−(1−b/2)|w|} dw`. -/
theorem integral_riemannAutocorr_mul_le_linexp {C₁ : ℝ}
    (hC₁ : ∀ y, riemannAutocorr y ≤ C₁ * Real.exp (-(2 * |y|))) {P : ℝ → ℝ}
    (hP0 : ∀ v, 0 ≤ P v) {b CP : ℝ} (hb0 : 0 ≤ b) (hb : b < 2)
    (hP : ∀ v, P v ≤ CP * ((1 + |v|) * Real.exp (-(b * |v|)))) (c : ℝ) :
    ∫ v, riemannAutocorr (v - c) * P v ≤ C₁ * CP * (1 + 2 / (2 - b)) *
      expAbsMoment ((2 - b) / 2) * ((1 + |c|) * Real.exp (-(b * |c|))) := by
  have hCP : 0 ≤ CP := by
    have h := (hP0 0).trans (hP 0)
    simp only [abs_zero, add_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    exact h
  have hC₁0 : 0 ≤ C₁ := by
    have := (riemannAutocorr_nonneg 0).trans (hC₁ 0)
    simp at this
    exact this
  have hb2 : 0 < 2 - b := by linarith
  set A : ℝ := C₁ * CP * (1 + 2 / (2 - b)) * ((1 + |c|) * Real.exp (-(b * |c|))) with hA
  set M : ℝ → ℝ := fun v => A * Real.exp (-((2 - b) / 2 * |v - c|)) with hM
  have hMi : Integrable M :=
    ((integrable_exp_neg_mul_abs' (by linarith : (0 : ℝ) < (2 - b) / 2)).comp_sub_right c).const_mul
      _
  have hpt : ∀ v, riemannAutocorr (v - c) * P v ≤ M v := by
    intro v
    have htri : |c| ≤ |v| + |v - c| := by
      have := abs_sub v (v - c)
      rwa [sub_sub_cancel] at this
    have hv : |v| ≤ |c| + |v - c| := by
      have := abs_sub (v - c) (-c)
      simp only [sub_neg_eq_add, sub_add_cancel, abs_neg] at this
      linarith
    have h1 : 1 + |v| ≤ (1 + |c|) * (1 + |v - c|) := by
      nlinarith [abs_nonneg c, abs_nonneg (v - c)]
    have hexp : Real.exp (-(2 * |v - c|)) * Real.exp (-(b * |v|)) ≤
        Real.exp (-(b * |c|)) * Real.exp (-((2 - b) * |v - c|)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [abs_nonneg v, abs_nonneg (v - c)]
    have hlin := one_add_mul_exp_neg_le hb2 (abs_nonneg (v - c))
    calc riemannAutocorr (v - c) * P v
        ≤ (C₁ * Real.exp (-(2 * |v - c|))) * (CP * ((1 + |v|) * Real.exp (-(b * |v|)))) :=
          mul_le_mul (hC₁ _) (hP v) (hP0 v) (by positivity)
      _ ≤ (C₁ * Real.exp (-(2 * |v - c|))) *
            (CP * (((1 + |c|) * (1 + |v - c|)) * Real.exp (-(b * |v|)))) := by gcongr
      _ = C₁ * CP * (1 + |c|) * (1 + |v - c|) *
            (Real.exp (-(2 * |v - c|)) * Real.exp (-(b * |v|))) := by ring
      _ ≤ C₁ * CP * (1 + |c|) * (1 + |v - c|) *
            (Real.exp (-(b * |c|)) * Real.exp (-((2 - b) * |v - c|))) := by gcongr
      _ = C₁ * CP * (1 + |c|) * Real.exp (-(b * |c|)) *
            ((1 + |v - c|) * Real.exp (-((2 - b) * |v - c|))) := by ring
      _ ≤ C₁ * CP * (1 + |c|) * Real.exp (-(b * |c|)) *
            ((1 + 2 / (2 - b)) * Real.exp (-((2 - b) / 2 * |v - c|))) := by gcongr
      _ = M v := by rw [hM, hA]; ring
  calc ∫ v, riemannAutocorr (v - c) * P v ≤ ∫ v, M v :=
        integral_mono_of_nonneg (Eventually.of_forall fun v =>
          mul_nonneg (riemannAutocorr_nonneg _) (hP0 v)) hMi (Eventually.of_forall hpt)
    _ = A * expAbsMoment ((2 - b) / 2) := by
        rw [hM, integral_const_mul]
        congr 1
        exact integral_sub_right_eq_self (fun w => Real.exp (-((2 - b) / 2 * |w|))) c
    _ = _ := by rw [hA]; ring

/-- **The null potential paired with `𝓕(Ξ²g)` is `∫ ψ_u 𝓕g`**, for every integrable transform whose
kernel smoothings at `±log n` are dominated by `W(n)` with `Σ |u(n)| W(n) < ∞`. -/
theorem nullPotential_pairing_eq_integral_of_smoothing (hu0 : u 0 = 0)
    {g : ℝ → ℂ} (hg : Integrable g) (hFg : Integrable (𝓕 g)) {W : ℕ → ℝ}
    (hW : ∀ n : ℕ, n ≠ 0 → (∫ v, riemannAutocorr (v - Real.log n) * ‖𝓕 g v‖) +
      ∫ v, riemannAutocorr (v - -Real.log n) * ‖𝓕 g v‖ ≤ W n)
    (hsum : Summable fun n : ℕ => |u n| * W n) :
    ∑' n : ℕ, (u n : ℂ) * (𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (Real.log n) +
        𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (-Real.log n)) =
      ∫ v, (nullPotential u v : ℂ) * 𝓕 g v := by
  set P : ℝ → ℝ := fun v => ‖𝓕 g v‖ with hP
  have hP0 : ∀ v, 0 ≤ P v := fun v => norm_nonneg _
  set F : ℕ → ℝ → ℂ := fun n v => (u n : ℂ) *
    (((riemannAutocorr (v - Real.log n) + riemannAutocorr (v + Real.log n) : ℝ) : ℂ) * 𝓕 g v)
    with hF
  have hKc : ∀ c : ℝ, Continuous fun v => riemannAutocorr (v - c) :=
    fun c => continuous_riemannAutocorr.comp (continuous_id.sub continuous_const)
  have hKi : ∀ c : ℝ, Integrable fun v => ((riemannAutocorr (v - c) : ℝ) : ℂ) * 𝓕 g v := by
    intro c
    refine (hFg.norm.const_mul (riemannAutocorr 0)).mono'
      (((Complex.continuous_ofReal.comp (hKc c)).mul
        (continuous_fourier_integrable hg)).aestronglyMeasurable)
      (Eventually.of_forall fun v => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (riemannAutocorr_nonneg _)]
    exact mul_le_mul_of_nonneg_right (riemannAutocorr_le_zero _) (norm_nonneg _)
  have hKPi : ∀ c : ℝ, Integrable fun v => riemannAutocorr (v - c) * P v := by
    intro c
    refine (hFg.norm.const_mul (riemannAutocorr 0)).mono'
      (((hKc c).mul (continuous_fourier_integrable hg).norm).aestronglyMeasurable)
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (riemannAutocorr_nonneg _) (hP0 v))]
    exact mul_le_mul_of_nonneg_right (riemannAutocorr_le_zero _) (hP0 v)
  have hFi : ∀ n, Integrable (F n) := by
    intro n
    have h := ((hKi (Real.log n)).add (hKi (-Real.log n))).const_mul (u n : ℂ)
    refine h.congr (Eventually.of_forall fun v => ?_)
    simp only [hF, Pi.add_apply, sub_neg_eq_add]; push_cast; ring
  have hterm : ∀ n : ℕ, (u n : ℂ) *
      (𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (Real.log n) +
        𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (-Real.log n)) = ∫ v, F n v := by
    intro n
    rw [fourier_riemannXi_sq_mul hg, fourier_riemannXi_sq_mul hg,
      ← integral_add (hKi _) (hKi _), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hF, sub_neg_eq_add]; push_cast; ring
  have hnorm : ∀ n, ∫ v, ‖F n v‖ = |u n| *
      ((∫ v, riemannAutocorr (v - Real.log n) * P v) +
        ∫ v, riemannAutocorr (v - -Real.log n) * P v) := by
    intro n
    rw [← integral_add (hKPi _) (hKPi _), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hF, hP, norm_mul, Complex.norm_real, Real.norm_eq_abs, sub_neg_eq_add]
    rw [abs_of_nonneg (add_nonneg (riemannAutocorr_nonneg _) (riemannAutocorr_nonneg _))]
    ring
  have hbound : ∀ n : ℕ, ∫ v, ‖F n v‖ ≤ |u n| * W n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hnorm, hu0, abs_zero, zero_mul, zero_mul]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (hW n hn.ne') (abs_nonneg _)
  have hsumnorm : Summable fun n => ∫ v, ‖F n v‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun v => norm_nonneg _) hbound hsum
  rw [tsum_congr hterm, integral_tsum_of_summable_integral_norm hFi hsumnorm]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [hF]
  unfold nullPotential
  rw [Complex.ofReal_tsum, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [add_comm (riemannAutocorr (v - Real.log n))]
  push_cast; ring

/-- **The null potential paired with `𝓕(Ξ²g)` is `∫ ψ_u 𝓕g`**, for exponentially decaying `𝓕g`. -/
theorem nullPotential_pairing_eq_integral_exp (hu0 : u 0 = 0) {b : ℝ} (hb0 : 0 < b) (hb : b < 2)
    (hsum : Summable fun n : ℕ => |u n| * (n : ℝ) ^ (-b))
    {g : ℝ → ℂ} (hg : Integrable g) {Cg : ℝ} (hdec : ∀ v, ‖𝓕 g v‖ ≤ Cg * Real.exp (-(b * |v|))) :
    ∑' n : ℕ, (u n : ℂ) * (𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (Real.log n) +
        𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (-Real.log n)) =
      ∫ v, (nullPotential u v : ℂ) * 𝓕 g v := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := RHTower.WeilExcess.exists_riemannAutocorr_le
  set E : ℝ := C₁ * Cg * expAbsMoment (2 - b) with hE
  refine nullPotential_pairing_eq_integral_of_smoothing hu0 hg
    (integrable_fourier_of_exp_decay hg hb0 hdec) (W := fun n => 2 * E * (n : ℝ) ^ (-b))
    (fun n hn => ?_) ?_
  · have h1 := integral_riemannAutocorr_mul_le_exp hC₁ (fun v => norm_nonneg _) hb0.le hb hdec
      (Real.log n)
    have h2 := integral_riemannAutocorr_mul_le_exp hC₁ (fun v => norm_nonneg _) hb0.le hb hdec
      (-Real.log n)
    rw [abs_neg] at h2
    rw [exp_neg_mul_abs_log b hn] at h1 h2
    linarith
  · refine (hsum.mul_left (2 * E)).congr fun n => ?_
    ring

theorem integrable_fourier_of_linexp_decay {g : ℝ → ℂ} (hg : Integrable g) {b : ℝ} (hb : 0 < b)
    {Cg : ℝ} (hdec : ∀ v, ‖𝓕 g v‖ ≤ Cg * ((1 + |v|) * Real.exp (-(b * |v|)))) :
    Integrable (𝓕 g) := by
  have hCg : 0 ≤ Cg := by
    have h := (norm_nonneg _).trans (hdec 0)
    simp only [abs_zero, add_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    exact h
  refine integrable_fourier_of_exp_decay hg (b := b / 2) (by linarith) (Cg := Cg * (1 + 2 / b))
    fun v => (hdec v).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (one_add_mul_exp_neg_le hb (abs_nonneg v)) hCg

/-- **The null potential paired with `𝓕(Ξ²g)` is `∫ ψ_u 𝓕g`**, for linear-exponentially decaying
`𝓕g`: `‖𝓕g(v)‖ ≤ C (1 + |v|) e^{−b|v|}` with `0 < b < 2`, provided
`Σ_n |u(n)| (1 + log n) n^{−b} < ∞`. -/
theorem nullPotential_pairing_eq_integral_linexp (hu0 : u 0 = 0) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 2) (hsum : Summable fun n : ℕ => |u n| * ((1 + Real.log n) * (n : ℝ) ^ (-b)))
    {g : ℝ → ℂ} (hg : Integrable g) {Cg : ℝ}
    (hdec : ∀ v, ‖𝓕 g v‖ ≤ Cg * ((1 + |v|) * Real.exp (-(b * |v|)))) :
    ∑' n : ℕ, (u n : ℂ) * (𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (Real.log n) +
        𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (-Real.log n)) =
      ∫ v, (nullPotential u v : ℂ) * 𝓕 g v := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := RHTower.WeilExcess.exists_riemannAutocorr_le
  have hFg := integrable_fourier_of_linexp_decay hg hb0 hdec
  set E : ℝ := C₁ * Cg * (1 + 2 / (2 - b)) * expAbsMoment ((2 - b) / 2) with hE
  refine nullPotential_pairing_eq_integral_of_smoothing hu0 hg hFg
    (W := fun n => 2 * E * ((1 + Real.log n) * (n : ℝ) ^ (-b))) (fun n hn => ?_) ?_
  · have hlog : |Real.log n| = Real.log n := abs_of_nonneg (Real.log_natCast_nonneg n)
    have h1 := integral_riemannAutocorr_mul_le_linexp hC₁ (fun v => norm_nonneg _) hb0.le hb hdec
      (Real.log n)
    have h2 := integral_riemannAutocorr_mul_le_linexp hC₁ (fun v => norm_nonneg _) hb0.le hb hdec
      (-Real.log n)
    rw [abs_neg] at h2
    rw [hlog, ← hlog, exp_neg_mul_abs_log b hn, hlog] at h1 h2
    linarith
  · refine (hsum.mul_left (2 * E)).congr fun n => ?_
    ring

/-- **The spectral pairing of a null potential, exponential form.** -/
theorem nullPotential_pairing_exp (hu0 : u 0 = 0) {b : ℝ} (hb0 : 0 < b) (hb : b < 2)
    (hsum : Summable fun n : ℕ => |u n| * (n : ℝ) ^ (-b))
    (σ : Measure ℝ) [IsFiniteMeasure σ] (hσ : ∀ t, charFun σ t = ((-nullPotential u t : ℝ) : ℂ))
    {g : ℝ → ℂ} (hgc : Continuous g) (hg : Integrable g) {Cg : ℝ}
    (hdec : ∀ v, ‖𝓕 g v‖ ≤ Cg * Real.exp (-(b * |v|))) :
    ∑' n : ℕ, (u n : ℂ) * (𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (Real.log n) +
        𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (-Real.log n)) =
      -∫ t, g (t / (2 * π)) ∂σ := by
  rw [nullPotential_pairing_eq_integral_exp hu0 hb0 hb hsum hg hdec,
    integral_nullPotential_mul_fourier σ hσ hgc hg (integrable_fourier_of_exp_decay hg hb0 hdec)]

/-- **The spectral pairing of a null potential, linear-exponential form.** -/
theorem nullPotential_pairing_linexp (hu0 : u 0 = 0) {b : ℝ} (hb0 : 0 < b) (hb : b < 2)
    (hsum : Summable fun n : ℕ => |u n| * ((1 + Real.log n) * (n : ℝ) ^ (-b)))
    (σ : Measure ℝ) [IsFiniteMeasure σ] (hσ : ∀ t, charFun σ t = ((-nullPotential u t : ℝ) : ℂ))
    {g : ℝ → ℂ} (hgc : Continuous g) (hg : Integrable g) {Cg : ℝ}
    (hdec : ∀ v, ‖𝓕 g v‖ ≤ Cg * ((1 + |v|) * Real.exp (-(b * |v|)))) :
    ∑' n : ℕ, (u n : ℂ) * (𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (Real.log n) +
        𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * g ξ) (-Real.log n)) =
      -∫ t, g (t / (2 * π)) ∂σ := by
  rw [nullPotential_pairing_eq_integral_linexp hu0 hb0 hb hsum hg hdec,
    integral_nullPotential_mul_fourier σ hσ hgc hg (integrable_fourier_of_linexp_decay hg hb0 hdec)]

end

end RHTower.WeilRegular
