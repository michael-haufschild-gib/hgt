import GaloisForLFunctions.RHTower.BesselKZeroMoments
import GaloisForLFunctions.HTGeometry.VerticalStripContourShift

/-!
# Mellin transforms for the `K₀`-theta function

* **Two-line Mellin engine** (`eq_of_hasMellin_two_lines`).  Let `E` be holomorphic on the closed
  strip `a ≤ Re s ≤ b` with `|E(s)| ≤ C/(1 + (Im s)²)` there.  If `f₁` has Mellin transform `E` on
  the line `Re s = b` and `f₂` has Mellin transform `E` on the line `Re s = a`, then `f₁ = f₂` at
  every point of continuity.  Mellin inversion on the two lines is joined by the contour shift.
* **The `K₀`-theta function** `Θ(y) = Σ_{n ≥ 1} g_n K₀(2πny)` has Mellin transform
  `¼ Γ_ℝ(s)² Σ g_n n^{−s}` for `Re s > 1` whenever `Σ |g_n| n^{−σ} < ∞` for `σ > 1`
  (`hasMellin_kTheta`): termwise, `∫₀^∞ K₀(2πny) y^{s−1} dy = (2πn)^{−s} 2^{s−2} Γ(s/2)²`.
-/

open Complex Set Filter MeasureTheory Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.MaassThetaMellin

open BesselKZero

/-! ## The two-line engine -/

/-- The inverse-Mellin integrand `y ↦ x^{−(σ+iy)} E(σ+iy)` is integrable when `E` decays like
`1/(1 + t²)` on a strip containing the line `Re s = σ`. -/
theorem integrable_cpow_mul_line {E : ℂ → ℂ} {a b C : ℝ}
    (hE : ContinuousOn E (verticalStrip a b))
    (hdecay : ∀ s ∈ verticalStrip a b, ‖E s‖ ≤ C / (1 + s.im ^ 2))
    {σ : ℝ} (hσa : a ≤ σ) (hσb : σ ≤ b) {x : ℝ} (hx : 0 < x) :
    Integrable fun y : ℝ => (x : ℂ) ^ (-((σ : ℂ) + y * I)) * E ((σ : ℂ) + y * I) := by
  have hmem : ∀ y : ℝ, (σ : ℂ) + y * I ∈ verticalStrip a b := by
    intro y
    rw [mem_verticalStrip]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_self,
      add_zero]
    exact ⟨hσa, hσb⟩
  have hcont : Continuous fun y : ℝ => (x : ℂ) ^ (-((σ : ℂ) + y * I)) * E ((σ : ℂ) + y * I) := by
    refine Continuous.mul ?_ ?_
    · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))
    · exact hE.comp_continuous (by fun_prop) hmem
  have hC : 0 ≤ C := by
    have h := hdecay _ (hmem 0)
    have h' : 0 ≤ C / (1 + ((σ : ℂ) + ((0 : ℝ) : ℂ) * I).im ^ 2) := (norm_nonneg _).trans h
    simpa using h'
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (x ^ (-σ) * C))
    hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (-((σ : ℂ) + y * I)).re = -σ := by simp
  have him : ((σ : ℂ) + y * I).im = y := by simp
  rw [hre]
  have hb := hdecay _ (hmem y)
  rw [him] at hb
  calc x ^ (-σ) * ‖E ((σ : ℂ) + y * I)‖ ≤ x ^ (-σ) * (C / (1 + y ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = x ^ (-σ) * C * (1 + y ^ 2)⁻¹ := by ring

/-- The horizontal edges of the inverse-Mellin integrand tend to zero. -/
theorem tendsto_integral_horizontal_cpow_mul {E : ℂ → ℂ} {a b C : ℝ}
    (hdecay : ∀ s ∈ verticalStrip a b, ‖E s‖ ≤ C / (1 + s.im ^ 2)) (hab : a ≤ b)
    {x : ℝ} (hx : 0 < x) {h : ℝ → ℝ} (hh : ∀ T, h T ^ 2 = T ^ 2) :
    Tendsto (fun T : ℝ => ∫ u in a..b,
      (x : ℂ) ^ (-((u : ℂ) + ((h T : ℝ) : ℂ) * I)) * E ((u : ℂ) + ((h T : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
  have hbound : ∀ T : ℝ, ‖∫ u in a..b,
      (x : ℂ) ^ (-((u : ℂ) + ((h T : ℝ) : ℂ) * I)) * E ((u : ℂ) + ((h T : ℝ) : ℂ) * I)‖ ≤
      (x ^ (-a) + x ^ (-b)) * (C / (1 + T ^ 2)) * |b - a| := by
    intro T
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    rw [uIoc_of_le hab] at hu
    have hmem : (u : ℂ) + ((h T : ℝ) : ℂ) * I ∈ verticalStrip a b := by
      rw [mem_verticalStrip]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_self,
        add_zero]
      exact ⟨hu.1.le, hu.2⟩
    have hb := hdecay _ hmem
    have him : ((u : ℂ) + ((h T : ℝ) : ℂ) * I).im = h T := by simp
    rw [him, hh T] at hb
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hre : (-((u : ℂ) + ((h T : ℝ) : ℂ) * I)).re = -u := by simp
    rw [hre]
    have hxu : x ^ (-u) ≤ x ^ (-a) + x ^ (-b) := by
      rcases le_total 1 x with h1 | h1
      · have := Real.rpow_le_rpow_of_exponent_le h1 (show -u ≤ -a by linarith [hu.1])
        linarith [Real.rpow_pos_of_pos hx (-b)]
      · have := Real.rpow_le_rpow_of_exponent_ge hx h1 (show -b ≤ -u by linarith [hu.2])
        linarith [Real.rpow_pos_of_pos hx (-a)]
    exact mul_le_mul hxu hb (norm_nonneg _) (by positivity)
  have hlim : Tendsto (fun T : ℝ => (x ^ (-a) + x ^ (-b)) * (C / (1 + T ^ 2)) * |b - a|)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => 1 + T ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)
    have h2 : Tendsto (fun T : ℝ => C / (1 + T ^ 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h1
    simpa using (h2.const_mul (x ^ (-a) + x ^ (-b))).mul_const |b - a|
  exact squeeze_zero_norm hbound hlim

/-- **The two-line Mellin engine.** -/
theorem eq_of_hasMellin_two_lines {f₁ f₂ : ℝ → ℂ} {E : ℂ → ℂ} {a b C : ℝ} (hab : a ≤ b)
    (hE : DifferentiableOn ℂ E (verticalStrip a b))
    (hdecay : ∀ s ∈ verticalStrip a b, ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (h₁ : ∀ s : ℂ, s.re = b → HasMellin f₁ s (E s))
    (h₂ : ∀ s : ℂ, s.re = a → HasMellin f₂ s (E s))
    {x : ℝ} (hx : 0 < x) (hc₁ : ContinuousAt f₁ x) (hc₂ : ContinuousAt f₂ x) : f₁ x = f₂ x := by
  have hEc : ContinuousOn E (verticalStrip a b) := hE.continuousOn
  have hline : ∀ (σ : ℝ) (f : ℝ → ℂ), (∀ s : ℂ, s.re = σ → HasMellin f s (E s)) →
      a ≤ σ → σ ≤ b → ContinuousAt f x →
      f x = (1 / (2 * Real.pi)) • ∫ y : ℝ, (x : ℂ) ^ (-((σ : ℂ) + y * I)) * E ((σ : ℂ) + y * I) := by
    intro σ f hf hσa hσb hcf
    have hconv : MellinConvergent f σ := (hf σ (by simp)).1
    have hvert : Complex.VerticalIntegrable (mellin f) σ := by
      have h := integrable_cpow_mul_line hEc hdecay hσa hσb (x := 1) one_pos
      refine h.congr (Eventually.of_forall fun y => ?_)
      simp only [ofReal_one, one_cpow, one_mul]
      exact ((hf _ (by simp)).2).symm
    rw [← mellinInv_mellin_eq σ f hx hconv hvert hcf, mellinInv]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    rw [(hf _ (by simp)).2]
  rw [hline b f₁ h₁ hab le_rfl hc₁, hline a f₂ h₂ le_rfl hab hc₂]
  congr 1
  have hG : DifferentiableOn ℂ (fun w : ℂ => (x : ℂ) ^ (-w) * E w) (verticalStrip a b) := by
    refine DifferentiableOn.mul ?_ hE
    intro w _
    exact (differentiableAt_id.neg.const_cpow
      (Or.inl (by exact_mod_cast hx.ne'))).differentiableWithinAt
  exact integral_vertical_line_eq_of_horizontal_tendsto hab hG
    (integrable_cpow_mul_line hEc hdecay le_rfl hab hx)
    (integrable_cpow_mul_line hEc hdecay hab le_rfl hx)
    (tendsto_integral_horizontal_cpow_mul hdecay hab hx (h := fun T => -T) (fun T => by ring))
    (tendsto_integral_horizontal_cpow_mul hdecay hab hx (h := fun T => T) (fun T => rfl))

/-! ## The `K₀`-theta function -/

variable {g : ℕ → ℂ}

/-- `Θ(y) = Σ_{n ≥ 1} g_n K₀(2πny)`. -/
def kTheta (g : ℕ → ℂ) (y : ℝ) : ℂ := ∑' n, g (n + 1) * (kMoment 0 (2 * Real.pi * (n + 1) * y) : ℂ)

/-- One term: `∫₀^∞ K₀(cy) y^{s−1} dy = c^{−s} 2^{s−2} Γ(s/2)²`. -/
theorem integral_kMoment_scaled {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) :
    ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) * (kMoment 0 (c * y) : ℂ) =
      (c : ℂ) ^ (-s) * ((2 : ℂ) ^ (s - 2) * Complex.Gamma (s / 2) ^ 2) := by
  have h := mellin_kZero hs
  have hscale := integral_comp_mul_left_Ioi
    (fun u : ℝ => (u : ℂ) ^ (s - 1) * (kMoment 0 u : ℂ)) 0 hc
  simp only [mul_zero] at hscale
  rw [h] at hscale
  -- `(cy)^{s−1} = c^{s−1} y^{s−1}`
  have hpt : ∀ y ∈ Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) * (kMoment 0 (c * y) : ℂ) =
      (c : ℂ) ^ (-(s - 1)) * (((c * y : ℝ) : ℂ) ^ (s - 1) * (kMoment 0 (c * y) : ℂ)) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le hy0.le, ← mul_assoc, ← mul_assoc,
      ← Complex.cpow_add _ _ (by exact_mod_cast hc.ne'), neg_add_cancel, Complex.cpow_zero, one_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hscale, Complex.real_smul,
    ← mul_assoc]
  congr 1
  rw [show (c : ℂ) ^ (-s) = (c : ℂ) ^ (-(s - 1)) * (c : ℂ)⁻¹ by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ (by exact_mod_cast hc.ne')]; ring_nf]
  push_cast
  ring

/-- The absolute value of a term: `∫₀^∞ K₀(cy) y^{σ−1} dy = c^{−σ} 2^{σ−2} Γ(σ/2)²`. -/
theorem integral_norm_kTerm {c : ℝ} (hc : 0 < c) {σ : ℝ} (hσ : 0 < σ) :
    ∫ y in Ioi (0 : ℝ), y ^ (σ - 1) * kMoment 0 (c * y) =
      c ^ (-σ) * (2 ^ (σ - 2) * Real.Gamma (σ / 2) ^ 2) := by
  have h := integral_kMoment_scaled hc (s := (σ : ℂ)) (by simpa using hσ)
  have hreal : ∀ y ∈ Ioi (0 : ℝ), ((y ^ (σ - 1) * kMoment 0 (c * y) : ℝ) : ℂ) =
      (y : ℂ) ^ ((σ : ℂ) - 1) * (kMoment 0 (c * y) : ℂ) := by
    intro y hy
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt hy)]
    push_cast; rfl
  have h2 : ((∫ y in Ioi (0 : ℝ), y ^ (σ - 1) * kMoment 0 (c * y) : ℝ) : ℂ) =
      ((c ^ (-σ) * (2 ^ (σ - 2) * Real.Gamma (σ / 2) ^ 2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, setIntegral_congr_fun measurableSet_Ioi hreal, h]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hc.le, Complex.ofReal_mul,
      Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_pow, ← Complex.Gamma_ofReal]
    push_cast
    ring_nf
  exact_mod_cast h2

theorem kMoment_continuous_pos : ContinuousOn (fun y : ℝ => kMoment 0 y) (Ioi 0) :=
  continuousOn_kMoment 0

/-- Polynomial growth from absolute convergence beyond `1`: `‖g_{n+1}‖ ≤ M (n + 1)²`. -/
theorem exists_norm_le_sq (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ‖g (n + 1)‖ ≤ M * ((n : ℝ) + 1) ^ 2 := by
  have hs := hsum 2 (by norm_num)
  have hnn : ∀ n : ℕ, 0 ≤ ‖g n‖ * (n : ℝ) ^ (-(2 : ℝ)) := fun n => by positivity
  refine ⟨∑' n : ℕ, ‖g n‖ * (n : ℝ) ^ (-(2 : ℝ)), tsum_nonneg hnn, fun n => ?_⟩
  have hle := hs.le_tsum (n + 1) (fun j _ => hnn j)
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hrp : ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) * ((n : ℝ) + 1) ^ 2 = 1 := by
    rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hpos.le,
      ← Real.rpow_natCast]
    push_cast
    rw [inv_mul_cancel₀ (by positivity)]
  calc ‖g (n + 1)‖ = ‖g (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) * ((n : ℝ) + 1) ^ 2 := by
        rw [mul_assoc, hrp, mul_one]
    _ ≤ (∑' n : ℕ, ‖g n‖ * (n : ℝ) ^ (-(2 : ℝ))) * ((n : ℝ) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hle (by positivity)

/-- The Mellin integrand of the `n`-th term. -/
def kThetaTerm (g : ℕ → ℂ) (s : ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (s - 1) * (g (n + 1) * (kMoment 0 (2 * Real.pi * (n + 1) * y) : ℂ))

theorem kTheta_term_hasMellin (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun y : ℝ => g (n + 1) * (kMoment 0 (2 * Real.pi * (n + 1) * y) : ℂ)) s
      (g (n + 1) * (((2 * Real.pi * (n + 1) : ℝ) : ℂ) ^ (-s) *
        ((2 : ℂ) ^ (s - 2) * Complex.Gamma (s / 2) ^ 2))) := by
  have hc : (0 : ℝ) < 2 * Real.pi * (n + 1) := by positivity
  have hK := hasMellin_kZero hs
  have hconv : MellinConvergent (fun y : ℝ => (kMoment 0 (2 * Real.pi * (n + 1) * y) : ℂ)) s :=
    (MellinConvergent.comp_mul_left (f := fun r : ℝ => (kMoment 0 r : ℂ)) hc).mpr hK.1
  have hval : mellin (fun y : ℝ => (kMoment 0 (2 * Real.pi * (n + 1) * y) : ℂ)) s =
      ((2 * Real.pi * (n + 1) : ℝ) : ℂ) ^ (-s) * ((2 : ℂ) ^ (s - 2) * Complex.Gamma (s / 2) ^ 2) := by
    rw [mellin_comp_mul_left (fun r : ℝ => (kMoment 0 r : ℂ)) s hc, hK.2, smul_eq_mul]
  have h := hasMellin_const_smul hconv (g (n + 1))
  refine ⟨h.1, ?_⟩
  rw [show (fun y : ℝ => g (n + 1) * (kMoment 0 (2 * Real.pi * (n + 1) * y) : ℂ)) =
    fun y : ℝ => g (n + 1) • (kMoment 0 (2 * Real.pi * (n + 1) * y) : ℂ) from rfl, h.2, hval]
  rfl

/-- `Θ` is continuous on `(0, ∞)`: on `y > y₀/2` the terms are `O((n+1)² e^{−π(n+1)y₀})`. -/
theorem continuousOn_kTheta (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ)) :
    ContinuousOn (kTheta g) (Ioi 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_le_sq hsum
  intro y₀ hy₀
  have hy₀' : (0 : ℝ) < y₀ := hy₀
  have hr : 0 < Real.pi * y₀ := by positivity
  set K : ℝ := Real.exp (Real.pi * y₀) * kMoment 0 (Real.pi * y₀) with hK
  have hK0 : 0 ≤ K := by have := kMoment_nonneg 0 (Real.pi * y₀); positivity
  have hu : Summable fun n : ℕ => M * K * (((n + 1 : ℕ) : ℝ) ^ 2 *
      Real.exp (-(Real.pi * y₀) * ((n + 1 : ℕ) : ℝ))) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul 2 hr)).mul_left _
  have hcont : ContinuousOn (kTheta g) (Ioi (y₀ / 2)) := by
    refine continuousOn_tsum (fun n => ?_) hu (fun n y hy => ?_)
    · have hc : ContinuousOn (fun y : ℝ => kMoment 0 (2 * Real.pi * (n + 1) * y)) (Ioi (y₀ / 2)) :=
        (continuousOn_kMoment 0).comp (by fun_prop) (fun y hy => by
          have : (0 : ℝ) < y := lt_trans (by positivity) hy
          show 0 < 2 * Real.pi * (n + 1) * y
          positivity)
      exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hc)
    · have hy' : y₀ / 2 < y := hy
      have hle : Real.pi * y₀ ≤ 2 * Real.pi * (n + 1) * y := by
        have : y₀ ≤ 2 * ((n : ℝ) + 1) * y := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        nlinarith [Real.pi_pos]
      have hKb := kMoment_le_exp_mul 0 hr hle
      have hexp : Real.exp (-(2 * Real.pi * (n + 1) * y - Real.pi * y₀)) ≤
          Real.exp (Real.pi * y₀) * Real.exp (-(Real.pi * y₀) * ((n + 1 : ℕ) : ℝ)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith [Real.pi_pos]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kMoment_nonneg _ _)]
      have hn := hM n
      calc ‖g (n + 1)‖ * kMoment 0 (2 * Real.pi * (n + 1) * y)
          ≤ (M * ((n : ℝ) + 1) ^ 2) * (Real.exp (Real.pi * y₀) *
              Real.exp (-(Real.pi * y₀) * ((n + 1 : ℕ) : ℝ)) * kMoment 0 (Real.pi * y₀)) := by
            refine mul_le_mul hn (hKb.trans ?_) (kMoment_nonneg _ _) (by positivity)
            exact mul_le_mul_of_nonneg_right hexp (kMoment_nonneg _ _)
        _ = M * K * (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(Real.pi * y₀) * ((n + 1 : ℕ) : ℝ))) := by
            rw [hK]; push_cast; ring
  exact hcont.continuousWithinAt (by simp; linarith) |>.mono_of_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith)))

/-- **The Mellin transform of the `K₀`-theta function.** -/
theorem hasMellin_kTheta (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖g n‖ * (n : ℝ) ^ (-σ))
    {s : ℂ} (hs : 1 < s.re) :
    HasMellin (kTheta g) s ((1 / 4 : ℂ) * Complex.Gammaℝ s ^ 2 * LSeries g s) := by
  have hs0 : 0 < s.re := by linarith
  set F : ℕ → ℝ → ℂ := fun n y =>
    (y : ℂ) ^ (s - 1) • (g (n + 1) * (kMoment 0 (2 * Real.pi * (n + 1) * y) : ℂ)) with hFdef
  have hT := fun n => kTheta_term_hasMellin (g := g) n hs0
  have hFi : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n => (hT n).1
  have hFnorm : ∀ n, ∫ y in Ioi (0 : ℝ), ‖F n y‖ = ‖g (n + 1)‖ *
      ((2 * Real.pi * (n + 1)) ^ (-s.re) * (2 ^ (s.re - 2) * Real.Gamma (s.re / 2) ^ 2)) := by
    intro n
    have hc : (0 : ℝ) < 2 * Real.pi * (n + 1) := by positivity
    have hpt : ∀ y ∈ Ioi (0 : ℝ), ‖F n y‖ =
        ‖g (n + 1)‖ * (y ^ (s.re - 1) * kMoment 0 (2 * Real.pi * (n + 1) * y)) := by
      intro y hy
      have hy0 : (0 : ℝ) < y := hy
      simp only [hFdef, smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kMoment_nonneg _ _), sub_re, one_re]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      integral_norm_kTerm hc hs0]
  have hFs : Summable fun n => ∫ y in Ioi (0 : ℝ), ‖F n y‖ := by
    simp_rw [hFnorm]
    have hs' : Summable fun n : ℕ => ‖g (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re) :=
      (summable_nat_add_iff 1).mpr (hsum s.re hs)
    refine (hs'.mul_right ((2 * Real.pi) ^ (-s.re) *
      (2 ^ (s.re - 2) * Real.Gamma (s.re / 2) ^ 2))).congr fun n => ?_
    rw [Real.mul_rpow (x := 2 * Real.pi) (y := (n : ℝ) + 1) (by positivity) (by positivity)]
    push_cast
    ring
  have hHS := hasSum_integral_of_summable_integral_norm hFi hFs
  have hsumF : ∀ y : ℝ, ∑' n, F n y = (y : ℂ) ^ (s - 1) • kTheta g y := by
    intro y
    simp only [hFdef, kTheta, smul_eq_mul]
    rw [tsum_mul_left]
  have hconv : MellinConvergent (kTheta g) s := by
    unfold MellinConvergent
    refine ⟨?_, ?_⟩
    · have hc : ContinuousOn (fun y : ℝ => (y : ℂ) ^ (s - 1) • kTheta g y) (Ioi 0) := by
        intro y hy
        have hy0 : (0 : ℝ) < y := hy
        exact ((Complex.continuousAt_ofReal_cpow_const y (s - 1) (Or.inr hy0.ne')).continuousWithinAt).smul
          (continuousOn_kTheta hsum y hy)
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · rw [HasFiniteIntegral]
      calc ∫⁻ y in Ioi (0 : ℝ), ‖(y : ℂ) ^ (s - 1) • kTheta g y‖ₑ
          = ∫⁻ y in Ioi (0 : ℝ), ‖∑' n, F n y‖ₑ := by simp_rw [hsumF]
        _ ≤ ∫⁻ y in Ioi (0 : ℝ), ∑' n, ‖F n y‖ₑ := lintegral_mono fun y => enorm_tsum_le_tsum_enorm
        _ = ∑' n, ∫⁻ y in Ioi (0 : ℝ), ‖F n y‖ₑ :=
            lintegral_tsum fun n => (hFi n).aestronglyMeasurable.enorm
        _ < ⊤ := by
            have hfin : ∀ n, ∫⁻ y in Ioi (0 : ℝ), ‖F n y‖ₑ =
                ENNReal.ofReal (∫ y in Ioi (0 : ℝ), ‖F n y‖) := by
              intro n
              rw [ofReal_integral_eq_lintegral_ofReal (hFi n).norm
                (Eventually.of_forall fun y => norm_nonneg _)]
              congr 1
              funext y
              rw [ofReal_norm]
            simp_rw [hfin]
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun y => norm_nonneg _) hFs]
            exact ENNReal.ofReal_lt_top
  refine ⟨hconv, ?_⟩
  have hval : mellin (kTheta g) s = ∑' n, ∫ y in Ioi (0 : ℝ), F n y := by
    rw [mellin, hHS.tsum_eq]
    exact setIntegral_congr_fun measurableSet_Ioi fun y _ => (hsumF y).symm
  rw [hval]
  have hterm : ∀ n, ∫ y in Ioi (0 : ℝ), F n y = ((2 : ℂ) ^ (s - 2) * Complex.Gamma (s / 2) ^ 2 *
      (2 * Real.pi : ℂ) ^ (-s)) * LSeries.term g s (n + 1) := by
    intro n
    have h := (hT n).2
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
    simp only [mellin] at h
    rw [show (fun y : ℝ => F n y) = fun y : ℝ =>
      (y : ℂ) ^ (s - 1) • (g (n + 1) * (kMoment 0 (2 * Real.pi * (n + 1) * y) : ℂ)) from rfl, h]
    have hc : ((2 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) ^ (-s) =
        ((2 * Real.pi : ℝ) : ℂ) ^ (-s) * ((n + 1 : ℕ) : ℂ) ^ (-s) := by
      rw [show (2 * Real.pi * ((n : ℝ) + 1)) = (2 * Real.pi) * ((n + 1 : ℕ) : ℝ) by push_cast; ring,
        Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
        Complex.ofReal_natCast]
    rw [hc, Complex.cpow_neg ((n + 1 : ℕ) : ℂ) s, div_eq_mul_inv]
    push_cast
    ring
  simp_rw [hterm]
  have hLs : LSeriesSummable g s := by
    rw [LSeriesSummable]
    refine (hsum s.re hs).of_norm_bounded (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [LSeries.term_zero, norm_zero]
      exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg 0) _)
    · rw [LSeries.norm_term_eq, if_neg (by omega), Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hshift : LSeries g s = ∑' n : ℕ, LSeries.term g s (n + 1) := by
    rw [LSeries, hLs.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  have hconst : (2 : ℂ) ^ (s - 2) * Complex.Gamma (s / 2) ^ 2 * (2 * Real.pi : ℂ) ^ (-s) =
      (1 / 4 : ℂ) * Complex.Gammaℝ s ^ 2 := by
    rw [Complex.Gammaℝ_def]
    have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    have h2π : (2 * Real.pi : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * (Real.pi : ℂ) ^ (-s) := by
      rw [show (2 * Real.pi : ℂ) = ((2 : ℝ) : ℂ) * ((Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg (by norm_num) hpi]
      push_cast; ring
    have hpow : ((Real.pi : ℂ) ^ (-s / 2)) ^ 2 = (Real.pi : ℂ) ^ (-s) := by
      rw [sq, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
      ring_nf
    have h22 : (2 : ℂ) ^ (s - 2) * (2 : ℂ) ^ (-s) = 1 / 4 := by
      rw [← Complex.cpow_add _ _ (by norm_num), show s - 2 + -s = ((-2 : ℤ) : ℂ) by push_cast; ring,
        Complex.cpow_intCast]
      norm_num
    rw [h2π, mul_pow, hpow]
    linear_combination (Complex.Gamma (s / 2) ^ 2 * (Real.pi : ℂ) ^ (-s)) * h22
  rw [tsum_mul_left, ← hshift, hconst]

end RHTower.MaassThetaMellin
