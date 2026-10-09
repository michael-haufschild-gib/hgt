import GaloisForLFunctions.RHTower.StretchedBoseRiemannEquivalence

/-!
# For `a > 1` the integer dilates of `D_a` are never dense

**Theorem** (`defectDilateL2_span_closure_ne_top`).  For `a > 1` the closed span of the integer
dilates `D_a(k·)`, `k ≥ 1`, is a proper subspace of `L²(0,∞)`.  No hypothesis on `ζ` is needed.

**Proof.**  Take the pole-free separator

`ψ₀(y) = S₂ sin(πy) e^{-λ₁y} - S₁ sin(πy) e^{-λ₂y}`,   `S_j = Γ(1)B_{λ_j}(1) = π/(λ_j² + π²)`,

with Mellin transform `Ψ₀ = S₂ Γ B_{λ₁} - S₁ Γ B_{λ₂}`.  It is holomorphic on `Re s > 0`, decays at
rate `π/2 - π²/(2 min λ)`, vanishes at `s = 1`, and `ψ₀` vanishes on `ℕ`.  The vector `g₀` with
Mellin transform `conj(Ψ₀/F_a)` is orthogonal to every `D_a(k·)`: the contour shift to `Re s = 2`
meets only the removable point `s = 1`, and there `ζ` becomes `Σ n^{-s}`.  Its pairing with
`f_a(t/2)` is `ψ₀(1/2) ≠ 0`, so `g₀ ≠ 0`.

With `boseDilateL2_span_dense` (`a = 1`) this shows that density of the integer dilates holds at
`a = 1` and fails for all `a > 1`.
-/

open MeasureTheory Set Filter Complex
open scoped Topology ComplexConjugate InnerProductSpace

noncomputable section

namespace RHTower.StretchedBose

open GaloisForLFunctions.HTGeometry
open RHTower.SincSeparator

variable {a : ℝ}

/-- The pole-free separator Mellin function `Ψ₀ = S₂ Γ B_{λ₁} - S₁ Γ B_{λ₂}`. -/
def pairMellin (l₁ l₂ : ℝ) (s : ℂ) : ℂ :=
  sinMellin l₂ 1 * sinMellin l₁ s - sinMellin l₁ 1 * sinMellin l₂ s

/-- The pole-free separator kernel `ψ₀ = S₂ sin(πy)e^{-λ₁y} - S₁ sin(πy)e^{-λ₂y}`. -/
def pairKernel (l₁ l₂ : ℝ) (y : ℝ) : ℂ :=
  sinMellin l₂ 1 * ((sinExp l₁ y : ℝ) : ℂ) - sinMellin l₁ 1 * ((sinExp l₂ y : ℝ) : ℂ)

theorem pairMellin_one (l₁ l₂ : ℝ) : pairMellin l₁ l₂ 1 = 0 := by
  unfold pairMellin; ring

theorem pairKernel_natCast (l₁ l₂ : ℝ) (n : ℕ) : pairKernel l₁ l₂ n = 0 := by
  simp [pairKernel, sinExp_natCast]

theorem differentiableAt_pairMellin {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₂ : 0 < l₂) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (pairMellin l₁ l₂) s := by
  unfold pairMellin
  exact ((differentiableAt_const _).mul (differentiableAt_sinMellin h₁ hs)).sub
    ((differentiableAt_const _).mul (differentiableAt_sinMellin h₂ hs))

theorem continuous_pairKernel (l₁ l₂ : ℝ) : Continuous (pairKernel l₁ l₂) := by
  unfold pairKernel sinExp; fun_prop

/-- Vertical decay of `Γ(s) B_λ(s)`. -/
theorem exists_norm_sinMellin_le {lam : ℝ} (hlam : 0 < lam) (σ₁ σ₂ : ℝ) :
    ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 1 ≤ |s.im| →
      ‖sinMellin lam s‖ ≤ K * |s.im| ^ N *
        Real.exp (-((Real.pi / 2 - Real.pi ^ 2 / (2 * lam)) * |s.im|)) := by
  obtain ⟨C, N, hC, hΓ⟩ := exists_sharp_bound_norm_Gamma_strip σ₁ σ₂
  set b : ℝ := ‖kp lam‖ with hb
  have hb0 : 0 < b := norm_pos_iff.mpr (kp_ne_zero hlam)
  refine ⟨C * (b ^ (-σ₂) + b ^ (-σ₁)), N, by positivity, fun s h1 h2 ht => ?_⟩
  have hB : ‖sinPair lam s‖ ≤ (b ^ (-σ₂) + b ^ (-σ₁)) *
      Real.exp (Real.pi ^ 2 / (2 * lam) * |s.im|) := by
    refine (norm_sinPair_le hlam s).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    exact rpow_le_add_of_mem hb0 (by linarith) (by linarith)
  unfold sinMellin
  rw [norm_mul]
  calc ‖Complex.Gamma s‖ * ‖sinPair lam s‖
      ≤ (C * |s.im| ^ N * Real.exp (-(Real.pi * |s.im| / 2))) *
          ((b ^ (-σ₂) + b ^ (-σ₁)) * Real.exp (Real.pi ^ 2 / (2 * lam) * |s.im|)) :=
        mul_le_mul (hΓ s h1 h2 ht) hB (norm_nonneg _) (by positivity)
    _ = C * (b ^ (-σ₂) + b ^ (-σ₁)) * |s.im| ^ N *
          (Real.exp (-(Real.pi * |s.im| / 2)) * Real.exp (Real.pi ^ 2 / (2 * lam) * |s.im|)) := by
        ring
    _ = _ := by rw [← Real.exp_add]; ring_nf

/-- Vertical decay of `Ψ₀` at the common rate `π/2 - π²/(2L)`, `L ≤ λ₁, λ₂`. -/
theorem exists_norm_pairMellin_le {L l₁ l₂ : ℝ} (hL : 0 < L) (h₁ : L ≤ l₁) (h₂ : L ≤ l₂)
    (σ₁ σ₂ : ℝ) :
    ∃ K : ℝ, ∃ N : ℕ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 1 ≤ |s.im| →
      ‖pairMellin l₁ l₂ s‖ ≤ K * |s.im| ^ N *
        Real.exp (-((Real.pi / 2 - Real.pi ^ 2 / (2 * L)) * |s.im|)) := by
  obtain ⟨K₁, N₁, hK₁0, hK₁⟩ := exists_norm_sinMellin_le (lam := l₁) (by linarith) σ₁ σ₂
  obtain ⟨K₂, N₂, hK₂0, hK₂⟩ := exists_norm_sinMellin_le (lam := l₂) (by linarith) σ₁ σ₂
  refine ⟨‖sinMellin l₂ 1‖ * K₁ + ‖sinMellin l₁ 1‖ * K₂, N₁ + N₂, fun s h1 h2 ht => ?_⟩
  set t : ℝ := |s.im|
  have hrate : ∀ l : ℝ, L ≤ l → Real.exp (-((Real.pi / 2 - Real.pi ^ 2 / (2 * l)) * t)) ≤
      Real.exp (-((Real.pi / 2 - Real.pi ^ 2 / (2 * L)) * t)) := by
    intro l hl
    rw [Real.exp_le_exp]
    have : Real.pi ^ 2 / (2 * l) ≤ Real.pi ^ 2 / (2 * L) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have ht0 : 0 ≤ t := abs_nonneg _
    nlinarith
  have hN1 : t ^ N₁ ≤ t ^ (N₁ + N₂) := pow_le_pow_right₀ ht (by omega)
  have hN2 : t ^ N₂ ≤ t ^ (N₁ + N₂) := pow_le_pow_right₀ ht (by omega)
  set E := Real.exp (-((Real.pi / 2 - Real.pi ^ 2 / (2 * L)) * t))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hb1 : ‖sinMellin l₁ s‖ ≤ K₁ * t ^ (N₁ + N₂) * E :=
    (hK₁ s h1 h2 ht).trans (mul_le_mul (mul_le_mul_of_nonneg_left hN1 hK₁0) (hrate l₁ h₁)
      (Real.exp_pos _).le (by positivity))
  have hb2 : ‖sinMellin l₂ s‖ ≤ K₂ * t ^ (N₁ + N₂) * E :=
    (hK₂ s h1 h2 ht).trans (mul_le_mul (mul_le_mul_of_nonneg_left hN2 hK₂0) (hrate l₂ h₂)
      (Real.exp_pos _).le (by positivity))
  unfold pairMellin
  calc ‖sinMellin l₂ 1 * sinMellin l₁ s - sinMellin l₁ 1 * sinMellin l₂ s‖
      ≤ ‖sinMellin l₂ 1‖ * ‖sinMellin l₁ s‖ + ‖sinMellin l₁ 1‖ * ‖sinMellin l₂ s‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
    _ ≤ ‖sinMellin l₂ 1‖ * (K₁ * t ^ (N₁ + N₂) * E) + ‖sinMellin l₁ 1‖ * (K₂ * t ^ (N₁ + N₂) * E) := by
        gcongr
    _ = _ := by ring

theorem exists_norm_pairMellin_le_inv {L l₁ l₂ : ℝ} (hL : Real.pi < L) (h₁ : L ≤ l₁) (h₂ : L ≤ l₂)
    (σ₁ σ₂ : ℝ) :
    ∃ M T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
      ‖pairMellin l₁ l₂ s‖ ≤ M * (1 + s.im ^ 2)⁻¹ := by
  obtain ⟨K, N, hK⟩ := exists_norm_pairMellin_le (Real.pi_pos.trans hL) h₁ h₂ σ₁ σ₂
  obtain ⟨M, hM⟩ := exists_pow_mul_exp_neg_le (decay_pos hL) N
  refine ⟨|K| * M, 1, fun s h1 h2 ht => ?_⟩
  refine (hK s h1 h2 ht).trans ?_
  calc K * |s.im| ^ N * Real.exp (-((Real.pi / 2 - Real.pi ^ 2 / (2 * L)) * |s.im|))
      ≤ |K| * (|s.im| ^ N * Real.exp (-((Real.pi / 2 - Real.pi ^ 2 / (2 * L)) * |s.im|))) := by
        rw [← mul_assoc]; gcongr; exact le_abs_self K
    _ ≤ |K| * (M * (1 + s.im ^ 2)⁻¹) := mul_le_mul_of_nonneg_left (hM _ ht) (abs_nonneg K)
    _ = _ := by ring

theorem exists_norm_zeta_mul_pairMellin_le_inv {L l₁ l₂ : ℝ} (hL : Real.pi < L) (h₁ : L ≤ l₁)
    (h₂ : L ≤ l₂) {σ₁ σ₂ : ℝ} (hσ₁ : 1 / 4 ≤ σ₁) {k : ℕ} (hk : 1 ≤ k) :
    ∃ M T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
      ‖riemannZeta s * pairMellin l₁ l₂ s * (k : ℂ) ^ (-s)‖ ≤ M * (1 + s.im ^ 2)⁻¹ := by
  obtain ⟨K, N, hK⟩ := exists_norm_pairMellin_le (Real.pi_pos.trans hL) h₁ h₂ σ₁ σ₂
  obtain ⟨M, hM⟩ := exists_pow_mul_exp_neg_le (decay_pos hL) (N + 1)
  refine ⟨10 * |K| * M, 2, fun s h1 h2 ht => ?_⟩
  have ht1 : 1 ≤ |s.im| := by linarith
  have hz : ‖riemannZeta s‖ ≤ 10 * |s.im| := by
    have := RHTower.norm_riemannZeta_le_quarter (by linarith) ht
    linarith
  have hkk : ‖(k : ℂ) ^ (-s)‖ ≤ 1 := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    rw [show (k : ℂ) = ((k : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hk0, Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk) (by linarith)
  set E := Real.exp (-((Real.pi / 2 - Real.pi ^ 2 / (2 * L)) * |s.im|))
  have hΨ := (hK s h1 h2 ht1).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)) (Real.exp_pos _).le)
  rw [norm_mul, norm_mul]
  calc ‖riemannZeta s‖ * ‖pairMellin l₁ l₂ s‖ * ‖(k : ℂ) ^ (-s)‖
      ≤ (10 * |s.im|) * (|K| * |s.im| ^ N * E) * 1 := by gcongr
    _ = 10 * |K| * (|s.im| ^ (N + 1) * E) := by ring
    _ ≤ 10 * |K| * (M * (1 + s.im ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (hM _ ht1) (by positivity)
    _ = _ := by ring

theorem integrableOn_sinExp_cpow {lam : ℝ} (hlam : 0 < lam) {v : ℂ} (hv : 0 < v.re) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (v - 1) * ((sinExp lam y : ℝ) : ℂ)) (Ioi 0) := by
  have hp := HTGeometry.integrableOn_complexRateGammaIntegrand hv
    (show 0 < (kp lam).re by rw [kp_re]; exact hlam)
  have hm := HTGeometry.integrableOn_complexRateGammaIntegrand hv
    (show 0 < (km lam).re by rw [km_re]; exact hlam)
  refine IntegrableOn.congr_fun ((hp.sub hm).div_const (2 * I)) (fun y _ => ?_) measurableSet_Ioi
  rw [Pi.sub_apply, HTGeometry.complexRateGammaIntegrand, HTGeometry.complexRateGammaIntegrand,
    sinExp_eq]
  ring

theorem mellinConvergent_pairKernel {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₂ : 0 < l₂) {s : ℂ}
    (hs : 0 < s.re) : MellinConvergent (pairKernel l₁ l₂) s := by
  have h := ((integrableOn_sinExp_cpow h₁ hs).const_mul (sinMellin l₂ 1)).sub
    ((integrableOn_sinExp_cpow h₂ hs).const_mul (sinMellin l₁ 1))
  refine IntegrableOn.congr_fun h (fun y _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, smul_eq_mul, pairKernel]
  ring

theorem mellin_pairKernel {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₂ : 0 < l₂) {s : ℂ} (hs : 0 < s.re) :
    mellin (pairKernel l₁ l₂) s = pairMellin l₁ l₂ s := by
  have hc₁ := integrableOn_sinExp_cpow h₁ hs
  have hc₂ := integrableOn_sinExp_cpow h₂ hs
  unfold mellin pairMellin
  rw [← integral_sinExp_cpow h₁ hs, ← integral_sinExp_cpow h₂ hs, ← integral_const_mul,
    ← integral_const_mul, ← integral_sub (hc₁.const_mul _) (hc₂.const_mul _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  simp only [smul_eq_mul, pairKernel]
  ring

/-- Mellin inversion on `Re s = 2`. -/
theorem integral_pairMellin_two_mul_cpow {L l₁ l₂ : ℝ} (hL : Real.pi < L) (h₁ : L ≤ l₁)
    (h₂ : L ≤ l₂) {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ, pairMellin l₁ l₂ (2 + t * I) * (x : ℂ) ^ (-(2 + t * I)) =
      2 * Real.pi * pairKernel l₁ l₂ x := by
  have hl₁ : 0 < l₁ := by linarith [Real.pi_pos]
  have hl₂ : 0 < l₂ := by linarith [Real.pi_pos]
  have hconv := mellinConvergent_pairKernel hl₁ hl₂ (s := ((2 : ℝ) : ℂ)) (by norm_num)
  have hline : ∀ t : ℝ, mellin (pairKernel l₁ l₂) ((2 : ℝ) + t * I) =
      pairMellin l₁ l₂ ((2 : ℝ) + t * I) := fun t => mellin_pairKernel hl₁ hl₂ (by simp)
  obtain ⟨M, T₀, hM⟩ := exists_norm_pairMellin_le_inv hL h₁ h₂ 2 2
  have hvi : VerticalIntegrable (mellin (pairKernel l₁ l₂)) 2 := by
    have h : Integrable fun t : ℝ => pairMellin l₁ l₂ ((2 : ℝ) + t * I) :=
      integrable_line_of_bound (T₀ := T₀) (C := M)
        (fun t => (differentiableAt_pairMellin hl₁ hl₂ (by simp)).continuousAt)
        (fun t ht => by simpa using hM ((2 : ℝ) + t * I) (by simp) (by simp) (by simpa using ht))
    refine h.congr (Eventually.of_forall fun t => ?_)
    show pairMellin l₁ l₂ ((2 : ℝ) + t * I) = mellin (pairKernel l₁ l₂) ((2 : ℝ) + t * I)
    rw [hline t]
  have hinv := mellinInv_mellin_eq 2 (pairKernel l₁ l₂) hx hconv hvi
    (continuous_pairKernel l₁ l₂).continuousAt
  rw [mellinInv] at hinv
  have heq : ∫ t : ℝ, (x : ℂ) ^ (-((2 : ℝ) + t * I)) • mellin (pairKernel l₁ l₂) ((2 : ℝ) + t * I) =
      ∫ t : ℝ, pairMellin l₁ l₂ (2 + t * I) * (x : ℂ) ^ (-(2 + t * I)) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_eq_mul]
    rw [hline t]
    push_cast
    ring
  rw [heq, Complex.real_smul] at hinv
  have hone : (2 * Real.pi : ℂ) * (((1 / (2 * Real.pi) : ℝ) : ℂ)) = 1 := by
    push_cast; field_simp
  calc ∫ t : ℝ, pairMellin l₁ l₂ (2 + t * I) * (x : ℂ) ^ (-(2 + t * I))
      = (2 * Real.pi : ℂ) * (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, pairMellin l₁ l₂ (2 + t * I) * (x : ℂ) ^ (-(2 + t * I))) := by
        rw [← mul_assoc, hone, one_mul]
    _ = 2 * Real.pi * pairKernel l₁ l₂ x := by rw [hinv]

/-! ## Critical-line integrals -/

/-- `∫ Ψ₀(1/2+it) x^{-1/2-it} dt = 2π ψ₀(x)`. -/
theorem integral_pairMellin_half_mul_cpow {L l₁ l₂ : ℝ} (hL : Real.pi < L) (h₁ : L ≤ l₁)
    (h₂ : L ≤ l₂) {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ, pairMellin l₁ l₂ (1 / 2 + t * I) * (x : ℂ) ^ (-(1 / 2 + t * I)) =
      2 * Real.pi * pairKernel l₁ l₂ x := by
  have hl₁ : 0 < l₁ := by linarith [Real.pi_pos]
  have hl₂ : 0 < l₂ := by linarith [Real.pi_pos]
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set F : ℂ → ℂ := fun s => pairMellin l₁ l₂ s * (x : ℂ) ^ (-s) with hF
  have hdx : ∀ s : ℂ, DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ (-s)) s := fun s =>
    (differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl hx0)
  obtain ⟨M, T₀, hM⟩ := exists_norm_pairMellin_le_inv hL h₁ h₂ (1 / 2) 2
  set Cx : ℝ := x ^ (-(2 : ℝ)) + x ^ (-(1 / 2 : ℝ)) with hCx
  have hxb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → ‖(x : ℂ) ^ (-s)‖ ≤ Cx := by
    intro s h1 h2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]
    exact rpow_le_add_of_mem hx (by linarith) (by linarith)
  have hb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → T₀ ≤ |s.im| →
      ‖F s‖ ≤ (M * Cx) * (1 + s.im ^ 2)⁻¹ := by
    intro s h1 h2 ht
    have hM' := hM s h1 h2 ht
    have hpos : 0 ≤ M * (1 + s.im ^ 2)⁻¹ := (norm_nonneg _).trans hM'
    simp only [hF, norm_mul]
    calc ‖pairMellin l₁ l₂ s‖ * ‖(x : ℂ) ^ (-s)‖ ≤ (M * (1 + s.im ^ 2)⁻¹) * Cx :=
          mul_le_mul hM' (hxb s h1 h2) (norm_nonneg _) hpos
      _ = M * Cx * (1 + s.im ^ 2)⁻¹ := by ring
  have hFc : ContinuousAt F 1 :=
    ((differentiableAt_pairMellin hl₁ hl₂ (by norm_num)).mul (hdx 1)).continuousAt
  have hres : Tendsto (fun s => (s - 1) * F s) (𝓝[≠] 1) (𝓝 0) := by
    have hc : ContinuousAt (fun s : ℂ => (s - 1) * F s) 1 :=
      ((continuousAt_id (x := (1 : ℂ))).sub (continuousAt_const (y := (1 : ℂ)))).mul hFc
    have := hc.tendsto
    simp only [sub_self, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hshift := integral_line_sub_integral_line_eq (F := F) (a := 1 / 2) (b := 2) (p := 1)
    (A := 0) (by norm_num) (by norm_num)
    (fun s h1 _ _ => (differentiableAt_pairMellin hl₁ hl₂ (by linarith)).mul (hdx s)) hres hb
  have h2 := integral_pairMellin_two_mul_cpow hL h₁ h₂ hx
  have h2' : ∫ t : ℝ, F ((2 : ℝ) + t * I) = 2 * Real.pi * pairKernel l₁ l₂ x := by
    rw [← h2]; refine integral_congr_ae (Eventually.of_forall fun t => ?_); simp [hF]
  rw [h2', mul_zero, sub_eq_zero] at hshift
  rw [hshift]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp [hF]

/-- `∫ ζ(1/2+it) Ψ₀(1/2+it) k^{-1/2-it} dt = 0`. -/
theorem integral_zeta_mul_pairMellin_half {L l₁ l₂ : ℝ} (hL : Real.pi < L) (h₁ : L ≤ l₁)
    (h₂ : L ≤ l₂) {k : ℕ} (hk : 1 ≤ k) :
    ∫ t : ℝ, riemannZeta (1 / 2 + t * I) * pairMellin l₁ l₂ (1 / 2 + t * I) *
      (k : ℂ) ^ (-(1 / 2 + t * I)) = 0 := by
  have hl₁ : 0 < l₁ := by linarith [Real.pi_pos]
  have hl₂ : 0 < l₂ := by linarith [Real.pi_pos]
  set F : ℂ → ℂ := fun s => riemannZeta s * pairMellin l₁ l₂ s * (k : ℂ) ^ (-s) with hF
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hdiffk : ∀ s : ℂ, DifferentiableAt ℂ (fun s : ℂ => (k : ℂ) ^ (-s)) s := fun s =>
    (differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl hk0)
  obtain ⟨M, T₀, hM⟩ := exists_norm_zeta_mul_pairMellin_le_inv hL h₁ h₂ (σ₁ := 1 / 2) (σ₂ := 2)
    (by norm_num) hk
  have hshift := integral_line_sub_integral_line_eq (F := F) (a := 1 / 2) (b := 2) (p := 1) (A := 0)
    (by norm_num) (by norm_num) (fun s h1 _ hs1 => ((differentiableAt_riemannZeta hs1).mul
      (differentiableAt_pairMellin hl₁ hl₂ (by linarith))).mul (hdiffk s)) ?_ (T₀ := T₀) (C := M) hM
  rotate_left
  · have hΨc : ContinuousAt (pairMellin l₁ l₂) 1 :=
      (differentiableAt_pairMellin hl₁ hl₂ (by norm_num)).continuousAt
    have hkc : ContinuousAt (fun s : ℂ => (k : ℂ) ^ (-s)) 1 := (hdiffk 1).continuousAt
    have hlim := (riemannZeta_residue_one.mul (hΨc.tendsto.mono_left nhdsWithin_le_nhds)).mul
      (hkc.tendsto.mono_left nhdsWithin_le_nhds)
    rw [pairMellin_one, mul_zero, zero_mul] at hlim
    refine hlim.congr' (Eventually.of_forall fun s => ?_)
    simp only [hF]; ring
  have h2 : ∫ t : ℝ, F ((2 : ℝ) + t * I) = 0 := by
    have hterm : ∀ n : ℕ, ∫ t : ℝ, pairMellin l₁ l₂ (2 + t * I) *
        (((n + 1) * k : ℕ) : ℂ) ^ (-(2 + t * I)) = 0 := by
      intro n
      have hpos : (0 : ℝ) < ((n + 1) * k : ℕ) := by
        have : 0 < (n + 1) * k := Nat.mul_pos (Nat.succ_pos n) (by omega)
        exact_mod_cast this
      have h := integral_pairMellin_two_mul_cpow hL h₁ h₂ hpos
      rw [show (((((n + 1) * k : ℕ) : ℝ)) : ℂ) = (((n + 1) * k : ℕ) : ℂ) by push_cast; ring] at h
      rw [h]
      have := pairKernel_natCast l₁ l₂ ((n + 1) * k)
      rw [this, mul_zero]
    set G : ℕ → ℝ → ℂ := fun n t => pairMellin l₁ l₂ (2 + t * I) *
        (((n + 1) * k : ℕ) : ℂ) ^ (-(2 + t * I)) with hG
    obtain ⟨M₂, T₂, hM₂⟩ := exists_norm_pairMellin_le_inv hL h₁ h₂ 2 2
    have hΨint : Integrable fun t : ℝ => pairMellin l₁ l₂ (2 + t * I) := by
      have h : Integrable fun t : ℝ => pairMellin l₁ l₂ ((2 : ℝ) + t * I) :=
        integrable_line_of_bound (T₀ := T₂) (C := M₂)
          (fun t => (differentiableAt_pairMellin hl₁ hl₂ (by simp)).continuousAt)
          (fun t ht => by simpa using hM₂ ((2 : ℝ) + t * I) (by simp) (by simp) (by simpa using ht))
      simpa using h
    have hnorm : ∀ n : ℕ, ∀ t : ℝ, ‖G n t‖ =
        ‖pairMellin l₁ l₂ (2 + t * I)‖ * ((((n + 1) * k : ℕ) : ℝ) ^ (-(2 : ℝ))) := by
      intro n t
      have hpos : (0 : ℝ) < ((n + 1) * k : ℕ) := by
        have : 0 < (n + 1) * k := Nat.mul_pos (Nat.succ_pos n) (by omega)
        exact_mod_cast this
      simp only [hG, norm_mul]
      rw [show (((n + 1) * k : ℕ) : ℂ) = (((((n + 1) * k : ℕ) : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hpos]
      simp
    have hGint : ∀ n : ℕ, Integrable (G n) := by
      intro n
      refine (hΨint.norm.mul_const ((((n + 1) * k : ℕ) : ℝ) ^ (-(2 : ℝ)))).mono'
        ?_ (Eventually.of_forall fun t => (hnorm n t).le)
      have hcont : Continuous fun t : ℝ => (((n + 1) * k : ℕ) : ℂ) ^ (-(2 + t * I)) := by
        refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
        exact_mod_cast (Nat.mul_pos (Nat.succ_pos n) (by omega)).ne'
      exact hΨint.aestronglyMeasurable.mul hcont.aestronglyMeasurable
    have hsum : Summable fun n : ℕ => ∫ t : ℝ, ‖G n t‖ := by
      have hs : Summable fun n : ℕ => (∫ t : ℝ, ‖pairMellin l₁ l₂ (2 + t * I)‖) *
          ((((n + 1) * k : ℕ) : ℝ) ^ (-(2 : ℝ))) := by
        refine Summable.mul_left _ ?_
        have hb := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
        refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hb
        have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hle : (n : ℝ) + 1 ≤ (((n + 1) * k : ℕ) : ℝ) := by
          have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
          push_cast; nlinarith
        calc (((n + 1) * k : ℕ) : ℝ) ^ (-(2 : ℝ)) ≤ ((n : ℝ) + 1) ^ (-(2 : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos hn hle (by norm_num)
          _ = 1 / |(n : ℝ) + 1| ^ (2 : ℝ) := by
              rw [abs_of_pos hn, Real.rpow_neg hn.le, one_div]
      refine hs.congr fun n => ?_
      simp_rw [hnorm n]
      rw [integral_mul_const]
    have hfub := integral_tsum_of_summable_integral_norm hGint hsum
    have hpoint : ∀ t : ℝ, F ((2 : ℝ) + t * I) = ∑' n : ℕ, G n t := by
      intro t
      have hre : 1 < ((2 : ℝ) + t * I : ℂ).re := by simp
      simp only [hF, hG]
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre, ← tsum_mul_right, ← tsum_mul_right]
      refine tsum_congr fun n => ?_
      have hcast : (((n + 1) * k : ℕ) : ℂ) = ((n + 1 : ℕ) : ℂ) * (k : ℂ) := by push_cast; ring
      rw [hcast, Complex.natCast_mul_natCast_cpow]
      simp only [Complex.cpow_neg, one_div]
      push_cast
      ring_nf
    have hterm' : ∀ n : ℕ, ∫ t : ℝ, G n t = 0 := fun n => hterm n
    rw [integral_congr_ae (Eventually.of_forall hpoint), ← hfub, tsum_congr hterm', tsum_zero]
  push_cast at hshift h2
  rw [h2, mul_zero, zero_sub, neg_eq_zero] at hshift
  simpa [hF] using hshift

/-! ## Dilated kernels -/

theorem memLp_kernel_real (ha0 : 0 < a) : MemLp (kernel a) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hm : AEStronglyMeasurable (kernel a) (volume.restrict (Ioi (0 : ℝ))) :=
    (continuous_kernel ha0).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  refine (integrableOn_kernel ha0).mono' (hm.pow 2) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq]
  exact mul_le_of_le_one_left (kernel_pos a t).le (kernel_le_one ht0)

theorem memLp_kernelDilate (ha0 : 0 < a) {x : ℝ} (hx : 0 < x) :
    MemLp (fun t => (kernel a (x * t) : ℂ)) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (RHTower.chronological_memLp_dilate (memLp_kernel_real ha0)
    (continuous_kernel ha0).continuousOn hx).ofReal

/-- `t ↦ f_a(xt)` as a vector of `L²((0,∞))`. -/
def kernelDilateL2 (ha0 : 0 < a) {x : ℝ} (hx : 0 < x) : HalfLineL2 :=
  (memLp_kernelDilate ha0 hx).toLp fun t => (kernel a (x * t) : ℂ)

theorem halfDensityPullback_comp_mul (g : ℝ → ℂ) {x : ℝ} (hx : 0 < x) (y : ℝ) :
    halfDensityPullback (fun t => g (x * t)) y =
      ((Real.sqrt x)⁻¹ : ℝ) * halfDensityPullback g (y + Real.log x) := by
  unfold halfDensityPullback
  rw [Real.exp_add, Real.exp_log hx, Real.sqrt_mul (Real.exp_pos y).le, mul_comm (Real.exp y) x]
  have hs : (Real.sqrt x : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hx).ne'
  push_cast
  field_simp

theorem integrable_halfDensityPullback_kernelDilate (ha0 : 0 < a) {x : ℝ} (hx : 0 < x) :
    Integrable (halfDensityPullback fun t => (kernel a (x * t) : ℂ)) := by
  have h := (integrable_halfDensityPullback_kernel ha0).comp_add_right (Real.log x)
  have h' := h.const_mul (((Real.sqrt x)⁻¹ : ℝ) : ℂ)
  refine h'.congr (Eventually.of_forall fun y => ?_)
  rw [halfDensityPullback_comp_mul (fun t => (kernel a t : ℂ)) hx y]

theorem halfLineMellinUnitary_kernelDilateL2 (ha0 : 0 < a) {x : ℝ} (hx : 0 < x) :
    (halfLineMellinUnitary (kernelDilateL2 ha0 hx) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (x : ℂ) ^ (-mellinLinePoint ξ) * mellinFactor a (mellinLinePoint ξ) := by
  have h := halfLineMellinUnitary_ae_eq_mellin (kernelDilateL2 ha0 hx)
    (fun t => (kernel a (x * t) : ℂ)) (MemLp.coeFn_toLp _)
    (integrable_halfDensityPullback_kernelDilate ha0 hx)
  filter_upwards [h] with ξ hξ
  rw [hξ]
  have hm := mellin_comp_mul_left (fun t => (kernel a t : ℂ)) (mellinLinePoint ξ) hx
  change mellin (fun t => (kernel a (x * t) : ℂ)) (mellinLinePoint ξ) = _
  rw [hm, mellin_kernel ha0 (by rw [mellinLinePoint_re]; norm_num), smul_eq_mul]

/-! ## The pole-free separator vector -/

theorem conj_conj_div_mul {Ψ F z : ℂ} (hF : F ≠ 0) : conj (conj (Ψ / F)) * (F * z) = Ψ * z := by
  rw [Complex.conj_conj]; field_simp

theorem continuous_conj_pairMellin_div {l₁ l₂ : ℝ} (h₁ : 0 < l₁) (h₂ : 0 < l₂) (ha0 : 0 < a) :
    Continuous fun ξ : ℝ =>
      conj (pairMellin l₁ l₂ (mellinLinePoint ξ) / mellinFactor a (mellinLinePoint ξ)) := by
  rw [continuous_iff_continuousAt]
  intro ξ
  have hΨ : ContinuousAt (pairMellin l₁ l₂) (mellinLinePoint ξ) :=
    (differentiableAt_pairMellin h₁ h₂ (by rw [mellinLinePoint_re]; norm_num)).continuousAt
  have hF : ContinuousAt (mellinFactor a) (mellinLinePoint ξ) :=
    (analyticAt_mellinFactor ha0 (by rw [mellinLinePoint_re]; norm_num)).continuousAt
  have hc := continuous_mellinLinePoint.continuousAt (x := ξ)
  exact (Complex.continuous_conj.continuousAt).comp
    ((hΨ.comp hc).div (hF.comp hc) (mellinFactor_ne_zero ha0 ξ))

theorem pairKernel_half {L : ℝ} (hL : 4 ≤ L) : pairKernel L (2 * L) (1 / 2) ≠ 0 := by
  have hs : ∀ l : ℝ, sinExp l (1 / 2) = Real.exp (-(l / 2)) := by
    intro l
    unfold sinExp
    rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two, one_mul]
    ring_nf
  unfold pairKernel
  rw [sinMellin_one, sinMellin_one, hs, hs]
  set E1 := Real.exp (-(L / 2))
  set E2 := Real.exp (-(2 * L / 2))
  have hval : ((Real.pi : ℂ) / (((2 * L : ℝ) : ℂ) ^ 2 + (Real.pi : ℂ) ^ 2)) * (E1 : ℂ) -
      ((Real.pi : ℂ) / ((L : ℂ) ^ 2 + (Real.pi : ℂ) ^ 2)) * (E2 : ℂ) =
      ((Real.pi / ((2 * L) ^ 2 + Real.pi ^ 2) * E1 - Real.pi / (L ^ 2 + Real.pi ^ 2) * E2 : ℝ) :
        ℂ) := by push_cast; ring
  rw [hval]
  refine Complex.ofReal_ne_zero.mpr (ne_of_gt ?_)
  have hπ := Real.pi_pos
  have hE : E2 = E1 * E1 := by
    simp only [E1, E2]; rw [← Real.exp_add]; ring_nf
  have hE1 : 0 < E1 := Real.exp_pos _
  have h5 : 5 * E1 ≤ 1 := by
    have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ L / 2 by linarith)
    have hinv : E1 * Real.exp (L / 2) = 1 := by simp only [E1]; rw [← Real.exp_add]; simp
    nlinarith
  rw [sub_pos, hE, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  have key : E1 * (4 * L ^ 2 + Real.pi ^ 2) < (L ^ 2 + Real.pi ^ 2) := by
    nlinarith [sq_nonneg L]
  nlinarith [mul_pos hπ hE1, mul_pos (mul_pos hπ hE1) hE1]

/-- **For `a > 1` the integer dilates of `D_a` are not dense in `L²(0,∞)`.** -/
theorem defectDilateL2_span_closure_ne_top {a : ℝ} (ha : 1 < a) :
    (Submodule.span ℂ (Set.range (defectDilateL2 (a := a) (by linarith)))).topologicalClosure ≠ ⊤ := by
  have ha0 : 0 < a := by linarith
  set L : ℝ := Real.pi * a / (a - 1) + 4 with hLdef
  have ha1 : 0 < a - 1 := by linarith
  have hq : 0 < Real.pi * a / (a - 1) := by positivity
  have hL4 : 4 ≤ L := by linarith
  have hL : Real.pi < L := by linarith [Real.pi_lt_four]
  have hL0 : 0 < L := by linarith
  have hrate : 0 < (Real.pi / 2 - Real.pi ^ 2 / (2 * L)) - Real.pi / (2 * a) := by
    have h0 := separator_rate_pos ha
    have hle : Real.pi ^ 2 / (2 * L) ≤ Real.pi ^ 2 / (2 * (Real.pi * a / (a - 1) + Real.pi)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith [Real.pi_lt_four])
    linarith
  set l₁ : ℝ := L
  set l₂ : ℝ := 2 * L
  have h₁ : L ≤ l₁ := le_rfl
  have h₂ : L ≤ l₂ := by simp only [l₂]; linarith
  have hl₁ : 0 < l₁ := hL0
  have hl₂ : 0 < l₂ := by simp only [l₂]; linarith
  obtain ⟨K, N, hK⟩ := exists_norm_pairMellin_le (by linarith : (0 : ℝ) < L) h₁ h₂ (1 / 2) (1 / 2)
  have hmem := memLp_conj_div_mellinFactor ha0 hrate
    (continuous_conj_pairMellin_div hl₁ hl₂ ha0) le_rfl
    (fun s hs ht => hK s hs.ge hs.le ht)
  set g := halfLineMellinUnitary.symm (hmem.toLp _) with hg
  set K' := Submodule.span ℂ (Set.range (defectDilateL2 (a := a) ha0)) with hK'
  have hgK : g ∈ K'ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction (p := fun u _ => ⟪u, g⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨k, rfl⟩
      rw [inner_eq_zero_symm, inner_separator_eq (u := g) hmem
        (halfLineMellinUnitary_defectDilateL2 ha0 k) rfl]
      have hpt : ∀ ξ : ℝ, conj (conj (pairMellin l₁ l₂ (mellinLinePoint ξ) /
          mellinFactor a (mellinLinePoint ξ))) *
          -(((k + 1 : ℕ) : ℂ) ^ (-mellinLinePoint ξ) * mellinFactor a (mellinLinePoint ξ) *
            riemannZeta (mellinLinePoint ξ)) =
          -(riemannZeta (mellinLinePoint ξ) * pairMellin l₁ l₂ (mellinLinePoint ξ) *
            ((k + 1 : ℕ) : ℂ) ^ (-mellinLinePoint ξ)) := fun ξ => by
        have h := conj_conj_div_mul (Ψ := pairMellin l₁ l₂ (mellinLinePoint ξ))
          (z := -(((k + 1 : ℕ) : ℂ) ^ (-mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)))
          (mellinFactor_ne_zero ha0 ξ)
        rw [show mellinFactor a (mellinLinePoint ξ) *
            -(((k + 1 : ℕ) : ℂ) ^ (-mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)) =
            -(((k + 1 : ℕ) : ℂ) ^ (-mellinLinePoint ξ) * mellinFactor a (mellinLinePoint ξ) *
              riemannZeta (mellinLinePoint ξ)) by ring] at h
        rw [h]; ring
      rw [integral_congr_ae (Eventually.of_forall hpt), integral_neg,
        integral_comp_mellinLinePoint (fun s => riemannZeta s * pairMellin l₁ l₂ s *
          ((k + 1 : ℕ) : ℂ) ^ (-s)),
        integral_zeta_mul_pairMellin_half hL h₁ h₂ (Nat.le_add_left 1 k)]
      simp
    · exact inner_zero_left _
    · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
    · intro r x _ hx; rw [inner_smul_left, hx, mul_zero]
  intro htop
  have hx : (0 : ℝ) < 1 / 2 := by norm_num
  have hmemv : kernelDilateL2 ha0 hx ∈ K'.topologicalClosure := by rw [htop]; trivial
  have hclos : K'.topologicalClosure ≤ K'ᗮᗮ :=
    K'.topologicalClosure_minimal K'.le_orthogonal_orthogonal K'ᗮ.isClosed_orthogonal
  have h0 := (Submodule.mem_orthogonal _ _).mp (hclos hmemv) g hgK
  rw [inner_separator_eq (u := g) hmem (halfLineMellinUnitary_kernelDilateL2 ha0 hx) rfl] at h0
  have hpt : ∀ ξ : ℝ, conj (conj (pairMellin l₁ l₂ (mellinLinePoint ξ) /
      mellinFactor a (mellinLinePoint ξ))) *
      (((1 / 2 : ℝ) : ℂ) ^ (-mellinLinePoint ξ) * mellinFactor a (mellinLinePoint ξ)) =
      pairMellin l₁ l₂ (mellinLinePoint ξ) * ((1 / 2 : ℝ) : ℂ) ^ (-mellinLinePoint ξ) := fun ξ => by
    have h := conj_conj_div_mul (Ψ := pairMellin l₁ l₂ (mellinLinePoint ξ))
      (z := ((1 / 2 : ℝ) : ℂ) ^ (-mellinLinePoint ξ)) (mellinFactor_ne_zero ha0 ξ)
    rw [mul_comm (mellinFactor a _)] at h
    exact h
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_comp_mellinLinePoint (fun s => pairMellin l₁ l₂ s * ((1 / 2 : ℝ) : ℂ) ^ (-s)),
    integral_pairMellin_half_mul_cpow hL h₁ h₂ hx, Complex.real_smul] at h0
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hψ : pairKernel l₁ l₂ (1 / 2) = 0 := by
    have : ((2 * Real.pi)⁻¹ : ℝ) * (2 * Real.pi) = (1 : ℂ) := by push_cast; field_simp
    calc pairKernel l₁ l₂ (1 / 2) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
          (2 * ↑Real.pi * pairKernel l₁ l₂ (1 / 2)) := by
          rw [← mul_assoc, this, one_mul]
      _ = 0 := h0
  exact pairKernel_half hL4 hψ

end RHTower.StretchedBose
