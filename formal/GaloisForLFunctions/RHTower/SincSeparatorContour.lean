import GaloisForLFunctions.RHTower.SincSeparatorMellin
import GaloisForLFunctions.RHTower.ZetaStripPolynomialBound
import GaloisForLFunctions.HTGeometry.VerticalStripResidueShift
import Mathlib.Analysis.MellinInversion

/-!
# Contour shifts for the sinc separator

Let `λ > π`, let `ζ(ρ) = 0` with `1/2 < Re ρ < 1`, and choose `c` so that `Ψ(1) = 0`, where `Ψ` is
the separator Mellin function of `SincSeparatorMellin`.

* `integral_sepMellin_two_mul_cpow`: `∫ Ψ(2+it) x^{-(2+it)} dt = 2π ψ(x)` (Mellin inversion).
* `integral_sepMellin_half`: `∫ Ψ(1/2+it) dt = 2π`.  The shift to `Re s = 2` crosses the simple
  pole at `ρ` (residue `-1`), and `ψ(1) = 0`.
* `integral_zeta_mul_sepMellin_half`: `∫ ζ(1/2+it) Ψ(1/2+it) k^{-1/2-it} dt = 0` for every `k ≥ 1`.
  Both singularities of `ζΨ` in `1/2 ≤ Re s ≤ 2` are removable: at `ρ` because `ζ(ρ) = 0`, at `1`
  because `Ψ(1) = 0`.  On `Re s = 2` the Dirichlet series of `ζ` turns the integral into
  `2π Σ_n ψ(nk) = 0`.
-/

open MeasureTheory Set Filter Complex
open scoped Topology

noncomputable section

namespace RHTower.SincSeparator

open GaloisForLFunctions.HTGeometry
open HTGeometry

variable {lam : ℝ}

/-- The decay rate `δ = π/2 - π²/(2λ)`, positive for `λ > π`. -/
theorem decay_pos (hlam : Real.pi < lam) : 0 < Real.pi / 2 - Real.pi ^ 2 / (2 * lam) := by
  have hl : 0 < lam := Real.pi_pos.trans hlam
  rw [sub_pos, div_lt_div_iff₀ (by linarith) (by norm_num)]
  nlinarith [Real.pi_pos]

/-- On a vertical strip, `|Ψ(s)| ≤ M (1 + t²)⁻¹` far from the real axis. -/
theorem exists_norm_sepMellin_le_inv (hlam : Real.pi < lam) (ρ c : ℂ) (σ₁ σ₂ : ℝ) :
    ∃ M T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
      ‖sepMellin lam ρ c s‖ ≤ M * (1 + s.im ^ 2)⁻¹ := by
  have hl : 0 < lam := Real.pi_pos.trans hlam
  obtain ⟨K, N, hK⟩ := exists_norm_sepMellin_le hl ρ c σ₁ σ₂
  obtain ⟨M, hM⟩ := exists_pow_mul_exp_neg_le (decay_pos hlam) N
  refine ⟨|K| * M, |ρ.im| + 2, fun s h1 h2 ht => ?_⟩
  have ht1 : 1 ≤ |s.im| := by linarith [abs_nonneg ρ.im]
  refine (hK s h1 h2 ht).trans ?_
  have hb := hM s.im ht1
  calc K * |s.im| ^ N * Real.exp (-((Real.pi / 2 - Real.pi ^ 2 / (2 * lam)) * |s.im|))
      ≤ |K| * (|s.im| ^ N * Real.exp (-((Real.pi / 2 - Real.pi ^ 2 / (2 * lam)) * |s.im|))) := by
        rw [← mul_assoc]; gcongr; exact le_abs_self K
    _ ≤ |K| * (M * (1 + s.im ^ 2)⁻¹) := by gcongr
    _ = _ := by ring

/-- With a zeta factor and a Dirichlet monomial: `|ζ(s) Ψ(s) k^{-s}| ≤ M (1 + t²)⁻¹`. -/
theorem exists_norm_zeta_mul_sepMellin_le_inv (hlam : Real.pi < lam) (ρ c : ℂ) {σ₁ σ₂ : ℝ}
    (hσ₁ : 1 / 4 ≤ σ₁) {k : ℕ} (hk : 1 ≤ k) :
    ∃ M T₀ : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → T₀ ≤ |s.im| →
      ‖riemannZeta s * sepMellin lam ρ c s * (k : ℂ) ^ (-s)‖ ≤ M * (1 + s.im ^ 2)⁻¹ := by
  have hl : 0 < lam := Real.pi_pos.trans hlam
  obtain ⟨K, N, hK⟩ := exists_norm_sepMellin_le hl ρ c σ₁ σ₂
  obtain ⟨M, hM⟩ := exists_pow_mul_exp_neg_le (decay_pos hlam) (N + 1)
  refine ⟨10 * |K| * M, |ρ.im| + 2, fun s h1 h2 ht => ?_⟩
  have ht1 : 1 ≤ |s.im| := by linarith [abs_nonneg ρ.im]
  have ht2 : 2 ≤ |s.im| := by linarith [abs_nonneg ρ.im]
  have hz : ‖riemannZeta s‖ ≤ 10 * |s.im| := by
    have := RHTower.norm_riemannZeta_le_quarter (by linarith) ht2
    linarith
  have hkk : ‖(k : ℂ) ^ (-s)‖ ≤ 1 := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    rw [show (k : ℂ) = ((k : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hk0, Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk) (by linarith)
  set E := Real.exp (-((Real.pi / 2 - Real.pi ^ 2 / (2 * lam)) * |s.im|))
  have hΨ := (hK s h1 h2 ht).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)) (Real.exp_pos _).le)
  rw [norm_mul, norm_mul]
  calc ‖riemannZeta s‖ * ‖sepMellin lam ρ c s‖ * ‖(k : ℂ) ^ (-s)‖
      ≤ (10 * |s.im|) * (|K| * |s.im| ^ N * E) * 1 := by gcongr
    _ = 10 * |K| * (|s.im| ^ (N + 1) * E) := by ring
    _ ≤ 10 * |K| * (M * (1 + s.im ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (hM s.im ht1) (by positivity)
    _ = _ := by ring

theorem continuousAt_sepMellin (hlam : 0 < lam) {ρ c s : ℂ} (hs0 : 0 < s.re)
    (hs : ρ.re - 1 < s.re) (hsρ : s ≠ ρ) : ContinuousAt (sepMellin lam ρ c) s :=
  (differentiableAt_sepMellin hlam hs0 hs hsρ).continuousAt

theorem verticalIntegrable_sepMellin (hlam : Real.pi < lam) (ρ c : ℂ)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ : ρ.re - 1 < σ) (hσρ : σ ≠ ρ.re) :
    Integrable fun t : ℝ => sepMellin lam ρ c (σ + t * I) := by
  have hl : 0 < lam := Real.pi_pos.trans hlam
  obtain ⟨M, T₀, hM⟩ := exists_norm_sepMellin_le_inv hlam ρ c σ σ
  refine integrable_line_of_bound (T₀ := T₀) (C := M) (fun t => ?_) (fun t ht => ?_)
  · refine continuousAt_sepMellin hl (by simpa using hσ0) (by simpa using hσ) fun h => hσρ ?_
    rw [← h]; simp
  · simpa using hM (σ + t * I) (by simp) (by simp) (by simpa using ht)

theorem mellinConvergent_sepKernel (hlam : 0 < lam) {ρ : ℂ} (c : ℂ) {σ : ℝ}
    (hσ : ρ.re + 1 < σ) (hσpos : 0 < σ) : MellinConvergent (sepKernel lam ρ c) σ := by
  set w : ℂ := (σ : ℂ) - ρ - 1 with hw
  have hw0 : 0 < w.re := by simp [hw]; linarith
  have hσ0 : 0 < ((σ : ℂ)).re := by simpa using hσpos
  have hint (v : ℂ) (hv : 0 < v.re) :
      IntegrableOn (fun y : ℝ => (y : ℂ) ^ (v - 1) * ((sinExp lam y : ℝ) : ℂ)) (Ioi 0) := by
    have hp := integrableOn_complexRateGammaIntegrand hv (show 0 < (kp lam).re by rw [kp_re]; exact hlam)
    have hm := integrableOn_complexRateGammaIntegrand hv (show 0 < (km lam).re by rw [km_re]; exact hlam)
    refine IntegrableOn.congr_fun ((hp.sub hm).div_const (2 * I)) (fun y _ => ?_) measurableSet_Ioi
    rw [Pi.sub_apply, complexRateGammaIntegrand, complexRateGammaIntegrand, sinExp_eq]; ring
  have h := ((hint w hw0).const_mul (-(1 / (Real.pi : ℂ)))).add ((hint (σ : ℂ) hσ0).const_mul c)
  refine IntegrableOn.congr_fun h (fun y hy => ?_) measurableSet_Ioi
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show (0 : ℝ) < y from hy))
  have hpow : (y : ℂ) ^ ((σ : ℂ) - 1) * (y : ℂ) ^ (-ρ - 1) = (y : ℂ) ^ (w - 1) := by
    rw [← Complex.cpow_add _ _ hy0, hw]; ring_nf
  simp only [Pi.add_apply, smul_eq_mul, sepKernel]
  linear_combination (1 / (Real.pi : ℂ) * ((sinExp lam y : ℝ) : ℂ)) * hpow

/-- **Mellin inversion on `Re s = 2`:** `∫ Ψ(2+it) x^{-(2+it)} dt = 2π ψ(x)`. -/
theorem integral_sepMellin_two_mul_cpow (hlam : Real.pi < lam) {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (c : ℂ) {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ, sepMellin lam ρ c (2 + t * I) * (x : ℂ) ^ (-(2 + t * I)) =
      2 * Real.pi * sepKernel lam ρ c x := by
  have hl : 0 < lam := Real.pi_pos.trans hlam
  have hconv := mellinConvergent_sepKernel hl c (σ := 2) (by linarith) (by norm_num)
  have hline : ∀ t : ℝ, mellin (sepKernel lam ρ c) ((2 : ℝ) + t * I) =
      sepMellin lam ρ c ((2 : ℝ) + t * I) := by
    intro t
    exact mellin_sepKernel hl hρ0 (by simp; linarith)
  have hvi : VerticalIntegrable (mellin (sepKernel lam ρ c)) 2 := by
    have h := verticalIntegrable_sepMellin hlam ρ c (σ := 2) (by norm_num) (by linarith)
      (by linarith)
    refine h.congr (Eventually.of_forall fun t => ?_)
    show sepMellin lam ρ c ((2 : ℝ) + t * I) = mellin (sepKernel lam ρ c) ((2 : ℝ) + t * I)
    rw [hline t]
  have hinv := mellinInv_mellin_eq 2 (sepKernel lam ρ c) hx hconv hvi
    (continuousAt_sepKernel ρ c hx)
  rw [mellinInv] at hinv
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have heq : ∫ t : ℝ, (x : ℂ) ^ (-((2 : ℝ) + t * I)) • mellin (sepKernel lam ρ c) ((2 : ℝ) + t * I) =
      ∫ t : ℝ, sepMellin lam ρ c (2 + t * I) * (x : ℂ) ^ (-(2 + t * I)) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_eq_mul]
    rw [hline t]
    push_cast
    ring
  rw [heq, Complex.real_smul] at hinv
  have hone : (2 * Real.pi : ℂ) * (((1 / (2 * Real.pi) : ℝ) : ℂ)) = 1 := by
    push_cast; field_simp
  calc ∫ t : ℝ, sepMellin lam ρ c (2 + t * I) * (x : ℂ) ^ (-(2 + t * I))
      = (2 * Real.pi : ℂ) * (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, sepMellin lam ρ c (2 + t * I) * (x : ℂ) ^ (-(2 + t * I))) := by
        rw [← mul_assoc, hone, one_mul]
    _ = 2 * Real.pi * sepKernel lam ρ c x := by rw [hinv]

/-- **The critical-line integral of `Ψ`:** `∫ Ψ(1/2 + it) dt = 2π`. -/
theorem integral_sepMellin_half (hlam : Real.pi < lam) {ρ : ℂ} (hρ1 : 1 / 2 < ρ.re)
    (hρ2 : ρ.re < 1) (c : ℂ) :
    ∫ t : ℝ, sepMellin lam ρ c (1 / 2 + t * I) = 2 * Real.pi := by
  have hl : 0 < lam := Real.pi_pos.trans hlam
  have hρ0 : 0 < ρ.re := by linarith
  obtain ⟨M, T₀, hM⟩ := exists_norm_sepMellin_le_inv hlam ρ c (1 / 2) 2
  have hshift := integral_line_sub_integral_line_eq (F := sepMellin lam ρ c) (a := 1 / 2) (b := 2)
    (p := ρ) (A := -1) hρ1 (by linarith)
    (fun s h1 _ hsρ => differentiableAt_sepMellin hl (by linarith) (by linarith) hsρ)
    (tendsto_sub_mul_sepMellin hl hρ0) (T₀ := T₀) (C := M) hM
  have h2 := integral_sepMellin_two_mul_cpow hlam hρ0 hρ2 c (x := 1) one_pos
  have h1 : sepKernel lam ρ c 1 = 0 := by exact_mod_cast sepKernel_natCast ρ c 1
  rw [h1, mul_zero] at h2
  have h2' : ∫ t : ℝ, sepMellin lam ρ c ((2 : ℝ) + t * I) = 0 := by
    rw [← h2]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp
  push_cast at hshift h2'
  rw [h2'] at hshift
  have : ∫ t : ℝ, sepMellin lam ρ c ((1 / 2 : ℝ) + t * I) = 2 * Real.pi := by
    push_cast; linear_combination -hshift
  simpa using this

/-- **The zeta-weighted critical-line integral vanishes.**  If `ζ(ρ) = 0` and `Ψ(1) = 0`, then
`∫ ζ(1/2+it) Ψ(1/2+it) k^{-1/2-it} dt = 0` for every `k ≥ 1`. -/
theorem integral_zeta_mul_sepMellin_half (hlam : Real.pi < lam) {ρ : ℂ} (hρ1 : 1 / 2 < ρ.re)
    (hρ2 : ρ.re < 1) (hζ : riemannZeta ρ = 0) {c : ℂ} (hc : sepMellin lam ρ c 1 = 0)
    {k : ℕ} (hk : 1 ≤ k) :
    ∫ t : ℝ, riemannZeta (1 / 2 + t * I) * sepMellin lam ρ c (1 / 2 + t * I) *
      (k : ℂ) ^ (-(1 / 2 + t * I)) = 0 := by
  have hl : 0 < lam := Real.pi_pos.trans hlam
  have hρ0 : 0 < ρ.re := by linarith
  set F : ℂ → ℂ := fun s => riemannZeta s * sepMellin lam ρ c s * (k : ℂ) ^ (-s) with hF
  set m : ℝ := (ρ.re + 1) / 2 with hm
  have hm1 : ρ.re < m := by rw [hm]; linarith
  have hm2 : m < 1 := by rw [hm]; linarith
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hdiffk : ∀ s : ℂ, DifferentiableAt ℂ (fun s : ℂ => (k : ℂ) ^ (-s)) s := fun s =>
    (differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl hk0)
  obtain ⟨M₁, T₁, hM₁⟩ := exists_norm_zeta_mul_sepMellin_le_inv hlam ρ c (σ₁ := 1 / 2) (σ₂ := m)
    (by norm_num) hk
  obtain ⟨M₂, T₂, hM₂⟩ := exists_norm_zeta_mul_sepMellin_le_inv hlam ρ c (σ₁ := m) (σ₂ := 2)
    (by linarith) hk
  -- shift from `1/2` to `m` past the removable point `ρ`
  have hshift1 := integral_line_sub_integral_line_eq (F := F) (a := 1 / 2) (b := m) (p := ρ) (A := 0)
    hρ1 hm1 (fun s h1 h2 hsρ => ?_) ?_ (T₀ := T₁) (C := M₁) hM₁
  rotate_left
  · have hs1 : s ≠ 1 := by intro h; rw [h] at h2; simp at h2; linarith
    exact ((differentiableAt_riemannZeta hs1).mul
      (differentiableAt_sepMellin hl (by linarith) (by linarith) hsρ)).mul (hdiffk s)
  · have hζc : ContinuousAt riemannZeta ρ := (differentiableAt_riemannZeta (by
      intro h; rw [h] at hρ2; simp at hρ2)).continuousAt
    have hkc : ContinuousAt (fun s : ℂ => (k : ℂ) ^ (-s)) ρ := (hdiffk ρ).continuousAt
    have hlim := ((hζc.tendsto.mono_left nhdsWithin_le_nhds).mul
      (tendsto_sub_mul_sepMellin hl hρ0 (c := c))).mul (hkc.tendsto.mono_left nhdsWithin_le_nhds)
    rw [hζ, zero_mul, zero_mul] at hlim
    refine hlim.congr' (Eventually.of_forall fun s => ?_)
    simp only [hF]; ring
  -- shift from `m` to `2` past the removable point `1`
  have hshift2 := integral_line_sub_integral_line_eq (F := F) (a := m) (b := 2) (p := 1) (A := 0)
    (by simpa using hm2) (by norm_num) (fun s h1 h2 hs1 => ?_) ?_ (T₀ := T₂) (C := M₂) hM₂
  rotate_left
  · have hsρ : s ≠ ρ := by intro h; rw [h] at h1; linarith
    exact ((differentiableAt_riemannZeta hs1).mul
      (differentiableAt_sepMellin hl (by linarith) (by linarith) hsρ)).mul (hdiffk s)
  · have hΨc : ContinuousAt (sepMellin lam ρ c) 1 :=
      continuousAt_sepMellin hl (by norm_num) (by simp; linarith) (by
        intro h; rw [← h] at hρ2; simp at hρ2)
    have hkc : ContinuousAt (fun s : ℂ => (k : ℂ) ^ (-s)) 1 := (hdiffk 1).continuousAt
    have hlim := (riemannZeta_residue_one.mul (hΨc.tendsto.mono_left nhdsWithin_le_nhds)).mul
      (hkc.tendsto.mono_left nhdsWithin_le_nhds)
    rw [hc, mul_zero, zero_mul] at hlim
    refine hlim.congr' (Eventually.of_forall fun s => ?_)
    simp only [hF]; ring
  -- the line `Re s = 2`
  have h2 : ∫ t : ℝ, F ((2 : ℝ) + t * I) = 0 := by
    have hterm : ∀ n : ℕ, ∫ t : ℝ, sepMellin lam ρ c (2 + t * I) *
        (((n + 1) * k : ℕ) : ℂ) ^ (-(2 + t * I)) = 0 := by
      intro n
      have hpos : (0 : ℝ) < ((n + 1) * k : ℕ) := by
        have : 0 < (n + 1) * k := Nat.mul_pos (Nat.succ_pos n) (by omega)
        exact_mod_cast this
      have h := integral_sepMellin_two_mul_cpow hlam hρ0 hρ2 c hpos
      rw [show (((((n + 1) * k : ℕ) : ℝ)) : ℂ) = (((n + 1) * k : ℕ) : ℂ) by push_cast; ring] at h
      rw [h, show ((((n + 1) * k : ℕ) : ℝ)) = (((n + 1) * k : ℕ) : ℝ) from rfl]
      have := sepKernel_natCast (lam := lam) ρ c ((n + 1) * k)
      rw [this, mul_zero]
    -- Fubini against the Dirichlet series of `ζ`
    set G : ℕ → ℝ → ℂ := fun n t => sepMellin lam ρ c (2 + t * I) *
        (((n + 1) * k : ℕ) : ℂ) ^ (-(2 + t * I)) with hG
    have hΨint : Integrable fun t : ℝ => sepMellin lam ρ c (2 + t * I) := by
      have := verticalIntegrable_sepMellin hlam ρ c (σ := 2) (by norm_num) (by linarith)
        (by linarith)
      simpa using this
    have hnorm : ∀ n : ℕ, ∀ t : ℝ, ‖G n t‖ =
        ‖sepMellin lam ρ c (2 + t * I)‖ * ((((n + 1) * k : ℕ) : ℝ) ^ (-(2 : ℝ))) := by
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
      have hs : Summable fun n : ℕ => (∫ t : ℝ, ‖sepMellin lam ρ c (2 + t * I)‖) *
          ((((n + 1) * k : ℕ) : ℝ) ^ (-(2 : ℝ))) := by
        refine Summable.mul_left _ ?_
        have hb := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
        refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hb
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hle : (n : ℝ) + 1 ≤ (((n + 1) * k : ℕ) : ℝ) := by push_cast; nlinarith
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
  push_cast at hshift1 hshift2 h2
  have : ∫ t : ℝ, F ((1 / 2 : ℝ) + t * I) = 0 := by
    push_cast
    linear_combination -hshift1 - hshift2 + h2
  simpa [hF] using this

end RHTower.SincSeparator
