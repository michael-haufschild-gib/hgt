import Zeta23.Tail
import Zeta23.Tail.Package
import Zeta23.Taper
import Zeta23.Taper.Params
import Zeta23.Taper.Norms
import Zeta23.ZeroSide
import Zeta23.Poisson

/-!
# Alpöge–Furman's tail and Poisson inputs at bandwidths above one

Alpöge–Furman's parameters `P = (ϱ, λ, w)` give the window function
`φ(u) = ϱ((L/2 − |u|)/w)` with `L = λ log(T/2π)`, and their validity predicate requires `λ ≤ 1`.
That bound is used only on the prime side (`X = e^L ≤ T`).  The zero-side inputs of the two-thirds
argument depend on `φ` through `L` alone and need only the taper profile and `w ≥ 1`:

* `half_le_a_fam`: `a ≥ 1/2` once `8w ≤ L`;
* `norm_phiHat_sub_I_mul_le_fam`: the strip decay
  `‖φ̂(r − iy)‖ ≤ e^{L/4} C₁ / |r − iy|²` for `|y| ≤ 1/2`;
* `C1_le_fam`: `C₁ ≤ 2‖ϱ''‖₁`;
* `poissonSq_fam`: `∑_k φ̂(γ − τ_k)² = a L²` for every real `γ`;
* `tailInputs_fam`: the tail package `TailInputs Z P T θ₀` for `T ≥ 300`, `2 ≤ L`, `8w ≤ L` and any
  zero configuration with a unit-window count `N(t, t+1] ≤ A₀ log(|t| + 3)`;
* `theta0_le_fam`: `θ₀ ≤ 32 A₀ R² log(T/2π) T^{λ/2 − 1}` when `C₁ ≤ 2R`.

These hold for every `λ > 0`.  They are the inputs a family version of the argument needs, where the
bandwidth is measured against the family conductor and exceeds `log(T/2π)`.
-/

open Complex Filter

noncomputable section

namespace RHTower

open Zeta23

/-- Validity of the window parameters without an upper bound on the bandwidth: a taper profile,
`λ > 0` and `w ≥ 1`. -/
structure ParamsValidFam (P : Params) : Prop where
  taper : TaperProfile P.ϱ
  lam_pos : 0 < P.lam
  one_le_w : 1 ≤ P.w

variable {P : Params} {T : ℝ}

lemma ParamsValidFam.w_pos (hP : ParamsValidFam P) : 0 < P.w :=
  lt_of_lt_of_le one_pos hP.one_le_w

lemma ParamsValidFam.two_w_le (hP : ParamsValidFam P) (hwL : 8 * P.w ≤ P.L T) :
    2 * P.w ≤ P.L T := by
  linarith [hP.one_le_w]

/-- `a ≥ 1/2` once `8w ≤ L`. -/
theorem half_le_a_fam (hP : ParamsValidFam P) (hwL : 8 * P.w ≤ P.L T) : 1 / 2 ≤ P.a T := by
  have hb := Taper.bConst_le_aConst hP.taper hP.w_pos (hP.two_w_le hwL)
  have h1 := Taper.one_sub_le_bConst hP.taper hP.w_pos (hP.two_w_le hwL)
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have h2 : 2 * P.w / P.L T ≤ 1 / 4 := by
    rw [div_le_iff₀ hL]; linarith
  rw [Params.a_eq]
  linarith

/-- `C₁ = ‖φ''‖₁ ≤ 2‖ϱ''‖₁`. -/
theorem C1_le_fam (hP : ParamsValidFam P) (hwL : 8 * P.w ≤ P.L T) :
    P.C1 T ≤ 2 * Taper.l1Deriv2 P.ϱ :=
  Taper.C1_le hP.taper hP.one_le_w (hP.two_w_le hwL)

/-- Strip decay of `φ̂`. -/
theorem norm_phiHat_sub_I_mul_le_fam (hP : ParamsValidFam P) (hwL : 8 * P.w ≤ P.L T)
    (r y : ℝ) (hy : |y| ≤ 1 / 2) (hz : (r : ℂ) - I * y ≠ 0) :
    ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * P.C1 T / ‖(r : ℂ) - I * y‖ ^ 2 :=
  Taper.norm_phiHat_sub_I_mul_le hP.taper hP.w_pos (hP.two_w_le hwL) r y hy hz

/-- Poisson summation over the grid: `∑_k φ̂(γ − τ_k)² = a L²` for every real `γ`. -/
theorem poissonSq_fam (hP : ParamsValidFam P) (hwL : 8 * P.w ≤ P.L T) :
    ZeroSide.PoissonSq T P := fun γ =>
  Taper.hasSum_phiHatR_sq hP.taper hP.w_pos (hP.two_w_le hwL) T γ

/-- **Tail package at any bandwidth.**  For `T ≥ 300`, `2 ≤ L`, `8w ≤ L` and a zero configuration
with unit-window counts `N(t, t+1] ≤ A₀ log(|t| + 3)`, `A₀ ≥ 1`, the tail inputs hold with
`θ₀ = 4 A₀ (e^{L/4} C₁)² log(4T)/T`. -/
theorem tailInputs_fam (Z : ZeroConfig) (hP : ParamsValidFam P) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hT : Tail.T₀ ≤ T) (hL : 2 ≤ P.L T) (hwL : 8 * P.w ≤ P.L T) :
    Assembly.TailInputs Z P T (Tail.theta0 A₀ (Real.exp (P.L T / 4) * P.C1 T) T) := by
  have H : Tail.TailHyp Z P T A₀ (P.C1 T) :=
    { hT := hT, hL := hL, hA₀ := hA₀, hloc := hloc, hC₁ := Tail.C1_nonneg P T,
      hdecay := fun r y hy hz => norm_phiHat_sub_I_mul_le_fam hP hwL r y hy hz }
  have ha : 0 < P.a T := lt_of_lt_of_le (by norm_num) (half_le_a_fam hP hwL)
  exact H.tailInputs ha (fun z => Params.phiHat_conj z)

/-- **Size of the tail parameter at any bandwidth.**  For `T ≥ 300` and `C₁ ≤ 2R`,
`θ₀ ≤ 32 A₀ R² log(T/2π) T^{λ/2 − 1}`. -/
theorem theta0_le_fam (hP : ParamsValidFam P) {A₀ C₁ R : ℝ} (hT : Tail.T₀ ≤ T) (hA₀ : 0 ≤ A₀)
    (hC₁ : 0 ≤ C₁) (hC₁R : C₁ ≤ 2 * R) :
    Tail.theta0 A₀ (Real.exp (P.L T / 4) * C₁) T ≤ 32 * A₀ * R ^ 2 * l T * T ^ (P.lam / 2 - 1) := by
  have hT' : (300:ℝ) ≤ T := hT
  have hT0 : 0 < T := by linarith
  have hlam := hP.lam_pos
  have hexp : Real.exp (P.L T / 4) ^ 2 ≤ T ^ (P.lam / 2) := by
    rw [← Real.exp_nat_mul]; push_cast
    have : (2:ℝ) * (P.L T / 4) = (P.lam / 2) * Real.log (T / (2 * Real.pi)) := by
      unfold Params.L l; ring
    rw [this, ← Real.log_rpow (by positivity), Real.exp_log (by positivity)]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    rw [div_le_iff₀ (by positivity)]; nlinarith [Real.two_le_pi]
  have hlog := Tail.log_four_mul_le_two_mul_l hT
  have hl0 : 0 ≤ l T := by
    have := Tail.one_le_log_four_mul hT; linarith
  have hK2 : (Real.exp (P.L T / 4) * C₁) ^ 2 ≤ T ^ (P.lam / 2) * (4 * R ^ 2) := by
    rw [mul_pow]
    apply mul_le_mul hexp _ (by positivity) (by positivity)
    nlinarith
  unfold Tail.theta0
  rw [div_le_iff₀ hT0]
  have hTpow : T ^ (P.lam / 2 - 1) * T = T ^ (P.lam / 2) := by
    rw [Real.rpow_sub hT0, Real.rpow_one, div_mul_cancel₀ _ hT0.ne']
  calc 4 * A₀ * (Real.exp (P.L T / 4) * C₁) ^ 2 * Real.log (4 * T)
      ≤ 4 * A₀ * (T ^ (P.lam / 2) * (4 * R ^ 2)) * (2 * l T) := by
        apply mul_le_mul _ hlog (by linarith [Tail.one_le_log_four_mul hT]) (by positivity)
        exact mul_le_mul_of_nonneg_left hK2 (by positivity)
    _ = 32 * A₀ * R ^ 2 * l T * T ^ (P.lam / 2 - 1) * T := by rw [mul_assoc _ _ T, hTpow]; ring

end RHTower
