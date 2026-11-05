import GaloisForLFunctions.ZeroConfigurationGeometry.NearCoincidencesAreReadThroughTheirMoments
import GaloisForLFunctions.HTGeometry.InfiniteProductNearOne
import GaloisForLFunctions.ZeroConfigurationGeometry.SquareRootInversion.SubSpacingLocalInversion

/-!
# Isolating windows vary slowly at their target

The isolating windows of the local camera have transform `F̂ = S · b̂² · Π r_k`: a sine
`S(w) = sin((π/H)(w − θH))`, a bump `b̂`, and the product over the filled lattice. Their value at
the target `w₀` may be very small, but near `w₀` they vary slowly *relative to that value*
(`core_window_slow`, `isolating_window_slow`):
`|F̂(w) − F̂(w₀)| ≤ (e^{|w − w₀| Λ} − 1)|F̂(w₀)|` for `|w − w₀| ≤ min(H/8, 1/2)`, with `Λ = slowRate`
collecting one rate per factor:

* **the sine** (`norm_sin_shift_sub_le`), with `|S(w₀)| ≥ 1/2`;
* **the bump** (`norm_paperFT_sub_le_of_exp_bound`), by Cauchy's estimate from `|b̂| ≤ C₀ e^{ε|Im|}`
  and `|b̂(w₀)| ≥ 1`;
* **the product** (`tprod_pertFactor_ratio`): `Π r_k(w) = Π r_k(w₀) · Π q_k` with
  `q_k − 1 = (w − w₀)(ν_k − μ_k)/((w₀ − ν_k)(w − μ_k))`, so `|Π q_k − 1| ≤ e^{|w − w₀| Λ_P} − 1`,
  `Λ_P = 64 L(1 + L/η) S₀/H²`, `S₀ = Σ_k (1 + k²)⁻¹`.

**The image reads the moments** (`discMoment_readout_slow`). Replacing the floor-relative
Lipschitz bound of `norm_discMoment_le` by the relative one, the image differences `ΔW_j` on the
annihilated windows satisfy `‖ΔW_j − (−i)^j Φ μ_j‖ ≤ N r^{j+1} · 6Λ ‖Φ‖ + tail` for `rΛ ≤ 1/2`,
with `Φ` the image at the target. For mimics `ΔW_j = 0`, so `‖μ_j‖ ≤ N r^{j+1} · 6Λ + tail/c_η²`
(`norm_discMoment_le_slow`).

**Polynomial scales** (`six_slowRate_le_rpow`, `camera_tail_budget`). For clusters of
Riemann–von Mangoldt type at height `T`, aperture `λ · ½ log(T/2π)` and isolation `T^{−M'}`, the
rate is polynomial, `6Λ ≤ T^{M' + κ_λ}` with `κ_λ = πλ/2 + λ + 3`, while decay order
`k ≍ (K + K') log²(T/2π)` makes the tail `≤ e^{−K' log³(T/2π)}`. Hence, uniformly in `T`:

* `discMoment_readout_rvm`: `‖ΔW_j/((−i)^j Φ) − μ_j‖ ≤ N r^{j+1} T^{M' + κ_λ} + e^{−K' log³(T/2π)}`
  for `r ≤ T^{−(M' + κ_λ + 1)}`, every order `j ≤ J`, for any two configurations;
* `norm_discMoment_rvm_le`: for mimics, `‖μ_j‖ ≤ N r^{j+1} T^{M' + κ_λ} + e^{−K' log³(T/2π)}`;
* `pair_centre_and_gap_rvm`: a near-coincident pair `P₁, P₂` of `Z` against `Q₁, Q₂` of `Z'` has
  the same centre to `4r² T^{M' + κ_λ} + E` and the same squared gap to `24 r³ T^{M' + κ_λ} + 4E`;
* `dipole_collapse_rvm`: an isolated dipole closer than `T^{−(M' + κ_λ + 1)}` is closer than `2E`.

The floor need not be polynomial in the isolation radius: errors are measured against the image at
the target, and only the tail is measured against the floor.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-! ### The sine -/

theorem norm_cos_le_exp_abs_im' (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have hcos : Complex.cos z = (cexp (z * I) + cexp (-z * I)) / 2 := rfl
  have h1 : ‖cexp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have h2 : ‖cexp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  rw [hcos, norm_div, Complex.norm_two]
  have h3 := norm_add_le (cexp (z * I)) (cexp (-z * I))
  rw [h1, h2] at h3
  have h4 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  have h5 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  linarith

theorem abs_im_le_of_mem_closedBall {w₀ ζ : ℂ} {ρ : ℝ} (hζ : ζ ∈ Metric.closedBall w₀ ρ) :
    |ζ.im| ≤ |w₀.im| + ρ := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hζ
  have h1 : |ζ.im - w₀.im| ≤ ‖ζ - w₀‖ := by
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
  have h2 := abs_sub_abs_le_abs_sub ζ.im w₀.im
  linarith

/-- **The sine varies slowly.** -/
theorem norm_sin_shift_sub_le {H d ρ : ℝ} (hH : 0 < H) (hρ : 0 ≤ ρ) {w₀ w : ℂ}
    (hw : ‖w - w₀‖ ≤ ρ) :
    ‖Complex.sin (((π / H : ℝ) : ℂ) * (w - (d : ℂ))) - Complex.sin (((π / H : ℝ) : ℂ) * (w₀ - (d : ℂ)))‖ ≤
      π / H * Real.exp (π / H * (|w₀.im| + ρ)) * ‖w - w₀‖ := by
  set c : ℂ := ((π / H : ℝ) : ℂ) with hc
  have hd : ∀ z, HasDerivAt (fun w => Complex.sin (c * (w - (d : ℂ))))
      (Complex.cos (c * (z - (d : ℂ))) * (c * 1)) z := fun z =>
    (((hasDerivAt_id z).sub_const (d : ℂ)).const_mul c).csin
  refine (convex_closedBall w₀ ρ).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (hd z).differentiableAt) (fun z hz => ?_)
    (Metric.mem_closedBall_self hρ) (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hw)
  rw [(hd z).deriv, mul_one, norm_mul, hc, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity), mul_comm]
  refine mul_le_mul_of_nonneg_left ((norm_cos_le_exp_abs_im' _).trans
    (Real.exp_le_exp.mpr ?_)) (by positivity)
  have him : (((π / H : ℝ) : ℂ) * (z - (d : ℂ))).im = π / H * z.im := by
    simp [Complex.mul_im]
  rw [him, abs_mul, abs_of_pos (by positivity : 0 < π / H)]
  exact mul_le_mul_of_nonneg_left (abs_im_le_of_mem_closedBall hz) (by positivity)

/-! ### The bump -/

/-- **A transform with exponential bounds varies slowly** (Cauchy's estimate on unit circles). -/
theorem norm_paperFT_sub_le_of_exp_bound {b : ℝ → ℂ} (hb : Continuous b)
    (hbc : HasCompactSupport b) {ε C0 ρ : ℝ} (hε : 0 ≤ ε) (hρ : 0 ≤ ρ)
    (hC0 : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|)) {w₀ w : ℂ}
    (hw : ‖w - w₀‖ ≤ ρ) :
    ‖paperFT b w - paperFT b w₀‖ ≤ C0 * Real.exp (ε * (|w₀.im| + ρ + 1)) * ‖w - w₀‖ := by
  have hdiff := _root_.RHTower.EvenSector.differentiable_paperFT_of_compact hb hbc
  have hC00 : 0 ≤ C0 := by
    have h1 := hC0 0
    rw [Complex.zero_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at h1
    exact le_trans (norm_nonneg _) h1
  refine (convex_closedBall w₀ ρ).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => hdiff z) (fun z hz => ?_)
    (Metric.mem_closedBall_self hρ) (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hw)
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1)
    (C := C0 * Real.exp (ε * (|w₀.im| + ρ + 1))) one_pos hdiff.diffContOnCl fun ξ hξ => by
      refine (hC0 ξ).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC00)
      refine mul_le_mul_of_nonneg_left ?_ hε
      have h1 := abs_im_le_of_mem_closedBall hz
      have h2 : |ξ.im| ≤ |z.im| + 1 := by
        have := abs_im_le_of_mem_closedBall (w₀ := z) (ρ := 1)
          (Metric.sphere_subset_closedBall hξ)
        exact this
      linarith
  rwa [div_one] at hcauchy

/-! ### The product -/

/-- The ratio of two factors of the product: `q − 1 = (w − w₀)(ν − μ)/((w₀ − ν)(w − μ))`. -/
theorem pertFactor_div_sub_one {H θ : ℝ} (ν : ℤ → ℂ) (k : ℤ) {w w₀ : ℂ}
    (hν : I - ν k ≠ 0) (hw₀ν : w₀ - ν k ≠ 0) (hwμ : w - (latPt H θ k : ℂ) ≠ 0) :
    pertFactor H θ ν k w / pertFactor H θ ν k w₀ - 1 =
      (w - w₀) * (ν k - latPt H θ k) / ((w₀ - ν k) * (w - latPt H θ k)) := by
  have h3 : I - (latPt H θ k : ℂ) ≠ 0 := I_sub_ofReal_ne_zero _
  rw [pertFactor, pertFactor]
  field_simp
  ring

/-- `(k + θ)² ≥ (1 + k²)/32` for `θ ∈ [1/4, 3/4]`. -/
theorem one_add_sq_le_of_shift {θ : ℝ} (hθ0 : 1 / 4 ≤ θ) (hθ1 : θ ≤ 3 / 4) (k : ℤ) :
    (1 + (k : ℝ) ^ 2) / 32 ≤ ((k : ℝ) + θ) ^ 2 := by
  rcases le_or_gt 2 k with h | h
  · have hk : (2 : ℝ) ≤ k := by exact_mod_cast h
    nlinarith
  · rcases le_or_gt k (-2) with h' | h'
    · have hk : (k : ℝ) ≤ -2 := by exact_mod_cast h'
      nlinarith
    · have hk1 : k ≤ 1 := by omega
      have hk2 : -1 ≤ k := by omega
      interval_cases k <;> push_cast <;> nlinarith

theorem summable_inv_one_add_sq_int : Summable fun k : ℤ => (1 + (k : ℝ) ^ 2)⁻¹ := by
  refine Summable.of_norm_bounded_eventually (Real.summable_one_div_int_pow.mpr
    (by norm_num : 1 < 2)) ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : ℤ)).subset fun k hk => ?_
  simp only [Set.mem_setOf_eq, not_le] at hk
  by_contra hne
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hne
  have : ‖(1 + (k : ℝ) ^ 2)⁻¹‖ ≤ 1 / (k : ℝ) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), one_div]
    exact inv_anti₀ (by positivity) (by linarith)
  linarith

/-- The absolute constant `S₀ = Σ_k (1 + k²)⁻¹`. -/
def latticeSumConst : ℝ := ∑' k : ℤ, (1 + (k : ℝ) ^ 2)⁻¹

theorem latticeSumConst_nonneg : 0 ≤ latticeSumConst :=
  tsum_nonneg fun k => by positivity

/-- The product rate `Λ_P = 64 L(1 + L/η) S₀/H²`. -/
def productRate (H L η : ℝ) : ℝ := 64 * L * (1 + L / η) / H ^ 2 * latticeSumConst

/-- **One factor ratio.** Near a target `w₀` on the imaginary axis, `η`-far from `ν`,
`|q_k − 1| ≤ |w − w₀| · 64 L(1 + L/η)/H² · (1 + k²)⁻¹`. -/
theorem norm_pertFactor_ratio_sub_one_le {H θ L η : ℝ} (hH : 0 < H) (hθ0 : 1 / 4 < θ)
    (hθ1 : θ < 3 / 4) {ν : ℤ → ℂ} (hL : ∀ k, ‖ν k - latPt H θ k‖ ≤ L)
    (him : ∀ k, |(ν k).im| ≤ 1 / 2) (hη : 0 < η) {w₀ w : ℂ} (hw₀re : w₀.re = 0)
    (hw₀ν : ∀ k, η ≤ ‖w₀ - ν k‖) (hw : ‖w - w₀‖ ≤ H / 8) (k : ℤ) :
    ‖pertFactor H θ ν k w / pertFactor H θ ν k w₀ - 1‖ ≤
      ‖w - w₀‖ * (64 * L * (1 + L / η) / H ^ 2) * (1 + (k : ℝ) ^ 2)⁻¹ := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  obtain ⟨A, hA⟩ : ∃ A, A = ‖w₀ - (latPt H θ k : ℂ)‖ := ⟨_, rfl⟩
  have hAre : |(k : ℝ) + θ| * H ≤ A := by
    rw [hA]
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.sub_re, hw₀re, Complex.ofReal_re, latPt, zero_sub, abs_neg, abs_mul,
      abs_of_pos hH]
  have hA4 : H / 4 ≤ A := by nlinarith [one_fourth_le_abs_int_add hθ0 hθ1 k]
  have hA0 : 0 < A := by linarith
  have hA2 : H ^ 2 * (1 + (k : ℝ) ^ 2) / 32 ≤ A ^ 2 := by
    have h1 := one_add_sq_le_of_shift hθ0.le hθ1.le k
    have h2 : (|(k : ℝ) + θ| * H) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (by positivity) hAre 2
    rw [mul_pow, sq_abs] at h2
    nlinarith
  have hwμ : A / 2 ≤ ‖w - (latPt H θ k : ℂ)‖ := by
    have := norm_sub_norm_le (w₀ - (latPt H θ k : ℂ)) (w₀ - w)
    rw [show w₀ - (latPt H θ k : ℂ) - (w₀ - w) = w - latPt H θ k by ring, norm_sub_rev w₀ w,
      ← hA] at this
    linarith
  have hw₀ν' : A / (1 + L / η) ≤ ‖w₀ - ν k‖ := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : A ≤ ‖w₀ - ν k‖ + L := by
      rw [hA]
      have := norm_sub_le_norm_sub_add_norm_sub w₀ (ν k) (latPt H θ k : ℂ)
      linarith [hL k]
    have h2 : L ≤ ‖w₀ - ν k‖ * (L / η) := by
      rw [mul_div_assoc', le_div_iff₀ hη]; nlinarith [hw₀ν k]
    linarith
  have hν0 : I - ν k ≠ 0 := I_sub_ne_zero (him k)
  have hw₀ν0 : w₀ - ν k ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hη (hw₀ν k))
  have hwμ0 : w - (latPt H θ k : ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hwμ)
  rw [pertFactor_div_sub_one ν k hν0 hw₀ν0 hwμ0, norm_div, norm_mul, norm_mul]
  have hden : A ^ 2 / (2 * (1 + L / η)) ≤ ‖w₀ - ν k‖ * ‖w - (latPt H θ k : ℂ)‖ := by
    have := mul_le_mul hw₀ν' hwμ (by positivity) (norm_nonneg _)
    calc A ^ 2 / (2 * (1 + L / η)) = A / (1 + L / η) * (A / 2) := by field_simp
      _ ≤ _ := this
  have hpos : 0 < A ^ 2 / (2 * (1 + L / η)) := by positivity
  calc ‖w - w₀‖ * ‖ν k - (latPt H θ k : ℂ)‖ / (‖w₀ - ν k‖ * ‖w - (latPt H θ k : ℂ)‖)
      ≤ ‖w - w₀‖ * L / (A ^ 2 / (2 * (1 + L / η))) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (hL k) (norm_nonneg _)) hpos hden
    _ = ‖w - w₀‖ * (2 * L * (1 + L / η)) / A ^ 2 := by field_simp
    _ ≤ ‖w - w₀‖ * (2 * L * (1 + L / η)) / (H ^ 2 * (1 + (k : ℝ) ^ 2) / 32) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hA2
    _ = ‖w - w₀‖ * (64 * L * (1 + L / η) / H ^ 2) * (1 + (k : ℝ) ^ 2)⁻¹ := by
        field_simp; ring

/-- **The product varies slowly.** `Π r_k(w) = Π r_k(w₀) · Π q_k` and
`|Π q_k − 1| ≤ exp(|w − w₀| Λ_P) − 1`. -/
theorem tprod_pertFactor_ratio {H θ L η : ℝ} (hH : 0 < H) (hθ0 : 1 / 4 < θ)
    (hθ1 : θ < 3 / 4) {ν : ℤ → ℂ} (hL : ∀ k, ‖ν k - latPt H θ k‖ ≤ L)
    (him : ∀ k, |(ν k).im| ≤ 1 / 2) (hη : 0 < η) {w₀ w : ℂ} (hw₀re : w₀.re = 0)
    (hw₀ν : ∀ k, η ≤ ‖w₀ - ν k‖) (hw : ‖w - w₀‖ ≤ H / 8) :
    (∏' k, pertFactor H θ ν k w) = (∏' k, pertFactor H θ ν k w₀) *
        ∏' k, (pertFactor H θ ν k w / pertFactor H θ ν k w₀) ∧
      ‖(∏' k, (pertFactor H θ ν k w / pertFactor H θ ν k w₀)) - 1‖ ≤
        Real.exp (‖w - w₀‖ * productRate H L η) - 1 := by
  have hθ : |θ| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hw₀lat : ∀ k, w₀ ≠ latPt H θ k := fun k e => by
    have h1 := congrArg Complex.re e
    rw [hw₀re, Complex.ofReal_re, latPt] at h1
    have h2 : (k : ℝ) + θ = 0 := (mul_eq_zero.mp h1.symm).resolve_right hH.ne'
    have h3 : k < 0 := by exact_mod_cast (show (k : ℝ) < 0 by linarith)
    have h4 : -1 < k := by exact_mod_cast (show (-1 : ℝ) < k by linarith)
    omega
  have hr0 : ∀ k, pertFactor H θ ν k w₀ ≠ 0 := fun k =>
    pertFactor_ne_zero ν k (I_sub_ne_zero (him k)) (hw₀lat k)
      (sub_ne_zero.mp (norm_pos_iff.mp (lt_of_lt_of_le hη (hw₀ν k))))
  set q : ℤ → ℂ := fun k => pertFactor H θ ν k w / pertFactor H θ ν k w₀ with hq
  have hbound := norm_pertFactor_ratio_sub_one_le hH hθ0 hθ1 hL him hη hw₀re hw₀ν hw
  have hsum : Summable fun k => ‖q k - 1‖ :=
    (summable_inv_one_add_sq_int.mul_left (‖w - w₀‖ * (64 * L * (1 + L / η) / H ^ 2))).of_nonneg_of_le
      (fun k => norm_nonneg _) hbound
  have hmq : Multipliable q := by
    have := multipliable_one_add_of_summable hsum
    exact this.congr fun k => by ring
  have hmr : Multipliable fun k => pertFactor H θ ν k w₀ :=
    multipliable_pertFactor hH hθ hL him hw₀lat
  refine ⟨?_, ?_⟩
  · rw [← hmr.tprod_mul hmq]
    exact tprod_congr fun k => by rw [hq]; simp only; field_simp [hr0 k]
  · have hS : ∑' k, ‖q k - 1‖ ≤ ‖w - w₀‖ * productRate H L η := by
      calc ∑' k, ‖q k - 1‖ ≤ ∑' k : ℤ, ‖w - w₀‖ * (64 * L * (1 + L / η) / H ^ 2) *
            (1 + (k : ℝ) ^ 2)⁻¹ := hsum.tsum_le_tsum hbound
            (summable_inv_one_add_sq_int.mul_left _)
        _ = ‖w - w₀‖ * productRate H L η := by
            rw [tsum_mul_left, productRate, latticeSumConst]; ring
    have hP : HasProd (fun k => 1 + (q k - 1)) (∏' k, q k) := by
      have e : (fun k => 1 + (q k - 1)) = q := funext fun k => by ring
      rw [e]; exact hmq.hasProd
    exact HTGeometry.norm_tprod_one_add_sub_one_le hP hsum hS

/-! ### The isolating windows -/

theorem norm_sub_one_le_exp_sub_one {x : ℂ} {α : ℝ} (h : ‖x - 1‖ ≤ α) :
    ‖x - 1‖ ≤ Real.exp α - 1 := by
  linarith [Real.add_one_le_exp α]

/-- Deviations from one compose: `|x − 1| ≤ e^α − 1`, `|y − 1| ≤ e^β − 1` give
`|xy − 1| ≤ e^{α+β} − 1`. -/
theorem norm_mul_sub_one_le_exp {x y : ℂ} {α β : ℝ} (hx : ‖x - 1‖ ≤ Real.exp α - 1)
    (hy : ‖y - 1‖ ≤ Real.exp β - 1) : ‖x * y - 1‖ ≤ Real.exp (α + β) - 1 := by
  have e : x * y - 1 = (x - 1) * (y - 1) + (x - 1) + (y - 1) := by ring
  have hx0 : 0 ≤ Real.exp α - 1 := (norm_nonneg _).trans hx
  rw [e, Real.exp_add]
  refine (norm_add₃_le).trans ?_
  rw [norm_mul]
  have := mul_le_mul hx hy (norm_nonneg _) hx0
  nlinarith

/-- The relative rate of the isolating windows:
`Λ = 2(π/H) e^{π/H} + 2 C₀ e^{2ε} + Λ_P(H, windowSlack H L, min η (H/2))`. -/
def slowRate (H L η ε C0 : ℝ) : ℝ :=
  2 * (π / H) * Real.exp (π / H) + 2 * (C0 * Real.exp (2 * ε)) +
    productRate H (windowSlack H L) (min η (H / 2))

theorem productRate_nonneg {H L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η) : 0 ≤ productRate H L η := by
  unfold productRate
  exact mul_nonneg (by positivity) latticeSumConst_nonneg

theorem slowRate_nonneg {H L η ε C0 : ℝ} (hH : 0 < H) (hL : 0 ≤ L) (hη : 0 < η)
    (hC0 : 0 ≤ C0) : 0 ≤ slowRate H L η ε C0 := by
  have hL' : 0 ≤ windowSlack H L := by unfold windowSlack; linarith
  have := productRate_nonneg (H := H) hL' (lt_min hη (by linarith : 0 < H / 2))
  unfold slowRate
  positivity

/-- **The core window varies slowly at its target.** For `|w − w₀| ≤ min(H/8, 1/2)`,
`|F̂(w) − F̂(w₀)| ≤ (e^{|w − w₀| Λ} − 1)|F̂(w₀)|` with `Λ = slowRate H L η ε C₀`. -/
theorem core_window_slow {H L η ε C0 : ℝ} (hH : 0 < H) (hη : 0 < η) (hε : 0 ≤ ε)
    {b : ℝ → ℂ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (hb1 : ∀ y : ℝ, 1 ≤ ‖paperFT b ((y : ℂ) * I)‖)
    (hC0 : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|)) {w₀ : ℂ}
    (hw₀re : w₀.re = 0) (hw₀im : |w₀.im| ≤ 1 / 2) {θ : ℝ} (hθ0 : 1 / 4 < θ) (hθ1 : θ < 3 / 4)
    {ν : ℤ → ℂ} (hνb : ∀ j, ‖ν j - latPt H θ j‖ ≤ windowSlack H L)
    (hνim : ∀ j, |(ν j).im| ≤ 1 / 2) (hνw₀ : ∀ j, min η (H / 2) ≤ ‖w₀ - ν j‖) {F : ℝ → ℂ}
    (hformula : ∀ w : ℂ, (∀ j, w ≠ latPt H θ j) → paperFT F w =
        Complex.sin (((π / H : ℝ) : ℂ) * (w - ((θ * H : ℝ) : ℂ))) * paperFT b w *
          (∏' j, pertFactor H θ ν j w) * paperFT b w)
    {w : ℂ} (hw : ‖w - w₀‖ ≤ min (H / 8) (1 / 2)) :
    ‖paperFT F w - paperFT F w₀‖ ≤
      (Real.exp (‖w - w₀‖ * slowRate H L η ε C0) - 1) * ‖paperFT F w₀‖ := by
  have hρ1 : ‖w - w₀‖ ≤ H / 8 := hw.trans (min_le_left _ _)
  have hρ2 : ‖w - w₀‖ ≤ 1 / 2 := hw.trans (min_le_right _ _)
  have hη' : 0 < min η (H / 2) := lt_min hη (by linarith)
  have hδ0 : 0 ≤ ‖w - w₀‖ := norm_nonneg _
  -- both points avoid the lattice
  have hzlat : ∀ j : ℤ, H / 4 ≤ |w₀.re - latPt H θ j| := by
    intro j
    rw [hw₀re, zero_sub, abs_neg, latPt, abs_mul, abs_of_pos hH]
    nlinarith [one_fourth_le_abs_int_add hθ0 hθ1 j]
  have hre : |w.re - w₀.re| ≤ ‖w - w₀‖ := by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  have hoff : ∀ v : ℂ, |v.re - w₀.re| ≤ H / 8 → ∀ j, v ≠ latPt H θ j := fun v hv j e => by
    rw [e, Complex.ofReal_re, abs_sub_comm] at hv
    linarith [hzlat j]
  have hw₀lat := hoff w₀ (by rw [sub_self, abs_zero]; positivity)
  have hwlat := hoff w (hre.trans hρ1)
  -- the sine
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, S₀ = Complex.sin (((π / H : ℝ) : ℂ) * (w₀ - ((θ * H : ℝ) : ℂ))) :=
    ⟨_, rfl⟩
  obtain ⟨S₁, hS₁⟩ : ∃ S₁, S₁ = Complex.sin (((π / H : ℝ) : ℂ) * (w - ((θ * H : ℝ) : ℂ))) :=
    ⟨_, rfl⟩
  have hS₀n : 1 / 2 ≤ ‖S₀‖ := hS₀ ▸ half_le_norm_sin_shift hH hθ0 hθ1 hw₀re
  have hS₀0 : S₀ ≠ 0 := norm_pos_iff.mp (by linarith)
  have hSd : ‖S₁ - S₀‖ ≤ π / H * Real.exp (π / H) * ‖w - w₀‖ := by
    rw [hS₀, hS₁]
    refine (norm_sin_shift_sub_le hH (by positivity) le_rfl).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
      (by positivity)) hδ0
    refine le_of_le_of_eq (mul_le_mul_of_nonneg_left (by linarith : |w₀.im| + ‖w - w₀‖ ≤ 1)
      (by positivity)) (mul_one _)
  have hx : ‖S₁ / S₀ - 1‖ ≤ Real.exp (‖w - w₀‖ * (2 * (π / H) * Real.exp (π / H))) - 1 := by
    refine norm_sub_one_le_exp_sub_one ?_
    rw [div_sub_one hS₀0, norm_div, div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (S₁ - S₀), Real.exp_pos (π / H), Real.pi_pos]
  -- the bump
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = paperFT b w₀ := ⟨_, rfl⟩
  have hB₀n : 1 ≤ ‖B₀‖ := by
    have hw₀ : ((w₀.im : ℝ) : ℂ) * I = w₀ := by apply Complex.ext <;> simp [hw₀re]
    have := hb1 w₀.im
    rwa [hw₀, ← hB₀] at this
  have hB₀0 : B₀ ≠ 0 := norm_pos_iff.mp (by linarith)
  have hBd : ‖paperFT b w - B₀‖ ≤ C0 * Real.exp (2 * ε) * ‖w - w₀‖ := by
    rw [hB₀]
    refine (norm_paperFT_sub_le_of_exp_bound hb hbc hε hδ0 hC0 le_rfl).trans ?_
    have hC00 : 0 ≤ C0 := by
      have h1 := hC0 0
      rw [Complex.zero_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at h1
      exact le_trans (norm_nonneg _) h1
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC00)
      hδ0
    nlinarith
  have hy : ‖paperFT b w / B₀ - 1‖ ≤ Real.exp (‖w - w₀‖ * (C0 * Real.exp (2 * ε))) - 1 := by
    refine norm_sub_one_le_exp_sub_one ?_
    rw [div_sub_one hB₀0, norm_div, div_le_iff₀ (by linarith)]
    have : 0 ≤ C0 * Real.exp (2 * ε) * ‖w - w₀‖ := (norm_nonneg _).trans hBd
    nlinarith
  -- the product
  obtain ⟨hPi, hq⟩ := tprod_pertFactor_ratio hH hθ0 hθ1 hνb hνim hη' hw₀re hνw₀ hρ1
  -- assembling
  have hFw₀ := hformula w₀ hw₀lat
  have hFw := hformula w hwlat
  rw [← hS₀, ← hB₀] at hFw₀
  rw [← hS₁, hPi] at hFw
  set q := ∏' k, (pertFactor H θ ν k w / pertFactor H θ ν k w₀)
  have hprod : paperFT F w = paperFT F w₀ *
      ((S₁ / S₀) * (paperFT b w / B₀) * q * (paperFT b w / B₀)) := by
    rw [hFw, hFw₀]
    field_simp
  have htot := norm_mul_sub_one_le_exp (norm_mul_sub_one_le_exp (norm_mul_sub_one_le_exp hx hy) hq) hy
  rw [hprod, show paperFT F w₀ * ((S₁ / S₀) * (paperFT b w / B₀) * q * (paperFT b w / B₀)) -
      paperFT F w₀ = paperFT F w₀ * ((S₁ / S₀) * (paperFT b w / B₀) * q * (paperFT b w / B₀) - 1)
      by ring, norm_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right (htot.trans_eq ?_) (norm_nonneg _)
  congr 1
  unfold slowRate
  ring_nf

/-- **Isolating windows that vary slowly at their target.** The windows of
`isolating_window_of_bump`, which in addition satisfy
`|F̂(w) − F̂(w₀)| ≤ (e^{|w − w₀| Λ} − 1)|F̂(w₀)|` for `|w − w₀| ≤ min(H/8, 1/2)`, with
`Λ = slowRate H L η ε C₀`. -/
theorem isolating_window_slow {H L r η ε : ℝ} (hH : 0 < H) (hL : 0 ≤ L) (hη : 0 < η)
    (hε : 0 < ε) (hεr : π / H + 2 * ε ≤ r) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbs : tsupport b ⊆ Icc (-ε) ε) (hb1 : ∀ y : ℝ, 1 ≤ ‖paperFT b ((y : ℂ) * I)‖) {k m : ℕ}
    (hm : windowExponent H L + k ≤ m) {Cm C0 : ℝ}
    (hCm : ∀ w : ℂ, (1 + ‖w‖) ^ m * ‖paperFT b w‖ ≤ Cm * Real.exp (ε * |w.im|))
    (hC0 : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|))
    {ι : Type} (lam : ι → ℂ) (τ : ι → ℤ) (P : Set ι) (hτ : Set.InjOn τ P)
    (hPL : ∀ i ∈ P, ‖lam i - τ i * H‖ ≤ L) (hPim : ∀ i ∈ P, |(lam i).im| ≤ 1 / 2) {w₀ : ℂ}
    (hw₀re : w₀.re = 0) (hw₀im : |w₀.im| ≤ 1 / 2) (hw₀P : ∀ i ∈ P, η ≤ ‖w₀ - lam i‖) :
    ∃ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ ApertureWindow r f ∧ (∀ i ∈ P, paperFT f (lam i) = 0) ∧
      windowFloor H L η ≤ ‖paperFT f w₀‖ ∧
      (∀ w : ℂ, |w.im| ≤ 1 / 2 →
        ‖paperFT f w‖ * (1 + |w.re|) ^ k ≤ windowGrowth H L * Cm * C0 * Real.exp ε) ∧
      ∀ w : ℂ, ‖w - w₀‖ ≤ min (H / 8) (1 / 2) → ‖paperFT f w - paperFT f w₀‖ ≤
        (Real.exp (‖w - w₀‖ * slowRate H L η ε C0) - 1) * ‖paperFT f w₀‖ := by
  have hbc : HasCompactSupport b := isCompact_Icc.of_isClosed_subset (isClosed_tsupport b) hbs
  obtain ⟨θ, ν, F, hθ0, hθ1, hνb, hνim, hνw₀, hFsmooth, hFs, hblind, hformula⟩ :=
    isolating_window_core (η := η) hH hL hε hεr hb hbs lam τ P hτ hPL hPim hw₀re hw₀P
  obtain ⟨h1, h2⟩ := core_window_floor_decay hH hL hη hε hb1 hm hCm hC0 hw₀re hw₀im hθ0 hθ1 hνb
    hνim hνw₀ hFsmooth (isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hFs) hformula
  exact ⟨F, hFsmooth, ⟨hFsmooth.of_le (by norm_cast), hFs⟩, hblind, h1, h2, fun w hw =>
    core_window_slow hH hη hε.le hb.continuous hbc hb1 hC0 hw₀re hw₀im hθ0 hθ1 hνb hνim hνw₀
      hformula hw⟩

/-! ### The moments of a near-coincident cluster, relative to the image -/

/-- Relative perturbation of a pair image: `|u − u₀| ≤ α|u₀|`, `|v − v₀| ≤ α|v₀|` give
`|u conj v − u₀ conj v₀| ≤ (2α + α²)|u₀||v₀|`. -/
theorem norm_mul_conj_sub_le_of_rel {u u₀ v v₀ : ℂ} {α : ℝ} (hα : 0 ≤ α)
    (hu : ‖u - u₀‖ ≤ α * ‖u₀‖) (hv : ‖v - v₀‖ ≤ α * ‖v₀‖) :
    ‖u * conj v - u₀ * conj v₀‖ ≤ (2 * α + α ^ 2) * (‖u₀‖ * ‖v₀‖) := by
  have e : u * conj v - u₀ * conj v₀ = (u - u₀) * conj v + u₀ * conj (v - v₀) := by
    rw [map_sub]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  have hv' : ‖v‖ ≤ (1 + α) * ‖v₀‖ := by
    have := norm_sub_norm_le v v₀
    linarith
  have h1 := mul_le_mul hu hv' (norm_nonneg _) (mul_nonneg hα (norm_nonneg _))
  have h2 := mul_le_mul_of_nonneg_left hv (norm_nonneg u₀)
  nlinarith [norm_nonneg u₀, norm_nonneg v₀]

/-- **The pair image varies slowly.** If `u, v` vary slowly at `ω` and `conj ω` with rate `Λ` on
balls of radius `ρ ≥ r`, and `rΛ ≤ 1/2`, then for `|w − ω| ≤ r`
`|u(w) conj v(conj w) − u(ω) conj v(conj ω)| ≤ 6rΛ |u(ω)| |v(conj ω)|`. -/
theorem norm_pairImage_sub_le_slow {u v : ℂ → ℂ} {ω w : ℂ} {Λ r ρ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hr : 0 ≤ r) (hrΛ : r * Λ ≤ 1 / 2) (hrρ : r ≤ ρ)
    (hu : ∀ x, ‖x - ω‖ ≤ ρ → ‖u x - u ω‖ ≤ (Real.exp (‖x - ω‖ * Λ) - 1) * ‖u ω‖)
    (hv : ∀ x, ‖x - conj ω‖ ≤ ρ →
      ‖v x - v (conj ω)‖ ≤ (Real.exp (‖x - conj ω‖ * Λ) - 1) * ‖v (conj ω)‖)
    (hw : ‖w - ω‖ ≤ r) :
    ‖u w * conj (v (conj w)) - u ω * conj (v (conj ω))‖ ≤
      6 * (r * Λ) * (‖u ω‖ * ‖v (conj ω)‖) := by
  have hrΛ0 : 0 ≤ r * Λ := mul_nonneg hr hΛ0
  obtain ⟨α, hα⟩ : ∃ α, α = Real.exp (r * Λ) - 1 := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := by rw [hα]; linarith only [Real.add_one_le_exp (r * Λ), hrΛ0]
  have hα2 : α ≤ 2 * (r * Λ) := by
    have h := Real.abs_exp_sub_one_le (x := r * Λ) (by rw [abs_of_nonneg hrΛ0]; linarith only [hrΛ])
    rw [abs_of_nonneg hrΛ0] at h
    rw [hα]; exact (le_abs_self _).trans h
  have hmono : Real.exp (‖w - ω‖ * Λ) - 1 ≤ α := by
    have := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hw hΛ0)
    rw [hα]; linarith only [this]
  have hcd : ‖conj w - conj ω‖ = ‖w - ω‖ := by rw [← map_sub, Complex.norm_conj]
  have h1 := (hu w (hw.trans hrρ)).trans (mul_le_mul_of_nonneg_right hmono (norm_nonneg _))
  have h2 := hv (conj w) (by rw [hcd]; exact hw.trans hrρ)
  rw [hcd] at h2
  have hpair := norm_mul_conj_sub_le_of_rel hα0 h1
    (h2.trans (mul_le_mul_of_nonneg_right hmono (norm_nonneg _)))
  have hα1 : α ≤ 1 := by linarith only [hα2, hrΛ]
  have hsq : α ^ 2 ≤ α := by nlinarith only [hα0, hα1]
  have hc' : 2 * α + α ^ 2 ≤ 6 * (r * Λ) := by linarith only [hsq, hα2]
  exact hpair.trans (mul_le_mul_of_nonneg_right hc' (by positivity))

/-- `P μ ≤ T + N P` with `P ≥ c² > 0` gives `μ ≤ N + T/c²`. -/
theorem le_add_div_of_mul_le {P μ N T c : ℝ} (hc : 0 < c) (hP : c * c ≤ P) (hT : 0 ≤ T)
    (h : P * μ ≤ T + N * P) : μ ≤ N + T / (c * c) := by
  have hP0 : 0 < P := lt_of_lt_of_le (mul_pos hc hc) hP
  have hq : μ - N ≤ T / P := by rw [le_div_iff₀ hP0]; linarith only [h]
  have hq' : T / P ≤ T / (c * c) := div_le_div_of_nonneg_left hT (mul_pos hc hc) hP
  linarith only [hq, hq']

/-- **A slowly varying local isolating pair.** The pair of `exists_local_isolating_pair`, whose
windows in addition vary slowly at their targets `γ_{z₀} − X` and `conj γ_{z₀} − X`
(`isolating_window_slow`). -/
theorem exists_local_slow_pair {a D C₀ η ε : ℝ} (hD : 0 < D) (hη : 0 < η) (hε : 0 < ε)
    (hεa : π * D / 2 + 2 * ε ≤ a) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbs : tsupport b ⊆ Icc (-ε) ε) (hb1 : ∀ y : ℝ, 1 ≤ ‖paperFT b ((y : ℂ) * I)‖) {k m : ℕ}
    (hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + k ≤ m) {Cm C0 : ℝ}
    (hCm : ∀ w : ℂ, (1 + ‖w‖) ^ m * ‖paperFT b w‖ ≤ Cm * Real.exp (ε * |w.im|))
    (hC0 : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|))
    (Z Z' : ZeroConfig) {z₀ : ℂ} (hz₀ : |z₀.re - 1 / 2| ≤ 1 / 2) {R : ℝ} (Q : ℂ → Prop)
    (hQ : ∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ R → ¬ Q z → η ≤ ‖z - z₀‖)
    (hcount : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - z₀.im| ≤ R ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀) :
    ∃ F₁ G₁ : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ContDiff ℝ (⊤ : ℕ∞) G₁ ∧
      ApertureWindow a F₁ ∧ ApertureWindow a G₁ ∧
      (∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ R → ¬ Q z →
        paperFT F₁ (gammaOf z - z₀.im) = 0 ∨ paperFT G₁ (conj (gammaOf z) - z₀.im) = 0) ∧
      windowFloor (2 * D⁻¹) (localSlack D C₀) η ≤ ‖paperFT F₁ (gammaOf z₀ - z₀.im)‖ ∧
      windowFloor (2 * D⁻¹) (localSlack D C₀) η ≤ ‖paperFT G₁ (conj (gammaOf z₀) - z₀.im)‖ ∧
      (∀ w : ℂ, |w.im| ≤ 1 / 2 → ‖paperFT F₁ w‖ * (1 + |w.re|) ^ k ≤
        windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε) ∧
      (∀ w : ℂ, |w.im| ≤ 1 / 2 → ‖paperFT G₁ w‖ * (1 + |w.re|) ^ k ≤
        windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε) ∧
      (∀ w : ℂ, ‖w - (gammaOf z₀ - z₀.im)‖ ≤ min (2 * D⁻¹ / 8) (1 / 2) →
        ‖paperFT F₁ w - paperFT F₁ (gammaOf z₀ - z₀.im)‖ ≤
          (Real.exp (‖w - (gammaOf z₀ - z₀.im)‖ * slowRate (2 * D⁻¹) (localSlack D C₀) η ε C0) -
            1) * ‖paperFT F₁ (gammaOf z₀ - z₀.im)‖) ∧
      (∀ w : ℂ, ‖w - (conj (gammaOf z₀) - z₀.im)‖ ≤ min (2 * D⁻¹ / 8) (1 / 2) →
        ‖paperFT G₁ w - paperFT G₁ (conj (gammaOf z₀) - z₀.im)‖ ≤
          (Real.exp (‖w - (conj (gammaOf z₀) - z₀.im)‖ *
            slowRate (2 * D⁻¹) (localSlack D C₀) η ε C0) - 1) *
              ‖paperFT G₁ (conj (gammaOf z₀) - z₀.im)‖) := by
  have hh : (0 : ℝ) < 2 * D⁻¹ := by positivity
  have hL0 : 0 ≤ localSlack D C₀ := by unfold localSlack; positivity
  have hr : π / (2 * D⁻¹) + 2 * ε ≤ a := by
    rw [show π / (2 * D⁻¹) = π * D / 2 by field_simp]
    exact hεa
  obtain ⟨F₁, G₁, hblind, hF, hG⟩ := exists_local_pair_of_windows (η := η) hD
    (fun f w₀ => ContDiff ℝ (⊤ : ℕ∞) f ∧ ApertureWindow a f ∧
      windowFloor (2 * D⁻¹) (localSlack D C₀) η ≤ ‖paperFT f w₀‖ ∧
      (∀ w : ℂ, |w.im| ≤ 1 / 2 → ‖paperFT f w‖ * (1 + |w.re|) ^ k ≤
        windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε) ∧
      ∀ w : ℂ, ‖w - w₀‖ ≤ min (2 * D⁻¹ / 8) (1 / 2) → ‖paperFT f w - paperFT f w₀‖ ≤
        (Real.exp (‖w - w₀‖ * slowRate (2 * D⁻¹) (localSlack D C₀) η ε C0) - 1) *
          ‖paperFT f w₀‖)
    (fun lam τ P hτ hPL hPim w₀ h1 h2 h3 => by
      obtain ⟨f, hfs, hfw, hfP, hf0, hfd, hfsl⟩ := isolating_window_slow hh hL0 hη hε hr hb hbs
        hb1 hm hCm hC0 lam τ P hτ hPL hPim h1 h2 h3
      exact ⟨f, hfP, hfs, hfw, hf0, hfd, hfsl⟩) Z Z' hz₀ Q hQ hcount
  exact ⟨F₁, G₁, hF.1, hG.1, hF.2.1, hG.2.1, hblind, hF.2.2.1, hG.2.2.1, hF.2.2.2.1, hG.2.2.2.1,
    hF.2.2.2.2, hG.2.2.2.2⟩

/-- A readout `‖ΔW − (−i)^j Φ μ‖ ≤ N‖Φ‖ + T` with `‖Φ‖ ≥ c²` gives
`‖ΔW/((−i)^j Φ) − μ‖ ≤ N + T/c²`. -/
theorem readout_div_le {ΔW Φ μ : ℂ} {N T c : ℝ} {j : ℕ} (hc : 0 < c) (hΦ : c ^ 2 ≤ ‖Φ‖)
    (hT : 0 ≤ T) (h : ‖ΔW - (-I) ^ j * Φ * μ‖ ≤ N * ‖Φ‖ + T) :
    ‖ΔW / ((-I) ^ j * Φ) - μ‖ ≤ N + T / c ^ 2 := by
  have hΦ0 : 0 < ‖Φ‖ := lt_of_lt_of_le (pow_pos hc 2) hΦ
  have hnormI : ‖(-I : ℂ) ^ j‖ = 1 := by rw [norm_pow, norm_neg, Complex.norm_I, one_pow]
  have hne : (-I : ℂ) ^ j * Φ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)) (norm_pos_iff.mp hΦ0)
  have e : ΔW / ((-I) ^ j * Φ) - μ = (ΔW - (-I) ^ j * Φ * μ) / ((-I) ^ j * Φ) := by
    rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]; ring
  rw [e, norm_div, norm_mul, hnormI, one_mul, div_le_iff₀ hΦ0]
  have h1 : T ≤ T / c ^ 2 * ‖Φ‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc 2)]
    exact mul_le_mul_of_nonneg_left hΦ hT
  have e2 : (N + T / c ^ 2) * ‖Φ‖ = N * ‖Φ‖ + T / c ^ 2 * ‖Φ‖ := by ring
  linarith

/-- **The camera reads the moments of a near-coincident cluster from the image.** Under the
hypotheses of `norm_discMoment_le`, with `r ≤ min(D⁻¹/4, 1/2)` and `rΛ ≤ 1/2` for
`Λ = slowRate (2/D) (localSlack D C₀) η ε C₀`, there are windows `F₁, G₁` of aperture `a` with
image `Φ = pointImage F G z₀ ≥ c_η²` at the target such that, for `F_j = annihilatePow` of order
`j ≤ J` and `ΔW_j = Z.W F_j G − Z'.W F_j G`,
`‖ΔW_j − (−i)^j Φ μ_j‖ ≤ N r^{j+1} · 6Λ ‖Φ‖ + M² e^a (5/4)(1 + |X|)²/(1 + R)^{2k−2} · S`. -/
theorem discMoment_readout_slow {a D C₀ η ε r : ℝ} {J : ℕ} (hD : 0 < D) (hη : 0 < η) (hε : 0 < ε)
    (hεa : π * D / 2 + 2 * ε ≤ a) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbs : tsupport b ⊆ Icc (-ε) ε) (hb1 : ∀ y : ℝ, 1 ≤ ‖paperFT b ((y : ℂ) * I)‖) {k m : ℕ}
    (hk : 1 ≤ k) (hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + ((k + J : ℕ) : ℝ) ≤ m)
    {Cm C0 : ℝ}
    (hCm : ∀ w : ℂ, (1 + ‖w‖) ^ m * ‖paperFT b w‖ ≤ Cm * Real.exp (ε * |w.im|))
    (hC0 : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|))
    {Z Z' : ZeroConfig} (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    {z₀ : ℂ}
    (hz₀ : |z₀.re - 1 / 2| ≤ 1 / 2) {R : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hrD : r ≤ min (2 * D⁻¹ / 8) (1 / 2))
    (hrΛ : r * slowRate (2 * D⁻¹) (localSlack D C₀) η ε C0 ≤ 1 / 2)
    (hiso : ∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ R → ‖z - z₀‖ ≤ r ∨ η ≤ ‖z - z₀‖)
    (hcount : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - z₀.im| ≤ R ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀)
    {s : Finset ℂ} (hsd : ∀ z ∈ s, ‖z - z₀‖ ≤ r)
    (hds : ∀ z, multDiff Z Z' z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s) :
    ∃ F₁ G₁ : ℝ → ℂ, ApertureWindow a F₁ ∧ ApertureWindow a G₁ ∧
      windowFloor (2 * D⁻¹) (localSlack D C₀) η ^ 2 ≤
        ‖pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀‖ ∧
      ∀ j : ℕ, j ≤ J →
        ApertureWindow a (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁)) ∧
        ‖(Z.W (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁)) (localWindow z₀.im G₁) -
            Z'.W (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁))
              (localWindow z₀.im G₁)) -
          (-I) ^ j * pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀ *
            ∑ z ∈ s, multDiff Z Z' z * (gammaOf z - gammaOf z₀) ^ j‖ ≤
          (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (j + 1) *
              (6 * slowRate (2 * D⁻¹) (localSlack D C₀) η ε C0) *
              ‖pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀‖ +
            (windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε) ^ 2 * Real.exp a *
              (5 / 4 * (1 + |z₀.im|) ^ 2 / (1 + R) ^ (2 * k - 2)) *
                ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) := by
  classical
  obtain ⟨c, hcdef⟩ : ∃ c, c = windowFloor (2 * D⁻¹) (localSlack D C₀) η := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M,
      M = windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε := ⟨_, rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = slowRate (2 * D⁻¹) (localSlack D C₀) η ε C0 := ⟨_, rfl⟩
  rw [← hcdef, ← hMdef, ← hΛ]
  rw [← hΛ] at hrΛ
  have hh : (0 : ℝ) < 2 * D⁻¹ := by positivity
  have hL0 : 0 ≤ localSlack D C₀ := by unfold localSlack; positivity
  have hc0 : 0 < c := by rw [hcdef]; exact windowFloor_pos hh hL0 hη
  have ha : 0 ≤ a := by nlinarith [Real.pi_pos]
  have hCm0 : 0 ≤ Cm := by
    have h1 := hCm 0
    rw [Complex.zero_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at h1
    exact le_trans (by positivity) h1
  have hC00 : 0 ≤ C0 := by
    have h1 := hC0 0
    rw [Complex.zero_im, abs_zero, mul_zero, Real.exp_zero, mul_one] at h1
    exact le_trans (norm_nonneg _) h1
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg (windowGrowth_nonneg hh hL0) hCm0)
      hC00) (Real.exp_pos _).le
  have hΛ0 : 0 ≤ Λ := hΛ ▸ slowRate_nonneg hh hL0 hη hC00
  -- the slowly varying isolating pair, blind outside the disc
  obtain ⟨F₁, G₁, hF₁s, hG₁s, hF₁, hG₁, hblind, hF₁0, hG₁0, hF₁d, hG₁d, hF₁sl, hG₁sl⟩ :=
    exists_local_slow_pair (k := k + J) hD hη hε hεa hb hbs hb1 hm hCm hC0 Z Z' hz₀
      (fun z => ‖z - z₀‖ ≤ r) (fun z hcz hzR hnot => (hiso z hcz hzR).resolve_left hnot) hcount
  rw [← hcdef] at hF₁0 hG₁0
  rw [← hMdef] at hF₁d hG₁d
  rw [← hΛ] at hF₁sl hG₁sl
  obtain ⟨X, hX⟩ : ∃ X, X = z₀.im := ⟨_, rfl⟩
  rw [← hX] at hiso hcount hblind hF₁0 hG₁0 hF₁sl hG₁sl ⊢
  have hstrip : ∀ z, multDiff Z Z' z ≠ 0 → |z.re - 1 / 2| ≤ 1 / 2 := by
    intro z hz
    rcases mem_carrier_of_multDiff_ne_zero hz with h' | h'
    · obtain ⟨h1, h2⟩ := Z.strip _ h'
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨h1, h2⟩ := Z'.strip _ h'
      rw [abs_le]; constructor <;> linarith
  -- the target
  obtain ⟨ω, hω⟩ : ∃ ω, ω = gammaOf z₀ - X := ⟨_, rfl⟩
  have hωre : ω.re = 0 := by
    rw [hω, Complex.sub_re, Complex.ofReal_re, gammaOf_re, hX, sub_self]
  have hωim' : ω.im = -(z₀.re - 1 / 2) := by
    rw [hω, Complex.sub_im, Complex.ofReal_im, sub_zero, gammaOf_im]
  have hωim : |ω.im| ≤ 1 / 2 := by rw [hωim', abs_neg]; exact hz₀
  have hconjω : conj ω = conj (gammaOf z₀) - X := by rw [hω, map_sub, Complex.conj_ofReal]
  rw [← hω] at hF₁sl hF₁0 ⊢
  rw [← hconjω] at hG₁sl hG₁0
  have hPI0 : pointImage (localWindow X F₁) (localWindow X G₁) z₀ =
      paperFT F₁ ω * conj (paperFT G₁ (conj ω)) := by
    rw [pointImage, paperFT_localWindow, paperFT_localWindow, ← hω, hconjω]
  refine ⟨F₁, G₁, hF₁, hG₁, ?_, fun j hj => ?_⟩
  · rw [hPI0, norm_mul, Complex.norm_conj, sq]
    exact mul_le_mul hF₁0 hG₁0 hc0.le (hc0.le.trans hF₁0)
  -- the windows of order `j`, modulated to height `X`
  obtain ⟨hAs, hAt, hAft⟩ := annihilatePow_props (κ := ω) hF₁s hF₁.hasCompactSupport j
  have hF₁jw : ApertureWindow a (annihilatePow ω j F₁) :=
    ⟨hAs.of_le (by norm_cast), hAt.trans hF₁.2⟩
  set F := localWindow X (annihilatePow ω j F₁) with hF
  set G := localWindow X G₁ with hG
  have hFw : ApertureWindow a F := apertureWindow_localWindow hF₁jw X
  have hGw : ApertureWindow a G := apertureWindow_localWindow hG₁ X
  have hFdec : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT F w‖ * (1 + |w.re - X|) ^ k ≤ M * Real.exp (a * |w.im|) := by
    intro w hw
    rw [hF, paperFT_localWindow, hAft]
    have hv : ‖w - X - ω‖ ≤ 1 + |w.re - X| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [Complex.sub_re, Complex.sub_re, Complex.ofReal_re, hωre, sub_zero, Complex.sub_im,
        Complex.sub_im, Complex.ofReal_im, sub_zero]
      have : |w.im - ω.im| ≤ 1 := (abs_sub _ _).trans (by linarith)
      linarith
    have hd := hF₁d (w - X) (by rw [Complex.sub_im, Complex.ofReal_im, sub_zero]; exact hw)
    rw [Complex.sub_re, Complex.ofReal_re] at hd
    have h1 : (1 : ℝ) ≤ 1 + |w.re - X| := by linarith [abs_nonneg (w.re - X)]
    have hj' : (1 + |w.re - X|) ^ j * (1 + |w.re - X|) ^ k ≤ (1 + |w.re - X|) ^ (k + J) := by
      rw [← pow_add]; exact pow_le_pow_right₀ h1 (by omega)
    calc ‖(-I * (w - X - ω)) ^ j * paperFT F₁ (w - X)‖ * (1 + |w.re - X|) ^ k
        = ‖w - X - ω‖ ^ j * (‖paperFT F₁ (w - X)‖ * (1 + |w.re - X|) ^ k) := by
          rw [norm_mul, norm_pow, norm_mul, norm_neg, Complex.norm_I, one_mul]; ring
      _ ≤ (1 + |w.re - X|) ^ j * (‖paperFT F₁ (w - X)‖ * (1 + |w.re - X|) ^ k) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hv j) (by positivity)
      _ = ‖paperFT F₁ (w - X)‖ * ((1 + |w.re - X|) ^ j * (1 + |w.re - X|) ^ k) := by ring
      _ ≤ ‖paperFT F₁ (w - X)‖ * (1 + |w.re - X|) ^ (k + J) :=
          mul_le_mul_of_nonneg_left hj' (norm_nonneg _)
      _ ≤ M := hd
      _ ≤ M * Real.exp (a * |w.im|) := le_mul_of_one_le_right hM0 (Real.one_le_exp (by positivity))
  have hGdec : ∀ w : ℂ, |w.im| ≤ 1 / 2 →
      ‖paperFT G w‖ * (1 + |w.re - X|) ^ k ≤ M * Real.exp (a * |w.im|) := by
    intro w hw
    rw [hG, paperFT_localWindow]
    have hd := hG₁d (w - X) (by rw [Complex.sub_im, Complex.ofReal_im, sub_zero]; exact hw)
    rw [Complex.sub_re, Complex.ofReal_re] at hd
    have h1 : (1 : ℝ) ≤ 1 + |w.re - X| := by linarith [abs_nonneg (w.re - X)]
    calc ‖paperFT G₁ (w - X)‖ * (1 + |w.re - X|) ^ k
        ≤ ‖paperFT G₁ (w - X)‖ * (1 + |w.re - X|) ^ (k + J) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) (norm_nonneg _)
      _ ≤ M := hd
      _ ≤ M * Real.exp (a * |w.im|) := le_mul_of_one_le_right hM0 (Real.one_le_exp (by positivity))
  -- the image of a point
  set Φ : ℂ → ℂ := fun w => paperFT F₁ w * conj (paperFT G₁ (conj w)) with hΦ
  have hconjX : ∀ z : ℂ, conj (gammaOf z) - (X : ℂ) = conj (gammaOf z - X) := fun z => by
    rw [map_sub, Complex.conj_ofReal]
  have hPI : ∀ z, pointImage F G z =
      (-I) ^ j * ((gammaOf z - gammaOf z₀) ^ j * Φ (gammaOf z - X)) := by
    intro z
    rw [pointImage, hF, hG, paperFT_localWindow, paperFT_localWindow, hAft, hconjX,
      show gammaOf z - (X : ℂ) - ω = gammaOf z - gammaOf z₀ by rw [hω]; ring, mul_pow]
    simp only [hΦ]
    ring
  have hzero_out : ∀ z, multDiff Z Z' z ≠ 0 → |z.im - X| ≤ R → ¬ ‖z - z₀‖ ≤ r →
      Φ (gammaOf z - X) = 0 := by
    intro z hcz hzR hnot
    simp only [hΦ]
    rcases hblind z hcz hzR hnot with h0 | h0
    · rw [h0, zero_mul]
    · rw [← hconjX, h0, map_zero, mul_zero]
  have hsplit : ∀ z, multDiff Z Z' z * pointImage F G z =
      (if z ∈ s then multDiff Z Z' z * pointImage F G z else 0) +
        (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0) := by
    intro z
    by_cases hzs : z ∈ s
    · have hle : |z.im - X| ≤ r := by
        have := hsd z hzs
        rw [hX, ← Complex.sub_im]
        exact (Complex.abs_im_le_norm _).trans this
      rw [if_pos hzs, if_neg (by linarith), add_zero]
    · rw [if_neg hzs, zero_add]
      split_ifs with hfar
      · rfl
      · by_cases hcz : multDiff Z Z' z = 0
        · rw [hcz, zero_mul]
        · have hnot : ¬ ‖z - z₀‖ ≤ r := fun h => hzs (hds z hcz h)
          rw [hPI, hzero_out z hcz (not_lt.mp hfar) hnot, mul_zero, mul_zero, mul_zero]
  have htot := summable_multDiff_pointImage hZ hZ' hFw.1 hFw.hasCompactSupport hGw.1
    hGw.hasCompactSupport
  have hdiscS : Summable fun z => if z ∈ s then multDiff Z Z' z * pointImage F G z else 0 :=
    summable_of_ne_finset_zero (s := s) fun z hz => if_neg hz
  have hfarS : Summable fun z => if R < |z.im - X| then multDiff Z Z' z * pointImage F G z
      else 0 :=
    (htot.sub hdiscS).congr fun z => sub_eq_of_eq_add' (hsplit z)
  have hdisc_eq : ∑' z, (if z ∈ s then multDiff Z Z' z * pointImage F G z else 0) =
      ∑ z ∈ s, multDiff Z Z' z * pointImage F G z := by
    rw [tsum_eq_sum (s := s) fun z hz => if_neg hz]
    exact Finset.sum_congr rfl fun z hz => if_pos hz
  refine ⟨hFw, ?_⟩
  have hWdiff := W_sub_W_eq_tsum hZ hZ' hFw.1 hFw.hasCompactSupport hGw.1 hGw.hasCompactSupport
  rw [tsum_congr hsplit, hdiscS.tsum_add hfarS, hdisc_eq] at hWdiff
  -- the far tail
  obtain ⟨hfs, hfle⟩ := tsum_far_multDiff_le hZ hZ' hk ha hFdec hGdec hR
  have hfnorm : ∀ z, ‖(if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ =
      farTerm (multDiff Z Z') F G X R z := fun z => by
    unfold farTerm
    split_ifs
    · rw [norm_mul]
    · rw [norm_zero]
  obtain ⟨Tl, hTl⟩ : ∃ Tl, Tl = M * M * Real.exp a * (5 / 4 * (1 + |X|) ^ 2 /
      (1 + R) ^ (2 * k - 2)) * ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) :=
    ⟨_, rfl⟩
  have hfarle : ‖∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ ≤
      Tl := hTl ▸
    (norm_tsum_le_tsum_norm (hfs.congr fun z => (hfnorm z).symm)).trans
      ((tsum_congr hfnorm).le.trans hfle)
  -- the moment and the relative error
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = ∑ z ∈ s, multDiff Z Z' z * (gammaOf z - gammaOf z₀) ^ j :=
    ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = ∑ z ∈ s, multDiff Z Z' z * (gammaOf z - gammaOf z₀) ^ j *
      (Φ (gammaOf z - X) - Φ ω) := ⟨_, rfl⟩
  have hsum_eq : ∑ z ∈ s, multDiff Z Z' z * pointImage F G z = (-I) ^ j * (Φ ω * μ + E) := by
    rw [hμ, hE, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [hPI]; ring
  have hnormI : ‖(-I : ℂ) ^ j‖ = 1 := by rw [norm_pow, norm_neg, Complex.norm_I, one_pow]
  have hΦω : ‖Φ ω‖ = ‖paperFT F₁ ω‖ * ‖paperFT G₁ (conj ω)‖ := by
    simp only [hΦ]; rw [norm_mul, Complex.norm_conj]
  have hslowΦ : ∀ z ∈ s, ‖Φ (gammaOf z - X) - Φ ω‖ ≤ 6 * (r * Λ) * ‖Φ ω‖ := by
    intro z hz
    have hdz : ‖(gammaOf z - X) - ω‖ ≤ r := by
      rw [show (gammaOf z - X) - ω = gammaOf z - gammaOf z₀ by rw [hω]; ring, norm_gammaOf_sub]
      exact hsd z hz
    rw [hΦω]
    exact norm_pairImage_sub_le_slow (u := paperFT F₁) (v := paperFT G₁) hΛ0 hr hrΛ hrD hF₁sl
      hG₁sl hdz
  have hLip : ‖E‖ ≤ (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (j + 1) * (6 * Λ) * ‖Φ ω‖ := by
    rw [hE]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun z hz => ?_
    have hdz : ‖gammaOf z - gammaOf z₀‖ ≤ r := by rw [norm_gammaOf_sub]; exact hsd z hz
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖multDiff Z Z' z‖ * ‖gammaOf z - gammaOf z₀‖ ^ j * ‖Φ (gammaOf z - X) - Φ ω‖
        ≤ ‖multDiff Z Z' z‖ * r ^ j * (6 * (r * Λ) * ‖Φ ω‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdz j)
            (norm_nonneg _)) (hslowΦ z hz) (norm_nonneg _) (by positivity)
      _ = ‖multDiff Z Z' z‖ * r ^ (j + 1) * (6 * Λ) * ‖Φ ω‖ := by ring
  have hPI0' : pointImage (localWindow X F₁) G z₀ = Φ ω := by rw [hG, hPI0]
  rw [hWdiff, hsum_eq, hPI0', ← hμ]
  have e : (-I) ^ j * (Φ ω * μ + E) +
      ∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0) -
        (-I) ^ j * Φ ω * μ = (-I) ^ j * E +
      ∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0) := by ring
  rw [e]
  calc _ ≤ ‖(-I) ^ j * E‖ +
        ‖∑' z, (if R < |z.im - X| then multDiff Z Z' z * pointImage F G z else 0)‖ :=
        norm_add_le _ _
    _ ≤ (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (j + 1) * (6 * Λ) * ‖Φ ω‖ + Tl := by
        rw [norm_mul, hnormI, one_mul]; exact add_le_add hLip hfarle
    _ = _ := by rw [hTl]; ring

/-- **The camera reads the moments of a near-coincident cluster, relative to its image.** Under
the hypotheses of `norm_discMoment_le`, with the disc radius `r ≤ min(D⁻¹/4, 1/2)` and
`r Λ ≤ 1/2` for `Λ = slowRate (2/D) (localSlack D C₀) η ε C₀`, the moments
`μ_j = Σ_{disc} c(z)(γ_z − γ_{z₀})^j`, `j ≤ J`, satisfy
`‖μ_j‖ ≤ N r^{j+1} · 6Λ + M² e^a (5/4)(1 + |X|)²/(1 + R)^{2k−2} · S / c_η²`.
The disc error is measured against the image at the target, not against the floor. -/
theorem norm_discMoment_le_slow {a D C₀ η ε r : ℝ} {J : ℕ} (hD : 0 < D) (hη : 0 < η) (hε : 0 < ε)
    (hεa : π * D / 2 + 2 * ε ≤ a) {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbs : tsupport b ⊆ Icc (-ε) ε) (hb1 : ∀ y : ℝ, 1 ≤ ‖paperFT b ((y : ℂ) * I)‖) {k m : ℕ}
    (hk : 1 ≤ k) (hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + ((k + J : ℕ) : ℝ) ≤ m)
    {Cm C0 : ℝ}
    (hCm : ∀ w : ℂ, (1 + ‖w‖) ^ m * ‖paperFT b w‖ ≤ Cm * Real.exp (ε * |w.im|))
    (hC0 : ∀ w : ℂ, ‖paperFT b w‖ ≤ C0 * Real.exp (ε * |w.im|))
    {Z Z' : ZeroConfig} (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f) {z₀ : ℂ}
    (hz₀ : |z₀.re - 1 / 2| ≤ 1 / 2) {R : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hrD : r ≤ min (2 * D⁻¹ / 8) (1 / 2))
    (hrΛ : r * slowRate (2 * D⁻¹) (localSlack D C₀) η ε C0 ≤ 1 / 2)
    (hiso : ∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ R → ‖z - z₀‖ ≤ r ∨ η ≤ ‖z - z₀‖)
    (hcount : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - z₀.im| ≤ R ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀)
    {s : Finset ℂ} (hsd : ∀ z ∈ s, ‖z - z₀‖ ≤ r)
    (hds : ∀ z, multDiff Z Z' z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s) {j : ℕ} (hj : j ≤ J) :
    ‖∑ z ∈ s, multDiff Z Z' z * (gammaOf z - gammaOf z₀) ^ j‖ ≤
      (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (j + 1) *
          (6 * slowRate (2 * D⁻¹) (localSlack D C₀) η ε C0) +
        (windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε) ^ 2 * Real.exp a *
          (5 / 4 * (1 + |z₀.im|) ^ 2 / (1 + R) ^ (2 * k - 2)) *
            (∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z))) /
              windowFloor (2 * D⁻¹) (localSlack D C₀) η ^ 2 := by
  obtain ⟨F₁, G₁, -, hG₁, hfl, hread⟩ := discMoment_readout_slow hD hη hε hεa hb hbs hb1 hk hm
    hCm hC0 hZ hZ' hz₀ hR hr hrR hrD hrΛ hiso hcount hsd hds
  obtain ⟨hFj, hbd⟩ := hread j hj
  rw [W_eq_of_mimic hZ hZ' hW hFj (apertureWindow_localWindow hG₁ _), sub_self] at hbd
  have hc0 : 0 < windowFloor (2 * D⁻¹) (localSlack D C₀) η :=
    windowFloor_pos (by positivity) (by unfold localSlack; positivity) hη
  have hSg0 : 0 ≤ ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) :=
    tsum_nonneg fun z => div_nonneg (norm_nonneg _)
      (by have := Complex.normSq_nonneg (gammaOf z); linarith)
  have hTl0 : 0 ≤ (windowGrowth (2 * D⁻¹) (localSlack D C₀) * Cm * C0 * Real.exp ε) ^ 2 *
      Real.exp a * (5 / 4 * (1 + |z₀.im|) ^ 2 / (1 + R) ^ (2 * k - 2)) *
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) :=
    mul_nonneg (by positivity) hSg0
  have h := readout_div_le hc0 hfl hTl0 hbd
  rwa [zero_div, zero_sub, norm_neg] at h

/-! ### Polynomial rates for clusters of Riemann–von Mangoldt type -/

/-- The slow rate at spacing `2/D`: `Λ ≤ πD e^{πD/2} + 2e^{2ε} + 16σ(1 + σ(η⁻¹ + D)) D² S₀` with
`σ = slackBound ℓ`. -/
theorem slowRate_le {D C₀ ℓ η ε : ℝ} (hD : 1 ≤ D) (hC : |C₀| ≤ ℓ * D) (hη : 0 < η) :
    slowRate (2 * D⁻¹) (localSlack D C₀) η ε 1 ≤
      π * D * Real.exp (π * D / 2) + 2 * Real.exp (2 * ε) +
        16 * slackBound ℓ * (1 + slackBound ℓ * (η⁻¹ + D)) * D ^ 2 * latticeSumConst := by
  have hD0 : 0 < D := by linarith
  have hσ := windowSlack_localSlack_le hD hC
  have hσ0 := windowSlack_localSlack_nonneg (C₀ := C₀) hD0
  obtain ⟨L', hL'⟩ : ∃ L', L' = windowSlack (2 * D⁻¹) (localSlack D C₀) := ⟨_, rfl⟩
  rw [← hL'] at hσ hσ0
  have hmin : min η (2 * D⁻¹ / 2) = min η D⁻¹ := by ring_nf
  have hη' : 0 < min η D⁻¹ := lt_min hη (inv_pos.mpr hD0)
  have hinv : (min η D⁻¹)⁻¹ ≤ η⁻¹ + D := by
    rcases min_choice η D⁻¹ with h | h
    · rw [h]; linarith
    · rw [h, inv_inv]; linarith [inv_pos.mpr hη]
  have hS0 := latticeSumConst_nonneg
  unfold slowRate productRate
  rw [← hL', hmin, show π / (2 * D⁻¹) = π * D / 2 by field_simp, one_mul]
  have hP : 64 * L' * (1 + L' / min η D⁻¹) / (2 * D⁻¹) ^ 2 * latticeSumConst ≤
      16 * slackBound ℓ * (1 + slackBound ℓ * (η⁻¹ + D)) * D ^ 2 * latticeSumConst := by
    have e : 64 * L' * (1 + L' / min η D⁻¹) / (2 * D⁻¹) ^ 2 =
        16 * L' * (1 + L' * (min η D⁻¹)⁻¹) * D ^ 2 := by field_simp; ring
    rw [e]
    have h1 : L' * (min η D⁻¹)⁻¹ ≤ slackBound ℓ * (η⁻¹ + D) :=
      mul_le_mul hσ hinv (inv_pos.mpr hη').le (hσ0.trans hσ)
    have h2 : 16 * L' * (1 + L' * (min η D⁻¹)⁻¹) ≤
        16 * slackBound ℓ * (1 + slackBound ℓ * (η⁻¹ + D)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by positivity)) hS0
  linarith [show 2 * (π * D / 2) * Real.exp (π * D / 2) = π * D * Real.exp (π * D / 2) by ring]

/-- The exponent `κ_λ = πλ/2 + λ + 3` of the slow rate at aperture `λ · ½ log(T/2π)`. -/
def slowExponent (lam : ℝ) : ℝ := π * lam / 2 + lam + 3

/-- The constant of the slow rate. -/
def slowConst (lam ℓ M' : ℝ) : ℝ :=
  π * lam + 2 + 64 * slackBound ℓ * lam ^ 2 * latticeSumConst *
    (1 + slackBound ℓ * (2 * π) ^ M' + slackBound ℓ * lam)

theorem rpow_two_pi_exp {u x : ℝ} : (2 * π * Real.exp u) ^ x = (2 * π) ^ x * Real.exp (u * x) := by
  rw [Real.mul_rpow (by positivity) (Real.exp_pos u).le, ← Real.exp_mul]

/-- **The slow rate is polynomial in the height.** At density `D ≤ λu`, bump width
`ε = βu/8` (`β ≤ λ`), isolation `η = T^{−M'}` and `T = 2πe^u` with `e^u ≥ 6 · slowConst`,
`6Λ ≤ T^{M' + κ_λ}`. -/
theorem six_slowRate_le_rpow {lam β ℓ M' T u D C₀ ε η : ℝ} (hu1 : 1 ≤ u)
    (hTu : T = 2 * π * Real.exp u) (hM' : 0 ≤ M') (hlam : 0 < lam)
    (hβlam : β ≤ lam) (hD1 : 1 ≤ D) (hDup : D ≤ lam * u) (hC : |C₀| ≤ ℓ * D)
    (hε : ε = β * u / 8) (hη : η = T ^ (-M'))
    (hbig : 6 * slowConst lam ℓ M' ≤ Real.exp u) :
    6 * slowRate (2 * D⁻¹) (localSlack D C₀) η ε 1 ≤ T ^ (M' + slowExponent lam) := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by rw [hTu]; positivity
  have hη0 : 0 < η := by rw [hη]; exact Real.rpow_pos_of_pos hT0 _
  have hℓ0 : 0 ≤ ℓ := nonneg_of_mul_nonneg_left ((abs_nonneg C₀).trans hC) (by linarith)
  have hσ0 : 0 ≤ slackBound ℓ := by unfold slackBound; linarith
  have hS0 := latticeSumConst_nonneg
  have hΛ := slowRate_le (ε := ε) hD1 hC hη0
  set σ := slackBound ℓ
  set E := Real.exp u with hE
  have hE1 : 1 ≤ E := Real.one_le_exp hu0.le
  have huE : u ≤ E := by linarith [Real.add_one_le_exp u]
  have hu2E : u ^ 2 ≤ 4 * E := by
    have := HTGeometry.sq_div_four_le_exp hu0.le
    linarith
  -- the three exponentials
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = M' + (π * lam / 2 + lam + 2) := ⟨_, rfl⟩
  have hpil : 0 ≤ π * lam / 2 := by have := mul_pos Real.pi_pos hlam; linarith
  have hκ1 : π * lam / 2 + 1 ≤ κ := by rw [hκ]; linarith
  have hκ2 : β * u / 4 ≤ κ * u := by
    have : β / 4 ≤ κ := by rw [hκ]; linarith
    have := mul_le_mul_of_nonneg_right this hu0.le
    linarith
  have hκ3 : M' + 2 ≤ κ := by rw [hκ]; linarith
  have hexpκ : ∀ x, x ≤ κ → Real.exp (x * u) ≤ Real.exp (κ * u) := fun x hx =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hx hu0.le)
  -- term 1
  have ht1 : π * D * Real.exp (π * D / 2) ≤ π * lam * Real.exp (κ * u) := by
    have h1 : Real.exp (π * D / 2) ≤ Real.exp (π * lam / 2 * u) := by
      refine Real.exp_le_exp.mpr ?_
      have := mul_le_mul_of_nonneg_left hDup Real.pi_pos.le
      linarith
    have h2 : π * D ≤ π * lam * E := by
      have := mul_le_mul_of_nonneg_left (hDup.trans (mul_le_mul_of_nonneg_left huE hlam.le))
        Real.pi_pos.le
      linarith
    calc π * D * Real.exp (π * D / 2) ≤ π * lam * E * Real.exp (π * lam / 2 * u) :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = π * lam * Real.exp ((π * lam / 2 + 1) * u) := by
          rw [hE, mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ π * lam * Real.exp (κ * u) :=
          mul_le_mul_of_nonneg_left (hexpκ _ hκ1) (by positivity)
  -- term 2
  have ht2 : 2 * Real.exp (2 * ε) ≤ 2 * Real.exp (κ * u) := by
    rw [hε]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  -- term 3
  have hηinv : η⁻¹ = (2 * π) ^ M' * Real.exp (u * M') := by
    rw [hη, Real.rpow_neg hT0.le, inv_inv, hTu, rpow_two_pi_exp]
  have hM'E : Real.exp (u * M') * E ≤ Real.exp (κ * u) := by
    rw [hE, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_right (show M' + 1 ≤ κ by linarith) hu0.le
    linarith
  have ht3 : 16 * σ * (1 + σ * (η⁻¹ + D)) * D ^ 2 * latticeSumConst ≤
      64 * σ * lam ^ 2 * latticeSumConst * (1 + σ * (2 * π) ^ M' + σ * lam) *
        Real.exp (κ * u) := by
    have hD2 : D ^ 2 ≤ lam ^ 2 * (4 * E) := by
      have h1 : D ^ 2 ≤ (lam * u) ^ 2 := pow_le_pow_left₀ (by linarith) hDup 2
      rw [mul_pow] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hu2E (sq_nonneg lam))
    have hP : 0 ≤ (2 * π) ^ M' := by positivity
    have hE1κ : E ≤ Real.exp (κ * u) := by
      have := hexpκ 1 (by linarith)
      rwa [one_mul] at this
    have hE2κ : E * E ≤ Real.exp (κ * u) := by
      have := hexpκ 2 (by linarith)
      rwa [show Real.exp (2 * u) = E * E by rw [hE, ← Real.exp_add]; ring_nf] at this
    have hDE : D * E ≤ lam * (E * E) := by
      have := mul_le_mul_of_nonneg_right (hDup.trans (mul_le_mul_of_nonneg_left huE hlam.le))
        (Real.exp_pos u).le
      rw [← hE] at this
      linarith
    have hinner : (1 + σ * (η⁻¹ + D)) * E ≤
        (1 + σ * (2 * π) ^ M' + σ * lam) * Real.exp (κ * u) := by
      rw [hηinv]
      have h1 : σ * ((2 * π) ^ M' * Real.exp (u * M')) * E ≤
          σ * (2 * π) ^ M' * Real.exp (κ * u) := by
        have := mul_le_mul_of_nonneg_left hM'E (mul_nonneg hσ0 hP)
        linarith
      have h2 : σ * D * E ≤ σ * lam * Real.exp (κ * u) := by
        have h3 := mul_le_mul_of_nonneg_left hDE hσ0
        have h4 := mul_le_mul_of_nonneg_left hE2κ (mul_nonneg hσ0 hlam.le)
        linarith
      have e : (1 + σ * ((2 * π) ^ M' * Real.exp (u * M') + D)) * E =
          E + σ * ((2 * π) ^ M' * Real.exp (u * M')) * E + σ * D * E := by ring
      rw [e]
      linarith
    calc 16 * σ * (1 + σ * (η⁻¹ + D)) * D ^ 2 * latticeSumConst
        ≤ 16 * σ * (1 + σ * (η⁻¹ + D)) * (lam ^ 2 * (4 * E)) * latticeSumConst := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD2 ?_) hS0
          have : 0 ≤ η⁻¹ := (inv_pos.mpr hη0).le
          positivity
      _ = 64 * σ * lam ^ 2 * latticeSumConst * ((1 + σ * (η⁻¹ + D)) * E) := by ring
      _ ≤ 64 * σ * lam ^ 2 * latticeSumConst *
            ((1 + σ * (2 * π) ^ M' + σ * lam) * Real.exp (κ * u)) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = _ := by ring
  -- assembling
  have hsum : slowRate (2 * D⁻¹) (localSlack D C₀) η ε 1 ≤
      slowConst lam ℓ M' * Real.exp (κ * u) := by
    unfold slowConst
    linarith
  have hfin : Real.exp ((κ + 1) * u) ≤ T ^ (M' + slowExponent lam) := by
    rw [hTu, rpow_two_pi_exp]
    have e : (κ + 1) * u = u * (M' + slowExponent lam) := by
      rw [hκ, slowExponent]; ring
    rw [e]
    exact le_mul_of_one_le_left (Real.exp_pos _).le
      (Real.one_le_rpow (by linarith [Real.pi_gt_three])
        (by unfold slowExponent; have := mul_pos Real.pi_pos hlam; linarith))
  calc 6 * slowRate (2 * D⁻¹) (localSlack D C₀) η ε 1
      ≤ 6 * (slowConst lam ℓ M' * Real.exp (κ * u)) := by linarith
    _ = 6 * slowConst lam ℓ M' * Real.exp (κ * u) := by ring
    _ ≤ E * Real.exp (κ * u) := mul_le_mul_of_nonneg_right hbig (Real.exp_pos _).le
    _ = Real.exp ((κ + 1) * u) := by rw [hE, ← Real.exp_add]; ring_nf
    _ ≤ _ := hfin

/-! ### The tail budget at polynomial isolation -/

theorem max_log_inv_rpow_neg_le' {T u M : ℝ} (hu1 : 1 ≤ u)
    (hTu : T = 2 * π * Real.exp u) (hM : 0 ≤ M) :
    max 0 (Real.log (1 / T ^ (-M))) ≤ 8 * M * u := by
  have h2π0 : 0 < 2 * π := by positivity
  have hT0 : 0 < T := by rw [hTu]; positivity
  have hlog2π : Real.log (2 * π) ≤ 7 := by
    have := Real.log_le_sub_one_of_pos h2π0
    linarith [Real.pi_le_four]
  have hlogT : Real.log T ≤ 8 * u := by
    rw [hTu, Real.log_mul h2π0.ne' (Real.exp_pos u).ne', Real.log_exp]
    linarith
  rw [one_div, Real.rpow_neg hT0.le, inv_inv, Real.log_rpow hT0]
  exact max_le (by positivity) ((mul_le_mul_of_nonneg_left hlogT hM).trans_eq (by ring))

theorem exp_le_one_add_quarter_pow {T u : ℝ} {k : ℕ} (hTu : T = 2 * π * Real.exp u)
    (hk : 1 ≤ k) : Real.exp (2 * ((k : ℝ) - 1) * u) ≤ (1 + T / 4) ^ (2 * k - 2) := by
  have e1 : 2 * k - 2 = 2 * (k - 1) := by omega
  have e2 : 2 * ((k : ℝ) - 1) * u = ((2 * (k - 1) : ℕ) : ℝ) * u := by
    push_cast [hk]; ring
  have hexp : Real.exp u ≤ 1 + T / 4 := by
    rw [hTu]
    have := Real.exp_pos u
    nlinarith [Real.pi_gt_three]
  rw [e1, e2, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos u).le hexp _

theorem one_add_abs_im_sq_le {T u : ℝ} {z₀ : ℂ} (hu1 : 1 ≤ u)
    (hTu : T = 2 * π * Real.exp u) (hz₀ : |z₀.im - T| ≤ T / 4) :
    (1 + |z₀.im|) ^ 2 ≤ 121 * Real.exp (2 * u) := by
  have hT0 : 0 < T := by rw [hTu]; positivity
  have habs : |z₀.im| ≤ 5 * T / 4 := by
    have h1 := abs_le.mp hz₀
    rw [abs_le]; constructor <;> linarith
  have hexp1 : 1 ≤ Real.exp u := Real.one_le_exp (by linarith)
  have hlin : 1 + |z₀.im| ≤ 11 * Real.exp u := by
    have h5T : 5 * T / 4 ≤ 10 * Real.exp u := by
      rw [hTu]; have := Real.exp_pos u; nlinarith [Real.pi_le_four]
    linarith
  calc (1 + |z₀.im|) ^ 2 ≤ (11 * Real.exp u) ^ 2 := pow_le_pow_left₀ (by positivity) hlin 2
    _ = 121 * (Real.exp u * Real.exp u) := by ring
    _ = 121 * Real.exp (2 * u) := by rw [← Real.exp_add, two_mul]

/-- **The tail budget at polynomial isolation.** With isolation `η = T^{−M}`, density `D ≤ λu`,
bump width `ε = βu/8`, spline order `m ≤ M_K u²` and decay order `k ≥ (K + K')u²`
(`K = c/2 + 2`), the camera tail `E` with `E (1 + T/4)^{2k−2} ≤ localCameraConst · (1 + |X|)² S`
satisfies `E ≤ e^{−2K'u³}/4`. -/
theorem camera_tail_budget {lam β M ℓ c K K' MK ρ α q S'' T u a ε D C₀ η Sg E : ℝ} {z₀ : ℂ}
    {k m : ℕ} (hu1 : 1 ≤ u) (hTu : T = 2 * π * Real.exp u) (hM : 0 ≤ M) (hlam0 : 0 < lam)
    (hβlam : β ≤ lam) (hℓ0 : 0 ≤ ℓ)
    (hc : c = 2 * growthRate ℓ * lam ^ 2 + 2 * floorRate ℓ * lam ^ 2 * (lam + 8 * M))
    (hK : K = c / 2 + 2) (hMK0 : 0 < MK) (hρ0 : 0 < ρ)
    (hα : α = 1 / (8 * MK * (1 + ρ))) (hα0 : 0 < α)
    (hq : q = max 0 (Real.log α⁻¹)) (hS''1 : 1 ≤ S'')
    (hu_bud : 2 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1 ≤ u)
    (ha : a = lam * (u / 2)) (hε : ε = β * u / 8) (hε0 : 0 < ε)
    (hD1 : 1 ≤ D) (hDup : D ≤ lam * u) (hC₀ℓ : |C₀| ≤ ℓ * D)
    (hη : η = T ^ (-M)) (hη0 : 0 < η)
    (hkK : (K + K') * u ^ 2 ≤ k) (hk1 : 1 ≤ k)
    (hmle : (m : ℝ) ≤ MK * u ^ 2) (hmε : (m : ℝ) / ε ≤ ρ * u)
    (hz₀ : |z₀.im - T| ≤ T / 4) (hSg0 : 0 ≤ Sg) (hSgS'' : Sg ≤ S'')
    (htail : E * (1 + T / 4) ^ (2 * k - 2) ≤
      localCameraConst a D C₀ η ε ((4 * (1 + (m : ℝ) / ε)) ^ m) 1 * (1 + |z₀.im|) ^ 2 * Sg) :
    E ≤ Real.exp (-(2 * K' * u ^ 3)) / 4 := by
  have hu0 : 0 < u := by linarith
  have hD0 : 0 < D := by linarith
  have hg0 := growthRate_nonneg hℓ0
  have hf0 := floorRate_nonneg hℓ0
  have hq0 : 0 ≤ q := by rw [hq]; exact le_max_left _ _
  have hlS''0 : 0 ≤ Real.log S'' := Real.log_nonneg hS''1
  obtain ⟨Cm, hCm⟩ : ∃ Cm, Cm = (4 * (1 + (m : ℝ) / ε)) ^ m := ⟨_, rfl⟩
  rw [← hCm] at htail
  have hCm0 : 0 < Cm := by rw [hCm]; positivity
  have hlogCm : 2 * Real.log Cm ≤ u ^ 3 + 2 * MK * q * u ^ 2 := by
    rw [hCm, Real.log_pow]
    have h4u : 4 * (1 + (m : ℝ) / ε) ≤ 4 * (1 + ρ) * u := by
      have : 1 + ρ * u ≤ (1 + ρ) * u := by linarith [mul_le_mul_of_nonneg_left hu1 hρ0.le]
      linarith
    have hlog1 : Real.log (4 * (1 + (m : ℝ) / ε)) ≤ Real.log (4 * (1 + ρ) * u) :=
      Real.log_le_log (by positivity) h4u
    have hlog2 := log_le_mul_add_log_inv (show 0 < 4 * (1 + ρ) * u by positivity) hα0
    have hαmul : α * (4 * (1 + ρ) * u) = u / (2 * MK) := by
      rw [hα]; field_simp; ring
    have hlog3 : Real.log (4 * (1 + (m : ℝ) / ε)) ≤ u / (2 * MK) + q := by
      have hle_q : Real.log α⁻¹ ≤ q := by rw [hq]; exact le_max_right _ _
      linarith
    have h1ge : 1 ≤ 4 * (1 + (m : ℝ) / ε) := by
      have : 0 ≤ (m : ℝ) / ε := div_nonneg (Nat.cast_nonneg m) hε0.le
      linarith
    calc 2 * ((m : ℝ) * Real.log (4 * (1 + (m : ℝ) / ε)))
        ≤ 2 * ((MK * u ^ 2) * (u / (2 * MK) + q)) := by
          have := mul_le_mul hmle hlog3 (Real.log_nonneg h1ge) (by positivity)
          linarith
      _ = u ^ 3 + 2 * MK * q * u ^ 2 := by field_simp
  have hGterm : 2 * (growthRate ℓ * D * (1 + Real.log D)) ≤
      2 * growthRate ℓ * lam ^ 2 * u ^ 3 := by
    have h1 : D * (1 + Real.log D) ≤ D ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_left (one_add_log_le hD1) hD0.le
    have h2 : D ^ 2 ≤ (lam * u) ^ 2 := pow_le_pow_left₀ hD0.le hDup 2
    have hu23 : u ^ 2 ≤ u ^ 3 := by
      have := mul_le_mul_of_nonneg_right hu1 (sq_nonneg u)
      linarith [show 1 * u ^ 2 = u ^ 2 by ring, show u * u ^ 2 = u ^ 3 by ring]
    have h3 : (lam * u) ^ 2 ≤ lam ^ 2 * u ^ 3 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hu23 (sq_nonneg lam)
    have h4 := mul_le_mul_of_nonneg_left ((h1.trans h2).trans h3) hg0
    linarith
  have hFterm : 2 * (floorRate ℓ * D * (1 + Real.log D) *
      (1 + Real.log D + max 0 (Real.log (1 / η)))) ≤
      2 * floorRate ℓ * lam ^ 2 * (lam + 8 * M) * u ^ 3 := by
    have hmax := max_log_inv_rpow_neg_le' hu1 hTu hM
    rw [← hη] at hmax
    have h1 : 1 + Real.log D ≤ lam * u := (one_add_log_le hD1).trans hDup
    have h2 : 1 + Real.log D + max 0 (Real.log (1 / η)) ≤ (lam + 8 * M) * u := by linarith
    have h3 : D * (1 + Real.log D) ≤ lam ^ 2 * u ^ 2 := by
      calc D * (1 + Real.log D) ≤ (lam * u) * (lam * u) :=
            mul_le_mul hDup h1 (by linarith [Real.log_nonneg hD1]) (mul_nonneg hlam0.le hu0.le)
        _ = lam ^ 2 * u ^ 2 := by ring
    have h4 : D * (1 + Real.log D) * (1 + Real.log D + max 0 (Real.log (1 / η))) ≤
        lam ^ 2 * (lam + 8 * M) * u ^ 3 := by
      calc D * (1 + Real.log D) * (1 + Real.log D + max 0 (Real.log (1 / η)))
          ≤ (lam ^ 2 * u ^ 2) * ((lam + 8 * M) * u) :=
            mul_le_mul h3 h2
              (by linarith [Real.log_nonneg hD1, le_max_left 0 (Real.log (1 / η))])
              (by have := mul_nonneg hlam0.le hu0.le; positivity)
        _ = lam ^ 2 * (lam + 8 * M) * u ^ 3 := by ring
    have h5 := mul_le_mul_of_nonneg_left h4 hf0
    linarith
  have hB := localCameraConst_subspacing_le (a := a) (ε := ε) hD1 hC₀ℓ hη0 hCm0
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = 2 * (growthRate ℓ * D * (1 + Real.log D)) +
      2 * Real.log Cm + 2 * ε + a +
      2 * (floorRate ℓ * D * (1 + Real.log D) *
        (1 + Real.log D + max 0 (Real.log (1 / η)))) := ⟨_, rfl⟩
  rw [← hΦ] at hB
  have h2εa : 2 * ε + a ≤ lam * u := by
    rw [hε, ha]
    have : β * u ≤ lam * u := mul_le_mul_of_nonneg_right hβlam hu0.le
    linarith
  have hΦle : Φ ≤ (c + 1) * u ^ 3 + 2 * MK * q * u ^ 2 + lam * u := by
    rw [hΦ, hc]
    linarith [hGterm, hFterm, hlogCm, h2εa]
  have hY := one_add_abs_im_sq_le hu1 hTu hz₀
  have hlog605 : Real.log 605 ≤ 605 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 605)
    linarith
  have h4prod : 4 * (localCameraConst a D C₀ η ε Cm 1 * (1 + |z₀.im|) ^ 2 * Sg) ≤
      Real.exp (Φ + 2 * u + Real.log S'' + Real.log 605) := by
    calc 4 * (localCameraConst a D C₀ η ε Cm 1 * (1 + |z₀.im|) ^ 2 * Sg)
        ≤ 4 * (5 / 4 * Real.exp Φ * (121 * Real.exp (2 * u)) * S'') := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul (mul_le_mul hB hY (by positivity) (by positivity)) hSgS'' hSg0
            (by positivity)
      _ = Real.exp (Real.log 605) * Real.exp Φ * Real.exp (2 * u) *
            Real.exp (Real.log S'') := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 605), Real.exp_log (by linarith)]
          ring
      _ = Real.exp (Φ + 2 * u + Real.log S'' + Real.log 605) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
  have hexp_cmp : Φ + 2 * u + Real.log S'' + Real.log 605 + 2 * K' * u ^ 3 ≤
      2 * ((k : ℝ) - 1) * u := by
    have hk_low : (c + 4) * u ^ 3 + 2 * K' * u ^ 3 - 2 * u ≤ 2 * ((k : ℝ) - 1) * u := by
      have h1 : 2 * ((K + K') * u ^ 2 - 1) * u ≤ 2 * ((k : ℝ) - 1) * u :=
        mul_le_mul_of_nonneg_right (by linarith) hu0.le
      rw [hK] at h1
      linarith [show 2 * ((c / 2 + 2 + K') * u ^ 2 - 1) * u =
        (c + 4) * u ^ 3 + 2 * K' * u ^ 3 - 2 * u by ring]
    have hu2 : u ≤ u ^ 2 := by
      simpa [sq] using mul_le_mul_of_nonneg_right hu1 hu0.le
    have h1u2 : 1 ≤ u ^ 2 := hu1.trans hu2
    have hrem : 2 * MK * q * u ^ 2 + (lam + 4) * u + (Real.log S'' + 605) ≤ u ^ 3 := by
      have hlin1 : (lam + 4) * u ≤ (lam + 4) * u ^ 2 :=
        mul_le_mul_of_nonneg_left hu2 (by linarith)
      have hlin2 : Real.log S'' + 605 ≤ (Real.log S'' + 605) * u ^ 2 :=
        le_mul_of_one_le_right (by positivity) h1u2
      have hsum : (2 * MK * q + (lam + 4) + (Real.log S'' + 605)) * u ^ 2 ≤ u * u ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [hu_bud]) (sq_nonneg u)
      linarith [show u * u ^ 2 = u ^ 3 by ring,
        show (2 * MK * q + (lam + 4) + (Real.log S'' + 605)) * u ^ 2 =
          2 * MK * q * u ^ 2 + (lam + 4) * u ^ 2 + (Real.log S'' + 605) * u ^ 2 by ring]
    linarith [hΦle, hlog605, hk_low, hrem, pow_nonneg hu0.le 3]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (1 + T / 4) ^ (2 * k - 2) := ⟨_, rfl⟩
  have hQ0 : 0 < Q := by rw [hQ, hTu]; positivity
  have h4bound : 4 * (localCameraConst a D C₀ η ε Cm 1 * (1 + |z₀.im|) ^ 2 * Sg) ≤
      Q * Real.exp (-(2 * K' * u ^ 3)) := by
    refine h4prod.trans ?_
    have h1 : Real.exp (Φ + 2 * u + Real.log S'' + Real.log 605) ≤
        Real.exp (2 * ((k : ℝ) - 1) * u) * Real.exp (-(2 * K' * u ^ 3)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    rw [hQ]; exact exp_le_one_add_quarter_pow hTu hk1
  rw [← hQ] at htail
  have h4E : 4 * E * Q ≤ Real.exp (-(2 * K' * u ^ 3)) * Q := by
    calc 4 * E * Q = 4 * (E * Q) := by ring
      _ ≤ 4 * (localCameraConst a D C₀ η ε Cm 1 * (1 + |z₀.im|) ^ 2 * Sg) :=
          mul_le_mul_of_nonneg_left htail (by norm_num)
      _ ≤ _ := h4bound.trans_eq (by ring)
  have := le_of_mul_le_mul_right h4E hQ0
  linarith

/-! ### Second-order local inversion at polynomial scales -/

theorem slowConst_nonneg {lam ℓ M' : ℝ} (hlam : 0 < lam) (hℓ : 0 ≤ ℓ) :
    0 ≤ slowConst lam ℓ M' := by
  have hσ : 0 ≤ slackBound ℓ := by unfold slackBound; linarith
  have := latticeSumConst_nonneg
  unfold slowConst
  positivity

/-- Disc radii below `T^{−(M' + κ + 1)}` are small for the camera: `r ≤ min(D⁻¹/4, 1/2)` and
`rΛ ≤ 1/2` once `6Λ ≤ T^{M' + κ}`, `4D ≤ T²` and `T ≥ 2`. -/
theorem disc_radius_small {r T D Λ x : ℝ} (hT2' : 2 ≤ T) (hx : 1 ≤ x)
    (hr : r ≤ T ^ (-(x + 1))) (hΛ0 : 0 ≤ Λ) (hΛ : 6 * Λ ≤ T ^ x) (hD : 0 < D)
    (hDT : 4 * D ≤ T ^ 2) :
    r ≤ min (2 * D⁻¹ / 8) (1 / 2) ∧ r * Λ ≤ 1 / 2 := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hr2 : r ≤ T ^ (-2 : ℝ) :=
    hr.trans (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith))
  have hT2 : T ^ (-2 : ℝ) = (T ^ 2)⁻¹ := by
    rw [Real.rpow_neg hT0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hT2] at hr2
  have hTsq : 1 ≤ T ^ 2 := one_le_pow₀ hT1
  refine ⟨le_min ?_ ?_, ?_⟩
  · have : (T ^ 2)⁻¹ ≤ 2 * D⁻¹ / 8 := by
      rw [show 2 * D⁻¹ / 8 = (4 * D)⁻¹ by field_simp; ring]
      exact inv_anti₀ (by positivity) hDT
    linarith
  · have : (T ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hTsq
    have h2 : (T ^ 2)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num), one_div, inv_inv]
      nlinarith only [hT2']
    linarith
  · have hprod : T ^ (-(x + 1)) * T ^ x = T⁻¹ := by
      rw [← Real.rpow_add hT0, show -(x + 1) + x = -1 by ring, Real.rpow_neg_one]
    have h6 : 6 * (r * Λ) ≤ T⁻¹ := by
      calc 6 * (r * Λ) = r * (6 * Λ) := by ring
        _ ≤ T ^ (-(x + 1)) * T ^ x :=
            mul_le_mul hr hΛ (by positivity) (by positivity)
        _ = T⁻¹ := hprod
    have : T⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hT1
    linarith

/-- **The analytic core of `discMoment_readout_rvm`.** For the camera parameters chosen there, the
image reads the disc moments: `‖ΔW_j/((−i)^j Φ) − μ_j‖ ≤ N r^{j+1} T^{M' + κ_λ} + e^{−K'u³}`. -/
theorem rvm_readout_core {lam β M' K' ℓ c K MK ρ α q S'' T u a ε D C₀ η r : ℝ} {k m J : ℕ}
    {Z Z' : ZeroConfig} {z₀ : ℂ} {s : Finset ℂ}
    (hu1 : 1 ≤ u) (hTu : T = 2 * π * Real.exp u) (hM' : 0 ≤ M') (hlam0 : 0 < lam)
    (hβ0 : 0 < β) (hβlam : β ≤ lam) (hℓ0 : 0 ≤ ℓ)
    (hc : c = 2 * growthRate ℓ * lam ^ 2 + 2 * floorRate ℓ * lam ^ 2 * (lam + 8 * M'))
    (hK : K = c / 2 + 2) (hK' : 0 ≤ K') (hMK0 : 0 < MK) (hρ0 : 0 < ρ)
    (hα : α = 1 / (8 * MK * (1 + ρ))) (hα0 : 0 < α) (hq : q = max 0 (Real.log α⁻¹))
    (hS''1 : 1 ≤ S'') (hu_bud : 2 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1 ≤ u)
    (ha : a = lam * (u / 2)) (hε : ε = β * u / 8)
    (hD1 : 1 ≤ D) (hDup : D ≤ lam * u) (hC₀ℓ : |C₀| ≤ ℓ * D) (hDa : π * D / 2 + 2 * ε ≤ a)
    (hη : η = T ^ (-M')) (hkK : (K + K') * u ^ 2 ≤ k) (hk1 : 1 ≤ k)
    (hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + ((k + J : ℕ) : ℝ) ≤ m)
    (hmle : (m : ℝ) ≤ MK * u ^ 2) (hmε : (m : ℝ) / ε ≤ ρ * u)
    (hbig : 6 * slowConst lam ℓ M' ≤ Real.exp u) (h4lam : 4 * lam ≤ Real.exp u)
    (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    (hStail : ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S'')
    (hz₀ : |z₀.im - T| ≤ T / 4) (hz₀re : |z₀.re - 1 / 2| ≤ 1 / 2)
    (hr0 : 0 ≤ r) (hr : r ≤ T ^ (-(M' + slowExponent lam + 1)))
    (hiso' : ∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ T / 4 →
      ‖z - z₀‖ ≤ r ∨ η ≤ ‖z - z₀‖)
    (hcount' : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - z₀.im| ≤ T / 4 ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀)
    (hsd : ∀ z ∈ s, ‖z - z₀‖ ≤ r) (hds : ∀ z, multDiff Z Z' z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s) :
    ∃ F₁ G₁ : ℝ → ℂ, ApertureWindow a F₁ ∧ ApertureWindow a G₁ ∧
      pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀ ≠ 0 ∧
      ∀ j : ℕ, j ≤ J →
        ApertureWindow a (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁)) ∧
        ‖(Z.W (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁)) (localWindow z₀.im G₁) -
            Z'.W (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁)) (localWindow z₀.im G₁)) /
            ((-I) ^ j * pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀) -
          ∑ z ∈ s, multDiff Z Z' z * (gammaOf z - gammaOf z₀) ^ j‖ ≤
          (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (j + 1) * T ^ (M' + slowExponent lam) +
            Real.exp (-(K' * u ^ 3)) := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by rw [hTu]; positivity
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hD0 : 0 < D := by linarith
  have hη0 : 0 < η := by rw [hη]; exact Real.rpow_pos_of_pos hT0 _
  have hET : Real.exp u ≤ T := by
    rw [hTu]; nlinarith [Real.exp_pos u, Real.pi_gt_three]
  have hT2 : 2 ≤ T := by
    have := Real.add_one_le_exp u
    linarith
  obtain ⟨b, hb, hbs, hb1, hb0, hbm⟩ := exists_explicit_bump hε0 m
  -- the slow rate and the disc radius
  have hΛ := six_slowRate_le_rpow hu1 hTu hM' hlam0 hβlam hD1 hDup hC₀ℓ hε hη hbig
  have hΛ0 : 0 ≤ slowRate (2 * D⁻¹) (localSlack D C₀) η ε 1 :=
    slowRate_nonneg (by positivity) (localSlack_nonneg hD0) hη0 zero_le_one
  have hDT : 4 * D ≤ T ^ 2 := by
    have h1 : 4 * D ≤ 4 * lam * Real.exp u := by
      have := mul_le_mul_of_nonneg_left (hDup.trans (mul_le_mul_of_nonneg_left
        (show u ≤ Real.exp u by linarith [Real.add_one_le_exp u]) hlam0.le)) (by norm_num : (0 : ℝ) ≤ 4)
      linarith
    have h2 : 4 * lam * Real.exp u ≤ Real.exp u * Real.exp u :=
      mul_le_mul_of_nonneg_right h4lam (Real.exp_pos u).le
    have h3 : Real.exp u * Real.exp u ≤ T ^ 2 := by
      rw [sq]; exact mul_le_mul hET hET (Real.exp_pos u).le hT0.le
    linarith
  obtain ⟨hrD, hrΛ⟩ := disc_radius_small hT2
    (by unfold slowExponent; have := mul_pos Real.pi_pos hlam0; linarith :
      1 ≤ M' + slowExponent lam) hr hΛ0
    hΛ hD0 hDT
  have hrR : r ≤ T / 4 := by
    have : min (2 * D⁻¹ / 8) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have h1 : (1 : ℝ) / 2 ≤ T / 4 := by linarith
    linarith
  -- the moments, read from the image
  obtain ⟨F₁, G₁, hF₁, hG₁, hfl, hread⟩ := discMoment_readout_slow hD0 hη0 hε0 hDa hb hbs hb1 hk1
    hm hbm (C0 := 1) (fun w => by rw [one_mul]; exact hb0 w) hZ hZ' hz₀re (R := T / 4)
    (by positivity) hr0 hrR hrD hrΛ hiso' hcount' hsd hds
  -- the tail
  have hSg0 : 0 ≤ ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) :=
    tsum_nonneg fun z => div_nonneg (norm_nonneg _)
      (by have := Complex.normSq_nonneg (gammaOf z); linarith)
  have hfl0 : 0 < windowFloor (2 * D⁻¹) (localSlack D C₀) η :=
    windowFloor_pos (by positivity) (localSlack_nonneg hD0) hη0
  have hQ0 : 0 < (1 + T / 4) ^ (2 * k - 2) := by positivity
  have hQne := hQ0.ne'
  have hflne : windowFloor (2 * D⁻¹) (localSlack D C₀) η ^ 2 ≠ 0 := (pow_pos hfl0 2).ne'
  have hexp : Real.exp (-(2 * K' * u ^ 3)) / 4 ≤ Real.exp (-(K' * u ^ 3)) := by
    have hK3 : 0 ≤ K' * u ^ 3 := mul_nonneg hK' (pow_pos hu0 3).le
    have : Real.exp (-(2 * K' * u ^ 3)) ≤ Real.exp (-(K' * u ^ 3)) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith [Real.exp_pos (-(2 * K' * u ^ 3))]
  obtain ⟨Tl, hTl⟩ : ∃ Tl, Tl = (windowGrowth (2 * D⁻¹) (localSlack D C₀) *
      (4 * (1 + (m : ℝ) / ε)) ^ m * 1 * Real.exp ε) ^ 2 * Real.exp a *
        (5 / 4 * (1 + |z₀.im|) ^ 2 / (1 + T / 4) ^ (2 * k - 2)) *
          ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) := ⟨_, rfl⟩
  have hTl0 : 0 ≤ Tl := by rw [hTl]; exact mul_nonneg (by positivity) hSg0
  have htail : Tl / windowFloor (2 * D⁻¹) (localSlack D C₀) η ^ 2 ≤ Real.exp (-(K' * u ^ 3)) := by
    rw [hTl]
    refine (camera_tail_budget (z₀ := z₀) (Sg := ∑' z, ‖multDiff Z Z' z‖ /
      (1 + Complex.normSq (gammaOf z))) hu1 hTu hM' hlam0 hβlam hℓ0 hc hK hMK0 hρ0 hα hα0 hq
      hS''1 hu_bud ha hε hε0 hD1 hDup hC₀ℓ hη hη0 hkK hk1 hmle hmε hz₀ hSg0
      hStail (le_of_eq ?_)).trans hexp
    unfold localCameraConst
    field_simp
  have hΦ0 := norm_pos_iff.mp (lt_of_lt_of_le (pow_pos hfl0 2) hfl)
  refine ⟨F₁, G₁, hF₁, hG₁, hΦ0, fun j hj => ?_⟩
  obtain ⟨hFj, hbd⟩ := hread j hj
  rw [← hTl] at hbd
  refine ⟨hFj, (readout_div_le hfl0 hfl hTl0 hbd).trans (add_le_add ?_ htail)⟩
  exact mul_le_mul_of_nonneg_left hΛ
    (mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (pow_nonneg hr0 _))

/-- The density and aperture of the camera at height scale `u`: `D = (θ + β)u/2π`, `β = λ − θ/2`,
`ε = βu/8`, `a = λu/2`, `C₀ = Au`. -/
theorem rvm_density_facts {θ lam A β ℓ u a ε D C₀ : ℝ} (hθ : 0 ≤ θ) (hlam : θ / 2 < lam)
    (hA : 0 ≤ A)
    (hβ : β = lam - θ / 2) (hℓ : ℓ = 2 * π * A / lam) (hu0 : 0 < u) (hu_lam : 2 * π / lam ≤ u)
    (ha : a = lam * (u / 2)) (hε : ε = β * u / 8) (hD : D = (θ + β) / (2 * π) * u)
    (hC₀ : C₀ = A * u) :
    π * D / 2 + 2 * ε ≤ a ∧ 1 ≤ D ∧ D ≤ lam * u ∧ |C₀| ≤ ℓ * D := by
  have h2π0 : 0 < 2 * π := by positivity
  have hlam0 : 0 < lam := by linarith
  have hDlow : lam / (2 * π) * u ≤ D := by
    rw [hD, hβ]
    have : lam ≤ θ + (lam - θ / 2) := by linarith
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right this h2π0.le) hu0.le
  refine ⟨le_of_eq ?_, ?_, ?_, ?_⟩
  · rw [hD, hε, ha, hβ]; field_simp; ring
  · refine le_trans ?_ hDlow
    have h1 := (div_le_iff₀ hlam0).mp hu_lam
    rw [div_mul_eq_mul_div, le_div_iff₀ h2π0]
    linarith
  · rw [hD, hβ]
    have h1 : (θ + (lam - θ / 2)) / (2 * π) ≤ lam := by
      rw [div_le_iff₀ h2π0]
      have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ 2 * π by linarith [Real.pi_gt_three])
        hlam0.le
      linarith
    exact mul_le_mul_of_nonneg_right h1 hu0.le
  · rw [hC₀, abs_of_nonneg (by positivity), hℓ]
    have huD : u ≤ 2 * π / lam * D := by
      calc u = 2 * π / lam * (lam / (2 * π) * u) := by field_simp
        _ ≤ 2 * π / lam * D := mul_le_mul_of_nonneg_left hDlow (by positivity)
    calc A * u ≤ A * (2 * π / lam * D) := mul_le_mul_of_nonneg_left huD hA
      _ = 2 * π * A / lam * D := by ring

/-- The decay and spline orders of the camera: `k = ⌈(K + K')u²⌉₊` and `m = ⌈W⌉₊ + k + J` satisfy
`m ≤ M_K u²` and `m/ε ≤ ρu`. -/
theorem rvm_order_facts {K K' MK e lam β ρ u ε D W : ℝ} {k m J : ℕ} (hK1 : 2 ≤ K) (hK' : 0 ≤ K')
    (he0 : 0 ≤ e) (hlam0 : 0 < lam) (hβ0 : 0 < β) (hMK : MK = e * lam + K + K' + 2 + J)
    (hρ : ρ = 8 * MK / β) (hu1 : 1 ≤ u) (hε : ε = β * u / 8) (hDup : D ≤ lam * u)
    (hW0 : 0 ≤ W) (hWle : W ≤ e * D) (hk : k = ⌈(K + K') * u ^ 2⌉₊)
    (hm : m = ⌈W⌉₊ + (k + J)) :
    (K + K') * u ^ 2 ≤ k ∧ 1 ≤ k ∧ W + ((k + J : ℕ) : ℝ) ≤ m ∧ (m : ℝ) ≤ MK * u ^ 2 ∧
      (m : ℝ) / ε ≤ ρ * u := by
  have hu0 : 0 < u := by linarith
  have hu21 : 1 ≤ u ^ 2 := one_le_pow₀ hu1
  have hkK : (K + K') * u ^ 2 ≤ k := by rw [hk]; exact Nat.le_ceil _
  have hkle : (k : ℝ) ≤ (K + K') * u ^ 2 + 1 := by
    rw [hk]; exact (Nat.ceil_lt_add_one (by positivity)).le
  have hk1 : 1 ≤ k := by
    have h1 : (1 : ℝ) ≤ (K + K') * u ^ 2 :=
      one_le_mul_of_one_le_of_one_le (by linarith) hu21
    exact_mod_cast h1.trans hkK
  have hmle : (m : ℝ) ≤ MK * u ^ 2 := by
    rw [hm, hMK]; push_cast
    have h1 : (⌈W⌉₊ : ℝ) ≤ W + 1 := (Nat.ceil_lt_add_one hW0).le
    have h2 : e * D ≤ e * (lam * u) := mul_le_mul_of_nonneg_left hDup he0
    have hu2 : u ≤ u ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hu0.le hu1
    have h3 : e * (lam * u) ≤ e * lam * u ^ 2 := by
      calc e * (lam * u) = e * lam * u := by ring
        _ ≤ e * lam * u ^ 2 := mul_le_mul_of_nonneg_left hu2 (mul_nonneg he0 hlam0.le)
    have hexp : (e * lam + K + K' + 2 + J) * u ^ 2 =
        e * lam * u ^ 2 + (K + K') * u ^ 2 + 2 * u ^ 2 + J * u ^ 2 := by ring
    have hJ : (J : ℝ) ≤ J * u ^ 2 := le_mul_of_one_le_right (Nat.cast_nonneg J) hu21
    linarith [h1, hWle, h2, h3, hkle, hu21, hexp, hJ]
  refine ⟨hkK, hk1, ?_, hmle, ?_⟩
  · rw [hm]; push_cast; linarith [Nat.le_ceil W]
  · have hε0 : 0 < ε := by rw [hε]; positivity
    rw [div_le_iff₀ hε0, hρ, hε]
    have : 8 * MK / β * u * (β * u / 8) = MK * u ^ 2 := by
      calc 8 * MK / β * u * (β * u / 8) = MK * u ^ 2 * (β / β) := by ring
        _ = MK * u ^ 2 := by rw [div_self hβ0.ne', mul_one]
    rw [this]; exact hmle

/-- **The image reads the disc moments, uniformly in the height.** Let `0 ≤ θ`, `λ > θ/2`,
`A, S, M', K' ≥ 0`, and `κ_λ = πλ/2 + λ + 3`. For all `T ≥ T₀`: let `Z, Z'` be tempered, with
`Σ_z |c(z)|/(1 + |γ_z|²) ≤ S` and cluster count `≤ (θ/2π) log(T/2π)(y − x) + A log(T/2π)` in
`[T/2, 3T/2]`. Let `z₀` lie in `|Im z₀ − T| ≤ T/4`, and let every cluster point in `[T/2, 3T/2]` lie
in the disc `‖z − z₀‖ ≤ r` or at distance `≥ T^{−M'}` from `z₀`, where `r ≤ T^{−(M' + κ_λ + 1)}`.
Then there are windows of aperture `λ · ½ log(T/2π)` with nonzero image `Φ` at `z₀` whose image
differences `ΔW_j` read the disc moments:
`‖ΔW_j/((−i)^j Φ) − μ_j‖ ≤ N r^{j+1} T^{M' + κ_λ} + exp(−K' log³(T/2π))` for every order
`j ≤ J`. -/
theorem discMoment_readout_rvm (J : ℕ) {θ lam A S M' K' : ℝ} (hθ : 0 ≤ θ) (hlam : θ / 2 < lam)
    (hA : 0 ≤ A) (_hS : 0 ≤ S) (hM' : 0 ≤ M') (hK' : 0 ≤ K') :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → |z₀.re - 1 / 2| ≤ 1 / 2 →
        ∀ r : ℝ, 0 ≤ r → r ≤ T ^ (-(M' + slowExponent lam + 1)) →
        (∀ z, multDiff Z Z' z ≠ 0 → |z.im - T| ≤ T / 2 →
          ‖z - z₀‖ ≤ r ∨ T ^ (-M') ≤ ‖z - z₀‖) →
        ∀ s : Finset ℂ, (∀ z ∈ s, ‖z - z₀‖ ≤ r) →
        (∀ z, multDiff Z Z' z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s) →
        ∃ F₁ G₁ : ℝ → ℂ, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F₁ ∧
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G₁ ∧
          pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀ ≠ 0 ∧
          ∀ j : ℕ, j ≤ J →
            ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁)) ∧
            ‖(Z.W (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁)) (localWindow z₀.im G₁) -
                Z'.W (localWindow z₀.im (annihilatePow (gammaOf z₀ - z₀.im) j F₁)) (localWindow z₀.im G₁)) /
                ((-I) ^ j * pointImage (localWindow z₀.im F₁) (localWindow z₀.im G₁) z₀) -
              ∑ z ∈ s, multDiff Z Z' z * (gammaOf z - gammaOf z₀) ^ j‖ ≤
              (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (j + 1) * T ^ (M' + slowExponent lam) +
                Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := by
  have h2π0 : 0 < 2 * π := by positivity
  have hlam0 : 0 < lam := by linarith
  obtain ⟨β, hβ⟩ : ∃ β, β = lam - θ / 2 := ⟨_, rfl⟩
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hβlam : β ≤ lam := by rw [hβ]; linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = 2 * π * A / lam := ⟨_, rfl⟩
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; positivity
  obtain ⟨e, he⟩ : ∃ e, e = 6 * slackBound ℓ * (1 + slackBound ℓ) := ⟨_, rfl⟩
  have : 0 ≤ slackBound ℓ := by unfold slackBound; linarith
  have he0 : 0 ≤ e := by rw [he]; positivity
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * growthRate ℓ * lam ^ 2 +
      2 * floorRate ℓ * lam ^ 2 * (lam + 8 * M') := ⟨_, rfl⟩
  have : 0 ≤ growthRate ℓ := growthRate_nonneg hℓ0
  have : 0 ≤ floorRate ℓ := floorRate_nonneg hℓ0
  have : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨K, hK⟩ : ∃ K, K = c / 2 + 2 := ⟨_, rfl⟩
  have hK1 : 2 ≤ K := by rw [hK]; linarith
  obtain ⟨MK, hMK⟩ : ∃ MK, MK = e * lam + K + K' + 2 + J := ⟨_, rfl⟩
  have hMK0 : 0 < MK := by rw [hMK]; positivity
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = 8 * MK / β := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  obtain ⟨α, hα⟩ : ∃ α, α = 1 / (8 * MK * (1 + ρ)) := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  obtain ⟨q, hq⟩ : ∃ q, q = max 0 (Real.log α⁻¹) := ⟨_, rfl⟩
  obtain ⟨S'', hS''⟩ : ∃ S'', S'' = max S 1 := ⟨_, rfl⟩
  have hS''1 : 1 ≤ S'' := by rw [hS'']; exact le_max_right _ _
  obtain ⟨V, hV⟩ : ∃ V, V = max (6 * slowConst lam ℓ M') (4 * lam) + 1 := ⟨_, rfl⟩
  have hV0 : 0 < V := by rw [hV]; linarith [le_max_right (6 * slowConst lam ℓ M') (4 * lam)]
  obtain ⟨U₀, hU₀⟩ : ∃ U₀, U₀ = max (max (max 1 (2 * π / lam))
      (2 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1)) (Real.log V) := ⟨_, rfl⟩
  have hU₀1 : 1 ≤ U₀ := by
    rw [hU₀]; exact ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)
  refine ⟨2 * π * Real.exp U₀, ?_, fun T hT Z Z' hZ hZ' hStail hcount z₀ hz₀ hz₀re r hr0 hr
    hiso s hsd hds => ?_⟩
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hU₀1) h2π0.le
  -- height scale `u = log(T / 2π)`
  have hTdiv : Real.exp U₀ ≤ T / (2 * π) := by rw [le_div_iff₀ h2π0]; linarith
  obtain ⟨u, hu⟩ : ∃ u, u = Real.log (T / (2 * π)) := ⟨_, rfl⟩
  rw [← hu] at hcount ⊢
  have huU₀ : U₀ ≤ u := by
    rw [hu, ← Real.log_exp U₀]
    exact Real.log_le_log (Real.exp_pos _) hTdiv
  rw [hU₀] at huU₀
  have hu1 : 1 ≤ u :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans huU₀
  have hu0 : 0 < u := by linarith
  have hu_lam : 2 * π / lam ≤ u :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans huU₀
  have hu_bud : 2 * MK * q + (lam + 4) + (Real.log S'' + 605) + 1 ≤ u :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans huU₀
  have hTu : T = 2 * π * Real.exp u := by
    rw [hu, Real.exp_log (lt_of_lt_of_le (Real.exp_pos _) hTdiv)]
    field_simp
  have hT0 : 0 < T := by rw [hTu]; positivity
  have hEV : V ≤ Real.exp u := by
    have h1 : Real.log V ≤ u := (le_max_right _ _).trans huU₀
    calc V = Real.exp (Real.log V) := (Real.exp_log hV0).symm
      _ ≤ Real.exp u := Real.exp_le_exp.mpr h1
  have hbig : 6 * slowConst lam ℓ M' ≤ Real.exp u := by
    rw [hV] at hEV; linarith [le_max_left (6 * slowConst lam ℓ M') (4 * lam)]
  have h4lam : 4 * lam ≤ Real.exp u := by
    rw [hV] at hEV; linarith [le_max_right (6 * slowConst lam ℓ M') (4 * lam)]
  have hET : Real.exp u ≤ T := by
    rw [hTu]; nlinarith [Real.exp_pos u, Real.pi_gt_three]
  have hT1 : 1 ≤ T := (Real.one_le_exp hu0.le).trans hET
  -- camera parameters
  obtain ⟨a, ha⟩ : ∃ a, a = lam * (u / 2) := ⟨_, rfl⟩
  rw [← ha]
  obtain ⟨ε, hε⟩ : ∃ ε, ε = β * u / 8 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = (θ + β) / (2 * π) * u := ⟨_, rfl⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = A * u := ⟨_, rfl⟩
  obtain ⟨hDa, hD1, hDup, hC₀ℓ⟩ :=
    rvm_density_facts hθ hlam hA hβ hℓ hu0 hu_lam ha hε hD hC₀
  have hD0 : 0 < D := by linarith
  obtain ⟨η, hη⟩ : ∃ η, η = T ^ (-M') := ⟨_, rfl⟩
  -- decay order `k = ⌈(K + K') u²⌉₊` and spline order `m = ⌈W⌉₊ + k + J`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌈(K + K') * u ^ 2⌉₊ := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = windowExponent (2 * D⁻¹) (localSlack D C₀) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hWdef, windowExponent]
    have := windowSlack_localSlack_nonneg (C₀ := C₀) hD0
    positivity
  have hWle : W ≤ e * D := by rw [hWdef, he]; exact windowExponent_le hD1 hC₀ℓ
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈W⌉₊ + (k + J) := ⟨_, rfl⟩
  obtain ⟨hkK, hk1, hm', hmle, hmε⟩ :=
    rvm_order_facts hK1 hK' he0 hlam0 hβ0 hMK hρ hu1 hε hDup hW0 hWle hk hmdef
  have hm : windowExponent (2 * D⁻¹) (localSlack D C₀) + ((k + J : ℕ) : ℝ) ≤ m := hWdef ▸ hm'
  -- the cluster near `z₀`
  have hsub_band : ∀ z : ℂ, |z.im - z₀.im| ≤ T / 4 → |z.im - T| ≤ T / 2 := fun z hz => by
    have h1 := abs_le.mp hz
    have h2 := abs_le.mp hz₀
    rw [abs_le]; constructor <;> linarith
  have hiso' : ∀ z, multDiff Z Z' z ≠ 0 → |z.im - z₀.im| ≤ T / 4 →
      ‖z - z₀‖ ≤ r ∨ η ≤ ‖z - z₀‖ :=
    fun z hcz hzR => by rw [hη]; exact hiso z hcz (hsub_band z hzR)
  have hcount' : ∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
      (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - z₀.im| ≤ T / 4 ∧ z.im ∈ Icc x y) →
        (s.card : ℝ) ≤ D * (y - x) + C₀ := by
    intro s x y hxy hs
    have hc1 := hcount s x y hxy fun z hz =>
      ⟨(hs z hz).1, hsub_band z (hs z hz).2.1, (hs z hz).2.2⟩
    rw [← hC₀] at hc1
    have hDθ : θ / (2 * π) * u ≤ D := by
      rw [hD]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by linarith [hβ0]) h2π0.le) hu0.le
    have hmul : θ / (2 * π) * u * (y - x) ≤ D * (y - x) :=
      mul_le_mul_of_nonneg_right hDθ (sub_nonneg.mpr hxy)
    linarith
  exact rvm_readout_core hu1 hTu hM' hlam0 hβ0 hβlam hℓ0 hc hK hK' hMK0 hρ0 hα hα0 hq hS''1
    hu_bud ha hε hD1 hDup hC₀ℓ hDa hη hkK hk1 hm hmle hmε hbig h4lam hZ hZ'
    (hStail.trans (by rw [hS'']; exact le_max_left _ _)) hz₀ hz₀re hr0 hr hiso' hcount' hsd hds

/-- **Second-order local inversion, uniformly in the height.** Let `0 ≤ θ`, `λ > θ/2`,
`A, S, M', K' ≥ 0`, and `κ_λ = πλ/2 + λ + 3`. For all `T ≥ T₀`: let `Z, Z'` be tempered mimics on
windows of aperture `λ · ½ log(T/2π)`, with `Σ_z |c(z)|/(1 + |γ_z|²) ≤ S` and cluster count
`≤ (θ/2π) log(T/2π)(y − x) + A log(T/2π)` in `[T/2, 3T/2]`. Let `z₀` lie in `|Im z₀ − T| ≤ T/4`, and
let every cluster point in `[T/2, 3T/2]` lie in the disc `‖z − z₀‖ ≤ r` or at distance
`≥ T^{−M'}` from `z₀`, where `r ≤ T^{−(M' + κ_λ + 1)}`. Then the disc moments satisfy, for every order `j ≤ J`,
`‖μ_j‖ ≤ N r^{j+1} T^{M' + κ_λ} + exp(−K' log³(T/2π))`, `N = Σ_{disc} |c|`. -/
theorem norm_discMoment_rvm_le (J : ℕ) {θ lam A S M' K' : ℝ} (hθ : 0 ≤ θ) (hlam : θ / 2 < lam)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hM' : 0 ≤ M') (hK' : 0 ≤ K') :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → |z₀.re - 1 / 2| ≤ 1 / 2 →
        ∀ r : ℝ, 0 ≤ r → r ≤ T ^ (-(M' + slowExponent lam + 1)) →
        (∀ z, multDiff Z Z' z ≠ 0 → |z.im - T| ≤ T / 2 →
          ‖z - z₀‖ ≤ r ∨ T ^ (-M') ≤ ‖z - z₀‖) →
        ∀ s : Finset ℂ, (∀ z ∈ s, ‖z - z₀‖ ≤ r) →
        (∀ z, multDiff Z Z' z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s) →
        ∀ j : ℕ, j ≤ J →
          ‖∑ z ∈ s, multDiff Z Z' z * (gammaOf z - gammaOf z₀) ^ j‖ ≤
            (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (j + 1) * T ^ (M' + slowExponent lam) +
              Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := by
  obtain ⟨T₀, hT₀, hread⟩ := discMoment_readout_rvm J hθ hlam hA hS hM' hK'
  refine ⟨T₀, hT₀, fun T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso s hsd hds j
    hj => ?_⟩
  obtain ⟨F₁, G₁, -, hG₁, -, hj'⟩ :=
    hread T hT Z Z' hZ hZ' hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso s hsd hds
  obtain ⟨hFj, hbd⟩ := hj' j hj
  rw [W_eq_of_mimic hZ hZ' hW hFj (apertureWindow_localWindow hG₁ _), sub_self, zero_div, zero_sub,
    norm_neg] at hbd
  exact hbd

/-- The sum of a function against a signed pair-against-pair cluster. -/
theorem sum_pair_cluster {p₁ p₂ q₁ q₂ : ℂ} (f : ℂ → ℂ) :
    ∑ z ∈ ({p₁, p₂, q₁, q₂} : Finset ℂ), ((if z = p₁ then 1 else 0) + (if z = p₂ then 1 else 0) -
      (if z = q₁ then 1 else 0) - (if z = q₂ then 1 else 0) : ℂ) * f z =
      f p₁ + f p₂ - f q₁ - f q₂ := by
  classical
  simp only [add_mul, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_insert, Finset.mem_singleton,
    true_or, or_true, if_true]

theorem sum_norm_pair_cluster_le {p₁ p₂ q₁ q₂ : ℂ} :
    ∑ z ∈ ({p₁, p₂, q₁, q₂} : Finset ℂ), ‖((if z = p₁ then 1 else 0) +
      (if z = p₂ then 1 else 0) - (if z = q₁ then 1 else 0) - (if z = q₂ then 1 else 0) : ℂ)‖ ≤
      4 := by
  classical
  have h : ∀ z, ‖((if z = p₁ then 1 else 0) + (if z = p₂ then 1 else 0) -
      (if z = q₁ then 1 else 0) - (if z = q₂ then 1 else 0) : ℂ)‖ ≤
      ‖(if z = p₁ then 1 else 0 : ℂ)‖ + ‖(if z = p₂ then 1 else 0 : ℂ)‖ +
        ‖(if z = q₁ then 1 else 0 : ℂ)‖ + ‖(if z = q₂ then 1 else 0 : ℂ)‖ := fun z => by
    have h1 := norm_sub_le ((if z = p₁ then 1 else 0 : ℂ) + (if z = p₂ then 1 else 0) -
      (if z = q₁ then 1 else 0)) (if z = q₂ then 1 else 0)
    have h2 := norm_sub_le ((if z = p₁ then 1 else 0 : ℂ) + (if z = p₂ then 1 else 0))
      (if z = q₁ then 1 else 0)
    have h3 := norm_add_le (if z = p₁ then 1 else 0 : ℂ) (if z = p₂ then 1 else 0)
    linarith
  have hδ : ∀ p : ℂ, ∑ z ∈ ({p₁, p₂, q₁, q₂} : Finset ℂ), ‖(if z = p then 1 else 0 : ℂ)‖ ≤ 1 :=
    fun p => by
      have : ∀ z, ‖(if z = p then 1 else 0 : ℂ)‖ = if z = p then 1 else 0 := fun z => by
        split_ifs <;> simp
      simp only [this, Finset.sum_ite_eq']
      split_ifs <;> norm_num
  refine (Finset.sum_le_sum fun z _ => h z).trans ?_
  simp only [Finset.sum_add_distrib]
  linarith [hδ p₁, hδ p₂, hδ q₁, hδ q₂]

/-- **Near-coincident pairs have the same centre and the same squared gap, uniformly in the
height.** Under the hypotheses of `norm_discMoment_rvm_le`, suppose that inside the disc
`‖z − z₀‖ ≤ r` the cluster is a pair `p₁, p₂` of `Z` against a pair `q₁, q₂` of `Z'`
(`c = δ_{p₁} + δ_{p₂} − δ_{q₁} − δ_{q₂}`, points repeated with multiplicity). Write
`P_i = γ_{p_i}`, `Q_i = γ_{q_i}` and `E = exp(−K' log³(T/2π))`. Then
`|(P₁ + P₂) − (Q₁ + Q₂)| ≤ 4 r² T^{M' + κ_λ} + E` and
`|(P₁ − P₂)² − (Q₁ − Q₂)²| ≤ 24 r³ T^{M' + κ_λ} + 4E`. -/
theorem pair_centre_and_gap_rvm {θ lam A S M' K' : ℝ} (hθ : 0 ≤ θ) (hlam : θ / 2 < lam)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hM' : 0 ≤ M') (hK' : 0 ≤ K') :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → |z₀.re - 1 / 2| ≤ 1 / 2 →
        ∀ r : ℝ, 0 ≤ r → r ≤ T ^ (-(M' + slowExponent lam + 1)) →
        (∀ z, multDiff Z Z' z ≠ 0 → |z.im - T| ≤ T / 2 →
          ‖z - z₀‖ ≤ r ∨ T ^ (-M') ≤ ‖z - z₀‖) →
        ∀ p₁ p₂ q₁ q₂ : ℂ, ‖p₁ - z₀‖ ≤ r → ‖p₂ - z₀‖ ≤ r → ‖q₁ - z₀‖ ≤ r → ‖q₂ - z₀‖ ≤ r →
        (∀ z, ‖z - z₀‖ ≤ r → multDiff Z Z' z = (if z = p₁ then 1 else 0) +
          (if z = p₂ then 1 else 0) - (if z = q₁ then 1 else 0) - (if z = q₂ then 1 else 0)) →
          ‖(gammaOf p₁ + gammaOf p₂) - (gammaOf q₁ + gammaOf q₂)‖ ≤
              4 * r ^ 2 * T ^ (M' + slowExponent lam) +
                Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) ∧
            ‖(gammaOf p₁ - gammaOf p₂) ^ 2 - (gammaOf q₁ - gammaOf q₂) ^ 2‖ ≤
              24 * r ^ 3 * T ^ (M' + slowExponent lam) +
                4 * Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := by
  classical
  obtain ⟨T₀, hT₀, hmain⟩ := norm_discMoment_rvm_le 2 hθ hlam hA hS hM' hK'
  refine ⟨T₀, hT₀, fun T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso p₁ p₂ q₁ q₂
    hp₁ hp₂ hq₁ hq₂ hc => ?_⟩
  set s : Finset ℂ := {p₁, p₂, q₁, q₂} with hs
  have hsd : ∀ z ∈ s, ‖z - z₀‖ ≤ r := by
    intro z hz
    simp only [hs, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have hds : ∀ z, multDiff Z Z' z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s := by
    intro z hcz hzr
    by_contra hzs
    simp only [hs, Finset.mem_insert, Finset.mem_singleton, not_or] at hzs
    apply hcz
    rw [hc z hzr, if_neg hzs.1, if_neg hzs.2.1, if_neg hzs.2.2.1, if_neg hzs.2.2.2]
    ring
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = T ^ (M' + slowExponent lam) := ⟨_, rfl⟩
  rw [← hE, ← hP]
  have hm := fun j hj => hmain T hT Z Z' hZ hZ' hW hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso s
    hsd hds j hj
  rw [← hE, ← hP] at hm
  have hsum : ∀ f : ℂ → ℂ, ∑ z ∈ s, multDiff Z Z' z * f z = f p₁ + f p₂ - f q₁ - f q₂ := by
    intro f
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)], sum_pair_cluster]
  have hN : ∑ z ∈ s, ‖multDiff Z Z' z‖ ≤ 4 := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)]]
    exact sum_norm_pair_cluster_le
  have h2πe : 2 ≤ 2 * π * Real.exp 1 := by
    have h1 := Real.one_le_exp (zero_le_one : (0 : ℝ) ≤ 1)
    nlinarith [Real.pi_gt_three]
  have hT2 : 2 ≤ T := h2πe.trans (hT₀.trans hT)
  have hP0 : 0 ≤ P := by rw [hP]; exact Real.rpow_nonneg (by linarith) _
  have hE0 : 0 ≤ E := by rw [hE]; exact (Real.exp_pos _).le
  set ω := gammaOf z₀
  have hd : ∀ z, ‖z - z₀‖ ≤ r → ‖gammaOf z - ω‖ ≤ r := fun z hz => by
    rw [norm_gammaOf_sub]; exact hz
  -- first and second moments
  have h1 := hm 1 (by norm_num)
  have h2 := hm 2 (by norm_num)
  rw [hsum] at h1 h2
  have e1 : (gammaOf p₁ - ω) ^ 1 + (gammaOf p₂ - ω) ^ 1 - (gammaOf q₁ - ω) ^ 1 -
      (gammaOf q₂ - ω) ^ 1 = (gammaOf p₁ + gammaOf p₂) - (gammaOf q₁ + gammaOf q₂) := by ring
  rw [e1] at h1
  have hr2 : (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (1 + 1) * P ≤ 4 * r ^ 2 * P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hN (by positivity)) hP0
  have hcentre : ‖(gammaOf p₁ + gammaOf p₂) - (gammaOf q₁ + gammaOf q₂)‖ ≤ 4 * r ^ 2 * P + E := by
    linarith
  refine ⟨hcentre, ?_⟩
  have hr3 : (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (2 + 1) * P ≤ 4 * r ^ 3 * P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hN (by positivity)) hP0
  have hμ₂ : ‖(gammaOf p₁ - ω) ^ 2 + (gammaOf p₂ - ω) ^ 2 - (gammaOf q₁ - ω) ^ 2 -
      (gammaOf q₂ - ω) ^ 2‖ ≤ 4 * r ^ 3 * P + E := by linarith
  have hid : (gammaOf p₁ - gammaOf p₂) ^ 2 - (gammaOf q₁ - gammaOf q₂) ^ 2 =
      2 * ((gammaOf p₁ - ω) ^ 2 + (gammaOf p₂ - ω) ^ 2 - (gammaOf q₁ - ω) ^ 2 -
        (gammaOf q₂ - ω) ^ 2) - ((gammaOf p₁ + gammaOf p₂) - (gammaOf q₁ + gammaOf q₂)) *
          ((gammaOf p₁ - ω) + (gammaOf p₂ - ω) + (gammaOf q₁ - ω) + (gammaOf q₂ - ω)) := by
    ring
  have h4r : ‖(gammaOf p₁ - ω) + (gammaOf p₂ - ω) + (gammaOf q₁ - ω) + (gammaOf q₂ - ω)‖ ≤
      4 * r := by
    have e1 := norm_add_le ((gammaOf p₁ - ω) + (gammaOf p₂ - ω) + (gammaOf q₁ - ω))
      (gammaOf q₂ - ω)
    have e2 := norm_add_le ((gammaOf p₁ - ω) + (gammaOf p₂ - ω)) (gammaOf q₁ - ω)
    have e3 := norm_add_le (gammaOf p₁ - ω) (gammaOf p₂ - ω)
    linarith [hd p₁ hp₁, hd p₂ hp₂, hd q₁ hq₁, hd q₂ hq₂]
  have hr1 : r ≤ 1 / 2 := by
    have hT1 : 1 ≤ T := by linarith
    have hexp : -(M' + slowExponent lam + 1) ≤ (-1 : ℝ) := by
      have := mul_pos Real.pi_pos (show 0 < lam by linarith)
      unfold slowExponent
      linarith
    have h := hr.trans (Real.rpow_le_rpow_of_exponent_le hT1 hexp)
    rw [Real.rpow_neg_one] at h
    have h2 : T⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num), one_div, inv_inv]
      exact hT2
    linarith
  rw [hid]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_two]
  have hprod := mul_le_mul hcentre h4r (norm_nonneg _) (by positivity)
  have hrE : r * E ≤ 1 / 2 * E := mul_le_mul_of_nonneg_right hr1 hE0
  linarith [hprod, hμ₂, hrE]

theorem sum_dipole {p q : ℂ} (f : ℂ → ℂ) :
    ∑ z ∈ ({p, q} : Finset ℂ), ((if z = p then 1 else 0) - (if z = q then 1 else 0) : ℂ) * f z =
      f p - f q := by
  classical
  simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_insert, Finset.mem_singleton, true_or, or_true, if_true]

theorem sum_norm_dipole_le {p q : ℂ} :
    ∑ z ∈ ({p, q} : Finset ℂ), ‖((if z = p then 1 else 0) - (if z = q then 1 else 0) : ℂ)‖ ≤ 2 := by
  classical
  have hδ : ∀ x : ℂ, ∑ z ∈ ({p, q} : Finset ℂ), ‖(if z = x then 1 else 0 : ℂ)‖ ≤ 1 := fun x => by
    have : ∀ z, ‖(if z = x then 1 else 0 : ℂ)‖ = if z = x then 1 else 0 := fun z => by
      split_ifs <;> simp
    simp only [this, Finset.sum_ite_eq']
    split_ifs <;> norm_num
  refine (Finset.sum_le_sum fun z _ => norm_sub_le _ _).trans ?_
  rw [Finset.sum_add_distrib]
  linarith [hδ p, hδ q]

/-- **Isolated dipoles collapse, uniformly in the height.** Under the hypotheses of
`norm_discMoment_rvm_le`, let a point `p` of `Z` and a point `q` of `Z'` form the whole cluster
in the disc `‖z − p‖ ≤ ‖q − p‖`, with `‖q − p‖ ≤ T^{−(M' + κ_λ + 1)}` and every other cluster
point in `[T/2, 3T/2]` at distance `≥ T^{−M'}` from `p`. Then
`‖γ_p − γ_q‖ ≤ 2 exp(−K' log³(T/2π))`: the first moment `γ_p − γ_q` is bounded by its own square
times `T^{M' + κ_λ}`. -/
theorem dipole_collapse_rvm {θ lam A S M' K' : ℝ} (hθ : 0 ≤ θ) (hlam : θ / 2 < lam)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hM' : 0 ≤ M') (hK' : 0 ≤ K') :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z Z' : ZeroConfig, TemperedConfig Z → TemperedConfig Z' →
        (∀ f, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f → Z.W f f = Z'.W f f) →
        ∑' z, ‖multDiff Z Z' z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z Z' z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ p q : ℂ, |p.im - T| ≤ T / 4 → |p.re - 1 / 2| ≤ 1 / 2 →
        ‖q - p‖ ≤ T ^ (-(M' + slowExponent lam + 1)) →
        (∀ z, ‖z - p‖ ≤ ‖q - p‖ →
          multDiff Z Z' z = (if z = p then 1 else 0) - (if z = q then 1 else 0)) →
        (∀ z, multDiff Z Z' z ≠ 0 → |z.im - T| ≤ T / 2 →
          ‖z - p‖ ≤ ‖q - p‖ ∨ T ^ (-M') ≤ ‖z - p‖) →
          ‖gammaOf p - gammaOf q‖ ≤ 2 * Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := by
  classical
  obtain ⟨T₀, hT₀, hmain⟩ := norm_discMoment_rvm_le 2 hθ hlam hA hS hM' hK'
  refine ⟨T₀, hT₀, fun T hT Z Z' hZ hZ' hW hStail hcount p q hp hpre hr hc hiso => ?_⟩
  have h2πe : 4 ≤ 2 * π * Real.exp 1 := by
    have h1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    nlinarith [Real.pi_gt_three]
  have hT4 : 4 ≤ T := h2πe.trans (hT₀.trans hT)
  have hT0 : 0 < T := by linarith
  set r := ‖q - p‖ with hrdef
  set s : Finset ℂ := {p, q} with hs
  have hsd : ∀ z ∈ s, ‖z - p‖ ≤ r := by
    intro z hz
    simp only [hs, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · rw [sub_self, norm_zero]; exact norm_nonneg _
    · exact le_rfl
  have hds : ∀ z, multDiff Z Z' z ≠ 0 → ‖z - p‖ ≤ r → z ∈ s := by
    intro z hcz hzr
    by_contra hzs
    simp only [hs, Finset.mem_insert, Finset.mem_singleton, not_or] at hzs
    apply hcz
    rw [hc z hzr, if_neg hzs.1, if_neg hzs.2, sub_zero]
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = T ^ (M' + slowExponent lam) := ⟨_, rfl⟩
  rw [← hE]
  have hm := hmain T hT Z Z' hZ hZ' hW hStail hcount p hp hpre r (norm_nonneg _) hr hiso s hsd
    hds 1 (by norm_num)
  rw [← hE, ← hP] at hm
  have hsum : ∑ z ∈ s, multDiff Z Z' z * (gammaOf z - gammaOf p) ^ 1 = gammaOf p - gammaOf q := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)], sum_dipole]
    ring
  have hN : ∑ z ∈ s, ‖multDiff Z Z' z‖ ≤ 2 := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)]]
    exact sum_norm_dipole_le
  rw [hsum] at hm
  have hrγ : ‖gammaOf p - gammaOf q‖ = r := by rw [norm_gammaOf_sub, norm_sub_rev]
  rw [hrγ] at hm ⊢
  have hP0 : 0 ≤ P := by rw [hP]; exact Real.rpow_nonneg hT0.le _
  -- `r P ≤ T⁻¹ ≤ 1/4`
  have hrP : r * P ≤ 1 / 4 := by
    have hprod : T ^ (-(M' + slowExponent lam + 1)) * P = T⁻¹ := by
      rw [hP, ← Real.rpow_add hT0, show -(M' + slowExponent lam + 1) + (M' + slowExponent lam) =
        -1 by ring, Real.rpow_neg_one]
    have h1 : r * P ≤ T⁻¹ := hprod ▸ mul_le_mul_of_nonneg_right hr hP0
    have h2 : T⁻¹ ≤ 1 / 4 := by
      rw [inv_le_comm₀ hT0 (by norm_num), one_div, inv_inv]; exact hT4
    linarith
  have hr0 : 0 ≤ r := norm_nonneg _
  have hNr : (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (1 + 1) * P ≤ 2 * r * (r * P) := by
    have h := mul_le_mul_of_nonneg_right hN (mul_nonneg (mul_nonneg hr0 hr0) hP0)
    calc (∑ z ∈ s, ‖multDiff Z Z' z‖) * r ^ (1 + 1) * P
        = (∑ z ∈ s, ‖multDiff Z Z' z‖) * (r * r * P) := by ring
      _ ≤ 2 * (r * r * P) := h
      _ = 2 * r * (r * P) := by ring
  have h2 : 2 * r * (r * P) ≤ r / 2 := by
    have := mul_le_mul_of_nonneg_left hrP (by linarith : (0 : ℝ) ≤ 2 * r)
    linarith
  linarith

end GaloisForLFunctions.ZeroConfigurationGeometry
