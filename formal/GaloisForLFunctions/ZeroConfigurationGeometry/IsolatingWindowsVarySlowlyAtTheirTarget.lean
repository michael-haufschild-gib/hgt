import GaloisForLFunctions.ZeroConfigurationGeometry.NearCoincidencesAreReadThroughTheirMoments
import GaloisForLFunctions.HTGeometry.InfiniteProductNearOne

/-!
# Isolating windows vary slowly at their target

The isolating windows of the local camera have transform `F̂ = S · b̂² · Π r_k`: a sine
`S(w) = sin((π/H)(w − θH))`, a bump `b̂`, and the product over the filled lattice. Their value at
the target `w₀` may be very small, but near `w₀` they vary slowly *relative to that value*. Each
factor does:

* **the sine** (`norm_sin_shift_sub_le`): `|S(w) − S(w₀)| ≤ |w − w₀| (π/H) e^{(π/H)(|Im w₀| + ρ)}`;
* **the bump** (`norm_paperFT_sub_le_of_exp_bound`): from `|b̂| ≤ C₀ e^{ε|Im|}` and Cauchy's
  estimate, `|b̂(w) − b̂(w₀)| ≤ |w − w₀| C₀ e^{ε(|Im w₀| + ρ + 1)}`;
* **the product** (`tprod_pertFactor_eq_mul`, `norm_tprod_ratio_sub_one_le`):
  `Π r_k(w) = Π r_k(w₀) · Π q_k`, with
  `q_k − 1 = (w − w₀)(ν_k − μ_k)/((w₀ − ν_k)(w − μ_k))`. Hence
  `|Π q_k − 1| ≤ exp(|w − w₀| Λ_P) − 1` with `Λ_P = 64 L(1 + L/η) S₀/H²`, where
  `S₀ = Σ_k (1 + k²)⁻¹`.

These relative bounds are polynomial in the height for the windows of `ζ`. The absolute Lipschitz
bound of `norm_pairImage_sub_le` is not, since it is measured against the floor.
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

end GaloisForLFunctions.ZeroConfigurationGeometry
