import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A scale of exponentially weighted sequence norms

The characteristic reduction of the clock equation in dimension `n + 2` leaves

`∂ξ∂η u = (Δ⊥ u + V u) / 4`,

so when the potential depends on the transverse coordinates the Volterra iteration loses two
transverse derivatives at each step. The classical remedy is to run the iteration in a *scale* of
Banach spaces of transverse-analytic functions, in which the lost derivatives are paid for by
shrinking the radius of analyticity — the loss is bounded by `C / (ρ - ρ')²`.

This file builds the scale in its concrete Fourier form: for a transverse variable on a circle, a
function analytic in a strip of half-width `ρ` is exactly one whose Fourier coefficients are
summable against the weight `e^{ρ|k|}`. The two facts the iteration needs are proved here:

* the scale is decreasing — a smaller radius has a smaller norm;
* the transverse Laplacian, which is multiplication by `-k²` on coefficients, maps radius `ρ` to
  radius `ρ'` with norm at most `4 / (ρ - ρ')²`.

The elementary inequality behind the second is `s² ≤ 4 e^s`, itself a squared instance of
`1 + s ≤ e^s`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Topology

/-! ## The elementary bound -/

/-- **A square is dominated by four times the exponential.** -/
theorem sq_le_four_mul_exp {s : ℝ} (hs : 0 ≤ s) : s ^ (2 : ℕ) ≤ 4 * Real.exp s := by
  have h1 : 1 + s / 2 ≤ Real.exp (s / 2) := by
    have h := Real.add_one_le_exp (s / 2)
    linarith
  have h2 : (0 : ℝ) ≤ s / 2 := by linarith
  have h3 : (s / 2) ^ (2 : ℕ) ≤ (Real.exp (s / 2)) ^ (2 : ℕ) := by
    nlinarith [h1, h2, Real.exp_pos (s / 2)]
  have hexp : (Real.exp (s / 2)) ^ (2 : ℕ) = Real.exp s := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [hexp] at h3
  nlinarith [h3]

/-- **The derivative-loss inequality.** Two derivatives cost `4 / δ²` in radius `δ`. -/
theorem sq_mul_exp_neg_le {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    t ^ (2 : ℕ) * Real.exp (-(δ * t)) ≤ 4 / δ ^ (2 : ℕ) := by
  have hs : (0 : ℝ) ≤ δ * t := mul_nonneg hδ.le ht
  have hbase := sq_le_four_mul_exp hs
  have hexp : Real.exp (-(δ * t)) * Real.exp (δ * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hpos : (0 : ℝ) < Real.exp (-(δ * t)) := Real.exp_pos _
  have hδ2 : (0 : ℝ) < δ ^ (2 : ℕ) := by positivity
  rw [le_div_iff₀ hδ2]
  calc t ^ (2 : ℕ) * Real.exp (-(δ * t)) * δ ^ (2 : ℕ)
      = (δ * t) ^ (2 : ℕ) * Real.exp (-(δ * t)) := by ring
    _ ≤ 4 * Real.exp (δ * t) * Real.exp (-(δ * t)) := by
        exact mul_le_mul_of_nonneg_right hbase hpos.le
    _ = 4 := by
        rw [mul_assoc, mul_comm (Real.exp (δ * t)), hexp, mul_one]

/-! ## The weighted norm -/

/-- The exponentially weighted `ℓ¹` norm of a two-sided sequence of Fourier coefficients: the norm
of a function analytic in a strip of half-width `ρ`. -/
noncomputable def wienerNorm (ρ : ℝ) (g : ℤ → ℝ) : ℝ :=
  ∑' k : ℤ, |g k| * Real.exp (ρ * |(k : ℝ)|)

/-- Membership in the space of radius `ρ`. -/
def WienerSummable (ρ : ℝ) (g : ℤ → ℝ) : Prop :=
  Summable fun k : ℤ => |g k| * Real.exp (ρ * |(k : ℝ)|)

theorem wienerNorm_nonneg (ρ : ℝ) (g : ℤ → ℝ) : 0 ≤ wienerNorm ρ g :=
  tsum_nonneg fun _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

theorem weight_le_weight {ρ' ρ : ℝ} (hρ : ρ' ≤ ρ) (g : ℤ → ℝ) (k : ℤ) :
    |g k| * Real.exp (ρ' * |(k : ℝ)|) ≤ |g k| * Real.exp (ρ * |(k : ℝ)|) := by
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
  exact mul_le_mul_of_nonneg_right hρ (abs_nonneg _)

/-- **The scale is decreasing.** -/
theorem wienerSummable_of_le {ρ' ρ : ℝ} (hρ : ρ' ≤ ρ) {g : ℤ → ℝ}
    (hg : WienerSummable ρ g) : WienerSummable ρ' g :=
  hg.of_nonneg_of_le (fun _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
    (weight_le_weight hρ g)

theorem wienerNorm_mono {ρ' ρ : ℝ} (hρ : ρ' ≤ ρ) {g : ℤ → ℝ} (hg : WienerSummable ρ g) :
    wienerNorm ρ' g ≤ wienerNorm ρ g :=
  Summable.tsum_le_tsum (weight_le_weight hρ g) (wienerSummable_of_le hρ hg) hg

/-! ## The transverse Laplacian loses two derivatives -/

/-- Multiplication of Fourier coefficients by `k²`: the transverse Laplacian up to sign. -/
noncomputable def sqMul (g : ℤ → ℝ) : ℤ → ℝ := fun k => (k : ℝ) ^ (2 : ℕ) * g k

theorem abs_sqMul (g : ℤ → ℝ) (k : ℤ) : |sqMul g k| = (k : ℝ) ^ (2 : ℕ) * |g k| := by
  rw [sqMul, abs_mul, abs_pow, sq_abs]

/-- The pointwise form of the loss: the weight at the smaller radius absorbs `k²`. -/
theorem abs_sqMul_weight_le {ρ' ρ : ℝ} (hρ : ρ' < ρ) (g : ℤ → ℝ) (k : ℤ) :
    |sqMul g k| * Real.exp (ρ' * |(k : ℝ)|)
      ≤ 4 / (ρ - ρ') ^ (2 : ℕ) * (|g k| * Real.exp (ρ * |(k : ℝ)|)) := by
  have hδ : 0 < ρ - ρ' := by linarith
  have ht : (0 : ℝ) ≤ |(k : ℝ)| := abs_nonneg _
  have hkey := sq_mul_exp_neg_le (δ := ρ - ρ') (t := |(k : ℝ)|) hδ ht
  have hsplit : Real.exp (ρ' * |(k : ℝ)|)
      = Real.exp (-((ρ - ρ') * |(k : ℝ)|)) * Real.exp (ρ * |(k : ℝ)|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc |sqMul g k| * Real.exp (ρ' * |(k : ℝ)|)
      = |(k : ℝ)| ^ (2 : ℕ) * Real.exp (-((ρ - ρ') * |(k : ℝ)|))
          * (|g k| * Real.exp (ρ * |(k : ℝ)|)) := by
        rw [abs_sqMul, hsplit, sq_abs]
        ring
    _ ≤ 4 / (ρ - ρ') ^ (2 : ℕ) * (|g k| * Real.exp (ρ * |(k : ℝ)|)) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)

/-- **The transverse Laplacian maps radius `ρ` to radius `ρ'` with norm at most
`4 / (ρ - ρ')²`.** -/
theorem wienerSummable_sqMul {ρ' ρ : ℝ} (hρ : ρ' < ρ) {g : ℤ → ℝ}
    (hg : WienerSummable ρ g) : WienerSummable ρ' (sqMul g) :=
  (hg.mul_left (4 / (ρ - ρ') ^ (2 : ℕ))).of_nonneg_of_le
    (fun _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
    (abs_sqMul_weight_le hρ g)

theorem wienerNorm_sqMul_le {ρ' ρ : ℝ} (hρ : ρ' < ρ) {g : ℤ → ℝ}
    (hg : WienerSummable ρ g) :
    wienerNorm ρ' (sqMul g) ≤ 4 / (ρ - ρ') ^ (2 : ℕ) * wienerNorm ρ g := by
  rw [wienerNorm, wienerNorm, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (abs_sqMul_weight_le hρ g) (wienerSummable_sqMul hρ hg)
    (hg.mul_left (4 / (ρ - ρ') ^ (2 : ℕ)))

/-! ## Multiplication: the scale is an algebra at each radius

Multiplication of functions is convolution of Fourier coefficients, and the weight is submultiplicative
because `|k| ≤ |j| + |k - j|`. So each radius carries a Banach-algebra estimate, which is how the
potential enters the iteration.
-/

/-- Convolution of coefficient sequences: the coefficients of a product of functions. -/
noncomputable def wienerConv (f g : ℤ → ℝ) : ℤ → ℝ := fun k => ∑' j : ℤ, f j * g (k - j)

/-- **The weight is submultiplicative.** -/
theorem exp_weight_triangle {ρ : ℝ} (hρ : 0 ≤ ρ) (k j : ℤ) :
    Real.exp (ρ * |(k : ℝ)|)
      ≤ Real.exp (ρ * |(j : ℝ)|) * Real.exp (ρ * |((k - j : ℤ) : ℝ)|) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hsplit : (k : ℝ) = (j : ℝ) + ((k - j : ℤ) : ℝ) := by push_cast; ring
  have htri : |(k : ℝ)| ≤ |(j : ℝ)| + |((k - j : ℤ) : ℝ)| := by
    rw [hsplit]
    exact abs_add_le _ _
  calc ρ * |(k : ℝ)| ≤ ρ * (|(j : ℝ)| + |((k - j : ℤ) : ℝ)|) :=
        mul_le_mul_of_nonneg_left htri hρ
    _ = ρ * |(j : ℝ)| + ρ * |((k - j : ℤ) : ℝ)| := by ring

/-- **Each radius of the scale carries a Banach-algebra estimate.** -/
theorem wienerSummable_conv_and_norm_le {ρ : ℝ} (hρ : 0 ≤ ρ) {f g : ℤ → ℝ}
    (hf : WienerSummable ρ f) (hg : WienerSummable ρ g) :
    WienerSummable ρ (wienerConv f g) ∧
      wienerNorm ρ (wienerConv f g) ≤ wienerNorm ρ f * wienerNorm ρ g := by
  classical
  set F : ℤ → ℝ := fun j => |f j| * Real.exp (ρ * |(j : ℝ)|) with hFdef
  set G : ℤ → ℝ := fun m => |g m| * Real.exp (ρ * |(m : ℝ)|) with hGdef
  have hFnn : ∀ j, 0 ≤ F j := fun j => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hGnn : ∀ m, 0 ≤ G m := fun m => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hH : Summable fun p : ℤ × ℤ => F p.1 * G p.2 := hf.mul_of_nonneg hg hFnn hGnn
  -- the shear `(k, j) ↦ (j, k - j)`
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun q => (q.2, q.1 - q.2)
      invFun := fun p => (p.1 + p.2, p.1)
      left_inv := by intro q; simp
      right_inv := by intro p; simp }
  have hHe : Summable fun q : ℤ × ℤ => F q.2 * G (q.1 - q.2) := e.summable_iff.mpr hH
  have hshear : (∑' q : ℤ × ℤ, F q.2 * G (q.1 - q.2)) = ∑' p : ℤ × ℤ, F p.1 * G p.2 :=
    e.tsum_eq fun p => F p.1 * G p.2
  set K : ℤ × ℤ → ℝ := fun q => |f q.2| * |g (q.1 - q.2)| * Real.exp (ρ * |(q.1 : ℝ)|) with hKdef
  have hKnn : ∀ q, 0 ≤ K q := fun q =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le
  have hKle : ∀ q : ℤ × ℤ, K q ≤ F q.2 * G (q.1 - q.2) := by
    intro q
    have hw := exp_weight_triangle hρ q.1 q.2
    have hnn : 0 ≤ |f q.2| * |g (q.1 - q.2)| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc K q = (|f q.2| * |g (q.1 - q.2)|) * Real.exp (ρ * |(q.1 : ℝ)|) := by
          rw [hKdef]
      _ ≤ (|f q.2| * |g (q.1 - q.2)|)
            * (Real.exp (ρ * |(q.2 : ℝ)|) * Real.exp (ρ * |((q.1 - q.2 : ℤ) : ℝ)|)) :=
          mul_le_mul_of_nonneg_left hw hnn
      _ = F q.2 * G (q.1 - q.2) := by rw [hFdef, hGdef]; ring
  have hKsum : Summable K := hHe.of_nonneg_of_le hKnn hKle
  have hprodval : (∑' p : ℤ × ℤ, F p.1 * G p.2) = (∑' j, F j) * ∑' m, G m := by
    rw [hH.tsum_prod]
    have hinner : ∀ j : ℤ, (∑' m : ℤ, F j * G m) = F j * ∑' m : ℤ, G m :=
      fun j => tsum_mul_left
    rw [tsum_congr hinner]
    exact tsum_mul_right
  -- the pointwise bound
  have hbound : ∀ k : ℤ,
      |wienerConv f g k| * Real.exp (ρ * |(k : ℝ)|) ≤ ∑' j, K (k, j) := by
    intro k
    have hsec : Summable fun j => K (k, j) := hKsum.prod_factor k
    have hcabs : Summable fun j => |f j * g (k - j)| := by
      have hrw : (fun j => K (k, j))
          = fun j => |f j * g (k - j)| * Real.exp (ρ * |(k : ℝ)|) := by
        funext j
        rw [hKdef, abs_mul]
      rw [hrw] at hsec
      exact (summable_mul_right_iff (Real.exp_ne_zero _)).mp hsec
    have h1 : |wienerConv f g k| ≤ ∑' j, |f j * g (k - j)| := by
      rw [wienerConv]
      have := norm_tsum_le_tsum_norm (f := fun j : ℤ => f j * g (k - j)) (by simpa using hcabs)
      simpa using this
    have h2 : (∑' j, |f j * g (k - j)|) * Real.exp (ρ * |(k : ℝ)|) = ∑' j, K (k, j) := by
      rw [← tsum_mul_right]
      refine tsum_congr fun j => ?_
      rw [hKdef, abs_mul]
    rw [← h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hfib : Summable fun k : ℤ => ∑' j, K (k, j) := hKsum.prod
  have hsum : WienerSummable ρ (wienerConv f g) :=
    hfib.of_nonneg_of_le (fun _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) hbound
  refine ⟨hsum, ?_⟩
  calc wienerNorm ρ (wienerConv f g) ≤ ∑' k : ℤ, ∑' j, K (k, j) :=
        Summable.tsum_le_tsum hbound hsum hfib
    _ = ∑' q : ℤ × ℤ, K q := hKsum.tsum_prod.symm
    _ ≤ ∑' q : ℤ × ℤ, F q.2 * G (q.1 - q.2) := Summable.tsum_le_tsum hKle hKsum hHe
    _ = (∑' j, F j) * ∑' m, G m := by rw [hshear, hprodval]
    _ = wienerNorm ρ f * wienerNorm ρ g := rfl

theorem wienerSummable_conv {ρ : ℝ} (hρ : 0 ≤ ρ) {f g : ℤ → ℝ}
    (hf : WienerSummable ρ f) (hg : WienerSummable ρ g) :
    WienerSummable ρ (wienerConv f g) :=
  (wienerSummable_conv_and_norm_le hρ hf hg).1

theorem wienerNorm_conv_le {ρ : ℝ} (hρ : 0 ≤ ρ) {f g : ℤ → ℝ}
    (hf : WienerSummable ρ f) (hg : WienerSummable ρ g) :
    wienerNorm ρ (wienerConv f g) ≤ wienerNorm ρ f * wienerNorm ρ g :=
  (wienerSummable_conv_and_norm_le hρ hf hg).2

end GaloisForLFunctions.HTGeometry
