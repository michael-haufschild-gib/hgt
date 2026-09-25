import GaloisForLFunctions.RHTower.GL3EpsteinEisenstein
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Normed.Module.FiniteDimension


/-!
# The theta transformation for the ternary forms of `h³`

In Iwasawa coordinates the quadratic form of a point is already a sum of squares,
`Q(v) = (Y v₀)² + (y₁(v₁ + x₂v₀))² + (v₂ + x₁v₁ + x₃v₀)²` (`gaussQ`, `Y = y₁y₂`), so the theta
series `Σ_v exp(−π t Q(v))` can be transformed by three one-dimensional Poisson summations:
first in `v₂` (`step1`), then in `v₁` after exchanging `Σ_{v₁}` and the new `Σ_{n₂}` (`step2`),
then in `v₀` after exchanging it past `Σ_{n₂}` and `Σ_{n₁}` (`theta_transform`). The result is
`t^{-3/2} (y₁Y)^{-1} Σ_n exp(−π Q*(n)/t)` with
`Q*(n) = n₂² + (n₁ − x₁n₂)²/y₁² + (n₀ − x₃n₂ − x₂(n₁ − x₁n₂))²/Y²` (`kern3`).

The one-dimensional input is the shifted and modulated Poisson formula
`Σ_v exp(−πd(v+a)² + 2πibv) = d^{-1/2} Σ_n exp(−π(n−b)²/d + 2πia(n−b))` (`poisson1`, from mathlib's
Gaussian Poisson summation). The exchanges of summation are justified by product Gaussian majorants
(`tsum_comm_of_le`) and by the bound `Σ_n exp(−π(n−c)²/D) ≤ Σ_k M_D(k)`, uniform in the shift `c`
(`tsum_gauss_shift_le`), obtained by comparing with the nearest integer to `c`.
-/

open Complex Real

namespace GaloisForLFunctions.RHTower.GL3

/-- **One-dimensional Poisson summation for a shifted, modulated Gaussian**:
`Σ_v exp(−π d (v + a)² + 2πi b v) = d^{-1/2} Σ_n exp(−π (n − b)²/d + 2πi a (n − b))`. -/
theorem poisson1 {d : ℝ} (hd : 0 < d) (a b : ℝ) :
    ∑' v : ℤ, cexp (-π * d * (v + a) ^ 2 + 2 * π * I * b * v) =
      1 / (Real.sqrt d : ℂ) * ∑' n : ℤ, cexp (-π * (n - b) ^ 2 / d + 2 * π * I * a * (n - b)) := by
  have hdC : 0 < (d : ℂ).re := by simpa using hd
  have key := Complex.tsum_exp_neg_quadratic hdC (-(d * a) + I * b)
  have hsq : (d : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt d : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hd.le]; push_cast; ring_nf
  rw [hsq] at key
  have hL : ∀ v : ℤ, cexp (-π * d * (v + a) ^ 2 + 2 * π * I * b * v) =
      cexp (-π * d * a ^ 2) * cexp (-π * d * v ^ 2 + 2 * π * (-(d * a) + I * b) * v) := by
    intro v; rw [← Complex.exp_add]; congr 1; ring
  have hR : ∀ n : ℤ, cexp (-π * d * a ^ 2) * cexp (-π / d * (n + I * (-(d * a) + I * b)) ^ 2) =
      cexp (-π * (n - b) ^ 2 / d + 2 * π * I * a * (n - b)) := by
    intro n
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [← Complex.exp_add]; congr 1
    field_simp
    linear_combination (2 * (d : ℂ) * a * b * I - (b : ℂ) ^ 2 * (I ^ 2 - 1) - (d : ℂ) ^ 2 * a ^ 2 -
      2 * (n : ℂ) * b) * Complex.I_sq
  simp_rw [hL]
  rw [tsum_mul_left, key, ← mul_assoc, mul_comm (cexp _) (1 / _), mul_assoc, ← tsum_mul_left]
  congr 1
  exact tsum_congr hR

/-! ### Gaussian summability and Fubini -/

/-- A shifted modulated Gaussian is summable over `ℤ`. -/
theorem summable_gauss {d : ℝ} (hd : 0 < d) (a b : ℝ) :
    Summable fun n : ℤ => cexp (-π * d * (n + a) ^ 2 + 2 * π * I * b * n) := by
  have h := (summable_jacobiTheta₂_term_iff ((b : ℂ) + I * (d * a)) (I * d)).2 (by simpa using hd)
  refine (h.mul_left (cexp (-π * d * a ^ 2))).congr fun n => ?_
  simp only [jacobiTheta₂_term]
  rw [← Complex.exp_add]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

theorem norm_gauss (d a b : ℝ) (n : ℤ) :
    ‖cexp (-π * d * (n + a) ^ 2 + 2 * π * I * b * n)‖ = Real.exp (-π * d * (n + a) ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [add_re, mul_re, neg_re, ofReal_re, ofReal_im, I_re, I_im]
  norm_cast
  simp

theorem summable_realGauss {d : ℝ} (hd : 0 < d) (a : ℝ) :
    Summable fun n : ℤ => Real.exp (-π * d * (n + a) ^ 2) := by
  have := (summable_norm_iff.2 (summable_gauss hd a 0))
  refine this.congr fun n => ?_
  rw [norm_gauss]

/-- Fubini for double series dominated by a product of summable functions. -/
theorem tsum_comm_of_le {f : ℤ → ℤ → ℂ} {A B : ℤ → ℝ} (hA : Summable A) (hB : Summable B)
    (hA0 : ∀ a, 0 ≤ A a) (hB0 : ∀ b, 0 ≤ B b) (hf : ∀ a b, ‖f a b‖ ≤ A a * B b) :
    ∑' a, ∑' b, f a b = ∑' b, ∑' a, f a b := by
  have hprod : Summable fun p : ℤ × ℤ => A p.1 * B p.2 := hA.mul_of_nonneg hB hA0 hB0
  have hu : Summable (Function.uncurry f) :=
    Summable.of_norm_bounded hprod fun p => hf p.1 p.2
  refine (hu.tsum_comm' (fun a => ?_) (fun b => ?_)).symm
  · exact Summable.of_norm_bounded (hB.mul_left (A a)) fun b => hf a b
  · exact Summable.of_norm_bounded (hA.mul_right (B b)) fun a => hf a b

/-- The majorant `k ↦ exp(−π k²/(4D)) + [k = 0]`. -/
noncomputable def gaussMaj (D : ℝ) (k : ℤ) : ℝ :=
  Real.exp (-π * (1 / (4 * D)) * ((k : ℝ) + 0) ^ 2) + if k = 0 then 1 else 0

theorem summable_gaussMaj {D : ℝ} (hD : 0 < D) : Summable (gaussMaj D) := by
  refine (summable_realGauss (by positivity : 0 < 1 / (4 * D)) 0).add ?_
  exact summable_of_ne_finset_zero (s := {0}) fun k hk => by simp at hk; simp [hk]

theorem gaussMaj_nonneg (D : ℝ) (k : ℤ) : 0 ≤ gaussMaj D k := by
  unfold gaussMaj; positivity

/-- **Shifted Gaussians are dominated uniformly in the shift**:
`exp(−π(n − c)²/D) ≤ M(n − round c)`. -/
theorem gauss_shift_le {D : ℝ} (hD : 0 < D) (c : ℝ) (n : ℤ) :
    Real.exp (-π * (1 / D) * ((n : ℝ) + -c) ^ 2) ≤ gaussMaj D (n - round c) := by
  unfold gaussMaj
  set k := n - round c
  have hc : |c - round c| ≤ 1 / 2 := abs_sub_round c
  by_cases hk : k = 0
  · simp only [hk, if_true]
    have : Real.exp (-π * (1 / D) * ((n : ℝ) + -c) ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ π * (1 / D) * ((n : ℝ) + -c) ^ 2 := by positivity
      linarith
    have := Real.exp_pos (-π * (1 / (4 * D)) * (((0 : ℤ) : ℝ) + 0) ^ 2)
    linarith
  · simp only [hk, if_false, add_zero]
    have hk1 : 1 ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      exact_mod_cast this
    have hnk : (n : ℝ) + -c = k - (c - round c) := by simp [k]; ring
    have hbound : (k : ℝ) ^ 2 / 4 ≤ ((n : ℝ) + -c) ^ 2 := by
      rw [hnk]
      have h1 : |(k : ℝ)| / 2 ≤ |(k : ℝ) - (c - round c)| := by
        have := abs_sub_abs_le_abs_sub (k : ℝ) (c - round c)
        linarith
      have h2 : ((k : ℝ) ^ 2) / 4 = (|(k : ℝ)| / 2) ^ 2 := by rw [div_pow, sq_abs]; ring
      rw [h2, ← sq_abs ((k : ℝ) - _)]
      exact pow_le_pow_left₀ (by positivity) h1 2
    rw [Real.exp_le_exp]
    have hpi := Real.pi_pos
    have : π * (1 / (4 * D)) * (k : ℝ) ^ 2 ≤ π * (1 / D) * ((n : ℝ) + -c) ^ 2 := by
      rw [show π * (1 / (4 * D)) * (k : ℝ) ^ 2 = π * (1 / D) * ((k : ℝ) ^ 2 / 4) by
        field_simp]
      exact mul_le_mul_of_nonneg_left hbound (by positivity)
    linarith

/-- The uniform bound `Σ_n exp(−π(n − c)²/D) ≤ Σ_k M(k)`. -/
theorem tsum_gauss_shift_le {D : ℝ} (hD : 0 < D) (c : ℝ) :
    ∑' n : ℤ, Real.exp (-π * (1 / D) * ((n : ℝ) + -c) ^ 2) ≤ ∑' k : ℤ, gaussMaj D k := by
  have hs := summable_gaussMaj hD
  set e : ℤ ≃ ℤ := Equiv.subRight (round c)
  have hshift : Summable (gaussMaj D ∘ e) := e.summable_iff.2 hs
  have hg : Summable fun n : ℤ => Real.exp (-π * (1 / D) * ((n : ℝ) + -c) ^ 2) :=
    summable_realGauss (by positivity) (-c)
  have hle : ∀ n : ℤ, Real.exp (-π * (1 / D) * ((n : ℝ) + -c) ^ 2) ≤ (gaussMaj D ∘ e) n :=
    fun n => gauss_shift_le hD c n
  calc ∑' n : ℤ, Real.exp (-π * (1 / D) * ((n : ℝ) + -c) ^ 2)
      ≤ ∑' n : ℤ, (gaussMaj D ∘ e) n := Summable.tsum_le_tsum hle hg hshift
    _ = ∑' k : ℤ, gaussMaj D k := e.tsum_eq (gaussMaj D)

/-! ### The iterated Poisson computation -/

theorem norm_cexp_re_im (r u : ℝ) : ‖cexp (-π * r + 2 * π * I * u)‖ = Real.exp (-π * r) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [add_re, mul_re, neg_re, ofReal_re, ofReal_im, I_re, I_im]
  norm_num

/-- Poisson in one variable with a constant factor in front. -/
theorem poisson1_mul (C : ℂ) {d : ℝ} (hd : 0 < d) (a b : ℝ) :
    ∑' v : ℤ, C * cexp (-π * d * (v + a) ^ 2 + 2 * π * I * b * v) =
      1 / (Real.sqrt d : ℂ) *
        ∑' n : ℤ, C * cexp (-π * (n - b) ^ 2 / d + 2 * π * I * a * (n - b)) := by
  rw [tsum_mul_left, poisson1 hd, tsum_mul_left]
  ring

section Theta
variable (t x1 x2 x3 y1 Y : ℝ)

/-- The ternary Gaussian `exp(−π t Q(v))` with `Q(v) = (Y v₀)² + (y₁(v₁ + x₂v₀))² + (v₂ + x₁v₁ + x₃v₀)²`. -/
noncomputable def gaussQ (v0 v1 v2 : ℤ) : ℂ :=
  cexp (-π * t * (((Y * v0 : ℝ) : ℂ) ^ 2 + ((y1 * (v1 + x2 * v0) : ℝ) : ℂ) ^ 2 +
    ((v2 + x1 * v1 + x3 * v0 : ℝ) : ℂ) ^ 2))

variable {t}

/-- **Step 1**: Poisson in `v₂`. -/
theorem step1 (ht : 0 < t) (v0 v1 : ℤ) :
    ∑' v2 : ℤ, gaussQ t x1 x2 x3 y1 Y v0 v1 v2 =
      1 / (Real.sqrt t : ℂ) * ∑' n2 : ℤ,
        cexp (-π * t * (((Y * v0 : ℝ) : ℂ) ^ 2 + ((y1 * (v1 + x2 * v0) : ℝ) : ℂ) ^ 2)) *
          cexp (-π * (n2 - (0 : ℝ)) ^ 2 / t +
            2 * π * I * ((x1 * v1 + x3 * v0 : ℝ) : ℂ) * (n2 - (0 : ℝ))) := by
  rw [← poisson1_mul _ ht]
  refine tsum_congr fun v2 => ?_
  rw [gaussQ, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The summand after two Poisson steps. -/
noncomputable def kern2 (t : ℝ) (v0 n2 n1 : ℤ) : ℂ :=
  cexp (-π * t * ((Y * v0 : ℝ) : ℂ) ^ 2) *
    cexp (-π * (n2 - (0 : ℝ)) ^ 2 / t + 2 * π * I * ((x3 * v0 : ℝ) : ℂ) * (n2 - (0 : ℝ))) *
    cexp (-π * (n1 - ((x1 * n2 : ℝ) : ℂ)) ^ 2 / ((t * y1 ^ 2 : ℝ) : ℂ) +
      2 * π * I * ((x2 * v0 : ℝ) : ℂ) * (n1 - ((x1 * n2 : ℝ) : ℂ)))

theorem norm_step1_term (t : ℝ) (v0 v1 n2 : ℤ) :
    ‖cexp (-π * t * (((Y * v0 : ℝ) : ℂ) ^ 2 + ((y1 * (v1 + x2 * v0) : ℝ) : ℂ) ^ 2)) *
        cexp (-π * (n2 - (0 : ℝ)) ^ 2 / t +
          2 * π * I * ((x1 * v1 + x3 * v0 : ℝ) : ℂ) * (n2 - (0 : ℝ)))‖ =
      (Real.exp (-π * t * (Y * v0) ^ 2) *
        Real.exp (-π * (t * y1 ^ 2) * ((v1 : ℝ) + x2 * v0) ^ 2)) *
        Real.exp (-π * (1 / t) * ((n2 : ℝ) + 0) ^ 2) := by
  rw [norm_mul]
  congr 1
  · rw [show -π * t * (((Y * v0 : ℝ) : ℂ) ^ 2 + ((y1 * (v1 + x2 * v0) : ℝ) : ℂ) ^ 2) =
        ((-π * t * ((Y * v0) ^ 2 + (y1 * (v1 + x2 * v0)) ^ 2) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_ofReal, ← Real.exp_add]
    congr 1; ring
  · rw [show -π * (n2 - ((0 : ℝ) : ℂ)) ^ 2 / t +
        2 * π * I * ((x1 * v1 + x3 * v0 : ℝ) : ℂ) * (n2 - ((0 : ℝ) : ℂ)) =
        -π * ((n2 : ℝ) ^ 2 / t : ℝ) + 2 * π * I * ((x1 * v1 + x3 * v0) * n2 : ℝ) by
        push_cast; ring,
      norm_cexp_re_im]
    congr 1; ring

/-- **Step 2**: Poisson in `v₁` after exchanging `Σ_{v₁}` and `Σ_{n₂}`. -/
theorem step2 {t : ℝ} (ht : 0 < t) (hy1 : 0 < y1) (v0 : ℤ) :
    ∑' v1 : ℤ, ∑' v2 : ℤ, gaussQ t x1 x2 x3 y1 Y v0 v1 v2 =
      1 / (Real.sqrt t : ℂ) * (1 / (Real.sqrt (t * y1 ^ 2) : ℂ) *
        ∑' n2 : ℤ, ∑' n1 : ℤ, kern2 x1 x2 x3 y1 Y t v0 n2 n1) := by
  have hd : 0 < t * y1 ^ 2 := by positivity
  simp_rw [step1 x1 x2 x3 y1 Y ht]
  rw [tsum_mul_left]
  congr 1
  rw [tsum_comm_of_le (A := fun v1 : ℤ => Real.exp (-π * t * (Y * v0) ^ 2) *
      Real.exp (-π * (t * y1 ^ 2) * ((v1 : ℝ) + x2 * v0) ^ 2))
    (B := fun n2 : ℤ => Real.exp (-π * (1 / t) * ((n2 : ℝ) + 0) ^ 2))
    ((summable_realGauss hd _).mul_left _) (summable_realGauss (by positivity) _)
    (fun _ => by positivity) (fun _ => by positivity)
    (fun v1 n2 => le_of_eq (norm_step1_term x1 x2 x3 y1 Y t v0 v1 n2))]
  rw [← tsum_mul_left]
  refine tsum_congr fun n2 => ?_
  have e : ∀ v1 : ℤ,
      cexp (-π * t * (((Y * v0 : ℝ) : ℂ) ^ 2 + ((y1 * (v1 + x2 * v0) : ℝ) : ℂ) ^ 2)) *
        cexp (-π * (n2 - (0 : ℝ)) ^ 2 / t +
          2 * π * I * ((x1 * v1 + x3 * v0 : ℝ) : ℂ) * (n2 - (0 : ℝ))) =
      (cexp (-π * t * ((Y * v0 : ℝ) : ℂ) ^ 2) *
        cexp (-π * (n2 - (0 : ℝ)) ^ 2 / t + 2 * π * I * ((x3 * v0 : ℝ) : ℂ) * (n2 - (0 : ℝ)))) *
        cexp (-π * (t * y1 ^ 2 : ℝ) * (v1 + (x2 * v0 : ℝ)) ^ 2 +
          2 * π * I * ((x1 * n2 : ℝ) : ℂ) * v1) := by
    intro v1
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [e]
  rw [poisson1_mul _ hd]
  congr 1

theorem norm_kern2 (t : ℝ) (v0 n2 n1 : ℤ) :
    ‖kern2 x1 x2 x3 y1 Y t v0 n2 n1‖ =
      Real.exp (-π * (t * Y ^ 2) * ((v0 : ℝ) + 0) ^ 2) *
        (Real.exp (-π * (1 / t) * ((n2 : ℝ) + 0) ^ 2) *
          Real.exp (-π * (1 / (t * y1 ^ 2)) * ((n1 : ℝ) + -(x1 * n2)) ^ 2)) := by
  simp only [kern2, norm_mul]
  rw [show -π * t * ((Y * v0 : ℝ) : ℂ) ^ 2 = ((-π * (t * Y ^ 2) * ((v0 : ℝ) + 0) ^ 2 : ℝ) : ℂ) by
      push_cast; ring,
    Complex.norm_exp_ofReal,
    show -π * (n2 - ((0 : ℝ) : ℂ)) ^ 2 / t + 2 * π * I * ((x3 * v0 : ℝ) : ℂ) * (n2 - ((0 : ℝ) : ℂ)) =
      -π * ((1 / t) * ((n2 : ℝ) + 0) ^ 2 : ℝ) + 2 * π * I * (x3 * v0 * n2 : ℝ) by
      push_cast; ring,
    norm_cexp_re_im,
    show -π * (n1 - ((x1 * n2 : ℝ) : ℂ)) ^ 2 / ((t * y1 ^ 2 : ℝ) : ℂ) +
        2 * π * I * ((x2 * v0 : ℝ) : ℂ) * (n1 - ((x1 * n2 : ℝ) : ℂ)) =
      -π * ((1 / (t * y1 ^ 2)) * ((n1 : ℝ) + -(x1 * n2)) ^ 2 : ℝ) +
        2 * π * I * (x2 * v0 * (n1 - x1 * n2) : ℝ) by
      push_cast; ring,
    norm_cexp_re_im]
  simp only [mul_assoc]

/-- The summand after three Poisson steps. -/
noncomputable def kern3 (t : ℝ) (n2 n1 n0 : ℤ) : ℂ :=
  cexp (-π * (n2 - (0 : ℝ)) ^ 2 / t) *
    cexp (-π * (n1 - ((x1 * n2 : ℝ) : ℂ)) ^ 2 / ((t * y1 ^ 2 : ℝ) : ℂ)) *
    cexp (-π * (n0 - ((x3 * n2 + x2 * (n1 - x1 * n2) : ℝ) : ℂ)) ^ 2 / ((t * Y ^ 2 : ℝ) : ℂ) +
      2 * π * I * ((0 : ℝ) : ℂ) * (n0 - ((x3 * n2 + x2 * (n1 - x1 * n2) : ℝ) : ℂ)))

/-- **The ternary theta transformation** (three Poisson steps). -/
theorem theta_transform {t : ℝ} (ht : 0 < t) (hy1 : 0 < y1) (hY : 0 < Y) :
    ∑' v0 : ℤ, ∑' v1 : ℤ, ∑' v2 : ℤ, gaussQ t x1 x2 x3 y1 Y v0 v1 v2 =
      1 / (Real.sqrt t : ℂ) * (1 / (Real.sqrt (t * y1 ^ 2) : ℂ) *
        (1 / (Real.sqrt (t * Y ^ 2) : ℂ) *
          ∑' n2 : ℤ, ∑' n1 : ℤ, ∑' n0 : ℤ, kern3 x1 x2 x3 y1 Y t n2 n1 n0)) := by
  have hd1 : 0 < t * y1 ^ 2 := by positivity
  have hd0 : 0 < t * Y ^ 2 := by positivity
  simp_rw [step2 x1 x2 x3 y1 Y ht hy1]
  rw [tsum_mul_left, tsum_mul_left]
  congr 2
  set M := ∑' k : ℤ, gaussMaj (t * y1 ^ 2) k
  have hM : 0 ≤ M := tsum_nonneg (gaussMaj_nonneg _)
  -- exchange `v₀` and `n₂`
  have hsum1 : ∀ v0 n2 : ℤ, Summable fun n1 : ℤ => kern2 x1 x2 x3 y1 Y t v0 n2 n1 := by
    intro v0 n2
    refine Summable.of_norm_bounded
      ((summable_realGauss (d := 1 / (t * y1 ^ 2)) (by positivity) (-(x1 * n2))).mul_left
      (Real.exp (-π * (t * Y ^ 2) * ((v0 : ℝ) + 0) ^ 2) *
        Real.exp (-π * (1 / t) * ((n2 : ℝ) + 0) ^ 2))) fun n1 => ?_
    rw [norm_kern2]; exact le_of_eq (by ring)
  rw [tsum_comm_of_le (A := fun v0 : ℤ => Real.exp (-π * (t * Y ^ 2) * ((v0 : ℝ) + 0) ^ 2))
    (B := fun n2 : ℤ => Real.exp (-π * (1 / t) * ((n2 : ℝ) + 0) ^ 2) * M)
    (summable_realGauss hd0 _) ((summable_realGauss (d := 1 / t) (by positivity) _).mul_right M)
    (fun _ => by positivity) (fun _ => by positivity) ?_]
  swap
  · intro v0 n2
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · exact (summable_norm_iff.2 (hsum1 v0 n2))
    simp only [norm_kern2]
    rw [tsum_mul_left, tsum_mul_left, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
    exact tsum_gauss_shift_le hd1 (x1 * n2)
  rw [← tsum_mul_left]
  refine tsum_congr fun n2 => ?_
  -- exchange `v₀` and `n₁`
  rw [tsum_comm_of_le (A := fun v0 : ℤ => Real.exp (-π * (t * Y ^ 2) * ((v0 : ℝ) + 0) ^ 2))
    (B := fun n1 : ℤ => Real.exp (-π * (1 / t) * ((n2 : ℝ) + 0) ^ 2) *
      Real.exp (-π * (1 / (t * y1 ^ 2)) * ((n1 : ℝ) + -(x1 * n2)) ^ 2))
    (summable_realGauss hd0 _)
    ((summable_realGauss (d := 1 / (t * y1 ^ 2)) (by positivity) _).mul_left _)
    (fun _ => by positivity) (fun _ => by positivity)
    (fun v0 n1 => le_of_eq (norm_kern2 x1 x2 x3 y1 Y t v0 n2 n1))]
  rw [← tsum_mul_left]
  refine tsum_congr fun n1 => ?_
  have e : ∀ v0 : ℤ, kern2 x1 x2 x3 y1 Y t v0 n2 n1 =
      (cexp (-π * (n2 - (0 : ℝ)) ^ 2 / t) *
        cexp (-π * (n1 - ((x1 * n2 : ℝ) : ℂ)) ^ 2 / ((t * y1 ^ 2 : ℝ) : ℂ))) *
        cexp (-π * (t * Y ^ 2 : ℝ) * (v0 + ((0 : ℝ) : ℂ)) ^ 2 +
          2 * π * I * ((x3 * n2 + x2 * (n1 - x1 * n2) : ℝ) : ℂ) * v0) := by
    intro v0
    simp only [kern2]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [e]
  rw [poisson1_mul _ hd0]
  congr 1

end Theta

end GaloisForLFunctions.RHTower.GL3
