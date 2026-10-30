import GaloisForLFunctions.HilbertianExplicitFormulas.TheSamePointQuantumOfAReflectionConfiguration
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The resolvent Hilbertian explicit formula

For a point `s = σ + it` with `σ > 1/2`, the resolvent test `1/(s - ρ)` has

* same-point norm `S(s) = ∑ m_ρ / |s - ρ|²` (a Hilbert norm, not holomorphic in the zeros);
* explicit value `E(s) = ∑ m_ρ Re (1/(s - ρ))`, which for the zeta divisor is `Re ξ'/ξ (s)` and hence,
  for `σ > 1`, a prime sum plus archimedean terms.

The exact relation, on every reflection configuration (`sub_mul_samePointResolvent_eq`), is

  `(σ - 1/2) S(s) = E(s) + D(s)`,  `D(s) = ∑ m_ρ · 2(σ - 1/2)(β - 1/2)² / (|s - ρ|² |s - ρ*|²)`,

obtained from the pair identity `|s - ρ*|² - |s - ρ|² = (2σ - 1)(2β - 1)` and symmetrization over
`ρ ↦ ρ* = 1 - conj ρ`. The defect `D` is a weighted second depth moment: it is nonnegative and vanishes
exactly on critical configurations. Two consequences:

* **Sandwich.** If every point has `Re ρ ≤ 1/2 + w`, then `(σ - 1/2 - w) S ≤ E ≤ (σ - 1/2) S`: the
  explicit formula reads the same-point norm up to relative error `w/(σ - 1/2)`, and exactly iff the
  configuration is critical.
* **Depth moments.** Along the vertical line, `∫ D(σ + it) dt = π ∑ m_ρ d²/(u² - d²)` with
  `u = σ - 1/2`, `d = β - 1/2`, which is `π ∑_{k ≥ 1} M_{2k} u^{-2k}` with `M_{2k} = ∑ m_ρ d^{2k}`.
-/

open Complex MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.HilbertianExplicitFormulas

noncomputable section

/-! ## The pair identity -/

/-- `|s - ρ|² = (σ - β)² + (t - γ)²`. -/
theorem normSq_sub_eq (s ρ : ℂ) :
    normSq (s - ρ) = (s.re - ρ.re) ^ 2 + (s.im - ρ.im) ^ 2 := by
  rw [normSq_apply, sub_re, sub_im]; ring

/-- `|s - ρ*|² - |s - ρ|² = (2σ - 1)(2β - 1)`. -/
theorem normSq_sub_lineReflect_sub_normSq (s ρ : ℂ) :
    normSq (s - RHTower.lineReflect ρ) - normSq (s - ρ) = (2 * s.re - 1) * (2 * ρ.re - 1) := by
  rw [normSq_sub_eq, normSq_sub_eq, RHTower.lineReflect_re,
    ReflectionConfiguration.lineReflect_im]
  ring

/-- **Pair identity.** The depth-weighted resolvent norms of `ρ` and `ρ*` add up to
`4(σ - 1/2)(β - 1/2)² / (|s - ρ|² |s - ρ*|²)`. -/
theorem pair_depth_resolvent (s ρ : ℂ) (hA : normSq (s - ρ) ≠ 0)
    (hB : normSq (s - RHTower.lineReflect ρ) ≠ 0) :
    (ρ.re - 1 / 2) / normSq (s - ρ) +
        ((RHTower.lineReflect ρ).re - 1 / 2) / normSq (s - RHTower.lineReflect ρ) =
      4 * (s.re - 1 / 2) * (ρ.re - 1 / 2) ^ 2 /
        (normSq (s - ρ) * normSq (s - RHTower.lineReflect ρ)) := by
  have hdiff := normSq_sub_lineReflect_sub_normSq s ρ
  rw [RHTower.lineReflect_re, div_add_div _ _ hA hB,
    div_eq_div_iff (mul_ne_zero hA hB) (mul_ne_zero hA hB)]
  linear_combination (ρ.re - 1 / 2) * (normSq (s - ρ) * normSq (s - RHTower.lineReflect ρ)) * hdiff

/-- Pointwise: `(σ - 1/2)/|s - ρ|² - Re (1/(s - ρ)) = (β - 1/2)/|s - ρ|²`. -/
theorem sub_inv_re_eq (s ρ : ℂ) :
    (s.re - 1 / 2) / normSq (s - ρ) - ((s - ρ)⁻¹).re = (ρ.re - 1 / 2) / normSq (s - ρ) := by
  rw [Complex.inv_re, sub_re, ← sub_div]
  ring_nf

namespace ReflectionConfiguration

variable (Z : ReflectionConfiguration)

/-- Same-point resolvent norm `S(s) = ∑ m_ρ / |s - ρ|²`. -/
def samePointResolvent (s : ℂ) : ℝ := ∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) / normSq (s - ρ)

/-- Explicit resolvent value `E(s) = ∑ m_ρ Re (1/(s - ρ))`. -/
def explicitResolvent (s : ℂ) : ℝ := ∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) * ((s - ρ)⁻¹).re

/-- Resolvent line-reflection defect `D(s)`. -/
def resolventDefect (s : ℂ) : ℝ :=
  ∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) *
    (2 * (s.re - 1 / 2) * (ρ.re - 1 / 2) ^ 2 /
      (normSq (s - ρ) * normSq (s - RHTower.lineReflect ρ)))

/-- Reindexing a configuration sum by line reflection. -/
theorem sum_lineReflect (f : ℂ → ℝ) :
    ∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) * f (RHTower.lineReflect ρ) =
      ∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) * f ρ := by
  refine Finset.sum_nbij' RHTower.lineReflect RHTower.lineReflect
    (fun ρ hρ => Z.reflect_mem ρ hρ) (fun ρ hρ => Z.reflect_mem ρ hρ)
    (fun ρ _ => RHTower.lineReflect_involutive ρ) (fun ρ _ => RHTower.lineReflect_involutive ρ)
    (fun ρ _ => ?_)
  rw [Z.mult_reflect]

theorem normSq_sub_ne_zero {s ρ : ℂ} (hs : s ∉ Z.support) (hρ : ρ ∈ Z.support) :
    normSq (s - ρ) ≠ 0 := by
  rw [Ne, normSq_eq_zero, sub_eq_zero]
  rintro rfl
  exact hs hρ

/-- **Resolvent Hilbertian explicit formula.** `(σ - 1/2) S(s) = E(s) + D(s)`. -/
theorem sub_mul_samePointResolvent_eq {s : ℂ} (hs : s ∉ Z.support) :
    (s.re - 1 / 2) * Z.samePointResolvent s = Z.explicitResolvent s + Z.resolventDefect s := by
  have hpt : (s.re - 1 / 2) * Z.samePointResolvent s - Z.explicitResolvent s =
      ∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) * ((ρ.re - 1 / 2) / normSq (s - ρ)) := by
    rw [samePointResolvent, explicitResolvent, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [← sub_inv_re_eq]
    ring
  have hsym := Z.sum_lineReflect (fun ρ => (ρ.re - 1 / 2) / normSq (s - ρ))
  have hpair : 2 * ∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) * ((ρ.re - 1 / 2) / normSq (s - ρ)) =
      2 * Z.resolventDefect s := by
    calc 2 * ∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) * ((ρ.re - 1 / 2) / normSq (s - ρ))
        = ∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) * ((ρ.re - 1 / 2) / normSq (s - ρ)) +
            ∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) * (((RHTower.lineReflect ρ).re - 1 / 2) /
              normSq (s - RHTower.lineReflect ρ)) := by rw [hsym]; ring
      _ = ∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) * ((ρ.re - 1 / 2) / normSq (s - ρ) +
            ((RHTower.lineReflect ρ).re - 1 / 2) / normSq (s - RHTower.lineReflect ρ)) := by
          rw [← Finset.sum_add_distrib]; simp_rw [mul_add]
      _ = 2 * Z.resolventDefect s := by
          rw [resolventDefect, Finset.mul_sum]
          refine Finset.sum_congr rfl fun ρ hρ => ?_
          rw [pair_depth_resolvent s ρ (Z.normSq_sub_ne_zero hs hρ)
            (Z.normSq_sub_ne_zero hs (Z.reflect_mem ρ hρ))]
          ring
  linarith

theorem resolventDefect_nonneg {s : ℂ} (hσ : 1 / 2 < s.re) : 0 ≤ Z.resolventDefect s :=
  Finset.sum_nonneg fun ρ _ => mul_nonneg (Nat.cast_nonneg _)
    (div_nonneg (by nlinarith [sq_nonneg (ρ.re - 1 / 2)])
      (mul_nonneg (normSq_nonneg _) (normSq_nonneg _)))

/-- The resolvent defect vanishes exactly on critical configurations. -/
theorem resolventDefect_eq_zero_iff {s : ℂ} (hs : s ∉ Z.support) (hσ : 1 / 2 < s.re) :
    Z.resolventDefect s = 0 ↔ Z.IsCritical := by
  constructor
  · intro h ρ hρ
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun ρ _ => mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (by nlinarith [sq_nonneg (ρ.re - 1 / 2)])
        (mul_nonneg (normSq_nonneg _) (normSq_nonneg _))))).mp h ρ hρ
    have hA := (normSq_nonneg (s - ρ)).lt_of_ne' (Z.normSq_sub_ne_zero hs hρ)
    have hB := (normSq_nonneg _).lt_of_ne'
      (Z.normSq_sub_ne_zero hs (Z.reflect_mem ρ hρ))
    have hm : (0 : ℝ) < Z.mult ρ := by exact_mod_cast Z.mult_pos ρ hρ
    rcases mul_eq_zero.mp hterm with h0 | h0
    · exact absurd h0 hm.ne'
    · rw [div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · have : (ρ.re - 1 / 2) ^ 2 = 0 := by
          rcases mul_eq_zero.mp h0 with h1 | h1
          · rcases mul_eq_zero.mp h1 with h2 | h2
            · norm_num at h2
            · linarith
          · exact h1
        nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp this]
      · exact absurd h0 (mul_pos hA hB).ne'
  · intro hZ
    refine Finset.sum_eq_zero fun ρ hρ => ?_
    rw [hZ ρ hρ]
    simp

/-- The explicit value never exceeds the scaled same-point norm. -/
theorem explicitResolvent_le {s : ℂ} (hs : s ∉ Z.support) (hσ : 1 / 2 < s.re) :
    Z.explicitResolvent s ≤ (s.re - 1 / 2) * Z.samePointResolvent s := by
  rw [Z.sub_mul_samePointResolvent_eq hs]
  linarith [Z.resolventDefect_nonneg hσ]

/-- **Sandwich.** If every point satisfies `Re ρ ≤ 1/2 + w`, then `(σ - 1/2 - w) S ≤ E`. -/
theorem sub_width_mul_samePointResolvent_le {s : ℂ} {w : ℝ}
    (hw : ∀ ρ ∈ Z.support, ρ.re ≤ 1 / 2 + w) :
    (s.re - 1 / 2 - w) * Z.samePointResolvent s ≤ Z.explicitResolvent s := by
  rw [samePointResolvent, explicitResolvent, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  rw [Complex.inv_re, sub_re]
  calc (s.re - 1 / 2 - w) * ((Z.mult ρ : ℝ) / normSq (s - ρ))
      = (Z.mult ρ : ℝ) * ((s.re - 1 / 2 - w) / normSq (s - ρ)) := by ring
    _ ≤ (Z.mult ρ : ℝ) * ((s.re - ρ.re) / normSq (s - ρ)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (by linarith [hw ρ hρ]) (normSq_nonneg _))
          (Nat.cast_nonneg _)

/-- The explicit formula computes the same-point resolvent norm exactly iff the configuration is
critical. -/
theorem explicitResolvent_eq_iff {s : ℂ} (hs : s ∉ Z.support) (hσ : 1 / 2 < s.re) :
    Z.explicitResolvent s = (s.re - 1 / 2) * Z.samePointResolvent s ↔ Z.IsCritical := by
  rw [← Z.resolventDefect_eq_zero_iff hs hσ, Z.sub_mul_samePointResolvent_eq hs]
  constructor <;> intro h <;> linarith

/-! ## The vertical integral of the defect -/

theorem integrable_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => (a ^ 2 + t ^ 2)⁻¹) := by
  have h := (integrable_inv_one_add_sq.comp_div ha.ne').const_mul (a⁻¹ ^ 2)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only
  field_simp

theorem integral_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ, (a ^ 2 + t ^ 2)⁻¹ = Real.pi / a := by
  calc ∫ t : ℝ, (a ^ 2 + t ^ 2)⁻¹ = ∫ t : ℝ, a⁻¹ ^ 2 * (1 + (t / a) ^ 2)⁻¹ := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        simp only
        field_simp
    _ = a⁻¹ ^ 2 * (|a| * ∫ t : ℝ, (1 + t ^ 2)⁻¹) := by
        rw [integral_const_mul]
        congr 1
        exact (Measure.integral_comp_div (fun t : ℝ => (1 + t ^ 2)⁻¹) a).trans (smul_eq_mul _ _)
    _ = Real.pi / a := by
        rw [integral_univ_inv_one_add_sq, abs_of_pos ha]
        field_simp

/-- Partial fractions for two Cauchy kernels: `∫ dt / ((a² + t²)(b² + t²)) = π / (a b (a + b))`. -/
theorem integral_inv_mul_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ∫ t : ℝ, ((a ^ 2 + t ^ 2) * (b ^ 2 + t ^ 2))⁻¹ = Real.pi / (a * b * (a + b)) := by
  have hba : b ^ 2 - a ^ 2 ≠ 0 := by
    intro h
    have : (b - a) * (b + a) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hab (by linarith)
    · linarith
  have hpf : ∀ t : ℝ, ((a ^ 2 + t ^ 2) * (b ^ 2 + t ^ 2))⁻¹ =
      (b ^ 2 - a ^ 2)⁻¹ * ((a ^ 2 + t ^ 2)⁻¹ - (b ^ 2 + t ^ 2)⁻¹) := by
    intro t
    have h1 : a ^ 2 + t ^ 2 ≠ 0 := by positivity
    have h2 : b ^ 2 + t ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [hpf]
  rw [integral_const_mul, integral_sub (integrable_inv_sq_add_sq ha) (integrable_inv_sq_add_sq hb),
    integral_inv_sq_add_sq ha, integral_inv_sq_add_sq hb]
  have hab' : a + b ≠ 0 := by positivity
  field_simp
  ring

theorem integrable_inv_mul_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Integrable (fun t : ℝ => ((a ^ 2 + t ^ 2) * (b ^ 2 + t ^ 2))⁻¹) := by
  have h := ((integrable_inv_sq_add_sq ha).sub (integrable_inv_sq_add_sq hb)).const_mul
    (b ^ 2 - a ^ 2)⁻¹
  refine h.congr (Eventually.of_forall fun t => ?_)
  have hba : b ^ 2 - a ^ 2 ≠ 0 := by
    intro h
    have : (b - a) * (b + a) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hab (by linarith)
    · linarith
  have h1 : a ^ 2 + t ^ 2 ≠ 0 := by positivity
  have h2 : b ^ 2 + t ^ 2 ≠ 0 := by positivity
  simp only [Pi.sub_apply]
  field_simp
  ring

/-- The defect summand of one point along the vertical line `Re s = σ`. -/
def pointDefect (σ : ℝ) (ρ : ℂ) (t : ℝ) : ℝ :=
  2 * (σ - 1 / 2) * (ρ.re - 1 / 2) ^ 2 /
    (normSq ((σ + t * I) - ρ) * normSq ((σ + t * I) - RHTower.lineReflect ρ))

theorem pointDefect_eq (σ : ℝ) (ρ : ℂ) (t : ℝ) :
    pointDefect σ ρ t = 2 * (σ - 1 / 2) * (ρ.re - 1 / 2) ^ 2 *
      (((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2) * ((σ - 1 + ρ.re) ^ 2 + (t - ρ.im) ^ 2))⁻¹ := by
  rw [pointDefect, normSq_sub_eq, normSq_sub_eq, RHTower.lineReflect_re,
    ReflectionConfiguration.lineReflect_im, div_eq_mul_inv]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add]
  ring_nf

/-- **One point along the vertical line.** For `|β - 1/2| < σ - 1/2`,
`∫ pointDefect dt = π d² / (u² - d²)` with `u = σ - 1/2`, `d = β - 1/2`. -/
theorem integral_pointDefect {σ : ℝ} {ρ : ℂ} (hρ : |ρ.re - 1 / 2| < σ - 1 / 2) :
    Integrable (pointDefect σ ρ) ∧
      ∫ t : ℝ, pointDefect σ ρ t =
        Real.pi * (ρ.re - 1 / 2) ^ 2 / ((σ - 1 / 2) ^ 2 - (ρ.re - 1 / 2) ^ 2) := by
  rcases eq_or_ne ρ.re (1 / 2) with hc | hc
  · have h0 : pointDefect σ ρ = 0 := by
      funext t; rw [pointDefect_eq, hc, Pi.zero_apply]; ring
    rw [h0, hc]
    simp
  have ha : 0 < σ - ρ.re := by linarith [le_abs_self (ρ.re - 1 / 2)]
  have hb : 0 < σ - 1 + ρ.re := by linarith [neg_abs_le (ρ.re - 1 / 2)]
  have hab : σ - ρ.re ≠ σ - 1 + ρ.re := by
    intro h; exact hc (by linarith)
  have hfun : pointDefect σ ρ = fun t => 2 * (σ - 1 / 2) * (ρ.re - 1 / 2) ^ 2 *
      (fun u : ℝ => (((σ - ρ.re) ^ 2 + u ^ 2) * ((σ - 1 + ρ.re) ^ 2 + u ^ 2))⁻¹) (t - ρ.im) := by
    funext t; rw [pointDefect_eq]
  rw [hfun]
  refine ⟨((integrable_inv_mul_inv ha hb hab).comp_sub_right ρ.im).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun u : ℝ => (((σ - ρ.re) ^ 2 + u ^ 2) * ((σ - 1 + ρ.re) ^ 2 + u ^ 2))⁻¹),
    integral_inv_mul_inv ha hb hab]
  have hden : (σ - 1 / 2) ^ 2 - (ρ.re - 1 / 2) ^ 2 = (σ - ρ.re) * (σ - 1 + ρ.re) := by ring
  rw [hden]
  have hsum : σ - ρ.re + (σ - 1 + ρ.re) = 2 * (σ - 1 / 2) := by ring
  rw [hsum]
  have hu : σ - 1 / 2 ≠ 0 := by linarith [abs_nonneg (ρ.re - 1 / 2)]
  have hu2 : 2 * σ - 1 ≠ 0 := fun h => hu (by linarith)
  field_simp

/-- The resolvent defect along the vertical line is the sum of the point defects. -/
theorem resolventDefect_vertical (σ t : ℝ) :
    Z.resolventDefect (σ + t * I) = ∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) * pointDefect σ ρ t := by
  rw [resolventDefect]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [pointDefect]
  simp

/-- Even depth moment `M_{2k} = ∑ m_ρ (β - 1/2)^{2k}`. -/
def depthMoment (k : ℕ) : ℝ := ∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) * (ρ.re - 1 / 2) ^ (2 * k)

/-- **Depth moments from the resolvent defect.** If every point has `|β - 1/2| < σ - 1/2`, the
vertical integral of the defect is `π ∑ m_ρ d²/(u² - d²)`, and this is the generating series
`π ∑_{k ≥ 1} M_{2k} u^{-2k}` of the even depth moments. -/
theorem integral_resolventDefect_vertical {σ : ℝ}
    (hw : ∀ ρ ∈ Z.support, |ρ.re - 1 / 2| < σ - 1 / 2) :
    ∫ t : ℝ, Z.resolventDefect (σ + t * I) =
        Real.pi * ∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) *
          ((ρ.re - 1 / 2) ^ 2 / ((σ - 1 / 2) ^ 2 - (ρ.re - 1 / 2) ^ 2)) ∧
      HasSum (fun k : ℕ => Z.depthMoment (k + 1) / (σ - 1 / 2) ^ (2 * (k + 1)))
        (∑ ρ ∈ Z.support, (Z.mult ρ : ℝ) *
          ((ρ.re - 1 / 2) ^ 2 / ((σ - 1 / 2) ^ 2 - (ρ.re - 1 / 2) ^ 2))) := by
  constructor
  · simp_rw [Z.resolventDefect_vertical σ]
    rw [integral_finsetSum _ fun ρ hρ => ((integral_pointDefect (hw ρ hρ)).1).const_mul _,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [integral_const_mul, (integral_pointDefect (hw ρ hρ)).2]
    ring
  · have hterm : ∀ ρ ∈ Z.support, HasSum
        (fun k : ℕ => (Z.mult ρ : ℝ) * (ρ.re - 1 / 2) ^ (2 * (k + 1)) / (σ - 1 / 2) ^ (2 * (k + 1)))
        ((Z.mult ρ : ℝ) * ((ρ.re - 1 / 2) ^ 2 / ((σ - 1 / 2) ^ 2 - (ρ.re - 1 / 2) ^ 2))) := by
      intro ρ hρ
      set u := σ - 1 / 2
      set d := ρ.re - 1 / 2
      have hu : 0 < u := (abs_nonneg d).trans_lt (hw ρ hρ)
      have hdu : d ^ 2 < u ^ 2 := sq_lt_sq' (by linarith [neg_abs_le d, hw ρ hρ])
        (by linarith [le_abs_self d, hw ρ hρ])
      set r := (d / u) ^ 2
      have hr0 : 0 ≤ r := sq_nonneg _
      have hr1 : r < 1 := by
        simp only [r, div_pow]
        rwa [div_lt_one (by positivity)]
      have hgeo := (hasSum_geometric_of_lt_one hr0 hr1).mul_left ((Z.mult ρ : ℝ) * r)
      have hu2 : u ^ 2 ≠ 0 := by positivity
      have hne : u ^ 2 - d ^ 2 ≠ 0 := by linarith
      have hf : (fun k : ℕ => (Z.mult ρ : ℝ) * d ^ (2 * (k + 1)) / u ^ (2 * (k + 1))) =
          fun k : ℕ => (Z.mult ρ : ℝ) * r * r ^ k := by
        funext k
        simp only [r, div_pow, ← pow_mul, mul_add, mul_one, pow_add]
        field_simp
      have hv : (Z.mult ρ : ℝ) * (d ^ 2 / (u ^ 2 - d ^ 2)) = (Z.mult ρ : ℝ) * r * (1 - r)⁻¹ := by
        simp only [r, div_pow]
        field_simp
      rw [hf, hv]
      exact hgeo
    have := hasSum_sum hterm
    simpa only [depthMoment, Finset.sum_div] using this

end ReflectionConfiguration

end

end GaloisForLFunctions.HilbertianExplicitFormulas
