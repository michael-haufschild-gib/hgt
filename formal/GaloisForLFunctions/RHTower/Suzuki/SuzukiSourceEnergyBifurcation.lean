import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The two-scale split of the literal source energy

The paired parity energy of a rotated exponential pair is an exact Pythagorean identity: the two
rotated components recombine into `(1 + γ²)` times the unrotated squares.  Against the condensed
shift scale, Jensen's resolvent bound turns a small Stieltjes factor into a large first moment.

The energy split itself is the pointwise decomposition `t = min(t,T) + (t-T)₊`.  Weak collapse kills
the truncated part while the first moment is conserved, so all of the energy passes into the excess
part, whose carrier has vanishing probability.  Cauchy–Schwarz against the constant one on that
carrier then forces the second moment to diverge.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## `(337)`: the rotated parity energy -/

/-- **The rotated parity pair recombines exactly.** -/
theorem rotated_parity_energy (A B γ θ : ℝ) :
    (A * Real.cos θ + γ * (B * Real.sin θ)) ^ 2
        + (B * Real.sin θ - γ * (A * Real.cos θ)) ^ 2
      = (1 + γ ^ 2) * ((A * Real.cos θ) ^ 2 + (B * Real.sin θ) ^ 2) := by
  ring

/-! ## `(340)`: the first moment against the shift scale -/

/-- **`(340)`: a small Stieltjes factor forces a large first moment relative to the shift.** -/
theorem moment_div_shift_ge {x m r R : ℝ} (hr : 0 < r) (hx : 0 < x)
    (hjensen : r / (r + m) ≤ x) (hm : 0 ≤ m) (hR : 0 < R) (hxR : x ≤ 1 / R) :
    R - 1 ≤ m / r := by
  have hrm : (0 : ℝ) < r + m := by linarith
  have hstep : r ≤ x * (r + m) := by
    rw [div_le_iff₀ hrm] at hjensen
    linarith
  have hxm : r * (1 - x) ≤ x * m := by nlinarith
  have hxpos : 0 < x := hx
  have hinv : R ≤ 1 / x := by
    rw [le_div_iff₀ hxpos]
    rw [le_div_iff₀ hR] at hxR
    linarith
  have hmr : (1 - x) / x ≤ m / r := by
    rw [div_le_div_iff₀ hxpos hr]
    nlinarith
  have hval : (1 - x) / x = 1 / x - 1 := by
    field_simp
  rw [hval] at hmr
  linarith

/-! ## `(343)`: the exact energy split -/

/-- **`(343)`: the pointwise truncation identity.** -/
theorem min_add_posPart (t T : ℝ) : min t T + max (t - T) 0 = t := by
  rcases le_total t T with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_left (by linarith)]
    ring

/-! ## `(344)`: Cauchy--Schwarz against the constant one -/

/-- A nonnegative quadratic in the free parameter bounds the discriminant. -/
theorem sq_le_of_quadratic_nonneg {m A B : ℝ} (hm : 0 ≤ m)
    (hzero : m = 0 → A = 0)
    (h : ∀ c : ℝ, 0 ≤ m * c ^ 2 - 2 * c * A + B) : A ^ 2 ≤ m * B := by
  rcases eq_or_lt_of_le hm with hm0 | hmpos
  · have hA : A = 0 := hzero hm0.symm
    rw [hA, ← hm0]
    have := h 0
    simp at this
    nlinarith [this]
  · have hc := h (A / m)
    have hmne : m ≠ 0 := ne_of_gt hmpos
    have hexp : m * (A / m) ^ 2 - 2 * (A / m) * A + B = B - A ^ 2 / m := by
      field_simp
      ring
    rw [hexp] at hc
    have : A ^ 2 / m ≤ B := by linarith
    rw [div_le_iff₀ hmpos] at this
    linarith

/-- **Cauchy--Schwarz against the constant one on a set of finite measure.** -/
theorem sq_setIntegral_le_measureReal_mul {ν : Measure ℝ} {E : Set ℝ} {f : ℝ → ℝ}
    (hE : MeasurableSet E) (hfin : ν E ≠ ⊤)
    (hf : IntegrableOn f E ν) (hf2 : IntegrableOn (fun t => f t ^ 2) E ν) :
    (∫ t in E, f t ∂ν) ^ 2 ≤ ν.real E * ∫ t in E, f t ^ 2 ∂ν := by
  haveI hfinm : IsFiniteMeasure (ν.restrict E) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr hfin
  set A : ℝ := ∫ t in E, f t ∂ν with hA
  set B : ℝ := ∫ t in E, f t ^ 2 ∂ν with hB
  set m : ℝ := ν.real E with hm
  have hmnn : 0 ≤ m := by
    rw [hm]
    exact ENNReal.toReal_nonneg
  have hquad : ∀ c : ℝ, 0 ≤ m * c ^ 2 - 2 * c * A + B := by
    intro c
    have hnn : 0 ≤ ∫ t in E, (f t - c) ^ 2 ∂ν :=
      setIntegral_nonneg hE fun t _ => sq_nonneg _
    have hexp : ∫ t in E, (f t - c) ^ 2 ∂ν = B - 2 * c * A + m * c ^ 2 := by
      have hcongr : ∀ t : ℝ, (f t - c) ^ 2 = f t ^ 2 - 2 * c * f t + c ^ 2 := by
        intro t; ring
      have hi0 : IntegrableOn (fun t : ℝ => 2 * c * f t) E ν := hf.const_mul (2 * c)
      have hi1 : IntegrableOn (fun t : ℝ => f t ^ 2 - 2 * c * f t) E ν := hf2.sub hi0
      have hi2 : IntegrableOn (fun _ : ℝ => c ^ 2) E ν := integrable_const _
      rw [setIntegral_congr_fun hE (fun t _ => hcongr t)]
      rw [integral_add hi1 hi2, integral_sub hf2 hi0, MeasureTheory.integral_const_mul,
        setIntegral_const]
      rw [hA, hB, hm, Measure.real, smul_eq_mul]
    rw [hexp] at hnn
    linarith
  have hzero : m = 0 → A = 0 := by
    intro h0
    have hnull : ν E = 0 := by
      rw [hm, Measure.real] at h0
      exact (ENNReal.toReal_eq_zero_iff _).mp h0 |>.resolve_right hfin
    rw [hA, Measure.restrict_eq_zero.mpr hnull]
    simp
  exact sq_le_of_quadratic_nonneg hmnn hzero hquad

end GaloisForLFunctions.RHTower
