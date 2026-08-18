import GaloisForLFunctions.HTGeometry.ObserverComplementOrderParameter

/-!
# The capacity-normalized accessibility amplification

Dividing the first-entrance reporter by its own capacity scale produces a dimensionless density:
non-negative, of unit `π`-mass, equal to `(1−a)/cap` on the target, obeying Markov's inequality on
its super-level sets, and with a logarithm sandwiched by the robust word complexity through the
first-entrance path bounds.  Reweighting `π` by it gives the accessibility likelihood, whose target
mass is `(1−a)π(A)/cap` and therefore lies between `1−a` and one.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Accessibility

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **`(11r)`.**  The capacity-normalized accessibility amplification. -/
def accessAmp (a cap : ℝ) (h : X → ℝ) : X → ℝ := fun x => (1 - a) * h x / cap

theorem accessAmp_nonneg {a cap : ℝ} {h : X → ℝ} (ha1 : a < 1) (hcap : 0 < cap)
    (hh : ∀ x, 0 ≤ h x) (x : X) : 0 ≤ accessAmp a cap h x := by
  rw [accessAmp]
  have h1 : (0 : ℝ) ≤ 1 - a := by linarith
  exact div_nonneg (mul_nonneg h1 (hh x)) hcap.le

/-- **`(11s)`, unit mass.**  With the capacity normalized as `(1−a)∫h dπ`, the amplification has
unit `π`-mass. -/
theorem sum_pi_accessAmp {a cap : ℝ} {h pi : X → ℝ} (hcap : 0 < cap)
    (hnorm : cap = (1 - a) * ∑ x, pi x * h x) :
    (∑ x, pi x * accessAmp a cap h x) = 1 := by
  have hstep : ∀ x : X, pi x * accessAmp a cap h x = (1 - a) * (pi x * h x) / cap := by
    intro x
    rw [accessAmp]
    ring
  rw [Finset.sum_congr rfl fun x _ => hstep x, ← Finset.sum_div, ← Finset.mul_sum, ← hnorm,
    div_self (ne_of_gt hcap)]

/-- **`(11s)`, boundary value.**  On the target the amplification is `(1−a)/cap`. -/
theorem accessAmp_of_mem {a cap : ℝ} {h : X → ℝ} {x : X} (hx : h x = 1) :
    accessAmp a cap h x = (1 - a) / cap := by
  rw [accessAmp, hx, mul_one]

/-- **`(11w)`.**  Markov's inequality for the amplification. -/
theorem measure_accessAmp_ge_le {a cap z : ℝ} {h pi : X → ℝ} (hz : 0 < z) (hcap : 0 < cap)
    (ha1 : a < 1) (hh : ∀ x, 0 ≤ h x) (hpi : ∀ x, 0 ≤ pi x)
    (hnorm : cap = (1 - a) * ∑ x, pi x * h x) :
    (∑ x ∈ Finset.univ.filter fun x => z ≤ accessAmp a cap h x, pi x) ≤ z⁻¹ := by
  classical
  have hmass := sum_pi_accessAmp (pi := pi) hcap hnorm
  have hlow : (∑ x ∈ Finset.univ.filter fun x => z ≤ accessAmp a cap h x, pi x * z)
      ≤ ∑ x ∈ Finset.univ.filter fun x => z ≤ accessAmp a cap h x,
          pi x * accessAmp a cap h x := by
    refine Finset.sum_le_sum fun x hx => ?_
    exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hx).2 (hpi x)
  have hall : (∑ x ∈ Finset.univ.filter fun x => z ≤ accessAmp a cap h x,
      pi x * accessAmp a cap h x) ≤ ∑ x, pi x * accessAmp a cap h x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun x _ _ => mul_nonneg (hpi x) (accessAmp_nonneg ha1 hcap hh x)
  rw [← Finset.sum_mul] at hlow
  have hchain : (∑ x ∈ Finset.univ.filter fun x => z ≤ accessAmp a cap h x, pi x) * z ≤ 1 := by
    calc (∑ x ∈ Finset.univ.filter fun x => z ≤ accessAmp a cap h x, pi x) * z
        ≤ ∑ x ∈ Finset.univ.filter fun x => z ≤ accessAmp a cap h x,
            pi x * accessAmp a cap h x := hlow
      _ ≤ ∑ x, pi x * accessAmp a cap h x := hall
      _ = 1 := hmass
  rw [← le_div_iff₀ hz, one_div] at hchain
  exact hchain

/-- **`(11v)`.**  The logarithm of the amplification is sandwiched by the robust word
complexity. -/
theorem complexity_sandwich {a M cap amp : ℝ} {C : ℕ}
    (ha : 0 < a) (ha1 : a < 1) (haM : a < M) (hcap : 0 < cap) (hamp : 0 < amp)
    (hlow : (a / M) ^ C ≤ cap * amp / (1 - a))
    (hup : cap * amp / (1 - a) ≤ a ^ C) :
    Real.log ((1 - a) / (cap * amp)) / Real.log (M / a) ≤ (C : ℝ) ∧
      (C : ℝ) ≤ Real.log ((1 - a) / (cap * amp)) / Real.log (1 / a) := by
  have hden : (0 : ℝ) < 1 - a := by linarith
  have hM0 : (0 : ℝ) < M := lt_trans ha haM
  have hu : (0 : ℝ) < cap * amp / (1 - a) := by positivity
  have hlogu : Real.log ((1 - a) / (cap * amp)) = -Real.log (cap * amp / (1 - a)) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  have hMa : (1 : ℝ) < M / a := (one_lt_div ha).mpr haM
  have hlogMa : 0 < Real.log (M / a) := Real.log_pos hMa
  have hinva : (1 : ℝ) < 1 / a := (one_lt_div ha).mpr ha1
  have hloginva : 0 < Real.log (1 / a) := Real.log_pos hinva
  constructor
  · have hlog : (C : ℝ) * Real.log (a / M) ≤ Real.log (cap * amp / (1 - a)) := by
      have := Real.log_le_log (by positivity) hlow
      rwa [Real.log_pow] at this
    have hrel : Real.log (a / M) = -Real.log (M / a) := by
      rw [Real.log_div (ne_of_gt ha) (ne_of_gt hM0), Real.log_div (ne_of_gt hM0) (ne_of_gt ha)]
      ring
    rw [hrel] at hlog
    rw [hlogu, div_le_iff₀ hlogMa]
    linarith
  · have hlog : Real.log (cap * amp / (1 - a)) ≤ (C : ℝ) * Real.log a := by
      have := Real.log_le_log hu hup
      rwa [Real.log_pow] at this
    have hrel : Real.log a = -Real.log (1 / a) := by
      rw [Real.log_div one_ne_zero (ne_of_gt ha), Real.log_one]
      ring
    rw [hrel] at hlog
    rw [hlogu, le_div_iff₀ hloginva]
    linarith

/-- **`(11y)`, `(11z)`.**  The accessibility likelihood of the target is `(1−a)π(A)/cap`, hence
between `1−a` and one. -/
theorem accessLikelihood_target {a cap : ℝ} {h pi : X → ℝ} (A : Finset X)
    (hA : ∀ x ∈ A, h x = 1) :
    (∑ x ∈ A, pi x * accessAmp a cap h x) = (1 - a) * (∑ x ∈ A, pi x) / cap := by
  have hstep : ∀ x ∈ A, pi x * accessAmp a cap h x = (1 - a) * pi x / cap := by
    intro x hx
    rw [accessAmp, hA x hx, mul_one]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_div, ← Finset.mul_sum]

theorem accessLikelihood_target_mem_Icc {a cap : ℝ} {pi : X → ℝ} (A : Finset X)
    (hcap : 0 < cap) (ha1 : a < 1)
    (hcaple : cap ≤ ∑ x ∈ A, pi x) (hlow : (1 - a) * (∑ x ∈ A, pi x) ≤ cap) :
    1 - a ≤ (1 - a) * (∑ x ∈ A, pi x) / cap ∧
      (1 - a) * (∑ x ∈ A, pi x) / cap ≤ 1 := by
  have hden : (0 : ℝ) < 1 - a := by linarith
  constructor
  · rw [le_div_iff₀ hcap]
    nlinarith [hcaple, hden]
  · rw [div_le_one hcap]
    exact hlow

end Accessibility

end

end GaloisForLFunctions.HTGeometry
