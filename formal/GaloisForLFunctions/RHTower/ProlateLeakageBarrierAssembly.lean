import GaloisForLFunctions.RHTower.ProlateLeakageUpperScalar
import GaloisForLFunctions.RHTower.BandBarrierRatio

/-!
# The leakage upper bound driven by the barrier ratio

The three sharp inputs of the leakage estimate — exterior mass from above, interior mass from below,
and the barrier ratio — combine by pure scalar algebra.  Writing the interior mass lower bound in the
shape `mass_lower_of_fluxBound` produces, `w · (Phi(y₀) e^(−E))²`, and the barrier ratio in the shape
`prolateBand_barrier_ratio_lower` produces, `e^A / Dnm ≤ Phi(y₀)`, one gets

```text
leakage ≤ (C/c) · (Dnm² e^(2E) / w) · e^(−2A) .
```

With `A = c·Xi_s(y₀) + 6 log((1−α)/(1−y₀))` and `Dnm = 6π sqrt(c·Xi_s(α))` this is
`C' · c · e^(−2c·Xi_s(y₀))`, and `Xi_s(√s)` is the sharp action.  The `c` in front is the entire
overhead, it does not depend on the mode index, and it cancels in the ladder ratio.
-/

noncomputable section

open Set MeasureTheory

namespace GaloisForLFunctions.RHTower

section

variable {c w E Φy₀ Dnm A U leakage : ℝ}

/-- **The scalar substitution.**  A lower bound on the mode at the interior anchor converts a
`U/(c·L)` leakage bound into an explicit exponential. -/
theorem leakage_le_of_anchor_lower (hc : 0 < c) (hw : 0 < w) (hDnm : 0 < Dnm)
    (hratio : Real.exp A / Dnm ≤ Φy₀) (hU : 0 ≤ U)
    (hleak : leakage ≤ U / c / (w * (Φy₀ * Real.exp (-E)) ^ (2 : ℕ))) :
    leakage ≤ U / c * (Dnm ^ (2 : ℕ) * Real.exp (2 * E) / w) * Real.exp (-(2 * A)) := by
  have hApos : (0 : ℝ) < Real.exp A / Dnm := by positivity
  have hΦ : 0 < Φy₀ := lt_of_lt_of_le hApos hratio
  have hEexp : (0 : ℝ) < Real.exp (-E) := Real.exp_pos _
  have hsq : (Real.exp A / Dnm * Real.exp (-E)) ^ (2 : ℕ) ≤ (Φy₀ * Real.exp (-E)) ^ (2 : ℕ) := by
    have h1 : Real.exp A / Dnm * Real.exp (-E) ≤ Φy₀ * Real.exp (-E) :=
      mul_le_mul_of_nonneg_right hratio hEexp.le
    nlinarith [h1, mul_pos hApos hEexp]
  have hLlow : w * (Real.exp A / Dnm * Real.exp (-E)) ^ (2 : ℕ) ≤ w * (Φy₀ * Real.exp (-E)) ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left hsq hw.le
  have hLpos : (0 : ℝ) < w * (Real.exp A / Dnm * Real.exp (-E)) ^ (2 : ℕ) := by positivity
  have hstep : U / c / (w * (Φy₀ * Real.exp (-E)) ^ (2 : ℕ))
      ≤ U / c / (w * (Real.exp A / Dnm * Real.exp (-E)) ^ (2 : ℕ)) := by
    refine div_le_div_of_nonneg_left (by positivity) hLpos hLlow
  refine le_trans hleak (le_trans hstep (le_of_eq ?_))
  have hexpA : Real.exp A ≠ 0 := (Real.exp_pos A).ne'
  have hexpE : Real.exp (-E) ≠ 0 := (Real.exp_pos (-E)).ne'
  have hsq2 : (Real.exp A / Dnm * Real.exp (-E)) ^ (2 : ℕ)
      = Real.exp (2 * A) * Real.exp (-(2 * E)) / Dnm ^ (2 : ℕ) := by
    rw [mul_pow, div_pow]
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    push_cast
    field_simp
  rw [hsq2]
  have hE2 : Real.exp (-(2 * E)) = 1 / Real.exp (2 * E) := by
    rw [Real.exp_neg]
    field_simp
  have hA2 : Real.exp (-(2 * A)) = 1 / Real.exp (2 * A) := by
    rw [Real.exp_neg]
    field_simp
  rw [hE2, hA2]
  have h1 : (0 : ℝ) < Real.exp (2 * A) := Real.exp_pos _
  have h2 : (0 : ℝ) < Real.exp (2 * E) := Real.exp_pos _
  field_simp

/-- **The leakage bound for an actual radial prolate mode, driven by the barrier ratio.** -/
theorem prolate_leakage_le_of_barrier {s : ℝ} {R DR DDR : ℝ → ℝ} {inside value : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 5 ≤ c)
    (hR1 : R 1 = 1) (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hw : 0 < w) (hDnm : 0 < Dnm) (hratio : Real.exp A / Dnm ≤ Φy₀)
    (hin : w * (Φy₀ * Real.exp (-E)) ^ (2 : ℕ) ≤ inside)
    (hvalue : value ^ (2 : ℕ) ≤ 1) (hv : value ≠ 0) (hleak : 0 ≤ leakage)
    (hmass : (∫ x in Ioi (1 : ℝ), R x ^ (2 : ℕ)) = inside * leakage / value ^ (2 : ℕ)) :
    leakage ≤ radialProlateExteriorMassConstant / c
      * (Dnm ^ (2 : ℕ) * Real.exp (2 * E) / w) * Real.exp (-(2 * A)) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc
  have hApos : (0 : ℝ) < Real.exp A / Dnm := by positivity
  have hΦ : 0 < Φy₀ := lt_of_lt_of_le hApos hratio
  have hLpos : (0 : ℝ) < w * (Φy₀ * Real.exp (-E)) ^ (2 : ℕ) := by positivity
  have hbase := leakage_upper_of_prolate_masses (s := s) (c := c) (R := R) (DR := DR) (DDR := DDR)
    (inside := inside) (value := value) (leakage := leakage)
    (L := w * (Φy₀ * Real.exp (-E)) ^ (2 : ℕ)) hs0 hs1 hc hR1 hR hDR hode hLpos hin hvalue hv hleak hmass
  exact leakage_le_of_anchor_lower hc0 hw hDnm hratio
    radialProlateExteriorMassConstant_nonneg hbase

/-- **The leakage upper bound at the sharp action.**  Every factor is explicit: the exterior mass
constant, the interior-mass width and flux loss, the endpoint envelope `6π sqrt(c Xi(α))`, and the
sharp exponent `c Xi_s(y₀)`. -/
theorem prolate_leakage_le_exp_action {s α y₀ : ℝ} {Φ R DR DDR : ℝ → ℝ} {inside value : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hc : 5 ≤ c)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hcollar : 600 * (1 - α) ≤ 1 / 4)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, _root_.RHTower.prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1)
    (hy0 : 0 ≤ y₀) (hy0α : y₀ ≤ α) (hsy0 : s < y₀ ^ (2 : ℕ))
    (hposΦ : ∀ t ∈ Icc y₀ 1, 0 < Φ t)
    (hz : 1 ≤ c * bandEndpointPhase s α)
    (hR1 : R 1 = 1) (hR : ∀ t : ℝ, HasDerivAt R (DR t) t)
    (hDR : ∀ t : ℝ, HasDerivAt DR (DDR t) t)
    (hode : ∀ t : ℝ, (t ^ (2 : ℕ) - 1) * DDR t + 2 * t * DR t
      - (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * t ^ (2 : ℕ)) * R t = 0)
    (hw : 0 < w)
    (hin : w * (Φ y₀ * Real.exp (-E)) ^ (2 : ℕ) ≤ inside)
    (hvalue : value ^ (2 : ℕ) ≤ 1) (hv : value ≠ 0) (hleak : 0 ≤ leakage)
    (hmass : (∫ x in Ioi (1 : ℝ), R x ^ (2 : ℕ)) = inside * leakage / value ^ (2 : ℕ)) :
    leakage ≤ radialProlateExteriorMassConstant / c
      * ((6 * Real.pi * Real.sqrt (c * bandEndpointPhase s α)) ^ (2 : ℕ) * Real.exp (2 * E) / w)
      * Real.exp (-(2 * (c * bandEndpointPhase s y₀
          + 6 * (Real.log (1 - α) - Real.log (1 - y₀))))) := by
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le (by norm_num) hc
  have hDnm : (0 : ℝ) < 6 * Real.pi * Real.sqrt (c * bandEndpointPhase s α) := by
    have h1 : (0 : ℝ) < Real.sqrt (c * bandEndpointPhase s α) :=
      Real.sqrt_pos.2 (by linarith)
    have := Real.pi_pos
    positivity
  have hratio := prolateBand_barrier_ratio_lower (s := s) (c := c) (α := α) (y₀ := y₀) (Φ := Φ)
    hs0 hs1 hc0 hα hα1 hcollar hsm heig hΦ1 hy0 hy0α hsy0 hposΦ hz
  exact prolate_leakage_le_of_barrier (s := s) (R := R) (DR := DR) (DDR := DDR)
    (inside := inside) (value := value) hs0 (by linarith) hc hR1 hR hDR hode hw hDnm hratio
    hin hvalue hv hleak hmass

end

end GaloisForLFunctions.RHTower

end
