import GaloisForLFunctions.RHTower.ProlateJointEigenExistence
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The prolate endpoint cannot be exponentially small in an uncontrolled way

The prolate equation in Sturm–Liouville form is

```text
((1-y²) psi')' = (chi + c² y²) psi,
```

and the flux `(1-y²) psi'` vanishes at `y = 1` because the weight does.  Integrating the equation from
`y` to the endpoint therefore gives an exact representation of the flux,

```text
(1-y²) psi'(y) = -∫_y^1 (chi + c² t²) psi(t) dt,
```

with two consequences beyond the turning point (where `chi + c² y² >= 0`) for a positive solution:
the flux is nonpositive, so `psi` is *decreasing*; and bounding the integrand by its value at the left
endpoint gives the differential inequality

```text
(1 + y) psi'(y) >= -(chi + c²) psi(y),
```

whose integrating factor is the pure power `(1+y)^(chi+c²)`.  Hence

```text
psi(1) >= psi(y₀) · ((1+y₀)/2)^(chi + c²) :
```

**a positive prolate solution has an explicit lower bound at the endpoint** — the singular endpoint of
the equation cannot swallow the solution faster than that power.  This is the elementary form of the
endpoint control that the sharp Fuchs asymptotic refines; the mechanism (flux representation, monotonicity
beyond the turning point, integrating factor) is exactly the one a WKB estimate sharpens.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral

open _root_.RHTower

/-! ## The Sturm–Liouville flux -/

/-- The Sturm–Liouville flux of the prolate problem. -/
def prolateFlux (Φ : ℝ → ℝ) (y : ℝ) : ℝ := (1 - y ^ 2) * deriv Φ y

theorem prolateFlux_one (Φ : ℝ → ℝ) : prolateFlux Φ 1 = 0 := by
  rw [prolateFlux]
  norm_num

/-- On the band the flux differentiates to the right-hand side of the prolate equation. -/
theorem hasDerivAt_prolateFlux {c χ : ℝ} {Φ : ℝ → ℝ} (hd2 : Differentiable ℝ (deriv Φ))
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y) {y : ℝ}
    (hy : y ∈ Icc (-1 : ℝ) 1) :
    HasDerivAt (prolateFlux Φ) ((χ + c ^ 2 * y ^ 2) * Φ y) y := by
  have hbase := _root_.RHTower.hasDerivAt_bandFlux (f := Φ) (t := y) (hd2 y)
  have h := heig y hy
  rw [prolateSLAction] at h
  refine hbase.congr_deriv ?_
  linear_combination h

/-- **The flux representation.**  Integrating the equation from `y` to the singular endpoint, where the
flux vanishes. -/
theorem prolateFlux_eq_neg_integral {c χ : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y) {y : ℝ}
    (hy : y ∈ Icc (-1 : ℝ) 1) :
    prolateFlux Φ y = -∫ t in y..1, (χ + c ^ 2 * t ^ 2) * Φ t := by
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hd2 : Differentiable ℝ (deriv Φ) :=
    (contDiff_infty_iff_deriv.mp ((contDiff_infty_iff_deriv.mp hsm).2)).1
  have hsub : uIcc y 1 ⊆ Icc (-1 : ℝ) 1 := by
    rw [Set.uIcc_of_le hy.2]
    intro t ht
    exact ⟨le_trans hy.1 ht.1, ht.2⟩
  have hderiv : ∀ t ∈ uIcc y 1, HasDerivAt (prolateFlux Φ) ((χ + c ^ 2 * t ^ 2) * Φ t) t :=
    fun t ht => hasDerivAt_prolateFlux hd2 heig (hsub ht)
  have hint : IntervalIntegrable (fun t => (χ + c ^ 2 * t ^ 2) * Φ t) volume y 1 := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.add (continuous_const.mul (continuous_id.pow 2))).mul hd1.continuous
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [prolateFlux_one] at hFTC
  linarith [hFTC]

/-! ## Monotonicity beyond the turning point -/

/-- Beyond the turning point a positive solution has nonpositive flux, hence is decreasing. -/
theorem deriv_nonpos_of_turning {c χ y₀ : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    (hy₀ : -1 < y₀) (hpos : ∀ t ∈ Icc y₀ 1, 0 ≤ Φ t)
    (hturn : ∀ t ∈ Icc y₀ 1, 0 ≤ χ + c ^ 2 * t ^ 2) {y : ℝ} (hy : y ∈ Ico y₀ 1) :
    deriv Φ y ≤ 0 := by
  have hyband : y ∈ Icc (-1 : ℝ) 1 := ⟨le_of_lt (lt_of_lt_of_le hy₀ hy.1), le_of_lt hy.2⟩
  have hrep := prolateFlux_eq_neg_integral hsm heig hyband
  have hnonneg : 0 ≤ ∫ t in y..1, (χ + c ^ 2 * t ^ 2) * Φ t := by
    refine intervalIntegral.integral_nonneg (le_of_lt hy.2) fun t ht => ?_
    have htmem : t ∈ Icc y₀ 1 := ⟨le_trans hy.1 ht.1, ht.2⟩
    exact mul_nonneg (hturn t htmem) (hpos t htmem)
  have hfluxle : prolateFlux Φ y ≤ 0 := by
    rw [hrep]
    linarith
  have hwpos : 0 < 1 - y ^ 2 := by
    have h1 : -1 < y := lt_of_lt_of_le hy₀ hy.1
    have h2 : y < 1 := hy.2
    nlinarith
  rw [prolateFlux] at hfluxle
  exact nonpos_of_mul_nonpos_right hfluxle hwpos

/-! ## The endpoint lower bound -/

/-- **The prolate endpoint lower bound.**  Beyond the turning point a positive solution decays at most
like the power `((1+y)/2)^(chi + c²)`. -/
theorem endpoint_lower_bound {c χ y₀ : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    (hy₀ : -1 < y₀) (hy₁ : y₀ < 1)
    (hpos : ∀ t ∈ Icc y₀ 1, 0 ≤ Φ t)
    (hturn : ∀ t ∈ Icc y₀ 1, 0 ≤ χ + c ^ 2 * t ^ 2)
    (hA : 0 ≤ χ + c ^ 2) :
    Φ y₀ * ((1 + y₀) / 2) ^ (χ + c ^ 2) ≤ Φ 1 := by
  set A : ℝ := χ + c ^ 2 with hAdef
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hy₀pos : 0 < 1 + y₀ := by linarith
  -- the solution is decreasing beyond the turning point
  have hderivnonpos : ∀ y ∈ Ico y₀ 1, deriv Φ y ≤ 0 := fun y hy =>
    deriv_nonpos_of_turning hsm heig hy₀ hpos hturn hy
  have hanti : AntitoneOn Φ (Icc y₀ 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hd1.continuous.continuousOn
      hd1.differentiableOn fun y hy => ?_
    rw [interior_Icc] at hy
    exact hderivnonpos y ⟨le_of_lt hy.1, hy.2⟩
  -- the differential inequality with the pure-power integrating factor
  have hdiff : ∀ y ∈ Ioo y₀ 1, -(A * Φ y) ≤ (1 + y) * deriv Φ y := by
    intro y hy
    have hyband : y ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hy.1], le_of_lt hy.2⟩
    have hymem : y ∈ Icc y₀ 1 := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have hrep := prolateFlux_eq_neg_integral hsm heig hyband
    -- the integrand is dominated by its value at the left endpoint
    have hbound : (∫ t in y..1, (χ + c ^ 2 * t ^ 2) * Φ t) ≤ ∫ _t in y..1, A * Φ y := by
      refine intervalIntegral.integral_mono_on (le_of_lt hy.2) ?_ ?_ fun t ht => ?_
      · apply Continuous.intervalIntegrable
        exact (continuous_const.add (continuous_const.mul (continuous_id.pow 2))).mul
          hd1.continuous
      · exact intervalIntegrable_const
      · have htmem : t ∈ Icc y₀ 1 := ⟨le_trans (le_of_lt hy.1) ht.1, ht.2⟩
        have htsq : χ + c ^ 2 * t ^ 2 ≤ A := by
          have h1 : t ^ 2 ≤ 1 := by
            have h2 : -1 ≤ t := by linarith [htmem.1]
            have h3 : t ≤ 1 := htmem.2
            nlinarith
          have h4 : (0 : ℝ) ≤ c ^ 2 := by positivity
          rw [hAdef]
          nlinarith
        have hΦle : Φ t ≤ Φ y := hanti hymem htmem ht.1
        have hΦnn : 0 ≤ Φ t := hpos t htmem
        have hnn : 0 ≤ χ + c ^ 2 * t ^ 2 := hturn t htmem
        calc (χ + c ^ 2 * t ^ 2) * Φ t ≤ A * Φ t := mul_le_mul_of_nonneg_right htsq hΦnn
          _ ≤ A * Φ y := mul_le_mul_of_nonneg_left hΦle hA
    have hconst : (∫ _t in y..1, A * Φ y) = (1 - y) * (A * Φ y) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [hconst] at hbound
    -- convert to the derivative inequality
    have hflux : (1 - y ^ 2) * deriv Φ y = -∫ t in y..1, (χ + c ^ 2 * t ^ 2) * Φ t := by
      rw [← prolateFlux]
      exact hrep
    have hylt : 0 < 1 - y := by linarith [hy.2]
    have hstep : -((1 - y) * (A * Φ y)) ≤ (1 - y ^ 2) * deriv Φ y := by
      rw [hflux]
      linarith
    have hfac : (1 - y ^ 2) = (1 - y) * (1 + y) := by ring
    rw [hfac] at hstep
    have hcancel : -(A * Φ y) ≤ (1 + y) * deriv Φ y := by
      have h := (mul_le_mul_iff_of_pos_left hylt).mp (by linarith [hstep] :
        (1 - y) * (-(A * Φ y)) ≤ (1 - y) * ((1 + y) * deriv Φ y))
      exact h
    exact hcancel
  -- the integrating factor is monotone
  set g : ℝ → ℝ := fun y => Φ y * (1 + y) ^ A with hg
  have hgderiv : ∀ y ∈ Ioo y₀ 1,
      HasDerivAt g (deriv Φ y * (1 + y) ^ A + Φ y * (A * (1 + y) ^ (A - 1))) y := by
    intro y hy
    have hbase : 0 < 1 + y := by linarith [hy.1]
    have hpow : HasDerivAt (fun t : ℝ => (1 + t) ^ A) (A * (1 + y) ^ (A - 1)) y := by
      have hinner : HasDerivAt (fun t : ℝ => 1 + t) 1 y := by
        simpa using (hasDerivAt_id y).const_add (1 : ℝ)
      have hpow0 := hinner.rpow_const (p := A) (Or.inl (ne_of_gt hbase))
      rw [one_mul] at hpow0
      exact hpow0
    exact (hd1 y).hasDerivAt.mul hpow
  have hgmono : MonotoneOn g (Icc y₀ 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ fun y hy => ?_
    · -- continuity of the integrating factor on the band
      have hcont : ContinuousOn (fun y : ℝ => (1 + y) ^ A) (Icc y₀ 1) := by
        refine ContinuousOn.rpow_const (by fun_prop) fun y hy => ?_
        left
        have : 0 < 1 + y := by linarith [hy.1]
        exact ne_of_gt this
      exact hd1.continuous.continuousOn.mul hcont
    · rw [interior_Icc]
      exact fun y hy => (hgderiv y hy).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at hy
      rw [(hgderiv y hy).deriv]
      -- the derivative is nonnegative by the differential inequality
      have hbase : 0 < 1 + y := by linarith [hy.1]
      have hkey := hdiff y hy
      have hpowpos : 0 < (1 + y) ^ (A - 1) := Real.rpow_pos_of_pos hbase _
      have hsplit : (1 + y) ^ A = (1 + y) ^ (A - 1) * (1 + y) := by
        have h := Real.rpow_add hbase (A - 1) 1
        rw [Real.rpow_one] at h
        have hAA : A - 1 + 1 = A := by ring
        rw [hAA] at h
        exact h
      calc (0 : ℝ) ≤ (1 + y) ^ (A - 1) * ((1 + y) * deriv Φ y + A * Φ y) := by
            have : 0 ≤ (1 + y) * deriv Φ y + A * Φ y := by linarith [hkey]
            exact mul_nonneg (le_of_lt hpowpos) this
        _ = deriv Φ y * (1 + y) ^ A + Φ y * (A * (1 + y) ^ (A - 1)) := by
            rw [hsplit]
            ring
  -- compare the endpoints
  have hcmp : Φ y₀ * (1 + y₀) ^ A ≤ Φ 1 * (2 : ℝ) ^ A := by
    have h : g y₀ ≤ g 1 := hgmono (left_mem_Icc.mpr (le_of_lt hy₁))
      (right_mem_Icc.mpr (le_of_lt hy₁)) (le_of_lt hy₁)
    have hgy₀ : g y₀ = Φ y₀ * (1 + y₀) ^ A := rfl
    have hg1 : g 1 = Φ 1 * (2 : ℝ) ^ A := by
      rw [hg]
      norm_num
    rw [hgy₀, hg1] at h
    exact h
  -- divide by `2 ^ A`
  have hpow2 : (0 : ℝ) < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) _
  have hdivpow : ((1 + y₀) / 2) ^ A = (1 + y₀) ^ A / (2 : ℝ) ^ A :=
    Real.div_rpow (le_of_lt hy₀pos) (by norm_num) A
  rw [hdivpow, ← mul_div_assoc, div_le_iff₀ hpow2]
  exact hcmp

end GaloisForLFunctions.RHTower

end
