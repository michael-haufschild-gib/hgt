import GaloisForLFunctions.RHTower.BandSolutionComparison
import GaloisForLFunctions.RHTower.BesselIZeroLowerBound
import GaloisForLFunctions.RHTower.ProlateEndpointUpperBound
import GaloisForLFunctions.RHTower.FuchsProlateScale

/-!
# The barrier ratio of the prolate band, at the sharp exponential rate

The two halves of the band now join.  On the endpoint collar the mode is trapped by `I₀(cΞ)`, whose
own lower bound is `e^z/(2π√z)`; below the collar the Riccati comparison transports at the WKB rate
with a loss that is now an absolute constant, because the collar has fixed width.  The phase itself
is additive,

```text
Ξ_s(a) - Ξ_s(b) = ∫_a^b sqrt((t²-s)/(1-t²)) dt ,
```

so the two exponents concatenate exactly, and the result is

```text
Phi(y₀)  ≥  exp( c·Ξ_s(y₀) + 6 log((1-α)/(1-y₀)) ) / (6π sqrt(c·Ξ_s(α)))
```

for a mode normalised by `Phi(1) = 1`.  Since `Ξ_s(√s) = prolateAngleAction s` by definition, this
is the sharp action `c·A(s)` with an overhead of `sqrt c` and absolute constants — no power of `c`
beyond `1/2`, and none at all depending on the mode index.
-/

noncomputable section

open Set

open _root_.RHTower

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

section

variable {s c α y₀ : ℝ} {Φ : ℝ → ℝ}

/-- **The phase is additive.**  Its increment is the WKB profile integral. -/
theorem bandEndpointPhase_sub_eq_integral {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1)
    (hsa : s ≤ a ^ 2) :
    bandEndpointPhase s a - bandEndpointPhase s b = ∫ t in a..b, prolateWKBProfile s t := by
  have hsub : uIcc a b ⊆ Icc a b := by
    rw [uIcc_of_le hab]
  have hmem : ∀ t ∈ uIcc a b, -1 < t ∧ t < 1 ∧ s ≤ t ^ 2 := by
    intro t ht
    have ht' := hsub ht
    have h1 : a ≤ t := ht'.1
    have h2 : t ≤ b := ht'.2
    refine ⟨by linarith, by linarith, ?_⟩
    nlinarith [hsa, ha, h1]
  have hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (bandEndpointPhase s) (-(prolateWKBProfile s t)) t := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hmem t ht
    exact hasDerivAt_bandEndpointPhase h1 h2 h3
  have hsubIoo : uIcc a b ⊆ Ioo (-1 : ℝ) 1 := fun u hu => ⟨(hmem u hu).1, (hmem u hu).2.1⟩
  have hcont : ContinuousOn (fun t : ℝ => -(prolateWKBProfile s t)) (uIcc a b) :=
    ((continuousOn_prolateWKBProfile_Ioo s).mono hsubIoo).neg
  have hint : IntervalIntegrable (fun t : ℝ => -(prolateWKBProfile s t))
      MeasureTheory.volume a b := hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hneg : (∫ t in a..b, -(prolateWKBProfile s t))
      = -∫ t in a..b, prolateWKBProfile s t := intervalIntegral.integral_neg
  rw [hneg] at hFTC
  linarith [hFTC]

/-- **The phase at the turning point is the sharp action.**  The two are the same angular integral. -/
theorem bandEndpointPhase_sqrt_eq_prolateAngleAction (s : ℝ) :
    bandEndpointPhase s (Real.sqrt s) = prolateAngleAction s := rfl

/-- **The mode at the collar edge, from below.**  The trapping by `I₀` and the `I₀` lower bound
combine into an explicit exponential. -/
theorem exp_div_le_prolateBand_collar (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hc : 0 < c)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hcollar : 600 * (1 - α) ≤ 1 / 4)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hode : ∀ x ∈ Ioo α 1,
      (1 - x ^ 2) * deriv (deriv Φ) x - 2 * x * deriv Φ x
        + (s * c ^ 2 - c ^ 2 * x ^ 2) * Φ x = 0)
    (hΦ1 : Φ 1 = 1)
    (hz : 1 ≤ c * bandEndpointPhase s α) :
    Real.exp (c * bandEndpointPhase s α)
        / (6 * Real.pi * Real.sqrt (c * bandEndpointPhase s α)) ≤ Φ α := by
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hd2 : Differentiable ℝ (deriv Φ) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hsm).2).1
  have hΦc : ContinuousOn Φ (Icc α 1) := hd1.continuous.continuousOn
  have hDΦc : ContinuousOn (deriv Φ) (Icc α 1) := hd2.continuous.continuousOn
  have hΦd : ∀ x ∈ Ioo α 1, HasDerivAt Φ (deriv Φ x) x := fun x _ => (hd1 x).hasDerivAt
  have hDΦd : ∀ x ∈ Ioo α 1, HasDerivAt (deriv Φ) (deriv (deriv Φ) x) x :=
    fun x _ => (hd2 x).hasDerivAt
  have hmain := prolateBand_le_and_le (s := s) (c := c) (Φ := Φ) (DΦ := deriv Φ)
    (DDΦ := deriv (deriv Φ)) hs0 hs1 hc hα hα1 hcollar hΦc hDΦc hΦd hDΦd hode hΦ1
    α ⟨le_rfl, hα1.le⟩
  have hI := exp_div_le_besselI0 hz
  have hV : bandModel s c α = besselI0 (c * bandEndpointPhase s α) := rfl
  have hpos : (0 : ℝ) < 6 * Real.pi * Real.sqrt (c * bandEndpointPhase s α) := by
    have h1 : (0 : ℝ) < Real.sqrt (c * bandEndpointPhase s α) :=
      Real.sqrt_pos.2 (by linarith)
    have := Real.pi_pos
    positivity
  rw [div_le_iff₀ hpos]
  have hstep : Real.exp (c * bandEndpointPhase s α)
      ≤ besselI0 (c * bandEndpointPhase s α)
        * (2 * Real.pi * Real.sqrt (c * bandEndpointPhase s α)) := by
    have h2 : (0 : ℝ) < 2 * Real.pi * Real.sqrt (c * bandEndpointPhase s α) := by
      have h1 : (0 : ℝ) < Real.sqrt (c * bandEndpointPhase s α) :=
        Real.sqrt_pos.2 (by linarith)
      have := Real.pi_pos
      positivity
    exact (div_le_iff₀ h2).mp hI
  have hlow : 1 / 3 * besselI0 (c * bandEndpointPhase s α) ≤ Φ α := by
    rw [← hV]
    exact hmain.1
  nlinarith [hstep, hlow, Real.sqrt_nonneg (c * bandEndpointPhase s α), Real.pi_pos]

/-- **The barrier ratio, from below at the sharp rate.**  The collar contributes `Ξ_s(α)` and the
Riccati transport contributes `Ξ_s(y₀) - Ξ_s(α)`; the two exponents concatenate exactly. -/
theorem prolateBand_barrier_ratio_lower (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 8) (hc : 0 < c)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hcollar : 600 * (1 - α) ≤ 1 / 4)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ 2) * Φ y)
    (hΦ1 : Φ 1 = 1)
    (hy0 : 0 ≤ y₀) (hy0α : y₀ ≤ α) (hsy0 : s < y₀ ^ 2)
    (hpos : ∀ t ∈ Icc y₀ 1, 0 < Φ t)
    (hz : 1 ≤ c * bandEndpointPhase s α) :
    Real.exp (c * bandEndpointPhase s y₀ + 6 * (Real.log (1 - α) - Real.log (1 - y₀)))
        / (6 * Real.pi * Real.sqrt (c * bandEndpointPhase s α)) ≤ Φ y₀ := by
  have hode : ∀ x ∈ Ioo α 1,
      (1 - x ^ 2) * deriv (deriv Φ) x - 2 * x * deriv Φ x
        + (s * c ^ 2 - c ^ 2 * x ^ 2) * Φ x = 0 := by
    intro x hx
    have hmem : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1, hα], hx.2.le⟩
    have h := heig x hmem
    rw [prolateSLAction] at h
    linarith [h]
  have hcollarBound := exp_div_le_prolateBand_collar hs0 hs1 hc hα hα1 hcollar hsm hode hΦ1 hz
  -- the Riccati transport below the collar
  have hcχ : 0 ≤ c ^ 2 + -(s * c ^ 2) := by nlinarith [sq_nonneg c, hs1, hs0]
  have hturn : ∀ t ∈ Icc y₀ 1, 0 ≤ -(s * c ^ 2) + c ^ 2 * t ^ 2 := by
    intro t ht
    have h1 : y₀ ≤ t := ht.1
    have hsq : y₀ ^ 2 ≤ t ^ 2 := by nlinarith [hy0, h1]
    nlinarith [mul_nonneg (sq_nonneg c) (by linarith : (0:ℝ) ≤ t ^ 2 - s)]
  have hQ0 : 0 < -(s * c ^ 2) + c ^ 2 * y₀ ^ 2 := by
    nlinarith [mul_pos (pow_pos hc 2) (sub_pos.2 hsy0)]
  have hstep := prolate_endpoint_le_log (Φ := Φ) (c := c) (χ := -(s * c ^ 2)) hsm heig hcχ
    hy0 hy0α hα1 hpos hturn hQ0
  -- identify the two integrals
  have hprof : (∫ t in y₀..α, prolateWKB c (-(s * c ^ 2)) t)
      = c * (bandEndpointPhase s y₀ - bandEndpointPhase s α) := by
    have hfun : (∫ t in y₀..α, prolateWKB c (-(s * c ^ 2)) t)
        = ∫ t in y₀..α, c * prolateWKBProfile s t := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      exact prolateWKB_eq_mul_profile hc.le
    rw [hfun, intervalIntegral.integral_const_mul,
      bandEndpointPhase_sub_eq_integral hy0 hy0α hα1 hsy0.le]
  have hlog := integral_six_div_one_sub (a := y₀) (b := α) hy0α hα1
  have hsplit : (∫ t in y₀..α, (prolateWKB c (-(s * c ^ 2)) t - 6 / (1 - t)))
      = (∫ t in y₀..α, prolateWKB c (-(s * c ^ 2)) t) - ∫ t in y₀..α, 6 / (1 - t) := by
    refine intervalIntegral.integral_sub ?_ ?_
    · refine ContinuousOn.intervalIntegrable ?_
      have hfun : prolateWKB c (-(s * c ^ 2))
          = fun t : ℝ => Real.sqrt ((-(s * c ^ 2) + c ^ 2 * t ^ 2) / (1 - t ^ 2)) := by
        funext t
        rw [prolateWKB]
      rw [hfun]
      refine Real.continuous_sqrt.comp_continuousOn
        (ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => ?_)
      have ht' : t ∈ Icc y₀ α := by rwa [uIcc_of_le hy0α] at ht
      have h1 : (0:ℝ) < 1 - t ^ 2 := by nlinarith [ht'.1, ht'.2, hy0, hα1]
      exact h1.ne'
    · refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => ?_
      have ht' : t ∈ Icc y₀ α := by rwa [uIcc_of_le hy0α] at ht
      have : (0 : ℝ) < 1 - t := by linarith [ht'.2, hα1]
      exact this.ne'
  -- assemble
  have hΦαpos : 0 < Φ α := hpos α ⟨hy0α, hα1.le⟩
  have hexp : Real.exp (-∫ t in y₀..α, (prolateWKB c (-(s * c ^ 2)) t - 6 / (1 - t)))
      = Real.exp (-(c * (bandEndpointPhase s y₀ - bandEndpointPhase s α))
        + 6 * (Real.log (1 - y₀) - Real.log (1 - α))) := by
    rw [hsplit, hprof, hlog]
    ring_nf
  rw [hexp] at hstep
  have hkey : Real.exp (c * bandEndpointPhase s y₀
        + 6 * (Real.log (1 - α) - Real.log (1 - y₀)))
      = Real.exp (c * bandEndpointPhase s α)
        * Real.exp (c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
          + 6 * (Real.log (1 - α) - Real.log (1 - y₀))) := by
    rw [← Real.exp_add]
    ring_nf
  have hEpos : (0 : ℝ) < Real.exp (c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
      + 6 * (Real.log (1 - α) - Real.log (1 - y₀))) := Real.exp_pos _
  have hden : (0 : ℝ) < 6 * Real.pi * Real.sqrt (c * bandEndpointPhase s α) := by
    have h1 : (0 : ℝ) < Real.sqrt (c * bandEndpointPhase s α) :=
      Real.sqrt_pos.2 (by linarith)
    have := Real.pi_pos
    positivity
  have hinv : Real.exp (-(c * (bandEndpointPhase s y₀ - bandEndpointPhase s α))
        + 6 * (Real.log (1 - y₀) - Real.log (1 - α)))
      * Real.exp (c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
        + 6 * (Real.log (1 - α) - Real.log (1 - y₀))) = 1 := by
    rw [← Real.exp_add]
    have : (-(c * (bandEndpointPhase s y₀ - bandEndpointPhase s α))
        + 6 * (Real.log (1 - y₀) - Real.log (1 - α)))
        + (c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
          + 6 * (Real.log (1 - α) - Real.log (1 - y₀))) = 0 := by ring
    rw [this, Real.exp_zero]
  rw [hkey, div_le_iff₀ hden]
  set D : ℝ := 6 * Real.pi * Real.sqrt (c * bandEndpointPhase s α) with hDdef
  set E : ℝ := Real.exp (c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
      + 6 * (Real.log (1 - α) - Real.log (1 - y₀))) with hEdef
  set E' : ℝ := Real.exp (-(c * (bandEndpointPhase s y₀ - bandEndpointPhase s α))
      + 6 * (Real.log (1 - y₀) - Real.log (1 - α))) with hE'def
  have hcollar' : Real.exp (c * bandEndpointPhase s α) ≤ Φ α * D :=
    (div_le_iff₀ hden).mp hcollarBound
  calc Real.exp (c * bandEndpointPhase s α) * E
      ≤ (Φ α * D) * E := mul_le_mul_of_nonneg_right hcollar' hEpos.le
    _ ≤ ((Φ y₀ * E') * D) * E :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstep hden.le) hEpos.le
    _ = Φ y₀ * D * (E' * E) := by ring
    _ = Φ y₀ * D := by rw [hinv]; ring

end

end GaloisForLFunctions.RHTower

end
