import GaloisForLFunctions.RHTower.EulerFisherLowTemperature
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Finite radial distance at the cold end of the Euler Fisher superspace

The conformal scale of the zeta Fisher metric is the second Euler prime-power moment
`M₂(β) = ∑' z, eulerPrimePowerWeight β z * eulerPrimePowerEnergy z ^ 2`.  The ground-state
selection theorem `eulerPrimePowerMoment_scaled_tendsto 2` gives `2 ^ β * M₂ β → (log 2) ^ 2`,
i.e. `√(M₂ β) ~ (log 2) * 2 ^ (-β/2)`.  This file proves that the radial line element integrates
to a finite length at the cold end, with the sharp constant

`2 ^ (β/2) * ∫_{u>β} √(M₂ u) du → 2`,

so `β = ∞` sits at finite metric distance while its scalar curvature diverges.

The analytic core is a reusable abstract lemma: for `c > 0`, if `exp(c·u)·g(u) → L` and `g` is
tail-measurable, then `exp(c·β) · ∫_{u>β} g → L / c`.
-/

noncomputable section

open Filter Topology Set MeasureTheory Real

namespace RHTower

/-- Reusable tail-integral asymptotic.  If `exp(c·u)·g(u) → L` with `c > 0` and `g` is measurable
on every upper tail, then the exponentially rescaled tail integral converges:
`exp(c·β) · ∫_{u>β} g u du → L / c`.  Proof: `|exp(cβ)∫g − L/c| = exp(cβ)·|∫(g − L·e^{−c·})|`
is bounded by `exp(cβ)·ε₁·e^{−cβ}/c = ε₁/c` once the integrand is within `ε₁·e^{−cu}` of the model
`L·e^{−cu}` on the tail. -/
theorem tendsto_expMul_tail_integral
    {g : ℝ → ℝ} {c L : ℝ} (hc : 0 < c)
    (hmeas : ∀ᶠ β in atTop, AEStronglyMeasurable g (volume.restrict (Ioi β)))
    (hasymp : Tendsto (fun u => Real.exp (c * u) * g u) atTop (𝓝 L)) :
    Tendsto (fun β : ℝ => Real.exp (c * β) * ∫ u in Ioi β, g u)
      atTop (𝓝 (L / c)) := by
  have hcneg : -c < 0 := by linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε₁ : ℝ := c * ε / 2 with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.mp hasymp) ε₁ hε₁
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hmeas
  refine ⟨max T₀ T₁, fun β hβ => ?_⟩
  have hβT₀ : T₀ ≤ β := le_trans (le_max_left _ _) hβ
  have hβT₁ : T₁ ≤ β := le_trans (le_max_right _ _) hβ
  have hpt : ∀ u ∈ Ioi β, |g u - L * Real.exp (-c * u)| ≤ ε₁ * Real.exp (-c * u) := by
    intro u hu
    have huT₀ : T₀ ≤ u := le_of_lt (lt_of_le_of_lt hβT₀ hu)
    have hd : |Real.exp (c * u) * g u - L| < ε₁ := by
      have := hT₀ u huT₀; rwa [Real.dist_eq] at this
    have hexp_pos : 0 < Real.exp (-c * u) := Real.exp_pos _
    have hEE : Real.exp (-c * u) * Real.exp (c * u) = 1 := by
      rw [← Real.exp_add, show (-c * u + c * u) = 0 by ring, Real.exp_zero]
    have factor : g u - L * Real.exp (-c * u)
        = Real.exp (-c * u) * (Real.exp (c * u) * g u - L) := by
      rw [mul_sub, ← mul_assoc, hEE, one_mul]; ring
    have hkey : |g u - L * Real.exp (-c * u)|
        = Real.exp (-c * u) * |Real.exp (c * u) * g u - L| := by
      rw [factor, abs_mul, Real.abs_exp]
    calc |g u - L * Real.exp (-c * u)|
        = Real.exp (-c * u) * |Real.exp (c * u) * g u - L| := hkey
      _ ≤ Real.exp (-c * u) * ε₁ :=
          mul_le_mul_of_nonneg_left (le_of_lt hd) (le_of_lt hexp_pos)
      _ = ε₁ * Real.exp (-c * u) := by ring
  have hbnd : ∀ u ∈ Ioi β, ‖g u‖ ≤ (|L| + ε₁) * Real.exp (-c * u) := by
    intro u hu
    have huT₀ : T₀ ≤ u := le_of_lt (lt_of_le_of_lt hβT₀ hu)
    have hd : |Real.exp (c * u) * g u - L| < ε₁ := by
      have := hT₀ u huT₀; rwa [Real.dist_eq] at this
    have hX : |Real.exp (c * u) * g u| ≤ |L| + ε₁ := by
      have h1 : |Real.exp (c * u) * g u| - |L| ≤ |Real.exp (c * u) * g u - L| :=
        abs_sub_abs_le_abs_sub _ _
      linarith
    have hEE : Real.exp (-c * u) * Real.exp (c * u) = 1 := by
      rw [← Real.exp_add, show (-c * u + c * u) = 0 by ring, Real.exp_zero]
    have hgu : ‖g u‖ = Real.exp (-c * u) * |Real.exp (c * u) * g u| := by
      rw [Real.norm_eq_abs, abs_mul, Real.abs_exp, ← mul_assoc, hEE, one_mul]
    rw [hgu]
    calc Real.exp (-c * u) * |Real.exp (c * u) * g u|
        ≤ Real.exp (-c * u) * (|L| + ε₁) :=
          mul_le_mul_of_nonneg_left hX (le_of_lt (Real.exp_pos _))
      _ = (|L| + ε₁) * Real.exp (-c * u) := by ring
  have hdomint : IntegrableOn (fun u => (|L| + ε₁) * Real.exp (-c * u)) (Ioi β) :=
    (integrableOn_exp_mul_Ioi hcneg β).const_mul (|L| + ε₁)
  have hgmeas : AEStronglyMeasurable g (volume.restrict (Ioi β)) := hT₁ β hβT₁
  have hgint : IntegrableOn g (Ioi β) :=
    hdomint.mono' hgmeas (ae_restrict_of_forall_mem measurableSet_Ioi hbnd)
  have hφint : IntegrableOn (fun u => L * Real.exp (-c * u)) (Ioi β) :=
    (integrableOn_exp_mul_Ioi hcneg β).const_mul L
  have hintφ : (∫ u in Ioi β, L * Real.exp (-c * u)) = L * (Real.exp (-c * β) / c) := by
    rw [integral_const_mul, integral_exp_mul_Ioi hcneg β]; field_simp
  have hLc : L / c = Real.exp (c * β) * (∫ u in Ioi β, L * Real.exp (-c * u)) := by
    rw [hintφ, show Real.exp (c * β) * (L * (Real.exp (-c * β) / c))
          = L / c * (Real.exp (c * β) * Real.exp (-c * β)) by ring,
      ← Real.exp_add, show (c * β + -c * β) = 0 by ring, Real.exp_zero, mul_one]
  rw [Real.dist_eq, hLc, ← mul_sub, ← integral_sub hgint hφint, abs_mul, Real.abs_exp]
  have hexpβ : 0 < Real.exp (c * β) := Real.exp_pos _
  have hnorm : |∫ u in Ioi β, (g u - L * Real.exp (-c * u))|
      ≤ ∫ u in Ioi β, ‖g u - L * Real.exp (-c * u)‖ := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := volume.restrict (Ioi β))
        (fun u => g u - L * Real.exp (-c * u))
  have hmono2 : (∫ u in Ioi β, ‖g u - L * Real.exp (-c * u)‖)
      ≤ ∫ u in Ioi β, ε₁ * Real.exp (-c * u) := by
    refine setIntegral_mono_on ((hgint.sub hφint).norm)
      ((integrableOn_exp_mul_Ioi hcneg β).const_mul ε₁) measurableSet_Ioi ?_
    intro u hu; rw [Real.norm_eq_abs]; exact hpt u hu
  have hintε : (∫ u in Ioi β, ε₁ * Real.exp (-c * u)) = ε₁ * (Real.exp (-c * β) / c) := by
    rw [integral_const_mul, integral_exp_mul_Ioi hcneg β]; field_simp
  calc Real.exp (c * β) * |∫ u in Ioi β, (g u - L * Real.exp (-c * u))|
      ≤ Real.exp (c * β) * (∫ u in Ioi β, ε₁ * Real.exp (-c * u)) :=
        mul_le_mul_of_nonneg_left (le_trans hnorm hmono2) (le_of_lt hexpβ)
    _ = Real.exp (c * β) * (ε₁ * (Real.exp (-c * β) / c)) := by rw [hintε]
    _ = ε₁ / c * (Real.exp (c * β) * Real.exp (-c * β)) := by ring
    _ = ε₁ / c := by
        rw [← Real.exp_add, show (c * β + -c * β) = 0 by ring, Real.exp_zero, mul_one]
    _ = ε / 2 := by rw [hε₁def]; field_simp
    _ < ε := by linarith

/-- The Euler conformal scale `M₂` is continuous on every tail `Ioi b` with `b > 1`, by the
Weierstrass `M`-test: on `Ioi b` each mode `(n_z)^{-β}(log n_z)²/(k+1)` is bounded by its value at
`b`, and that bound family is summable. -/
theorem continuousOn_eulerConformalScale (b : ℝ) (hb : 1 < b) :
    ContinuousOn
      (fun β => fisherWeightedTsumMoment (eulerPrimePowerWeight β) eulerPrimePowerEnergy 2)
      (Ioi b) := by
  rw [continuousOn_iff_continuous_restrict]
  have hfcont : ∀ z, Continuous
      (fun p : ↥(Ioi b) => eulerPrimePowerWeight (p : ℝ) z * eulerPrimePowerEnergy z ^ 2) := by
    intro z
    have hn : (0 : ℝ) < (eulerPrimePowerNat z : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) (two_le_eulerPrimePowerNat z))
    have hbase : Continuous (fun β : ℝ => (eulerPrimePowerNat z : ℝ) ^ (-β)) :=
      (Real.continuous_const_rpow (ne_of_gt hn)).comp continuous_neg
    have hcp : Continuous (fun p : ↥(Ioi b) => (eulerPrimePowerNat z : ℝ) ^ (-(p : ℝ))) :=
      hbase.comp continuous_subtype_val
    simp only [eulerPrimePowerWeight]
    exact (hcp.div_const _).mul continuous_const
  have hGsummable : Summable
      (fun z => eulerPrimePowerWeight b z * eulerPrimePowerEnergy z ^ 2) := by
    refine (summable_abs_eulerPrimePower_moment 2 b hb).congr (fun z => ?_)
    exact abs_of_nonneg (by dsimp [eulerPrimePowerWeight, eulerPrimePowerEnergy]; positivity)
  have hbound : ∀ z (p : ↥(Ioi b)),
      ‖eulerPrimePowerWeight (p : ℝ) z * eulerPrimePowerEnergy z ^ 2‖ ≤
        eulerPrimePowerWeight b z * eulerPrimePowerEnergy z ^ 2 := by
    intro z p
    have hp : b < (p : ℝ) := p.2
    have hn1 : (1 : ℝ) ≤ (eulerPrimePowerNat z : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 2) (two_le_eulerPrimePowerNat z))
    have hle : (eulerPrimePowerNat z : ℝ) ^ (-(p : ℝ)) ≤ (eulerPrimePowerNat z : ℝ) ^ (-b) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by dsimp [eulerPrimePowerWeight]; positivity)]
    dsimp [eulerPrimePowerWeight]
    gcongr
  exact continuous_tsum hfcont hGsummable hbound

/-- The radial line element `√(M₂(u))` selects the ground mode: `exp((log 2 / 2)·u)·√(M₂ u)`
converges to `log 2`.  This is the square-root of the second-moment ground selection
`2 ^ u · M₂ u → (log 2)²`. -/
theorem eulerColdEndSqrt_asymptotic :
    Tendsto (fun u => Real.exp (Real.log 2 / 2 * u) *
        Real.sqrt (fisherWeightedTsumMoment (eulerPrimePowerWeight u) eulerPrimePowerEnergy 2))
      atTop (𝓝 (Real.log 2)) := by
  have h := (eulerPrimePowerMoment_scaled_tendsto 2).sqrt
  rw [show Real.sqrt ((Real.log 2) ^ 2) = Real.log 2 from
    Real.sqrt_sq (Real.log_nonneg (by norm_num))] at h
  refine h.congr (fun u => ?_)
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ u)]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1; ring

/-- Finite radial distance at the cold end of the zeta Fisher superspace, with the sharp `2,3`
prime-power constant: `2 ^ (β/2) · ∫_{u>β} √(M₂ u) du → 2`.  Hence `β = ∞` lies at finite metric
distance even though its scalar curvature diverges to `-∞`. -/
theorem eulerColdEndRadialDistance_tendsto :
    Tendsto (fun β : ℝ => (2 : ℝ) ^ (β / 2) *
        ∫ u in Ioi β, Real.sqrt (fisherWeightedTsumMoment
          (eulerPrimePowerWeight u) eulerPrimePowerEnergy 2))
      atTop (𝓝 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (0 : ℝ) < Real.log 2 / 2 := by linarith
  have hmeas : ∀ᶠ β in atTop, AEStronglyMeasurable
      (fun u => Real.sqrt (fisherWeightedTsumMoment
        (eulerPrimePowerWeight u) eulerPrimePowerEnergy 2))
      (volume.restrict (Ioi β)) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with β hβ
    have hcont : ContinuousOn
        (fun u => Real.sqrt (fisherWeightedTsumMoment
          (eulerPrimePowerWeight u) eulerPrimePowerEnergy 2)) (Ioi β) :=
      Real.continuous_sqrt.comp_continuousOn
        (continuousOn_eulerConformalScale β (by linarith))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have habs := tendsto_expMul_tail_integral hc hmeas eulerColdEndSqrt_asymptotic
  rw [show Real.log 2 / (Real.log 2 / 2) = 2 by
    field_simp] at habs
  refine habs.congr (fun β => ?_)
  congr 1
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1; ring

end RHTower
