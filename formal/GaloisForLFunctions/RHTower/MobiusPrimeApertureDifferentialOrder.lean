import GaloisForLFunctions.RHTower.MobiusPrimeApertureQuantile
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount

/-!
# The scalar differential-order cost of the critical prime aperture

The prime number theorem turns the critical cutoff `N_ω = exp(c/(2ω))` into an explicit prime
count `π(N_ω) ~ (2ω/c)·exp(c/(2ω))`.  Under the full-mass criterion the resulting aperture is so
large that `ω·log(aperture)` diverges: no family whose scalar differential order grows like
`exp(O(1/ω))` with a bounded exponent constant can retain the whole critical channel.
-/

open Filter Set Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

/-- The prime-counting ratio against `x / log x` tends to one. -/
theorem tendsto_primeCounting_ratio :
    Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (nhds 1) := by
  have h0 := GaloisForLFunctions.HTGeometry.isLittleO_primeCounting_sub.tendsto_div_nhds_zero
  have heq : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x))
      =ᶠ[atTop] fun x : ℝ =>
        ((Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x) / (x / Real.log x) + 1 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlx : 0 < Real.log x := Real.log_pos hx
    have hx0 : 0 < x := by linarith
    have hne : x / Real.log x ≠ 0 := by positivity
    field_simp
    ring
  rw [tendsto_congr' heq]
  have := h0.add_const 1
  rwa [zero_add] at this

/-- **Equation (21).**  At the critical cutoff the prime aperture is asymptotic to
`(2ω/c)·exp(c/(2ω))`. -/
theorem tendsto_criticalAperture_ratio {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ω : ℝ => (Nat.primeCounting ⌊criticalCutoff c ω⌋₊ : ℝ)
        / ((2 * ω / c) * criticalCutoff c ω)) (𝓝[>] (0 : ℝ)) (nhds 1) := by
  have hcomp := tendsto_primeCounting_ratio.comp (tendsto_criticalCutoff hc)
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hωmem
  have hω : 0 < ω := mem_Ioi.mp hωmem
  have hlog : Real.log (criticalCutoff c ω) = c / (2 * ω) := by
    rw [criticalCutoff, Real.log_exp]
  show (Nat.primeCounting ⌊criticalCutoff c ω⌋₊ : ℝ)
      / (criticalCutoff c ω / Real.log (criticalCutoff c ω)) = _
  rw [hlog]
  congr 1
  field_simp

/-! ## The full-mass differential-order divergence -/

/-- The scaled cutoff exponent `log N_ω = C ω / (2ω)`. -/
def cutoffExponent (C : ℝ → ℝ) (ω : ℝ) : ℝ := C ω / (2 * ω)

theorem log_criticalCutoff {c ω : ℝ} (_hω : 0 < ω) :
    Real.log (criticalCutoff c ω) = c / (2 * ω) := by
  rw [criticalCutoff, Real.log_exp]

theorem tendsto_cutoffExponent {C : ℝ → ℝ} (hC : Tendsto C (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto (cutoffExponent C) (𝓝[>] (0 : ℝ)) atTop := by
  have hinv : Tendsto (fun ω : ℝ => (2 * ω)⁻¹) (𝓝[>] (0 : ℝ)) atTop := by
    have h := tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
    have hmul : Tendsto (fun ω : ℝ => (2 : ℝ)⁻¹ * ω⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) h
    exact hmul.congr fun ω => by rw [mul_inv]
  have h := hC.atTop_mul_atTop₀ hinv
  exact h.congr fun ω => by rw [cutoffExponent, div_eq_mul_inv]

/-- **Equation (23).**  Under full mass transport the scalar differential aperture grows faster
than any `exp(O(1/ω))` family with bounded exponent constant. -/
theorem tendsto_omega_mul_log_aperture_atTop {C : ℝ → ℝ}
    (hC : Tendsto C (𝓝[>] (0 : ℝ)) atTop) :
    Tendsto (fun ω : ℝ =>
        ω * Real.log (Nat.primeCounting ⌊criticalCutoff (C ω) ω⌋₊ : ℝ))
      (𝓝[>] (0 : ℝ)) atTop := by
  have htTop : Tendsto (cutoffExponent C) (𝓝[>] (0 : ℝ)) atTop := tendsto_cutoffExponent hC
  have hcut : ∀ ω : ℝ, 0 < ω →
      Real.log (criticalCutoff (C ω) ω) = cutoffExponent C ω := by
    intro ω hω
    rw [log_criticalCutoff hω, cutoffExponent]
  have hN : Tendsto (fun ω : ℝ => criticalCutoff (C ω) ω) (𝓝[>] (0 : ℝ)) atTop := by
    have h := Real.tendsto_exp_atTop.comp htTop
    exact h.congr fun ω => by simp [Function.comp, criticalCutoff, cutoffExponent]
  have hratio := tendsto_primeCounting_ratio.comp hN
  have hhalf : ∀ᶠ ω in 𝓝[>] (0 : ℝ),
      (1 / 2 : ℝ) * (criticalCutoff (C ω) ω / cutoffExponent C ω)
        ≤ (Nat.primeCounting ⌊criticalCutoff (C ω) ω⌋₊ : ℝ) := by
    have hev : ∀ᶠ ω in 𝓝[>] (0 : ℝ),
        (1 / 2 : ℝ) < (Nat.primeCounting ⌊criticalCutoff (C ω) ω⌋₊ : ℝ)
          / (criticalCutoff (C ω) ω / Real.log (criticalCutoff (C ω) ω)) :=
      hratio.eventually (Ioi_mem_nhds (by norm_num))
    filter_upwards [hev, htTop.eventually_gt_atTop 0, self_mem_nhdsWithin] with ω h1 h2 h3
    have hω : 0 < ω := mem_Ioi.mp h3
    rw [hcut ω hω] at h1
    have hpos : 0 < criticalCutoff (C ω) ω / cutoffExponent C ω :=
      div_pos (criticalCutoff_pos _ _) h2
    have h4 := (lt_div_iff₀ hpos).mp h1
    linarith
  have hlogdiv : Tendsto (fun ω : ℝ => Real.log (cutoffExponent C ω) / cutoffExponent C ω)
      (𝓝[>] (0 : ℝ)) (nhds 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp htTop
  have hprod : Tendsto (fun ω : ℝ => (ω * cutoffExponent C ω)
      * (1 - Real.log (cutoffExponent C ω) / cutoffExponent C ω
        - Real.log 2 / cutoffExponent C ω)) (𝓝[>] (0 : ℝ)) atTop := by
    have h1 : Tendsto (fun ω : ℝ => ω * cutoffExponent C ω) (𝓝[>] (0 : ℝ)) atTop := by
      have hhalfC : Tendsto (fun ω : ℝ => (1 / 2 : ℝ) * C ω) (𝓝[>] (0 : ℝ)) atTop :=
        Filter.Tendsto.const_mul_atTop (by norm_num) hC
      refine hhalfC.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ω hωmem
      have hω : 0 < ω := mem_Ioi.mp hωmem
      rw [cutoffExponent]
      field_simp
    have h2 : Tendsto (fun ω : ℝ => Real.log 2 / cutoffExponent C ω) (𝓝[>] (0 : ℝ)) (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds htTop
    have h3 : Tendsto (fun ω : ℝ => 1 - Real.log (cutoffExponent C ω) / cutoffExponent C ω
        - Real.log 2 / cutoffExponent C ω) (𝓝[>] (0 : ℝ)) (nhds 1) := by
      have h4 := ((tendsto_const_nhds (x := (1:ℝ)) (f := 𝓝[>] (0:ℝ))).sub hlogdiv).sub h2
      simpa using h4
    exact Filter.Tendsto.atTop_mul_pos (by norm_num) h1 h3
  refine tendsto_atTop_mono' _ ?_ hprod
  filter_upwards [hhalf, htTop.eventually_gt_atTop 1, self_mem_nhdsWithin] with ω hb ht1 hωmem
  have hω : 0 < ω := mem_Ioi.mp hωmem
  have htpos : 0 < cutoffExponent C ω := by linarith
  have hNpos : 0 < criticalCutoff (C ω) ω := criticalCutoff_pos _ _
  have hproxy : 0 < (1 / 2 : ℝ) * (criticalCutoff (C ω) ω / cutoffExponent C ω) := by positivity
  have hlogle : Real.log ((1 / 2 : ℝ) * (criticalCutoff (C ω) ω / cutoffExponent C ω))
      ≤ Real.log (Nat.primeCounting ⌊criticalCutoff (C ω) ω⌋₊ : ℝ) :=
    Real.log_le_log hproxy hb
  have hexpand : Real.log ((1 / 2 : ℝ) * (criticalCutoff (C ω) ω / cutoffExponent C ω))
      = cutoffExponent C ω - Real.log (cutoffExponent C ω) - Real.log 2 := by
    rw [Real.log_mul (by norm_num) (by positivity),
      Real.log_div (ne_of_gt hNpos) (ne_of_gt htpos), hcut ω hω, one_div, Real.log_inv]
    ring
  rw [hexpand] at hlogle
  have hfac : (ω * cutoffExponent C ω) * (1 - Real.log (cutoffExponent C ω) / cutoffExponent C ω
      - Real.log 2 / cutoffExponent C ω)
      = ω * (cutoffExponent C ω - Real.log (cutoffExponent C ω) - Real.log 2) := by
    field_simp
  rw [hfac]
  exact mul_le_mul_of_nonneg_left hlogle hω.le

end

end RHTower
