import GaloisForLFunctions.RHTower.EulerTiltCovariance
import GaloisForLFunctions.RHTower.EulerTiltSaddleAperture

/-!
# The Euler-edge escape frequency and Schur complement

At the source-faithful tilt the parity–energy data of the Euler-tilted Gibbs source are

```text
A = Var N,   B = Cov(N, E),   C = Var E,   t* = π B / C,   D = π²(A - B²/C).
```

With the canonical cofinal aperture the tilt is `δ ≍ 2 log ℓ/ℓ²`, so `A = log ℓ + O(1)`,
`B = ℓ + O(log ℓ)` and `C = ℓ²/2 + O(ℓ log ℓ)`; hence `t* ℓ → 2π`, `D/log ℓ → π²`, and the
physical shell is resonant: `t* E* → 2π`.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- The logarithm of the canonical aperture. -/
def apertureLog (L : ℝ) : ℝ := Real.log (cofinalAperture L)

/-- The escape frequency `t* = π Cov(N,E) / Var E`. -/
def eulerTiltEscapeFrequency (σ Y : ℝ) : ℝ :=
  Real.pi * eulerTiltCovariance σ Y / eulerTiltEnergyVariance σ Y

/-- The parity–energy Schur complement `D = π² (Var N - Cov(N,E)²/Var E)`. -/
def eulerTiltSchurComplement (σ Y : ℝ) : ℝ :=
  Real.pi ^ 2 * (eulerTiltMass σ Y
    - eulerTiltCovariance σ Y ^ 2 / eulerTiltEnergyVariance σ Y)

open Classical in
/-- The source-faithful saddle tilt at aperture parameter `L`. -/
def saddleTilt (L : ℝ) : ℝ :=
  if h : ∃ δ : ℝ, δ ∈ Ioc (0 : ℝ) 1
      ∧ eulerTiltSaddleDefect δ (cofinalAperture L) (Real.exp (-L)) = 0 then h.choose else 0

theorem eventually_saddleTilt_spec :
    ∀ᶠ L in atTop, saddleTilt L ∈ Ioc (0 : ℝ) 1
      ∧ eulerTiltSaddleDefect (saddleTilt L) (cofinalAperture L) (Real.exp (-L)) = 0
      ∧ |saddleTilt L - 2 * cofinalApertureWidth L / apertureLog L ^ 2|
          ≤ 2 * (eulerTiltEnergyConst + 1) / apertureLog L ^ 2
            + 16 * cofinalApertureWidth L ^ 2 / (3 * apertureLog L ^ 3) := by
  filter_upwards [eventually_saddle_root_expansion] with L hL
  obtain ⟨huniq, hexp⟩ := hL
  obtain ⟨δ, ⟨hδmem, hδroot⟩, _⟩ := huniq
  have hex : ∃ δ : ℝ, δ ∈ Ioc (0 : ℝ) 1
      ∧ eulerTiltSaddleDefect δ (cofinalAperture L) (Real.exp (-L)) = 0 := ⟨δ, hδmem, hδroot⟩
  have hval : saddleTilt L = hex.choose := by
    rw [saddleTilt, dif_pos hex]
  obtain ⟨hmem, hroot⟩ := hex.choose_spec
  rw [hval]
  exact ⟨hmem, hroot, hexp _ hmem hroot⟩

/-! ## Aperture limits -/

theorem tendsto_apertureLog : Tendsto apertureLog atTop atTop := by
  have hfun : ∀ᶠ L in atTop, apertureLog L = cofinalApertureWidth L + L := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    exact log_cofinalAperture hL
  have hsum : Tendsto (fun L : ℝ => cofinalApertureWidth L + L) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (tendsto_id (α := ℝ))
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hw : 0 ≤ cofinalApertureWidth L := by
      rw [cofinalApertureWidth]
      have h1 : 0 ≤ Real.log L := Real.log_nonneg hL
      have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    simpa using hw
  exact hsum.congr' (hfun.mono fun L h => h.symm)

theorem tendsto_width_div_apertureLog :
    Tendsto (fun L : ℝ => cofinalApertureWidth L / apertureLog L) atTop (nhds 0) := by
  have hsq := tendsto_widthSq_div_logAperture
  have hA := tendsto_cofinalApertureWidth
  have hquot : Tendsto (fun L : ℝ =>
      (cofinalApertureWidth L ^ 2 / apertureLog L) / cofinalApertureWidth L) atTop (nhds 0) :=
    hsq.div_atTop hA
  refine hquot.congr' ?_
  filter_upwards [hA.eventually_gt_atTop 0, eventually_gt_atTop (1 : ℝ)] with L hApos hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hlog : apertureLog L = cofinalApertureWidth L + L := log_cofinalAperture hL0
  have hne : cofinalApertureWidth L ≠ 0 := ne_of_gt hApos
  field_simp

theorem tendsto_saddleTilt_mul_apertureLog :
    Tendsto (fun L : ℝ => saddleTilt L * apertureLog L) atTop (nhds 0) := by
  have hspec := eventually_saddleTilt_spec
  have hratio := tendsto_width_div_apertureLog
  have hsq := tendsto_widthSq_div_logAperture
  have hinv : Tendsto (fun L : ℝ => (apertureLog L)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_apertureLog
  have hmaj : Tendsto (fun L : ℝ =>
      2 * (cofinalApertureWidth L / apertureLog L)
        + 2 * (eulerTiltEnergyConst + 1) * (apertureLog L)⁻¹
        + 16 / 3 * ((cofinalApertureWidth L ^ 2 / apertureLog L) * (apertureLog L)⁻¹))
      atTop (nhds 0) := by
    have h1 := hratio.const_mul (2 : ℝ)
    have h2 := hinv.const_mul (2 * (eulerTiltEnergyConst + 1))
    have h3 := (hsq.mul hinv).const_mul (16 / 3 : ℝ)
    rw [mul_zero] at h1 h2
    rw [mul_zero, mul_zero] at h3
    have h := (h1.add h2).add h3
    rwa [add_zero, add_zero] at h
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [hspec, tendsto_apertureLog.eventually_gt_atTop 1] with L hL hℓ
  obtain ⟨hmem, _, hexp⟩ := hL
  have hℓ0 : 0 < apertureLog L := by linarith
  have hb := abs_le.mp hexp
  have hpos : 0 < saddleTilt L := hmem.1
  have hupper : saddleTilt L ≤ 2 * cofinalApertureWidth L / apertureLog L ^ 2
      + (2 * (eulerTiltEnergyConst + 1) / apertureLog L ^ 2
        + 16 * cofinalApertureWidth L ^ 2 / (3 * apertureLog L ^ 3)) := by
    linarith [hb.2]
  have hstep := mul_le_mul_of_nonneg_right hupper hℓ0.le
  have hval : (2 * cofinalApertureWidth L / apertureLog L ^ 2
      + (2 * (eulerTiltEnergyConst + 1) / apertureLog L ^ 2
        + 16 * cofinalApertureWidth L ^ 2 / (3 * apertureLog L ^ 3))) * apertureLog L
      = 2 * (cofinalApertureWidth L / apertureLog L)
        + 2 * (eulerTiltEnergyConst + 1) * (apertureLog L)⁻¹
        + 16 / 3 * ((cofinalApertureWidth L ^ 2 / apertureLog L) * (apertureLog L)⁻¹) := by
    field_simp
    ring
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < saddleTilt L * apertureLog L)]
  calc saddleTilt L * apertureLog L
      ≤ (2 * cofinalApertureWidth L / apertureLog L ^ 2
        + (2 * (eulerTiltEnergyConst + 1) / apertureLog L ^ 2
          + 16 * cofinalApertureWidth L ^ 2 / (3 * apertureLog L ^ 3))) * apertureLog L := hstep
    _ = 2 * (cofinalApertureWidth L / apertureLog L)
        + 2 * (eulerTiltEnergyConst + 1) * (apertureLog L)⁻¹
        + 16 / 3 * ((cofinalApertureWidth L ^ 2 / apertureLog L) * (apertureLog L)⁻¹) := hval

end

end RHTower
