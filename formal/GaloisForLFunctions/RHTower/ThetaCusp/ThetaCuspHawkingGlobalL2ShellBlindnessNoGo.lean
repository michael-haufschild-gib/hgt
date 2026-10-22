import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingCausalHardyIndexEndpoint
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTiltedMirrorOpticalTheoremEndpoint
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier

/-!
# Global L² shell blindness of the theta-cusp Hawking channel

The de-embedded moving-mirror pair carrier at tilt `a` is the literal boundary value
`XiC (w + a i)`.  We divide it by `1 + ‖XiC (w + a i)‖` only to obtain a bounded scattering
symbol; this preserves every dark shell.

Ordinary continuum scattering acts on almost-everywhere classes.  This file makes that obstruction
exact: replacing one dark shell by a bright value changes the pointwise response but leaves the
entire `L²` multiplication operator, hence every wavepacket output, unchanged.  At an upper
theta-Hawking resonance the same point is nevertheless visible in the analytic Hardy completion as
a one-dimensional Gamow defect with Wigner--Smith charge one.

The healed symbol is deliberately nonanalytic.  It is not a second theta source.  It witnesses that
the ordinary `L²` scattering/KMS equivalence class alone cannot recover source-selected point
values.  Any RH-bearing completion must therefore derive an analytic Hardy/RKHS state space (or an
equivalent distributional shell observable), not merely global CCR, KMS, losslessness, or
asymptotic completeness.
-/

open Complex Real MeasureTheory

noncomputable section

namespace RHTower

/-- Bounded normalization of the exact de-embedded theta-cusp Hawking pair carrier. -/
def thetaCuspHawkingNormalizedTiltedShellResponse (a w : ℝ) : ℂ :=
  thetaCuspHawkingTiltedDeembeddedPairCarrier a w /
    ((1 + ‖thetaCuspHawkingTiltedDeembeddedPairCarrier a w‖ : ℝ) : ℂ)

theorem continuous_thetaCuspHawkingNormalizedTiltedShellResponse (a : ℝ) :
    Continuous (thetaCuspHawkingNormalizedTiltedShellResponse a) := by
  have hcarrier : Continuous (fun w : ℝ =>
      thetaCuspHawkingTiltedDeembeddedPairCarrier a w) := by
    unfold thetaCuspHawkingTiltedDeembeddedPairCarrier
    exact XiC_differentiable.continuous.comp (by fun_prop)
  unfold thetaCuspHawkingNormalizedTiltedShellResponse
  exact hcarrier.div (by fun_prop) (fun w => by
    exact_mod_cast (ne_of_gt (by positivity :
      0 < 1 + ‖thetaCuspHawkingTiltedDeembeddedPairCarrier a w‖)))

/-- The source normalization is contractive, so it defines an `L²` scattering multiplier. -/
theorem norm_thetaCuspHawkingNormalizedTiltedShellResponse_le_one (a w : ℝ) :
    ‖thetaCuspHawkingNormalizedTiltedShellResponse a w‖ ≤ 1 := by
  unfold thetaCuspHawkingNormalizedTiltedShellResponse
  rw [norm_div]
  have hden :
      ‖((1 + ‖thetaCuspHawkingTiltedDeembeddedPairCarrier a w‖ : ℝ) : ℂ)‖ =
        1 + ‖thetaCuspHawkingTiltedDeembeddedPairCarrier a w‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hden]
  have hn : 0 ≤ ‖thetaCuspHawkingTiltedDeembeddedPairCarrier a w‖ := norm_nonneg _
  exact (div_le_one (by positivity)).2 (by linarith)

/-- Change exactly one total-frequency shell to the bright value `1`. -/
def thetaCuspHawkingBrightHealTiltedShell (a w₀ w : ℝ) : ℂ :=
  if w = w₀ then 1 else thetaCuspHawkingNormalizedTiltedShellResponse a w

theorem measurable_thetaCuspHawkingBrightHealTiltedShell (a w₀ : ℝ) :
    Measurable (thetaCuspHawkingBrightHealTiltedShell a w₀) := by
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton]
      using (measurableSet_singleton w₀)
  · exact measurable_const
  · exact (continuous_thetaCuspHawkingNormalizedTiltedShellResponse a).measurable

theorem norm_thetaCuspHawkingBrightHealTiltedShell_le_one (a w₀ w : ℝ) :
    ‖thetaCuspHawkingBrightHealTiltedShell a w₀ w‖ ≤ 1 := by
  by_cases h : w = w₀
  · simp [thetaCuspHawkingBrightHealTiltedShell, h]
  · simp [thetaCuspHawkingBrightHealTiltedShell, h,
      norm_thetaCuspHawkingNormalizedTiltedShellResponse_le_one]

/-- A one-shell healing is invisible to Lebesgue almost-everywhere equivalence. -/
theorem thetaCuspHawkingBrightHealTiltedShell_ae_eq (a w₀ : ℝ) :
    thetaCuspHawkingBrightHealTiltedShell a w₀ =ᵐ[volume]
      thetaCuspHawkingNormalizedTiltedShellResponse a := by
  change ∀ᵐ w ∂volume,
    thetaCuspHawkingBrightHealTiltedShell a w₀ w =
      thetaCuspHawkingNormalizedTiltedShellResponse a w
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_singleton w₀)
  intro w hw
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hw ⊢
  by_contra hne
  exact hw (by simp [thetaCuspHawkingBrightHealTiltedShell, hne])

/-- Physical total-frequency wavepacket carrier for the de-embedded pair channel. -/
abbrev ThetaCuspHawkingShellL2 := Lp ℂ 2 (volume : Measure ℝ)

/-- `L²` scattering multiplier of the bounded exact theta-Hawking response. -/
def thetaCuspHawkingNormalizedTiltedShellScattering (a : ℝ) :
    ThetaCuspHawkingShellL2 →L[ℂ] ThetaCuspHawkingShellL2 :=
  lpBoundedMulCLM
    (continuous_thetaCuspHawkingNormalizedTiltedShellResponse a).measurable
    (by norm_num) (norm_thetaCuspHawkingNormalizedTiltedShellResponse_le_one a)

/-- `L²` scattering multiplier after bright-healing one exact shell. -/
def thetaCuspHawkingBrightHealedTiltedShellScattering (a w₀ : ℝ) :
    ThetaCuspHawkingShellL2 →L[ℂ] ThetaCuspHawkingShellL2 :=
  lpBoundedMulCLM (measurable_thetaCuspHawkingBrightHealTiltedShell a w₀)
    (by norm_num) (norm_thetaCuspHawkingBrightHealTiltedShell_le_one a w₀)

/-- **Global `L²` shell-blindness.** Bright-healing one exact total-frequency shell leaves the full
wavepacket scattering operator unchanged. -/
theorem thetaCuspHawkingBrightHealedTiltedShellScattering_eq (a w₀ : ℝ) :
    thetaCuspHawkingBrightHealedTiltedShellScattering a w₀ =
      thetaCuspHawkingNormalizedTiltedShellScattering a := by
  unfold thetaCuspHawkingBrightHealedTiltedShellScattering
    thetaCuspHawkingNormalizedTiltedShellScattering
  exact lpBoundedMulCLM_congr
    (measurable_thetaCuspHawkingBrightHealTiltedShell a w₀)
    (continuous_thetaCuspHawkingNormalizedTiltedShellResponse a).measurable
    (by norm_num) (norm_thetaCuspHawkingBrightHealTiltedShell_le_one a w₀)
    (by norm_num) (norm_thetaCuspHawkingNormalizedTiltedShellResponse_le_one a)
    (thetaCuspHawkingBrightHealTiltedShell_ae_eq a w₀)

/-- Every physical `L²` wavepacket has exactly the same outgoing state after a one-shell healing. -/
theorem thetaCuspHawkingBrightHealedTiltedShellScattering_apply_eq
    (a w₀ : ℝ) (ψ : ThetaCuspHawkingShellL2) :
    thetaCuspHawkingBrightHealedTiltedShellScattering a w₀ ψ =
      thetaCuspHawkingNormalizedTiltedShellScattering a ψ := by
  rw [thetaCuspHawkingBrightHealedTiltedShellScattering_eq]

/-- A backreaction resonance is a dark shell of the exact normalized theta-Hawking response. -/
theorem thetaCuspHawkingNormalizedTiltedShellResponse_resonance_eq_zero
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingNormalizedTiltedShellResponse r.1.im r.1.re = 0 := by
  have harg : ((r.1.re : ℂ) + (r.1.im : ℂ) * I) = r.1 := by
    apply Complex.ext <;> simp
  simp [thetaCuspHawkingNormalizedTiltedShellResponse,
    thetaCuspHawkingTiltedDeembeddedPairCarrier, harg,
    thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero r]

theorem thetaCuspHawkingBrightHealTiltedShell_resonance_eq_one
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingBrightHealTiltedShell r.1.im r.1.re r.1.re = 1 := by
  simp [thetaCuspHawkingBrightHealTiltedShell]

/-- **`L²`-blind/Hardy-visible resonance theorem.** At every upper theta-Hawking resonance, a dark
shell can be made pointwise bright without changing global `L²` scattering, while analytic causal
completion detects exactly one missing direction and one unit of Wigner--Smith charge. -/
theorem thetaCuspHawking_resonance_L2_invisible_Hardy_visible
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) :
    thetaCuspHawkingNormalizedTiltedShellResponse r.1.im r.1.re = 0 ∧
      thetaCuspHawkingBrightHealTiltedShell r.1.im r.1.re r.1.re = 1 ∧
      thetaCuspHawkingBrightHealedTiltedShellScattering r.1.im r.1.re =
        thetaCuspHawkingNormalizedTiltedShellScattering r.1.im ∧
      Module.finrank ℂ ((thetaCuspHawkingCausalHardyRange r hr)ᗮ) = 1 ∧
      thetaCuspHawkingAllPassWindingCharge r = 1 := by
  exact ⟨thetaCuspHawkingNormalizedTiltedShellResponse_resonance_eq_zero r,
    thetaCuspHawkingBrightHealTiltedShell_resonance_eq_one r,
    thetaCuspHawkingBrightHealedTiltedShellScattering_eq r.1.im r.1.re,
    finrank_thetaCuspHawkingCausalHardyDefect_eq_one r hr,
    thetaCuspHawkingAllPassWindingCharge_eq_one r hr⟩

end RHTower
