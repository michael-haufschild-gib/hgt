import GaloisForLFunctions.RHTower.ProlateRescaledProfileBounds
import GaloisForLFunctions.RHTower.ProlateHermitePairingHypotheses
import GaloisForLFunctions.RHTower.ProlateCanonicalRadialFamily
import GaloisForLFunctions.RHTower.ProlateBandEigenMass

/-!
# The signed mode is pinned to the oscillator ladder at rate `1/c`

The canonical radial representative of a live signed mode is an endpoint-normalized band
eigenfunction, hence globally bounded together with its first two derivatives.  Its Hermite
rescaling therefore satisfies every hypothesis of the ladder pin, and the pin reads

```text
|c·s − (2m+1)| · |⟨u, φ_m⟩|  =  |⟨u, W_m⟩| / c ,
```

an identity whose right-hand side carries the full factor `1/c` and involves the profile only
through a bounded pairing against a fixed Gaussian-decaying weight.  So the scaled separation
constant is within `O(1/c)` of every oscillator rung whose Hermite pairing does not vanish.
-/

noncomputable section

open MeasureTheory Filter

open scoped Topology ContDiff

namespace RHTower

/-- The canonical radial representative of a live signed mode is a global band eigenfunction. -/
theorem bandTransform_signedModeRadialData_R {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hvalue : evenProlateSignedValue a n ≠ 0) (x : ℝ) :
    bandTransform (signedModeRadialBandwidth a) (signedModeRadialData a n).R x
      = evenProlateSignedValue a n ^ 2 * (signedModeRadialData a n).R x := by
  have hD := signedModeRadialData_isExact ha n hvalue
  have hRdef : (signedModeRadialData a n).R
      = prolateEndpointNormalize (signedModeRadialData a n).Phi := hD.2.2.2.2.1
  have hband := hD.2.2.2.2.2.2.2.2.1
  rw [hRdef]
  exact GaloisForLFunctions.RHTower.bandTransform_endpointNormalize_eigen hband x

/-- The canonical radial representative is bounded together with its first two derivatives. -/
theorem exists_bound_signedModeRadialData_R {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ x, |(signedModeRadialData a n).R x| ≤ B) ∧
      (∀ x, |deriv (signedModeRadialData a n).R x| ≤ B) ∧
      (∀ x, |deriv (deriv (signedModeRadialData a n).R) x| ≤ B) := by
  have hD := signedModeRadialData_isExact ha n hvalue
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (signedModeRadialData a n).R :=
    hD.2.2.2.2.2.1
  have hcont : Continuous (signedModeRadialData a n).R := hsm.continuous
  have hband := bandTransform_signedModeRadialData_R ha n hvalue
  have hlam : evenProlateSignedValue a n ^ 2 ≠ 0 := pow_ne_zero 2 hvalue
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_bound_of_bandTransform_eigen hlam hcont hband
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_deriv_of_bandTransform_eigen hlam hcont hband
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_bound_deriv2_of_bandTransform_eigen hlam hcont hband
  refine ⟨max C₀ (max C₁ C₂), le_trans hC₀0 (le_max_left _ _), fun x => ?_, fun x => ?_,
    fun x => ?_⟩
  · exact le_trans (hC₀ x) (le_max_left _ _)
  · exact le_trans (hC₁ x) (le_trans (le_max_left _ _) (le_max_right _ _))
  · exact le_trans (hC₂ x) (le_trans (le_max_right _ _) (le_max_right _ _))

/-- The Hermite rescaling of the canonical radial representative. -/
def signedModeRescaledProfile (a : ℝ) (n : ℕ) : ℝ → ℝ :=
  prolateHermiteRescale (signedModeRadialBandwidth a) (signedModeRadialData a n).R

theorem signedModeRadialBandwidth_pos {a : ℝ} (ha : 0 < a) :
    0 < signedModeRadialBandwidth a := by
  rw [signedModeRadialBandwidth]
  positivity

/-- **The rescaled signed mode is pinned to every oscillator rung it pairs with.** -/
theorem exists_bound_abs_signedMode_scaledSeparation_sub_rung {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℕ,
      (∫ x, signedModeRescaledProfile a n x * hermiteFun m x) ≠ 0 →
      |signedModeRadialBandwidth a * (signedModeRadialData a n).s - (2 * m + 1)|
        ≤ B * (∫ x, |prolateDefectWeight m x|)
            / (signedModeRadialBandwidth a
                * |∫ x, signedModeRescaledProfile a n x * hermiteFun m x|) := by
  classical
  have hc : 0 < signedModeRadialBandwidth a := signedModeRadialBandwidth_pos ha
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  have hcne : c ≠ 0 := hc.ne'
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  set R : ℝ → ℝ := (signedModeRadialData a n).R with hRdef
  have hD := signedModeRadialData_isExact ha n hvalue
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R := hD.2.2.2.2.2.1
  have heig : ∀ x : ℝ, prolateSLAction c R x = (signedModeRadialData a n).chi * R x :=
    hD.2.2.2.2.2.2.2.2.2.1
  have hs : (signedModeRadialData a n).s
      = radialSeparationRatio c (signedModeRadialData a n).chi :=
    hD.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨B, hB0, hBR, hBR', hBR''⟩ := exists_bound_signedModeRadialData_R ha n hvalue
  have hdiff : Differentiable ℝ R := (contDiff_infty_iff_deriv.mp hsm).1
  have hsmd : ContDiff ℝ ∞ (deriv R) := (contDiff_infty_iff_deriv.mp hsm).2
  have hdiff2 : Differentiable ℝ (deriv R) := (contDiff_infty_iff_deriv.mp hsmd).1
  have hsmd2 : ContDiff ℝ ∞ (deriv (deriv R)) := (contDiff_infty_iff_deriv.mp hsmd).2
  set u : ℝ → ℝ := signedModeRescaledProfile a n with hudef
  set u' : ℝ → ℝ := fun ξ => deriv R (ξ / Real.sqrt c) / Real.sqrt c with hu'def
  set u'' : ℝ → ℝ := fun ξ => deriv (deriv R) (ξ / Real.sqrt c) / c with hu''def
  have hueq : u = prolateHermiteRescale c R := rfl
  have hderiv1 : deriv u = u' := by
    rw [hueq, hu'def]
    exact deriv_prolateHermiteRescale hc hdiff
  have hu : ∀ x, HasDerivAt u (u' x) x := by
    intro x
    rw [hueq]
    exact hasDerivAt_prolateHermiteRescale hc hdiff x
  have hu' : ∀ x, HasDerivAt u' (u'' x) x := by
    intro x
    have h := hasDerivAt_deriv_prolateHermiteRescale hc hdiff hdiff2 x
    rw [← hueq, hderiv1] at h
    exact h
  have hinner : Continuous fun ξ : ℝ => ξ / Real.sqrt c :=
    continuous_id.div_const _
  have hcu : Continuous u := by
    rw [hueq]
    exact (hsm.continuous).comp hinner
  have hcu' : Continuous u' := by
    rw [hu'def]
    exact ((hsmd.continuous).comp hinner).div_const _
  have hcu'' : Continuous u'' := by
    rw [hu''def]
    exact ((hsmd2.continuous).comp hinner).div_const _
  -- the three uniform bounds after rescaling
  set Bmax : ℝ := max B (max (B / Real.sqrt c) (B / c)) with hBmaxdef
  have hBmax0 : 0 ≤ Bmax := le_trans hB0 (le_max_left _ _)
  have hbu : ∀ x, |u x| ≤ Bmax := fun x =>
    le_trans (hBR (x / Real.sqrt c)) (le_max_left _ _)
  have hbu' : ∀ x, |u' x| ≤ Bmax := by
    intro x
    have h : |u' x| = |deriv R (x / Real.sqrt c)| / Real.sqrt c := by
      rw [hu'def]
      simp only
      rw [abs_div, abs_of_pos hsc]
    rw [h]
    have hstep : |deriv R (x / Real.sqrt c)| / Real.sqrt c ≤ B / Real.sqrt c := by
      gcongr
      exact hBR' _
    exact le_trans hstep (le_trans (le_max_left _ _) (le_max_right _ _))
  have hbu'' : ∀ x, |u'' x| ≤ Bmax := by
    intro x
    have h : |u'' x| = |deriv (deriv R) (x / Real.sqrt c)| / c := by
      rw [hu''def]
      simp only
      rw [abs_div, abs_of_pos hc]
    rw [h]
    have hstep : |deriv (deriv R) (x / Real.sqrt c)| / c ≤ B / c := by
      gcongr
      exact hBR'' _
    exact le_trans hstep (le_trans (le_max_right _ _) (le_max_right _ _))
  -- the exact prolate-to-oscillator identity
  have heq : ∀ x, hermiteSLAction u x + (c * (signedModeRadialData a n).s) * u x
      = (x ^ 2 * u'' x + 2 * x * u' x) / c := by
    intro x
    have h := prolateHermiteRescale_radial_defect hc heig x
    rw [← hueq] at h
    rw [hderiv1] at h
    have h2 : deriv u' = u'' := by
      funext ξ
      exact (hu' ξ).deriv
    rw [h2] at h
    rw [hs]
    exact h
  refine ⟨Bmax, hBmax0, fun m hne => ?_⟩
  have hmain := abs_sub_ladder_le_of_bounded (u := u) (u' := u') (u'' := u'') (c := c)
    (μ := c * (signedModeRadialData a n).s) (B := Bmax) m hcne hcu hcu' hcu'' hu hu'
    hbu hbu' hbu'' heq hne
  rwa [abs_of_pos hc] at hmain

/-- **The pin with an externally supplied value bound.**  Only the bound on the profile itself
enters the estimate; the bounds on its derivatives are used solely to discharge integrability. -/
theorem abs_signedMode_scaledSeparation_sub_rung_le {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hvalue : evenProlateSignedValue a n ≠ 0) (m : ℕ) {Bval : ℝ}
    (hBval : ∀ x, |signedModeRescaledProfile a n x| ≤ Bval)
    (hne : (∫ x, signedModeRescaledProfile a n x * hermiteFun m x) ≠ 0) :
    |signedModeRadialBandwidth a * (signedModeRadialData a n).s - (2 * m + 1)|
      ≤ Bval * (∫ x, |prolateDefectWeight m x|)
          / (signedModeRadialBandwidth a
              * |∫ x, signedModeRescaledProfile a n x * hermiteFun m x|) := by
  classical
  have hc : 0 < signedModeRadialBandwidth a := signedModeRadialBandwidth_pos ha
  set c : ℝ := signedModeRadialBandwidth a with hcdef
  have hcne : c ≠ 0 := hc.ne'
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  set R : ℝ → ℝ := (signedModeRadialData a n).R with hRdef
  have hD := signedModeRadialData_isExact ha n hvalue
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R := hD.2.2.2.2.2.1
  have heig : ∀ x : ℝ, prolateSLAction c R x = (signedModeRadialData a n).chi * R x :=
    hD.2.2.2.2.2.2.2.2.2.1
  have hs : (signedModeRadialData a n).s
      = radialSeparationRatio c (signedModeRadialData a n).chi :=
    hD.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨B, hB0, hBR, hBR', hBR''⟩ := exists_bound_signedModeRadialData_R ha n hvalue
  have hdiff : Differentiable ℝ R := (contDiff_infty_iff_deriv.mp hsm).1
  have hsmd : ContDiff ℝ ∞ (deriv R) := (contDiff_infty_iff_deriv.mp hsm).2
  have hdiff2 : Differentiable ℝ (deriv R) := (contDiff_infty_iff_deriv.mp hsmd).1
  have hsmd2 : ContDiff ℝ ∞ (deriv (deriv R)) := (contDiff_infty_iff_deriv.mp hsmd).2
  set u : ℝ → ℝ := signedModeRescaledProfile a n with hudef
  set u' : ℝ → ℝ := fun ξ => deriv R (ξ / Real.sqrt c) / Real.sqrt c with hu'def
  set u'' : ℝ → ℝ := fun ξ => deriv (deriv R) (ξ / Real.sqrt c) / c with hu''def
  have hueq : u = prolateHermiteRescale c R := rfl
  have hderiv1 : deriv u = u' := by
    rw [hueq, hu'def]
    exact deriv_prolateHermiteRescale hc hdiff
  have hu : ∀ x, HasDerivAt u (u' x) x := by
    intro x
    rw [hueq]
    exact hasDerivAt_prolateHermiteRescale hc hdiff x
  have hu' : ∀ x, HasDerivAt u' (u'' x) x := by
    intro x
    have h := hasDerivAt_deriv_prolateHermiteRescale hc hdiff hdiff2 x
    rw [← hueq, hderiv1] at h
    exact h
  have hinner : Continuous fun ξ : ℝ => ξ / Real.sqrt c :=
    continuous_id.div_const _
  have hcu : Continuous u := by
    rw [hueq]
    exact (hsm.continuous).comp hinner
  have hcu' : Continuous u' := by
    rw [hu'def]
    exact ((hsmd.continuous).comp hinner).div_const _
  have hcu'' : Continuous u'' := by
    rw [hu''def]
    exact ((hsmd2.continuous).comp hinner).div_const _
  -- the three uniform bounds after rescaling
  set Bmax : ℝ := max B (max (B / Real.sqrt c) (B / c)) with hBmaxdef
  have hBmax0 : 0 ≤ Bmax := le_trans hB0 (le_max_left _ _)
  have hbu : ∀ x, |u x| ≤ Bmax := fun x =>
    le_trans (hBR (x / Real.sqrt c)) (le_max_left _ _)
  have hbu' : ∀ x, |u' x| ≤ Bmax := by
    intro x
    have h : |u' x| = |deriv R (x / Real.sqrt c)| / Real.sqrt c := by
      rw [hu'def]
      simp only
      rw [abs_div, abs_of_pos hsc]
    rw [h]
    have hstep : |deriv R (x / Real.sqrt c)| / Real.sqrt c ≤ B / Real.sqrt c := by
      gcongr
      exact hBR' _
    exact le_trans hstep (le_trans (le_max_left _ _) (le_max_right _ _))
  have hbu'' : ∀ x, |u'' x| ≤ Bmax := by
    intro x
    have h : |u'' x| = |deriv (deriv R) (x / Real.sqrt c)| / c := by
      rw [hu''def]
      simp only
      rw [abs_div, abs_of_pos hc]
    rw [h]
    have hstep : |deriv (deriv R) (x / Real.sqrt c)| / c ≤ B / c := by
      gcongr
      exact hBR'' _
    exact le_trans hstep (le_trans (le_max_right _ _) (le_max_right _ _))
  -- the exact prolate-to-oscillator identity
  have heq : ∀ x, hermiteSLAction u x + (c * (signedModeRadialData a n).s) * u x
      = (x ^ 2 * u'' x + 2 * x * u' x) / c := by
    intro x
    have h := prolateHermiteRescale_radial_defect hc heig x
    rw [← hueq] at h
    rw [hderiv1] at h
    have h2 : deriv u' = u'' := by
      funext ξ
      exact (hu' ξ).deriv
    rw [h2] at h
    rw [hs]
    exact h
  have hmain := abs_sub_ladder_le_of_bounded (u := u) (u' := u') (u'' := u'') (c := c)
    (μ := c * (signedModeRadialData a n).s) (B := Bval) (B₂ := Bmax) m hcne hcu hcu' hcu'' hu hu'
    hBval hbu' hbu'' heq hne
  rwa [abs_of_pos hc] at hmain

end RHTower

end
