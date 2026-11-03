import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.TheTateTwistTiltsTheJumpMeasure

/-!
# The imaginary Tate twist is unitary

The Tate twist by a real dimension `k` moves the zeros of `ζ` horizontally, to `ρ ± k`, and is
negative on every window in large dimension (`exists_window_tateTwistedForm_neg`). The twist by an
imaginary dimension `iθ` is the unitary twist `n^{−iθ}` (the archimedean character): it moves the zeros
along the critical line. Its window form is Weil's form of the modulated test `H e^{iθu}`,

`Q^{(iθ)}(H) = Q(H cos(θ·)) + Q(H sin(θ·))` (`imagTwistedForm`).

* **The modulation acts on autocorrelations by `cos(θt)`** (`autoCorr_cos_add_autoCorr_sin`), and on
  the jump measure by `cos(θt)` (`imagTwistedForm_eq_tilted`): archimedean rate `ω(t)cos(θt)`, prime
  rate `Λ(n)n^{−1/2}cos(θ log n) = Re Λ(n)n^{−1/2−iθ}`. Real dimension tilts by `cosh(kt)`, imaginary
  dimension by `cos(θt)`.
* **It preserves positivity window by window** (`imagTwistedForm_nonneg_of_window`): if Weil's form is
  nonnegative on a window, so is every imaginary twist; at `θ = 0` it is Weil's form
  (`imagTwistedForm_zero`).

So positivity is a property of the line `Re k = 0` of complex Tate dimension: unitary along it,
destroyed off it in large real dimension. Dimension zero is the only real point where positivity is
available, and the positivity there is invariant under the unitary (imaginary) directions — the
dimension-zero geometry of `Spec ℤ` is a one-dimensional line of positive forms, not a point.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis ArithmeticCriticalityTheory
open CohomologyOfWindowsOfSpecZ _root_.RHTower

/-- The **imaginary Tate twist** `Q^{(iθ)}(H) = Q(H cos(θ·)) + Q(H sin(θ·))`: Weil's form of the
modulated test `H e^{iθu}`. -/
def imagTwistedForm (θ : ℝ) (H : ℝ → ℝ) : ℝ :=
  weilQuad (fun u => H u * Real.cos (θ * u)) + weilQuad (fun u => H u * Real.sin (θ * u))

theorem imagTwistedForm_zero (H : ℝ → ℝ) : imagTwistedForm 0 H = weilQuad H := by
  have h0 : weilQuad (fun _ : ℝ => (0 : ℝ)) = 0 := by
    have hz : (fun _ : ℝ => (0 : ℝ)) = (0 : ℝ) • H := by funext u; simp
    rw [hz]
    show weilPair ((0 : ℝ) • H) ((0 : ℝ) • H) = 0
    rw [weilPair_smul_left, zero_mul]
  simp only [imagTwistedForm, zero_mul, Real.cos_zero, mul_one, Real.sin_zero, mul_zero]
  rw [h0, add_zero]

/-- **The modulation acts on autocorrelations by `cos(θt)`.** -/
theorem autoCorr_cos_add_autoCorr_sin {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (θ t : ℝ) :
    autoCorr (fun x => F x * Real.cos (θ * x)) t + autoCorr (fun x => F x * Real.sin (θ * x)) t =
      Real.cos (θ * t) * autoCorr F t := by
  unfold autoCorr
  have h1 : Integrable fun x => F x * Real.cos (θ * x) * (F (x + t) * Real.cos (θ * (x + t))) :=
    (by fun_prop : Continuous fun x => F x * Real.cos (θ * x) * (F (x + t) *
      Real.cos (θ * (x + t)))).integrable_of_hasCompactSupport hFc.mul_right.mul_right
  have h2 : Integrable fun x => F x * Real.sin (θ * x) * (F (x + t) * Real.sin (θ * (x + t))) :=
    (by fun_prop : Continuous fun x => F x * Real.sin (θ * x) * (F (x + t) *
      Real.sin (θ * (x + t)))).integrable_of_hasCompactSupport hFc.mul_right.mul_right
  rw [← integral_add h1 h2, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  have h := Real.cos_sub (θ * (x + t)) (θ * x)
  rw [show θ * (x + t) - θ * x = θ * t by ring] at h
  rw [h]
  ring

/-- **Imaginary twists preserve positivity window by window.** -/
theorem imagTwistedForm_nonneg_of_window {A : ℝ}
    (hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G) {H : ℝ → ℝ} (hH : IsWindowTest A H)
    (θ : ℝ) : 0 ≤ imagTwistedForm θ H := by
  have hc : IsWindowTest A fun u => H u * Real.cos (θ * u) :=
    ⟨hH.contDiff.mul (by fun_prop), fun y hy => by rw [hH.vanish y hy, zero_mul]⟩
  have hs : IsWindowTest A fun u => H u * Real.sin (θ * u) :=
    ⟨hH.contDiff.mul (by fun_prop), fun y hy => by rw [hH.vanish y hy, zero_mul]⟩
  exact add_nonneg (hpos _ hc) (hpos _ hs)

/-- The imaginary tilt of the archimedean jumps: `∫_{t>0} ω(t)(2‖H‖² − 2cos(θt)c_H(t)) dt`. -/
def imagTiltedLevyEnergy (θ : ℝ) (H : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), archLevyDensity t * (2 * (∫ u, H u ^ 2) - 2 * Real.cos (θ * t) * autoCorr H t)

/-- The imaginary tilt of the prime jumps: `Σ_n Λ(n)n^{−1/2}cos(θ log n)(c_H(−log n) + c_H(log n))`. -/
def imagTiltedPrimeSum (θ : ℝ) (H : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n *
    (Real.cos (θ * Real.log n) * (autoCorr H (-Real.log n) + autoCorr H (Real.log n)))

/-- The pole part of the imaginary twist. -/
def imagTiltedPole (θ : ℝ) (H : ℝ → ℝ) : ℝ :=
  (2 * coshHalfMoment (fun u => H u * Real.cos (θ * u)) ^ 2 -
      2 * sinhHalfMoment (fun u => H u * Real.cos (θ * u)) ^ 2) +
    (2 * coshHalfMoment (fun u => H u * Real.sin (θ * u)) ^ 2 -
      2 * sinhHalfMoment (fun u => H u * Real.sin (θ * u)) ^ 2)

/-- **The imaginary twist modulates the jump measure by `cos(θt)`.** -/
theorem imagTwistedForm_eq_tilted {H : ℝ → ℝ} (hH : H ∈ realTests) (θ : ℝ) :
    imagTwistedForm θ H = 2 * gammaHardyPhaseRate 0 * (∫ u, H u ^ 2) + imagTiltedLevyEnergy θ H -
      imagTiltedPrimeSum θ H + imagTiltedPole θ H := by
  have hc : (fun u => H u * Real.cos (θ * u)) ∈ realTests := mul_mem_realTests hH (by fun_prop)
  have hs : (fun u => H u * Real.sin (θ * u)) ∈ realTests := mul_mem_realTests hH (by fun_prop)
  set Hc : ℝ → ℝ := fun u => H u * Real.cos (θ * u) with hHc
  set Hs : ℝ → ℝ := fun u => H u * Real.sin (θ * u) with hHs
  have hsq : ∀ F : ℝ → ℝ, F ∈ realTests → Integrable fun u => F u ^ 2 := fun F hF =>
    (hF.1.continuous.pow 2).integrable_of_hasCompactSupport
      (by simpa [sq] using hF.2.mul_right (f' := F))
  have hnorm : (∫ u, Hc u ^ 2) + (∫ u, Hs u ^ 2) = ∫ u, H u ^ 2 := by
    rw [← integral_add (hsq Hc hc) (hsq Hs hs)]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hHc, hHs]
    have := Real.cos_sq_add_sin_sq (θ * u)
    nlinarith [this]
  have hlevy : levyEnergy Hc + levyEnergy Hs = imagTiltedLevyEnergy θ H := by
    rw [levyEnergy, levyEnergy, ← integral_add (integrableOn_levyIntegrand hc.1 hc.2)
      (integrableOn_levyIntegrand hs.1 hs.2), imagTiltedLevyEnergy]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [integral_sub_shift_sq hc.1.continuous hc.2, integral_sub_shift_sq hs.1.continuous hs.2,
      ← hnorm]
    have hac : autoCorr Hc t + autoCorr Hs t = Real.cos (θ * t) * autoCorr H t :=
      autoCorr_cos_add_autoCorr_sin hH.1.continuous hH.2 θ t
    linear_combination (-2 * archLevyDensity t) * hac
  have hprime : primeSum Hc + primeSum Hs = imagTiltedPrimeSum θ H := by
    rw [primeSum, primeSum, ← (summable_primeSum_terms hc.2).tsum_add
      (summable_primeSum_terms hs.2), imagTiltedPrimeSum]
    refine tsum_congr fun n => ?_
    have e1 : ∀ F : ℝ → ℝ, (∫ t, F t * F (t - Real.log n)) = autoCorr F (-Real.log n) :=
      fun F => by simp only [autoCorr, sub_eq_add_neg]
    have hac1 : autoCorr Hc (-Real.log n) + autoCorr Hs (-Real.log n) =
        Real.cos (θ * Real.log n) * autoCorr H (-Real.log n) := by
      have := autoCorr_cos_add_autoCorr_sin hH.1.continuous hH.2 θ (-Real.log n)
      rwa [mul_neg, Real.cos_neg] at this
    have hac2 : autoCorr Hc (Real.log n) + autoCorr Hs (Real.log n) =
        Real.cos (θ * Real.log n) * autoCorr H (Real.log n) :=
      autoCorr_cos_add_autoCorr_sin hH.1.continuous hH.2 θ (Real.log n)
    rw [e1 Hc, e1 Hs]
    show vonMangoldtAtom n * (autoCorr Hc (-Real.log n) + autoCorr Hc (Real.log n)) +
      vonMangoldtAtom n * (autoCorr Hs (-Real.log n) + autoCorr Hs (Real.log n)) = _
    linear_combination vonMangoldtAtom n * hac1 + vonMangoldtAtom n * hac2
  rw [imagTwistedForm, weilQuad_eq hc.1 hc.2, weilQuad_eq hs.1 hs.2, imagTiltedPole, ← hlevy,
    ← hprime, ← hnorm]
  ring

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ
