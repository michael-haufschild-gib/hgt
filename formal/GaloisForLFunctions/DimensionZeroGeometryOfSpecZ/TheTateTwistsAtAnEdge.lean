import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.ZeroModesOfAWindowAreItsRadical
import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.TheImaginaryTateTwistIsUnitary

/-!
# The Tate twists at an edge

At a zero mode `H` of a nonnegative window (an edge of the positive cone) the radical property
(`weilPair_eq_zero_of_zeroMode`) removes every cross term between `H` and its corrections, and the
two kinds of Tate twist become explicit differences of nonnegative quantities:

* **Real dimension** (`tateTwistedForm_zeroMode`):
  `Q^{(k)}(H) = Q(H(cosh(k·) − 1)) − Q(H sinh(k·))`, hence `Q^{(k)}(H) ≤ Q(H(cosh(k·) − 1))`
  (`tateTwistedForm_zeroMode_le`).
* **Imaginary dimension** (`imagTwistedForm_zeroMode`):
  `Q^{(iθ)}(H) = Q(H(cos(θ·) − 1)) + Q(H sin(θ·))`.

At an edge the real and imaginary twists differ exactly in the sign in front of the odd correction:
the imaginary twist adds the odd correction's energy, the real twist subtracts it. The even
correction `H(cosh(k·) − 1)` is of fourth order in `k` and the odd one `H sinh(k·)` of second order, so
the real twist pushes an edge into negativity at second order unless the odd correction `uH` is itself
a zero mode, while the imaginary twist keeps it nonnegative.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

open ArithmeticCastelnuovoSeveri CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis

variable {A : ℝ} {H : ℝ → ℝ}

theorem isWindowTest_mul {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hH : IsWindowTest A H) :
    IsWindowTest A fun u => H u * φ u :=
  ⟨hH.contDiff.mul hφ, fun y hy => by rw [hH.vanish y hy, zero_mul]⟩

/-- At a zero mode, Weil's form of `H + G` is Weil's form of `G`. -/
theorem weilQuad_add_zeroMode (hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G)
    (hH : IsWindowTest A H) (h0 : weilQuad H = 0) {G : ℝ → ℝ} (hG : IsWindowTest A G) :
    weilQuad (fun u => H u + G u) = weilQuad G := by
  have h := weilQuad_plane (mem_realTests_of_isWindowTest hH) (mem_realTests_of_isWindowTest hG) 1 1
  simp only [one_mul] at h
  rw [h, h0, weilPair_eq_zero_of_zeroMode hpos hH h0 hG]
  ring

/-- **The real Tate twist at an edge**: `Q^{(k)}(H) = Q(H(cosh(k·) − 1)) − Q(H sinh(k·))`. -/
theorem tateTwistedForm_zeroMode (hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G)
    (hH : IsWindowTest A H) (h0 : weilQuad H = 0) (k : ℝ) :
    tateTwistedForm k H = weilQuad (fun u => H u * (Real.cosh (k * u) - 1)) -
      weilQuad (fun u => H u * Real.sinh (k * u)) := by
  rw [tateTwistedForm_eq (mem_realTests_of_isWindowTest hH)]
  have hG := isWindowTest_mul (φ := fun u => Real.cosh (k * u) - 1) (by fun_prop) hH
  have e : (fun u => H u * Real.cosh (k * u)) = fun u => H u + H u * (Real.cosh (k * u) - 1) := by
    funext u; ring
  rw [e, weilQuad_add_zeroMode hpos hH h0 hG]

/-- At an edge the real Tate twist is at most the energy of the even correction. -/
theorem tateTwistedForm_zeroMode_le (hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G)
    (hH : IsWindowTest A H) (h0 : weilQuad H = 0) (k : ℝ) :
    tateTwistedForm k H ≤ weilQuad (fun u => H u * (Real.cosh (k * u) - 1)) := by
  rw [tateTwistedForm_zeroMode hpos hH h0]
  have := hpos _ (isWindowTest_mul (φ := fun u => Real.sinh (k * u)) (by fun_prop) hH)
  linarith

/-- **The imaginary Tate twist at an edge**: `Q^{(iθ)}(H) = Q(H(cos(θ·) − 1)) + Q(H sin(θ·))`. -/
theorem imagTwistedForm_zeroMode (hpos : ∀ G : ℝ → ℝ, IsWindowTest A G → 0 ≤ weilQuad G)
    (hH : IsWindowTest A H) (h0 : weilQuad H = 0) (θ : ℝ) :
    imagTwistedForm θ H = weilQuad (fun u => H u * (Real.cos (θ * u) - 1)) +
      weilQuad (fun u => H u * Real.sin (θ * u)) := by
  rw [imagTwistedForm]
  have hG := isWindowTest_mul (φ := fun u => Real.cos (θ * u) - 1) (by fun_prop) hH
  have e : (fun u => H u * Real.cos (θ * u)) = fun u => H u + H u * (Real.cos (θ * u) - 1) := by
    funext u; ring
  rw [e, weilQuad_add_zeroMode hpos hH h0 hG]

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ
