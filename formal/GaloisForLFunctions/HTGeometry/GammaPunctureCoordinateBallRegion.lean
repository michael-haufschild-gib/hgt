import GaloisForLFunctions.HTGeometry.GammaPunctureLaurentCover

/-!
# The Gamma-puncture ball condition is a half-plane

The capacity and tangent laws of the puncture atlas are stated for base points whose Laurent
coordinate lies in a small ball about the origin, and that hypothesis was never produced.  It is
not an implicit condition: the Laurent coordinate is `exp z`, so its modulus is `exp (Re z)`, and
membership in the closed ball of radius `r` is exactly the half-plane `Re z ≤ log r`.

The region is therefore explicit, nonempty for every positive radius, and invariant under the deck
translation `z ↦ z + 2πi` — which is the invariance the atlas laws themselves record for the
sheets.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- The modulus of the Laurent coordinate is the exponential of the real part. -/
@[simp] theorem norm_gammaPunctureCoordinate (z : ℂ) :
    ‖gammaPunctureCoordinate z‖ = Real.exp z.re := by
  rw [gammaPunctureCoordinate, Complex.norm_exp]

/-- **The ball condition is a half-plane.**  The Laurent coordinate lies in the closed ball of
radius `r > 0` exactly when the real part is at most `log r`. -/
theorem gammaPunctureCoordinate_mem_closedBall_iff {z : ℂ} {r : ℝ} (hr : 0 < r) :
    gammaPunctureCoordinate z ∈ Metric.closedBall (0 : ℂ) r ↔ z.re ≤ Real.log r := by
  rw [mem_closedBall_zero_iff, norm_gammaPunctureCoordinate]
  exact (Real.le_log_iff_exp_le hr).symm

/-- The producer used by the atlas laws: a sufficiently negative real part puts the Laurent
coordinate in the quarter ball. -/
theorem gammaPunctureCoordinate_mem_closedBall_quarter {z : ℂ}
    (hz : z.re ≤ Real.log (1 / 4)) :
    gammaPunctureCoordinate z ∈ Metric.closedBall (0 : ℂ) (1 / 4) :=
  (gammaPunctureCoordinate_mem_closedBall_iff (by norm_num)).mpr hz

/-- The region is nonempty for every positive radius. -/
theorem exists_gammaPunctureCoordinate_mem_closedBall {r : ℝ} (hr : 0 < r) :
    ∃ z : ℂ, gammaPunctureCoordinate z ∈ Metric.closedBall (0 : ℂ) r := by
  refine ⟨(Real.log r : ℂ), ?_⟩
  rw [gammaPunctureCoordinate_mem_closedBall_iff hr]
  simp

/-- The region is invariant under the deck translation of the logarithmic cover. -/
theorem gammaPunctureCoordinate_mem_closedBall_deck {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : gammaPunctureCoordinate z ∈ Metric.closedBall (0 : ℂ) r) :
    gammaPunctureCoordinate (z + 2 * (Real.pi : ℂ) * Complex.I) ∈
      Metric.closedBall (0 : ℂ) r := by
  rw [gammaPunctureCoordinate_mem_closedBall_iff hr] at hz ⊢
  simpa using hz

end GaloisForLFunctions.HTGeometry
