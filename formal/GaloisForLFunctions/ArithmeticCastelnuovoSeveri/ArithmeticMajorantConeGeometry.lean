import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticMajorantsSupplyBezout
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PositiveQuadraticSourceCones

/-!
# Convex geometry of the aperture arithmetic majorants

The explicit positive quadratic reserve defines a pointed generating convex cone
on every positive-aperture cycle space. Its Bézout and ample properties concern
the original intersection pairing; its Riemann–Roch obstruction remains unchanged.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Bilinear form of the aperture arithmetic majorant. -/
def arithmeticMajorantBilinear (r : ℝ) :
    (ℝ × ℝ × realTestsAt r) →ₗ[ℝ] (ℝ × ℝ × realTestsAt r) →ₗ[ℝ] ℝ :=
  (scalingSubsurface (realTestsAt r)).defectLinearMap +
    l2ReserveBilinear (2 * (10 + 72 * Real.exp r)) (realTestsAt r)

theorem arithmeticMajorantBilinear_symm (r : ℝ) (x y : ℝ × ℝ × realTestsAt r) :
    arithmeticMajorantBilinear r x y = arithmeticMajorantBilinear r y x := by
  change (scalingSubsurface (realTestsAt r)).defect x y + l2ReserveBilinear _ _ x y =
    (scalingSubsurface (realTestsAt r)).defect y x + l2ReserveBilinear _ _ y x
  rw [PolarSurface.defect_comm, l2ReserveBilinear_symm]

theorem arithmeticMajorantBilinear_self {r : ℝ} (hr : 0 < r) (x : ℝ × ℝ × realTestsAt r) :
    arithmeticMajorantBilinear r x x = arithmeticMajorantSourceEnergy r x := by
  change (scalingSubsurface (realTestsAt r)).defect x x + l2ReserveBilinear _ _ x x = _
  rw [l2ReserveBilinear_self, arithmeticMajorantSourceEnergy,
    criticalDeficitSourceEnergy_eq_defect hr.le le_rfl]

private theorem majorant_cone_eq {r : ℝ} (hr : 0 < r) :
    arithmeticMajorantSourceCone r = (scalingSubsurface (realTestsAt r)).sourceCone
      (fun x => arithmeticMajorantBilinear r x x) := by
  unfold arithmeticMajorantSourceCone
  congr 1
  exact funext fun x => (arithmeticMajorantBilinear_self hr x).symm

theorem arithmeticMajorantSourceCone_add_closed {r : ℝ} (hr : 0 < r) :
    ∀ x ∈ arithmeticMajorantSourceCone r, ∀ y ∈ arithmeticMajorantSourceCone r,
      x + y ∈ arithmeticMajorantSourceCone r := by
  rw [majorant_cone_eq hr]
  exact (scalingSubsurface (realTestsAt r)).sourceCone_quadratic_add_closed
    (arithmeticMajorantBilinear r) (arithmeticMajorantBilinear_symm r)
    (fun x => by rw [arithmeticMajorantBilinear_self hr]; exact arithmeticMajorantSourceEnergy_nonneg hr x)

theorem arithmeticMajorantSourceCone_smul {r : ℝ} (hr : 0 < r)
    {a : ℝ} (ha : 0 ≤ a) {x : ℝ × ℝ × realTestsAt r} (hx : x ∈ arithmeticMajorantSourceCone r) :
    a • x ∈ arithmeticMajorantSourceCone r := by
  rw [majorant_cone_eq hr] at hx ⊢
  exact (scalingSubsurface (realTestsAt r)).smul_mem_sourceCone_quadratic
    (arithmeticMajorantBilinear r) ha hx

theorem zero_mem_arithmeticMajorantSourceCone {r : ℝ} (hr : 0 < r) :
    (0 : ℝ × ℝ × realTestsAt r) ∈ arithmeticMajorantSourceCone r := by
  rw [majorant_cone_eq hr]
  exact (scalingSubsurface (realTestsAt r)).zero_mem_sourceCone_quadratic (arithmeticMajorantBilinear r)

/-- Each arithmetic majorant effective set is convex at every positive aperture. -/
theorem arithmeticMajorantSourceCone_convex {r : ℝ} (hr : 0 < r) :
    Convex ℝ (arithmeticMajorantSourceCone r) := by
  rw [majorant_cone_eq hr]
  exact (scalingSubsurface (realTestsAt r)).sourceCone_quadratic_convex
    (arithmeticMajorantBilinear r) (arithmeticMajorantBilinear_symm r)
    (fun x => by rw [arithmeticMajorantBilinear_self hr]; exact arithmeticMajorantSourceEnergy_nonneg hr x)

/-- Actual strict ampleness makes the arithmetic majorant cone pointed. -/
theorem arithmeticMajorantSourceCone_pointed {r : ℝ} (hr : 0 < r)
    {x : ℝ × ℝ × realTestsAt r} (hx : x ∈ arithmeticMajorantSourceCone r)
    (hnx : -x ∈ arithmeticMajorantSourceCone r) : x = 0 := by
  apply arithmeticMajorantSourceCone_ample_zero hr x hx
  change x ∈ (scalingSubsurface (realTestsAt r)).sourceCone (arithmeticMajorantSourceEnergy r) at hx
  change -x ∈ (scalingSubsurface (realTestsAt r)).sourceCone (arithmeticMajorantSourceEnergy r) at hnx
  rw [PolarSurface.mem_sourceCone_iff] at hx hnx
  have hnH : 0 ≤ -((scalingSubsurface (realTestsAt r)).pair x)
      (scalingSubsurface (realTestsAt r)).H := by
    calc
      0 ≤ ((scalingSubsurface (realTestsAt r)).pair (-x))
          (scalingSubsurface (realTestsAt r)).H := hnx.1
      _ = _ := ((scalingSubsurface (realTestsAt r)).pair.flip
        (scalingSubsurface (realTestsAt r)).H).map_neg x
  have hnV : 0 ≤ -((scalingSubsurface (realTestsAt r)).pair x)
      (scalingSubsurface (realTestsAt r)).V := by
    calc
      0 ≤ ((scalingSubsurface (realTestsAt r)).pair (-x))
          (scalingSubsurface (realTestsAt r)).V := hnx.2.1
      _ = _ := ((scalingSubsurface (realTestsAt r)).pair.flip
        (scalingSubsurface (realTestsAt r)).V).map_neg x
  rw [PolarSurface.pair_ample]
  linarith only [hx.1, hx.2.1, hnH, hnV]

/-- Every aperture cycle is a difference of two arithmetic effective cycles. -/
theorem arithmeticMajorantSourceCone_generating {r : ℝ} (hr : 0 < r)
    (x : ℝ × ℝ × realTestsAt r) :
    ∃ y ∈ arithmeticMajorantSourceCone r, ∃ z ∈ arithmeticMajorantSourceCone r, x = y - z := by
  apply (scalingSubsurface (realTestsAt r)).sourceCone_generating (Φ := arithmeticMajorantSourceEnergy r) ?_ ?_ x
  · intro u a b
    have hs : (u + a • (scalingSubsurface (realTestsAt r)).H +
        b • (scalingSubsurface (realTestsAt r)).V).2.2 = u.2.2 := by
      change u.2.2 + a • (0 : realTestsAt r) + b • 0 = u.2.2
      simp only [smul_zero, add_zero]
    simp only [arithmeticMajorantSourceEnergy, criticalDeficitSourceEnergy, l2SourceEnergy, hs]
  · rw [← arithmeticMajorantBilinear_self hr]
    simp only [map_zero, le_refl]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.arithmeticMajorantSourceCone_add_closed
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.arithmeticMajorantSourceCone_convex
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.arithmeticMajorantSourceCone_pointed
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.arithmeticMajorantSourceCone_generating
