import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphic
import GaloisForLFunctions.HTGeometry.BesselOrderPositiveComparison

/-!
# Nonvanishing cyclic Bessel determinant

The Schlaefli kernel at order one strictly dominates the order-zero kernel on the positive
integration ray.  Evaluating the cyclic Casoratian at order `-1` therefore proves that the
state vector of the actual Bessel solution and its translate are pointwise nondegenerate in
the meromorphic field.  Because the companion matrix is nonautonomous, this cyclic pair is
not asserted to be two solution columns of one common system.
-/

open Filter MeasureTheory Set Topology

namespace GaloisForLFunctions.HTGeometry

open Bottcher

noncomputable section

local instance cyclicDeterminantDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

/-- Casoratian of two consecutive translates of the actual meromorphic Bessel solution. -/
def modifiedBesselKOrderCyclicDetMero (s : ℝ) (hs : 0 < s) :
    meroField (Set.univ : Set ℂ) :=
  modifiedBesselKOrderMero s hs * modifiedBesselKOrderShiftMero s hs 2 -
    modifiedBesselKOrderShiftMero s hs 1 * modifiedBesselKOrderShiftMero s hs 1

/-- The cyclic Bessel Casoratian is nonzero.  At order `-1` it is
`K₁(s)² - K₀(s)² > 0`. -/
theorem modifiedBesselKOrderCyclicDetMero_ne_zero
    {s : ℝ} (hs : 0 < s) :
    modifiedBesselKOrderCyclicDetMero s hs ≠ 0 := by
  let f : ℂ → ℂ := fun z =>
    modifiedBesselKOrder s z * modifiedBesselKOrder s (z + 2) -
      modifiedBesselKOrder s (z + 1) * modifiedBesselKOrder s (z + 1)
  have hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    ((analyticOnNhd_modifiedBesselKOrder hs).mul
      (analyticOnNhd_comp_addTranslation
        (analyticOnNhd_modifiedBesselKOrder hs) 2)).sub
      ((analyticOnNhd_comp_addTranslation
        (analyticOnNhd_modifiedBesselKOrder hs) 1).mul
      (analyticOnNhd_comp_addTranslation
        (analyticOnNhd_modifiedBesselKOrder hs) 1))
  have hmero : modifiedBesselKOrderCyclicDetMero s hs =
      analyticMeroElement f hf := by
    rw [modifiedBesselKOrderCyclicDetMero, modifiedBesselKOrderMero,
      modifiedBesselKOrderShiftMero, modifiedBesselKOrderShiftMero,
      ← analyticMeroElement_mul, ← analyticMeroElement_mul,
      ← analyticMeroElement_sub]
  intro hzero
  rw [hmero] at hzero
  have hpoint := (analyticMeroElement_eq_zero_iff hf).1 hzero (-1) (Set.mem_univ _)
  have hlt := realModifiedBesselKOrder_zero_lt_one hs
  have hpos := realModifiedBesselKOrder_pos hs 0
  have hK1 : modifiedBesselKOrder s (1 : ℂ) =
      (realModifiedBesselKOrder s 1 : ℂ) := by
    simpa using modifiedBesselKOrder_ofReal hs 1
  have hK0 : modifiedBesselKOrder s (0 : ℂ) =
      (realModifiedBesselKOrder s 0 : ℂ) := by
    simpa using modifiedBesselKOrder_ofReal hs 0
  simp only [f] at hpoint
  rw [show (-1 : ℂ) + 2 = 1 by norm_num,
    show (-1 : ℂ) + 1 = 0 by norm_num,
    modifiedBesselKOrder_neg s 1,
    hK1, hK0] at hpoint
  apply_fun Complex.re at hpoint
  norm_num at hpoint
  nlinarith

end

end GaloisForLFunctions.HTGeometry
