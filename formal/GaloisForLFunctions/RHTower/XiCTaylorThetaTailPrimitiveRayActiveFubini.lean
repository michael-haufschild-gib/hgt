import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayChangeOfVariables
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Moving-fibre Fubini form of the primitive-ray active chamber

The arithmetic-polar change of variables produces a two-dimensional active chamber.  The
pointwise endpoint laws already identify each angular slice of that chamber.  This file packages
those laws as an exact set identity and then gives the corresponding Fubini formula for an
arbitrary jointly integrable kernel.  No endpoint or finite-section term is separated and no sign
hypothesis is introduced.
-/

open Complex Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- The active primitive-ray chamber is exactly the family of swept open angular intervals. -/
theorem thetaCuspPrimitiveRayActiveSet_eq_movingIoo (a b : ℕ) :
    thetaCuspPrimitiveRayActiveSet a b =
      {q : ℝ × ℝ |
        q.2 ∈ Ioo
          (thetaCuspPrimitiveRayCorePolarLowerEndpoint q.1
            (-Real.log (a : ℝ)))
          (thetaCuspPrimitiveRayCorePolarUpperEndpoint q.1
            (-Real.log (b : ℝ)))} := by
  ext q
  constructor
  · rintro ⟨hu0, hu1, hx, hy⟩
    exact (thetaCuspPrimitiveRayArithmeticPolar_activeDomain_iff
      a b q.1 hu0 hu1).2 ⟨hx, hy⟩
  · intro hq
    have hlower0 :
        0 < thetaCuspPrimitiveRayCorePolarLowerEndpoint q.1
          (-Real.log (a : ℝ)) := by
      unfold thetaCuspPrimitiveRayCorePolarLowerEndpoint
      positivity
    have hupper1 :
        thetaCuspPrimitiveRayCorePolarUpperEndpoint q.1
            (-Real.log (b : ℝ)) < 1 := by
      unfold thetaCuspPrimitiveRayCorePolarUpperEndpoint
      have hexp : 0 < Real.exp (-2 * (q.1 + -Real.log (b : ℝ))) := Real.exp_pos _
      linarith
    have hu0 : 0 < q.2 := hlower0.trans hq.1
    have hu1 : q.2 < 1 := hq.2.trans hupper1
    have hxy := (thetaCuspPrimitiveRayArithmeticPolar_activeDomain_iff
      a b q.1 hu0 hu1).1 hq
    exact ⟨hu0, hu1, hxy.1, hxy.2⟩

/-- **Joint active-fibre Fubini bridge.**  Under the single natural absolute-integrability
condition on the chamber-restricted kernel, integration over the full active chamber is exactly
the radial integral of the moving angular-window integrals. -/
theorem integral_thetaCuspPrimitiveRayActiveSet_eq_movingIoo
    (a b : ℕ) (f : ℝ × ℝ → ℝ)
    (hf : Integrable
      ((thetaCuspPrimitiveRayActiveSet a b).indicator f)
      (volume.prod volume)) :
    (∫ q in thetaCuspPrimitiveRayActiveSet a b, f q) =
      ∫ r : ℝ,
        ∫ u in Ioo
          (thetaCuspPrimitiveRayCorePolarLowerEndpoint r
            (-Real.log (a : ℝ)))
          (thetaCuspPrimitiveRayCorePolarUpperEndpoint r
            (-Real.log (b : ℝ))),
          f (r, u) := by
  rw [← integral_indicator (measurableSet_thetaCuspPrimitiveRayActiveSet a b),
    Measure.volume_eq_prod, integral_prod _ hf]
  apply integral_congr_ae
  filter_upwards with r
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with u
  have hmem :
      (r, u) ∈ thetaCuspPrimitiveRayActiveSet a b ↔
        u ∈ Ioo
          (thetaCuspPrimitiveRayCorePolarLowerEndpoint r
            (-Real.log (a : ℝ)))
          (thetaCuspPrimitiveRayCorePolarUpperEndpoint r
            (-Real.log (b : ℝ))) := by
    rw [thetaCuspPrimitiveRayActiveSet_eq_movingIoo]
    rfl
  by_cases hactive : (r, u) ∈ thetaCuspPrimitiveRayActiveSet a b
  · simp [hactive, hmem.mp hactive]
  · have hwindow :
        u ∉ Ioo
          (thetaCuspPrimitiveRayCorePolarLowerEndpoint r
            (-Real.log (a : ℝ)))
          (thetaCuspPrimitiveRayCorePolarUpperEndpoint r
            (-Real.log (b : ℝ))) := by
      exact fun hu => hactive (hmem.mpr hu)
    simp [hactive, hwindow]

end

end RHTower
