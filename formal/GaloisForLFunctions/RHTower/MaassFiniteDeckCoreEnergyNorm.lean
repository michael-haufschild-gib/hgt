import GaloisForLFunctions.RHTower.MaassFiniteDeckCoreStripEnergy

/-!
# Finite-deck Dirichlet energy in form coordinates

The invariant chart-gradient energy on the modular fundamental domain is
exactly the sum of the two `L²` gradient-coordinate norm squares.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The modular invariant energy is exactly the two derivative-coordinate
energies of the finite-deck form triple. -/
theorem integral_hyperbolicChartGradientDensity_eq_gradNormSq {N : ℕ}
    (F : formPreDomain N) :
    (∫ z in ModularGroup.fd,
      hyperbolicChartGradientDensity (F : ℍ → DeckSpace N) z) =
      ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
          (formPreDomain.memLp_gradX F)‖ ^ 2 +
      ‖toDeckL2 (hypGradY (F : ℍ → DeckSpace N))
          (formPreDomain.memLp_gradY F)‖ ^ 2 := by
  have hX : IntegrableOn (fun z => ‖hypGradX (F : ℍ → DeckSpace N) z‖ ^ 2)
      ModularGroup.fd volume :=
    (memLp_two_iff_integrable_sq_norm (formPreDomain.memLp_gradX F).aestronglyMeasurable).mp
      (formPreDomain.memLp_gradX F)
  have hY : IntegrableOn (fun z => ‖hypGradY (F : ℍ → DeckSpace N) z‖ ^ 2)
      ModularGroup.fd volume :=
    (memLp_two_iff_integrable_sq_norm (formPreDomain.memLp_gradY F).aestronglyMeasurable).mp
      (formPreDomain.memLp_gradY F)
  have hnormX :
      ‖toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
          (formPreDomain.memLp_gradX F)‖ ^ 2 =
        ∫ z in ModularGroup.fd, ‖hypGradX (F : ℍ → DeckSpace N) z‖ ^ 2 := by
    rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    calc
      (∫ z, ‖((toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
        (formPreDomain.memLp_gradX F) : DeckL2 N) : ℍ → DeckSpace N) z‖ ^ 2 ∂cellMeasure) =
          ∫ z, ‖hypGradX (F : ℍ → DeckSpace N) z‖ ^ 2 ∂cellMeasure := by
          apply integral_congr_ae
          filter_upwards [MemLp.coeFn_toLp (formPreDomain.memLp_gradX F)] with z hz
          change ‖(MemLp.toLp (hypGradX (F : ℍ → DeckSpace N))
            (formPreDomain.memLp_gradX F) : ℍ → DeckSpace N) z‖ ^ 2 = _
          rw [hz]
      _ = ∫ z in ModularGroup.fd, ‖hypGradX (F : ℍ → DeckSpace N) z‖ ^ 2 := by rfl
  have hnormY :
      ‖toDeckL2 (hypGradY (F : ℍ → DeckSpace N))
          (formPreDomain.memLp_gradY F)‖ ^ 2 =
        ∫ z in ModularGroup.fd, ‖hypGradY (F : ℍ → DeckSpace N) z‖ ^ 2 := by
    rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    calc
      (∫ z, ‖((toDeckL2 (hypGradY (F : ℍ → DeckSpace N))
        (formPreDomain.memLp_gradY F) : DeckL2 N) : ℍ → DeckSpace N) z‖ ^ 2 ∂cellMeasure) =
          ∫ z, ‖hypGradY (F : ℍ → DeckSpace N) z‖ ^ 2 ∂cellMeasure := by
          apply integral_congr_ae
          filter_upwards [MemLp.coeFn_toLp (formPreDomain.memLp_gradY F)] with z hz
          change ‖(MemLp.toLp (hypGradY (F : ℍ → DeckSpace N))
            (formPreDomain.memLp_gradY F) : ℍ → DeckSpace N) z‖ ^ 2 = _
          rw [hz]
      _ = ∫ z in ModularGroup.fd, ‖hypGradY (F : ℍ → DeckSpace N) z‖ ^ 2 := by rfl
  calc
    (∫ z in ModularGroup.fd,
      hyperbolicChartGradientDensity (F : ℍ → DeckSpace N) z) =
        ∫ z in ModularGroup.fd,
          ‖hypGradX (F : ℍ → DeckSpace N) z‖ ^ 2 +
            ‖hypGradY (F : ℍ → DeckSpace N) z‖ ^ 2 := by
          apply setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet
          intro z _
          exact hyperbolicChartGradientDensity_eq_hypGradNormSq _ z
    _ = (∫ z in ModularGroup.fd, ‖hypGradX (F : ℍ → DeckSpace N) z‖ ^ 2) +
        ∫ z in ModularGroup.fd, ‖hypGradY (F : ℍ → DeckSpace N) z‖ ^ 2 :=
      integral_add hX hY
    _ = _ := by rw [← hnormX, ← hnormY]

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
