import GaloisForLFunctions.HTGeometry.LoopEisenstein.IwahoriGaussCoordinates

/-!
# Finite torus and unipotent factors of the Iwahori

The nonzero constant upper-left entry is a multiplicative coordinate on the
Iwahori. Its kernel is exactly the positive unipotent subgroup, and the
constant diagonal splits it. Consequently every Iwahori element has unique
finite-torus and unipotent factors.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

/-- Embed coefficient units as constant power-series units. -/
def powerSeriesConstantUnit : Fˣ →* (PowerSeries F)ˣ :=
  Units.map (PowerSeries.C : F →+* PowerSeries F).toMonoidHom

/-- The nonzero constant upper-left entry of an Iwahori matrix. -/
def iwahoriFiniteCoordinate : iwahoriMatrices F →* Fˣ where
  toFun g := Units.mk0 (PowerSeries.constantCoeff ((g : PowerSeriesSL2 F) 0 0))
    (iwahori_upper_left_constant_ne_zero F g)
  map_one' := by
    apply Units.ext
    change PowerSeries.constantCoeff (1 : PowerSeries F) = 1
    exact map_one _
  map_mul' g h := by
    apply Units.ext
    change PowerSeries.constantCoeff (((g : PowerSeriesSL2 F) * (h : PowerSeriesSL2 F)) 0 0) =
      PowerSeries.constantCoeff ((g : PowerSeriesSL2 F) 0 0) *
        PowerSeries.constantCoeff ((h : PowerSeriesSL2 F) 0 0)
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      map_add, map_mul]
    rw [(mem_iwahoriMatrices F h).1 h.property, mul_zero, add_zero]

/-- The constant diagonal gives the finite coroot in the Iwahori. -/
def iwahoriFiniteCoroot : Fˣ →* iwahoriMatrices F where
  toFun a := ⟨powerSeriesDiagonal F (powerSeriesConstantUnit F a), by
    rw [mem_iwahoriMatrices]
    change PowerSeries.constantCoeff (0 : PowerSeries F) = 0
    exact map_zero _⟩
  map_one' := by
    apply Subtype.ext
    change powerSeriesDiagonalHom F (powerSeriesConstantUnit F 1) = 1
    rw [map_one, map_one]
  map_mul' a b := by
    apply Subtype.ext
    change powerSeriesDiagonalHom F (powerSeriesConstantUnit F (a * b)) =
      powerSeriesDiagonalHom F (powerSeriesConstantUnit F a) *
        powerSeriesDiagonalHom F (powerSeriesConstantUnit F b)
    rw [map_mul, map_mul]

@[simp] theorem iwahoriFiniteCoordinate_finiteCoroot (a : Fˣ) :
    iwahoriFiniteCoordinate F (iwahoriFiniteCoroot F a) = a := by
  apply Units.ext
  change PowerSeries.constantCoeff (PowerSeries.C (a : F)) = (a : F)
  exact PowerSeries.constantCoeff_C _

/-- The unipotent subgroup is the exact kernel of the finite torus coordinate. -/
theorem iwahoriFiniteCoordinate_eq_one_iff (g : iwahoriMatrices F) :
    iwahoriFiniteCoordinate F g = 1 ↔
      (g : PowerSeriesSL2 F) ∈ positiveUnipotentMatrices F := by
  constructor
  · intro h
    have ha : PowerSeries.constantCoeff ((g : PowerSeriesSL2 F) 0 0) = 1 :=
      congrArg (fun a : Fˣ => (a : F)) h
    have hc := (mem_iwahoriMatrices F g).1 g.property
    have hd := Matrix.SpecialLinearGroup.det_coe (powerSeriesReduction F g)
    rw [Matrix.det_fin_two] at hd
    simp only [powerSeriesReduction_apply, ha, hc, one_mul, mul_zero, sub_zero] at hd
    exact (mem_positiveUnipotentMatrices F g).2 ⟨ha, hc, hd⟩
  · intro h
    apply Units.ext
    exact ((mem_positiveUnipotentMatrices F g).1 h).1

/-- Inclusion of the positive unipotent matrices into the Iwahori. -/
def positiveUnipotentToIwahori : positiveUnipotentMatrices F →* iwahoriMatrices F where
  toFun u := ⟨u, positiveUnipotentMatrices_le_iwahori F u.property⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; rfl

theorem positiveUnipotentToIwahori_injective : Function.Injective (positiveUnipotentToIwahori F) := by
  intro u v h
  apply Subtype.ext
  exact congrArg (fun b : iwahoriMatrices F => (b : PowerSeriesSL2 F)) h

@[simp] theorem iwahoriFiniteCoordinate_unipotent (u : positiveUnipotentMatrices F) :
    iwahoriFiniteCoordinate F (positiveUnipotentToIwahori F u) = 1 :=
  (iwahoriFiniteCoordinate_eq_one_iff F _).2 u.property

/-- Remove the constant diagonal to obtain the unique positive unipotent factor. -/
def iwahoriUnipotentPart (g : iwahoriMatrices F) : positiveUnipotentMatrices F :=
  ⟨(((iwahoriFiniteCoroot F (iwahoriFiniteCoordinate F g))⁻¹ * g : iwahoriMatrices F) :
      PowerSeriesSL2 F), by
    apply (iwahoriFiniteCoordinate_eq_one_iff F _).1
    rw [map_mul, map_inv, iwahoriFiniteCoordinate_finiteCoroot, inv_mul_cancel]⟩

theorem iwahori_torus_unipotent (g : iwahoriMatrices F) :
    iwahoriFiniteCoroot F (iwahoriFiniteCoordinate F g) *
      positiveUnipotentToIwahori F (iwahoriUnipotentPart F g) = g := by
  apply Subtype.ext
  change (iwahoriFiniteCoroot F (iwahoriFiniteCoordinate F g) : PowerSeriesSL2 F) *
    ((iwahoriFiniteCoroot F (iwahoriFiniteCoordinate F g) : PowerSeriesSL2 F)⁻¹ *
      (g : PowerSeriesSL2 F)) = (g : PowerSeriesSL2 F)
  rw [← mul_assoc, mul_inv_cancel, one_mul]

theorem iwahori_torus_unipotent_injective :
    Function.Injective (fun p : Fˣ × positiveUnipotentMatrices F =>
      iwahoriFiniteCoroot F p.1 * positiveUnipotentToIwahori F p.2) := by
  intro p q h
  change iwahoriFiniteCoroot F p.1 * positiveUnipotentToIwahori F p.2 =
    iwahoriFiniteCoroot F q.1 * positiveUnipotentToIwahori F q.2 at h
  have ha := congrArg (iwahoriFiniteCoordinate F) h
  simp only [map_mul, iwahoriFiniteCoordinate_finiteCoroot,
    iwahoriFiniteCoordinate_unipotent, mul_one] at ha
  have hu : p.2 = q.2 := by
    rw [ha] at h
    have hU : positiveUnipotentToIwahori F p.2 = positiveUnipotentToIwahori F q.2 :=
      mul_left_cancel h
    exact positiveUnipotentToIwahori_injective F hU
  exact Prod.ext ha hu

/-- Unique finite-torus and completed-unipotent coordinates on the Iwahori. -/
def iwahoriTorusUnipotentEquiv : Fˣ × positiveUnipotentMatrices F ≃ iwahoriMatrices F where
  toFun p := iwahoriFiniteCoroot F p.1 * positiveUnipotentToIwahori F p.2
  invFun g := (iwahoriFiniteCoordinate F g, iwahoriUnipotentPart F g)
  left_inv _ := iwahori_torus_unipotent_injective F (iwahori_torus_unipotent F _)
  right_inv := iwahori_torus_unipotent F

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
