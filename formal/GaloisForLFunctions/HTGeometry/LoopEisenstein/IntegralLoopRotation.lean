import GaloisForLFunctions.HTGeometry.LoopEisenstein.PositiveLoopRotation
import GaloisForLFunctions.HTGeometry.LoopEisenstein.RingSL2DiagonalRescaling
import GaloisForLFunctions.HTGeometry.LoopEisenstein.IntegralLoopBorelIntersection

/-!
# Rotation of both coefficient-integral loop vertices

At the shifted vertex, rotating the Laurent variable introduces inverse
constant scalars in the two root directions. Their valuations are one
when the rotation scalar is a valuation unit. Both completed integral
vertices, and hence their generated group, are preserved.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
open scoped WithZero WithZeroMulInt
noncomputable section
variable {F : Type*} [Field F]

/-- Constant diagonal rescaling on positive matrices. -/
def powerSeriesConstantRescale (q : Fˣ) : PowerSeriesSL2 F →* PowerSeriesSL2 F :=
  ringSL2Rescale (Units.map (PowerSeries.C (R := F)).toMonoidHom q)

@[simp] theorem powerSeriesConstantRescale_upper (q : Fˣ) (p : PowerSeries F) :
    powerSeriesConstantRescale q (FiniteRingSl2.upper p) =
      FiniteRingSl2.upper (PowerSeries.C (q : F) * p) :=
  ringSL2Rescale_upper (Units.map (PowerSeries.C (R := F)).toMonoidHom q) p

@[simp] theorem powerSeriesConstantRescale_lower (q : Fˣ) (p : PowerSeries F) :
    powerSeriesConstantRescale q (FiniteRingSl2.lower p) =
      FiniteRingSl2.lower (PowerSeries.C ((q⁻¹ : Fˣ) : F) * p) :=
  ringSL2Rescale_lower (Units.map (PowerSeries.C (R := F)).toMonoidHom q) p

private theorem rotation_shifted_upper_parameter (q : Fˣ) (p : PowerSeries F) :
    laurentRotation q (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) *
      laurentRotation q (p : LaurentSeries F) =
      (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) *
        ((PowerSeries.C ((q⁻¹ : Fˣ) : F) * PowerSeries.rescale (q : F) p : PowerSeries F) :
          LaurentSeries F) := by
  have he : laurentUnitRotation q (laurentXUnit F)⁻¹ =
      (laurentXUnit F)⁻¹ * laurentConstantUnit F q⁻¹ := by
    rw [map_inv, laurentUnitRotation_X, mul_inv_rev]
    rfl
  have hv := congrArg (fun u : (LaurentSeries F)ˣ => (u : LaurentSeries F)) he
  change laurentRotation q (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) =
    (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) *
      ((PowerSeries.C ((q⁻¹ : Fˣ) : F) : PowerSeries F) : LaurentSeries F) at hv
  rw [hv, laurentRotation_powerSeries, map_mul]
  exact mul_assoc _ _ _

private theorem rotation_shifted_lower_parameter (q : Fˣ) (p : PowerSeries F) :
    laurentRotation q (laurentXUnit F : LaurentSeries F) * laurentRotation q (p : LaurentSeries F) =
      (laurentXUnit F : LaurentSeries F) *
        ((PowerSeries.C (q : F) * PowerSeries.rescale (q : F) p : PowerSeries F) :
          LaurentSeries F) := by
  have hv := congrArg (fun u : (LaurentSeries F)ˣ => (u : LaurentSeries F))
    (laurentUnitRotation_X F q)
  change laurentRotation q (laurentXUnit F : LaurentSeries F) =
    ((PowerSeries.C (q : F) : PowerSeries F) : LaurentSeries F) *
      (laurentXUnit F : LaurentSeries F) at hv
  rw [hv, laurentRotation_powerSeries, map_mul]
  ring

/-- Rotation preserves every integral power-series coefficient at a valuation-unit scalar. -/
theorem powerSeriesRotation_integral (v : Valuation F ℤᵐ⁰) (q : Fˣ)
    (hq : v (q : F) = 1) (p : PowerSeriesSL2 F)
    (hp : p ∈ valuationIntegralPowerSeriesSL2 v) :
    powerSeriesRotation q p ∈ valuationIntegralPowerSeriesSL2 v := by
  intro i j n
  change v (PowerSeries.coeff n (PowerSeries.rescale (q : F) (p i j))) ≤ 1
  rw [PowerSeries.coeff_rescale, map_mul, map_pow, hq, one_pow, one_mul]
  exact hp i j n

private theorem constant_mul_integral (v : Valuation F ℤᵐ⁰) (q : Fˣ)
    (hq : v (q : F) = 1) (p : PowerSeries F)
    (hp : p ∈ integralPowerSeriesCoefficients v) :
    PowerSeries.C (q : F) * p ∈ integralPowerSeriesCoefficients v := by
  intro n
  change v (PowerSeries.coeff n (PowerSeries.C (q : F) * p)) ≤ 1
  rw [PowerSeries.coeff_C_mul, map_mul, hq, one_mul]
  exact hp n

/-- Constant inverse off-diagonal scalars preserve coefficient integrality. -/
theorem powerSeriesConstantRescale_integral (v : Valuation F ℤᵐ⁰) (q : Fˣ)
    (hq : v (q : F) = 1) (p : PowerSeriesSL2 F)
    (hp : p ∈ valuationIntegralPowerSeriesSL2 v) :
    powerSeriesConstantRescale q p ∈ valuationIntegralPowerSeriesSL2 v := by
  have hqi : v ((q⁻¹ : Fˣ) : F) = 1 := (valuationUnitSubgroup v).inv_mem hq
  intro i j
  fin_cases i <;> fin_cases j
  · exact hp 0 0
  · exact constant_mul_integral v q hq (p 0 1) (hp 0 1)
  · exact constant_mul_integral v q⁻¹ hqi (p 1 0) (hp 1 0)
  · exact hp 1 1

namespace LoopSL2

/-- The actual shifted positive lift rotates by the expected constant diagonal correction. -/
theorem rotation_shiftedPositiveEmbedding (q : Fˣ) (p : PowerSeriesSL2 F) :
    rotation q (diagonalRescale F (laurentXUnit F)⁻¹ (positiveEmbedding F p)) =
      diagonalRescale F (laurentXUnit F)⁻¹
        (positiveEmbedding F (powerSeriesConstantRescale q⁻¹ (powerSeriesRotation q p))) := by
  obtain ⟨x, y, z, w, rfl⟩ := powerSeriesSL2_four_factors F p
  simp only [map_mul, powerSeriesRotation_upper, powerSeriesRotation_lower,
    powerSeriesConstantRescale_upper, powerSeriesConstantRescale_lower,
    positiveEmbedding_upper, positiveEmbedding_lower, diagonalRescale_upperRoot,
    diagonalRescale_lowerRoot, rotation_upperRoot, rotation_lowerRoot, inv_inv,
    rotation_shifted_upper_parameter, rotation_shifted_lower_parameter]

/-- Rotation by a valuation unit preserves the full positive integral vertex. -/
theorem rotation_mem_integralPositiveVertex (v : Valuation F ℤᵐ⁰) (q : Fˣ)
    (hq : v (q : F) = 1) {g : LoopSL2 F} (hg : g ∈ integralPositiveVertex v) :
    rotation q g ∈ integralPositiveVertex v := by
  obtain ⟨⟨c, p⟩, ⟨hc, hp⟩, rfl⟩ := hg
  refine ⟨(c, powerSeriesRotation q p), ⟨hc, powerSeriesRotation_integral v q hq p hp⟩, ?_⟩
  change centralEmbedding F c * positiveEmbedding F (powerSeriesRotation q p) =
    rotation q (centralEmbedding F c * positiveEmbedding F p)
  rw [map_mul, rotation_centralEmbedding, rotation_positiveEmbedding]

/-- Rotation by a valuation unit also preserves the shifted integral vertex. -/
theorem rotation_mem_integralAffineVertex (v : Valuation F ℤᵐ⁰) (q : Fˣ)
    (hq : v (q : F) = 1) {g : LoopSL2 F} (hg : g ∈ integralAffineVertex v) :
    rotation q g ∈ integralAffineVertex v := by
  obtain ⟨g, hg, rfl⟩ := hg
  obtain ⟨⟨c, p⟩, ⟨hc, hp⟩, rfl⟩ := hg
  have hqi : v ((q⁻¹ : Fˣ) : F) = 1 := (valuationUnitSubgroup v).inv_mem hq
  let p' := powerSeriesConstantRescale q⁻¹ (powerSeriesRotation q p)
  have hp' : p' ∈ valuationIntegralPowerSeriesSL2 v :=
    powerSeriesConstantRescale_integral v q⁻¹ hqi _ (powerSeriesRotation_integral v q hq p hp)
  refine ⟨centralPositiveEmbedding F (c, p'), ⟨(c, p'), ⟨hc, hp'⟩, rfl⟩, ?_⟩
  change diagonalRescale F (laurentXUnit F)⁻¹ (centralEmbedding F c * positiveEmbedding F p') =
    rotation q (diagonalRescale F (laurentXUnit F)⁻¹
      (centralEmbedding F c * positiveEmbedding F p))
  simp only [map_mul, diagonalRescale_centralEmbedding, rotation_centralEmbedding,
    rotation_shiftedPositiveEmbedding, p']

/-- The group generated by both completed integral vertices is preserved by unit rotation. -/
theorem rotation_mem_integralLoop (v : Valuation F ℤᵐ⁰) (q : Fˣ)
    (hq : v (q : F) = 1) {g : LoopSL2 F} (hg : g ∈ integralLoop v) :
    rotation q g ∈ integralLoop v := by
  have he : integralLoop v ≤ (integralLoop v).comap (rotation q).toMonoidHom := by
    apply sup_le
    · intro x hx
      change rotation q x ∈ integralLoop v
      exact (show integralVertex v false ≤ integralLoop v from le_sup_left)
        (rotation_mem_integralPositiveVertex v q hq hx)
    · intro x hx
      change rotation q x ∈ integralLoop v
      apply (show integralVertex v true ≤ integralLoop v from le_sup_right)
      rw [integralVertex_true] at hx ⊢
      exact rotation_mem_integralAffineVertex v q hq hx
  exact he hg

/-- Unit rotation preserves and reflects membership in the full coefficient-integral group. -/
theorem rotation_mem_integralLoop_iff (v : Valuation F ℤᵐ⁰) (q : Fˣ)
    (hq : v (q : F) = 1) (g : LoopSL2 F) :
    rotation q g ∈ integralLoop v ↔ g ∈ integralLoop v := by
  constructor
  · intro h
    have hqi : v ((q⁻¹ : Fˣ) : F) = 1 := (valuationUnitSubgroup v).inv_mem hq
    have hi := rotation_mem_integralLoop v q⁻¹ hqi h
    have he : rotation q⁻¹ (rotation q g) = g := (rotation q).left_inv g
    exact he ▸ hi
  · exact rotation_mem_integralLoop v q hq

end LoopSL2
end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.rotation_shiftedPositiveEmbedding
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.rotation_mem_integralLoop_iff
