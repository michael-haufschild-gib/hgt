import GaloisForLFunctions.HTGeometry.LoopEisenstein.IntegralPowerSeriesCoefficients
import GaloisForLFunctions.HTGeometry.LoopEisenstein.RealBorelCharacters
import GaloisForLFunctions.HTGeometry.LoopEisenstein.VertexParabolics

/-!
# The integral standard vertex and its Borel coordinates

Central valuation units and coefficient-integral positive matrices form
an actual subgroup. Its intersection with positive Borel has unit-valued
central and finite torus coordinates, by faithful splitting and the
constant determinant relation.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
open Matrix
open scoped WithZero WithZeroMulInt
noncomputable section
variable {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)

/-- Coefficient-field units whose valuation is one. -/
def valuationUnitSubgroup : Subgroup Fˣ where
  carrier := {a | v (a : F) = 1}
  one_mem' := by
    change v ((1 : Fˣ) : F) = 1
    exact map_one v
  mul_mem' := by
    intro a b ha hb
    change v ((a * b : Fˣ) : F) = 1
    change v (a : F) = 1 at ha
    change v (b : F) = 1 at hb
    rw [Units.val_mul, map_mul, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    change v ((a⁻¹ : Fˣ) : F) = 1
    change v (a : F) = 1 at ha
    rw [Units.val_inv_eq_inv_val, Valuation.map_inv, ha, inv_one]

namespace LoopSL2

/-- The commuting central and full positive factors form a faithful product homomorphism. -/
def centralPositiveEmbedding (F : Type*) [Field F] : Fˣ × PowerSeriesSL2 F →* LoopSL2 F where
  toFun p := centralEmbedding F p.1 * positiveEmbedding F p.2
  map_one' := by
    change centralEmbedding F 1 * positiveEmbedding F 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' p q := by
    change centralEmbedding F (p.1 * q.1) * positiveEmbedding F (p.2 * q.2) =
      (centralEmbedding F p.1 * positiveEmbedding F p.2) *
        (centralEmbedding F q.1 * positiveEmbedding F q.2)
    rw [map_mul, map_mul]
    have hc : centralEmbedding F q.1 * positiveEmbedding F p.2 =
        positiveEmbedding F p.2 * centralEmbedding F q.1 :=
      SL2SymbolExtension.centralEmbedding_commute
        (Multiplicative.ofAdd (Additive.ofMul q.1)) (positiveEmbedding F p.2)
    calc
      _ = centralEmbedding F p.1 * (centralEmbedding F q.1 * positiveEmbedding F p.2) *
          positiveEmbedding F q.2 := by simp only [mul_assoc]
      _ = centralEmbedding F p.1 * (positiveEmbedding F p.2 * centralEmbedding F q.1) *
          positiveEmbedding F q.2 := by rw [hc]
      _ = _ := by simp only [mul_assoc]

theorem centralPositiveEmbedding_injective (F : Type*) [Field F] :
    Function.Injective (centralPositiveEmbedding F) := by
  intro p q h
  have hp : p.2 = q.2 := by
    apply powerSeriesSL2Map_injective F
    have he := congrArg (projection F) h
    change projection F (centralEmbedding F p.1 * positiveEmbedding F p.2) =
      projection F (centralEmbedding F q.1 * positiveEmbedding F q.2) at he
    simpa only [map_mul, projection_centralEmbedding, projection_positiveEmbedding, one_mul] using he
  have hc : p.1 = q.1 := by
    apply centralEmbedding_injective F
    change centralEmbedding F p.1 * positiveEmbedding F p.2 =
      centralEmbedding F q.1 * positiveEmbedding F q.2 at h
    rw [hp] at h
    exact mul_right_cancel h
  exact Prod.ext hc hp

/-- The actual coefficient-integral standard vertex, including its central valuation units. -/
def integralPositiveVertex : Subgroup (LoopSL2 F) :=
  ((valuationUnitSubgroup v).prod (valuationIntegralPowerSeriesSL2 v)).map
    (centralPositiveEmbedding F)

/-- The standard integral Borel is the literal vertex–Borel intersection. -/
def integralPositiveBorel : Subgroup (LoopSL2 F) :=
  integralPositiveVertex v ⊓ positiveBorel F

theorem centralPositiveEmbedding_mem_borel_iff (c : Fˣ) (p : PowerSeriesSL2 F) :
    centralPositiveEmbedding F (c, p) ∈ positiveBorel F ↔ p ∈ iwahoriMatrices F := by
  constructor
  · intro h
    have hm := projection_mem_laurentIwahori F h
    change projection F (centralEmbedding F c * positiveEmbedding F p) ∈ laurentIwahori F at hm
    rw [map_mul, projection_centralEmbedding, projection_positiveEmbedding, one_mul] at hm
    obtain ⟨q, hq, he⟩ := hm
    have hpq : q = p := powerSeriesSL2Map_injective F he
    change q ∈ iwahoriMatrices F at hq
    exact hpq ▸ hq
  · intro hp
    exact ⟨(c, ⟨p, hp⟩), rfl⟩

/-- The two intrinsic Borel torus coordinates are valuation units on the integral standard vertex. -/
theorem integralPositiveVertex_borel_torus_values (g : positiveBorel F)
    (hg : (g : LoopSL2 F) ∈ integralPositiveVertex v) :
    v (((borelTorusHom F g).1 : Fˣ) : F) = 1 ∧
      v (((borelTorusHom F g).2 : Fˣ) : F) = 1 := by
  obtain ⟨⟨c, p⟩, ⟨hc, hp⟩, he⟩ := hg
  have hpi : p ∈ iwahoriMatrices F := (centralPositiveEmbedding_mem_borel_iff c p).mp
    (by rw [he]; exact g.property)
  let q : iwahoriMatrices F := ⟨p, hpi⟩
  have hf : positiveBorelFactors F g = (c, q) :=
    positiveBorelEmbedding_injective F ((positiveBorelFactors_spec F g).trans he.symm)
  change v (((positiveBorelFactors F g).1 : Fˣ) : F) = 1 ∧
    v ((iwahoriFiniteCoordinate F (positiveBorelFactors F g).2 : Fˣ) : F) = 1
  rw [hf]
  refine ⟨hc, ?_⟩
  have hred := integralPowerSeriesSL2_constant_reduction v p hp
  have htri : powerSeriesReduction F p 1 0 = 0 := (mem_iwahoriMatrices F p).mp hpi
  exact (valued_sl2_triangular_diagonal_value v (powerSeriesReduction F p) hred htri).1

end LoopSL2
end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2.integralPositiveVertex_borel_torus_values
