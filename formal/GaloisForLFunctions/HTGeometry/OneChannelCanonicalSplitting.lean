import GaloisForLFunctions.HTGeometry.OneChannelPowerSolvability

/-!
# Intrinsic splitting of a one-channel resonance

The observed complement is the stabilized range of the pencil. The full
root projection is therefore independent of the source, trace, or parametrix
used to construct it. The reduced inverse solves both complementary equations.
-/

noncomputable section
open Module

namespace HTGeometry.OneChannelParametrix
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (P : OneChannelParametrix K V) [FiniteDimensional K P.rootSpace]

theorem complement_eq_range_power_rank :
    P.complement = LinearMap.range (P.pencil^P.rank) := by
  ext x
  rw [P.mem_complement,LinearMap.mem_range,P.power_range_iff,min_self]

theorem projection_kernel :
    LinearMap.ker P.projection = LinearMap.range (P.pencil^P.rank) := by
  ext x
  rw [LinearMap.mem_ker,P.projection_eq_zero_iff,← P.complement_eq_range_power_rank]

/-- The full root projection depends only on the pencil. Auxiliary compact
sources, trace normalizations, and parametrices cannot change it. -/
theorem projection_independent (Q : OneChannelParametrix K V)
    [FiniteDimensional K Q.rootSpace] (hN : P.pencil=Q.pencil) :
    P.projection=Q.projection := by
  have he : P.rootSpace=Q.rootSpace := by
    simp only [rootSpace,hN]
  have hm : P.rank=Q.rank := by
    change Module.finrank K P.rootSpace=Module.finrank K Q.rootSpace
    rw [he]
  have hw : P.complement=Q.complement := by
    rw [P.complement_eq_range_power_rank,Q.complement_eq_range_power_rank,hN,hm]
  ext x
  have hr : Q.projection x ∈ P.rootSpace := by
    rw [he]
    exact Q.projection_mem x
  have hc : x-Q.projection x ∈ P.complement := by
    rw [hw]
    exact Q.remainder_mem x
  have hz := (P.projection_eq_zero_iff _).mpr hc
  rw [map_sub,P.projection_eq_self hr] at hz
  exact sub_eq_zero.mp hz

def reducedInverse : Module.End K V := P.complementInverse.comp (1-P.projection)

theorem pencil_reducedInverse (x : V) :
    P.pencil (P.reducedInverse x)=x-P.projection x :=
  P.pencil_complementInverse (P.remainder_mem x)

theorem reducedInverse_pencil (x : V) :
    P.reducedInverse (P.pencil x)=x-P.projection x := by
  change P.complementInverse (P.pencil x-P.projection (P.pencil x))=x-P.projection x
  rw [P.projection_pencil,← map_sub,P.complementInverse_pencil (P.remainder_mem x)]

theorem reducedInverse_mem (x : V) : P.reducedInverse x ∈ P.complement :=
  P.complementInverse_mem (P.remainder_mem x)

theorem reducedInverse_projection (x : V) : P.reducedInverse (P.projection x)=0 := by
  change P.complementInverse (P.projection x-P.projection (P.projection x))=0
  rw [P.projection_idempotent,sub_self,map_zero]

theorem projection_reducedInverse (x : V) : P.projection (P.reducedInverse x)=0 :=
  (P.projection_eq_zero_iff _).mpr (P.reducedInverse_mem x)

end HTGeometry.OneChannelParametrix
