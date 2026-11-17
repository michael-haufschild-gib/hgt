import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeSectorGrams
import Mathlib.LinearAlgebra.Trace

/-!
# Reflection closure and character averages of finite probe spaces

Adjoining the reflected probes gives a finite-dimensional invariant space.
The averages `(1+R)/2` and `(1-R)/2` on this space extract its actual Weil
sectors. Their traces recover the sector dimensions. This applies the
fixed-space averaging mechanism of Aoki, *Distribution of Primes in Galois
Extensions of Global Fields with Explicit Constant Terms*, Lemma 3,
to the order-two action on zeta-zero coordinates.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk

variable {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})

/-- The smallest reflection-stable subspace containing the given probes. -/
def reflectionHull : Submodule ℂ ZeroSpace :=
  probeSpace p ⊔ (probeSpace p).map zeroReflection.toLinearMap

instance reflectionHull_finiteDimensional : FiniteDimensional ℂ (reflectionHull p) := by
  unfold reflectionHull
  infer_instance

theorem probeSpace_le_reflectionHull : probeSpace p ≤ reflectionHull p := le_sup_left

theorem zeroReflection_mem_reflectionHull {x : ZeroSpace} (hx : x ∈ reflectionHull p) :
    zeroReflection x ∈ reflectionHull p := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
  change zeroReflection (u + zeroReflection w) ∈ reflectionHull p
  rw [map_add, zeroReflection_involutive]
  exact (reflectionHull p).add_mem
    (le_sup_right (Submodule.mem_map.mpr ⟨u, hu, rfl⟩)) (le_sup_left hw)

/-- Restriction of the genuine zero reflection, without assuming probe-span invariance. -/
def hullReflection : Module.End ℂ (reflectionHull p) :=
  zeroReflection.toLinearMap.restrict (fun _ hx => zeroReflection_mem_reflectionHull p hx)

@[simp] theorem hullReflection_apply (x : reflectionHull p) :
    (hullReflection p x : ZeroSpace) = zeroReflection x := rfl

theorem hullReflection_sq : hullReflection p * hullReflection p = 1 := by
  apply LinearMap.ext
  intro x
  exact Subtype.ext (zeroReflection_involutive x)

/-- Averaging the order-two action selects its fixed vectors. -/
def hullPositive : Module.End ℂ (reflectionHull p) :=
  (1 / 2 : ℂ) • (1 + hullReflection p)

/-- The nontrivial character average selects the negative reflection sector. -/
def hullNegative : Module.End ℂ (reflectionHull p) :=
  (1 / 2 : ℂ) • (1 - hullReflection p)

theorem hullPositive_idempotent : IsIdempotentElem (hullPositive p) := by
  change hullPositive p * hullPositive p = hullPositive p
  unfold hullPositive
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, add_mul, mul_add,
    one_mul, mul_one, hullReflection_sq]
  module

theorem hullNegative_idempotent : IsIdempotentElem (hullNegative p) := by
  change hullNegative p * hullNegative p = hullNegative p
  unfold hullNegative
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub,
    one_mul, mul_one, hullReflection_sq]
  module

theorem hullPositive_add_hullNegative : hullPositive p + hullNegative p = 1 := by
  unfold hullPositive hullNegative
  module

/-- The averaging range consists exactly of actual reflection-fixed vectors. -/
theorem mem_range_hullPositive_iff (x : reflectionHull p) :
    x ∈ LinearMap.range (hullPositive p) ↔ zeroReflection (x : ZeroSpace) = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact zeroReflection_positivePart y
  · intro hx
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change (1 / 2 : ℂ) • ((x : ZeroSpace) + zeroReflection x) = x
    rw [hx]
    module

/-- The other averaging range consists exactly of actual reflection-odd vectors. -/
theorem mem_range_hullNegative_iff (x : reflectionHull p) :
    x ∈ LinearMap.range (hullNegative p) ↔ zeroReflection (x : ZeroSpace) = -x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact zeroReflection_negativePart y
  · intro hx
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change (1 / 2 : ℂ) • ((x : ZeroSpace) - zeroReflection x) = x
    rw [hx]
    module

/-- Fixed-sector dimension is the average of identity and reflection characters. -/
theorem hullPositive_dimension :
    (Module.finrank ℂ (LinearMap.range (hullPositive p)) : ℂ) =
      ((Module.finrank ℂ (reflectionHull p) : ℂ) +
        LinearMap.trace ℂ (reflectionHull p) (hullReflection p)) / 2 := by
  rw [← (hullPositive_idempotent p).isProj_range.trace]
  simp only [hullPositive, map_smul, map_add, LinearMap.trace_one, smul_eq_mul]
  ring

/-- The complementary character average counts negative-sector dimensions exactly. -/
theorem hullNegative_dimension :
    (Module.finrank ℂ (LinearMap.range (hullNegative p)) : ℂ) =
      ((Module.finrank ℂ (reflectionHull p) : ℂ) -
        LinearMap.trace ℂ (reflectionHull p) (hullReflection p)) / 2 := by
  rw [← (hullNegative_idempotent p).isProj_range.trace]
  simp only [hullNegative, map_smul, map_sub, LinearMap.trace_one, smul_eq_mul]
  ring

/-- The actual reflection character is the difference of its two sector dimensions. -/
theorem hullReflection_trace :
    LinearMap.trace ℂ (reflectionHull p) (hullReflection p) =
      (Module.finrank ℂ (LinearMap.range (hullPositive p)) : ℂ) -
        (Module.finrank ℂ (LinearMap.range (hullNegative p)) : ℂ) := by
  rw [hullPositive_dimension, hullNegative_dimension]
  ring

#print axioms hullPositive_dimension
#print axioms hullNegative_dimension
#print axioms hullReflection_trace

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
