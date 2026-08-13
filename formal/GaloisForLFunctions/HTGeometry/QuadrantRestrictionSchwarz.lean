import GaloisForLFunctions.HTGeometry.QuadrantReflectedCarrier
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Restriction to a carrier, and Schwarz reality of the Euler tangent

Restriction to a subset of the critical quadrant is a real-linear map from the quadrant's
holomorphic space to the continuous functions on the subset.

The symmetrised prime Euler tangent is Schwarz real: it is built from `p ^ (-s)` with a positive
real base, so conjugating the argument conjugates the value.

* `GaloisForLFunctions.HTGeometry.quadrantRestrict`;
* `GaloisForLFunctions.HTGeometry.feEulerTangent_conj`.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

/-- Restriction of an element of the quadrant's holomorphic space to a subset. -/
def quadrantRestrict {K : Set ℂ} (hK : K ⊆ criticalQuadrant) :
    holoQuadrant →ₗ[ℝ] C(K, ℂ) where
  toFun := fun g => (g : C((criticalQuadrant : Set ℂ), ℂ)).comp
    ⟨fun z => ⟨(z : ℂ), hK z.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

@[simp] theorem quadrantRestrict_apply {K : Set ℂ} (hK : K ⊆ criticalQuadrant)
    (g : holoQuadrant) (z : K) :
    quadrantRestrict hK g z = (g : C((criticalQuadrant : Set ℂ), ℂ)) ⟨(z : ℂ), hK z.2⟩ := rfl

/-! ## Schwarz reality of the Euler tangent -/

theorem prime_cpow_conj {p : ℕ} (hp : 0 < p) (s : ℂ) :
    (p : ℂ) ^ ((starRingEnd ℂ) s) = (starRingEnd ℂ) ((p : ℂ) ^ s) := by
  have harg : ((p : ℂ)).arg ≠ Real.pi := by
    have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    rw [show ((p : ℂ)) = ((p : ℝ) : ℂ) by norm_cast, Complex.arg_ofReal_of_nonneg hpos.le]
    exact fun h => absurd h.symm Real.pi_ne_zero
  have hconj : (starRingEnd ℂ) ((p : ℂ)) = (p : ℂ) := by
    rw [show ((p : ℂ)) = ((p : ℝ) : ℂ) by norm_cast, Complex.conj_ofReal]
  rw [Complex.cpow_conj _ _ harg, hconj]

theorem eulerTangent_conj {p : ℕ} (hp : 0 < p) (s : ℂ) :
    eulerTangent p ((starRingEnd ℂ) s) = (starRingEnd ℂ) (eulerTangent p s) := by
  have hneg : (starRingEnd ℂ) (-s) = -((starRingEnd ℂ) s) := map_neg _ _
  have hpow : (p : ℂ) ^ (-((starRingEnd ℂ) s)) = (starRingEnd ℂ) ((p : ℂ) ^ (-s)) := by
    rw [← hneg, prime_cpow_conj hp]
  have hlog : (starRingEnd ℂ) ((Real.log p : ℝ) : ℂ) = ((Real.log p : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  unfold eulerTangent
  rw [hpow]
  rw [map_div₀, map_mul, map_pow, map_sub, map_one, hlog]

theorem feEulerTangent_conj {p : ℕ} (hp : 0 < p) (s : ℂ) :
    feEulerTangent p ((starRingEnd ℂ) s) = (starRingEnd ℂ) (feEulerTangent p s) := by
  have h1 : (1 : ℂ) - (starRingEnd ℂ) s = (starRingEnd ℂ) (1 - s) := by
    rw [map_sub, map_one]
  unfold feEulerTangent
  rw [eulerTangent_conj hp, h1, eulerTangent_conj hp, map_sub]

end GaloisForLFunctions.HTGeometry
