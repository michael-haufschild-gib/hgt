import GaloisForLFunctions.RHTower.DeningerCohomologyFunctor
import GaloisForLFunctions.RHTower.DeningerStagePowerPermutation

/-!
# Frobenius acts on the cohomology of a stage by a power of the exponent

The power map of a character stage is the transition whose exponent matrix is the exponent times the
identity, so the linear map it induces on the covering space is that scalar, and an alternating form
of degree `k` composed with a scalar is the scalar to the `k`-th power times the form.  Hence the map
induced on the cohomology of the stage is multiplication by the `k`-th power of the exponent: the
action of Frobenius on cohomology is the pure power action.

* `deningerMatrixCLM_power` : the power transition induces a scalar on the covering space.
* `deningerCohomologyMap_power` : Frobenius acts on the cohomology of degree `k` by `q ^ k`.
* `deningerCohomologyMap_perm` : a Galois permutation acts by the permutation of the coordinates.
-/

set_option maxSynthPendingDepth 3

namespace RHTower

open Complex

section PowerAction

variable {r k : ℕ}

/-- **The power transition induces multiplication by the exponent on the covering space.** -/
theorem deningerMatrixCLM_power (q : ℤ) :
    deningerMatrixCLM (deningerPowerMatrix r q) =
      (q : ℂ) • ContinuousLinearMap.id ℂ (Fin r → ℂ) := by
  refine ContinuousLinearMap.ext fun w => ?_
  funext i
  rw [deningerMatrixCLM_apply]
  show (∑ j, ((deningerPowerMatrix r q i j : ℤ) : ℂ) * w j) = (q : ℂ) * w i
  rw [Finset.sum_eq_single i]
  · rw [show deningerPowerMatrix r q i i = q from if_pos rfl]
  · intro j _ hj
    rw [show deningerPowerMatrix r q i j = 0 from if_neg (Ne.symm hj), Int.cast_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **An alternating form of degree `k` composed with a scalar is the scalar to the `k`-th power
times the form.** -/
theorem deningerCompCLM_smul_id (α : (Fin r → ℂ) [⋀^Fin k]→L[ℂ] ℂ) (c : ℂ) :
    α.compContinuousLinearMap (c • ContinuousLinearMap.id ℂ (Fin r → ℂ)) = (c ^ k) • α := by
  ext v
  show α (fun a => c • v a) = (c ^ k) • α v
  rw [α.map_smul_univ]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Frobenius acts on the cohomology of a character stage by the power of its exponent.**  The
power map of the stage induces multiplication by `q ^ k` on the cohomology of degree `k`. -/
theorem deningerCohomologyMap_power (q : ℤ) (n : ℕ) (ξ : deningerCohomology r n) :
    deningerCohomologyMap (deningerPowerMatrix r q) n ξ = ((q : ℂ) ^ (n + 1)) • ξ := by
  obtain ⟨α, rfl⟩ := (deningerCohomologyEquiv r n).surjective ξ
  show deningerCohomologyMap (deningerPowerMatrix r q) n (deningerConstantClass r n α) =
    ((q : ℂ) ^ (n + 1)) • deningerConstantClass r n α
  rw [deningerCohomologyMap_constantClass, deningerMatrixCLM_power, deningerCompCLM_smul_id,
    map_smul]

/-- **A Galois permutation induces the permutation of the coordinates** on the covering space. -/
theorem deningerMatrixCLM_perm (σ : Equiv.Perm (Fin r)) (w : Fin r → ℂ) (i : Fin r) :
    deningerMatrixCLM (deningerPermMatrix σ) w i = w (σ i) := by
  rw [deningerMatrixCLM_apply]
  show (∑ j, ((deningerSelectMatrix (fun i => σ i) i j : ℤ) : ℂ) * w j) = w (σ i)
  rw [Finset.sum_eq_single (σ i)]
  · rw [show deningerSelectMatrix (fun i => σ i) i (σ i) = 1 from if_pos rfl, Int.cast_one,
      one_mul]
  · intro j _ hj
    rw [show deningerSelectMatrix (fun i => σ i) i j = 0 from if_neg hj, Int.cast_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (σ i)) h

/-- **A Galois permutation acts on the cohomology of a character stage by permuting the
coordinates of the alternating form.** -/
theorem deningerCohomologyMap_perm (σ : Equiv.Perm (Fin r)) (n : ℕ)
    (α : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) :
    deningerCohomologyMap (deningerPermMatrix σ) n (deningerConstantClass r n α) =
      deningerConstantClass r n
        (α.compContinuousLinearMap (deningerMatrixCLM (deningerPermMatrix σ))) :=
  deningerCohomologyMap_constantClass _ _ _

end PowerAction

end RHTower
