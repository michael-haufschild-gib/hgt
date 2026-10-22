import GaloisForLFunctions.RHTower.Deninger.DeningerDlogTransition
import GaloisForLFunctions.RHTower.Deninger.DeningerCylinderForm

/-!
# Power maps and coordinate permutations of a character stage

Frobenius acts on a character stage by raising every coordinate to the same power and a Galois
element acts by permuting the evaluation coordinates.  Both are monomial transition maps, so the
holomorphic de Rham complex of the stage is stable under them and the exterior derivative
transports.  On the generators the power map multiplies by the exponent and the permutation permutes
them, which is the action of Frobenius and of Galois on the cohomology of a stage.

* `deningerPowerMatrix`, `deningerPowerMap_eq` : the power map as a monomial map.
* `deningerDlogForm_power_pullback` : the power map multiplies the generators by the exponent.
* `deningerPermMatrix`, `deningerPermMap_eq` : a coordinate permutation as a monomial map.
* `deningerDlogForm_perm_pullback` : a permutation permutes the generators.
-/

namespace RHTower

section PowerMap

variable {r : ℕ}

/-- The exponent matrix of the power map: the diagonal matrix of a fixed exponent. -/
def deningerPowerMatrix (r : ℕ) (q : ℤ) : Fin r → Fin r → ℤ := fun i j => if i = j then q else 0

/-- **The power map of a character stage** raises every coordinate to the same power. -/
theorem deningerPowerMap_eq (q : ℤ) :
    deningerMonomialMap (deningerPowerMatrix r q) = fun z i => (z i) ^ q := by
  funext z i
  show (∏ j, (z j) ^ (deningerPowerMatrix r q i j)) = (z i) ^ q
  rw [Finset.prod_eq_single i]
  · simp [deningerPowerMatrix]
  · intro j _ hj
    rw [show deningerPowerMatrix r q i j = 0 from if_neg (Ne.symm hj), zpow_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **The power map multiplies the logarithmic differentials by the exponent**: this is the action
of Frobenius on the generators of the cohomology of a stage. -/
theorem deningerDlogForm_power_pullback (q : ℤ) (i : Fin r) {z : Fin r → ℂ}
    (hz : z ∈ deningerStageTorus r) :
    deningerStagePullback (deningerMonomialMap (deningerPowerMatrix r q))
        (deningerDlogForm r i) z = (q : ℂ) • deningerDlogForm r i z := by
  rw [deningerDlogForm_pullback (deningerPowerMatrix r q) i hz]
  rw [Finset.sum_eq_single i]
  · rw [show deningerPowerMatrix r q i i = q from if_pos rfl]
  · intro j _ hj
    rw [show deningerPowerMatrix r q i j = 0 from if_neg (Ne.symm hj), Int.cast_zero]
    exact zero_smul ℂ (deningerDlogForm r j z)
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The power map preserves holomorphy of stage forms. -/
theorem deningerPowerPullback_holomorphic (q : ℤ) {n : ℕ} {ω : DeningerStageForm r n}
    (hω : DeningerIsHolomorphicForm ω) :
    DeningerIsHolomorphicForm
      (deningerStagePullback (deningerMonomialMap (deningerPowerMatrix r q)) ω) :=
  deningerMonomialPullback_holomorphic _ hω

/-- The exterior derivative transports along the power map. -/
theorem deningerPowerPullback_extDeriv (q : ℤ) {n : ℕ} {ω : DeningerStageForm r n}
    (hω : DeningerIsHolomorphicForm ω) {z : Fin r → ℂ} (hz : z ∈ deningerStageTorus r) :
    extDeriv (deningerStagePullback (deningerMonomialMap (deningerPowerMatrix r q)) ω) z =
      deningerStagePullback (deningerMonomialMap (deningerPowerMatrix r q)) (extDeriv ω) z :=
  deningerMonomialPullback_extDeriv _ hω hz

end PowerMap

section PermutationMap

variable {r : ℕ}

/-- The exponent matrix of a coordinate permutation. -/
def deningerPermMatrix (σ : Equiv.Perm (Fin r)) : Fin r → Fin r → ℤ :=
  deningerSelectMatrix (fun i => σ i)

/-- **A Galois element permutes the evaluation coordinates.** -/
theorem deningerPermMap_eq (σ : Equiv.Perm (Fin r)) :
    deningerMonomialMap (deningerPermMatrix σ) = fun z i => z (σ i) :=
  deningerMonomialMap_select (fun i => σ i)

/-- **A coordinate permutation permutes the logarithmic differentials**: this is the action of
Galois on the generators of the cohomology of a stage. -/
theorem deningerDlogForm_perm_pullback (σ : Equiv.Perm (Fin r)) (i : Fin r) {z : Fin r → ℂ}
    (hz : z ∈ deningerStageTorus r) :
    deningerStagePullback (deningerMonomialMap (deningerPermMatrix σ))
        (deningerDlogForm r i) z = deningerDlogForm r (σ i) z := by
  rw [deningerDlogForm_pullback (deningerPermMatrix σ) i hz]
  rw [Finset.sum_eq_single (σ i)]
  · rw [show deningerPermMatrix σ i (σ i) = 1 from if_pos rfl]
    simp
  · intro j _ hj
    rw [show deningerPermMatrix σ i j = 0 from if_neg hj, Int.cast_zero]
    exact zero_smul ℂ (deningerDlogForm r j z)
  · intro h
    exact absurd (Finset.mem_univ (σ i)) h

/-- A coordinate permutation preserves holomorphy of stage forms. -/
theorem deningerPermPullback_holomorphic (σ : Equiv.Perm (Fin r)) {n : ℕ}
    {ω : DeningerStageForm r n} (hω : DeningerIsHolomorphicForm ω) :
    DeningerIsHolomorphicForm
      (deningerStagePullback (deningerMonomialMap (deningerPermMatrix σ)) ω) :=
  deningerMonomialPullback_holomorphic _ hω

/-- The exterior derivative transports along a coordinate permutation. -/
theorem deningerPermPullback_extDeriv (σ : Equiv.Perm (Fin r)) {n : ℕ}
    {ω : DeningerStageForm r n} (hω : DeningerIsHolomorphicForm ω) {z : Fin r → ℂ}
    (hz : z ∈ deningerStageTorus r) :
    extDeriv (deningerStagePullback (deningerMonomialMap (deningerPermMatrix σ)) ω) z =
      deningerStagePullback (deningerMonomialMap (deningerPermMatrix σ)) (extDeriv ω) z :=
  deningerMonomialPullback_extDeriv _ hω hz

end PermutationMap

end RHTower
