import GaloisForLFunctions.HeckeKreinToeplitz.Index.LocallyPeriodicProjection

/-!
# Functoriality of periodic fixed projections

Finite orbit averages respect intertwining, nested powers, commuting actions, and inversion.
-/

open Module Finset
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz
variable {K V : Type*} [Field K] [CharZero K] [AddCommMonoid V] [Module K V]

/-- Intertwining locally periodic actions also intertwines their fixed-space projections. -/
theorem locallyPeriodicProjection_intertwine (T U S : End K V)
    (hT : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (T ^ m) x = x)
    (hU : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (U ^ m) x = x)
    (hS : U * S = S * T) (x : V) :
    locallyPeriodicProjection U hU (S x) = S (locallyPeriodicProjection T hT x) := by
  have hpow (n : ℕ) : U ^ n * S = S * T ^ n := by
    induction n with
    | zero => simp only [pow_zero, one_mul, mul_one]
    | succ n ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, hS, mul_assoc, ← pow_succ']
  have happ (n : ℕ) : (U ^ n) (S x) = S ((T ^ n) x) := LinearMap.congr_fun (hpow n) x
  obtain ⟨m, hm, hx⟩ := hT x
  have hSx : (U ^ m) (S x) = S x := by rw [happ, hx]
  rw [locallyPeriodicProjection_eq_average U hU hm hSx,
    locallyPeriodicProjection_eq_average T hT hm hx]
  simp only [periodicOrbitAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, happ]

/-- Raising a locally periodic action to a natural power enlarges its fixed space. -/
theorem locallyPeriodicProjection_pow_fixed (T : End K V)
    (hT : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (T ^ m) x = x) (n : ℕ) (x : V) :
    (T ^ n) (locallyPeriodicProjection T hT x) = locallyPeriodicProjection T hT x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, Module.End.mul_apply, locallyPeriodicProjection_fixed, ih]

/-- Fixed projections for an action and its power are nested in both composition orders. -/
theorem locallyPeriodicProjection_pow_nested (T : End K V)
    (hT : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (T ^ m) x = x) (n : ℕ)
    (hU : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ ((T ^ n) ^ m) x = x) (x : V) :
    locallyPeriodicProjection (T ^ n) hU (locallyPeriodicProjection T hT x) =
        locallyPeriodicProjection T hT x ∧
      locallyPeriodicProjection T hT (locallyPeriodicProjection (T ^ n) hU x) =
        locallyPeriodicProjection T hT x := by
  constructor
  · exact locallyPeriodicProjection_apply_of_fixed (T ^ n) hU
      (locallyPeriodicProjection_pow_fixed T hT n x)
  · obtain ⟨m, hm, hx⟩ := hU x
    rw [locallyPeriodicProjection_eq_average (T ^ n) hU hm hx]
    have hterm (j : ℕ) : locallyPeriodicProjection T hT (((T ^ n) ^ j) x) =
        locallyPeriodicProjection T hT x := by
      rw [← pow_mul, locallyPeriodicProjection_pow_apply]
    have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm
    simp only [periodicOrbitAverage, LinearMap.smul_apply, LinearMap.sum_apply,
      map_smul, map_sum, hterm, sum_const, card_range,
      ← Nat.cast_smul_eq_nsmul K m, smul_smul, inv_mul_cancel₀ hmK, one_smul]

/-- Commuting periodic actions have commuting fixed-space projections. -/
theorem locallyPeriodicProjection_commute_pair (T U : End K V)
    (hT : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (T ^ m) x = x)
    (hU : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (U ^ m) x = x)
    (hTU : Commute T U) :
    Commute (locallyPeriodicProjection T hT) (locallyPeriodicProjection U hU) := by
  have h := locallyPeriodicProjection_commute T hT U hTU
  exact (locallyPeriodicProjection_commute U hU _ h.symm).symm

/-- A periodic action and its inverse have the same canonical fixed projection. -/
theorem locallyPeriodicProjection_eq_of_inverse (T U : End K V)
    (hT : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (T ^ m) x = x)
    (hU : ∀ x : V, ∃ m : ℕ, m ≠ 0 ∧ (U ^ m) x = x)
    (hTU : T * U = 1) (hUT : U * T = 1) :
    locallyPeriodicProjection T hT = locallyPeriodicProjection U hU := by
  have hc := locallyPeriodicProjection_commute_pair T U hT hU (hTU.trans hUT.symm)
  apply LinearMap.ext
  intro x
  have hfixU : U (locallyPeriodicProjection T hT x) = locallyPeriodicProjection T hT x := by
    have h := LinearMap.congr_fun hUT (locallyPeriodicProjection T hT x)
    simpa only [Module.End.mul_apply, Module.End.one_apply, locallyPeriodicProjection_fixed] using h
  have hfixT : T (locallyPeriodicProjection U hU x) = locallyPeriodicProjection U hU x := by
    have h := LinearMap.congr_fun hTU (locallyPeriodicProjection U hU x)
    simpa only [Module.End.mul_apply, Module.End.one_apply, locallyPeriodicProjection_fixed] using h
  have he := LinearMap.congr_fun hc.eq x
  rw [Module.End.mul_apply, Module.End.mul_apply,
    locallyPeriodicProjection_apply_of_fixed T hT hfixT,
    locallyPeriodicProjection_apply_of_fixed U hU hfixU] at he
  exact he.symm

#print axioms locallyPeriodicProjection_intertwine
#print axioms locallyPeriodicProjection_pow_nested
#print axioms locallyPeriodicProjection_eq_of_inverse
end GaloisForLFunctions.HeckeKreinToeplitz
