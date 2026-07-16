import GaloisForLFunctions.HTGeometry.QuantumTorusPrincipalSymbol
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# A finite quantum-torus representation

The cyclic phase space `(ι → ZMod d)` carries an explicit finite representation of the
pairwise `q`-commuting generator algebra.  Generator `i` shifts the `i`th cyclic coordinate and
multiplies by the additive-character charge in all coordinates strictly above `i`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K]
  {ι : Type*} [Fintype ι] [LinearOrder ι]
  {d : ℕ} [NeZero d] [Fact (1 < d)]

/-- The finite phase space underlying the regular quantum packet. -/
abbrev FiniteQuantumState (ι : Type*) (d : ℕ) := ι → ZMod d

/-- Charge in all coordinates strictly above `i`. -/
def finiteQuantumTailCharge (i : ι) (a : FiniteQuantumState ι d) : ZMod d :=
  ∑ j with i < j, a j

/-- Decrement one cyclic coordinate. -/
def finiteQuantumShift (i : ι) (a : FiniteQuantumState ι d) :
    FiniteQuantumState ι d :=
  Function.update a i (a i - 1)

theorem finiteQuantumShift_apply_same
    (i : ι) (a : FiniteQuantumState ι d) :
    finiteQuantumShift i a i = a i - 1 := by
  simp [finiteQuantumShift]

theorem finiteQuantumShift_apply_of_ne
    {i j : ι} (hij : j ≠ i) (a : FiniteQuantumState ι d) :
    finiteQuantumShift i a j = a j := by
  simp [finiteQuantumShift, hij]

theorem finiteQuantumShift_comm
    {i j : ι} (hij : i ≠ j) (a : FiniteQuantumState ι d) :
    finiteQuantumShift i (finiteQuantumShift j a) =
      finiteQuantumShift j (finiteQuantumShift i a) := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [finiteQuantumShift, hij]
  · by_cases hkj : k = j
    · subst k
      simp [finiteQuantumShift, hij, hki]
    · simp [finiteQuantumShift, hki, hkj]

theorem finiteQuantumTailCharge_shift_lower
    {i j : ι} (hij : i < j) (a : FiniteQuantumState ι d) :
    finiteQuantumTailCharge j (finiteQuantumShift i a) =
      finiteQuantumTailCharge j a := by
  classical
  apply Finset.sum_congr rfl
  intro k hk
  have hjk : j < k := by simpa using hk
  have hki : k ≠ i := ne_of_gt (lt_trans hij hjk)
  exact finiteQuantumShift_apply_of_ne hki a

theorem finiteQuantumTailCharge_shift_member
    {i j : ι} (hij : i < j) (a : FiniteQuantumState ι d) :
    finiteQuantumTailCharge i (finiteQuantumShift j a) =
      finiteQuantumTailCharge i a - 1 := by
  classical
  let s : Finset ι := Finset.univ.filter (i < ·)
  have hjs : j ∈ s := by simp [s, hij]
  calc
    finiteQuantumTailCharge i (finiteQuantumShift j a) =
        ∑ k ∈ s, (a k - if k = j then 1 else 0) := by
      unfold finiteQuantumTailCharge
      change (∑ k ∈ s, finiteQuantumShift j a k) = _
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkj : k = j
      · subst k
        simp [finiteQuantumShift]
      · simp [finiteQuantumShift, hkj]
    _ = (∑ k ∈ s, a k) - ∑ k ∈ s, (if k = j then 1 else 0) := by
      rw [Finset.sum_sub_distrib]
    _ = finiteQuantumTailCharge i a - 1 := by
      simp [finiteQuantumTailCharge, s, hjs]

/-- The root-of-unity additive character used as the clock phase. -/
def finiteQuantumCharacter (d : ℕ) [NeZero d] (q : K) (hq : q ^ d = 1) :
    AddChar (ZMod d) K :=
  AddChar.zmodChar d hq

@[simp]
theorem finiteQuantumCharacter_zero
    (q : K) (hq : q ^ d = 1) :
    finiteQuantumCharacter d q hq 0 = 1 := by
  exact AddChar.map_zero_eq_one _

@[simp]
theorem finiteQuantumCharacter_one
    (q : K) (hq : q ^ d = 1) :
    finiteQuantumCharacter d q hq 1 = q := by
  simpa [finiteQuantumCharacter] using
    (AddChar.zmodChar_apply' (C := K) hq 1)

theorem finiteQuantumCharacter_sub_one_mul
    (q : K) (hq : q ^ d = 1) (x : ZMod d) :
    finiteQuantumCharacter d q hq (x - 1) * q =
      finiteQuantumCharacter d q hq x := by
  have hmap := AddChar.map_add_eq_mul
    (finiteQuantumCharacter d q hq) (x - 1) 1
  simpa using hmap.symm

/-- The `i`th finite quantum-torus generator. -/
def finiteQuantumGenerator
    (d : ℕ) [NeZero d] (q : K) (hq : q ^ d = 1) (i : ι) :
    Module.End K (FiniteQuantumState ι d → K) where
  toFun f a :=
    finiteQuantumCharacter d q hq (finiteQuantumTailCharge i a) *
      f (finiteQuantumShift i a)
  map_add' f g := by
    funext a
    simp [mul_add]
  map_smul' c f := by
    funext a
    simp
    ring

/-- The finite generators satisfy the required ordered `q`-commutation law. -/
theorem finiteQuantumGenerator_mul_of_lt
    (q : K) (hq : q ^ d = 1) {i j : ι} (hij : i < j) :
    finiteQuantumGenerator d q hq i * finiteQuantumGenerator d q hq j =
      q • (finiteQuantumGenerator d q hq j * finiteQuantumGenerator d q hq i) := by
  apply LinearMap.ext
  intro f
  funext a
  simp only [Module.End.mul_apply, finiteQuantumGenerator, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply]
  rw [finiteQuantumTailCharge_shift_lower hij,
    finiteQuantumTailCharge_shift_member hij,
    finiteQuantumShift_comm (ne_of_lt hij)]
  have hphase := finiteQuantumCharacter_sub_one_mul q hq
    (finiteQuantumTailCharge i a)
  calc
    finiteQuantumCharacter d q hq (finiteQuantumTailCharge i a) *
          (finiteQuantumCharacter d q hq (finiteQuantumTailCharge j a) *
            f (finiteQuantumShift j (finiteQuantumShift i a))) =
        finiteQuantumCharacter d q hq (finiteQuantumTailCharge j a) *
          (finiteQuantumCharacter d q hq (finiteQuantumTailCharge i a) *
            f (finiteQuantumShift j (finiteQuantumShift i a))) := by ring
    _ = q *
        (finiteQuantumCharacter d q hq (finiteQuantumTailCharge j a) *
          (finiteQuantumCharacter d q hq (finiteQuantumTailCharge i a - 1) *
            f (finiteQuantumShift j (finiteQuantumShift i a)))) := by
      rw [← hphase]
      ring

/-- The phase-space state recording an increasing coordinate pair. -/
def finiteQuantumPairState (p : QuantumLawPair ι) : FiniteQuantumState ι d :=
  Function.update (Function.update 0 p.lower 1) p.upper 1

@[simp]
theorem finiteQuantumPairState_lower (p : QuantumLawPair ι) :
    finiteQuantumPairState (d := d) p p.lower = 1 := by
  simp [finiteQuantumPairState, ne_of_lt p.isLt]

@[simp]
theorem finiteQuantumPairState_upper (p : QuantumLawPair ι) :
    finiteQuantumPairState (d := d) p p.upper = 1 := by
  simp [finiteQuantumPairState]

theorem finiteQuantumPairState_eq_one_iff
    (p : QuantumLawPair ι) (k : ι) :
    finiteQuantumPairState (d := d) p k = 1 ↔
      k = p.lower ∨ k = p.upper := by
  by_cases hku : k = p.upper
  · subst k
    simp
  · by_cases hkl : k = p.lower
    · subst k
      simp
    · simp [finiteQuantumPairState, hku, hkl]

theorem finiteQuantumPairState_injective :
    Function.Injective (finiteQuantumPairState (d := d) :
      QuantumLawPair ι → FiniteQuantumState ι d) := by
  intro p r hpr
  have hset : ({p.lower, p.upper} : Set ι) = {r.lower, r.upper} := by
    ext k
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [← finiteQuantumPairState_eq_one_iff (d := d) p k,
      hpr, finiteQuantumPairState_eq_one_iff (d := d) r k]
  rcases Set.pair_eq_pair_iff.mp hset with hsame | hswap
  · cases p
    cases r
    simp_all
  · have hback : p.upper < p.lower := by
      calc
        p.upper = r.lower := hswap.2
        _ < r.upper := r.isLt
        _ = p.lower := hswap.1.symm
    exact (lt_asymm p.isLt hback).elim

/-- The delta state at the phase-space origin. -/
def finiteQuantumRoot : FiniteQuantumState ι d → K :=
  Pi.basisFun K (FiniteQuantumState ι d) 0

theorem finiteQuantumPair_doubleShift_eq_zero_iff
    (p : QuantumLawPair ι) (a : FiniteQuantumState ι d) :
    finiteQuantumShift p.lower (finiteQuantumShift p.upper a) = 0 ↔
      a = finiteQuantumPairState (d := d) p := by
  constructor
  · intro h
    funext k
    by_cases hkl : k = p.lower
    · subst k
      have hk := congrFun h p.lower
      have hlu : p.lower ≠ p.upper := ne_of_lt p.isLt
      simp [finiteQuantumShift, hlu] at hk
      simpa using (sub_eq_zero.mp hk)
    · by_cases hku : k = p.upper
      · subst k
        have hk := congrFun h p.upper
        have hul : p.upper ≠ p.lower := (ne_of_lt p.isLt).symm
        simp [finiteQuantumShift, hul] at hk
        simpa using (sub_eq_zero.mp hk)
      · have hk := congrFun h k
        simp [finiteQuantumShift, hkl, hku] at hk
        simpa [finiteQuantumPairState, hkl, hku] using hk
  · intro h
    subst a
    funext k
    by_cases hkl : k = p.lower
    · subst k
      simp [finiteQuantumShift, ne_of_lt p.isLt]
    · by_cases hku : k = p.upper
      · subst k
        simp [finiteQuantumShift, (ne_of_lt p.isLt).symm]
      · simp [finiteQuantumShift, finiteQuantumPairState, hkl, hku]

theorem finiteQuantumTailCharge_pairState_upper
    (p : QuantumLawPair ι) :
    finiteQuantumTailCharge p.upper (finiteQuantumPairState (d := d) p) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro k hk
  have huk : p.upper < k := by simpa using hk
  have hkl : k ≠ p.lower := ne_of_gt (lt_trans p.isLt huk)
  have hku : k ≠ p.upper := ne_of_gt huk
  simp [finiteQuantumPairState, hkl, hku]

theorem finiteQuantumTailCharge_shiftUpper_pairState_lower
    (p : QuantumLawPair ι) :
    finiteQuantumTailCharge p.lower
        (finiteQuantumShift p.upper (finiteQuantumPairState (d := d) p)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro k hk
  have hlk : p.lower < k := by simpa using hk
  by_cases hku : k = p.upper
  · subst k
    simp [finiteQuantumShift]
  · have hkl : k ≠ p.lower := ne_of_gt hlk
    simp [finiteQuantumShift, finiteQuantumPairState, hkl, hku]

/-- An ordered quadratic monomial sends the origin delta state to its distinct pair state. -/
theorem finiteQuantumPairOperator_root
    (q : K) (hq : q ^ d = 1) (p : QuantumLawPair ι) :
    quantumPairOperator (fun i : ι ↦ finiteQuantumGenerator d q hq i) p
        (finiteQuantumRoot (K := K) (ι := ι) (d := d)) =
      Pi.basisFun K (FiniteQuantumState ι d)
        (finiteQuantumPairState (d := d) p) := by
  funext a
  simp only [quantumPairOperator, Module.End.mul_apply, finiteQuantumGenerator,
    LinearMap.coe_mk, AddHom.coe_mk]
  by_cases ha :
      finiteQuantumShift p.lower (finiteQuantumShift p.upper a) = 0
  · have ha' := (finiteQuantumPair_doubleShift_eq_zero_iff (d := d) p a).mp ha
    subst a
    rw [finiteQuantumTailCharge_pairState_upper,
      finiteQuantumTailCharge_shiftUpper_pairState_lower]
    rw [ha]
    simp [finiteQuantumRoot]
  · have ha' : a ≠ finiteQuantumPairState (d := d) p := by
      intro hap
      apply ha
      exact (finiteQuantumPair_doubleShift_eq_zero_iff (d := d) p a).2 hap
    simp [finiteQuantumRoot, ha, ha']

/-- The ordered quadratic monomials of the finite representation are linearly independent. -/
theorem finiteQuantumPairOperator_linearIndependent
    (q : K) (hq : q ^ d = 1) :
    LinearIndependent K
      (quantumPairOperator
        (fun i : ι ↦ finiteQuantumGenerator d q hq i)) := by
  apply LinearIndependent.of_comp
    (LinearMap.applyₗ (R := K) (finiteQuantumRoot (K := K) (ι := ι) (d := d)))
  have hbasis : LinearIndependent K
      (fun p : QuantumLawPair ι ↦
        Pi.basisFun K (FiniteQuantumState ι d)
          (finiteQuantumPairState (d := d) p)) :=
    (Pi.basisFun K (FiniteQuantumState ι d)).linearIndependent.comp
      (finiteQuantumPairState (d := d)) finiteQuantumPairState_injective
  simpa [Function.comp_def, finiteQuantumPairOperator_root] using hbasis

/-- **Unconditional finite quantum principal symbol.**  Every injective coefficient family has a
finite cyclic quantum realization with injective internal exterior commutator symbol. -/
theorem finiteQuantumTorus_endomorphismCommutatorMap_injective
    {V : Type*} [AddCommGroup V] [Module K V]
    (q : K) (hqpow : q ^ d = 1) (hq : q ≠ 1)
    (L : V →ₗ[K] (ι → K)) (hL : Function.Injective L) :
    Function.Injective
      (endomorphismCommutatorMap
        ((quantumGeneratorSymbol
          (fun i : ι ↦ finiteQuantumGenerator d q hqpow i)).comp L)) := by
  exact quantumTorus_endomorphismCommutatorMap_injective
    q (fun i : ι ↦ finiteQuantumGenerator d q hqpow i) L hL hq
    (fun i j hij ↦ finiteQuantumGenerator_mul_of_lt q hqpow hij)
    (finiteQuantumPairOperator_linearIndependent q hqpow)

/-- The same finite packet gives maximal exterior commutator rank after rational-field shift
suspension. -/
theorem finiteQuantumTorus_derivationCommutatorMap_injective
    {V : Type*} [AddCommGroup V] [Module K V]
    (q : K) (hqpow : q ^ d = 1) (hq : q ≠ 1)
    (L : V →ₗ[K] (ι → K)) (hL : Function.Injective L) :
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          ((quantumGeneratorSymbol
            (fun i : ι ↦ finiteQuantumGenerator d q hqpow i)).comp L))) := by
  exact quantumTorus_derivationCommutatorMap_injective
    q (fun i : ι ↦ finiteQuantumGenerator d q hqpow i) L hL hq
    (fun i j hij ↦ finiteQuantumGenerator_mul_of_lt q hqpow hij)
    (finiteQuantumPairOperator_linearIndependent q hqpow)

/-- Decrement one cyclic coordinate `n` times at once. -/
def finiteQuantumShiftN (n : ℕ) (i : ι) (a : FiniteQuantumState ι d) :
    FiniteQuantumState ι d :=
  Function.update a i (a i - n)

@[simp]
theorem finiteQuantumShiftN_zero (i : ι) (a : FiniteQuantumState ι d) :
    finiteQuantumShiftN 0 i a = a := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [finiteQuantumShiftN]
  · simp [finiteQuantumShiftN, hki]

theorem finiteQuantumShift_shiftN
    (n : ℕ) (i : ι) (a : FiniteQuantumState ι d) :
    finiteQuantumShift i (finiteQuantumShiftN n i a) =
      finiteQuantumShiftN (n + 1) i a := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [finiteQuantumShift, finiteQuantumShiftN]
    ring
  · simp [finiteQuantumShift, finiteQuantumShiftN, hki]

theorem finiteQuantumTailCharge_shiftN
    (n : ℕ) (i : ι) (a : FiniteQuantumState ι d) :
    finiteQuantumTailCharge i (finiteQuantumShiftN n i a) =
      finiteQuantumTailCharge i a := by
  classical
  apply Finset.sum_congr rfl
  intro k hk
  have hik : i < k := by simpa using hk
  have hki : k ≠ i := ne_of_gt hik
  simp [finiteQuantumShiftN, hki]

/-- Closed formula for every power of one finite quantum generator. -/
theorem finiteQuantumGenerator_pow_apply
    (q : K) (hqpow : q ^ d = 1) (i : ι) (n : ℕ)
    (f : FiniteQuantumState ι d → K) (a : FiniteQuantumState ι d) :
    ((finiteQuantumGenerator d q hqpow i) ^ n) f a =
      (finiteQuantumCharacter d q hqpow (finiteQuantumTailCharge i a)) ^ n *
        f (finiteQuantumShiftN n i a) := by
  induction n generalizing f a with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, ih]
      change
        (finiteQuantumCharacter d q hqpow (finiteQuantumTailCharge i a)) ^ n *
            (finiteQuantumCharacter d q hqpow
              (finiteQuantumTailCharge i (finiteQuantumShiftN n i a)) *
              f (finiteQuantumShift i (finiteQuantumShiftN n i a))) = _
      rw [finiteQuantumTailCharge_shiftN, finiteQuantumShift_shiftN]
      simp only [Nat.succ_eq_add_one, pow_succ]
      ring

theorem finiteQuantumCharacter_pow_degree
    (q : K) (hqpow : q ^ d = 1) (x : ZMod d) :
    (finiteQuantumCharacter d q hqpow x) ^ d = 1 := by
  rw [finiteQuantumCharacter, AddChar.zmodChar_apply]
  calc
    (q ^ x.val) ^ d = q ^ (x.val * d) := by rw [pow_mul]
    _ = q ^ (d * x.val) := by rw [Nat.mul_comm]
    _ = (q ^ d) ^ x.val := by rw [pow_mul]
    _ = 1 := by rw [hqpow, one_pow]

@[simp]
theorem finiteQuantumShiftN_degree
    (i : ι) (a : FiniteQuantumState ι d) :
    finiteQuantumShiftN d i a = a := by
  funext k
  by_cases hki : k = i
  · subst k
    simp [finiteQuantumShiftN]
  · simp [finiteQuantumShiftN, hki]

/-- Every finite generator has exact order dividing `d`. -/
theorem finiteQuantumGenerator_pow_degree
    (q : K) (hqpow : q ^ d = 1) (i : ι) :
    (finiteQuantumGenerator d q hqpow i) ^ d = 1 := by
  apply LinearMap.ext
  intro f
  funext a
  rw [finiteQuantumGenerator_pow_apply,
    finiteQuantumCharacter_pow_degree, finiteQuantumShiftN_degree]
  simp

end

end GaloisForLFunctions.HTGeometry
