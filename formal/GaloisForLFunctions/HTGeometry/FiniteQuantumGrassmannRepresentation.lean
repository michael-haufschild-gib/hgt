import GaloisForLFunctions.HTGeometry.FiniteQuantumTorusRepresentation
import GaloisForLFunctions.HTGeometry.QuantumBinomialRootOfUnity

/-!
# A finite nilpotent quantum-Grassmann detector

The cyclic quantum-torus phase space becomes a generalized Grassmann packet by killing a
generator whenever its shifted coordinate is already zero.  The same tail-charge cocycle gives
ordered `q`-commutation, while the boundary makes every generator nilpotent of order `d`.
Ordered quadratic monomials still send the vacuum to distinct pair states, so the exterior
commutator symbol remains information-complete.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K]
  {d : ℕ} [NeZero d] [Fact (1 < d)]
  {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- A boundary-killed version of the finite quantum-torus generator. -/
def finiteQuantumGrassmannGenerator
    (d : ℕ) [NeZero d] (q : K) (hq : q ^ d = 1) (i : ι) :
    Module.End K (FiniteQuantumState ι d → K) where
  toFun f a :=
    if a i = 0 then 0
    else finiteQuantumCharacter d q hq (finiteQuantumTailCharge i a) *
      f (finiteQuantumShift i a)
  map_add' f g := by
    funext a
    by_cases h : a i = 0
    · simp [h]
    · simp [h, mul_add]
  map_smul' c f := by
    funext a
    by_cases h : a i = 0
    · simp [h]
    · simp [h]
      ring

omit [CharZero K] [Fact (1 < d)] in
/-- Boundary killing does not disturb the ordered quantum-torus commutation law. -/
theorem finiteQuantumGrassmannGenerator_mul_of_lt
    (q : K) (hq : q ^ d = 1) {i j : ι} (hij : i < j) :
    finiteQuantumGrassmannGenerator d q hq i *
        finiteQuantumGrassmannGenerator d q hq j =
      q • (finiteQuantumGrassmannGenerator d q hq j *
        finiteQuantumGrassmannGenerator d q hq i) := by
  apply LinearMap.ext
  intro f
  funext a
  have hijne : i ≠ j := ne_of_lt hij
  have hjine : j ≠ i := hijne.symm
  by_cases hi : a i = 0
  · have hiShift : finiteQuantumShift j a i = 0 := by
      rw [finiteQuantumShift_apply_of_ne hijne]
      exact hi
    simp [finiteQuantumGrassmannGenerator, Module.End.mul_apply, hi, hiShift]
  · by_cases hj : a j = 0
    · have hjShift : finiteQuantumShift i a j = 0 := by
        rw [finiteQuantumShift_apply_of_ne hjine]
        exact hj
      simp [finiteQuantumGrassmannGenerator, Module.End.mul_apply, hj, hjShift]
    · have hiShift : finiteQuantumShift j a i ≠ 0 := by
        rw [finiteQuantumShift_apply_of_ne hijne]
        exact hi
      have hjShift : finiteQuantumShift i a j ≠ 0 := by
        rw [finiteQuantumShift_apply_of_ne hjine]
        exact hj
      simp only [Module.End.mul_apply, finiteQuantumGrassmannGenerator,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply,
        if_neg hi, if_neg hj, if_neg hiShift, if_neg hjShift]
      rw [finiteQuantumTailCharge_shift_lower hij,
        finiteQuantumTailCharge_shift_member hij,
        finiteQuantumShift_comm hijne]
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

omit [Fintype ι] in
theorem finiteQuantumShift_val_sub_one
    (i : ι) (a : FiniteQuantumState ι d) (hi : a i ≠ 0) :
    (finiteQuantumShift i a i).val = (a i).val - 1 := by
  rw [finiteQuantumShift_apply_same]
  have hpos : 0 < (a i).val := by
    exact (ZMod.val_pos.mpr hi)
  have hone : (1 : ZMod d).val ≤ (a i).val := by
    rw [ZMod.val_one]
    exact hpos
  rw [ZMod.val_sub hone]
  simp only [ZMod.val_one]

omit [CharZero K] in
/-- At a state of height `r`, `r+1` applications of the boundary-killed generator vanish. -/
theorem finiteQuantumGrassmannGenerator_pow_succ_val_apply
    (q : K) (hq : q ^ d = 1) (i : ι)
    (f : FiniteQuantumState ι d → K) (a : FiniteQuantumState ι d) :
    ((finiteQuantumGrassmannGenerator d q hq i) ^ ((a i).val + 1)) f a = 0 := by
  induction hval : (a i).val using Nat.strong_induction_on generalizing a f with
  | h r ih =>
      by_cases hi : a i = 0
      · have hr : r = 0 := by simpa [hi] using hval.symm
        subst r
        simp [finiteQuantumGrassmannGenerator, hi]
      · have hrpos : 0 < r := by
          rw [← hval]
          exact ZMod.val_pos.mpr hi
        rw [show r + 1 = 1 + (r - 1 + 1) by omega, pow_add,
          Module.End.mul_apply]
        change finiteQuantumGrassmannGenerator d q hq i
          (((finiteQuantumGrassmannGenerator d q hq i) ^ (r - 1 + 1)) f) a = 0
        simp only [finiteQuantumGrassmannGenerator, LinearMap.coe_mk, AddHom.coe_mk,
          if_neg hi]
        have hshift : (finiteQuantumShift i a i).val = r - 1 := by
          rw [finiteQuantumShift_val_sub_one i a hi, hval]
        have hzero := ih (r - 1) (by omega)
          f (finiteQuantumShift i a) hshift
        change finiteQuantumCharacter d q hq (finiteQuantumTailCharge i a) *
          ((finiteQuantumGrassmannGenerator d q hq i) ^ (r - 1 + 1)) f
            (finiteQuantumShift i a) = 0
        rw [hzero, mul_zero]

omit [CharZero K] in
/-- Every boundary-killed generator has `d`th power zero. -/
theorem finiteQuantumGrassmannGenerator_pow_degree
    (q : K) (hq : q ^ d = 1) (i : ι) :
    (finiteQuantumGrassmannGenerator d q hq i) ^ d = 0 := by
  apply LinearMap.ext
  intro f
  funext a
  change ((finiteQuantumGrassmannGenerator d q hq i) ^ d) f a = 0
  have hle : (a i).val + 1 ≤ d := Nat.succ_le_iff.mpr (ZMod.val_lt (a i))
  let G := finiteQuantumGrassmannGenerator d q hq i
  change (G ^ d) f a = 0
  have hd : d = ((a i).val + 1) + (d - ((a i).val + 1)) := by omega
  have hpow : G ^ d = G ^ (((a i).val + 1) + (d - ((a i).val + 1))) :=
    congrArg (fun e : ℕ ↦ G ^ e) hd
  rw [hpow, pow_add, Module.End.mul_apply]
  exact finiteQuantumGrassmannGenerator_pow_succ_val_apply q hq i _ a

omit [CharZero K] in
/-- Ordered quadratic Grassmann monomials retain the same exact pair-state vacuum readout as the
cyclic quantum-torus packet. -/
theorem finiteQuantumGrassmannPairOperator_root
    (q : K) (hq : q ^ d = 1) (p : QuantumLawPair ι) :
    quantumPairOperator
        (fun i : ι ↦ finiteQuantumGrassmannGenerator d q hq i) p
        (finiteQuantumRoot (K := K) (ι := ι) (d := d)) =
      Pi.basisFun K (FiniteQuantumState ι d)
        (finiteQuantumPairState (d := d) p) := by
  funext a
  simp only [quantumPairOperator, Module.End.mul_apply,
    finiteQuantumGrassmannGenerator, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases ha :
      finiteQuantumShift p.lower (finiteQuantumShift p.upper a) = 0
  · have ha' := (finiteQuantumPair_doubleShift_eq_zero_iff (d := d) p a).mp ha
    subst a
    have hl : finiteQuantumPairState (d := d) p p.lower ≠ 0 := by simp
    have hu : finiteQuantumPairState (d := d) p p.upper ≠ 0 := by simp
    have hlShift :
        finiteQuantumShift p.upper (finiteQuantumPairState (d := d) p) p.lower ≠ 0 := by
      rw [finiteQuantumShift_apply_of_ne (ne_of_lt p.isLt)]
      exact hl
    rw [if_neg hu, if_neg hlShift,
      finiteQuantumTailCharge_pairState_upper,
      finiteQuantumTailCharge_shiftUpper_pairState_lower]
    rw [ha]
    simp [finiteQuantumRoot]
  · have ha' : a ≠ finiteQuantumPairState (d := d) p := by
      intro hap
      apply ha
      exact (finiteQuantumPair_doubleShift_eq_zero_iff (d := d) p a).2 hap
    simp [finiteQuantumRoot, ha, ha']

omit [CharZero K] in
/-- Ordered quadratic monomials of the nilpotent detector are linearly independent. -/
theorem finiteQuantumGrassmannPairOperator_linearIndependent
    (q : K) (hq : q ^ d = 1) :
    LinearIndependent K
      (quantumPairOperator
        (fun i : ι ↦ finiteQuantumGrassmannGenerator d q hq i)) := by
  apply LinearIndependent.of_comp
    (LinearMap.applyₗ (R := K) (finiteQuantumRoot (K := K) (ι := ι) (d := d)))
  have hbasis : LinearIndependent K
      (fun p : QuantumLawPair ι ↦
        Pi.basisFun K (FiniteQuantumState ι d)
          (finiteQuantumPairState (d := d) p)) :=
    (Pi.basisFun K (FiniteQuantumState ι d)).linearIndependent.comp
      (finiteQuantumPairState (d := d)) finiteQuantumPairState_injective
  simpa [Function.comp_def, finiteQuantumGrassmannPairOperator_root] using hbasis

/-- Every linear combination of a finite ordered Grassmann family has `d`th power zero. -/
theorem finiteQuantumGrassmannSymbol_pow_degree_zero
    (q : K) (hq : IsPrimitiveRoot q d) (c : Fin n → K) :
    (quantumGeneratorSymbol
      (fun i : Fin n ↦ finiteQuantumGrassmannGenerator d q hq.pow_eq_one i) c) ^ d = 0 := by
  rw [quantumGeneratorSymbol, Fintype.linearCombination_apply,
    quantumMultinomial_fin_smul_pow_primitive hq
      (lt_trans Nat.zero_lt_one Fact.out)
      (fun i : Fin n ↦ finiteQuantumGrassmannGenerator d q hq.pow_eq_one i) c
      (fun i j hij ↦
        finiteQuantumGrassmannGenerator_mul_of_lt q hq.pow_eq_one hij)]
  simp [finiteQuantumGrassmannGenerator_pow_degree]

omit [CharZero K] in
/-- The nilpotent packet is an information-complete exterior detector despite carrying the zero
scalar degree-`d` form. -/
theorem finiteQuantumGrassmann_endomorphismCommutatorMap_injective
    (q : K) (hq : IsPrimitiveRoot q d) :
    Function.Injective
      (endomorphismCommutatorMap
        (quantumGeneratorSymbol
          (fun i : ι ↦ finiteQuantumGrassmannGenerator d q hq.pow_eq_one i))) := by
  exact quantumGenerator_endomorphismCommutatorMap_injective
    q (fun i : ι ↦ finiteQuantumGrassmannGenerator d q hq.pow_eq_one i)
    (hq.ne_one Fact.out)
    (fun i j hij ↦ finiteQuantumGrassmannGenerator_mul_of_lt q hq.pow_eq_one hij)
    (finiteQuantumGrassmannPairOperator_linearIndependent q hq.pow_eq_one)

end

end GaloisForLFunctions.HTGeometry
