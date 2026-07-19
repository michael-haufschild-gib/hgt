import GaloisForLFunctions.HTGeometry.FiniteQuantumGrassmannRepresentation
import GaloisForLFunctions.HTGeometry.GeneralExteriorPrincipalSymbolDecoder
import GaloisForLFunctions.HTGeometry.CyclicClockLift

/-!
# Universal principal-symbol completion

An arbitrary scalar generalized-Clifford pencil is coupled to a finite nilpotent detector.  A
clock phase makes the scalar and detector sectors `q`-commute, so primitive-order cancellation
preserves the original scalar power relation exactly.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {M : Type v} [AddCommGroup M] [Module K M]
  {d n : ℕ} [NeZero d] [Fact (1 < d)]

/-- The finite state space of the clocked nilpotent completion. -/
abbrev QuantumPrincipalCompletionState (M : Type v) (n d : ℕ) :=
  CyclicClockState M (FiniteQuantumState (Fin n) d) d

/-- A nilpotent detector generator that also shifts the cyclic clock coordinate. -/
def quantumCompletionDetectorGenerator
    (q : K) (hq : q ^ d = 1) (i : Fin n) :
    Module.End K (QuantumPrincipalCompletionState M n d) where
  toFun f a k :=
    if a i = 0 then 0
    else finiteQuantumCharacter d q hq (finiteQuantumTailCharge i a) •
      f (finiteQuantumShift i a) (k - 1)
  map_add' f g := by
    funext a k
    by_cases hi : a i = 0
    · simp [hi]
    · simp [hi, smul_add]
  map_smul' c f := by
    funext a k
    by_cases hi : a i = 0
    · simp [hi]
    · simp [hi, smul_smul]
      ring

/-- The clocked detector retains ordered `q`-commutation. -/
theorem quantumCompletionDetectorGenerator_mul_of_lt
    (q : K) (hq : q ^ d = 1) {i j : Fin n} (hij : i < j) :
    quantumCompletionDetectorGenerator (M := M) q hq i *
        quantumCompletionDetectorGenerator (M := M) q hq j =
      q • (quantumCompletionDetectorGenerator (M := M) q hq j *
        quantumCompletionDetectorGenerator (M := M) q hq i) := by
  apply LinearMap.ext
  intro f
  funext a k
  have hijne : i ≠ j := ne_of_lt hij
  have hjine : j ≠ i := hijne.symm
  by_cases hi : a i = 0
  · have hiShift : finiteQuantumShift j a i = 0 := by
      rw [finiteQuantumShift_apply_of_ne hijne]
      exact hi
    simp [quantumCompletionDetectorGenerator, Module.End.mul_apply, hi, hiShift]
  · by_cases hj : a j = 0
    · have hjShift : finiteQuantumShift i a j = 0 := by
        rw [finiteQuantumShift_apply_of_ne hjine]
        exact hj
      simp [quantumCompletionDetectorGenerator, Module.End.mul_apply, hj, hjShift]
    · have hiShift : finiteQuantumShift j a i ≠ 0 := by
        rw [finiteQuantumShift_apply_of_ne hijne]
        exact hi
      have hjShift : finiteQuantumShift i a j ≠ 0 := by
        rw [finiteQuantumShift_apply_of_ne hjine]
        exact hj
      simp only [Module.End.mul_apply, quantumCompletionDetectorGenerator,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply,
        if_neg hi, if_neg hj, if_neg hiShift, if_neg hjShift]
      rw [finiteQuantumTailCharge_shift_lower hij,
        finiteQuantumTailCharge_shift_member hij,
        finiteQuantumShift_comm hijne]
      have hphase := finiteQuantumCharacter_sub_one_mul q hq
        (finiteQuantumTailCharge i a)
      rw [← hphase]
      module

/-- At coordinate height `r`, the clocked detector is killed after `r+1` applications. -/
theorem quantumCompletionDetectorGenerator_pow_succ_val_apply
    (q : K) (hq : q ^ d = 1) (i : Fin n)
    (f : QuantumPrincipalCompletionState M n d)
    (a : FiniteQuantumState (Fin n) d) (k : ZMod d) :
    ((quantumCompletionDetectorGenerator (M := M) q hq i) ^ ((a i).val + 1)) f a k = 0 := by
  induction hval : (a i).val using Nat.strong_induction_on generalizing a f k with
  | h r ih =>
      by_cases hi : a i = 0
      · have hr : r = 0 := by simpa [hi] using hval.symm
        subst r
        simp [quantumCompletionDetectorGenerator, hi]
      · have hrpos : 0 < r := by
          rw [← hval]
          exact ZMod.val_pos.mpr hi
        rw [show r + 1 = 1 + (r - 1 + 1) by omega, pow_add,
          Module.End.mul_apply]
        change quantumCompletionDetectorGenerator (M := M) q hq i
          (((quantumCompletionDetectorGenerator (M := M) q hq i) ^ (r - 1 + 1)) f) a k = 0
        simp only [quantumCompletionDetectorGenerator, LinearMap.coe_mk, AddHom.coe_mk,
          if_neg hi]
        have hshift : (finiteQuantumShift i a i).val = r - 1 := by
          rw [finiteQuantumShift_val_sub_one i a hi, hval]
        have hzero := ih (r - 1) (by omega)
          f (finiteQuantumShift i a) (k - 1) hshift
        change finiteQuantumCharacter d q hq (finiteQuantumTailCharge i a) •
          ((quantumCompletionDetectorGenerator (M := M) q hq i) ^ (r - 1 + 1)) f
            (finiteQuantumShift i a) (k - 1) = 0
        rw [hzero, smul_zero]

/-- Every clocked detector generator has `d`th power zero. -/
theorem quantumCompletionDetectorGenerator_pow_degree
    (q : K) (hq : q ^ d = 1) (i : Fin n) :
    (quantumCompletionDetectorGenerator (M := M) q hq i) ^ d = 0 := by
  apply LinearMap.ext
  intro f
  funext a k
  change ((quantumCompletionDetectorGenerator (M := M) q hq i) ^ d) f a k = 0
  have hle : (a i).val + 1 ≤ d := Nat.succ_le_iff.mpr (ZMod.val_lt (a i))
  let G := quantumCompletionDetectorGenerator (M := M) q hq i
  change (G ^ d) f a k = 0
  have hd : d = ((a i).val + 1) + (d - ((a i).val + 1)) := by omega
  have hpow : G ^ d = G ^ (((a i).val + 1) + (d - ((a i).val + 1))) :=
    congrArg (fun e : ℕ ↦ G ^ e) hd
  rw [hpow, pow_add, Module.End.mul_apply]
  exact quantumCompletionDetectorGenerator_pow_succ_val_apply q hq i _ a k

/-- The clocked nilpotent detector pencil. -/
def quantumCompletionDetectorSymbol
    (q : K) (hq : q ^ d = 1) :
    (Fin n → K) →ₗ[K]
      Module.End K (QuantumPrincipalCompletionState M n d) :=
  quantumGeneratorSymbol
    (fun i : Fin n ↦ quantumCompletionDetectorGenerator (M := M) q hq i)

/-- Every value of the clocked detector pencil has `d`th power zero. -/
theorem quantumCompletionDetectorSymbol_pow_degree_zero
    (q : K) (hq : IsPrimitiveRoot q d) (c : Fin n → K) :
    (quantumCompletionDetectorSymbol (M := M) q hq.pow_eq_one c) ^ d = 0 := by
  rw [quantumCompletionDetectorSymbol, quantumGeneratorSymbol,
    Fintype.linearCombination_apply,
    quantumMultinomial_fin_smul_pow_primitive hq
      (lt_trans Nat.zero_lt_one Fact.out)
      (fun i : Fin n ↦ quantumCompletionDetectorGenerator (M := M) q hq.pow_eq_one i) c
      (fun i j hij ↦
        quantumCompletionDetectorGenerator_mul_of_lt q hq.pow_eq_one hij)]
  simp [quantumCompletionDetectorGenerator_pow_degree]

/-- The clock sector `q`-commutes with every detector generator. -/
theorem quantumCompletionClockLift_mul_detectorGenerator
    (q : K) (hq : q ^ d = 1) (A : Module.End K M) (i : Fin n) :
    cyclicClockLift (ι := FiniteQuantumState (Fin n) d) q hq A *
        quantumCompletionDetectorGenerator (M := M) q hq i =
      q • (quantumCompletionDetectorGenerator (M := M) q hq i *
        cyclicClockLift (ι := FiniteQuantumState (Fin n) d) q hq A) := by
  apply LinearMap.ext
  intro f
  funext a k
  by_cases hi : a i = 0
  · simp [cyclicClockLift, quantumCompletionDetectorGenerator,
      Module.End.mul_apply, hi]
  · simp only [Module.End.mul_apply, cyclicClockLift,
      quantumCompletionDetectorGenerator, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.smul_apply, Pi.smul_apply, if_neg hi, map_smul]
    have hclock := finiteQuantumCharacter_sub_one_mul q hq k
    rw [← hclock]
    module

/-- The clock sector `q`-commutes with every value of the detector pencil. -/
theorem quantumCompletionClockLift_mul_detectorSymbol
    (q : K) (hq : q ^ d = 1) (A : Module.End K M) (c : Fin n → K) :
    cyclicClockLift (ι := FiniteQuantumState (Fin n) d) q hq A *
        quantumCompletionDetectorSymbol (M := M) q hq c =
      q • (quantumCompletionDetectorSymbol (M := M) q hq c *
        cyclicClockLift (ι := FiniteQuantumState (Fin n) d) q hq A) := by
  classical
  rw [quantumCompletionDetectorSymbol, quantumGeneratorSymbol,
    Fintype.linearCombination_apply, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    cyclicClockLift (ι := FiniteQuantumState (Fin n) d) q hq A *
        (c i • quantumCompletionDetectorGenerator (M := M) q hq i) =
      c i • (cyclicClockLift (ι := FiniteQuantumState (Fin n) d) q hq A *
        quantumCompletionDetectorGenerator (M := M) q hq i) := by simp
    _ = c i • (q •
        (quantumCompletionDetectorGenerator (M := M) q hq i *
          cyclicClockLift (ι := FiniteQuantumState (Fin n) d) q hq A)) := by
      rw [quantumCompletionClockLift_mul_detectorGenerator]
    _ = q • ((c i • quantumCompletionDetectorGenerator (M := M) q hq i) *
        cyclicClockLift (ι := FiniteQuantumState (Fin n) d) q hq A) := by
      simp [smul_smul]
      congr 1
      ring

/-- Add the nilpotent detector to an arbitrary scalar pencil. -/
def quantumPrincipalSymbolCompletion
    (q : K) (hq : q ^ d = 1)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M) :
    (Fin n → K) →ₗ[K]
      Module.End K (QuantumPrincipalCompletionState M n d) :=
  (cyclicClockLiftLinear (ι := FiniteQuantumState (Fin n) d) q hq).comp A₀ +
    quantumCompletionDetectorSymbol (M := M) q hq

@[simp]
theorem quantumPrincipalSymbolCompletion_basisFun
    (q : K) (hq : q ^ d = 1)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M) (i : Fin n) :
    quantumPrincipalSymbolCompletion q hq A₀ (Pi.basisFun K (Fin n) i) =
      cyclicClockLift (ι := FiniteQuantumState (Fin n) d) q hq
          (A₀ (Pi.basisFun K (Fin n) i)) +
        quantumCompletionDetectorGenerator (M := M) q hq i := by
  classical
  simp [quantumPrincipalSymbolCompletion, quantumCompletionDetectorSymbol,
    quantumGeneratorSymbol, cyclicClockLiftLinear]

/-- **Scalar preservation under principal-symbol completion.**  The nilpotent detector changes no
degree-`d` scalar law. -/
theorem quantumPrincipalSymbolCompletion_pow
    (q : K) (hq : IsPrimitiveRoot q d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M) (F : (Fin n → K) → K)
    (hA₀ : ∀ c, (A₀ c) ^ d = F c • LinearMap.id) (c : Fin n → K) :
    (quantumPrincipalSymbolCompletion q hq.pow_eq_one A₀ c) ^ d =
      F c • LinearMap.id := by
  change (cyclicClockLift (ι := FiniteQuantumState (Fin n) d) q hq.pow_eq_one (A₀ c) +
    quantumCompletionDetectorSymbol (M := M) q hq.pow_eq_one c) ^ d = _
  rw [quantumBinomial_pow_primitive hq
      (lt_trans Nat.zero_lt_one Fact.out)
      (cyclicClockLift (ι := FiniteQuantumState (Fin n) d) q hq.pow_eq_one (A₀ c))
      (quantumCompletionDetectorSymbol (M := M) q hq.pow_eq_one c)
      (quantumCompletionClockLift_mul_detectorSymbol q hq.pow_eq_one (A₀ c) c),
    cyclicClockLift_pow_degree (ι := FiniteQuantumState (Fin n) d) q hq.pow_eq_one (A₀ c) (F c) (hA₀ c),
    quantumCompletionDetectorSymbol_pow_degree_zero q hq]
  simp

/-- Vacuum state for the completed packet. -/
def quantumPrincipalCompletionRoot (m : M) :
    QuantumPrincipalCompletionState M n d :=
  Pi.single 0 (Pi.single 0 m)

theorem quantumPrincipalCompletionRoot_ne_zero
    (m : M) (hm : m ≠ 0) :
    quantumPrincipalCompletionRoot (n := n) (d := d) m ≠ 0 := by
  classical
  intro hzero
  have hstate := congrFun hzero (0 : FiniteQuantumState (Fin n) d)
  have hclock := congrFun hstate (0 : ZMod d)
  exact hm (by simpa [quantumPrincipalCompletionRoot] using hclock)

theorem zmod_sub_one_sub_one_eq_zero_iff (k : ZMod d) :
    k - 1 - 1 = 0 ↔ k = 2 := by
  have htwo : (2 : ZMod d) = 1 + 1 := by norm_num
  constructor
  · intro h
    have h₁ : k - 1 = 1 := sub_eq_zero.mp h
    have h₂ : k = 1 + 1 := (sub_eq_iff_eq_add).mp h₁
    exact h₂.trans htwo.symm
  · intro h
    apply sub_eq_zero.mpr
    apply (sub_eq_iff_eq_add).mpr
    exact h.trans htwo

/-- The two detector shifts send the completed vacuum to the pair state at clock degree two. -/
theorem quantumCompletionDetectorPairOperator_root
    (q : K) (hq : q ^ d = 1) (m : M) (p : QuantumLawPair (Fin n)) :
    quantumPairOperator
        (fun i : Fin n ↦ quantumCompletionDetectorGenerator (M := M) q hq i) p
        (quantumPrincipalCompletionRoot (d := d) m) =
      Pi.single (finiteQuantumPairState (d := d) p)
        (Pi.single (2 : ZMod d) m) := by
  classical
  funext a k
  simp only [quantumPairOperator, Module.End.mul_apply,
    quantumCompletionDetectorGenerator, LinearMap.coe_mk, AddHom.coe_mk]
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
    by_cases hk : k = 2
    · subst k
      have htwo : (2 : ZMod d) - 1 - 1 = 0 :=
        (zmod_sub_one_sub_one_eq_zero_iff (2 : ZMod d)).2 rfl
      simp [quantumPrincipalCompletionRoot, htwo]
    · have hk' : k - 1 - 1 ≠ 0 := by
        exact fun h ↦ hk ((zmod_sub_one_sub_one_eq_zero_iff k).mp h)
      simp [quantumPrincipalCompletionRoot, hk, hk']
  · have ha' : a ≠ finiteQuantumPairState (d := d) p := by
      intro hap
      apply ha
      exact (finiteQuantumPair_doubleShift_eq_zero_iff (d := d) p a).2 hap
    simp [quantumPrincipalCompletionRoot, ha, ha']

/-- Read an endomorphism on the completed vacuum along all detector pair states. -/
def quantumPrincipalCompletionPairReadout (m : M) :
    Module.End K (QuantumPrincipalCompletionState M n d) →ₗ[K]
      (QuantumLawPair (Fin n) → ZMod d → M) where
  toFun T p k := T (quantumPrincipalCompletionRoot (d := d) m)
    (finiteQuantumPairState (d := d) p) k
  map_add' T U := by
    funext p k
    simp
  map_smul' c T := by
    funext p k
    simp

theorem finiteQuantumPairState_ne_zero (p : QuantumLawPair (Fin n)) :
    finiteQuantumPairState (d := d) p ≠ 0 := by
  intro h
  have hl := congrFun h p.lower
  simp at hl

theorem finiteQuantumShift_pairState_ne_zero_of_apply_ne_zero
    (p : QuantumLawPair (Fin n)) (i : Fin n)
    (hi : finiteQuantumPairState (d := d) p i ≠ 0) :
    finiteQuantumShift i (finiteQuantumPairState (d := d) p) ≠ 0 := by
  intro hzero
  by_cases hil : i = p.lower
  · subst i
    have hu := congrFun hzero p.upper
    simp [finiteQuantumShift, (ne_of_lt p.isLt).symm] at hu
  · by_cases hiu : i = p.upper
    · subst i
      have hl := congrFun hzero p.lower
      simp [finiteQuantumShift, ne_of_lt p.isLt] at hl
    · have : finiteQuantumPairState (d := d) p i = 0 := by
        simp [finiteQuantumPairState, hil, hiu]
      exact hi this

/-- Pair readout of one detector quadratic monomial is the corresponding standard pair state. -/
theorem quantumPrincipalCompletionPairReadout_detectorPair
    (q : K) (hq : q ^ d = 1) (m : M) (r : QuantumLawPair (Fin n)) :
    quantumPrincipalCompletionPairReadout (d := d) m
        (quantumPairOperator
          (fun i : Fin n ↦ quantumCompletionDetectorGenerator (M := M) q hq i) r) =
      Pi.single r (Pi.single (2 : ZMod d) m) := by
  classical
  funext p k
  change (quantumPairOperator
      (fun i : Fin n ↦ quantumCompletionDetectorGenerator (M := M) q hq i) r)
      (quantumPrincipalCompletionRoot (d := d) m)
      (finiteQuantumPairState (d := d) p) k = _
  rw [quantumCompletionDetectorPairOperator_root]
  by_cases hpr : p = r
  · subst p
    simp
  · have hstate : finiteQuantumPairState (d := d) p ≠
        finiteQuantumPairState (d := d) r :=
      fun h ↦ hpr (finiteQuantumPairState_injective h)
    simp [hpr, hstate]

/-- The scalar clock sector has no degree-two detector readout. -/
theorem quantumPrincipalCompletionPairReadout_clock_mul_clock
    (q : K) (hq : q ^ d = 1) (m : M) (A B : Module.End K M) :
    quantumPrincipalCompletionPairReadout (d := d) m
        (cyclicClockLift (ι := FiniteQuantumState (Fin n) d) q hq A *
          cyclicClockLift (ι := FiniteQuantumState (Fin n) d) q hq B) = 0 := by
  funext p k
  simp [quantumPrincipalCompletionPairReadout, Module.End.mul_apply,
    cyclicClockLift, quantumPrincipalCompletionRoot,
    finiteQuantumPairState_ne_zero]

/-- A clock-then-detector cross term has no degree-two detector readout. -/
theorem quantumPrincipalCompletionPairReadout_clock_mul_detector
    (q : K) (hq : q ^ d = 1) (m : M) (A : Module.End K M) (i : Fin n) :
    quantumPrincipalCompletionPairReadout (d := d) m
        (cyclicClockLift (ι := FiniteQuantumState (Fin n) d) q hq A *
          quantumCompletionDetectorGenerator (M := M) q hq i) = 0 := by
  funext p k
  by_cases hi : finiteQuantumPairState (d := d) p i = 0
  · simp [quantumPrincipalCompletionPairReadout, Module.End.mul_apply,
      cyclicClockLift, quantumCompletionDetectorGenerator, hi]
  · have hshift := finiteQuantumShift_pairState_ne_zero_of_apply_ne_zero p i hi
    simp [quantumPrincipalCompletionPairReadout, Module.End.mul_apply,
      cyclicClockLift, quantumCompletionDetectorGenerator,
      quantumPrincipalCompletionRoot, hi, hshift]

/-- A detector-then-clock cross term has no degree-two detector readout. -/
theorem quantumPrincipalCompletionPairReadout_detector_mul_clock
    (q : K) (hq : q ^ d = 1) (m : M) (A : Module.End K M) (i : Fin n) :
    quantumPrincipalCompletionPairReadout (d := d) m
        (quantumCompletionDetectorGenerator (M := M) q hq i *
          cyclicClockLift (ι := FiniteQuantumState (Fin n) d) q hq A) = 0 := by
  funext p k
  by_cases hi : finiteQuantumPairState (d := d) p i = 0
  · simp [quantumPrincipalCompletionPairReadout, Module.End.mul_apply,
      cyclicClockLift, quantumCompletionDetectorGenerator, hi]
  · have hshift := finiteQuantumShift_pairState_ne_zero_of_apply_ne_zero p i hi
    simp [quantumPrincipalCompletionPairReadout, Module.End.mul_apply,
      cyclicClockLift, quantumCompletionDetectorGenerator,
      quantumPrincipalCompletionRoot, hi, hshift]

/-- The pair readout sees the detector commutator as one nonzero coordinate vector. -/
theorem quantumPrincipalCompletionPairReadout_detectorBracket
    (q : K) (hq : q ^ d = 1) (m : M) (r : QuantumLawPair (Fin n)) :
    quantumPrincipalCompletionPairReadout (d := d) m
        (quantumCompletionDetectorGenerator (M := M) q hq r.lower *
            quantumCompletionDetectorGenerator (M := M) q hq r.upper -
          quantumCompletionDetectorGenerator (M := M) q hq r.upper *
            quantumCompletionDetectorGenerator (M := M) q hq r.lower) =
      (q - 1) • Pi.single r (Pi.single (2 : ZMod d) m) := by
  classical
  rw [quantumCompletionDetectorGenerator_mul_of_lt q hq r.isLt,
    map_sub, map_smul]
  change q • quantumPrincipalCompletionPairReadout (d := d) m
      (quantumPairOperator
        (fun i : Fin n ↦ quantumCompletionDetectorGenerator (M := M) q hq i) r) -
    quantumPrincipalCompletionPairReadout (d := d) m
      (quantumPairOperator
        (fun i : Fin n ↦ quantumCompletionDetectorGenerator (M := M) q hq i) r) = _
  rw [quantumPrincipalCompletionPairReadout_detectorPair]
  module

/-- Every completed coordinate commutator has a detector-only standard-coordinate readout. -/
theorem quantumPrincipalCompletionPairReadout_principalBracketPair
    (q : K) (hq : q ^ d = 1)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M) (m : M)
    (r : QuantumLawPair (Fin n)) :
    quantumPrincipalCompletionPairReadout (d := d) m
        (principalBracketPair (quantumPrincipalSymbolCompletion q hq A₀) r) =
      (q - 1) • Pi.single r (Pi.single (2 : ZMod d) m) := by
  classical
  rw [principalBracketPair,
    quantumPrincipalSymbolCompletion_basisFun,
    quantumPrincipalSymbolCompletion_basisFun]
  simp only [mul_add, add_mul, map_sub, map_add]
  rw [quantumPrincipalCompletionPairReadout_clock_mul_clock,
    quantumPrincipalCompletionPairReadout_clock_mul_detector,
    quantumPrincipalCompletionPairReadout_detector_mul_clock,
    quantumPrincipalCompletionPairReadout_clock_mul_clock,
    quantumPrincipalCompletionPairReadout_clock_mul_detector,
    quantumPrincipalCompletionPairReadout_detector_mul_clock]
  simpa using quantumPrincipalCompletionPairReadout_detectorBracket
    (d := d) q hq m r

/-- The coordinate commutators of the universal completion are linearly independent. -/
theorem quantumPrincipalSymbolCompletion_principalBracketPair_linearIndependent
    (q : K) (hq : IsPrimitiveRoot q d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M)
    (m : M) (hm : m ≠ 0) :
    LinearIndependent K
      (principalBracketPair
        (quantumPrincipalSymbolCompletion q hq.pow_eq_one A₀)) := by
  classical
  apply LinearIndependent.of_comp
    (quantumPrincipalCompletionPairReadout (d := d) m)
  have hclock : (Pi.single (2 : ZMod d) m : ZMod d → M) ≠ 0 := by
    intro hzero
    have htwo := congrFun hzero (2 : ZMod d)
    apply hm
    simpa using htwo
  have hcoefficient : q - 1 ≠ 0 := sub_ne_zero.mpr (hq.ne_one Fact.out)
  have hcoordinate :
      ∀ _r : QuantumLawPair (Fin n),
        (q - 1) • (Pi.single (2 : ZMod d) m : ZMod d → M) ≠ 0 := by
    intro _r
    exact smul_ne_zero hcoefficient hclock
  have hsingle := Pi.linearIndependent_single_of_ne_zero (R := K) hcoordinate
  have heq :
      (fun r : QuantumLawPair (Fin n) ↦
        (q - 1) •
          (Pi.single r (Pi.single (2 : ZMod d) m : ZMod d → M) :
            QuantumLawPair (Fin n) → ZMod d → M)) =
      (fun r : QuantumLawPair (Fin n) ↦
        (Pi.single r ((q - 1) • (Pi.single (2 : ZMod d) m : ZMod d → M)) :
          QuantumLawPair (Fin n) → ZMod d → M)) := by
    funext r
    ext p k
    by_cases hpr : p = r <;> simp [Pi.single_apply, hpr]
  have hstandard : LinearIndependent K
      (fun r : QuantumLawPair (Fin n) ↦
        (q - 1) •
          (Pi.single r (Pi.single (2 : ZMod d) m : ZMod d → M) :
            QuantumLawPair (Fin n) → ZMod d → M)) := by
    rw [heq]
    exact hsingle
  simpa [Function.comp_def,
    quantumPrincipalCompletionPairReadout_principalBracketPair] using hstandard

/-- **Universal principal-symbol completion theorem.**  Every finite scalar pencil on a nonzero
state space admits an exact scalar-preserving completion whose full exterior commutator symbol is
injective.  No smoothness, Waring decomposition, or prior commutation law for the scalar pencil is
required. -/
theorem quantumPrincipalSymbolCompletion_endomorphismCommutatorMap_injective
    (q : K) (hq : IsPrimitiveRoot q d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M)
    (m : M) (hm : m ≠ 0) :
    Function.Injective
      (endomorphismCommutatorMap
        (quantumPrincipalSymbolCompletion q hq.pow_eq_one A₀)) :=
  endomorphismCommutatorMap_injective_of_principalBracketPair_linearIndependent
    (quantumPrincipalSymbolCompletion q hq.pow_eq_one A₀)
    (quantumPrincipalSymbolCompletion_principalBracketPair_linearIndependent
      q hq A₀ m hm)

/-- Scalar reality and maximal two-plane information coexist in one finite completion. -/
theorem quantumPrincipalSymbolCompletion_scalarLaw_and_maximalPrincipalSymbol
    (q : K) (hq : IsPrimitiveRoot q d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M)
    (F : (Fin n → K) → K)
    (hA₀ : ∀ c, (A₀ c) ^ d = F c • LinearMap.id)
    (m : M) (hm : m ≠ 0) :
    (∀ c, (quantumPrincipalSymbolCompletion q hq.pow_eq_one A₀ c) ^ d =
      F c • LinearMap.id) ∧
    Function.Injective
      (endomorphismCommutatorMap
        (quantumPrincipalSymbolCompletion q hq.pow_eq_one A₀)) := by
  exact ⟨quantumPrincipalSymbolCompletion_pow q hq A₀ F hA₀,
    quantumPrincipalSymbolCompletion_endomorphismCommutatorMap_injective q hq A₀ m hm⟩

/-- The scalar zero locus is the exact complete-jet dependence horizon of the universal
completion. -/
theorem quantumPrincipalSymbolCompletion_dependenceHorizon_eq_zeroLocus
    (q : K) (hq : IsPrimitiveRoot q d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M)
    (F : (Fin n → K) → K)
    (hA₀ : ∀ c, (A₀ c) ^ d = F c • LinearMap.id)
    (m : M) (hm : m ≠ 0) :
    {c : Fin n → K | ¬ AlgebraicIndependent K
      (generalizedCliffordShiftJet
        (quantumPrincipalSymbolCompletion q hq.pow_eq_one A₀ c)
        (quantumPrincipalCompletionRoot (n := n) (d := d) m))} =
      {c : Fin n → K | F c = 0} := by
  apply generalizedCliffordShift_dependenceHorizon_eq_zeroLocus
    (quantumPrincipalSymbolCompletion q hq.pow_eq_one A₀) F d
    (Nat.ne_of_gt (lt_trans Nat.zero_lt_one Fact.out))
    (quantumPrincipalCompletionRoot (n := n) (d := d) m)
    (quantumPrincipalCompletionRoot_ne_zero m hm)
  exact quantumPrincipalSymbolCompletion_pow q hq A₀ F hA₀

/-- **Before-time holographic horizon theorem.**  Every represented scalar law on a nonzero
finite state space has a finite scalar-invisible completion whose rational differential-field
horizon is exactly the scalar zero locus and whose derivation commutator remembers every
two-plane. -/
theorem quantumPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol
    (q : K) (hq : IsPrimitiveRoot q d)
    (A₀ : (Fin n → K) →ₗ[K] Module.End K M)
    (F : (Fin n → K) → K)
    (hA₀ : ∀ c, (A₀ c) ^ d = F c • LinearMap.id)
    (m : M) (hm : m ≠ 0) :
    ({c : Fin n → K | ¬ AlgebraicIndependent K
        (generalizedCliffordShiftFieldJet
          (quantumPrincipalSymbolCompletion q hq.pow_eq_one A₀ c)
          (quantumPrincipalCompletionRoot (n := n) (d := d) m))} =
      {c : Fin n → K | F c = 0}) ∧
    Function.Injective
      (derivationCommutatorMap
        (generalizedCliffordShiftFieldDerivationLaw
          (quantumPrincipalSymbolCompletion q hq.pow_eq_one A₀))) := by
  constructor
  · apply generalizedCliffordShiftField_dependenceHorizon_eq_zeroLocus
      (quantumPrincipalSymbolCompletion q hq.pow_eq_one A₀) F d
      (Nat.ne_of_gt (lt_trans Nat.zero_lt_one Fact.out))
      (quantumPrincipalCompletionRoot (n := n) (d := d) m)
      (quantumPrincipalCompletionRoot_ne_zero m hm)
    exact quantumPrincipalSymbolCompletion_pow q hq A₀ F hA₀
  · rw [generalizedCliffordField_derivationCommutatorMap_injective_iff]
    exact quantumPrincipalSymbolCompletion_endomorphismCommutatorMap_injective
      q hq A₀ m hm

end

end GaloisForLFunctions.HTGeometry
