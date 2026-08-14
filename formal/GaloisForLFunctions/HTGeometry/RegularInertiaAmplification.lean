import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.NumberTheory.Divisors
import GaloisForLFunctions.RHTower.RHLadderTheory

/-!
# Regular-inertia amplification, cycle rank, and cofinal selection

Finite cyclic regular representations recover marked charges modulo depth, classify unmarked
packets by cycle type, diagonalize in the discrete Fourier basis, and produce an exact normalized
Hilbert--Schmidt action.  Cofinal action finiteness, vanishing, and sublinear growth all force zero
integer charge.  Specializing the charge to strict-right Xi analytic order gives unconditional
equivalences with the Riemann hypothesis.
-/

open scoped Matrix.Norms.Frobenius

namespace GaloisForLFunctions.HTGeometry

def regularTranslation (n : ℕ) (q : ℤ) : Equiv.Perm (ZMod n) :=
  Equiv.addRight (-(q : ZMod n))

def regularInertia (n : ℕ) (q : ℤ) : Matrix (ZMod n) (ZMod n) ℂ :=
  (regularTranslation n q).permMatrix ℂ

def basisVector (n : ℕ) (x : ZMod n) : ZMod n → ℂ :=
  Pi.single x 1

theorem regularInertia_mulVec_basis {n : ℕ} [NeZero n] (q : ℤ) (x : ZMod n) :
    Matrix.mulVec (regularInertia n q) (basisVector n x) =
      basisVector n (x + (q : ZMod n)) := by
  rw [regularInertia, Matrix.permMatrix_mulVec]
  ext y
  simp only [regularTranslation, basisVector, Function.comp_apply]
  by_cases h : y + -(q : ZMod n) = x
  · have hy : y = x + (q : ZMod n) := by
      calc
        y = (y + -(q : ZMod n)) + (q : ZMod n) := by simp [add_assoc]
        _ = x + (q : ZMod n) := by rw [h]
    simp [hy]
  · have hy : y ≠ x + (q : ZMod n) := by
      intro hy
      apply h
      rw [hy]
      simp [add_assoc]
    simp [h, hy]

theorem regularInertia_unitary {n : ℕ} [NeZero n] (q : ℤ) :
    regularInertia n q ∈ Matrix.unitaryGroup (ZMod n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  simp only [regularInertia, Matrix.conjTranspose_permMatrix]
  rw [← Matrix.permMatrix_mul]
  simp

theorem regularInertia_eq_one_iff {n : ℕ} [NeZero n] (q : ℤ) :
    regularInertia n q = 1 ↔ (n : ℤ) ∣ q := by
  constructor
  · intro h
    have hp : regularTranslation n q = 1 := by
      have hm : ((regularTranslation n q).toPEquiv.toMatrix :
            Matrix (ZMod n) (ZMod n) ℂ) =
          ((1 : Equiv.Perm (ZMod n)).toPEquiv.toMatrix :
            Matrix (ZMod n) (ZMod n) ℂ) := by
        simpa [regularInertia] using h
      have hpPE := PEquiv.toMatrix_injective (α := ℂ) hm
      ext x
      simpa using congrArg (fun e : PEquiv (ZMod n) (ZMod n) => e x) hpPE
    have hq : (q : ZMod n) = 0 := by
      have hz := Equiv.congr_fun hp (0 : ZMod n)
      simpa [regularTranslation] using congrArg Neg.neg hz
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd q n).mp hq
  · intro h
    have hq : (q : ZMod n) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd q n).mpr h
    simp [regularInertia, regularTranslation, hq]

theorem regularInertia_trace {n : ℕ} [NeZero n] (q : ℤ) :
    Matrix.trace (regularInertia n q) =
      if (n : ℤ) ∣ q then (n : ℂ) else 0 := by
  by_cases hq : (q : ZMod n) = 0
  · have hd : (n : ℤ) ∣ q :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd q n).mp hq
    simp [regularInertia, regularTranslation, hq, hd]
  · have hd : ¬(n : ℤ) ∣ q := by
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hq
    have hf : Function.fixedPoints (regularTranslation n q) = ∅ := by
      ext x
      simp only [Function.mem_fixedPoints, Set.mem_empty_iff_false, iff_false]
      intro hx
      apply hq
      have hnq : -(q : ZMod n) = 0 := by
        change x + -(q : ZMod n) = x at hx
        have hx' : x + -(q : ZMod n) = x + 0 := by
          rw [add_zero]
          exact hx
        exact add_left_cancel hx'
      exact neg_eq_zero.mp hnq
    unfold regularInertia
    rw [Matrix.trace_permutation]
    rw [hf]
    simp [hd]

theorem regularInertia_entry {n : ℕ} [NeZero n] (q : ℤ) (i j : ZMod n) :
    regularInertia n q i j = if i + -(q : ZMod n) = j then 1 else 0 := by
  simp [regularInertia, regularTranslation, Equiv.Perm.permMatrix, PEquiv.toMatrix]

theorem regularInertia_hilbertSchmidt_sq {n : ℕ} [NeZero n] (q : ℤ) :
    ‖regularInertia n q - 1‖ ^ 2 =
      if (n : ℤ) ∣ q then 0 else (2 * n : ℝ) := by
  let D : Matrix (ZMod n) (ZMod n) ℂ := regularInertia n q - 1
  change ‖D‖ ^ 2 = _
  by_cases hq : (q : ZMod n) = 0
  · have hd : (n : ℤ) ∣ q :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd q n).mp hq
    simp [D, regularInertia, regularTranslation, hq, hd]
  · have hd : ¬(n : ℤ) ∣ q := by
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hq
    have hrow (i : ZMod n) :
        ∑ j : ZMod n, ‖D i j‖ ^ (2 : ℝ) = (2 : ℝ) := by
      have hne : i + -(q : ZMod n) ≠ i := by
        intro hi
        apply hq
        have : -(q : ZMod n) = 0 := by
          apply add_left_cancel (a := i)
          simpa using hi
        exact neg_eq_zero.mp this
      classical
      simp only [D, Matrix.sub_apply, regularInertia_entry, Matrix.one_apply]
      calc
        (∑ j : ZMod n,
            ‖(if i + -(q : ZMod n) = j then (1 : ℂ) else 0) -
              (if i = j then 1 else 0)‖ ^ (2 : ℝ)) =
            ∑ j : ZMod n,
              if j = i + -(q : ZMod n) then (1 : ℝ)
              else if j = i then 1 else 0 := by
                apply Finset.sum_congr rfl
                intro j _
                by_cases hjq : j = i + -(q : ZMod n)
                · subst j
                  simp [hne.symm]
                · by_cases hji : j = i
                  · subst j
                    simp [hne, hne.symm]
                  · simp [hjq, hji, Ne.symm hji, eq_comm]
        _ = ∑ j : ZMod n,
              ((if j = i + -(q : ZMod n) then (1 : ℝ) else 0) +
                if j = i then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hjq : j = i + -(q : ZMod n) <;>
                by_cases hji : j = i <;> simp_all
        _ = 2 := by
              rw [Finset.sum_add_distrib]
              simp
              ring
    have hsum :
        (∑ i : ZMod n, ∑ j : ZMod n, ‖D i j‖ ^ (2 : ℝ)) = (2 * n : ℝ) := by
      calc
        (∑ i : ZMod n, ∑ j : ZMod n, ‖D i j‖ ^ (2 : ℝ)) =
            ∑ _i : ZMod n, (2 : ℝ) := by
              apply Finset.sum_congr rfl
              intro i _
              exact hrow i
        _ = (2 * n : ℝ) := by simp [mul_comm]
    have hnorm : ‖D‖ =
        (∑ i : ZMod n, ∑ j : ZMod n, ‖D i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
      Matrix.frobenius_norm_def D
    calc
      ‖D‖ ^ 2 =
          ((∑ i : ZMod n, ∑ j : ZMod n, ‖D i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) hnorm
      _ = ((2 * n : ℝ) ^ (1 / 2 : ℝ)) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2)
          (congrArg (fun x : ℝ => x ^ (1 / 2 : ℝ)) hsum)
      _ = (2 * n : ℝ) := by
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
        positivity
      _ = if (n : ℤ) ∣ q then 0 else (2 * n : ℝ) := by simp [hd]

def chargeGcd (n : ℕ) (q : ℤ) : ℕ :=
  n.gcd q.natAbs

def recurrencePeriod (n : ℕ) (q : ℤ) : ℕ :=
  n / chargeGcd n q

theorem addOrderOf_intCast {n : ℕ} (hn : n ≠ 0) (q : ℤ) :
    addOrderOf (q : ZMod n) = recurrencePeriod n q := by
  cases q with
  | ofNat a =>
      simpa [recurrencePeriod, chargeGcd] using ZMod.addOrderOf_coe a hn
  | negSucc a =>
      rw [Int.cast_negSucc, addOrderOf_neg]
      simpa [recurrencePeriod, chargeGcd] using ZMod.addOrderOf_coe (a + 1) hn

def translationSubgroup (n : ℕ) (q : ℤ) : AddSubgroup (ZMod n) :=
  AddSubgroup.zmultiples (q : ZMod n)

abbrev regularCycleClass (n : ℕ) (q : ℤ) :=
  ZMod n ⧸ translationSubgroup n q

theorem translationSubgroup_card {n : ℕ} [NeZero n] (q : ℤ) :
    Nat.card (translationSubgroup n q) = recurrencePeriod n q := by
  unfold translationSubgroup
  rw [Nat.card_zmultiples, addOrderOf_intCast (NeZero.ne n)]

theorem translationSubgroup_index {n : ℕ} [NeZero n] (q : ℤ) :
    (translationSubgroup n q).index = chargeGcd n q := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hd : chargeGcd n q ∣ n := Nat.gcd_dvd_left n q.natAbs
  have hdpos : 0 < chargeGcd n q :=
    Nat.gcd_pos_of_pos_left q.natAbs hn
  have hlenpos : 0 < recurrencePeriod n q := by
    exact Nat.div_pos (Nat.le_of_dvd hn hd) hdpos
  have hmul := (translationSubgroup n q).index_mul_card
  have hmul' :
      (translationSubgroup n q).index * recurrencePeriod n q = n := by
    calc
      (translationSubgroup n q).index * recurrencePeriod n q =
          (translationSubgroup n q).index * Nat.card (translationSubgroup n q) := by
            rw [translationSubgroup_card q]
      _ = n := by simpa [Nat.card_zmod] using hmul
  apply Nat.eq_of_mul_eq_mul_right hlenpos
  calc
    (translationSubgroup n q).index * recurrencePeriod n q = n := hmul'
    _ = chargeGcd n q * recurrencePeriod n q := by
      symm
      exact Nat.mul_div_cancel' hd

theorem regularCycleClass_card {n : ℕ} [NeZero n] (q : ℤ) :
    Nat.card (regularCycleClass n q) = chargeGcd n q := by
  calc
    Nat.card (regularCycleClass n q) = (translationSubgroup n q).index :=
      (translationSubgroup n q).index_eq_card.symm
    _ = chargeGcd n q := translationSubgroup_index q

theorem same_regularCycleClass_iff (n : ℕ) (q : ℤ) (x y : ZMod n) :
    (x : regularCycleClass n q) = y ↔
      ∃ k : ℤ, y = x + k • (q : ZMod n) := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  change x - y ∈ AddSubgroup.zmultiples (q : ZMod n) ↔ _
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    symm
    calc
      x + (-k) • (q : ZMod n) = x - k • (q : ZMod n) := by
        rw [neg_smul]
        rw [sub_eq_add_neg]
      _ = x - (x - y) := by rw [hk]
      _ = y := by abel
  · rintro ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    rw [neg_smul]
    abel

theorem chargeGcd_mul_recurrencePeriod {n : ℕ} [NeZero n] (q : ℤ) :
    chargeGcd n q * recurrencePeriod n q = n := by
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_left n q.natAbs)

theorem recurrencePeriod_pos {n : ℕ} [NeZero n] (q : ℤ) :
    0 < recurrencePeriod n q := by
  rw [← addOrderOf_intCast (NeZero.ne n)]
  exact addOrderOf_pos (q : ZMod n)

theorem regularTranslation_pow_apply_iff {n : ℕ} [NeZero n] (q : ℤ)
    (k : ℕ) (x : ZMod n) :
    ((regularTranslation n q) ^ k) x = x ↔ recurrencePeriod n q ∣ k := by
  have hpow : ((regularTranslation n q) ^ k) x = x - k • (q : ZMod n) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, ih]
        simp only [regularTranslation, Equiv.coe_addRight]
        rw [add_nsmul, one_nsmul]
        abel
  rw [hpow]
  constructor
  · intro h
    have hk : k • (q : ZMod n) = 0 := by
      apply sub_eq_self.mp h
    rw [← addOrderOf_intCast (NeZero.ne n)]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hk
  · intro hk
    have hz : k • (q : ZMod n) = 0 := by
      apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
      rwa [addOrderOf_intCast (NeZero.ne n)]
    simp [hz]

theorem regularTranslation_cycle_length {n : ℕ} [NeZero n] (q : ℤ)
    (hq : (q : ZMod n) ≠ 0) (x : ZMod n) :
    ((regularTranslation n q).cycleOf x).support.card = recurrencePeriod n q := by
  let σ := regularTranslation n q
  have hx : σ x ≠ x := by
    intro h
    apply hq
    change x + -(q : ZMod n) = x at h
    have : -(q : ZMod n) = 0 := by
      apply add_left_cancel (a := x)
      simpa using h
    exact neg_eq_zero.mp this
  have hc : (Equiv.Perm.cycleOf σ x).IsCycle := Equiv.Perm.isCycle_cycleOf σ hx
  have hcx : Equiv.Perm.cycleOf σ x x ≠ x := by
    simpa using hx
  have hpow (k : ℕ) :
      (Equiv.Perm.cycleOf σ x) ^ k = 1 ↔ recurrencePeriod n q ∣ k := by
    rw [hc.pow_eq_one_iff' hcx]
    rw [Equiv.Perm.cycleOf_pow_apply_self]
    exact regularTranslation_pow_apply_iff q k x
  have hord : orderOf (Equiv.Perm.cycleOf σ x) = recurrencePeriod n q := by
    apply Nat.dvd_antisymm
    · exact (orderOf_dvd_iff_pow_eq_one.mpr ((hpow _).mpr dvd_rfl))
    · exact (hpow _).mp (pow_orderOf_eq_one _)
  rw [← hc.orderOf]
  exact hord

theorem regularTranslation_cycleType_of_ne_zero {n : ℕ} [NeZero n] (q : ℤ)
    (hq : (q : ZMod n) ≠ 0) :
    (regularTranslation n q).cycleType =
      Multiset.replicate (chargeGcd n q) (recurrencePeriod n q) := by
  let σ := regularTranslation n q
  have hall (m : ℕ) (hm : m ∈ σ.cycleType) : m = recurrencePeriod n q := by
    rw [Equiv.Perm.cycleType_def, Multiset.mem_map] at hm
    obtain ⟨c, hc, rfl⟩ := hm
    have hc' : c ∈ σ.cycleFactorsFinset := hc
    obtain ⟨x, hx⟩ := Equiv.Perm.IsCycle.nonempty_support
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc').1
    rw [Equiv.Perm.cycle_is_cycleOf hx hc']
    exact regularTranslation_cycle_length q hq x
  have hrep : σ.cycleType =
      Multiset.replicate σ.cycleType.card (recurrencePeriod n q) :=
    Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsupp : σ.support = Finset.univ := by
    ext x
    simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
    intro hx
    apply hq
    change x + -(q : ZMod n) = x at hx
    have : -(q : ZMod n) = 0 := by
      apply add_left_cancel (a := x)
      simpa using hx
    exact neg_eq_zero.mp this
  have hcard : σ.cycleType.card = chargeGcd n q := by
    apply Nat.eq_of_mul_eq_mul_right (recurrencePeriod_pos (n := n) q)
    calc
      σ.cycleType.card * recurrencePeriod n q =
          (Multiset.replicate σ.cycleType.card (recurrencePeriod n q)).sum := by simp
      _ = σ.cycleType.sum := congrArg Multiset.sum hrep.symm
      _ = σ.support.card := σ.sum_cycleType
      _ = n := by
        rw [hsupp]
        exact ZMod.card n
      _ = chargeGcd n q * recurrencePeriod n q :=
        (chargeGcd_mul_recurrencePeriod q).symm
  rw [hrep, hcard]

theorem regularTranslation_partition {n : ℕ} [NeZero n] (q : ℤ) :
    (regularTranslation n q).partition.parts =
      Multiset.replicate (chargeGcd n q) (recurrencePeriod n q) := by
  by_cases hq : (q : ZMod n) = 0
  · have hσ : regularTranslation n q = 1 := by
      ext x
      simp [regularTranslation, hq]
    have hell : recurrencePeriod n q = 1 := by
      rw [← addOrderOf_intCast (NeZero.ne n)]
      simp [hq]
    have hd : chargeGcd n q = n := by
      have := chargeGcd_mul_recurrencePeriod (n := n) q
      simpa [hell] using this
    rw [hσ, Equiv.Perm.parts_partition, hell, hd]
    simp
  · rw [Equiv.Perm.parts_partition, regularTranslation_cycleType_of_ne_zero q hq]
    have hsupp : (regularTranslation n q).support = Finset.univ := by
      ext x
      simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
      intro hx
      apply hq
      change x + -(q : ZMod n) = x at hx
      have : -(q : ZMod n) = 0 := by
        apply add_left_cancel (a := x)
        simpa using hx
      exact neg_eq_zero.mp this
    rw [hsupp]
    simp

theorem regularTranslation_isConj_iff {n : ℕ} [NeZero n] (q r : ℤ) :
    IsConj (regularTranslation n q) (regularTranslation n r) ↔
      chargeGcd n q = chargeGcd n r := by
  rw [Equiv.Perm.partition_eq_of_isConj]
  constructor
  · intro h
    have hp := congrArg (fun p => p.parts) h
    have hc := congrArg Multiset.card hp
    simpa [regularTranslation_partition] using hc
  · intro hd
    apply Nat.Partition.ext
    rw [regularTranslation_partition, regularTranslation_partition, hd]
    simp [recurrencePeriod, hd]

theorem regularInertia_det {n : ℕ} [NeZero n] (q : ℤ) :
    (regularInertia n q).det = (-1 : ℂ) ^ (n - chargeGcd n q) := by
  by_cases hq : (q : ZMod n) = 0
  · have hd : chargeGcd n q = n := by
      have hell : recurrencePeriod n q = 1 := by
        rw [← addOrderOf_intCast (NeZero.ne n)]
        simp [hq]
      have hmul := chargeGcd_mul_recurrencePeriod (n := n) q
      simpa [hell] using hmul
    simp [regularInertia, regularTranslation, hq, hd]
  · let σ := regularTranslation n q
    have hcycle : σ.cycleType =
        Multiset.replicate (chargeGcd n q) (recurrencePeriod n q) :=
      regularTranslation_cycleType_of_ne_zero q hq
    have hsupp : σ.support = Finset.univ := by
      ext x
      simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
      intro hx
      apply hq
      change x + -(q : ZMod n) = x at hx
      have : -(q : ZMod n) = 0 := by
        apply add_left_cancel (a := x)
        simpa using hx
      exact neg_eq_zero.mp this
    have hsum : σ.cycleType.sum = n := by
      calc
        σ.cycleType.sum = σ.support.card := σ.sum_cycleType
        _ = n := by
          rw [hsupp]
          exact ZMod.card n
    have hcard : σ.cycleType.card = chargeGcd n q := by simp [hcycle]
    have hdle : chargeGcd n q ≤ n :=
      Nat.gcd_le_left q.natAbs (Nat.pos_of_ne_zero (NeZero.ne n))
    have hexp : n + chargeGcd n q =
        (n - chargeGcd n q) + 2 * chargeGcd n q := by
      calc
        n + chargeGcd n q =
            (n - chargeGcd n q + chargeGcd n q) + chargeGcd n q := by
              rw [Nat.sub_add_cancel hdle]
        _ = (n - chargeGcd n q) + 2 * chargeGcd n q := by ring
    have hsign : Equiv.Perm.sign σ =
        (-1 : ℤˣ) ^ (n - chargeGcd n q) := by
      rw [Equiv.Perm.sign_of_cycleType, hsum, hcard, hexp, pow_add]
      simp [pow_mul]
      rfl
    calc
      (regularInertia n q).det = ((Equiv.Perm.sign σ : ℤˣ) : ℂ) := by
        change (Equiv.Perm.permMatrix ℂ (regularTranslation n q)).det =
          ((Equiv.Perm.sign (regularTranslation n q) : ℤˣ) : ℂ)
        exact Matrix.det_permutation (R := ℂ) (regularTranslation n q)
      _ = (((-1 : ℤˣ) ^ (n - chargeGcd n q) : ℤˣ) : ℂ) := by rw [hsign]
      _ = (-1 : ℂ) ^ (n - chargeGcd n q) := by
        change ((((-1 : ℤ) ^ (n - chargeGcd n q) : ℤ)) : ℂ) =
          (-1 : ℂ) ^ (n - chargeGcd n q)
        rw [Int.cast_pow, Int.cast_neg, Int.cast_one]

theorem regularInertia_fusion {n : ℕ} [NeZero n] (q r : ℤ) :
    regularInertia n (q + r) = regularInertia n q * regularInertia n r := by
  unfold regularInertia
  rw [← Matrix.permMatrix_mul]
  congr 1
  ext x
  simp [regularTranslation]
  abel

theorem regularInertia_pow {n : ℕ} [NeZero n] (q : ℤ) (k : ℕ) :
    regularInertia n q ^ k = regularInertia n ((k : ℤ) * q) := by
  induction k with
  | zero => simp [regularInertia, regularTranslation]
  | succ k ih =>
      rw [pow_succ, ih, ← regularInertia_fusion]
      congr 2
      push_cast
      ring

theorem regularInertia_exact_recurrence {n : ℕ} [NeZero n] (q : ℤ) (k : ℕ) :
    regularInertia n q ^ k = 1 ↔ recurrencePeriod n q ∣ k := by
  rw [regularInertia_pow]
  constructor
  · intro h
    have hd : (n : ℤ) ∣ (k : ℤ) * q :=
      (regularInertia_eq_one_iff ((k : ℤ) * q)).mp h
    have hz : (((k : ℤ) * q : ℤ) : ZMod n) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
    have hsmul : k • (q : ZMod n) = 0 := by
      simpa [Int.cast_mul, nsmul_eq_mul] using hz
    rw [← addOrderOf_intCast (NeZero.ne n)]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hsmul
  · intro hk
    have hsmul : k • (q : ZMod n) = 0 := by
      apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
      rwa [addOrderOf_intCast (NeZero.ne n)]
    apply (regularInertia_eq_one_iff ((k : ℤ) * q)).mpr
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa [Int.cast_mul, nsmul_eq_mul] using hsmul

theorem regularInertia_eq_iff {n : ℕ} [NeZero n] (q r : ℤ) :
    regularInertia n q = regularInertia n r ↔ (q : ZMod n) = (r : ZMod n) := by
  constructor
  · intro h
    have hm : ((regularTranslation n q).toPEquiv.toMatrix :
          Matrix (ZMod n) (ZMod n) ℂ) =
        ((regularTranslation n r).toPEquiv.toMatrix :
          Matrix (ZMod n) (ZMod n) ℂ) := by
      simpa [regularInertia] using h
    have hpPE := PEquiv.toMatrix_injective (α := ℂ) hm
    have hp : regularTranslation n q = regularTranslation n r := by
      ext x
      simpa using congrArg (fun e : PEquiv (ZMod n) (ZMod n) => e x) hpPE
    have hz := Equiv.congr_fun hp (0 : ZMod n)
    simpa [regularTranslation] using congrArg Neg.neg hz
  · intro h
    simp [regularInertia, regularTranslation, h]

theorem regularInertia_eq_iff_modEq {n : ℕ} [NeZero n] (q r : ℤ) :
    regularInertia n q = regularInertia n r ↔ q ≡ r [ZMOD n] := by
  rw [regularInertia_eq_iff, ZMod.intCast_eq_intCast_iff]

theorem regularInertia_marked_readout {n : ℕ} [NeZero n] (q : ℤ) :
    Matrix.mulVec (regularInertia n q) (basisVector n 0) =
      basisVector n (q : ZMod n) := by
  simpa using regularInertia_mulVec_basis q (0 : ZMod n)

theorem complete_marked_regularTower_injective (q r : ℤ) :
    (∀ n : ℕ, 2 ≤ n → regularInertia n q = regularInertia n r) ↔ q = r := by
  constructor
  · intro h
    by_contra hqr
    have hdiff : q - r ≠ 0 := sub_ne_zero.mpr hqr
    let m := (q - r).natAbs
    have hmpos : 0 < m := by
      simpa [m] using Int.natAbs_pos.mpr hdiff
    let n := m + 1
    have hn2 : 2 ≤ n := by
      exact Nat.succ_le_succ hmpos
    letI : NeZero n := ⟨ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hn2)⟩
    have hcast : (q : ZMod n) = (r : ZMod n) :=
      (regularInertia_eq_iff q r).mp (h n hn2)
    have hd : (n : ℤ) ∣ r - q :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub q r n).mp hcast
    have hdNat : n ∣ (r - q).natAbs := Int.natCast_dvd.mp hd
    have habs : (r - q).natAbs = m := by
      have hrs : r - q = -(q - r) := by ring
      rw [hrs, Int.natAbs_neg]
    have hsucc : m + 1 ∣ m := by simpa [n, habs] using hdNat
    have hle : m + 1 ≤ m := Nat.le_of_dvd hmpos hsucc
    exact (Nat.not_succ_le_self m) hle
  · rintro rfl
    intro _n _hn
    rfl

noncomputable def regularCost (n : ℕ) (q : ℤ) : ℝ :=
  if hn : n = 0 then 0 else
    letI : NeZero n := ⟨hn⟩
    (n : ℝ)⁻¹ * ‖regularInertia n q - 1‖ ^ 2

theorem regularCost_eq {n : ℕ} (hn : n ≠ 0) (q : ℤ) :
    regularCost n q = if (n : ℤ) ∣ q then 0 else 2 := by
  rw [regularCost, dif_neg hn]
  letI : NeZero n := ⟨hn⟩
  rw [regularInertia_hilbertSchmidt_sq]
  split_ifs with hd
  · simp
  · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp

def activeDepths (N : ℕ) (q : ℤ) : Finset ℕ :=
  (Finset.Icc 2 N).filter fun n => ¬(n : ℤ) ∣ q

def divisorDepths (N : ℕ) (q : ℤ) : Finset ℕ :=
  (Finset.Icc 2 N).filter fun n => (n : ℤ) ∣ q

theorem divisorDepths_eq {N : ℕ} {q : ℤ} (hq : q ≠ 0) (hQN : q.natAbs ≤ N) :
    divisorDepths N q = q.natAbs.divisors.erase 1 := by
  have hQpos : 0 < q.natAbs := Int.natAbs_pos.mpr hq
  have hQ0 : q.natAbs ≠ 0 := ne_of_gt hQpos
  ext n
  simp only [divisorDepths, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_erase, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hn2, _hnN⟩, hnd⟩
    have hndNat : n ∣ q.natAbs := Int.natCast_dvd.mp hnd
    exact ⟨ne_of_gt (lt_of_lt_of_le Nat.one_lt_two hn2), hndNat, hQ0⟩
  · rintro ⟨hn1, hndNat, _hQ0⟩
    have hnpos : 0 < n := Nat.pos_of_dvd_of_pos hndNat hQpos
    have hn2 : 2 ≤ n := Nat.succ_le_iff.mpr
      (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ne_of_gt hnpos, hn1⟩)
    have hnN : n ≤ N := (Nat.le_of_dvd hQpos hndNat).trans hQN
    exact ⟨⟨hn2, hnN⟩, Int.natCast_dvd.mpr hndNat⟩

theorem activeDepths_card {N : ℕ} {q : ℤ} (hq : q ≠ 0) (hQN : q.natAbs ≤ N)
    (hN : 2 ≤ N) :
    (activeDepths N q).card = N - q.natAbs.divisors.card := by
  have hQ0 : q.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hq
  have htaupos : 0 < q.natAbs.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hQ0⟩
  have hdivcard : (divisorDepths N q).card = q.natAbs.divisors.card - 1 := by
    rw [divisorDepths_eq hq hQN]
    exact Finset.card_erase_of_mem (Nat.one_mem_divisors.mpr hQ0)
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc 2 N) (fun n : ℕ => (n : ℤ) ∣ q)
  change (divisorDepths N q).card + (activeDepths N q).card =
    (Finset.Icc 2 N).card at hpartition
  rw [hdivcard, Nat.card_Icc] at hpartition
  have hNm1 : N + 1 - 2 = N - 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    simp [Nat.add_comm, Nat.add_left_comm]
  rw [hNm1] at hpartition
  have htau : q.natAbs.divisors.card - 1 + 1 = q.natAbs.divisors.card :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr htaupos)
  have hNm : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hN)))
  have hadd : q.natAbs.divisors.card + (activeDepths N q).card = N := by
    calc
      q.natAbs.divisors.card + (activeDepths N q).card =
          (q.natAbs.divisors.card - 1 + 1) + (activeDepths N q).card := by rw [htau]
      _ = (q.natAbs.divisors.card - 1) + (activeDepths N q).card + 1 := by ac_rfl
      _ = (N - 1) + 1 := by rw [hpartition]
      _ = N := hNm
  exact Nat.eq_sub_of_add_eq (by simpa [add_comm] using hadd)

theorem regularTruncatedAction_exact {N : ℕ} {q : ℤ} (hq : q ≠ 0)
    (hQN : q.natAbs ≤ N) (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, regularCost n q) =
      (2 * (N - q.natAbs.divisors.card) : ℝ) := by
  calc
    (∑ n ∈ Finset.Icc 2 N, regularCost n q) =
        ∑ n ∈ Finset.Icc 2 N, if ¬(n : ℤ) ∣ q then (2 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
          have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hn2)
          rw [regularCost_eq hn0]
          split_ifs <;> simp_all
    _ = ∑ _n ∈ activeDepths N q, (2 : ℝ) := by
          unfold activeDepths
          rw [Finset.sum_filter]
    _ = (2 * (N - q.natAbs.divisors.card) : ℝ) := by
          have htauN : q.natAbs.divisors.card ≤ N :=
            (Nat.card_divisors_le_self q.natAbs).trans hQN
          rw [Finset.sum_const, nsmul_eq_mul, activeDepths_card hq hQN hN]
          rw [Nat.cast_sub htauN]
          ring

noncomputable def regularTruncatedAction (N : ℕ) (q : ℤ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, regularCost n q

theorem regularTruncatedAction_zero (N : ℕ) : regularTruncatedAction N 0 = 0 := by
  unfold regularTruncatedAction
  apply Finset.sum_eq_zero
  intro n hn
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hn2)
  rw [regularCost_eq hn0]
  simp

theorem regularTruncatedAction_tendsto_atTop {q : ℤ} (hq : q ≠ 0) :
    Filter.Tendsto (fun N => regularTruncatedAction N q)
      Filter.atTop Filter.atTop := by
  have hlinear : Filter.Tendsto
      (fun N : ℕ => (2 : ℝ) * ((N : ℝ) - (q.natAbs.divisors.card : ℝ)))
      Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2)
    exact Filter.tendsto_atTop_add_const_right Filter.atTop
      (-(q.natAbs.divisors.card : ℝ)) tendsto_natCast_atTop_atTop
  apply hlinear.congr'
  filter_upwards [Filter.eventually_ge_atTop (max 2 q.natAbs)] with N hN
  have h2 : 2 ≤ N := (le_max_left 2 q.natAbs).trans hN
  have hQ : q.natAbs ≤ N := (le_max_right 2 q.natAbs).trans hN
  symm
  simpa [regularTruncatedAction] using regularTruncatedAction_exact hq hQ h2

/-- Finiteness of the nonnegative regular action, expressed by a uniform bound on all truncations. -/
def RegularActionFinite (q : ℤ) : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, regularTruncatedAction N q ≤ C

/-- Vanishing of the regular action at every truncation depth. -/
def RegularActionZero (q : ℤ) : Prop :=
  ∀ N : ℕ, regularTruncatedAction N q = 0

/-- One-sided `o(N)` for the nonnegative regular action. -/
def RegularActionSublinear (q : ℤ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ N : ℕ in Filter.atTop,
      regularTruncatedAction N q ≤ ε * (N : ℝ)

theorem regularActionFinite_iff (q : ℤ) : RegularActionFinite q ↔ q = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hq
    have hlarge : ∀ᶠ N : ℕ in Filter.atTop,
        C + 1 ≤ regularTruncatedAction N q :=
      regularTruncatedAction_tendsto_atTop hq
        (Filter.eventually_ge_atTop (C + 1))
    obtain ⟨N, hN⟩ := hlarge.exists
    exact (not_lt_of_ge (hC N)) (lt_of_lt_of_le (lt_add_one C) hN)
  · rintro rfl
    exact ⟨0, fun N => by rw [regularTruncatedAction_zero]⟩

theorem regularActionZero_iff (q : ℤ) : RegularActionZero q ↔ q = 0 := by
  constructor
  · intro hzero
    apply (regularActionFinite_iff q).mp
    exact ⟨0, fun N => by rw [hzero N]⟩
  · rintro rfl
    exact regularTruncatedAction_zero

theorem regularActionSublinear_iff (q : ℤ) : RegularActionSublinear q ↔ q = 0 := by
  constructor
  · intro hsub
    by_contra hq
    let τ := q.natAbs.divisors.card
    have hevent := hsub 1 zero_lt_one
    have hdepth : ∀ᶠ N : ℕ in Filter.atTop,
        max (max 2 q.natAbs) (2 * τ + 1) ≤ N :=
      Filter.eventually_ge_atTop _
    obtain ⟨N, hupper, hN⟩ := (hevent.and hdepth).exists
    have h2 : 2 ≤ N := by
      calc
        2 ≤ max 2 q.natAbs := Nat.le_max_left _ _
        _ ≤ max (max 2 q.natAbs) (2 * τ + 1) := Nat.le_max_left _ _
        _ ≤ N := hN
    have hqN : q.natAbs ≤ N := by
      calc
        q.natAbs ≤ max 2 q.natAbs := Nat.le_max_right _ _
        _ ≤ max (max 2 q.natAbs) (2 * τ + 1) := Nat.le_max_left _ _
        _ ≤ N := hN
    have hτN : τ ≤ N := by
      exact (Nat.card_divisors_le_self q.natAbs).trans hqN
    have htwotau : 2 * τ < N := by
      exact (Nat.lt_succ_self (2 * τ)).trans_le
        ((Nat.le_max_right (max 2 q.natAbs) (2 * τ + 1)).trans hN)
    have hexact : regularTruncatedAction N q = (2 * (N - τ) : ℝ) := by
      simpa [regularTruncatedAction, τ] using regularTruncatedAction_exact hq hqN h2
    rw [hexact] at hupper
    have htwotauR : (2 : ℝ) * τ < N := by exact_mod_cast htwotau
    linarith
  · rintro rfl
    intro ε hε
    filter_upwards [] with N
    rw [regularTruncatedAction_zero]
    exact mul_nonneg (le_of_lt hε) (Nat.cast_nonneg N)

def regularFixedSubspace (n : ℕ) (q : ℤ) : Submodule ℂ (ZMod n → ℂ) where
  carrier := {v | ∀ x y : ZMod n,
    (x : regularCycleClass n q) = y → v x = v y}
  zero_mem' := by intro x y _; rfl
  add_mem' := by
    intro f g hf hg x y hxy
    simp only [Pi.add_apply]
    rw [hf x y hxy, hg x y hxy]
  smul_mem' := by
    intro c f hf x y hxy
    simp only [Pi.smul_apply]
    rw [hf x y hxy]

noncomputable def cycleFunctionsLinearEquivFixedSubspace (n : ℕ) (q : ℤ) :
    (regularCycleClass n q → ℂ) ≃ₗ[ℂ] regularFixedSubspace n q where
  toFun f := ⟨fun x => f (x : regularCycleClass n q), by
    intro x y hxy
    exact congrArg f hxy⟩
  invFun v := fun c => v.1 c.out
  left_inv f := by
    funext c
    change f ((c.out : ZMod n) : regularCycleClass n q) = f c
    exact congrArg f (Quotient.out_eq' c)
  right_inv v := by
    apply Subtype.ext
    funext x
    change v.1 ((x : regularCycleClass n q).out : ZMod n) = v.1 x
    exact v.2 _ _ (Quotient.out_eq _)
  map_add' f g := rfl
  map_smul' c f := rfl

theorem regularFixedSubspace_finrank {n : ℕ} [NeZero n] (q : ℤ) :
    Module.finrank ℂ (regularFixedSubspace n q) = chargeGcd n q := by
  letI : Fintype (regularCycleClass n q) := Fintype.ofFinite _
  calc
    Module.finrank ℂ (regularFixedSubspace n q) =
        Module.finrank ℂ (regularCycleClass n q → ℂ) :=
      (cycleFunctionsLinearEquivFixedSubspace n q).finrank_eq.symm
    _ = Fintype.card (regularCycleClass n q) :=
      Module.finrank_fintype_fun_eq_card ℂ
    _ = Nat.card (regularCycleClass n q) := Nat.card_eq_fintype_card.symm
    _ = chargeGcd n q := regularCycleClass_card q

theorem invariant_add_zsmul {n : ℕ} (q : ℤ) (v : ZMod n → ℂ)
    (h : ∀ x : ZMod n, v (x - (q : ZMod n)) = v x)
    (x : ZMod n) (k : ℤ) :
    v (x + k • (q : ZMod n)) = v x := by
  have hplus (y : ZMod n) : v (y + (q : ZMod n)) = v y := by
    have hy := h (y + (q : ZMod n))
    symm
    simpa using hy
  have hpos (m : ℕ) : v (x + m • (q : ZMod n)) = v x := by
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          v (x + (m + 1) • (q : ZMod n)) =
              v ((x + m • (q : ZMod n)) + (q : ZMod n)) := by
                apply congrArg v
                rw [add_nsmul, one_nsmul]
                abel
          _ = v (x + m • (q : ZMod n)) := hplus _
          _ = v x := ih
  have hneg (m : ℕ) : v (x - m • (q : ZMod n)) = v x := by
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          v (x - (m + 1) • (q : ZMod n)) =
              v ((x - m • (q : ZMod n)) - (q : ZMod n)) := by
                apply congrArg v
                rw [add_nsmul, one_nsmul]
                abel
          _ = v (x - m • (q : ZMod n)) := h _
          _ = v x := ih
  cases k with
  | ofNat m => simpa using hpos m
  | negSucc m =>
      rw [negSucc_zsmul]
      simpa [sub_eq_add_neg] using hneg (m + 1)

theorem mem_regularFixedSubspace_iff {n : ℕ} (q : ℤ) (v : ZMod n → ℂ) :
    v ∈ regularFixedSubspace n q ↔
      ∀ x : ZMod n, v (x - (q : ZMod n)) = v x := by
  constructor
  · intro hv x
    apply hv
    apply (same_regularCycleClass_iff n q _ _).mpr
    refine ⟨1, ?_⟩
    simp
  · intro hv x y hxy
    obtain ⟨k, rfl⟩ := (same_regularCycleClass_iff n q x y).mp hxy
    exact (invariant_add_zsmul q v hv x k).symm

def regularFixedKernel {n : ℕ} [NeZero n] (q : ℤ) : Submodule ℂ (ZMod n → ℂ) :=
  LinearMap.ker (Matrix.mulVecLin (1 - regularInertia n q))

theorem regularFixedKernel_eq {n : ℕ} [NeZero n] (q : ℤ) :
    regularFixedKernel q = regularFixedSubspace n q := by
  apply Submodule.ext
  intro v
  unfold regularFixedKernel
  rw [LinearMap.mem_ker, mem_regularFixedSubspace_iff]
  change Matrix.mulVec (1 - regularInertia n q) v = 0 ↔ _
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [show Matrix.mulVec (regularInertia n q) v = v ∘ regularTranslation n q by
    exact Matrix.permMatrix_mulVec (regularTranslation n q)]
  constructor
  · intro hv x
    have hx : v x - v (x - (q : ZMod n)) = 0 := by
      have hx' := congrFun hv x
      simp only [Pi.sub_apply, Pi.zero_apply, Function.comp_apply] at hx'
      rw [regularTranslation, Equiv.coe_addRight] at hx'
      simpa only [sub_eq_add_neg] using hx'
    exact eq_of_sub_eq_zero hx |>.symm
  · intro hv
    funext x
    simp only [Pi.sub_apply, Pi.zero_apply, Function.comp_apply]
    rw [regularTranslation, Equiv.coe_addRight]
    change v x - v (x + -(q : ZMod n)) = 0
    have hvx : v (x + -(q : ZMod n)) = v x := by
      simpa only [sub_eq_add_neg] using hv x
    rw [hvx]
    simp

theorem regularFixedKernel_finrank {n : ℕ} [NeZero n] (q : ℤ) :
    Module.finrank ℂ (regularFixedKernel (n := n) q) = chargeGcd n q := by
  rw [regularFixedKernel_eq (n := n)]
  exact regularFixedSubspace_finrank q

theorem regularInertia_defect_rank {n : ℕ} [NeZero n] (q : ℤ) :
    (1 - regularInertia n q).rank = n - chargeGcd n q := by
  let T := Matrix.mulVecLin (1 - regularInertia n q)
  have hrk : (1 - regularInertia n q).rank = Module.finrank ℂ (LinearMap.range T) := rfl
  have hnull : Module.finrank ℂ (LinearMap.ker T) = chargeGcd n q := by
    change Module.finrank ℂ (regularFixedKernel (n := n) q) = chargeGcd n q
    exact regularFixedKernel_finrank (n := n) q
  have hdim := LinearMap.finrank_range_add_finrank_ker T
  rw [hnull, Module.finrank_fintype_fun_eq_card ℂ, ZMod.card] at hdim
  rw [hrk]
  exact Nat.eq_sub_of_add_eq hdim

def regularFrequencyHom (n : ℕ) (q : ℤ) : ZMod n →+ ZMod n where
  toFun k := -(q : ZMod n) * k
  map_zero' := by simp
  map_add' := by intros; ring

noncomputable def regularEigenChar {n : ℕ} [NeZero n] (q : ℤ) : AddChar (ZMod n) ℂ :=
  ZMod.stdAddChar.compAddMonoidHom (regularFrequencyHom n q)

noncomputable def regularEigenvalue {n : ℕ} [NeZero n] (q : ℤ) (k : ZMod n) : ℂ :=
  regularEigenChar q k

noncomputable def regularEigenRootHom {n : ℕ} [NeZero n] (q : ℤ) :
    Multiplicative (ZMod n) →* rootsOfUnity (recurrencePeriod n q) ℂ := by
  let ψ := regularEigenChar (n := n) q
  let f := ψ.toMonoidHom.toHomUnits
  apply f.codRestrict (rootsOfUnity (recurrencePeriod n q) ℂ)
  intro k
  rw [mem_rootsOfUnity']
  change (ψ k.toAdd) ^ recurrencePeriod n q = 1
  rw [← ψ.map_nsmul_eq_pow]
  have hqzero : recurrencePeriod n q • (q : ZMod n) = 0 := by
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    rw [addOrderOf_intCast (NeZero.ne n)]
  have hfreq : regularFrequencyHom n q (recurrencePeriod n q • k.toAdd) = 0 := by
    change -(q : ZMod n) * (recurrencePeriod n q • k.toAdd) = 0
    calc
      -(q : ZMod n) * (recurrencePeriod n q • k.toAdd) =
          -(recurrencePeriod n q • (q : ZMod n)) * k.toAdd := by
        simp only [nsmul_eq_mul]
        ring
      _ = 0 := by rw [hqzero]; simp
  change ZMod.stdAddChar
    (regularFrequencyHom n q (recurrencePeriod n q • k.toAdd)) = 1
  rw [hfreq]
  exact ZMod.stdAddChar.map_zero_eq_one

@[simp]
theorem regularEigenRootHom_value {n : ℕ} [NeZero n] (q : ℤ)
    (k : Multiplicative (ZMod n)) :
    ((((regularEigenRootHom q k : rootsOfUnity (recurrencePeriod n q) ℂ) : ℂˣ) : ℂ)) =
      regularEigenvalue q k.toAdd := by
  change ((((regularEigenChar q).toMonoidHom.toHomUnits k : ℂˣ) : ℂ)) =
    regularEigenChar q k.toAdd
  exact MonoidHom.coe_toHomUnits _ _

theorem regularEigenvalue_def {n : ℕ} [NeZero n] (q : ℤ) (k : ZMod n) :
    regularEigenvalue q k = ZMod.stdAddChar (-(q : ZMod n) * k) := by
  rfl

theorem regularEigenRootHom_eq_one_iff {n : ℕ} [NeZero n] (q : ℤ) (k : ZMod n) :
    regularEigenRootHom q (.ofAdd k) = 1 ↔ q.natAbs • k = 0 := by
  have heigen : regularEigenvalue q k = 1 ↔ q.natAbs • k = 0 := by
    rw [regularEigenvalue_def (n := n),
      ← (ZMod.stdAddChar (N := n)).map_zero_eq_one,
      (ZMod.injective_stdAddChar (N := n)).eq_iff]
    cases q with
    | ofNat a => simp [nsmul_eq_mul]
    | negSucc a => simp [nsmul_eq_mul]
  constructor
  · intro h
    apply heigen.mp
    have hv := congrArg
      (fun z : rootsOfUnity (recurrencePeriod n q) ℂ => (((z : ℂˣ) : ℂ))) h
    simpa using hv
  · intro h
    apply Subtype.ext
    apply Units.ext
    change regularEigenvalue q k = 1
    exact heigen.mpr h

noncomputable def regularEigenRootKerEquiv {n : ℕ} [NeZero n] (q : ℤ) :
    (regularEigenRootHom (n := n) q).ker ≃
      (nsmulAddMonoidHom q.natAbs : ZMod n →+ ZMod n).ker where
  toFun k := ⟨k.1.toAdd, by
    change q.natAbs • k.1.toAdd = 0
    exact (regularEigenRootHom_eq_one_iff q k.1.toAdd).mp k.2⟩
  invFun k := ⟨.ofAdd k.1, by
    change regularEigenRootHom q (.ofAdd k.1) = 1
    apply (regularEigenRootHom_eq_one_iff q k.1).mpr
    exact k.2⟩
  left_inv k := by ext; rfl
  right_inv k := by ext; rfl

theorem regularEigenRootHom_ker_card {n : ℕ} [NeZero n] (q : ℤ) :
    Nat.card (regularEigenRootHom (n := n) q).ker = chargeGcd n q := by
  calc
    Nat.card (regularEigenRootHom (n := n) q).ker =
        Nat.card (nsmulAddMonoidHom q.natAbs : ZMod n →+ ZMod n).ker :=
      Nat.card_congr (regularEigenRootKerEquiv q)
    _ = (Nat.card (ZMod n)).gcd q.natAbs :=
      IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod n) q.natAbs
    _ = chargeGcd n q := by simp [chargeGcd]

theorem regularEigenRootHom_surjective {n : ℕ} [NeZero n] (q : ℤ) :
    Function.Surjective (regularEigenRootHom (n := n) q) := by
  letI : NeZero (recurrencePeriod n q) :=
    ⟨(recurrencePeriod_pos (n := n) q).ne'⟩
  apply MonoidHom.surjective_of_card_ker_le_div
  rw [regularEigenRootHom_ker_card]
  have hdiv : n / recurrencePeriod n q = chargeGcd n q := by
    calc
      n / recurrencePeriod n q =
          (chargeGcd n q * recurrencePeriod n q) / recurrencePeriod n q := by
        rw [chargeGcd_mul_recurrencePeriod (n := n) q]
      _ = chargeGcd n q := by
        rw [Nat.mul_comm]
        exact Nat.mul_div_right _ (recurrencePeriod_pos (n := n) q)
  change chargeGcd n q ≤
    Nat.card (Multiplicative (ZMod n)) /
      Nat.card (rootsOfUnity (recurrencePeriod n q) ℂ)
  rw [show Nat.card (Multiplicative (ZMod n)) = n by simp]
  rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity ℂ (recurrencePeriod n q)]
  exact hdiv.ge

theorem regularEigenRoot_fiber_card {n : ℕ} [NeZero n] (q : ℤ)
    (z : rootsOfUnity (recurrencePeriod n q) ℂ) :
    (Finset.univ.filter fun k : Multiplicative (ZMod n) =>
      regularEigenRootHom q k = z).card = chargeGcd n q := by
  let f := regularEigenRootHom (n := n) q
  have hz : z ∈ Set.range f := regularEigenRootHom_surjective q z
  have h1 : (1 : rootsOfUnity (recurrencePeriod n q) ℂ) ∈ Set.range f :=
    ⟨1, f.map_one⟩
  have heq := MonoidHom.card_fiber_eq_of_mem_range f hz h1
  calc
    (Finset.univ.filter fun k : Multiplicative (ZMod n) => f k = z).card =
        (Finset.univ.filter fun k : Multiplicative (ZMod n) => f k = 1).card := heq
    _ = Nat.card f.ker := by
      rw [Nat.card_eq_fintype_card]
      let e : f.ker ≃ {k : Multiplicative (ZMod n) // f k = 1} :=
        { toFun := fun k => ⟨k.1, k.2⟩
          invFun := fun k => ⟨k.1, k.2⟩
          left_inv := fun k => by ext; rfl
          right_inv := fun k => by ext; rfl }
      calc
        (Finset.univ.filter fun k : Multiplicative (ZMod n) => f k = 1).card =
            Fintype.card {k : Multiplicative (ZMod n) // f k = 1} := by
          symm
          apply Fintype.card_ofFinset
        _ = Fintype.card f.ker := (Fintype.card_congr e).symm
    _ = chargeGcd n q := by
      simpa [f] using regularEigenRootHom_ker_card (n := n) q

theorem regularInertia_dft {n : ℕ} [NeZero n] (q : ℤ) (v : ZMod n → ℂ)
    (k : ZMod n) :
    ZMod.dft (Matrix.mulVec (regularInertia n q) v) k =
      regularEigenvalue q k * ZMod.dft v k := by
  unfold regularInertia
  rw [Matrix.permMatrix_mulVec]
  simp only [ZMod.dft_apply, Function.comp_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (regularTranslation n q)
    (fun j : ZMod n => ZMod.stdAddChar (-(j * k)) * v (regularTranslation n q j))
    (fun j : ZMod n => regularEigenvalue q k * (ZMod.stdAddChar (-(j * k)) * v j))
    fun j => ?_
  simp only [regularTranslation, Equiv.coe_addRight]
  change ZMod.stdAddChar (-(j * k)) * v (j + -(q : ZMod n)) =
    regularEigenvalue q k *
      (ZMod.stdAddChar (-((j + -(q : ZMod n)) * k)) * v (j + -(q : ZMod n)))
  rw [show -(j * k) = (-(q : ZMod n) * k) +
      (-((j + -(q : ZMod n)) * k)) by ring]
  rw [ZMod.stdAddChar.map_add_eq_mul]
  change ZMod.stdAddChar (-(q : ZMod n) * k) *
      ZMod.stdAddChar (-((j + -(q : ZMod n)) * k)) * v (j + -(q : ZMod n)) =
    ZMod.stdAddChar (-(q : ZMod n) * k) *
      (ZMod.stdAddChar (-((j + -(q : ZMod n)) * k)) * v (j + -(q : ZMod n)))
  ring

noncomputable def regularFourierEigenvector {n : ℕ} [NeZero n] (k : ZMod n) :
    ZMod n → ℂ :=
  ZMod.dft.symm (basisVector n k)

noncomputable def regularFourierBasis (n : ℕ) [NeZero n] :
    Module.Basis (ZMod n) ℂ (ZMod n → ℂ) :=
  (Pi.basisFun ℂ (ZMod n)).map ZMod.dft.symm

@[simp]
theorem regularFourierBasis_apply {n : ℕ} [NeZero n] (k : ZMod n) :
    regularFourierBasis n k = regularFourierEigenvector k := by
  simp [regularFourierBasis, regularFourierEigenvector, basisVector]

theorem regularFourierEigenvector_eigen {n : ℕ} [NeZero n] (q : ℤ) (k : ZMod n) :
    Matrix.mulVec (regularInertia n q) (regularFourierEigenvector k) =
      regularEigenvalue q k • regularFourierEigenvector k := by
  apply ZMod.dft.injective
  funext j
  rw [regularInertia_dft]
  simp only [regularFourierEigenvector, LinearEquiv.apply_symm_apply,
    LinearEquiv.map_smul, Pi.smul_apply]
  by_cases h : j = k
  · subst j
    simp [basisVector]
  · simp [basisVector, h]

theorem regularInertia_toLin_diagonal {n : ℕ} [NeZero n] (q : ℤ) :
    (regularInertia n q).toLin' =
      (Matrix.diagonal (regularEigenvalue (n := n) q)).toLin
        (regularFourierBasis n) (regularFourierBasis n) := by
  apply (regularFourierBasis n).ext
  intro k
  calc
    (regularInertia n q).toLin' (regularFourierBasis n k) =
        Matrix.mulVec (regularInertia n q) (regularFourierBasis n k) := rfl
    _ = regularEigenvalue q k • regularFourierBasis n k := by
      rw [regularFourierBasis_apply]
      exact regularFourierEigenvector_eigen q k
    _ = (Matrix.diagonal (regularEigenvalue (n := n) q)).toLin
        (regularFourierBasis n) (regularFourierBasis n) (regularFourierBasis n k) :=
      (hasEigenvector_toLin_diagonal
        (regularEigenvalue (n := n) q) k (regularFourierBasis n)).apply_eq_smul.symm

theorem regularInertia_charpoly {n : ℕ} [NeZero n] (q : ℤ) :
    (regularInertia n q).charpoly =
      (Matrix.diagonal (regularEigenvalue (n := n) q)).charpoly := by
  calc
    (regularInertia n q).charpoly = (regularInertia n q).toLin'.charpoly := by
      rw [Matrix.charpoly_toLin']
    _ = ((Matrix.diagonal (regularEigenvalue (n := n) q)).toLin
        (regularFourierBasis n) (regularFourierBasis n)).charpoly := by
      rw [regularInertia_toLin_diagonal]
    _ = (Matrix.diagonal (regularEigenvalue (n := n) q)).charpoly :=
      Matrix.charpoly_toLin _ _

theorem regularInertia_spectrum {n : ℕ} [NeZero n] (q : ℤ) :
    spectrum ℂ (regularInertia n q) = Set.range (regularEigenvalue (n := n) q) := by
  calc
    spectrum ℂ (regularInertia n q) = spectrum ℂ (regularInertia n q).toLin' := by
      rw [Matrix.spectrum_toLin']
    _ = spectrum ℂ ((Matrix.diagonal (regularEigenvalue (n := n) q)).toLin
        (regularFourierBasis n) (regularFourierBasis n)) := by
      rw [regularInertia_toLin_diagonal]
    _ = spectrum ℂ (Matrix.diagonal (regularEigenvalue (n := n) q)) :=
      Matrix.spectrum_toLin _ _
    _ = Set.range (regularEigenvalue (n := n) q) := spectrum_diagonal _

/-- The regular packet has exactly the roots of unity of its recurrence period as spectrum. -/
theorem regularInertia_spectrum_roots {n : ℕ} [NeZero n] (q : ℤ) :
    spectrum ℂ (regularInertia n q) =
      Set.range (fun z : rootsOfUnity (recurrencePeriod n q) ℂ => ((z : ℂˣ) : ℂ)) := by
  rw [regularInertia_spectrum]
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨regularEigenRootHom q (.ofAdd k), ?_⟩
    exact regularEigenRootHom_value q (.ofAdd k)
  · rintro ⟨z, rfl⟩
    obtain ⟨k, hk⟩ := regularEigenRootHom_surjective q z
    refine ⟨k.toAdd, ?_⟩
    calc
      regularEigenvalue q k.toAdd =
          (((regularEigenRootHom q k : rootsOfUnity (recurrencePeriod n q) ℂ) : ℂˣ) : ℂ) :=
        (regularEigenRootHom_value q k).symm
      _ = ((z : ℂˣ) : ℂ) := congrArg (fun w : rootsOfUnity (recurrencePeriod n q) ℂ =>
        ((w : ℂˣ) : ℂ)) hk

/-- Complete root-spectrum classification, including exact geometric multiplicity. -/
theorem regularInertia_complete_root_spectrum {n : ℕ} [NeZero n] (q : ℤ) :
    spectrum ℂ (regularInertia n q) =
        Set.range (fun z : rootsOfUnity (recurrencePeriod n q) ℂ => ((z : ℂˣ) : ℂ)) ∧
      ∀ z : rootsOfUnity (recurrencePeriod n q) ℂ,
        (Finset.univ.filter fun k : Multiplicative (ZMod n) =>
          regularEigenRootHom q k = z).card = chargeGcd n q := by
  exact ⟨regularInertia_spectrum_roots q, regularEigenRoot_fiber_card q⟩

/-! ## Strict-right Xi specialization -/

/-- Local integer charge carried by a strict-right Xi zero. -/
noncomputable def xiRegularInertiaCharge (ρ : ℂ) : ℤ :=
  ((analyticOrderAt RHTower.xi ρ).toNat : ℤ)

theorem xiRegularInertiaCharge_ne_zero {ρ : ℂ} (hzero : RHTower.xi ρ = 0) :
    xiRegularInertiaCharge ρ ≠ 0 := by
  exact Int.ofNat_ne_zero.mpr (RHTower.xi_order_toNat_ne_zero hzero)

/-- Every strict-right local regular action has bounded truncations. -/
def AllRightZeroRegularActionsFinite : Prop :=
  ∀ ρ ∈ RHTower.rightHalf, RHTower.xi ρ = 0 →
    RegularActionFinite (xiRegularInertiaCharge ρ)

/-- Every strict-right local regular action vanishes at every truncation depth. -/
def AllRightZeroRegularActionsZero : Prop :=
  ∀ ρ ∈ RHTower.rightHalf, RHTower.xi ρ = 0 →
    RegularActionZero (xiRegularInertiaCharge ρ)

/-- Every strict-right local regular action is `o(N)`. -/
def AllRightZeroRegularActionsSublinear : Prop :=
  ∀ ρ ∈ RHTower.rightHalf, RHTower.xi ρ = 0 →
    RegularActionSublinear (xiRegularInertiaCharge ρ)

theorem riemannHypothesis_iff_allRightZero_regularActionsFinite :
    RiemannHypothesis ↔ AllRightZeroRegularActionsFinite := by
  constructor
  · intro hRH ρ hρ hzero
    exact (RHTower.rh_iff_xi_ne_zero_right.mp hRH ρ hρ hzero).elim
  · intro hfinite
    apply RHTower.rh_iff_xi_ne_zero_right.mpr
    intro ρ hρ hzero
    have hcharge := (regularActionFinite_iff (xiRegularInertiaCharge ρ)).mp
      (hfinite ρ hρ hzero)
    exact (xiRegularInertiaCharge_ne_zero hzero hcharge).elim

theorem riemannHypothesis_iff_allRightZero_regularActionsZero :
    RiemannHypothesis ↔ AllRightZeroRegularActionsZero := by
  constructor
  · intro hRH ρ hρ hzero
    exact (RHTower.rh_iff_xi_ne_zero_right.mp hRH ρ hρ hzero).elim
  · intro hzeroAction
    apply RHTower.rh_iff_xi_ne_zero_right.mpr
    intro ρ hρ hzero
    have hcharge := (regularActionZero_iff (xiRegularInertiaCharge ρ)).mp
      (hzeroAction ρ hρ hzero)
    exact (xiRegularInertiaCharge_ne_zero hzero hcharge).elim

theorem riemannHypothesis_iff_allRightZero_regularActionsSublinear :
    RiemannHypothesis ↔ AllRightZeroRegularActionsSublinear := by
  constructor
  · intro hRH ρ hρ hzero
    exact (RHTower.rh_iff_xi_ne_zero_right.mp hRH ρ hρ hzero).elim
  · intro hsublinear
    apply RHTower.rh_iff_xi_ne_zero_right.mpr
    intro ρ hρ hzero
    have hcharge := (regularActionSublinear_iff (xiRegularInertiaCharge ρ)).mp
      (hsublinear ρ hρ hzero)
    exact (xiRegularInertiaCharge_ne_zero hzero hcharge).elim

/-- Exact four-way RH specialization of regular-inertia divisor selection. -/
theorem regularInertia_rh_equivalences :
    (RiemannHypothesis ↔ AllRightZeroRegularActionsFinite) ∧
    (RiemannHypothesis ↔ AllRightZeroRegularActionsZero) ∧
    (RiemannHypothesis ↔ AllRightZeroRegularActionsSublinear) := by
  exact ⟨riemannHypothesis_iff_allRightZero_regularActionsFinite,
    riemannHypothesis_iff_allRightZero_regularActionsZero,
    riemannHypothesis_iff_allRightZero_regularActionsSublinear⟩

end GaloisForLFunctions.HTGeometry
