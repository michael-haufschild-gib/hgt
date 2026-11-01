import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPositiveMatrixCoding
import Mathlib.Data.List.Rotate
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.Ring

/-! Primitive roots and rotation periods of the digit-pair words that code
integral hyperbolic conjugacy classes. -/

open Function
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoding
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPrimitiveCycles

variable {α : Type*}

theorem wordPower_length (u : List α) (n : ℕ) : (wordPower u n).length = n*u.length := by
  induction n with
  | zero => simp only [wordPower,List.length_nil,Nat.zero_mul]
  | succ n ih => rw [wordPower,List.length_append,ih]; ring

theorem wordPower_nil (n : ℕ) : wordPower ([] : List α) n = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [wordPower,List.nil_append] using ih

theorem wordPower_mul (u : List α) (m n : ℕ) :
    wordPower (wordPower u m) n = wordPower u (m*n) := by
  induction n with
  | zero => simp only [Nat.mul_zero,wordPower]
  | succ n ih =>
      rw [wordPower,ih,show m*(n+1) = m+m*n by ring,wordPower_add]

/-- A nonempty word which is not a proper whole-word power. -/
def Primitive (u : List α) : Prop :=
  u ≠ [] ∧ ∀ v : List α, ∀ n : ℕ, 1 < n → u ≠ wordPower v n

/-- Every nonempty word has a primitive whole-word root. -/
theorem exists_primitive_root (u : List α) (hu : u ≠ []) :
    ∃ v : List α, ∃ n : ℕ, Primitive v ∧ 0 < n ∧ u = wordPower v n := by
  classical
  generalize hN : u.length = N
  induction N using Nat.strong_induction_on generalizing u with
  | h N ih =>
      by_cases hp : Primitive u
      · refine ⟨u,1,hp,by omega,?_⟩
        simp only [wordPower,List.append_nil]
      have hex : ∃ v : List α, ∃ n : ℕ, 1 < n ∧ u = wordPower v n := by
        by_contra! hn
        exact hp ⟨hu,hn⟩
      obtain ⟨v,n,hn,he⟩ := hex
      have hv0 : v ≠ [] := by
        intro h; rw [h,wordPower_nil] at he; exact hu he
      have hvlen : 0 < v.length := List.length_pos_iff.mpr hv0
      have hlen : N = n*v.length := by rw [← hN,he,wordPower_length]
      have hlt : v.length < N := by nlinarith only [hlen,hn,hvlen]
      obtain ⟨t,m,ht,hm,hv⟩ := ih v.length hlt v hv0 rfl
      refine ⟨t,m*n,ht,Nat.mul_pos hm (by omega),?_⟩
      rw [he,hv,wordPower_mul]

/-- Single-step rotation iterates to ordinary list rotation. -/
theorem iterate_rotate_one (u : List α) (n : ℕ) :
    (fun v : List α => v.rotate 1)^[n] u = u.rotate n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply',ih,List.rotate_rotate]

/-- Each nonempty word is a periodic point of rotation. -/
theorem periodic_rotate (u : List α) :
    Function.IsPeriodicPt (fun v : List α => v.rotate 1) u.length u := by
  change (fun v : List α => v.rotate 1)^[u.length] u = u
  rw [iterate_rotate_one,List.rotate_length]

/-- A primitive word has exactly its length as minimal rotation period. -/
theorem minimalPeriod_primitive (u : List α) (hu : Primitive u) :
    Function.minimalPeriod (fun v : List α => v.rotate 1) u = u.length := by
  let f : List α → List α := fun v => v.rotate 1
  let m := Function.minimalPeriod f u
  have hul : 0 < u.length := List.length_pos_iff.mpr hu.1
  have hm0 : 0 < m := (periodic_rotate u).minimalPeriod_pos hul
  have hm : m ≤ u.length := (periodic_rotate u).minimalPeriod_le hul
  have hrot : u.rotate m = u := by
    rw [← iterate_rotate_one]
    exact Function.iterate_minimalPeriod
  have hcomm : u.take m ++ u.drop m = u.drop m ++ u.take m := by
    rw [List.take_append_drop, ← List.rotate_eq_drop_append_take hm]
    exact hrot.symm
  obtain ⟨v,a,b,ha,hb⟩ := commuting_words_common_root (u.take m) (u.drop m) hcomm
  have he : u = wordPower v (a+b) := by
    rw [← List.take_append_drop m u,ha,hb,← wordPower_add]
  have hab : a+b ≤ 1 := by
    by_contra! hn
    exact hu.2 v (a+b) hn he
  have hma : m = a*v.length := by
    have h := congrArg List.length ha
    simpa only [List.length_take,Nat.min_eq_left hm,wordPower_length] using h
  have ha0 : 0 < a := by
    by_contra! hn
    have hz : a = 0 := Nat.eq_zero_of_le_zero hn
    simp only [hz,Nat.zero_mul] at hma
    omega
  have hae : a = 1 := by omega
  have hbe : b = 0 := by omega
  have hlen := congrArg List.length he
  simp only [wordPower_length,hae,hbe,Nat.add_zero,Nat.one_mul] at hlen
  change m = u.length
  simpa only [hae,Nat.one_mul,← hlen] using hma

/-- Cyclically moving a prefix through a whole-word power. -/
theorem wordPower_conjugate (u v : List α) (n : ℕ) :
    wordPower (u++v) n ++ u = u ++ wordPower (v++u) n := by
  induction n with
  | zero => simp only [wordPower,List.nil_append,List.append_nil]
  | succ n ih =>
      simp only [wordPower,List.append_assoc]
      rw [ih]

/-- Single-step rotation commutes with whole-word repetition. -/
theorem wordPower_rotate_one (u : List α) (n : ℕ) :
    (wordPower u n).rotate 1 = wordPower (u.rotate 1) n := by
  cases u with
  | nil => simp only [wordPower_nil,List.rotate_nil]
  | cons a v =>
      cases n with
      | zero => simp only [wordPower,List.rotate_nil]
      | succ n =>
          calc
            _ = v ++ (wordPower (a::v) n ++ [a]) := by
              simp only [wordPower,List.cons_append,List.rotate_cons_succ,List.rotate_zero,
                List.append_assoc]
            _ = v ++ ([a] ++ wordPower (v++[a]) n) :=
              congrArg (fun t => v++t) (wordPower_conjugate [a] v n)
            _ = _ := by
              simp only [wordPower,List.rotate_cons_succ,List.rotate_zero,List.append_assoc]

/-- Rotation at every offset commutes with whole-word repetition. -/
theorem wordPower_rotate (u : List α) (n k : ℕ) :
    (wordPower u n).rotate k = wordPower (u.rotate k) n := by
  induction k with
  | zero => simp only [List.rotate_zero]
  | succ k ih =>
      rw [← List.rotate_rotate _ k 1,ih,wordPower_rotate_one,List.rotate_rotate]

/-- A positive whole-word power determines its base word uniquely. -/
theorem wordPower_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (fun u : List α => wordPower u n) := by
  intro u v he
  have hlen := congrArg List.length he
  simp only [wordPower_length] at hlen
  have huv : u.length = v.length := Nat.mul_left_cancel hn hlen
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have ht (t : List α) : (wordPower t (k+1)).take t.length = t := by
    rw [wordPower,List.take_append_of_le_length le_rfl,List.take_length]
  have h := congrArg (fun t : List α => t.take u.length) he
  rw [ht,huv,ht] at h
  exact h

/-- Repeating a word does not change its minimal rotation period. -/
theorem minimalPeriod_wordPower (u : List α) {n : ℕ} (hn : 0 < n) :
    Function.minimalPeriod (fun v : List α => v.rotate 1) (wordPower u n) =
      Function.minimalPeriod (fun v : List α => v.rotate 1) u := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro k
  change ((fun v : List α => v.rotate 1)^[k] (wordPower u n) = wordPower u n) ↔
    ((fun v : List α => v.rotate 1)^[k] u = u)
  rw [iterate_rotate_one,iterate_rotate_one,wordPower_rotate]
  exact (wordPower_injective hn).eq_iff

/-- Equality of positive powers of primitive words forces equality of the roots. -/
theorem primitive_root_unique {u v : List α} (hu : Primitive u) (hv : Primitive v)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (he : wordPower u m = wordPower v n) : u = v := by
  have hl : u.length = v.length := by
    rw [← minimalPeriod_primitive u hu,← minimalPeriod_primitive v hv,
      ← minimalPeriod_wordPower u hm,← minimalPeriod_wordPower v hn,he]
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have h := congrArg (fun t : List α => t.take u.length) he
  simp only [wordPower,List.take_append_of_le_length le_rfl,List.take_length] at h
  rw [hl,List.take_append_of_le_length le_rfl,List.take_length] at h
  exact h

/-- For nonempty words, primitive means maximal rotation period. -/
theorem primitive_iff_minimalPeriod {u : List α} (hu : u ≠ []) :
    Primitive u ↔ Function.minimalPeriod (fun v : List α => v.rotate 1) u = u.length := by
  refine ⟨minimalPeriod_primitive u,fun hp => ⟨hu,?_⟩⟩
  intro v n hn he
  have hv : v ≠ [] := by intro hz; rw [hz,wordPower_nil] at he; exact hu he
  have hvlen : 0 < v.length := List.length_pos_iff.mpr hv
  have hm := (periodic_rotate v).minimalPeriod_le hvlen
  rw [he,minimalPeriod_wordPower v (by omega),wordPower_length] at hp
  nlinarith only [hm,hp,hn,hvlen]

/-- Every rotation of a primitive word remains primitive. -/
theorem Primitive.rotate {u : List α} (hu : Primitive u) (k : ℕ) : Primitive (u.rotate k) := by
  have hne : u.rotate k ≠ [] := by
    intro he
    have hlen := congrArg List.length he
    simp only [List.length_rotate,List.length_nil] at hlen
    exact hu.1 (List.length_eq_zero_iff.mp hlen)
  apply (primitive_iff_minimalPeriod hne).mpr
  have hx := Function.mk_mem_periodicPts (List.length_pos_iff.mpr hu.1) (periodic_rotate u)
  have h := Function.minimalPeriod_apply_iterate hx k
  simpa only [iterate_rotate_one,minimalPeriod_primitive u hu,List.length_rotate] using h

/-- Primitive pair cycles and their repetition exponents are unique. -/
theorem primitive_powers_isRotated_iff {u v : List α} (hu : Primitive u) (hv : Primitive v)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    List.IsRotated (wordPower u m) (wordPower v n) ↔ List.IsRotated u v ∧ m = n := by
  constructor
  · rintro ⟨k,hk⟩
    rw [wordPower_rotate] at hk
    have hroot : u.rotate k = v := primitive_root_unique (hu.rotate k) hv hm hn hk
    have hlen := congrArg List.length hk
    simp only [wordPower_length,List.length_rotate] at hlen
    have huv : u.length = v.length := by simpa only [List.length_rotate] using congrArg List.length hroot
    rw [huv] at hlen
    exact ⟨⟨k,hroot⟩,Nat.mul_right_cancel (List.length_pos_iff.mpr hv.1) hlen⟩
  · rintro ⟨⟨k,hk⟩,rfl⟩
    exact ⟨k,by rw [wordPower_rotate,hk]⟩

/-- A primitive word has exactly one distinct rotation for each of its positions. -/
def primitiveRotationEquiv (u : List α) (hu : Primitive u) :
    Fin u.length ≃ {v : List α // List.IsRotated u v} :=
  Equiv.ofBijective (fun i => ⟨u.rotate i.val,⟨i.val,rfl⟩⟩) (by
    constructor
    · intro i j hij
      apply Fin.ext
      apply (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
        (by rw [minimalPeriod_primitive u hu];exact i.isLt)
        (by rw [minimalPeriod_primitive u hu];exact j.isLt)).mp
      simpa only [iterate_rotate_one] using congrArg Subtype.val hij
    · intro v
      obtain ⟨k,hk⟩ := v.property
      refine ⟨⟨k%u.length,Nat.mod_lt _ (List.length_pos_iff.mpr hu.1)⟩,Subtype.ext ?_⟩
      exact (List.rotate_mod u k).trans hk)

#print axioms exists_primitive_root
#print axioms minimalPeriod_primitive
#print axioms wordPower_rotate
#print axioms wordPower_injective
#print axioms minimalPeriod_wordPower
#print axioms primitive_root_unique
#print axioms primitive_iff_minimalPeriod
#print axioms Primitive.rotate
#print axioms primitive_powers_isRotated_iff
#print axioms primitiveRotationEquiv
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPrimitiveCycles
