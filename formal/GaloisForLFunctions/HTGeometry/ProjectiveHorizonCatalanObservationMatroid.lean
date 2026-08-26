import GaloisForLFunctions.HTGeometry.ProjectiveHorizonObservationMatroid
import Mathlib.Combinatorics.Enumerative.DyckWord

open List
open DyckStep

namespace GaloisForLFunctions.HTGeometry

/-- Expansion of one two-coloured Motzkin observation step into two Dyck steps. -/
def reciprocalObservationStepDyckPair : ReciprocalObservationStep → List DyckStep
  | .up => [U, U]
  | .down => [D, D]
  | .rawOnly => [D, U]
  | .reciprocalOnly => [U, D]

/-- Pairwise Dyck expansion of a finite observation word, without forced endpoints. -/
def reciprocalObservationDyckBody : List ReciprocalObservationStep → List DyckStep
  | [] => []
  | s :: w => reciprocalObservationStepDyckPair s ++ reciprocalObservationDyckBody w

@[simp] theorem length_reciprocalObservationStepDyckPair (s : ReciprocalObservationStep) :
    (reciprocalObservationStepDyckPair s).length = 2 := by
  cases s <;> rfl

@[simp] theorem length_reciprocalObservationDyckBody
    (w : List ReciprocalObservationStep) :
    (reciprocalObservationDyckBody w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      simp [reciprocalObservationDyckBody, ih]
      omega

theorem count_U_reciprocalObservationDyckBody
    (w : List ReciprocalObservationStep) :
    (reciprocalObservationDyckBody w).count U =
      2 * w.count .up + w.count .rawOnly + w.count .reciprocalOnly := by
  induction w with
  | nil => simp [reciprocalObservationDyckBody]
  | cons s w ih =>
      cases s <;> simp [reciprocalObservationDyckBody, reciprocalObservationStepDyckPair, ih] <;>
        omega

theorem count_D_reciprocalObservationDyckBody
    (w : List ReciprocalObservationStep) :
    (reciprocalObservationDyckBody w).count D =
      2 * w.count .down + w.count .rawOnly + w.count .reciprocalOnly := by
  induction w with
  | nil => simp [reciprocalObservationDyckBody]
  | cons s w ih =>
      cases s <;> simp [reciprocalObservationDyckBody, reciprocalObservationStepDyckPair, ih] <;>
        omega

/-- Prefix nonnegativity of a two-coloured Motzkin word, with an initial height allowance. -/
def ReciprocalObservationNonnegativeFrom
    (k : ℕ) (w : List ReciprocalObservationStep) : Prop :=
  ∀ i, (w.take i).count .down ≤ k + (w.take i).count .up

theorem reciprocalObservationNonnegativeFrom_tail_up {k : ℕ}
    {w : List ReciprocalObservationStep}
    (h : ReciprocalObservationNonnegativeFrom k (.up :: w)) :
    ReciprocalObservationNonnegativeFrom (k + 1) w := by
  intro i
  have hi := h (i + 1)
  simpa [ReciprocalObservationNonnegativeFrom, take_succ_cons, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hi

theorem reciprocalObservationNonnegativeFrom_tail_down {k : ℕ}
    {w : List ReciprocalObservationStep}
    (h : ReciprocalObservationNonnegativeFrom k (.down :: w)) :
    0 < k ∧ ReciprocalObservationNonnegativeFrom (k - 1) w := by
  have hk := h 1
  have hkpos : 0 < k := by
    simp at hk
    omega
  refine ⟨hkpos, fun i => ?_⟩
  have hi := h (i + 1)
  simp only [take_succ_cons, count_cons, beq_self_eq_true, ite_true,
    beq_iff_eq, reduceCtorEq, ite_false] at hi
  omega

theorem reciprocalObservationNonnegativeFrom_tail_rawOnly {k : ℕ}
    {w : List ReciprocalObservationStep}
    (h : ReciprocalObservationNonnegativeFrom k (.rawOnly :: w)) :
    ReciprocalObservationNonnegativeFrom k w := by
  intro i
  simpa [ReciprocalObservationNonnegativeFrom, take_succ_cons] using h (i + 1)

theorem reciprocalObservationNonnegativeFrom_tail_reciprocalOnly {k : ℕ}
    {w : List ReciprocalObservationStep}
    (h : ReciprocalObservationNonnegativeFrom k (.reciprocalOnly :: w)) :
    ReciprocalObservationNonnegativeFrom k w := by
  intro i
  simpa [ReciprocalObservationNonnegativeFrom, take_succ_cons] using h (i + 1)

/-- Prefix nonnegativity of a Dyck-step list with an initial height allowance. -/
def DyckNonnegativeFrom (k : ℕ) (w : List DyckStep) : Prop :=
  ∀ i, (w.take i).count D ≤ k + (w.take i).count U

theorem reciprocalObservationDyckBody_nonnegativeFrom
    (w : List ReciprocalObservationStep) (k : ℕ)
    (h : ReciprocalObservationNonnegativeFrom k w) :
    DyckNonnegativeFrom (2 * k + 1) (reciprocalObservationDyckBody w) := by
  induction w generalizing k with
  | nil => simp [DyckNonnegativeFrom, reciprocalObservationDyckBody]
  | cons s w ih =>
      cases s with
      | up =>
          have ht := reciprocalObservationNonnegativeFrom_tail_up h
          have htail := ih (k + 1) ht
          intro i
          by_cases hi : i ≤ 2
          · interval_cases i <;>
              simp [reciprocalObservationDyckBody, reciprocalObservationStepDyckPair]
          · have hi2 : 2 ≤ i := by omega
            have htake :
                ([U, U] ++ reciprocalObservationDyckBody w).take i =
                  [U, U] ++ (reciprocalObservationDyckBody w).take (i - 2) := by
              rw [take_append]
              have hp : [U, U].length ≤ i := by simp; omega
              rw [take_of_length_le hp]
              simp
            rw [reciprocalObservationDyckBody, reciprocalObservationStepDyckPair, htake]
            simp only [count_append, count_cons, count_nil, beq_self_eq_true, ite_true,
              beq_iff_eq, reduceCtorEq, ite_false, Nat.zero_add, Nat.add_zero]
            have := htail (i - 2)
            change ((reciprocalObservationDyckBody w).take (i - 2)).count D ≤
              2 * (k + 1) + 1 +
                ((reciprocalObservationDyckBody w).take (i - 2)).count U at this
            omega
      | down =>
          obtain ⟨hk, ht⟩ := reciprocalObservationNonnegativeFrom_tail_down h
          have htail := ih (k - 1) ht
          intro i
          by_cases hi : i ≤ 2
          · interval_cases i <;>
              simp [reciprocalObservationDyckBody, reciprocalObservationStepDyckPair] <;>
              omega
          · have hi2 : 2 ≤ i := by omega
            have htake :
                ([D, D] ++ reciprocalObservationDyckBody w).take i =
                  [D, D] ++ (reciprocalObservationDyckBody w).take (i - 2) := by
              rw [take_append]
              have hp : [D, D].length ≤ i := by simp; omega
              rw [take_of_length_le hp]
              simp
            rw [reciprocalObservationDyckBody, reciprocalObservationStepDyckPair, htake]
            simp only [count_append, count_cons, count_nil, beq_self_eq_true, ite_true,
              beq_iff_eq, reduceCtorEq, ite_false, Nat.zero_add, Nat.add_zero]
            have := htail (i - 2)
            change ((reciprocalObservationDyckBody w).take (i - 2)).count D ≤
              2 * (k - 1) + 1 +
                ((reciprocalObservationDyckBody w).take (i - 2)).count U at this
            omega
      | rawOnly =>
          have ht := reciprocalObservationNonnegativeFrom_tail_rawOnly h
          have htail := ih k ht
          intro i
          by_cases hi : i ≤ 2
          · interval_cases i <;>
              simp [reciprocalObservationDyckBody, reciprocalObservationStepDyckPair]
          · have hi2 : 2 ≤ i := by omega
            have htake :
                ([D, U] ++ reciprocalObservationDyckBody w).take i =
                  [D, U] ++ (reciprocalObservationDyckBody w).take (i - 2) := by
              rw [take_append]
              have hp : [D, U].length ≤ i := by simp; omega
              rw [take_of_length_le hp]
              simp
            rw [reciprocalObservationDyckBody, reciprocalObservationStepDyckPair, htake]
            simp only [count_append, count_cons, count_nil, beq_self_eq_true, ite_true,
              beq_iff_eq, reduceCtorEq, ite_false, Nat.zero_add, Nat.add_zero]
            have := htail (i - 2)
            change ((reciprocalObservationDyckBody w).take (i - 2)).count D ≤
              2 * k + 1 +
                ((reciprocalObservationDyckBody w).take (i - 2)).count U at this
            omega
      | reciprocalOnly =>
          have ht := reciprocalObservationNonnegativeFrom_tail_reciprocalOnly h
          have htail := ih k ht
          intro i
          by_cases hi : i ≤ 2
          · interval_cases i <;>
              simp [reciprocalObservationDyckBody, reciprocalObservationStepDyckPair]
          · have hi2 : 2 ≤ i := by omega
            have htake :
                ([U, D] ++ reciprocalObservationDyckBody w).take i =
                  [U, D] ++ (reciprocalObservationDyckBody w).take (i - 2) := by
              rw [take_append]
              have hp : [U, D].length ≤ i := by simp; omega
              rw [take_of_length_le hp]
              simp
            rw [reciprocalObservationDyckBody, reciprocalObservationStepDyckPair, htake]
            simp only [count_append, count_cons, count_nil, beq_self_eq_true, ite_true,
              beq_iff_eq, reduceCtorEq, ite_false, Nat.zero_add, Nat.add_zero]
            have := htail (i - 2)
            change ((reciprocalObservationDyckBody w).take (i - 2)).count D ≤
              2 * k + 1 +
                ((reciprocalObservationDyckBody w).take (i - 2)).count U at this
            omega

/-- A balanced nonnegative two-coloured Motzkin word of reciprocal observations. -/
structure ReciprocalObservationWord where
  toList : List ReciprocalObservationStep
  count_up_eq_count_down : toList.count .up = toList.count .down
  count_down_le_count_up (i : ℕ) :
    (toList.take i).count .down ≤ (toList.take i).count .up

/-- Forced-endpoint Dyck expansion `U · pair(word) · D`. -/
def reciprocalObservationWordDyckList (p : ReciprocalObservationWord) : List DyckStep :=
  U :: reciprocalObservationDyckBody p.toList ++ [D]

theorem reciprocalObservationWordDyckList_count_U_eq_count_D
    (p : ReciprocalObservationWord) :
    (reciprocalObservationWordDyckList p).count U =
      (reciprocalObservationWordDyckList p).count D := by
  simp only [reciprocalObservationWordDyckList, count_cons, count_append,
    count_U_reciprocalObservationDyckBody,
    count_D_reciprocalObservationDyckBody, p.count_up_eq_count_down]
  simp

theorem reciprocalObservationWordDyckList_nonnegative
    (p : ReciprocalObservationWord) (i : ℕ) :
    ((reciprocalObservationWordDyckList p).take i).count D ≤
      ((reciprocalObservationWordDyckList p).take i).count U := by
  have hp : ReciprocalObservationNonnegativeFrom 0 p.toList := by
    intro j
    simpa using p.count_down_le_count_up j
  have hbody := reciprocalObservationDyckBody_nonnegativeFrom p.toList 0 hp
  cases i with
  | zero => simp
  | succ j =>
      change ((U :: (reciprocalObservationDyckBody p.toList ++ [D])).take (j + 1)).count D ≤
        ((U :: (reciprocalObservationDyckBody p.toList ++ [D])).take (j + 1)).count U
      rw [take_succ_cons]
      simp only [count_cons, beq_iff_eq, reduceCtorEq, ite_false, beq_self_eq_true, ite_true]
      by_cases hj : j ≤ (reciprocalObservationDyckBody p.toList).length
      · rw [take_append_of_le_length hj]
        have := hbody j
        simpa [DyckNonnegativeFrom, Nat.add_comm] using this
      · have hlen :
          (reciprocalObservationDyckBody p.toList ++ [D]).length ≤ j := by
          simp only [length_append, length_singleton]
          omega
        rw [take_of_length_le hlen]
        have hbal := reciprocalObservationWordDyckList_count_U_eq_count_D p
        simpa [reciprocalObservationWordDyckList] using hbal.ge

/-- Dyck word canonically encoded by a complete reciprocal observation word. -/
def ReciprocalObservationWord.toDyckWord (p : ReciprocalObservationWord) : DyckWord where
  toList := reciprocalObservationWordDyckList p
  count_U_eq_count_D := reciprocalObservationWordDyckList_count_U_eq_count_D p
  count_D_le_count_U := reciprocalObservationWordDyckList_nonnegative p

@[simp] theorem reciprocalObservationWord_toDyckWord_length
    (p : ReciprocalObservationWord) :
    p.toDyckWord.toList.length = 2 * (p.toList.length + 1) := by
  simp [ReciprocalObservationWord.toDyckWord, reciprocalObservationWordDyckList,
    Nat.mul_add]

@[simp] theorem reciprocalObservationWord_toDyckWord_semilength
    (p : ReciprocalObservationWord) :
    p.toDyckWord.semilength = p.toList.length + 1 := by
  have hlen := p.toDyckWord.two_mul_semilength_eq_length
  rw [reciprocalObservationWord_toDyckWord_length] at hlen
  omega

/-- Decoding of one Dyck-step pair into a two-coloured Motzkin observation step. -/
def reciprocalObservationStepOfDyckPair : DyckStep → DyckStep → ReciprocalObservationStep
  | U, U => .up
  | D, D => .down
  | D, U => .rawOnly
  | U, D => .reciprocalOnly

/-- Pairwise decoding of an even Dyck-step list. A final unpaired step is discarded. -/
def reciprocalObservationDecodeBody : List DyckStep → List ReciprocalObservationStep
  | a :: b :: w => reciprocalObservationStepOfDyckPair a b ::
      reciprocalObservationDecodeBody w
  | _ => []

@[simp] theorem reciprocalObservationDecodeBody_encode
    (w : List ReciprocalObservationStep) :
    reciprocalObservationDecodeBody (reciprocalObservationDyckBody w) = w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
      cases s <;>
        simp [reciprocalObservationDyckBody, reciprocalObservationStepDyckPair,
          reciprocalObservationDecodeBody, reciprocalObservationStepOfDyckPair, ih]

theorem reciprocalObservationDyckBody_decode_of_even_length :
    ∀ w : List DyckStep, 2 ∣ w.length →
      reciprocalObservationDyckBody (reciprocalObservationDecodeBody w) = w
  | [], _ => rfl
  | [a], h => by
      rcases h with ⟨k, hk⟩
      simp at hk
      omega
  | a :: b :: w, h => by
      have hw : 2 ∣ w.length := by
        rcases h with ⟨k, hk⟩
        refine ⟨k - 1, ?_⟩
        simp only [length_cons] at hk
        omega
      simp only [reciprocalObservationDecodeBody, reciprocalObservationDyckBody]
      rw [reciprocalObservationDyckBody_decode_of_even_length w hw]
      cases a <;> cases b <;> rfl

@[simp] theorem reciprocalObservationDecodeBody_length_of_even_length
    (w : List DyckStep) (h : 2 ∣ w.length) :
    2 * (reciprocalObservationDecodeBody w).length = w.length := by
  rw [← length_reciprocalObservationDyckBody,
    reciprocalObservationDyckBody_decode_of_even_length w h]

theorem reciprocalObservationDyckBody_take
    (w : List ReciprocalObservationStep) (i : ℕ) :
    reciprocalObservationDyckBody (w.take i) =
      (reciprocalObservationDyckBody w).take (2 * i) := by
  induction w generalizing i with
  | nil => simp [reciprocalObservationDyckBody]
  | cons s w ih =>
      cases i with
      | zero => simp [reciprocalObservationDyckBody]
      | succ i =>
          rw [take_succ_cons, reciprocalObservationDyckBody,
            reciprocalObservationDyckBody, ih]
          cases s <;>
            simp [reciprocalObservationStepDyckPair, Nat.mul_succ]

@[simp] theorem reciprocalObservationDecodeBody_take_two_mul
    (w : List DyckStep) (i : ℕ) :
    reciprocalObservationDecodeBody (w.take (2 * i)) =
      (reciprocalObservationDecodeBody w).take i := by
  induction i generalizing w with
  | zero => simp [reciprocalObservationDecodeBody]
  | succ i ih =>
      cases w with
      | nil => simp [reciprocalObservationDecodeBody]
      | cons a w =>
          cases w with
          | nil =>
              rw [show 2 * (i + 1) = (2 * i + 1) + 1 by omega, take_succ_cons]
              simp [reciprocalObservationDecodeBody]
          | cons b w =>
              rw [show 2 * (i + 1) = (2 * i + 1) + 1 by omega, take_succ_cons,
                take_succ_cons]
              simp [reciprocalObservationDecodeBody, ih]

/-- Interior obtained by removing the forced first and last steps of a nonempty Dyck word. -/
def reciprocalObservationDyckInner (p : DyckWord) : List DyckStep :=
  p.toList.dropLast.tail

theorem reciprocalObservationDyckInner_length (p : DyckWord) (h : p ≠ 0) :
    (reciprocalObservationDyckInner p).length + 2 = 2 * p.semilength := by
  have hsemi : 0 < p.semilength := by
    by_contra hz
    apply h
    rw [← DyckWord.toList_eq_nil]
    have hlen := p.two_mul_semilength_eq_length
    simp at hz
    simpa [hz] using hlen.symm
  have hlen := p.two_mul_semilength_eq_length
  simp only [reciprocalObservationDyckInner, length_tail, length_dropLast]
  omega

theorem reciprocalObservationDyckInner_even (p : DyckWord) (h : p ≠ 0) :
    2 ∣ (reciprocalObservationDyckInner p).length := by
  use p.semilength - 1
  have := reciprocalObservationDyckInner_length p h
  have hsemi : 0 < p.semilength := by
    by_contra hz
    have : p.toList.length = 0 := by
      rw [← p.two_mul_semilength_eq_length]
      omega
    apply h
    rw [← DyckWord.toList_eq_nil]
    simpa using this
  omega

theorem reciprocalObservationDyckInner_count_U_eq_count_D
    (p : DyckWord) (h : p ≠ 0) :
    (reciprocalObservationDyckInner p).count U =
      (reciprocalObservationDyckInner p).count D := by
  have hbal := p.count_U_eq_count_D
  have hrec := p.cons_tail_dropLast_concat h
  rw [← hrec] at hbal
  simpa [reciprocalObservationDyckInner] using hbal

theorem reciprocalObservationDecodeDyckInner_count_up_eq_count_down
    (p : DyckWord) (h : p ≠ 0) :
    (reciprocalObservationDecodeBody (reciprocalObservationDyckInner p)).count .up =
      (reciprocalObservationDecodeBody (reciprocalObservationDyckInner p)).count .down := by
  let w := reciprocalObservationDecodeBody (reciprocalObservationDyckInner p)
  have henc : reciprocalObservationDyckBody w = reciprocalObservationDyckInner p :=
    reciprocalObservationDyckBody_decode_of_even_length _
      (reciprocalObservationDyckInner_even p h)
  have hbal := reciprocalObservationDyckInner_count_U_eq_count_D p h
  rw [← henc, count_U_reciprocalObservationDyckBody,
    count_D_reciprocalObservationDyckBody] at hbal
  change w.count .up = w.count .down
  omega

theorem reciprocalObservationDecodeDyckInner_nonnegative
    (p : DyckWord) (h : p ≠ 0) (i : ℕ) :
    ((reciprocalObservationDecodeBody (reciprocalObservationDyckInner p)).take i).count .down ≤
      ((reciprocalObservationDecodeBody (reciprocalObservationDyckInner p)).take i).count .up := by
  let w := reciprocalObservationDecodeBody (reciprocalObservationDyckInner p)
  have henc : reciprocalObservationDyckBody w = reciprocalObservationDyckInner p :=
    reciprocalObservationDyckBody_decode_of_even_length _
      (reciprocalObservationDyckInner_even p h)
  by_cases hi : i ≤ w.length
  · have hpref :
        2 * i + 1 ≤ (U :: reciprocalObservationDyckBody w).length := by
      simp
      omega
    have htake :
        (((U :: reciprocalObservationDyckBody w) ++ [D]).take (2 * i + 1)) =
          U :: reciprocalObservationDyckBody (w.take i) := by
      rw [take_append_of_le_length hpref, take_succ_cons,
        reciprocalObservationDyckBody_take]
    have hd := p.count_D_le_count_U (2 * i + 1)
    have hrec := p.cons_tail_dropLast_concat h
    have henc' : p.toList.dropLast.tail = reciprocalObservationDyckBody w := by
      simpa [reciprocalObservationDyckInner] using henc.symm
    rw [← hrec, henc', htake] at hd
    simp only [count_cons, beq_iff_eq, reduceCtorEq, ite_false, beq_self_eq_true, ite_true,
      count_U_reciprocalObservationDyckBody,
      count_D_reciprocalObservationDyckBody] at hd
    change (w.take i).count .down ≤ (w.take i).count .up
    omega
  · have hwi : w.length ≤ i := by omega
    change (w.take i).count .down ≤ (w.take i).count .up
    rw [take_of_length_le hwi]
    exact (reciprocalObservationDecodeDyckInner_count_up_eq_count_down p h).ge

@[ext] theorem ReciprocalObservationWord.ext
    {p q : ReciprocalObservationWord} (h : p.toList = q.toList) : p = q := by
  cases p
  cases q
  cases h
  rfl

/-- Canonical reciprocal observation word decoded from a nonempty Dyck word. -/
def ReciprocalObservationWord.ofDyckWord (p : DyckWord) (h : p ≠ 0) :
    ReciprocalObservationWord where
  toList := reciprocalObservationDecodeBody (reciprocalObservationDyckInner p)
  count_up_eq_count_down :=
    reciprocalObservationDecodeDyckInner_count_up_eq_count_down p h
  count_down_le_count_up :=
    reciprocalObservationDecodeDyckInner_nonnegative p h

@[simp] theorem ReciprocalObservationWord.ofDyckWord_toList
    (p : DyckWord) (h : p ≠ 0) :
    (ReciprocalObservationWord.ofDyckWord p h).toList =
      reciprocalObservationDecodeBody (reciprocalObservationDyckInner p) := rfl

theorem ReciprocalObservationWord.toDyckWord_ne_zero
    (p : ReciprocalObservationWord) : p.toDyckWord ≠ 0 := by
  rw [← DyckWord.toList_ne_nil]
  simp [ReciprocalObservationWord.toDyckWord, reciprocalObservationWordDyckList]

@[simp] theorem ReciprocalObservationWord.toDyckWord_ofDyckWord
    (p : DyckWord) (h : p ≠ 0) :
    (ReciprocalObservationWord.ofDyckWord p h).toDyckWord = p := by
  apply DyckWord.ext
  change (U :: reciprocalObservationDyckBody
    (reciprocalObservationDecodeBody (reciprocalObservationDyckInner p))) ++ [D] = p.toList
  rw [reciprocalObservationDyckBody_decode_of_even_length _
    (reciprocalObservationDyckInner_even p h)]
  simpa [reciprocalObservationDyckInner] using p.cons_tail_dropLast_concat h

@[simp] theorem ReciprocalObservationWord.ofDyckWord_toDyckWord
    (p : ReciprocalObservationWord) :
    ReciprocalObservationWord.ofDyckWord p.toDyckWord p.toDyckWord_ne_zero = p := by
  apply ReciprocalObservationWord.ext
  change reciprocalObservationDecodeBody
    (([U] ++ reciprocalObservationDyckBody p.toList ++ [D]).dropLast.tail) = p.toList
  rw [dropLast_concat]
  simp [reciprocalObservationDecodeBody_encode]

theorem dyckWord_ne_zero_of_semilength_eq_succ
    (p : DyckWord) {n : ℕ} (h : p.semilength = n + 1) : p ≠ 0 := by
  intro hp
  subst p
  simp at h

@[simp] theorem ReciprocalObservationWord.ofDyckWord_length_add_one
    (p : DyckWord) (h : p ≠ 0) :
    (ReciprocalObservationWord.ofDyckWord p h).toList.length + 1 = p.semilength := by
  have heven := reciprocalObservationDyckInner_even p h
  have hdecode := reciprocalObservationDecodeBody_length_of_even_length
    (reciprocalObservationDyckInner p) heven
  have hinner := reciprocalObservationDyckInner_length p h
  change (reciprocalObservationDecodeBody (reciprocalObservationDyckInner p)).length + 1 =
    p.semilength
  omega

/-- Fixed-length complete reciprocal observations are exactly Dyck words one semilength longer. -/
def reciprocalObservationWordEquivDyckWord (n : ℕ) :
    {p : ReciprocalObservationWord // p.toList.length = n} ≃
      {p : DyckWord // p.semilength = n + 1} where
  toFun p := ⟨p.1.toDyckWord, by simp [p.2]⟩
  invFun p := by
    have hp : p.1 ≠ 0 := dyckWord_ne_zero_of_semilength_eq_succ p.1 p.2
    refine ⟨ReciprocalObservationWord.ofDyckWord p.1 hp, ?_⟩
    have hlen := ReciprocalObservationWord.ofDyckWord_length_add_one p.1 hp
    omega
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv p := by
    apply Subtype.ext
    have hp : p.1 ≠ 0 := dyckWord_ne_zero_of_semilength_eq_succ p.1 p.2
    simp

noncomputable instance reciprocalObservationWordFixedLengthFintype (n : ℕ) :
    Fintype {p : ReciprocalObservationWord // p.toList.length = n} :=
  Fintype.ofEquiv _ (reciprocalObservationWordEquivDyckWord n).symm

/-- Catalan law for complete reciprocal observation words of fixed length. -/
theorem card_reciprocalObservationWord_length_eq_catalan (n : ℕ) :
    Fintype.card {p : ReciprocalObservationWord // p.toList.length = n} =
      catalan (n + 1) := by
  rw [Fintype.card_congr (reciprocalObservationWordEquivDyckWord n),
    DyckWord.card_dyckWord_semilength_eq_catalan]

/-- For strictly ordered packets, prefix dominance is also sufficient for componentwise order. -/
theorem indexedObservation_componentwise_of_prefixCount
    {k n : ℕ} {missingRaw observedReciprocal : Fin k → Fin n}
    (hMissing : StrictMono missingRaw) (hObserved : StrictMono observedReciprocal)
    (hPrefix : ∀ r, indexedObservationPrefixCount observedReciprocal r ≤
      indexedObservationPrefixCount missingRaw r) :
    ∀ i, missingRaw i ≤ observedReciprocal i := by
  intro i
  by_contra hle
  have hstrict : observedReciprocal i < missingRaw i := lt_of_not_ge hle
  let r : ℕ := (observedReciprocal i : ℕ) + 1
  have hObservedSubset :
      Finset.Iic i ⊆
        (Finset.univ : Finset (Fin k)).filter
          (fun j => (observedReciprocal j : ℕ) < r) := by
    intro j hj
    simp only [Finset.mem_Iic] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hji : observedReciprocal j ≤ observedReciprocal i := hObserved.monotone hj
    exact Nat.lt_succ_of_le (by exact_mod_cast hji)
  have hMissingSubset :
      (Finset.univ : Finset (Fin k)).filter
          (fun j => (missingRaw j : ℕ) < r) ⊆ Finset.Iio i := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_Iio]
    by_contra hji
    have hij : i ≤ j := not_lt.mp hji
    have hmij : missingRaw i ≤ missingRaw j := hMissing.monotone hij
    have hmij' : (missingRaw i : ℕ) ≤ missingRaw j := by exact_mod_cast hmij
    have hstrict' : (observedReciprocal i : ℕ) < missingRaw i := by
      exact_mod_cast hstrict
    dsimp [r] at hj
    omega
  have hobsCard := Finset.card_le_card hObservedSubset
  have hmissingCard := Finset.card_le_card hMissingSubset
  have hp := hPrefix r
  simp only [indexedObservationPrefixCount] at hp
  simp at hobsCard hmissingCard
  omega

/-- Ordered componentwise dominance is equivalent to every prefix having nonnegative balance. -/
theorem indexedObservation_componentwise_iff_prefixCount
    {k n : ℕ} {missingRaw observedReciprocal : Fin k → Fin n}
    (hMissing : StrictMono missingRaw) (hObserved : StrictMono observedReciprocal) :
    (∀ i, missingRaw i ≤ observedReciprocal i) ↔
      (∀ r, indexedObservationPrefixCount observedReciprocal r ≤
        indexedObservationPrefixCount missingRaw r) := by
  constructor
  · intro h r
    exact indexedObservationPrefixCount_le_of_componentwise h r
  · exact indexedObservation_componentwise_of_prefixCount hMissing hObserved

/-- Ordered componentwise dominance is exactly nonnegativity of every latent-information prefix. -/
theorem indexedObservation_componentwise_iff_height_nonnegative
    {k n : ℕ} {missingRaw observedReciprocal : Fin k → Fin n}
    (hMissing : StrictMono missingRaw) (hObserved : StrictMono observedReciprocal) :
    (∀ i, missingRaw i ≤ observedReciprocal i) ↔
      (∀ r, 0 ≤ indexedObservationHeight missingRaw observedReciprocal r) := by
  rw [indexedObservation_componentwise_iff_prefixCount hMissing hObserved]
  constructor
  · intro h r
    simp only [indexedObservationHeight, sub_nonneg]
    exact_mod_cast h r
  · intro h r
    have hr := h r
    simp only [indexedObservationHeight, sub_nonneg] at hr
    exact_mod_cast hr

/-- Closed formalization package for the Catalan reciprocal-observation core. -/
theorem projectiveHorizonCatalanObservationMatroid_unconditional :
    (∀ (k n : ℕ) (missingRaw observedReciprocal : Fin k → Fin n),
      StrictMono missingRaw → StrictMono observedReciprocal →
        ((∀ i, missingRaw i ≤ observedReciprocal i) ↔
          ∀ r, 0 ≤ indexedObservationHeight missingRaw observedReciprocal r)) ∧
    (∀ n : ℕ, Nonempty
      ({p : ReciprocalObservationWord // p.toList.length = n} ≃
        {p : DyckWord // p.semilength = n + 1})) ∧
    (∀ n : ℕ,
      Fintype.card {p : ReciprocalObservationWord // p.toList.length = n} =
        catalan (n + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k n missingRaw observedReciprocal hMissing hObserved
    exact indexedObservation_componentwise_iff_height_nonnegative hMissing hObserved
  · intro n
    exact ⟨reciprocalObservationWordEquivDyckWord n⟩
  · exact card_reciprocalObservationWord_length_eq_catalan

end GaloisForLFunctions.HTGeometry
