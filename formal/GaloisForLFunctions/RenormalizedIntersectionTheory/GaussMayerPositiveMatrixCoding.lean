import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Positive modular words and integral matrix intertwiners

Every nonnegative integral determinant-one matrix has a unique word in the two
oriented unipotent generators. Euclidean row subtraction proves existence and
row dominance proves uniqueness. Positive integral intertwiners correspond
exactly to cyclic word splittings. Commuting matrices are powers of one word,
by Euclidean prefix cancellation.
-/

set_option autoImplicit false
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoding

abbrev NatMatrix := Matrix (Fin 2) (Fin 2) ℕ

/-- The determinant-one equation without truncated subtraction. -/
def Unimodular (A : NatMatrix) : Prop := A 0 0*A 1 1 = A 0 1*A 1 0+1

/-- The two oriented nonnegative modular generators. -/
def generator (b : Bool) : NatMatrix :=
  if b then !![1,1;0,1] else !![1,0;1,1]

/-- A literal product in the two oriented modular generators. -/
def matrixWord : List Bool → NatMatrix
  | [] => 1
  | b::v => generator b*matrixWord v

private theorem generator_true_mul (A : NatMatrix) :
    generator true*A = !![A 0 0+A 1 0,A 0 1+A 1 1;A 1 0,A 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator,Matrix.mul_apply,Fin.sum_univ_two]

private theorem generator_false_mul (A : NatMatrix) :
    generator false*A = !![A 0 0,A 0 1;A 0 0+A 1 0,A 0 1+A 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [generator,Matrix.mul_apply,Fin.sum_univ_two]

private theorem unimodular_one : Unimodular (1 : NatMatrix) := by
  norm_num [Unimodular,Matrix.one_apply]

private theorem unimodular_generator_mul {A : NatMatrix} (hA : Unimodular A) (b : Bool) :
    Unimodular (generator b*A) := by
  cases b
  · rw [generator_false_mul]
    change A 0 0*(A 0 1+A 1 1) = A 0 1*(A 0 0+A 1 0)+1
    dsimp [Unimodular] at hA
    nlinarith only [hA]
  · rw [generator_true_mul]
    change (A 0 0+A 1 0)*A 1 1 = (A 0 1+A 1 1)*A 1 0+1
    dsimp [Unimodular] at hA
    nlinarith only [hA]

/-- Every positive generator word has determinant one. -/
theorem matrixWord_unimodular (v : List Bool) : Unimodular (matrixWord v) := by
  induction v with
  | nil => exact unimodular_one
  | cons b v ih => exact unimodular_generator_mul ih b

private theorem diagonal_pos {A : NatMatrix} (hA : Unimodular A) :
    0 < A 0 0 ∧ 0 < A 1 1 := by
  dsimp [Unimodular] at hA
  constructor
  · by_contra h
    have hz : A 0 0 = 0 := by omega
    rw [hz,zero_mul] at hA
    omega
  · by_contra h
    have hz : A 1 1 = 0 := by omega
    rw [hz,mul_zero] at hA
    omega

private theorem rows_comparable_or_one {A : NatMatrix} (hA : Unimodular A) :
    (A 0 0 ≤ A 1 0 ∧ A 0 1 ≤ A 1 1) ∨
      (A 1 0 ≤ A 0 0 ∧ A 1 1 ≤ A 0 1) ∨ A = 1 := by
  have hp := diagonal_pos hA
  dsimp [Unimodular] at hA
  by_cases hac : A 0 0 ≤ A 1 0
  · left
    refine ⟨hac,?_⟩
    by_contra hbd
    have hbd' : A 1 1+1 ≤ A 0 1 := by omega
    have hm := Nat.mul_le_mul hac hbd'
    nlinarith only [hm,hA,hp.1]
  · by_cases hdb : A 1 1 ≤ A 0 1
    · exact Or.inr (Or.inl ⟨by omega,hdb⟩)
    · right; right
      have hac' : A 1 0+1 ≤ A 0 0 := by omega
      have hbd' : A 0 1+1 ≤ A 1 1 := by omega
      have hm := Nat.mul_le_mul hac' hbd'
      have hb : A 0 1 = 0 := by nlinarith only [hm,hA]
      have hc : A 1 0 = 0 := by nlinarith only [hm,hA]
      have had : A 0 0*A 1 1 = 1 := by simpa only [hb,hc,zero_mul,zero_add] using hA
      have ha : A 0 0 = 1 := by
        have h := Nat.le_mul_of_pos_right (A 0 0) hp.2
        omega
      have hd : A 1 1 = 1 := by
        rw [ha,one_mul] at had
        exact had
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha,hb,hc,hd]

/-- Euclidean row subtraction gives a word for every nonnegative unimodular matrix. -/
theorem exists_matrixWord (A : NatMatrix) (hA : Unimodular A) :
    ∃ v : List Bool, matrixWord v = A := by
  generalize hm : A 0 0+A 0 1+A 1 0+A 1 1 = m
  induction m using Nat.strong_induction_on generalizing A with
  | h m ih =>
      have hp := diagonal_pos hA
      rcases rows_comparable_or_one hA with hr | hr | rfl
      · let B : NatMatrix := !![A 0 0,A 0 1;A 1 0-A 0 0,A 1 1-A 0 1]
        have hc : (A 1 0-A 0 0)+A 0 0 = A 1 0 := Nat.sub_add_cancel hr.1
        have hd : (A 1 1-A 0 1)+A 0 1 = A 1 1 := Nat.sub_add_cancel hr.2
        have hB : Unimodular B := by
          change A 0 0*(A 1 1-A 0 1) = A 0 1*(A 1 0-A 0 0)+1
          dsimp [Unimodular] at hA
          nlinarith only [hA,hc,hd]
        have hsize : B 0 0+B 0 1+B 1 0+B 1 1 < m := by
          dsimp [B]
          omega
        obtain ⟨v,hv⟩ := ih _ hsize B hB rfl
        refine ⟨false::v,?_⟩
        rw [matrixWord,hv,generator_false_mul]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [B,hr.1,hr.2]
      · let B : NatMatrix := !![A 0 0-A 1 0,A 0 1-A 1 1;A 1 0,A 1 1]
        have ha : (A 0 0-A 1 0)+A 1 0 = A 0 0 := Nat.sub_add_cancel hr.1
        have hb : (A 0 1-A 1 1)+A 1 1 = A 0 1 := Nat.sub_add_cancel hr.2
        have hB : Unimodular B := by
          change (A 0 0-A 1 0)*A 1 1 = (A 0 1-A 1 1)*A 1 0+1
          dsimp [Unimodular] at hA
          nlinarith only [hA,ha,hb]
        have hsize : B 0 0+B 0 1+B 1 0+B 1 1 < m := by
          dsimp [B]
          omega
        obtain ⟨v,hv⟩ := ih _ hsize B hB rfl
        refine ⟨true::v,?_⟩
        rw [matrixWord,hv,generator_true_mul]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [B,ha,hb]
      · exact ⟨[],rfl⟩

private theorem generator_mul_injective (b : Bool) :
    Function.Injective (fun A : NatMatrix => generator b*A) := by
  intro A B h
  change generator b*A = generator b*B at h
  have h00 := congrArg (fun M : NatMatrix => M 0 0) h
  have h01 := congrArg (fun M : NatMatrix => M 0 1) h
  have h10 := congrArg (fun M : NatMatrix => M 1 0) h
  have h11 := congrArg (fun M : NatMatrix => M 1 1) h
  cases b
  · rw [generator_false_mul,generator_false_mul] at h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp at * <;> omega
  · rw [generator_true_mul,generator_true_mul] at h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp at * <;> omega

private theorem generator_word_ne_one (b : Bool) (v : List Bool) :
    generator b*matrixWord v ≠ 1 := by
  intro h
  have hp := diagonal_pos (matrixWord_unimodular v)
  cases b
  · have he := congrArg (fun M : NatMatrix => M 1 0) h
    rw [generator_false_mul] at he
    norm_num [Matrix.one_apply] at he
    omega
  · have he := congrArg (fun M : NatMatrix => M 0 1) h
    rw [generator_true_mul] at he
    norm_num [Matrix.one_apply] at he
    omega

private theorem opposite_generator_words_ne (u v : List Bool) :
    generator true*matrixWord u ≠ generator false*matrixWord v := by
  intro h
  have h00 := congrArg (fun M : NatMatrix => M 0 0) h
  have h01 := congrArg (fun M : NatMatrix => M 0 1) h
  have h10 := congrArg (fun M : NatMatrix => M 1 0) h
  have h11 := congrArg (fun M : NatMatrix => M 1 1) h
  rw [generator_true_mul,generator_false_mul] at h00 h01 h10 h11
  dsimp at h00 h01 h10 h11
  have hp := diagonal_pos (matrixWord_unimodular u)
  omega

/-- A nonnegative determinant-one matrix has exactly one word in the two modular generators. -/
theorem matrixWord_injective : Function.Injective matrixWord := by
  intro u
  induction u with
  | nil =>
      intro v hv
      cases v with
      | nil => rfl
      | cons b v => exact False.elim (generator_word_ne_one b v hv.symm)
  | cons b u ih =>
      intro v hv
      cases v with
      | nil => exact False.elim (generator_word_ne_one b u hv)
      | cons c v =>
          by_cases hbc : b = c
          · subst c
            exact congrArg (List.cons b) (ih (generator_mul_injective b hv))
          · cases b <;> cases c
            · exact False.elim (hbc rfl)
            · exact False.elim (opposite_generator_words_ne v u hv.symm)
            · exact False.elim (opposite_generator_words_ne u v hv)
            · exact False.elim (hbc rfl)

#print axioms exists_matrixWord
#print axioms matrixWord_injective

/-- Concatenation is the literal multiplication of the integral source matrices. -/
theorem matrixWord_append (u v : List Bool) :
    matrixWord (u++v) = matrixWord u*matrixWord v := by
  induction u with
  | nil => simp only [List.nil_append,matrixWord,one_mul]
  | cons b u ih => simp only [List.cons_append,matrixWord,ih,mul_assoc]

private theorem append_prefix_cases {α : Type*} (u v x y : List α)
    (h : u++x = v++y) :
    (∃ t, v = u++t ∧ x = t++y) ∨ (∃ t, u = v++t ∧ y = t++x) := by
  induction u generalizing v with
  | nil => exact Or.inl ⟨v,rfl,h⟩
  | cons a u ih =>
      cases v with
      | nil => exact Or.inr ⟨a::u,rfl,h.symm⟩
      | cons b v =>
          have hab : a = b := (List.cons.inj h).1
          subst b
          rcases ih v (List.cons.inj h).2 with ⟨t,hv,hx⟩ | ⟨t,hu,hy⟩
          · exact Or.inl ⟨t,congrArg (List.cons a) hv,hx⟩
          · exact Or.inr ⟨t,congrArg (List.cons a) hu,hy⟩

/-- A free-word intertwiner forces an exact cyclic splitting, with no loss of letters. -/
theorem cyclic_split_of_intertwiner {α : Type*} (u v c : List α)
    (h : v++c = c++u) : ∃ a b, u = a++b ∧ v = b++a := by
  generalize hm : c.length = m
  induction m using Nat.strong_induction_on generalizing c with
  | h m ih =>
      by_cases hv : v = []
      · subst v
        have hl := congrArg List.length h
        simp only [List.nil_append,List.length_append] at hl
        have hu : u = [] := by simpa using (show u.length = 0 by omega)
        subst u
        exact ⟨[],[],rfl,rfl⟩
      · rcases append_prefix_cases v c c u h with ⟨t,hc,ht⟩ | ⟨t,hv,hu⟩
        · have hl := congrArg List.length hc
          simp only [List.length_append] at hl
          have hvpos : 0 < v.length := by
            cases v with
            | nil => exact (hv rfl).elim
            | cons a v => exact Nat.succ_pos _
          have hlt : t.length < m := by omega
          exact ih _ hlt t (hc.symm.trans ht) rfl
        · exact ⟨t,c,hu,hv⟩

/-- Positive integral conjugators identify exactly cyclic words in the two modular generators. -/
theorem positive_intertwiner_iff_cyclic_split (u v : List Bool) :
    (∃ C : NatMatrix, Unimodular C ∧ C*matrixWord u = matrixWord v*C) ↔
      ∃ a b, u = a++b ∧ v = b++a := by
  constructor
  · rintro ⟨C,hC,h⟩
    obtain ⟨c,rfl⟩ := exists_matrixWord C hC
    have he : matrixWord (v++c) = matrixWord (c++u) := by
      rw [matrixWord_append,matrixWord_append]
      exact h.symm
    exact cyclic_split_of_intertwiner u v c (matrixWord_injective he)
  · rintro ⟨a,b,rfl,rfl⟩
    refine ⟨matrixWord b,matrixWord_unimodular b,?_⟩
    rw [matrixWord_append,matrixWord_append,mul_assoc]

#print axioms cyclic_split_of_intertwiner
#print axioms positive_intertwiner_iff_cyclic_split


/-- Repetition of an entire modular word. -/
def wordPower {α : Type*} (v : List α) : ℕ → List α
  | 0 => []
  | n+1 => v++wordPower v n

theorem wordPower_add {α : Type*} (v : List α) (m n : ℕ) :
    wordPower v (m+n) = wordPower v m++wordPower v n := by
  induction m with
  | zero => simp only [Nat.zero_add,wordPower,List.nil_append]
  | succ m ih =>
      rw [Nat.succ_add,wordPower,ih,wordPower,List.append_assoc]

theorem matrixWord_wordPower (v : List Bool) (n : ℕ) :
    matrixWord (wordPower v n) = matrixWord v^n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wordPower,matrixWord_append,ih,pow_succ']

/-- Euclidean prefix cancellation puts every commuting pair of words in one cyclic monoid. -/
theorem commuting_words_common_root {α : Type*} (u v : List α) (h : u++v = v++u) :
    ∃ w : List α, ∃ m n : ℕ, u = wordPower w m ∧ v = wordPower w n := by
  generalize hN : u.length+v.length = N
  induction N using Nat.strong_induction_on generalizing u v with
  | h N ih =>
      by_cases hu : u = []
      · subst u
        refine ⟨v,0,1,rfl,?_⟩
        simp only [wordPower,List.append_nil]
      by_cases hv : v = []
      · subst v
        refine ⟨u,1,0,?_,rfl⟩
        simp only [wordPower,List.append_nil]
      have hup : 0 < u.length := by
        cases u with
        | nil => exact (hu rfl).elim
        | cons a u => exact Nat.succ_pos _
      have hvp : 0 < v.length := by
        cases v with
        | nil => exact (hv rfl).elim
        | cons a v => exact Nat.succ_pos _
      rcases append_prefix_cases u v v u h with ⟨t,hv,ht⟩ | ⟨t,hu,ht⟩
      · have hl := congrArg List.length hv
        simp only [List.length_append] at hl
        have hlt : u.length+t.length < N := by omega
        obtain ⟨w,m,n,hum,htn⟩ := ih _ hlt u t (hv.symm.trans ht) rfl
        refine ⟨w,m,m+n,hum,?_⟩
        rw [hv,hum,htn,wordPower_add]
      · have hl := congrArg List.length hu
        simp only [List.length_append] at hl
        have hlt : v.length+t.length < N := by omega
        obtain ⟨w,m,n,hvm,htn⟩ := ih _ hlt v t (hu.symm.trans ht) rfl
        refine ⟨w,m+n,m,?_,hvm⟩
        rw [hu,hvm,htn,wordPower_add]

/-- Commuting nonnegative unimodular matrices are powers of one positive generator word. -/
theorem commuting_matrices_common_root (A B : NatMatrix) (hA : Unimodular A)
    (hB : Unimodular B) (h : A*B = B*A) :
    ∃ w : List Bool, ∃ m n : ℕ, A = matrixWord w^m ∧ B = matrixWord w^n := by
  obtain ⟨u,rfl⟩ := exists_matrixWord A hA
  obtain ⟨v,rfl⟩ := exists_matrixWord B hB
  have he : matrixWord (u++v) = matrixWord (v++u) := by
    rw [matrixWord_append,matrixWord_append]
    exact h
  obtain ⟨w,m,n,hu,hv⟩ := commuting_words_common_root u v (matrixWord_injective he)
  refine ⟨w,m,n,?_,?_⟩
  · rw [hu,matrixWord_wordPower]
  · rw [hv,matrixWord_wordPower]

#print axioms commuting_words_common_root
#print axioms commuting_matrices_common_root

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCoding
