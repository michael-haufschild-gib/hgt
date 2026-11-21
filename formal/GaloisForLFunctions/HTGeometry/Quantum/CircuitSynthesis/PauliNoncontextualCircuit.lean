import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliSectorAnticommuting
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliContextuality

/-!
# Exact circuits from noncontextual Pauli support

Commutation partitions the noncentral support into classes. Multiplying
a term by its class representative yields a central Pauli word up to
sign. Its eigenvalue becomes a coefficient in the sector Hamiltonian.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

open DiagonalSynthesis

noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
private abbrev Word (n : ℕ) := Fin n → Option (Fin 3)

/-- Noncontextuality is equivalent to commutation classes being exactly
the classes of equal noncommuting neighborhoods on the noncentral support. -/
theorem pauliNoncontextual_iff_commuting_twins {ι R : Type*} [Mul R] (A : ι → R) :
    PauliNoncontextual A ↔ ∀ i j, PauliNoncentral A i → PauliNoncentral A j →
      (Commute (A i) (A j) ↔ ∀ x, (¬ Commute (A i) (A x)) ↔ ¬ Commute (A j) (A x)) := by
  classical
  constructor
  · intro h i j hi hj
    constructor
    · intro hij x
      constructor
      · intro hix hjx
        have hx : PauliNoncentral A x := ⟨i, fun hxi => hix hxi.symm⟩
        exact hix (h j i x hj hi hx hij.symm hjx)
      · intro hjx hix
        have hx : PauliNoncentral A x := ⟨j, fun hxj => hjx hxj.symm⟩
        exact hjx (h i j x hi hj hx hij hix)
    · intro hsame
      by_contra hij
      exact (hsame j).mp hij (Commute.refl _)
  · intro h i j k hi hj _ hij hik
    by_contra hjk
    exact (((h i j hi hj).mp hij) k).mpr hjk hik

private theorem pauli_identity_matrix (n : ℕ) : finitePauliMatrix (pauliIdentityLabel n) = (1 : Reg n) := by
  ext x y
  exact finitePauliMatrix_pauliIdentityLabel x y

/-- Distinct commutation behavior of Pauli words gives exact anticommutation. -/
theorem finitePauliMatrix_anticommute_of_not_commute {n : ℕ} (P Q : Word n)
    (h : ¬ Commute (finitePauliMatrix P) (finitePauliMatrix Q)) :
    finitePauliMatrix P * finitePauliMatrix Q = -(finitePauliMatrix Q * finitePauliMatrix P) := by
  let c := finitePauliConjugationSign P Q
  have hc : c * c = 1 := finitePauliConjugationSign_sq P Q
  have hz : (c - 1) * (c + 1) = 0 := calc
    _ = c * c - 1 := by ring
    _ = 0 := by rw [hc, sub_self]
  have he : c = -1 := eq_neg_of_add_eq_zero_left <| (mul_eq_zero.mp hz).resolve_left fun h₁ =>
    h ((finitePauli_commute_iff_sign P Q).mpr (sub_eq_zero.mp h₁))
  have hi := congrArg (fun M : Reg n => M * finitePauliMatrix P) (finitePauliMatrix_conj P Q)
  change finitePauliMatrix P * finitePauliMatrix Q * finitePauliMatrix P * finitePauliMatrix P =
    (c • finitePauliMatrix Q) * finitePauliMatrix P at hi
  rwa [mul_assoc _ (finitePauliMatrix P) (finitePauliMatrix P), finitePauliMatrix_mul_self,
    mul_one, he, neg_one_smul, neg_mul] at hi

private theorem pauliControlProjection_sub {n : ℕ} (P : Word n) :
    pauliControlProjection P false - pauliControlProjection P true = finitePauliMatrix P := by
  have h : (1 : Reg n) + finitePauliMatrix P - (1 - finitePauliMatrix P) =
      (2 : ℂ) • finitePauliMatrix P := by rw [two_smul]; abel
  simp only [pauliControlProjection]
  rw [← smul_sub, h, smul_smul]
  norm_num

private theorem pauliSectorScalar_const {n : ℕ} (S : List (Word n)) (r : ℝ) :
    pauliSectorScalar S (fun _ => r) = (r : ℂ) • (1 : Reg n) :=
  pauliSectorCases_const S _

private theorem pauliSectorScalar_zero {n : ℕ} (S : List (Word n)) :
    pauliSectorScalar S (fun _ => 0) = 0 := by
  rw [pauliSectorScalar_const, Complex.ofReal_zero, zero_smul]

private theorem pauliSectorScalar_add {n : ℕ} (S : List (Word n)) (f g : List Bool → ℝ) :
    pauliSectorScalar S (fun s => f s + g s) = pauliSectorScalar S f + pauliSectorScalar S g := by
  simpa only [pauliSectorScalar, Complex.ofReal_add, add_smul] using
    pauliSectorCases_add S (fun s => (f s : ℂ) • (1 : Reg n)) (fun s => (g s : ℂ) • (1 : Reg n))

private theorem pauliSectorScalar_mul_const {n : ℕ} (S : List (Word n)) (r : ℝ) (f : List Bool → ℝ) :
    pauliSectorScalar S (fun s => r * f s) = (r : ℂ) • pauliSectorScalar S f := by
  simpa only [pauliSectorScalar, Complex.ofReal_mul, smul_smul] using
    pauliSectorCases_smul S (r : ℂ) (fun s => (f s : ℂ) • (1 : Reg n))

/-- Each listed control word is recovered by its sign function on the
sectors. This holds even when some sign combinations are impossible. -/
theorem exists_pauliSectorScalar_eq_control {n : ℕ} (S : List (Word n)) {P : Word n} (hP : P ∈ S) :
    ∃ f : List Bool → ℝ, pauliSectorScalar S f = finitePauliMatrix P := by
  induction S with
  | nil => simp at hP
  | cons Q S ih =>
    rcases List.mem_cons.mp hP with he | hP
    · subst Q
      refine ⟨fun s => if s.headD false then -1 else 1, ?_⟩
      change pauliControlProjection P false * pauliSectorScalar S (fun _ => 1) +
        pauliControlProjection P true * pauliSectorScalar S (fun _ => -1) = finitePauliMatrix P
      simp only [pauliSectorScalar_const, Complex.ofReal_neg, Complex.ofReal_one, one_smul, neg_one_smul,
        mul_one, mul_neg, ← sub_eq_add_neg, pauliControlProjection_sub]
    · obtain ⟨f, hf⟩ := ih hP
      refine ⟨fun s => f s.tail, ?_⟩
      change pauliControlProjection Q false * pauliSectorScalar S f +
        pauliControlProjection Q true * pauliSectorScalar S f = finitePauliMatrix P
      rw [← add_mul, pauliControlProjection_add, one_mul, hf]

private def pivotMatrix {n : ℕ} : Option (Word n) → Reg n
  | none => 1
  | some P => finitePauliMatrix P

private theorem pauliSectorCombination_add {n : ℕ} (S : List (Word n)) (R : Finset (Word n))
    (f g : Word n → List Bool → ℝ) :
    pauliSectorCombination S R (fun P s => f P s + g P s) =
      pauliSectorCombination S R f + pauliSectorCombination S R g := by
  simp only [pauliSectorCombination, pauliSectorScalar_add, add_mul, Finset.sum_add_distrib]

private theorem pauliSectorForm_sum {n : ℕ} {ι : Type*} (S : List (Word n)) (R : Finset (Word n))
    (T : Finset ι) (F : ι → Reg n)
    (h : ∀ x ∈ T, ∃ f c, F x = pauliSectorCombination S R f + pauliSectorScalar S c) :
    ∃ f c, (∑ x ∈ T, F x) = pauliSectorCombination S R f + pauliSectorScalar S c := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨fun _ _ => 0, fun _ => 0, by simp [pauliSectorCombination, pauliSectorScalar_zero]⟩
  | @insert x T hx ih =>
    obtain ⟨f, c, hf⟩ := h x (Finset.mem_insert_self _ _)
    obtain ⟨g, d, hg⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
    refine ⟨fun P s => f P s + g P s, fun s => c s + d s, ?_⟩
    rw [Finset.sum_insert hx, hf, hg, pauliSectorCombination_add, pauliSectorScalar_add]
    abel

private theorem pauliSectorForm_single {n : ℕ} (S : List (Word n)) (R : Finset (Word n))
    (q : Option (Word n)) (g : List Bool → ℝ) (hq : ∀ P, q = some P → P ∈ R) :
    ∃ f c, pauliSectorScalar S g * pivotMatrix q = pauliSectorCombination S R f + pauliSectorScalar S c := by
  classical
  cases q with
  | none =>
    exact ⟨fun _ _ => 0, g, by simp [pivotMatrix, pauliSectorCombination, pauliSectorScalar_zero]⟩
  | some P =>
    refine ⟨fun Q s => if Q = P then g s else 0, fun _ => 0, ?_⟩
    rw [pivotMatrix, pauliSectorScalar_zero, add_zero, pauliSectorCombination,
      Finset.sum_eq_single_of_mem P (hq P rfl)]
    · simp only [if_true]
    · intro Q _ hQ
      simp only [if_neg hQ, pauliSectorScalar_zero, zero_mul]

/-- A commuting pair determines a signed dressing word, with the same
commutant as the product of the pair. -/
theorem exists_pauli_commuting_dressing {n : ℕ} (P Q : Word n)
    (h : Commute (finitePauliMatrix P) (finitePauliMatrix Q)) :
    ∃ (D : Word n) (ε : ℝ), finitePauliMatrix P = ((ε : ℂ) • finitePauliMatrix D) * finitePauliMatrix Q ∧
      ∀ M : Reg n, Commute M (finitePauliMatrix D) ↔ Commute M (finitePauliMatrix P * finitePauliMatrix Q) := by
  obtain ⟨D, hD | hD⟩ := exists_signed_pauli_product_of_commute P Q h
  · refine ⟨D, 1, ?_, fun M => by rw [hD]⟩
    have he := congrArg (fun X : Reg n => X * finitePauliMatrix Q) hD
    change (finitePauliMatrix P * finitePauliMatrix Q) * finitePauliMatrix Q = _ at he
    rw [mul_assoc, finitePauliMatrix_mul_self, mul_one] at he
    simpa only [Complex.ofReal_one, one_smul] using he
  · refine ⟨D, -1, ?_, fun M => ?_⟩
    · have he := congrArg (fun X : Reg n => X * finitePauliMatrix Q) hD
      change (finitePauliMatrix P * finitePauliMatrix Q) * finitePauliMatrix Q = _ at he
      rw [mul_assoc, finitePauliMatrix_mul_self, mul_one] at he
      simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul] using he
    · rw [hD]
      exact ⟨fun hc => hc.neg_right, fun hc => by simpa only [neg_neg] using hc.neg_right⟩

/-- Noncontextual commutation of the original support yields commuting
controls and anticommuting representatives. Both lists are fixed before
choosing coefficients. There is at most one control per removed word. -/
theorem exists_pauliNoncontextual_sector_form {n : ℕ} (T : Finset (Word n))
    (hnc : PauliNoncontextual (fun P : {P // P ∈ T} => finitePauliMatrix P.1)) :
    ∃ (S : List (Word n)) (R : Finset (Word n)), S.length + R.card ≤ T.card ∧ R ⊆ T ∧
      (∀ K ∈ S, ∀ L ∈ S, Commute (finitePauliMatrix K) (finitePauliMatrix L)) ∧
      (∀ K ∈ S, ∀ Q ∈ R, Commute (finitePauliMatrix K) (finitePauliMatrix Q)) ∧
      (∀ P ∈ R, ∀ Q ∈ R, P ≠ Q → finitePauliMatrix P * finitePauliMatrix Q =
        -(finitePauliMatrix Q * finitePauliMatrix P)) ∧
      ∀ a : Word n → ℝ, ∃ f c, (∑ P ∈ T, (a P : ℂ) • finitePauliMatrix P) =
        pauliSectorCombination S R f + pauliSectorScalar S c := by
  classical
  let I := {P // P ∈ T}
  let A (i : I) := finitePauliMatrix i.1
  let J := {i : I // PauliNoncentral A i}
  let s : Setoid J := ⟨fun i j => Commute (A i.1) (A j.1),
    ⟨fun i => Commute.refl _, fun h => h.symm,
      fun {i j k} hi hj => hnc j.1 i.1 k.1 j.2 i.2 k.2 hi.symm hj⟩⟩
  let r (x : J) : J := Quotient.out (Quotient.mk s x)
  have hr (x : J) : Commute (A (r x).1) (A x.1) := by
    change s.r (r x) x
    exact Quotient.exact (Quotient.out_eq (Quotient.mk s x))
  let R : Finset (Word n) := Finset.univ.image fun x : J => (r x).1.1
  have hrR (x : J) : (r x).1.1 ∈ R := Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hRT : R ⊆ T := by
    intro P hP
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hP
    exact (r x).1.2
  have hAnti : ∀ P ∈ R, ∀ Q ∈ R, P ≠ Q → finitePauliMatrix P * finitePauliMatrix Q =
      -(finitePauliMatrix Q * finitePauliMatrix P) := by
    intro P hP Q hQ hne
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hQ
    refine finitePauliMatrix_anticommute_of_not_commute _ _ ?_
    intro hc
    have hh : s.r (r x) (r y) := hc
    have he : Quotient.mk s (r x) = Quotient.mk s (r y) := Quotient.sound hh
    have hxy : Quotient.mk s x = Quotient.mk s y := by simpa only [r, Quotient.out_eq] using he
    exact hne (congrArg (fun q : Quotient s => q.out.1.1) hxy)
  have hdress (i : I) : ∃ (D : Word n) (q : Option (Word n)) (ε : ℝ),
      (∀ j : I, Commute (finitePauliMatrix D) (A j)) ∧
      (∀ M : Reg n, (∀ j : I, Commute M (A j)) → Commute M (finitePauliMatrix D)) ∧
      (∀ P, q = some P → P ∈ R) ∧
      (i.1 ∈ R → D = pauliIdentityLabel n) ∧
      A i = ((ε : ℂ) • finitePauliMatrix D) * pivotMatrix q := by
    by_cases hiR : i.1 ∈ R
    · refine ⟨pauliIdentityLabel n, some i.1, 1, ?_, ?_, ?_, fun _ => rfl, ?_⟩
      · intro j
        rw [pauli_identity_matrix]
        exact (Commute.one_right _).symm
      · intro M _
        rw [pauli_identity_matrix]
        exact Commute.one_right _
      · intro P hP
        simpa only [Option.some.inj hP] using hiR
      · simp only [A, pivotMatrix, pauli_identity_matrix, Complex.ofReal_one, one_smul, one_mul]
    · by_cases hi : PauliNoncentral A i
      · let x : J := ⟨i, hi⟩
        let p := (r x).1
        have hpi : Commute (A p) (A i) := hr x
        have hp : PauliNoncentral A p := (r x).2
        have htwins := ((pauliNoncontextual_iff_commuting_twins A).mp hnc i p hi hp).mp hpi.symm
        have hcentral (j : I) : Commute (A i * A p) (A j) := by
          by_cases hij : Commute (A i) (A j)
          · have hpj : Commute (A p) (A j) := by
              by_contra h
              exact (htwins j).mpr h hij
            exact hij.mul_left hpj
          · exact commute_product_of_anticommute (finitePauliMatrix_anticommute_of_not_commute _ _ hij)
              (finitePauliMatrix_anticommute_of_not_commute _ _ ((htwins j).mp hij))
        obtain ⟨D, ε, he, hc⟩ := exists_pauli_commuting_dressing i.1 p.1 hpi.symm
        refine ⟨D, some p.1, ε, fun j => ((hc (A j)).mpr (hcentral j).symm).symm,
          fun M hM => (hc M).mpr ((hM i).mul_right (hM p)), ?_, fun h => (hiR h).elim, he⟩
        intro P hP
        have hpR : p.1 ∈ R := hrR x
        exact Option.some.inj hP ▸ hpR
      · refine ⟨i.1, none, 1, ?_, fun M hM => hM i, ?_, fun h => (hiR h).elim, ?_⟩
        · intro j
          by_contra he
          exact hi ⟨j, he⟩
        · intro P hP
          cases hP
        · simp only [A, pivotMatrix, Complex.ofReal_one, one_smul, mul_one]
  choose d q ε hc hg hq hid he using hdress
  let dWord (P : Word n) := if hP : P ∈ T then d ⟨P, hP⟩ else pauliIdentityLabel n
  let K := (T \ R).image dWord
  let S := K.toList
  have hcover (D : Word n) (hD : D ∈ S) : ∃ i : I, d i = D := by
    obtain ⟨P, hP, hD⟩ := Finset.mem_image.mp (Finset.mem_toList.mp hD)
    have hPT := (Finset.mem_sdiff.mp hP).1
    exact ⟨⟨P, hPT⟩, by simpa only [dWord, dif_pos hPT] using hD⟩
  have hK : ∀ D ∈ S, ∀ E ∈ S, Commute (finitePauliMatrix D) (finitePauliMatrix E) := by
    intro D hD E hE
    obtain ⟨i, rfl⟩ := hcover D hD
    obtain ⟨j, rfl⟩ := hcover E hE
    exact hg j _ (hc i)
  have hKR : ∀ D ∈ S, ∀ P ∈ R, Commute (finitePauliMatrix D) (finitePauliMatrix P) := by
    intro D hD P hP
    obtain ⟨i, rfl⟩ := hcover D hD
    exact hc i ⟨P, hRT hP⟩
  have hcount : S.length + R.card ≤ T.card := by
    change K.toList.length + R.card ≤ T.card
    rw [Finset.length_toList]
    exact (Nat.add_le_add_right Finset.card_image_le _).trans_eq (Finset.card_sdiff_add_card_eq_card hRT)
  have hdScalar (i : I) : ∃ f, pauliSectorScalar S f = finitePauliMatrix (d i) := by
    by_cases hi : i.1 ∈ R
    · exact ⟨fun _ => 1, by rw [hid i hi, pauli_identity_matrix, pauliSectorScalar_const,
        Complex.ofReal_one, one_smul]⟩
    · apply exists_pauliSectorScalar_eq_control S
      apply Finset.mem_toList.mpr
      exact Finset.mem_image.mpr ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, hi⟩, dif_pos i.2⟩
  choose φ hφ using hdScalar
  refine ⟨S, R, hcount, hRT, hK, hKR, hAnti, fun a => ?_⟩
  apply pauliSectorForm_sum S R T
  intro P hP
  let i : I := ⟨P, hP⟩
  have hterm : (a P : ℂ) • finitePauliMatrix P =
      pauliSectorScalar S (fun b => (a P * ε i) * φ i b) * pivotMatrix (q i) := by
    change (a P : ℂ) • A i = _
    rw [he i, pauliSectorScalar_mul_const, hφ i]
    simp only [Complex.ofReal_mul, Matrix.smul_mul, smul_smul]
  rw [hterm]
  exact pauliSectorForm_single S R (q i) _ (hq i)

/-- A fixed noncontextual support has one gate budget for all coefficients
and all times. The representative count and control count are charged
against disjoint parts of the original support. -/
theorem exists_pauliNoncontextual_gate_cap {n : ℕ} (hn : 2 ≤ n) (T : Finset (Word n))
    (hnc : PauliNoncontextual (fun P : {P // P ∈ T} => finitePauliMatrix P.1)) :
    ∃ k m : ℕ, k + m ≤ T.card ∧ m ≤ 2 * n + 1 ∧
      ∀ (a : Word n → ℝ) (t : ℝ), Realizes ((2 * m - 1 + 1) * (2 ^ k * (2 * n + 1)))
        (unitaryEvolution (∑ P ∈ T, (a P : ℂ) • finitePauliMatrix P) t) := by
  obtain ⟨S, R, hcount, _, hS, hR, ha, hform⟩ := exists_pauliNoncontextual_sector_form T hnc
  refine ⟨S.length, R.card, hcount, card_anticommuting_finitePauliMatrix_le R ha, fun a t => ?_⟩
  obtain ⟨f, c, hf⟩ := hform a
  rw [hf]
  exact pauliSectorAnticommuting_realizes hn S R f c hS hR ha t

private theorem twice_le_two_pow (m : ℕ) : 2 * m ≤ 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    by_cases hm : m = 0
    · subst m
      norm_num
    · rw [pow_succ]
      omega

/-- Noncontextual Pauli support gives an exact, time-independent cap
depending only on the support size and the register size. -/
theorem pauliNoncontextual_uniform_gate_cap {n : ℕ} (hn : 2 ≤ n) (T : Finset (Word n))
    (hnc : PauliNoncontextual (fun P : {P // P ∈ T} => finitePauliMatrix P.1))
    (a : Word n → ℝ) (t : ℝ) :
    HasProjectiveCircuitApproximation n 0 (2 ^ T.card * (2 * n + 1))
      (unitaryEvolution (∑ P ∈ T, (a P : ℂ) • finitePauliMatrix P) t) := by
  obtain ⟨k, m, hcount, _, h⟩ := exists_pauliNoncontextual_gate_cap hn T hnc
  have hb : 2 * m - 1 + 1 ≤ 2 ^ m := by
    by_cases hm : m = 0
    · simp [hm]
    · have h := twice_le_two_pow m
      omega
  have hcap : (2 * m - 1 + 1) * (2 ^ k * (2 * n + 1)) ≤ 2 ^ T.card * (2 * n + 1) := calc
    _ ≤ 2 ^ m * (2 ^ k * (2 * n + 1)) := Nat.mul_le_mul_right _ hb
    _ = 2 ^ (m + k) * (2 * n + 1) := by rw [pow_add, mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
  obtain ⟨z, hz, C, hc, he⟩ := h a t
  exact ⟨z, hz, C, hc.trans hcap, by rw [he, sub_self, norm_zero]⟩

#print axioms pauliNoncontextual_iff_commuting_twins
#print axioms finitePauliMatrix_anticommute_of_not_commute
#print axioms exists_pauliSectorScalar_eq_control
#print axioms exists_pauli_commuting_dressing
#print axioms exists_pauliNoncontextual_sector_form
#print axioms exists_pauliNoncontextual_gate_cap
#print axioms pauliNoncontextual_uniform_gate_cap

end

end GaloisForLFunctions.HTGeometry
