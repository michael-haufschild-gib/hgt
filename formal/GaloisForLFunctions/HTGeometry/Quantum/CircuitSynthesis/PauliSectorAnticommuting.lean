import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.AnticommutingPauli
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliSectorRotations

/-!
# Exact evolution with sector-dependent anticommuting coefficients

Each plane elimination uses the same Pauli axis in every joint symmetry
sector. Only its angle changes. Compiling those angles as one controlled
rotation gives a fixed change of basis for the whole Hamiltonian orbit.
-/

open Matrix NormedSpace
open scoped BigOperators Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

open DiagonalSynthesis

noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
private abbrev Word (n : ℕ) := Fin n → Option (Fin 3)

private theorem pairwise_control_words {n : ℕ} (S : List (Word n))
    (h : ∀ P ∈ S, ∀ Q ∈ S, Commute (finitePauliMatrix P) (finitePauliMatrix Q)) :
    S.Pairwise fun P Q => Commute (finitePauliMatrix P) (finitePauliMatrix Q) := by
  induction S with
  | nil => exact .nil
  | cons P S ih =>
    exact List.pairwise_cons.mpr ⟨fun Q hQ => h P (by simp) Q (List.mem_cons_of_mem _ hQ),
      ih (fun Q hQ R hR => h Q (List.mem_cons_of_mem _ hQ) R (List.mem_cons_of_mem _ hR))⟩

/-- One sector-controlled rotation aligns two anticommuting words in
every symmetry sector. It fixes every control-preserving spectator
that commutes with the product of the two words. -/
theorem exists_pauliSector_plane_alignment {n : ℕ} (hn : 2 ≤ n) (S : List (Word n))
    (P Q : Word n) (f g : List Bool → ℝ)
    (hS : ∀ K ∈ S, ∀ L ∈ S, Commute (finitePauliMatrix K) (finitePauliMatrix L))
    (hP : ∀ K ∈ S, Commute (finitePauliMatrix K) (finitePauliMatrix P))
    (hQ : ∀ K ∈ S, Commute (finitePauliMatrix K) (finitePauliMatrix Q))
    (hanti : finitePauliMatrix P * finitePauliMatrix Q = -(finitePauliMatrix Q * finitePauliMatrix P)) :
    ∃ (r : List Bool → ℝ) (C : TwoQubitCircuit n), C.gateCount ≤ 2 ^ S.length * (2 * n + 1) ∧
      (C.eval : Reg n) * (pauliSectorScalar S f * finitePauliMatrix P +
        pauliSectorScalar S g * finitePauliMatrix Q) =
        (pauliSectorScalar S r * finitePauliMatrix P) * (C.eval : Reg n) ∧
      ∀ M : Reg n, (∀ K ∈ S, Commute M (finitePauliMatrix K)) →
        Commute (finitePauliMatrix P * finitePauliMatrix Q) M → Commute (C.eval : Reg n) M := by
  let A := finitePauliMatrix P
  let B := finitePauliMatrix Q
  have halign (s : List Bool) := exists_exp_plane_alignment A B (finitePauliMatrix_mul_self P)
    (finitePauliMatrix_mul_self Q) hanti (f s) (g s)
  choose r θ hr hplane using halign
  let U (s : List Bool) : Reg n := exp ((θ s : ℂ) • (A * B))
  let V := pauliSectorCases S U
  have hSP (K : Word n) (hK : K ∈ S) : Commute (finitePauliMatrix K) (A * B) :=
    (hP K hK).mul_right (hQ K hK)
  have hUC (s : List Bool) (K : Word n) (hK : K ∈ S) : Commute (U s) (finitePauliMatrix K) :=
    ((hSP K hK).symm.smul_left (θ s : ℂ)).exp_left
  have hpair := pairwise_control_words S hS
  obtain ⟨R, c, haxis, haxisComm⟩ := exists_pauli_product_rotation_axis P Q hanti
  let a (s : List Bool) := c * θ s
  have hRC (K : Word n) (hK : K ∈ S) : Commute (finitePauliMatrix K) (finitePauliMatrix R) :=
    haxisComm _ (hSP K hK)
  have hv : V = unitaryEvolution (pauliSectorScalar S a * finitePauliMatrix R) 1 := by
    rw [← pauliSectorCases_real_smul_word]
    rw [unitaryEvolution_pauliSectorCases S _ hpair (fun s K hK => (hRC K hK).symm.smul_left (a s : ℂ))]
    simp only [unitaryEvolution_scale_pauli, mul_one]
    exact congrArg (pauliSectorCases S) (funext fun s => haxis (θ s))
  have hV : Realizes (2 ^ S.length * (2 * n + 1)) V := by
    rw [hv]
    exact pauliSectorRotation_realizes hn S a R 1 hS hRC
  obtain ⟨z, hz, C, hC, hVC⟩ := hV
  have hzne : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact zero_ne_one hz
  have hVint : V * (pauliSectorScalar S f * A + pauliSectorScalar S g * B) =
      (pauliSectorScalar S r * A) * V := by
    calc
      _ = pauliSectorCases S (fun s => U s * ((f s : ℂ) • A + (g s : ℂ) • B)) := by
        rw [pauliSectorCases_mul S U _ hpair hUC, pauliSectorCases_add]
        simp only [A, B, pauliSectorCases_real_smul_word, V]
      _ = pauliSectorCases S (fun s => ((r s : ℂ) • A) * U s) :=
        congrArg (pauliSectorCases S) (funext hplane)
      _ = _ := by
        rw [pauliSectorCases_mul S (fun s => (r s : ℂ) • A) U hpair
          (fun s K hK => (hP K hK).symm.smul_left (r s : ℂ))]
        simp only [A, pauliSectorCases_real_smul_word, V]
  refine ⟨r, C, hC, ?_, ?_⟩
  · rw [hVC, Matrix.smul_mul, Matrix.mul_smul] at hVint
    exact smul_right_injective (Reg n) hzne hVint
  · intro M hMS hAM
    have h := (commute_pauliSectorCases S U M hMS (fun s => ((hAM.smul_left (θ s : ℂ)).exp_left).symm)).symm.eq
    change V * M = M * V at h
    rw [hVC, Matrix.smul_mul, Matrix.mul_smul] at h
    exact smul_right_injective (Reg n) hzne h

/-- A Pauli sum whose coefficients are real functions of the joint
symmetry signs. -/
def pauliSectorCombination {n : ℕ} (S : List (Word n)) (T : Finset (Word n))
    (a : Word n → List Bool → ℝ) : Reg n :=
  ∑ P ∈ T, pauliSectorScalar S (a P) * finitePauliMatrix P

theorem commute_pauliSectorCombination {n : ℕ} (S : List (Word n)) (T : Finset (Word n))
    (a : Word n → List Bool → ℝ) (M : Reg n)
    (hS : ∀ K ∈ S, Commute M (finitePauliMatrix K))
    (hT : ∀ P ∈ T, Commute M (finitePauliMatrix P)) :
    Commute M (pauliSectorCombination S T a) := by
  change M * (∑ P ∈ T, pauliSectorScalar S (a P) * finitePauliMatrix P) =
    (∑ P ∈ T, pauliSectorScalar S (a P) * finitePauliMatrix P) * M
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun P hP =>
    ((commute_pauliSectorScalar S (a P) M hS).mul_right (hT P hP)).eq

/-- Successive controlled plane rotations eliminate every nonpivot
coefficient with one rotation per removed word. -/
theorem exists_pauliSector_anticommuting_alignment {n : ℕ} (hn : 2 ≤ n) (S : List (Word n))
    (P : Word n) (T : Finset (Word n)) (f : List Bool → ℝ) (a : Word n → List Bool → ℝ)
    (hS : ∀ K ∈ S, ∀ L ∈ S, Commute (finitePauliMatrix K) (finitePauliMatrix L))
    (hP : ∀ K ∈ S, Commute (finitePauliMatrix K) (finitePauliMatrix P))
    (hT : ∀ K ∈ S, ∀ Q ∈ T, Commute (finitePauliMatrix K) (finitePauliMatrix Q))
    (hp : ∀ Q ∈ T, finitePauliMatrix P * finitePauliMatrix Q =
      -(finitePauliMatrix Q * finitePauliMatrix P))
    (ha : ∀ Q ∈ T, ∀ R ∈ T, Q ≠ R → finitePauliMatrix Q * finitePauliMatrix R =
      -(finitePauliMatrix R * finitePauliMatrix Q)) :
    ∃ (r : List Bool → ℝ) (C : TwoQubitCircuit n),
      C.gateCount ≤ T.card * (2 ^ S.length * (2 * n + 1)) ∧
      (C.eval : Reg n) * (pauliSectorScalar S f * finitePauliMatrix P + pauliSectorCombination S T a) =
        (pauliSectorScalar S r * finitePauliMatrix P) * (C.eval : Reg n) := by
  classical
  induction T using Finset.induction_on generalizing f with
  | empty =>
    exact ⟨f, TwoQubitCircuit.one n, Nat.zero_le _,
      by simp [TwoQubitCircuit.one_eval, pauliSectorCombination]⟩
  | @insert Q T hQ ih =>
    have hQmem := Finset.mem_insert_self Q T
    obtain ⟨r, U, hU, hplane, hcomm⟩ := exists_pauliSector_plane_alignment hn S P Q f (a Q) hS hP
      (fun K hK => hT K hK Q hQmem) (hp Q hQmem)
    have ht (K : Word n) (hK : K ∈ S) (R : Word n) (hR : R ∈ T) := hT K hK R (Finset.mem_insert_of_mem hR)
    have hp' (R : Word n) (hR : R ∈ T) := hp R (Finset.mem_insert_of_mem hR)
    obtain ⟨r', V, hV, htail⟩ := ih r ht hp' (fun R hR W hW hne =>
      ha R (Finset.mem_insert_of_mem hR) W (Finset.mem_insert_of_mem hW) hne)
    let H := pauliSectorCombination S T a
    have hHC (K : Word n) (hK : K ∈ S) : Commute H (finitePauliMatrix K) :=
      (commute_pauliSectorCombination S T a _ (hS K hK) (ht K hK)).symm
    have hPH : Commute (finitePauliMatrix P * finitePauliMatrix Q) H :=
      commute_pauliSectorCombination S T a _
        (fun K hK => ((hP K hK).mul_right (hT K hK Q hQmem)).symm)
        (fun R hR => commute_product_of_anticommute (hp' R hR)
          (ha Q hQmem R (Finset.mem_insert_of_mem hR) fun he => hQ (he ▸ hR)))
    have hUH := (hcomm H hHC hPH).eq
    have hstep : (U.eval : Reg n) * (pauliSectorScalar S f * finitePauliMatrix P +
        pauliSectorCombination S (insert Q T) a) =
        (pauliSectorScalar S r * finitePauliMatrix P + H) * (U.eval : Reg n) := by
      rw [pauliSectorCombination, Finset.sum_insert hQ, ← add_assoc]
      change (U.eval : Reg n) * ((pauliSectorScalar S f * finitePauliMatrix P +
        pauliSectorScalar S (a Q) * finitePauliMatrix Q) + H) = _
      rw [mul_add, add_mul, hplane, hUH]
    refine ⟨r', V.mul U, ?_, ?_⟩
    · rw [TwoQubitCircuit.mul_gateCount, Finset.card_insert_of_notMem hQ, Nat.add_mul, Nat.one_mul]
      rw [Nat.add_comm U.gateCount V.gateCount]
      exact Nat.add_le_add hV hU
    · rw [TwoQubitCircuit.mul_eval]
      change ((V.eval : Reg n) * (U.eval : Reg n)) * (pauliSectorScalar S f * finitePauliMatrix P +
        pauliSectorCombination S (insert Q T) a) =
        (pauliSectorScalar S r' * finitePauliMatrix P) * ((V.eval : Reg n) * (U.eval : Reg n))
      rw [mul_assoc, hstep, ← mul_assoc _ (pauliSectorScalar S r * finitePauliMatrix P + H), htail, mul_assoc]

/-- Every time on the sector-dependent anticommuting orbit has an exact
projective circuit. The change of basis can be fixed for the whole orbit. -/
theorem pauliSectorAnticommutingSum_realizes {n : ℕ} (hn : 2 ≤ n) (S : List (Word n))
    (T : Finset (Word n)) (a : Word n → List Bool → ℝ)
    (hS : ∀ K ∈ S, ∀ L ∈ S, Commute (finitePauliMatrix K) (finitePauliMatrix L))
    (hT : ∀ K ∈ S, ∀ Q ∈ T, Commute (finitePauliMatrix K) (finitePauliMatrix Q))
    (ha : ∀ P ∈ T, ∀ Q ∈ T, P ≠ Q → finitePauliMatrix P * finitePauliMatrix Q =
      -(finitePauliMatrix Q * finitePauliMatrix P)) (t : ℝ) :
    Realizes ((2 * T.card - 1) * (2 ^ S.length * (2 * n + 1)))
      (unitaryEvolution (pauliSectorCombination S T a) t) := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨P, hP⟩
  · simpa [unitaryEvolution, pauliSectorCombination] using Realizes.one n
  let B := 2 ^ S.length * (2 * n + 1)
  let H := pauliSectorCombination S T a
  have hH : H = pauliSectorScalar S (a P) * finitePauliMatrix P + pauliSectorCombination S (T.erase P) a :=
    (Finset.add_sum_erase T (fun Q => pauliSectorScalar S (a Q) * finitePauliMatrix Q) hP).symm
  have hPC (K : Word n) (hK : K ∈ S) := hT K hK P hP
  obtain ⟨r, C, hC, hA⟩ := exists_pauliSector_anticommuting_alignment hn S P (T.erase P) (a P) a hS hPC
    (fun K hK Q hQ => hT K hK Q (Finset.mem_of_mem_erase hQ))
    (fun Q hQ => ha P hP Q (Finset.mem_of_mem_erase hQ) (Finset.ne_of_mem_erase hQ).symm)
    (fun Q hQ R hR hne => ha Q (Finset.mem_of_mem_erase hQ) R (Finset.mem_of_mem_erase hR) hne)
  let V : Reg n := C.eval
  let D := pauliSectorScalar S r * finitePauliMatrix P
  have hV : V ∈ unitary (Reg n) := C.eval.2
  have hconj : V * H * star V = D := by
    rw [hH]
    change (((C.eval : Reg n) * _) * star V) = _
    rw [hA, mul_assoc, (Unitary.mem_iff.mp hV).2, mul_one]
  have hvR : Realizes ((T.erase P).card * B) V := ⟨1, norm_one, C, hC, by simp [V]⟩
  have hdR : Realizes B (unitaryEvolution D t) := pauliSectorRotation_realizes hn S r P t hS hPC
  have he := unitaryEvolution_conj V H (Unitary.isUnit_coe (U := C.eval)) t
  rw [inv_eq_star_of_mem_unitary hV, hconj] at he
  have hcancel (X : Reg n) : star V * (V * X * star V) * V = X := by
    calc
      _ = (star V * V) * X * (star V * V) := by simp only [mul_assoc]
      _ = _ := by simp only [(Unitary.mem_iff.mp hV).1, one_mul, mul_one]
  have hrepr : unitaryEvolution H t = star V * (unitaryEvolution D t * V) := by
    have hh := congrArg (fun X : Reg n => star V * X * V) he.symm
    change star V * (V * unitaryEvolution H t * star V) * V = star V * unitaryEvolution D t * V at hh
    rw [hcancel, mul_assoc] at hh
    exact hh
  have hcount : 2 * (T.erase P).card + 1 = 2 * T.card - 1 := by
    have hpos := Finset.card_pos.mpr (show T.Nonempty from ⟨P, hP⟩)
    rw [Finset.card_erase_of_mem hP]
    omega
  have hbudget : (T.erase P).card * B + (B + (T.erase P).card * B) = (2 * T.card - 1) * B := by
    rw [← hcount]
    ring
  have hR := hvR.adjoint.mul (hdR.mul hvR)
  rw [hbudget, ← hrepr] at hR
  exact hR

/-- An arbitrary central phase can be included alongside anticommuting
terms with sector-dependent coefficients. -/
theorem pauliSectorAnticommuting_realizes {n : ℕ} (hn : 2 ≤ n) (S : List (Word n))
    (T : Finset (Word n)) (a : Word n → List Bool → ℝ) (center : List Bool → ℝ)
    (hS : ∀ K ∈ S, ∀ L ∈ S, Commute (finitePauliMatrix K) (finitePauliMatrix L))
    (hT : ∀ K ∈ S, ∀ Q ∈ T, Commute (finitePauliMatrix K) (finitePauliMatrix Q))
    (ha : ∀ P ∈ T, ∀ Q ∈ T, P ≠ Q → finitePauliMatrix P * finitePauliMatrix Q =
      -(finitePauliMatrix Q * finitePauliMatrix P)) (t : ℝ) :
    Realizes ((2 * T.card - 1 + 1) * (2 ^ S.length * (2 * n + 1)))
      (unitaryEvolution (pauliSectorCombination S T a + pauliSectorScalar S center) t) := by
  have hc : Commute (pauliSectorCombination S T a) (pauliSectorScalar S center) :=
    commute_pauliSectorScalar S center _ fun K hK =>
      (commute_pauliSectorCombination S T a _ (hS K hK) (hT K hK)).symm
  rw [unitaryEvolution_add_of_commuting hc, Nat.add_mul, Nat.one_mul]
  exact (pauliSectorAnticommutingSum_realizes hn S T a hS hT ha t).mul
    (pauliSectorPhase_realizes hn S center hS t)

/-- The sector-dependent anticommuting model has a time-independent
zero-error gate cap quadratic in register size and exponential only in
the number of listed symmetries. -/
theorem pauliSectorAnticommuting_uniform_gate_cap {n : ℕ} (hn : 2 ≤ n) (S : List (Word n))
    (T : Finset (Word n)) (a : Word n → List Bool → ℝ) (center : List Bool → ℝ)
    (hS : ∀ K ∈ S, ∀ L ∈ S, Commute (finitePauliMatrix K) (finitePauliMatrix L))
    (hT : ∀ K ∈ S, ∀ Q ∈ T, Commute (finitePauliMatrix K) (finitePauliMatrix Q))
    (ha : ∀ P ∈ T, ∀ Q ∈ T, P ≠ Q → finitePauliMatrix P * finitePauliMatrix Q =
      -(finitePauliMatrix Q * finitePauliMatrix P)) (t : ℝ) :
    HasProjectiveCircuitApproximation n 0 ((4 * n + 2) * (2 ^ S.length * (2 * n + 1)))
      (unitaryEvolution (pauliSectorCombination S T a + pauliSectorScalar S center) t) := by
  obtain ⟨z, hz, C, hC, he⟩ := pauliSectorAnticommuting_realizes hn S T a center hS hT ha t
  have hcard := card_anticommuting_finitePauliMatrix_le T ha
  refine ⟨z, hz, C, hC.trans (Nat.mul_le_mul_right _ (by omega)), ?_⟩
  rw [he, sub_self, norm_zero]

#print axioms exists_pauliSector_plane_alignment
#print axioms commute_pauliSectorCombination
#print axioms exists_pauliSector_anticommuting_alignment
#print axioms pauliSectorAnticommutingSum_realizes
#print axioms pauliSectorAnticommuting_realizes
#print axioms pauliSectorAnticommuting_uniform_gate_cap

end

end GaloisForLFunctions.HTGeometry
