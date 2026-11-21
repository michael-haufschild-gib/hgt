import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.PhaseCircuit
import GaloisForLFunctions.HTGeometry.PauliProductLaw

/-!
# Rotations controlled by commuting Pauli symmetries

The two projectors of each symmetry select the operator assigned to
its eigenvalue. Splitting the selected angles into their average and
half-difference gives an exact circuit with one Pauli rotation per
binary character of the control list.
-/

open Matrix NormedSpace
open scoped BigOperators Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
private abbrev Word (n : ℕ) := Fin n → Option (Fin 3)

/-- The false branch selects eigenvalue `+1` and the true branch selects `-1`. -/
def pauliControlProjection {n : ℕ} (P : Word n) : Bool → Reg n
  | false => (1 / 2 : ℂ) • (1 + finitePauliMatrix P)
  | true => (1 / 2 : ℂ) • (1 - finitePauliMatrix P)

theorem pauliControlProjection_add {n : ℕ} (P : Word n) :
    pauliControlProjection P false + pauliControlProjection P true = 1 := by
  have h : (1 : Reg n) + finitePauliMatrix P + (1 - finitePauliMatrix P) = (2 : ℂ) • (1 : Reg n) := by
    rw [two_smul]
    abel
  rw [pauliControlProjection, pauliControlProjection, ← smul_add, h, smul_smul]
  norm_num

/-- The two projectors of a Pauli symmetry are idempotent and orthogonal. -/
theorem pauliControlProjection_mul {n : ℕ} (P : Word n) (b c : Bool) :
    pauliControlProjection P b * pauliControlProjection P c = if b = c then pauliControlProjection P b else 0 := by
  let A := finitePauliMatrix P
  have hA : A * A = 1 := finitePauliMatrix_mul_self P
  have hpp : (1 + A) * (1 + A) = (2 : ℂ) • (1 + A) := by
    simp only [add_mul, mul_add, one_mul, mul_one, hA, two_smul]
    abel
  have hpm : (1 + A) * (1 - A) = 0 := by
    simp only [add_mul, mul_sub, one_mul, mul_one, hA]
    abel
  have hmp : (1 - A) * (1 + A) = 0 := by
    simp only [sub_mul, mul_add, one_mul, mul_one, hA]
    abel
  have hmm : (1 - A) * (1 - A) = (2 : ℂ) • (1 - A) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hA, two_smul]
    abel
  cases b <;> cases c <;>
    simp only [pauliControlProjection, ← show A = finitePauliMatrix P from rfl,
      smul_mul_smul_comm, hpp, hpm, hmp, hmm, smul_smul]
  all_goals norm_num

private theorem pauliControlProjection_self {n : ℕ} (P : Word n) (b : Bool) :
    pauliControlProjection P b * pauliControlProjection P b = pauliControlProjection P b := by
  rw [pauliControlProjection_mul, if_pos rfl]

private theorem pauliControlProjection_cross {n : ℕ} (P : Word n) {b c : Bool} (h : b ≠ c) :
    pauliControlProjection P b * pauliControlProjection P c = 0 := by
  rw [pauliControlProjection_mul, if_neg h]

/-- Assemble a family of operators by the simultaneous signs of a
list of Pauli symmetries. The list can contain dependent symmetries. -/
def pauliSectorCases {n : ℕ} : List (Word n) → (List Bool → Reg n) → Reg n
  | [], f => f []
  | P :: S, f =>
      pauliControlProjection P false * pauliSectorCases S (fun s => f (false :: s)) +
      pauliControlProjection P true * pauliSectorCases S (fun s => f (true :: s))

theorem pauliSectorCases_const {n : ℕ} (S : List (Word n)) (A : Reg n) :
    pauliSectorCases S (fun _ => A) = A := by
  induction S with
  | nil => rfl
  | cons P S ih =>
    simp only [pauliSectorCases, ih]
    rw [← add_mul, pauliControlProjection_add, one_mul]

theorem pauliSectorCases_add {n : ℕ} (S : List (Word n)) (f g : List Bool → Reg n) :
    pauliSectorCases S (fun s => f s + g s) = pauliSectorCases S f + pauliSectorCases S g := by
  induction S generalizing f g with
  | nil => rfl
  | cons P S ih =>
    simp only [pauliSectorCases, ih, mul_add]
    abel

theorem pauliSectorCases_smul {n : ℕ} (S : List (Word n)) (c : ℂ) (f : List Bool → Reg n) :
    pauliSectorCases S (fun s => c • f s) = c • pauliSectorCases S f := by
  induction S generalizing f with
  | nil => rfl
  | cons P S ih =>
    simp only [pauliSectorCases, ih, Matrix.mul_smul, smul_add]

theorem pauliSectorCases_mul_const {n : ℕ} (S : List (Word n)) (f : List Bool → Reg n) (M : Reg n) :
    pauliSectorCases S (fun s => f s * M) = pauliSectorCases S f * M := by
  induction S generalizing f with
  | nil => rfl
  | cons P S ih =>
    simp only [pauliSectorCases, ih, add_mul, mul_assoc]

private theorem commute_pauliControlProjection {n : ℕ} {P : Word n} {M : Reg n}
    (h : Commute M (finitePauliMatrix P)) (b : Bool) : Commute M (pauliControlProjection P b) := by
  cases b
  · exact ((Commute.one_right M).add_right h).smul_right (1 / 2 : ℂ)
  · exact ((Commute.one_right M).sub_right h).smul_right (1 / 2 : ℂ)

theorem commute_pauliSectorCases {n : ℕ} (S : List (Word n)) (f : List Bool → Reg n) (M : Reg n)
    (hS : ∀ P ∈ S, Commute M (finitePauliMatrix P)) (hf : ∀ s, Commute M (f s)) :
    Commute M (pauliSectorCases S f) := by
  induction S generalizing f with
  | nil => exact hf []
  | cons P S ih =>
    have hp := hS P (List.mem_cons_self ..)
    have hs (Q) (hQ : Q ∈ S) := hS Q (List.mem_cons_of_mem _ hQ)
    apply Commute.add_right
    · exact (commute_pauliControlProjection hp false).mul_right (ih _ hs fun s => hf (false :: s))
    · exact (commute_pauliControlProjection hp true).mul_right (ih _ hs fun s => hf (true :: s))

private theorem sector_block_reorder {n : ℕ} (P Q A B : Reg n) (h : Commute A Q) :
    P * A * (Q * B) = (P * Q) * (A * B) := by
  calc
    _ = P * (A * Q) * B := by simp only [mul_assoc]
    _ = _ := by rw [h.eq]; simp only [mul_assoc]

/-- Products of sectorwise operators are computed sector by sector
when the first family's operators preserve every control. -/
theorem pauliSectorCases_mul {n : ℕ} (S : List (Word n)) (f g : List Bool → Reg n)
    (hS : S.Pairwise fun P Q => Commute (finitePauliMatrix P) (finitePauliMatrix Q))
    (hf : ∀ s P, P ∈ S → Commute (f s) (finitePauliMatrix P)) :
    pauliSectorCases S (fun s => f s * g s) = pauliSectorCases S f * pauliSectorCases S g := by
  induction S generalizing f g with
  | nil => rfl
  | cons P S ih =>
    obtain ⟨hP, htail⟩ := List.pairwise_cons.mp hS
    have hcomm (b c : Bool) :
        Commute (pauliSectorCases S fun s => f (b :: s)) (pauliControlProjection P c) :=
      (commute_pauliSectorCases S _ _
        (fun Q hQ => (commute_pauliControlProjection (hP Q hQ).symm c).symm)
        (fun s => (commute_pauliControlProjection (hf (b :: s) P (List.mem_cons_self ..)) c).symm)).symm
    have hh (b : Bool) := ih (fun s => f (b :: s)) (fun s => g (b :: s)) htail
      (fun s Q hQ => hf (b :: s) Q (List.mem_cons_of_mem _ hQ))
    simp only [pauliSectorCases, hh, add_mul, mul_add,
      sector_block_reorder _ _ _ _ (hcomm false false), sector_block_reorder _ _ _ _ (hcomm false true),
      sector_block_reorder _ _ _ _ (hcomm true false), sector_block_reorder _ _ _ _ (hcomm true true),
      pauliControlProjection_self,
      pauliControlProjection_cross P (Bool.false_ne_true),
      pauliControlProjection_cross P (Ne.symm Bool.false_ne_true),
      zero_mul, zero_add, add_zero]

private theorem pauliSectorCases_pow {n : ℕ} (S : List (Word n)) (f : List Bool → Reg n)
    (hS : S.Pairwise fun P Q => Commute (finitePauliMatrix P) (finitePauliMatrix Q))
    (hf : ∀ s P, P ∈ S → Commute (f s) (finitePauliMatrix P)) (k : ℕ) :
    pauliSectorCases S (fun s => f s ^ k) = (pauliSectorCases S f) ^ k := by
  induction k with
  | zero => simp only [pow_zero, pauliSectorCases_const]
  | succ k ih =>
    simp only [pow_succ]
    rw [pauliSectorCases_mul S (fun s => f s ^ k) f hS (fun s P hP => (hf s P hP).pow_left k), ih]

private theorem pauliSectorCases_hasSum {n : ℕ} (S : List (Word n))
    (f : ℕ → List Bool → Reg n) (g : List Bool → Reg n)
    (h : ∀ s, HasSum (fun k => f k s) (g s)) :
    HasSum (fun k => pauliSectorCases S (f k)) (pauliSectorCases S g) := by
  induction S generalizing f g with
  | nil => exact h []
  | cons P S ih =>
    have h₀ := ih (fun k s => f k (false :: s)) (fun s => g (false :: s)) (fun s => h (false :: s))
    have h₁ := ih (fun k s => f k (true :: s)) (fun s => g (true :: s)) (fun s => h (true :: s))
    simpa only [pauliSectorCases] using
      (h₀.mul_left (pauliControlProjection P false)).add (h₁.mul_left (pauliControlProjection P true))

/-- The matrix exponential acts sector by sector on a family that
preserves the commuting control symmetries. -/
theorem exp_pauliSectorCases {n : ℕ} (S : List (Word n)) (f : List Bool → Reg n)
    (hS : S.Pairwise fun P Q => Commute (finitePauliMatrix P) (finitePauliMatrix Q))
    (hf : ∀ s P, P ∈ S → Commute (f s) (finitePauliMatrix P)) :
    exp (pauliSectorCases S f) = pauliSectorCases S (fun s => exp (f s)) := by
  have hexp (A : Reg n) : HasSum (fun k => ((k.factorial : ℂ)⁻¹) • A ^ k) (exp A) :=
    (expSeries_hasSum_exp (𝕂 := ℂ) A).congr_fun fun k => (expSeries_apply_eq (𝕂 := ℂ) A k).symm
  have h := pauliSectorCases_hasSum S (fun k s => ((k.factorial : ℂ)⁻¹) • (f s) ^ k)
    (fun s => exp (f s)) (fun s => hexp (f s))
  have hf' : HasSum (fun k => ((k.factorial : ℂ)⁻¹) • (pauliSectorCases S f) ^ k)
      (pauliSectorCases S fun s => exp (f s)) := by
    simpa only [pauliSectorCases_smul, pauliSectorCases_pow S f hS hf] using h
  exact (hexp (pauliSectorCases S f)).unique hf'

/-- Fixed-Hamiltonian evolution is the assembly of the evolutions in the
joint symmetry sectors. -/
theorem unitaryEvolution_pauliSectorCases {n : ℕ} (S : List (Word n)) (f : List Bool → Reg n)
    (hS : S.Pairwise fun P Q => Commute (finitePauliMatrix P) (finitePauliMatrix Q))
    (hf : ∀ s P, P ∈ S → Commute (f s) (finitePauliMatrix P)) (t : ℝ) :
    unitaryEvolution (pauliSectorCases S f) t = pauliSectorCases S (fun s => unitaryEvolution (f s) t) := by
  have he := exp_pauliSectorCases S (fun s => (t : ℂ) • ((-Complex.I) • f s)) hS
    (fun s P hP => ((hf s P hP).smul_left (-Complex.I)).smul_left (t : ℂ))
  change exp ((t : ℂ) • ((-Complex.I) • pauliSectorCases S f)) =
    pauliSectorCases S (fun s => exp ((t : ℂ) • ((-Complex.I) • f s)))
  simpa only [pauliSectorCases_smul] using he

/-- The scalar operator prescribed by a real-valued function of the
commuting symmetry signs. -/
def pauliSectorScalar {n : ℕ} (S : List (Word n)) (f : List Bool → ℝ) : Reg n :=
  pauliSectorCases S fun s => (f s : ℂ) • (1 : Reg n)

/-- A sector-dependent coefficient times a fixed word is the assembled
scalar operator multiplied by that word. -/
theorem pauliSectorCases_real_smul_word {n : ℕ} (S : List (Word n)) (f : List Bool → ℝ) (Q : Word n) :
    pauliSectorCases S (fun s => (f s : ℂ) • finitePauliMatrix Q) =
      pauliSectorScalar S f * finitePauliMatrix Q := by
  unfold pauliSectorScalar
  rw [← pauliSectorCases_mul_const]
  apply congrArg (pauliSectorCases S)
  funext s
  rw [Matrix.smul_mul, one_mul]

theorem commute_pauliSectorScalar {n : ℕ} (S : List (Word n)) (f : List Bool → ℝ) (M : Reg n)
    (hS : ∀ P ∈ S, Commute M (finitePauliMatrix P)) : Commute M (pauliSectorScalar S f) :=
  commute_pauliSectorCases S _ M hS fun s => (Commute.one_right M).smul_right (f s : ℂ)

/-- Inserting arbitrary scalar functions of commuting controls preserves
commutation between operators that preserve those controls. -/
theorem commute_pauliSectorScalar_mul {n : ℕ} (S : List (Word n)) (f g : List Bool → ℝ) (M N : Reg n)
    (hS : ∀ P ∈ S, ∀ Q ∈ S, Commute (finitePauliMatrix P) (finitePauliMatrix Q))
    (hM : ∀ P ∈ S, Commute M (finitePauliMatrix P))
    (hN : ∀ P ∈ S, Commute N (finitePauliMatrix P)) (hMN : Commute M N) :
    Commute (pauliSectorScalar S f * M) (pauliSectorScalar S g * N) := by
  have hfg : Commute (pauliSectorScalar S f) (pauliSectorScalar S g) :=
    commute_pauliSectorScalar S _ _ fun P hP => (commute_pauliSectorScalar S f _ (hS P hP)).symm
  have hMg := commute_pauliSectorScalar S g M hM
  have hfN := (commute_pauliSectorScalar S f N hN).symm
  exact (hfg.mul_left hMg).mul_right (hfN.mul_left hMN)

private theorem pauliSectorScalar_linear {n : ℕ} (S : List (Word n)) (a b : ℝ) (f g : List Bool → ℝ) :
    pauliSectorScalar S (fun s => a * f s + b * g s) =
      (a : ℂ) • pauliSectorScalar S f + (b : ℂ) • pauliSectorScalar S g := by
  unfold pauliSectorScalar
  rw [← pauliSectorCases_smul, ← pauliSectorCases_smul, ← pauliSectorCases_add]
  apply congrArg (pauliSectorCases S)
  funext s
  simp only [smul_smul, ← add_smul, Complex.ofReal_add, Complex.ofReal_mul]

private theorem pauliSectorScalar_neg {n : ℕ} (S : List (Word n)) (f : List Bool → ℝ) :
    pauliSectorScalar S (fun s => -f s) = -pauliSectorScalar S f := by
  simpa only [pauliSectorScalar, Complex.ofReal_neg, neg_smul, one_smul] using
    pauliSectorCases_smul S (-1 : ℂ) (fun s => (f s : ℂ) • (1 : Reg n))

/-- Average of the two angles obtained by fixing the first sign. -/
def sectorAverage (f : List Bool → ℝ) (s : List Bool) : ℝ :=
  (1 / 2) * f (false :: s) + (1 / 2) * f (true :: s)

/-- Half of the positive-sign angle minus the negative-sign angle. -/
def sectorDifference (f : List Bool → ℝ) (s : List Bool) : ℝ :=
  (1 / 2) * f (false :: s) + -(1 / 2) * f (true :: s)

/-- One step of real Walsh expansion on the symmetry list. -/
theorem pauliSectorScalar_cons_expand {n : ℕ} (P : Word n) (S : List (Word n)) (f : List Bool → ℝ)
    (hP : ∀ Q ∈ S, Commute (finitePauliMatrix P) (finitePauliMatrix Q)) :
    pauliSectorScalar (P :: S) f = pauliSectorScalar S (sectorAverage f) +
      pauliSectorScalar S (sectorDifference f) * finitePauliMatrix P := by
  let X := pauliSectorScalar S fun s => f (false :: s)
  let Y := pauliSectorScalar S fun s => f (true :: s)
  have hX : Commute (finitePauliMatrix P) X := commute_pauliSectorScalar S _ _ hP
  have hY : Commute (finitePauliMatrix P) Y := commute_pauliSectorScalar S _ _ hP
  unfold sectorAverage sectorDifference
  rw [pauliSectorScalar_linear, pauliSectorScalar_linear]
  change pauliControlProjection P false * X + pauliControlProjection P true * Y =
    (((1 / 2 : ℝ) : ℂ) • X + ((1 / 2 : ℝ) : ℂ) • Y) +
      (((1 / 2 : ℝ) : ℂ) • X + ((-(1 / 2) : ℝ) : ℂ) • Y) * finitePauliMatrix P
  simp only [pauliControlProjection, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, Matrix.smul_mul, add_mul, sub_mul, one_mul, smul_add, smul_sub, neg_smul, neg_mul,
    hX.eq, hY.eq]
  abel

/-- Two commuting Pauli matrices multiply to a Pauli matrix with a real sign. -/
theorem exists_signed_pauli_product_of_commute {n : ℕ} (P Q : Word n)
    (h : Commute (finitePauliMatrix P) (finitePauliMatrix Q)) :
    ∃ R : Word n, finitePauliMatrix P * finitePauliMatrix Q = finitePauliMatrix R ∨
      finitePauliMatrix P * finitePauliMatrix Q = -finitePauliMatrix R := by
  let A := finitePauliMatrix P
  let B := finitePauliMatrix Q
  let R (v : Fin n) := optMul (P v) (Q v)
  let z : ℂ := ∏ v, optPhase (P v) (Q v)
  have hprod : A * B = z • finitePauliMatrix R := finitePauliMatrix_mul P Q
  have hAB : A * B = B * A := h.eq
  have hA : A * A = 1 := finitePauliMatrix_mul_self P
  have hB : B * B = 1 := finitePauliMatrix_mul_self Q
  have hs : (A * B) * (A * B) = 1 := by
    calc
      _ = (A * (B * A)) * B := by simp only [mul_assoc]
      _ = _ := by rw [← hAB, ← mul_assoc A A B, hA, one_mul, hB]
  rw [hprod, smul_mul_smul_comm, finitePauliMatrix_mul_self] at hs
  let x : Fin n → Bool := fun _ => false
  have hz : z * z = 1 := by
    have hx := congrArg (fun M : Reg n => M x x) hs
    simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using hx
  have hr : (z - 1) * (z + 1) = 0 := calc
    _ = z * z - 1 := by ring
    _ = 0 := by rw [hz, sub_self]
  refine ⟨R, ?_⟩
  rcases mul_eq_zero.mp hr with hp | hn
  · exact Or.inl (by rw [hprod, sub_eq_zero.mp hp, one_smul])
  · exact Or.inr (by rw [hprod, eq_neg_of_add_eq_zero_left hn, neg_one_smul])

/-- The evolution of a commuting sum factors without product-formula error. -/
theorem unitaryEvolution_add_of_commuting {n : ℕ} {A B : Reg n}
    (h : Commute A B) (t : ℝ) : unitaryEvolution (A + B) t = unitaryEvolution A t * unitaryEvolution B t := by
  letI : NormedAlgebra ℚ (Reg n) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hc : Commute (t • ((-Complex.I) • A)) (t • ((-Complex.I) • B)) :=
    (((h.smul_left (-Complex.I)).smul_right (-Complex.I)).smul_left t).smul_right t
  rw [unitaryEvolution, unitaryEvolution, unitaryEvolution, smul_add, smul_add, exp_add_of_commute hc]

/-- A real Pauli coefficient rescales the rotation time. -/
theorem unitaryEvolution_scale_pauli {n : ℕ} (Q : Word n) (a t : ℝ) :
    unitaryEvolution ((a : ℂ) • finitePauliMatrix Q) t = unitaryEvolution (finitePauliMatrix Q) (a * t) := by
  unfold unitaryEvolution
  congr 1
  change (t : ℂ) • ((-Complex.I) • ((a : ℂ) • finitePauliMatrix Q)) =
    ((a * t : ℝ) : ℂ) • ((-Complex.I) • finitePauliMatrix Q)
  simp only [smul_smul, Complex.ofReal_mul]
  congr 1
  ring

open DiagonalSynthesis in
/-- A Pauli rotation with an arbitrary real angle in each symmetry
sector has an exact projective circuit with at most `2^k (2n+1)` gates,
where `k` is the number of listed controls. -/
theorem pauliSectorRotation_realizes {n : ℕ} (hn : 2 ≤ n) (S : List (Word n))
    (f : List Bool → ℝ) (Q : Word n) (t : ℝ)
    (hS : ∀ P ∈ S, ∀ R ∈ S, Commute (finitePauliMatrix P) (finitePauliMatrix R))
    (hQ : ∀ P ∈ S, Commute (finitePauliMatrix P) (finitePauliMatrix Q)) :
    Realizes (2 ^ S.length * (2 * n + 1))
      (unitaryEvolution (pauliSectorScalar S f * finitePauliMatrix Q) t) := by
  induction S generalizing f Q with
  | nil =>
    change Realizes (2 ^ (0 : ℕ) * (2 * n + 1))
      (unitaryEvolution (((f [] : ℝ) : ℂ) • (1 : Reg n) * finitePauliMatrix Q) t)
    rw [pow_zero, one_mul, Matrix.smul_mul, one_mul, unitaryEvolution_scale_pauli]
    obtain ⟨z, hz, C, hC, he⟩ := exists_projective_pauli_rotation_circuit hn Q (f [] * t)
    have hw : pauliWeight Q ≤ n := (Finset.card_le_univ _).trans (by simp)
    exact ⟨z, hz, C, by omega, he⟩
  | cons P S ih =>
    have hPS R (hR : R ∈ S) := hS P (by simp) R (List.mem_cons_of_mem _ hR)
    have htS R (hR : R ∈ S) Z (hZ : Z ∈ S) :=
      hS R (List.mem_cons_of_mem _ hR) Z (List.mem_cons_of_mem _ hZ)
    have htQ R (hR : R ∈ S) := hQ R (List.mem_cons_of_mem _ hR)
    have hpq := hQ P (by simp)
    let X := pauliSectorScalar S (sectorAverage f)
    let Y := pauliSectorScalar S (sectorDifference f)
    let A := finitePauliMatrix Q
    let B := finitePauliMatrix P
    have hcomm : Commute (X * A) (Y * (B * A)) :=
      commute_pauliSectorScalar_mul S _ _ A (B * A) htS (fun R hR => (htQ R hR).symm)
        (fun R hR => ((hPS R hR).symm.mul_right (htQ R hR)).symm)
        (hpq.symm.mul_right (Commute.refl A))
    have hdecomp : pauliSectorScalar (P :: S) f * A = X * A + Y * (B * A) := by
      rw [pauliSectorScalar_cons_expand P S f hPS, add_mul, mul_assoc]
    have hU := ih (sectorAverage f) Q htS htQ
    have hV : Realizes (2 ^ S.length * (2 * n + 1)) (unitaryEvolution (Y * (B * A)) t) := by
      obtain ⟨R, hR | hR⟩ := exists_signed_pauli_product_of_commute P Q hpq
      · have hrT (T : Word n) (hT : T ∈ S) : Commute (finitePauliMatrix T) (finitePauliMatrix R) := by
          rw [← hR]
          exact (hPS T hT).symm.mul_right (htQ T hT)
        change Realizes _ (unitaryEvolution (Y * (finitePauliMatrix P * finitePauliMatrix Q)) t)
        rw [hR]
        exact ih (sectorDifference f) R htS hrT
      · have hrT (T : Word n) (hT : T ∈ S) : Commute (finitePauliMatrix T) (finitePauliMatrix R) := by
          have hh := ((hPS T hT).symm.mul_right (htQ T hT)).neg_right
          rwa [hR, neg_neg] at hh
        change Realizes _ (unitaryEvolution (Y * (finitePauliMatrix P * finitePauliMatrix Q)) t)
        rw [hR, mul_neg, ← neg_mul]
        change Realizes _ (unitaryEvolution ((-pauliSectorScalar S (sectorDifference f)) * finitePauliMatrix R) t)
        rw [← pauliSectorScalar_neg]
        exact ih (fun s => -sectorDifference f s) R htS hrT
    change Realizes (2 ^ (S.length + 1) * (2 * n + 1)) (unitaryEvolution (pauliSectorScalar (P :: S) f * A) t)
    rw [hdecomp, unitaryEvolution_add_of_commuting hcomm, pow_succ]
    have hbudget : (2 ^ S.length * 2) * (2 * n + 1) =
        2 ^ S.length * (2 * n + 1) + 2 ^ S.length * (2 * n + 1) := by ring
    rw [hbudget]
    exact hU.mul hV

open DiagonalSynthesis in
/-- A phase specified on the joint symmetry signs has the same exact
gate cap as a sector-controlled rotation. -/
theorem pauliSectorPhase_realizes {n : ℕ} (hn : 2 ≤ n) (S : List (Word n)) (f : List Bool → ℝ)
    (hS : ∀ P ∈ S, ∀ Q ∈ S, Commute (finitePauliMatrix P) (finitePauliMatrix Q)) (t : ℝ) :
    Realizes (2 ^ S.length * (2 * n + 1)) (unitaryEvolution (pauliSectorScalar S f) t) := by
  have hI : finitePauliMatrix (pauliIdentityLabel n) = (1 : Reg n) := by
    ext x y
    exact finitePauliMatrix_pauliIdentityLabel x y
  have h := pauliSectorRotation_realizes hn S f (pauliIdentityLabel n) t hS (by
    intro P _
    rw [hI]
    exact Commute.one_right _)
  simpa only [hI, mul_one] using h

open DiagonalSynthesis in
/-- A sum of commuting sector-weighted Pauli terms has an exact circuit
whose cost is at most the number of target terms times the one-term cap. -/
theorem pauliSectorCommutingSum_realizes {n : ℕ} (hn : 2 ≤ n) (S : List (Word n))
    (T : Finset (Word n)) (f : Word n → List Bool → ℝ)
    (hS : ∀ P ∈ S, ∀ Q ∈ S, Commute (finitePauliMatrix P) (finitePauliMatrix Q))
    (hT : ∀ P ∈ T, ∀ Q ∈ T, Commute (finitePauliMatrix P) (finitePauliMatrix Q))
    (hST : ∀ P ∈ S, ∀ Q ∈ T, Commute (finitePauliMatrix P) (finitePauliMatrix Q)) (t : ℝ) :
    Realizes (T.card * (2 ^ S.length * (2 * n + 1)))
      (unitaryEvolution (∑ Q ∈ T, pauliSectorScalar S (f Q) * finitePauliMatrix Q) t) := by
  classical
  let B := 2 ^ S.length * (2 * n + 1)
  let H (Q : Word n) := pauliSectorScalar S (f Q) * finitePauliMatrix Q
  change Realizes (T.card * B) (unitaryEvolution (∑ Q ∈ T, H Q) t)
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.card_empty, zero_mul, Finset.sum_empty, unitaryEvolution, smul_zero, exp_zero]
    exact Realizes.one n
  | @insert Q T hQ ih =>
    have htail := ih (fun P hP R hR => hT P (Finset.mem_insert_of_mem hP) R (Finset.mem_insert_of_mem hR))
      (fun P hP R hR => hST P hP R (Finset.mem_insert_of_mem hR))
    have hhead : Realizes B (unitaryEvolution (H Q) t) :=
      pauliSectorRotation_realizes hn S (f Q) Q t hS fun P hP => hST P hP Q (Finset.mem_insert_self _ _)
    have hc : Commute (H Q) (∑ R ∈ T, H R) := by
      change H Q * (∑ R ∈ T, H R) = (∑ R ∈ T, H R) * H Q
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun R hR =>
        (commute_pauliSectorScalar_mul S (f Q) (f R) _ _ hS
          (fun P hP => (hST P hP Q (Finset.mem_insert_self _ _)).symm)
          (fun P hP => (hST P hP R (Finset.mem_insert_of_mem hR)).symm)
          (hT Q (Finset.mem_insert_self _ _) R (Finset.mem_insert_of_mem hR))).eq
    rw [Finset.sum_insert hQ, unitaryEvolution_add_of_commuting hc, Finset.card_insert_of_notMem hQ,
      Nat.add_mul, Nat.one_mul, Nat.add_comm (T.card * B) B]
    exact hhead.mul htail

#print axioms pauliControlProjection_mul
#print axioms pauliSectorCases_mul
#print axioms exp_pauliSectorCases
#print axioms unitaryEvolution_pauliSectorCases
#print axioms pauliSectorCases_real_smul_word
#print axioms pauliSectorScalar_cons_expand
#print axioms commute_pauliSectorScalar_mul
#print axioms exists_signed_pauli_product_of_commute
#print axioms pauliSectorRotation_realizes
#print axioms pauliSectorPhase_realizes
#print axioms pauliSectorCommutingSum_realizes

end

end GaloisForLFunctions.HTGeometry
