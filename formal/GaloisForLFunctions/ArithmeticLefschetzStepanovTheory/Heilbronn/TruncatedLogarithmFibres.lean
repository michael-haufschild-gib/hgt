import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.TruncatedLogarithmJets
import GaloisForLFunctions.HTGeometry.TriangularLineFieldInvariants
import GaloisForLFunctions.HTGeometry.MvPolynomialGradient
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Stepanov's bound for finite-logarithm fibres

The field X(1-X)∂X+(X-Z)∂Y commutes with substitution (X,L_p,X^p).
Linear constraints on its iterates give an auxiliary with high multiplicity
at every fibre point except 0 and 1. Logarithmic-mode independence makes
that auxiliary nonzero. Counting its roots and choosing A=n², B=C=n,
D=⌊n²/8⌋, with n=⌊p^(1/3)⌋, gives #fibre³≤100³p².
-/

open Polynomial Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn

variable {K : Type*} [Field K]

/-- The polynomial vector field adapted to L_p and the inseparable coordinate X^p. -/
def auxiliaryEuler (P : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.X 0 * (1 - MvPolynomial.X 0) * MvPolynomial.pderiv 0 P +
    (MvPolynomial.X 0 - MvPolynomial.X 2) * MvPolynomial.pderiv 1 P

/-- Evaluation on the graph (X,L_p(X),X^p). -/
def auxiliarySubstitution (p : ℕ) : MvPolynomial (Fin 3) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X, truncatedLog K p, Polynomial.X ^ p]

theorem auxiliarySubstitution_euler {p : ℕ} [CharP K p] (hp : 0 < p)
    (P : MvPolynomial (Fin 3) K) :
    auxiliarySubstitution p (auxiliaryEuler P) =
      Polynomial.X * (1 - Polynomial.X) * (auxiliarySubstitution p P).derivative := by
  let D : Derivation K (Polynomial K) (Polynomial K) :=
    (Polynomial.X * (1 - Polynomial.X) : Polynomial K) • Polynomial.derivative'
  have hX : D Polynomial.X = Polynomial.X * (1 - Polynomial.X) := by
    simp [D]
  have hL : D (truncatedLog K p) = Polynomial.X - Polynomial.X ^ p := by
    simp only [D, Derivation.smul_apply, Polynomial.derivative'_apply, smul_eq_mul]
    rw [mul_assoc, truncatedLog_weighted_derivative, mul_sub, mul_one]
    rw [← pow_succ', Nat.sub_add_cancel hp]
  have hXp : D (Polynomial.X ^ p) = 0 := by
    simp [D]
  have hc := HTGeometry.derivation_aeval_eq_sum_pderiv D
    ![Polynomial.X, truncatedLog K p, Polynomial.X ^ p] P
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, hX, hL, hXp, mul_zero] at hc
  simp only [auxiliaryEuler, auxiliarySubstitution, map_add, map_mul,
    map_sub, map_one, MvPolynomial.aeval_X]
  simp only [D, Derivation.smul_apply, Polynomial.derivative'_apply, smul_eq_mul] at hc
  change Polynomial.X * (1 - Polynomial.X) *
      (auxiliarySubstitution p (MvPolynomial.pderiv 0 P)) +
      (Polynomial.X - Polynomial.X ^ p) *
      (auxiliarySubstitution p (MvPolynomial.pderiv 1 P)) =
      Polynomial.X * (1 - Polynomial.X) * (auxiliarySubstitution p P).derivative
  change Polynomial.X * (1 - Polynomial.X) * (auxiliarySubstitution p P).derivative =
      (auxiliarySubstitution p (MvPolynomial.pderiv 0 P)) * (Polynomial.X * (1 - Polynomial.X)) +
      (auxiliarySubstitution p (MvPolynomial.pderiv 1 P)) * (Polynomial.X - Polynomial.X ^ p) at hc
  rw [hc]
  ring

theorem natDegree_aeval_linear_le_totalDegree {σ : Type*}
    (f : σ → Polynomial K) (hf : ∀ i, (f i).natDegree ≤ 1)
    (P : MvPolynomial σ K) : (MvPolynomial.aeval f P).natDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  rw [MvPolynomial.aeval_monomial]
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [show (algebraMap K (Polynomial K)) (MvPolynomial.coeff m P) =
      Polynomial.C (MvPolynomial.coeff m P) from rfl,
    Polynomial.natDegree_C, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hm)
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Polynomial.natDegree_pow_le.trans (by nlinarith [hf i])

theorem auxiliaryEuler_totalDegree_le (P : MvPolynomial (Fin 3) K) :
    (auxiliaryEuler P).totalDegree ≤ P.totalDegree + 2 := by
  have hd (i : Fin 3) : (MvPolynomial.pderiv i P).totalDegree ≤ P.totalDegree := by
    by_cases h : MvPolynomial.pderiv i P = 0
    · simp [h]
    · exact (GaloisForLFunctions.totalDegree_pderiv_lt P i h).le
  have hW : (MvPolynomial.X 0 * (1 - MvPolynomial.X 0) :
      MvPolynomial (Fin 3) K).totalDegree ≤ 2 := by
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have hs := MvPolynomial.totalDegree_sub (1 : MvPolynomial (Fin 3) K) (MvPolynomial.X 0)
    simp only [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X, max_eq_right (by omega : 0 ≤ 1)] at hs ⊢
    omega
  have hV : (MvPolynomial.X 0 - MvPolynomial.X 2 : MvPolynomial (Fin 3) K).totalDegree ≤ 1 := by
    simpa only [MvPolynomial.totalDegree_X, max_self] using
      MvPolynomial.totalDegree_sub (MvPolynomial.X 0 : MvPolynomial (Fin 3) K) (MvPolynomial.X 2)
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le
    ((MvPolynomial.totalDegree_mul _ _).trans (by have := hd 0; omega))
    ((MvPolynomial.totalDegree_mul _ _).trans (by have := hd 1; omega)))

theorem auxiliaryEuler_iterate_totalDegree_le (P : MvPolynomial (Fin 3) K) (n : ℕ) :
    (auxiliaryEuler^[n] P).totalDegree ≤ P.totalDegree + 2 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have := auxiliaryEuler_totalDegree_le (auxiliaryEuler^[n] P)
    omega

/-- Differentiation along the polynomial vector field W. -/
def weightedDerivative (W P : K[X]) : K[X] := W * P.derivative

theorem eval_iterate_derivative_weighted (W P : K[X]) (x : K) (n : ℕ)
    (hz : ∀ j < n, (derivative^[j + 1] P).eval x = 0) :
    (derivative^[n] (weightedDerivative W P)).eval x =
      W.eval x * (derivative^[n + 1] P).eval x := by
  rw [weightedDerivative, iterate_derivative_mul, eval_finsetSum]
  rw [sum_eq_single n]
  · simp only [Nat.choose_self, one_smul, eval_mul, Nat.sub_self,
      Function.iterate_zero_apply, Function.iterate_succ_apply]
  · intro j hj hne
    have hjn : j < n := by have := mem_range.mp hj; omega
    rw [eval_smul, eval_mul, ← Function.iterate_succ_apply, hz j hjn, mul_zero, smul_zero]
  · simp

/-- When lower ordinary jets vanish, the leading weighted jet is W(x)^n times the ordinary jet. -/
theorem weightedDerivative_iterate_eval (W P : K[X]) (x : K) (n : ℕ)
    (hz : ∀ j < n, (derivative^[j] P).eval x = 0) :
    ((weightedDerivative W)^[n] P).eval x =
      W.eval x ^ n * (derivative^[n] P).eval x := by
  induction n generalizing P with
  | zero => simp
  | succ n ih =>
    have hz' : ∀ j < n, (derivative^[j] (weightedDerivative W P)).eval x = 0 := by
      intro j hj
      rw [eval_iterate_derivative_weighted W P x j (fun k hk => hz (k + 1) (by omega)),
        hz (j + 1) (by omega), mul_zero]
    rw [Function.iterate_succ_apply, ih _ hz',
      eval_iterate_derivative_weighted W P x n (fun j hj => hz (j + 1) (by omega)),
      pow_succ]
    ring

theorem derivative_jets_of_weightedDerivative_jets (W P : K[X]) (x : K)
    (hW : W.eval x ≠ 0) (N : ℕ)
    (hz : ∀ n < N, ((weightedDerivative W)^[n] P).eval x = 0) :
    ∀ n < N, (derivative^[n] P).eval x = 0 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hlow : ∀ j < n, (derivative^[j] P).eval x = 0 :=
      fun j hj => ih j hj (hj.trans hn)
    have heq := weightedDerivative_iterate_eval W P x n hlow
    rw [hz n hn] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero _ hW)

theorem auxiliarySubstitution_iterate {p : ℕ} [CharP K p] (hp : 0 < p)
    (P : MvPolynomial (Fin 3) K) (n : ℕ) :
    auxiliarySubstitution p (auxiliaryEuler^[n] P) =
      (weightedDerivative (X * (1 - X)))^[n] (auxiliarySubstitution p P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', auxiliarySubstitution_euler hp, ih,
      Function.iterate_succ_apply']
    rfl

theorem le_rootMultiplicity_of_weightedDerivative_jets {p N : ℕ} [CharP K p]
    (W P : K[X]) (x : K) (hW : W.eval x ≠ 0) (hP : P ≠ 0) (hN : N ≤ p)
    (hz : ∀ n < N, ((weightedDerivative W)^[n] P).eval x = 0) :
    N ≤ P.rootMultiplicity x := by
  by_cases hN0 : N = 0
  · simp [hN0]
  have hord := derivative_jets_of_weightedDerivative_jets W P x hW N hz
  have hfact : ((N - 1).factorial : K) ∈ nonZeroDivisors K :=
    mem_nonZeroDivisors_iff_ne_zero.mpr (factorial_ne_zero_of_lt_char (by omega : N - 1 < p))
  have hmult := lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors
    hP (fun n hn => hord n (by omega)) hfact
  omega

/-- Vanishing weighted jets below the characteristic count roots with their full multiplicity. -/
theorem weightedDerivative_jet_count {p N : ℕ} [CharP K p]
    (W P : K[X]) (S : Finset K) (hP : P ≠ 0) (hN : N ≤ p)
    (hW : ∀ x ∈ S, W.eval x ≠ 0)
    (hz : ∀ x ∈ S, ∀ n < N, ((weightedDerivative W)^[n] P).eval x = 0) :
    N * S.card ≤ P.natDegree := by
  classical
  have hroot : ∀ x ∈ S, (X - C x) ^ N ∣ P := by
    intro x hx
    exact (pow_dvd_pow (X - C x)
      (le_rootMultiplicity_of_weightedDerivative_jets W P x (hW x hx) hP hN (hz x hx))).trans
      (P.pow_rootMultiplicity_dvd x)
  have hprod : (∏ x ∈ S, (X - C x) ^ N) ∣ P := by
    apply Finset.prod_dvd_of_coprime
    · intro x _ y _ hxy
      exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hxy).isUnit).pow
    · exact hroot
  have hdeg : (∏ x ∈ S, (X - C x) ^ N : K[X]).natDegree = N * S.card := by
    rw [natDegree_prod _ _ (fun x _ => pow_ne_zero _ (X_sub_C_ne_zero x))]
    simp [natDegree_pow, mul_comm]
  rw [← hdeg]
  exact natDegree_le_of_dvd hprod hP

def auxiliaryBlock {A B : ℕ} (c : LogSlot A B → K) : MvPolynomial (Fin 3) K :=
  ∑ k, MvPolynomial.C (c k) *
    ((1 - MvPolynomial.X 0) ^ (gammaJetSlotNode (fun _ : Fin A => B) k : ℕ) *
      MvPolynomial.X 1 ^ gammaJetSlotOrder (fun _ : Fin A => B) k)

/-- The trivariate auxiliary in Horner form in its inseparable coordinate. -/
def auxiliaryPolynomial (A B : ℕ) :
    (C : ℕ) → (Fin C → LogSlot A B → K) → MvPolynomial (Fin 3) K
  | 0, _ => 0
  | C + 1, c => auxiliaryBlock (c 0) +
      MvPolynomial.X 2 * auxiliaryPolynomial A B C (fun j => c j.succ)

theorem auxiliarySubstitution_block (p : ℕ) {A B : ℕ} (c : LogSlot A B → K) :
    auxiliarySubstitution p (auxiliaryBlock c) = logarithmicBlock p c := by
  simp [auxiliaryBlock, auxiliarySubstitution, logarithmicBlock, logarithmicMode, map_sum]

theorem auxiliarySubstitution_polynomial (p A B C : ℕ) (c : Fin C → LogSlot A B → K) :
    auxiliarySubstitution p (auxiliaryPolynomial A B C c) = logarithmicAuxiliary p A B C c := by
  induction C with
  | zero => simp [auxiliaryPolynomial, logarithmicAuxiliary]
  | succ C ih =>
    simp only [auxiliaryPolynomial, logarithmicAuxiliary, map_add, map_mul,
      auxiliarySubstitution_block, ih]
    simp [auxiliarySubstitution]

theorem auxiliaryBlock_totalDegree_le {A B : ℕ} (c : LogSlot A B → K) :
    (auxiliaryBlock c).totalDegree ≤ A + B := by
  unfold auxiliaryBlock
  refine MvPolynomial.totalDegree_finsetSum_le fun k _ => ?_
  have ha := (gammaJetSlotNode (fun _ : Fin A => B) k).isLt
  have hb : gammaJetSlotOrder (fun _ : Fin A => B) k < B :=
    (gammaJetSlotOrderIso (fun _ : Fin A => B) k).2.isLt
  have hW : (1 - MvPolynomial.X 0 : MvPolynomial (Fin 3) K).totalDegree ≤ 1 := by
    simpa using MvPolynomial.totalDegree_sub (1 : MvPolynomial (Fin 3) K) (MvPolynomial.X 0)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_X_pow]
  have hp := MvPolynomial.totalDegree_pow (1 - MvPolynomial.X 0 : MvPolynomial (Fin 3) K)
    (gammaJetSlotNode (fun _ : Fin A => B) k : ℕ)
  have hpow := hp.trans (Nat.mul_le_mul_left _ hW)
  simp only [mul_one] at hpow
  omega

theorem auxiliaryPolynomial_totalDegree_le (A B C : ℕ) (c : Fin C → LogSlot A B → K) :
    (auxiliaryPolynomial A B C c).totalDegree ≤ A + B + C := by
  induction C with
  | zero => simp [auxiliaryPolynomial]
  | succ C ih =>
    rw [auxiliaryPolynomial]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (auxiliaryBlock_totalDegree_le _).trans (by omega)
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_X]
      have := ih (fun j => c j.succ)
      omega

def auxiliaryDiagonal (z : K) : MvPolynomial (Fin 3) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval ![Polynomial.X, Polynomial.C z, Polynomial.X]

/-- Restrict an iterated auxiliary derivative to the fibre L_p=z and X^p=X. -/
def auxiliaryConstraint (z : K) (n A B C : ℕ) (c : Fin C → LogSlot A B → K) : Polynomial K :=
  auxiliaryDiagonal z (auxiliaryEuler^[n] (auxiliaryPolynomial A B C c))

theorem auxiliaryConstraint_natDegree_le (z : K) (n A B C : ℕ)
    (c : Fin C → LogSlot A B → K) :
    (auxiliaryConstraint z n A B C c).natDegree ≤ A + B + C + 2 * n := by
  refine (natDegree_aeval_linear_le_totalDegree _ ?_ _).trans
    ((auxiliaryEuler_iterate_totalDegree_le _ n).trans ?_)
  · intro i
    fin_cases i <;> simp
  · have := auxiliaryPolynomial_totalDegree_le A B C c
    omega

theorem auxiliaryBlock_linear {A B : ℕ} (c d : LogSlot A B → K) (t : K) :
    auxiliaryBlock (c + t • d) = auxiliaryBlock c + MvPolynomial.C t * auxiliaryBlock d := by
  unfold auxiliaryBlock
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

theorem auxiliaryPolynomial_linear (A B C : ℕ)
    (c d : Fin C → LogSlot A B → K) (t : K) :
    auxiliaryPolynomial A B C (c + t • d) =
      auxiliaryPolynomial A B C c + MvPolynomial.C t * auxiliaryPolynomial A B C d := by
  induction C with
  | zero => simp [auxiliaryPolynomial]
  | succ C ih =>
    change auxiliaryBlock (c 0 + t • d 0) + MvPolynomial.X 2 *
        auxiliaryPolynomial A B C ((fun j => c j.succ) + t • (fun j => d j.succ)) = _
    rw [auxiliaryBlock_linear, ih]
    simp only [auxiliaryPolynomial]
    ring

theorem auxiliaryEuler_linear (P Q : MvPolynomial (Fin 3) K) (t : K) :
    auxiliaryEuler (P + MvPolynomial.C t * Q) =
      auxiliaryEuler P + MvPolynomial.C t * auxiliaryEuler Q := by
  simp only [auxiliaryEuler, map_add, MvPolynomial.pderiv_C_mul]
  ring

theorem auxiliaryEuler_iterate_linear (P Q : MvPolynomial (Fin 3) K) (t : K) (n : ℕ) :
    auxiliaryEuler^[n] (P + MvPolynomial.C t * Q) =
      auxiliaryEuler^[n] P + MvPolynomial.C t * auxiliaryEuler^[n] Q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, auxiliaryEuler_linear,
      Function.iterate_succ_apply', Function.iterate_succ_apply']

theorem auxiliaryConstraint_linear (z : K) (n A B C : ℕ)
    (c d : Fin C → LogSlot A B → K) (t : K) :
    auxiliaryConstraint z n A B C (c + t • d) =
      auxiliaryConstraint z n A B C c + Polynomial.C t * auxiliaryConstraint z n A B C d := by
  simp only [auxiliaryConstraint, auxiliaryPolynomial_linear, auxiliaryEuler_iterate_linear,
    map_add, map_mul]
  simp [auxiliaryDiagonal]

/-- More coefficients than jet equations give a nonzero coefficient array satisfying every equation. -/
theorem exists_auxiliary_constraints (z : K) (A B C D : ℕ)
    (hdim : D * (A + B + C + 2 * D + 1) < C * (A * B)) :
    ∃ c : Fin C → LogSlot A B → K, c ≠ 0 ∧
      ∀ n : Fin D, auxiliaryConstraint z n A B C c = 0 := by
  let M := A + B + C + 2 * D + 1
  let L : (Fin C → LogSlot A B → K) →ₗ[K] (Fin D → Fin M → K) :=
    { toFun := fun c n m => (auxiliaryConstraint z n A B C c).coeff m
      map_add' := by
        intro c d
        funext n m
        have h := auxiliaryConstraint_linear z n A B C c d 1
        simp only [one_smul, Polynomial.C_1, one_mul] at h
        simp [h]
      map_smul' := by
        intro t c
        funext n m
        have h0 : auxiliaryConstraint z n A B C (0 : Fin C → LogSlot A B → K) = 0 := by
          have h := auxiliaryConstraint_linear z n A B C 0 0 1
          simp only [smul_zero, add_zero, Polynomial.C_1, one_mul] at h
          linear_combination -h
        have h := auxiliaryConstraint_linear z n A B C 0 c t
        simp only [zero_add, h0] at h
        simp [h, Polynomial.coeff_C_mul] }
  have hfin : Module.finrank K (Fin D → Fin M → K) <
      Module.finrank K (Fin C → LogSlot A B → K) := by
    simpa [M, LogSlot, Module.finrank_pi_fintype, Nat.mul_assoc] using hdim
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hfin)
  refine ⟨c, hc0, fun n => ?_⟩
  ext m
  simp only [Polynomial.coeff_zero]
  by_cases hm : m < M
  · have := congrFun (congrFun (LinearMap.mem_ker.mp hc) n) ⟨m, hm⟩
    simpa [L] using this
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hd := auxiliaryConstraint_natDegree_le z n A B C c
    have hn := n.isLt
    dsimp [M] at hm
    omega

theorem truncatedLog_natDegree_le (p : ℕ) : (truncatedLog K p).natDegree ≤ p := by
  unfold truncatedLog
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := mem_range.mp hi; omega)

theorem logarithmicMode_natDegree_le (p a b : ℕ) :
    (logarithmicMode K p a b).natDegree ≤ a + p * b := by
  unfold logarithmicMode
  refine Polynomial.natDegree_mul_le.trans ?_
  have hX : (1 - Polynomial.X : Polynomial K).natDegree ≤ 1 := by
    simpa using Polynomial.natDegree_sub_le (1 : Polynomial K) Polynomial.X
  have h1 := (Polynomial.natDegree_pow_le (p := (1 - Polynomial.X : Polynomial K)) (n := a)).trans
    (Nat.mul_le_mul_left a hX)
  have h2 := (Polynomial.natDegree_pow_le (p := truncatedLog K p) (n := b)).trans
    (Nat.mul_le_mul_left b (truncatedLog_natDegree_le p))
  nlinarith only [h1, h2]

theorem logarithmicBlock_natDegree_le (p : ℕ) {A B : ℕ} (c : LogSlot A B → K) :
    (logarithmicBlock p c).natDegree ≤ A + p * B := by
  unfold logarithmicBlock
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C, zero_add]
  refine (logarithmicMode_natDegree_le _ _ _).trans ?_
  have ha := (gammaJetSlotNode (fun _ : Fin A => B) k).isLt
  have hb : gammaJetSlotOrder (fun _ : Fin A => B) k < B :=
    (gammaJetSlotOrderIso (fun _ : Fin A => B) k).2.isLt
  exact Nat.add_le_add ha.le (Nat.mul_le_mul_left p hb.le)

theorem logarithmicAuxiliary_natDegree_le (p A B C : ℕ) (c : Fin C → LogSlot A B → K) :
    (logarithmicAuxiliary p A B C c).natDegree ≤ A + p * (B + C) := by
  induction C with
  | zero => simp [logarithmicAuxiliary]
  | succ C ih =>
    rw [logarithmicAuxiliary]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (logarithmicBlock_natDegree_le p _).trans (by nlinarith only [Nat.zero_le (p * (C + 1))])
    · refine Polynomial.natDegree_mul_le.trans ?_
      rw [Polynomial.natDegree_X_pow]
      have := ih (fun j => c j.succ)
      nlinarith only [this]

theorem eval_auxiliarySubstitution_eq_diagonal (p : ℕ) (x z : K)
    (hxp : x ^ p = x) (hz : (truncatedLog K p).eval x = z)
    (P : MvPolynomial (Fin 3) K) :
    (auxiliarySubstitution p P).eval x = (auxiliaryDiagonal z P).eval x := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [auxiliarySubstitution, auxiliaryDiagonal]
  | add P Q hP hQ => simp only [map_add, Polynomial.eval_add, hP, hQ]
  | mul_X P i hP =>
    rw [map_mul, map_mul, Polynomial.eval_mul, Polynomial.eval_mul, hP]
    congr 1
    fin_cases i <;> simp [auxiliarySubstitution, auxiliaryDiagonal, hz, hxp]

def truncatedLogFibre (p : ℕ) [Fact p.Prime] (z : ZMod p) : Finset (ZMod p) :=
  univ.filter fun x => x ≠ 0 ∧ x ≠ 1 ∧ (truncatedLog (ZMod p) p).eval x = z

/-- The Stepanov degree-to-multiplicity bound, with explicit numerical parameter conditions. -/
theorem truncatedLog_fibre_count {p : ℕ} [Fact p.Prime] (z : ZMod p)
    (A B C D : ℕ) (hA : 0 < A) (hB : 0 < B) (hAB : A * B ≤ p) (hD : D ≤ p)
    (hdim : D * (A + B + C + 2 * D + 1) < C * (A * B)) :
    D * (truncatedLogFibre p z).card ≤ A + p * (B + C) := by
  obtain ⟨c, hc, hconstraints⟩ := exists_auxiliary_constraints z A B C D hdim
  let R := logarithmicAuxiliary p A B C c
  have hR : R ≠ 0 := logarithmicAuxiliary_ne_zero hA hB hAB hc
  have hcount : D * (truncatedLogFibre p z).card ≤ R.natDegree := by
    refine weightedDerivative_jet_count (Polynomial.X * (1 - Polynomial.X)) R
      (truncatedLogFibre p z) hR hD ?_ ?_
    · intro x hx
      have hx' := (mem_filter.mp hx).2
      simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
      exact mul_ne_zero hx'.1 (sub_ne_zero.mpr (Ne.symm hx'.2.1))
    · intro x hx n hn
      have hx' := (mem_filter.mp hx).2
      have hxp : x ^ p = x := by
        simpa only [ZMod.card] using FiniteField.pow_card x
      change ((weightedDerivative (Polynomial.X * (1 - Polynomial.X)))^[n]
        (logarithmicAuxiliary p A B C c)).eval x = 0
      rw [← auxiliarySubstitution_polynomial,
        ← auxiliarySubstitution_iterate (Fact.out : p.Prime).pos,
        eval_auxiliarySubstitution_eq_diagonal p x z hxp hx'.2.2]
      change (auxiliaryConstraint z n A B C c).eval x = 0
      rw [hconstraints ⟨n, hn⟩, Polynomial.eval_zero]
  exact hcount.trans (logarithmicAuxiliary_natDegree_le p A B C c)

/-- Cubic-scale parameters leave more coefficients than vanishing constraints. -/
theorem cubic_parameters {n : ℕ} (hn : 4 ≤ n) :
    n ^ 2 ≤ 16 * (n ^ 2 / 8) ∧
      n ^ 2 / 8 * (n ^ 2 + n + n + 2 * (n ^ 2 / 8) + 1) < n * (n ^ 2 * n) := by
  have hd : 8 * (n ^ 2 / 8) ≤ n ^ 2 := by
    have := Nat.div_mul_le_self (n ^ 2) 8
    omega
  have hrem : n ^ 2 < 8 * (n ^ 2 / 8 + 1) := by omega
  have h16 : 16 ≤ n ^ 2 := by
    have := Nat.mul_le_mul hn hn
    nlinarith only [this]
  refine ⟨by omega, ?_⟩
  have hsmall : 2 * n + 1 ≤ n ^ 2 := by
    have := Nat.mul_le_mul_left n hn
    nlinarith only [hn, this]
  have hM : n ^ 2 + n + n + 2 * (n ^ 2 / 8) + 1 ≤ 3 * n ^ 2 := by omega
  have hprod := Nat.mul_le_mul_left (n ^ 2 / 8) hM
  have hscale := Nat.mul_le_mul_right (n ^ 2) hd
  have hpos : 0 < n ^ 4 := pow_pos (by omega : 0 < n) _
  nlinarith only [hprod, hscale, hpos]

/-- The full finite-logarithm fibre, including 0 and 1. -/
def truncatedLogFullFibre (p : ℕ) [Fact p.Prime] (z : ZMod p) : Finset (ZMod p) :=
  univ.filter fun x => (truncatedLog (ZMod p) p).eval x = z

theorem truncatedLogFullFibre_card_le (p : ℕ) [Fact p.Prime] (z : ZMod p) :
    (truncatedLogFullFibre p z).card ≤ p := by
  simpa only [truncatedLogFullFibre, card_univ, ZMod.card] using
    card_le_card (filter_subset (fun x : ZMod p => (truncatedLog (ZMod p) p).eval x = z) univ)

theorem truncatedLogFullFibre_card_le_add_two (p : ℕ) [Fact p.Prime] (z : ZMod p) :
    (truncatedLogFullFibre p z).card ≤ (truncatedLogFibre p z).card + 2 := by
  classical
  have hsub : truncatedLogFullFibre p z ⊆ truncatedLogFibre p z ∪ {0, 1} := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hx1 : x = 1
    · simp [hx1]
    exact mem_union_left _ (mem_filter.mpr ⟨mem_univ x, hx0, hx1, (mem_filter.mp hx).2⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (by simp))

/-- Every fibre of L_p over F_p has at most 100 p^(2/3) points, expressed without roots. -/
theorem truncatedLog_fibre_cubic_bound (p : ℕ) [Fact p.Prime] (z : ZMod p) :
    (truncatedLogFullFibre p z).card ^ 3 ≤ 100 ^ 3 * p ^ 2 := by
  by_cases hp64 : 64 ≤ p
  · let n := Nat.nthRoot 3 p
    have hn : 4 ≤ n := (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr hp64
    have hn0 : 0 < n := by omega
    have hlo : n ^ 3 ≤ p := Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0))
    have hhi : p < (n + 1) ^ 3 := Nat.lt_pow_nthRoot_add_one (by decide : 3 ≠ 0) p
    have hnp : n ≤ p := (Nat.le_self_pow (by decide : 3 ≠ 0) n).trans hlo
    have hdim := (cubic_parameters hn).2
    have hD : n ^ 2 / 8 ≤ p := by
      have hd := Nat.div_le_self (n ^ 2) 8
      have hn2 := Nat.mul_le_mul_left (n ^ 2) (by omega : 1 ≤ n)
      nlinarith only [hd, hn2, hlo]
    have hcount := truncatedLog_fibre_count z (n ^ 2) n n (n ^ 2 / 8)
      (pow_pos hn0 _) hn0 (by nlinarith only [hlo]) hD hdim
    have hlow := (cubic_parameters hn).1
    have hmult1 := Nat.mul_le_mul_left 16 hcount
    have hmult2 := Nat.mul_le_mul_right (truncatedLogFibre p z).card hlow
    have hnp2 := Nat.mul_le_mul_right n hnp
    have hnk : n * (truncatedLogFibre p z).card ≤ 48 * p := by
      apply (mul_le_mul_iff_left₀ hn0).mp
      nlinarith only [hmult1, hmult2, hnp2]
    have hfull : n * (truncatedLogFullFibre p z).card ≤ 50 * p := by
      have h := Nat.mul_le_mul_left n (truncatedLogFullFibre_card_le_add_two p z)
      nlinarith only [h, hnk, hnp]
    have hcube := Nat.pow_le_pow_left hfull 3
    have hstep : n + 1 ≤ 2 * n := by omega
    have hstep3 := Nat.pow_le_pow_left hstep 3
    have hp8 : p ≤ 8 * n ^ 3 := by nlinarith only [hhi, hstep3]
    have hscale := Nat.mul_le_mul_left (50 ^ 3 * p ^ 2) hp8
    apply (mul_le_mul_iff_left₀ (pow_pos hn0 3)).mp
    nlinarith only [hcube, hscale]
  · have hcard := Nat.pow_le_pow_left (truncatedLogFullFibre_card_le p z) 3
    have hp : p ≤ 100 ^ 3 := by omega
    have hscale := Nat.mul_le_mul_left (p ^ 2) hp
    nlinarith only [hcard, hscale]

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn

#print axioms GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.weightedDerivative_jet_count

#print axioms GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.exists_auxiliary_constraints

#print axioms GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.truncatedLog_fibre_count

#print axioms GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.truncatedLog_fibre_cubic_bound
