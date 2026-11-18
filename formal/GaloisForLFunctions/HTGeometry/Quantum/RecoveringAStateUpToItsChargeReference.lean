import GaloisForLFunctions.HTGeometry.Quantum.EdgePhasesOfAnIntegerCharge
import GaloisForLFunctions.HTGeometry.Quantum.TwoCopyChargeObservations
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Recovering arbitrary Hermitian states up to their charge reference

The charge-preserving entries of finitely many tensor powers determine a
Hermitian matrix up to conjugation by one charge rotation. Two copies
supply the phases on the occupied gaps; bounded balanced pairs force
these phases to arise from the same rotation. At nonzero common trace,
partial trace recovers every shorter observation from one tensor power.
-/

noncomputable section
open Finset Matrix
open scoped Classical ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.Quantum.TensorObservation
open CollectiveDiophantineGeometry.Simplex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A shared charge rotation cancels in every surviving tensor entry. -/
theorem observe_charge_rotation (q : ι → ℤ) (A : Matrix ι ι ℂ) (t : Circle) (n : ℕ) :
    observe q (twist q t A) n=observe q A n := by
  ext I J
  rw [observe_twist]
  by_cases h : displacement q I J=0
  · rw [h,zpow_zero,one_mul]
  · rw [observe_entry,if_neg h,mul_zero]

/-- For Hermitian states the two-copy tensor entries give exactly the
charge-gap Gram data of the coefficient matrix and its adjoint. -/
theorem two_copy_gram (q : ι → ℤ) {A B : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (h : observe q A 2=observe q B 2) : pairedCharge q A=pairedCharge q B := by
  apply (pairedCharge_eq_iff_gram q A B).2
  intro i j k l he
  have hd : displacement q ![i,l] ![j,k]=0 := by
    simp [displacement,Fin.sum_univ_succ]
    omega
  have hh := congrArg (fun M : Matrix (Fin 2 → ι) (Fin 2 → ι) ℂ => M ![i,l] ![j,k]) h
  simp only [observe_entry,if_pos hd] at hh
  change A i j*star (A k l)=B i j*star (B k l)
  rw [hA.apply,hB.apply]
  simpa [Fin.prod_univ_succ] using hh

private def phaseBlock (q : ι → ℤ) (A B : Matrix ι ι ℂ) (n : ℕ) (a : ℤ) (z : Circle) :=
  ∃ I J : Fin n → ι, displacement q I J=a ∧ (∏ k, A (I k) (J k))≠0 ∧
    (∏ k, B (I k) (J k))=(z : ℂ)*∏ k, A (I k) (J k)

private theorem constant_block (q : ι → ℤ) {A B : Matrix ι ι ℂ} (i j : ι) (u : Circle)
    (ha : A i j≠0) (h : B i j=(u : ℂ)*A i j) (k : ℕ) :
    phaseBlock q A B k ((k : ℤ)*(q i-q j)) (u^k) := by
  refine ⟨fun _ => i,fun _ => j,?_,?_,?_⟩
  · exact constant_displacement q k i j
  · simpa using pow_ne_zero k ha
  · simp [h,mul_pow]

private theorem signed_block (q : ι → ℤ) {A B : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (e : Edge A) (φ : Circle)
    (h : B e.val.1 e.val.2=(φ : ℂ)*A e.val.1 e.val.2) (m : ℤ) :
    phaseBlock q A B m.natAbs (m*edgeGap q e) (φ^m) := by
  cases m with
  | ofNat k => exact constant_block q _ _ _ e.property h k
  | negSucc k =>
    have hr : A e.val.2 e.val.1≠0 := by
      intro he
      exact e.property (by rw [← hA.apply,he,star_zero])
    have hb : B e.val.2 e.val.1=((φ⁻¹ : Circle) : ℂ)*A e.val.2 e.val.1 := by
      calc
        B e.val.2 e.val.1 = conj (B e.val.1 e.val.2) := (hB.apply _ _).symm
        _ = _ := by rw [h,map_mul,← Circle.coe_inv_eq_conj]; congr 1; exact hA.apply _ _
    have hc := constant_block q _ _ _ hr hb (k+1)
    have ht : ((k+1 : ℕ) : ℤ)*(q e.val.2-q e.val.1)=(Int.negSucc k)*edgeGap q e := by
      simp only [edgeGap,Int.negSucc_eq,Int.natCast_succ]
      ring
    rw [ht] at hc
    simpa only [Int.natAbs_negSucc,Int.negSucc_eq,zpow_neg,zpow_natCast,inv_pow] using hc

/-- A balanced pair of signed edges forces the corresponding relation
on their measured phase ratios at precisely its copy cost. -/
theorem pair_ratio (q : ι → ℤ) {A B : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (φ : Edge A → Circle)
    (hφ : ∀ e, B e.val.1 e.val.2=(φ e : ℂ)*A e.val.1 e.val.2)
    (e f : Edge A) (a b : ℤ) (bal : a*edgeGap q e+b*edgeGap q f=0)
    (h : observe q A (a.natAbs+b.natAbs)=observe q B (a.natAbs+b.natAbs)) :
    (φ e)^a*(φ f)^b=1 := by
  obtain ⟨I,J,hq,hne,he⟩ := signed_block q hA hB e _ (hφ e) a
  obtain ⟨U,V,hq',hne',he'⟩ := signed_block q hA hB f _ (hφ f) b
  have hd : displacement q (Fin.addCases I U) (Fin.addCases J V)=0 := by
    simpa only [displacement,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right] using
      (show displacement q I J+displacement q U V=0 by rw [hq,hq',bal])
  have hh := congrArg (fun M : Matrix (Fin (a.natAbs+b.natAbs) → ι) (Fin (a.natAbs+b.natAbs) → ι) ℂ =>
    M (Fin.addCases I U) (Fin.addCases J V)) h
  simp only [observe_entry,if_pos hd,Fin.prod_univ_add,Fin.addCases_left,Fin.addCases_right,he,he'] at hh
  apply Circle.ext
  change (((φ e)^a : Circle) : ℂ)*(((φ f)^b : Circle) : ℂ)=1
  apply mul_right_cancel₀ (mul_ne_zero hne hne')
  rw [one_mul]
  linear_combination -hh

/-- The complete observation fiber through the universal bound is one
charge-rotation orbit, for arbitrary Hermitian matrices on the same basis. -/
theorem finite_state_fiber (q : ι → ℤ) {A B : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (Q : ℕ)
    (hQ : ∀ e : Edge A, (edgeGap q e / content (edgeGap q (A:=A))).natAbs≤Q) :
    (∀ n≤max 2 (2*Q-1), observe q A n=observe q B n) ↔ ∃ t : Circle, B=twist q t A := by
  constructor
  · intro h
    obtain ⟨u,hu,he⟩ := (pairedCharge_eq_iff_gap_phases q A B).1
      (two_copy_gram q hA hB (h 2 (le_max_left ..)))
    let φ (e : Edge A) : Circle := ⟨u (edgeGap q e),mem_sphere_zero_iff_norm.2 (hu _)⟩
    have hp (e : Edge A) : B e.val.1 e.val.2=(φ e : ℂ)*A e.val.1 e.val.2 := he _ _
    obtain ⟨t,ht⟩ := (finite_pair_iff (edgeGap q) φ Q hQ).1
      (fun e f a b hbal hn => pair_ratio q hA hB φ hp e f a b hbal (h _ hn))
    refine ⟨t,?_⟩
    ext i j
    by_cases hz : A i j=0
    · rw [he,twist,hz,mul_zero,mul_zero]
    · let e : Edge A := ⟨(i,j),hz⟩
      simpa only [ht,Circle.coe_zpow,e,edgeGap,twist] using hp e
  · rintro ⟨t,rfl⟩ n _
    exact (observe_charge_rotation q A t n).symm

/-- Partial trace of the shared-charge observation removes one copy
and multiplies the shorter observation by the original trace. -/
theorem observation_partial_trace (q : ι → ℤ) (A : Matrix ι ι ℂ) {n : ℕ} (I J : Fin n → ι) :
    (∑ i, observe q A (n+1) (Fin.cons i I) (Fin.cons i J))=A.trace*observe q A n I J := by
  have hd (i : ι) : displacement q (Fin.cons i I) (Fin.cons i J)=displacement q I J := by
    simp [displacement,Fin.sum_univ_succ]
  simp only [observe_entry,hd]
  split
  · simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,← sum_mul,trace,diag_apply]
  · simp only [sum_const_zero,mul_zero]

/-- At a common nonzero trace, equality of one observation implies
equality at every smaller copy count. -/
theorem shorter_observations (q : ι → ℤ) {A B : Matrix ι ι ℂ} (ht : A.trace=B.trace)
    (hne : A.trace≠0) {N : ℕ} (h : observe q A N=observe q B N) :
    ∀ n≤N, observe q A n=observe q B n := by
  induction N with
  | zero => intro n hn; obtain rfl := Nat.eq_zero_of_le_zero hn; exact h
  | succ N ih =>
    have prev : observe q A N=observe q B N := by
      ext I J
      apply mul_left_cancel₀ hne
      calc
        _ = ∑ i, observe q A (N+1) (Fin.cons i I) (Fin.cons i J) := (observation_partial_trace q A I J).symm
        _ = _ := by rw [h,observation_partial_trace,ht]
    intro n hn
    rcases lt_or_eq_of_le hn with hlt | rfl
    · exact ih prev n (Nat.le_of_lt_succ hlt)
    · exact h

/-- A single tensor observation at the stated bound recovers the full
orbit of any pair of Hermitian states of trace one. -/
theorem single_state_fiber (q : ι → ℤ) {A B : Matrix ι ι ℂ} (ha : A.IsHermitian) (hb : B.IsHermitian)
    (htA : A.trace=1) (htB : B.trace=1) (Q : ℕ)
    (hQ : ∀ e : Edge A, (edgeGap q e / content (edgeGap q (A:=A))).natAbs≤Q) :
    let N := max 2 (2*Q-1)
    observe q A N=observe q B N ↔ ∃ t : Circle, B=twist q t A := by
  intro N
  rw [← finite_state_fiber q ha hb Q hQ]
  exact ⟨shorter_observations q (htA.trans htB.symm) (by rw [htA]; exact one_ne_zero),
    fun h => h N le_rfl⟩

end GaloisForLFunctions.HTGeometry.Quantum.TensorObservation

#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.observe_charge_rotation
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.two_copy_gram
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.pair_ratio
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.finite_state_fiber
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.observation_partial_trace
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.shorter_observations
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.single_state_fiber
