import GaloisForLFunctions.HTGeometry.Quantum.ChargeSectorPinching
import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Phase frequencies visible to a finite number of copies

A diagonal circle action assigns an independent integer weight to each basis
state. After total-charge pinching of a tensor power, every surviving matrix
entry is a single character of the circle. Its frequency is the difference
of total weights of the two basis words. This identifies the full stabilizer
of the observation, even when the coefficient matrix has zeros.
-/

noncomputable section
open Finset Matrix
open scoped ComplexOrder
namespace GaloisForLFunctions.HTGeometry.Quantum.TensorObservation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A diagonal change of phase weighted by integer labels. -/
def twist (b : ι → ℤ) (z : Circle) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => (z : ℂ)^(b i-b j)*A i j

private def phaseMatrix (b : ι → ℤ) (z : Circle) :=
  diagonal fun i => ((z^(b i) : Circle) : ℂ)

private theorem twist_eq_conjugate (b : ι → ℤ) (z : Circle) (A : Matrix ι ι ℂ) :
    twist b z A = phaseMatrix b z*A*(phaseMatrix b z)ᴴ := by
  ext i j
  simp only [phaseMatrix,diagonal_conjTranspose,diagonal_mul,mul_diagonal,twist]
  change (z : ℂ)^(b i-b j)*A i j = ((z^(b i) : Circle) : ℂ)*A i j*
    (starRingEnd ℂ) ((z^(b j) : Circle) : ℂ)
  rw [← Circle.coe_inv_eq_conj,Circle.coe_inv,Circle.coe_zpow,Circle.coe_zpow,
    zpow_sub₀ z.coe_ne_zero,div_eq_mul_inv]
  ac_rfl

/-- A phase twist is conjugation by a diagonal unitary, hence preserves the
positive cone. -/
theorem twist_posSemidef (b : ι → ℤ) (z : Circle) (A : Matrix ι ι ℂ) (h : A.PosSemidef) :
    (twist b z A).PosSemidef := by
  rw [twist_eq_conjugate]
  exact h.mul_mul_conjTranspose_same _

/-- Every phase on the observation orbit has the same spectrum with multiplicity. -/
theorem twist_charpoly (b : ι → ℤ) (z : Circle) (A : Matrix ι ι ℂ) :
    (twist b z A).charpoly = A.charpoly := by
  have hu : (phaseMatrix b z)ᴴ * phaseMatrix b z = 1 := by
    rw [phaseMatrix,diagonal_conjTranspose,diagonal_mul_diagonal]
    change diagonal (fun i => (starRingEnd ℂ) ((z^(b i) : Circle) : ℂ) *
      ((z^(b i) : Circle) : ℂ)) = 1
    simp only [← Circle.coe_inv_eq_conj,← Circle.coe_mul,inv_mul_cancel,Circle.coe_one]
    rfl
  rw [twist_eq_conjugate,charpoly_mul_comm _ (phaseMatrix b z)ᴴ,← Matrix.mul_assoc,hu,one_mul]

omit [DecidableEq ι] in
theorem twist_trace (b : ι → ℤ) (z : Circle) (A : Matrix ι ι ℂ) :
    (twist b z A).trace=A.trace := by
  simp [trace,diag_apply,twist]

/-- The tensor power with one shared charge reference. -/
def observe (q : ι → ℤ) (A : Matrix ι ι ℂ) (n : ℕ) :
    Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  chargePinch (fun u => ∑ k, q (u k)) (fun u v => ∏ k, A (u k) (v k))

/-- Total displacement along an integer grading. -/
def displacement {n : ℕ} (b : ι → ℤ) (u v : Fin n → ι) : ℤ :=
  ∑ k, (b (u k)-b (v k))

theorem observe_entry (q : ι → ℤ) (A : Matrix ι ι ℂ) {n : ℕ} (u v : Fin n → ι) :
    observe q A n u v = if displacement q u v = 0 then ∏ k, A (u k) (v k) else 0 := by
  rw [observe,chargePinch_apply]
  simp only [displacement,sum_sub_distrib,sub_eq_zero]

private theorem phase_product {α : Type*} (s : Finset α) (f : α → ℤ) (z : Circle) :
    (∏ k ∈ s, (z : ℂ)^(f k)) = (z : ℂ)^(∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [prod_insert hk,sum_insert hk,ih,zpow_add₀ z.coe_ne_zero]

/-- Each entry transforms by its total weight difference, including after pinching. -/
theorem observe_twist (q b : ι → ℤ) (A : Matrix ι ι ℂ) (z : Circle)
    {n : ℕ} (u v : Fin n → ι) :
    observe q (twist b z A) n u v =
      (z : ℂ)^(displacement b u v) * observe q A n u v := by
  simp only [observe_entry]
  split
  · simp only [twist,prod_mul_distrib,phase_product,displacement]
  · rw [mul_zero]

/-- The active frequencies are the weight differences of pairs of equally charged
words whose matched one-copy entries all survive. -/
def frequencies (q b : ι → ℤ) (A : Matrix ι ι ℂ) (n : ℕ) : Finset ℤ := by
  classical
  exact (univ.filter (fun p : (Fin n → ι) × (Fin n → ι) =>
    displacement q p.1 p.2 = 0 ∧ ∀ k, A (p.1 k) (p.2 k) ≠ 0)).image
    (fun p => displacement b p.1 p.2)

private theorem nonzero_word (q : ι → ℤ) (A : Matrix ι ι ℂ) {n : ℕ} (u v : Fin n → ι) :
    observe q A n u v ≠ 0 ↔ displacement q u v=0 ∧ ∀ k, A (u k) (v k) ≠ 0 := by
  rw [observe_entry]
  by_cases h : displacement q u v=0
  · simp only [h,if_pos,true_and,prod_ne_zero_iff,mem_univ,true_implies]
  · simp [h]

theorem frequency_iff (q b : ι → ℤ) (A : Matrix ι ι ℂ) (n : ℕ) (d : ℤ) :
    d ∈ frequencies q b A n ↔ ∃ u v : Fin n → ι,
      observe q A n u v ≠ 0 ∧ displacement b u v = d := by
  classical
  simp only [frequencies,mem_image,mem_filter,mem_univ,true_and,Prod.exists,← nonzero_word]

/-- Concatenating nonzero balanced words adds their frequencies and their
copy counts. Oppositely charged factors may create further frequencies. -/
theorem add_frequency (q b : ι → ℤ) (A : Matrix ι ι ℂ) {m n : ℕ} {d e : ℤ}
    (hd : d ∈ frequencies q b A m) (he : e ∈ frequencies q b A n) :
    d+e ∈ frequencies q b A (m+n) := by
  obtain ⟨u,v,hu,rfl⟩ := (frequency_iff _ _ _ _ _).1 hd
  obtain ⟨U,V,hU,rfl⟩ := (frequency_iff _ _ _ _ _).1 he
  obtain ⟨hq,hA⟩ := (nonzero_word q A u v).1 hu
  obtain ⟨hQ,hB⟩ := (nonzero_word q A U V).1 hU
  have hsum (a : ι → ℤ) :
      displacement a (Fin.addCases u U) (Fin.addCases v V) = displacement a u v + displacement a U V := by
    simp only [displacement,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right]
  refine (frequency_iff _ _ _ _ _).2 ⟨Fin.addCases u U,Fin.addCases v V,?_,hsum b⟩
  apply (nonzero_word _ _ _ _).2
  refine ⟨by rw [hsum,hq,hQ,add_zero],?_⟩
  intro k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa only [Fin.addCases_left] using hA i
  · simpa only [Fin.addCases_right] using hB j

/-- Repeating a balanced word realizes every positive multiple with the
corresponding multiple of the original copy count. -/
theorem multiple_frequency (q b : ι → ℤ) (A : Matrix ι ι ℂ) {n : ℕ} {d : ℤ}
    (hd : d ∈ frequencies q b A n) (k : ℕ) : (k : ℤ)*d ∈ frequencies q b A (k*n) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero,zero_mul]
    apply (frequency_iff _ _ _ _ _).2
    exact ⟨Fin.elim0,Fin.elim0,by simp [observe_entry,displacement],by simp [displacement]⟩
  | succ k ih =>
    simpa only [Nat.cast_succ,add_mul,one_mul,Nat.succ_mul] using add_frequency q b A ih hd

/-- Exchanging the two words reverses the frequency for the transposed support. -/
theorem transpose_frequency (q b : ι → ℤ) (A : Matrix ι ι ℂ) {n : ℕ} {d : ℤ}
    (hd : d ∈ frequencies q b A n) : -d ∈ frequencies q b A.transpose n := by
  obtain ⟨u,v,hu,rfl⟩ := (frequency_iff _ _ _ _ _).1 hd
  obtain ⟨hq,hA⟩ := (nonzero_word q A u v).1 hu
  have swap (a : ι → ℤ) : displacement a v u = -displacement a u v := by
    simp only [displacement,sum_sub_distrib,neg_sub]
  refine (frequency_iff _ _ _ _ _).2 ⟨v,u,(nonzero_word _ _ _ _).2 ⟨?_,hA⟩,swap b⟩
  rw [swap,hq,neg_zero]

/-- Two phases give exactly the same observation when their characters agree
on every active frequency. -/
theorem indistinguishable_iff (q b : ι → ℤ) (A : Matrix ι ι ℂ) (n : ℕ) (z w : Circle) :
    observe q (twist b z A) n = observe q (twist b w A) n ↔
      ∀ d ∈ frequencies q b A n, z^d=w^d := by
  constructor
  · intro he d hd
    obtain ⟨u,v,hne,rfl⟩ := (frequency_iff q b A n d).1 hd
    have h := congrArg (fun M : Matrix (Fin n → ι) (Fin n → ι) ℂ => M u v) he
    simp only [observe_twist] at h
    exact Subtype.ext (mul_right_cancel₀ hne h)
  · intro h
    ext u v
    rw [observe_twist,observe_twist]
    by_cases hz : observe q A n u v=0
    · rw [hz,mul_zero,mul_zero]
    · have he := h _ ((frequency_iff q b A n _).2 ⟨u,v,hz,rfl⟩)
      exact congrArg (fun c : Circle => (c : ℂ)*observe q A n u v) he

/-- A nonzero diagonal entry pads either word equally. Once a frequency
is visible it stays visible at every greater number of copies. -/
theorem frequencies_mono (q b : ι → ℤ) (A : Matrix ι ι ℂ) (i : ι) (hi : A i i ≠ 0)
    (n : ℕ) : frequencies q b A n ⊆ frequencies q b A (n+1) := by
  intro d hd
  obtain ⟨u,v,hne,he⟩ := (frequency_iff q b A n d).1 hd
  apply (frequency_iff q b A (n+1) d).2
  have hdisp (a : ι → ℤ) :
      displacement a (Fin.cons i u) (Fin.cons i v) = displacement a u v := by
    simp [displacement,Fin.sum_univ_succ]
  refine ⟨Fin.cons i u,Fin.cons i v,?_,(hdisp b).trans he⟩
  rw [observe_entry] at hne ⊢
  rw [hdisp]
  split at hne <;> rename_i h
  · rw [if_pos h,Fin.prod_univ_succ]
    exact mul_ne_zero hi hne
  · exact (hne rfl).elim

end GaloisForLFunctions.HTGeometry.Quantum.TensorObservation

#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.twist_posSemidef
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.twist_trace
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.observe_entry
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.observe_twist
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.frequency_iff
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.add_frequency
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.multiple_frequency
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.transpose_frequency
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.indistinguishable_iff
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.frequencies_mono

#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.twist_charpoly
