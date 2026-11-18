import GaloisForLFunctions.HTGeometry.Quantum.ChargeSectorPinching
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Complex.Circle

/-!
# Two-copy observations under a total-charge rule

Vaughan's superselection rule (arXiv:2611.17051, §§2.4 and 4) removes
coherences between distinct charges. With a shared reference the two copies
carry one total charge. Their surviving entries record all pairwise products
inside each charge-difference class, determining that class up to one phase.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.Quantum
open Matrix
open scoped Kronecker ComplexConjugate

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup κ] [DecidableEq κ]

/-- The observation of a coefficient matrix and its adjoint with a common charge reference. -/
def pairedCharge (q : ι → κ) (A : Matrix ι ι ℂ) : Matrix (ι × ι) (ι × ι) ℂ :=
  chargePinch (fun p : ι × ι => q p.1 + q p.2) (A ⊗ₖ A.conjTranspose)

/-- Equal charge differences are exactly the pairs retaining their relative phase. -/
theorem pairedCharge_entry (q : ι → κ) (A : Matrix ι ι ℂ) (i j k l : ι) :
    pairedCharge q A (i,l) (j,k) =
      if q i - q j = q k - q l then A i j * conj (A k l) else 0 := by
  have h : q i + q l = q j + q k ↔ q i - q j = q k - q l := by
    rw [sub_eq_sub_iff_add_eq_add]
    constructor <;> intro he <;> simpa only [add_comm (q j) (q k)] using he
  simp only [pairedCharge, chargePinch_apply, h, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply]
  rfl

/-- Even a single entry invisible to one copy leaves its squared amplitude in the swap entry. -/
theorem pairedCharge_swap (q : ι → κ) (A : Matrix ι ι ℂ) (i j : ι) :
    pairedCharge q A (i,j) (j,i) = (Complex.normSq (A i j) : ℂ) := by
  rw [pairedCharge_entry, if_pos rfl, Complex.mul_conj]

/-- Two-copy equality is exactly equality of the Gram matrices on every charge gap. -/
theorem pairedCharge_eq_iff_gram (q : ι → κ) (A B : Matrix ι ι ℂ) :
    pairedCharge q A = pairedCharge q B ↔
      ∀ i j k l, q i - q j = q k - q l →
        A i j * conj (A k l) = B i j * conj (B k l) := by
  constructor
  · intro h i j k l hd
    have he := congrArg (fun M : Matrix (ι × ι) (ι × ι) ℂ => M (i,l) (j,k)) h
    simpa only [pairedCharge_entry, if_pos hd] using he
  · intro H
    ext ⟨i,l⟩ ⟨j,k⟩
    simp only [pairedCharge_entry]
    split
    · exact H _ _ _ _ ‹_›
    · rfl

private theorem gram_phase {α : Type*} (f g : α → ℂ)
    (h : ∀ i j, f i * conj (f j) = g i * conj (g j)) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ i, g i = u * f i := by
  have hn (i : α) : ‖f i‖ = ‖g i‖ := by
    have he := congrArg norm (h i i)
    simp only [norm_mul, Complex.norm_conj] at he
    nlinarith only [he, norm_nonneg (f i), norm_nonneg (g i)]
  by_cases hz : ∀ i, f i = 0
  · refine ⟨1, norm_one, fun i => ?_⟩
    have he := (hn i).symm
    rw [hz i, norm_zero, norm_eq_zero] at he
    simp [hz i, he]
  · push Not at hz
    obtain ⟨j,hj⟩ := hz
    have hgj : g j ≠ 0 := norm_ne_zero_iff.mp ((hn j) ▸ norm_ne_zero_iff.mpr hj)
    refine ⟨conj (f j) / conj (g j), ?_, fun i => ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_conj, hn j, div_self (norm_ne_zero_iff.mpr hgj)]
    · have hg : conj (g j) ≠ 0 := by simpa using hgj
      field_simp [hg]
      linear_combination -(h i j)

/-- A complete classification: each charge gap has exactly one undetectable unit phase
on its nonzero coefficients. Empty and identically zero gaps need no distinguished phase. -/
theorem pairedCharge_eq_iff_gap_phases (q : ι → κ) (A B : Matrix ι ι ℂ) :
    pairedCharge q A = pairedCharge q B ↔
      ∃ u : κ → ℂ, (∀ d, ‖u d‖ = 1) ∧ ∀ i j, B i j = u (q i - q j) * A i j := by
  rw [pairedCharge_eq_iff_gram]
  constructor
  · intro H
    have hex (d : κ) := gram_phase
      (fun p : {p : ι × ι // q p.1 - q p.2 = d} => A p.val.1 p.val.2)
      (fun p => B p.val.1 p.val.2)
      (fun i j => H _ _ _ _ (i.property.trans j.property.symm))
    choose u hu he using hex
    exact ⟨u, hu, fun i j => he _ ⟨(i,j),rfl⟩⟩
  · rintro ⟨u,hu,he⟩ i j k l hd
    rw [he i j, he k l, hd, map_mul]
    have hnorm : u (q k - q l) * conj (u (q k - q l)) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
      simp
    linear_combination -(A i j * conj (A k l)) * hnorm

/-- Pinching the two copies separately loses information exactly when one-copy
off-charge coefficients were present. -/
theorem pairedCharge_eq_after_pinching_iff (q : ι → κ) (A : Matrix ι ι ℂ) :
    pairedCharge q A = pairedCharge q (chargePinch q A) ↔ chargePinch q A = A := by
  constructor
  · intro he
    apply (chargePinch_eq_self_iff q A).2
    intro i j hij
    have h := congrArg (fun M : Matrix (ι × ι) (ι × ι) ℂ => M (i,j) (j,i)) he
    simp only [pairedCharge_swap, chargePinch_apply, if_neg hij, Complex.normSq_zero,
      Complex.ofReal_zero, Complex.ofReal_eq_zero, Complex.normSq_eq_zero] at h
    exact h
  · intro h
    rw [h]

/-- A gap is occupied when it carries a nonzero coefficient. -/
def occupiedGap (q : ι → κ) (A : Matrix ι ι ℂ) (d : κ) : Prop :=
  ∃ i j, q i - q j = d ∧ A i j ≠ 0

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- On occupied gaps the unit phase recovered from two copies is unique. -/
theorem gap_phase_unique (q : ι → κ) (A B : Matrix ι ι ℂ) (d : κ) :
    occupiedGap q A d →
      ∀ u v : ℂ, (∀ i j, q i-q j = d → B i j = u*A i j) →
        (∀ i j, q i-q j = d → B i j = v*A i j) → u = v := by
  rintro ⟨i,j,hd,hA⟩ u v hu hv
  exact mul_right_cancel₀ hA ((hu i j hd).symm.trans (hv i j hd))

/-- Three copies retain products whose first two charge gaps sum to the third. -/
def tripleCharge (q : ι → κ) (A : Matrix ι ι ℂ) :
    Matrix ((ι × ι) × ι) ((ι × ι) × ι) ℂ :=
  chargePinch (fun p : (ι × ι) × ι => q p.1.1 + q p.1.2 + q p.2)
    ((A ⊗ₖ A) ⊗ₖ A.conjTranspose)

theorem tripleCharge_entry (q : ι → κ) (A : Matrix ι ι ℂ) (i j k l r s : ι) :
    tripleCharge q A ((i,k),s) ((j,l),r) =
      if (q i-q j)+(q k-q l) = q r-q s then A i j*A k l*conj (A r s) else 0 := by
  have he : q i+q k+q s = q j+q l+q r ↔ (q i-q j)+(q k-q l) = q r-q s := by
    rw [← sub_eq_zero, ← sub_eq_zero (a := (q i-q j)+(q k-q l))]
    abel_nf
  simp only [tripleCharge, chargePinch_apply, he, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply]
  rfl

/-- Three-copy observations impose the character law precisely on occupied additive
triples of gaps. Gaps absent from the matrix impose no phase conditions. -/
theorem tripleCharge_eq_iff_phase_add (q : ι → κ) (A : Matrix ι ι ℂ) (u : κ → Circle) :
    tripleCharge q A = tripleCharge q (fun i j => (u (q i-q j) : ℂ)*A i j) ↔
      ∀ d e, occupiedGap q A d → occupiedGap q A e → occupiedGap q A (d+e) →
        u (d+e) = u d * u e := by
  have unit (d : κ) : conj (u d : ℂ) * (u d : ℂ) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    simp
  constructor
  · rintro H d e ⟨i,j,hij,ha⟩ ⟨k,l,hkl,hb⟩ ⟨r,s,hrs,hc⟩
    have h := congrArg (fun M : Matrix ((ι × ι) × ι) ((ι × ι) × ι) ℂ =>
      M ((i,k),s) ((j,l),r)) H
    simp only [tripleCharge_entry,hij,hkl,hrs,if_true,map_mul] at h
    have hne : A i j*A k l*conj (A r s) ≠ 0 := mul_ne_zero (mul_ne_zero ha hb) (by simpa using hc)
    apply Subtype.ext
    change (u (d+e) : ℂ) = (u d : ℂ)*(u e : ℂ)
    apply mul_right_cancel₀ hne
    linear_combination (u (d+e) : ℂ) * h +
      ((u d : ℂ)*(u e : ℂ)*(A i j*A k l*conj (A r s))) * unit (d+e)
  · intro H
    ext ⟨⟨i,k⟩,s⟩ ⟨⟨j,l⟩,r⟩
    simp only [tripleCharge_entry]
    split
    · rename_i he
      by_cases ha : A i j = 0
      · simp [ha]
      by_cases hb : A k l = 0
      · simp [hb]
      by_cases hc : A r s = 0
      · simp [hc]
      have hu := H _ _ ⟨i,j,rfl,ha⟩ ⟨k,l,rfl,hb⟩ ⟨r,s,he.symm,hc⟩
      have hval := congrArg (fun z : Circle => (z : ℂ)) hu
      rw [he] at hval
      change (u (q r-q s) : ℂ) = (u (q i-q j) : ℂ)*(u (q k-q l) : ℂ) at hval
      rw [map_mul]
      linear_combination -(A i j*A k l*conj (A r s)) * unit (q r-q s) +
        (A i j*A k l*conj (A r s)*conj (u (q r-q s) : ℂ)) * hval
    · rfl

end GaloisForLFunctions.HTGeometry.Quantum

#print axioms GaloisForLFunctions.HTGeometry.Quantum.pairedCharge_entry
#print axioms GaloisForLFunctions.HTGeometry.Quantum.pairedCharge_swap
#print axioms GaloisForLFunctions.HTGeometry.Quantum.pairedCharge_eq_iff_gram
#print axioms GaloisForLFunctions.HTGeometry.Quantum.pairedCharge_eq_iff_gap_phases
#print axioms GaloisForLFunctions.HTGeometry.Quantum.pairedCharge_eq_after_pinching_iff
#print axioms GaloisForLFunctions.HTGeometry.Quantum.gap_phase_unique
#print axioms GaloisForLFunctions.HTGeometry.Quantum.tripleCharge_entry
#print axioms GaloisForLFunctions.HTGeometry.Quantum.tripleCharge_eq_iff_phase_add
