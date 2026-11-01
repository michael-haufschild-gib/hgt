import Mathlib

/-! Finite monomials as symmetric multilinear forms. The top-degree permutation sum
determines the top homogeneous polynomial, including degree zero. -/

open Finset
open scoped Classical
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.DilationPolynomialPolarization
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- One slot for each occurrence of a variable in a monomial. -/
abbrev Slots (d : ι →₀ ℕ) := (i : ι) × Fin (d i)

def slotDegree (d : ι →₀ ℕ) : ℕ := Fintype.card (Slots d)

def monomialWord (d : ι →₀ ℕ) : Fin (slotDegree d) → ι :=
  fun j => ((Fintype.equivFin (Slots d)).symm j).1

theorem slotDegree_eq (d : ι →₀ ℕ) : slotDegree d = ∑ i, d i := by
  simp only [slotDegree,Fintype.card_sigma,Fintype.card_fin]

/-- Expanding a monomial into slots preserves its product exactly. -/
theorem prod_monomialWord (d : ι →₀ ℕ) (v : ι → ℂ) :
    (∏ j, v (monomialWord d j)) = ∏ i, v i ^ d i := by
  have he : (∏ j, v (monomialWord d j)) = ∏ s : Slots d, v s.1 := by
    exact Fintype.prod_equiv (Fintype.equivFin (Slots d)).symm _ _ (fun _ => rfl)
  rw [he,Fintype.prod_sigma]
  apply prod_congr rfl
  intro i _
  simp only [prod_const,card_univ,Fintype.card_fin]

def monomialMultilinear (d : ι →₀ ℕ) :
    MultilinearMap ℂ (fun _ : Fin (slotDegree d) => ι → ℂ) ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ (Fin (slotDegree d)) ℂ).compLinearMap
    (fun j => LinearMap.proj (monomialWord d j))

theorem monomialMultilinear_apply (d : ι →₀ ℕ)
    (v : Fin (slotDegree d) → ι → ℂ) :
    monomialMultilinear d v = ∏ j, v j (monomialWord d j) := rfl

def degreePiece (D : ℕ) (d : ι →₀ ℕ) :
    MultilinearMap ℂ (fun _ : Fin D => ι → ℂ) ℂ :=
  if h : slotDegree d = D then
    (monomialMultilinear d).domDomCongr (finCongr h)
  else 0

/-- Sum all slot permutations; its diagonal is `D!` times the degree-`D` monomial. -/
def symmetricDegreePiece (D : ℕ) (d : ι →₀ ℕ) :
    MultilinearMap ℂ (fun _ : Fin D => ι → ℂ) ℂ :=
  ∑ e : Equiv.Perm (Fin D), (degreePiece D d).domDomCongr e

def permutationMultiplicity (D : ℕ) : ℂ := Fintype.card (Equiv.Perm (Fin D))

theorem permutationMultiplicity_ne_zero (D : ℕ) : permutationMultiplicity D ≠ 0 := by
  unfold permutationMultiplicity
  exact_mod_cast (Fintype.card_ne_zero (α := Equiv.Perm (Fin D)))

theorem degreePiece_diagonal (D : ℕ) (d : ι →₀ ℕ) (v : ι → ℂ) :
    degreePiece D d (fun _ => v) =
      if slotDegree d = D then ∏ i, v i ^ d i else 0 := by
  by_cases h : slotDegree d = D
  · simp only [degreePiece,dif_pos h,if_pos h,MultilinearMap.domDomCongr_apply,
      monomialMultilinear_apply,prod_monomialWord]
  · simp only [degreePiece,dif_neg h,if_neg h]
    rfl

theorem symmetricDegreePiece_diagonal (D : ℕ) (d : ι →₀ ℕ) (v : ι → ℂ) :
    symmetricDegreePiece D d (fun _ => v) = permutationMultiplicity D *
      (if slotDegree d = D then ∏ i, v i ^ d i else 0) := by
  simp only [symmetricDegreePiece,_root_.sum_apply,
    MultilinearMap.domDomCongr_apply,degreePiece_diagonal,sum_const,card_univ,
    nsmul_eq_mul,permutationMultiplicity]

/-- The literal degree-`D` part, selected by monomial slot count. -/
def degreePolynomial (P : MvPolynomial ι ℂ) (D : ℕ) : MvPolynomial ι ℂ :=
  ∑ d ∈ P.support.filter (fun d => slotDegree d = D), MvPolynomial.monomial d (P.coeff d)

/-- The symmetric multilinear form whose diagonal recovers the degree-`D` part. -/
def polynomialMultilinear (P : MvPolynomial ι ℂ) (D : ℕ) :
    MultilinearMap ℂ (fun _ : Fin D => ι → ℂ) ℂ :=
  ∑ d ∈ P.support, P.coeff d • symmetricDegreePiece D d

private theorem eval_monomial_fintype (d : ι →₀ ℕ) (c : ℂ) (v : ι → ℂ) :
    MvPolynomial.eval v (MvPolynomial.monomial d c) = c * ∏ i, v i ^ d i := by
  rw [MvPolynomial.eval_monomial,Finsupp.prod_fintype d (fun i n => v i ^ n)
    (fun _ => pow_zero _)]

theorem eval_degreePolynomial (P : MvPolynomial ι ℂ) (D : ℕ) (v : ι → ℂ) :
    MvPolynomial.eval v (degreePolynomial P D) =
      ∑ d ∈ P.support, P.coeff d *
        (if slotDegree d = D then ∏ i, v i ^ d i else 0) := by
  simp only [degreePolynomial,map_sum,sum_filter]
  apply sum_congr rfl
  intro d _
  split_ifs
  · exact eval_monomial_fintype d (P.coeff d) v
  · simp only [map_zero,mul_zero]

/-- Top-degree polarization preserves every coefficient, with the nonzero permutation factor. -/
theorem polynomialMultilinear_diagonal (P : MvPolynomial ι ℂ) (D : ℕ) (v : ι → ℂ) :
    polynomialMultilinear P D (fun _ => v) =
      permutationMultiplicity D * MvPolynomial.eval v (degreePolynomial P D) := by
  simp only [polynomialMultilinear,_root_.sum_apply,_root_.smul_apply,
    smul_eq_mul,symmetricDegreePiece_diagonal,eval_degreePolynomial,mul_sum]
  apply sum_congr rfl
  intro d _
  ring

/-- Vanishing of the extracted multilinear form annihilates the entire homogeneous polynomial. -/
theorem degreePolynomial_eq_zero_of_polynomialMultilinear_eq_zero
    (P : MvPolynomial ι ℂ) (D : ℕ) (h : polynomialMultilinear P D = 0) :
    degreePolynomial P D = 0 := by
  apply MvPolynomial.funext
  intro v
  have he := polynomialMultilinear_diagonal P D v
  rw [h] at he
  have hz : permutationMultiplicity D * MvPolynomial.eval v (degreePolynomial P D) = 0 :=
    he.symm
  simpa only [map_zero] using (mul_eq_zero.mp hz).resolve_left
    (permutationMultiplicity_ne_zero D)

/-- Every supported monomial retains its coefficient in its own homogeneous component. -/
theorem coeff_degreePolynomial (P : MvPolynomial ι ℂ) (d : ι →₀ ℕ)
    (hd : d ∈ P.support) :
    (degreePolynomial P (slotDegree d)).coeff d = P.coeff d := by
  rw [degreePolynomial,MvPolynomial.coeff_sum,sum_eq_single d]
  · simp only [MvPolynomial.coeff_monomial,ite_true]
  · intro e _ hed
    simp only [MvPolynomial.coeff_monomial,if_neg hed]
  · intro hn
    exact (hn (mem_filter.mpr ⟨hd,rfl⟩)).elim

/-- Any nonzero coefficient forces a nonzero multilinear form in that degree. -/
theorem polynomialMultilinear_ne_zero (P : MvPolynomial ι ℂ) (d : ι →₀ ℕ)
    (hd : d ∈ P.support) : polynomialMultilinear P (slotDegree d) ≠ 0 := by
  intro hz
  have hp := degreePolynomial_eq_zero_of_polynomialMultilinear_eq_zero P (slotDegree d) hz
  have hc := coeff_degreePolynomial P d hd
  rw [hp,MvPolynomial.coeff_zero] at hc
  exact (MvPolynomial.mem_support_iff.mp hd) hc.symm

#print axioms prod_monomialWord
#print axioms permutationMultiplicity_ne_zero
#print axioms degreePiece_diagonal
#print axioms symmetricDegreePiece_diagonal
#print axioms eval_degreePolynomial
#print axioms polynomialMultilinear_diagonal
#print axioms degreePolynomial_eq_zero_of_polynomialMultilinear_eq_zero
#print axioms coeff_degreePolynomial
#print axioms polynomialMultilinear_ne_zero
end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.DilationPolynomialPolarization
