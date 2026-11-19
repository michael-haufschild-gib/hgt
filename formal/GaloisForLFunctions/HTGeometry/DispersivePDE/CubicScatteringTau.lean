import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchySolitonScattering
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# A determinant for the positive-momentum Hirota tau polynomial

In Shi's cubic family the coefficient of a subset of waves is the product
of their pair phases. It is exactly a principal minor of the weighted
Cauchy coherence matrix. The degree therefore counts distinct momenta,
even when the wave amplitudes at a repeated momentum are different.
-/

noncomputable section
open Finset Matrix Polynomial
open GaloisForLFunctions.HilbertMetric.CauchyDephasing
namespace GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScattering

/-- A wave amplitude weights its row of the Cauchy kernel. -/
def waveMatrix {n : ℕ} (r a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.exp (a i)*coherence (r i) (r j)

/-- The power of X counts occupied waves. -/
def tauPolynomial {n : ℕ} (r a : Fin n → ℝ) : ℝ[X] :=
  (1 + (X : ℝ[X]) • (waveMatrix r a).map C).det

private def nodes {n : ℕ} (s : Finset (Fin n)) (r : Fin n → ℝ) (i : Fin s.card) :=
  r ((s.orderIsoOfFin rfl) i)

/-- Exponential amplitudes times all pair transmission factors on one subset. -/
def waveTerm {n : ℕ} (r a : Fin n → ℝ) (s : Finset (Fin n)) : ℝ :=
  (∏ i : Fin s.card, Real.exp (nodes s a i)) *
    ∏ i, ∏ j ∈ Ioi i, contrast (nodes s r j) (nodes s r i)^2

private theorem term_minor {n : ℕ} (r a : Fin n → ℝ) (s : Finset (Fin n)) :
    ((waveMatrix r a).submatrix (Subtype.val : s → Fin n) Subtype.val).det = waveTerm r a s := by
  rw [← Matrix.det_submatrix_equiv_self (s.orderIsoOfFin rfl).toEquiv]
  change (Matrix.of fun i j : Fin s.card => Real.exp (nodes s a i) *
    (Matrix.of fun k l => coherence (nodes s r k) (nodes s r l)) i j).det = _
  rw [Matrix.det_mul_column,coherence_det_eq_scattering]
  rfl

/-- Every coefficient is exactly the corresponding Hirota subset sum. -/
theorem tau_coefficient {n : ℕ} (r a : Fin n → ℝ) (k : ℕ) :
    (tauPolynomial r a).coeff k =
      ∑ s ∈ (univ : Finset (Fin n)).powersetCard k, waveTerm r a s := by
  simp only [tauPolynomial,Matrix.coeff_det_one_add_X_smul_eq_sum_minors,term_minor]

private theorem term_nonneg {n : ℕ} (r a : Fin n → ℝ) (s : Finset (Fin n)) :
    0 ≤ waveTerm r a s :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
    (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => sq_nonneg _)

private theorem term_pos_iff {n : ℕ} (r a : Fin n → ℝ) (s : Finset (Fin n)) :
    0 < waveTerm r a s ↔ Set.InjOn r (s : Set (Fin n)) := by
  have hprod : 0 < ∏ i : Fin s.card, Real.exp (nodes s a i) := Finset.prod_pos fun _ _ => Real.exp_pos _
  rw [lt_iff_le_and_ne, and_iff_right (term_nonneg r a s),ne_comm, waveTerm,
    ← coherence_det_eq_scattering, mul_ne_zero_iff, and_iff_right hprod.ne', coherence_det_ne_zero_iff]
  let e := s.orderIsoOfFin rfl
  constructor
  · intro h x hx y hy hxy
    let a' : s := ⟨x,hx⟩
    let b' : s := ⟨y,hy⟩
    have h' : nodes s r (e.symm a') = nodes s r (e.symm b') := by
      simpa only [nodes, ← show e = s.orderIsoOfFin rfl from rfl, e.apply_symm_apply] using hxy
    simpa only [e.apply_symm_apply] using congrArg (fun i => (e i : Fin n)) (h h')
  · intro h i j hij
    apply e.injective
    exact Subtype.ext (h (e i).property (e j).property hij)

/-- The degree-k coefficient is strictly positive precisely while k distinct
momenta can be chosen. Repeated labels cause no cancellation among survivors. -/
theorem tau_coefficient_pos_iff {n : ℕ} (r a : Fin n → ℝ) (k : ℕ) :
    0 < (tauPolynomial r a).coeff k ↔ k ≤ (univ.image r).card := by
  classical
  rw [tau_coefficient]
  have hnon (s : Finset (Fin n)) (_ : s ∈ (univ : Finset (Fin n)).powersetCard k) :
      0 ≤ waveTerm r a s := term_nonneg r a s
  constructor
  · intro h
    by_contra! hk
    have hz (s : Finset (Fin n)) (hs : s ∈ (univ : Finset (Fin n)).powersetCard k) : waveTerm r a s = 0 := by
      apply le_antisymm _ (term_nonneg r a s)
      apply le_of_not_gt
      intro hp
      have hinj := (term_pos_iff r a s).mp hp
      have hle := Finset.card_le_card (Finset.image_subset_image (f := r) (Finset.subset_univ s))
      rw [Finset.card_image_of_injOn hinj,(mem_powersetCard.mp hs).2] at hle
      omega
    rw [Finset.sum_eq_zero hz] at h
    exact h.false
  · intro hk
    have hsur : Set.SurjOn r Set.univ (↑(univ.image r) : Set ℝ) := by
      intro y hy
      obtain ⟨i,_,hi⟩ := mem_image.mp hy
      exact ⟨i,Set.mem_univ _,hi⟩
    obtain ⟨s,_,hi,he⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn Set.univ (univ.image r) hsur
    rw [← he, Finset.card_image_of_injOn hi] at hk
    obtain ⟨t,ht,hk'⟩ := Finset.exists_subset_card_eq hk
    exact Finset.sum_pos' hnon ⟨t,mem_powersetCard.mpr ⟨subset_univ _,hk'⟩,
      (term_pos_iff r a t).mpr (hi.mono ht)⟩

/-- The exact polynomial degree is the number of distinct momenta. -/
theorem tau_natDegree {n : ℕ} (r a : Fin n → ℝ) :
    (tauPolynomial r a).natDegree = (univ.image r).card := by
  classical
  apply le_antisymm
  · by_contra! h
    have hn : (tauPolynomial r a) ≠ 0 := by
      intro hz
      have hp := (tau_coefficient_pos_iff r a 0).mpr (Nat.zero_le _)
      rw [hz,Polynomial.coeff_zero] at hp
      exact hp.false
    have hlead : (tauPolynomial r a).coeff (tauPolynomial r a).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hn
    have hnon : 0 ≤ (tauPolynomial r a).coeff (tauPolynomial r a).natDegree := by
      rw [tau_coefficient]
      exact Finset.sum_nonneg fun s _ => term_nonneg r a s
    exact h.not_ge ((tau_coefficient_pos_iff r a _).mp (lt_of_le_of_ne hnon hlead.symm))
  · exact Polynomial.le_natDegree_of_ne_zero ((tau_coefficient_pos_iff r a _).mpr le_rfl).ne'

/-- At physical amplitude X = 1 the determinant is the complete tau sum. -/
theorem tau_determinant {n : ℕ} (r a : Fin n → ℝ) :
    (1 + waveMatrix r a).det = ∑ s : Finset (Fin n), waveTerm r a s := by
  classical
  let M := waveMatrix r a
  let D := (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^(Fin n)]→ₗ[ℝ] ℝ)
  change (1+M).det = _
  rw [add_comm]
  refine (D.map_add_univ M.row (1 : Matrix (Fin n) (Fin n) ℝ).row).trans ?_
  apply Finset.sum_congr rfl
  intro s _
  exact (Matrix.det_piecewise_one_eq_submatrix_det M s).trans (term_minor r a s)

/-- The constant term prevents a zero of the positive-amplitude tau function,
also at repeated momenta. -/
theorem tau_at_least_one {n : ℕ} (r a : Fin n → ℝ) : 1 ≤ (1+waveMatrix r a).det := by
  rw [tau_determinant]
  have h := Finset.single_le_sum (f := waveTerm r a) (fun s _ => term_nonneg r a s) (Finset.mem_univ ∅)
  simpa [waveTerm] using h

#print axioms tau_coefficient
#print axioms tau_coefficient_pos_iff
#print axioms tau_natDegree
#print axioms tau_determinant
#print axioms tau_at_least_one
end GaloisForLFunctions.HTGeometry.DispersivePDE.CubicScattering
