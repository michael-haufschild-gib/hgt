import Mathlib
import GaloisForLFunctions.HTGeometry.HermitianInertia

/-!
# Exact inertia conservation for the complete atomic block fusion

Finitely many source atoms carry Hermitian channel matrices `A x`.  Evaluating the channel
polynomials at pairwise distinct nodes `z x` fuses the atoms into a single block matrix

`F (i,a) (j,b) = ∑_x conj (z x ^ i) * z x ^ j * A x a b`,

which is exactly the block Hankel matrix when the nodes are real (`z x = λ x`, so the entry is the
moment `M_{i+j}`) and the complete finite Fourier block when the nodes are unimodular.

The fusion is an invertible congruence of the block-diagonal atom matrix.  By Sylvester's law of
inertia the fused block therefore has the componentwise sum of the atom inertia triples: negative
spectral channels cannot cancel between atoms at full interpolation depth.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Complex

noncomputable section

variable {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

/-- The block-diagonal matrix of the atom interventions. -/
def atomDiag (A : Fin N → Matrix E E ℂ) : Matrix (Fin N × E) (Fin N × E) ℂ :=
  fun p q => if p.1 = q.1 then A p.1 p.2 q.2 else 0

/-- The complete evaluation matrix: row `(x,a)` reads the `a`-th channel of the coefficient
vector at the node `z x`. -/
def evalMatrix (E : Type*) [Fintype E] [DecidableEq E] {N : ℕ} (z : Fin N → ℂ) :
    Matrix (Fin N × E) (Fin N × E) ℂ :=
  fun p q => if p.2 = q.2 then z p.1 ^ (q.1 : ℕ) else 0

/-! ### The block-diagonal calculus -/

omit [DecidableEq E] in
theorem atomDiag_mul (A B : Fin N → Matrix E E ℂ) :
    atomDiag A * atomDiag B = atomDiag (fun x => A x * B x) := by
  ext p q
  simp only [atomDiag, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single p.1]
  · by_cases h : p.1 = q.1
    · simp [h]
    · simp [h]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

omit [Fintype E] [DecidableEq E] in
theorem atomDiag_conjTranspose (A : Fin N → Matrix E E ℂ) :
    (atomDiag A)ᴴ = atomDiag (fun x => (A x)ᴴ) := by
  ext p q
  simp only [atomDiag, Matrix.conjTranspose_apply]
  by_cases h : p.1 = q.1
  · rw [h]
    simp
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp

omit [Fintype E] in
theorem atomDiag_diagonal (μ : Fin N → E → ℂ) :
    atomDiag (fun x => diagonal (μ x)) = diagonal (fun p : Fin N × E => μ p.1 p.2) := by
  ext p q
  simp only [atomDiag, Matrix.diagonal_apply, Prod.ext_iff]
  by_cases h1 : p.1 = q.1
  · by_cases h2 : p.2 = q.2 <;> simp [h1, h2]
  · simp [h1]

omit [Fintype E] in
theorem atomDiag_one : atomDiag (fun _ : Fin N => (1 : Matrix E E ℂ)) = 1 := by
  ext p q
  simp only [atomDiag, Matrix.one_apply, Prod.ext_iff]
  by_cases h1 : p.1 = q.1
  · by_cases h2 : p.2 = q.2 <;> simp [h1, h2]
  · simp [h1]

theorem isUnit_atomDiag {A : Fin N → Matrix E E ℂ} (h : ∀ x, IsUnit (A x)) :
    IsUnit (atomDiag A) := by
  refine ⟨⟨atomDiag A, atomDiag (fun x => ((h x).unit⁻¹ : (Matrix E E ℂ)ˣ)), ?_, ?_⟩, rfl⟩
  · rw [atomDiag_mul, ← atomDiag_one]
    congr 1
    funext x
    exact (h x).mul_val_inv
  · rw [atomDiag_mul, ← atomDiag_one]
    congr 1
    funext x
    exact (h x).val_inv_mul

/-! ### The evaluation congruence -/

theorem evalMatrix_mulVec (z : Fin N → ℂ) (v : Fin N × E → ℂ) (p : Fin N × E) :
    (evalMatrix E z *ᵥ v) p = ∑ j : Fin N, z p.1 ^ (j : ℕ) * v (j, p.2) := by
  simp only [Matrix.mulVec, dotProduct, evalMatrix, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_eq_single p.2]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem isUnit_evalMatrix {z : Fin N → ℂ} (hz : Function.Injective z) :
    IsUnit (evalMatrix E z) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨p, hp⟩ : ∃ p, v p ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hv0 (funext hc)
  have hvan : Matrix.vandermonde z *ᵥ (fun j => v (j, p.2)) = 0 := by
    funext x
    have hx := congrFun hv (x, p.2)
    rw [evalMatrix_mulVec] at hx
    simpa [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply] using hx
  have hvne : (Matrix.vandermonde z).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hz
  have hzero : (fun j => v (j, p.2)) = 0 := by
    by_contra hc
    exact hvne (Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hc, hvan⟩)
  exact hp (by simpa using congrFun hzero p.1)

/-- The evaluation congruence of the block-diagonal atom matrix is the complete fused block. -/
theorem evalMatrix_conjugate_atomDiag (z : Fin N → ℂ) (A : Fin N → Matrix E E ℂ)
    (p q : Fin N × E) :
    ((evalMatrix E z)ᴴ * atomDiag A * evalMatrix E z) p q =
      ∑ x : Fin N, (starRingEnd ℂ) (z x ^ (p.1 : ℕ)) * z x ^ (q.1 : ℕ) * A x p.2 q.2 := by
  have hstep : ∀ r : Fin N × E,
      (atomDiag A * evalMatrix E z) r q = A r.1 r.2 q.2 * z r.1 ^ (q.1 : ℕ) := by
    intro r
    simp only [atomDiag, evalMatrix, Matrix.mul_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single r.1]
    · rw [Finset.sum_eq_single q.2]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, hstep, Matrix.conjTranspose_apply, evalMatrix,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single p.2]
  · simp
    ring
  · intro b _ hb
    simp [hb]
  · simp

/-! ### Exact inertia conservation -/

omit [DecidableEq E] in
theorem card_filter_prod (P : Fin N → E → Prop) [DecidablePred fun p : Fin N × E => P p.1 p.2]
    [∀ x, DecidablePred (P x)] :
    (Finset.univ.filter fun p : Fin N × E => P p.1 p.2).card
      = ∑ x : Fin N, (Finset.univ.filter fun a => P x a).card := by
  simp_rw [Finset.card_filter]
  rw [Fintype.sum_prod_type]

/-- Each Hermitian atom is a unitary congruence of its real eigenvalue diagonal. -/
theorem eq_conjugate_diagonal_eigenvalues {A : Matrix E E ℂ} (hA : A.IsHermitian) :
    A = ((hA.eigenvectorUnitary : Matrix E E ℂ)ᴴ)ᴴ *
        diagonal (fun a => ((hA.eigenvalues a : ℝ) : ℂ)) * (hA.eigenvectorUnitary : Matrix E E ℂ)ᴴ := by
  have hd := conjTranspose_mul_mul_eigenvectorUnitary hA
  set V := ((hA.eigenvectorUnitary : Matrix E E ℂ)) with hV
  have h1 : V * Vᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self _
  rw [← hd, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc, h1,
    Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- **Exact inertia additivity of the block-diagonal atom matrix.** -/
theorem inertia_atomDiag {A : Fin N → Matrix E E ℂ} (hA : ∀ x, (A x).IsHermitian) :
    posIndex (atomDiag A) = ∑ x, posIndex (A x) ∧
      negIndex (atomDiag A) = ∑ x, negIndex (A x) ∧
      nullIndex (atomDiag A) = ∑ x, nullIndex (A x) := by
  classical
  set U : Fin N → Matrix E E ℂ :=
    fun x => ((hA x).eigenvectorUnitary : Matrix E E ℂ)ᴴ with hU
  set μ : Fin N × E → ℝ := fun p => (hA p.1).eigenvalues p.2 with hμ
  have hUunit : ∀ x, IsUnit (U x) := fun x =>
    isUnit_conjTranspose (isUnit_eigenvectorUnitary (hA x))
  have hcong : atomDiag A =
      (atomDiag U)ᴴ * diagonal (fun p : Fin N × E => ((μ p : ℝ) : ℂ)) * atomDiag U := by
    rw [← atomDiag_diagonal (fun x a => (((hA x).eigenvalues a : ℝ) : ℂ)),
      atomDiag_conjTranspose, atomDiag_mul, atomDiag_mul]
    congr 1
    funext x
    exact eq_conjugate_diagonal_eigenvalues (hA x)
  have hSunit : IsUnit (atomDiag U) := isUnit_atomDiag hUunit
  refine ⟨?_, ?_, ?_⟩
  · rw [hcong, posIndex_conjugate _ hSunit, posIndex_diagonal]
    rw [card_filter_prod (fun x a => 0 < (hA x).eigenvalues a)]
    exact Finset.sum_congr rfl (fun x _ => (posIndex_eq_card_pos_eigenvalues (hA x)).symm)
  · rw [hcong, negIndex_conjugate _ hSunit, negIndex_diagonal]
    rw [card_filter_prod (fun x a => (hA x).eigenvalues a < 0)]
    exact Finset.sum_congr rfl (fun x _ => (negIndex_eq_card_neg_eigenvalues (hA x)).symm)
  · rw [hcong, nullIndex_conjugate _ hSunit, nullIndex_diagonal]
    rw [card_filter_prod (fun x a => (hA x).eigenvalues a = 0)]
    exact Finset.sum_congr rfl (fun x _ => (nullIndex_eq_card_zero_eigenvalues (hA x)).symm)

/-- **Exact inertia conservation of the complete fusion (CFH.14).**  At full interpolation depth
the fused block carries exactly the componentwise sum of the atom inertia triples: no negative
spectral channel cancels between atoms. -/
theorem inertia_evalMatrix_fusion {A : Fin N → Matrix E E ℂ} (hA : ∀ x, (A x).IsHermitian)
    {z : Fin N → ℂ} (hz : Function.Injective z) :
    posIndex ((evalMatrix E z)ᴴ * atomDiag A * evalMatrix E z) = ∑ x, posIndex (A x) ∧
      negIndex ((evalMatrix E z)ᴴ * atomDiag A * evalMatrix E z) = ∑ x, negIndex (A x) ∧
      nullIndex ((evalMatrix E z)ᴴ * atomDiag A * evalMatrix E z) = ∑ x, nullIndex (A x) := by
  obtain ⟨hp, hn, h0⟩ := inertia_atomDiag hA
  have hunit : IsUnit (evalMatrix E z) := isUnit_evalMatrix hz
  exact ⟨by rw [posIndex_conjugate _ hunit, hp], by rw [negIndex_conjugate _ hunit, hn],
    by rw [nullIndex_conjugate _ hunit, h0]⟩

/-- **The real-node fusion is the block Hankel matrix.**  For real nodes the fused entry is the
moment `M_{i+j}` of the atom family. -/
theorem evalMatrix_conjugate_atomDiag_real (lam : Fin N → ℝ) (A : Fin N → Matrix E E ℂ)
    (p q : Fin N × E) :
    ((evalMatrix E (fun x => ((lam x : ℝ) : ℂ)))ᴴ * atomDiag A *
        evalMatrix E (fun x => ((lam x : ℝ) : ℂ))) p q =
      ∑ x : Fin N, ((lam x : ℝ) : ℂ) ^ ((p.1 : ℕ) + (q.1 : ℕ)) * A x p.2 q.2 := by
  rw [evalMatrix_conjugate_atomDiag]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Complex.ofReal_pow, Complex.conj_ofReal, Complex.ofReal_pow, ← pow_add]

/-- **Both organs have the same inertia (CFH.14).**  The block Hankel matrix at pairwise distinct
real nodes and the complete Fourier block at any pairwise distinct nodes carry the same inertia
triple, namely the atomwise sum. -/
theorem hankel_fourier_inertia_eq {A : Fin N → Matrix E E ℂ} (hA : ∀ x, (A x).IsHermitian)
    {lam : Fin N → ℝ} (hlam : Function.Injective lam)
    {z : Fin N → ℂ} (hz : Function.Injective z) :
    posIndex ((evalMatrix E (fun x => ((lam x : ℝ) : ℂ)))ᴴ * atomDiag A *
        evalMatrix E (fun x => ((lam x : ℝ) : ℂ))) =
      posIndex ((evalMatrix E z)ᴴ * atomDiag A * evalMatrix E z) ∧
    negIndex ((evalMatrix E (fun x => ((lam x : ℝ) : ℂ)))ᴴ * atomDiag A *
        evalMatrix E (fun x => ((lam x : ℝ) : ℂ))) =
      negIndex ((evalMatrix E z)ᴴ * atomDiag A * evalMatrix E z) ∧
    nullIndex ((evalMatrix E (fun x => ((lam x : ℝ) : ℂ)))ᴴ * atomDiag A *
        evalMatrix E (fun x => ((lam x : ℝ) : ℂ))) =
      nullIndex ((evalMatrix E z)ᴴ * atomDiag A * evalMatrix E z) := by
  have hlamC : Function.Injective (fun x => ((lam x : ℝ) : ℂ)) :=
    fun a b h => hlam (Complex.ofReal_injective h)
  obtain ⟨hp1, hn1, h01⟩ := inertia_evalMatrix_fusion hA hlamC
  obtain ⟨hp2, hn2, h02⟩ := inertia_evalMatrix_fusion hA hz
  exact ⟨by rw [hp1, hp2], by rw [hn1, hn2], by rw [h01, h02]⟩

end

end GaloisForLFunctions.HTGeometry
