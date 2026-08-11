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
    hermPosIndex (atomDiag A) = ∑ x, hermPosIndex (A x) ∧
      hermNegIndex (atomDiag A) = ∑ x, hermNegIndex (A x) ∧
      hermNullIndex (atomDiag A) = ∑ x, hermNullIndex (A x) := by
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
    hermPosIndex ((evalMatrix E z)ᴴ * atomDiag A * evalMatrix E z) = ∑ x, hermPosIndex (A x) ∧
      hermNegIndex ((evalMatrix E z)ᴴ * atomDiag A * evalMatrix E z) = ∑ x, hermNegIndex (A x) ∧
      hermNullIndex ((evalMatrix E z)ᴴ * atomDiag A * evalMatrix E z) = ∑ x, hermNullIndex (A x) := by
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
    hermPosIndex ((evalMatrix E (fun x => ((lam x : ℝ) : ℂ)))ᴴ * atomDiag A *
        evalMatrix E (fun x => ((lam x : ℝ) : ℂ))) =
      hermPosIndex ((evalMatrix E z)ᴴ * atomDiag A * evalMatrix E z) ∧
    hermNegIndex ((evalMatrix E (fun x => ((lam x : ℝ) : ℂ)))ᴴ * atomDiag A *
        evalMatrix E (fun x => ((lam x : ℝ) : ℂ))) =
      hermNegIndex ((evalMatrix E z)ᴴ * atomDiag A * evalMatrix E z) ∧
    hermNullIndex ((evalMatrix E (fun x => ((lam x : ℝ) : ℂ)))ᴴ * atomDiag A *
        evalMatrix E (fun x => ((lam x : ℝ) : ℂ))) =
      hermNullIndex ((evalMatrix E z)ᴴ * atomDiag A * evalMatrix E z) := by
  have hlamC : Function.Injective (fun x => ((lam x : ℝ) : ℂ)) :=
    fun a b h => hlam (Complex.ofReal_injective h)
  obtain ⟨hp1, hn1, h01⟩ := inertia_evalMatrix_fusion hA hlamC
  obtain ⟨hp2, hn2, h02⟩ := inertia_evalMatrix_fusion hA hz
  exact ⟨by rw [hp1, hp2], by rw [hn1, hn2], by rw [h01, h02]⟩

/-! ### The card's compensation pencil and Fourier nodes -/

/-- The compensated atom pencil `A x c = c • W x - H x`. -/
def atomPencil (W H : Fin N → Matrix E E ℂ) (c : ℝ) (x : Fin N) : Matrix E E ℂ :=
  (c : ℂ) • W x - H x

omit [Fintype E] [DecidableEq E] in
theorem isHermitian_atomPencil {W H : Fin N → Matrix E E ℂ} (hW : ∀ x, (W x).IsHermitian)
    (hH : ∀ x, (H x).IsHermitian) (c : ℝ) (x : Fin N) :
    (atomPencil W H c x).IsHermitian := by
  unfold Matrix.IsHermitian atomPencil
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, (hH x).eq, (hW x).eq]
  simp

/-- The Fourier node attached to a time scale. -/
def fourierNode (τ : ℝ) (lam : Fin N → ℝ) (x : Fin N) : ℂ :=
  Complex.exp ((-(τ * lam x) : ℝ) * Complex.I)

/-- **A nonzero time scale separating the Fourier nodes exists.**  Any scale below
`π / (1 + max |λ x - λ y|)` keeps every phase difference inside one period. -/
theorem exists_fourierNode_injective {lam : Fin N → ℝ} (hlam : Function.Injective lam) :
    ∃ τ : ℝ, τ ≠ 0 ∧ Function.Injective (fourierNode τ lam) := by
  obtain ⟨D, hD⟩ := Finite.exists_le (fun p : Fin N × Fin N => |lam p.1 - lam p.2|)
  set D' : ℝ := max D 0 with hD'
  have hD'0 : 0 ≤ D' := le_max_right _ _
  have hden : (0 : ℝ) < 1 + D' := by linarith
  set τ : ℝ := Real.pi / (1 + D') with hτ
  have hτpos : 0 < τ := by positivity
  refine ⟨τ, hτpos.ne', ?_⟩
  intro x y hxy
  by_contra hne
  have hbound : |τ * (lam y - lam x)| < 2 * Real.pi := by
    rw [abs_mul, abs_of_pos hτpos]
    have h1 : |lam y - lam x| ≤ D' := le_trans (hD (y, x)) (le_max_left _ _)
    have h2 : τ * |lam y - lam x| ≤ τ * D' := mul_le_mul_of_nonneg_left h1 hτpos.le
    have h3 : τ * D' < Real.pi := by
      rw [hτ, div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith [Real.pi_pos]
    linarith [Real.pi_pos]
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hxy
  have hreal : (-(τ * lam x) : ℝ) = (-(τ * lam y) : ℝ) + 2 * Real.pi * m := by
    have h := congrArg Complex.im hm
    simp at h
    linarith
  have hm0 : m = 0 := by
    by_contra hm0
    have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have hm1 : (1 : ℤ) ≤ |m| := Int.one_le_abs (by exact_mod_cast hm0)
      have h2 := (Int.cast_le (R := ℝ)).mpr hm1
      rwa [Int.cast_abs, Int.cast_one] at h2
    have heq : τ * (lam y - lam x) = 2 * Real.pi * m := by ring_nf; ring_nf at hreal; linarith
    rw [heq, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hbound
    nlinarith [Real.pi_pos]
  rw [hm0] at hreal
  simp only [Int.cast_zero, mul_zero, add_zero, neg_inj] at hreal
  have : lam x = lam y := by
    have := mul_left_cancel₀ hτpos.ne' hreal
    exact this
  exact hne (hlam this)


/-! ### Complete order reflection and the collapse of amplification -/

open scoped ComplexOrder

omit [DecidableEq E] in
theorem atomDiag_mulVec (A : Fin N → Matrix E E ℂ) (v : Fin N × E → ℂ) (p : Fin N × E) :
    (atomDiag A *ᵥ v) p = (A p.1 *ᵥ fun a => v (p.1, a)) p.2 := by
  simp only [Matrix.mulVec, dotProduct, atomDiag, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single p.1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

omit [DecidableEq E] in
theorem atomDiag_quadratic (A : Fin N → Matrix E E ℂ) (v : Fin N × E → ℂ) :
    star v ⬝ᵥ atomDiag A *ᵥ v =
      ∑ x, star (fun a => v (x, a)) ⬝ᵥ A x *ᵥ (fun a => v (x, a)) := by
  simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, atomDiag_mulVec]

omit [Fintype E] [DecidableEq E] in
theorem isHermitian_atomDiag {A : Fin N → Matrix E E ℂ} (hA : ∀ x, (A x).IsHermitian) :
    (atomDiag A).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [atomDiag_conjTranspose]
  congr 1
  funext x
  exact (hA x).eq

omit [DecidableEq E] in
/-- **Complete order reflection for the block-diagonal atom matrix.** -/
theorem posSemidef_atomDiag_iff {A : Fin N → Matrix E E ℂ} :
    (atomDiag A).PosSemidef ↔ ∀ x, (A x).PosSemidef := by
  constructor
  · intro h x
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext a b
      have hh : atomDiag (fun y => (A y)ᴴ) = atomDiag A := by
        rw [← atomDiag_conjTranspose]
        exact h.1
      have hab := congrFun (congrFun hh (x, a)) (x, b)
      simpa [atomDiag] using hab
    · intro u
      have hq := h.dotProduct_mulVec_nonneg (fun p : Fin N × E => if p.1 = x then u p.2 else 0)
      rw [atomDiag_quadratic, Finset.sum_eq_single x] at hq
      · simpa using hq
      · intro y _ hy
        have hzero : (fun a => (if y = x then u a else 0)) = (0 : E → ℂ) := by
          funext a
          simp [hy]
        simp [hzero]
      · simp
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (isHermitian_atomDiag (fun x => (h x).1)) (fun v => ?_)
    rw [atomDiag_quadratic]
    exact Finset.sum_nonneg (fun x _ => (h x).dotProduct_mulVec_nonneg _)

/-- **Complete order reflection for the fused block (CFH.11).**  The fused response is positive
semidefinite exactly when every atom is. -/
theorem posSemidef_evalMatrix_fusion_iff {A : Fin N → Matrix E E ℂ} {z : Fin N → ℂ}
    (hz : Function.Injective z) :
    ((evalMatrix E z)ᴴ * atomDiag A * evalMatrix E z).PosSemidef ↔ ∀ x, (A x).PosSemidef := by
  rw [← posSemidef_atomDiag_iff]
  exact posSemidef_conjugate_iff _ (isUnit_evalMatrix hz)

/-- The finite commutative source map `Φ(f) = ∑_x f x • A x`. -/
def sourceMap (A : Fin N → Matrix E E ℂ) (f : Fin N → ℝ) : Matrix E E ℂ := ∑ x, f x • A x

/-- The matrix amplification of the source map at a finite matrix level. -/
def sourceAmplification {k : Type*} (A : Fin N → Matrix E E ℂ) (F : Fin N → Matrix k k ℂ) :
    Matrix (k × E) (k × E) ℂ := ∑ x, Matrix.kroneckerMap (fun a b => a * b) (F x) (A x)

omit [Fintype E] [DecidableEq E] in
/-- **Positivity of the source map (Theorem 4.1, clause 1).** -/
theorem posSemidef_sourceMap {A : Fin N → Matrix E E ℂ} (hA : ∀ x, (A x).PosSemidef)
    {f : Fin N → ℝ} (hf : ∀ x, 0 ≤ f x) : (sourceMap A f).PosSemidef :=
  posSemidef_sum _ (fun x _ => (hA x).smul (hf x))

omit [DecidableEq E] in
/-- **Complete positivity of the source map (Theorem 4.1, clause 3).**  Every matrix
amplification of a positive source map is positive. -/
theorem posSemidef_sourceAmplification {A : Fin N → Matrix E E ℂ} (hA : ∀ x, (A x).PosSemidef)
    {k : Type*} [Finite k] (F : Fin N → Matrix k k ℂ) (hF : ∀ x, (F x).PosSemidef) :
    (sourceAmplification A F).PosSemidef :=
  posSemidef_sum _ (fun x _ => (hF x).kronecker (hA x))

omit [Fintype E] [DecidableEq E] in
/-- **Positivity reflects to the atoms.**  Testing the source map on the minimal projections
recovers positive semidefiniteness of every atom. -/
theorem posSemidef_of_posSemidef_sourceMap {A : Fin N → Matrix E E ℂ}
    (h : ∀ f : Fin N → ℝ, (∀ x, 0 ≤ f x) → (sourceMap A f).PosSemidef) (x : Fin N) :
    (A x).PosSemidef := by
  have hx := h (fun y => if y = x then 1 else 0) (by
    intro y
    by_cases hy : y = x <;> simp [hy])
  simpa [sourceMap, Finset.sum_ite_eq'] using hx

omit [Fintype E] [DecidableEq E] in
/-- **Complete positivity reflects to the atoms.**  Level-one amplification already recovers
positive semidefiniteness of every atom. -/
theorem posSemidef_of_posSemidef_sourceAmplification {A : Fin N → Matrix E E ℂ}
    (h : ∀ (k : Type) [Fintype k] [DecidableEq k] (F : Fin N → Matrix k k ℂ),
      (∀ x, (F x).PosSemidef) → (sourceAmplification A F).PosSemidef) (x : Fin N) :
    (A x).PosSemidef := by
  have hx := h (Fin 1) (fun y => if y = x then 1 else 0) (by
    intro y
    by_cases hy : y = x
    · simpa [hy] using (Matrix.PosSemidef.one : (1 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef)
    · simpa [hy] using (Matrix.PosSemidef.zero : (0 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef))
  have hsub := hx.submatrix (fun a : E => ((0 : Fin 1), a))
  have hEq : (sourceAmplification A (fun y => if y = x then 1 else 0)).submatrix
      (fun a : E => ((0 : Fin 1), a)) (fun a : E => ((0 : Fin 1), a)) = A x := by
    ext a b
    rw [Matrix.submatrix_apply, sourceAmplification, Matrix.sum_apply,
      Finset.sum_eq_single x]
    · simp [Matrix.kroneckerMap_apply]
    · intro y _ hy
      simp [hy, Matrix.kroneckerMap_apply]
    · simp
  rwa [hEq] at hsub

/-- **Amplification collapses on a finite commutative source (Theorem 4.1).**  Positivity of the
source map, atomwise positive semidefiniteness, complete positivity, and positive semidefiniteness
of the complete fused block are all equivalent. -/
theorem sourceMap_amplification_collapse {A : Fin N → Matrix E E ℂ} {z : Fin N → ℂ}
    (hz : Function.Injective z) :
    ((∀ f : Fin N → ℝ, (∀ x, 0 ≤ f x) → (sourceMap A f).PosSemidef) ↔ ∀ x, (A x).PosSemidef) ∧
      ((∀ x, (A x).PosSemidef) ↔
        ((evalMatrix E z)ᴴ * atomDiag A * evalMatrix E z).PosSemidef) ∧
      ((∀ x, (A x).PosSemidef) ↔
        ∀ (k : Type) [Fintype k] [DecidableEq k] (F : Fin N → Matrix k k ℂ),
          (∀ x, (F x).PosSemidef) → (sourceAmplification A F).PosSemidef) :=
  ⟨⟨fun h => posSemidef_of_posSemidef_sourceMap h, fun h _ hf => posSemidef_sourceMap h hf⟩,
    (posSemidef_evalMatrix_fusion_iff hz).symm,
    ⟨fun h _ _ _ F hF => posSemidef_sourceAmplification h F hF,
      fun h => posSemidef_of_posSemidef_sourceAmplification h⟩⟩


end

end GaloisForLFunctions.HTGeometry

