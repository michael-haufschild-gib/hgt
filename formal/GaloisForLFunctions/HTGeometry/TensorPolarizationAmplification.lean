import GaloisForLFunctions.HTGeometry.HermitianInertia

namespace GaloisForLFunctions.HTGeometry

mutual
  /- Positive inertia count after `d` independent tensor formations of a packet with
  `p` positive and `q` negative channels. -/
  def tensorPolarPos (p q : ℕ) : ℕ → ℕ
    | 0 => 1
    | d + 1 => p * tensorPolarPos p q d + q * tensorPolarNeg p q d

  /- Negative inertia count after `d` independent tensor formations. -/
  def tensorPolarNeg (p q : ℕ) : ℕ → ℕ
    | 0 => 0
    | d + 1 => q * tensorPolarPos p q d + p * tensorPolarNeg p q d
end

theorem tensorPolar_total (p q d : ℕ) :
    tensorPolarPos p q d + tensorPolarNeg p q d = (p + q) ^ d := by
  induction d with
  | zero => simp [tensorPolarPos, tensorPolarNeg]
  | succ d ih =>
      rw [pow_succ, ← ih]
      simp only [tensorPolarPos, tensorPolarNeg]
      ring

theorem tensorPolar_signature (p q d : ℕ) :
    (tensorPolarPos p q d : ℤ) - tensorPolarNeg p q d =
      ((p : ℤ) - q) ^ d := by
  induction d with
  | zero => simp [tensorPolarPos, tensorPolarNeg]
  | succ d ih =>
      rw [pow_succ]
      simp only [tensorPolarPos, tensorPolarNeg, Nat.cast_add, Nat.cast_mul]
      rw [← ih]
      ring

theorem tensorPolar_twice_negative (p q d : ℕ) :
    (2 : ℤ) * tensorPolarNeg p q d =
      (((p + q) ^ d : ℕ) : ℤ) - (((p : ℤ) - q) ^ d) := by
  have htotal := congrArg (fun n : ℕ => (n : ℤ)) (tensorPolar_total p q d)
  have hsig := tensorPolar_signature p q d
  simp only [Nat.cast_add, Nat.cast_pow] at htotal
  push_cast
  linarith

theorem tensorPolar_negative_ge_total_prev {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (d : ℕ) :
    (p + q) ^ d ≤ tensorPolarNeg p q (d + 1) := by
  rw [← tensorPolar_total p q d]
  simp only [tensorPolarNeg]
  exact Nat.add_le_add (Nat.le_mul_of_pos_left _ hq) (Nat.le_mul_of_pos_left _ hp)

theorem tensorPolar_negative_strictly_amplifies {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (d : ℕ) :
    d < tensorPolarNeg p q (d + 1) := by
  refine lt_of_lt_of_le Nat.lt_two_pow_self ?_
  refine le_trans (Nat.pow_le_pow_left ?_ d) (tensorPolar_negative_ge_total_prev hp hq d)
  omega

/-- Every bounded negative-index sublevel lies in a finite formation-depth window.  This is the
discrete properness statement supplied by tensor-polarization amplification. -/
theorem tensorPolar_negative_sublevel_window {p q d K : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hbudget : tensorPolarNeg p q (d + 1) ≤ K) :
    d < K := by
  exact lt_of_lt_of_le (tensorPolar_negative_strictly_amplifies hp hq d) hbudget

/-- No fixed finite negative-index budget can admit all tensor formations of a genuinely
indefinite packet. -/
theorem tensorPolar_no_uniform_negative_budget {p q K : ℕ} (hp : 0 < p) (hq : 0 < q) :
    ∃ d, K < tensorPolarNeg p q d := by
  exact ⟨K + 1, tensorPolar_negative_strictly_amplifies hp hq K⟩

@[simp] theorem tensorPolarNeg_zero_right (p d : ℕ) : tensorPolarNeg p 0 d = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [tensorPolarNeg, ih]

/-- **Global tensor-formation selection.** In the presence of at least one positive channel,
uniformly bounded negative index across every tensor degree is equivalent to absence of every
negative channel at degree one. -/
theorem tensorPolar_uniform_negative_budget_iff {p q : ℕ} (hp : 0 < p) :
    (∃ K, ∀ d, tensorPolarNeg p q d ≤ K) ↔ q = 0 := by
  constructor
  · rintro ⟨K, hK⟩
    by_contra hq
    have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    obtain ⟨d, hd⟩ := tensorPolar_no_uniform_negative_budget (K := K) hp hqpos
    exact (not_lt_of_ge (hK d)) hd
  · rintro rfl
    exact ⟨0, fun d => by simp⟩

def TensorPolarizationAmplificationLaw : Prop :=
  ∀ p q K : ℕ, 0 < p → 0 < q →
    (tensorPolarPos p q K + tensorPolarNeg p q K = (p + q) ^ K) ∧
    ((tensorPolarPos p q K : ℤ) - tensorPolarNeg p q K = ((p : ℤ) - q) ^ K) ∧
    ∃ d, K < tensorPolarNeg p q d

theorem tensorPolarizationAmplification_closed : TensorPolarizationAmplificationLaw := by
  intro p q K hp hq
  exact ⟨tensorPolar_total p q K, tensorPolar_signature p q K,
    tensorPolar_no_uniform_negative_budget hp hq⟩

def TensorPolarizationSelectionLaw : Prop :=
  ∀ p q : ℕ, 0 < p →
    ((∃ K, ∀ d, tensorPolarNeg p q d ≤ K) ↔ q = 0) ∧
    (0 < q → ∀ d K, tensorPolarNeg p q (d + 1) ≤ K → d < K)

theorem tensorPolarizationSelection_closed : TensorPolarizationSelectionLaw := by
  intro p q hp
  exact ⟨tensorPolar_uniform_negative_budget_iff hp,
    fun hq d K hbudget => tensorPolar_negative_sublevel_window hp hq hbudget⟩

open Matrix

theorem card_mul_neg {I J : Type*} [Fintype I] [Fintype J]
    (mu : I → ℝ) (nu : J → ℝ) :
    ({ij | mu ij.1 * nu ij.2 < 0} : Finset (I × J)).card =
      ({i | 0 < mu i} : Finset I).card * ({j | nu j < 0} : Finset J).card +
      ({i | mu i < 0} : Finset I).card * ({j | 0 < nu j} : Finset J).card := by
  classical
  let PI : Finset I := {i | 0 < mu i}
  let NI : Finset I := {i | mu i < 0}
  let PJ : Finset J := {j | 0 < nu j}
  let NJ : Finset J := {j | nu j < 0}
  have hset : ({ij | mu ij.1 * nu ij.2 < 0} : Finset (I × J)) =
      (PI ×ˢ NJ) ∪ (NI ×ˢ PJ) := by
    ext ij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_product, PI, NI, PJ, NJ]
    exact mul_neg_iff
  have hdisj : Disjoint (PI ×ˢ NJ) (NI ×ˢ PJ) := by
    rw [Finset.disjoint_product]
    left
    rw [Finset.disjoint_left]
    intro i hiP hiN
    simp only [PI, NI, Finset.mem_filter, Finset.mem_univ, true_and] at hiP hiN
    linarith
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_product,
    Finset.card_product]

theorem card_mul_pos {I J : Type*} [Fintype I] [Fintype J]
    (mu : I → ℝ) (nu : J → ℝ) :
    ({ij | 0 < mu ij.1 * nu ij.2} : Finset (I × J)).card =
      ({i | 0 < mu i} : Finset I).card * ({j | 0 < nu j} : Finset J).card +
      ({i | mu i < 0} : Finset I).card * ({j | nu j < 0} : Finset J).card := by
  classical
  let PI : Finset I := {i | 0 < mu i}
  let NI : Finset I := {i | mu i < 0}
  let PJ : Finset J := {j | 0 < nu j}
  let NJ : Finset J := {j | nu j < 0}
  have hset : ({ij | 0 < mu ij.1 * nu ij.2} : Finset (I × J)) =
      (PI ×ˢ PJ) ∪ (NI ×ˢ NJ) := by
    ext ij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_product, PI, NI, PJ, NJ]
    exact mul_pos_iff
  have hdisj : Disjoint (PI ×ˢ PJ) (NI ×ˢ NJ) := by
    rw [Finset.disjoint_product]
    left
    rw [Finset.disjoint_left]
    intro i hiP hiN
    simp only [PI, NI, Finset.mem_filter, Finset.mem_univ, true_and] at hiP hiN
    linarith
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_product,
    Finset.card_product]

theorem negIndex_diagonal_kronecker {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (mu : I → ℝ) (nu : J → ℝ) :
    hermNegIndex
        (Matrix.kronecker (Matrix.diagonal (fun i => (mu i : ℂ)))
          (Matrix.diagonal (fun j => (nu j : ℂ)))) =
      hermPosIndex (Matrix.diagonal (fun i => (mu i : ℂ))) *
          hermNegIndex (Matrix.diagonal (fun j => (nu j : ℂ))) +
        hermNegIndex (Matrix.diagonal (fun i => (mu i : ℂ))) *
          hermPosIndex (Matrix.diagonal (fun j => (nu j : ℂ))) := by
  unfold Matrix.kronecker
  rw [Matrix.diagonal_kronecker_diagonal]
  have hdiag : (fun mn : I × J => (mu mn.1 : ℂ) * (nu mn.2 : ℂ)) =
      (fun mn : I × J => ((mu mn.1 * nu mn.2 : ℝ) : ℂ)) := by
    funext mn
    exact (Complex.ofReal_mul _ _).symm
  rw [hdiag, negIndex_diagonal, posIndex_diagonal, negIndex_diagonal,
    posIndex_diagonal, negIndex_diagonal]
  exact card_mul_neg mu nu

theorem posIndex_diagonal_kronecker {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (mu : I → ℝ) (nu : J → ℝ) :
    hermPosIndex
        (Matrix.kronecker (Matrix.diagonal (fun i => (mu i : ℂ)))
          (Matrix.diagonal (fun j => (nu j : ℂ)))) =
      hermPosIndex (Matrix.diagonal (fun i => (mu i : ℂ))) *
          hermPosIndex (Matrix.diagonal (fun j => (nu j : ℂ))) +
        hermNegIndex (Matrix.diagonal (fun i => (mu i : ℂ))) *
          hermNegIndex (Matrix.diagonal (fun j => (nu j : ℂ))) := by
  unfold Matrix.kronecker
  rw [Matrix.diagonal_kronecker_diagonal]
  have hdiag : (fun mn : I × J => (mu mn.1 : ℂ) * (nu mn.2 : ℂ)) =
      (fun mn : I × J => ((mu mn.1 * nu mn.2 : ℝ) : ℂ)) := by
    funext mn
    exact (Complex.ofReal_mul _ _).symm
  rw [hdiag, posIndex_diagonal, posIndex_diagonal, posIndex_diagonal,
    negIndex_diagonal, negIndex_diagonal]
  exact card_mul_pos mu nu

/-- **Tensor-polarization fusion, negative sector.** The negative index of a tensor product of
finite Hermitian forms is the sum of the two opposite-sign channel products. -/
theorem negIndex_kronecker {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {H : Matrix I I ℂ} {K : Matrix J J ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    hermNegIndex (Matrix.kronecker H K) =
      hermPosIndex H * hermNegIndex K + hermNegIndex H * hermPosIndex K := by
  let U : Matrix I I ℂ := hH.eigenvectorUnitary
  let V : Matrix J J ℂ := hK.eigenvectorUnitary
  let S : Matrix (I × J) (I × J) ℂ := Matrix.kronecker U V
  have hU : IsUnit U := isUnit_eigenvectorUnitary hH
  have hV : IsUnit V := isUnit_eigenvectorUnitary hK
  have hS : IsUnit S := hU.kronecker hV
  have hconj : Sᴴ * Matrix.kronecker H K * S =
      Matrix.kronecker
        (Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)))
        (Matrix.diagonal (fun j => ((hK.eigenvalues j : ℝ) : ℂ))) := by
    dsimp only [S, U, V]
    unfold Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, conjTranspose_mul_mul_eigenvectorUnitary hH,
      conjTranspose_mul_mul_eigenvectorUnitary hK]
  rw [← negIndex_conjugate (Matrix.kronecker H K) hS, hconj,
    negIndex_diagonal_kronecker]
  have hpH : hermPosIndex
      (Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ))) = hermPosIndex H := by
    rw [← conjTranspose_mul_mul_eigenvectorUnitary hH, posIndex_conjugate H hU]
  have hnH : hermNegIndex
      (Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ))) = hermNegIndex H := by
    rw [← conjTranspose_mul_mul_eigenvectorUnitary hH, negIndex_conjugate H hU]
  have hpK : hermPosIndex
      (Matrix.diagonal (fun j => ((hK.eigenvalues j : ℝ) : ℂ))) = hermPosIndex K := by
    rw [← conjTranspose_mul_mul_eigenvectorUnitary hK, posIndex_conjugate K hV]
  have hnK : hermNegIndex
      (Matrix.diagonal (fun j => ((hK.eigenvalues j : ℝ) : ℂ))) = hermNegIndex K := by
    rw [← conjTranspose_mul_mul_eigenvectorUnitary hK, negIndex_conjugate K hV]
  rw [hpH, hnH, hpK, hnK]

/-- Tensor-polarization fusion, positive sector. -/
theorem posIndex_kronecker {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {H : Matrix I I ℂ} {K : Matrix J J ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    hermPosIndex (Matrix.kronecker H K) =
      hermPosIndex H * hermPosIndex K + hermNegIndex H * hermNegIndex K := by
  let U : Matrix I I ℂ := hH.eigenvectorUnitary
  let V : Matrix J J ℂ := hK.eigenvectorUnitary
  let S : Matrix (I × J) (I × J) ℂ := Matrix.kronecker U V
  have hU : IsUnit U := isUnit_eigenvectorUnitary hH
  have hV : IsUnit V := isUnit_eigenvectorUnitary hK
  have hS : IsUnit S := hU.kronecker hV
  have hconj : Sᴴ * Matrix.kronecker H K * S =
      Matrix.kronecker
        (Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)))
        (Matrix.diagonal (fun j => ((hK.eigenvalues j : ℝ) : ℂ))) := by
    dsimp only [S, U, V]
    unfold Matrix.kronecker
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, conjTranspose_mul_mul_eigenvectorUnitary hH,
      conjTranspose_mul_mul_eigenvectorUnitary hK]
  rw [← posIndex_conjugate (Matrix.kronecker H K) hS, hconj,
    posIndex_diagonal_kronecker]
  have hpH : hermPosIndex
      (Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ))) = hermPosIndex H := by
    rw [← conjTranspose_mul_mul_eigenvectorUnitary hH, posIndex_conjugate H hU]
  have hnH : hermNegIndex
      (Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ))) = hermNegIndex H := by
    rw [← conjTranspose_mul_mul_eigenvectorUnitary hH, negIndex_conjugate H hU]
  have hpK : hermPosIndex
      (Matrix.diagonal (fun j => ((hK.eigenvalues j : ℝ) : ℂ))) = hermPosIndex K := by
    rw [← conjTranspose_mul_mul_eigenvectorUnitary hK, posIndex_conjugate K hV]
  have hnK : hermNegIndex
      (Matrix.diagonal (fun j => ((hK.eigenvalues j : ℝ) : ℂ))) = hermNegIndex K := by
    rw [← conjTranspose_mul_mul_eigenvectorUnitary hK, negIndex_conjugate K hV]
  rw [hpH, hnH, hpK, hnK]

end GaloisForLFunctions.HTGeometry
