import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNeutralPartOfAWindowOfRatioTwoHasOneNegativeSquareAtEveryBlockSize

/-!
# The bound states of a window are at most the sinks of a positive trial vector

Let `B` be a real symmetric matrix whose entries off the diagonal are `≤ 0`: a potential plus the
Dirichlet form of a weighted graph. For a positive vector `v`, a trial ground state,

  `Σ σ_i σ_j B_ij ≥ Σ_i (σ_i² / v_i) (B v)_i`   (`sum_div_mul_mulVec_le`),

because the difference is `½ Σ (−B_ij) v_i v_j (σ_i/v_i − σ_j/v_j)²`. A **sink** of `v` is an
index with `(B v)_i < 0`.

* **Count** (`hermNegIndex_le_card_sinks`): the number of negative squares of `B` is at most the
  number of sinks of `v`. For `v = 1` the sinks are the wells of the potential.
* **Count with a charge** (`hermNegIndex_le_one_add_card_sinks`): if a charge vector `c` and a
  number `λ` satisfy `B_ij + λ c_i c_j ≤ 0` off the diagonal (the couplings dominate the product
  of the charges), then the number of negative squares is at most one plus the number of
  indices with `(B v)_i + λ c_i (c · v) < 0`: on the packets without charge the form of `B` is
  the form of `B + λ c ⊗ c`.
* **Windows.** The neutral part of a window has at most as many negative squares as blocks of
  negative potential (`hermNegIndex_neutralWindow_le_card_wells`). If every pair of blocks of
  the window is coupled by at least `λ`, it has at most one negative square more than the
  number of blocks whose potential is below `−λ J`
  (`hermNegIndex_neutralWindow_le_one_add_card_deepWells`); a window whose potential is at least
  `−λ J` at every block holds at most one bound state
  (`hermNegIndex_neutralWindow_le_one_of_shallow`).
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### A potential and a Dirichlet form under a positive trial vector -/

section General

variable {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ)

/-- The real form of a real matrix as a double sum. -/
theorem dotProduct_mulVec_eq_sum_sum (y : ι → ℝ) :
    y ⬝ᵥ (B *ᵥ y) = ∑ i, ∑ j, y i * y j * B i j := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The ground state substitution.** For a symmetric matrix with entries `≤ 0` off the diagonal
and a positive `v`, the form is at least `Σ_i (σ_i² / v_i) (B v)_i`. -/
theorem sum_div_mul_mulVec_le (hB : ∀ i j, B i j = B j i) (hoff : ∀ i j, i ≠ j → B i j ≤ 0)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) (σ : ι → ℝ) :
    ∑ i, σ i ^ 2 / v i * (B *ᵥ v) i ≤ ∑ i, ∑ j, σ i * σ j * B i j := by
  have hL : ∑ i, σ i ^ 2 / v i * (B *ᵥ v) i = ∑ i, ∑ j, σ i ^ 2 / v i * (B i j * v j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec, dotProduct, Finset.mul_sum]
  have hdiff : ∑ i, ∑ j, σ i * σ j * B i j - ∑ i, ∑ j, σ i ^ 2 / v i * (B i j * v j) =
      ∑ i, ∑ j, (σ i * σ j * B i j - σ i ^ 2 / v i * (B i j * v j)) := by
    simp only [Finset.sum_sub_distrib]
  -- the difference is half the sum of the squares of the differences of `σ / v`
  have hsym : ∑ i, ∑ j, (σ i * σ j * B i j - σ i ^ 2 / v i * (B i j * v j)) =
      (1 / 2) * ∑ i, ∑ j, -(B i j * v i * v j * (σ i / v i - σ j / v j) ^ 2) := by
    have hswap : ∑ i, ∑ j, (σ i * σ j * B i j - σ i ^ 2 / v i * (B i j * v j)) =
        ∑ i, ∑ j, (σ j * σ i * B j i - σ j ^ 2 / v j * (B j i * v i)) := Finset.sum_comm
    have h2 : ∑ i, ∑ j, -(B i j * v i * v j * (σ i / v i - σ j / v j) ^ 2) =
        ∑ i, ∑ j, ((σ i * σ j * B i j - σ i ^ 2 / v i * (B i j * v j)) +
          (σ j * σ i * B j i - σ j ^ 2 / v j * (B j i * v i))) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hi := (hv i).ne'
      have hj := (hv j).ne'
      rw [hB j i]
      field_simp
      ring
    rw [h2]
    simp only [Finset.sum_add_distrib]
    rw [← hswap]
    ring
  rw [hL, ← sub_nonneg, hdiff, hsym]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
  by_cases hij : i = j
  · rw [hij, sub_self]
    simp
  · have h1 : B i j * v i * v j ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (hoff i j hij) (hv i).le) (hv j).le
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg h1 (sq_nonneg _))

/-- The form is nonnegative on the packets that vanish at the sinks of `v`. -/
theorem dotProduct_mulVec_nonneg_of_sinks (hB : ∀ i j, B i j = B j i)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) {v : ι → ℝ} (hv : ∀ i, 0 < v i) {σ : ι → ℝ}
    (hσ : ∀ i, (B *ᵥ v) i < 0 → σ i = 0) : 0 ≤ σ ⬝ᵥ (B *ᵥ σ) := by
  rw [dotProduct_mulVec_eq_sum_sum]
  refine le_trans (Finset.sum_nonneg fun i _ => ?_) (sum_div_mul_mulVec_le B hB hoff hv σ)
  by_cases hi : (B *ᵥ v) i < 0
  · rw [hσ i hi]
    simp
  · exact mul_nonneg (div_nonneg (sq_nonneg _) (hv i).le) (not_lt.mp hi)

/-- **The negative squares are at most the sinks of a positive trial vector.** -/
theorem hermNegIndex_le_card_sinks (hB : ∀ i j, B i j = B j i)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0) {v : ι → ℝ} (hv : ∀ i, 0 < v i) :
    hermNegIndex (B.map (↑) : Matrix ι ι ℂ) ≤ Fintype.card {i // (B *ᵥ v) i < 0} := by
  refine ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker _
    (fun k : {i // (B *ᵥ v) i < 0} => LinearMap.proj (k : ι)) fun x hx => ?_
  have hx0 : ∀ i, (B *ᵥ v) i < 0 → x i = 0 := fun i hi => hx ⟨i, hi⟩
  rw [HeckeKreinToeplitz.hermQuad_map_ofReal]
  exact add_nonneg
    (dotProduct_mulVec_nonneg_of_sinks B hB hoff hv fun i hi => by rw [hx0 i hi, Complex.zero_re])
    (dotProduct_mulVec_nonneg_of_sinks B hB hoff hv fun i hi => by rw [hx0 i hi, Complex.zero_im])

/-- The charge of a complex packet for a real charge vector. -/
def realChargeForm (c : ι → ℝ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ i, (c i : ℂ) * x i
  map_add' x y := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **The count with a charge.** If the couplings dominate `λ` times the product of the
charges, the negative squares are at most one more than the sinks of the matrix shifted by
`λ c ⊗ c`. -/
theorem hermNegIndex_le_one_add_card_sinks (hB : ∀ i j, B i j = B j i) (c : ι → ℝ) (lam : ℝ)
    (hoff : ∀ i j, i ≠ j → B i j + lam * c i * c j ≤ 0) {v : ι → ℝ} (hv : ∀ i, 0 < v i) :
    hermNegIndex (B.map (↑) : Matrix ι ι ℂ) ≤
      1 + Fintype.card {i // (B *ᵥ v) i + lam * c i * (c ⬝ᵥ v) < 0} := by
  -- the matrix shifted by the product of the charges
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix ι ι ℝ, ∀ i j, B' i j = B i j + lam * c i * c j :=
    ⟨Matrix.of fun i j => B i j + lam * c i * c j, fun _ _ => rfl⟩
  have hB's : ∀ i j, B' i j = B' j i := fun i j => by
    rw [hB', hB', hB i j]
    ring
  have hmv : ∀ i, (B' *ᵥ v) i = (B *ᵥ v) i + lam * c i * (c ⬝ᵥ v) := by
    intro i
    simp only [mulVec, dotProduct, hB', add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  -- on the packets without charge the two forms agree
  have hform : ∀ σ : ι → ℝ, ∑ i, c i * σ i = 0 → σ ⬝ᵥ (B *ᵥ σ) = σ ⬝ᵥ (B' *ᵥ σ) := by
    intro σ hσ
    have hshift : ∑ i, ∑ j, σ i * σ j * B' i j =
        ∑ i, ∑ j, σ i * σ j * B i j + lam * (∑ i, c i * σ i) ^ 2 := by
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by
        rw [hB']
        ring
    rw [dotProduct_mulVec_eq_sum_sum, dotProduct_mulVec_eq_sum_sum, hshift, hσ]
    ring
  have h := ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker
    (B.map (↑) : Matrix ι ι ℂ)
    (fun k : Option {i // (B *ᵥ v) i + lam * c i * (c ⬝ᵥ v) < 0} =>
      k.elim (realChargeForm c) fun k => LinearMap.proj (k : ι)) fun x hx => ?_
  · rwa [Fintype.card_option, add_comm] at h
  · -- the real and the imaginary part have no charge and vanish at the sinks
    have hc : ∑ i, (c i : ℂ) * x i = 0 := hx none
    have hre : ∑ i, c i * (x i).re = 0 := by
      have h1 := congrArg Complex.re hc
      rw [Complex.re_sum, Complex.zero_re] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => (Complex.re_ofReal_mul _ _).symm
    have him : ∑ i, c i * (x i).im = 0 := by
      have h1 := congrArg Complex.im hc
      rw [Complex.im_sum, Complex.zero_im] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => (Complex.im_ofReal_mul _ _).symm
    have hx0 : ∀ i, (B' *ᵥ v) i < 0 → x i = 0 := fun i hi =>
      hx (some ⟨i, by rwa [hmv i] at hi⟩)
    rw [HeckeKreinToeplitz.hermQuad_map_ofReal, hform _ hre, hform _ him]
    exact add_nonneg
      (dotProduct_mulVec_nonneg_of_sinks B' hB's (fun i j hij => by
        rw [hB']
        exact hoff i j hij) hv fun i hi => by rw [hx0 i hi, Complex.zero_re])
      (dotProduct_mulVec_nonneg_of_sinks B' hB's (fun i j hij => by
        rw [hB']
        exact hoff i j hij) hv fun i hi => by rw [hx0 i hi, Complex.zero_im])

end General

/-! ### The windows -/

/-- The row sums of the neutral part of a window are the potential. -/
theorem neutralWindow_mulVec_one (Q R J : ℕ) (j : Fin J) :
    (neutralWindow Q R J *ᵥ fun _ => (1 : ℝ)) j = blockPotential Q R J j := by
  rw [mulVec, dotProduct, blockPotential,
    ← Fin.sum_univ_eq_sum_range (fun l => neutralBlock Q (R + j) (R + l)) J]
  exact Finset.sum_congr rfl fun l _ => mul_one _

/-- **The neutral part of a window has at most as many negative squares as blocks of negative
potential.** -/
theorem hermNegIndex_neutralWindow_le_card_wells (Q R J : ℕ) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤
      Fintype.card {j : Fin J // blockPotential Q R J j < 0} := by
  have h := hermNegIndex_le_card_sinks (neutralWindow Q R J)
    (fun i j => neutralBlock_comm Q _ _)
    (fun i j hij => (neutralBlock_neg (fun h => hij (Fin.ext (Nat.add_left_cancel h))) Q).le)
    (v := fun _ => (1 : ℝ)) fun _ => one_pos
  refine h.trans (le_of_eq ?_)
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun j => by
    rw [neutralWindow_mulVec_one])

/-- **A count of the bound states of a window from its potential and its couplings.** If every
pair of blocks of the window is coupled by at least `λ`, the neutral part has at most one
negative square more than the number of blocks whose potential is below `−λ J`. -/
theorem hermNegIndex_neutralWindow_le_one_add_card_deepWells (Q R J : ℕ) (lam : ℝ)
    (hlam : ∀ j l : Fin J, j ≠ l → lam ≤ blockWeight Q (R + j) (R + l)) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤
      1 + Fintype.card {j : Fin J // blockPotential Q R J j + lam * J < 0} := by
  have h := hermNegIndex_le_one_add_card_sinks (neutralWindow Q R J)
    (fun i j => neutralBlock_comm Q _ _) (fun _ => (1 : ℝ)) lam
    (fun i j hij => by
      have hw := hlam i j hij
      unfold blockWeight at hw
      show neutralBlock Q (R + i) (R + j) + lam * 1 * 1 ≤ 0
      linarith)
    (v := fun _ => (1 : ℝ)) fun _ => one_pos
  refine h.trans (le_of_eq ?_)
  congr 1
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun j => ?_)
  have hJ : (fun _ : Fin J => (1 : ℝ)) ⬝ᵥ (fun _ => (1 : ℝ)) = J := by
    simp [dotProduct]
  rw [neutralWindow_mulVec_one, hJ, mul_one]

/-- **A window whose potential is at least `−λ J` at every block, with all couplings at least
`λ`, holds at most one bound state.** -/
theorem hermNegIndex_neutralWindow_le_one_of_shallow (Q R J : ℕ) (lam : ℝ)
    (hlam : ∀ j l : Fin J, j ≠ l → lam ≤ blockWeight Q (R + j) (R + l))
    (hV : ∀ j : Fin J, 0 ≤ blockPotential Q R J j + lam * J) :
    hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤ 1 := by
  have h := hermNegIndex_neutralWindow_le_one_add_card_deepWells Q R J lam hlam
  have h0 : Fintype.card {j : Fin J // blockPotential Q R J j + lam * J < 0} = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun j => absurd j.2 (not_lt.mpr (hV j.1))⟩
  rwa [h0, add_zero] at h

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
