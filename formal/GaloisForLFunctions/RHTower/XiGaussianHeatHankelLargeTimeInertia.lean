import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLargeTimeCensus
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelDeterminantSignLaw
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLinearHorizon

/-!
# Exact large-time inertia of the heat Hankel ladder

**Theorem** (`eventually_hermNegIndex_heatMomentSection_eq`).  For every level `L`, with `S_L` the
distinct heat frequencies of real part `≤ L` and `N = |S_L|`, for all large heat times the rank-`N`
section has negative index exactly the number of off-line frequencies in `S_L` with `Im w > 0`,
i.e. the number of off-line pairs below `L`.

This sharpens the parity census (`eventually_sign_mul_heatMomentDet_pos`).

Proof.  In the values `v = W x` at the nodes of `S_L` the moment form is `vᵀ (D + Y) v`, with
`D = diag(m_w e^{−a w})` and `Y = O(e^{−a g})` relative to `D`.  Write `s_w² = m_w e^{−a w}`.
* Real nodes: the vector `v = s_w⁻¹ e_w` gives `+1`.
* An off-line pair `(u, ū)`: the vectors `(s_u⁻¹, \overline{s_u⁻¹})` and `(i s_u⁻¹, \overline{i s_u⁻¹})`
  give `+2` and `−2`.
* Conjugation-symmetric value vectors pull back to real coefficient vectors (`isReal_inv_mulVec`).
  On their complex span the Hermitian form is the Gram form `c* G c`, with `G` diagonal up to
  `O(e^{−a g})`.
* The `−2` family spans a negative-definite subspace of dimension `p`, and the `+1, +2` family a
  positive-definite one of dimension `N − p` (`isPosDefOn_span_of_gram`).  Since the positive,
  negative and null indices add up to `N`, the negative index is `p`.
-/

open Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry (leadingMatrix hermQuad hermQuad_neg IsPosDefOn hermPosIndex
  hermNegIndex hermNullIndex finrank_le_posIndex posIndex_add_negIndex_add_nullIndex)

namespace RHTower

noncomputable section

variable (L : ℝ)

/-! ## Symmetry of the multiplicities and the square-root weights -/

theorem censusMult_conj (w : ℂ) : censusMult L ((starRingEnd ℂ) w) = censusMult L w := by
  classical
  unfold censusMult
  refine Finset.card_bij (fun q _ => xiZeroCopyLineConjEquiv q) (fun q hq => ?_) (fun q₁ _ q₂ _ h =>
    xiZeroCopyLineConjEquiv.injective h) (fun q hq => ?_)
  · rw [Finset.mem_filter, mem_censusCopies] at hq ⊢
    rw [xiHeatFrequency_lineConj, Complex.conj_re]
    refine ⟨hq.1, ?_⟩
    rw [hq.2, Complex.conj_conj]
  · rw [Finset.mem_filter, mem_censusCopies] at hq
    refine ⟨xiZeroCopyLineConjEquiv.symm q, ?_, by simp⟩
    rw [Finset.mem_filter, mem_censusCopies]
    have h := xiHeatFrequency_lineConj (xiZeroCopyLineConjEquiv.symm q)
    rw [Equiv.apply_symm_apply] at h
    have h' : xiHeatFrequency (xiZeroCopyLineConjEquiv.symm q) = (starRingEnd ℂ) (xiHeatFrequency q) := by
      rw [h, Complex.conj_conj]
    rw [h']
    exact ⟨by rw [Complex.conj_re]; exact hq.1, by rw [hq.2]⟩

/-- The square-root weight `s_k = √m_k · e^{−a ν_k / 2}`. -/
def censusSqrtWeight (a : ℝ) (k : Fin (censusFreq L).card) : ℂ :=
  ((Real.sqrt (censusMult L (censusNode L k)) : ℝ) : ℂ) * Complex.exp (-(a : ℂ) * censusNode L k / 2)

theorem censusSqrtWeight_sq (a : ℝ) (k : Fin (censusFreq L).card) :
    censusSqrtWeight L a k ^ 2 = censusWeight L a k := by
  rw [censusSqrtWeight, censusWeight, mul_pow, ← Complex.ofReal_pow,
    Real.sq_sqrt (Nat.cast_nonneg _), ← Complex.exp_nat_mul]
  push_cast
  ring_nf

theorem censusSqrtWeight_ne_zero (a : ℝ) (k : Fin (censusFreq L).card) : censusSqrtWeight L a k ≠ 0 := by
  intro h
  have := censusSqrtWeight_sq L a k
  rw [h, zero_pow two_ne_zero] at this
  exact censusWeight_ne_zero L a k this.symm

theorem censusSqrtWeight_conjPerm (a : ℝ) (k : Fin (censusFreq L).card) :
    censusSqrtWeight L a (censusConjPerm L k) = (starRingEnd ℂ) (censusSqrtWeight L a k) := by
  rw [censusSqrtWeight, censusSqrtWeight, censusNode_censusConjPerm, censusMult_conj, map_mul,
    Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  rw [map_div₀, map_mul, map_neg, Complex.conj_ofReal, map_ofNat]

theorem censusWeight_conjPerm (a : ℝ) (k : Fin (censusFreq L).card) :
    censusWeight L a (censusConjPerm L k) = (starRingEnd ℂ) (censusWeight L a k) := by
  rw [← censusSqrtWeight_sq, ← censusSqrtWeight_sq, censusSqrtWeight_conjPerm, map_pow]

theorem norm_inv_censusSqrtWeight_sq_le {a : ℝ} (ha : 0 ≤ a) (k : Fin (censusFreq L).card) :
    ‖(censusSqrtWeight L a k)⁻¹‖ ^ 2 ≤ Real.exp (a * L) := by
  rw [← norm_pow, inv_pow, censusSqrtWeight_sq]
  exact norm_inv_censusWeight_le (L := L) ha k

/-! ## Value vectors and their real coefficient vectors -/

/-- The value vector supported on `{k, π k}` with value `z` at `k` and `z̄` at `π k`. -/
def censusData (k : Fin (censusFreq L).card) (z : ℂ) : Fin (censusFreq L).card → ℂ :=
  fun i => if i = k then z else if i = censusConjPerm L k then (starRingEnd ℂ) z else 0

theorem censusConjPerm_involutive (k : Fin (censusFreq L).card) :
    censusConjPerm L (censusConjPerm L k) = k := by
  apply censusNode_injective L
  rw [censusNode_censusConjPerm, censusNode_censusConjPerm, Complex.conj_conj]

/-- `W⁻¹ v` is real when `v` is conjugation-symmetric. -/
theorem isReal_inv_mulVec {v : Fin (censusFreq L).card → ℂ}
    (hv : ∀ i, v (censusConjPerm L i) = (starRingEnd ℂ) (v i)) (i : Fin (censusFreq L).card) :
    (starRingEnd ℂ) (((censusVandermonde L)⁻¹ *ᵥ v) i) = ((censusVandermonde L)⁻¹ *ᵥ v) i := by
  set W := censusVandermonde L
  set x := W⁻¹ *ᵥ v
  have hW : IsUnit W.det := isUnit_iff_ne_zero.2 (det_censusVandermonde_ne_zero L)
  have hWx : W *ᵥ x = v := by rw [mulVec_mulVec, mul_nonsing_inv _ hW, one_mulVec]
  have hWy : W *ᵥ (fun j => (starRingEnd ℂ) (x j)) = v := by
    funext k
    have h := congrFun hWx (censusConjPerm L k)
    rw [hv k] at h
    have h2 := congrArg (starRingEnd ℂ) h
    rw [Complex.conj_conj] at h2
    rw [← h2]
    simp only [mulVec, dotProduct, map_sum, map_mul, W, censusVandermonde, vandermonde_apply,
      map_pow, censusNode_censusConjPerm, Complex.conj_conj]
  have hy : (fun j => (starRingEnd ℂ) (x j)) = x := by
    have := congrArg (fun u => W⁻¹ *ᵥ u) hWy
    rwa [mulVec_mulVec, nonsing_inv_mul _ hW, one_mulVec] at this
  exact congrFun hy i

theorem censusData_symm {k : Fin (censusFreq L).card} {z : ℂ}
    (hz : censusConjPerm L k = k → (starRingEnd ℂ) z = z) (i : Fin (censusFreq L).card) :
    censusData L k z (censusConjPerm L i) = (starRingEnd ℂ) (censusData L k z i) := by
  unfold censusData
  by_cases hik : i = k
  · subst hik
    by_cases hfix : censusConjPerm L i = i
    · rw [if_pos hfix, if_pos rfl, hz hfix]
    · rw [if_neg hfix, if_pos rfl, if_pos rfl]
  · by_cases hik' : i = censusConjPerm L k
    · subst hik'
      rw [censusConjPerm_involutive, if_pos rfl, if_neg hik, if_pos rfl, Complex.conj_conj]
    · have h1 : censusConjPerm L i ≠ k := fun h => hik' (by
        rw [← h, censusConjPerm_involutive])
      have h2 : censusConjPerm L i ≠ censusConjPerm L k := fun h => hik ((censusConjPerm L).injective h)
      rw [if_neg h1, if_neg h2, if_neg hik, if_neg hik', map_zero]

/-! ## The Gram form in value coordinates -/

theorem heatMomentSection_eq_C (a : ℝ) (N : ℕ) : heatMomentSection a N = heatMomentMatrixC a N := by
  ext i j
  simp only [heatMomentSection, Matrix.map_apply, leadingMatrix, Matrix.of_apply, heatMomentArray,
    heatMomentMatrixC]
  exact Complex.ext (by simp) (by simp [im_xiHeatMoment])

/-- The coefficient vector `W⁻¹ v` of a value vector. -/
def censusCoeff (k : Fin (censusFreq L).card) (z : ℂ) : Fin (censusFreq L).card → ℂ :=
  (censusVandermonde L)⁻¹ *ᵥ censusData L k z

theorem vandermonde_mulVec_censusCoeff (k : Fin (censusFreq L).card) (z : ℂ) :
    censusVandermonde L *ᵥ censusCoeff L k z = censusData L k z := by
  have hW : IsUnit (censusVandermonde L).det := isUnit_iff_ne_zero.2 (det_censusVandermonde_ne_zero L)
  rw [censusCoeff, mulVec_mulVec, mul_nonsing_inv _ hW, one_mulVec]

theorem star_censusCoeff {k : Fin (censusFreq L).card} {z : ℂ}
    (hz : censusConjPerm L k = k → (starRingEnd ℂ) z = z) :
    star (censusCoeff L k z) = censusCoeff L k z := by
  funext i
  rw [Pi.star_apply, Complex.star_def]
  exact isReal_inv_mulVec L (censusData_symm L hz) i

theorem censusCoeff_dotProduct (a : ℝ) (k l : Fin (censusFreq L).card) (z z' : ℂ) :
    censusCoeff L k z ⬝ᵥ (heatMomentMatrixC a (censusFreq L).card *ᵥ censusCoeff L l z') =
      censusData L k z ⬝ᵥ ((diagonal (censusWeight L a) + censusHighCore L a) *ᵥ censusData L l z') := by
  rw [heatMomentMatrixC_eq, ← mulVec_mulVec, ← mulVec_mulVec, vandermonde_mulVec_censusCoeff,
    dotProduct_mulVec, vecMul_transpose, vandermonde_mulVec_censusCoeff]

/-- **Gram expansion** of the Hermitian form on combinations of real vectors. -/
theorem hermQuad_sum_of_star_eq {ι : Type*} (s : Finset ι) {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (u : ι → Fin n → ℂ) (hu : ∀ k, star (u k) = u k) (c : ι → ℂ) :
    hermQuad H (∑ k ∈ s, c k • u k) =
      (∑ k ∈ s, ∑ l ∈ s, (starRingEnd ℂ) (c k) * c l * (u k ⬝ᵥ H *ᵥ u l)).re := by
  unfold hermQuad
  congr 1
  rw [star_sum, mulVec_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [star_smul, hu, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    Complex.star_def]
  ring

/-! ## Index sets -/

/-- The indices of the upper off-line frequencies, `Im ν > 0`. -/
def censusUpper : Finset (Fin (censusFreq L).card) :=
  Finset.univ.filter fun k => 0 < (censusNode L k).im

/-- The indices with `Im ν ≥ 0`. -/
def censusNonneg : Finset (Fin (censusFreq L).card) :=
  Finset.univ.filter fun k => 0 ≤ (censusNode L k).im

theorem censusConjPerm_eq_self_iff (k : Fin (censusFreq L).card) :
    censusConjPerm L k = k ↔ (censusNode L k).im = 0 := by
  constructor
  · intro h
    have := censusNode_censusConjPerm L k
    rw [h] at this
    exact Complex.conj_eq_iff_im.1 this.symm
  · intro h
    apply censusNode_injective L
    rw [censusNode_censusConjPerm]
    exact Complex.conj_eq_iff_im.2 h

theorem im_censusNode_conjPerm (k : Fin (censusFreq L).card) :
    (censusNode L (censusConjPerm L k)).im = -(censusNode L k).im := by
  rw [censusNode_censusConjPerm, Complex.conj_im]

/-- Value vectors of distinct nonnegative indices have disjoint supports. -/
theorem censusData_mul_eq_zero {k l : Fin (censusFreq L).card} (hk : k ∈ censusNonneg L)
    (hl : l ∈ censusNonneg L) (hkl : k ≠ l) (z z' : ℂ) (i : Fin (censusFreq L).card) :
    censusData L k z i * censusData L l z' i = 0 := by
  have hk0 : 0 ≤ (censusNode L k).im := (Finset.mem_filter.1 hk).2
  have hl0 : 0 ≤ (censusNode L l).im := (Finset.mem_filter.1 hl).2
  unfold censusData
  by_cases h1 : i = k
  · subst h1
    rw [if_neg hkl]
    by_cases h2 : i = censusConjPerm L l
    · exfalso
      have him := im_censusNode_conjPerm L l
      rw [← h2] at him
      have hl' : (censusNode L l).im = 0 := by linarith
      have := (censusConjPerm_eq_self_iff L l).2 hl'
      exact hkl (h2.trans this)
    · rw [if_neg h2, mul_zero]
  · rw [if_neg h1]
    by_cases h3 : i = censusConjPerm L k
    · by_cases h4 : i = l
      · exfalso
        have him := im_censusNode_conjPerm L k
        rw [← h3, h4] at him
        have hk' : (censusNode L k).im = 0 := by linarith
        have := (censusConjPerm_eq_self_iff L k).2 hk'
        exact hkl (this.symm.trans (h3.symm.trans h4))
      · by_cases h5 : i = censusConjPerm L l
        · exfalso
          exact hkl ((censusConjPerm L).injective (h3.symm.trans h5))
        · rw [if_neg h4, if_neg h5, mul_zero]
    · rw [if_neg h3, zero_mul]

/-- The diagonal value of a normalized value vector: `c²` at a real node, `c² + c̄²` at a pair. -/
theorem censusData_diag_dot (a : ℝ) (k : Fin (censusFreq L).card) (c : ℂ) :
    censusData L k (c / censusSqrtWeight L a k) ⬝ᵥ
        (diagonal (censusWeight L a) *ᵥ censusData L k (c / censusSqrtWeight L a k)) =
      if censusConjPerm L k = k then c ^ 2 else c ^ 2 + (starRingEnd ℂ) (c ^ 2) := by
  have hs := censusSqrtWeight_ne_zero L a k
  have hsq := censusSqrtWeight_sq L a k
  have hkey : censusWeight L a k * (c / censusSqrtWeight L a k) ^ 2 = c ^ 2 := by
    rw [← hsq]; field_simp
  rw [dotProduct]
  simp only [mulVec_diagonal]
  by_cases hfix : censusConjPerm L k = k
  · rw [if_pos hfix, Finset.sum_eq_single k]
    · simp only [censusData, ↓reduceIte]
      rw [← hkey]; ring
    · intro i _ hik
      simp [censusData, hik, hfix]
    · simp
  · rw [if_neg hfix, Finset.sum_eq_add_of_mem k (censusConjPerm L k) (Finset.mem_univ _)
      (Finset.mem_univ _) (Ne.symm hfix)]
    · simp only [censusData, ↓reduceIte, hfix]
      rw [censusWeight_conjPerm]
      have h2 : (starRingEnd ℂ) (c / censusSqrtWeight L a k) * ((starRingEnd ℂ) (censusWeight L a k) *
          (starRingEnd ℂ) (c / censusSqrtWeight L a k)) = (starRingEnd ℂ) (c ^ 2) := by
        rw [← hkey, map_mul, map_pow]; ring
      rw [h2]
      linear_combination hkey
    · intro i _ hi
      have h1 : i ≠ k := fun h => hi.1 h
      have h2 : i ≠ censusConjPerm L k := fun h => hi.2 h
      simp [censusData, h1, h2]

/-! ## Near-diagonal Gram matrices of real families are definite -/

/-- **Gram lower bound.**  If the Gram matrix of a family of real vectors is within `δ` of a
diagonal matrix with entries `μ_k ≥ 1`, the Hermitian form on `Σ c_k u_k` is at least
`(1 − δ · #ι) Σ |c_k|²`. -/
theorem le_hermQuad_sum_of_gram {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (u : ι → Fin n → ℂ) (hu : ∀ k, star (u k) = u k)
    (μ : ι → ℝ) (hμ : ∀ k, 1 ≤ μ k) {δ : ℝ} (hδ : 0 ≤ δ)
    (hG : ∀ k l, ‖u k ⬝ᵥ H *ᵥ u l - (if k = l then (μ k : ℂ) else 0)‖ ≤ δ) (c : ι → ℂ) :
    (1 - δ * Fintype.card ι) * ∑ k, ‖c k‖ ^ 2 ≤ hermQuad H (∑ k, c k • u k) := by
  rw [hermQuad_sum_of_star_eq Finset.univ H u hu c]
  obtain ⟨E, hE⟩ : ∃ E : ι → ι → ℂ,
      E = fun k l => u k ⬝ᵥ H *ᵥ u l - (if k = l then (μ k : ℂ) else 0) := ⟨_, rfl⟩
  have hsplit : ∑ k, ∑ l, (starRingEnd ℂ) (c k) * c l * (u k ⬝ᵥ H *ᵥ u l) =
      ∑ k, ((μ k * ‖c k‖ ^ 2 : ℝ) : ℂ) + ∑ k, ∑ l, (starRingEnd ℂ) (c k) * c l * E k l := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : ∑ l, (starRingEnd ℂ) (c k) * c l * (u k ⬝ᵥ H *ᵥ u l) =
        ∑ l, (if k = l then (starRingEnd ℂ) (c k) * c l * (μ k : ℂ) else 0) +
          ∑ l, (starRingEnd ℂ) (c k) * c l * E k l := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hE]
      split_ifs <;> ring
    rw [h1, Finset.sum_ite_eq, if_pos (Finset.mem_univ _), Complex.conj_mul']
    push_cast
    ring
  have hnorm : ‖∑ k, ∑ l, (starRingEnd ℂ) (c k) * c l * E k l‖ ≤ δ * (∑ k, ‖c k‖) ^ 2 := by
    calc ‖∑ k, ∑ l, (starRingEnd ℂ) (c k) * c l * E k l‖
        ≤ ∑ k, ∑ l, ‖(starRingEnd ℂ) (c k) * c l * E k l‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _)
      _ ≤ ∑ k, ∑ l, δ * (‖c k‖ * ‖c l‖) :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => by
            rw [norm_mul, norm_mul, Complex.norm_conj, mul_comm δ]
            have hkl : ‖E k l‖ ≤ δ := by rw [hE]; exact hG k l
            exact mul_le_mul_of_nonneg_left hkl (by positivity)
      _ = δ * (∑ k, ‖c k‖) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
  have hcs : (∑ k, ‖c k‖) ^ 2 ≤ Fintype.card ι * ∑ k, ‖c k‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => ‖c k‖)
    rwa [Finset.card_univ] at this
  have hμsum : ∑ k, ‖c k‖ ^ 2 ≤ ∑ k, μ k * ‖c k‖ ^ 2 :=
    Finset.sum_le_sum fun k _ => le_mul_of_one_le_left (sq_nonneg _) (hμ k)
  rw [hsplit, Complex.add_re, Complex.re_sum]
  simp only [Complex.ofReal_re]
  have hre := (abs_le.1 (Complex.abs_re_le_norm
    (∑ k, ∑ l, (starRingEnd ℂ) (c k) * c l * E k l))).1
  nlinarith [mul_le_mul_of_nonneg_left hcs hδ]

/-- **Definiteness from a near-diagonal Gram matrix.**  Under the hypotheses of
`le_hermQuad_sum_of_gram` with `δ · #ι < 1`, the form is positive definite on the span of the
family and the family is linearly independent. -/
theorem isPosDefOn_span_of_gram {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (u : ι → Fin n → ℂ) (hu : ∀ k, star (u k) = u k)
    (μ : ι → ℝ) (hμ : ∀ k, 1 ≤ μ k) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ * Fintype.card ι < 1)
    (hG : ∀ k l, ‖u k ⬝ᵥ H *ᵥ u l - (if k = l then (μ k : ℂ) else 0)‖ ≤ δ) :
    IsPosDefOn H (Submodule.span ℂ (Set.range u)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range u)) = Fintype.card ι := by
  have hpos : ∀ c : ι → ℂ, c ≠ 0 → 0 < hermQuad H (∑ k, c k • u k) := by
    intro c hc
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hc
    have hsum : 0 < ∑ k, ‖c k‖ ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hk) 2⟩
    exact (mul_pos (by linarith) hsum).trans_le (le_hermQuad_sum_of_gram H u hu μ hμ hδ hG c)
  have hli : LinearIndependent ℂ u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    by_contra hi
    have h := hpos c fun h => hi (congrFun h i)
    rw [hc] at h
    simp [hermQuad] at h
  refine ⟨fun x hx hx0 => ?_, finrank_span_eq_card hli⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx
  exact hpos c fun h => hx0 (by simp [h])

/-! ## The normalized size of the high core -/

/-- `δ(a) = Σ_{i,j} e^{aL} |Y_{ij}(a)|`. -/
def censusDefect (a : ℝ) : ℝ := ∑ i, ∑ j, Real.exp (a * L) * ‖censusHighCore L a i j‖

theorem censusDefect_nonneg (a : ℝ) : 0 ≤ censusDefect L a :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem tendsto_exp_mul_norm_censusHighCore (k j : Fin (censusFreq L).card) :
    Tendsto (fun a : ℝ => Real.exp (a * L) * ‖censusHighCore L a k j‖) atTop (𝓝 0) := by
  obtain ⟨g, hg, hgap⟩ := exists_gap_above_level L
  set S₀ := ∑' q : XiZeroCopy, (1 + ‖xiHeatFrequency q‖) ^ (2 * (censusFreq L).card) *
    Real.exp (-(1 * (xiHeatFrequency q).re))
  set C : ℝ := ∑ l, ∑ m, ‖(censusVandermonde L)⁻¹ l k‖ * ‖(censusVandermonde L)⁻¹ m j‖
  have hlim : Tendsto (fun a : ℝ => Real.exp (-(a * g))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hg)
  have hbound : ∀ a : ℝ, 1 ≤ a → ‖Real.exp (a * L) * ‖censusHighCore L a k j‖‖ ≤
      C * S₀ * Real.exp (L + g) * Real.exp (-(a * g)) := by
    intro a ha
    have hY : ‖censusHighCore L a k j‖ ≤ C * (S₀ * Real.exp (-((a - 1) * (L + g)))) :=
      norm_censusHighCore_le ha hgap k j
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.exp (a * L) * ‖censusHighCore L a k j‖
        ≤ Real.exp (a * L) * (C * (S₀ * Real.exp (-((a - 1) * (L + g))))) :=
          mul_le_mul_of_nonneg_left hY (Real.exp_pos _).le
      _ = C * S₀ * (Real.exp (a * L) * Real.exp (-((a - 1) * (L + g)))) := by ring
      _ = C * S₀ * (Real.exp (L + g) * Real.exp (-(a * g))) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 2
          ring
      _ = C * S₀ * Real.exp (L + g) * Real.exp (-(a * g)) := by ring
  have hzero : Tendsto (fun a : ℝ => C * S₀ * Real.exp (L + g) * Real.exp (-(a * g))) atTop (𝓝 0) := by
    simpa using hlim.const_mul (C * S₀ * Real.exp (L + g))
  exact squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨1, hbound⟩) hzero

theorem tendsto_censusDefect : Tendsto (censusDefect L) atTop (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => tendsto_exp_mul_norm_censusHighCore L i j
  rw [show censusDefect L = fun a => ∑ i, ∑ j, Real.exp (a * L) * ‖censusHighCore L a i j‖ from rfl]
  simpa using h

theorem norm_censusData_le (k : Fin (censusFreq L).card) (z : ℂ) (i : Fin (censusFreq L).card) :
    ‖censusData L k z i‖ ≤ ‖z‖ := by
  unfold censusData
  split_ifs <;> simp

/-- The high core seen by two normalized value vectors is at most `δ(a)`. -/
theorem norm_censusData_highCore_le {a : ℝ} (ha : 0 ≤ a) (k l : Fin (censusFreq L).card)
    {c c' : ℂ} (hc : ‖c‖ = 1) (hc' : ‖c'‖ = 1) :
    ‖censusData L k (c / censusSqrtWeight L a k) ⬝ᵥ
        (censusHighCore L a *ᵥ censusData L l (c' / censusSqrtWeight L a l))‖ ≤ censusDefect L a := by
  have hk := norm_inv_censusSqrtWeight_sq_le L ha k
  have hl := norm_inv_censusSqrtWeight_sq_le L ha l
  have hprod : ‖(censusSqrtWeight L a k)⁻¹‖ * ‖(censusSqrtWeight L a l)⁻¹‖ ≤ Real.exp (a * L) := by
    nlinarith [sq_nonneg (‖(censusSqrtWeight L a k)⁻¹‖ - ‖(censusSqrtWeight L a l)⁻¹‖)]
  have hdk : ∀ i, ‖censusData L k (c / censusSqrtWeight L a k) i‖ ≤ ‖(censusSqrtWeight L a k)⁻¹‖ :=
    fun i => (norm_censusData_le L k _ i).trans (by rw [div_eq_mul_inv, norm_mul, hc, one_mul])
  have hdl : ∀ j, ‖censusData L l (c' / censusSqrtWeight L a l) j‖ ≤ ‖(censusSqrtWeight L a l)⁻¹‖ :=
    fun j => (norm_censusData_le L l _ j).trans (by rw [div_eq_mul_inv, norm_mul, hc', one_mul])
  rw [censusDefect]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
  rw [norm_mul, norm_mul]
  calc ‖censusData L k (c / censusSqrtWeight L a k) i‖ *
        (‖censusHighCore L a i j‖ * ‖censusData L l (c' / censusSqrtWeight L a l) j‖)
      ≤ ‖(censusSqrtWeight L a k)⁻¹‖ * (‖censusHighCore L a i j‖ * ‖(censusSqrtWeight L a l)⁻¹‖) :=
        mul_le_mul (hdk i) (mul_le_mul_of_nonneg_left (hdl j) (norm_nonneg _)) (by positivity)
          (norm_nonneg _)
    _ = (‖(censusSqrtWeight L a k)⁻¹‖ * ‖(censusSqrtWeight L a l)⁻¹‖) * ‖censusHighCore L a i j‖ := by
        ring
    _ ≤ Real.exp (a * L) * ‖censusHighCore L a i j‖ :=
        mul_le_mul_of_nonneg_right hprod (norm_nonneg _)

/-- Value vectors of distinct nonnegative indices are orthogonal for the low part. -/
theorem censusData_diag_dot_eq_zero (a : ℝ) {k l : Fin (censusFreq L).card} (hk : k ∈ censusNonneg L)
    (hl : l ∈ censusNonneg L) (hkl : k ≠ l) (z z' : ℂ) :
    censusData L k z ⬝ᵥ (diagonal (censusWeight L a) *ᵥ censusData L l z') = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mulVec_diagonal]
  linear_combination (censusWeight L a i) * censusData_mul_eq_zero L hk hl hkl z z' i

/-- **The Gram matrix of the normalized coefficient vectors.**  For unimodular `γ`, the vectors
`u_k = W⁻¹ d_k(γ_k / s_k)`, `k` with `Im ν_k ≥ 0`, have Gram entries within `δ(a)` of the diagonal
values `γ_k²` (real node) and `γ_k² + \overline{γ_k²}` (pair). -/
theorem norm_censusCoeff_gram_sub_le {a : ℝ} (ha : 0 ≤ a) (γ : Fin (censusFreq L).card → ℂ)
    (hγ : ∀ k, ‖γ k‖ = 1) {k l : Fin (censusFreq L).card} (hk : k ∈ censusNonneg L)
    (hl : l ∈ censusNonneg L) :
    ‖censusCoeff L k (γ k / censusSqrtWeight L a k) ⬝ᵥ
        (heatMomentMatrixC a (censusFreq L).card *ᵥ censusCoeff L l (γ l / censusSqrtWeight L a l)) -
      (if k = l then (if censusConjPerm L k = k then γ k ^ 2 else γ k ^ 2 + (starRingEnd ℂ) (γ k ^ 2))
        else 0)‖ ≤ censusDefect L a := by
  rw [censusCoeff_dotProduct, add_mulVec, dotProduct_add]
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl, censusData_diag_dot, add_sub_cancel_left]
    exact norm_censusData_highCore_le L ha k k (hγ k) (hγ k)
  · rw [if_neg hkl, censusData_diag_dot_eq_zero L a hk hl hkl, zero_add, sub_zero]
    exact norm_censusData_highCore_le L ha k l (hγ k) (hγ l)

/-! ## The two definite families -/

theorem conj_censusSqrtWeight_of_fixed {a : ℝ} {k : Fin (censusFreq L).card}
    (hk : censusConjPerm L k = k) :
    (starRingEnd ℂ) (censusSqrtWeight L a k) = censusSqrtWeight L a k := by
  rw [← censusSqrtWeight_conjPerm, hk]

theorem not_fixed_of_mem_censusUpper {k : Fin (censusFreq L).card} (hk : k ∈ censusUpper L) :
    censusConjPerm L k ≠ k := fun h =>
  (Finset.mem_filter.1 hk).2.ne' ((censusConjPerm_eq_self_iff L k).1 h)

theorem censusUpper_subset : censusUpper L ⊆ censusNonneg L := fun _ hk =>
  Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hk).2.le⟩

/-- The negative family `u_k = W⁻¹ d_k(i / s_k)` over the upper off-line frequencies. -/
def censusNegVec (a : ℝ) (k : ↥(censusUpper L)) : Fin (censusFreq L).card → ℂ :=
  censusCoeff L k (Complex.I / censusSqrtWeight L a k)

/-- The positive family `u_k = W⁻¹ d_k(1 / s_k)` over the frequencies with `Im ν ≥ 0`. -/
def censusPosVec (a : ℝ) (k : ↥(censusNonneg L)) : Fin (censusFreq L).card → ℂ :=
  censusCoeff L k (1 / censusSqrtWeight L a k)

theorem star_censusNegVec (a : ℝ) (k : ↥(censusUpper L)) :
    star (censusNegVec L a k) = censusNegVec L a k :=
  star_censusCoeff L fun h => absurd h (not_fixed_of_mem_censusUpper L k.2)

theorem star_censusPosVec (a : ℝ) (k : ↥(censusNonneg L)) :
    star (censusPosVec L a k) = censusPosVec L a k :=
  star_censusCoeff L fun h => by rw [map_div₀, map_one, conj_censusSqrtWeight_of_fixed L h]

/-- Each upper pair contributes the diagonal value `−2`. -/
theorem norm_censusNegVec_gram_sub_le {a : ℝ} (ha : 0 ≤ a) (k l : ↥(censusUpper L)) :
    ‖censusNegVec L a k ⬝ᵥ (-heatMomentMatrixC a (censusFreq L).card) *ᵥ censusNegVec L a l -
      (if k = l then ((2 : ℝ) : ℂ) else 0)‖ ≤ censusDefect L a := by
  have h := norm_censusCoeff_gram_sub_le L ha (fun _ => Complex.I) (fun _ => by simp)
    (censusUpper_subset L k.2) (censusUpper_subset L l.2)
  beta_reduce at h
  unfold censusNegVec
  rw [neg_mulVec, dotProduct_neg]
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl, if_neg (not_fixed_of_mem_censusUpper L k.2)] at h
    rw [if_pos rfl]
    have hI : Complex.I ^ 2 + (starRingEnd ℂ) (Complex.I ^ 2) = -2 := by
      rw [Complex.I_sq, map_neg, map_one]; norm_num
    rw [hI] at h
    rw [show ∀ x : ℂ, -x - ((2 : ℝ) : ℂ) = -(x - -2) from fun x => by push_cast; ring, norm_neg]
    exact h
  · have hkl' : (k : Fin (censusFreq L).card) ≠ l := fun h' => hkl (Subtype.ext h')
    rw [if_neg hkl'] at h
    rw [if_neg hkl, sub_zero, norm_neg]
    rwa [sub_zero] at h

/-- A real node contributes the diagonal value `1`, an upper pair `2`. -/
theorem norm_censusPosVec_gram_sub_le {a : ℝ} (ha : 0 ≤ a) (k l : ↥(censusNonneg L)) :
    ‖censusPosVec L a k ⬝ᵥ heatMomentMatrixC a (censusFreq L).card *ᵥ censusPosVec L a l -
      (if k = l then (((if censusConjPerm L k = k then 1 else 2 : ℝ)) : ℂ) else 0)‖ ≤
        censusDefect L a := by
  have h := norm_censusCoeff_gram_sub_le L ha (fun _ => 1) (fun _ => by simp) k.2 l.2
  beta_reduce at h
  unfold censusPosVec
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl] at h ⊢
    have hval : (if censusConjPerm L k = k then (1 : ℂ) ^ 2 else 1 ^ 2 + (starRingEnd ℂ) (1 ^ 2)) =
        (((if censusConjPerm L k = k then 1 else 2 : ℝ)) : ℂ) := by
      split_ifs <;> norm_num
    rw [hval] at h
    exact h
  · have hkl' : (k : Fin (censusFreq L).card) ≠ l := fun h' => hkl (Subtype.ext h')
    rw [if_neg hkl'] at h
    rw [if_neg hkl]
    exact h

theorem card_censusNonneg_add_card_censusUpper :
    (censusNonneg L).card + (censusUpper L).card = (censusFreq L).card := by
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (censusFreq L).card))) (fun k => 0 ≤ (censusNode L k).im)
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 : (censusUpper L).card =
      (Finset.univ.filter fun k : Fin (censusFreq L).card => ¬ 0 ≤ (censusNode L k).im).card := by
    refine Finset.card_bij (fun k _ => censusConjPerm L k) (fun k hk => ?_)
      (fun k₁ _ k₂ _ h => (censusConjPerm L).injective h) (fun k hk => ?_)
    · rw [censusUpper, Finset.mem_filter] at hk
      rw [Finset.mem_filter, im_censusNode_conjPerm]
      exact ⟨Finset.mem_univ _, not_le.2 (by linarith [hk.2])⟩
    · rw [Finset.mem_filter] at hk
      refine ⟨censusConjPerm L k, ?_, censusConjPerm_involutive L k⟩
      rw [censusUpper, Finset.mem_filter, im_censusNode_conjPerm]
      exact ⟨Finset.mem_univ _, by linarith [not_le.1 hk.2]⟩
  rw [h2]
  exact h1

/-! ## Exact large-time inertia -/

/-- **Exact large-time inertia, census form.**  For all large heat times the rank-`|S_L|` section
has negative index the number of upper off-line frequencies and positive index the number of
frequencies with `Im ν ≥ 0`. -/
theorem eventually_hermNegIndex_eq_card_censusUpper :
    ∀ᶠ a in atTop, hermNegIndex (heatMomentSection a (censusFreq L).card) = (censusUpper L).card ∧
      hermPosIndex (heatMomentSection a (censusFreq L).card) = (censusNonneg L).card := by
  have hN : (0 : ℝ) < (censusFreq L).card + 1 := by positivity
  have hev : ∀ᶠ a in atTop, censusDefect L a < 1 / ((censusFreq L).card + 1) :=
    (tendsto_censusDefect L).eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev, eventually_ge_atTop 0] with a hδ ha
  have hδ0 := censusDefect_nonneg L a
  rw [lt_div_iff₀ hN] at hδ
  have hcard : ∀ s : Finset (Fin (censusFreq L).card),
      censusDefect L a * (Fintype.card ↥s : ℝ) < 1 := by
    intro s
    have : (Fintype.card ↥s : ℝ) ≤ (censusFreq L).card := by
      rw [Fintype.card_coe]
      exact_mod_cast (Finset.card_le_univ s).trans (Fintype.card_fin _).le
    nlinarith
  set M := heatMomentMatrixC a (censusFreq L).card
  have hsec : heatMomentSection a (censusFreq L).card = M := heatMomentSection_eq_C a _
  obtain ⟨hnegdef, hnegrank⟩ := isPosDefOn_span_of_gram (-M) (censusNegVec L a)
    (star_censusNegVec L a) (fun _ => 2) (fun _ => by norm_num) hδ0 (hcard _)
    (norm_censusNegVec_gram_sub_le L ha)
  obtain ⟨hposdef, hposrank⟩ := isPosDefOn_span_of_gram M (censusPosVec L a)
    (star_censusPosVec L a) (fun k => if censusConjPerm L k = k then 1 else 2)
    (fun k => by split_ifs <;> norm_num) hδ0 (hcard _) (norm_censusPosVec_gram_sub_le L ha)
  have hneg : (censusUpper L).card ≤ hermNegIndex M := by
    have := finrank_le_posIndex hnegdef
    rwa [hnegrank, Fintype.card_coe] at this
  have hpos : (censusNonneg L).card ≤ hermPosIndex M := by
    have := finrank_le_posIndex hposdef
    rwa [hposrank, Fintype.card_coe] at this
  have hsum := posIndex_add_negIndex_add_nullIndex
    (isHermitian_heatMomentSection a (censusFreq L).card)
  rw [hsec, Fintype.card_fin] at hsum
  have hc := card_censusNonneg_add_card_censusUpper L
  rw [hsec]
  omega

theorem censusFreq_eq_heatFrequenciesBelow : censusFreq L = heatFrequenciesBelow L := by
  ext w
  rw [mem_censusFreq, mem_heatFrequenciesBelow]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, rfl, hq⟩
  · rintro ⟨q, rfl, hq⟩
    exact ⟨q, hq, rfl⟩

theorem card_censusUpper : (censusUpper L).card = (lowUpperHeatFrequencies L).card := by
  rw [lowUpperHeatFrequencies, ← censusFreq_eq_heatFrequenciesBelow]
  refine Finset.card_bij (fun k _ => censusNode L k) (fun k hk => ?_)
    (fun k₁ _ k₂ _ h => censusNode_injective L h) (fun w hw => ?_)
  · exact Finset.mem_filter.2 ⟨censusNode_mem L k, (Finset.mem_filter.1 hk).2⟩
  · obtain ⟨hw, him⟩ := Finset.mem_filter.1 hw
    refine ⟨(censusFreqEnum L).symm ⟨w, hw⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [censusNode, Equiv.apply_symm_apply]
      exact him
    · rw [censusNode, Equiv.apply_symm_apply]

/-- **Exact large-time inertia.**  For every level `L`, for all large heat times the heat Hankel
section of rank `|S_L|` has negative index exactly the number of upper off-line heat frequencies
with `Re w ≤ L`. -/
theorem eventually_hermNegIndex_heatMomentSection_eq :
    ∀ᶠ a in atTop, hermNegIndex (heatMomentSection a (heatFrequenciesBelow L).card) =
      (lowUpperHeatFrequencies L).card := by
  filter_upwards [eventually_hermNegIndex_eq_card_censusUpper L] with a ha
  rw [← censusFreq_eq_heatFrequenciesBelow, ← card_censusUpper]
  exact ha.1

/-- **RH as large-time definiteness at every level.**  RH holds iff for every level `L` the rank-`|S_L|`
heat Hankel section has negative index `0` for all large heat times. -/
theorem riemannHypothesis_iff_forall_eventually_hermNegIndex_eq_zero :
    RiemannHypothesis ↔ ∀ L : ℝ, ∀ᶠ a in atTop,
      hermNegIndex (heatMomentSection a (heatFrequenciesBelow L).card) = 0 := by
  constructor
  · intro hRH L
    filter_upwards [eventually_hermNegIndex_heatMomentSection_eq L] with a ha
    rw [ha, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    obtain ⟨hw, him⟩ := Finset.mem_filter.1 hw
    obtain ⟨q, rfl, -⟩ := mem_heatFrequenciesBelow.1 hw
    have hq := (riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero.1 hRH) q
    exact (xiHeatFrequency_im_ne_zero_iff q).1 him.ne' hq
  · intro h
    by_contra hRH
    rw [riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero] at hRH
    push Not at hRH
    obtain ⟨q, hq⟩ := hRH
    have hw := (xiHeatFrequency_im_ne_zero_iff q).2 hq
    obtain ⟨u, hu, him⟩ : ∃ u ∈ heatFrequenciesBelow (xiHeatFrequency q).re, 0 < u.im := by
      rcases lt_or_gt_of_ne hw with hlt | hgt
      · refine ⟨(starRingEnd ℂ) (xiHeatFrequency q), conj_mem_heatFrequenciesBelow
          (mem_heatFrequenciesBelow.2 ⟨q, rfl, le_rfl⟩), ?_⟩
        rw [Complex.conj_im]
        linarith
      · exact ⟨_, mem_heatFrequenciesBelow.2 ⟨q, rfl, le_rfl⟩, hgt⟩
    obtain ⟨a, ha0, ha⟩ := ((h (xiHeatFrequency q).re).and
      (eventually_hermNegIndex_heatMomentSection_eq (xiHeatFrequency q).re)).exists
    rw [ha0] at ha
    have hpos : 0 < (lowUpperHeatFrequencies (xiHeatFrequency q).re).card :=
      Finset.card_pos.2 ⟨u, Finset.mem_filter.2 ⟨hu, him⟩⟩
    omega

end

end RHTower
