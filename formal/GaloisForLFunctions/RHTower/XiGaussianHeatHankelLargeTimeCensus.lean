import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLargeTimeDetection
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelDeterminantBlowup

/-!
# The large-time census of the heat Hankel ladder

Fix a level `L` and let `S_L` be the finitely many distinct heat frequencies `w` with `Re w ≤ L`,
`N = |S_L|`.  Complex conjugation permutes `S_L` (`censusConjPerm`); it fixes the real frequencies
(zeros on the line) and swaps each off-line pair `u, ū`.

**Theorem** (`eventually_sign_mul_heatMomentDet_pos`).  For all large heat times,

`sign(conj on S_L) · Δ_N(a) > 0`.

So the large-time sign of the rank-`N` determinant is the parity of the number of off-line pairs
below the level.  In particular `Δ_N(a) > 0` eventually when no off-line frequency lies below `L`
(`eventually_heatMomentDet_pos_of_censusFreq_real`).

Proof.  Write the moment matrix as `M = Wᵀ (D + Y) W` with `W` the Vandermonde matrix of `S_L` and
`D = diag(m_w e^{−a w})` (`m_w` the multiplicity).  `Y` collects the frequencies above `L`, whose real
parts exceed `L` by a fixed gap `g`; hence `D⁻¹ Y = O(e^{−a g})` and `det(I + D⁻¹ Y) → 1`.
* The product `∏ m_w e^{−aw}` is positive, since `S_L` is closed under conjugation.
* Conjugation permutes the rows of `W`, so `conj(det W) = sign(π) det W` and
  `(det W)² = sign(π) |det W|²` (`vandermonde_det_sq_eq_sign_mul_normSq`).
-/

open Complex Matrix Filter Topology
open GaloisForLFunctions.HTGeometry (leadingMatrix)

namespace RHTower

noncomputable section

/-! ## The frequencies below a level -/

/-- The zero copies with heat frequency of real part `≤ L`. -/
def censusCopies (L : ℝ) : Finset XiZeroCopy := (finite_setOf_re_xiHeatFrequency_le L).toFinset

theorem mem_censusCopies {L : ℝ} {q : XiZeroCopy} :
    q ∈ censusCopies L ↔ (xiHeatFrequency q).re ≤ L := by
  rw [censusCopies, Set.Finite.mem_toFinset]
  rfl

/-- The distinct heat frequencies of real part `≤ L`. -/
def censusFreq (L : ℝ) : Finset ℂ := (censusCopies L).image xiHeatFrequency

theorem mem_censusFreq {L : ℝ} {w : ℂ} :
    w ∈ censusFreq L ↔ ∃ q : XiZeroCopy, (xiHeatFrequency q).re ≤ L ∧ xiHeatFrequency q = w := by
  rw [censusFreq, Finset.mem_image]
  simp only [mem_censusCopies]

theorem conj_mem_censusFreq {L : ℝ} {w : ℂ} (hw : w ∈ censusFreq L) :
    (starRingEnd ℂ) w ∈ censusFreq L := by
  obtain ⟨q, hq, rfl⟩ := mem_censusFreq.1 hw
  refine mem_censusFreq.2 ⟨xiZeroCopyLineConjEquiv q, ?_, xiHeatFrequency_lineConj q⟩
  rw [xiHeatFrequency_lineConj, Complex.conj_re]
  exact hq

/-- Complex conjugation as a permutation of the low frequencies. -/
def censusFreqConj (L : ℝ) : ↥(censusFreq L) ≃ ↥(censusFreq L) where
  toFun w := ⟨(starRingEnd ℂ) w, conj_mem_censusFreq w.2⟩
  invFun w := ⟨(starRingEnd ℂ) w, conj_mem_censusFreq w.2⟩
  left_inv w := Subtype.ext (Complex.conj_conj w.1)
  right_inv w := Subtype.ext (Complex.conj_conj w.1)

/-- An enumeration of the low frequencies. -/
def censusFreqEnum (L : ℝ) : Fin (censusFreq L).card ≃ ↥(censusFreq L) := (censusFreq L).equivFin.symm

/-- The `k`-th low frequency. -/
def censusNode (L : ℝ) (k : Fin (censusFreq L).card) : ℂ := (censusFreqEnum L k : ℂ)

theorem censusNode_mem (L : ℝ) (k : Fin (censusFreq L).card) : censusNode L k ∈ censusFreq L :=
  (censusFreqEnum L k).2

theorem censusNode_injective (L : ℝ) : Function.Injective (censusNode L) := fun _ _ h =>
  (censusFreqEnum L).injective (Subtype.ext h)

/-- Complex conjugation as a permutation of the indices. -/
def censusConjPerm (L : ℝ) : Equiv.Perm (Fin (censusFreq L).card) :=
  (censusFreqEnum L).trans ((censusFreqConj L).trans (censusFreqEnum L).symm)

theorem censusNode_censusConjPerm (L : ℝ) (k : Fin (censusFreq L).card) :
    censusNode L (censusConjPerm L k) = (starRingEnd ℂ) (censusNode L k) := by
  simp [censusNode, censusConjPerm, censusFreqConj]

/-- The multiplicity of a heat frequency among the copies below `L`. -/
def censusMult (L : ℝ) (w : ℂ) : ℕ := ((censusCopies L).filter fun q => xiHeatFrequency q = w).card

theorem censusMult_pos (L : ℝ) (k : Fin (censusFreq L).card) : 0 < censusMult L (censusNode L k) := by
  obtain ⟨q, hq, hqk⟩ := mem_censusFreq.1 (censusNode_mem L k)
  exact Finset.card_pos.2 ⟨q, Finset.mem_filter.2 ⟨mem_censusCopies.2 hq, hqk⟩⟩

/-- **Regrouping by frequency.** -/
theorem sum_censusCopies_eq (L : ℝ) (f : ℂ → ℂ) :
    ∑ q ∈ censusCopies L, f (xiHeatFrequency q) =
      ∑ k : Fin (censusFreq L).card, (censusMult L (censusNode L k) : ℂ) * f (censusNode L k) := by
  classical
  rw [Finset.sum_comp f xiHeatFrequency]
  rw [show Finset.image xiHeatFrequency (censusCopies L) = censusFreq L from rfl,
    ← Finset.sum_coe_sort (censusFreq L)]
  rw [← Equiv.sum_comp (censusFreqEnum L)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nsmul_eq_mul]
  rfl

/-! ## The Vandermonde sign law -/

/-- The Vandermonde matrix of the low frequencies. -/
def censusVandermonde (L : ℝ) : Matrix (Fin (censusFreq L).card) (Fin (censusFreq L).card) ℂ :=
  vandermonde (censusNode L)

theorem det_censusVandermonde_ne_zero (L : ℝ) : (censusVandermonde L).det ≠ 0 :=
  det_vandermonde_ne_zero_iff.2 (censusNode_injective L)

/-- Conjugation permutes the rows: `conj(det W) = sign(π) det W`. -/
theorem conj_det_censusVandermonde (L : ℝ) :
    (starRingEnd ℂ) (censusVandermonde L).det =
      ((Equiv.Perm.sign (censusConjPerm L) : ℤ) : ℂ) * (censusVandermonde L).det := by
  rw [RingHom.map_det]
  have h : (starRingEnd ℂ).mapMatrix (censusVandermonde L) =
      (censusVandermonde L).submatrix (censusConjPerm L) id := by
    ext k j
    simp [censusVandermonde, vandermonde_apply, censusNode_censusConjPerm, map_pow]
  rw [h, det_permute]

/-- **The sign of the squared Vandermonde.**  `(det W)² = sign(π) · |det W|²`. -/
theorem vandermonde_det_sq_eq_sign_mul_normSq (L : ℝ) :
    (censusVandermonde L).det ^ 2 =
      ((Equiv.Perm.sign (censusConjPerm L) : ℤ) : ℂ) * (Complex.normSq (censusVandermonde L).det : ℂ) := by
  set d := (censusVandermonde L).det
  set σ : ℂ := ((Equiv.Perm.sign (censusConjPerm L) : ℤ) : ℂ)
  have hσ2 : σ * σ = 1 := by
    have : (Equiv.Perm.sign (censusConjPerm L) : ℤ) * (Equiv.Perm.sign (censusConjPerm L) : ℤ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (censusConjPerm L)) with h | h <;> simp [h]
    simp only [σ]
    exact_mod_cast this
  have hc := conj_det_censusVandermonde L
  rw [← Complex.mul_conj, hc]
  linear_combination (-d ^ 2) * hσ2

/-! ## The moment matrix split at the level -/

/-- The complex moment matrix `(M_{i+j}(a))_{i,j<N}`. -/
def heatMomentMatrixC (a : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => xiHeatMoment ((i : ℕ) + j) a

theorem heatMomentDet_ofReal (a : ℝ) (N : ℕ) :
    ((heatMomentDet N a : ℝ) : ℂ) = (heatMomentMatrixC a N).det := by
  rw [heatMomentDet, show ((leadingMatrix (heatMomentArray a) N).det : ℂ) =
    Complex.ofRealHom (leadingMatrix (heatMomentArray a) N).det from rfl, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, leadingMatrix, heatMomentArray,
    Matrix.of_apply, heatMomentMatrixC, Complex.ofRealHom_eq_coe]
  exact Complex.ext (by simp) (by simp [im_xiHeatMoment])

/-- The weights `m_w e^{−a w}` of the low frequencies. -/
def censusWeight (L a : ℝ) (k : Fin (censusFreq L).card) : ℂ :=
  (censusMult L (censusNode L k) : ℂ) * Complex.exp (-(a : ℂ) * censusNode L k)

theorem censusWeight_ne_zero (L a : ℝ) (k : Fin (censusFreq L).card) : censusWeight L a k ≠ 0 :=
  mul_ne_zero (by exact_mod_cast (censusMult_pos L k).ne') (Complex.exp_ne_zero _)

/-- The low part `Wᵀ D W` of the moment matrix. -/
def censusLowPart (L a : ℝ) : Matrix (Fin (censusFreq L).card) (Fin (censusFreq L).card) ℂ :=
  (censusVandermonde L)ᵀ * diagonal (censusWeight L a) * censusVandermonde L

theorem censusLowPart_apply (L a : ℝ) (i j : Fin (censusFreq L).card) :
    censusLowPart L a i j = ∑ q ∈ censusCopies L,
      xiHeatFrequency q ^ ((i : ℕ) + j) * Complex.exp (-(a : ℂ) * xiHeatFrequency q) := by
  rw [sum_censusCopies_eq L (fun w => w ^ ((i : ℕ) + j) * Complex.exp (-(a : ℂ) * w)), censusLowPart,
    Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_diagonal, transpose_apply, censusVandermonde, vandermonde_apply, vandermonde_apply,
    censusWeight, pow_add]
  ring

/-- The part of the moment matrix carried by the frequencies above `L`. -/
def censusHighPart (L a : ℝ) : Matrix (Fin (censusFreq L).card) (Fin (censusFreq L).card) ℂ :=
  heatMomentMatrixC a (censusFreq L).card - censusLowPart L a

theorem censusHighPart_apply {L a : ℝ} (ha : 0 < a) (i j : Fin (censusFreq L).card) :
    censusHighPart L a i j = ∑' q : ↥((censusCopies L : Set XiZeroCopy)ᶜ),
      xiHeatFrequency q ^ ((i : ℕ) + j) * Complex.exp (-(a : ℂ) * xiHeatFrequency q) := by
  have h := (summable_pow_mul_exp_xiHeatFrequency ha ((i : ℕ) + j)).sum_add_tsum_compl
    (s := censusCopies L)
  rw [censusHighPart, Matrix.sub_apply, heatMomentMatrixC, Matrix.of_apply, xiHeatMoment, censusLowPart_apply,
    ← h]
  ring

/-- **A gap above the level.** -/
theorem exists_gap_above_level (L : ℝ) :
    ∃ g : ℝ, 0 < g ∧ ∀ q : XiZeroCopy, L < (xiHeatFrequency q).re → L + g ≤ (xiHeatFrequency q).re := by
  classical
  set G := (finite_setOf_re_xiHeatFrequency_le (L + 1)).toFinset.filter
    fun q => L < (xiHeatFrequency q).re
  rcases G.eq_empty_or_nonempty with hG | hG
  · refine ⟨1, one_pos, fun q hq => ?_⟩
    by_contra h
    have hmem : q ∈ G := Finset.mem_filter.2 ⟨by
      rw [Set.Finite.mem_toFinset]; show (xiHeatFrequency q).re ≤ L + 1; linarith, hq⟩
    rw [hG] at hmem
    exact Finset.notMem_empty q hmem
  · obtain ⟨q₀, hq₀, hmin⟩ := G.exists_min_image (fun q => (xiHeatFrequency q).re) hG
    have hq₀L : L < (xiHeatFrequency q₀).re := (Finset.mem_filter.1 hq₀).2
    refine ⟨min 1 ((xiHeatFrequency q₀).re - L), lt_min one_pos (by linarith), fun q hq => ?_⟩
    by_cases hq1 : (xiHeatFrequency q).re ≤ L + 1
    · have hmem : q ∈ G := Finset.mem_filter.2 ⟨by
        rw [Set.Finite.mem_toFinset]; exact hq1, hq⟩
      have := hmin q hmem
      have := min_le_right 1 ((xiHeatFrequency q₀).re - L)
      linarith
    · have := min_le_left 1 ((xiHeatFrequency q₀).re - L)
      linarith

/-- **The high part is exponentially small.**  For `a ≥ 1` each entry is at most
`S₀ e^{−(a−1)(L+g)}`. -/
theorem norm_censusHighPart_le {L a g : ℝ} (ha : 1 ≤ a)
    (hgap : ∀ q : XiZeroCopy, L < (xiHeatFrequency q).re → L + g ≤ (xiHeatFrequency q).re)
    (i j : Fin (censusFreq L).card) :
    ‖censusHighPart L a i j‖ ≤
      (∑' q : XiZeroCopy, (1 + ‖xiHeatFrequency q‖) ^ (2 * (censusFreq L).card) *
        Real.exp (-(1 * (xiHeatFrequency q).re))) * Real.exp (-((a - 1) * (L + g))) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  obtain ⟨B, hB⟩ : ∃ B : XiZeroCopy → ℝ, B = fun q => (1 + ‖xiHeatFrequency q‖) ^
      (2 * (censusFreq L).card) * Real.exp (-(1 * (xiHeatFrequency q).re)) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (-((a - 1) * (L + g))) := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : XiZeroCopy → ℂ, f = fun q =>
      xiHeatFrequency q ^ ((i : ℕ) + j) * Complex.exp (-(a : ℂ) * xiHeatFrequency q) := ⟨_, rfl⟩
  have hS : Summable B := by rw [hB]; exact summable_one_add_norm_pow_mul_exp one_pos _
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hbound : ∀ q : XiZeroCopy, q ∉ censusCopies L → ‖f q‖ ≤ B q * E := by
    intro q hq
    have hre : L < (xiHeatFrequency q).re := by
      by_contra h; exact hq (mem_censusCopies.2 (not_lt.1 h))
    have hgq := hgap q hre
    have hij : (i : ℕ) + j ≤ 2 * (censusFreq L).card := by omega
    rw [hf, hB, hE]
    simp only [norm_mul, norm_pow, Complex.norm_exp]
    have hr : (-(a : ℂ) * xiHeatFrequency q).re = -(a * (xiHeatFrequency q).re) := by simp
    rw [hr]
    have h1 : ‖xiHeatFrequency q‖ ^ ((i : ℕ) + j) ≤
        (1 + ‖xiHeatFrequency q‖) ^ (2 * (censusFreq L).card) :=
      (pow_le_pow_left₀ (norm_nonneg _) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith [norm_nonneg (xiHeatFrequency q)]) hij)
    have h2 : Real.exp (-(a * (xiHeatFrequency q).re)) ≤
        Real.exp (-(1 * (xiHeatFrequency q).re)) * Real.exp (-((a - 1) * (L + g))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith
    calc ‖xiHeatFrequency q‖ ^ ((i : ℕ) + j) * Real.exp (-(a * (xiHeatFrequency q).re))
        ≤ (1 + ‖xiHeatFrequency q‖) ^ (2 * (censusFreq L).card) *
            (Real.exp (-(1 * (xiHeatFrequency q).re)) * Real.exp (-((a - 1) * (L + g)))) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hsub : Summable fun q : ↥((censusCopies L : Set XiZeroCopy)ᶜ) => B q * E :=
    (hS.subtype _).mul_right _
  have hnorm : Summable fun q : ↥((censusCopies L : Set XiZeroCopy)ᶜ) => ‖f q‖ :=
    hsub.of_nonneg_of_le (fun _ => norm_nonneg _) fun q => hbound q q.2
  have hB0 : ∀ q, 0 ≤ B q := fun q => by rw [hB]; positivity
  rw [censusHighPart_apply ha0, ← hE]
  have hgoal : (∑' q : ↥((censusCopies L : Set XiZeroCopy)ᶜ),
      xiHeatFrequency q ^ ((i : ℕ) + j) * Complex.exp (-(a : ℂ) * xiHeatFrequency q)) =
        ∑' q : ↥((censusCopies L : Set XiZeroCopy)ᶜ), f q := by rw [hf]
  have hBsum : (∑' q : XiZeroCopy, (1 + ‖xiHeatFrequency q‖) ^ (2 * (censusFreq L).card) *
      Real.exp (-(1 * (xiHeatFrequency q).re))) = ∑' q, B q := by rw [hB]
  rw [hgoal, hBsum]
  calc ‖∑' q : ↥((censusCopies L : Set XiZeroCopy)ᶜ), f q‖
      ≤ ∑' q : ↥((censusCopies L : Set XiZeroCopy)ᶜ), ‖f q‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' q : ↥((censusCopies L : Set XiZeroCopy)ᶜ), B q * E :=
        hnorm.tsum_le_tsum (fun q => hbound q q.2) hsub
    _ = (∑' q : ↥((censusCopies L : Set XiZeroCopy)ᶜ), B q) * E := tsum_mul_right
    _ ≤ (∑' q, B q) * E :=
        mul_le_mul_of_nonneg_right ((hS.subtype _).tsum_le_tsum_of_inj Subtype.val
          Subtype.val_injective (fun q _ => hB0 q) (fun _ => le_rfl) hS) hE0

/-! ## The determinant at large heat time -/

/-- The high part in Vandermonde coordinates, `Y = (W⁻¹)ᵀ M_high W⁻¹`. -/
def censusHighCore (L a : ℝ) : Matrix (Fin (censusFreq L).card) (Fin (censusFreq L).card) ℂ :=
  (censusVandermonde L)⁻¹ᵀ * censusHighPart L a * (censusVandermonde L)⁻¹

theorem heatMomentMatrixC_eq (L a : ℝ) :
    heatMomentMatrixC a (censusFreq L).card =
      (censusVandermonde L)ᵀ * (diagonal (censusWeight L a) + censusHighCore L a) * censusVandermonde L := by
  have hW : IsUnit (censusVandermonde L).det := isUnit_iff_ne_zero.2 (det_censusVandermonde_ne_zero L)
  have hWT : IsUnit (censusVandermonde L)ᵀ.det := by rwa [det_transpose]
  have h1 : (censusVandermonde L)ᵀ * censusHighCore L a * censusVandermonde L = censusHighPart L a := by
    rw [censusHighCore, transpose_nonsing_inv, ← mul_assoc, ← mul_assoc, mul_nonsing_inv _ hWT, one_mul,
      mul_assoc, nonsing_inv_mul _ hW, mul_one]
  rw [mul_add, add_mul, h1, ← censusLowPart, censusHighPart]
  abel

/-- `Z = 1 + D⁻¹ Y`. -/
def censusZ (L a : ℝ) : Matrix (Fin (censusFreq L).card) (Fin (censusFreq L).card) ℂ :=
  1 + diagonal (fun k => (censusWeight L a k)⁻¹) * censusHighCore L a

theorem diagonal_add_censusHighCore_eq (L a : ℝ) :
    diagonal (censusWeight L a) + censusHighCore L a = diagonal (censusWeight L a) * censusZ L a := by
  rw [censusZ, mul_add, mul_one, ← mul_assoc, diagonal_mul_diagonal]
  have h : (fun k => censusWeight L a k * (censusWeight L a k)⁻¹) = fun _ => (1 : ℂ) :=
    funext fun k => mul_inv_cancel₀ (censusWeight_ne_zero L a k)
  rw [h, diagonal_one, one_mul]

theorem det_heatMomentMatrixC_eq (L a : ℝ) :
    (heatMomentMatrixC a (censusFreq L).card).det =
      (censusVandermonde L).det ^ 2 * (∏ k, censusWeight L a k) * (censusZ L a).det := by
  rw [heatMomentMatrixC_eq, diagonal_add_censusHighCore_eq, det_mul, det_mul, det_mul, det_transpose,
    det_diagonal]
  ring

theorem norm_inv_censusWeight_le {L a : ℝ} (ha : 0 ≤ a) (k : Fin (censusFreq L).card) :
    ‖(censusWeight L a k)⁻¹‖ ≤ Real.exp (a * L) := by
  rw [norm_inv, censusWeight, norm_mul, Complex.norm_exp, Complex.norm_natCast]
  have hm : (1 : ℝ) ≤ censusMult L (censusNode L k) := by exact_mod_cast censusMult_pos L k
  have hre : (-(a : ℂ) * censusNode L k).re = -(a * (censusNode L k).re) := by simp
  rw [hre]
  obtain ⟨q, hq, hqk⟩ := mem_censusFreq.1 (censusNode_mem L k)
  have hνL : (censusNode L k).re ≤ L := by rw [← hqk]; exact hq
  rw [mul_inv, ← Real.exp_neg, neg_neg]
  have h1 : (censusMult L (censusNode L k) : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm
  have h2 : Real.exp (a * (censusNode L k).re) ≤ Real.exp (a * L) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hνL ha)
  calc (censusMult L (censusNode L k) : ℝ)⁻¹ * Real.exp (a * (censusNode L k).re)
      ≤ 1 * Real.exp (a * L) := mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one
    _ = _ := one_mul _

/-- Each entry of the high core is at most `C_{kj} S₀ e^{−(a−1)(L+g)}` for `a ≥ 1`, with
`C_{kj} = Σ_{l,m} |W⁻¹_{lk}| |W⁻¹_{mj}|`. -/
theorem norm_censusHighCore_le {L a g : ℝ} (ha : 1 ≤ a)
    (hgap : ∀ q : XiZeroCopy, L < (xiHeatFrequency q).re → L + g ≤ (xiHeatFrequency q).re)
    (k j : Fin (censusFreq L).card) :
    ‖censusHighCore L a k j‖ ≤
      (∑ l, ∑ m, ‖(censusVandermonde L)⁻¹ l k‖ * ‖(censusVandermonde L)⁻¹ m j‖) *
        ((∑' q : XiZeroCopy, (1 + ‖xiHeatFrequency q‖) ^ (2 * (censusFreq L).card) *
          Real.exp (-(1 * (xiHeatFrequency q).re))) * Real.exp (-((a - 1) * (L + g)))) := by
  set S₀ := ∑' q : XiZeroCopy, (1 + ‖xiHeatFrequency q‖) ^ (2 * (censusFreq L).card) *
    Real.exp (-(1 * (xiHeatFrequency q).re))
  set V := (censusVandermonde L)⁻¹
  have hentry : censusHighCore L a k j = ∑ l, ∑ m, V l k * censusHighPart L a l m * V m j := by
    rw [censusHighCore, Matrix.mul_apply]
    simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hentry]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [norm_mul, norm_mul]
  have := norm_censusHighPart_le (a := a) ha hgap l m
  calc ‖V l k‖ * ‖censusHighPart L a l m‖ * ‖V m j‖
      = ‖V l k‖ * ‖V m j‖ * ‖censusHighPart L a l m‖ := by ring
    _ ≤ ‖V l k‖ * ‖V m j‖ * (S₀ * Real.exp (-((a - 1) * (L + g)))) :=
      mul_le_mul_of_nonneg_left this (by positivity)

/-- **`Z(a) → 1`** as the heat time grows. -/
theorem tendsto_censusZ (L : ℝ) : Tendsto (censusZ L) atTop (𝓝 1) := by
  obtain ⟨g, hg, hgap⟩ := exists_gap_above_level L
  set S₀ := ∑' q : XiZeroCopy, (1 + ‖xiHeatFrequency q‖) ^ (2 * (censusFreq L).card) *
    Real.exp (-(1 * (xiHeatFrequency q).re))
  set V := (censusVandermonde L)⁻¹
  have hlim : Tendsto (fun a : ℝ => Real.exp (-(a * g))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hg)
  refine tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun j => ?_
  have hsplit : ∀ a, censusZ L a k j =
      (1 : Matrix (Fin (censusFreq L).card) (Fin (censusFreq L).card) ℂ) k j +
        (censusWeight L a k)⁻¹ * censusHighCore L a k j := fun a => by
    rw [censusZ, Matrix.add_apply, diagonal_mul]
  simp only [hsplit]
  conv => rhs; rw [← add_zero ((1 : Matrix (Fin (censusFreq L).card) (Fin (censusFreq L).card) ℂ) k j)]
  refine tendsto_const_nhds.add ?_
  set C : ℝ := ∑ l, ∑ m, ‖V l k‖ * ‖V m j‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hbound : ∀ a : ℝ, 1 ≤ a → ‖(censusWeight L a k)⁻¹ * censusHighCore L a k j‖ ≤
      C * S₀ * Real.exp (L + g) * Real.exp (-(a * g)) := by
    intro a ha
    have hY : ‖censusHighCore L a k j‖ ≤ C * (S₀ * Real.exp (-((a - 1) * (L + g)))) :=
      norm_censusHighCore_le ha hgap k j
    have hW := norm_inv_censusWeight_le (L := L) (by linarith : (0 : ℝ) ≤ a) k
    rw [norm_mul]
    have hS₀ : 0 ≤ S₀ := tsum_nonneg fun _ => by positivity
    calc ‖(censusWeight L a k)⁻¹‖ * ‖censusHighCore L a k j‖
        ≤ Real.exp (a * L) * (C * (S₀ * Real.exp (-((a - 1) * (L + g))))) :=
          mul_le_mul hW hY (norm_nonneg _) (Real.exp_pos _).le
      _ = C * S₀ * Real.exp (L + g) * Real.exp (-(a * g)) := by
          rw [show Real.exp (a * L) * (C * (S₀ * Real.exp (-((a - 1) * (L + g))))) =
            C * S₀ * (Real.exp (a * L) * Real.exp (-((a - 1) * (L + g)))) by ring,
            ← Real.exp_add, show C * S₀ * Real.exp (L + g) * Real.exp (-(a * g)) =
            C * S₀ * (Real.exp (L + g) * Real.exp (-(a * g))) by ring, ← Real.exp_add]
          congr 2
          ring
  have hzero : Tendsto (fun a : ℝ => C * S₀ * Real.exp (L + g) * Real.exp (-(a * g))) atTop (𝓝 0) := by
    simpa using hlim.const_mul (C * S₀ * Real.exp (L + g))
  exact squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨1, hbound⟩) hzero

/-- The total frequency `Σ_k ν_k` of the low frequencies is real. -/
theorem im_sum_censusNode (L : ℝ) : (∑ k, censusNode L k).im = 0 := by
  have h : (starRingEnd ℂ) (∑ k, censusNode L k) = ∑ k, censusNode L k := by
    rw [map_sum]
    simp_rw [← censusNode_censusConjPerm]
    exact Equiv.sum_comp (censusConjPerm L) (censusNode L)
  exact Complex.conj_eq_iff_im.1 h

theorem prod_censusWeight_eq (L a : ℝ) :
    ∏ k, censusWeight L a k =
      (((∏ k, (censusMult L (censusNode L k) : ℝ)) * Real.exp (-(a * (∑ k, censusNode L k).re)) : ℝ) : ℂ) := by
  unfold censusWeight
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  have hs : ∑ k, -(a : ℂ) * censusNode L k = (((-(a * (∑ k, censusNode L k).re)) : ℝ) : ℂ) := by
    rw [← Finset.mul_sum]
    have him := im_sum_censusNode L
    rw [Complex.im_sum] at him
    apply Complex.ext
    · simp [him]
    · simp [him]
  rw [hs, ← Complex.ofReal_exp]
  push_cast
  ring

/-- **The large-time census.**  For every level `L`, with `N = |S_L|` and `π` the conjugation
permutation of `S_L`, eventually `sign(π) · Δ_N(a) > 0`. -/
theorem eventually_sign_mul_heatMomentDet_pos (L : ℝ) :
    ∀ᶠ a in atTop, 0 < ((Equiv.Perm.sign (censusConjPerm L) : ℤ) : ℝ) *
      heatMomentDet (censusFreq L).card a := by
  have hdet : Tendsto (fun a => (censusZ L a).det) atTop (𝓝 1) := by
    have h : Tendsto (fun a => (censusZ L a).det) atTop
        (𝓝 (det (1 : Matrix (Fin (censusFreq L).card) (Fin (censusFreq L).card) ℂ))) :=
      ((continuous_id.matrix_det).tendsto _).comp (tendsto_censusZ L)
    rwa [det_one] at h
  have hre : Tendsto (fun a => ((censusZ L a).det).re) atTop (𝓝 1) := by
    have h := (Complex.continuous_re.tendsto _).comp hdet
    rw [Complex.one_re] at h
    exact h
  filter_upwards [hre.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with a ha
  set σ : ℝ := ((Equiv.Perm.sign (censusConjPerm L) : ℤ) : ℝ)
  have hσ2 : σ * σ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (censusConjPerm L)) with h | h <;> simp [σ, h]
  set d := (censusVandermonde L).det
  set P : ℝ := Complex.normSq d * ((∏ k, (censusMult L (censusNode L k) : ℝ)) *
    Real.exp (-(a * (∑ k, censusNode L k).re)))
  have hP : 0 < P := by
    have hd : 0 < Complex.normSq d := Complex.normSq_pos.2 (det_censusVandermonde_ne_zero L)
    have hm : 0 < ∏ k, (censusMult L (censusNode L k) : ℝ) :=
      Finset.prod_pos fun k _ => by exact_mod_cast censusMult_pos L k
    positivity
  have hkey : ((heatMomentDet (censusFreq L).card a : ℝ) : ℂ) = ((σ * P : ℝ) : ℂ) * (censusZ L a).det := by
    rw [heatMomentDet_ofReal, det_heatMomentMatrixC_eq, vandermonde_det_sq_eq_sign_mul_normSq,
      prod_censusWeight_eq]
    simp only [σ, P]
    push_cast
    ring
  have hval : heatMomentDet (censusFreq L).card a = σ * P * ((censusZ L a).det).re := by
    have := congrArg Complex.re hkey
    rwa [Complex.ofReal_re, Complex.re_ofReal_mul] at this
  rw [hval, show σ * (σ * P * (censusZ L a).det.re) = (σ * σ) * P * (censusZ L a).det.re by ring,
    hσ2, one_mul]
  exact mul_pos hP ha

/-- **No off-line frequency below the level.**  If every heat frequency of real part `≤ L` is real,
then `Δ_N(a) > 0` for all large `a`. -/
theorem eventually_heatMomentDet_pos_of_censusFreq_real {L : ℝ}
    (hreal : ∀ w ∈ censusFreq L, w.im = 0) :
    ∀ᶠ a in atTop, 0 < heatMomentDet (censusFreq L).card a := by
  have hπ : censusConjPerm L = 1 := by
    ext k
    apply congrArg Fin.val
    apply censusNode_injective L
    rw [censusNode_censusConjPerm, Equiv.Perm.one_apply]
    exact Complex.conj_eq_iff_im.2 (hreal _ (censusNode_mem L k))
  filter_upwards [eventually_sign_mul_heatMomentDet_pos L] with a ha
  rwa [hπ, Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul] at ha

/-- **One off-line pair below the level.**  If the only non-real heat frequencies of real part
`≤ L` are `u` and `ū`, then `Δ_N(a) < 0` for all large `a`. -/
theorem eventually_heatMomentDet_neg_of_one_pair {L : ℝ} {u : ℂ} (hu : u ∈ censusFreq L)
    (hui : u.im ≠ 0)
    (hpair : ∀ w ∈ censusFreq L, w.im ≠ 0 → w = u ∨ w = (starRingEnd ℂ) u) :
    ∀ᶠ a in atTop, heatMomentDet (censusFreq L).card a < 0 := by
  classical
  have hū : (starRingEnd ℂ) u ∈ censusFreq L := conj_mem_censusFreq hu
  set i₀ := (censusFreqEnum L).symm ⟨u, hu⟩
  set j₀ := (censusFreqEnum L).symm ⟨(starRingEnd ℂ) u, hū⟩
  have hi₀ : censusNode L i₀ = u := by simp [censusNode, i₀]
  have hj₀ : censusNode L j₀ = (starRingEnd ℂ) u := by simp [censusNode, j₀]
  have hne : i₀ ≠ j₀ := by
    intro h
    have := congrArg (censusNode L) h
    rw [hi₀, hj₀] at this
    exact hui (Complex.conj_eq_iff_im.1 this.symm)
  have hπ : censusConjPerm L = Equiv.swap i₀ j₀ := by
    ext k
    apply congrArg Fin.val
    apply censusNode_injective L
    rw [censusNode_censusConjPerm]
    by_cases hk₁ : k = i₀
    · rw [hk₁, Equiv.swap_apply_left, hi₀, hj₀]
    by_cases hk₂ : k = j₀
    · rw [hk₂, Equiv.swap_apply_right, hi₀, hj₀, Complex.conj_conj]
    rw [Equiv.swap_apply_of_ne_of_ne hk₁ hk₂]
    by_contra hconj
    have him : (censusNode L k).im ≠ 0 := fun h0 => hconj (Complex.conj_eq_iff_im.2 h0)
    rcases hpair _ (censusNode_mem L k) him with h | h
    · exact hk₁ (censusNode_injective L (h.trans hi₀.symm))
    · exact hk₂ (censusNode_injective L (h.trans hj₀.symm))
  filter_upwards [eventually_sign_mul_heatMomentDet_pos L] with a ha
  rw [hπ, Equiv.Perm.sign_swap hne] at ha
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
    Left.neg_pos_iff] at ha
  exact ha

end

end RHTower
