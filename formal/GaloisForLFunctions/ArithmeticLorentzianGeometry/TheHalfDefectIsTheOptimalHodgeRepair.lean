import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexOfTheScalingSurfaceIsHyperbolicity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanDefectCountsTheOuterEigenvalues
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhichArithmeticDataForceTheSign
import GaloisForLFunctions.HTGeometry.ExponentialKernelAlternatingInertia

/-!
# The half-defect is the optimal Hodge repair

Split Frobenius evaluation into its even and odd parts under circle reflection. The reflected
Gram is the even Gram minus the odd Gram. Adding the odd Gram therefore restores positivity;
its quadratic form is one half of the usual reflection defect. Once the window contains the
spectrum, this correction has the least possible rank, the number of distinct outer eigenvalues.
The construction preserves the pole couplings of the completed intersection form.
-/

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open Complex Finset Matrix
open scoped ComplexOrder ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ArithmeticCastelnuovoSeveri

noncomputable section

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The reflection-even part of Frobenius evaluation. -/
def frobeniusEven (n : ℕ) : Matrix ι (Fin n) ℂ :=
  fun j k => (D.β j ^ (k : ℕ) + circleReflect (D.β j) ^ (k : ℕ)) / 2

/-- The reflection-odd part of Frobenius evaluation. -/
def frobeniusOdd (n : ℕ) : Matrix ι (Fin n) ℂ :=
  fun j k => (D.β j ^ (k : ℕ) - circleReflect (D.β j) ^ (k : ℕ)) / 2

/-- The Gram of the odd evaluation: one half of the reflection defect. -/
def halfDefectRepair (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (frobeniusOdd D n)ᴴ * frobeniusOdd D n

private theorem spanGram_entry (n : ℕ) (k l : Fin n) :
    D.spanGram n k l = ∑ j, conj (D.β j ^ (k : ℕ)) *
      circleReflect (D.β j) ^ (l : ℕ) := by
  simpa [dotProduct, mulVec, windowEval_apply] using
    D.spanGram_sesq n (fun a => if a = k then 1 else 0)
      (fun a => if a = l then 1 else 0)

/-- The reflected Gram splits into positive even and negative odd evaluation Grams. -/
theorem spanGram_add_halfDefectRepair (n : ℕ) :
    D.spanGram n + halfDefectRepair D n = (frobeniusEven D n)ᴴ * frobeniusEven D n := by
  have hdiff : (frobeniusEven D n)ᴴ * frobeniusEven D n - halfDefectRepair D n =
      D.spanGram n := by
    ext k l
    have hflip : (∑ j, conj (circleReflect (D.β j) ^ (k : ℕ)) * D.β j ^ (l : ℕ)) =
        ∑ j, conj (D.β j ^ (k : ℕ)) * circleReflect (D.β j) ^ (l : ℕ) := by
      rw [← Equiv.sum_comp D.reflPerm]
      simp only [D.β_reflPerm, circleReflect_circleReflect]
    simp only [Matrix.sub_apply, Matrix.mul_apply, halfDefectRepair,
      Matrix.conjTranspose_apply, frobeniusEven, frobeniusOdd, Complex.star_def,
      map_div₀, map_add, map_sub, map_ofNat]
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ j, (conj (D.β j ^ (k : ℕ)) * circleReflect (D.β j) ^ (l : ℕ) +
          conj (circleReflect (D.β j) ^ (k : ℕ)) * D.β j ^ (l : ℕ)) / 2 := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = D.spanGram n k l := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hflip, spanGram_entry]
        ring
  exact (sub_eq_iff_eq_add.mp hdiff).symm

/-- The correction is positive semidefinite on every window. -/
theorem halfDefectRepair_posSemidef (n : ℕ) : (halfDefectRepair D n).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

/-- Half the reflection defect already suffices for positivity. -/
theorem spanGram_halfDefectRepair_posSemidef (n : ℕ) :
    (D.spanGram n + halfDefectRepair D n).PosSemidef := by
  rw [spanGram_add_halfDefectRepair]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Window restriction commutes with the correction. -/
theorem halfDefectRepair_submatrix {m n : ℕ} (h : m ≤ n) :
    (halfDefectRepair D n).submatrix (Fin.castLE h) (Fin.castLE h) =
      halfDefectRepair D m := by
  ext k l
  simp only [halfDefectRepair, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, frobeniusOdd, Fin.val_castLE]

private theorem gram_hermQuad {a b : Type*} [Fintype a] [Fintype b]
    (A : Matrix a b ℂ) (x : b → ℂ) :
    hermQuad (Aᴴ * A) x = ∑ j, normSq ((A *ᵥ x) j) := by
  rw [hermQuad, ← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]

/-- Odd evaluation is half the difference of the two reflected evaluations. -/
theorem frobeniusOdd_mulVec (n : ℕ) (x : Fin n → ℂ) (j : ι) :
    (frobeniusOdd D n *ᵥ x) j =
      (windowEval n (D.β j) x - windowEval n (circleReflect (D.β j)) x) / 2 := by
  simp only [mulVec, dotProduct, frobeniusOdd, windowEval_apply,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Even evaluation is half the sum of the two reflected evaluations. -/
theorem frobeniusEven_mulVec (n : ℕ) (x : Fin n → ℂ) (j : ι) :
    (frobeniusEven D n *ᵥ x) j =
      (windowEval n (D.β j) x + windowEval n (circleReflect (D.β j)) x) / 2 := by
  simp only [mulVec, dotProduct, frobeniusEven, windowEval_apply,
    ← Finset.sum_add_distrib]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The repair energy is a quarter of the sum of squared reflection differences. -/
theorem halfDefectRepair_energy (n : ℕ) (x : Fin n → ℂ) :
    hermQuad (halfDefectRepair D n) x =
      ∑ j, normSq ((windowEval n (D.β j) x -
        windowEval n (circleReflect (D.β j)) x) / 2) := by
  rw [halfDefectRepair, gram_hermQuad]
  simp_rw [frobeniusOdd_mulVec]

/-- On real classes the correction is exactly half the existing Frobenius reflection defect. -/
theorem halfDefectRepair_eq_half_frobReflectionDefect (n : ℕ) (e : ℕ → ℝ) :
    hermQuad (halfDefectRepair D n) (fun k => (e k : ℂ)) =
      D.frobReflectionDefect (Finset.range n) e / 2 := by
  have heval : ∀ z : ℂ, windowEval n z (fun k => (e k : ℂ)) =
      frobPoly (Finset.range n) e z := by
    intro z
    exact Fin.sum_univ_eq_sum_range (fun k => (e k : ℂ) * z ^ k) n
  rw [halfDefectRepair_energy, CurveDatum.frobReflectionDefect]
  simp_rw [heval, ← D.β_reflPerm, Complex.normSq_div, Complex.normSq_eq_norm_sq]
  norm_num only [norm_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num]
  rw [← Finset.sum_div]
  ring

/-- Signed reflection coordinates indexed by the distinct outer spectrum. -/
def outerReflectionCoordinates : Matrix ι D.outerSpectrum ℂ :=
  fun j z => CurveDatum.pairValue z (D.β j)

/-- One odd evaluation row for each distinct outer eigenvalue. -/
def outerFrobeniusOdd (n : ℕ) : Matrix D.outerSpectrum (Fin n) ℂ :=
  fun z k => ((z : ℂ) ^ (k : ℕ) - circleReflect z ^ (k : ℕ)) / 2

/-- The odd evaluation factors through one coordinate per distinct outer eigenvalue. -/
theorem frobeniusOdd_factor (n : ℕ) :
    frobeniusOdd D n = outerReflectionCoordinates D * outerFrobeniusOdd D n := by
  classical
  ext j k
  change (D.β j ^ (k : ℕ) - circleReflect (D.β j) ^ (k : ℕ)) / 2 =
    ∑ z : D.outerSpectrum, CurveDatum.pairValue z (D.β j) *
      (((z : ℂ) ^ (k : ℕ) - circleReflect z ^ (k : ℕ)) / 2)
  have hout : ∀ z : D.outerSpectrum, 1 < ‖(z : ℂ)‖ :=
    fun z => (Finset.mem_filter.mp z.2).2
  rcases lt_trichotomy ‖D.β j‖ 1 with hj | hj | hj
  · have hr : 1 < ‖D.β (D.reflPerm j)‖ := by
      rw [D.β_reflPerm, norm_circleReflect]
      exact (one_lt_inv₀ (norm_pos_iff.mpr (D.β_ne_zero j))).mpr hj
    let z : D.outerSpectrum := ⟨D.β (D.reflPerm j), D.mem_outerSpectrum hr⟩
    rw [Finset.sum_eq_single z]
    · have hz : (z : ℂ) = circleReflect (D.β j) := D.β_reflPerm j
      have hne : D.β j ≠ (z : ℂ) := by
        intro h
        have := hout z
        rw [← h] at this
        linarith
      rw [hz] at hne
      simp only [CurveDatum.pairValue, hz, circleReflect_circleReflect, if_neg hne, if_true]
      ring
    · intro w _ hw
      have h1 : D.β j ≠ (w : ℂ) := by
        intro h
        have := hout w
        rw [← h] at this
        linarith
      have h2 : D.β j ≠ circleReflect w := by
        intro h
        apply hw
        apply Subtype.ext
        change (w : ℂ) = D.β (D.reflPerm j)
        rw [D.β_reflPerm, h, circleReflect_circleReflect]
      simp [CurveDatum.pairValue, h1, h2]
    · simp
  · have hr : circleReflect (D.β j) = D.β j := circleReflect_of_norm_one hj
    rw [hr, sub_self, zero_div]
    symm
    apply Finset.sum_eq_zero
    intro z _
    have h1 : D.β j ≠ (z : ℂ) := by
      intro h
      have := hout z
      rw [← h, hj] at this
      exact lt_irrefl _ this
    have h2 : D.β j ≠ circleReflect z := by
      intro h
      have := norm_circleReflect_lt_one (hout z)
      rw [← h, hj] at this
      exact lt_irrefl _ this
    simp [CurveDatum.pairValue, h1, h2]
  · let z : D.outerSpectrum := ⟨D.β j, D.mem_outerSpectrum hj⟩
    rw [Finset.sum_eq_single z]
    · have hr : D.β j ≠ circleReflect (D.β j) := by
        intro h
        have := norm_circleReflect_lt_one hj
        rw [← h] at this
        linarith
      simp [z, CurveDatum.pairValue, hr]
    · intro w _ hw
      have h1 : D.β j ≠ (w : ℂ) := fun h => hw (Subtype.ext h.symm)
      have h2 : D.β j ≠ circleReflect w := by
        intro h
        have := norm_circleReflect_lt_one (hout w)
        rw [← h] at this
        linarith
      simp [CurveDatum.pairValue, h1, h2]
    · simp

/-- The coherent correction has at most one rank per distinct outer eigenvalue. -/
theorem rank_halfDefectRepair_le (n : ℕ) :
    (halfDefectRepair D n).rank ≤ D.outerSpectrum.card := by
  classical
  calc
    (halfDefectRepair D n).rank ≤ (frobeniusOdd D n).rank :=
      Matrix.rank_mul_le_right _ _
    _ ≤ D.outerSpectrum.card := by
      rw [frobeniusOdd_factor]
      refine (Matrix.rank_mul_le_left _ _).trans ?_
      simpa using Matrix.rank_le_card_width (outerReflectionCoordinates D)

private theorem hermQuad_nonneg_of_psd {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosSemidef) (x : Fin n → ℂ) : 0 ≤ hermQuad H x :=
  (Complex.nonneg_iff.mp (hH.dotProduct_mulVec_nonneg x)).1

/-- Any correction making a complete Frobenius window positive has at least one rank per
outer eigenvalue. The competing correction need not itself be positive. -/
theorem outerSpectrum_card_le_rank_repair {n : ℕ} (hn : D.spectrum.card ≤ n)
    (R : Matrix (Fin n) (Fin n) ℂ) (hR : (D.spanGram n + R).PosSemidef) :
    D.outerSpectrum.card ≤ R.rank := by
  have hzero : hermNegIndex (D.spanGram n + R) = 0 :=
    negIndex_eq_zero_of_hermQuad_nonneg (hermQuad_nonneg_of_psd hR)
  have h := hermNegIndex_le_add_rank (D.spanGram n) R
  rwa [D.negIndex_spanGram_eq hn, hzero, zero_add] at h

/-- The explicit half-defect correction attains the minimum possible rank. -/
theorem rank_halfDefectRepair {n : ℕ} (hn : D.spectrum.card ≤ n) :
    (halfDefectRepair D n).rank = D.outerSpectrum.card :=
  le_antisymm (rank_halfDefectRepair_le D n)
    (outerSpectrum_card_le_rank_repair D hn _ (spanGram_halfDefectRepair_posSemidef D n))

/-- Exact rank budget for positive repair, with an explicit attaining correction. -/
theorem exists_positive_repair_iff {n : ℕ} (hn : D.spectrum.card ≤ n) (r : ℕ) :
    (∃ R : Matrix (Fin n) (Fin n) ℂ, R.PosSemidef ∧ R.rank ≤ r ∧
      (D.spanGram n + R).PosSemidef) ↔ D.outerSpectrum.card ≤ r := by
  constructor
  · rintro ⟨R, _, hr, hR⟩
    exact (outerSpectrum_card_le_rank_repair D hn R hR).trans hr
  · intro hr
    exact ⟨halfDefectRepair D n, halfDefectRepair_posSemidef D n,
      (rank_halfDefectRepair_le D n).trans hr, spanGram_halfDefectRepair_posSemidef D n⟩

private theorem pairValue_reflect (z w : ℂ) :
    CurveDatum.pairValue z (circleReflect w) = -CurveDatum.pairValue z w := by
  have h1 : circleReflect w = z ↔ w = circleReflect z :=
    ⟨fun h => by rw [← circleReflect_circleReflect w, h],
      fun h => by rw [h, circleReflect_circleReflect]⟩
  have h2 : circleReflect w = circleReflect z ↔ w = z :=
    ⟨fun h => by rw [← circleReflect_circleReflect w, h, circleReflect_circleReflect],
      fun h => congrArg circleReflect h⟩
  simp only [CurveDatum.pairValue, h1, h2]
  ring

private theorem halfDefectRepair_eq_zero_of_unitary (hU : ∀ j, ‖D.β j‖ = 1) (n : ℕ) :
    halfDefectRepair D n = 0 := by
  have hodd : frobeniusOdd D n = 0 := by
    ext j k
    simp [frobeniusOdd, circleReflect_of_norm_one (hU j)]
  simp [halfDefectRepair, hodd]

/-- A spectrum-complete window detects the exact coefficient of the half-defect repair:
any reduction below one fails unless the spectrum is already unitary. -/
theorem spanGram_scaled_halfDefectRepair_posSemidef_iff {n : ℕ}
    (hn : D.spectrum.card ≤ n) (t : ℝ) :
    (D.spanGram n + (t : ℂ) • halfDefectRepair D n).PosSemidef ↔
      (∀ j, ‖D.β j‖ = 1) ∨ 1 ≤ t := by
  constructor
  · intro hpos
    by_cases hU : ∀ j, ‖D.β j‖ = 1
    · exact Or.inl hU
    right
    have hcard : 0 < D.outerSpectrum.card := by
      by_contra h
      apply hU
      apply D.unitary_iff_negIndex_spanGram_eq_zero.mpr
      rw [D.pontryagin_law_curve.2 _ le_rfl]
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hcard
    have hzo : 1 < ‖z‖ := (Finset.mem_filter.mp hz).2
    have hzs : z ∈ D.spectrum := (Finset.mem_filter.mp hz).1
    let x := D.pairClass n z
    have hval : ∀ j, windowEval n (D.β j) x = CurveDatum.pairValue z (D.β j) :=
      fun j => D.windowEval_pairClass hn z (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    have hrval : ∀ j, windowEval n (circleReflect (D.β j)) x =
        -CurveDatum.pairValue z (D.β j) := by
      intro j
      rw [← D.β_reflPerm, hval, D.β_reflPerm, pairValue_reflect]
    have heven : frobeniusEven D n *ᵥ x = 0 := by
      funext j
      rw [frobeniusEven_mulVec, hval, hrval]
      simp
    have hodd : ∀ j, (frobeniusOdd D n *ᵥ x) j = CurveDatum.pairValue z (D.β j) := by
      intro j
      rw [frobeniusOdd_mulVec, hval, hrval]
      ring
    have henergy : 0 < hermQuad (halfDefectRepair D n) x := by
      rw [halfDefectRepair, gram_hermQuad]
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hzs
      apply Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
      refine ⟨j, Finset.mem_univ j, ?_⟩
      have hne : z ≠ circleReflect z := by
        intro h
        have := norm_circleReflect_lt_one hzo
        rw [← h] at this
        linarith
      rw [hodd, hj]
      simp [CurveDatum.pairValue, hne]
    have hsum : hermQuad (D.spanGram n) x + hermQuad (halfDefectRepair D n) x = 0 := by
      rw [← hermQuad_add, spanGram_add_halfDefectRepair, gram_hermQuad, heven]
      simp
    have hnonneg := hermQuad_nonneg_of_psd hpos x
    rw [hermQuad_add] at hnonneg
    have hscale : hermQuad ((t : ℂ) • halfDefectRepair D n) x =
        t * hermQuad (halfDefectRepair D n) x := by
      simp only [hermQuad, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        Complex.re_ofReal_mul]
    rw [hscale] at hnonneg
    nlinarith only [henergy, hsum, hnonneg]
  · rintro (hU | ht)
    · have hzero := halfDefectRepair_eq_zero_of_unitary D hU n
      simpa only [hzero, smul_zero, add_zero] using spanGram_halfDefectRepair_posSemidef D n
    · have hdecomp : D.spanGram n + (t : ℂ) • halfDefectRepair D n =
          (D.spanGram n + halfDefectRepair D n) +
            ((t - 1 : ℝ) : ℂ) • halfDefectRepair D n := by
        rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
        abel
      rw [hdecomp]
      exact (spanGram_halfDefectRepair_posSemidef D n).add
        ((halfDefectRepair_posSemidef D n).smul (by exact_mod_cast sub_nonneg.mpr ht))

/-! ### Pole-preserving Hodge completion -/

/-- Complete a window defect `G` by the hyperbolic pole plane and prescribed pole couplings.
Only the graph block changes when `G` is corrected. -/
def hodgeCompletion {n : ℕ} (B : Matrix (Fin 2) (Fin n) ℂ)
    (G : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin 2 ⊕ Fin n) (Fin 2 ⊕ Fin n) ℂ :=
  Matrix.fromBlocks polePlane B Bᴴ (Bᴴ * polePlane * B - G)

private theorem hodgeCompletion_isHermitian {n : ℕ} (B : Matrix (Fin 2) (Fin n) ℂ)
    {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian) :
    (hodgeCompletion B G).IsHermitian := by
  have hL := (Matrix.isHermitian_conjTranspose_mul_mul B polePlane_isHermitian).sub hG
  rw [hodgeCompletion, Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose,
    polePlane_isHermitian.eq, hL.eq, Matrix.conjTranspose_conjTranspose]

/-- The pole plane contributes one positive square; the window contributes its negative index. -/
theorem posIndex_hodgeCompletion {n : ℕ} (B : Matrix (Fin 2) (Fin n) ℂ)
    {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian) :
    hermPosIndex (hodgeCompletion B G) = 1 + hermNegIndex G := by
  rw [hodgeCompletion, haynsworth_posIndex isUnit_polePlane polePlane_isHermitian B
    ((Matrix.isHermitian_conjTranspose_mul_mul B polePlane_isHermitian).sub hG),
    posIndex_polePlane, polePlane_inv, sub_sub_cancel_left, hermNegIndex]

/-- Hodge index of the completion is positivity of its prescribed window defect. -/
theorem hodgeCompletion_isHyperbolicHerm_iff {n : ℕ} (B : Matrix (Fin 2) (Fin n) ℂ)
    {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian) :
    IsHyperbolicHerm (hodgeCompletion B G) ↔ G.PosSemidef := by
  rw [← hermPosIndex_le_one_iff (hodgeCompletion_isHermitian B hG),
    posIndex_hodgeCompletion B hG, ← hermNegIndex_eq_zero_iff_posSemidef hG]
  omega

/-- Correcting the defect subtracts exactly the correction from the graph block, preserving
both pole couplings and the pole plane. -/
theorem hodgeCompletion_add {n : ℕ} (B : Matrix (Fin 2) (Fin n) ℂ)
    (G R : Matrix (Fin n) (Fin n) ℂ) :
    hodgeCompletion B (G + R) = hodgeCompletion B G - Matrix.fromBlocks 0 0 0 R := by
  ext (a | k) (b | l) <;> simp [hodgeCompletion, sub_add_eq_sub_sub]

private theorem repairedSpanGram_isHermitian (n : ℕ) (t : ℝ) :
    (D.spanGram n + (t : ℂ) • halfDefectRepair D n).IsHermitian := by
  have hG : (D.spanGram n).IsHermitian := by
    ext k l
    simp [CurveDatum.spanGram, Matrix.conjTranspose_apply, Nat.dist_comm]
  exact hG.add ((halfDefectRepair_posSemidef D n).isHermitian.smul
    (by simp [IsSelfAdjoint]))

/-- Every Frobenius window has an explicit pole-preserving Hodge repair. -/
theorem halfDefectRepair_hodgeIndex (n : ℕ) (B : Matrix (Fin 2) (Fin n) ℂ) :
    IsHyperbolicHerm (hodgeCompletion B (D.spanGram n + halfDefectRepair D n)) :=
  (hodgeCompletion_isHyperbolicHerm_iff B
    (spanGram_halfDefectRepair_posSemidef D n).isHermitian).mpr
      (spanGram_halfDefectRepair_posSemidef D n)

/-- The exact Hodge repair threshold is independent of both prescribed pole couplings. -/
theorem halfDefectRepair_hodgeIndex_iff {n : ℕ} (hn : D.spectrum.card ≤ n)
    (B : Matrix (Fin 2) (Fin n) ℂ) (t : ℝ) :
    IsHyperbolicHerm
      (hodgeCompletion B (D.spanGram n + (t : ℂ) • halfDefectRepair D n)) ↔
        (∀ j, ‖D.β j‖ = 1) ∨ 1 ≤ t := by
  rw [hodgeCompletion_isHyperbolicHerm_iff B (repairedSpanGram_isHermitian D n t),
    spanGram_scaled_halfDefectRepair_posSemidef_iff D hn]

/-- On the spectrum window, the same explicit correction restores Hodge index for every pole
row, attains the minimum rank among all positive repairs, and has sharp scalar threshold. -/
theorem optimal_frobenius_hodge_repair :
    let n := D.spectrum.card
    let C := halfDefectRepair D n
    C.PosSemidef ∧ C.rank = D.outerSpectrum.card ∧
      (∀ R : Matrix (Fin n) (Fin n) ℂ,
        (D.spanGram n + R).PosSemidef → C.rank ≤ R.rank) ∧
      (∀ B : Matrix (Fin 2) (Fin n) ℂ,
        IsHyperbolicHerm (hodgeCompletion B (D.spanGram n + C))) ∧
      (∀ (B : Matrix (Fin 2) (Fin n) ℂ) (t : ℝ),
        IsHyperbolicHerm (hodgeCompletion B (D.spanGram n + (t : ℂ) • C)) ↔
          (∀ j, ‖D.β j‖ = 1) ∨ 1 ≤ t) := by
  refine ⟨halfDefectRepair_posSemidef D _, rank_halfDefectRepair D le_rfl, ?_,
    halfDefectRepair_hodgeIndex D _, fun B t => halfDefectRepair_hodgeIndex_iff D le_rfl B t⟩
  intro R hR
  rw [rank_halfDefectRepair D le_rfl]
  exact outerSpectrum_card_le_rank_repair D le_rfl R hR

/-- The diagonal graph has zero odd evaluation, so its whole row is untouched. -/
theorem halfDefectRepair_zero_row (n : ℕ) (k : Fin (n + 1)) :
    halfDefectRepair D (n + 1) 0 k = 0 := by
  simp [halfDefectRepair, Matrix.mul_apply, Matrix.conjTranspose_apply, frobeniusOdd]

/-- The correction also preserves every pairing against the diagonal graph. -/
theorem halfDefectRepair_zero_column (n : ℕ) (k : Fin (n + 1)) :
    halfDefectRepair D (n + 1) k 0 = 0 := by
  simp [halfDefectRepair, Matrix.mul_apply, Matrix.conjTranspose_apply, frobeniusOdd]

/-- The raw Frobenius span defect is repaired by half the reflection defect in its normalized
coordinates. This includes arbitrary signed real graph coefficients. -/
theorem spanDefect_add_half_reflectionDefect_nonneg (n : ℕ) (d : ℕ → ℝ) :
    0 ≤ D.spanDefect (Finset.range n) d +
      D.frobReflectionDefect (Finset.range n) (fun k => d k * D.sqrtq ^ k) / 2 := by
  have h := hermQuad_nonneg_of_psd (spanGram_halfDefectRepair_posSemidef D n)
    (fun k => ((d k * D.sqrtq ^ (k : ℕ) : ℝ) : ℂ))
  rw [hermQuad_add,
    D.hermQuad_spanGram_ofReal n (fun k => d k * D.sqrtq ^ k),
    halfDefectRepair_eq_half_frobReflectionDefect D n (fun k => d k * D.sqrtq ^ k),
    ← D.spanDefect_eq_toeplitz] at h
  exact h

#print axioms spanGram_add_halfDefectRepair
#print axioms halfDefectRepair_submatrix
#print axioms halfDefectRepair_eq_half_frobReflectionDefect
#print axioms rank_halfDefectRepair
#print axioms spanGram_scaled_halfDefectRepair_posSemidef_iff
#print axioms optimal_frobenius_hodge_repair
#print axioms spanDefect_add_half_reflectionDefect_nonneg

end GaloisForLFunctions.ArithmeticLorentzianGeometry
