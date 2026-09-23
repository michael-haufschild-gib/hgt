import GaloisForLFunctions.RHTower.XiZerosInfinite
import GaloisForLFunctions.RHTower.XiTraceHankelCountableCriterion
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement

open Complex Set Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

theorem xiCentralReciprocalSquare_eq_iff
    (ρ σ : ↥(MeromorphicOn.divisor xi Set.univ).support) :
    xiCentralReciprocalSquare (ρ : ℂ) = xiCentralReciprocalSquare (σ : ℂ) ↔
      ρ = σ ∨ (ρ : ℂ) + (σ : ℂ) = 1 := by
  rw [xiCentralReciprocalSquare, xiCentralReciprocalSquare, neg_inj]
  constructor
  · intro h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with hsame | hneg
    · left
      apply Subtype.ext
      have hinv : (ρ : ℂ) - 1 / 2 = (σ : ℂ) - 1 / 2 := inv_injective hsame
      exact sub_left_inj.mp hinv
    · right
      have hneg' : ((ρ : ℂ) - 1 / 2)⁻¹ = (-((σ : ℂ) - 1 / 2))⁻¹ := by
        rw [inv_neg]
        exact hneg
      have hcoord : (ρ : ℂ) - 1 / 2 = -((σ : ℂ) - 1 / 2) :=
        inv_injective hneg'
      linear_combination hcoord
  · rintro (rfl | hsum)
    · rfl
    · have hcoord : (ρ : ℂ) - 1 / 2 = -((σ : ℂ) - 1 / 2) := by
        linear_combination hsum
      rw [hcoord, inv_neg, neg_sq]

theorem xiCentralReciprocalSquare_range_infinite :
    (Set.range (fun ρ : ↥(MeromorphicOn.divisor xi Set.univ).support =>
      xiCentralReciprocalSquare (ρ : ℂ))).Infinite := by
  let I := ↥(MeromorphicOn.divisor xi Set.univ).support
  let f : I → ℂ := fun ρ => xiCentralReciprocalSquare (ρ : ℂ)
  by_contra hfinite
  have hrangeFinite := Set.not_infinite.mp hfinite
  have himage : (f '' (Set.univ : Set I)).Finite := by
    simpa only [Set.image_univ] using hrangeFinite
  have huniv : (Set.univ : Set I).Finite := by
    apply Set.Finite.of_finite_fibers f himage
    intro x hx
    obtain ⟨ρ₀, _hρ₀, hρ₀x⟩ := hx
    have hsecond : ({ρ : I | (ρ : ℂ) = 1 - (ρ₀ : ℂ)} : Set I).Finite := by
      change (Subtype.val ⁻¹' ({1 - (ρ₀ : ℂ)} : Set ℂ)).Finite
      exact Set.Finite.preimage Subtype.val_injective.injOn (Set.finite_singleton _)
    apply (Set.finite_singleton ρ₀).union hsecond |>.subset
    intro ρ hρ
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and,
      Set.mem_preimage, Set.mem_singleton_iff] at hρ
    have heq : f ρ = f ρ₀ := hρ.trans hρ₀x.symm
    rcases (xiCentralReciprocalSquare_eq_iff ρ ρ₀).mp heq with hsame | href
    · change ρ = ρ₀ ∨ (ρ : ℂ) = 1 - (ρ₀ : ℂ)
      exact Or.inl hsame
    · change ρ = ρ₀ ∨ (ρ : ℂ) = 1 - (ρ₀ : ℂ)
      right
      linear_combination href
  have hIfinite : Finite I := Set.finite_univ_iff.mp huniv
  have hsupportFinite : (MeromorphicOn.divisor xi Set.univ).support.Finite :=
    Set.finite_coe_iff.mp hIfinite
  exact xiDivisorSupport_infinite hsupportFinite

theorem exists_xiCentralReciprocalSquare_not_root_of_polynomial
    {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∃ ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
      evalRealPolynomial p (xiCentralReciprocalSquare (ρ : ℂ)) ≠ 0 := by
  let q : Polynomial ℂ := p.map (algebraMap ℝ ℂ)
  have hq : q ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hp
  by_contra hnone
  push Not at hnone
  have hrangeFinite :
      (Set.range (fun ρ : ↥(MeromorphicOn.divisor xi Set.univ).support =>
        xiCentralReciprocalSquare (ρ : ℂ))).Finite := by
    apply q.roots.toFinset.finite_toSet.subset
    rintro z ⟨ρ, rfl⟩
    change xiCentralReciprocalSquare (ρ : ℂ) ∈ q.roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hq]
    exact hnone ρ
  exact xiCentralReciprocalSquare_range_infinite hrangeFinite

theorem xiCentralTraceHankel_re_pos_of_riemannHypothesis
    (hRH : RiemannHypothesis) {p : Polynomial ℝ} (hp : p ≠ 0) :
    0 < (xiCentralTraceHankel p).re := by
  obtain ⟨ρ₀, hpρ₀⟩ := exists_xiCentralReciprocalSquare_not_root_of_polynomial hp
  have hsumre : Summable (fun ρ => (xiCentralTraceHankelTerm p ρ).re) := by
    simpa only [Function.comp_apply] using!
      (xi_central_traceHankel_summable p).map Complex.reCLM Complex.reCLM.continuous
  rw [xiCentralTraceHankel,
    Complex.re_tsum (xi_central_traceHankel_summable p)]
  apply hsumre.tsum_pos
  · intro ρ
    obtain ⟨x, hx, hcoord⟩ := xiCentralReciprocalSquare_pos_real_of_rh hRH ρ
    rw [xiCentralTraceHankelTerm, hcoord, evalRealPolynomial_ofReal]
    have hw : 0 ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
      exact_mod_cast xi_divisor_nonneg Set.univ (ρ : ℂ)
    rw [show ((((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) : ℂ) *
        (x : ℂ) * (((Polynomial.eval x p : ℝ) : ℂ)) ^ (2 : ℕ)) =
        ((((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * x *
          (Polynomial.eval x p) ^ (2 : ℕ) : ℝ) : ℂ) by push_cast; ring]
    simp only [Complex.ofReal_re]
    positivity
  · rw [xiCentralTraceHankelTerm]
    obtain ⟨x, hx, hcoord⟩ := xiCentralReciprocalSquare_pos_real_of_rh hRH ρ₀
    rw [hcoord, evalRealPolynomial_ofReal] at hpρ₀ ⊢
    have hw : 0 < ((MeromorphicOn.divisor xi Set.univ) (ρ₀ : ℂ) : ℝ) := by
      exact_mod_cast xi_divisor_pos_on_support ρ₀
    rw [show ((((MeromorphicOn.divisor xi Set.univ) (ρ₀ : ℂ) : ℝ) : ℂ) *
        (x : ℂ) * (((Polynomial.eval x p : ℝ) : ℂ)) ^ (2 : ℕ)) =
        ((((MeromorphicOn.divisor xi Set.univ) (ρ₀ : ℂ) : ℝ) * x *
          (Polynomial.eval x p) ^ (2 : ℕ) : ℝ) : ℂ) by push_cast; ring]
    simp only [Complex.ofReal_re]
    exact mul_pos (mul_pos hw hx) (sq_pos_of_ne_zero (by exact_mod_cast hpρ₀))

def xiCentralMomentHankelMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (xiCentralReciprocalMoment ((i : ℕ) + (j : ℕ))).re

theorem xiCentralMomentHankelMatrix_isHermitian (n : ℕ) :
    (xiCentralMomentHankelMatrix n).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_id_of_comm]
  rw [xiCentralMomentHankelMatrix, xiCentralMomentHankelMatrix, add_comm]

theorem dotProduct_mulVec_xiCentralMomentHankelMatrix
    (n : ℕ) (a : Fin n → ℝ) :
    a ⬝ᵥ (xiCentralMomentHankelMatrix n).mulVec a =
      xiCentralTraceHankelVector n a := by
  rw [xiCentralTraceHankelVector, xiCentralTraceHankel_ofFn]
  simp only [dotProduct, Matrix.mulVec, xiCentralMomentHankelMatrix,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem xiCentralMomentHankelMatrix_posDef_of_riemannHypothesis
    (hRH : RiemannHypothesis) (n : ℕ) :
    (xiCentralMomentHankelMatrix n).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨xiCentralMomentHankelMatrix_isHermitian n, ?_⟩
  intro a ha
  rw [star_trivial, dotProduct_mulVec_xiCentralMomentHankelMatrix]
  apply xiCentralTraceHankel_re_pos_of_riemannHypothesis hRH
  intro hp
  apply ha
  apply Polynomial.injective_ofFn n
  rw [hp, Polynomial.ofFn_zero]

theorem det_xiCentralMomentHankelMatrix_pos_of_riemannHypothesis
    (hRH : RiemannHypothesis) (n : ℕ) :
    0 < (xiCentralMomentHankelMatrix n).det :=
  (xiCentralMomentHankelMatrix_posDef_of_riemannHypothesis hRH n).det_pos

/-- Every finite central reciprocal-moment Hankel matrix is positive definite. -/
def XiCentralMomentHankelPosDef : Prop :=
  ∀ n : ℕ, (xiCentralMomentHankelMatrix n).PosDef

/-- The positive-definite hierarchy of central reciprocal-moment Hankel matrices is exactly RH. -/
theorem xiCentralMomentHankelPosDef_iff_riemannHypothesis :
    XiCentralMomentHankelPosDef ↔ RiemannHypothesis := by
  constructor
  · intro hpos
    apply riemannHypothesis_of_xiCentralTraceHankelNonnegative
    intro p
    by_cases hp : p = 0
    · subst p
      simp [xiCentralTraceHankel, xiCentralTraceHankelTerm]
    · let n := p.natDegree + 1
      let a : Fin n → ℝ := Polynomial.toFn n p
      have hpof : Polynomial.ofFn n a = p := by
        exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)
      have ha : a ≠ 0 := by
        intro ha
        apply hp
        rw [← hpof, ha, Polynomial.ofFn_zero]
      have hquad : 0 < a ⬝ᵥ (xiCentralMomentHankelMatrix n).mulVec a := by
        exact (hpos n).dotProduct_mulVec_pos ha
      rw [dotProduct_mulVec_xiCentralMomentHankelMatrix,
        xiCentralTraceHankelVector, hpof] at hquad
      exact hquad.le
  · intro hRH n
    exact xiCentralMomentHankelMatrix_posDef_of_riemannHypothesis hRH n

private theorem posDef_fin_one_of_det_pos
    {M : Matrix (Fin 1) (Fin 1) ℝ} (hdet : 0 < M.det) : M.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i
    fin_cases j
    simp
  · intro x hx
    have hx0 : x 0 ≠ 0 := by
      intro hx0
      apply hx
      funext i
      fin_cases i
      exact hx0
    rw [Matrix.det_fin_one] at hdet
    simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
    rw [show x 0 * (M 0 0 * x 0) = (x 0) ^ (2 : ℕ) * M 0 0 by ring]
    exact mul_pos (sq_pos_of_ne_zero hx0) hdet

private theorem xiCentralMomentHankelMatrix_succ_reindex_toBlocks₁₁ (n : ℕ) :
    let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
    let M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
      Matrix.reindex e.symm e.symm (xiCentralMomentHankelMatrix (n + 1))
    M.toBlocks₁₁ = xiCentralMomentHankelMatrix n := by
  dsimp
  ext i j
  rfl

private theorem xiCentralMomentHankelMatrix_succ_reindex_toBlocks₂₁ (n : ℕ) :
    let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
    let M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
      Matrix.reindex e.symm e.symm (xiCentralMomentHankelMatrix (n + 1))
    M.toBlocks₂₁ = M.toBlocks₁₂.conjTranspose := by
  dsimp
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂,
    xiCentralMomentHankelMatrix, add_comm]

private theorem xiCentralMomentHankelMatrix_succ_block (n : ℕ) :
    let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
    let M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
      Matrix.reindex e.symm e.symm (xiCentralMomentHankelMatrix (n + 1))
    Matrix.fromBlocks (xiCentralMomentHankelMatrix n) M.toBlocks₁₂
      M.toBlocks₁₂.conjTranspose M.toBlocks₂₂ = M := by
  dsimp only
  rw [← xiCentralMomentHankelMatrix_succ_reindex_toBlocks₁₁ n,
    ← xiCentralMomentHankelMatrix_succ_reindex_toBlocks₂₁ n]
  exact Matrix.fromBlocks_toBlocks _

/-- Positivity of every leading central Hankel determinant. -/
def XiCentralMomentHankelDeterminantsPositive : Prop :=
  ∀ n : ℕ, 0 < (xiCentralMomentHankelMatrix n).det

private theorem xiCentralMomentHankelPosDef_of_determinantsPositive
    (hdet : XiCentralMomentHankelDeterminantsPositive) :
    XiCentralMomentHankelPosDef := by
  intro k
  induction k with
  | zero =>
      rw [Matrix.posDef_iff_dotProduct_mulVec]
      refine ⟨xiCentralMomentHankelMatrix_isHermitian 0, ?_⟩
      intro x hx
      exact (hx (Subsingleton.elim x 0)).elim
  | succ n ih =>
      let A : Matrix (Fin n) (Fin n) ℝ := xiCentralMomentHankelMatrix n
      let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
      let M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
        Matrix.reindex e.symm e.symm (xiCentralMomentHankelMatrix (n + 1))
      let B : Matrix (Fin n) (Fin 1) ℝ := M.toBlocks₁₂
      let D : Matrix (Fin 1) (Fin 1) ℝ := M.toBlocks₂₂
      have hA : A.PosDef := ih
      letI : Invertible A := hA.isUnit.invertible
      let S : Matrix (Fin 1) (Fin 1) ℝ := D - B.conjTranspose * A⁻¹ * B
      have hblock : Matrix.fromBlocks A B B.conjTranspose D = M := by
        exact xiCentralMomentHankelMatrix_succ_block n
      have hdetM : 0 < M.det := by
        change 0 < (Matrix.reindex e.symm e.symm
          (xiCentralMomentHankelMatrix (n + 1))).det
        rw [Matrix.det_reindex_self]
        exact hdet (n + 1)
      have hfactor : M.det = A.det * S.det := by
        rw [← hblock, Matrix.det_fromBlocks₁₁]
        rw [Matrix.invOf_eq_nonsing_inv]
      have hdetS : 0 < S.det := by
        apply pos_of_mul_pos_right (hfactor ▸ hdetM)
        exact (hdet n).le
      have hS : S.PosDef := posDef_fin_one_of_det_pos hdetS
      have hblockSemidef :
          (Matrix.fromBlocks A B B.conjTranspose D).PosSemidef := by
        exact (Matrix.PosDef.fromBlocks₁₁ B D hA).mpr hS.posSemidef
      have hMsemidef : M.PosSemidef := hblock ▸ hblockSemidef
      have hM : M.PosDef :=
        (hMsemidef.posDef_iff_det_ne_zero).mpr (ne_of_gt hdetM)
      have hback := hM.submatrix e.symm.injective
      simpa [M, Matrix.reindex_apply, Matrix.submatrix_submatrix] using hback

/-- Sylvester's criterion for the nested Xi central moment matrices. -/
theorem xiCentralMomentHankelDeterminantsPositive_iff_posDef :
    XiCentralMomentHankelDeterminantsPositive ↔ XiCentralMomentHankelPosDef := by
  constructor
  · exact xiCentralMomentHankelPosDef_of_determinantsPositive
  · intro hpos n
    exact (hpos n).det_pos

/-- **Leading-determinant criterion for RH.** RH is equivalent to one strict scalar inequality in
each finite degree: positivity of the leading determinant of the central reciprocal-moment Hankel
matrix. -/
theorem xiCentralMomentHankelDeterminantsPositive_iff_riemannHypothesis :
    XiCentralMomentHankelDeterminantsPositive ↔ RiemannHypothesis := by
  rw [xiCentralMomentHankelDeterminantsPositive_iff_posDef,
    xiCentralMomentHankelPosDef_iff_riemannHypothesis]

end
end RHTower
