import GaloisForLFunctions.RHTower.ThetaParityFiniteHead
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Polynomial.Basic

/-!
# Directed theta parity square

Finite positive sine/cosine Gram cores give a positive reference square and
its actual directed rank-one feedback. A finite diagonal transport to the
physical parity head excludes every real characteristic root beyond a fixed
operator-norm radius. The exterior characteristic determinant is positive.
No inverse of the sine Gram and no sign assumption on cross residues is used.
-/

open Matrix
open scoped BigOperators MatrixOrder
namespace RHTower
noncomputable section

/-- Finite frequency weight; all normalizations below are finite-dimensional. -/
def thetaParityWeight (n : ℕ) : ℝ := Real.sqrt (n + 1)

theorem thetaParityWeight_pos (n : ℕ) : 0 < thetaParityWeight n := by
  unfold thetaParityWeight
  positivity

theorem thetaParityWeight_sq (n : ℕ) : thetaParityWeight n ^ 2 = (n : ℝ) + 1 :=
  Real.sq_sqrt (by positivity)

def thetaParityScale (n : ℕ) : ℝ := (thetaParityWeight n)⁻¹

def thetaParitySineCore (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun m n => thetaParityScale m * thetaCdfSineGram (m + 1) (n + 1) * thetaParityScale n

def thetaParityCosineCore (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun m n => thetaParityScale m * thetaCdfCosineGram (m + 1) (n + 1) * thetaParityScale n

theorem thetaParitySineCore_posSemidef (N : ℕ) : (thetaParitySineCore N).PosSemidef := by
  have h := (thetaCdfSineGram_posSemidef (fun n : Fin N => (n : ℤ) + 1)).conjTranspose_mul_mul_same
    (Matrix.diagonal fun n : Fin N => thetaParityScale n)
  convert h using 1
  ext i j
  simp [thetaParitySineCore, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_assoc]

theorem thetaParityCosineCore_posSemidef (N : ℕ) : (thetaParityCosineCore N).PosSemidef := by
  have h := (thetaCdfCosineGram_posSemidef (fun n : Fin N => (n : ℤ) + 1)).conjTranspose_mul_mul_same
    (Matrix.diagonal fun n : Fin N => thetaParityScale n)
  convert h using 1
  ext i j
  simp [thetaParityCosineCore, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_assoc]

def thetaParityRoot (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := CFC.sqrt (thetaParitySineCore N)

theorem thetaParityRoot_isHermitian (N : ℕ) : (thetaParityRoot N).IsHermitian :=
  (CFC.sqrt_nonneg (thetaParitySineCore N)).posSemidef.isHermitian

theorem thetaParityRoot_mul_self (N : ℕ) :
    thetaParityRoot N * thetaParityRoot N = thetaParitySineCore N :=
  CFC.sqrt_mul_sqrt_self _ (thetaParitySineCore_posSemidef N).nonneg

def thetaParityPositiveSquare (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  thetaParityRoot N * thetaParityCosineCore N * thetaParityRoot N

theorem thetaParityPositiveSquare_posSemidef (N : ℕ) : (thetaParityPositiveSquare N).PosSemidef := by
  have h := (thetaParityCosineCore_posSemidef N).conjTranspose_mul_mul_same (thetaParityRoot N)
  rw [show (thetaParityRoot N)ᴴ = thetaParityRoot N from thetaParityRoot_isHermitian N] at h
  exact h

def thetaParityBoundaryInput (N : ℕ) : Fin N → ℝ := fun n => thetaParityScale n

def thetaParityBoundaryOutput (N : ℕ) : Fin N → ℝ :=
  fun n => thetaParityScale n * cdfAction (n + 1)

def thetaParityDirectedCore (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  thetaParityCosineCore N - Matrix.vecMulVec (thetaParityBoundaryInput N) (thetaParityBoundaryOutput N)

def thetaParitySquareInput (N : ℕ) : Fin N → ℝ := thetaParityRoot N *ᵥ thetaParityBoundaryInput N

def thetaParitySquareOutput (N : ℕ) : Fin N → ℝ := thetaParityRoot N *ᵥ thetaParityBoundaryOutput N

/-- Positive reference square with its literal directed rank-one feedback. -/
def thetaParityFeedbackSquare (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  thetaParityPositiveSquare N - Matrix.vecMulVec (thetaParitySquareInput N) (thetaParitySquareOutput N)

theorem thetaParityFeedbackSquare_eq (N : ℕ) :
    thetaParityFeedbackSquare N = thetaParityRoot N * thetaParityDirectedCore N * thetaParityRoot N := by
  have htranspose : (thetaParityRoot N)ᵀ = thetaParityRoot N := by
    ext i j
    exact (thetaParityRoot_isHermitian N).apply i j
  have hv : thetaParityBoundaryOutput N ᵥ* thetaParityRoot N =
      thetaParityRoot N *ᵥ thetaParityBoundaryOutput N := by
    conv_lhs => rw [← htranspose]
    rw [Matrix.vecMul_transpose]
  rw [thetaParityDirectedCore, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]
  rfl

theorem charpoly_thetaParityFeedbackSquare (N : ℕ) :
    (thetaParityFeedbackSquare N).charpoly =
      (thetaParityDirectedCore N * thetaParitySineCore N).charpoly := by
  rw [thetaParityFeedbackSquare_eq, Matrix.mul_assoc,
    Matrix.charpoly_mul_comm (thetaParityRoot N) (thetaParityDirectedCore N * thetaParityRoot N),
    Matrix.mul_assoc, thetaParityRoot_mul_self]

def thetaParityNormalizedHead (N : ℕ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  Matrix.fromBlocks 0 (thetaParityDirectedCore N) (thetaParitySineCore N) 0

def thetaParityHeadWeight (N : ℕ) : Fin N ⊕ Fin N → ℝ :=
  Sum.elim (fun n => thetaParityWeight n) (fun n => thetaParityWeight n)

theorem thetaParityHeadWeight_pos (N : ℕ) (i : Fin N ⊕ Fin N) : 0 < thetaParityHeadWeight N i := by
  cases i <;> exact thetaParityWeight_pos _

/-- Exact finite diagonal transport to the bounded physical head. -/
theorem thetaParityHead_weighted_entry (N : ℕ) (i j : Fin N ⊕ Fin N) :
    thetaParityHead N i j * (thetaParityHeadWeight N j : ℂ) =
      ((thetaParityHeadWeight N i / Real.pi * thetaParityNormalizedHead N i j : ℝ) : ℂ) := by
  rcases i with i | i <;> rcases j with j | j
  · simp [thetaParityHead, thetaParityHeadWeight, thetaParityNormalizedHead]
  · change (((thetaCdfCosineGram ((i : ℤ) + 1) ((j : ℤ) + 1) - cdfAction ((j : ℤ) + 1)) /
        (Real.pi * ((j : ℝ) + 1)) : ℝ) : ℂ) * (thetaParityWeight j : ℂ) = _
    rw [← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    change ((thetaCdfCosineGram _ _ - cdfAction _) / (Real.pi * ((j : ℝ) + 1))) *
      thetaParityWeight j = thetaParityWeight i / Real.pi *
        (thetaParityScale i * thetaCdfCosineGram _ _ * thetaParityScale j -
          thetaParityScale i * (thetaParityScale j * cdfAction _))
    rw [← thetaParityWeight_sq (j : ℕ)]
    unfold thetaParityScale
    have hi := (thetaParityWeight_pos i).ne'
    have hj := (thetaParityWeight_pos j).ne'
    field_simp
  · change ((thetaCdfSineGram ((i : ℤ) + 1) ((j : ℤ) + 1) /
        (Real.pi * ((j : ℝ) + 1)) : ℝ) : ℂ) * (thetaParityWeight j : ℂ) = _
    rw [← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    change (thetaCdfSineGram _ _ / (Real.pi * ((j : ℝ) + 1))) * thetaParityWeight j =
      thetaParityWeight i / Real.pi * (thetaParityScale i * thetaCdfSineGram _ _ * thetaParityScale j)
    rw [← thetaParityWeight_sq (j : ℕ)]
    unfold thetaParityScale
    have hi := (thetaParityWeight_pos i).ne'
    have hj := (thetaParityWeight_pos j).ne'
    field_simp
  · simp [thetaParityHead, thetaParityHeadWeight, thetaParityNormalizedHead]

def thetaParityWeightedVector (N : ℕ) (x : (Fin N ⊕ Fin N) → ℝ) : (Fin N ⊕ Fin N) → ℂ :=
  fun i => ((thetaParityHeadWeight N i * x i : ℝ) : ℂ)

theorem thetaParityWeightedVector_ne_zero (N : ℕ) {x : (Fin N ⊕ Fin N) → ℝ} (hx : x ≠ 0) :
    thetaParityWeightedVector N x ≠ 0 := by
  intro h
  apply hx
  funext i
  have hi := congrFun h i
  change ((thetaParityHeadWeight N i * x i : ℝ) : ℂ) = 0 at hi
  exact (mul_eq_zero.mp (Complex.ofReal_eq_zero.mp hi)).resolve_left (thetaParityHeadWeight_pos N i).ne'

theorem thetaParityWeightedVector_eigen (N : ℕ) {x : (Fin N ⊕ Fin N) → ℝ} {z : ℝ}
    (he : thetaParityNormalizedHead N *ᵥ x = z • x) :
    thetaParityHead N *ᵥ thetaParityWeightedVector N x =
      ((z / Real.pi : ℝ) : ℂ) • thetaParityWeightedVector N x := by
  funext i
  have he' := congrFun he i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at he'
  simp only [Matrix.mulVec, dotProduct, thetaParityWeightedVector, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_mul]
  calc
    (∑ j, thetaParityHead N i j * ((thetaParityHeadWeight N j : ℂ) * (x j : ℂ))) =
        ∑ j, ((thetaParityHeadWeight N i / Real.pi * thetaParityNormalizedHead N i j : ℝ) : ℂ) * (x j : ℂ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_assoc, thetaParityHead_weighted_entry]
    _ = ((thetaParityHeadWeight N i / Real.pi * ∑ j, thetaParityNormalizedHead N i j * x j : ℝ) : ℂ) := by
      rw [Finset.mul_sum]
      push_cast
      exact Finset.sum_congr rfl fun j _ => by ring
    _ = ((z / Real.pi : ℝ) : ℂ) * ((thetaParityHeadWeight N i : ℂ) * (x i : ℂ)) := by
      rw [he']
      push_cast
      ring

theorem abs_thetaParityNormalizedHead_eigenvalue_le (N : ℕ)
    {x : (Fin N ⊕ Fin N) → ℝ} (hx : x ≠ 0) {z : ℝ}
    (he : thetaParityNormalizedHead N *ᵥ x = z • x) : |z| ≤ Real.pi * ‖thetaQuotientOperator‖ := by
  have h := norm_thetaParityHead_eigenvalue_le N (thetaParityWeightedVector_ne_zero N hx)
    (thetaParityWeightedVector_eigen N he)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos Real.pi_pos] at h
  exact (div_le_iff₀ Real.pi_pos).mp h |>.trans_eq (mul_comm _ _)

/-- The fixed exterior radius comes from the actual bounded quotient operator. -/
def thetaParityExteriorRadius : ℝ := Real.pi ^ 2 * ‖thetaQuotientOperator‖ ^ 2

theorem thetaParityExteriorRadius_nonneg : 0 ≤ thetaParityExteriorRadius := by
  unfold thetaParityExteriorRadius
  positivity

/-- Directed finite square feedback has no real characteristic root beyond the
physical radius. No positivity of its cross residues is assumed. -/
theorem thetaParityFeedbackSquare_charpoly_ne_zero (N : ℕ) {t : ℝ}
    (ht : thetaParityExteriorRadius < t) :
    (thetaParityFeedbackSquare N).charpoly.eval t ≠ 0 := by
  intro hzero
  have htpos : 0 < t := lt_of_le_of_lt thetaParityExteriorRadius_nonneg ht
  have hroot : (thetaParityDirectedCore N * thetaParitySineCore N).charpoly.IsRoot t := by
    simpa only [Polynomial.IsRoot, charpoly_thetaParityFeedbackSquare] using hzero
  have hh : Module.End.HasEigenvalue
      (thetaParityDirectedCore N * thetaParitySineCore N).mulVecLin t :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ t).mpr (by
      simpa only [Matrix.charpoly_mulVecLin] using hroot)
  obtain ⟨v, hv⟩ := hh.exists_hasEigenvector
  let z := Real.sqrt t
  have hz : 0 < z := Real.sqrt_pos.mpr htpos
  have hzsq : z ^ 2 = t := Real.sq_sqrt htpos.le
  have hzmul : z⁻¹ * t = z := by
    rw [← hzsq]
    field_simp
  let w : (Fin N ⊕ Fin N) → ℝ := Sum.elim v (z⁻¹ • (thetaParitySineCore N *ᵥ v))
  have hw : w ≠ 0 := by
    intro hw
    apply hv.2
    funext i
    exact congrFun hw (Sum.inl i)
  have he : thetaParityNormalizedHead N *ᵥ w = z • w := by
    rw [thetaParityNormalizedHead, Matrix.fromBlocks_mulVec]
    have hv' : thetaParityDirectedCore N *ᵥ (thetaParitySineCore N *ᵥ v) = t • v := by
      rw [Matrix.mulVec_mulVec]
      exact hv.apply_eq_smul
    funext i
    rcases i with i | i
    · change ((0 : Matrix (Fin N) (Fin N) ℝ) *ᵥ v + thetaParityDirectedCore N *ᵥ
          (z⁻¹ • (thetaParitySineCore N *ᵥ v))) i = z * v i
      rw [Matrix.zero_mulVec, zero_add, Matrix.mulVec_smul, hv', smul_smul, hzmul]
      rfl
    · change (thetaParitySineCore N *ᵥ v + (0 : Matrix (Fin N) (Fin N) ℝ) *ᵥ
          (z⁻¹ • (thetaParitySineCore N *ᵥ v))) i =
          z * (z⁻¹ * (thetaParitySineCore N *ᵥ v) i)
      rw [Matrix.zero_mulVec, add_zero, ← mul_assoc, mul_inv_cancel₀ hz.ne', one_mul]
  have hbound := abs_thetaParityNormalizedHead_eigenvalue_le N hw he
  rw [abs_of_pos hz] at hbound
  have hsquare : z ^ 2 ≤ (Real.pi * ‖thetaQuotientOperator‖) ^ 2 :=
    sq_le_sq₀ hz.le (mul_nonneg Real.pi_pos.le (norm_nonneg _)) |>.mpr hbound
  rw [hzsq, mul_pow] at hsquare
  exact (not_le.mpr ht) hsquare

/-- The characteristic determinant is strictly positive throughout the real
exterior interval, including at reference eigenvalues. -/
theorem thetaParityFeedbackSquare_charpoly_pos (N : ℕ) {t : ℝ}
    (ht : thetaParityExteriorRadius < t) :
    0 < (thetaParityFeedbackSquare N).charpoly.eval t := by
  by_cases hN : N = 0
  · subst N
    simp
  let p := (thetaParityFeedbackSquare N).charpoly
  have hdeg : 0 < p.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (by
    simpa only [p, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using Nat.pos_of_ne_zero hN)
  have hlead : 0 ≤ p.leadingCoeff := by
    rw [show p.leadingCoeff = 1 from (Matrix.charpoly_monic _).leadingCoeff]
    norm_num
  have hlim := p.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlead
  obtain ⟨s, hs, hps⟩ := ((Filter.eventually_gt_atTop t).and
    (hlim.eventually (Filter.eventually_gt_atTop (0 : ℝ)))).exists
  by_contra hpos
  have hpt : p.eval t ≤ 0 := le_of_not_gt hpos
  obtain ⟨u, hu, hzero⟩ := intermediate_value_Icc hs.le p.continuousOn ⟨hpt, hps.le⟩
  exact thetaParityFeedbackSquare_charpoly_ne_zero N (ht.trans_le hu.1) hzero

end
end RHTower
