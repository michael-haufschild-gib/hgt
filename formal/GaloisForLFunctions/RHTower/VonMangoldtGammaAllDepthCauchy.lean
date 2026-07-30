import GaloisForLFunctions.RHTower.VonMangoldtGammaOrientedAnomaly
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# The all-depth von Mangoldt--Gamma anomaly has a positive Cauchy packet

Every coordinate of the oriented finite Gamma descent anomaly supplies a real positive-rate
Taylor remainder.  Dividing its source-mass square root by the Cauchy denominator produces a
finite response vector indexed jointly by source atoms and Gamma-jet coordinates.  Its finite
packet Gram is positive semidefinite before continuation or passage to the Euler unit boundary.

The numerator relation is exact: restoring the other source-mass square root recovers the actual
oriented descent-anomaly coordinate.  Positivity is therefore attached to the source comparison,
not to an independently chosen target matrix.  The reduced causal/polar Euler-boundary comparison
with the completed prime--Gamma moment germ remains open.
-/

open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Cauchy coordinate of one oriented all-depth Gamma-anomaly atom. -/
def finiteExponentialAllDepthCauchyFeature
    {P : Type*} (weight rate : P → ℝ) (N : ℕ) (i : Fin N)
    (w : ℂ) (p : P) : ℂ :=
  (Real.sqrt (weight p) * rate p ^ (i : ℕ) *
      expNegOrientedRemainder (N - (i : ℕ)) (rate p) : ℝ) /
    (w + (rate p : ℂ))

theorem finiteExponentialAllDepthCauchyFeature_mul
    {P : Type*} (weight rate : P → ℝ) (N : ℕ) (i : Fin N)
    (w : ℂ) (p : P) (hden : w + (rate p : ℂ) ≠ 0) :
    finiteExponentialAllDepthCauchyFeature weight rate N i w p *
        (w + (rate p : ℂ)) =
      (Real.sqrt (weight p) * rate p ^ (i : ℕ) *
        expNegOrientedRemainder (N - (i : ℕ)) (rate p) : ℝ) := by
  rw [finiteExponentialAllDepthCauchyFeature]
  exact div_mul_cancel₀ _ hden

/-- The Cauchy numerator is exactly the oriented source anomaly after restoring the remaining
square-root source mass. -/
theorem sqrtWeight_mul_allDepthCauchyFeature_mul_eq_orientedAnomaly
    {P : Type*} (weight rate : P → ℝ) (hweight : ∀ p, 0 ≤ weight p)
    (N : ℕ) (i : Fin N) (w : ℂ) (p : P)
    (hden : w + (rate p : ℂ) ≠ 0) :
    (Real.sqrt (weight p) : ℂ) *
        (finiteExponentialAllDepthCauchyFeature weight rate N i w p *
          (w + (rate p : ℂ))) =
      (((-1 : ℝ) ^ (N + 1) *
        (finiteExponentialGammaAnomaly
          (fun _ : Fin 1 => (weight p : ℂ))
          (fun _ : Fin 1 => (rate p : ℂ)) 0 N
          (fun _ => 1) i).re : ℝ) : ℂ) := by
  rw [finiteExponentialAllDepthCauchyFeature_mul weight rate N i w p hden]
  have horiented := finiteExponentialGammaAnomaly_singleton_oriented_re_eq
    (weight p) (rate p) 0 N i
  have horientedC := congrArg Complex.ofReal horiented
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at horientedC
  have horientedC' :
      (((-1 : ℝ) ^ (N + 1) *
        (finiteExponentialGammaAnomaly
          (fun _ : Fin 1 => (weight p : ℂ))
          (fun _ : Fin 1 => (rate p : ℂ)) 0 N
          (fun _ => 1) i).re : ℝ) : ℂ) =
        (weight p * rate p ^ (i : ℕ) *
          expNegOrientedRemainder (N - (i : ℕ)) (rate p) : ℝ) := by
    simpa using horientedC
  rw [horientedC']
  push_cast
  have hsqrtC :
      (Real.sqrt (weight p) : ℂ) * (Real.sqrt (weight p) : ℂ) =
        (weight p : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (hweight p)
  calc
    (Real.sqrt (weight p) : ℂ) *
        ((Real.sqrt (weight p) : ℂ) * (rate p : ℂ) ^ (i : ℕ) *
          (expNegOrientedRemainder (N - (i : ℕ)) (rate p) : ℂ)) =
      ((Real.sqrt (weight p) : ℂ) * (Real.sqrt (weight p) : ℂ)) *
        (rate p : ℂ) ^ (i : ℕ) *
          (expNegOrientedRemainder (N - (i : ℕ)) (rate p) : ℂ) := by ring
    _ = _ := by rw [hsqrtC]

/-- Source vector containing every prime coordinate and every jet coordinate at one Cauchy
point. -/
def finiteExponentialAllDepthCauchyVector
    {P : Type*} [Fintype P] (weight rate : P → ℝ) (N : ℕ) (w : ℂ) :
    EuclideanSpace ℂ (P × Fin N) :=
  WithLp.toLp 2 fun pi =>
    star (finiteExponentialAllDepthCauchyFeature weight rate N pi.2 w pi.1)

/-- The finite all-depth anomaly response Gram. -/
def finiteExponentialAllDepthCauchyGram
    {P : Type*} [Fintype P] {K : ℕ}
    (weight rate : P → ℝ) (N : ℕ) (w : Fin K → ℂ) :
    Matrix (Fin K) (Fin K) ℂ :=
  Matrix.gram ℂ (fun a => finiteExponentialAllDepthCauchyVector weight rate N (w a))

theorem finiteExponentialAllDepthCauchyGram_apply
    {P : Type*} [Fintype P] {K : ℕ}
    (weight rate : P → ℝ) (N : ℕ) (w : Fin K → ℂ) (a b : Fin K) :
    finiteExponentialAllDepthCauchyGram weight rate N w a b =
      ∑ pi : P × Fin N,
        finiteExponentialAllDepthCauchyFeature weight rate N pi.2 (w a) pi.1 *
          star (finiteExponentialAllDepthCauchyFeature weight rate N pi.2 (w b) pi.1) := by
  rw [finiteExponentialAllDepthCauchyGram, Matrix.gram_apply, PiLp.inner_apply]
  simp only [finiteExponentialAllDepthCauchyVector, WithLp.ofLp_toLp,
    RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro pi hpi
  change star (finiteExponentialAllDepthCauchyFeature weight rate N pi.2 (w b) pi.1) *
      star (star (finiteExponentialAllDepthCauchyFeature weight rate N pi.2 (w a) pi.1)) = _
  rw [star_star]
  ring

/-- Every finite all-depth anomaly response packet is positive semidefinite before continuation
or passage to the Euler boundary. -/
theorem finiteExponentialAllDepthCauchyGram_posSemidef
    {P : Type*} [Fintype P] {K : ℕ}
    (weight rate : P → ℝ) (N : ℕ) (w : Fin K → ℂ) :
    (finiteExponentialAllDepthCauchyGram weight rate N w).PosSemidef :=
  Matrix.posSemidef_gram ℂ _

/-- The real resolved von Mangoldt mass `Lambda(n) / n`. -/
def finiteVonMangoldtRealWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / n

theorem finiteVonMangoldtRealWeight_nonneg (n : ℕ) :
    0 ≤ finiteVonMangoldtRealWeight n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)

def finiteVonMangoldtAllDepthCauchyFeature
    (N : ℕ) (i : Fin N) (w : ℂ) (n : ℕ) : ℂ :=
  finiteExponentialAllDepthCauchyFeature
    finiteVonMangoldtRealWeight (fun n : ℕ => Real.log n) N i w n

/-- The actual von Mangoldt all-depth Cauchy numerator is exactly its oriented Gamma-descent
anomaly coordinate. -/
theorem sqrtVonMangoldtWeight_mul_allDepthCauchyFeature_mul_eq_orientedAnomaly
    {n : ℕ} (hn : n ≠ 0) (N : ℕ) (i : Fin N) (w : ℂ)
    (hden : w + (Real.log n : ℂ) ≠ 0) :
    (Real.sqrt (finiteVonMangoldtRealWeight n) : ℂ) *
        (finiteVonMangoldtAllDepthCauchyFeature N i w n *
          (w + (Real.log n : ℂ))) =
      (((-1 : ℝ) ^ (N + 1) *
        (finiteExponentialGammaAnomaly
          (fun _ : Fin 1 => finiteVonMangoldtWeight n)
          (fun _ : Fin 1 => finiteVonMangoldtFrequency n) 0 N
          (fun _ => 1) i).re : ℝ) : ℂ) := by
  rw [finiteVonMangoldtWeight_eq_ofReal hn]
  exact sqrtWeight_mul_allDepthCauchyFeature_mul_eq_orientedAnomaly
    finiteVonMangoldtRealWeight (fun n : ℕ => Real.log n)
    finiteVonMangoldtRealWeight_nonneg
    N i w n hden

/-- Finite positive von Mangoldt/Gamma Cauchy Gram containing every source channel and every
Gamma-jet coordinate at depth `N`. -/
def finiteVonMangoldtAllDepthCauchyGram
    (M N : ℕ) {K : ℕ} (w : Fin K → ℂ) : Matrix (Fin K) (Fin K) ℂ :=
  finiteExponentialAllDepthCauchyGram
    (fun n : Fin M => finiteVonMangoldtRealWeight (n + 2))
    (fun n : Fin M => Real.log (n + 2)) N w

/-- Unconditional positive finite Gram of all von Mangoldt channels and all Gamma-jet anomaly
coordinates. -/
theorem finiteVonMangoldtAllDepthCauchyGram_posSemidef
    (M N : ℕ) {K : ℕ} (w : Fin K → ℂ) :
    (finiteVonMangoldtAllDepthCauchyGram M N w).PosSemidef :=
  finiteExponentialAllDepthCauchyGram_posSemidef _ _ _ _

/-! ### Canonical two-boundary compression -/

def finiteVonMangoldtAllDepthCauchyVector
    (M N : ℕ) (w : ℂ) : EuclideanSpace ℂ (Fin M × Fin N) :=
  finiteExponentialAllDepthCauchyVector
    (fun n : Fin M => finiteVonMangoldtRealWeight (n + 2))
    (fun n : Fin M => Real.log (n + 2)) N w

/-- The two source boundary modes corresponding to the Mellin characters at `+1/2` and `-1/2`. -/
def finiteVonMangoldtAllDepthBoundarySubspace (M N : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin M × Fin N)) :=
  Submodule.span ℂ
    {finiteVonMangoldtAllDepthCauchyVector M N (1 / 2),
      finiteVonMangoldtAllDepthCauchyVector M N (-1 / 2)}

/-- Canonical finite packet after removing both causal/polar boundary modes. -/
def finiteVonMangoldtAllDepthBalancedCauchyVector
    (M N : ℕ) (w : ℂ) : EuclideanSpace ℂ (Fin M × Fin N) :=
  ((finiteVonMangoldtAllDepthBoundarySubspace M N)ᗮ.orthogonalProjectionOnto
    (finiteVonMangoldtAllDepthCauchyVector M N w) :
      EuclideanSpace ℂ (Fin M × Fin N))

theorem finiteVonMangoldtAllDepthBalancedCauchyVector_plus_half_eq_zero
    (M N : ℕ) :
    finiteVonMangoldtAllDepthBalancedCauchyVector M N (1 / 2) = 0 := by
  rw [finiteVonMangoldtAllDepthBalancedCauchyVector]
  have hv : finiteVonMangoldtAllDepthCauchyVector M N (1 / 2) ∈
      ((finiteVonMangoldtAllDepthBoundarySubspace M N)ᗮ)ᗮ := by
    apply (finiteVonMangoldtAllDepthBoundarySubspace M N).le_orthogonal_orthogonal
    apply Submodule.subset_span
    simp
  have hproj :=
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hv
  exact congrArg Subtype.val hproj

theorem finiteVonMangoldtAllDepthBalancedCauchyVector_neg_half_eq_zero
    (M N : ℕ) :
    finiteVonMangoldtAllDepthBalancedCauchyVector M N (-1 / 2) = 0 := by
  rw [finiteVonMangoldtAllDepthBalancedCauchyVector]
  have hv : finiteVonMangoldtAllDepthCauchyVector M N (-1 / 2) ∈
      ((finiteVonMangoldtAllDepthBoundarySubspace M N)ᗮ)ᗮ := by
    apply (finiteVonMangoldtAllDepthBoundarySubspace M N).le_orthogonal_orthogonal
    apply Submodule.subset_span
    simp
  have hproj :=
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hv
  exact congrArg Subtype.val hproj

/-- Every compressed source vector satisfies the positive-half boundary constraint. -/
theorem inner_balancedCauchyVector_boundary_plus_half_eq_zero
    (M N : ℕ) (w : ℂ) :
    inner ℂ (finiteVonMangoldtAllDepthBalancedCauchyVector M N w)
      (finiteVonMangoldtAllDepthCauchyVector M N (1 / 2)) = 0 := by
  let S := finiteVonMangoldtAllDepthBoundarySubspace M N
  have hplus : finiteVonMangoldtAllDepthCauchyVector M N (1 / 2) ∈ S := by
    apply Submodule.subset_span
    simp
  have hbal : finiteVonMangoldtAllDepthBalancedCauchyVector M N w ∈ Sᗮ := by
    exact ((finiteVonMangoldtAllDepthBoundarySubspace M N)ᗮ.orthogonalProjectionOnto
      (finiteVonMangoldtAllDepthCauchyVector M N w)).property
  exact Submodule.inner_left_of_mem_orthogonal hplus hbal

/-- Every compressed source vector satisfies the negative-half boundary constraint. -/
theorem inner_balancedCauchyVector_boundary_neg_half_eq_zero
    (M N : ℕ) (w : ℂ) :
    inner ℂ (finiteVonMangoldtAllDepthBalancedCauchyVector M N w)
      (finiteVonMangoldtAllDepthCauchyVector M N (-1 / 2)) = 0 := by
  let S := finiteVonMangoldtAllDepthBoundarySubspace M N
  have hminus : finiteVonMangoldtAllDepthCauchyVector M N (-1 / 2) ∈ S := by
    apply Submodule.subset_span
    simp
  have hbal : finiteVonMangoldtAllDepthBalancedCauchyVector M N w ∈ Sᗮ := by
    exact ((finiteVonMangoldtAllDepthBoundarySubspace M N)ᗮ.orthogonalProjectionOnto
      (finiteVonMangoldtAllDepthCauchyVector M N w)).property
  exact Submodule.inner_left_of_mem_orthogonal hminus hbal

/-- Finite Gram after canonical removal of the two source boundary modes. -/
def finiteVonMangoldtAllDepthBalancedCauchyGram
    (M N : ℕ) {K : ℕ} (w : Fin K → ℂ) : Matrix (Fin K) (Fin K) ℂ :=
  Matrix.gram ℂ
    (fun a => finiteVonMangoldtAllDepthBalancedCauchyVector M N (w a))

/-- The codimension-at-most-two causal/polar compression preserves finite positivity. -/
theorem finiteVonMangoldtAllDepthBalancedCauchyGram_posSemidef
    (M N : ℕ) {K : ℕ} (w : Fin K → ℂ) :
    (finiteVonMangoldtAllDepthBalancedCauchyGram M N w).PosSemidef :=
  Matrix.posSemidef_gram ℂ _

end

end RHTower
