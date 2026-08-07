import GaloisForLFunctions.HTGeometry.BilinearFibreSystem
import GaloisForLFunctions.HTGeometry.BiprojectiveHilbertBezout

namespace GaloisForLFunctions.HTGeometry

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] {m n : ℕ}

/-- Embed a low first-block variable into the corresponding projective block. -/
def biprojLeftLow (i : Fin m) : BiprojVar m n := Sum.inl i.castSucc

/-- Homogenizing coordinate of the first projective block. -/
def biprojLeftInfinity : BiprojVar m n := Sum.inl (Fin.last m)

/-- Embed a low second-block variable into the corresponding projective block. -/
def biprojRightLow (j : Fin n) : BiprojVar m n := Sum.inr j.castSucc

/-- Homogenizing coordinate of the second projective block. -/
def biprojRightInfinity : BiprojVar m n := Sum.inr (Fin.last n)

/-- Universal low polynomial in the first projective block. -/
noncomputable def biprojectiveUnivA (K : Type*) [Field K] (m n : ℕ) :
    (MvPolynomial (BiprojVar m n) K)[X] :=
  ∑ i : Fin m, Polynomial.C (MvPolynomial.X (biprojLeftLow i)) * Polynomial.X ^ (i : ℕ)

/-- Universal low polynomial in the second projective block. -/
noncomputable def biprojectiveUnivB (K : Type*) [Field K] (m n : ℕ) :
    (MvPolynomial (BiprojVar m n) K)[X] :=
  ∑ j : Fin n, Polynomial.C (MvPolynomial.X (biprojRightLow j)) * Polynomial.X ^ (j : ℕ)

/-- First separately homogenized factor `A + alpha U`. -/
noncomputable def biprojectiveLeftFactor (U : K[X]) (m n : ℕ) :
    (MvPolynomial (BiprojVar m n) K)[X] :=
  biprojectiveUnivA K m n +
    Polynomial.C (MvPolynomial.X biprojLeftInfinity) * U.map MvPolynomial.C

/-- Second separately homogenized factor `B + beta V`. -/
noncomputable def biprojectiveRightFactor (V : K[X]) (m n : ℕ) :
    (MvPolynomial (BiprojVar m n) K)[X] :=
  biprojectiveUnivB K m n +
    Polynomial.C (MvPolynomial.X biprojRightInfinity) * V.map MvPolynomial.C

/-- Exact biprojective homogenization of `criticalLowProduct U V A B - 1`.

The correction `alpha * beta * (1 + U * V)` makes dehomogenization an identity at every
coefficient.  For coefficients below `m+n`, the `U*V` term vanishes under the critical tail
divisibility assumptions, leaving the card's equation
`(A + alpha U) (B + beta V) = alpha beta mod X^(m+n)`. -/
noncomputable def biprojectiveCriticalPolynomial (U V : K[X]) (m n : ℕ) :
    (MvPolynomial (BiprojVar m n) K)[X] :=
  biprojectiveLeftFactor U m n * biprojectiveRightFactor V m n -
    Polynomial.C
        (MvPolynomial.X biprojLeftInfinity * MvPolynomial.X biprojRightInfinity) *
      (1 + (U * V).map MvPolynomial.C)

/-- The `k`-th compactified critical-fibre equation. -/
noncomputable def biprojectiveCriticalEquation (U V : K[X]) (m n k : ℕ) :
    MvPolynomial (BiprojVar m n) K :=
  (biprojectiveCriticalPolynomial U V m n).coeff k

theorem biprojectiveUnivA_coeff (i : ℕ) :
    (biprojectiveUnivA K m n).coeff i =
      if h : i < m then MvPolynomial.X (biprojLeftLow ⟨i, h⟩) else 0 := by
  classical
  rw [biprojectiveUnivA, Polynomial.finsetSum_coeff]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨i, h⟩ : Fin m)]
    · simp
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
      exact fun hcon => hb (Fin.ext hcon.symm)
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    intro hcon
    exact h (hcon ▸ b.2)

theorem biprojectiveUnivB_coeff (j : ℕ) :
    (biprojectiveUnivB K m n).coeff j =
      if h : j < n then MvPolynomial.X (biprojRightLow ⟨j, h⟩) else 0 := by
  classical
  rw [biprojectiveUnivB, Polynomial.finsetSum_coeff]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨j, h⟩ : Fin n)]
    · simp
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
      exact fun hcon => hb (Fin.ext hcon.symm)
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    intro hcon
    exact h (hcon ▸ b.2)

theorem biprojectiveUnivA_coeff_isWeightedHomogeneous (i : ℕ) :
    ((biprojectiveUnivA K m n).coeff i).IsWeightedHomogeneous
      biprojectiveWeight (1, 0) := by
  rw [biprojectiveUnivA_coeff]
  split_ifs with hi
  · convert (MvPolynomial.isWeightedHomogeneous_X
        (R := K) biprojectiveWeight (biprojLeftLow (⟨i, hi⟩ : Fin m))) using 1
    all_goals simp [biprojLeftLow, biprojectiveWeight]
  · exact MvPolynomial.isWeightedHomogeneous_zero (R := K) biprojectiveWeight (1, 0)

theorem biprojectiveUnivB_coeff_isWeightedHomogeneous (j : ℕ) :
    ((biprojectiveUnivB K m n).coeff j).IsWeightedHomogeneous
      biprojectiveWeight (0, 1) := by
  rw [biprojectiveUnivB_coeff]
  split_ifs with hj
  · convert (MvPolynomial.isWeightedHomogeneous_X
        (R := K) biprojectiveWeight (biprojRightLow (⟨j, hj⟩ : Fin n))) using 1
    all_goals simp [biprojRightLow, biprojectiveWeight]
  · exact MvPolynomial.isWeightedHomogeneous_zero (R := K) biprojectiveWeight (0, 1)

theorem biprojectiveLeftFactor_coeff_isWeightedHomogeneous (U : K[X]) (k : ℕ) :
    ((biprojectiveLeftFactor U m n).coeff k).IsWeightedHomogeneous
      biprojectiveWeight (1, 0) := by
  rw [biprojectiveLeftFactor, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_map]
  apply MvPolynomial.IsWeightedHomogeneous.add
  · exact biprojectiveUnivA_coeff_isWeightedHomogeneous k
  · simpa [biprojLeftInfinity, biprojectiveWeight] using
      ((MvPolynomial.isWeightedHomogeneous_X
          (R := K) biprojectiveWeight biprojLeftInfinity).mul
        (MvPolynomial.isWeightedHomogeneous_C biprojectiveWeight (U.coeff k)))

theorem biprojectiveRightFactor_coeff_isWeightedHomogeneous (V : K[X]) (k : ℕ) :
    ((biprojectiveRightFactor V m n).coeff k).IsWeightedHomogeneous
      biprojectiveWeight (0, 1) := by
  rw [biprojectiveRightFactor, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_map]
  apply MvPolynomial.IsWeightedHomogeneous.add
  · exact biprojectiveUnivB_coeff_isWeightedHomogeneous k
  · simpa [biprojRightInfinity, biprojectiveWeight] using
      ((MvPolynomial.isWeightedHomogeneous_X
          (R := K) biprojectiveWeight biprojRightInfinity).mul
        (MvPolynomial.isWeightedHomogeneous_C biprojectiveWeight (V.coeff k)))

/-- Coefficients of a product of polynomial families inherit the sum of their fixed weights. -/
theorem polynomial_mul_coeff_isWeightedHomogeneous
    {p q : ℕ × ℕ} (P Q : (MvPolynomial (BiprojVar m n) K)[X])
    (hP : ∀ i, (P.coeff i).IsWeightedHomogeneous biprojectiveWeight p)
    (hQ : ∀ j, (Q.coeff j).IsWeightedHomogeneous biprojectiveWeight q)
    (k : ℕ) :
    ((P * Q).coeff k).IsWeightedHomogeneous biprojectiveWeight (p + q) := by
  rw [Polynomial.coeff_mul]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro ij _
  exact (hP ij.1).mul (hQ ij.2)

theorem biprojectiveCorrection_coeff_isWeightedHomogeneous (U V : K[X]) (k : ℕ) :
    ((Polynomial.C
          (MvPolynomial.X (biprojLeftInfinity : BiprojVar m n) *
            MvPolynomial.X (biprojRightInfinity : BiprojVar m n)) *
        (1 + (U * V).map MvPolynomial.C)).coeff k).IsWeightedHomogeneous
      biprojectiveWeight (1, 1) := by
  rw [Polynomial.coeff_C_mul]
  have hAlpha : ((MvPolynomial.X (biprojLeftInfinity : BiprojVar m n) :
      MvPolynomial (BiprojVar m n) K)).IsWeightedHomogeneous
      biprojectiveWeight (1, 0) := by
    simpa [biprojLeftInfinity, biprojectiveWeight] using
      (MvPolynomial.isWeightedHomogeneous_X (R := K) biprojectiveWeight
        (biprojLeftInfinity : BiprojVar m n))
  have hBeta : ((MvPolynomial.X (biprojRightInfinity : BiprojVar m n) :
      MvPolynomial (BiprojVar m n) K)).IsWeightedHomogeneous
      biprojectiveWeight (0, 1) := by
    simpa [biprojRightInfinity, biprojectiveWeight] using
      (MvPolynomial.isWeightedHomogeneous_X (R := K) biprojectiveWeight
        (biprojRightInfinity : BiprojVar m n))
  have hScalar : ((1 + (U * V).map
      (MvPolynomial.C : K →+* MvPolynomial (BiprojVar m n) K)).coeff k).IsWeightedHomogeneous
      biprojectiveWeight 0 := by
    rw [Polynomial.coeff_add, Polynomial.coeff_map]
    rcases k with rfl | k
    · simpa using
        (MvPolynomial.isWeightedHomogeneous_one K biprojectiveWeight).add
          (MvPolynomial.isWeightedHomogeneous_C biprojectiveWeight ((U * V).coeff 0))
    · simpa [Polynomial.coeff_one] using
        (MvPolynomial.isWeightedHomogeneous_C biprojectiveWeight ((U * V).coeff (k + 1)))
  simpa using (hAlpha.mul hBeta).mul hScalar

/-- Every compactified fibre equation has exact bidegree `(1,1)`. -/
theorem biprojectiveCriticalEquation_isWeightedHomogeneous (U V : K[X]) (k : ℕ) :
    (biprojectiveCriticalEquation U V m n k).IsWeightedHomogeneous
      biprojectiveWeight (1, 1) := by
  rw [biprojectiveCriticalEquation, biprojectiveCriticalPolynomial, Polynomial.coeff_sub]
  apply (MvPolynomial.weightedHomogeneousSubmodule K biprojectiveWeight (1, 1)).sub_mem
  · simpa using polynomial_mul_coeff_isWeightedHomogeneous
      (biprojectiveLeftFactor U m n) (biprojectiveRightFactor V m n)
      (biprojectiveLeftFactor_coeff_isWeightedHomogeneous U)
      (biprojectiveRightFactor_coeff_isWeightedHomogeneous V) k
  · exact biprojectiveCorrection_coeff_isWeightedHomogeneous U V k

/-! ## Exact affine-chart recovery -/

/-- The affine chart `alpha = beta = 1` containing the original jet variables. -/
def biprojectiveAffineChartPoint (x : (Fin m ⊕ Fin n) → K) : BiprojVar m n → K
  | Sum.inl i => Fin.lastCases 1 (fun a => x (Sum.inl a)) i
  | Sum.inr j => Fin.lastCases 1 (fun b => x (Sum.inr b)) j

@[simp] theorem biprojectiveAffineChartPoint_leftLow
    (x : (Fin m ⊕ Fin n) → K) (i : Fin m) :
    biprojectiveAffineChartPoint x (biprojLeftLow i) = x (Sum.inl i) := by
  simp [biprojectiveAffineChartPoint, biprojLeftLow]

@[simp] theorem biprojectiveAffineChartPoint_leftInfinity
    (x : (Fin m ⊕ Fin n) → K) :
    biprojectiveAffineChartPoint x (biprojLeftInfinity : BiprojVar m n) = 1 := by
  simp [biprojectiveAffineChartPoint, biprojLeftInfinity]

@[simp] theorem biprojectiveAffineChartPoint_rightLow
    (x : (Fin m ⊕ Fin n) → K) (j : Fin n) :
    biprojectiveAffineChartPoint x (biprojRightLow j) = x (Sum.inr j) := by
  simp [biprojectiveAffineChartPoint, biprojRightLow]

@[simp] theorem biprojectiveAffineChartPoint_rightInfinity
    (x : (Fin m ⊕ Fin n) → K) :
    biprojectiveAffineChartPoint x (biprojRightInfinity : BiprojVar m n) = 1 := by
  simp [biprojectiveAffineChartPoint, biprojRightInfinity]

theorem map_biprojectiveUnivA (x : (Fin m ⊕ Fin n) → K) :
    (biprojectiveUnivA K m n).map (MvPolynomial.eval (biprojectiveAffineChartPoint x)) =
      jetOfPoint x := by
  rw [biprojectiveUnivA, jetOfPoint, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem map_biprojectiveUnivB (x : (Fin m ⊕ Fin n) → K) :
    (biprojectiveUnivB K m n).map (MvPolynomial.eval (biprojectiveAffineChartPoint x)) =
      recipOfPoint x := by
  rw [biprojectiveUnivB, recipOfPoint, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem map_map_C_biprojective (x : (Fin m ⊕ Fin n) → K) (P : K[X]) :
    (P.map (MvPolynomial.C : K →+* MvPolynomial (BiprojVar m n) K)).map
        (MvPolynomial.eval (biprojectiveAffineChartPoint x)) = P := by
  rw [Polynomial.map_map]
  have hcomp : ((MvPolynomial.eval (biprojectiveAffineChartPoint x)).comp
      (MvPolynomial.C : K →+* MvPolynomial (BiprojVar m n) K)) = RingHom.id K := by
    ext a
    simp
  rw [hcomp, Polynomial.map_id]

theorem map_biprojectiveLeftFactor (U : K[X]) (x : (Fin m ⊕ Fin n) → K) :
    (biprojectiveLeftFactor U m n).map
        (MvPolynomial.eval (biprojectiveAffineChartPoint x)) = jetOfPoint x + U := by
  rw [biprojectiveLeftFactor, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    map_biprojectiveUnivA, map_map_C_biprojective]
  simp

theorem map_biprojectiveRightFactor (V : K[X]) (x : (Fin m ⊕ Fin n) → K) :
    (biprojectiveRightFactor V m n).map
        (MvPolynomial.eval (biprojectiveAffineChartPoint x)) = recipOfPoint x + V := by
  rw [biprojectiveRightFactor, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    map_biprojectiveUnivB, map_map_C_biprojective]
  simp

/-- On `alpha = beta = 1`, compactified equations are exactly the original bilinear equations. -/
theorem eval_biprojectiveCriticalEquation_affineChart
    (U V : K[X]) (x : (Fin m ⊕ Fin n) → K) (k : ℕ) :
    MvPolynomial.eval (biprojectiveAffineChartPoint x)
        (biprojectiveCriticalEquation U V m n k) =
      MvPolynomial.eval x (bilinSysPoly U V m n k) := by
  have hCorrection :
      (Polynomial.C
            (MvPolynomial.X (biprojLeftInfinity : BiprojVar m n) *
              MvPolynomial.X (biprojRightInfinity : BiprojVar m n)) *
          (1 + (U * V).map MvPolynomial.C)).map
            (MvPolynomial.eval (biprojectiveAffineChartPoint x)) = 1 + U * V := by
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_add, Polynomial.map_one,
      map_map_C_biprojective]
    simp
  rw [eval_bilinSysPoly, biprojectiveCriticalEquation, ← Polynomial.coeff_map,
    biprojectiveCriticalPolynomial, Polynomial.map_sub, Polynomial.map_mul,
    map_biprojectiveLeftFactor, map_biprojectiveRightFactor, hCorrection]
  congr 1
  simp only [criticalLowProduct]
  ring

/-! ## Card equation below the critical horizon -/

/-- Literal separately homogenized equation `(A + alpha U)(B + beta V) - alpha beta`. -/
noncomputable def biprojectiveCardPolynomial (U V : K[X]) (m n : ℕ) :
    (MvPolynomial (BiprojVar m n) K)[X] :=
  biprojectiveLeftFactor U m n * biprojectiveRightFactor V m n -
    Polynomial.C
      (MvPolynomial.X biprojLeftInfinity * MvPolynomial.X biprojRightInfinity)

/-- Its `k`-th coefficient. -/
noncomputable def biprojectiveCardEquation (U V : K[X]) (m n k : ℕ) :
    MvPolynomial (BiprojVar m n) K :=
  (biprojectiveCardPolynomial U V m n).coeff k

theorem biprojectiveCriticalEquation_eq_cardEquation
    (U V : K[X]) (hU : (Polynomial.X : K[X]) ^ m ∣ U)
    (hV : (Polynomial.X : K[X]) ^ n ∣ V) {k : ℕ} (hk : k < m + n) :
    biprojectiveCriticalEquation U V m n k = biprojectiveCardEquation U V m n k := by
  have hUV : (Polynomial.X : K[X]) ^ (m + n) ∣ U * V := by
    rw [pow_add]
    exact mul_dvd_mul hU hV
  have hcoeff : (U * V).coeff k = 0 :=
    (Polynomial.X_pow_dvd_iff.mp hUV) k hk
  rw [biprojectiveCriticalEquation, biprojectiveCardEquation,
    biprojectiveCriticalPolynomial, biprojectiveCardPolynomial]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_add,
    Polynomial.coeff_map, hcoeff, map_zero, add_zero]
  rw [← Polynomial.coeff_C_mul, mul_one]

theorem biprojectiveCardEquation_isWeightedHomogeneous
    (U V : K[X]) (hU : (Polynomial.X : K[X]) ^ m ∣ U)
    (hV : (Polynomial.X : K[X]) ^ n ∣ V) {k : ℕ} (hk : k < m + n) :
    (biprojectiveCardEquation U V m n k).IsWeightedHomogeneous
      biprojectiveWeight (1, 1) := by
  rw [← biprojectiveCriticalEquation_eq_cardEquation U V hU hV hk]
  exact biprojectiveCriticalEquation_isWeightedHomogeneous U V k

end GaloisForLFunctions.HTGeometry
