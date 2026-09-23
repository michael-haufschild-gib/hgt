import GaloisForLFunctions.RHTower.XiShiftedHardEdgeAdaptiveArithmeticSourceLaw
import GaloisForLFunctions.RHTower.PrimeArchScaledHausdorffDivisorValueRelation

/-!
# Complete Hausdorff-diagonal landing of the hard-edge arithmetic source

Inverse reciprocal clearing sends a hard-edge monomial `U^j` to the finite endpoint polynomial

`X^(D-j) (1-yX)^j`.

Consequently the literal adaptive rational--Gamma-minus-von Mangoldt source is a weighted sum of
one complete scaled-Hausdorff diagonal of total degree `D = M+N+2`.  This identifies the cofinal
source producer with the Hausdorff object used by the corpus RH criteria, without adding a fixed
reporter.

The reverse-Euler operator has no kernel below depth `D`.  Thus source construction loses no
finite hard-edge information; the remaining obstruction is sign on the admitted cone.  Pointwise
sign was already disproved in the parent module.
-/

open Complex Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem reflect_sub_pow (y : ℝ) (j : ℕ) :
    (((X : Polynomial ℝ) - C y) ^ j).reflect j =
      (1 - C y * X) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hbase : ((X : Polynomial ℝ) - C y).natDegree ≤ 1 := by
        exact le_trans (Polynomial.natDegree_sub_le _ _) (by simp)
      have hpow : (((X : Polynomial ℝ) - C y) ^ j).natDegree ≤ j := by
        calc
          (((X : Polynomial ℝ) - C y) ^ j).natDegree ≤
              j * ((X : Polynomial ℝ) - C y).natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ j * 1 := Nat.mul_le_mul_left j hbase
          _ = j := Nat.mul_one j
      rw [pow_succ, Polynomial.reflect_mul _ _ hpow hbase, ih]
      have hreflectBase : ((X : Polynomial ℝ) - C y).reflect 1 = 1 - C y * X := by
        rw [Polynomial.reflect_sub, Polynomial.reflect_one_X, Polynomial.reflect_C]
        ring
      rw [hreflectBase, pow_succ]

/-- A hard-edge monomial is exactly a member of the finite complete Hausdorff diagonal after
inverse reciprocal clearing. -/
theorem xiShiftedHardEdgeReciprocalUnclearing_X_pow
    {y : ℝ} {D j : ℕ} (hj : j ≤ D) :
    xiShiftedHardEdgeReciprocalUnclearing y D ((X : Polynomial ℝ) ^ j) =
      X ^ (D - j) * (1 - C y * X) ^ j := by
  rw [xiShiftedHardEdgeReciprocalUnclearing]
  simp only [Polynomial.pow_comp, Polynomial.X_comp]
  rw [← Nat.sub_add_cancel hj]
  conv_lhs =>
    rw [← one_mul (((X : Polynomial ℝ) - C y) ^ j)]
  have hpow : (((X : Polynomial ℝ) - C y) ^ j).natDegree ≤ j := by
    calc
      (((X : Polynomial ℝ) - C y) ^ j).natDegree ≤
          j * ((X : Polynomial ℝ) - C y).natDegree :=
        Polynomial.natDegree_pow_le
      _ ≤ j * 1 := Nat.mul_le_mul_left j
        (le_trans (Polynomial.natDegree_sub_le _ _) (by simp))
      _ = j := Nat.mul_one j
  rw [Polynomial.reflect_mul 1 _ (by simp) hpow,
    Polynomial.reflect_one, reflect_sub_pow]
  have hexponent : D - j + j - j = D - j := by omega
  rw [hexponent]

/-- Dual hard-edge monomials are exactly scaled Hausdorff differences on one complete diagonal. -/
theorem momentFunctional_hardEdgeUnclearing_X_pow_eq_scaledHausdorff
    (m : ℕ → ℝ) {y : ℝ} (hy : 0 < y) {D j : ℕ} (hj : j ≤ D) :
    HTGeometry.momentFunctional m
        (xiShiftedHardEdgeReciprocalUnclearing y D ((X : Polynomial ℝ) ^ j)) =
      y ^ j * scaledHausdorffMomentDifference (1 / y) m (D - j) j := by
  rw [xiShiftedHardEdgeReciprocalUnclearing_X_pow hj,
    scaledHausdorffMomentDifference_eq_momentFunctional,
    ← HTGeometry.momentFunctional_smul]
  congr 1
  simp only [Polynomial.smul_eq_C_mul]
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hpoly : C y * (C (1 / y) - X) = 1 - C y * X := by
    rw [mul_sub, ← Polynomial.C_mul]
    field_simp [hy0]
    simp
  symm
  calc
    C (y ^ j) * (X ^ (D - j) * (C (1 / y) - X) ^ j) =
        X ^ (D - j) * (C y * (C (1 / y) - X)) ^ j := by
      rw [map_pow, mul_pow]
      ring
    _ = _ := by rw [hpoly]

/-- Every depth-bounded hard-edge polynomial lands on a single complete scaled-Hausdorff
diagonal; no off-diagonal or fixed observation is introduced. -/
theorem momentFunctional_hardEdgeUnclearing_eq_completeHausdorffDiagonal
    (m : ℕ → ℝ) {y : ℝ} (hy : 0 < y) {D : ℕ}
    {T : Polynomial ℝ} (hT : T.natDegree ≤ D) :
    HTGeometry.momentFunctional m
        (xiShiftedHardEdgeReciprocalUnclearing y D T) =
      T.support.sum (fun j =>
        T.coeff j * (y ^ j *
          scaledHausdorffMomentDifference (1 / y) m (D - j) j)) := by
  have hjD (j : ℕ) (hj : j ∈ T.support) : j ≤ D := by
    exact (Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hj)).trans hT
  conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq T]
  simp only [Polynomial.sum, xiShiftedHardEdgeReciprocalUnclearing]
  rw [Polynomial.sum_comp]
  have hreflectSum (s : Finset ℕ) (f : ℕ → Polynomial ℝ) :
      (∑ j ∈ s, f j).reflect D = ∑ j ∈ s, (f j).reflect D := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hjs ih => simp [hjs, ih, Polynomial.reflect_add]
  rw [hreflectSum, HTGeometry.momentFunctional_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.reflect_C_mul,
    HTGeometry.momentFunctional_C_mul]
  change T.coeff j * HTGeometry.momentFunctional m
      (xiShiftedHardEdgeReciprocalUnclearing y D (X ^ j)) = _
  rw [momentFunctional_hardEdgeUnclearing_X_pow_eq_scaledHausdorff
    m hy (hjD j hj)]

/-- Clearing preserves its supplied admission-degree bound. -/
theorem natDegree_xiShiftedHardEdgeReciprocalClearing_le
    {A : Polynomial ℝ} {N : ℕ} (hA : A.natDegree ≤ N) (y : ℝ) :
    (xiShiftedHardEdgeReciprocalClearing y N A).natDegree ≤ N := by
  rw [xiShiftedHardEdgeReciprocalClearing]
  calc
    ((A.reflect N).comp (X + C y)).natDegree ≤
        (A.reflect N).natDegree * (X + C y).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ N * 1 := by
      gcongr
      · exact Polynomial.natDegree_reflect_le.trans (max_le le_rfl hA)
      · calc
          (X + C y).natDegree ≤ max X.natDegree (C y).natDegree :=
            Polynomial.natDegree_add_le _ _
          _ ≤ 1 := by simp
    _ = N := Nat.mul_one N

/-- Reverse Euler does not raise the degree of its input. -/
theorem natDegree_xiShiftedHardEdgeReverseEulerSource_le
    {S : Polynomial ℝ} {K : ℕ} (hS : S.natDegree ≤ K) (y : ℝ) (d : ℕ) :
    (xiShiftedHardEdgeReverseEulerSource y d S).natDegree ≤ K := by
  rw [xiShiftedHardEdgeReverseEulerSource]
  apply le_trans (Polynomial.natDegree_sub_le _ _)
  apply max_le
  · exact le_trans (Polynomial.natDegree_smul_le _ _) hS
  · by_cases hd : S.derivative = 0
    · rw [hd, mul_zero]
      simp
    · have hSpos : 0 < S.natDegree := by
        apply Nat.pos_of_ne_zero
        intro hzero
        exact hd (Polynomial.derivative_eq_zero.mpr hzero)
      calc
        ((X + C y) * S.derivative).natDegree ≤
            (X + C y).natDegree + S.derivative.natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ 1 + (S.natDegree - 1) := by
          exact Nat.add_le_add
            (le_trans (Polynomial.natDegree_add_le _ _) (by simp))
            (Polynomial.natDegree_derivative_le S)
        _ ≤ S.natDegree := by omega
        _ ≤ K := hS

/-- The hard-edge bilinear source lies two degrees below its reverse-Euler depth. -/
theorem natDegree_xiShiftedHardEdgeAdaptiveBilinearSource_le
    {A B : Polynomial ℝ} {M N : ℕ}
    (hA : A.natDegree ≤ M) (hB : B.natDegree ≤ N) (y : ℝ) :
    (xiShiftedHardEdgeAdaptiveBilinearSource y M N A B).natDegree ≤ M + N := by
  apply natDegree_xiShiftedHardEdgeReverseEulerSource_le
    (K := M + N)
  calc
    (xiShiftedHardEdgeReciprocalClearing y M A *
        xiShiftedHardEdgeReciprocalClearing y N B).natDegree ≤
      (xiShiftedHardEdgeReciprocalClearing y M A).natDegree +
        (xiShiftedHardEdgeReciprocalClearing y N B).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ M + N := Nat.add_le_add
      (natDegree_xiShiftedHardEdgeReciprocalClearing_le hA y)
      (natDegree_xiShiftedHardEdgeReciprocalClearing_le hB y)

/-- Coefficients of reverse Euler form a triangular transport along the complete Hausdorff
diagonal. -/
theorem coeff_xiShiftedHardEdgeReverseEulerSource
    (y : ℝ) (d : ℕ) (S : Polynomial ℝ) (k : ℕ) :
    (xiShiftedHardEdgeReverseEulerSource y d S).coeff k =
      ((d : ℝ) - (k : ℝ)) * S.coeff k -
        y * ((k : ℝ) + 1) * S.coeff (k + 1) := by
  have hX : (X * S.derivative).coeff k = (k : ℝ) * S.coeff k := by
    cases k with
    | zero => simp
    | succ k =>
        rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
        push_cast
        ring
  rw [xiShiftedHardEdgeReverseEulerSource, Polynomial.coeff_sub,
    Polynomial.coeff_smul]
  rw [add_mul, Polynomial.coeff_add, hX,
    Polynomial.coeff_C_mul, Polynomial.coeff_derivative]
  ring

/-- **No finite information loss.** Reverse Euler has no kernel below its admission depth. -/
theorem xiShiftedHardEdgeReverseEulerSource_eq_zero_iff_of_natDegree_lt
    {y : ℝ} {d : ℕ} {S : Polynomial ℝ} (hSdeg : S.natDegree < d) :
    xiShiftedHardEdgeReverseEulerSource y d S = 0 ↔ S = 0 := by
  constructor
  · intro hsource
    by_contra hS
    have hcoeff := congrArg
      (fun P : Polynomial ℝ => P.coeff S.natDegree) hsource
    rw [coeff_xiShiftedHardEdgeReverseEulerSource] at hcoeff
    simp only [Polynomial.coeff_zero] at hcoeff
    have hnext : S.coeff (S.natDegree + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
    rw [hnext, mul_zero, sub_zero] at hcoeff
    have hfactor : (d : ℝ) - (S.natDegree : ℝ) ≠ 0 := by
      have hcast : (S.natDegree : ℝ) < (d : ℝ) := by exact_mod_cast hSdeg
      linarith
    have hlead : S.leadingCoeff = 0 := by
      rw [Polynomial.leadingCoeff]
      exact (mul_eq_zero.mp hcoeff).resolve_left hfactor
    exact hS (Polynomial.leadingCoeff_eq_zero.mp hlead)
  · rintro rfl
    simp [xiShiftedHardEdgeReverseEulerSource]

/-- **Completed arithmetic complete-diagonal law.** The literal bilinear arithmetic source is a
weighted aggregate on one scaled-Hausdorff diagonal of total depth `M+N+2`. -/
theorem xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_completeHausdorffDiagonal
    {w : ℝ} (hw : 1 / 2 < w) {A B : Polynomial ℝ} {M N : ℕ}
    (hA : A.natDegree ≤ M) (hB : B.natDegree ≤ N) :
    let T := xiShiftedHardEdgeAdaptiveBilinearSource (w ^ (2 : ℕ)) M N A B
    xiShiftedAdaptiveBilinearCompletedArithmeticSource w A B =
      T.support.sum (fun j =>
        T.coeff j * ((w ^ (2 : ℕ)) ^ j *
          scaledHausdorffMomentDifference (1 / (w ^ (2 : ℕ)))
            (xiShiftedRealMomentSequence w) (M + N + 2 - j) j)) := by
  dsimp only
  rw [xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_hardEdgeLanding
    hw hA hB]
  exact momentFunctional_hardEdgeUnclearing_eq_completeHausdorffDiagonal
    (xiShiftedRealMomentSequence w)
    (sq_pos_of_pos (by linarith : 0 < w))
    ((natDegree_xiShiftedHardEdgeAdaptiveBilinearSource_le hA hB (w ^ (2 : ℕ))).trans
      (by omega))

/-- **Adaptive mixed `P^sharp` complete-diagonal law.** The diagonal rational--Gamma/von
Mangoldt formation lands on the same cofinal scaled-Hausdorff diagonal. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_eq_completeHausdorffDiagonal
    {w : ℝ} (hw : 1 / 2 < w) {A : Polynomial ℝ} {N : ℕ}
    (hA : A.natDegree ≤ N) :
    let T := xiShiftedHardEdgeAdaptiveBilinearSource (w ^ (2 : ℕ)) N N A A
    xiShiftedAdaptiveMixedCompletedArithmeticSource w A =
      T.support.sum (fun j =>
        T.coeff j * ((w ^ (2 : ℕ)) ^ j *
          scaledHausdorffMomentDifference (1 / (w ^ (2 : ℕ)))
            (xiShiftedRealMomentSequence w) (2 * N + 2 - j) j)) := by
  rw [← xiShiftedAdaptiveBilinearCompletedArithmeticSource_self_eq_mixed hw]
  simpa only [show N + N + 2 = 2 * N + 2 by omega] using
    xiShiftedAdaptiveBilinearCompletedArithmeticSource_eq_completeHausdorffDiagonal
      hw hA hA

end

end RHTower
