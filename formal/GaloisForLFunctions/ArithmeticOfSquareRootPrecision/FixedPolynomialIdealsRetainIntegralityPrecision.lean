import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheIntegralityLatticeOfTheHorizon
import GaloisForLFunctions.HTGeometry.ContinuousSquareIntegralPositive

/-!
# The arithmetic of Nair integrals in a polynomial ideal

Multiples of a fixed integer polynomial have rational moments with consecutive denominators.
Their integral lattice is governed by the gcd of these moments after multiplication by the
horizon period. Denominator cofactors isolate the leading coefficient from the lower terms.
-/

noncomputable section

open Polynomial Finset intervalIntegral

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- The rational moment `∫₀¹ x^j Q(x) dx`, written without an analytic integral. -/
def nairRationalMoment (Q : ℤ[X]) (j : ℕ) : ℚ :=
  ∑ i ∈ range (Q.natDegree + 1), (Q.coeff i : ℚ) / (j + i + 1 : ℕ)

theorem nairIntegral_mul_X_pow (Q : ℤ[X]) (j : ℕ) :
    nairIntegral (Q * X ^ j) = (nairRationalMoment Q j : ℝ) := by
  have hexp : (fun x : ℝ => aeval x (Q * X ^ j)) =
      fun x => ∑ i ∈ range (Q.natDegree + 1), (Q.coeff i : ℝ) * x ^ (j + i) := by
    funext x
    rw [map_mul, map_pow, aeval_X, aeval_eq_sum_range]
    simp only [zsmul_eq_mul, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← pow_add, Nat.add_comm]
  unfold nairIntegral
  rw [hexp, integral_finsetSum (f := fun i x => (Q.coeff i : ℝ) * x ^ (j + i))
    fun i _ => (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _]
  unfold nairRationalMoment
  push_cast
  refine sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_pow]
  norm_num [div_eq_mul_inv, add_assoc]

/-- The product of the lower denominators of the `j`th moment of a degree-`m` polynomial. -/
def momentDenominatorCofactor (m j : ℕ) : ℤ :=
  ∏ i ∈ range m, (j + i + 1 : ℕ)

private def fixedMomentCofactor (m : ℕ) : ℤ := ∏ i ∈ range m, ((i : ℤ) - m)

/-- The residue left by the last denominator, multiplied by its integer cofactor.
It equals `leadingCoeff(Q) (-1)^deg(Q) deg(Q)!`. -/
def idealMomentResidue (Q : ℤ[X]) : ℤ :=
  Q.coeff Q.natDegree * fixedMomentCofactor Q.natDegree

theorem idealMomentResidue_ne_zero {Q : ℤ[X]} (hQ : Q ≠ 0) :
    idealMomentResidue Q ≠ 0 := by
  refine mul_ne_zero ?_ (prod_ne_zero_iff.mpr fun i hi => ?_)
  · rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hQ
  · exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_lt (mem_range.mp hi)))

private theorem momentDenominatorCofactor_remainder (m j : ℕ) :
    ∃ z : ℤ, momentDenominatorCofactor m j =
      fixedMomentCofactor m + (j + m + 1 : ℕ) * z := by
  have hmod : Int.ModEq ((j + m + 1 : ℕ) : ℤ)
      (momentDenominatorCofactor m j) (fixedMomentCofactor m) := by
    refine Int.ModEq.prod fun i _ => Int.modEq_iff_dvd.mpr ⟨-1, ?_⟩
    push_cast
    ring
  obtain ⟨z, hz⟩ := Int.modEq_iff_dvd.mp hmod.symm
  exact ⟨z, by linarith only [hz]⟩

/-- Clearing the lower moment denominators leaves an integer and a fixed nonzero numerator
over the last denominator. The numerator is independent of the moment index. -/
theorem exists_int_cofactor_mul_nairRationalMoment (Q : ℤ[X]) (j : ℕ) :
    ∃ z : ℤ, (momentDenominatorCofactor Q.natDegree j : ℚ) * nairRationalMoment Q j =
      (z : ℚ) + (idealMomentResidue Q : ℚ) / (j + Q.natDegree + 1 : ℕ) := by
  let m := Q.natDegree
  let E : ℕ → ℤ := fun i => ∏ k ∈ (range m).erase i, (j + k + 1 : ℕ)
  obtain ⟨z, hz⟩ := momentDenominatorCofactor_remainder m j
  have hterm (i : ℕ) (hi : i ∈ range m) :
      (momentDenominatorCofactor m j : ℚ) * ((Q.coeff i : ℚ) / (j + i + 1 : ℕ)) =
        (Q.coeff i * E i : ℤ) := by
    have hprod : momentDenominatorCofactor m j = (j + i + 1 : ℕ) * E i :=
      (mul_prod_erase (range m) (fun k => ((j + k + 1 : ℕ) : ℤ)) hi).symm
    rw [hprod]
    push_cast
    field_simp
  refine ⟨(∑ i ∈ range m, Q.coeff i * E i) + Q.coeff m * z, ?_⟩
  unfold nairRationalMoment
  rw [sum_range_succ, mul_add, mul_sum]
  have hsum : (∑ i ∈ range m,
      (momentDenominatorCofactor m j : ℚ) * ((Q.coeff i : ℚ) / (j + i + 1 : ℕ))) =
        ((∑ i ∈ range m, Q.coeff i * E i : ℤ) : ℚ) := by
    rw [Int.cast_sum]
    exact sum_congr rfl hterm
  rw [hsum]
  have hz' : (momentDenominatorCofactor m j : ℚ) =
      (fixedMomentCofactor m : ℚ) + ((j + m + 1 : ℕ) : ℚ) * (z : ℚ) := by
    exact_mod_cast hz
  rw [hz']
  simp only [idealMomentResidue, Int.cast_add, Int.cast_mul]
  change _ = _ + _ / ((j + m + 1 : ℕ) : ℚ)
  have hd : ((j + m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp
  ring

theorem nairIntegral_C_mul (c : ℤ) (P : ℤ[X]) :
    nairIntegral (C c * P) = (c : ℝ) * nairIntegral P := by
  unfold nairIntegral
  simp only [map_mul, map_intCast, eq_intCast]
  exact integral_const_mul _ _

theorem nairIntegral_sub (P R : ℤ[X]) :
    nairIntegral (P - R) = nairIntegral P - nairIntegral R := by
  unfold nairIntegral
  simp only [map_sub]
  exact integral_sub ((continuous_aeval P).intervalIntegrable _ _)
    ((continuous_aeval R).intervalIntegrable _ _)

theorem nairIntegral_sum {ι : Type*} (s : Finset ι) (P : ι → ℤ[X]) :
    nairIntegral (∑ i ∈ s, P i) = ∑ i ∈ s, nairIntegral (P i) := by
  unfold nairIntegral
  simp only [map_sum]
  exact integral_finsetSum fun i _ => (continuous_aeval (P i)).intervalIntegrable _ _

private theorem nairIntegral_mul_self_pos {Q : ℤ[X]} (hQ : Q ≠ 0) :
    0 < nairIntegral (Q * Q) := by
  have hmap : Q.map (algebraMap ℤ ℝ) ≠ 0 := by
    intro hz
    apply hQ
    apply Polynomial.map_injective (algebraMap ℤ ℝ) Int.cast_injective
    simpa only [Polynomial.map_zero] using hz
  have hpoint : ∃ x ∈ Set.Ioo (0 : ℝ) 1, aeval x Q ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hmap
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ (Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1))
    intro x hx
    simpa only [IsRoot, eval_map, ← aeval_def] using hn x hx
  obtain ⟨x, hx, hne⟩ := hpoint
  have hpos := HTGeometry.integral_sq_pos_of_ne_zero (continuous_aeval Q) hx hne
  simpa only [nairIntegral, map_mul, pow_two] using hpos

private theorem exists_positive_integral_multiple {Q : ℤ[X]} (hQ : Q ≠ 0) :
    ∃ H : ℤ[X], ∃ K : ℤ, Q ∣ H ∧ H.natDegree ≤ 2 * Q.natDegree ∧
      0 < K ∧ nairIntegral H = (K : ℝ) := by
  have hdeg : (Q * Q).natDegree ≤ 2 * Q.natDegree := by
    simpa only [two_mul] using natDegree_mul_le Q Q
  obtain ⟨K, hK⟩ := ArithmeticEffectivityTheory.exists_int_eq_lcmUpto_mul_integral
    (Q * Q) hdeg
  let d : ℤ := Nat.lcmUpto (2 * Q.natDegree + 1)
  have hint : nairIntegral (C d * (Q * Q)) = (K : ℝ) := by
    rw [nairIntegral_C_mul]
    exact hK
  refine ⟨C d * (Q * Q), K, ⟨C d * Q, by ring⟩,
    (natDegree_C_mul_le _ _).trans hdeg, ?_, hint⟩
  have hpos : (0 : ℝ) < nairIntegral (C d * (Q * Q)) := by
    rw [nairIntegral_C_mul]
    exact mul_pos (by exact_mod_cast Nat.lcmUpto_pos (2 * Q.natDegree + 1))
      (nairIntegral_mul_self_pos hQ)
  rw [hint] at hpos
  exact_mod_cast hpos

private theorem exists_multiple_nairIntegral_eq_residue (Q H : ℤ[X]) (K : ℤ)
    (hH : Q ∣ H) (hdegH : H.natDegree ≤ 2 * Q.natDegree)
    (hintH : nairIntegral H = (K : ℝ)) (j : ℕ) :
    ∃ P : ℤ[X], Q ∣ P ∧ P.natDegree ≤ max (Q.natDegree + j) (2 * Q.natDegree) ∧
      nairIntegral P = (K : ℝ) * idealMomentResidue Q / (j + Q.natDegree + 1 : ℕ) := by
  obtain ⟨z, hz⟩ := exists_int_cofactor_mul_nairRationalMoment Q j
  refine ⟨C (K * momentDenominatorCofactor Q.natDegree j) * (Q * X ^ j) - C z * H,
    dvd_sub (dvd_mul_of_dvd_right (dvd_mul_right Q (X ^ j)) _) (dvd_mul_of_dvd_right hH _),
    (natDegree_sub_le _ _).trans (max_le_max ?_ ?_), ?_⟩
  · exact (natDegree_C_mul_le _ _).trans
      ((natDegree_mul_le _ _).trans (Nat.add_le_add_left (natDegree_X_pow_le j) _))
  · exact (natDegree_C_mul_le _ _).trans hdegH
  · rw [nairIntegral_sub, nairIntegral_C_mul, nairIntegral_C_mul,
      nairIntegral_mul_X_pow, hintH, Int.cast_mul]
    have hz' : (momentDenominatorCofactor Q.natDegree j : ℝ) *
        (nairRationalMoment Q j : ℝ) =
          (z : ℝ) + (idealMomentResidue Q : ℝ) / (j + Q.natDegree + 1 : ℕ) := by
      exact_mod_cast hz
    rw [mul_assoc, hz']
    ring

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
