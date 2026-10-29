import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheIntegralityLatticeOfTheHorizon
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheIntegralityExponentIsTheZeroWidth
import GaloisForLFunctions.HTGeometry.ContinuousSquareIntegralPositive

/-!
# The arithmetic of Nair integrals in a polynomial ideal

Multiples of a fixed integer polynomial have rational moments with consecutive denominators.
Their integral lattice is governed by the gcd of these moments after multiplication by the
horizon period. Denominator cofactors isolate the leading coefficient from the lower terms.
-/

noncomputable section

open Polynomial Finset intervalIntegral Filter Topology

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
    simpa only [two_mul] using (natDegree_mul_le (p := Q) (q := Q))
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
      ((natDegree_mul_le (p := Q) (q := X ^ j)).trans
        (Nat.add_le_add_left (natDegree_X_pow_le j) _))
  · exact (natDegree_C_mul_le _ _).trans hdegH
  · rw [nairIntegral_sub, nairIntegral_C_mul, nairIntegral_C_mul,
      nairIntegral_mul_X_pow, hintH, Int.cast_mul]
    have hz' : (momentDenominatorCofactor Q.natDegree j : ℝ) *
        (nairRationalMoment Q j : ℝ) =
          (z : ℝ) + (idealMomentResidue Q : ℝ) / (j + Q.natDegree + 1 : ℕ) := by
      exact_mod_cast hz
    rw [mul_assoc, hz']
    ring

private theorem exists_uniform_reciprocal_multiples {Q : ℤ[X]} (hQ : Q ≠ 0) :
    ∃ C₀ : ℤ, 0 < C₀ ∧ ∀ n : ℕ, 2 * Q.natDegree ≤ n →
      ∀ k ∈ Icc 1 (n + 1), ∃ P : ℤ[X], Q ∣ P ∧ P.natDegree ≤ n ∧
        nairIntegral P = (C₀ : ℝ) / k := by
  obtain ⟨H, K, hH, hdegH, hK, hintH⟩ := exists_positive_integral_multiple hQ
  let A := idealMomentResidue Q
  let d := Nat.lcmUpto Q.natDegree
  let σ : ℤ := if 0 ≤ A then 1 else -1
  have hA : A ≠ 0 := idealMomentResidue_ne_zero hQ
  have hσ : σ * A = |A| := by
    dsimp [σ]
    split_ifs with ha
    · simp only [one_mul, abs_of_nonneg ha]
    · simp only [neg_one_mul, abs_of_neg (lt_of_not_ge ha)]
  refine ⟨K * |A| * d, mul_pos (mul_pos hK (abs_pos.mpr hA))
    (by exact_mod_cast Nat.lcmUpto_pos Q.natDegree), ?_⟩
  intro n hn k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
  by_cases hkm : k ≤ Q.natDegree
  · have hkd : k ∣ d := Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨(mem_Icc.mp hk).1, hkm⟩)
    obtain ⟨e, he⟩ := hkd
    refine ⟨C (|A| * e) * H, dvd_mul_of_dvd_right hH _,
      (natDegree_C_mul_le _ _).trans (hdegH.trans hn), ?_⟩
    rw [nairIntegral_C_mul, hintH]
    push_cast
    have he' : (d : ℝ) = (k : ℝ) * e := by exact_mod_cast he
    rw [he']
    field_simp
    ring
  · let j := k - Q.natDegree - 1
    have hj : j + Q.natDegree + 1 = k := by dsimp [j]; omega
    obtain ⟨P, hP, hdegP, hintP⟩ :=
      exists_multiple_nairIntegral_eq_residue Q H K hH hdegH hintH j
    refine ⟨C (σ * d) * P, dvd_mul_of_dvd_right hP _,
      (natDegree_C_mul_le _ _).trans (hdegP.trans (max_le ?_ hn)), ?_⟩
    · have := (mem_Icc.mp hk).2
      omega
    · rw [nairIntegral_C_mul, hintP, hj]
      simp only [Int.cast_mul, Int.cast_natCast]
      have hσ' : (σ : ℝ) * (A : ℝ) = (|A| : ℤ) := by exact_mod_cast hσ
      change (σ : ℝ) * (d : ℝ) * ((K : ℝ) * (A : ℝ) / k) =
        (K : ℝ) * (|A| : ℤ) * (d : ℝ) / k
      calc
        _ = (K : ℝ) * ((σ : ℝ) * (A : ℝ)) * (d : ℝ) / k := by ring
        _ = _ := by rw [hσ']

/-- Every fixed nonzero polynomial ideal contains a reciprocal horizon witness with one
positive numerator independent of the horizon. Thus fixed divisibility costs only a bounded
factor in the integrality floor. -/
theorem exists_uniform_nairIntegral_multiple {Q : ℤ[X]} (hQ : Q ≠ 0) :
    ∃ C₀ : ℤ, 0 < C₀ ∧ ∀ n : ℕ, 2 * Q.natDegree ≤ n →
      ∃ P : ℤ[X], Q ∣ P ∧ P.natDegree ≤ n ∧
        nairIntegral P = (C₀ : ℝ) / (Nat.lcmUpto (n + 1) : ℕ) := by
  classical
  obtain ⟨C₀, hC₀, hrecip⟩ := exists_uniform_reciprocal_multiples hQ
  refine ⟨C₀, hC₀, fun n hn => ?_⟩
  obtain ⟨c, hc⟩ := exists_int_sum_div_eq_inv_lcm (Icc 1 (n + 1)) ⟨1, by simp⟩
    (f := id) fun i hi => (mem_Icc.mp hi).1
  choose P hP hdegP hintP using hrecip n hn
  let R : ℕ → ℤ[X] := fun k => if hk : k ∈ Icc 1 (n + 1) then C (c k) * P k hk else 0
  have hR (k : ℕ) (hk : k ∈ Icc 1 (n + 1)) : R k = C (c k) * P k hk := dif_pos hk
  refine ⟨∑ k ∈ Icc 1 (n + 1), R k, ?_, ?_, ?_⟩
  · exact Finset.dvd_sum fun k hk => by rw [hR k hk]; exact dvd_mul_of_dvd_right (hP k hk) _
  · exact natDegree_sum_le_of_forall_le _ _ fun k hk => by
      rw [hR k hk]
      exact (natDegree_C_mul_le _ _).trans (hdegP k hk)
  · rw [nairIntegral_sum]
    calc
      _ = ∑ k ∈ Icc 1 (n + 1), (C₀ : ℝ) * ((c k : ℝ) / k) := by
        refine sum_congr rfl fun k hk => ?_
        rw [hR k hk, nairIntegral_C_mul, hintP k hk]
        ring
      _ = (C₀ : ℝ) / (Nat.lcmUpto (n + 1) : ℕ) := by
        rw [← mul_sum, hc]
        simp only [Nat.lcmUpto, id_eq]
        ring

/-- The Siegel existence criterion with the auxiliary restricted to the ideal `(Q)`. -/
def IdealSiegelHalf (Q : ℤ[X]) (φ : ℝ → ℝ) : Prop :=
  ∃ C₀ : ℝ, ∀ᶠ n : ℕ in atTop, ∃ P : ℤ[X], Q ∣ P ∧ P.natDegree ≤ n ∧
    0 < nairIntegral P ∧
      nairIntegral P ≤ Real.exp (-((n + 1 : ℕ) : ℝ) + C₀ * φ (n + 1 : ℕ))

/-- The Liouville lower-bound criterion restricted to the ideal `(Q)`. -/
def IdealLiouvilleHalf (Q : ℤ[X]) (φ : ℝ → ℝ) : Prop :=
  ∃ C₀ : ℝ, ∀ᶠ n : ℕ in atTop, ∀ P : ℤ[X], Q ∣ P → P.natDegree ≤ n →
    0 < nairIntegral P →
      Real.exp (-((n + 1 : ℕ) : ℝ) - C₀ * φ (n + 1 : ℕ)) ≤ nairIntegral P

private theorem uniform_numerator_exp (C₀ : ℤ) (hC₀ : 0 < C₀) (N : ℕ) :
    (C₀ : ℝ) / (Nat.lcmUpto N : ℕ) =
      Real.exp (Real.log (C₀ : ℝ) - Chebyshev.psi N) := by
  rw [Real.exp_sub, Real.exp_log (by exact_mod_cast hC₀), Chebyshev.psi_eq_log_lcmUpto,
    Real.exp_log (by exact_mod_cast Nat.lcmUpto_pos N)]

/-- Fixed polynomial divisibility preserves the Siegel half at every admissible scale. -/
theorem idealSiegelHalf_iff {Q : ℤ[X]} (hQ : Q ≠ 0) {φ : ℝ → ℝ}
    (hφ : AdmissibleScale φ) : IdealSiegelHalf Q φ ↔ SiegelHalf φ := by
  constructor
  · rintro ⟨C₀, hC₀⟩
    exact ⟨C₀, hC₀.mono fun n ⟨P, _, hP, hpos, hle⟩ => ⟨P, hP, hpos, hle⟩⟩
  · intro hs
    obtain ⟨B, hB⟩ := (siegelHalf_iff φ).mp hs
    obtain ⟨C₀, hC₀, hC⟩ := exists_uniform_nairIntegral_multiple hQ
    have hlog : 0 ≤ Real.log (C₀ : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show (1 : ℤ) ≤ C₀ by omega))
    refine ⟨B + Real.log (C₀ : ℝ), ?_⟩
    filter_upwards [hB, tendsto_succ_cast_atTop.eventually hφ.eventually_one_le,
      eventually_ge_atTop (2 * Q.natDegree)] with n hn hφn hdeg
    obtain ⟨P, hP, hdegP, hint⟩ := hC n hdeg
    refine ⟨P, hP, hdegP, ?_, ?_⟩
    · rw [hint]
      exact div_pos (by exact_mod_cast hC₀) (by exact_mod_cast Nat.lcmUpto_pos _)
    · rw [hint, uniform_numerator_exp C₀ hC₀]
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hφn hlog
      nlinarith only [hn, hmul]

/-- Fixed polynomial divisibility preserves the Liouville half at every admissible scale. -/
theorem idealLiouvilleHalf_iff {Q : ℤ[X]} (hQ : Q ≠ 0) {φ : ℝ → ℝ}
    (hφ : AdmissibleScale φ) : IdealLiouvilleHalf Q φ ↔ LiouvilleHalf φ := by
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨C₀, hC₀, hC⟩ := exists_uniform_nairIntegral_multiple hQ
    have hlog : 0 ≤ Real.log (C₀ : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show (1 : ℤ) ≤ C₀ by omega))
    apply (liouvilleHalf_iff φ).mpr
    refine ⟨B + Real.log (C₀ : ℝ), ?_⟩
    filter_upwards [hB, tendsto_succ_cast_atTop.eventually hφ.eventually_one_le,
      eventually_ge_atTop (2 * Q.natDegree)] with n hn hφn hdeg
    obtain ⟨P, hP, hdegP, hint⟩ := hC n hdeg
    have hpos : 0 < nairIntegral P := by
      rw [hint]
      exact div_pos (by exact_mod_cast hC₀) (by exact_mod_cast Nat.lcmUpto_pos _)
    have hbound := hn P hP hdegP hpos
    rw [hint, uniform_numerator_exp C₀ hC₀] at hbound
    have hexp := Real.exp_le_exp.mp hbound
    have hmul := mul_le_mul_of_nonneg_left hφn hlog
    nlinarith only [hexp, hmul]
  · rintro ⟨B, hB⟩
    exact ⟨B, hB.mono fun n hn P _ hdeg hpos => hn P hdeg hpos⟩

/-- Every fixed nonzero polynomial ideal has the same square-root Siegel criterion: RH. -/
theorem riemannHypothesis_iff_idealSiegelHalf {Q : ℤ[X]} (hQ : Q ≠ 0) :
    RiemannHypothesis ↔ IdealSiegelHalf Q sqrtScale := by
  rw [idealSiegelHalf_iff hQ admissibleScale_sqrtScale,
    riemannHypothesis_iff_siegelHalf_sqrtScale]

/-- Every fixed nonzero polynomial ideal has the same square-root Liouville criterion: RH. -/
theorem riemannHypothesis_iff_idealLiouvilleHalf {Q : ℤ[X]} (hQ : Q ≠ 0) :
    RiemannHypothesis ↔ IdealLiouvilleHalf Q sqrtScale := by
  rw [idealLiouvilleHalf_iff hQ admissibleScale_sqrtScale,
    riemannHypothesis_iff_liouvilleHalf_sqrtScale]

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
