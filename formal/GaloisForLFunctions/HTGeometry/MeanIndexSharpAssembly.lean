import GaloisForLFunctions.HTGeometry.MeanIndexComparison

/-!
# The sharp assembly of the Wiman--Valiron estimate

Two losses in the assembled estimate are avoidable and both matter at the order of the answer.

The first is the division by the norm of the value.  The exact identity divides the weighted
projection by `‖W‖ = ‖f(z)‖ / mu(r)`, and bounding that denominator below by `1` throws away exactly
the factor that measures how many terms are comparable to the maximum term.  Keeping it gives the
estimate in the form `(S(r) |Lambda - nu| + E mu(r)) / ‖f(z)‖`.

The second is the weighted misalignment.  Bounding `sum |n - nu| d_n` by a window width times
`sum d_n` ignores that each `d_n` enters twice — once in the weight and once in the mass.
Cauchy--Schwarz splits it as `sqrt(sum (n-nu)^2 d_n) * sqrt(sum d_n)`, and since `d_n <= 2 ‖b_n‖`
the first factor is the second moment of the coefficient profile.  The result is
`sqrt(2 * Sigma_2 * D)` — the geometric mean of the second moment and the total misalignment, in
place of their product's crude substitute.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

variable {a : ℕ → ℂ} {r : ℝ}

/-! ## Second moments -/

/-- The squared index deviation is summable against the terms of an entire series. -/
theorem summable_index_deviation_sq (ha : EntireCoeffs a) (hr : 0 < r) (k : ℕ) :
    Summable fun n : ℕ => ((n : ℝ) - (k : ℝ)) ^ 2 * (‖a n‖ * r ^ n) := by
  have h1 : Summable fun n : ℕ => ‖a n‖ * r ^ n := summable_term ha hr
  have h2 : Summable fun n : ℕ => (n : ℝ) * (‖a n‖ * r ^ n) := by
    refine (summable_term (entireCoeffs_mul_index ha) hr).congr fun n => ?_
    rw [norm_mul, Complex.norm_natCast, mul_assoc]
  have h3 : Summable fun n : ℕ => (n : ℝ) * ((n : ℝ) * (‖a n‖ * r ^ n)) := by
    refine (summable_term (entireCoeffs_mul_index (entireCoeffs_mul_index ha)) hr).congr
      fun n => ?_
    rw [norm_mul, Complex.norm_natCast, norm_mul, Complex.norm_natCast]
    ring
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (h3.add ((h2.mul_left (2 * (k : ℝ))).add (h1.mul_left ((k : ℝ) ^ 2))))
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hT : (0 : ℝ) ≤ ‖a n‖ * r ^ n := term_nonneg a hr n
  have hsq : ((n : ℝ) - (k : ℝ)) ^ 2
      ≤ (n : ℝ) * (n : ℝ) + 2 * (k : ℝ) * (n : ℝ) + (k : ℝ) ^ 2 := by nlinarith
  calc ((n : ℝ) - (k : ℝ)) ^ 2 * (‖a n‖ * r ^ n)
      ≤ ((n : ℝ) * (n : ℝ) + 2 * (k : ℝ) * (n : ℝ) + (k : ℝ) ^ 2) * (‖a n‖ * r ^ n) :=
        mul_le_mul_of_nonneg_right hsq hT
    _ = (n : ℝ) * ((n : ℝ) * (‖a n‖ * r ^ n))
        + (2 * (k : ℝ) * ((n : ℝ) * (‖a n‖ * r ^ n)) + (k : ℝ) ^ 2 * (‖a n‖ * r ^ n)) := by
        ring

/-- The normalised coefficients are summable in modulus. -/
theorem summable_norm_normalisedCoeff
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r) :
    Summable fun n : ℕ => ‖normalisedCoeff a r z n‖ := by
  have hzpos : 0 < ‖z‖ := by rw [hz]; exact hr
  have hbase := summable_term ha hzpos
  have hCn : ‖a (centralIndex a r) * z ^ centralIndex a r‖ = maxTerm a r := by
    rw [norm_mul, norm_pow, hz]
    exact term_centralIndex_eq ha hr hn₀
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  refine (hbase.mul_left (maxTerm a r)⁻¹).congr fun n => ?_
  rw [normalisedCoeff_def, norm_div, hCn, norm_mul, norm_pow, hz]
  field_simp

/-- The squared index deviation is summable against the normalised coefficients. -/
theorem summable_index_deviation_sq_normalised
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r) (k : ℕ) :
    Summable fun n : ℕ => ((n : ℝ) - (k : ℝ)) ^ 2 * ‖normalisedCoeff a r z n‖ := by
  have hzpos : 0 < ‖z‖ := by rw [hz]; exact hr
  have hbase := summable_index_deviation_sq ha hzpos k
  have hCn : ‖a (centralIndex a r) * z ^ centralIndex a r‖ = maxTerm a r := by
    rw [norm_mul, norm_pow, hz]
    exact term_centralIndex_eq ha hr hn₀
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  refine (hbase.mul_left (maxTerm a r)⁻¹).congr fun n => ?_
  rw [normalisedCoeff_def, norm_div, hCn, norm_mul, norm_pow, hz]
  field_simp

/-! ## The weighted misalignment by Cauchy--Schwarz -/

/-- Each misalignment is at most twice the modulus of its term. -/
private theorem defect_le_two_mul_norm (c : ℂ) {u : ℂ} (hu : ‖u‖ = 1) :
    ‖c‖ - ((starRingEnd ℂ) u * c).re ≤ 2 * ‖c‖ := by
  have hnorm : ‖(starRingEnd ℂ) u * c‖ = ‖c‖ := by
    rw [norm_mul, RCLike.norm_conj, hu, one_mul]
  have h := Complex.abs_re_le_norm ((starRingEnd ℂ) u * c)
  rw [hnorm] at h
  have := (abs_le.mp h).1
  linarith

/-- **The weighted misalignment as a geometric mean.**  Cauchy--Schwarz splits the weighted
misalignment into the square root of the second moment of the profile times the square root of the
total misalignment. -/
theorem tsum_index_weighted_defect_le_sqrt
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    {u : ℂ} (hu : ‖u‖ = 1) {S₂ D : ℝ}
    (hS₂ : ∑' n : ℕ, ((n : ℝ) - (centralIndex a r : ℝ)) ^ 2 * ‖normalisedCoeff a r z n‖ ≤ S₂)
    (hD : ∑' n : ℕ, (‖normalisedCoeff a r z n‖
        - ((starRingEnd ℂ) u * normalisedCoeff a r z n).re) ≤ D) :
    ∑' n : ℕ, |(n : ℝ) - (centralIndex a r : ℝ)|
        * (‖normalisedCoeff a r z n‖
          - ((starRingEnd ℂ) u * normalisedCoeff a r z n).re)
      ≤ Real.sqrt (2 * S₂ * D) := by
  classical
  set k := centralIndex a r with hk
  set c : ℕ → ℂ := normalisedCoeff a r z with hc
  set d : ℕ → ℝ := fun n => ‖c n‖ - ((starRingEnd ℂ) u * c n).re with hd
  set w : ℕ → ℝ := fun n => (n : ℝ) - (k : ℝ) with hw
  have hdnn : ∀ n, 0 ≤ d n := fun n => alignment_defect_nonneg (c n) hu
  have hd2 : ∀ n, d n ≤ 2 * ‖c n‖ := fun n => defect_le_two_mul_norm (c n) hu
  have habs := summable_index_deviation_normalised ha hr hn₀ hz k
  have hsq := summable_index_deviation_sq_normalised ha hr hn₀ hz k
  have hnorm := summable_norm_normalisedCoeff ha hr hn₀ hz
  have hdsum : Summable d :=
    Summable.of_nonneg_of_le hdnn hd2 (hnorm.mul_left 2)
  have hsqd : Summable fun n => w n ^ 2 * d n := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (hdnn n)) (fun n => ?_)
      (hsq.mul_left 2)
    have h := hd2 n
    nlinarith [sq_nonneg (w n), norm_nonneg (c n)]
  have hwsum : Summable fun n => |w n| * d n := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (hdnn n)) (fun n => ?_)
      (habs.mul_left 2)
    have h := hd2 n
    nlinarith [abs_nonneg (w n), norm_nonneg (c n)]
  -- the two moment bounds
  have hS₂nn : (0 : ℝ) ≤ S₂ :=
    le_trans (tsum_nonneg fun n => mul_nonneg (sq_nonneg _) (norm_nonneg _)) hS₂
  have hDnn : (0 : ℝ) ≤ D := le_trans (tsum_nonneg hdnn) hD
  have hprod : (0 : ℝ) ≤ 2 * S₂ * D := by positivity
  refine le_of_tendsto hwsum.hasSum.tendsto_sum_nat (Filter.Eventually.of_forall fun m => ?_)
  set s : Finset ℕ := Finset.range m with hsdef
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s (fun n => |w n| * Real.sqrt (d n))
    (fun n => Real.sqrt (d n))
  have hprodeq : ∀ n : ℕ, (|w n| * Real.sqrt (d n)) * Real.sqrt (d n) = |w n| * d n := by
    intro n
    rw [mul_assoc, Real.mul_self_sqrt (hdnn n)]
  have hf2 : ∀ n : ℕ, (|w n| * Real.sqrt (d n)) ^ 2 = w n ^ 2 * d n := by
    intro n
    rw [mul_pow, sq_abs, Real.sq_sqrt (hdnn n)]
  have hg2 : ∀ n : ℕ, (Real.sqrt (d n)) ^ 2 = d n := fun n => Real.sq_sqrt (hdnn n)
  rw [Finset.sum_congr rfl (fun n _ => hprodeq n), Finset.sum_congr rfl (fun n _ => hf2 n),
    Finset.sum_congr rfl (fun n _ => hg2 n)] at hCS
  have hbound1 : ∑ n ∈ s, w n ^ 2 * d n ≤ 2 * S₂ := by
    refine le_trans (Summable.sum_le_tsum s (fun n _ => mul_nonneg (sq_nonneg _) (hdnn n)) hsqd) ?_
    refine le_trans (Summable.tsum_le_tsum (fun n => ?_) hsqd (hsq.mul_left 2)) ?_
    · have h := hd2 n
      nlinarith [sq_nonneg (w n), norm_nonneg (c n)]
    · rw [tsum_mul_left]
      linarith
  have hbound2 : ∑ n ∈ s, d n ≤ D :=
    le_trans (Summable.sum_le_tsum s (fun n _ => hdnn n) hdsum) hD
  have hsum_nn : (0 : ℝ) ≤ ∑ n ∈ s, |w n| * d n :=
    Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (hdnn n)
  have hsqnn : (0 : ℝ) ≤ ∑ n ∈ s, w n ^ 2 * d n :=
    Finset.sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (hdnn n)
  have hdnn' : (0 : ℝ) ≤ ∑ n ∈ s, d n := Finset.sum_nonneg fun n _ => hdnn n
  have hsquared : (∑ n ∈ s, |w n| * d n) ^ 2 ≤ 2 * S₂ * D := by
    refine le_trans hCS ?_
    calc (∑ n ∈ s, w n ^ 2 * d n) * ∑ n ∈ s, d n
        ≤ (2 * S₂) * ∑ n ∈ s, d n := mul_le_mul_of_nonneg_right hbound1 hdnn'
      _ ≤ (2 * S₂) * D := mul_le_mul_of_nonneg_left hbound2 (by linarith)
  nlinarith [Real.sq_sqrt hprod, Real.sqrt_nonneg (2 * S₂ * D), hsquared, hsum_nn]

/-! ## The estimate with the value in the denominator -/

/-- **The Wiman--Valiron estimate keeping the value in the denominator.**  Dividing by `‖f(z)‖`
rather than by the maximum term retains the factor that counts how many terms are comparable to the
maximum term, which is exactly what the crude form discards. -/
theorem norm_mul_logDeriv_sub_centralIndex_le_div
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    (hfz : maxTerm a r ≤ ‖coeffFun a z‖)
    (hcrit : (z * deriv (coeffFun a) z / coeffFun a z).im = 0)
    {u : ℂ} (hu : ‖u‖ = 1)
    (hWdir : ∑' n : ℕ, normalisedCoeff a r z n
      = ((‖∑' n : ℕ, normalisedCoeff a r z n‖ : ℝ) : ℂ) * u)
    {E : ℝ}
    (hE : ∑' n : ℕ, |(n : ℝ) - (centralIndex a r : ℝ)|
        * (‖normalisedCoeff a r z n‖
          - ((starRingEnd ℂ) u * normalisedCoeff a r z n).re) ≤ E) :
    ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a r : ℂ)‖
      ≤ (coeffSum a r * |meanIndex a r - (centralIndex a r : ℝ)| + E * maxTerm a r)
          / ‖coeffFun a z‖ := by
  obtain ⟨-, -, hμpos⟩ := exists_maxTerm_eq ha hr hn₀
  have hfpos : 0 < ‖coeffFun a z‖ := lt_of_lt_of_le hμpos hfz
  have hfne : coeffFun a z ≠ 0 := norm_pos_iff.mp hfpos
  have hCnorm : ‖a (centralIndex a r) * z ^ centralIndex a r‖ = maxTerm a r := by
    rw [norm_mul, norm_pow, hz]
    exact term_centralIndex_eq ha hr hn₀
  have hfac : coeffFun a z
      = (a (centralIndex a r) * z ^ centralIndex a r)
        * ∑' n : ℕ, normalisedCoeff a r z n :=
    coeffFun_eq_central_term_mul_tsum ha hr hn₀ hz
  have hWnorm : ‖∑' n : ℕ, normalisedCoeff a r z n‖ = ‖coeffFun a z‖ / maxTerm a r := by
    rw [hfac, norm_mul, hCnorm]
    field_simp
  rw [norm_mul_logDeriv_sub_centralIndex_eq ha hr hn₀ hz hfne hcrit hu hWdir, hWnorm,
    div_div_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ hfpos.le
  have hnum := abs_tsum_index_weighted_re_le ha hr hn₀ hz hu hE
  have hmul := mul_le_mul_of_nonneg_right hnum hμpos.le
  calc |∑' n : ℕ, ((n : ℝ) - (centralIndex a r : ℝ))
          * ((starRingEnd ℂ) u * normalisedCoeff a r z n).re| * maxTerm a r
      ≤ (coeffSum a r / maxTerm a r * |meanIndex a r - (centralIndex a r : ℝ)| + E)
          * maxTerm a r := hmul
    _ = coeffSum a r * |meanIndex a r - (centralIndex a r : ℝ)| + E * maxTerm a r := by
        field_simp

/-- **The Wiman--Valiron estimate in profile form.**  Combining the two sharpenings: the weighted
misalignment enters as the geometric mean of the second moment and the total misalignment, and both
terms are measured against the value rather than against the maximum term.  Writing `A` for
`‖f(z)‖ / mu(r)` and `Sigma_0` for `S(r) / mu(r)`, the bound reads
`(Sigma_0 / A) |Lambda - nu| + sqrt(2 Sigma_2 D) / A`. -/
theorem norm_mul_logDeriv_sub_centralIndex_le_profile
    (ha : EntireCoeffs a) (hr : 0 < r) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {z : ℂ} (hz : ‖z‖ = r)
    (hfz : maxTerm a r ≤ ‖coeffFun a z‖)
    (hcrit : (z * deriv (coeffFun a) z / coeffFun a z).im = 0)
    {u : ℂ} (hu : ‖u‖ = 1)
    (hWdir : ∑' n : ℕ, normalisedCoeff a r z n
      = ((‖∑' n : ℕ, normalisedCoeff a r z n‖ : ℝ) : ℂ) * u)
    {S₂ D : ℝ}
    (hS₂ : ∑' n : ℕ, ((n : ℝ) - (centralIndex a r : ℝ)) ^ 2 * ‖normalisedCoeff a r z n‖ ≤ S₂)
    (hD : ∑' n : ℕ, (‖normalisedCoeff a r z n‖
        - ((starRingEnd ℂ) u * normalisedCoeff a r z n).re) ≤ D) :
    ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a r : ℂ)‖
      ≤ (coeffSum a r * |meanIndex a r - (centralIndex a r : ℝ)|
          + Real.sqrt (2 * S₂ * D) * maxTerm a r) / ‖coeffFun a z‖ :=
  norm_mul_logDeriv_sub_centralIndex_le_div ha hr hn₀ hz hfz hcrit hu hWdir
    (tsum_index_weighted_defect_le_sqrt ha hr hn₀ hz hu hS₂ hD)

end GaloisForLFunctions.HTGeometry
