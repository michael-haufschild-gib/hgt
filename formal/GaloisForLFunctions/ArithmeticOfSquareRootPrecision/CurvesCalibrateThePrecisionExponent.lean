import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.UpperLefschetzBoundsAreBlindOnlyToRealZeros
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheWeilFloorOfACurveIsItsZeroWidth
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheHyperellipticCalibration

/-!
# Curves calibrate the precision exponent

For a curve datum (`q`, normalized Frobenius eigenvalues `β_i`, conjugation, functional equation
`β_{σ(i)} β_i = 1`) the point count is `N_k = q^k + 1 − q^{k/2} Σ_i β_i^k`. Precision over `𝔽_q`
is the size of `N_k − q^k − 1`.

* **The precision law** (`countAtPrecision_iff`, `lowerCountAtPrecision_iff`). The count at
  precision `θ`, `|N_k − q^k − 1| ≤ C q^{kθ}` for all `k`, holds iff every `‖β_i‖ ≤ q^{θ − ½}`, and
  already its lower half `N_k ≥ q^k + 1 − C q^{kθ}` forces this (an upper one-sided power-sum bound
  bounds every modulus).
* **The precision exponent** (`precisionExponent_eq`):
  `inf {θ : count at precision θ} = ½ + max_i log ‖β_i‖ / log q`. It is at least `½` because the
  functional equation pairs `β` with `β⁻¹`-type partners (`half_le_precisionExponent`), with
  equality iff the datum is unitary (`precisionExponent_eq_half_iff`).
* **Stepanov reaches square-root precision** (`hyperelliptic_precisionExponent`): the odd
  hyperelliptic data, unitary by counting, have exponent exactly `½`.
* **The golden datum is the relative-error twin** (`golden_tendsto_pointCount_div`,
  `golden_countAtPrecision_iff`): `N_k / 5^k → 1`, yet the count at precision `θ` holds iff
  `θ ≥ ½ + log φ / log 5`. Relative-error point counts cannot see the sign over `𝔽_q` either.
* **The upper half is blind to real outer eigenvalues** (`unitary_of_upperCountAtPrecision_half`,
  `golden_upperCount_and_not_lowerCount`): without a real outer eigenvalue an upper square-root
  count forces unitarity, while the golden datum satisfies `N_k ≤ q^k + 1` and fails the lower half.
  Over `ℤ` each half is RH, because `ζ` has no real zero in `(½, 1)`.
-/

noncomputable section

open Real Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

open ArithmeticCastelnuovoSeveri

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The count at precision `θ`: `|N_k − q^k − 1| ≤ C (q^θ)^k` for all `k`. -/
def CountAtPrecision (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ k : ℕ, |D.pointCount k - D.q ^ k - 1| ≤ C * (D.q ^ θ) ^ k

/-- The lower half of the count at precision `θ`. -/
def LowerCountAtPrecision (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ k : ℕ, D.q ^ k + 1 - C * (D.q ^ θ) ^ k ≤ D.pointCount k

theorem curve_q_pos : 0 < D.q := by linarith [D.one_lt_q]

/-- `q^θ = √q · q^{θ − ½}`. -/
theorem rpow_eq_sqrtq_mul (θ : ℝ) : D.q ^ θ = D.sqrtq * D.q ^ (θ - 1 / 2) := by
  rw [CurveDatum.sqrtq, Real.sqrt_eq_rpow, ← Real.rpow_add (curve_q_pos D)]; ring_nf

/-- **The precision law.** Every modulus `≤ q^{θ − ½}` gives the count at precision `θ`. -/
theorem countAtPrecision_of_norm_le {θ : ℝ} (h : ∀ i, ‖D.β i‖ ≤ D.q ^ (θ - 1 / 2)) :
    CountAtPrecision D θ := by
  refine ⟨Fintype.card ι, fun k => ?_⟩
  have hs : 0 ≤ D.sqrtq ^ k := pow_nonneg D.sqrtq_pos.le k
  have ht := D.abs_trace_le h k
  rw [show D.pointCount k - D.q ^ k - 1 = -(D.sqrtq ^ k * D.trace k) by unfold CurveDatum.pointCount; ring,
    abs_neg, abs_mul, abs_of_nonneg hs, rpow_eq_sqrtq_mul D, mul_pow]
  calc D.sqrtq ^ k * |D.trace k| ≤ D.sqrtq ^ k * (Fintype.card ι * (D.q ^ (θ - 1 / 2)) ^ k) :=
        mul_le_mul_of_nonneg_left ht hs
    _ = Fintype.card ι * (D.sqrtq ^ k * (D.q ^ (θ - 1 / 2)) ^ k) := by ring

/-- The lower half at precision `θ` bounds every modulus by `q^{θ − ½}`. -/
theorem norm_le_of_lowerCountAtPrecision {θ : ℝ} (h : LowerCountAtPrecision D θ) :
    ∀ i, ‖D.β i‖ ≤ D.q ^ (θ - 1 / 2) := by
  obtain ⟨C, hC⟩ := h
  refine norm_le_of_re_sum_pow_le D.β (Real.rpow_pos_of_pos (curve_q_pos D) _) (C := C) fun k => ?_
  have hs : 0 < D.sqrtq ^ k := pow_pos D.sqrtq_pos k
  have hk := hC k
  rw [rpow_eq_sqrtq_mul D, mul_pow] at hk
  unfold CurveDatum.pointCount at hk
  rw [← CurveDatum.powerSum, D.powerSum_eq_trace, Complex.ofReal_re]
  have : D.sqrtq ^ k * D.trace k ≤ D.sqrtq ^ k * (C * (D.q ^ (θ - 1 / 2)) ^ k) := by nlinarith
  exact le_of_mul_le_mul_left this hs

theorem countAtPrecision_imp_lower {θ : ℝ} (h : CountAtPrecision D θ) :
    LowerCountAtPrecision D θ := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun k => by linarith [(abs_le.mp (hC k)).1]⟩

/-- **The precision law**: count at precision `θ` ⟺ every `‖β_i‖ ≤ q^{θ − ½}`. -/
theorem countAtPrecision_iff (θ : ℝ) :
    CountAtPrecision D θ ↔ ∀ i, ‖D.β i‖ ≤ D.q ^ (θ - 1 / 2) :=
  ⟨fun h => (norm_le_of_lowerCountAtPrecision D) ((countAtPrecision_imp_lower D) h),
    (countAtPrecision_of_norm_le D)⟩

/-- **One half suffices**: the lower count at precision `θ` ⟺ every `‖β_i‖ ≤ q^{θ − ½}`. -/
theorem lowerCountAtPrecision_iff (θ : ℝ) :
    LowerCountAtPrecision D θ ↔ ∀ i, ‖D.β i‖ ≤ D.q ^ (θ - 1 / 2) :=
  ⟨(norm_le_of_lowerCountAtPrecision D),
    fun h => (countAtPrecision_imp_lower D) ((countAtPrecision_of_norm_le D) h)⟩

theorem curve_β_ne_zero (i : ι) : D.β i ≠ 0 := right_ne_zero_of_mul_eq_one (D.β_fePerm i)

/-- The modulus condition in logarithmic form. -/
theorem norm_le_rpow_iff_log {θ : ℝ} (i : ι) :
    ‖D.β i‖ ≤ D.q ^ (θ - 1 / 2) ↔ 1 / 2 + Real.log ‖D.β i‖ / Real.log D.q ≤ θ := by
  have hq : 0 < Real.log D.q := Real.log_pos D.one_lt_q
  rw [← Real.log_le_log_iff (norm_pos_iff.mpr (curve_β_ne_zero D i)) (Real.rpow_pos_of_pos (curve_q_pos D) _),
    Real.log_rpow (curve_q_pos D), ← le_sub_iff_add_le', div_le_iff₀ hq]

/-- **The precision exponent of a curve datum**:
`inf {θ : count at precision θ} = ½ + max_i log ‖β_i‖ / log q`. -/
theorem precisionExponent_eq [Nonempty ι] :
    sInf {θ : ℝ | CountAtPrecision D θ} =
      1 / 2 + (univ.sup' univ_nonempty fun i => Real.log ‖D.β i‖) / Real.log D.q := by
  have hq : 0 < Real.log D.q := Real.log_pos D.one_lt_q
  have hset : {θ : ℝ | CountAtPrecision D θ} = Set.Ici
      (1 / 2 + (univ.sup' univ_nonempty fun i => Real.log ‖D.β i‖) / Real.log D.q) := by
    ext θ
    simp only [Set.mem_setOf_eq, Set.mem_Ici, countAtPrecision_iff, norm_le_rpow_iff_log]
    rw [← le_sub_iff_add_le', div_le_iff₀ hq, Finset.sup'_le_iff]
    refine forall_congr' fun i => ?_
    simp only [mem_univ, true_implies]
    rw [← le_sub_iff_add_le', div_le_iff₀ hq]
  rw [hset, csInf_Ici]

/-- **The exponent is at least `½`**: the functional equation pairs each `β_i` with a partner of
reciprocal modulus. -/
theorem half_le_precisionExponent [Nonempty ι] :
    1 / 2 ≤ sInf {θ : ℝ | CountAtPrecision D θ} := by
  rw [(precisionExponent_eq D)]
  have hq : 0 < Real.log D.q := Real.log_pos D.one_lt_q
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hprod : ‖D.β (D.fePerm i)‖ * ‖D.β i‖ = 1 := by rw [← norm_mul, D.β_fePerm i, norm_one]
  have hlog : Real.log ‖D.β (D.fePerm i)‖ + Real.log ‖D.β i‖ = 0 := by
    rw [← Real.log_mul (norm_ne_zero_iff.mpr (curve_β_ne_zero D _)) (norm_ne_zero_iff.mpr
      (curve_β_ne_zero D i)), hprod, Real.log_one]
  have h1 : Real.log ‖D.β i‖ ≤ univ.sup' univ_nonempty fun i => Real.log ‖D.β i‖ :=
    Finset.le_sup' (fun i => Real.log ‖D.β i‖) (mem_univ i)
  have h2 : Real.log ‖D.β (D.fePerm i)‖ ≤ univ.sup' univ_nonempty fun i => Real.log ‖D.β i‖ :=
    Finset.le_sup' (fun i => Real.log ‖D.β i‖) (mem_univ (D.fePerm i))
  have hmax : 0 ≤ univ.sup' univ_nonempty fun i => Real.log ‖D.β i‖ := by linarith
  have := div_nonneg hmax hq.le
  linarith

/-- **Square-root precision is unitarity.** -/
theorem countAtPrecision_half_iff : CountAtPrecision D (1 / 2) ↔ ∀ i, ‖D.β i‖ = 1 := by
  rw [countAtPrecision_iff, sub_self, Real.rpow_zero]
  refine ⟨fun h i => le_antisymm (h i) ?_, fun h i => (h i).le⟩
  have hprod : ‖D.β (D.fePerm i)‖ * ‖D.β i‖ = 1 := by rw [← norm_mul, D.β_fePerm i, norm_one]
  have h0 : 0 < ‖D.β i‖ := norm_pos_iff.mpr (curve_β_ne_zero D i)
  nlinarith [h (D.fePerm i)]

/-- The exponent is `½` iff the datum is unitary. -/
theorem precisionExponent_eq_half_iff [Nonempty ι] :
    sInf {θ : ℝ | CountAtPrecision D θ} = 1 / 2 ↔ ∀ i, ‖D.β i‖ = 1 := by
  rw [← countAtPrecision_half_iff]
  have hq : 0 < Real.log D.q := Real.log_pos D.one_lt_q
  constructor
  · intro h
    have hle : (univ.sup' univ_nonempty fun i => Real.log ‖D.β i‖) ≤ 0 := by
      rw [(precisionExponent_eq D)] at h
      have : (univ.sup' univ_nonempty fun i => Real.log ‖D.β i‖) / Real.log D.q = 0 := by linarith
      rw [div_eq_zero_iff] at this
      rcases this with h0 | h0
      · exact h0.le
      · exact absurd h0 hq.ne'
    rw [countAtPrecision_iff]
    intro i
    rw [norm_le_rpow_iff_log]
    have := (Finset.sup'_le_iff _ _).mp hle i (mem_univ i)
    have := div_nonpos_of_nonpos_of_nonneg this hq.le
    linarith
  · intro h
    refine le_antisymm ?_ (half_le_precisionExponent D)
    exact csInf_le ⟨1 / 2, fun θ hθ => by
      have := (half_le_precisionExponent D)
      rw [(precisionExponent_eq D)] at this
      rw [Set.mem_setOf_eq, countAtPrecision_iff] at hθ
      have hle : (univ.sup' univ_nonempty fun i => Real.log ‖D.β i‖) / Real.log D.q ≤ θ - 1 / 2 := by
        rw [div_le_iff₀ hq, Finset.sup'_le_iff]
        intro i _
        have := ((norm_le_rpow_iff_log D) i).mp (hθ i)
        rw [← le_sub_iff_add_le', div_le_iff₀ hq] at this
        exact this
      linarith⟩ h

/-! ### Calibration: Stepanov and the golden datum -/

/-- **Stepanov reaches square-root precision**: odd hyperelliptic data count at precision `½`. -/
theorem hyperelliptic_countAtPrecision_half {F : Type*} [Field F] [Fintype F]
    (hF : ringChar F ≠ 2) {f : Polynomial F} (hsq : Squarefree f) (hodd : Odd f.natDegree) :
    CountAtPrecision (ArithmeticEffectivityTheory.hyperellipticDatum hF hsq hodd) (1 / 2) :=
  (countAtPrecision_half_iff _).mpr (ArithmeticEffectivityTheory.hyperellipticDatum_unitary hF hsq hodd)

/-- `‖β‖` of the golden datum is `φ` or `φ⁻¹`. -/
theorem golden_norm_le_iff {θ : ℝ} :
    (∀ i, ‖goldenDatum.β i‖ ≤ goldenDatum.q ^ (θ - 1 / 2)) ↔ goldenRatio ≤ (5 : ℝ) ^ (θ - 1 / 2) := by
  have hq : goldenDatum.q = 5 := rfl
  have h0 : ‖goldenDatum.β 0‖ = goldenRatio := by
    show ‖((goldenRatio : ℝ) : ℂ)‖ = goldenRatio
    rw [Complex.norm_real, Real.norm_of_nonneg goldenRatio_pos.le]
  have h1 : ‖goldenDatum.β 1‖ = goldenRatio⁻¹ := by
    show ‖((goldenRatio⁻¹ : ℝ) : ℂ)‖ = goldenRatio⁻¹
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr goldenRatio_pos).le]
  rw [hq, Fin.forall_fin_two, h0, h1]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  exact (inv_le_one_of_one_le₀ one_lt_goldenRatio.le).trans (one_lt_goldenRatio.le.trans h)

/-- **The golden datum counts at precision `θ` iff `θ ≥ ½ + log φ / log 5`.** -/
theorem golden_countAtPrecision_iff (θ : ℝ) :
    CountAtPrecision goldenDatum θ ↔ 1 / 2 + Real.log goldenRatio / Real.log 5 ≤ θ := by
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  rw [countAtPrecision_iff, golden_norm_le_iff, ← Real.log_le_log_iff goldenRatio_pos
    (Real.rpow_pos_of_pos (by norm_num) _), Real.log_rpow (by norm_num), ← le_sub_iff_add_le',
    div_le_iff₀ h5]

/-- **The golden datum passes every relative-error count**: `N_k / 5^k → 1`. -/
theorem golden_tendsto_pointCount_div :
    Tendsto (fun k : ℕ => goldenDatum.pointCount k / goldenDatum.q ^ k) atTop (𝓝 1) := by
  have hq : goldenDatum.q = 5 := rfl
  have hs : goldenDatum.sqrtq = √5 := rfl
  -- `N_k / 5^k = 1 + 5^{−k} − (√5 φ / 5)^k − (√5 φ⁻¹ / 5)^k`
  have hform : ∀ k : ℕ, goldenDatum.pointCount k / goldenDatum.q ^ k =
      1 + (1 / 5) ^ k - (√5 * goldenRatio / 5) ^ k - (√5 * goldenRatio⁻¹ / 5) ^ k := by
    intro k
    rw [CurveDatum.pointCount, goldenDatum_trace, hq, hs]
    generalize goldenRatio = φ
    generalize √5 = r
    simp only [div_pow, mul_pow, one_pow]
    field_simp
    ring
  have hr1 : √5 * goldenRatio / 5 < 1 := by
    rw [div_lt_one (by norm_num)]
    have h5 : √5 < 2.24 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hφ : goldenRatio < 1.62 := by
      rw [goldenRatio]; linarith
    nlinarith [Real.sqrt_nonneg 5, goldenRatio_pos]
  have hr2 : √5 * goldenRatio⁻¹ / 5 < 1 := by
    refine lt_of_le_of_lt ?_ hr1
    gcongr
    exact (inv_le_one_of_one_le₀ one_lt_goldenRatio.le).trans one_lt_goldenRatio.le
  have t1 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 5) (by norm_num)
  have t2 := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hr1
  have t3 := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by have := goldenRatio_pos; positivity) hr2
  have := ((tendsto_const_nhds (x := (1 : ℝ))).add t1).sub t2 |>.sub t3
  simp only [add_zero, sub_zero] at this
  exact this.congr fun k => (hform k).symm

/-- The golden exponent exceeds `½`: the golden datum fails the square-root count. -/
theorem golden_not_countAtPrecision_half : ¬ CountAtPrecision goldenDatum (1 / 2) := by
  rw [golden_countAtPrecision_iff]
  have : 0 < Real.log goldenRatio / Real.log 5 :=
    div_pos (Real.log_pos one_lt_goldenRatio) (Real.log_pos (by norm_num))
  linarith


/-! ### The upper half over `𝔽_q` is blind to real outer eigenvalues -/

/-- The upper half of the count at precision `θ`: `N_k ≤ q^k + 1 + C (q^θ)^k` for all `k`. -/
def UpperCountAtPrecision (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ k : ℕ, D.pointCount k ≤ D.q ^ k + 1 + C * (D.q ^ θ) ^ k

/-- **Without a real outer eigenvalue the upper half is square-root precision**: an upper square-root
count forces unitarity. -/
theorem unitary_of_upperCountAtPrecision_half (hreal : ¬ D.HasRealOuterEigenvalue)
    (h : UpperCountAtPrecision D (1 / 2)) : ∀ i, ‖D.β i‖ = 1 := by
  obtain ⟨C, hC⟩ := h
  refine D.unitary_of_neg_le_trace (C := C) (fun k => ?_) hreal
  have hk := hC k
  rw [show D.q ^ (1 / 2 : ℝ) = D.sqrtq by rw [CurveDatum.sqrtq, Real.sqrt_eq_rpow]] at hk
  exact (D.neg_le_trace_iff_pointCount_le k C).mpr hk

/-- **The golden datum passes the upper half at every precision** (`N_k ≤ q^k + 1`), and fails the
lower half below `½ + log φ / log 5`: over `𝔽_q` the upper half is blind to the real outer eigenvalue
`φ`. Over `ℤ` each half is RH (`upperCount_vonMangoldt_iff`, `lowerCount_vonMangoldt_iff`). -/
theorem golden_upperCount_and_not_lowerCount (θ : ℝ) :
    UpperCountAtPrecision goldenDatum θ ∧
      (LowerCountAtPrecision goldenDatum θ ↔ 1 / 2 + Real.log goldenRatio / Real.log 5 ≤ θ) := by
  refine ⟨⟨0, fun k => ?_⟩, ?_⟩
  · have ht := goldenDatum_trace_nonneg k
    have hs : 0 ≤ goldenDatum.sqrtq ^ k := pow_nonneg goldenDatum.sqrtq_pos.le k
    unfold CurveDatum.pointCount
    nlinarith
  · rw [lowerCountAtPrecision_iff, ← countAtPrecision_iff, golden_countAtPrecision_iff]

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
