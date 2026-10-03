import GaloisForLFunctions.HTGeometry.BinaryParityDriftExactLaws

/-!
# Diophantine data cannot decide the parity drift

For `|θ| ≤ 2/5` let `ν_θ` be the product measure on base-4 digit sequences with digits in
`{0, 1, 2}` of probabilities `1/3`, `1/3 − θ/2`, `1/3 + θ/2`, and let `Φ` send a digit sequence to
the real number `Σ dₙ 4^{−(n+1)}`.

* `drift_ofDigitSeq` : the parity drift of `Φ ω` is the partial sum of `[ωₙ = 2] − [ωₙ = 1]`, so the
  strong law of large numbers gives drift `θ` for `ν_θ`-almost every `ω`.
* `measure_abs_ofDigitSeq_sub_lt_le` : a mass-distribution bound.  An interval of radius `r` with
  `r 4ᵏ ≤ 1` has `ν_θ`-mass at most `3 (8/15)ᵏ`, because it meets at most three level-`k` cylinders.
* `ae_ofDigitSeq_not_liouvilleWith` : with `(8/15)⁷ ≤ 1/64` the Borel–Cantelli sum `Σ_q 18/q²`
  converges, so `ν_θ`-almost every point has irrationality exponent at most `7`.
* `exists_drift_not_liouvilleWith_not_mem` : for every countable set `C` there is a real number
  outside `C`, with parity drift `θ` and irrationality exponent at most `7`.

The best irrationality bound proved for `π` is `7.1032…`, and `C` may contain all numbers
algebraic over any countable field (for instance `ℚ(π, e^π, Γ(1/4))`).  Every Diophantine or
algebraic-independence statement about `π` therefore holds for numbers of every parity drift with
`|θ| ≤ 2/5`: a proof or a refutation of the Parity-Drift Hypothesis must use the specific series
structure of `π`.
-/

open Filter Topology Finset MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry.BinaryParityDrift

/-! ### The digit measure -/

/-- Digit probabilities `1/3`, `1/3 − θ/2`, `1/3 + θ/2`. -/
noncomputable def digitProb (θ : ℝ) (j : Fin 3) : ℝ :=
  if (j : ℕ) = 0 then 1 / 3 else if (j : ℕ) = 1 then 1 / 3 - θ / 2 else 1 / 3 + θ / 2

theorem digitProb_nonneg {θ : ℝ} (hθ : |θ| ≤ 2 / 5) (j : Fin 3) : 0 ≤ digitProb θ j := by
  have := abs_le.mp hθ
  fin_cases j <;> simp [digitProb] <;> linarith

theorem digitProb_le {θ : ℝ} (hθ : |θ| ≤ 2 / 5) (j : Fin 3) : digitProb θ j ≤ 8 / 15 := by
  have := abs_le.mp hθ
  fin_cases j <;> simp [digitProb] <;> linarith

theorem sum_digitProb (θ : ℝ) : ∑ j, digitProb θ j = 1 := by
  simp [Fin.sum_univ_three, digitProb]
  ring

/-- The digit law as a probability mass function on `{0, 1, 2}`. -/
noncomputable def digitPMF {θ : ℝ} (hθ : |θ| ≤ 2 / 5) : PMF (Fin 3) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (digitProb θ j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => digitProb_nonneg hθ j, sum_digitProb,
      ENNReal.ofReal_one])

/-- The product measure on digit sequences. -/
noncomputable def digitMeasure {θ : ℝ} (hθ : |θ| ≤ 2 / 5) : Measure (ℕ → Fin 3) :=
  Measure.infinitePi fun _ : ℕ => (digitPMF hθ).toMeasure

instance {θ : ℝ} (hθ : |θ| ≤ 2 / 5) : IsProbabilityMeasure (digitMeasure hθ) := by
  unfold digitMeasure; infer_instance

theorem digitPMF_singleton_le {θ : ℝ} (hθ : |θ| ≤ 2 / 5) (j : Fin 3) :
    (digitPMF hθ).toMeasure {j} ≤ ENNReal.ofReal (8 / 15) := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j), digitPMF, PMF.ofFintype_apply]
  exact ENNReal.ofReal_le_ofReal (digitProb_le hθ j)

/-! ### The real number of a digit sequence -/

/-- The integer digits of a sequence in `{0, 1, 2}`. -/
def digitInt (ω : ℕ → Fin 3) (n : ℕ) : ℤ := ((ω n : ℕ) : ℤ)

theorem digitInt_nonneg (ω : ℕ → Fin 3) (n : ℕ) : 0 ≤ digitInt ω n := Int.natCast_nonneg _

theorem digitInt_le_two (ω : ℕ → Fin 3) (n : ℕ) : digitInt ω n ≤ 2 := by
  have := (ω n).isLt
  unfold digitInt
  omega

/-- `Φ ω = Σ ωₙ 4^{−(n+1)}`. -/
noncomputable def ofDigitSeq (ω : ℕ → Fin 3) : ℝ := ofQuatDigits (digitInt ω)

theorem floor_ofDigitSeq (ω : ℕ → Fin 3) (k : ℕ) :
    ⌊(4 : ℝ) ^ k * ofDigitSeq ω⌋ = digitPrefix (digitInt ω) k :=
  floor_four_pow_mul_ofQuatDigits (digitInt_nonneg ω) (digitInt_le_two ω) k

theorem ofDigitSeq_mem_Ico (ω : ℕ → Fin 3) : 0 ≤ ofDigitSeq ω ∧ ofDigitSeq ω < 1 := by
  have h := floor_ofDigitSeq ω 0
  simp only [pow_zero, one_mul, digitPrefix] at h
  exact ⟨Int.floor_eq_zero_iff.mp h |>.1, Int.floor_eq_zero_iff.mp h |>.2⟩

/-- The digit increment `[ωₙ = 2] − [ωₙ = 1]`. -/
noncomputable def driftStep (j : Fin 3) : ℝ :=
  (if (j : ℕ) = 2 then 1 else 0) - (if (j : ℕ) = 1 then 1 else 0)

theorem drift_ofDigitSeq (ω : ℕ → Fin 3) (N : ℕ) :
    (drift (ofDigitSeq ω) N : ℝ) = ∑ n ∈ range N, driftStep (ω n) := by
  unfold drift ofDigitSeq
  push_cast
  refine sum_congr rfl fun n _ => ?_
  have h := binDigit_sub_binDigit_eq (ofQuatDigits (digitInt ω)) n
  rw [quatDigit_ofQuatDigits (digitInt_nonneg ω) (digitInt_le_two ω)] at h
  rw [show (binDigit (ofQuatDigits (digitInt ω)) (2 * n + 1) : ℝ) -
      binDigit (ofQuatDigits (digitInt ω)) (2 * n + 2) =
      ((binDigit (ofQuatDigits (digitInt ω)) (2 * n + 1) -
        binDigit (ofQuatDigits (digitInt ω)) (2 * n + 2) : ℤ) : ℝ) by push_cast; ring, h]
  unfold driftStep digitInt
  generalize ω n = j
  fin_cases j <;> simp

/-! ### Almost every point has drift `θ` -/

theorem integral_driftStep {θ : ℝ} (hθ : |θ| ≤ 2 / 5) :
    ∫ j, driftStep j ∂(digitPMF hθ).toMeasure = θ := by
  rw [PMF.integral_eq_sum]
  simp only [digitPMF, PMF.ofFintype_apply, Fin.sum_univ_three, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (digitProb_nonneg hθ _), ENNReal.toReal_ofReal (digitProb_nonneg hθ _),
    ENNReal.toReal_ofReal (digitProb_nonneg hθ _)]
  simp [driftStep, digitProb]
  ring

theorem ae_tendsto_drift {θ : ℝ} (hθ : |θ| ≤ 2 / 5) :
    ∀ᵐ ω ∂digitMeasure hθ,
      Tendsto (fun N : ℕ => (drift (ofDigitSeq ω) N : ℝ) / N) atTop (𝓝 θ) := by
  set X : ℕ → (ℕ → Fin 3) → ℝ := fun n ω => driftStep (ω n) with hX
  have hmeas : Measurable driftStep := measurable_of_finite _
  have hind : iIndepFun X (digitMeasure hθ) :=
    iIndepFun_infinitePi (P := fun _ => (digitPMF hθ).toMeasure) (X := fun _ => driftStep)
      fun _ => hmeas
  have hmap : ∀ i, (digitMeasure hθ).map (X i) = (digitPMF hθ).toMeasure.map driftStep := by
    intro i
    have h := measurePreserving_eval_infinitePi (fun _ : ℕ => (digitPMF hθ).toMeasure) i
    rw [show X i = driftStep ∘ Function.eval i from rfl, ← Measure.map_map hmeas h.measurable]
    unfold digitMeasure
    rw [h.map_eq]
  have hident : ∀ i, IdentDistrib (X i) (X 0) (digitMeasure hθ) (digitMeasure hθ) := fun i =>
    { aemeasurable_fst := (hmeas.comp (measurable_pi_apply i)).aemeasurable
      aemeasurable_snd := (hmeas.comp (measurable_pi_apply 0)).aemeasurable
      map_eq := by rw [hmap, hmap] }
  have hint : Integrable (X 0) (digitMeasure hθ) := by
    refine Integrable.of_bound (hmeas.comp (measurable_pi_apply 0)).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    simp only [hX, driftStep]
    split_ifs <;> norm_num
  have hE : ∫ ω, X 0 ω ∂digitMeasure hθ = θ := by
    have hX0 : AEMeasurable (X 0) (digitMeasure hθ) :=
      (hmeas.comp (measurable_pi_apply 0)).aemeasurable
    calc ∫ ω, X 0 ω ∂digitMeasure hθ = ∫ y, y ∂(digitMeasure hθ).map (X 0) :=
          (integral_map hX0 aestronglyMeasurable_id).symm
      _ = ∫ y, y ∂(digitPMF hθ).toMeasure.map driftStep := by rw [hmap 0]
      _ = ∫ j, driftStep j ∂(digitPMF hθ).toMeasure :=
          integral_map hmeas.aemeasurable aestronglyMeasurable_id
      _ = θ := integral_driftStep hθ
  have hslln := strong_law_ae X hint (fun i j hij => hind.indepFun hij) hident
  rw [hE] at hslln
  filter_upwards [hslln] with ω hω
  refine hω.congr fun N => ?_
  rw [smul_eq_mul, inv_mul_eq_div, drift_ofDigitSeq]

/-! ### Mass distribution -/

theorem digitInt_eq_of_digitPrefix_eq {ω ω' : ℕ → Fin 3} :
    ∀ k : ℕ, digitPrefix (digitInt ω) k = digitPrefix (digitInt ω') k → ∀ i < k, ω i = ω' i := by
  intro k
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
    intro h i hi
    have h0 := digitInt_nonneg ω k
    have h2 := digitInt_le_two ω k
    have h0' := digitInt_nonneg ω' k
    have h2' := digitInt_le_two ω' k
    simp only [digitPrefix] at h
    have hk : digitPrefix (digitInt ω) k = digitPrefix (digitInt ω') k := by omega
    have hd : digitInt ω k = digitInt ω' k := by omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact ih hk i hi
    · subst hi
      unfold digitInt at hd
      exact Fin.ext (by exact_mod_cast hd)

theorem measure_digitPrefix_eq_le {θ : ℝ} (hθ : |θ| ≤ 2 / 5) (k : ℕ) (v : ℤ) :
    digitMeasure hθ {ω | digitPrefix (digitInt ω) k = v} ≤ ENNReal.ofReal (8 / 15) ^ k := by
  by_cases hne : {ω : ℕ → Fin 3 | digitPrefix (digitInt ω) k = v}.Nonempty
  · obtain ⟨ω₀, hω₀⟩ := hne
    have hsub : {ω : ℕ → Fin 3 | digitPrefix (digitInt ω) k = v} ⊆
        Set.pi (range k : Set ℕ) fun i => {ω₀ i} := by
      intro ω hω i hi
      exact (digitInt_eq_of_digitPrefix_eq k (hω.trans hω₀.symm) i (mem_range.mp hi))
    calc _ ≤ digitMeasure hθ (Set.pi (range k : Set ℕ) fun i => {ω₀ i}) := measure_mono hsub
      _ = ∏ i ∈ range k, (digitPMF hθ).toMeasure {ω₀ i} :=
          Measure.infinitePi_pi _ fun i _ => measurableSet_singleton _
      _ ≤ ∏ _i ∈ range k, ENNReal.ofReal (8 / 15) :=
          prod_le_prod' fun i _ => digitPMF_singleton_le hθ _
      _ = ENNReal.ofReal (8 / 15) ^ k := by simp
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]
    exact bot_le

/-- **Mass distribution.**  If `r 4ᵏ ≤ 1`, the radius-`r` interval around `c` has mass at most
`3 (8/15)ᵏ`. -/
theorem measure_abs_ofDigitSeq_sub_lt_le {θ : ℝ} (hθ : |θ| ≤ 2 / 5) (c r : ℝ) (k : ℕ)
    (hr : r * 4 ^ k ≤ 1) :
    digitMeasure hθ {ω | |ofDigitSeq ω - c| < r} ≤ 3 * ENNReal.ofReal (8 / 15) ^ k := by
  set L : ℝ := (4 : ℝ) ^ k * (c - r) - 1
  have hsub : {ω : ℕ → Fin 3 | |ofDigitSeq ω - c| < r} ⊆
      ⋃ j ∈ ({1, 2, 3} : Finset ℤ), {ω | digitPrefix (digitInt ω) k = ⌊L⌋ + j} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    have hfl := floor_ofDigitSeq ω k
    have h1 := Int.floor_le ((4 : ℝ) ^ k * ofDigitSeq ω)
    have h2 := Int.lt_floor_add_one ((4 : ℝ) ^ k * ofDigitSeq ω)
    rw [hfl] at h1 h2
    have h4 : (0 : ℝ) < 4 ^ k := by positivity
    obtain ⟨ha, hb⟩ := abs_lt.mp hω
    have hlow : L < digitPrefix (digitInt ω) k := by
      simp only [L]; nlinarith
    have hup : (digitPrefix (digitInt ω) k : ℝ) < L + 3 := by
      simp only [L]; nlinarith
    have hL1 := Int.floor_le L
    have hL2 := Int.lt_floor_add_one L
    have i1 : ⌊L⌋ < digitPrefix (digitInt ω) k := by
      have : (⌊L⌋ : ℝ) < digitPrefix (digitInt ω) k := by linarith
      exact_mod_cast this
    have i2 : digitPrefix (digitInt ω) k < ⌊L⌋ + 4 := by
      have : (digitPrefix (digitInt ω) k : ℝ) < ⌊L⌋ + 4 := by linarith
      exact_mod_cast this
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨digitPrefix (digitInt ω) k - ⌊L⌋, ?_, by ring⟩
    have : digitPrefix (digitInt ω) k - ⌊L⌋ = 1 ∨ digitPrefix (digitInt ω) k - ⌊L⌋ = 2 ∨
        digitPrefix (digitInt ω) k - ⌊L⌋ = 3 := by omega
    rcases this with h | h | h <;> simp [h]
  calc _ ≤ digitMeasure hθ (⋃ j ∈ ({1, 2, 3} : Finset ℤ),
        {ω | digitPrefix (digitInt ω) k = ⌊L⌋ + j}) := measure_mono hsub
    _ ≤ ∑ j ∈ ({1, 2, 3} : Finset ℤ),
        digitMeasure hθ {ω | digitPrefix (digitInt ω) k = ⌊L⌋ + j} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ ({1, 2, 3} : Finset ℤ), ENNReal.ofReal (8 / 15) ^ k :=
        sum_le_sum fun j _ => measure_digitPrefix_eq_le hθ k _
    _ = 3 * ENNReal.ofReal (8 / 15) ^ k := by simp

/-! ### Irrationality exponent at most seven -/

/-- The points within `q⁻⁷` of a fraction with denominator `q`. -/
def nearFraction (q : ℕ) : Set (ℕ → Fin 3) :=
  {ω | ∃ a : ℤ, |ofDigitSeq ω - a / q| < 1 / (q : ℝ) ^ 7}

theorem eight_fifteenths_pow_le {q k : ℕ} (hq : 1 ≤ q) (hk : q ^ 7 < 4 ^ (k + 1)) :
    (8 / 15 : ℝ) ^ k ≤ 2 / (q : ℝ) ^ 3 := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hk' : ((q : ℝ)) ^ 7 < 4 ^ (k + 1) := by exact_mod_cast hk
  have h4k : (q : ℝ) ^ 7 / 4 < 4 ^ k := by
    have e : (4 : ℝ) ^ (k + 1) = 4 ^ k * 4 := pow_succ 4 k
    rw [e] at hk'; linarith
  have hqpos : (0 : ℝ) < q := by linarith
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (7 : ℕ) ≠ 0)]
  have hbase : ((8 / 15 : ℝ) ^ k) ^ 7 ≤ ((1 / 4 : ℝ) ^ k) ^ 3 := by
    rw [← pow_mul, ← pow_mul, pow_mul', pow_mul' (1 / 4 : ℝ)]
    refine pow_le_pow_left₀ (by positivity) ?_ k
    norm_num
  have hcube : ((1 / 4 : ℝ) ^ k) ^ 3 ≤ (4 / (q : ℝ) ^ 7) ^ 3 := by
    refine pow_le_pow_left₀ (by positivity) ?_ 3
    rw [one_div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc ((8 / 15 : ℝ) ^ k) ^ 7 ≤ (4 / (q : ℝ) ^ 7) ^ 3 := hbase.trans hcube
    _ ≤ (2 / (q : ℝ) ^ 3) ^ 7 := by
        rw [div_pow, div_pow, div_le_div_iff₀ (by positivity) (by positivity), ← pow_mul,
          ← pow_mul]
        norm_num
        have : (0 : ℝ) ≤ (q : ℝ) ^ 21 := by positivity
        nlinarith

theorem measure_nearFraction_le {θ : ℝ} (hθ : |θ| ≤ 2 / 5) (q : ℕ) :
    digitMeasure hθ (nearFraction q) ≤ ENNReal.ofReal (18 / (q : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have : nearFraction 0 = ∅ := by
      ext ω
      simp only [nearFraction, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨a, ha⟩
      norm_num at ha
      exact absurd ha (not_lt.mpr (abs_nonneg _))
    rw [this, measure_empty]
    exact bot_le
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  set k := Nat.log 4 (q ^ 7) with hkdef
  have hk1 : 4 ^ k ≤ q ^ 7 := Nat.pow_log_le_self 4 (by positivity)
  have hk2 : q ^ 7 < 4 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hr : 1 / (q : ℝ) ^ 7 * 4 ^ k ≤ 1 := by
    rw [one_div, inv_mul_le_one₀ (by positivity)]
    exact_mod_cast hk1
  have hsub : nearFraction q ⊆
      ⋃ a ∈ Finset.Ioo (-(q : ℤ)) (2 * q), {ω | |ofDigitSeq ω - a / q| < 1 / (q : ℝ) ^ 7} := by
    rintro ω ⟨a, ha⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_Ioo]
    refine ⟨a, ?_, ha⟩
    obtain ⟨h0, h1⟩ := ofDigitSeq_mem_Ico ω
    have hrad : 1 / (q : ℝ) ^ 7 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ hqr
    obtain ⟨hl, hu⟩ := abs_lt.mp ha
    have hqpos : (0 : ℝ) < q := by linarith
    have ha1 : (a : ℝ) / q > -1 := by linarith
    have ha2 : (a : ℝ) / q < 2 := by linarith
    rw [gt_iff_lt, lt_div_iff₀ hqpos] at ha1
    rw [div_lt_iff₀ hqpos] at ha2
    constructor
    · have : (-(q : ℝ)) < a := by linarith
      exact_mod_cast this
    · have : (a : ℝ) < 2 * q := by linarith
      exact_mod_cast this
  have hcard : (#(Finset.Ioo (-(q : ℤ)) (2 * q)) : ENNReal) ≤ 3 * q := by
    rw [Int.card_Ioo]
    have : (2 * (q : ℤ) - -(q : ℤ) - 1).toNat ≤ 3 * q := by omega
    exact_mod_cast this
  have hpow : ENNReal.ofReal (8 / 15) ^ k ≤ ENNReal.ofReal (2 / (q : ℝ) ^ 3) := by
    rw [← ENNReal.ofReal_pow (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (eight_fifteenths_pow_le hq hk2)
  calc digitMeasure hθ (nearFraction q)
      ≤ ∑ a ∈ Finset.Ioo (-(q : ℤ)) (2 * q),
          digitMeasure hθ {ω | |ofDigitSeq ω - a / q| < 1 / (q : ℝ) ^ 7} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _a ∈ Finset.Ioo (-(q : ℤ)) (2 * q), 3 * ENNReal.ofReal (2 / (q : ℝ) ^ 3) :=
        sum_le_sum fun a _ => (measure_abs_ofDigitSeq_sub_lt_le hθ _ _ k hr).trans
          (by gcongr)
    _ = #(Finset.Ioo (-(q : ℤ)) (2 * q)) * (3 * ENNReal.ofReal (2 / (q : ℝ) ^ 3)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (3 * q) * (3 * ENNReal.ofReal (2 / (q : ℝ) ^ 3)) := by gcongr
    _ = ENNReal.ofReal (18 / (q : ℝ) ^ 2) := by
        have hqpos : (0 : ℝ) < q := by linarith
        rw [show (3 : ENNReal) * q = ENNReal.ofReal (3 * q) by
              rw [ENNReal.ofReal_mul (by norm_num)]; simp,
          show (3 : ENNReal) = ENNReal.ofReal 3 by simp,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

theorem tsum_measure_nearFraction_ne_top {θ : ℝ} (hθ : |θ| ≤ 2 / 5) :
    ∑' q, digitMeasure hθ (nearFraction q) ≠ ⊤ := by
  have hs : Summable fun q : ℕ => 18 / (q : ℝ) ^ 2 := by
    exact ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 18).congr fun q => by ring
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun q => measure_nearFraction_le hθ q)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => by positivity) hs]
  exact ENNReal.ofReal_ne_top

/-- **Irrationality exponent at most `7`** for `ν_θ`-almost every point. -/
theorem ae_ofDigitSeq_not_liouvilleWith {θ : ℝ} (hθ : |θ| ≤ 2 / 5) :
    ∀ᵐ ω ∂digitMeasure hθ, ∀ p > (7 : ℝ), ¬ LiouvilleWith p (ofDigitSeq ω) := by
  filter_upwards [ae_eventually_notMem (tsum_measure_nearFraction_ne_top hθ)] with ω hω p hp hL
  have hfreq := hL.frequently_lt_rpow_neg hp
  obtain ⟨n, hn, m, -, hm⟩ := (hω.and_frequently hfreq).exists
  apply hn
  refine ⟨m, ?_⟩
  have : (n : ℝ) ^ (-(7 : ℝ)) = 1 / (n : ℝ) ^ 7 := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), one_div, show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
  rwa [this] at hm

/-! ### No atoms -/

theorem measure_ofDigitSeq_eq {θ : ℝ} (hθ : |θ| ≤ 2 / 5) (y : ℝ) :
    digitMeasure hθ {ω | ofDigitSeq ω = y} = 0 := by
  have hbound : ∀ k : ℕ, digitMeasure hθ {ω | ofDigitSeq ω = y} ≤
      3 * ENNReal.ofReal (8 / 15) ^ k := by
    intro k
    refine (measure_mono fun ω hω => ?_).trans
      (measure_abs_ofDigitSeq_sub_lt_le hθ y (1 / 4 ^ k) k (by field_simp; rfl))
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hω, sub_self, abs_zero]
    positivity
  have hlim : Tendsto (fun k : ℕ => 3 * ENNReal.ofReal (8 / 15) ^ k) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := ENNReal.ofReal (8 / 15))
        (by rw [ENNReal.ofReal_lt_one]; norm_num)) (Or.inr (by norm_num : (3 : ENNReal) ≠ ⊤))
    simpa using h
  exact le_antisymm (ge_of_tendsto' hlim hbound) bot_le

theorem ae_ofDigitSeq_not_mem {θ : ℝ} (hθ : |θ| ≤ 2 / 5) {C : Set ℝ} (hC : C.Countable) :
    ∀ᵐ ω ∂digitMeasure hθ, ofDigitSeq ω ∉ C := by
  rw [ae_iff]
  simp only [not_not]
  have : {ω | ofDigitSeq ω ∈ C} = ⋃ y ∈ C, {ω | ofDigitSeq ω = y} := by
    ext ω; simp
  rw [this]
  exact (measure_biUnion_null_iff hC).mpr fun y _ => measure_ofDigitSeq_eq hθ y

/-! ### The barrier -/

/-- **Diophantine barrier for the parity drift.**  For `|θ| ≤ 2/5` and every countable set `C` of
reals there is `x ∉ C` with parity drift `D_x(N)/N → θ` and irrationality exponent at most `7`. -/
theorem exists_drift_not_liouvilleWith_not_mem {θ : ℝ} (hθ : |θ| ≤ 2 / 5) {C : Set ℝ}
    (hC : C.Countable) :
    ∃ x : ℝ, x ∉ C ∧ Tendsto (fun N : ℕ => (drift x N : ℝ) / N) atTop (𝓝 θ) ∧
      ∀ p > (7 : ℝ), ¬ LiouvilleWith p x := by
  have hne : (ae (digitMeasure hθ)).NeBot := ae_neBot.mpr (IsProbabilityMeasure.ne_zero _)
  obtain ⟨ω, h1, h2, h3⟩ := ((ae_ofDigitSeq_not_mem hθ hC).and
    ((ae_tendsto_drift hθ).and (ae_ofDigitSeq_not_liouvilleWith hθ))).exists
  exact ⟨ofDigitSeq ω, h1, h2, h3⟩

/-- In particular the drift `θ` is carried by a transcendental number of irrationality exponent at
most `7`. -/
theorem exists_transcendental_drift_not_liouvilleWith {θ : ℝ} (hθ : |θ| ≤ 2 / 5) :
    ∃ x : ℝ, Transcendental ℚ x ∧ Tendsto (fun N : ℕ => (drift x N : ℝ) / N) atTop (𝓝 θ) ∧
      ∀ p > (7 : ℝ), ¬ LiouvilleWith p x := by
  obtain ⟨x, hx, h2, h3⟩ := exists_drift_not_liouvilleWith_not_mem hθ (Algebraic.countable ℚ ℝ)
  exact ⟨x, hx, h2, h3⟩

end GaloisForLFunctions.HTGeometry.BinaryParityDrift
