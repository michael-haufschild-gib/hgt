import GaloisForLFunctions.HTGeometry.ComplexSumConcentration

/-!
# Independent selection from weighted groups

Let `G₀, …, G_{n−1}` be finite sets of positive integers carrying weights `w ≥ 0` with
`Σ_{p ∈ G_i} w(p) ≤ 1`.  Choose independently in each group either one element `p ∈ G_i`, with
probability `w(p)`, or nothing (recorded as `0`), with the remaining probability.  For a test
`φ` with `|φ| ≤ 1` the deviation of group `i`,

`Y_i = Σ_{p ∈ G_i} (1[choice = p] − w(p)) φ(p)`,

is centred and bounded by `2`, and the groups are independent, so the complex Hoeffding bound
gives `P(|Σ_i Y_i| ≥ θ) ≤ 4 exp(−θ²/(16n))`.

**Theorem** (`exists_selection`).  For a countable family of tests `φ_e` and thresholds `θ_e` with
`Σ_e 4 exp(−θ_e²/(16n)) < 1` (summed in `ℝ≥0∞`) there is one choice `ω` (each `ω_i` is `0` or an element of `G_i`)
with `|Σ_i Y_i(ω)| < θ_e` for every `e` simultaneously.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.GroupedSelection

variable {n : ℕ} (G : Fin n → Finset ℕ) (w : ℕ → ℝ)

/-- The deviation of group `i` from its mean when the choice is `q`. -/
def groupDev (φ : ℕ → ℂ) (i : Fin n) (q : ℕ) : ℂ :=
  ∑ p ∈ G i, ((if q = p then (1 : ℂ) else 0) - (w p : ℂ)) * φ p

/-- The selection weights of group `i` as an `ℝ≥0∞`-valued function. -/
def selWeight (i : Fin n) (q : ℕ) : ℝ≥0∞ :=
  if q = 0 then ENNReal.ofReal (1 - ∑ p ∈ G i, w p)
  else if q ∈ G i then ENNReal.ofReal (w q) else 0

variable {G w}

theorem sum_selWeight (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ i, ∑ p ∈ G i, w p ≤ 1) (h0 : ∀ i, 0 ∉ G i)
    (i : Fin n) : ∑ q ∈ insert 0 (G i), selWeight G w i q = 1 := by
  rw [Finset.sum_insert (h0 i), selWeight, if_pos rfl]
  have hrest : ∑ q ∈ G i, selWeight G w i q = ∑ q ∈ G i, ENNReal.ofReal (w q) :=
    Finset.sum_congr rfl fun q hq => by
      have hq0 : q ≠ 0 := fun h => h0 i (h ▸ hq)
      rw [selWeight, if_neg hq0, if_pos hq]
  rw [hrest, ← ENNReal.ofReal_sum_of_nonneg fun q _ => hw0 q,
    ← ENNReal.ofReal_add (by linarith [hw1 i]) (Finset.sum_nonneg fun q _ => hw0 q)]
  simp

theorem selWeight_eq_zero {i : Fin n} {q : ℕ} (hq : q ∉ insert 0 (G i)) :
    selWeight G w i q = 0 := by
  rw [Finset.mem_insert, not_or] at hq
  rw [selWeight, if_neg hq.1, if_neg hq.2]

/-- The selection law of group `i`. -/
def groupPMF (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ i, ∑ p ∈ G i, w p ≤ 1) (h0 : ∀ i, 0 ∉ G i)
    (i : Fin n) : PMF ℕ :=
  PMF.ofFinset (selWeight G w i) (insert 0 (G i)) (sum_selWeight hw0 hw1 h0 i)
    fun _ hq => selWeight_eq_zero hq

theorem norm_groupDev_le (φ : ℕ → ℂ) (hφ : ∀ p, ‖φ p‖ ≤ 1) (hw0 : ∀ p, 0 ≤ w p)
    (hw1 : ∀ i, ∑ p ∈ G i, w p ≤ 1) (i : Fin n) (q : ℕ) : ‖groupDev G w φ i q‖ ≤ 2 := by
  classical
  unfold groupDev
  have hsplit : ∑ p ∈ G i, ((if q = p then (1 : ℂ) else 0) - (w p : ℂ)) * φ p =
      (∑ p ∈ G i, (if q = p then (1 : ℂ) else 0) * φ p) - ∑ p ∈ G i, (w p : ℂ) * φ p := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsplit]
  have h1 : ‖∑ p ∈ G i, (if q = p then (1 : ℂ) else 0) * φ p‖ ≤ 1 := by
    have : ∑ p ∈ G i, (if q = p then (1 : ℂ) else 0) * φ p =
        if q ∈ G i then φ q else 0 := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq]
    rw [this]
    split_ifs
    · exact hφ q
    · simp
  have h2 : ‖∑ p ∈ G i, (w p : ℂ) * φ p‖ ≤ 1 := by
    calc ‖∑ p ∈ G i, (w p : ℂ) * φ p‖ ≤ ∑ p ∈ G i, ‖(w p : ℂ) * φ p‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ G i, w p := Finset.sum_le_sum fun p _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 p)]
          exact mul_le_of_le_one_right (hw0 p) (hφ p)
      _ ≤ 1 := hw1 i
  calc _ ≤ ‖∑ p ∈ G i, (if q = p then (1 : ℂ) else 0) * φ p‖ + ‖∑ p ∈ G i, (w p : ℂ) * φ p‖ :=
        norm_sub_le _ _
    _ ≤ 2 := by linarith

/-- The deviation is linear in the test. -/
theorem groupDev_sub (φ φ' : ℕ → ℂ) (i : Fin n) (q : ℕ) :
    groupDev G w φ i q - groupDev G w φ' i q = groupDev G w (fun p => φ p - φ' p) i q := by
  unfold groupDev
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- The deviation only sees the test on the group. -/
theorem groupDev_congr {φ φ' : ℕ → ℂ} {i : Fin n} (h : ∀ p ∈ G i, φ p = φ' p) (q : ℕ) :
    groupDev G w φ i q = groupDev G w φ' i q := by
  unfold groupDev
  exact Finset.sum_congr rfl fun p hp => by rw [h p hp]

/-- A test bounded by `D` on the group gives a deviation bounded by `2D`. -/
theorem norm_groupDev_le_of_le (ψ : ℕ → ℂ) {D : ℝ} {i : Fin n} (hψ : ∀ p ∈ G i, ‖ψ p‖ ≤ D)
    (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ i, ∑ p ∈ G i, w p ≤ 1) (hD : 0 ≤ D) (q : ℕ) :
    ‖groupDev G w ψ i q‖ ≤ 2 * D := by
  classical
  unfold groupDev
  have hsplit : ∑ p ∈ G i, ((if q = p then (1 : ℂ) else 0) - (w p : ℂ)) * ψ p =
      (∑ p ∈ G i, (if q = p then (1 : ℂ) else 0) * ψ p) - ∑ p ∈ G i, (w p : ℂ) * ψ p := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsplit]
  have h1 : ‖∑ p ∈ G i, (if q = p then (1 : ℂ) else 0) * ψ p‖ ≤ D := by
    have : ∑ p ∈ G i, (if q = p then (1 : ℂ) else 0) * ψ p = if q ∈ G i then ψ q else 0 := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq]
    rw [this]
    split_ifs with hq
    · exact hψ q hq
    · simpa using hD
  have h2 : ‖∑ p ∈ G i, (w p : ℂ) * ψ p‖ ≤ D := by
    calc ‖∑ p ∈ G i, (w p : ℂ) * ψ p‖ ≤ ∑ p ∈ G i, ‖(w p : ℂ) * ψ p‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ G i, w p * D := Finset.sum_le_sum fun p hp => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 p)]
          exact mul_le_mul_of_nonneg_left (hψ p hp) (hw0 p)
      _ = (∑ p ∈ G i, w p) * D := by rw [Finset.sum_mul]
      _ ≤ 1 * D := mul_le_mul_of_nonneg_right (hw1 i) hD
      _ = D := one_mul D
  calc _ ≤ ‖∑ p ∈ G i, (if q = p then (1 : ℂ) else 0) * ψ p‖ + ‖∑ p ∈ G i, (w p : ℂ) * ψ p‖ :=
        norm_sub_le _ _
    _ ≤ 2 * D := by linarith

/-- **Each group deviation is centred** under its selection law. -/
theorem integral_groupDev (φ : ℕ → ℂ) (hφ : ∀ p, ‖φ p‖ ≤ 1) (hw0 : ∀ p, 0 ≤ w p)
    (hw1 : ∀ i, ∑ p ∈ G i, w p ≤ 1) (h0 : ∀ i, 0 ∉ G i) (i : Fin n) :
    ∫ q, groupDev G w φ i q ∂(groupPMF hw0 hw1 h0 i).toMeasure = 0 := by
  classical
  have hint : Integrable (groupDev G w φ i) (groupPMF hw0 hw1 h0 i).toMeasure :=
    Integrable.of_bound (measurable_from_nat (f := groupDev G w φ i)).aestronglyMeasurable 2
      (Filter.Eventually.of_forall fun q => norm_groupDev_le φ hφ hw0 hw1 i q)
  rw [PMF.integral_eq_tsum _ _ hint, tsum_eq_sum (s := insert 0 (G i)) fun q hq => by
    rw [groupPMF, PMF.ofFinset_apply, selWeight_eq_zero hq]; simp]
  have hP : ∀ q, ((groupPMF hw0 hw1 h0 i) q).toReal =
      if q = 0 then 1 - ∑ p ∈ G i, w p else if q ∈ G i then w q else 0 := by
    intro q
    rw [groupPMF, PMF.ofFinset_apply, selWeight]
    split_ifs with h1 h2
    · exact ENNReal.toReal_ofReal (by linarith [hw1 i])
    · exact ENNReal.toReal_ofReal (hw0 q)
    · simp
  simp only [hP, groupDev, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp0 : p ≠ 0 := fun h => h0 i (h ▸ hp)
  rw [Finset.sum_insert (h0 i)]
  simp only [if_neg (Ne.symm hp0)]
  have hsum : ∑ q ∈ G i, (if q = 0 then 1 - ∑ p ∈ G i, w p else if q ∈ G i then w q else 0) •
      (((if q = p then (1 : ℂ) else 0) - (w p : ℂ)) * φ p) =
      ∑ q ∈ G i, w q • (((if q = p then (1 : ℂ) else 0) - (w p : ℂ)) * φ p) :=
    Finset.sum_congr rfl fun q hq => by
      have hq0 : q ≠ 0 := fun h => h0 i (h ▸ hq)
      rw [if_neg hq0, if_pos hq]
  rw [hsum]
  have hsplit : ∑ q ∈ G i, w q • (((if q = p then (1 : ℂ) else 0) - (w p : ℂ)) * φ p) =
      (w p : ℂ) * φ p - (∑ q ∈ G i, (w q : ℂ)) * (w p : ℂ) * φ p := by
    simp only [Complex.real_smul, sub_mul, mul_sub, Finset.sum_sub_distrib, ite_mul, one_mul,
      zero_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' (G i) p, if_pos hp, Finset.sum_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [hsplit, Complex.real_smul]
  push_cast
  ring

/-- The product of the selection laws. -/
def selectionMeasure (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ i, ∑ p ∈ G i, w p ≤ 1)
    (h0 : ∀ i, 0 ∉ G i) : Measure (Fin n → ℕ) :=
  Measure.pi fun i => (groupPMF hw0 hw1 h0 i).toMeasure

instance (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ i, ∑ p ∈ G i, w p ≤ 1) (h0 : ∀ i, 0 ∉ G i) :
    IsProbabilityMeasure (selectionMeasure hw0 hw1 h0) := by
  haveI : ∀ i, IsProbabilityMeasure (groupPMF hw0 hw1 h0 i).toMeasure :=
    fun _ => PMF.toMeasure.isProbabilityMeasure _
  unfold selectionMeasure
  infer_instance

/-- **The deviation sum is rarely large.** -/
theorem measureReal_dev_ge_le (φ : ℕ → ℂ) (hφ : ∀ p, ‖φ p‖ ≤ 1) (hw0 : ∀ p, 0 ≤ w p)
    (hw1 : ∀ i, ∑ p ∈ G i, w p ≤ 1) (h0 : ∀ i, 0 ∉ G i) {θ : ℝ} (hθ : 0 ≤ θ) :
    (selectionMeasure hw0 hw1 h0).real {ω | θ ≤ ‖∑ i, groupDev G w φ i (ω i)‖}
      ≤ 4 * Real.exp (-θ ^ 2 / (16 * n)) := by
  classical
  set μ := selectionMeasure hw0 hw1 h0 with hμ
  set X : Fin n → (Fin n → ℕ) → ℂ := fun i ω => groupDev G w φ i (ω i) / 2 with hX
  have hindep : iIndepFun X μ := by
    rw [hμ, selectionMeasure]
    exact iIndepFun_pi (X := fun i q => groupDev G w φ i q / 2) fun i =>
      (measurable_from_nat (f := fun q => groupDev G w φ i q / 2)).aemeasurable
  have hindepRe : iIndepFun (fun i ω => (X i ω).re) μ :=
    hindep.comp (fun _ => Complex.re) fun _ => Complex.measurable_re
  have hindepIm : iIndepFun (fun i ω => (X i ω).im) μ :=
    hindep.comp (fun _ => Complex.im) fun _ => Complex.measurable_im
  have hmeasX : ∀ i, Measurable (X i) := fun i =>
    (measurable_from_nat (f := fun q => groupDev G w φ i q / 2)).comp (measurable_pi_apply i)
  have hbound : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ 1 := fun i => Filter.Eventually.of_forall fun ω => by
    simp only [hX, norm_div, Complex.norm_ofNat]
    linarith [norm_groupDev_le φ hφ hw0 hw1 i (ω i)]
  have hmarg : ∀ i (f : ℂ → ℝ), Measurable f →
      ∫ ω, f (X i ω) ∂μ = ∫ q, f (groupDev G w φ i q / 2) ∂(groupPMF hw0 hw1 h0 i).toMeasure := by
    intro i f hf
    have hmp : MeasurePreserving (fun ω : Fin n → ℕ => ω i) μ
        (groupPMF hw0 hw1 h0 i).toMeasure := by
      rw [hμ, selectionMeasure]
      haveI : ∀ i, IsProbabilityMeasure (groupPMF hw0 hw1 h0 i).toMeasure :=
        fun _ => PMF.toMeasure.isProbabilityMeasure _
      exact measurePreserving_eval _ i
    rw [← hmp.map_eq, integral_map (measurable_pi_apply i).aemeasurable
      (hf.comp (measurable_from_nat (f := fun q => groupDev G w φ i q / 2))).aestronglyMeasurable]
  have hintC : ∀ i, Integrable (fun q => groupDev G w φ i q / 2)
      (groupPMF hw0 hw1 h0 i).toMeasure := fun i =>
    Integrable.of_bound (measurable_from_nat (f := fun q => groupDev G w φ i q / 2)).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun q => by
        rw [norm_div, Complex.norm_ofNat]; linarith [norm_groupDev_le φ hφ hw0 hw1 i q])
  have hzero : ∀ i, ∫ q, groupDev G w φ i q / 2 ∂(groupPMF hw0 hw1 h0 i).toMeasure = 0 := by
    intro i
    rw [integral_div, integral_groupDev φ hφ hw0 hw1 h0 i, zero_div]
  have hcentreRe : ∀ i, ∫ ω, (X i ω).re ∂μ = 0 := by
    intro i
    have h := integral_re (hintC i)
    simp only [RCLike.re_to_complex] at h
    rw [hmarg i Complex.re Complex.measurable_re, h, hzero i, Complex.zero_re]
  have hcentreIm : ∀ i, ∫ ω, (X i ω).im ∂μ = 0 := by
    intro i
    have h := integral_im (hintC i)
    simp only [RCLike.im_to_complex] at h
    rw [hmarg i Complex.im Complex.measurable_im, h, hzero i, Complex.zero_im]
  have h := measureReal_norm_sum_ge_le (μ := μ) X hindepRe hindepIm
    (fun i => (hmeasX i).aemeasurable) hbound hcentreRe hcentreIm (ε := θ / 2) (by positivity)
  rw [Fintype.card_fin] at h
  have hset : {ω : Fin n → ℕ | θ ≤ ‖∑ i, groupDev G w φ i (ω i)‖} =
      {ω | θ / 2 ≤ ‖∑ i, X i ω‖} := by
    ext ω
    simp only [Set.mem_setOf_eq, hX, ← Finset.sum_div, norm_div, Complex.norm_ofNat]
    constructor <;> intro h' <;> linarith
  rw [hset]
  calc _ ≤ 4 * Real.exp (-(θ / 2) ^ 2 / (4 * (n : ℝ))) := h
    _ = 4 * Real.exp (-θ ^ 2 / (16 * n)) := by congr 2; ring

/-- **A good selection exists.**  For countably many tests with summable tail bounds below `1`, one
choice keeps every deviation sum below its threshold. -/
theorem exists_selection (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ i, ∑ p ∈ G i, w p ≤ 1)
    (h0 : ∀ i, 0 ∉ G i) {E : Type*} [Countable E] (φ : E → ℕ → ℂ) (hφ : ∀ e p, ‖φ e p‖ ≤ 1)
    (θ : E → ℝ) (hθ : ∀ e, 0 ≤ θ e)
    (hlt : ∑' e, ENNReal.ofReal (4 * Real.exp (-θ e ^ 2 / (16 * n))) < 1) :
    ∃ ω : Fin n → ℕ, (∀ i, ω i = 0 ∨ ω i ∈ G i) ∧
      ∀ e, ‖∑ i, groupDev G w (φ e) i (ω i)‖ < θ e := by
  classical
  set μ := selectionMeasure hw0 hw1 h0 with hμ
  set bad : E → Set (Fin n → ℕ) := fun e => {ω | θ e ≤ ‖∑ i, groupDev G w (φ e) i (ω i)‖}
  set off : Fin n → Set (Fin n → ℕ) := fun i => {ω | ω i ∉ insert 0 (G i)}
  have hoff : ∀ i, μ (off i) = 0 := by
    intro i
    have hmp : MeasurePreserving (fun ω : Fin n → ℕ => ω i) μ
        (groupPMF hw0 hw1 h0 i).toMeasure := by
      rw [hμ, selectionMeasure]
      haveI : ∀ i, IsProbabilityMeasure (groupPMF hw0 hw1 h0 i).toMeasure :=
        fun _ => PMF.toMeasure.isProbabilityMeasure _
      exact measurePreserving_eval _ i
    have hpre : off i = (fun ω : Fin n → ℕ => ω i) ⁻¹' ((insert 0 (G i) : Finset ℕ) : Set ℕ)ᶜ := by
      ext ω; simp [off]
    rw [hpre, hmp.measure_preimage (MeasurableSet.of_discrete).nullMeasurableSet,
      PMF.toMeasure_apply_eq_zero_iff _ MeasurableSet.of_discrete]
    rw [groupPMF, PMF.support_ofFinset]
    exact Set.disjoint_left.mpr fun q hq hq' => hq' hq.1
  have hbad : ∀ e, μ (bad e) ≤ ENNReal.ofReal (4 * Real.exp (-θ e ^ 2 / (16 * n))) := by
    intro e
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (bad e)), ← measureReal_def]
    exact ENNReal.ofReal_le_ofReal (measureReal_dev_ge_le (φ e) (hφ e) hw0 hw1 h0 (hθ e))
  have htotal : μ ((⋃ e, bad e) ∪ ⋃ i, off i) < 1 := by
    calc μ ((⋃ e, bad e) ∪ ⋃ i, off i) ≤ μ (⋃ e, bad e) + μ (⋃ i, off i) := measure_union_le _ _
      _ ≤ ∑' e, μ (bad e) + 0 := add_le_add (measure_iUnion_le _)
          (le_of_eq (measure_iUnion_null hoff))
      _ ≤ ∑' e, ENNReal.ofReal (4 * Real.exp (-θ e ^ 2 / (16 * n))) := by
          rw [add_zero]; exact ENNReal.tsum_le_tsum hbad
      _ < 1 := hlt
  have hcompl : μ ((⋃ e, bad e) ∪ ⋃ i, off i)ᶜ ≠ 0 := by
    intro h0'
    have := measure_add_measure_compl (μ := μ)
      (s := (⋃ e, bad e) ∪ ⋃ i, off i) (MeasurableSet.of_discrete)
    rw [h0', add_zero, measure_univ] at this
    exact absurd this htotal.ne
  obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero hcompl
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hω
  refine ⟨ω, fun i => ?_, fun e => ?_⟩
  · have := hω.2 i
    simp only [off, Set.mem_setOf_eq, not_not, Finset.mem_insert] at this
    exact this
  · have := hω.1 e
    simp only [bad, Set.mem_setOf_eq, not_le] at this
    exact this

end GaloisForLFunctions.HTGeometry.GroupedSelection
