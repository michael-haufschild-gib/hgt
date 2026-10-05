import GaloisForLFunctions.HTGeometry.GroupedSelectionConcentration

/-!
# Variance-sensitive control of the number of selected groups

In the independent group selection of `HTGeometry.GroupedSelection` group `i` is hit (some element
chosen) with probability `W_i = Σ_{p ∈ G_i} w(p)`.  The centred hit indicator
`Y_i = 1[ω_i ≠ 0] − W_i` (`countDev`) satisfies, for `|μ| ≤ 1`,

`E e^{μ Y_i} = (1 − W_i) e^{−μ W_i} + W_i e^{μ(1 − W_i)} ≤ e^{μ² min(W_i, 1 − W_i)}`

(`bernoulli_mgf_le`), from `1 + z ≤ e^z` and `|e^μ − 1 − μ| ≤ μ²`.  By independence and
Chernoff's bound, for `0 ≤ t ≤ 1` and `V ≥ Σ_{i ∈ s} min(W_i, 1 − W_i)`,

`P(|Σ_{i ∈ s} Y_i| ≥ λ) ≤ 2 e^{t² V − t λ}`   (`measureReal_abs_countDev_ge_le`).

Groups of mass close to `1` therefore contribute almost nothing: the count fluctuates on the scale
`√V`, not on the scale `√n` of Hoeffding's bound.

**Theorem** (`exists_selection_count`).  Countably many Hoeffding tests and countably many count
tests whose failure bounds sum to less than `1` are met by one selection simultaneously.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.GroupedSelection

variable {n : ℕ} {G : Fin n → Finset ℕ} {w : ℕ → ℝ}

/-- The mass `W_i = Σ_{p ∈ G_i} w(p)` of group `i`. -/
def groupMass (G : Fin n → Finset ℕ) (w : ℕ → ℝ) (i : Fin n) : ℝ := ∑ p ∈ G i, w p

/-- The centred hit indicator `1[q ≠ 0] − W_i`. -/
def countDev (G : Fin n → Finset ℕ) (w : ℕ → ℝ) (i : Fin n) (q : ℕ) : ℝ :=
  (if q = 0 then 0 else 1) - groupMass G w i

/-- **The Bernoulli exponential moment.** -/
theorem bernoulli_mgf_le {W μ : ℝ} (hW0 : 0 ≤ W) (hW1 : W ≤ 1) (hμ : |μ| ≤ 1) :
    (1 - W) * Real.exp (-μ * W) + W * Real.exp (μ * (1 - W)) ≤
      Real.exp (μ ^ 2 * min W (1 - W)) := by
  have hq : Real.exp μ - 1 - μ ≤ μ ^ 2 :=
    (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le hμ)
  have hq' : Real.exp (-μ) - 1 + μ ≤ μ ^ 2 := by
    have := (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le (x := -μ) (by rwa [abs_neg]))
    linarith [show (-μ) ^ 2 = μ ^ 2 by ring]
  have h1 : (1 - W) * Real.exp (-μ * W) + W * Real.exp (μ * (1 - W)) ≤ Real.exp (μ ^ 2 * W) := by
    have e : (1 - W) * Real.exp (-μ * W) + W * Real.exp (μ * (1 - W)) =
        Real.exp (-μ * W) * (1 + W * (Real.exp μ - 1)) := by
      rw [show μ * (1 - W) = μ + -μ * W by ring, Real.exp_add]; ring
    rw [e]
    calc Real.exp (-μ * W) * (1 + W * (Real.exp μ - 1)) ≤
          Real.exp (-μ * W) * Real.exp (W * (Real.exp μ - 1)) := by
          gcongr; linarith [Real.add_one_le_exp (W * (Real.exp μ - 1))]
      _ = Real.exp (W * (Real.exp μ - 1 - μ)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (μ ^ 2 * W) := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : (1 - W) * Real.exp (-μ * W) + W * Real.exp (μ * (1 - W)) ≤
      Real.exp (μ ^ 2 * (1 - W)) := by
    have e : (1 - W) * Real.exp (-μ * W) + W * Real.exp (μ * (1 - W)) =
        Real.exp (μ * (1 - W)) * (1 + (1 - W) * (Real.exp (-μ) - 1)) := by
      rw [show -μ * W = μ * (1 - W) + -μ by ring, Real.exp_add]; ring
    rw [e]
    calc Real.exp (μ * (1 - W)) * (1 + (1 - W) * (Real.exp (-μ) - 1)) ≤
          Real.exp (μ * (1 - W)) * Real.exp ((1 - W) * (Real.exp (-μ) - 1)) := by
          gcongr; linarith [Real.add_one_le_exp ((1 - W) * (Real.exp (-μ) - 1))]
      _ = Real.exp ((1 - W) * (Real.exp (-μ) - 1 + μ)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (μ ^ 2 * (1 - W)) := Real.exp_le_exp.mpr (by nlinarith)
  rcases le_total W (1 - W) with h | h
  · rw [min_eq_left h]; exact h1
  · rw [min_eq_right h]; exact h2

theorem groupMass_nonneg (hw0 : ∀ p, 0 ≤ w p) (i : Fin n) : 0 ≤ groupMass G w i :=
  Finset.sum_nonneg fun p _ => hw0 p

theorem abs_countDev_le (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ i, ∑ p ∈ G i, w p ≤ 1) (i : Fin n)
    (q : ℕ) : |countDev G w i q| ≤ 1 := by
  have h0 := groupMass_nonneg (G := G) hw0 i
  have h1 : groupMass G w i ≤ 1 := hw1 i
  unfold countDev
  rw [abs_le]
  split_ifs <;> constructor <;> linarith

/-- The exponential moment of one hit indicator under its selection law. -/
theorem integral_exp_countDev (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ i, ∑ p ∈ G i, w p ≤ 1)
    (h0 : ∀ i, 0 ∉ G i) (i : Fin n) (μ : ℝ) :
    ∫ q, Real.exp (μ * countDev G w i q) ∂(groupPMF hw0 hw1 h0 i).toMeasure =
      (1 - groupMass G w i) * Real.exp (-μ * groupMass G w i) +
        groupMass G w i * Real.exp (μ * (1 - groupMass G w i)) := by
  classical
  set W := groupMass G w i with hW
  have hint : Integrable (fun q => Real.exp (μ * countDev G w i q))
      (groupPMF hw0 hw1 h0 i).toMeasure := by
    refine Integrable.of_bound (measurable_from_nat (f := fun q =>
      Real.exp (μ * countDev G w i q))).aestronglyMeasurable (Real.exp (|μ|))
      (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ((le_abs_self _).trans ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_countDev_le hw0 hw1 i q)
  rw [PMF.integral_eq_tsum _ _ hint, tsum_eq_sum (s := insert 0 (G i)) fun q hq => by
    rw [groupPMF, PMF.ofFinset_apply, selWeight_eq_zero hq]; simp]
  rw [Finset.sum_insert (h0 i)]
  have hP0 : ((groupPMF hw0 hw1 h0 i) 0).toReal = 1 - W := by
    rw [groupPMF, PMF.ofFinset_apply, selWeight, if_pos rfl]
    exact ENNReal.toReal_ofReal (by linarith [hw1 i])
  have hPq : ∀ q ∈ G i, ((groupPMF hw0 hw1 h0 i) q).toReal = w q := by
    intro q hq
    have hq0 : q ≠ 0 := fun h => h0 i (h ▸ hq)
    rw [groupPMF, PMF.ofFinset_apply, selWeight, if_neg hq0, if_pos hq]
    exact ENNReal.toReal_ofReal (hw0 q)
  have hrest : ∑ q ∈ G i, ((groupPMF hw0 hw1 h0 i) q).toReal • Real.exp (μ * countDev G w i q) =
      W * Real.exp (μ * (1 - W)) := by
    have hterm : ∀ q ∈ G i, ((groupPMF hw0 hw1 h0 i) q).toReal •
        Real.exp (μ * countDev G w i q) = w q * Real.exp (μ * (1 - W)) := by
      intro q hq
      have hq0 : q ≠ 0 := fun h => h0 i (h ▸ hq)
      rw [hPq q hq, countDev, if_neg hq0, smul_eq_mul]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    rfl
  rw [hrest, hP0, countDev, if_pos rfl, smul_eq_mul, ← hW]
  ring_nf

/-- **The exponential moment of a count.** -/
theorem mgf_countDev_le (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ i, ∑ p ∈ G i, w p ≤ 1)
    (h0 : ∀ i, 0 ∉ G i) (s : Finset (Fin n)) {μ : ℝ} (hμ : |μ| ≤ 1) :
    mgf (fun ω : Fin n → ℕ => ∑ i ∈ s, countDev G w i (ω i)) (selectionMeasure hw0 hw1 h0) μ ≤
      Real.exp (μ ^ 2 * ∑ i ∈ s, min (groupMass G w i) (1 - groupMass G w i)) := by
  classical
  set P := selectionMeasure hw0 hw1 h0 with hP
  set X : Fin n → (Fin n → ℕ) → ℝ := fun i ω => countDev G w i (ω i) with hX
  have hindep : iIndepFun X P := by
    rw [hP, selectionMeasure]
    exact iIndepFun_pi (X := fun i q => countDev G w i q) fun i =>
      (measurable_from_nat (f := fun q => countDev G w i q)).aemeasurable
  have hmeas : ∀ i, Measurable (X i) := fun i =>
    (measurable_from_nat (f := fun q => countDev G w i q)).comp (measurable_pi_apply i)
  have hsum : (fun ω : Fin n → ℕ => ∑ i ∈ s, countDev G w i (ω i)) = ∑ i ∈ s, X i := by
    funext ω; simp [hX]
  rw [hsum, hindep.mgf_sum hmeas s, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod (fun i _ => mgf_nonneg) fun i _ => ?_
  have hmp : MeasurePreserving (fun ω : Fin n → ℕ => ω i) P (groupPMF hw0 hw1 h0 i).toMeasure := by
    rw [hP, selectionMeasure]
    haveI : ∀ i, IsProbabilityMeasure (groupPMF hw0 hw1 h0 i).toMeasure :=
      fun _ => PMF.toMeasure.isProbabilityMeasure _
    exact measurePreserving_eval _ i
  have hmarg : mgf (X i) P μ = ∫ q, Real.exp (μ * countDev G w i q) ∂(groupPMF hw0 hw1 h0 i).toMeasure := by
    unfold mgf
    rw [← hmp.map_eq, integral_map (measurable_pi_apply i).aemeasurable
      ((measurable_from_nat (f := fun q => Real.exp (μ * countDev G w i q)))).aestronglyMeasurable]
  rw [hmarg, integral_exp_countDev hw0 hw1 h0 i μ]
  exact bernoulli_mgf_le (groupMass_nonneg hw0 i) (hw1 i) hμ

/-- **Chernoff's bound for a count.** -/
theorem measureReal_abs_countDev_ge_le (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ i, ∑ p ∈ G i, w p ≤ 1)
    (h0 : ∀ i, 0 ∉ G i) (s : Finset (Fin n)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {V : ℝ}
    (hV : ∑ i ∈ s, min (groupMass G w i) (1 - groupMass G w i) ≤ V) (lam : ℝ) :
    (selectionMeasure hw0 hw1 h0).real
        {ω | lam ≤ |∑ i ∈ s, countDev G w i (ω i)|} ≤ 2 * Real.exp (t ^ 2 * V - t * lam) := by
  classical
  set P := selectionMeasure hw0 hw1 h0 with hP
  set Y : (Fin n → ℕ) → ℝ := fun ω => ∑ i ∈ s, countDev G w i (ω i) with hY
  have hYmeas : Measurable Y := by
    refine Finset.measurable_sum _ fun i _ => ?_
    exact (measurable_from_nat (f := fun q => countDev G w i q)).comp (measurable_pi_apply i)
  have hbound : ∀ ω, |Y ω| ≤ s.card := by
    intro ω
    calc |Y ω| ≤ ∑ i ∈ s, |countDev G w i (ω i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, (1 : ℝ) := Finset.sum_le_sum fun i _ => abs_countDev_le hw0 hw1 i (ω i)
      _ = s.card := by simp
  have hint : ∀ u : ℝ, Integrable (fun ω => Real.exp (u * Y ω)) P := by
    intro u
    refine Integrable.of_bound ((hYmeas.const_mul u).exp).aestronglyMeasurable
      (Real.exp (|u| * s.card)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ((le_abs_self _).trans ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hbound ω) (abs_nonneg _)
  have hmgf : ∀ u : ℝ, |u| ≤ 1 → mgf Y P u ≤ Real.exp (u ^ 2 * V) := by
    intro u hu
    refine (mgf_countDev_le hw0 hw1 h0 s hu).trans (Real.exp_le_exp.mpr ?_)
    exact mul_le_mul_of_nonneg_left hV (sq_nonneg u)
  have hup : P.real {ω | lam ≤ Y ω} ≤ Real.exp (t ^ 2 * V - t * lam) := by
    refine (measure_ge_le_exp_mul_mgf lam ht0 (hint t)).trans ?_
    calc Real.exp (-t * lam) * mgf Y P t ≤ Real.exp (-t * lam) * Real.exp (t ^ 2 * V) :=
          mul_le_mul_of_nonneg_left (hmgf t (by rw [abs_of_nonneg ht0]; exact ht1))
            (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; ring_nf
  have hlow : P.real {ω | Y ω ≤ -lam} ≤ Real.exp (t ^ 2 * V - t * lam) := by
    refine (measure_le_le_exp_mul_mgf (-lam) (by linarith : -t ≤ 0) (hint (-t))).trans ?_
    calc Real.exp (-(-t) * -lam) * mgf Y P (-t) ≤ Real.exp (-(-t) * -lam) * Real.exp ((-t) ^ 2 * V) :=
          mul_le_mul_of_nonneg_left (hmgf (-t) (by rw [abs_neg, abs_of_nonneg ht0]; exact ht1))
            (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; ring_nf
  have hsub : {ω | lam ≤ |Y ω|} ⊆ {ω | lam ≤ Y ω} ∪ {ω | Y ω ≤ -lam} := by
    intro ω h
    simp only [Set.mem_setOf_eq] at h
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases le_total 0 (Y ω) with hy | hy
    · left; rwa [abs_of_nonneg hy] at h
    · right; rw [abs_of_nonpos hy] at h; linarith
  calc P.real {ω | lam ≤ |Y ω|} ≤ P.real ({ω | lam ≤ Y ω} ∪ {ω | Y ω ≤ -lam}) :=
        measureReal_mono hsub
    _ ≤ P.real {ω | lam ≤ Y ω} + P.real {ω | Y ω ≤ -lam} := measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- **A selection good for both kinds of tests.** -/
theorem exists_selection_count (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ i, ∑ p ∈ G i, w p ≤ 1)
    (h0 : ∀ i, 0 ∉ G i) {E F : Type*} [Countable E] [Countable F] (φ : E → ℕ → ℂ)
    (hφ : ∀ e p, ‖φ e p‖ ≤ 1) (θ : E → ℝ) (hθ : ∀ e, 0 ≤ θ e) (s : F → Finset (Fin n))
    (lam t V : F → ℝ) (ht0 : ∀ f, 0 ≤ t f) (ht1 : ∀ f, t f ≤ 1)
    (hV : ∀ f, ∑ i ∈ s f, min (groupMass G w i) (1 - groupMass G w i) ≤ V f)
    (hlt : (∑' e, ENNReal.ofReal (4 * Real.exp (-θ e ^ 2 / (16 * n)))) +
      ∑' f, ENNReal.ofReal (2 * Real.exp (t f ^ 2 * V f - t f * lam f)) < 1) :
    ∃ ω : Fin n → ℕ, (∀ i, ω i = 0 ∨ ω i ∈ G i) ∧
      (∀ e, ‖∑ i, groupDev G w (φ e) i (ω i)‖ < θ e) ∧
      ∀ f, |∑ i ∈ s f, countDev G w i (ω i)| < lam f := by
  classical
  set μ := selectionMeasure hw0 hw1 h0 with hμ
  set bad : E → Set (Fin n → ℕ) := fun e => {ω | θ e ≤ ‖∑ i, groupDev G w (φ e) i (ω i)‖}
  set badc : F → Set (Fin n → ℕ) := fun f => {ω | lam f ≤ |∑ i ∈ s f, countDev G w i (ω i)|}
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
  have hbadc : ∀ f, μ (badc f) ≤ ENNReal.ofReal (2 * Real.exp (t f ^ 2 * V f - t f * lam f)) := by
    intro f
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (badc f)), ← measureReal_def]
    exact ENNReal.ofReal_le_ofReal
      (measureReal_abs_countDev_ge_le hw0 hw1 h0 (s f) (ht0 f) (ht1 f) (hV f) (lam f))
  have htotal : μ (((⋃ e, bad e) ∪ ⋃ f, badc f) ∪ ⋃ i, off i) < 1 := by
    calc μ (((⋃ e, bad e) ∪ ⋃ f, badc f) ∪ ⋃ i, off i)
        ≤ μ ((⋃ e, bad e) ∪ ⋃ f, badc f) + μ (⋃ i, off i) := measure_union_le _ _
      _ ≤ (μ (⋃ e, bad e) + μ (⋃ f, badc f)) + 0 :=
          add_le_add (measure_union_le _ _) (le_of_eq (measure_iUnion_null hoff))
      _ ≤ (∑' e, μ (bad e) + ∑' f, μ (badc f)) + 0 := by
          gcongr
          · exact measure_iUnion_le _
          · exact measure_iUnion_le _
      _ ≤ (∑' e, ENNReal.ofReal (4 * Real.exp (-θ e ^ 2 / (16 * n)))) +
            ∑' f, ENNReal.ofReal (2 * Real.exp (t f ^ 2 * V f - t f * lam f)) := by
          rw [add_zero]
          exact add_le_add (ENNReal.tsum_le_tsum hbad) (ENNReal.tsum_le_tsum hbadc)
      _ < 1 := hlt
  have hcompl : μ (((⋃ e, bad e) ∪ ⋃ f, badc f) ∪ ⋃ i, off i)ᶜ ≠ 0 := by
    intro h0'
    have := measure_add_measure_compl (μ := μ)
      (s := ((⋃ e, bad e) ∪ ⋃ f, badc f) ∪ ⋃ i, off i) (MeasurableSet.of_discrete)
    rw [h0', add_zero, measure_univ] at this
    exact absurd this htotal.ne
  obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero hcompl
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hω
  refine ⟨ω, fun i => ?_, fun e => ?_, fun f => ?_⟩
  · have := hω.2 i
    simp only [off, Set.mem_setOf_eq, not_not, Finset.mem_insert] at this
    exact this
  · have := hω.1.1 e
    simp only [bad, Set.mem_setOf_eq, not_le] at this
    exact this
  · have := hω.1.2 f
    simp only [badc, Set.mem_setOf_eq, not_le] at this
    exact this

end GaloisForLFunctions.HTGeometry.GroupedSelection
