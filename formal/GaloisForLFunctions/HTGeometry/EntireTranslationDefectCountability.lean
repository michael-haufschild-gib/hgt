import GaloisForLFunctions.HTGeometry.EntireFamilyDifferentialAlgebraicLocus
import GaloisForLFunctions.HTGeometry.AnalyticSlopeFactor
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicInvariance
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicAntiderivative
import GaloisForLFunctions.HTGeometry.IteratedDerivTranslate

/-!
# Countability of the DA translation spectrum of an entire HT source

For a jointly entire one-parameter family, the differential-algebraic fibre locus has a sharper
alternative than countable-or-everything: either one fixed jet complexity works for every fibre,
or the locus is countable.

Apply this to the translation defects `F (z + h) - F z`.  In the uniform branch, normalize every
nonzero defect by `h⁻¹`.  Its jets are divided differences of the jets of `F`, hence converge at
`h = 0` to the jets of `F'`.  The fixed-complexity determinant locus is closed, so `F'` is DA and
therefore `F` is DA.  A hypertranscendental entire source excludes that branch, leaving a countable
DA translation spectrum.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open Complex Set Filter Topology MeasureTheory

noncomputable section

/-- Uniform fixed-complexity alternative underlying the countable-or-everything theorem. -/
theorem entireFamily_uniformJetRelation_or_countable {Φ : ℂ × ℂ → ℂ}
    (hΦ : Differentiable ℂ Φ) :
    (∃ n d : ℕ, ∀ (φ : JetExponent n d → ℕ) (t : ℂ), familyMinorDet Φ n d φ t = 0) ∨
      {t : ℂ | DifferentiallyAlgebraic fun z => Φ (t, z)}.Countable := by
  classical
  by_cases hcase : ∃ n d : ℕ,
      ∀ (φ : JetExponent n d → ℕ) (t : ℂ), familyMinorDet Φ n d φ t = 0
  · exact Or.inl hcase
  · right
    push Not at hcase
    choose φ t ht using hcase
    have hsub : {s : ℂ | DifferentiallyAlgebraic fun z => Φ (s, z)} ⊆
        ⋃ p : ℕ × ℕ, {s : ℂ | familyMinorDet Φ p.1 p.2 (φ p.1 p.2) s = 0} := by
      intro s hs
      obtain ⟨n, d, h⟩ := (differentiallyAlgebraic_iff_forall_coordinateMinor_det_eq_zero
        (differentiable_fibre hΦ s)).1 hs
      exact Set.mem_iUnion.2 ⟨(n, d), h (φ n d)⟩
    refine Set.Countable.mono hsub (Set.countable_iUnion fun p => ?_)
    exact HTGeometry.countable_setOf_eq_zero_of_analyticOnNhd
      (Complex.analyticOnNhd_univ_iff_differentiable.2
        (differentiable_familyMinorDet hΦ p.1 p.2 (φ p.1 p.2)))
      ⟨t p.1 p.2, ht p.1 p.2⟩

/-- Joint translation-defect family, with shift parameter first. -/
def entireTranslationDefectFamily (F : ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  F (p.2 + p.1) - F p.2

theorem differentiable_entireTranslationDefectFamily {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) : Differentiable ℂ (entireTranslationDefectFamily F) := by
  unfold entireTranslationDefectFamily
  exact (hF.comp (by fun_prop)).sub (hF.comp (by fun_prop))

/-- Jet vector of the normalized translation defect, analytically extended to shift zero. -/
def translationSlopeJetVector (F : ℂ → ℂ) (n : ℕ) (h z : ℂ) : Fin (n + 2) → ℂ :=
  Fin.cons z fun j : Fin (n + 1) =>
    analyticSlope (iteratedDeriv (j : ℕ) F) z (z + h)

/-- Sample row of a normalized translation-defect monomial. -/
def translationSlopeSampleRow (F : ℂ → ℂ) (n d : ℕ) (m : JetExponent n d) :
    ℕ → ℂ → ℂ :=
  fun k h => ∏ i : Fin (n + 2),
    (translationSlopeJetVector F n h (sampleNode k) i) ^ (m i : ℕ)

/-- Square sample minor for normalized translation defects. -/
def translationSlopeMinor (F : ℂ → ℂ) (n d : ℕ) (φ : JetExponent n d → ℕ)
    (h : ℂ) : Matrix (JetExponent n d) (JetExponent n d) ℂ :=
  fun i j => translationSlopeSampleRow F n d j (φ i) h

def translationSlopeMinorDet (F : ℂ → ℂ) (n d : ℕ)
    (φ : JetExponent n d → ℕ) (h : ℂ) : ℂ :=
  (translationSlopeMinor F n d φ h).det

theorem translationSlopeJetVector_zero {F : ℂ → ℂ} (n : ℕ) (z : ℂ) :
    translationSlopeJetVector F n 0 z = entireJetVector (deriv F) n z := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
      simp only [translationSlopeJetVector, Fin.cons_succ, add_zero, analyticSlope_self,
        entireJetVector]
      rw [← congrFun (iteratedDeriv_succ (n := (j : ℕ)) (f := F)) z,
        iteratedDeriv_succ']

theorem translationSlopeSampleRow_zero {F : ℂ → ℂ} (n d : ℕ)
    (m : JetExponent n d) (k : ℕ) :
    translationSlopeSampleRow F n d m k 0 = jetSampleRow (deriv F) n d m k := by
  simp [translationSlopeSampleRow, jetSampleRow, jetMon, translationSlopeJetVector_zero]

theorem translationSlopeMinor_zero {F : ℂ → ℂ} (n d : ℕ)
    (φ : JetExponent n d → ℕ) :
    translationSlopeMinor F n d φ 0 = coordinateMinor (jetSampleRow (deriv F) n d) φ := by
  ext i j
  exact translationSlopeSampleRow_zero n d j (φ i)

theorem translationSlopeMinorDet_zero {F : ℂ → ℂ} (n d : ℕ)
    (φ : JetExponent n d → ℕ) :
    translationSlopeMinorDet F n d φ 0 =
      (coordinateMinor (jetSampleRow (deriv F) n d) φ).det := by
  rw [translationSlopeMinorDet, translationSlopeMinor_zero]

theorem continuousAt_translationSlopeJetVector {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (n : ℕ) (z : ℂ) (i : Fin (n + 2)) :
    ContinuousAt (fun h => translationSlopeJetVector F n h z i) 0 := by
  induction i using Fin.cases with
  | zero => simpa [translationSlopeJetVector] using (continuousAt_const :
      ContinuousAt (fun _ : ℂ => z) 0)
  | succ j =>
      have hjdiff := differentiable_iteratedDeriv_of_differentiable hF (j : ℕ)
      have hjanal : AnalyticAt ℂ (iteratedDeriv (j : ℕ) F) z :=
        (Complex.analyticOnNhd_univ_iff_differentiable.2 hjdiff) z (Set.mem_univ z)
      have hinner : ContinuousAt (fun h : ℂ => z + h) 0 := by fun_prop
      change ContinuousAt
        (fun h : ℂ => analyticSlope (iteratedDeriv (j : ℕ) F) z (z + h)) 0
      exact (continuousAt_analyticSlope hjanal).comp_of_eq hinner (by simp)

private theorem continuousAt_finsetProd {ι X M : Type*} [TopologicalSpace X]
    [TopologicalSpace M] [CommMonoid M] [ContinuousMul M]
    (s : Finset ι) (f : ι → X → M) (x : X)
    (hf : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y => ∏ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : X => (1 : M)) x)
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      change ContinuousAt ((f a) * fun y => ∏ i ∈ s, f i y) x
      exact (hf a (Finset.mem_insert_self a s)).mul
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem continuousAt_finsetSum {ι X M : Type*} [TopologicalSpace X]
    [TopologicalSpace M] [AddCommMonoid M] [ContinuousAdd M]
    (s : Finset ι) (f : ι → X → M) (x : X)
    (hf : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y => ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : X => (0 : M)) x)
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      change ContinuousAt ((f a) + fun y => ∑ i ∈ s, f i y) x
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem continuousAt_translationSlopeSampleRow {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (n d : ℕ) (m : JetExponent n d) (k : ℕ) :
    ContinuousAt (translationSlopeSampleRow F n d m k) 0 := by
  unfold translationSlopeSampleRow
  apply continuousAt_finsetProd Finset.univ
  intro i hi
  exact (continuousAt_translationSlopeJetVector hF n (sampleNode k) i).pow _

theorem continuousAt_translationSlopeMinorDet {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (n d : ℕ) (φ : JetExponent n d → ℕ) :
    ContinuousAt (translationSlopeMinorDet F n d φ) 0 := by
  have hcont : ContinuousAt (fun h : ℂ =>
      ∑ σ : Equiv.Perm (JetExponent n d), (Equiv.Perm.sign σ : ℂ) *
        ∏ i : JetExponent n d, translationSlopeMinor F n d φ h (σ i) i) 0 := by
    apply continuousAt_finsetSum Finset.univ
    intro σ hσ
    apply continuousAt_const.mul
    apply continuousAt_finsetProd Finset.univ
    intro i hi
    exact continuousAt_translationSlopeSampleRow hF n d i (φ (σ i))
  change ContinuousAt (fun h => (translationSlopeMinor F n d φ h).det) 0
  simpa only [Matrix.det_apply'] using hcont

/-- Total value-jet degree of a bounded differential monomial, excluding its node coordinate. -/
def jetValueDegree {n d : ℕ} (m : JetExponent n d) : ℕ :=
  ∑ j : Fin (n + 1), (m j.succ : ℕ)

theorem translationSlopeJetVector_of_ne {F : ℂ → ℂ} (n : ℕ) {h : ℂ} (hh : h ≠ 0)
    (z : ℂ) :
    translationSlopeJetVector F n h z =
      Fin.cons z fun j : Fin (n + 1) =>
        h⁻¹ * (iteratedDeriv (j : ℕ) F (z + h) - iteratedDeriv (j : ℕ) F z) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
      rw [translationSlopeJetVector, Fin.cons_succ, analyticSlope_of_ne (add_ne_left.mpr hh)]
      field_simp
      simp only [Fin.cons_succ]
      ring

theorem translationSlopeSampleRow_of_ne {F : ℂ → ℂ} (hF : Differentiable ℂ F) (n d : ℕ)
    (m : JetExponent n d) (k : ℕ) {h : ℂ} (hh : h ≠ 0) :
    translationSlopeSampleRow F n d m k h =
      h⁻¹ ^ jetValueDegree m *
        jetSampleRow (fun z => F (z + h) - F z) n d m k := by
  classical
  let A : Fin (n + 1) → ℂ := fun j =>
    iteratedDeriv (j : ℕ) F (sampleNode k + h) - iteratedDeriv (j : ℕ) F (sampleNode k)
  have hraw : jetSampleRow (fun z => F (z + h) - F z) n d m k =
      sampleNode k ^ (m 0 : ℕ) * ∏ j : Fin (n + 1), A j ^ (m j.succ : ℕ) := by
    rw [jetSampleRow, jetMon, Fin.prod_univ_succ]
    simp only [entireJetVector, Fin.cons_zero, Fin.cons_succ]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    dsimp only [A]
    have htrans : ContDiffAt ℂ (j : ℕ) (fun z => F (z + h)) (sampleNode k) :=
      (hF.comp (by fun_prop)).contDiff.contDiffAt
    have hbase : ContDiffAt ℂ (j : ℕ) F (sampleNode k) := hF.contDiff.contDiffAt
    rw [show (fun z => F (z + h) - F z) = (fun z => F (z + h)) - F from rfl]
    congr 1
    rw [iteratedDeriv_sub htrans hbase, iteratedDeriv_comp_add_right]
  have hscaled : (∏ j : Fin (n + 1), (h⁻¹ * A j) ^ (m j.succ : ℕ)) =
      h⁻¹ ^ jetValueDegree m * ∏ j : Fin (n + 1), A j ^ (m j.succ : ℕ) := by
    simp only [mul_pow]
    rw [Finset.prod_mul_distrib, jetValueDegree, Finset.prod_pow_eq_pow_sum]
  rw [translationSlopeSampleRow, translationSlopeJetVector_of_ne n hh,
    Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [hscaled, hraw]
  ring

theorem translationSlopeMinor_eq_mul_diagonal {F : ℂ → ℂ} (hF : Differentiable ℂ F) (n d : ℕ)
    (φ : JetExponent n d → ℕ) {h : ℂ} (hh : h ≠ 0) :
    translationSlopeMinor F n d φ h =
      coordinateMinor (jetSampleRow (fun z => F (z + h) - F z) n d) φ *
        Matrix.diagonal (fun m : JetExponent n d => h⁻¹ ^ jetValueDegree m) := by
  classical
  ext i j
  rw [translationSlopeMinor, Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · simp [translationSlopeSampleRow_of_ne hF n d j (φ i) hh, coordinateMinor]
    ring
  · intro b hb hbj
    simp [Matrix.diagonal, hbj]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem translationSlopeMinorDet_eq_mul {F : ℂ → ℂ} (hF : Differentiable ℂ F) (n d : ℕ)
    (φ : JetExponent n d → ℕ) {h : ℂ} (hh : h ≠ 0) :
    translationSlopeMinorDet F n d φ h =
      (coordinateMinor (jetSampleRow (fun z => F (z + h) - F z) n d) φ).det *
        ∏ m : JetExponent n d, h⁻¹ ^ jetValueDegree m := by
  rw [translationSlopeMinorDet, translationSlopeMinor_eq_mul_diagonal hF n d φ hh,
    Matrix.det_mul, Matrix.det_diagonal]

/-- Uniform bounded-complexity relations for all translation defects force the derivative to be DA. -/
theorem differentiallyAlgebraic_deriv_of_uniform_translation_relations {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {n d : ℕ}
    (hrel : ∀ (φ : JetExponent n d → ℕ) (h : ℂ),
      familyMinorDet (entireTranslationDefectFamily F) n d φ h = 0) :
    DifferentiallyAlgebraic (deriv F) := by
  refine (differentiallyAlgebraic_iff_forall_coordinateMinor_det_eq_zero hF.deriv).2
    ⟨n, d, fun φ => ?_⟩
  rw [← translationSlopeMinorDet_zero]
  have hslope : Tendsto (fun k : ℕ => translationSlopeMinorDet F n d φ (sampleNode k))
      atTop (𝓝 (translationSlopeMinorDet F n d φ 0)) :=
    (continuousAt_translationSlopeMinorDet hF n d φ).tendsto.comp
      (tendsto_sampleNode.mono_right inf_le_left)
  have hslope0 : Tendsto (fun k : ℕ => translationSlopeMinorDet F n d φ (sampleNode k))
      atTop (𝓝 0) := by
    have hz : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0) := tendsto_const_nhds
    refine hz.congr' ?_
    filter_upwards with k
    rw [translationSlopeMinorDet_eq_mul hF n d φ (sampleNode_ne_zero k)]
    have hraw : (coordinateMinor
        (jetSampleRow (fun z => F (z + sampleNode k) - F z) n d) φ).det = 0 := by
      simpa [familyMinorDet, entireTranslationDefectFamily] using hrel φ (sampleNode k)
    rw [hraw, zero_mul]
  exact tendsto_nhds_unique hslope hslope0

/-- **Entire translation-spectrum countability.**  Every hypertranscendental entire function has
at most countably many differentially algebraic additive translation defects. -/
theorem countable_differentiallyAlgebraic_translationDefect {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hFht : ¬ DifferentiallyAlgebraic F) :
    {h : ℂ | DifferentiallyAlgebraic fun z => F (z + h) - F z}.Countable := by
  rcases entireFamily_uniformJetRelation_or_countable
      (differentiable_entireTranslationDefectFamily hF) with huniform | hcount
  · obtain ⟨n, d, hrel⟩ := huniform
    have hderiv : DifferentiallyAlgebraic (deriv F) :=
      differentiallyAlgebraic_deriv_of_uniform_translation_relations hF hrel
    exact absurd (differentiallyAlgebraic_of_deriv hderiv) hFht
  · simpa [entireTranslationDefectFamily] using hcount

/-- Fixed jet-order/exponent-box stratum of the DA translation spectrum. -/
def entireTranslationJetStratum (F : ℂ → ℂ) (n d : ℕ) : Set ℂ :=
  {h | ∀ φ : JetExponent n d → ℕ,
    familyMinorDet (entireTranslationDefectFamily F) n d φ h = 0}

/-- An accumulating fixed-complexity translation stratum forces the source itself to be DA. -/
theorem differentiallyAlgebraic_of_translationJetStratum_accumulates {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {n d : ℕ} {u : ℕ → ℂ} (huinj : Function.Injective u)
    (hu : ∀ k, u k ∈ entireTranslationJetStratum F n d) {h₀ : ℂ}
    (hutend : Tendsto u atTop (𝓝 h₀)) : DifferentiallyAlgebraic F := by
  have hΦ : Differentiable ℂ (entireTranslationDefectFamily F) :=
    differentiable_entireTranslationDefectFamily hF
  have hne : ∀ᶠ k in atTop, u k ≠ h₀ := by
    by_cases hex : ∃ k₀, u k₀ = h₀
    · obtain ⟨k₀, hk₀⟩ := hex
      filter_upwards [eventually_gt_atTop k₀] with k hk hkeq
      exact (Nat.ne_of_gt hk) (huinj (hkeq.trans hk₀.symm))
    · push Not at hex
      exact Filter.Eventually.of_forall hex
  have huwithin : Tendsto u atTop (𝓝[≠] h₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hutend, hne⟩
  have hrel : ∀ (φ : JetExponent n d → ℕ) (h : ℂ),
      familyMinorDet (entireTranslationDefectFamily F) n d φ h = 0 := by
    intro φ
    have hfreq : ∃ᶠ h in 𝓝[≠] h₀,
        familyMinorDet (entireTranslationDefectFamily F) n d φ h = 0 :=
      huwithin.frequently (Filter.Frequently.of_forall fun k => hu k φ)
    have hanalytic : AnalyticOnNhd ℂ
        (familyMinorDet (entireTranslationDefectFamily F) n d φ) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.2
        (differentiable_familyMinorDet hΦ n d φ)
    have hzero := hanalytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ h₀) hfreq
    exact fun h => hzero (Set.mem_univ h)
  exact differentiallyAlgebraic_of_deriv
    (differentiallyAlgebraic_deriv_of_uniform_translation_relations hF hrel)

/-- A hypertranscendental entire source admits no convergent injective sequence inside one fixed
translation-relation complexity stratum. -/
theorem not_exists_injective_tendsto_translationJetStratum {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hFht : ¬ DifferentiallyAlgebraic F) (n d : ℕ) :
    ¬ ∃ (u : ℕ → ℂ) (h₀ : ℂ), Function.Injective u ∧
      (∀ k, u k ∈ entireTranslationJetStratum F n d) ∧ Tendsto u atTop (𝓝 h₀) := by
  rintro ⟨u, h₀, huinj, hu, hutend⟩
  exact hFht (differentiallyAlgebraic_of_translationJetStratum_accumulates
    hF huinj hu hutend)

/-- A nonzero ADE whose jet order is `n` and whose total polynomial degree is at most `d`. -/
def HasDifferentialRelationOfComplexity (f : ℂ → ℂ) (n d : ℕ) : Prop :=
  ∃ P : MvPolynomial (Fin (n + 2)) ℂ, P ≠ 0 ∧ P.totalDegree ≤ d ∧
    ∀ z, MvPolynomial.eval (entireJetVector f n z) P = 0

/-- A total-degree-bounded ADE gives the corresponding bounded-exponent jet relation. -/
theorem exists_jetRelation_of_hasDifferentialRelationOfComplexity {f : ℂ → ℂ} {n d : ℕ}
    (h : HasDifferentialRelationOfComplexity f n d) :
    ∃ c : JetExponent n d → ℂ, c ≠ 0 ∧ JetRelation f n d c := by
  classical
  obtain ⟨P, hP0, hPdeg, hP⟩ := h
  refine ⟨fun m => MvPolynomial.coeff (jetExponentToFinsupp m) P, ?_, ?_⟩
  · intro hc
    refine hP0 (MvPolynomial.ext P 0 fun μ => ?_)
    by_cases hμ : μ ∈ P.support
    · have hbd : ∀ i, μ i ≤ d := fun i =>
        le_trans (le_trans (finsupp_apply_le_sum μ i) (MvPolynomial.le_totalDegree hμ)) hPdeg
      have hmem : jetExponentToFinsupp
          (fun i => (⟨μ i, Nat.lt_succ_of_le (hbd i)⟩ : Fin (d + 1))) = μ := by
        ext i
        rfl
      have hcμ := congrFun hc
        (fun i => (⟨μ i, Nat.lt_succ_of_le (hbd i)⟩ : Fin (d + 1)))
      rw [hmem] at hcμ
      simpa using hcμ
    · simp [MvPolynomial.notMem_support_iff.1 hμ]
  · intro z
    have hbd : ∀ μ ∈ P.support, ∀ i, μ i ≤ d := fun μ hμ i =>
      le_trans (le_trans (finsupp_apply_le_sum μ i) (MvPolynomial.le_totalDegree hμ)) hPdeg
    have hsum := sum_jetExponent_eq_sum_support (d := d) P hbd
      (fun μ => MvPolynomial.coeff μ P *
        ∏ i : Fin (n + 2), (entireJetVector f n z i) ^ (μ i))
      (fun μ hμ => by simp [MvPolynomial.notMem_support_iff.1 hμ])
    rw [show (∑ m : JetExponent n d,
        MvPolynomial.coeff (jetExponentToFinsupp m) P * jetMon f n d m z) =
        ∑ m : JetExponent n d,
          (fun μ => MvPolynomial.coeff μ P *
            ∏ i : Fin (n + 2), (entireJetVector f n z i) ^ (μ i))
            (jetExponentToFinsupp m) from rfl,
      hsum, ← eval_entireJetVector_eq_sum]
    exact hP z

theorem forall_coordinateMinor_eq_zero_of_hasDifferentialRelationOfComplexity
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {n d : ℕ}
    (h : HasDifferentialRelationOfComplexity f n d) :
    ∀ φ : JetExponent n d → ℕ, (coordinateMinor (jetSampleRow f n d) φ).det = 0 := by
  have hnli := (exists_jetRelation_iff_not_linearIndependent f hf n d).1
    (exists_jetRelation_of_hasDifferentialRelationOfComplexity h)
  exact (not_linearIndependent_iff_forall_coordinateMinor_det_eq_zero f n d).1 hnli

theorem mem_entireTranslationJetStratum_of_hasDifferentialRelationOfComplexity
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) {n d : ℕ} {h : ℂ}
    (hADE : HasDifferentialRelationOfComplexity (fun z => F (z + h) - F z) n d) :
    h ∈ entireTranslationJetStratum F n d := by
  intro φ
  have hdefect : Differentiable ℂ (fun z => F (z + h) - F z) :=
    (hF.comp (by fun_prop)).sub hF
  simpa [familyMinorDet, entireTranslationDefectFamily] using
    forall_coordinateMinor_eq_zero_of_hasDifferentialRelationOfComplexity hdefect hADE φ

/-- Exact total-degree form of complexity escape at a fixed differential order. -/
theorem not_exists_injective_tendsto_boundedDegree_translationADE {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hFht : ¬ DifferentiallyAlgebraic F) (n d : ℕ) :
    ¬ ∃ (u : ℕ → ℂ) (h₀ : ℂ), Function.Injective u ∧ Tendsto u atTop (𝓝 h₀) ∧
      ∀ k, HasDifferentialRelationOfComplexity (fun z => F (z + u k) - F z) n d := by
  rintro ⟨u, h₀, huinj, hutend, huADE⟩
  exact (not_exists_injective_tendsto_translationJetStratum hF hFht n d)
    ⟨u, h₀, huinj,
      fun k => mem_entireTranslationJetStratum_of_hasDifferentialRelationOfComplexity
        hF (huADE k), hutend⟩

/-- Embed a lower jet packet into a larger packet without changing coordinate labels. -/
def jetOrderEmbed {n N : ℕ} (h : n ≤ N) : Fin (n + 2) → Fin (N + 2) :=
  Fin.castLE (Nat.add_le_add_right h 2)

theorem jetOrderEmbed_injective {n N : ℕ} (h : n ≤ N) :
    Function.Injective (jetOrderEmbed h) :=
  Fin.castLE_injective _

theorem entireJetVector_jetOrderEmbed {f : ℂ → ℂ} {n N : ℕ} (h : n ≤ N) (z : ℂ)
    (i : Fin (n + 2)) :
    entireJetVector f N z (jetOrderEmbed h i) = entireJetVector f n z i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ j => rfl

theorem HasDifferentialRelationOfComplexity.mono_order {f : ℂ → ℂ} {n N d : ℕ}
    (h : HasDifferentialRelationOfComplexity f n d) (hnN : n ≤ N) :
    HasDifferentialRelationOfComplexity f N d := by
  obtain ⟨P, hP0, hPdeg, hP⟩ := h
  refine ⟨MvPolynomial.rename (jetOrderEmbed hnN) P, ?_,
    le_trans (MvPolynomial.totalDegree_rename_le _ _) hPdeg, ?_⟩
  · intro hzero
    apply hP0
    apply MvPolynomial.rename_injective _ (jetOrderEmbed_injective hnN)
    simpa using hzero
  · intro z
    rw [MvPolynomial.eval_rename]
    have hvec : entireJetVector f N z ∘ jetOrderEmbed hnN = entireJetVector f n z := by
      funext i
      exact entireJetVector_jetOrderEmbed hnN z i
    rw [hvec]
    exact hP z

/-- Full paper-level complexity escape: differential orders and total degrees cannot both remain
bounded along an accumulating injective DA-defect sequence. -/
theorem not_exists_injective_tendsto_boundedOrderDegree_translationADE {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hFht : ¬ DifferentiallyAlgebraic F) (N d : ℕ) :
    ¬ ∃ (u : ℕ → ℂ) (r : ℕ → ℕ) (h₀ : ℂ), Function.Injective u ∧
      Tendsto u atTop (𝓝 h₀) ∧ (∀ k, r k ≤ N) ∧
      ∀ k, HasDifferentialRelationOfComplexity (fun z => F (z + u k) - F z) (r k) d := by
  rintro ⟨u, r, h₀, huinj, hutend, hr, huADE⟩
  exact (not_exists_injective_tendsto_boundedDegree_translationADE hF hFht N d)
    ⟨u, h₀, huinj, hutend, fun k => (huADE k).mono_order (hr k)⟩

end

end GaloisForLFunctions.HTGeometry
