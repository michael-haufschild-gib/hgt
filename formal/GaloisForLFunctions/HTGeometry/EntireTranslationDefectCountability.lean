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

end

end GaloisForLFunctions.HTGeometry
