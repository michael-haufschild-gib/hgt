import GaloisForLFunctions.HTGeometry.DomainJetRelationLocus
import GaloisForLFunctions.HTGeometry.EntireTranslationDefectCountability

/-!
# Normalized translation-defect minors on a domain

`EntireTranslationDefectCountability` normalizes the translation defect of an *entire* source by
`h⁻¹` and lets `h → 0`, turning a uniform bounded-complexity relation for all defects into a
relation for the derivative of the source.  Nothing in that argument uses entirety: it only needs
the source to be analytic at the sample nodes and at their translates.

This module carries the normalization to an arbitrary domain, with sample nodes inside a disc.
It is the local engine behind the meromorphic translation-spectrum theorems.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open Complex Set Filter Topology

noncomputable section

/-! ### Continuity of the normalized jet coordinates -/

theorem continuousAt_finsetProd' {ι X M : Type*} [TopologicalSpace X]
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

theorem continuousAt_finsetSum' {ι X M : Type*} [TopologicalSpace X]
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

theorem continuousAt_translationSlopeJetVector_of_analyticOnNhd {F : ℂ → ℂ} {Ω : Set ℂ}
    (hF : AnalyticOnNhd ℂ F Ω) (n : ℕ) {z : ℂ} (hz : z ∈ Ω) (i : Fin (n + 2)) :
    ContinuousAt (fun h => translationSlopeJetVector F n h z i) 0 := by
  induction i using Fin.cases with
  | zero => simpa [translationSlopeJetVector] using (continuousAt_const :
      ContinuousAt (fun _ : ℂ => z) 0)
  | succ j =>
      have hjanal : AnalyticAt ℂ (iteratedDeriv (j : ℕ) F) z :=
        analyticOnNhd_iteratedDeriv hF (j : ℕ) z hz
      have hinner : ContinuousAt (fun h : ℂ => z + h) 0 := by fun_prop
      change ContinuousAt
        (fun h : ℂ => analyticSlope (iteratedDeriv (j : ℕ) F) z (z + h)) 0
      exact (continuousAt_analyticSlope hjanal).comp_of_eq hinner (by simp)

/-! ### The normalized minor on a domain -/

/-- Sample row of a normalized translation-defect monomial at nodes inside a disc. -/
def domainSlopeSampleRow (F : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (n d : ℕ) (m : JetExponent n d) :
    ℕ → ℂ → ℂ :=
  fun k h => ∏ i : Fin (n + 2),
    (translationSlopeJetVector F n h (domainSampleNode z₀ r k) i) ^ (m i : ℕ)

/-- Square sample minor of the normalized translation defects on a domain. -/
def domainSlopeMinor (F : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (n d : ℕ) (φ : JetExponent n d → ℕ)
    (h : ℂ) : Matrix (JetExponent n d) (JetExponent n d) ℂ :=
  fun i j => domainSlopeSampleRow F z₀ r n d j (φ i) h

def domainSlopeMinorDet (F : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (n d : ℕ)
    (φ : JetExponent n d → ℕ) (h : ℂ) : ℂ :=
  (domainSlopeMinor F z₀ r n d φ h).det

theorem domainSlopeSampleRow_zero (F : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (n d : ℕ)
    (m : JetExponent n d) (k : ℕ) :
    domainSlopeSampleRow F z₀ r n d m k 0 = domainJetSampleRow (deriv F) z₀ r n d m k := by
  simp [domainSlopeSampleRow, domainJetSampleRow, jetMon, translationSlopeJetVector_zero]

theorem domainSlopeMinor_zero (F : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (n d : ℕ)
    (φ : JetExponent n d → ℕ) :
    domainSlopeMinor F z₀ r n d φ 0 = coordinateMinor (domainJetSampleRow (deriv F) z₀ r n d) φ := by
  ext i j
  exact domainSlopeSampleRow_zero F z₀ r n d j (φ i)

theorem domainSlopeMinorDet_zero (F : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) (n d : ℕ)
    (φ : JetExponent n d → ℕ) :
    domainSlopeMinorDet F z₀ r n d φ 0 =
      (coordinateMinor (domainJetSampleRow (deriv F) z₀ r n d) φ).det := by
  rw [domainSlopeMinorDet, domainSlopeMinor_zero]

theorem continuousAt_domainSlopeSampleRow {F : ℂ → ℂ} {Ω : Set ℂ} (hF : AnalyticOnNhd ℂ F Ω)
    {z₀ : ℂ} {r : ℝ} (hnodes : ∀ k, domainSampleNode z₀ r k ∈ Ω) (n d : ℕ)
    (m : JetExponent n d) (k : ℕ) :
    ContinuousAt (domainSlopeSampleRow F z₀ r n d m k) 0 := by
  unfold domainSlopeSampleRow
  apply continuousAt_finsetProd' Finset.univ
  intro i _
  exact (continuousAt_translationSlopeJetVector_of_analyticOnNhd hF n (hnodes k) i).pow _

theorem continuousAt_domainSlopeMinorDet {F : ℂ → ℂ} {Ω : Set ℂ} (hF : AnalyticOnNhd ℂ F Ω)
    {z₀ : ℂ} {r : ℝ} (hnodes : ∀ k, domainSampleNode z₀ r k ∈ Ω) (n d : ℕ)
    (φ : JetExponent n d → ℕ) :
    ContinuousAt (domainSlopeMinorDet F z₀ r n d φ) 0 := by
  have hcont : ContinuousAt (fun h : ℂ =>
      ∑ σ : Equiv.Perm (JetExponent n d), (Equiv.Perm.sign σ : ℂ) *
        ∏ i : JetExponent n d, domainSlopeMinor F z₀ r n d φ h (σ i) i) 0 := by
    apply continuousAt_finsetSum' Finset.univ
    intro σ _
    apply continuousAt_const.mul
    apply continuousAt_finsetProd' Finset.univ
    intro i _
    exact continuousAt_domainSlopeSampleRow hF hnodes n d i (φ (σ i))
  change ContinuousAt (fun h => (domainSlopeMinor F z₀ r n d φ h).det) 0
  simpa only [Matrix.det_apply'] using hcont

/-! ### The normalization identity away from `h = 0` -/

theorem domainSlopeSampleRow_of_ne {F : ℂ → ℂ} {Ω : Set ℂ} (hF : AnalyticOnNhd ℂ F Ω)
    {z₀ : ℂ} {r : ℝ} (hnodes : ∀ k, domainSampleNode z₀ r k ∈ Ω) (n d : ℕ)
    (m : JetExponent n d) (k : ℕ) {h : ℂ} (hh : h ≠ 0)
    (hshift : domainSampleNode z₀ r k + h ∈ Ω) :
    domainSlopeSampleRow F z₀ r n d m k h =
      h⁻¹ ^ jetValueDegree m *
        domainJetSampleRow (fun z => F (z + h) - F z) z₀ r n d m k := by
  classical
  set a : ℂ := domainSampleNode z₀ r k with ha
  let A : Fin (n + 1) → ℂ := fun j =>
    iteratedDeriv (j : ℕ) F (a + h) - iteratedDeriv (j : ℕ) F a
  have hFa : AnalyticAt ℂ F a := hF a (hnodes k)
  have hFah : AnalyticAt ℂ F (a + h) := hF (a + h) hshift
  have hraw : domainJetSampleRow (fun z => F (z + h) - F z) z₀ r n d m k =
      a ^ (m 0 : ℕ) * ∏ j : Fin (n + 1), A j ^ (m j.succ : ℕ) := by
    rw [domainJetSampleRow, jetMon, Fin.prod_univ_succ]
    simp only [entireJetVector, Fin.cons_zero, Fin.cons_succ]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    dsimp only [A]
    have htrans : ContDiffAt ℂ (j : ℕ) (fun z => F (z + h)) a := by
      have hcomp : AnalyticAt ℂ (fun z : ℂ => F (z + h)) a := by
        have hinner : AnalyticAt ℂ (fun z : ℂ => z + h) a := analyticAt_id.add analyticAt_const
        have hcomp0 : AnalyticAt ℂ (F ∘ fun z : ℂ => z + h) a :=
          AnalyticAt.comp (𝕜 := ℂ) (g := F) (f := fun z : ℂ => z + h) (x := a) hFah hinner
        exact hcomp0
      exact hcomp.contDiffAt
    have hbase : ContDiffAt ℂ (j : ℕ) F a := hFa.contDiffAt
    rw [show (fun z => F (z + h) - F z) = (fun z => F (z + h)) - F from rfl]
    congr 1
    rw [iteratedDeriv_sub htrans hbase, iteratedDeriv_comp_add_right]
  have hscaled : (∏ j : Fin (n + 1), (h⁻¹ * A j) ^ (m j.succ : ℕ)) =
      h⁻¹ ^ jetValueDegree m * ∏ j : Fin (n + 1), A j ^ (m j.succ : ℕ) := by
    simp only [mul_pow]
    rw [Finset.prod_mul_distrib, jetValueDegree, Finset.prod_pow_eq_pow_sum]
  rw [domainSlopeSampleRow, translationSlopeJetVector_of_ne n hh, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [hscaled, hraw]
  ring

theorem domainSlopeMinor_eq_mul_diagonal {F : ℂ → ℂ} {Ω : Set ℂ} (hF : AnalyticOnNhd ℂ F Ω)
    {z₀ : ℂ} {r : ℝ} (hnodes : ∀ k, domainSampleNode z₀ r k ∈ Ω) (n d : ℕ)
    (φ : JetExponent n d → ℕ) {h : ℂ} (hh : h ≠ 0)
    (hshift : ∀ k, domainSampleNode z₀ r k + h ∈ Ω) :
    domainSlopeMinor F z₀ r n d φ h =
      coordinateMinor (domainJetSampleRow (fun z => F (z + h) - F z) z₀ r n d) φ *
        Matrix.diagonal (fun m : JetExponent n d => h⁻¹ ^ jetValueDegree m) := by
  classical
  ext i j
  rw [domainSlopeMinor, Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · simp [domainSlopeSampleRow_of_ne hF hnodes n d j (φ i) hh (hshift (φ i)), coordinateMinor]
    ring
  · intro b _ hbj
    simp [Matrix.diagonal, hbj]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem domainSlopeMinorDet_eq_mul {F : ℂ → ℂ} {Ω : Set ℂ} (hF : AnalyticOnNhd ℂ F Ω)
    {z₀ : ℂ} {r : ℝ} (hnodes : ∀ k, domainSampleNode z₀ r k ∈ Ω) (n d : ℕ)
    (φ : JetExponent n d → ℕ) {h : ℂ} (hh : h ≠ 0)
    (hshift : ∀ k, domainSampleNode z₀ r k + h ∈ Ω) :
    domainSlopeMinorDet F z₀ r n d φ h =
      (coordinateMinor (domainJetSampleRow (fun z => F (z + h) - F z) z₀ r n d) φ).det *
        ∏ m : JetExponent n d, h⁻¹ ^ jetValueDegree m := by
  rw [domainSlopeMinorDet, domainSlopeMinor_eq_mul_diagonal hF hnodes n d φ hh hshift,
    Matrix.det_mul, Matrix.det_diagonal]

/-! ### Antiderivatives on a domain -/

/-- **A function whose derivative satisfies an algebraic differential equation on a set satisfies
one there itself.** -/
theorem differentiallyAlgebraicOn_of_deriv {f : ℂ → ℂ} {Ω : Set ℂ}
    (hf : DifferentiallyAlgebraicOn (deriv f) Ω) : DifferentiallyAlgebraicOn f Ω := by
  obtain ⟨n, P, hP, hrel⟩ := hf
  refine ⟨n + 1, MvPolynomial.rename (jetShiftIndex n) P, ?_, ?_⟩
  · exact fun h =>
      hP (MvPolynomial.rename_injective _ (jetShiftIndex_injective n) (by simpa using h))
  · intro z hz
    rw [MvPolynomial.eval_rename]
    have hcomp : (Fin.cons z (fun j : Fin (n + 2) => iteratedDeriv (j : ℕ) f z) :
          Fin (n + 3) → ℂ) ∘ jetShiftIndex n
        = Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (deriv f) z) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp [jetShiftIndex]
      · intro j
        have hne : (Fin.succ j : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero j
        simp only [Function.comp_apply, jetShiftIndex, if_neg hne, Fin.cons_succ]
        rw [Fin.val_succ, iteratedDeriv_succ']
    rw [hcomp]
    exact hrel z hz

/-! ### The uniform branch on a domain -/

/-- Uniform bounded-complexity relations for all small translation defects force the derivative of
the source to satisfy an algebraic differential equation on the whole domain. -/
theorem differentiallyAlgebraicOn_deriv_of_uniform_domain_translation_relations
    {F : ℂ → ℂ} {Ω : Set ℂ} (hconn : IsPreconnected Ω) (hF : AnalyticOnNhd ℂ F Ω)
    {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hz₀ : z₀ ∈ Ω)
    (hnodes : ∀ k, domainSampleNode z₀ r k ∈ Ω)
    {n d : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (hshift : ∀ h : ℂ, ‖h‖ < ρ → ∀ k, domainSampleNode z₀ r k + h ∈ Ω)
    (hrel : ∀ (φ : JetExponent n d → ℕ) (h : ℂ), ‖h‖ < ρ →
      (coordinateMinor (domainJetSampleRow (fun z => F (z + h) - F z) z₀ r n d) φ).det = 0) :
    DifferentiallyAlgebraicOn (deriv F) Ω := by
  refine (differentiallyAlgebraicOn_iff_forall_coordinateMinor_det_eq_zero hconn hF.deriv hz₀
    hnodes hr).2 ⟨n, d, fun φ => ?_⟩
  rw [← domainSlopeMinorDet_zero]
  set t : ℕ → ℂ := domainSampleNode 0 ρ with ht
  have htnorm : ∀ k, ‖t k‖ < ρ := by
    intro k
    have := dist_domainSampleNode (0 : ℂ) hρ k
    rw [dist_zero_right] at this
    rw [ht, this]
    have h2 : (1:ℝ) < (k : ℝ) + 2 := by
      have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    calc ρ / ((k:ℝ) + 2) < ρ / 1 := div_lt_div_of_pos_left hρ one_pos h2
      _ = ρ := by ring
  have htne : ∀ k, t k ≠ 0 := fun k => by
    simpa using domainSampleNode_ne (0 : ℂ) hρ k
  have htend : Tendsto t atTop (𝓝 (0 : ℂ)) :=
    (tendsto_domainSampleNode (0 : ℂ) hρ).mono_right inf_le_left
  have hslope : Tendsto (fun k : ℕ => domainSlopeMinorDet F z₀ r n d φ (t k)) atTop
      (𝓝 (domainSlopeMinorDet F z₀ r n d φ 0)) :=
    (continuousAt_domainSlopeMinorDet hF hnodes n d φ).tendsto.comp htend
  have hslope0 : Tendsto (fun k : ℕ => domainSlopeMinorDet F z₀ r n d φ (t k)) atTop (𝓝 0) := by
    have hz : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0) := tendsto_const_nhds
    refine hz.congr' ?_
    filter_upwards with k
    rw [domainSlopeMinorDet_eq_mul hF hnodes n d φ (htne k) (hshift (t k) (htnorm k)),
      hrel φ (t k) (htnorm k), zero_mul]
  exact tendsto_nhds_unique hslope hslope0

end

end GaloisForLFunctions.HTGeometry
