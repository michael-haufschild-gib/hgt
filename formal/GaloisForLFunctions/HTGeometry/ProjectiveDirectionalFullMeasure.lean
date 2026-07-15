import GaloisForLFunctions.HTGeometry.ComplexPolynomialZeroMeasure
import GaloisForLFunctions.HTGeometry.UncountableDirectionalZariskiDichotomy
import Mathlib.Analysis.Real.Cardinality

/-!
# Full measure in every projective directional chart

The homogeneous finite-law equations are dehomogenized in an arbitrary projective chart.  If no
finite order is universal, uncountable-field polynomial avoidance supplies a complete-HT point in
each chart.  Consequently every chart-level finite-law locus is proper, hence Lebesgue-null, and
their countable union is null.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped LinearAlgebra.Projectivization

variable {K L : Type*} [Field K] [Field L]
  [Algebra ℂ K] [Algebra K L] [Algebra ℂ L] [IsScalarTower ℂ K L]
  [CharZero K]

/-- The point of projective law space represented by the chart vector with `i`th coordinate one. -/
def projectiveChartPoint {m : ℕ} (i : Fin (m + 1)) (c : Fin m → ℂ) :
    ℙ ℂ (Fin (m + 1) → ℂ) :=
  Projectivization.mk ℂ (i.insertNth 1 c) (by
    intro h
    have hi := congrFun h i
    simp at hi)

/-- Every finite-law locus pulled back to an arbitrary projective chart is a finite complex
polynomial zero locus. -/
theorem exists_projectiveDirectionalChartFiniteLawPolynomialFinset
    {m : ℕ} (i : Fin (m + 1))
    (δ : Fin (m + 1) → Derivation ℂ L L) (x : L) (n : ℕ) :
    ∃ P : Finset (MvPolynomial (Fin m) ℂ),
      finitePolynomialZeroLocus P =
        {c | projectiveChartPoint i c ∈
          projectiveDirectionalFiniteLawLocus (K := K) δ x n} := by
  classical
  obtain ⟨Q, hQ⟩ :=
    exists_directionalFiniteLawPolynomialFinset (K := K) δ x n
  let P : Finset (MvPolynomial (Fin m) ℂ) := Q.image (dehomogenizeAt i)
  refine ⟨P, ?_⟩
  ext c
  change (∀ p ∈ P, MvPolynomial.eval c p = 0) ↔ _
  simp only [Set.mem_setOf_eq]
  rw [show projectiveChartPoint i c =
      Projectivization.mk ℂ (i.insertNth 1 c) (by
        intro h
        have hi := congrFun h i
        simp at hi) by rfl,
    mk_mem_projectiveDirectionalFiniteLawLocus_iff]
  rw [← hQ (i.insertNth 1 c)]
  constructor
  · intro h q hq
    rw [← eval_dehomogenizeAt]
    exact h (dehomogenizeAt i q) (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  · intro h p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    rw [eval_dehomogenizeAt]
    exact h q hq

/-- **Complex projective directional full-measure dichotomy.** Either one finite jet order is
dependent in every projective direction, or complete-HT directions have full Lebesgue measure in
every standard projective chart. -/
theorem complexProjectiveDirectionalFiniteLaw_collapse_or_fullMeasureInEveryChart
    (m : ℕ) (δ : Fin (m + 1) → Derivation ℂ L L) (x : L) :
    (∃ N, projectiveDirectionalFiniteLawLocus (K := K) δ x N = Set.univ) ∨
      ∀ i : Fin (m + 1),
        volume {c : Fin m → ℂ |
          projectiveChartPoint i c ∉ projectiveDirectionalHTLocus (K := K) δ x} = 0 := by
  classical
  letI : Uncountable ℂ := Complex.ofReal_injective.uncountable
  by_cases hcollapse :
      ∃ N, projectiveDirectionalFiniteLawLocus (K := K) δ x N = Set.univ
  · exact Or.inl hcollapse
  · right
    have hzariski :=
      projectiveDirectionalFiniteLaw_collapse_or_zariskiDense (K := K) m δ x
    rcases hzariski with hbad | hzariski
    · exact False.elim (hcollapse hbad)
    intro i
    obtain ⟨c, hc, hci, hcHT⟩ :=
      hzariski (MvPolynomial.X i) (MvPolynomial.X_ne_zero i)
    have hci' : c i ≠ 0 := by
      simpa using hci
    let a : ℂ := (c i)⁻¹
    have ha : a ≠ 0 := inv_ne_zero hci'
    let d : Fin (m + 1) → ℂ := a • c
    have hdi : d i = 1 := by
      simp [d, a, hci']
    let u : Fin m → ℂ := i.removeNth d
    have hrepr : i.insertNth 1 u = d := by
      rw [show u = i.removeNth d by rfl, Fin.insertNth_removeNth]
      exact Function.update_eq_self_iff.mpr hdi.symm
    have hcAI : AlgebraicIndependent K (fun n : ℕ ↦ directionalJet δ c n x) :=
      (mk_mem_projectiveDirectionalHTLocus_iff δ x c hc).mp hcHT
    have hdAI : AlgebraicIndependent K (fun n : ℕ ↦ directionalJet δ d n x) := by
      exact (directionalJet_algebraicIndependent_smul_iff_over δ c ha x).mpr hcAI
    have huHT : projectiveChartPoint i u ∈
        projectiveDirectionalHTLocus (K := K) δ x := by
      rw [show projectiveChartPoint i u =
          Projectivization.mk ℂ (i.insertNth 1 u) (by
            intro h
            have hi := congrFun h i
            simp at hi) by rfl,
        mk_mem_projectiveDirectionalHTLocus_iff, hrepr]
      exact hdAI
    choose P hP using fun n ↦
      exists_projectiveDirectionalChartFiniteLawPolynomialFinset (K := K) i δ x n
    have hproper : ∀ n, finitePolynomialZeroLocus (P n) ≠ Set.univ := by
      intro n hn
      have hu : u ∈ finitePolynomialZeroLocus (P n) := by
        rw [hn]
        exact Set.mem_univ u
      rw [hP n] at hu
      have hunot : projectiveChartPoint i u ∉
          projectiveDirectionalHTLocus (K := K) δ x :=
        (not_mem_projectiveDirectionalHTLocus_iff_exists_finiteLaw δ x _).mpr ⟨n, hu⟩
      exact hunot huHT
    rcases finitePolynomialZeroLoci_collapse_or_fullMeasure_fin P with hbad | hnull
    · obtain ⟨n, hn⟩ := hbad
      exact False.elim (hproper n hn)
    · have hset : {c : Fin m → ℂ |
          projectiveChartPoint i c ∉ projectiveDirectionalHTLocus (K := K) δ x} =
          {c | ∃ n, c ∈ finitePolynomialZeroLocus (P n)} := by
        ext c
        simp only [Set.mem_setOf_eq]
        rw [not_mem_projectiveDirectionalHTLocus_iff_exists_finiteLaw]
        apply exists_congr
        intro n
        rw [hP n]
        rfl
      rw [hset]
      exact hnull

/-- Under the generic alternative, the complete-HT locus meets every standard projective chart. -/
theorem exists_projectiveChartPoint_mem_projectiveDirectionalHTLocus
    (m : ℕ) (δ : Fin (m + 1) → Derivation ℂ L L) (x : L)
    (hcollapse : ¬∃ N,
      projectiveDirectionalFiniteLawLocus (K := K) δ x N = Set.univ)
    (i : Fin (m + 1)) :
    ∃ u : Fin m → ℂ,
      projectiveChartPoint i u ∈ projectiveDirectionalHTLocus (K := K) δ x := by
  classical
  letI : Uncountable ℂ := Complex.ofReal_injective.uncountable
  rcases projectiveDirectionalFiniteLaw_collapse_or_zariskiDense (K := K) m δ x with
    hbad | hzariski
  · exact False.elim (hcollapse hbad)
  · obtain ⟨c, hc, hci, hcHT⟩ :=
      hzariski (MvPolynomial.X i) (MvPolynomial.X_ne_zero i)
    have hci' : c i ≠ 0 := by
      simpa using hci
    let a : ℂ := (c i)⁻¹
    have ha : a ≠ 0 := inv_ne_zero hci'
    let d : Fin (m + 1) → ℂ := a • c
    have hdi : d i = 1 := by
      simp [d, a, hci']
    let u : Fin m → ℂ := i.removeNth d
    have hrepr : i.insertNth 1 u = d := by
      rw [show u = i.removeNth d by rfl, Fin.insertNth_removeNth]
      exact Function.update_eq_self_iff.mpr hdi.symm
    have hcAI : AlgebraicIndependent K (fun n : ℕ ↦ directionalJet δ c n x) :=
      (mk_mem_projectiveDirectionalHTLocus_iff δ x c hc).mp hcHT
    have hdAI : AlgebraicIndependent K (fun n : ℕ ↦ directionalJet δ d n x) :=
      (directionalJet_algebraicIndependent_smul_iff_over δ c ha x).mpr hcAI
    refine ⟨u, ?_⟩
    rw [show projectiveChartPoint i u =
        Projectivization.mk ℂ (i.insertNth 1 u) (by
          intro h
          have hi := congrFun h i
          simp at hi) by rfl,
      mk_mem_projectiveDirectionalHTLocus_iff, hrepr]
    exact hdAI

/-- If no finite order is universal, every chart admits a countable polynomial presentation by
proper finite-law loci. -/
theorem exists_projectiveDirectionalChartProperPolynomialFamily
    (m : ℕ) (δ : Fin (m + 1) → Derivation ℂ L L) (x : L)
    (hcollapse : ¬∃ N,
      projectiveDirectionalFiniteLawLocus (K := K) δ x N = Set.univ)
    (i : Fin (m + 1)) :
    ∃ P : ℕ → Finset (MvPolynomial (Fin m) ℂ),
      (∀ n, finitePolynomialZeroLocus (P n) =
        {c | projectiveChartPoint i c ∈
          projectiveDirectionalFiniteLawLocus (K := K) δ x n}) ∧
      ∀ n, finitePolynomialZeroLocus (P n) ≠ Set.univ := by
  classical
  obtain ⟨u, huHT⟩ :=
    exists_projectiveChartPoint_mem_projectiveDirectionalHTLocus
      (K := K) m δ x hcollapse i
  choose P hP using fun n ↦
    exists_projectiveDirectionalChartFiniteLawPolynomialFinset (K := K) i δ x n
  refine ⟨P, hP, ?_⟩
  intro n hn
  have hu : u ∈ finitePolynomialZeroLocus (P n) := by
    rw [hn]
    exact Set.mem_univ u
  rw [hP n] at hu
  have hunot : projectiveChartPoint i u ∉
      projectiveDirectionalHTLocus (K := K) δ x :=
    (not_mem_projectiveDirectionalHTLocus_iff_exists_finiteLaw δ x _).mpr ⟨n, hu⟩
  exact hunot huHT

/-- Over the complex numbers, the generic alternative is dense residual in every standard
projective chart, not merely in affine law-coordinate space. -/
theorem complexProjectiveDirectionalFiniteLaw_collapse_or_denseResidualInEveryChart
    (m : ℕ) (δ : Fin (m + 1) → Derivation ℂ L L) (x : L) :
    (∃ N, projectiveDirectionalFiniteLawLocus (K := K) δ x N = Set.univ) ∨
      ∀ i : Fin (m + 1),
        Dense {c : Fin m → ℂ |
          projectiveChartPoint i c ∈ projectiveDirectionalHTLocus (K := K) δ x} ∧
        {c : Fin m → ℂ |
          projectiveChartPoint i c ∈ projectiveDirectionalHTLocus (K := K) δ x} ∈
            residual (Fin m → ℂ) := by
  classical
  by_cases hcollapse :
      ∃ N, projectiveDirectionalFiniteLawLocus (K := K) δ x N = Set.univ
  · exact Or.inl hcollapse
  · right
    intro i
    obtain ⟨P, hP, hproper⟩ :=
      exists_projectiveDirectionalChartProperPolynomialFamily
        (K := K) m δ x hcollapse i
    rcases finitePolynomialZeroLoci_collapse_or_denseResidual P with hbad | hgeneric
    · obtain ⟨n, hn⟩ := hbad
      exact False.elim (hproper n hn)
    · have hset : {c : Fin m → ℂ |
          ∀ n, c ∉ finitePolynomialZeroLocus (P n)} =
          {c | projectiveChartPoint i c ∈
            projectiveDirectionalHTLocus (K := K) δ x} := by
        ext c
        simp only [Set.mem_setOf_eq]
        constructor
        · intro havoid
          by_contra hnot
          obtain ⟨n, hn⟩ :=
            (not_mem_projectiveDirectionalHTLocus_iff_exists_finiteLaw δ x _).mp hnot
          exact havoid n (by rwa [hP n])
        · intro hHT n hn
          have hfin : projectiveChartPoint i c ∈
              projectiveDirectionalFiniteLawLocus (K := K) δ x n := by
            have hn' : c ∈ {c | projectiveChartPoint i c ∈
                projectiveDirectionalFiniteLawLocus (K := K) δ x n} := by
              rw [← hP n]
              exact hn
            exact hn'
          have hnot :=
            (not_mem_projectiveDirectionalHTLocus_iff_exists_finiteLaw δ x _).mpr
              ⟨n, hfin⟩
          exact hnot hHT
      simpa [hset] using hgeneric

end

end GaloisForLFunctions.HTGeometry
