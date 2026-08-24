import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGeneralizedSchurKernel

open Complex
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The adjoint of a bounded analytic multiplier is faithful on a finite-Blaschke model space
when the multiplier is nonzero at every denominator zero, repetitions included. -/
theorem adjoint_hardyMul_eq_zero_of_mem_orthogonal_range_blaschkeOf :
    ∀ (k : ℕ) (a : Fin k → ℂ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
      (hle : ∀ j, ‖a j‖ ≤ c) (F : DiskMultiplier)
      (_hF : ∀ j, F.fn (a j) ≠ 0) (x : HardyDisk),
      x ∈ (LinearMap.range
        ((hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier :
          HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk))ᗮ →
      ContinuousLinearMap.adjoint (hardyMul F) x = 0 → x = 0
  | 0, a, c, hc0, hc1, hle, F, hF, x, hx, _ => by
      have hsurj : ∀ y : HardyDisk,
          hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier y = y := by
        intro y
        have hcong : hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier y =
            hardyMul DiskMultiplier.one y := by
          refine hardyMul_congr (fun z _ => ?_) y
          show (blaschkeOf a hc0 hc1 hle).fn z = 1
          exact blaschkeOf_zero_fn hc0 hc1 a hle z
        rw [hcong, hardyMul_one]
      have hrange : LinearMap.range
          ((hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier :
            HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk) = ⊤ := by
        refine LinearMap.range_eq_top.mpr fun y => ⟨y, ?_⟩
        exact hsurj y
      rw [hrange, Submodule.top_orthogonal_eq_bot] at hx
      exact hx
  | k + 1, a, c, hc0, hc1, hle, F, hF, x, hx, hxF => by
      let atail : Fin k → ℂ := fun j => a j.succ
      have h0 : ‖a 0‖ < 1 := lt_of_le_of_lt (hle 0) hc1
      let B0 : FiniteBlaschke := singleBlaschke h0
      let Btail : FiniteBlaschke :=
        blaschkeOf atail hc0 hc1 (fun j => hle j.succ)
      let T : HardyDisk →L[ℂ] HardyDisk := hardyMul B0.toMultiplier
      let y : HardyDisk := ContinuousLinearMap.adjoint T x
      have hyK : y ∈ (LinearMap.range
          ((hardyMul Btail.toMultiplier : HardyDisk →L[ℂ] HardyDisk) :
            HardyDisk →ₗ[ℂ] HardyDisk))ᗮ := by
        intro v hv
        obtain ⟨t, rfl⟩ := hv
        change (inner ℂ (hardyMul Btail.toMultiplier t) y : ℂ) = 0
        dsimp only [y]
        rw [ContinuousLinearMap.adjoint_inner_right]
        apply hx
        refine ⟨t, ?_⟩
        change hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier t =
          T (hardyMul Btail.toMultiplier t)
        exact hardyMul_blaschkeOf_succ a hc0 hc1 hle h0 t
      have hyF : ContinuousLinearMap.adjoint (hardyMul F) y = 0 := by
        refine ext_inner_right ℂ fun v => ?_
        rw [ContinuousLinearMap.adjoint_inner_left]
        change (inner ℂ (ContinuousLinearMap.adjoint T x) (hardyMul F v) : ℂ) = _
        rw [ContinuousLinearMap.adjoint_inner_left]
        have hcomm : T (hardyMul F v) = hardyMul F (T v) := by
          change hardyMul B0.toMultiplier (hardyMul F v) =
            hardyMul F (hardyMul B0.toMultiplier v)
          rw [hardyMul_mul, hardyMul_mul]
          apply hardyMul_congr
          · intro z _
            change B0.fn z * F.fn z = F.fn z * B0.fn z
            ring
        rw [hcomm, ← ContinuousLinearMap.adjoint_inner_left, hxF]
        simp
      have hy0 : y = 0 :=
        adjoint_hardyMul_eq_zero_of_mem_orthogonal_range_blaschkeOf
          k atail hc0 hc1 (fun j => hle j.succ) F (fun j => hF j.succ) y hyK hyF
      have hxK0 : x ∈ (LinearMap.range
          ((T : HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk))ᗮ := by
        intro v hv
        obtain ⟨t, rfl⟩ := hv
        calc
          (inner ℂ (T t) x : ℂ) =
              inner ℂ t (ContinuousLinearMap.adjoint T x) :=
            (ContinuousLinearMap.adjoint_inner_right T t x).symm
          _ = inner ℂ t y := rfl
          _ = 0 := by rw [hy0]; simp
      have hxspan : x ∈ ℂ ∙ hardyKernel h0 := by
        change x ∈ (LinearMap.range
          ((hardyMul (singleBlaschke h0).toMultiplier :
            HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk))ᗮ at hxK0
        rw [range_hardyMul_singleBlaschke h0,
          Submodule.orthogonal_orthogonal] at hxK0
        exact hxK0
      obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hxspan
      rw [← hd, map_smul, adjoint_hardyMul_hardyKernel F h0] at hxF
      have hconjF : (starRingEnd ℂ) (F.fn (a 0)) ≠ 0 :=
        (map_ne_zero (starRingEnd ℂ)).mpr (hF 0)
      have hnonzero :
          (starRingEnd ℂ) (F.fn (a 0)) • hardyKernel h0 ≠ 0 :=
        smul_ne_zero hconjF (hardyKernel_ne_zero h0)
      have hd0 : d = 0 := (smul_eq_zero.mp hxF).resolve_right hnonzero
      rw [← hd, hd0, zero_smul]

/-- Pointwise nonvanishing on the ordered zeros implies adjoint injectivity on the full model
space, including repeated factors. -/
theorem adjoint_hardyMul_domRestrict_finiteBlaschkeModelSpace_injective_of_nonzero
    (F : DiskMultiplier) (B : FiniteBlaschke)
    (hF : ∀ j : Fin B.deg, F.fn (B.zeros j) ≠ 0) :
    Function.Injective
      ((ContinuousLinearMap.adjoint (hardyMul F)).toLinearMap.domRestrict
        (finiteBlaschkeModelSpace B)) := by
  intro x y hxy
  have hsubMem : (x : HardyDisk) - (y : HardyDisk) ∈ finiteBlaschkeModelSpace B :=
    sub_mem x.property y.property
  have hsubAdj : ContinuousLinearMap.adjoint (hardyMul F)
      ((x : HardyDisk) - (y : HardyDisk)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  rcases B with ⟨k, a, c, hc0, hc1, hle⟩
  have hzero := adjoint_hardyMul_eq_zero_of_mem_orthogonal_range_blaschkeOf
    k a hc0 hc1 hle F hF ((x : HardyDisk) - (y : HardyDisk)) hsubMem hsubAdj
  exact Subtype.ext (sub_eq_zero.mp hzero)

/-- Pointwise denominator-zero nonvanishing gives the sharp upper bound for every literal finite
Gram packet. -/
theorem finiteBlaschkeGeneralizedSchur_finiteGram_negativeDimension_le_of_nonzero
    (F : DiskMultiplier) (B : FiniteBlaschke) (hFbd : F.bd ≤ 1)
    (hzero : ∀ j : Fin B.deg, F.fn (B.zeros j) ≠ 0) {r : ℕ}
    (hneg : (finiteBlaschkeGeneralizedSchurRealization F B).HasFiniteGramNegativeDimensionOn
      (Metric.ball 0 1) r) :
    r ≤ B.deg := by
  let R := finiteBlaschkeGeneralizedSchurRealization F B
  obtain ⟨d, hdneg⟩ := hneg
  let v : Fin r → HardyDisk := fun i =>
    R.finiteKernelCombination (Metric.ball 0 1) (d i)
  have hvneg : R.IsNegativeTuple v := hdneg
  have hvLI : LinearIndependent ℂ v := R.isNegativeTuple_linearIndependent hvneg
  let W : Submodule ℂ HardyDisk := LinearMap.range (finiteTupleSynthesisLinear v)
  have hWrank : Module.finrank ℂ W = r :=
    finrank_range_finiteTupleSynthesisLinear hvLI
  have hWneg : ∀ x ∈ W, x ≠ 0 →
      finiteBlaschkeGeneralizedSchurForm F B x < 0 := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := hx
    have hc0 : c ≠ 0 := by
      intro hc
      apply hx0
      rw [hc, map_zero]
    have hq := R.isNegativeTuple_quadratic_neg hvneg hc0
    change (inner ℂ
      (RHTower.AnalyticHermitianKernelRealization.sectionSynthesis v c)
      (finiteBlaschkeGeneralizedSchurOperator F B
        (RHTower.AnalyticHermitianKernelRealization.sectionSynthesis v c))).re < 0 at hq
    rw [finiteBlaschkeGeneralizedSchurOperator_quadratic] at hq
    simpa only [finiteTupleSynthesisLinear_apply] using hq
  have hinj := adjoint_hardyMul_domRestrict_finiteBlaschkeModelSpace_injective_of_nonzero
    F B hzero
  have hexact := finiteBlaschkeGeneralizedSchurForm_hasExactNegativeIndex
    F B hFbd hinj
  rw [← hWrank]
  exact hexact.2 W hWneg

/-- Denominator-zero nonvanishing exposes all degree-many negative directions in one literal
finite Gram packet. -/
theorem finiteBlaschkeGeneralizedSchur_hasFiniteGramNegativeDimension_of_nonzero
    (F : DiskMultiplier) (B : FiniteBlaschke)
    (hzero : ∀ j : Fin B.deg, F.fn (B.zeros j) ≠ 0) :
    (finiteBlaschkeGeneralizedSchurRealization F B).HasFiniteGramNegativeDimensionOn
      (Metric.ball 0 1) B.deg := by
  let R := finiteBlaschkeGeneralizedSchurRealization F B
  let K := finiteBlaschkeModelSpace B
  let b := Module.finBasis ℂ K
  let v : Fin (Module.finrank ℂ K) → HardyDisk := fun i => (b i : HardyDisk)
  have hvLI : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hcK : ∑ j, c j • b j = 0 := by
      apply Subtype.ext
      simpa [v] using hc
    exact (Fintype.linearIndependent_iff.mp b.linearIndependent c hcK) i
  have hinj := adjoint_hardyMul_domRestrict_finiteBlaschkeModelSpace_injective_of_nonzero
    F B hzero
  have hvneg : R.IsNegativeTuple v := by
    intro c hcunit
    have hc0 : c ≠ 0 := by
      intro hzero
      rw [hzero, norm_zero] at hcunit
      norm_num at hcunit
    have hsynth0 :
        RHTower.AnalyticHermitianKernelRealization.sectionSynthesis v c ≠ 0 := by
      intro hzero
      change ∑ i, c i • v i = 0 at hzero
      have hall := Fintype.linearIndependent_iff.mp hvLI c hzero
      exact hc0 (funext hall)
    have hsynthK :
        RHTower.AnalyticHermitianKernelRealization.sectionSynthesis v c ∈ K := by
      apply Submodule.sum_mem
      intro i _
      exact Submodule.smul_mem K (c i) (b i).property
    change (inner ℂ
      (RHTower.AnalyticHermitianKernelRealization.sectionSynthesis v c)
      (finiteBlaschkeGeneralizedSchurOperator F B
        (RHTower.AnalyticHermitianKernelRealization.sectionSynthesis v c))).re < 0
    rw [finiteBlaschkeGeneralizedSchurOperator_quadratic]
    exact projectedAdjointDefectForm_negative_on_projectionRange K (hardyMul F)
      hinj
      (RHTower.AnalyticHermitianKernelRealization.sectionSynthesis v c) hsynthK hsynth0
  have hglobal : R.HasNegativeDimensionOn (Metric.ball 0 1)
      (Module.finrank ℂ K) := by
    refine ⟨v, ?_, hvneg⟩
    intro i
    change v i ∈ (Submodule.span ℂ (R.kernelSection '' R.domain)).topologicalClosure
    rw [R.global_total]
    trivial
  have hfinite : R.HasFiniteGramNegativeDimensionOn (Metric.ball 0 1)
      (Module.finrank ℂ K) := by
    rw [R.hasFiniteGramNegativeDimensionOn_iff,
      R.hasFiniteSectionNegativeDimensionOn_iff]
    exact hglobal
  simpa [K, finrank_finiteBlaschkeModelSpace] using hfinite

/-- Multiplicity-aware finite Krein--Langer theorem under the intrinsic no-common-zero condition. -/
theorem finiteBlaschkeGeneralizedSchurKernel_exactNegativeSquares_of_nonzero
    (F : DiskMultiplier) (B : FiniteBlaschke) (hFbd : F.bd ≤ 1)
    (hzero : ∀ j : Fin B.deg, F.fn (B.zeros j) ≠ 0) :
    (finiteBlaschkeGeneralizedSchurRealization F B).HasFiniteGramNegativeDimensionOn
        (Metric.ball 0 1) B.deg ∧
      ∀ r : ℕ,
        (finiteBlaschkeGeneralizedSchurRealization F B).HasFiniteGramNegativeDimensionOn
          (Metric.ball 0 1) r → r ≤ B.deg := by
  exact ⟨finiteBlaschkeGeneralizedSchur_hasFiniteGramNegativeDimension_of_nonzero
      F B hzero,
    fun _ => finiteBlaschkeGeneralizedSchur_finiteGram_negativeDimension_le_of_nonzero
      F B hFbd hzero⟩

end GaloisForLFunctions.HTGeometry
