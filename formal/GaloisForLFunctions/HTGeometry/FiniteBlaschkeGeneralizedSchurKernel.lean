import GaloisForLFunctions.HTGeometry.FiniteBlaschkeAdjointDefect
import GaloisForLFunctions.HTGeometry.HardyDiskKernelContinuity
import GaloisForLFunctions.RHTower.AnalyticKernelUniquenessRegion

open Complex Set Metric Topology
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Bounded Hermitian operator whose quadratic form is the finite generalized-Schur defect. -/
def finiteBlaschkeGeneralizedSchurOperator (F : DiskMultiplier) (B : FiniteBlaschke) :
    HardyDisk →L[ℂ] HardyDisk :=
  (finiteBlaschkeMul B).comp (ContinuousLinearMap.adjoint (finiteBlaschkeMul B)) -
    (hardyMul F).comp (ContinuousLinearMap.adjoint (hardyMul F))

/-- Reproducing kernels are adjoint eigenvectors of every Hardy multiplier. -/
theorem adjoint_hardyMul_hardyKernel (F : DiskMultiplier) {a : ℂ} (ha : ‖a‖ < 1) :
    ContinuousLinearMap.adjoint (hardyMul F) (hardyKernel ha) =
      (starRingEnd ℂ) (F.fn a) • hardyKernel ha := by
  refine ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, inner_hardyKernel,
    hardyFun_hardyMul F x ha, inner_smul_left, inner_hardyKernel]
  simp

theorem finiteBlaschkeGeneralizedSchurOperator_hermitian
    (F : DiskMultiplier) (B : FiniteBlaschke) (x y : HardyDisk) :
    inner ℂ x (finiteBlaschkeGeneralizedSchurOperator F B y) =
      inner ℂ (finiteBlaschkeGeneralizedSchurOperator F B x) y := by
  have hself : ∀ (A : HardyDisk →L[ℂ] HardyDisk) (u v : HardyDisk),
      inner ℂ u (A (ContinuousLinearMap.adjoint A v)) =
        inner ℂ (A (ContinuousLinearMap.adjoint A u)) v := by
    intro A u v
    calc
      inner ℂ u (A (ContinuousLinearMap.adjoint A v)) =
          inner ℂ (ContinuousLinearMap.adjoint A u)
            (ContinuousLinearMap.adjoint A v) :=
        (ContinuousLinearMap.adjoint_inner_left A
          (ContinuousLinearMap.adjoint A v) u).symm
      _ = inner ℂ (A (ContinuousLinearMap.adjoint A u)) v :=
        ContinuousLinearMap.adjoint_inner_right A
          (ContinuousLinearMap.adjoint A u) v
  simp only [finiteBlaschkeGeneralizedSchurOperator, sub_apply,
    ContinuousLinearMap.comp_apply, inner_sub_right, inner_sub_left]
  rw [hself (finiteBlaschkeMul B), hself (hardyMul F)]

theorem finiteBlaschkeGeneralizedSchurOperator_quadratic
    (F : DiskMultiplier) (B : FiniteBlaschke) (x : HardyDisk) :
    (inner ℂ x (finiteBlaschkeGeneralizedSchurOperator F B x)).re =
      finiteBlaschkeGeneralizedSchurForm F B x := by
  have hnorm : ∀ (A : HardyDisk →L[ℂ] HardyDisk),
      (inner ℂ x (A (ContinuousLinearMap.adjoint A x))).re =
        ‖ContinuousLinearMap.adjoint A x‖ ^ (2 : ℕ) := by
    intro A
    rw [show inner ℂ x (A (ContinuousLinearMap.adjoint A x)) =
        inner ℂ (ContinuousLinearMap.adjoint A x)
          (ContinuousLinearMap.adjoint A x) by
      exact (ContinuousLinearMap.adjoint_inner_left A
        (ContinuousLinearMap.adjoint A x) x).symm]
    exact (InnerProductSpace.norm_sq_eq_re_inner
      (𝕜 := ℂ) (ContinuousLinearMap.adjoint A x)).symm
  simp only [finiteBlaschkeGeneralizedSchurOperator, sub_apply,
    ContinuousLinearMap.comp_apply, inner_sub_right, Complex.sub_re]
  rw [hnorm (finiteBlaschkeMul B), hnorm (hardyMul F),
    finiteBlaschkeGeneralizedSchurForm_eq_adjoint_energy_difference]

/-- Analytic Szegő section, totalized by zero outside the disk. -/
def analyticHardyKernelSection (z : ℂ) : HardyDisk :=
  if hz : ‖z‖ < 1 then hardyKernel (by simpa using hz) else 0

theorem analyticHardyKernelSection_eq {z : ℂ} (hz : ‖z‖ < 1) :
    analyticHardyKernelSection z = hardyKernel hz := by
  rw [analyticHardyKernelSection, dif_pos hz]

/-- Coefficientwise conjugation inside the Hardy coefficient model. -/
def hardyCoefficientConj (w : HardyDisk) : HardyDisk :=
  ⟨fun n => (starRingEnd ℂ) (w n), by
    have hw := w.property
    change Memℓp (fun n : ℕ => w n) 2 at hw
    change Memℓp (fun n : ℕ => (starRingEnd ℂ) (w n)) 2
    rw [memℓp_gen_iff (by norm_num)] at hw ⊢
    simpa only [norm_conj] using hw⟩

theorem inner_analyticHardyKernelSection (w : HardyDisk) {z : ℂ} (hz : ‖z‖ < 1) :
    inner ℂ w (analyticHardyKernelSection ((starRingEnd ℂ) z)) =
      hardyFun (hardyCoefficientConj w) z := by
  rw [analyticHardyKernelSection_eq (by simpa using hz), ← inner_conj_symm,
    inner_hardyKernel]
  rw [hardyFun, hardyFun]
  have hsum : Summable (fun n : ℕ => w n * (starRingEnd ℂ) z ^ n) :=
    summable_hardyDisk_terms w (by simpa using hz)
  calc
    (starRingEnd ℂ) (∑' n : ℕ, w n * (starRingEnd ℂ) z ^ n) =
        ∑' n : ℕ, (starRingEnd ℂ) (w n * (starRingEnd ℂ) z ^ n) :=
      hsum.map_tsum (starRingEnd ℂ) Complex.continuous_conj
    _ = ∑' n : ℕ, (hardyCoefficientConj w) n * z ^ n := by
      apply tsum_congr
      intro n
      simp [hardyCoefficientConj]

theorem analyticOnNhd_inner_analyticHardyKernelSection (w : HardyDisk) :
    AnalyticOnNhd ℂ
      (fun z => inner ℂ w (analyticHardyKernelSection ((starRingEnd ℂ) z)))
      (Metric.ball 0 1) := by
  apply AnalyticOnNhd.congr Metric.isOpen_ball
    ((differentiableOn_hardyFun (hardyCoefficientConj w)).analyticOnNhd Metric.isOpen_ball)
  intro z hz
  exact (inner_analyticHardyKernelSection w
    (by simpa [Metric.mem_ball, dist_zero_right] using hz)).symm

theorem conjugateAnalyticHardyKernelSection_global_total :
    (Submodule.span ℂ
      ((fun z => analyticHardyKernelSection ((starRingEnd ℂ) z)) ''
        Metric.ball (0 : ℂ) 1)).topologicalClosure = ⊤ := by
  rw [RHTower.topologicalClosure_span_eq_top_iff]
  intro w hw
  have hfun : ∀ z : ℂ, ‖z‖ < 1 → hardyFun (hardyCoefficientConj w) z = 0 := by
    intro z hz
    rw [← inner_analyticHardyKernelSection w hz]
    apply hw
    exact ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using hz, rfl⟩
  have hstar : hardyCoefficientConj w = 0 := by
    apply hardyDisk_ext
    intro z hz
    rw [hfun z hz]
    simp [hardyFun]
  apply lp.ext
  funext n
  have hn := congrArg (fun u : HardyDisk => u n) hstar
  simpa [hardyCoefficientConj] using congrArg (starRingEnd ℂ) hn

/-- Hardy realization of the finite generalized-Schur kernel. -/
def finiteBlaschkeGeneralizedSchurRealization (F : DiskMultiplier) (B : FiniteBlaschke) :
    RHTower.AnalyticHermitianKernelRealization HardyDisk where
  domain := Metric.ball 0 1
  kernelSection := fun z => analyticHardyKernelSection ((starRingEnd ℂ) z)
  domain_preconnected := convex_ball 0 1 |>.isPreconnected
  coefficient_analytic := analyticOnNhd_inner_analyticHardyKernelSection
  global_total := conjugateAnalyticHardyKernelSection_global_total
  form := finiteBlaschkeGeneralizedSchurOperator F B
  form_hermitian := finiteBlaschkeGeneralizedSchurOperator_hermitian F B

/-- Schwarz-reflected disk multiplier value, matching the analytic section orientation. -/
def reflectedDiskMultiplierValue (F : DiskMultiplier) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (F.fn ((starRingEnd ℂ) z))

/-- Literal generalized-Schur defect kernel on the disk. -/
def finiteBlaschkeGeneralizedSchurKernel
    (F : DiskMultiplier) (B : FiniteBlaschke) (z w : ℂ) : ℂ :=
  (reflectedDiskMultiplierValue B.toMultiplier z *
      (starRingEnd ℂ) (reflectedDiskMultiplierValue B.toMultiplier w) -
    reflectedDiskMultiplierValue F z *
      (starRingEnd ℂ) (reflectedDiskMultiplierValue F w)) /
    (1 - z * (starRingEnd ℂ) w)

theorem finiteBlaschkeGeneralizedSchurRealization_kernel_eq
    (F : DiskMultiplier) (B : FiniteBlaschke) {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    (finiteBlaschkeGeneralizedSchurRealization F B).kernel z w =
      finiteBlaschkeGeneralizedSchurKernel F B z w := by
  have hzc : ‖(starRingEnd ℂ) z‖ < 1 := by simpa using hz
  have hwc : ‖(starRingEnd ℂ) w‖ < 1 := by simpa using hw
  rw [RHTower.AnalyticHermitianKernelRealization.kernel,
    finiteBlaschkeGeneralizedSchurRealization]
  simp only [finiteBlaschkeGeneralizedSchurOperator, sub_apply,
    ContinuousLinearMap.comp_apply, inner_sub_right,
    analyticHardyKernelSection_eq hzc, analyticHardyKernelSection_eq hwc]
  change inner ℂ (hardyKernel hwc)
      (hardyMul B.toMultiplier
        (ContinuousLinearMap.adjoint (hardyMul B.toMultiplier) (hardyKernel hzc))) -
    inner ℂ (hardyKernel hwc)
      (hardyMul F (ContinuousLinearMap.adjoint (hardyMul F) (hardyKernel hzc))) = _
  rw [adjoint_hardyMul_hardyKernel B.toMultiplier hzc,
    adjoint_hardyMul_hardyKernel F hzc, map_smul, map_smul,
    inner_smul_right, inner_smul_right,
    inner_hardyKernel hwc,
    hardyFun_hardyMul B.toMultiplier (hardyKernel hzc) hwc,
    inner_hardyKernel hwc,
    hardyFun_hardyMul F (hardyKernel hzc) hwc,
    hardyFun_hardyKernel hwc hzc]
  rw [finiteBlaschkeGeneralizedSchurKernel]
  simp only [reflectedDiskMultiplierValue, FiniteBlaschke.toMultiplier]
  simp
  rw [div_eq_mul_inv]
  ring

/-! ## Exact negative squares of literal finite kernel packets -/

/-- Linear synthesis of a finite tuple. -/
def finiteTupleSynthesisLinear {r : ℕ} (v : Fin r → HardyDisk) :
    (Fin r → ℂ) →ₗ[ℂ] HardyDisk where
  toFun := fun c => ∑ i, c i • v i
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum]

@[simp]
theorem finiteTupleSynthesisLinear_apply {r : ℕ} (v : Fin r → HardyDisk)
    (c : Fin r → ℂ) :
    finiteTupleSynthesisLinear v c = RHTower.AnalyticHermitianKernelRealization.sectionSynthesis v c :=
  rfl

theorem finiteTupleSynthesisLinear_injective {r : ℕ} {v : Fin r → HardyDisk}
    (hv : LinearIndependent ℂ v) : Function.Injective (finiteTupleSynthesisLinear v) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  apply funext
  intro i
  change ∑ j, c j • v j = 0 at hc
  exact (Fintype.linearIndependent_iff.mp hv c hc) i

theorem finrank_range_finiteTupleSynthesisLinear {r : ℕ} {v : Fin r → HardyDisk}
    (hv : LinearIndependent ℂ v) :
    Module.finrank ℂ (LinearMap.range (finiteTupleSynthesisLinear v)) = r := by
  have hker : LinearMap.ker (finiteTupleSynthesisLinear v) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (finiteTupleSynthesisLinear_injective hv)
  have hrank := LinearMap.finrank_range_add_finrank_ker (finiteTupleSynthesisLinear v)
  rw [hker, finrank_bot, add_zero, Module.finrank_fin_fun] at hrank
  exact hrank

/-- No literal finite Gram packet has more negative directions than the finite Blaschke degree. -/
theorem finiteBlaschkeGeneralizedSchur_finiteGram_negativeDimension_le
    (F : DiskMultiplier) (B : FiniteBlaschke) (hF : F.bd ≤ 1)
    (hcop : HardyCoprimeWithFiniteBlaschke F B) {r : ℕ}
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
  have hexact := finiteBlaschkeGeneralizedSchurForm_hasExactNegativeIndex_of_coprime
    F B hF hcop
  rw [← hWrank]
  exact hexact.2 W hWneg

/-- The degree-many negative directions are visible in one literal finite Gram packet. -/
theorem finiteBlaschkeGeneralizedSchur_hasFiniteGramNegativeDimension
    (F : DiskMultiplier) (B : FiniteBlaschke)
    (hcop : HardyCoprimeWithFiniteBlaschke F B) :
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
      (adjoint_hardyMul_domRestrict_finiteBlaschkeModelSpace_injective_of_coprime
        F B hcop)
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

/-- Multiplicity-aware finite Krein--Langer theorem in literal kernel-Gram language. -/
theorem finiteBlaschkeGeneralizedSchurKernel_exactNegativeSquares
    (F : DiskMultiplier) (B : FiniteBlaschke) (hF : F.bd ≤ 1)
    (hcop : HardyCoprimeWithFiniteBlaschke F B) :
    (finiteBlaschkeGeneralizedSchurRealization F B).HasFiniteGramNegativeDimensionOn
        (Metric.ball 0 1) B.deg ∧
      ∀ r : ℕ,
        (finiteBlaschkeGeneralizedSchurRealization F B).HasFiniteGramNegativeDimensionOn
          (Metric.ball 0 1) r → r ≤ B.deg := by
  exact ⟨finiteBlaschkeGeneralizedSchur_hasFiniteGramNegativeDimension F B hcop,
    fun _ => finiteBlaschkeGeneralizedSchur_finiteGram_negativeDimension_le F B hF hcop⟩

end GaloisForLFunctions.HTGeometry
