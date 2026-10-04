import GaloisForLFunctions.HTGeometry.HilbertSchmidtColumns
import GaloisForLFunctions.HTGeometry.PhaseResonanceProjection
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.HTGeometry.SquareIntegrableKernelOperator
import GaloisForLFunctions.HTGeometry.CyclicHeatOrbitSelection
import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect
import GaloisForLFunctions.RHTower.TraceClassCyclicity
import GaloisForLFunctions.RHTower.SoninPrincipalRelativeCyclicExtension

/-!
# Atomless phase formation: ideal escape

Let `(X, μ)` be a probability space and `ζ : X → S¹` measurable with atomless law `ζ_* μ`, and let
`U f = ζ f` on `H = L²(X, μ)`.  On Hilbert–Schmidt operators `α(T) = U* T U`, `δ = 1 - α`.

* **Ideal escape** (any unitary without eigenvectors).  For a nonzero positive trace-class `T`,
  every Cesàro formation `M_N(T)` is positive trace class with `tr M_N(T) = tr T` and
  `‖M_N(T)‖₁ = ‖T‖₁ > 0`, while `‖M_N(T)‖₂ → 0`; so `(M_N(T))` has no trace-norm limit.
* **Kernel model.**  On `L²(X × X)` the conjugation is multiplication by `ζ̄(x) ζ(y)`.  The
  resonance relation `{ζ(x) = ζ(y)}` is `μ × μ`-null; hence `ker δ = 0`, `δ` has dense range, is
  not bounded below and has nonclosed range; kernels supported where `|1 - ζ̄(x)ζ(y)| ≥ ε` have
  primitives of norm at most `ε⁻¹`, with no uniform bound; the Cesàro averages tend to zero.
* **Operator model.**  `U` is a unitary without eigenvectors and with approximate eigenvectors.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.ContinuousLinearMap

/-! ### Ideal escape for a unitary without eigenvectors -/

section IdealEscape

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem adjoint_unitaryCLM (V : E ≃ₗᵢ[ℂ] E) :
    ContinuousLinearMap.adjoint (unitaryCLM V) = unitaryCLM V.symm := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => ?_).symm
  simp only [unitaryCLM_apply]
  rw [inner_map_symm, LinearIsometryEquiv.symm_symm]

theorem hsConj_eq_conj_adjoint (U : E ≃ₗᵢ[ℂ] E) (T : E →L[ℂ] E) :
    hsConj U T = unitaryCLM U.symm ∘L T ∘L ContinuousLinearMap.adjoint (unitaryCLM U.symm) := by
  rw [adjoint_unitaryCLM, LinearIsometryEquiv.symm_symm]
  rfl

theorem isPositive_hsConj (U : E ≃ₗᵢ[ℂ] E) {T : E →L[ℂ] E} (hT : T.IsPositive) :
    (hsConj U T).IsPositive := by
  rw [hsConj_eq_conj_adjoint]
  exact hT.conj_adjoint _

omit [CompleteSpace E] in
theorem memSchattenClass_one_hsConj (U : E ≃ₗᵢ[ℂ] E) {T : E →L[ℂ] E}
    (hT : RHTower.MemSchattenClass 1 T) : RHTower.MemSchattenClass 1 (hsConj U T) :=
  RHTower.memSchattenClass_one_comp_left (RHTower.memSchattenClass_one_comp_right hT _) _

/-- Unitary conjugation preserves the trace of a trace-class operator. -/
theorem opTrace_hsConj (U : E ≃ₗᵢ[ℂ] E) {T : E →L[ℂ] E} (hT : RHTower.MemSchattenClass 1 T) :
    opTrace (hsConj U T) = opTrace T := by
  have h := RHTower.MemSchattenClass.one_opTrace_comp_comm
    (RHTower.memSchattenClass_one_comp_right hT (unitaryCLM U)) (unitaryCLM U.symm)
  have heq : (T ∘L unitaryCLM U) ∘L unitaryCLM U.symm = T := by
    ext x
    simp
  rw [heq] at h
  exact h

/-- The Cesàro partial sum `∑_{n<N} αⁿ(T)`. -/
def hsConjSum (U : E ≃ₗᵢ[ℂ] E) (N : ℕ) (T : E →L[ℂ] E) : E →L[ℂ] E :=
  ∑ n ∈ Finset.range N, (hsConj U)^[n] T

omit [CompleteSpace E] in
theorem hsCesaro_eq (U : E ≃ₗᵢ[ℂ] E) (N : ℕ) (T : E →L[ℂ] E) :
    hsCesaro U N T = (N : ℂ)⁻¹ • hsConjSum U N T := rfl

theorem hsConj_iterate_properties (U : E ≃ₗᵢ[ℂ] E) {T : E →L[ℂ] E}
    (hT : RHTower.MemSchattenClass 1 T) (hpos : T.IsPositive) (n : ℕ) :
    RHTower.MemSchattenClass 1 ((hsConj U)^[n] T) ∧ ((hsConj U)^[n] T).IsPositive ∧
      opTrace ((hsConj U)^[n] T) = opTrace T := by
  induction n with
  | zero => exact ⟨hT, hpos, rfl⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨memSchattenClass_one_hsConj U ih.1, isPositive_hsConj U ih.2.1,
        (opTrace_hsConj U ih.1).trans ih.2.2⟩

theorem hsConjSum_properties (U : E ≃ₗᵢ[ℂ] E) {T : E →L[ℂ] E}
    (hT : RHTower.MemSchattenClass 1 T) (hpos : T.IsPositive) (N : ℕ) :
    RHTower.MemSchattenClass 1 (hsConjSum U N T) ∧ (hsConjSum U N T).IsPositive ∧
      opTrace (hsConjSum U N T) = N * opTrace T := by
  induction N with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simpa [hsConjSum] using RHTower.memSchattenClass_one_smul hT 0
      · simp [hsConjSum, isPositive_zero]
      · simp [hsConjSum, opTrace]
  | succ N ih =>
      have hn := hsConj_iterate_properties U hT hpos N
      have hsum : hsConjSum U (N + 1) T = hsConjSum U N T + (hsConj U)^[N] T :=
        Finset.sum_range_succ _ N
      rw [hsum]
      refine ⟨RHTower.memSchattenClass_one_add (ih.1.isCompactOperator one_pos)
          (hn.1.isCompactOperator one_pos) ih.1 hn.1, ih.2.1.add hn.2.1, ?_⟩
      rw [RHTower.opTrace_add_of_memSchattenClass_one ih.1 hn.1, ih.2.2, hn.2.2]
      push_cast
      ring

theorem hsNorm_le_traceNorm {T : E →L[ℂ] E} (hT : RHTower.MemSchattenClass 1 T) :
    hsNorm T ≤ RHTower.traceNorm E T := by
  rw [hsNorm]
  calc Real.sqrt (hsNormSq T) ≤ Real.sqrt (RHTower.traceNorm E T ^ 2) :=
        Real.sqrt_le_sqrt (hsNormSq_le_traceNorm_sq hT)
    _ = RHTower.traceNorm E T := Real.sqrt_sq (RHTower.traceNorm_nonneg T)

/-- **Theorem 4.2, `(AIE.6)`: trace conservation and ideal escape.**  For a unitary without
eigenvectors and a nonzero positive trace-class `T`: every `M_N(T)`, `N ≥ 1`, is positive trace
class with the same trace and trace norm `‖T‖₁ > 0`; `‖M_N(T)‖₂ → 0`; and `(M_N(T))` has no
trace-norm limit. -/
theorem positive_traceClass_idealEscape {U : E ≃ₗᵢ[ℂ] E} (hU : HasNoEigenvectors U)
    {T : E →L[ℂ] E} (hT : RHTower.MemSchattenClass 1 T) (hpos : T.IsPositive) (hT0 : T ≠ 0) :
    (∀ N, 1 ≤ N → (hsCesaro U N T).IsPositive ∧ RHTower.MemSchattenClass 1 (hsCesaro U N T) ∧
        opTrace (hsCesaro U N T) = opTrace T ∧
        RHTower.traceNorm E (hsCesaro U N T) = RHTower.traceNorm E T) ∧
      0 < RHTower.traceNorm E T ∧
      Tendsto (fun N => hsNorm (hsCesaro U N T)) atTop (𝓝 0) ∧
      ¬ ∃ L : E →L[ℂ] E, RHTower.MemSchattenClass 1 L ∧
        Tendsto (fun N => RHTower.traceNorm E (hsCesaro U N T - L)) atTop (𝓝 0) := by
  have hN : ∀ N, 1 ≤ N → (hsCesaro U N T).IsPositive ∧
      RHTower.MemSchattenClass 1 (hsCesaro U N T) ∧ opTrace (hsCesaro U N T) = opTrace T ∧
      RHTower.traceNorm E (hsCesaro U N T) = RHTower.traceNorm E T := by
    intro N hN1
    obtain ⟨h1, h2, h3⟩ := hsConjSum_properties U hT hpos N
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hcoef : (0 : ℂ) ≤ (N : ℂ)⁻¹ := by
      rw [show ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
      exact Complex.zero_le_real.mpr (by positivity)
    have hpos' : (hsCesaro U N T).IsPositive := h2.smul_of_nonneg hcoef
    have hmem : RHTower.MemSchattenClass 1 (hsCesaro U N T) :=
      RHTower.memSchattenClass_one_smul h1 _
    have htr : opTrace (hsCesaro U N T) = opTrace T := by
      rw [hsCesaro_eq, RHTower.opTrace_smul, h3, ← mul_assoc, inv_mul_cancel₀ hNc, one_mul]
    refine ⟨hpos', hmem, htr, ?_⟩
    rw [RHTower.traceNorm_eq_re_opTrace_of_isPositive hmem hpos',
      RHTower.traceNorm_eq_re_opTrace_of_isPositive hT hpos, htr]
  have hTpos : 0 < RHTower.traceNorm E T :=
    lt_of_le_of_ne (RHTower.traceNorm_nonneg T)
      (Ne.symm fun h => hT0 ((RHTower.traceNorm_eq_zero_iff hT.one_summable_approxNumber).mp h))
  have hHS := tendsto_hsNorm_hsCesaro hU hT.one_isHilbertSchmidt
  refine ⟨hN, hTpos, hHS, ?_⟩
  rintro ⟨L, hL, hlim⟩
  -- the trace-norm limit would also be a Hilbert–Schmidt limit, hence zero
  have hdiffHS : ∀ N, RHTower.MemSchattenClass 1 (hsCesaro U N T - L) := by
    intro N
    have hM : RHTower.MemSchattenClass 1 (hsCesaro U N T) := by
      rcases Nat.eq_zero_or_pos N with rfl | hpos
      · simpa [hsCesaro] using RHTower.memSchattenClass_one_smul hT 0
      · exact (hN N hpos).2.1
    have := RHTower.memSchattenClass_one_add (hM.isCompactOperator one_pos)
      ((RHTower.memSchattenClass_one_smul hL (-1)).isCompactOperator one_pos) hM
      (RHTower.memSchattenClass_one_smul hL (-1))
    simpa [sub_eq_add_neg] using this
  have hLHS := hL.one_isHilbertSchmidt
  have hLzero : hsNorm L = 0 := by
    refine le_antisymm (ge_of_tendsto' ((hHS.add (squeeze_zero (fun N => hsNorm_nonneg _)
      (fun N => hsNorm_le_traceNorm (hdiffHS N)) hlim)).trans (by rw [add_zero])) fun N => ?_)
      (hsNorm_nonneg L)
    have hMHS := isHilbertSchmidt_hsCesaro U hT.one_isHilbertSchmidt N
    have h := hsNorm_add_le hMHS (hMHS.sub hLHS).neg
    rw [show hsCesaro U N T + -(hsCesaro U N T - L) = L by abel] at h
    calc hsNorm L ≤ hsNorm (hsCesaro U N T) + hsNorm (-(hsCesaro U N T - L)) := h
      _ = hsNorm (hsCesaro U N T) + hsNorm (hsCesaro U N T - L) := by
          have hneg : hsNorm (-(hsCesaro U N T - L)) = hsNorm (hsCesaro U N T - L) := by
            rw [hsNorm, hsNorm, hsNormSq_neg_eq_self]
          rw [hneg]
  have hL0 : L = 0 := (hsNorm_eq_zero_iff hLHS).mp hLzero
  subst hL0
  simp only [sub_zero] at hlim
  have hconst : ∀ᶠ N in atTop, RHTower.traceNorm E (hsCesaro U N T) = RHTower.traceNorm E T :=
    eventually_atTop.mpr ⟨1, fun N hN1 => (hN N hN1).2.2.2⟩
  have := tendsto_nhds_unique (hlim.congr' hconst) tendsto_const_nhds
  linarith

end IdealEscape

/-! ### Atomless phases -/

section Atomless

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ] {ζ : X → ℂ}

/-- An **atomless unit phase**: a measurable unimodular function with atomless law `ζ_* μ`. -/
structure IsAtomlessPhase (μ : Measure X) (ζ : X → ℂ) : Prop where
  measurable : Measurable ζ
  norm_eq_one : ∀ x, ‖ζ x‖ = 1
  noAtoms : NullSingletonClass (μ.map ζ)

omit [IsProbabilityMeasure μ] in
theorem IsAtomlessPhase.measure_preimage_singleton (hζ : IsAtomlessPhase μ ζ) (c : ℂ) :
    μ (ζ ⁻¹' {c}) = 0 := by
  haveI := hζ.noAtoms
  rw [← Measure.map_apply hζ.measurable (measurableSet_singleton c), measure_singleton]

/-- **Lemma 2.1, `(AIE.2)`.**  The resonance relation `{ζ(x) = ζ(y)}` is `μ × μ`-null. -/
theorem IsAtomlessPhase.measure_resonance (hζ : IsAtomlessPhase μ ζ) :
    (μ.prod μ) {p : X × X | ζ p.1 = ζ p.2} = 0 := by
  have hS : MeasurableSet {p : X × X | ζ p.1 = ζ p.2} :=
    measurableSet_eq_fun (hζ.measurable.comp measurable_fst) (hζ.measurable.comp measurable_snd)
  rw [Measure.prod_apply hS]
  have hfib : ∀ x, μ (Prod.mk x ⁻¹' {p : X × X | ζ p.1 = ζ p.2}) = 0 := fun x => by
    have : Prod.mk x ⁻¹' {p : X × X | ζ p.1 = ζ p.2} = ζ ⁻¹' {ζ x} := by
      ext y
      simp [eq_comm]
    rw [this, hζ.measure_preimage_singleton]
  exact (lintegral_congr hfib).trans lintegral_zero

theorem IsAtomlessPhase.ae_nonresonant (hζ : IsAtomlessPhase μ ζ) :
    ∀ᵐ p ∂(μ.prod μ), ζ p.1 ≠ ζ p.2 := by
  rw [ae_iff]
  simpa using hζ.measure_resonance

theorem measurable_phaseRatio (hζ : Measurable ζ) : Measurable (phaseRatio ζ) :=
  (Complex.continuous_conj.measurable.comp (hζ.comp measurable_fst)).mul (hζ.comp measurable_snd)

/-- **`(AIE.1)`.**  Conjugation `α` on the kernel space `L²(X × X)`: multiplication by
`ζ̄(x) ζ(y)`. -/
def kernelPhaseConj (hζ : IsAtomlessPhase μ ζ) :
    Lp ℂ 2 (μ.prod μ) →L[ℂ] Lp ℂ 2 (μ.prod μ) :=
  lpBoundedMulCLM (measurable_phaseRatio hζ.measurable) zero_le_one
    fun p => (norm_phaseRatio hζ.norm_eq_one p).le

/-- **`(AIE.1)`.**  The kernel transgression `δ = 1 - α`: multiplication by `1 - ζ̄(x) ζ(y)`. -/
def kernelPhaseTransgression (hζ : IsAtomlessPhase μ ζ) :
    Lp ℂ 2 (μ.prod μ) →L[ℂ] Lp ℂ 2 (μ.prod μ) :=
  1 - kernelPhaseConj hζ

omit [IsProbabilityMeasure μ] in
theorem norm_kernelPhaseConj_le (hζ : IsAtomlessPhase μ ζ) : ‖kernelPhaseConj hζ‖ ≤ 1 :=
  norm_lpBoundedMulCLM_le _ _ _

omit [IsProbabilityMeasure μ] in
theorem kernelPhaseTransgression_coeFn (hζ : IsAtomlessPhase μ ζ) (f : Lp ℂ 2 (μ.prod μ)) :
    (kernelPhaseTransgression hζ f : X × X → ℂ) =ᵐ[μ.prod μ]
      fun p => (1 - phaseRatio ζ p) * f p := by
  have h1 : kernelPhaseTransgression hζ f = f - kernelPhaseConj hζ f := by
    rw [kernelPhaseTransgression, sub_apply, one_apply_eq_self]
  rw [h1]
  filter_upwards [Lp.coeFn_sub f (kernelPhaseConj hζ f),
    lpBoundedMulCLM_coeFn (p := 2) (μ := μ.prod μ) (measurable_phaseRatio hζ.measurable)
      zero_le_one (fun p => (norm_phaseRatio hζ.norm_eq_one p).le) f] with p h1 h2
  rw [h1, Pi.sub_apply, show (kernelPhaseConj hζ f : X × X → ℂ) p = phaseRatio ζ p * f p from h2]
  ring

/-- **Theorem 2.2, `(AIE.3)`, kernel model.**  `ker δ = 0`. -/
theorem kernelPhaseTransgression_eq_zero (hζ : IsAtomlessPhase μ ζ) {f : Lp ℂ 2 (μ.prod μ)}
    (hf : kernelPhaseTransgression hζ f = 0) : f = 0 := by
  have h0 := kernelPhaseTransgression_coeFn hζ f
  rw [hf] at h0
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  filter_upwards [h0, Lp.coeFn_zero ℂ 2 (μ.prod μ), hζ.ae_nonresonant] with p h1 h2 h3
  have : (1 - phaseRatio ζ p) * f p = 0 := by rw [← h1, h2]; rfl
  exact (mul_eq_zero.mp this).resolve_left fun h =>
    h3 ((one_sub_phaseRatio_eq_zero_iff hζ.norm_eq_one p).mp h)

theorem kernelPhaseConj_fixed (hζ : IsAtomlessPhase μ ζ) {f : Lp ℂ 2 (μ.prod μ)}
    (hf : kernelPhaseConj hζ f = f) : f = 0 :=
  kernelPhaseTransgression_eq_zero hζ (by
    rw [kernelPhaseTransgression, sub_apply, one_apply_eq_self, hf, sub_self])

/-- **Theorem 3.1, kernel model: density.** -/
theorem dense_range_kernelPhaseTransgression (hζ : IsAtomlessPhase μ ζ) :
    Dense (Set.range (kernelPhaseTransgression hζ)) := by
  have h := dense_range_sub_one_of_fixed (kernelPhaseConj hζ) (norm_kernelPhaseConj_le hζ)
    fun f hf => kernelPhaseConj_fixed hζ hf
  have heq : Set.range (kernelPhaseTransgression hζ) =
      Set.range (kernelPhaseConj hζ - 1 : Lp ℂ 2 (μ.prod μ) →L[ℂ] Lp ℂ 2 (μ.prod μ)) := by
    ext y
    constructor <;> rintro ⟨x, rfl⟩ <;> refine ⟨-x, ?_⟩ <;>
      simp only [kernelPhaseTransgression, sub_apply, one_apply_eq_self, map_neg] <;> abel
  rw [heq]
  exact h

/-- A ball around a point of the unit circle has positive phase mass. -/
theorem IsAtomlessPhase.exists_ball_pos (hζ : IsAtomlessPhase μ ζ) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ 0 < μ (ζ ⁻¹' Metric.ball w ε) := by
  obtain ⟨t, hts, htfin, hcover⟩ := (isCompact_sphere (0 : ℂ) 1).finite_cover_balls hε
  by_contra hcon
  push Not at hcon
  have hzero : ∀ w ∈ t, μ (ζ ⁻¹' Metric.ball w ε) = 0 := fun w hw =>
    le_antisymm (hcon w (mem_sphere_zero_iff_norm.mp (hts hw))) zero_le
  have hunion : μ (⋃ w ∈ t, ζ ⁻¹' Metric.ball w ε) = 0 :=
    (measure_biUnion_null_iff htfin.countable).mpr hzero
  have huniv : (Set.univ : Set X) ⊆ ⋃ w ∈ t, ζ ⁻¹' Metric.ball w ε := fun x _ => by
    have hx : ζ x ∈ Metric.sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr (hζ.norm_eq_one x)
    obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp (hcover hx)
    exact Set.mem_iUnion₂.mpr ⟨w, hw, hxw⟩
  have := measure_mono_null huniv hunion
  simp at this

omit [IsProbabilityMeasure μ] in
theorem norm_one_sub_phaseRatio_lt_of_mem (hζ : IsAtomlessPhase μ ζ) {w : ℂ} {r : ℝ}
    {p : X × X} (hp : p ∈ (ζ ⁻¹' Metric.ball w (r / 2)) ×ˢ (ζ ⁻¹' Metric.ball w (r / 2))) :
    ‖1 - phaseRatio ζ p‖ < r := by
  rw [norm_one_sub_phaseRatio hζ.norm_eq_one]
  obtain ⟨h1, h2⟩ := hp
  simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h1 h2
  calc ‖ζ p.1 - ζ p.2‖ ≤ ‖ζ p.1 - w‖ + ‖ζ p.2 - w‖ := by
        rw [norm_sub_rev (ζ p.2)]
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < r / 2 + r / 2 := add_lt_add h1 h2
    _ = r := add_halves r

/-- **Theorem 3.1, kernel model.**  The transgression is not bounded below: kernels concentrated
on a small phase arc are almost fixed. -/
theorem IsAtomlessPhase.exists_kernel_almost_fixed (hζ : IsAtomlessPhase μ ζ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : Lp ℂ 2 (μ.prod μ), g ≠ 0 ∧ ‖kernelPhaseTransgression hζ g‖ ≤ ε * ‖g‖ := by
  obtain ⟨w, -, hpos⟩ := hζ.exists_ball_pos (half_pos hε)
  set E := ζ ⁻¹' Metric.ball w (ε / 2)
  have hE : MeasurableSet E := hζ.measurable measurableSet_ball
  have hS : MeasurableSet (E ×ˢ E) := hE.prod hE
  have hSfin : (μ.prod μ) (E ×ˢ E) ≠ ⊤ := measure_ne_top _ _
  have hSpos : 0 < (μ.prod μ) (E ×ˢ E) := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos hpos.ne' hpos.ne'
  set g := indicatorConstLp 2 hS hSfin (1 : ℂ)
  have hgnorm : 0 < ‖g‖ := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul]
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hSpos.ne' hSfin) _
  refine ⟨g, norm_pos_iff.mp hgnorm, Lp.norm_le_mul_norm_of_ae_le_mul ?_⟩
  filter_upwards [kernelPhaseTransgression_coeFn hζ g,
    indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hSfin) (c := (1 : ℂ))] with p h1 h2
  rw [h1, h2]
  by_cases hp : p ∈ E ×ˢ E
  · rw [Set.indicator_of_mem hp, mul_one, norm_one, mul_one]
    exact (norm_one_sub_phaseRatio_lt_of_mem hζ hp).le
  · simp [Set.indicator_of_notMem hp]

/-- **Theorem 3.1, kernel model: nonclosed range.** -/
theorem not_isClosed_range_kernelPhaseTransgression (hζ : IsAtomlessPhase μ ζ) :
    ¬ IsClosed (Set.range (kernelPhaseTransgression hζ)) := by
  intro hcl
  obtain ⟨c, hc, hlow⟩ := (ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range _).mpr hcl
  have hker : LinearMap.ker (kernelPhaseTransgression hζ :
      Lp ℂ 2 (μ.prod μ) →ₗ[ℂ] Lp ℂ 2 (μ.prod μ)) = ⊥ :=
    LinearMap.ker_eq_bot'.mpr fun f hf => kernelPhaseTransgression_eq_zero hζ hf
  obtain ⟨g, hg0, hg⟩ := hζ.exists_kernel_almost_fixed (half_pos hc)
  have h := hlow g (by rw [hker, Submodule.bot_orthogonal_eq_top]; trivial)
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg0
  nlinarith

/-- The local resolvent symbol `(1 - ζ̄(x)ζ(y))⁻¹` on `{|1 - ζ̄(x)ζ(y)| ≥ ε}`. -/
def phaseResolventSymbol (ζ : X → ℂ) (ε : ℝ) (p : X × X) : ℂ :=
  if ε ≤ ‖1 - phaseRatio ζ p‖ then (1 - phaseRatio ζ p)⁻¹ else 0

omit [IsProbabilityMeasure μ] in
/-- **Corollary 3.2 (local exactness).**  A kernel supported where `|1 - ζ̄(x)ζ(y)| ≥ ε` has a
Hilbert–Schmidt primitive of norm at most `ε⁻¹` times its norm. -/
theorem exists_kernelPrimitive (hζ : IsAtomlessPhase μ ζ) {ε : ℝ} (hε : 0 < ε)
    {g : Lp ℂ 2 (μ.prod μ)} (hg : ∀ᵐ p ∂(μ.prod μ), ‖1 - phaseRatio ζ p‖ < ε → g p = 0) :
    ∃ G, kernelPhaseTransgression hζ G = g ∧ ‖G‖ ≤ ε⁻¹ * ‖g‖ := by
  have hmr := measurable_phaseRatio hζ.measurable
  have hmeas : Measurable (phaseResolventSymbol ζ ε) :=
    Measurable.ite (measurableSet_le measurable_const (measurable_const.sub hmr).norm)
      (measurable_const.sub hmr).inv measurable_const
  have hbound : ∀ p, ‖phaseResolventSymbol ζ ε p‖ ≤ ε⁻¹ := by
    intro p
    unfold phaseResolventSymbol
    split_ifs with h
    · rw [norm_inv]
      exact inv_anti₀ hε h
    · rw [norm_zero]
      exact inv_nonneg.mpr hε.le
  set R := lpBoundedMulCLM (p := 2) (μ := μ.prod μ) hmeas (inv_nonneg.mpr hε.le) hbound
  refine ⟨R g, ?_, ?_⟩
  · refine Lp.ext_iff.mpr ?_
    filter_upwards [kernelPhaseTransgression_coeFn hζ (R g),
      lpBoundedMulCLM_coeFn (p := 2) (μ := μ.prod μ) hmeas (inv_nonneg.mpr hε.le) hbound g,
      hg] with p h1 h2 h3
    rw [h1, show (R g : X × X → ℂ) p = phaseResolventSymbol ζ ε p * g p from h2]
    unfold phaseResolventSymbol
    split_ifs with h
    · have hne : 1 - phaseRatio ζ p ≠ 0 := fun h0 => by
        rw [h0, norm_zero] at h
        linarith
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    · rw [zero_mul, mul_zero, h3 (not_le.mp h)]
  · calc ‖R g‖ ≤ ‖R‖ * ‖g‖ := R.le_opNorm g
      _ ≤ ε⁻¹ * ‖g‖ := mul_le_mul_of_nonneg_right (norm_lpBoundedMulCLM_le _ _ _) (norm_nonneg _)

/-- **Corollary 3.2 (global failure).**  The local inverse norms are unbounded: for every `C`
some kernel supported where `|1 - ζ̄(x)ζ(y)| ≥ ε` has only primitives of norm `> C ‖g‖`. -/
theorem kernelPrimitive_unbounded (hζ : IsAtomlessPhase μ ζ) (C : ℝ) :
    ∃ ε > 0, ∃ g : Lp ℂ 2 (μ.prod μ), g ≠ 0 ∧
      (∀ᵐ p ∂(μ.prod μ), ‖1 - phaseRatio ζ p‖ < ε → g p = 0) ∧
      ∀ G, kernelPhaseTransgression hζ G = g → C * ‖g‖ < ‖G‖ := by
  set r : ℝ := 1 / (|C| + 1)
  have hr : 0 < r := by positivity
  obtain ⟨w, -, hpos⟩ := hζ.exists_ball_pos (half_pos hr)
  set E := ζ ⁻¹' Metric.ball w (r / 2)
  have hE : MeasurableSet E := hζ.measurable measurableSet_ball
  have hmr := measurable_phaseRatio hζ.measurable
  set S : ℕ → Set (X × X) := fun n =>
    (E ×ˢ E) ∩ {p | 1 / ((n : ℝ) + 1) ≤ ‖1 - phaseRatio ζ p‖}
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n =>
    (hE.prod hE).inter (measurableSet_le measurable_const (measurable_const.sub hmr).norm)
  obtain ⟨n, hn⟩ : ∃ n, 0 < (μ.prod μ) (S n) := by
    by_contra hcon
    push Not at hcon
    have hnull : (μ.prod μ) (⋃ n, S n) = 0 :=
      measure_iUnion_null fun n => le_antisymm (hcon n) zero_le
    have hsub : E ×ˢ E ⊆ (⋃ n, S n) ∪ {p : X × X | ζ p.1 = ζ p.2} := by
      intro p hp
      by_cases hres : ζ p.1 = ζ p.2
      · exact Or.inr hres
      · left
        have hpos' : 0 < ‖1 - phaseRatio ζ p‖ := norm_pos_iff.mpr fun h =>
          hres ((one_sub_phaseRatio_eq_zero_iff hζ.norm_eq_one p).mp h)
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos'
        exact Set.mem_iUnion.mpr ⟨m, hp, hm.le⟩
    have h0 : (μ.prod μ) (E ×ˢ E) = 0 :=
      measure_mono_null hsub (measure_union_null hnull hζ.measure_resonance)
    rw [Measure.prod_prod] at h0
    exact (ENNReal.mul_pos hpos.ne' hpos.ne').ne' h0
  have hSfin : (μ.prod μ) (S n) ≠ ⊤ := measure_ne_top _ _
  set g := indicatorConstLp 2 (hSmeas n) hSfin (1 : ℂ)
  have hgnorm : 0 < ‖g‖ := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul]
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hn.ne' hSfin) _
  have hgcoe := indicatorConstLp_coeFn (p := 2) (hs := hSmeas n) (hμs := hSfin) (c := (1 : ℂ))
  refine ⟨1 / ((n : ℝ) + 1), by positivity, g, norm_pos_iff.mp hgnorm, ?_, fun G hG => ?_⟩
  · filter_upwards [hgcoe] with p hp hlt
    rw [hp, Set.indicator_of_notMem]
    exact fun hmem => absurd hmem.2 (not_le.mpr hlt)
  · have hle : ‖g‖ ≤ r * ‖G‖ := by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      have hG' := kernelPhaseTransgression_coeFn hζ G
      rw [hG] at hG'
      filter_upwards [hG', hgcoe] with p h1 h2
      by_cases hp : p ∈ S n
      · rw [h1, norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_one_sub_phaseRatio_lt_of_mem hζ hp.1).le
          (norm_nonneg _)
      · rw [h2, Set.indicator_of_notMem hp, norm_zero]
        positivity
    have hGpos : (|C| + 1) * ‖g‖ ≤ ‖G‖ := by
      have := hle
      rw [show r = 1 / (|C| + 1) from rfl, div_mul_eq_mul_div, one_mul,
        le_div_iff₀ (by positivity)] at this
      linarith
    calc C * ‖g‖ ≤ |C| * ‖g‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
      _ < (|C| + 1) * ‖g‖ := by nlinarith
      _ ≤ ‖G‖ := hGpos

/-- **Theorem 4.1, kernel model.**  The Cesàro averages of the kernel conjugation tend to zero. -/
theorem tendsto_kernelPhaseCesaro (hζ : IsAtomlessPhase μ ζ) (f : Lp ℂ 2 (μ.prod μ)) :
    Tendsto (fun N => birkhoffAverage ℂ (kernelPhaseConj hζ) _root_.id N f) atTop (𝓝 0) :=
  tendsto_birkhoffAverage_zero_of_fixed _ (norm_kernelPhaseConj_le hζ)
    (fun _ hf => kernelPhaseConj_fixed hζ hf) f

/-! ### The operator model -/

omit [IsProbabilityMeasure μ] in
/-- Multiplication by a measurable unimodular function, as a unitary of `L²(X, μ)`. -/
def unimodularMulUnitary {φ : X → ℂ} (hφ : Measurable φ) (h1 : ∀ x, ‖φ x‖ = 1) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  have hφ' : Measurable fun x => conj (φ x) := Complex.continuous_conj.measurable.comp hφ
  have h1' : ∀ x, ‖conj (φ x)‖ ≤ 1 := fun x => by rw [Complex.norm_conj, h1]
  let M := lpBoundedMulCLM (p := 2) (μ := μ) hφ zero_le_one fun x => (h1 x).le
  let M' := lpBoundedMulCLM (p := 2) (μ := μ) hφ' zero_le_one h1'
  { toLinearEquiv := LinearEquiv.ofLinear (M : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) M'
      (LinearMap.ext fun f => Lp.ext_iff.mpr (by
        filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ zero_le_one
            (fun x => (h1 x).le) (M' f),
          lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ' zero_le_one h1' f] with x hx1 hx2
        simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
          LinearMap.id_coe, id_eq]
        rw [hx1, hx2, ← mul_assoc, mul_comm (φ x), conj_mul_self_of_norm_eq_one (h1 x), one_mul]))
      (LinearMap.ext fun f => Lp.ext_iff.mpr (by
        filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ' zero_le_one h1' (M f),
          lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ zero_le_one
            (fun x => (h1 x).le) f] with x hx1 hx2
        simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
          LinearMap.id_coe, id_eq]
        rw [hx1, hx2, ← mul_assoc, conj_mul_self_of_norm_eq_one (h1 x), one_mul]))
    norm_map' := fun f => by
      have h := lpBoundedMulCLM_inner_unimodular (μ := μ) hφ zero_le_one
        (fun x => (h1 x).le) (fun x => conj_mul_self_of_norm_eq_one (h1 x)) f f
      show ‖M f‖ = ‖f‖
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) f, h] }

omit [IsProbabilityMeasure μ] in
theorem unimodularMulUnitary_coeFn {φ : X → ℂ} (hφ : Measurable φ) (h1 : ∀ x, ‖φ x‖ = 1)
    (f : Lp ℂ 2 μ) :
    (unimodularMulUnitary hφ h1 f : X → ℂ) =ᵐ[μ] fun x => φ x * f x :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ zero_le_one (fun x => (h1 x).le) f

omit [IsProbabilityMeasure μ] in
theorem unimodularMulUnitary_symm_coeFn
    {φ : X → ℂ} (hφ : Measurable φ) (h1 : ∀ x, ‖φ x‖ = 1) (f : Lp ℂ 2 μ) :
    ((unimodularMulUnitary (μ := μ) hφ h1).symm f : X → ℂ) =ᵐ[μ]
      fun x => conj (φ x) * f x :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := μ) (Complex.continuous_conj.measurable.comp hφ)
    zero_le_one (fun x => by
      show ‖conj (φ x)‖ ≤ 1
      rw [Complex.norm_conj, h1]) f

/-- The phase unitary `U f = ζ f` on `L²(X, μ)`. -/
def phaseMulUnitary (hζ : IsAtomlessPhase μ ζ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  unimodularMulUnitary hζ.measurable hζ.norm_eq_one

omit [IsProbabilityMeasure μ] in
/-- An atomless phase unitary has no eigenvectors. -/
theorem hasNoEigenvectors_phaseMulUnitary (hζ : IsAtomlessPhase μ ζ) :
    HasNoEigenvectors (phaseMulUnitary hζ) := by
  intro f c hf
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  have hnull : ∀ᵐ x ∂μ, ζ x ≠ c := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    exact hζ.measure_preimage_singleton c
  filter_upwards [unimodularMulUnitary_coeFn hζ.measurable hζ.norm_eq_one f, Lp.coeFn_smul c f,
    Lp.ext_iff.mp hf, hnull] with x h1 h2 h3 h4
  have heq : (ζ x - c) * f x = 0 := by
    have : ζ x * f x = c * f x := by
      rw [← h1]
      exact h3.trans (by rw [h2]; rfl)
    rw [sub_mul, this, sub_self]
  exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr h4)

/-- An atomless phase unitary has approximate eigenvectors: normalized indicators of small phase
arcs. -/
theorem hasApproxEigenvectors_phaseMulUnitary (hζ : IsAtomlessPhase μ ζ) :
    HasApproxEigenvectors (phaseMulUnitary hζ) := by
  intro ε hε
  obtain ⟨w, hw1, hpos⟩ := hζ.exists_ball_pos hε
  set E := ζ ⁻¹' Metric.ball w ε
  have hE : MeasurableSet E := hζ.measurable measurableSet_ball
  have hEfin : μ E ≠ ⊤ := measure_ne_top _ _
  have hreal : 0 < μ.real E := ENNReal.toReal_pos hpos.ne' hEfin
  set c : ℂ := ((((μ.real E) ^ (1 / 2 : ℝ))⁻¹ : ℝ) : ℂ)
  set u := indicatorConstLp 2 hE hEfin c
  have hu : ‖u‖ = 1 := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    simp only [ENNReal.toReal_ofNat]
    exact inv_mul_cancel₀ (Real.rpow_pos_of_pos hreal _).ne'
  refine ⟨u, w, hu, hw1, ?_⟩
  calc ‖phaseMulUnitary hζ u - w • u‖ ≤ ε * ‖u‖ := by
        refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
        filter_upwards [Lp.coeFn_sub (phaseMulUnitary hζ u) (w • u),
          unimodularMulUnitary_coeFn hζ.measurable hζ.norm_eq_one u, Lp.coeFn_smul w u,
          indicatorConstLp_coeFn (p := 2) (hs := hE) (hμs := hEfin) (c := c)] with x h1 h2 h3 h4
        rw [h1, Pi.sub_apply, show (phaseMulUnitary hζ u : X → ℂ) x = ζ x * u x from h2, h3,
          Pi.smul_apply, smul_eq_mul, ← sub_mul, norm_mul]
        by_cases hx : x ∈ E
        · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          have := hx
          simp only [E, Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at this
          exact this.le
        · rw [h4, Set.indicator_of_notMem hx, norm_zero, mul_zero, mul_zero]
    _ = ε := by rw [hu, mul_one]

/-- **Theorems 2.2, 3.1, 4.1 on the Hilbert–Schmidt ideal of `L²(X, μ)`.**  For an atomless
phase: no nonzero Hilbert–Schmidt operator commutes with `U`; every Hilbert–Schmidt operator is a
Hilbert–Schmidt limit of transgressions `α(S) - S`; `δ` is not bounded below; and every Cesàro
formation tends to zero in Hilbert–Schmidt norm. -/
theorem atomlessPhase_hilbertSchmidt_formation (hζ : IsAtomlessPhase μ ζ) :
    (∀ T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, IsHilbertSchmidt T →
        hsConj (phaseMulUnitary hζ) T = T → T = 0) ∧
      (∀ T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, IsHilbertSchmidt T → ∀ ε > 0,
        ∃ S, IsHilbertSchmidt S ∧ hsNorm (T - (hsConj (phaseMulUnitary hζ) S - S)) < ε) ∧
      (¬ ∃ c > 0, ∀ T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, IsHilbertSchmidt T →
        c * hsNorm T ≤ hsNorm (hsConj (phaseMulUnitary hζ) T - T)) ∧
      (∀ T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, IsHilbertSchmidt T →
        Tendsto (fun N => hsNorm (hsCesaro (phaseMulUnitary hζ) N T)) atTop (𝓝 0)) :=
  ⟨fun _ hT hfix => eq_zero_of_hsConj_eq (hasNoEigenvectors_phaseMulUnitary hζ) hT hfix,
    fun _ hT _ hε =>
      exists_hsNorm_sub_transgression_lt (hasNoEigenvectors_phaseMulUnitary hζ) hT hε,
    not_exists_hsTransgression_lowerBound (hasApproxEigenvectors_phaseMulUnitary hζ),
    fun _ hT => tendsto_hsNorm_hsCesaro (hasNoEigenvectors_phaseMulUnitary hζ) hT⟩

/-- **Theorem 3.1 in the column Hilbert space of `S₂(L²(X, μ))`.**  The transgression has dense,
nonclosed range. -/
theorem atomlessPhase_columnTransgression {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (hζ : IsAtomlessPhase μ ζ) :
    Dense (Set.range (columnConj b (phaseMulUnitary hζ) - 1 :
        lp (fun _ : ι => Lp ℂ 2 μ) 2 →L[ℂ] lp (fun _ : ι => Lp ℂ 2 μ) 2)) ∧
      ¬ IsClosed (Set.range (columnConj b (phaseMulUnitary hζ) - 1 :
        lp (fun _ : ι => Lp ℂ 2 μ) 2 →L[ℂ] lp (fun _ : ι => Lp ℂ 2 μ) 2)) :=
  ⟨dense_range_columnTransgression b (hasNoEigenvectors_phaseMulUnitary hζ),
    not_isClosed_range_columnTransgression b (hasNoEigenvectors_phaseMulUnitary hζ)
      (hasApproxEigenvectors_phaseMulUnitary hζ)⟩

omit [IsProbabilityMeasure μ] in
/-- **Theorem 4.2 for an atomless phase.** -/
theorem atomlessPhase_traceClass_idealEscape (hζ : IsAtomlessPhase μ ζ)
    {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : RHTower.MemSchattenClass 1 T) (hpos : T.IsPositive)
    (hT0 : T ≠ 0) :
    (∀ N, 1 ≤ N → (hsCesaro (phaseMulUnitary hζ) N T).IsPositive ∧
        RHTower.MemSchattenClass 1 (hsCesaro (phaseMulUnitary hζ) N T) ∧
        opTrace (hsCesaro (phaseMulUnitary hζ) N T) = opTrace T ∧
        RHTower.traceNorm (Lp ℂ 2 μ) (hsCesaro (phaseMulUnitary hζ) N T) =
          RHTower.traceNorm (Lp ℂ 2 μ) T) ∧
      0 < RHTower.traceNorm (Lp ℂ 2 μ) T ∧
      Tendsto (fun N => hsNorm (hsCesaro (phaseMulUnitary hζ) N T)) atTop (𝓝 0) ∧
      ¬ ∃ L : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, RHTower.MemSchattenClass 1 L ∧
        Tendsto (fun N => RHTower.traceNorm (Lp ℂ 2 μ) (hsCesaro (phaseMulUnitary hζ) N T - L))
          atTop (𝓝 0) :=
  positive_traceClass_idealEscape (hasNoEigenvectors_phaseMulUnitary hζ) hT hpos hT0

/-! ### Kernel operators: the conjugation multiplier `(AIE.1)` -/

omit [IsProbabilityMeasure μ] in
/-- The phase-conjugated kernel `(y, x) ↦ ζ̄(y) k(y, x) ζ(x)`. -/
def SqIntKernel.phaseConj (hζ : IsAtomlessPhase μ ζ) (k : SqIntKernel μ μ) : SqIntKernel μ μ where
  toFun y x := conj (ζ y) * k.toFun y x * ζ x
  measurable := by
    have hc : Measurable fun p : X × X => conj (ζ p.1) :=
      Complex.continuous_conj.measurable.comp (hζ.measurable.comp measurable_fst)
    exact (hc.mul k.measurable).mul (hζ.measurable.comp measurable_snd)
  energy_lt_top := by
    have hunit : ∀ z : ℂ, ‖z‖ = 1 → ‖z‖ₑ = 1 := fun z hz => by
      rw [← ofReal_norm, hz, ENNReal.ofReal_one]
    have h : ∀ y x, ‖conj (ζ y) * k.toFun y x * ζ x‖ₑ = ‖k.toFun y x‖ₑ := fun y x => by
      rw [enorm_mul, enorm_mul, hunit _ (by rw [Complex.norm_conj, hζ.norm_eq_one]),
        hunit _ (hζ.norm_eq_one x), one_mul, mul_one]
    simp_rw [h]
    exact k.energy_lt_top

omit [IsProbabilityMeasure μ] in
/-- **`(AIE.1)` on kernel operators.**  Conjugation `U* T_k U` of a square-integrable kernel
operator is the kernel operator of `ζ̄(y) k(y, x) ζ(x)`. -/
theorem hsConj_sqIntKernel_op [SFinite μ] (hζ : IsAtomlessPhase μ ζ) (k : SqIntKernel μ μ) :
    hsConj (phaseMulUnitary hζ) k.op = (k.phaseConj hζ).op := by
  refine ContinuousLinearMap.ext fun f => Lp.ext_iff.mpr ?_
  have hUf := unimodularMulUnitary_coeFn hζ.measurable hζ.norm_eq_one f
  filter_upwards [unimodularMulUnitary_symm_coeFn hζ.measurable hζ.norm_eq_one
      (k.op (phaseMulUnitary hζ f)), k.op_coeFn (phaseMulUnitary hζ f),
    (k.phaseConj hζ).op_coeFn f] with y h1 h2 h3
  rw [hsConj_apply, show ((phaseMulUnitary hζ).symm (k.op (phaseMulUnitary hζ f)) : X → ℂ) y =
      conj (ζ y) * (k.op (phaseMulUnitary hζ f) : X → ℂ) y from h1, h2, h3, SqIntKernel.apply,
    SqIntKernel.apply, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hUf] with x hx
  rw [show (phaseMulUnitary hζ f : X → ℂ) x = ζ x * f x from hx]
  simp only [SqIntKernel.phaseConj]
  ring

end Atomless

end GaloisForLFunctions.HTGeometry
