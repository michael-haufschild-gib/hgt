import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaQuadraticRankHSRobinTraceNoGo
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoherentCausalDepthFusion
import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearSchattenBridge

open Complex Filter Topology ContinuousLinearMap
open scoped InnerProductSpace ENNReal
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- The actual causal prime-depth Gamma amplitudes are jointly absolutely summable. -/
theorem summable_suzukiCausalDepthGammaWeight_allPrime
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) :
    Summable (fun pe : Nat.Primes × ℕ =>
      suzukiCausalDepthGammaWeight h a pe) := by
  rw [summable_prod_of_nonneg
    (fun pe => (suzukiCausalDepthGammaWeight_pos hh ha pe).le)]
  constructor
  · intro p
    have hr0 : 0 < suzukiCriticalApertureDepthFusionRadius h a p :=
      suzukiCriticalApertureDepthFusionRadius_pos h a p
    have hr1 : suzukiCriticalApertureDepthFusionRadius h a p < 1 :=
      suzukiCriticalApertureDepthFusionRadius_lt_one hh ha p
    have hgeom : Summable (fun e : ℕ =>
        suzukiCriticalApertureDepthFusionRadius h a p ^ e) := by
      apply summable_geometric_of_norm_lt_one
      rw [Real.norm_eq_abs, abs_of_pos hr0]
      exact hr1
    simpa [suzukiCausalDepthGammaWeight] using
      hgeom.mul_left (suzukiCriticalEntryWallEndpointAmplitude h a p 0)
  · have hcap0 : 0 < suzukiCoherentCausalDepthRadiusCap := by
      rw [suzukiCoherentCausalDepthRadiusCap]
      positivity
    have hcap1 : suzukiCoherentCausalDepthRadiusCap < 1 :=
      suzukiCoherentCausalDepthRadiusCap_lt_one
    have hcapGeom : Summable (fun e : ℕ =>
        suzukiCoherentCausalDepthRadiusCap ^ e) := by
      apply summable_geometric_of_norm_lt_one
      rw [Real.norm_eq_abs, abs_of_pos hcap0]
      exact hcap1
    have hmajor : Summable
        (suzukiCriticalApertureDepthFusedCoherentMajorant h) := by
      refine ((summable_suzukiCriticalEntryWallCoherentMajorant h).mul_left
        (1 - suzukiCoherentCausalDepthRadiusCap)⁻¹).congr ?_
      intro p
      rfl
    refine Summable.of_nonneg_of_le
      (fun p => tsum_nonneg fun _ =>
        (suzukiCausalDepthGammaWeight_pos hh ha (p, _)).le)
      (fun p => ?_) hmajor
    have hr0 : 0 < suzukiCriticalApertureDepthFusionRadius h a p :=
      suzukiCriticalApertureDepthFusionRadius_pos h a p
    have hrCap : suzukiCriticalApertureDepthFusionRadius h a p ≤
        suzukiCoherentCausalDepthRadiusCap :=
      suzukiCriticalApertureDepthFusionRadius_le_coherentCap hh ha p
    have hA0 : 0 ≤ suzukiCriticalEntryWallEndpointAmplitude h a p 0 :=
      (suzukiCriticalEntryWallEndpointAmplitude_zero_pos hh ha p).le
    have hM0 : 0 ≤ suzukiCriticalEntryWallCoherentMajorant h p := by
      rw [suzukiCriticalEntryWallCoherentMajorant]
      positivity
    have hA : suzukiCriticalEntryWallEndpointAmplitude h a p 0 ≤
        suzukiCriticalEntryWallCoherentMajorant h p :=
      suzukiCriticalEntryWallEndpointAmplitude_zero_le_coherentMajorant hh ha p
    have hrow : Summable (fun e : ℕ =>
        suzukiCausalDepthGammaWeight h a (p, e)) := by
      simpa [suzukiCausalDepthGammaWeight] using
        (summable_geometric_of_norm_lt_one (by
          rw [Real.norm_eq_abs, abs_of_pos hr0]
          exact suzukiCriticalApertureDepthFusionRadius_lt_one hh ha p)).mul_left
          (suzukiCriticalEntryWallEndpointAmplitude h a p 0)
    have hmajRow : Summable (fun e : ℕ =>
        suzukiCriticalEntryWallCoherentMajorant h p *
          suzukiCoherentCausalDepthRadiusCap ^ e) :=
      hcapGeom.mul_left _
    calc
      (∑' e : ℕ, suzukiCausalDepthGammaWeight h a (p, e)) ≤
          ∑' e : ℕ, suzukiCriticalEntryWallCoherentMajorant h p *
            suzukiCoherentCausalDepthRadiusCap ^ e := by
        apply Summable.tsum_le_tsum
        · intro e
          rw [suzukiCausalDepthGammaWeight]
          exact mul_le_mul hA
            (pow_le_pow_left₀ hr0.le hrCap e)
            (pow_nonneg hr0.le e) hM0
        · exact hrow
        · exact hmajRow
      _ = suzukiCriticalApertureDepthFusedCoherentMajorant h p := by
        rw [tsum_mul_left,
          tsum_geometric_of_norm_lt_one (by
            rw [Real.norm_eq_abs, abs_of_pos hcap0]
            exact hcap1)]
        rw [suzukiCriticalApertureDepthFusedCoherentMajorant]
        ring

/-- A bounded operator on canonical `ℓ²` is nuclear when its canonical column norms are
summable. -/
theorem deningerIsNuclear_of_summable_norm_apply_lp_single
    {ι : Type} [DecidableEq ι]
    (T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)
    (hsum : Summable (fun i : ι =>
      ‖T (lp.single 2 i (1 : ℂ))‖)) :
    DeningerIsNuclear T := by
  let phi : ι → (lp (fun _ : ι => ℂ) 2 →L[ℂ] ℂ) := fun i =>
    lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i
  let y : ι → lp (fun _ : ι => ℂ) 2 := fun i =>
    T (lp.single 2 i (1 : ℂ))
  refine ⟨ι, phi, y, ?_, ?_⟩
  · apply Summable.of_nonneg_of_le
      (fun i => mul_nonneg (norm_nonneg (phi i)) (norm_nonneg (y i)))
      (fun i => ?_) hsum
    have hphi : ‖phi i‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro x
      change ‖x i‖ ≤ 1 * ‖x‖
      simpa using
        (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x i)
    change ‖phi i‖ * ‖y i‖ ≤ ‖y i‖
    exact mul_le_of_le_one_left (norm_nonneg (y i)) hphi
  · intro x
    have hs := T.hasSum
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
    change HasSum (fun i : ι => T (lp.single 2 i (x i))) (T x) at hs
    convert hs using 1
    funext i
    change x i • T (lp.single 2 i (1 : ℂ)) = T (lp.single 2 i (x i))
    rw [← map_smul]
    congr 1
    simpa using
      (lp.single_smul (E := fun _ : ι => ℂ) 2 i (x i) (1 : ℂ)).symm

/-- Exact squared norm of one actual prime-depth feature column. -/
theorem norm_sq_suzukiCausalDepthGammaFeatureOperator_single_source
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (pe : Nat.Primes × ℕ) :
    ‖suzukiCausalDepthGammaFeatureOperator h a hh ha
        (lp.single 2 (Sum.inl pe) (1 : ℂ))‖ ^ 2 =
      suzukiCausalDepthGammaWeight h a pe ^ 2 *
        gammaConductorModeSchurResidual
          (suzukiCausalDepthGammaFrequency pe)
          (suzukiCausalDepthGammaFrequency pe) := by
  rw [suzukiCausalDepthGammaFeatureOperator,
    HilbertSchmidt.norm_toOperator_single_sq]
  let f : SuzukiCausalDepthGammaTraceIndex → ℝ := fun i =>
    ‖suzukiCausalDepthGammaFeatureKernel h a (i, Sum.inl pe)‖ ^ 2
  have hleft : HasSum (f ∘ Sum.inl) 0 := by
    have hz : (f ∘ Sum.inl) =
        (fun _ : Nat.Primes × ℕ => (0 : ℝ)) := by
      funext x
      simp [f, suzukiCausalDepthGammaFeatureKernel]
    rw [hz]
    exact hasSum_zero
  have hrightSummable : Summable (f ∘ Sum.inr) := by
    refine (summable_sq_suzukiCausalDepthGammaWeightedFeature_row h a pe).congr
      (fun k => ?_)
    simp [f, suzukiCausalDepthGammaFeatureKernel,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsum : HasSum f (0 + ∑' k : ℕ, (f ∘ Sum.inr) k) :=
    hleft.sum hrightSummable.hasSum
  change (∑' i : SuzukiCausalDepthGammaTraceIndex, f i) = _
  rw [hsum.tsum_eq, zero_add]
  rw [show (∑' k : ℕ, (f ∘ Sum.inr) k) =
      ∑' k : ℕ, suzukiCausalDepthGammaWeightedFeature h a pe k ^ 2 by
    apply tsum_congr
    intro k
    simp [f, suzukiCausalDepthGammaFeatureKernel,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]]
  exact tsum_sq_suzukiCausalDepthGammaWeightedFeature_row h a pe

/-- Every canonical feature column is bounded by its actual prime-depth amplitude. -/
theorem norm_suzukiCausalDepthGammaFeatureOperator_single_le
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (i : SuzukiCausalDepthGammaTraceIndex) :
    ‖suzukiCausalDepthGammaFeatureOperator h a hh ha
        (lp.single 2 i (1 : ℂ))‖ ≤
      Sum.elim (suzukiCausalDepthGammaWeight h a) (fun _ => 0) i := by
  cases i with
  | inl pe =>
      simp only [Sum.elim_inl]
      have hsq := norm_sq_suzukiCausalDepthGammaFeatureOperator_single_source
        h a hh ha pe
      have hres := gammaConductorModeSchurResidual_self_le_one
        (suzukiCausalDepthGammaFrequency pe)
      have hw := (suzukiCausalDepthGammaWeight_pos hh ha pe).le
      have hn := norm_nonneg
        (suzukiCausalDepthGammaFeatureOperator h a hh ha
          (lp.single 2 (Sum.inl pe) (1 : ℂ)))
      nlinarith
  | inr k =>
      simp only [Sum.elim_inr]
      have hsq := HilbertSchmidt.norm_toOperator_single_sq
        (suzukiCausalDepthGammaFeatureKernel_isHS hh ha) (Sum.inr k)
      change ‖suzukiCausalDepthGammaFeatureOperator h a hh ha
        (lp.single 2 (Sum.inr k) (1 : ℂ))‖ ^ 2 =
          ∑' i : SuzukiCausalDepthGammaTraceIndex,
            ‖suzukiCausalDepthGammaFeatureKernel h a (i, Sum.inr k)‖ ^ 2 at hsq
      have hzero : (∑' i : SuzukiCausalDepthGammaTraceIndex,
          ‖suzukiCausalDepthGammaFeatureKernel h a (i, Sum.inr k)‖ ^ 2) = 0 := by
        simp [suzukiCausalDepthGammaFeatureKernel]
      rw [hzero] at hsq
      nlinarith [norm_nonneg
        (suzukiCausalDepthGammaFeatureOperator h a hh ha
          (lp.single 2 (Sum.inr k) (1 : ℂ)))]

set_option maxHeartbeats 800000 in
/-- The complete actual Gamma feature operator is nuclear before forming its Gram. -/
theorem suzukiCausalDepthGammaFeatureOperator_deningerIsNuclear
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) :
    DeningerIsNuclear (suzukiCausalDepthGammaFeatureOperator h a hh ha) := by
  apply deningerIsNuclear_of_summable_norm_apply_lp_single
  have hw := summable_suzukiCausalDepthGammaWeight_allPrime hh ha
  have hzero : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
  have hmajor : Summable
      (Sum.elim (suzukiCausalDepthGammaWeight h a) (fun _ => 0)) :=
    (hw.hasSum.sum hzero.hasSum).summable
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_suzukiCausalDepthGammaFeatureOperator_single_le h a hh ha) hmajor

/-- **Actual feature nuclearity.** The source feature itself, not only its positive Gram, is
Schatten-one. -/
theorem suzukiCausalDepthGammaFeatureOperator_memSchattenClass_one
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) :
    MemSchattenClass 1 (suzukiCausalDepthGammaFeatureOperator h a hh ha) :=
  (suzukiCausalDepthGammaFeatureOperator_deningerIsNuclear h a hh ha).memSchattenClass_one

theorem suzukiCanonicalCausalDepthGammaFeatureOperator_memSchattenClass_one :
    MemSchattenClass 1 suzukiCanonicalCausalDepthGammaFeatureOperator := by
  simpa [suzukiCanonicalCausalDepthGammaFeatureOperator] using
    suzukiCausalDepthGammaFeatureOperator_memSchattenClass_one
      1 1 zero_lt_one zero_lt_one

/-- Rank-free bounded response trace against the actual pre-Gram feature. -/
def suzukiCausalDepthGammaTraceClassFeatureCorrection
    (R : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2) (N : ℕ) : ℝ :=
  (opTrace (suzukiCanonicalCausalDepthGammaFeatureOperator ∘L
    ContinuousLinearMap.adjoint (R N))).re

/-- The rank-free trace-class extension is exactly the earlier pre-Gram Hilbert--Schmidt pairing,
not a replacement scalarization. -/
theorem suzukiCausalDepthGammaTraceClassFeatureCorrection_eq_quadraticRankHSCorrection
    (R : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2) (N : ℕ) :
    suzukiCausalDepthGammaTraceClassFeatureCorrection R N =
      suzukiCausalDepthGammaQuadraticRankHSCorrection R N := by
  unfold suzukiCausalDepthGammaTraceClassFeatureCorrection
    suzukiCausalDepthGammaQuadraticRankHSCorrection
  rw [← suzukiCanonicalCausalDepthGammaFeatureOperator_memSchattenClass_one.one_opTrace_comp_comm]
  rw [opTrace_comp_eq_hsInner]
  simp

/-- A uniformly operator-bounded response has a sublinear trace correction against the actual
trace-class feature, with no rank restriction. -/
theorem suzukiCausalDepthGammaTraceClassFeatureCorrection_sublinear
    (R : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2)
    (M : ℝ) (hM : 0 ≤ M) (hNorm : ∀ N : ℕ, ‖R N‖ ≤ M) :
    SuzukiTransitionCoreCorrectionSublinear
      (suzukiCausalDepthGammaTraceClassFeatureCorrection R) := by
  change Tendsto (fun N : ℕ =>
    suzukiCausalDepthGammaTraceClassFeatureCorrection R (8 * N) / (N : ℝ))
    atTop (𝓝 0)
  have hC : 0 ≤ traceNorm SuzukiCausalDepthGammaTraceL2
      suzukiCanonicalCausalDepthGammaFeatureOperator * M :=
    mul_nonneg (traceNorm_nonneg _) hM
  have htend : Tendsto (fun N : ℕ =>
      (traceNorm SuzukiCausalDepthGammaTraceL2
        suzukiCanonicalCausalDepthGammaFeatureOperator * M) / (N : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hevent : ∀ᶠ N : ℕ in atTop,
      (traceNorm SuzukiCausalDepthGammaTraceL2
        suzukiCanonicalCausalDepthGammaFeatureOperator * M) / (N : ℝ) < ε :=
    (tendsto_order.1 htend).2 ε hε
  rw [eventually_atTop] at hevent
  obtain ⟨N0, hN0⟩ := hevent
  refine ⟨max N0 1, fun N hNmax => ?_⟩
  have hN : 1 ≤ N := (le_max_right N0 1).trans hNmax
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have htrace :
      ‖opTrace (suzukiCanonicalCausalDepthGammaFeatureOperator ∘L
        ContinuousLinearMap.adjoint (R (8 * N)))‖ ≤
        traceNorm SuzukiCausalDepthGammaTraceL2
          suzukiCanonicalCausalDepthGammaFeatureOperator * M := by
    exact (norm_opTrace_comp_le_norm_mul_traceNorm
      suzukiCanonicalCausalDepthGammaFeatureOperator_memSchattenClass_one
      (ContinuousLinearMap.adjoint (R (8 * N)))).trans
        (mul_le_mul_of_nonneg_left (by simpa using hNorm (8 * N))
          (traceNorm_nonneg _))
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hNpos]
  calc
    |suzukiCausalDepthGammaTraceClassFeatureCorrection R (8 * N)| / (N : ℝ) ≤
        (traceNorm SuzukiCausalDepthGammaTraceL2
          suzukiCanonicalCausalDepthGammaFeatureOperator * M) / (N : ℝ) := by
      apply div_le_div_of_nonneg_right _ hNpos.le
      exact (Complex.abs_re_le_norm _).trans htrace
    _ < ε := hN0 N ((le_max_left N0 1).trans hNmax)

/-- Candidate CCM--FU producer using an arbitrary uniformly bounded response against the actual
trace-class pre-Gram Gamma feature. -/
structure SuzukiCausalDepthGammaTraceClassFeatureWardProducer where
  width : ℝ
  response : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
    SuzukiCausalDepthGammaTraceL2
  opNormCeiling : ℝ
  opNormCeiling_nonneg : 0 ≤ opNormCeiling
  response_opNorm_le : ∀ N : ℕ, ‖response N‖ ≤ opNormCeiling
  lower : ℝ
  ward_semibounded : ∀ᶠ n : ℕ in atTop,
    lower ≤ suzukiRectangularWardDefect width
      (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
        suzukiCausalDepthGammaTraceClassFeatureCorrection response N)
      (8 * n)

/-- **Rank-free bounded producer-class kill.** No uniformly operator-bounded response against the
actual trace-class pre-Gram Gamma feature can semibound the rectangular Ward defect. -/
theorem no_suzukiCausalDepthGammaTraceClassFeatureWardProducer :
    ¬ Nonempty SuzukiCausalDepthGammaTraceClassFeatureWardProducer := by
  rintro ⟨P⟩
  exact no_sublinear_transitionCore_rectangularWardProducer
    ⟨P.width, suzukiCausalDepthGammaTraceClassFeatureCorrection P.response,
      P.lower,
      suzukiCausalDepthGammaTraceClassFeatureCorrection_sublinear
        P.response P.opNormCeiling P.opNormCeiling_nonneg P.response_opNorm_le,
      P.ward_semibounded⟩

end

end RHTower
