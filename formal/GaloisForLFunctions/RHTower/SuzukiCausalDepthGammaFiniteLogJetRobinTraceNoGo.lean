/-
# Fixed logarithmic-jet Robin trace no-go

For every fixed jet order, the exact prime-power Wigner--Smith/Robin logarithmic
multiplier preserves nuclearity of the Suzuki causal-depth Gamma feature. Hence
no uniformly operator-bounded response in this class can produce the required
rectangular Ward lower bound.
-/

import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaTraceClassFeatureRobinTraceNoGo
import GaloisForLFunctions.RHTower.SoninSemilocalWeylGenerator
import GaloisForLFunctions.HTGeometry.PolydiscAnalytic
import GaloisForLFunctions.RHTower.SuzukiV0WeilForm

open Complex Filter Topology ContinuousLinearMap
open scoped InnerProductSpace ENNReal BigOperators
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Fixed logarithmic source-jet multiplier at one labelled prime power. -/
def suzukiCausalDepthGammaLogJetFactor
    (order : ℕ) (pe : Nat.Primes × ℕ) : ℝ :=
  Real.log (xiGammaEulerValuationNat pe : ℝ) ^ order

theorem log_xiGammaEulerValuationNat
    (p : Nat.Primes) (e : ℕ) :
    Real.log (xiGammaEulerValuationNat (p, e) : ℝ) =
      ((e : ℝ) + 1) * Real.log (p : ℝ) := by
  have h := xiGammaEulerBoundaryHalfHeight_eq_half_log_valuation p e
  unfold xiGammaEulerBoundaryHalfHeight at h
  linarith

theorem suzukiCausalDepthGammaLogJetFactor_nonneg
    (order : ℕ) (pe : Nat.Primes × ℕ) :
    0 ≤ suzukiCausalDepthGammaLogJetFactor order pe := by
  rcases pe with ⟨p, e⟩
  rw [suzukiCausalDepthGammaLogJetFactor,
    log_xiGammaEulerValuationNat]
  have hp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  positivity

theorem summable_logPow_mul_suzukiCriticalEntryWallCoherentMajorant
    (h : ℝ) (order : ℕ) :
    Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ order *
        suzukiCriticalEntryWallCoherentMajorant h p) := by
  have hbeta : (1 : ℝ) < 5 / 4 := by norm_num
  have h0 : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ order *
        (p : ℝ) ^ (-(5 / 4 : ℝ))) := by
    have hn : Summable (fun n : ℕ =>
        |Real.log n| ^ order * (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
      summable_abs_log_natCast_pow_mul_rpow_neg order (5 / 4) hbeta
    have hp := hn.comp_injective (i := fun p : Nat.Primes => (p : ℕ))
      Subtype.val_injective
    refine hp.congr (fun p => ?_)
    have hl : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.property.one_lt)
    simp [abs_of_pos hl]
  have h1 : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ (order + 1) *
        (p : ℝ) ^ (-(5 / 4 : ℝ))) := by
    have hn : Summable (fun n : ℕ =>
        |Real.log n| ^ (order + 1) * (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
      summable_abs_log_natCast_pow_mul_rpow_neg (order + 1) (5 / 4) hbeta
    have hp := hn.comp_injective (i := fun p : Nat.Primes => (p : ℕ))
      Subtype.val_injective
    refine hp.congr (fun p => ?_)
    have hl : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.property.one_lt)
    simp [abs_of_pos hl]
  have hsum : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ order * (1 + Real.log (p : ℝ)) *
        (p : ℝ) ^ (-(5 / 4 : ℝ))) := by
    convert h0.add h1 using 1
    funext p
    rw [pow_succ]
    ring
  refine (hsum.mul_left ((h * Real.sqrt h)⁻¹ / 2)).congr (fun p => ?_)
  rw [suzukiCriticalEntryWallCoherentMajorant, Real.rpow_def_of_pos
    (by exact_mod_cast p.property.pos : (0 : ℝ) < (p : ℝ))]
  ring_nf

theorem summable_suzukiCausalDepthGammaLogJetWeight_allPrime
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (order : ℕ) :
    Summable (fun pe : Nat.Primes × ℕ =>
      suzukiCausalDepthGammaLogJetFactor order pe *
        suzukiCausalDepthGammaWeight h a pe) := by
  have hcap0 : 0 < suzukiCoherentCausalDepthRadiusCap := by
    rw [suzukiCoherentCausalDepthRadiusCap]
    positivity
  have hcap1 : suzukiCoherentCausalDepthRadiusCap < 1 :=
    suzukiCoherentCausalDepthRadiusCap_lt_one
  have hcapDepth : Summable (fun e : ℕ =>
      (((e + 1) ^ order : ℕ) : ℝ) *
        suzukiCoherentCausalDepthRadiusCap ^ e) :=
    GaloisForLFunctions.HTGeometry.summable_succ_pow_mul_geometric
      order hcap0.le hcap1
  have hrows : ∀ p : Nat.Primes, Summable (fun e : ℕ =>
      suzukiCausalDepthGammaLogJetFactor order (p, e) *
        suzukiCausalDepthGammaWeight h a (p, e)) := by
    intro p
    have hr0 : 0 < suzukiCriticalApertureDepthFusionRadius h a p :=
      suzukiCriticalApertureDepthFusionRadius_pos h a p
    have hr1 : suzukiCriticalApertureDepthFusionRadius h a p < 1 :=
      suzukiCriticalApertureDepthFusionRadius_lt_one hh ha p
    have hdepth : Summable (fun e : ℕ =>
        (((e + 1) ^ order : ℕ) : ℝ) *
          suzukiCriticalApertureDepthFusionRadius h a p ^ e) :=
      GaloisForLFunctions.HTGeometry.summable_succ_pow_mul_geometric
        order hr0.le hr1
    refine (hdepth.mul_left
      (Real.log (p : ℝ) ^ order *
        suzukiCriticalEntryWallEndpointAmplitude h a p 0)).congr (fun e => ?_)
    rw [suzukiCausalDepthGammaLogJetFactor,
      log_xiGammaEulerValuationNat,
      suzukiCausalDepthGammaWeight, mul_pow]
    push_cast
    ring
  rw [summable_prod_of_nonneg (fun pe =>
    mul_nonneg (suzukiCausalDepthGammaLogJetFactor_nonneg order pe)
      (suzukiCausalDepthGammaWeight_pos hh ha pe).le)]
  refine ⟨hrows, ?_⟩
  let C : ℝ := ∑' e : ℕ,
    (((e + 1) ^ order : ℕ) : ℝ) *
      suzukiCoherentCausalDepthRadiusCap ^ e
  have hprime :=
    summable_logPow_mul_suzukiCriticalEntryWallCoherentMajorant h order
  have hmajor : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ order *
        suzukiCriticalEntryWallCoherentMajorant h p * C) :=
    hprime.mul_right C
  apply Summable.of_nonneg_of_le
    (fun p => tsum_nonneg fun _ =>
      mul_nonneg (suzukiCausalDepthGammaLogJetFactor_nonneg order (p, _))
        (suzukiCausalDepthGammaWeight_pos hh ha (p, _)).le)
    (fun p => ?_) hmajor
  have hr0 : 0 < suzukiCriticalApertureDepthFusionRadius h a p :=
    suzukiCriticalApertureDepthFusionRadius_pos h a p
  have hrCap : suzukiCriticalApertureDepthFusionRadius h a p ≤
      suzukiCoherentCausalDepthRadiusCap :=
    suzukiCriticalApertureDepthFusionRadius_le_coherentCap hh ha p
  have hA : suzukiCriticalEntryWallEndpointAmplitude h a p 0 ≤
      suzukiCriticalEntryWallCoherentMajorant h p :=
    suzukiCriticalEntryWallEndpointAmplitude_zero_le_coherentMajorant hh ha p
  have hM0 : 0 ≤ suzukiCriticalEntryWallCoherentMajorant h p := by
    rw [suzukiCriticalEntryWallCoherentMajorant]
    positivity
  have hmajRow : Summable (fun e : ℕ =>
      (Real.log (p : ℝ) ^ order *
        suzukiCriticalEntryWallCoherentMajorant h p) *
          ((((e + 1) ^ order : ℕ) : ℝ) *
            suzukiCoherentCausalDepthRadiusCap ^ e)) :=
    hcapDepth.mul_left _
  calc
    (∑' e : ℕ,
        suzukiCausalDepthGammaLogJetFactor order (p, e) *
          suzukiCausalDepthGammaWeight h a (p, e)) ≤
        ∑' e : ℕ,
          (Real.log (p : ℝ) ^ order *
            suzukiCriticalEntryWallCoherentMajorant h p) *
              ((((e + 1) ^ order : ℕ) : ℝ) *
                suzukiCoherentCausalDepthRadiusCap ^ e) := by
      apply Summable.tsum_le_tsum
      · intro e
        have hlog : 0 ≤ Real.log (p : ℝ) :=
          (Real.log_pos (by exact_mod_cast p.property.one_lt)).le
        have hscale : 0 ≤ Real.log (p : ℝ) ^ order *
            ((e : ℝ) + 1) ^ order := by positivity
        have hrad :
            suzukiCriticalEntryWallEndpointAmplitude h a p 0 *
                suzukiCriticalApertureDepthFusionRadius h a p ^ e ≤
              suzukiCriticalEntryWallCoherentMajorant h p *
                suzukiCoherentCausalDepthRadiusCap ^ e :=
          mul_le_mul hA
            (pow_le_pow_left₀ hr0.le hrCap e)
            (pow_nonneg hr0.le e) hM0
        calc
          suzukiCausalDepthGammaLogJetFactor order (p, e) *
              suzukiCausalDepthGammaWeight h a (p, e) =
            (Real.log (p : ℝ) ^ order * ((e : ℝ) + 1) ^ order) *
              (suzukiCriticalEntryWallEndpointAmplitude h a p 0 *
                suzukiCriticalApertureDepthFusionRadius h a p ^ e) := by
                  rw [suzukiCausalDepthGammaLogJetFactor,
                    log_xiGammaEulerValuationNat,
                    suzukiCausalDepthGammaWeight, mul_pow]
                  ring
          _ ≤ (Real.log (p : ℝ) ^ order * ((e : ℝ) + 1) ^ order) *
              (suzukiCriticalEntryWallCoherentMajorant h p *
                suzukiCoherentCausalDepthRadiusCap ^ e) :=
            mul_le_mul_of_nonneg_left hrad hscale
          _ = (Real.log (p : ℝ) ^ order *
              suzukiCriticalEntryWallCoherentMajorant h p) *
                ((((e + 1) ^ order : ℕ) : ℝ) *
                  suzukiCoherentCausalDepthRadiusCap ^ e) := by
                    push_cast
                    ring
      · exact hrows p
      · exact hmajRow
    _ = Real.log (p : ℝ) ^ order *
          suzukiCriticalEntryWallCoherentMajorant h p * C := by
      rw [tsum_mul_left]

/-- Actual feature coefficient after a fixed source logarithmic jet. -/
def suzukiCausalDepthGammaLogJetWeightedFeature
    (h a : ℝ) (order : ℕ) (pe : Nat.Primes × ℕ) (k : ℕ) : ℝ :=
  suzukiCausalDepthGammaLogJetFactor order pe *
    suzukiCausalDepthGammaWeightedFeature h a pe k

theorem summable_sq_suzukiCausalDepthGammaLogJetWeightedFeature_row
    (h a : ℝ) (order : ℕ) (pe : Nat.Primes × ℕ) :
    Summable (fun k : ℕ =>
      suzukiCausalDepthGammaLogJetWeightedFeature h a order pe k ^ 2) := by
  refine ((summable_sq_suzukiCausalDepthGammaWeightedFeature_row h a pe).mul_left
    (suzukiCausalDepthGammaLogJetFactor order pe ^ 2)).congr (fun k => ?_)
  rw [suzukiCausalDepthGammaLogJetWeightedFeature]
  ring

theorem tsum_sq_suzukiCausalDepthGammaLogJetWeightedFeature_row
    (h a : ℝ) (order : ℕ) (pe : Nat.Primes × ℕ) :
    (∑' k : ℕ,
      suzukiCausalDepthGammaLogJetWeightedFeature h a order pe k ^ 2) =
      (suzukiCausalDepthGammaLogJetFactor order pe *
        suzukiCausalDepthGammaWeight h a pe) ^ 2 *
          gammaConductorModeSchurResidual
            (suzukiCausalDepthGammaFrequency pe)
            (suzukiCausalDepthGammaFrequency pe) := by
  rw [show (∑' k : ℕ,
      suzukiCausalDepthGammaLogJetWeightedFeature h a order pe k ^ 2) =
      suzukiCausalDepthGammaLogJetFactor order pe ^ 2 *
        ∑' k : ℕ,
          suzukiCausalDepthGammaWeightedFeature h a pe k ^ 2 by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [suzukiCausalDepthGammaLogJetWeightedFeature]
    ring]
  rw [tsum_sq_suzukiCausalDepthGammaWeightedFeature_row]
  ring

theorem summable_sq_suzukiCausalDepthGammaLogJetWeightedFeature_allPrime
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (order : ℕ) :
    Summable (fun z : (Nat.Primes × ℕ) × ℕ =>
      suzukiCausalDepthGammaLogJetWeightedFeature h a order z.1 z.2 ^ 2) := by
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  constructor
  · exact fun pe =>
      summable_sq_suzukiCausalDepthGammaLogJetWeightedFeature_row h a order pe
  · have hweightL1 :=
      summable_suzukiCausalDepthGammaLogJetWeight_allPrime hh ha order
    have hweightSq := summable_sq_of_summable_nonneg
      (fun pe => mul_nonneg
        (suzukiCausalDepthGammaLogJetFactor_nonneg order pe)
        (suzukiCausalDepthGammaWeight_pos hh ha pe).le) hweightL1
    have houter : Summable (fun pe : Nat.Primes × ℕ =>
        (suzukiCausalDepthGammaLogJetFactor order pe *
          suzukiCausalDepthGammaWeight h a pe) ^ 2 *
            gammaConductorModeSchurResidual
              (suzukiCausalDepthGammaFrequency pe)
              (suzukiCausalDepthGammaFrequency pe)) := by
      refine Summable.of_nonneg_of_le (fun pe => ?_) (fun pe => ?_) hweightSq
      · exact mul_nonneg (sq_nonneg _)
          (gammaConductorModeSchurResidual_pos
            (suzukiCausalDepthGammaFrequency_pos pe)
            (suzukiCausalDepthGammaFrequency_pos pe)).le
      · have hr := gammaConductorModeSchurResidual_self_le_one
          (suzukiCausalDepthGammaFrequency pe)
        have hw := sq_nonneg
          (suzukiCausalDepthGammaLogJetFactor order pe *
            suzukiCausalDepthGammaWeight h a pe)
        nlinarith
    refine houter.congr (fun pe => ?_)
    exact (tsum_sq_suzukiCausalDepthGammaLogJetWeightedFeature_row
      h a order pe).symm

/-- Feature matrix after applying one fixed logarithmic source jet. -/
def suzukiCausalDepthGammaLogJetFeatureKernel
    (h a : ℝ) (order : ℕ) :
    SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex → ℂ := fun z =>
  match z with
  | (Sum.inr k, Sum.inl pe) =>
      (suzukiCausalDepthGammaLogJetWeightedFeature h a order pe k : ℂ)
  | _ => 0

private def suzukiCausalDepthGammaLogJetCrossEmbedding :
    (Nat.Primes × ℕ) × ℕ →
      SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex := fun z =>
  (Sum.inr z.2, Sum.inl z.1)

private theorem suzukiCausalDepthGammaLogJetCrossEmbedding_injective :
    Function.Injective suzukiCausalDepthGammaLogJetCrossEmbedding := by
  rintro ⟨pe, k⟩ ⟨qe, l⟩ h
  change (Sum.inr k, Sum.inl pe) = (Sum.inr l, Sum.inl qe) at h
  exact Prod.ext
    (Sum.inl_injective (congrArg Prod.snd h))
    (Sum.inr_injective (congrArg Prod.fst h))

private def suzukiCausalDepthGammaLogJetCrossSupport :
    Set (SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex) :=
  Set.range suzukiCausalDepthGammaLogJetCrossEmbedding

private def suzukiCausalDepthGammaLogJetCrossEquiv :
    ((Nat.Primes × ℕ) × ℕ) ≃ suzukiCausalDepthGammaLogJetCrossSupport :=
  Equiv.ofInjective suzukiCausalDepthGammaLogJetCrossEmbedding
    suzukiCausalDepthGammaLogJetCrossEmbedding_injective

theorem suzukiCausalDepthGammaLogJetFeatureKernel_isHS
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (order : ℕ) :
    HilbertSchmidt.IsHS (suzukiCausalDepthGammaLogJetFeatureKernel h a order) := by
  let energy :
      SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex → ℝ :=
    fun z => ‖suzukiCausalDepthGammaLogJetFeatureKernel h a order z‖ ^ 2
  have hcomp : Summable (fun z : (Nat.Primes × ℕ) × ℕ =>
      energy (suzukiCausalDepthGammaLogJetCrossEquiv z)) := by
    refine (summable_sq_suzukiCausalDepthGammaLogJetWeightedFeature_allPrime
      hh ha order).congr (fun z => ?_)
    change suzukiCausalDepthGammaLogJetWeightedFeature h a order z.1 z.2 ^ 2 =
      ‖(suzukiCausalDepthGammaLogJetWeightedFeature h a order z.1 z.2 : ℂ)‖ ^ 2
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsub : Summable
      (energy ∘ Subtype.val : suzukiCausalDepthGammaLogJetCrossSupport → ℝ) :=
    (suzukiCausalDepthGammaLogJetCrossEquiv.summable_iff).mp hcomp
  have hindicator :
      Summable (suzukiCausalDepthGammaLogJetCrossSupport.indicator energy) :=
    summable_subtype_iff_indicator.mp hsub
  exact hindicator.congr fun z => by
    show suzukiCausalDepthGammaLogJetCrossSupport.indicator energy z =
      ‖suzukiCausalDepthGammaLogJetFeatureKernel h a order z‖ ^ 2
    by_cases hz : z ∈ suzukiCausalDepthGammaLogJetCrossSupport
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      rcases z with ⟨i, j⟩
      cases i <;> cases j <;>
        simp [suzukiCausalDepthGammaLogJetCrossSupport,
          suzukiCausalDepthGammaLogJetCrossEmbedding,
          suzukiCausalDepthGammaLogJetFeatureKernel] at hz ⊢

/-- Bounded realization of the actual feature after a fixed logarithmic source jet. -/
def suzukiCausalDepthGammaLogJetFeatureOperator
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (order : ℕ) :
    SuzukiCausalDepthGammaTraceL2 →L[ℂ] SuzukiCausalDepthGammaTraceL2 :=
  HilbertSchmidt.toOperator
    (suzukiCausalDepthGammaLogJetFeatureKernel_isHS hh ha order)

theorem norm_sq_suzukiCausalDepthGammaLogJetFeatureOperator_single_source
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (order : ℕ)
    (pe : Nat.Primes × ℕ) :
    ‖suzukiCausalDepthGammaLogJetFeatureOperator h a hh ha order
        (lp.single 2 (Sum.inl pe) (1 : ℂ))‖ ^ 2 =
      (suzukiCausalDepthGammaLogJetFactor order pe *
        suzukiCausalDepthGammaWeight h a pe) ^ 2 *
          gammaConductorModeSchurResidual
            (suzukiCausalDepthGammaFrequency pe)
            (suzukiCausalDepthGammaFrequency pe) := by
  rw [suzukiCausalDepthGammaLogJetFeatureOperator,
    HilbertSchmidt.norm_toOperator_single_sq]
  let f : SuzukiCausalDepthGammaTraceIndex → ℝ := fun i =>
    ‖suzukiCausalDepthGammaLogJetFeatureKernel h a order (i, Sum.inl pe)‖ ^ 2
  have hleft : HasSum (f ∘ Sum.inl) 0 := by
    have hz : (f ∘ Sum.inl) =
        (fun _ : Nat.Primes × ℕ => (0 : ℝ)) := by
      funext x
      simp [f, suzukiCausalDepthGammaLogJetFeatureKernel]
    rw [hz]
    exact hasSum_zero
  have hrightSummable : Summable (f ∘ Sum.inr) := by
    refine (summable_sq_suzukiCausalDepthGammaLogJetWeightedFeature_row
      h a order pe).congr (fun k => ?_)
    simp [f, suzukiCausalDepthGammaLogJetFeatureKernel,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsum : HasSum f (0 + ∑' k : ℕ, (f ∘ Sum.inr) k) :=
    hleft.sum hrightSummable.hasSum
  change (∑' i : SuzukiCausalDepthGammaTraceIndex, f i) = _
  rw [hsum.tsum_eq, zero_add]
  rw [show (∑' k : ℕ, (f ∘ Sum.inr) k) =
      ∑' k : ℕ,
        suzukiCausalDepthGammaLogJetWeightedFeature h a order pe k ^ 2 by
    apply tsum_congr
    intro k
    simp [f, suzukiCausalDepthGammaLogJetFeatureKernel,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]]
  exact tsum_sq_suzukiCausalDepthGammaLogJetWeightedFeature_row h a order pe

theorem norm_suzukiCausalDepthGammaLogJetFeatureOperator_single_le
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (order : ℕ)
    (i : SuzukiCausalDepthGammaTraceIndex) :
    ‖suzukiCausalDepthGammaLogJetFeatureOperator h a hh ha order
        (lp.single 2 i (1 : ℂ))‖ ≤
      Sum.elim (fun pe =>
        suzukiCausalDepthGammaLogJetFactor order pe *
          suzukiCausalDepthGammaWeight h a pe) (fun _ => 0) i := by
  cases i with
  | inl pe =>
      simp only [Sum.elim_inl]
      have hsq := norm_sq_suzukiCausalDepthGammaLogJetFeatureOperator_single_source
        h a hh ha order pe
      have hres := gammaConductorModeSchurResidual_self_le_one
        (suzukiCausalDepthGammaFrequency pe)
      have hw : 0 ≤ suzukiCausalDepthGammaLogJetFactor order pe *
          suzukiCausalDepthGammaWeight h a pe :=
        mul_nonneg (suzukiCausalDepthGammaLogJetFactor_nonneg order pe)
          (suzukiCausalDepthGammaWeight_pos hh ha pe).le
      have hn := norm_nonneg
        (suzukiCausalDepthGammaLogJetFeatureOperator h a hh ha order
          (lp.single 2 (Sum.inl pe) (1 : ℂ)))
      nlinarith [sq_nonneg
        (suzukiCausalDepthGammaLogJetFactor order pe *
          suzukiCausalDepthGammaWeight h a pe)]
  | inr k =>
      simp only [Sum.elim_inr]
      have hsq := HilbertSchmidt.norm_toOperator_single_sq
        (suzukiCausalDepthGammaLogJetFeatureKernel_isHS hh ha order) (Sum.inr k)
      change ‖suzukiCausalDepthGammaLogJetFeatureOperator h a hh ha order
        (lp.single 2 (Sum.inr k) (1 : ℂ))‖ ^ 2 =
          ∑' i : SuzukiCausalDepthGammaTraceIndex,
            ‖suzukiCausalDepthGammaLogJetFeatureKernel h a order (i, Sum.inr k)‖ ^ 2 at hsq
      have hzero : (∑' i : SuzukiCausalDepthGammaTraceIndex,
          ‖suzukiCausalDepthGammaLogJetFeatureKernel h a order (i, Sum.inr k)‖ ^ 2) = 0 := by
        simp [suzukiCausalDepthGammaLogJetFeatureKernel]
      rw [hzero] at hsq
      nlinarith [norm_nonneg
        (suzukiCausalDepthGammaLogJetFeatureOperator h a hh ha order
          (lp.single 2 (Sum.inr k) (1 : ℂ)))]

set_option maxHeartbeats 800000 in
theorem suzukiCausalDepthGammaLogJetFeatureOperator_deningerIsNuclear
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (order : ℕ) :
    DeningerIsNuclear
      (suzukiCausalDepthGammaLogJetFeatureOperator h a hh ha order) := by
  apply deningerIsNuclear_of_summable_norm_apply_lp_single
  have hw := summable_suzukiCausalDepthGammaLogJetWeight_allPrime hh ha order
  have hzero : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
  have hmajor : Summable
      (Sum.elim (fun pe =>
        suzukiCausalDepthGammaLogJetFactor order pe *
          suzukiCausalDepthGammaWeight h a pe) (fun _ => 0)) :=
    (hw.hasSum.sum hzero.hasSum).summable
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_suzukiCausalDepthGammaLogJetFeatureOperator_single_le
      h a hh ha order) hmajor

theorem suzukiCausalDepthGammaLogJetFeatureOperator_memSchattenClass_one
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (order : ℕ) :
    MemSchattenClass 1
      (suzukiCausalDepthGammaLogJetFeatureOperator h a hh ha order) :=
  (suzukiCausalDepthGammaLogJetFeatureOperator_deningerIsNuclear
    h a hh ha order).memSchattenClass_one

/-- The represented jet feature scales each actual source column by the literal logarithmic
prime-power jet and changes nothing else. -/
theorem suzukiCausalDepthGammaLogJetFeatureOperator_single_source_eq_smul
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (order : ℕ)
    (pe : Nat.Primes × ℕ) :
    suzukiCausalDepthGammaLogJetFeatureOperator h a hh ha order
        (lp.single 2 (Sum.inl pe) (1 : ℂ)) =
      (suzukiCausalDepthGammaLogJetFactor order pe : ℂ) •
        suzukiCausalDepthGammaFeatureOperator h a hh ha
          (lp.single 2 (Sum.inl pe) (1 : ℂ)) := by
  ext i
  change (suzukiCausalDepthGammaLogJetFeatureOperator h a hh ha order
      (lp.single 2 (Sum.inl pe) (1 : ℂ))) i =
    (suzukiCausalDepthGammaLogJetFactor order pe : ℂ) *
      (suzukiCausalDepthGammaFeatureOperator h a hh ha
        (lp.single 2 (Sum.inl pe) (1 : ℂ))) i
  rw [suzukiCausalDepthGammaLogJetFeatureOperator,
    suzukiCausalDepthGammaFeatureOperator,
    HilbertSchmidt.toOperator_single,
    HilbertSchmidt.toOperator_single]
  cases i with
  | inl qe => simp [suzukiCausalDepthGammaLogJetFeatureKernel,
      suzukiCausalDepthGammaFeatureKernel]
  | inr k =>
      simp [suzukiCausalDepthGammaLogJetFeatureKernel,
        suzukiCausalDepthGammaLogJetWeightedFeature,
        suzukiCausalDepthGammaFeatureKernel,
        suzukiCausalDepthGammaWeightedFeature]

/-- The column multiplier is exactly every real-parameter Wigner--Smith prime-power charge raised
to the fixed jet order. -/
theorem suzukiCausalDepthGammaLogJetFactor_eq_wignerSmithCharge_re_pow
    (order : ℕ) (pe : Nat.Primes × ℕ) (t : ℝ) :
    suzukiCausalDepthGammaLogJetFactor order pe =
      (soninSemilocalWignerSmithCharge pe t).re ^ order := by
  rw [soninSemilocalWignerSmithCharge_eq_log_scale]
  simp only [Complex.ofReal_re, suzukiCausalDepthGammaLogJetFactor]
  have hs : soninSemilocalPrimePowerScale pe =
      (xiGammaEulerValuationNat pe : ℝ) := by
    rcases pe with ⟨p, e⟩
    simp [soninSemilocalPrimePowerScale, xiGammaEulerValuationNat]
  rw [hs]

/-- Actual unit-scale fixed-order logarithmic source-jet feature. -/
def suzukiCanonicalCausalDepthGammaLogJetFeatureOperator (order : ℕ) :
    SuzukiCausalDepthGammaTraceL2 →L[ℂ] SuzukiCausalDepthGammaTraceL2 :=
  suzukiCausalDepthGammaLogJetFeatureOperator
    1 1 zero_lt_one zero_lt_one order

theorem suzukiCanonicalCausalDepthGammaLogJetFeatureOperator_memSchattenClass_one
    (order : ℕ) :
    MemSchattenClass 1
      (suzukiCanonicalCausalDepthGammaLogJetFeatureOperator order) := by
  simpa [suzukiCanonicalCausalDepthGammaLogJetFeatureOperator] using
    suzukiCausalDepthGammaLogJetFeatureOperator_memSchattenClass_one
      1 1 zero_lt_one zero_lt_one order

/-- Rank-free response trace after a fixed exact logarithmic Wigner--Smith/Robin source jet. -/
def suzukiCausalDepthGammaFixedLogJetCorrection
    (order : ℕ)
    (R : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2) (N : ℕ) : ℝ :=
  (opTrace (suzukiCanonicalCausalDepthGammaLogJetFeatureOperator order ∘L
    ContinuousLinearMap.adjoint (R N))).re

/-- Every uniformly operator-bounded response after a fixed source logarithmic jet gives only a
sublinear transition-core correction. -/
theorem suzukiCausalDepthGammaFixedLogJetCorrection_sublinear
    (order : ℕ)
    (R : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2)
    (M : ℝ) (hM : 0 ≤ M) (hNorm : ∀ N : ℕ, ‖R N‖ ≤ M) :
    SuzukiTransitionCoreCorrectionSublinear
      (suzukiCausalDepthGammaFixedLogJetCorrection order R) := by
  change Tendsto (fun N : ℕ =>
    suzukiCausalDepthGammaFixedLogJetCorrection order R (8 * N) / (N : ℝ))
    atTop (𝓝 0)
  have hC : 0 ≤ traceNorm SuzukiCausalDepthGammaTraceL2
      (suzukiCanonicalCausalDepthGammaLogJetFeatureOperator order) * M :=
    mul_nonneg (traceNorm_nonneg _) hM
  have htend : Tendsto (fun N : ℕ =>
      (traceNorm SuzukiCausalDepthGammaTraceL2
        (suzukiCanonicalCausalDepthGammaLogJetFeatureOperator order) * M) /
          (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hevent : ∀ᶠ N : ℕ in atTop,
      (traceNorm SuzukiCausalDepthGammaTraceL2
        (suzukiCanonicalCausalDepthGammaLogJetFeatureOperator order) * M) /
          (N : ℝ) < ε :=
    (tendsto_order.1 htend).2 ε hε
  rw [eventually_atTop] at hevent
  obtain ⟨N0, hN0⟩ := hevent
  refine ⟨max N0 1, fun N hNmax => ?_⟩
  have hN : 1 ≤ N := (le_max_right N0 1).trans hNmax
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have htrace :
      ‖opTrace (suzukiCanonicalCausalDepthGammaLogJetFeatureOperator order ∘L
        ContinuousLinearMap.adjoint (R (8 * N)))‖ ≤
        traceNorm SuzukiCausalDepthGammaTraceL2
          (suzukiCanonicalCausalDepthGammaLogJetFeatureOperator order) * M := by
    exact (norm_opTrace_comp_le_norm_mul_traceNorm
      (suzukiCanonicalCausalDepthGammaLogJetFeatureOperator_memSchattenClass_one order)
      (ContinuousLinearMap.adjoint (R (8 * N)))).trans
        (mul_le_mul_of_nonneg_left (by simpa using hNorm (8 * N))
          (traceNorm_nonneg _))
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hNpos]
  calc
    |suzukiCausalDepthGammaFixedLogJetCorrection order R (8 * N)| / (N : ℝ) ≤
        (traceNorm SuzukiCausalDepthGammaTraceL2
          (suzukiCanonicalCausalDepthGammaLogJetFeatureOperator order) * M) /
            (N : ℝ) := by
      apply div_le_div_of_nonneg_right _ hNpos.le
      exact (Complex.abs_re_le_norm _).trans htrace
    _ < ε := hN0 N ((le_max_left N0 1).trans hNmax)

/-- Candidate CCM--FU producer obtained from an arbitrary fixed-order logarithmic source jet and a
uniformly bounded response. -/
structure SuzukiCausalDepthGammaFixedLogJetWardProducer where
  order : ℕ
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
        suzukiCausalDepthGammaFixedLogJetCorrection order response N)
      (8 * n)

/-- **Finite logarithmic-jet producer-class kill.** No fixed-order Wigner--Smith/Robin source jet
paired with a uniformly bounded response can semibound the rectangular Ward defect. -/
theorem no_suzukiCausalDepthGammaFixedLogJetWardProducer :
    ¬ Nonempty SuzukiCausalDepthGammaFixedLogJetWardProducer := by
  rintro ⟨P⟩
  exact no_sublinear_transitionCore_rectangularWardProducer
    ⟨P.width, suzukiCausalDepthGammaFixedLogJetCorrection P.order P.response,
      P.lower,
      suzukiCausalDepthGammaFixedLogJetCorrection_sublinear
        P.order P.response P.opNormCeiling P.opNormCeiling_nonneg P.response_opNorm_le,
      P.ward_semibounded⟩

end

end RHTower

