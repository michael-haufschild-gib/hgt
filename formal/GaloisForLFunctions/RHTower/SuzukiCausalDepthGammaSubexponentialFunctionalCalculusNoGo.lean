/-
# Subexponential Gamma-frequency functional-calculus no-go

Every discrete zero-exponential-type multiplier on the actual causal-depth Gamma spectrum preserves
nuclearity of the source feature. Therefore no uniformly bounded response in this class can supply
the linear correction forced by rectangular Ward semiboundedness.
-/

import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaFiniteLogJetRobinTraceNoGo

open Complex Filter Topology ContinuousLinearMap
open scoped InnerProductSpace ENNReal BigOperators
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

def suzukiCausalDepthGammaQuarterFrequencyEnvelope
    (pe : Nat.Primes × ℕ) : ℝ :=
  Real.exp (suzukiCausalDepthGammaFrequency pe / 4)

theorem suzukiCausalDepthGammaQuarterFrequencyEnvelope_eq
    (p : Nat.Primes) (e : ℕ) :
    suzukiCausalDepthGammaQuarterFrequencyEnvelope (p, e) =
      Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
        (Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ))) ^ e := by
  rw [suzukiCausalDepthGammaQuarterFrequencyEnvelope,
    suzukiCausalDepthGammaFrequency, log_xiGammaEulerValuationNat]
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

theorem unit_suzukiCriticalApertureDepthFusionRadius_mul_eighth_eq
    (p : Nat.Primes) :
    suzukiCriticalApertureDepthFusionRadius 1 1 p *
        Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) =
      Real.exp (-(9 / 8 : ℝ) * Real.log (p : ℝ)) := by
  rw [suzukiCriticalApertureDepthFusionRadius]
  norm_num
  rw [xiMobiusContinuousApertureDiskNode, ← Real.exp_nat_mul,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem summable_eighthExp_mul_suzukiCriticalEntryWallCoherentMajorant :
    Summable (fun p : Nat.Primes =>
      Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
        suzukiCriticalEntryWallCoherentMajorant 1 p) := by
  have hbeta : (1 : ℝ) < 9 / 8 := by norm_num
  have h0 : Summable (fun p : Nat.Primes =>
      (p : ℝ) ^ (-(9 / 8 : ℝ))) := by
    have hn : Summable (fun n : ℕ =>
        |Real.log n| ^ 0 * (n : ℝ) ^ (-(9 / 8 : ℝ))) :=
      summable_abs_log_natCast_pow_mul_rpow_neg 0 (9 / 8) hbeta
    have hp := hn.comp_injective (i := fun p : Nat.Primes => (p : ℕ))
      Subtype.val_injective
    refine hp.congr (fun p => ?_)
    simp
  have h1 : Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) * (p : ℝ) ^ (-(9 / 8 : ℝ))) := by
    have hn : Summable (fun n : ℕ =>
        |Real.log n| ^ 1 * (n : ℝ) ^ (-(9 / 8 : ℝ))) :=
      summable_abs_log_natCast_pow_mul_rpow_neg 1 (9 / 8) hbeta
    have hp := hn.comp_injective (i := fun p : Nat.Primes => (p : ℕ))
      Subtype.val_injective
    refine hp.congr (fun p => ?_)
    have hl : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.property.one_lt)
    simp [abs_of_pos hl]
  have hsum : Summable (fun p : Nat.Primes =>
      (1 + Real.log (p : ℝ)) * (p : ℝ) ^ (-(9 / 8 : ℝ))) := by
    convert h0.add h1 using 1
    funext p
    ring
  refine (hsum.mul_left (1 / 2 : ℝ)).congr (fun p => ?_)
  rw [suzukiCriticalEntryWallCoherentMajorant,
    Real.rpow_def_of_pos
      (by exact_mod_cast p.property.pos : (0 : ℝ) < (p : ℝ))]
  norm_num
  calc
    1 / 2 * ((1 + Real.log (p : ℝ)) *
        Real.exp (-(Real.log (p : ℝ) * (9 / 8)))) =
      (1 + Real.log (p : ℝ)) / 2 *
        Real.exp (-(9 / 8 : ℝ) * Real.log (p : ℝ)) := by ring
    _ = (1 + Real.log (p : ℝ)) / 2 *
        (Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
          Real.exp (-(5 / 4 : ℝ) * Real.log (p : ℝ))) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ = Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
        ((1 + Real.log (p : ℝ)) / 2 *
          Real.exp (-((5 / 4 : ℝ) * Real.log (p : ℝ)))) := by
      calc
        (1 + Real.log (p : ℝ)) / 2 *
            (Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
              Real.exp (-(5 / 4 : ℝ) * Real.log (p : ℝ))) =
          Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
            ((1 + Real.log (p : ℝ)) / 2 *
              Real.exp (-(5 / 4 : ℝ) * Real.log (p : ℝ))) := by ring
        _ = Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
            ((1 + Real.log (p : ℝ)) / 2 *
              Real.exp (-((5 / 4 : ℝ) * Real.log (p : ℝ)))) :=
          congrArg
            (fun x : ℝ => Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
              ((1 + Real.log (p : ℝ)) / 2 * x))
            (congrArg Real.exp
              (neg_mul (5 / 4 : ℝ) (Real.log (p : ℝ))))

def suzukiCausalDepthGammaSubexponentialDepthCap : ℝ :=
  Real.exp (-(9 / 8 : ℝ) * Real.log 2)

theorem suzukiCausalDepthGammaSubexponentialDepthCap_pos :
    0 < suzukiCausalDepthGammaSubexponentialDepthCap := by
  exact Real.exp_pos _

theorem suzukiCausalDepthGammaSubexponentialDepthCap_lt_one :
    suzukiCausalDepthGammaSubexponentialDepthCap < 1 := by
  rw [suzukiCausalDepthGammaSubexponentialDepthCap, Real.exp_lt_one_iff]
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  nlinarith

theorem unit_suzukiCriticalApertureDepthFusionRadius_mul_eighth_le_cap
    (p : Nat.Primes) :
    suzukiCriticalApertureDepthFusionRadius 1 1 p *
        Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) ≤
      suzukiCausalDepthGammaSubexponentialDepthCap := by
  rw [unit_suzukiCriticalApertureDepthFusionRadius_mul_eighth_eq,
    suzukiCausalDepthGammaSubexponentialDepthCap]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log 2 ≤ Real.log (p : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast p.property.two_le
  nlinarith

theorem summable_quarterFrequencyEnvelope_mul_suzukiCausalDepthGammaWeight :
    Summable (fun pe : Nat.Primes × ℕ =>
      suzukiCausalDepthGammaQuarterFrequencyEnvelope pe *
        suzukiCausalDepthGammaWeight 1 1 pe) := by
  have hcap0 : 0 < suzukiCausalDepthGammaSubexponentialDepthCap :=
    suzukiCausalDepthGammaSubexponentialDepthCap_pos
  have hcap1 : suzukiCausalDepthGammaSubexponentialDepthCap < 1 :=
    suzukiCausalDepthGammaSubexponentialDepthCap_lt_one
  have hcapGeom : Summable (fun e : ℕ =>
      suzukiCausalDepthGammaSubexponentialDepthCap ^ e) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_pos hcap0]
    exact hcap1
  have hrows : ∀ p : Nat.Primes, Summable (fun e : ℕ =>
      suzukiCausalDepthGammaQuarterFrequencyEnvelope (p, e) *
        suzukiCausalDepthGammaWeight 1 1 (p, e)) := by
    intro p
    have hr0 : 0 < suzukiCriticalApertureDepthFusionRadius 1 1 p :=
      suzukiCriticalApertureDepthFusionRadius_pos 1 1 p
    have hb0 : 0 < Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) :=
      Real.exp_pos _
    have hratio :
        suzukiCriticalApertureDepthFusionRadius 1 1 p *
            Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) < 1 :=
      (unit_suzukiCriticalApertureDepthFusionRadius_mul_eighth_le_cap p).trans_lt
        hcap1
    have hgeom : Summable (fun e : ℕ =>
        (suzukiCriticalApertureDepthFusionRadius 1 1 p *
          Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ))) ^ e) := by
      apply summable_geometric_of_norm_lt_one
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos hr0 hb0)]
      exact hratio
    refine (hgeom.mul_left
      (Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
        suzukiCriticalEntryWallEndpointAmplitude 1 1 p 0)).congr (fun e => ?_)
    rw [suzukiCausalDepthGammaQuarterFrequencyEnvelope_eq,
      suzukiCausalDepthGammaWeight, mul_pow]
    ring
  apply (summable_prod_of_nonneg (fun pe => mul_nonneg
    (Real.exp_nonneg _)
    (suzukiCausalDepthGammaWeight_pos zero_lt_one zero_lt_one pe).le)).2
  constructor
  · exact hrows
  · let C : ℝ := ∑' e : ℕ,
      suzukiCausalDepthGammaSubexponentialDepthCap ^ e
    have hprime :=
      summable_eighthExp_mul_suzukiCriticalEntryWallCoherentMajorant
    have hmajor : Summable (fun p : Nat.Primes =>
        (Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
          suzukiCriticalEntryWallCoherentMajorant 1 p) * C) :=
      hprime.mul_right C
    apply Summable.of_nonneg_of_le
      (fun p => tsum_nonneg fun _ => mul_nonneg
        (Real.exp_nonneg _)
        (suzukiCausalDepthGammaWeight_pos zero_lt_one zero_lt_one (p, _)).le)
      (fun p => ?_) hmajor
    have hr0 : 0 < suzukiCriticalApertureDepthFusionRadius 1 1 p :=
      suzukiCriticalApertureDepthFusionRadius_pos 1 1 p
    have hb0 : 0 < Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) :=
      Real.exp_pos _
    have hrCap :=
      unit_suzukiCriticalApertureDepthFusionRadius_mul_eighth_le_cap p
    have hA : suzukiCriticalEntryWallEndpointAmplitude 1 1 p 0 ≤
        suzukiCriticalEntryWallCoherentMajorant 1 p :=
      suzukiCriticalEntryWallEndpointAmplitude_zero_le_coherentMajorant
        zero_lt_one zero_lt_one p
    have hM0 : 0 ≤ suzukiCriticalEntryWallCoherentMajorant 1 p := by
      rw [suzukiCriticalEntryWallCoherentMajorant]
      positivity
    have hmajRow : Summable (fun e : ℕ =>
        (Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
          suzukiCriticalEntryWallCoherentMajorant 1 p) *
            suzukiCausalDepthGammaSubexponentialDepthCap ^ e) :=
      hcapGeom.mul_left _
    calc
      (∑' e : ℕ,
          suzukiCausalDepthGammaQuarterFrequencyEnvelope (p, e) *
            suzukiCausalDepthGammaWeight 1 1 (p, e)) ≤
        ∑' e : ℕ,
          (Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
            suzukiCriticalEntryWallCoherentMajorant 1 p) *
              suzukiCausalDepthGammaSubexponentialDepthCap ^ e := by
        apply Summable.tsum_le_tsum
        · intro e
          rw [suzukiCausalDepthGammaQuarterFrequencyEnvelope_eq,
            suzukiCausalDepthGammaWeight]
          have hpow :
              (suzukiCriticalApertureDepthFusionRadius 1 1 p *
                Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ))) ^ e ≤
                suzukiCausalDepthGammaSubexponentialDepthCap ^ e :=
            pow_le_pow_left₀ (mul_pos hr0 hb0).le hrCap e
          calc
            Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
                Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) ^ e *
                  (suzukiCriticalEntryWallEndpointAmplitude 1 1 p 0 *
                    suzukiCriticalApertureDepthFusionRadius 1 1 p ^ e) =
              (Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
                suzukiCriticalEntryWallEndpointAmplitude 1 1 p 0) *
                (suzukiCriticalApertureDepthFusionRadius 1 1 p *
                  Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ))) ^ e := by
                    rw [mul_pow]
                    ring
            _ ≤ (Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
                suzukiCriticalEntryWallCoherentMajorant 1 p) *
                  suzukiCausalDepthGammaSubexponentialDepthCap ^ e := by
              gcongr
        · exact hrows p
        · exact hmajRow
      _ = (Real.exp ((1 / 8 : ℝ) * Real.log (p : ℝ)) *
          suzukiCriticalEntryWallCoherentMajorant 1 p) * C := by
        rw [tsum_mul_left]

/-- Discrete zero-exponential-type growth on the actual Gamma source spectrum. -/
def SuzukiCausalDepthGammaMultiplierSubexponential
    (m : Nat.Primes × ℕ → ℂ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ pe,
    ‖m pe‖ ≤ C * Real.exp (δ * suzukiCausalDepthGammaFrequency pe)

theorem summable_norm_mul_suzukiCausalDepthGammaWeight_of_subexponential
    {m : Nat.Primes × ℕ → ℂ}
    (hm : SuzukiCausalDepthGammaMultiplierSubexponential m) :
    Summable (fun pe : Nat.Primes × ℕ =>
      ‖m pe‖ * suzukiCausalDepthGammaWeight 1 1 pe) := by
  obtain ⟨C, hC, hbound⟩ := hm (1 / 4) (by norm_num)
  have henv :=
    summable_quarterFrequencyEnvelope_mul_suzukiCausalDepthGammaWeight
  have hmajor : Summable (fun pe : Nat.Primes × ℕ =>
      C * (suzukiCausalDepthGammaQuarterFrequencyEnvelope pe *
        suzukiCausalDepthGammaWeight 1 1 pe)) :=
    henv.mul_left C
  refine Summable.of_nonneg_of_le
    (fun pe => mul_nonneg (norm_nonneg _) (suzukiCausalDepthGammaWeight_pos
      zero_lt_one zero_lt_one pe).le)
    (fun pe => ?_) hmajor
  have hw := (suzukiCausalDepthGammaWeight_pos
    zero_lt_one zero_lt_one pe).le
  calc
    ‖m pe‖ * suzukiCausalDepthGammaWeight 1 1 pe ≤
        (C * Real.exp ((1 / 4 : ℝ) *
          suzukiCausalDepthGammaFrequency pe)) *
            suzukiCausalDepthGammaWeight 1 1 pe :=
      mul_le_mul_of_nonneg_right (hbound pe) hw
    _ = C * (suzukiCausalDepthGammaQuarterFrequencyEnvelope pe *
        suzukiCausalDepthGammaWeight 1 1 pe) := by
      rw [suzukiCausalDepthGammaQuarterFrequencyEnvelope]
      have hexp : Real.exp ((1 / 4 : ℝ) *
          suzukiCausalDepthGammaFrequency pe) =
          Real.exp (suzukiCausalDepthGammaFrequency pe / 4) := by
        congr 1
        ring
      rw [hexp]
      ring

/-- Actual Gamma feature after a discrete source functional calculus multiplier. -/
def suzukiCausalDepthGammaSubexponentialWeightedFeature
    (m : Nat.Primes × ℕ → ℂ) (pe : Nat.Primes × ℕ) (k : ℕ) : ℂ :=
  m pe * (suzukiCausalDepthGammaWeightedFeature 1 1 pe k : ℂ)

theorem summable_norm_sq_suzukiCausalDepthGammaSubexponentialWeightedFeature_row
    (m : Nat.Primes × ℕ → ℂ) (pe : Nat.Primes × ℕ) :
    Summable (fun k : ℕ =>
      ‖suzukiCausalDepthGammaSubexponentialWeightedFeature m pe k‖ ^ 2) := by
  refine ((summable_sq_suzukiCausalDepthGammaWeightedFeature_row 1 1 pe).mul_left
    (‖m pe‖ ^ 2)).congr (fun k => ?_)
  rw [suzukiCausalDepthGammaSubexponentialWeightedFeature, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem tsum_norm_sq_suzukiCausalDepthGammaSubexponentialWeightedFeature_row
    (m : Nat.Primes × ℕ → ℂ) (pe : Nat.Primes × ℕ) :
    (∑' k : ℕ,
      ‖suzukiCausalDepthGammaSubexponentialWeightedFeature m pe k‖ ^ 2) =
      (‖m pe‖ * suzukiCausalDepthGammaWeight 1 1 pe) ^ 2 *
        gammaConductorModeSchurResidual
          (suzukiCausalDepthGammaFrequency pe)
          (suzukiCausalDepthGammaFrequency pe) := by
  rw [show (∑' k : ℕ,
      ‖suzukiCausalDepthGammaSubexponentialWeightedFeature m pe k‖ ^ 2) =
      ‖m pe‖ ^ 2 * ∑' k : ℕ,
        suzukiCausalDepthGammaWeightedFeature 1 1 pe k ^ 2 by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [suzukiCausalDepthGammaSubexponentialWeightedFeature, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ]
  rw [tsum_sq_suzukiCausalDepthGammaWeightedFeature_row]
  ring

theorem summable_norm_sq_suzukiCausalDepthGammaSubexponentialWeightedFeature_allPrime
    {m : Nat.Primes × ℕ → ℂ}
    (hm : SuzukiCausalDepthGammaMultiplierSubexponential m) :
    Summable (fun z : (Nat.Primes × ℕ) × ℕ =>
      ‖suzukiCausalDepthGammaSubexponentialWeightedFeature m z.1 z.2‖ ^ 2) := by
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).2
  constructor
  · exact fun pe =>
      summable_norm_sq_suzukiCausalDepthGammaSubexponentialWeightedFeature_row m pe
  · have hweightL1 :=
      summable_norm_mul_suzukiCausalDepthGammaWeight_of_subexponential hm
    have hweightSq := summable_sq_of_summable_nonneg
      (fun pe => mul_nonneg (norm_nonneg _)
        (suzukiCausalDepthGammaWeight_pos zero_lt_one zero_lt_one pe).le)
      hweightL1
    have houter : Summable (fun pe : Nat.Primes × ℕ =>
        (‖m pe‖ * suzukiCausalDepthGammaWeight 1 1 pe) ^ 2 *
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
          (‖m pe‖ * suzukiCausalDepthGammaWeight 1 1 pe)
        nlinarith
    refine houter.congr (fun pe => ?_)
    exact (tsum_norm_sq_suzukiCausalDepthGammaSubexponentialWeightedFeature_row
      m pe).symm

/-- Feature matrix after a zero-exponential-type source functional calculus. -/
def suzukiCausalDepthGammaSubexponentialFeatureKernel
    (m : Nat.Primes × ℕ → ℂ) :
    SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex → ℂ := fun z =>
  match z with
  | (Sum.inr k, Sum.inl pe) =>
      suzukiCausalDepthGammaSubexponentialWeightedFeature m pe k
  | _ => 0

private def suzukiCausalDepthGammaSubexponentialCrossEmbedding :
    (Nat.Primes × ℕ) × ℕ →
      SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex := fun z =>
  (Sum.inr z.2, Sum.inl z.1)

private theorem suzukiCausalDepthGammaSubexponentialCrossEmbedding_injective :
    Function.Injective suzukiCausalDepthGammaSubexponentialCrossEmbedding := by
  rintro ⟨pe, k⟩ ⟨qe, l⟩ h
  change (Sum.inr k, Sum.inl pe) = (Sum.inr l, Sum.inl qe) at h
  exact Prod.ext
    (Sum.inl_injective (congrArg Prod.snd h))
    (Sum.inr_injective (congrArg Prod.fst h))

private def suzukiCausalDepthGammaSubexponentialCrossSupport :
    Set (SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex) :=
  Set.range suzukiCausalDepthGammaSubexponentialCrossEmbedding

private def suzukiCausalDepthGammaSubexponentialCrossEquiv :
    ((Nat.Primes × ℕ) × ℕ) ≃ suzukiCausalDepthGammaSubexponentialCrossSupport :=
  Equiv.ofInjective suzukiCausalDepthGammaSubexponentialCrossEmbedding
    suzukiCausalDepthGammaSubexponentialCrossEmbedding_injective

theorem suzukiCausalDepthGammaSubexponentialFeatureKernel_isHS
    {m : Nat.Primes × ℕ → ℂ}
    (hm : SuzukiCausalDepthGammaMultiplierSubexponential m) :
    HilbertSchmidt.IsHS (suzukiCausalDepthGammaSubexponentialFeatureKernel m) := by
  let energy :
      SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex → ℝ :=
    fun z => ‖suzukiCausalDepthGammaSubexponentialFeatureKernel m z‖ ^ 2
  have hcomp : Summable (fun z : (Nat.Primes × ℕ) × ℕ =>
      energy (suzukiCausalDepthGammaSubexponentialCrossEquiv z)) := by
    refine (summable_norm_sq_suzukiCausalDepthGammaSubexponentialWeightedFeature_allPrime
      hm).congr (fun z => ?_)
    rfl
  have hsub : Summable
      (energy ∘ Subtype.val : suzukiCausalDepthGammaSubexponentialCrossSupport → ℝ) :=
    (suzukiCausalDepthGammaSubexponentialCrossEquiv.summable_iff).mp hcomp
  have hindicator : Summable
      (suzukiCausalDepthGammaSubexponentialCrossSupport.indicator energy) :=
    summable_subtype_iff_indicator.mp hsub
  exact hindicator.congr fun z => by
    show suzukiCausalDepthGammaSubexponentialCrossSupport.indicator energy z =
      ‖suzukiCausalDepthGammaSubexponentialFeatureKernel m z‖ ^ 2
    by_cases hz : z ∈ suzukiCausalDepthGammaSubexponentialCrossSupport
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      rcases z with ⟨i, j⟩
      cases i <;> cases j <;>
        simp [suzukiCausalDepthGammaSubexponentialCrossSupport,
          suzukiCausalDepthGammaSubexponentialCrossEmbedding,
          suzukiCausalDepthGammaSubexponentialFeatureKernel] at hz ⊢

/-- Bounded realization after a zero-exponential-type source functional calculus. -/
def suzukiCausalDepthGammaSubexponentialFeatureOperator
    (m : Nat.Primes × ℕ → ℂ)
    (hm : SuzukiCausalDepthGammaMultiplierSubexponential m) :
    SuzukiCausalDepthGammaTraceL2 →L[ℂ] SuzukiCausalDepthGammaTraceL2 :=
  HilbertSchmidt.toOperator
    (suzukiCausalDepthGammaSubexponentialFeatureKernel_isHS hm)

theorem norm_sq_suzukiCausalDepthGammaSubexponentialFeatureOperator_single_source
    (m : Nat.Primes × ℕ → ℂ)
    (hm : SuzukiCausalDepthGammaMultiplierSubexponential m)
    (pe : Nat.Primes × ℕ) :
    ‖suzukiCausalDepthGammaSubexponentialFeatureOperator m hm
        (lp.single 2 (Sum.inl pe) (1 : ℂ))‖ ^ 2 =
      (‖m pe‖ * suzukiCausalDepthGammaWeight 1 1 pe) ^ 2 *
        gammaConductorModeSchurResidual
          (suzukiCausalDepthGammaFrequency pe)
          (suzukiCausalDepthGammaFrequency pe) := by
  rw [suzukiCausalDepthGammaSubexponentialFeatureOperator,
    HilbertSchmidt.norm_toOperator_single_sq]
  let f : SuzukiCausalDepthGammaTraceIndex → ℝ := fun i =>
    ‖suzukiCausalDepthGammaSubexponentialFeatureKernel m
      (i, Sum.inl pe)‖ ^ 2
  have hleft : HasSum (f ∘ Sum.inl) 0 := by
    have hz : (f ∘ Sum.inl) =
        (fun _ : Nat.Primes × ℕ => (0 : ℝ)) := by
      funext x
      simp [f, suzukiCausalDepthGammaSubexponentialFeatureKernel]
    rw [hz]
    exact hasSum_zero
  have hrightSummable : Summable (f ∘ Sum.inr) := by
    refine (summable_norm_sq_suzukiCausalDepthGammaSubexponentialWeightedFeature_row
      m pe).congr (fun k => ?_)
    rfl
  have hsum : HasSum f (0 + ∑' k : ℕ, (f ∘ Sum.inr) k) :=
    hleft.sum hrightSummable.hasSum
  change (∑' i : SuzukiCausalDepthGammaTraceIndex, f i) = _
  rw [hsum.tsum_eq, zero_add]
  rw [show (∑' k : ℕ, (f ∘ Sum.inr) k) =
      ∑' k : ℕ,
        ‖suzukiCausalDepthGammaSubexponentialWeightedFeature m pe k‖ ^ 2 by
    apply tsum_congr
    intro k
    rfl]
  exact tsum_norm_sq_suzukiCausalDepthGammaSubexponentialWeightedFeature_row m pe

theorem norm_suzukiCausalDepthGammaSubexponentialFeatureOperator_single_le
    (m : Nat.Primes × ℕ → ℂ)
    (hm : SuzukiCausalDepthGammaMultiplierSubexponential m)
    (i : SuzukiCausalDepthGammaTraceIndex) :
    ‖suzukiCausalDepthGammaSubexponentialFeatureOperator m hm
        (lp.single 2 i (1 : ℂ))‖ ≤
      Sum.elim (fun pe =>
        ‖m pe‖ * suzukiCausalDepthGammaWeight 1 1 pe) (fun _ => 0) i := by
  cases i with
  | inl pe =>
      simp only [Sum.elim_inl]
      have hsq :=
        norm_sq_suzukiCausalDepthGammaSubexponentialFeatureOperator_single_source
          m hm pe
      have hres := gammaConductorModeSchurResidual_self_le_one
        (suzukiCausalDepthGammaFrequency pe)
      have hw : 0 ≤ ‖m pe‖ * suzukiCausalDepthGammaWeight 1 1 pe :=
        mul_nonneg (norm_nonneg _)
          (suzukiCausalDepthGammaWeight_pos zero_lt_one zero_lt_one pe).le
      have hn := norm_nonneg
        (suzukiCausalDepthGammaSubexponentialFeatureOperator m hm
          (lp.single 2 (Sum.inl pe) (1 : ℂ)))
      nlinarith [sq_nonneg
        (‖m pe‖ * suzukiCausalDepthGammaWeight 1 1 pe)]
  | inr k =>
      simp only [Sum.elim_inr]
      have hsq := HilbertSchmidt.norm_toOperator_single_sq
        (suzukiCausalDepthGammaSubexponentialFeatureKernel_isHS hm) (Sum.inr k)
      change ‖suzukiCausalDepthGammaSubexponentialFeatureOperator m hm
        (lp.single 2 (Sum.inr k) (1 : ℂ))‖ ^ 2 =
          ∑' i : SuzukiCausalDepthGammaTraceIndex,
            ‖suzukiCausalDepthGammaSubexponentialFeatureKernel m
              (i, Sum.inr k)‖ ^ 2 at hsq
      have hzero : (∑' i : SuzukiCausalDepthGammaTraceIndex,
          ‖suzukiCausalDepthGammaSubexponentialFeatureKernel m
            (i, Sum.inr k)‖ ^ 2) = 0 := by
        simp [suzukiCausalDepthGammaSubexponentialFeatureKernel]
      rw [hzero] at hsq
      nlinarith [norm_nonneg
        (suzukiCausalDepthGammaSubexponentialFeatureOperator m hm
          (lp.single 2 (Sum.inr k) (1 : ℂ)))]

set_option maxHeartbeats 800000 in
theorem suzukiCausalDepthGammaSubexponentialFeatureOperator_deningerIsNuclear
    (m : Nat.Primes × ℕ → ℂ)
    (hm : SuzukiCausalDepthGammaMultiplierSubexponential m) :
    DeningerIsNuclear
      (suzukiCausalDepthGammaSubexponentialFeatureOperator m hm) := by
  apply deningerIsNuclear_of_summable_norm_apply_lp_single
  have hw :=
    summable_norm_mul_suzukiCausalDepthGammaWeight_of_subexponential hm
  have hzero : Summable (fun _ : ℕ => (0 : ℝ)) := summable_zero
  have hmajor : Summable
      (Sum.elim (fun pe =>
        ‖m pe‖ * suzukiCausalDepthGammaWeight 1 1 pe) (fun _ => 0)) :=
    (hw.hasSum.sum hzero.hasSum).summable
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_suzukiCausalDepthGammaSubexponentialFeatureOperator_single_le m hm)
    hmajor

theorem suzukiCausalDepthGammaSubexponentialFeatureOperator_memSchattenClass_one
    (m : Nat.Primes × ℕ → ℂ)
    (hm : SuzukiCausalDepthGammaMultiplierSubexponential m) :
    MemSchattenClass 1
      (suzukiCausalDepthGammaSubexponentialFeatureOperator m hm) :=
  (suzukiCausalDepthGammaSubexponentialFeatureOperator_deningerIsNuclear
    m hm).memSchattenClass_one

/-- The represented feature scales exactly by the requested source functional calculus. -/
theorem suzukiCausalDepthGammaSubexponentialFeatureOperator_single_source_eq_smul
    (m : Nat.Primes × ℕ → ℂ)
    (hm : SuzukiCausalDepthGammaMultiplierSubexponential m)
    (pe : Nat.Primes × ℕ) :
    suzukiCausalDepthGammaSubexponentialFeatureOperator m hm
        (lp.single 2 (Sum.inl pe) (1 : ℂ)) =
      m pe • suzukiCausalDepthGammaFeatureOperator
        1 1 zero_lt_one zero_lt_one
          (lp.single 2 (Sum.inl pe) (1 : ℂ)) := by
  ext i
  change (suzukiCausalDepthGammaSubexponentialFeatureOperator m hm
      (lp.single 2 (Sum.inl pe) (1 : ℂ))) i =
    m pe * (suzukiCausalDepthGammaFeatureOperator
      1 1 zero_lt_one zero_lt_one
        (lp.single 2 (Sum.inl pe) (1 : ℂ))) i
  rw [suzukiCausalDepthGammaSubexponentialFeatureOperator,
    suzukiCausalDepthGammaFeatureOperator,
    HilbertSchmidt.toOperator_single,
    HilbertSchmidt.toOperator_single]
  cases i with
  | inl qe => simp [suzukiCausalDepthGammaSubexponentialFeatureKernel,
      suzukiCausalDepthGammaFeatureKernel]
  | inr k =>
      simp [suzukiCausalDepthGammaSubexponentialFeatureKernel,
        suzukiCausalDepthGammaSubexponentialWeightedFeature,
        suzukiCausalDepthGammaFeatureKernel,
        suzukiCausalDepthGammaWeightedFeature]

/-- Rank-free response trace after a zero-exponential-type source functional calculus. -/
def suzukiCausalDepthGammaSubexponentialCorrection
    (m : Nat.Primes × ℕ → ℂ)
    (hm : SuzukiCausalDepthGammaMultiplierSubexponential m)
    (R : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2) (N : ℕ) : ℝ :=
  (opTrace (suzukiCausalDepthGammaSubexponentialFeatureOperator m hm ∘L
    ContinuousLinearMap.adjoint (R N))).re

/-- Every bounded response against a zero-type source calculus is asymptotically negligible at
the transition-core scale. -/
theorem suzukiCausalDepthGammaSubexponentialCorrection_sublinear
    (m : Nat.Primes × ℕ → ℂ)
    (hm : SuzukiCausalDepthGammaMultiplierSubexponential m)
    (R : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2)
    (M : ℝ) (hM : 0 ≤ M) (hNorm : ∀ N : ℕ, ‖R N‖ ≤ M) :
    SuzukiTransitionCoreCorrectionSublinear
      (suzukiCausalDepthGammaSubexponentialCorrection m hm R) := by
  change Tendsto (fun N : ℕ =>
    suzukiCausalDepthGammaSubexponentialCorrection m hm R (8 * N) / (N : ℝ))
    atTop (𝓝 0)
  have hC : 0 ≤ traceNorm SuzukiCausalDepthGammaTraceL2
      (suzukiCausalDepthGammaSubexponentialFeatureOperator m hm) * M :=
    mul_nonneg (traceNorm_nonneg _) hM
  have htend : Tendsto (fun N : ℕ =>
      (traceNorm SuzukiCausalDepthGammaTraceL2
        (suzukiCausalDepthGammaSubexponentialFeatureOperator m hm) * M) /
          (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hevent : ∀ᶠ N : ℕ in atTop,
      (traceNorm SuzukiCausalDepthGammaTraceL2
        (suzukiCausalDepthGammaSubexponentialFeatureOperator m hm) * M) /
          (N : ℝ) < ε :=
    (tendsto_order.1 htend).2 ε hε
  rw [eventually_atTop] at hevent
  obtain ⟨N0, hN0⟩ := hevent
  refine ⟨max N0 1, fun N hNmax => ?_⟩
  have hN : 1 ≤ N := (le_max_right N0 1).trans hNmax
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have htrace :
      ‖opTrace (suzukiCausalDepthGammaSubexponentialFeatureOperator m hm ∘L
        ContinuousLinearMap.adjoint (R (8 * N)))‖ ≤
        traceNorm SuzukiCausalDepthGammaTraceL2
          (suzukiCausalDepthGammaSubexponentialFeatureOperator m hm) * M := by
    exact (norm_opTrace_comp_le_norm_mul_traceNorm
      (suzukiCausalDepthGammaSubexponentialFeatureOperator_memSchattenClass_one
        m hm)
      (ContinuousLinearMap.adjoint (R (8 * N)))).trans
        (mul_le_mul_of_nonneg_left (by simpa using hNorm (8 * N))
          (traceNorm_nonneg _))
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hNpos]
  calc
    |suzukiCausalDepthGammaSubexponentialCorrection m hm R (8 * N)| /
          (N : ℝ) ≤
        (traceNorm SuzukiCausalDepthGammaTraceL2
          (suzukiCausalDepthGammaSubexponentialFeatureOperator m hm) * M) /
            (N : ℝ) := by
      apply div_le_div_of_nonneg_right _ hNpos.le
      exact (Complex.abs_re_le_norm _).trans htrace
    _ < ε := hN0 N ((le_max_left N0 1).trans hNmax)

/-- Candidate CCM--FU producer built from arbitrary discrete zero-exponential-type source
functional calculus and a uniformly bounded response. -/
structure SuzukiCausalDepthGammaSubexponentialWardProducer where
  multiplier : Nat.Primes × ℕ → ℂ
  multiplier_subexponential :
    SuzukiCausalDepthGammaMultiplierSubexponential multiplier
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
        suzukiCausalDepthGammaSubexponentialCorrection multiplier
          multiplier_subexponential response N)
      (8 * n)

/-- **Zero-exponential-type functional-calculus producer-class kill.** No such source calculus,
paired with a uniformly bounded response, can semibound the rectangular Ward defect. -/
theorem no_suzukiCausalDepthGammaSubexponentialWardProducer :
    ¬ Nonempty SuzukiCausalDepthGammaSubexponentialWardProducer := by
  rintro ⟨P⟩
  exact no_sublinear_transitionCore_rectangularWardProducer
    ⟨P.width,
      suzukiCausalDepthGammaSubexponentialCorrection P.multiplier
        P.multiplier_subexponential P.response,
      P.lower,
      suzukiCausalDepthGammaSubexponentialCorrection_sublinear
        P.multiplier P.multiplier_subexponential P.response
          P.opNormCeiling P.opNormCeiling_nonneg P.response_opNorm_le,
      P.ward_semibounded⟩

end

end RHTower
