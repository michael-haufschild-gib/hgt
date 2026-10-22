import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaQuadraticRankHSRobinTraceNoGo
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaSubexponentialFunctionalCalculusNoGo

/-!
# Fixed diagonal Gamma graph-source no-go

Let an arbitrary cutoff-independent diagonal multiplier act on the actual prime-depth Gamma
source. If the transformed source is admitted by the ambient Hilbert graph, its weighted
coefficients are square summable and therefore define one fixed Hilbert--Schmidt feature.
Finite-rank density then makes its pairing with every uniformly bounded response of rank at most
`(qN)^(2 : ℕ)` sublinear. This contradicts the linear correction forced by rectangular Ward
semiboundedness.

Thus no fixed diagonal Hilbert-source functional calculus can close the CCM--FU Ward gate through
its natural quadratic-rank response. A survivor must move with the cutoff, have superquadratic
rank, blow up in operator norm, be non-diagonal, or leave the Hilbert graph for a distributional
relative trace.
-/

open Complex Filter Topology ContinuousLinearMap
open scoped InnerProductSpace
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Hilbert graph admission of an arbitrary fixed diagonal multiplier on the actual causal-depth
Gamma source. -/
def SuzukiCausalDepthGammaFixedDiagonalGraphAdmissible
    (m : Nat.Primes × ℕ → ℂ) : Prop :=
  Summable (fun pe : Nat.Primes × ℕ =>
    (‖m pe‖ * suzukiCausalDepthGammaWeight 1 1 pe) ^ (2 : ℕ))

theorem summable_norm_sq_suzukiCausalDepthGammaFixedDiagonalWeightedFeature_allPrime
    {m : Nat.Primes × ℕ → ℂ}
    (hm : SuzukiCausalDepthGammaFixedDiagonalGraphAdmissible m) :
    Summable (fun z : (Nat.Primes × ℕ) × ℕ =>
      ‖suzukiCausalDepthGammaSubexponentialWeightedFeature m z.1 z.2‖ ^ (2 : ℕ)) := by
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).2
  constructor
  · exact fun pe =>
      summable_norm_sq_suzukiCausalDepthGammaSubexponentialWeightedFeature_row m pe
  · have houter : Summable (fun pe : Nat.Primes × ℕ =>
        (‖m pe‖ * suzukiCausalDepthGammaWeight 1 1 pe) ^ (2 : ℕ) *
          gammaConductorModeSchurResidual
            (suzukiCausalDepthGammaFrequency pe)
            (suzukiCausalDepthGammaFrequency pe)) := by
      refine Summable.of_nonneg_of_le (fun pe => ?_) (fun pe => ?_) hm
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

private def suzukiCausalDepthGammaFixedDiagonalCrossEmbedding :
    (Nat.Primes × ℕ) × ℕ →
      SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex := fun z =>
  (Sum.inr z.2, Sum.inl z.1)

private theorem suzukiCausalDepthGammaFixedDiagonalCrossEmbedding_injective :
    Function.Injective suzukiCausalDepthGammaFixedDiagonalCrossEmbedding := by
  rintro ⟨pe, k⟩ ⟨qe, l⟩ h
  change (Sum.inr k, Sum.inl pe) = (Sum.inr l, Sum.inl qe) at h
  exact Prod.ext
    (Sum.inl_injective (congrArg Prod.snd h))
    (Sum.inr_injective (congrArg Prod.fst h))

private def suzukiCausalDepthGammaFixedDiagonalCrossSupport :
    Set (SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex) :=
  Set.range suzukiCausalDepthGammaFixedDiagonalCrossEmbedding

private def suzukiCausalDepthGammaFixedDiagonalCrossEquiv :
    ((Nat.Primes × ℕ) × ℕ) ≃ suzukiCausalDepthGammaFixedDiagonalCrossSupport :=
  Equiv.ofInjective suzukiCausalDepthGammaFixedDiagonalCrossEmbedding
    suzukiCausalDepthGammaFixedDiagonalCrossEmbedding_injective

theorem suzukiCausalDepthGammaFixedDiagonalFeatureKernel_isHS
    {m : Nat.Primes × ℕ → ℂ}
    (hm : SuzukiCausalDepthGammaFixedDiagonalGraphAdmissible m) :
    HilbertSchmidt.IsHS (suzukiCausalDepthGammaSubexponentialFeatureKernel m) := by
  let energy :
      SuzukiCausalDepthGammaTraceIndex × SuzukiCausalDepthGammaTraceIndex → ℝ :=
    fun z => ‖suzukiCausalDepthGammaSubexponentialFeatureKernel m z‖ ^ (2 : ℕ)
  have hcomp : Summable (fun z : (Nat.Primes × ℕ) × ℕ =>
      energy (suzukiCausalDepthGammaFixedDiagonalCrossEquiv z)) := by
    refine (summable_norm_sq_suzukiCausalDepthGammaFixedDiagonalWeightedFeature_allPrime
      hm).congr (fun z => ?_)
    rfl
  have hsub : Summable
      (energy ∘ Subtype.val : suzukiCausalDepthGammaFixedDiagonalCrossSupport → ℝ) :=
    (suzukiCausalDepthGammaFixedDiagonalCrossEquiv.summable_iff).mp hcomp
  have hindicator : Summable
      (suzukiCausalDepthGammaFixedDiagonalCrossSupport.indicator energy) :=
    summable_subtype_iff_indicator.mp hsub
  exact hindicator.congr fun z => by
    show suzukiCausalDepthGammaFixedDiagonalCrossSupport.indicator energy z =
      ‖suzukiCausalDepthGammaSubexponentialFeatureKernel m z‖ ^ (2 : ℕ)
    by_cases hz : z ∈ suzukiCausalDepthGammaFixedDiagonalCrossSupport
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      rcases z with ⟨i, j⟩
      cases i <;> cases j <;>
        simp [suzukiCausalDepthGammaFixedDiagonalCrossSupport,
          suzukiCausalDepthGammaFixedDiagonalCrossEmbedding,
          suzukiCausalDepthGammaSubexponentialFeatureKernel] at hz ⊢

/-- Fixed Hilbert--Schmidt feature represented by an arbitrary graph-admissible diagonal source
multiplier. -/
def suzukiCausalDepthGammaFixedDiagonalFeatureOperator
    (m : Nat.Primes × ℕ → ℂ)
    (hm : SuzukiCausalDepthGammaFixedDiagonalGraphAdmissible m) :
    SuzukiCausalDepthGammaTraceL2 →L[ℂ] SuzukiCausalDepthGammaTraceL2 :=
  HilbertSchmidt.toOperator
    (suzukiCausalDepthGammaFixedDiagonalFeatureKernel_isHS hm)

theorem suzukiCausalDepthGammaFixedDiagonalFeatureOperator_isHilbertSchmidt
    (m : Nat.Primes × ℕ → ℂ)
    (hm : SuzukiCausalDepthGammaFixedDiagonalGraphAdmissible m) :
    IsHilbertSchmidt (suzukiCausalDepthGammaFixedDiagonalFeatureOperator m hm) :=
  HilbertSchmidt.isHilbertSchmidt_toOperator
    (suzukiCausalDepthGammaFixedDiagonalFeatureKernel_isHS hm)

/-- The graph-admissible representation acts by the requested multiplier on every literal source
column. -/
theorem suzukiCausalDepthGammaFixedDiagonalFeatureOperator_single_source_eq_smul
    (m : Nat.Primes × ℕ → ℂ)
    (hm : SuzukiCausalDepthGammaFixedDiagonalGraphAdmissible m)
    (pe : Nat.Primes × ℕ) :
    suzukiCausalDepthGammaFixedDiagonalFeatureOperator m hm
        (lp.single 2 (Sum.inl pe) (1 : ℂ)) =
      m pe • suzukiCausalDepthGammaFeatureOperator
        1 1 zero_lt_one zero_lt_one
          (lp.single 2 (Sum.inl pe) (1 : ℂ)) := by
  ext i
  change (suzukiCausalDepthGammaFixedDiagonalFeatureOperator m hm
      (lp.single 2 (Sum.inl pe) (1 : ℂ))) i =
    m pe * (suzukiCausalDepthGammaFeatureOperator
      1 1 zero_lt_one zero_lt_one
        (lp.single 2 (Sum.inl pe) (1 : ℂ))) i
  rw [suzukiCausalDepthGammaFixedDiagonalFeatureOperator,
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

/-- Pre-Gram response pairing after an arbitrary fixed graph-admissible diagonal multiplier. -/
def suzukiCausalDepthGammaFixedDiagonalGraphCorrection
    (m : Nat.Primes × ℕ → ℂ)
    (hm : SuzukiCausalDepthGammaFixedDiagonalGraphAdmissible m)
    (R : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2) (N : ℕ) : ℝ :=
  (hsInner (R N)
    (suzukiCausalDepthGammaFixedDiagonalFeatureOperator m hm)).re

/-- Every bounded natural quadratic-rank response to a fixed diagonal Hilbert source is
sublinear at the transition-core scale. -/
theorem suzukiCausalDepthGammaFixedDiagonalGraphCorrection_sublinear
    (m : Nat.Primes × ℕ → ℂ)
    (hm : SuzukiCausalDepthGammaFixedDiagonalGraphAdmissible m)
    (R : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2)
    (q : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hRank : ∀ N : ℕ, HasRankLE (R N) ((q * N) ^ (2 : ℕ)))
    (hNorm : ∀ N : ℕ, ‖R N‖ ≤ M) :
    SuzukiTransitionCoreCorrectionSublinear
      (suzukiCausalDepthGammaFixedDiagonalGraphCorrection m hm R) := by
  apply tendsto_re_hsInner_div_nat_of_quadraticRank_uniformlyBounded
    (suzukiCausalDepthGammaFixedDiagonalFeatureOperator_isHilbertSchmidt m hm)
    (fun N => R (8 * N)) (8 * q) M hM
  · intro N
    simpa [mul_assoc, mul_left_comm, mul_comm] using hRank (8 * N)
  · intro N
    exact hNorm (8 * N)

/-- Candidate CCM--FU producer built from any cutoff-independent diagonal Hilbert source and a
uniformly bounded response of natural quadratic effective rank. -/
structure SuzukiCausalDepthGammaFixedDiagonalGraphWardProducer where
  multiplier : Nat.Primes × ℕ → ℂ
  graph_admissible :
    SuzukiCausalDepthGammaFixedDiagonalGraphAdmissible multiplier
  width : ℝ
  response : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
    SuzukiCausalDepthGammaTraceL2
  rankScale : ℕ
  opNormCeiling : ℝ
  opNormCeiling_nonneg : 0 ≤ opNormCeiling
  response_rank : ∀ N : ℕ,
    HasRankLE (response N) ((rankScale * N) ^ (2 : ℕ))
  response_opNorm_le : ∀ N : ℕ, ‖response N‖ ≤ opNormCeiling
  lower : ℝ
  ward_semibounded : ∀ᶠ n : ℕ in atTop,
    lower ≤ suzukiRectangularWardDefect width
      (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
        suzukiCausalDepthGammaFixedDiagonalGraphCorrection multiplier
          graph_admissible response N)
      (8 * n)

/-- **Fixed-diagonal Hilbert-source producer-class kill.** No cutoff-independent diagonal source
multiplier admitted by the Hilbert graph, paired with a uniformly bounded response of natural
quadratic rank, can semibound the rectangular Ward defect. -/
theorem no_suzukiCausalDepthGammaFixedDiagonalGraphWardProducer :
    ¬ Nonempty SuzukiCausalDepthGammaFixedDiagonalGraphWardProducer := by
  rintro ⟨P⟩
  exact no_sublinear_transitionCore_rectangularWardProducer
    ⟨P.width,
      suzukiCausalDepthGammaFixedDiagonalGraphCorrection
        P.multiplier P.graph_admissible P.response,
      P.lower,
      suzukiCausalDepthGammaFixedDiagonalGraphCorrection_sublinear
        P.multiplier P.graph_admissible P.response P.rankScale
          P.opNormCeiling P.opNormCeiling_nonneg
          P.response_rank P.response_opNorm_le,
      P.ward_semibounded⟩

end

end RHTower
