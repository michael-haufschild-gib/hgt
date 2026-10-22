import GaloisForLFunctions.HTGeometry.HilbertSchmidtFiniteRankDensity
import GaloisForLFunctions.RHTower.ConnesConsaniTraceClassReduction
import GaloisForLFunctions.RHTower.RectangularSemilocalObserverTailSeparation
import GaloisForLFunctions.RHTower.SchattenTwoIdentity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaSchurTraceClassCompletion
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTransitionCoreLinearCompensationNoGo

/-!
# Quadratic-rank Hilbert--Schmidt response no-go

The bounded Robin trace no-go uses the positive trace-class Gamma energy as a fixed carrier.  A
different pre-Gram mechanism could pair the actual Hilbert--Schmidt Gamma feature operator directly
with a moving finite-rank response.  Uniform operator-norm control alone does not bound that
pairing, because the response's Hilbert--Schmidt norm may grow with rank.

This module closes the natural quadratic-rank class.  If a response has rank at most `(qN)^(2 : ℕ)`
and uniformly bounded operator norm, its pairing with any fixed Hilbert--Schmidt source is `o(N)`.
The decisive gain over the crude `O(N)` rank estimate is finite-rank density of the fixed source:
the Hilbert--Schmidt tail is arbitrarily small, while the fixed finite-rank head pairs with the
response through a uniformly trace-duality-bounded scalar.

Applied to the actual canonical causal-depth Gamma feature, the resulting correction is sublinear
on the cofinal `8n` mesh.  Existing transition-core rigidity therefore rules out every such
rectangular Ward producer.  A surviving pre-Gram response must have superquadratic effective rank,
unbounded operator norm, or a cutoff-moving/non-Hilbert--Schmidt source.
-/

open Complex Filter Topology ContinuousLinearMap
open scoped InnerProductSpace
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A rank-`N` operator has Hilbert--Schmidt energy at most `N` times its squared operator
norm. -/
theorem hsNormSq_le_rank_mul_norm_sq_of_hasRankLE
    {T : H →L[ℂ] H} {N : ℕ} (hT : HasRankLE T N) :
    hsNormSq T ≤ (N : ℝ) * ‖T‖ ^ (2 : ℕ) := by
  have hHS : IsHilbertSchmidt T := isHilbertSchmidt_of_hasRankLE hT
  have hzero : ∀ k : ℕ, N ≤ k → approxNumber T k = 0 := by
    intro k hk
    refine le_antisymm ?_ (approxNumber_nonneg T k)
    have hle := approxNumber_le T k T (hT.mono hk)
    simpa using hle
  have hsum : Summable (fun k : ℕ => approxNumber T k ^ (2 : ℕ)) := by
    refine summable_of_ne_finset_zero (s := Finset.range N) ?_
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [hzero k hk]
    norm_num
  rw [hsNormSq_eq_tsum_approxNumber_sq hHS,
    ← hsum.sum_add_tsum_nat_add N]
  have htail : ∑' k : ℕ, approxNumber T (k + N) ^ (2 : ℕ) = 0 := by
    simp [hzero]
  rw [htail, add_zero]
  calc
    ∑ k ∈ Finset.range N, approxNumber T k ^ (2 : ℕ) ≤
        ∑ _k ∈ Finset.range N, ‖T‖ ^ (2 : ℕ) := by
      exact Finset.sum_le_sum fun k _ =>
        pow_le_pow_left₀ (approxNumber_nonneg T k)
          (approxNumber_le_norm T k) 2
    _ = (N : ℝ) * ‖T‖ ^ (2 : ℕ) := by simp

/-- Square-rank form of the finite-rank Hilbert--Schmidt/operator-norm comparison. -/
theorem hsNorm_le_rankRoot_mul_norm_of_hasRankLE_sq
    {T : H →L[ℂ] H} {d : ℕ} (hT : HasRankLE T (d ^ (2 : ℕ))) :
    hsNorm T ≤ (d : ℝ) * ‖T‖ := by
  have hsq := hsNormSq_le_rank_mul_norm_sq_of_hasRankLE hT
  have hleft : hsNorm T ^ (2 : ℕ) = hsNormSq T :=
    Real.sq_sqrt (hsNormSq_nonneg T)
  have hright : (((d : ℝ) * ‖T‖) ^ (2 : ℕ)) =
      ((d ^ (2 : ℕ) : ℕ) : ℝ) * ‖T‖ ^ (2 : ℕ) := by
    push_cast
    ring
  have hnonneg : 0 ≤ (d : ℝ) * ‖T‖ :=
    mul_nonneg (Nat.cast_nonneg d) (norm_nonneg T)
  nlinarith [hsNorm_nonneg T]

/-- A finite-rank second argument pairs with a Hilbert--Schmidt first argument through trace
duality, paying only the fixed trace norm and the moving operator norm. -/
theorem norm_hsInner_le_traceNorm_mul_norm_of_hasRankLE
    {F R : H →L[ℂ] H} {d : ℕ} (hF : HasRankLE F d)
    (hR : IsHilbertSchmidt R) :
    ‖hsInner R F‖ ≤ traceNorm H F * ‖R‖ := by
  have hFHS : IsHilbertSchmidt F := isHilbertSchmidt_of_hasRankLE hF
  calc
    ‖hsInner R F‖ =
        ‖opTrace (ContinuousLinearMap.adjoint R ∘L F)‖ := by
      rw [opTrace_comp_eq_hsInner]
      simp
    _ = ‖opTrace (F ∘L ContinuousLinearMap.adjoint R)‖ := by
      rw [opTrace_comp_comm hR.adjoint hFHS]
    _ ≤ traceNorm H F * ‖ContinuousLinearMap.adjoint R‖ :=
      norm_opTrace_comp_le_norm_mul_traceNorm
        (memSchattenClass_one_of_hasRankLE hF) _
    _ = traceNorm H F * ‖R‖ := by simp

/-- **Fixed-Hilbert--Schmidt/quadratic-rank little-`o` law.**  Pairing any fixed
Hilbert--Schmidt source with uniformly operator-bounded responses of rank at most `(qN)^(2 : ℕ)` is
sublinear in `N`. -/
theorem tendsto_re_hsInner_div_nat_of_quadraticRank_uniformlyBounded
    {F : H →L[ℂ] H} (hF : IsHilbertSchmidt F)
    (R : ℕ → H →L[ℂ] H) (q : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hRank : ∀ N : ℕ, HasRankLE (R N) ((q * N) ^ (2 : ℕ)))
    (hNorm : ∀ N : ℕ, ‖R N‖ ≤ M) :
    Tendsto (fun N : ℕ => (hsInner (R N) F).re / (N : ℝ))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let C : ℝ := (q : ℝ) * M
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg q) hM
  have hden : 0 < 4 * (C + 1) := by positivity
  let δ : ℝ := ε / (4 * (C + 1))
  have hδ : 0 < δ := div_pos hε hden
  have hCδ : C * δ < ε / 4 := by
    dsimp [δ]
    rw [show C * (ε / (4 * (C + 1))) =
      (C * ε) / (4 * (C + 1)) by ring]
    rw [div_lt_iff₀ hden]
    nlinarith
  obtain ⟨s, hF0rank, hFdiff⟩ :=
    hF.exists_hasRankLE_hsNorm_sub_lt hδ
  let F0 : H →L[ℂ] H := hsTruncation (hsBasis ℂ H) F s
  have hF0HS : IsHilbertSchmidt F0 :=
    isHilbertSchmidt_hsTruncation (hsBasis ℂ H) F s
  have hFdiffHS : IsHilbertSchmidt (F - F0) := hF.sub hF0HS
  have hfiniteTendsto :
      Tendsto (fun N : ℕ => (traceNorm H F0 * M) / (N : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfiniteEventually : ∀ᶠ N : ℕ in atTop,
      (traceNorm H F0 * M) / (N : ℝ) < ε / 2 :=
    (tendsto_order.1 hfiniteTendsto).2 (ε / 2) (by linarith)
  rw [eventually_atTop] at hfiniteEventually
  obtain ⟨N0, hN0⟩ := hfiniteEventually
  refine ⟨max N0 1, fun N hNmax => ?_⟩
  have hfinite := hN0 N ((le_max_left N0 1).trans hNmax)
  have hN : 1 ≤ N := (le_max_right N0 1).trans hNmax
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hRHS : IsHilbertSchmidt (R N) :=
    isHilbertSchmidt_of_hasRankLE (hRank N)
  have hRhsRoot :
      hsNorm (R N) ≤ ((q * N : ℕ) : ℝ) * ‖R N‖ :=
    hsNorm_le_rankRoot_mul_norm_of_hasRankLE_sq (hRank N)
  have hRhs :
      hsNorm (R N) ≤ C * (N : ℝ) := by
    calc
      hsNorm (R N) ≤ ((q * N : ℕ) : ℝ) * ‖R N‖ := hRhsRoot
      _ ≤ ((q * N : ℕ) : ℝ) * M :=
        mul_le_mul_of_nonneg_left (hNorm N) (Nat.cast_nonneg _)
      _ = C * (N : ℝ) := by
        rw [Nat.cast_mul]
        ring
  have hresPair :
      ‖hsInner (R N) (F - F0)‖ <
        (ε / 4) * (N : ℝ) := by
    calc
      ‖hsInner (R N) (F - F0)‖ ≤
          hsNorm (R N) * hsNorm (F - F0) :=
        norm_hsInner_le hRHS hFdiffHS
      _ ≤ (C * (N : ℝ)) * hsNorm (F - F0) :=
        mul_le_mul_of_nonneg_right hRhs (hsNorm_nonneg _)
      _ ≤ (C * (N : ℝ)) * δ := by
        exact mul_le_mul_of_nonneg_left hFdiff.le
          (mul_nonneg hC hNpos.le)
      _ = (C * δ) * (N : ℝ) := by ring
      _ < (ε / 4) * (N : ℝ) :=
        mul_lt_mul_of_pos_right hCδ hNpos
  have hresDiv :
      ‖hsInner (R N) (F - F0)‖ / (N : ℝ) < ε / 4 := by
    exact (div_lt_iff₀ hNpos).2 hresPair
  have hfinitePair :
      ‖hsInner (R N) F0‖ ≤ traceNorm H F0 * M := by
    exact (norm_hsInner_le_traceNorm_mul_norm_of_hasRankLE
      hF0rank hRHS).trans
        (mul_le_mul_of_nonneg_left (hNorm N) (traceNorm_nonneg F0))
  have hfiniteDiv :
      ‖hsInner (R N) F0‖ / (N : ℝ) < ε / 2 :=
    (div_le_div_of_nonneg_right hfinitePair hNpos.le).trans_lt hfinite
  have hsplit : F = (F - F0) + F0 := by abel
  have hpairSplit :
      hsInner (R N) F =
        hsInner (R N) (F - F0) + hsInner (R N) F0 := by
    calc
      hsInner (R N) F = hsInner (R N) ((F - F0) + F0) :=
        congrArg (fun T => hsInner (R N) T) hsplit
      _ = hsInner (R N) (F - F0) + hsInner (R N) F0 :=
        hsInner_add_right hRHS hFdiffHS hF0HS
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hNpos]
  calc
    |(hsInner (R N) F).re| / (N : ℝ) ≤
        ‖hsInner (R N) F‖ / (N : ℝ) := by
      gcongr
      exact Complex.abs_re_le_norm _
    _ ≤ (‖hsInner (R N) (F - F0)‖ +
          ‖hsInner (R N) F0‖) / (N : ℝ) := by
      gcongr
      rw [hpairSplit]
      exact norm_add_le _ _
    _ = ‖hsInner (R N) (F - F0)‖ / (N : ℝ) +
          ‖hsInner (R N) F0‖ / (N : ℝ) := by ring
    _ < ε / 4 + ε / 2 := add_lt_add hresDiv hfiniteDiv
    _ < ε := by linarith

/-- Actual causal-depth Gamma feature at the fixed unit source/aperture scale. -/
def suzukiCanonicalCausalDepthGammaFeatureOperator :
    SuzukiCausalDepthGammaTraceL2 →L[ℂ] SuzukiCausalDepthGammaTraceL2 :=
  suzukiCausalDepthGammaFeatureOperator 1 1 zero_lt_one zero_lt_one

theorem suzukiCanonicalCausalDepthGammaFeatureOperator_isHilbertSchmidt :
    IsHilbertSchmidt suzukiCanonicalCausalDepthGammaFeatureOperator :=
  suzukiCausalDepthGammaFeatureOperator_isHilbertSchmidt
    1 1 zero_lt_one zero_lt_one

/-- Pre-Gram scalar response obtained by pairing a moving response with the actual fixed Gamma
feature. -/
def suzukiCausalDepthGammaQuadraticRankHSCorrection
    (R : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2) (N : ℕ) : ℝ :=
  (hsInner (R N) suzukiCanonicalCausalDepthGammaFeatureOperator).re

/-- Every uniformly bounded quadratic-rank pre-Gram Gamma response is sublinear on the transition
core's cofinal mesh. -/
theorem suzukiCausalDepthGammaQuadraticRankHSCorrection_sublinear
    (R : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2)
    (q : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hRank : ∀ N : ℕ, HasRankLE (R N) ((q * N) ^ (2 : ℕ)))
    (hNorm : ∀ N : ℕ, ‖R N‖ ≤ M) :
    SuzukiTransitionCoreCorrectionSublinear
      (suzukiCausalDepthGammaQuadraticRankHSCorrection R) := by
  apply tendsto_re_hsInner_div_nat_of_quadraticRank_uniformlyBounded
    suzukiCanonicalCausalDepthGammaFeatureOperator_isHilbertSchmidt
    (fun N => R (8 * N)) (8 * q) M hM
  · intro N
    simpa [mul_assoc, mul_left_comm, mul_comm] using hRank (8 * N)
  · intro N
    exact hNorm (8 * N)

/-- Candidate CCM--FU producer using a uniformly operator-bounded response with at most quadratic
effective rank against the actual fixed Hilbert--Schmidt Gamma feature. -/
structure SuzukiCausalDepthGammaQuadraticRankHSWardProducer where
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
        suzukiCausalDepthGammaQuadraticRankHSCorrection response N)
      (8 * n)

/-- **Closed producer-class kill.**  No uniformly operator-bounded quadratic-rank response paired
with the actual fixed Hilbert--Schmidt Gamma feature can semibound the rectangular Ward defect. -/
theorem no_suzukiCausalDepthGammaQuadraticRankHSWardProducer :
    ¬ Nonempty SuzukiCausalDepthGammaQuadraticRankHSWardProducer := by
  rintro ⟨P⟩
  exact no_sublinear_transitionCore_rectangularWardProducer
    ⟨P.width, suzukiCausalDepthGammaQuadraticRankHSCorrection P.response,
      P.lower,
      suzukiCausalDepthGammaQuadraticRankHSCorrection_sublinear
        P.response P.rankScale P.opNormCeiling
        P.opNormCeiling_nonneg P.response_rank P.response_opNorm_le,
      P.ward_semibounded⟩

end

end RHTower
