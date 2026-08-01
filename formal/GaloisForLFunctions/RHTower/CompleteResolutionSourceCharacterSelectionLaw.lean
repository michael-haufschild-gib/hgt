import GaloisForLFunctions.RHTower.CompleteResolutionSummableConormalLanding
import GaloisForLFunctions.RHTower.XiSourceModularTypeSuperselectionLaw

/-!
# Complete source-resolution character selection

The complete high-exponent resolution is not merely a pointwise family of scalar multipliers.
At every point of the open right half-plane it is one nonzero vector in a fixed `ℓ¹` source
space.  This module applies the source-character conservation law to that actual vector.

The resulting statement is a literal carrier theorem: at every point in the closed right half
of the critical strip, the predeclared source vector is summable, has total coordinate one, and
contains a multiplicity-preserving channel.  Every equivariant norm-conservative descent of its
centered real character either erases that vector or places the point on the critical line.
-/

open scoped ENNReal

namespace RHTower

noncomputable section

/-- Fixed sequence space in which every complete-resolution multiplier vector lands. -/
abbrev CompleteResolutionSourceSpace := lp (fun _ : ℕ => ℂ) 1

/-- Canonical `ℓ¹` vector associated with an absolutely summable complex sequence. -/
def summableSourceVector
    (a : ℕ → ℂ) (ha : Summable a) : CompleteResolutionSourceSpace := by
  refine ⟨(a : PreLp (fun _ : ℕ => ℂ)), ?_⟩
  change Memℓp a 1
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simpa using ha.norm

@[simp] theorem summableSourceVector_apply
    (a : ℕ → ℂ) (ha : Summable a) (j : ℕ) :
    summableSourceVector a ha j = a j :=
  rfl

/-- A summable source vector whose coordinates add to one has `ℓ¹` norm at least one. -/
theorem one_le_norm_summableSourceVector_of_hasSum_one
    (a : ℕ → ℂ) (ha : Summable a) (hsum : HasSum a 1) :
    1 ≤ ‖summableSourceVector a ha‖ := by
  have htriangle := norm_tsum_le_tsum_norm ha.norm
  rw [hsum.tsum_eq, norm_one] at htriangle
  have hnorm :=
    lp.norm_eq_tsum_rpow
      (show 0 < (1 : ℝ≥0∞).toReal by norm_num)
      (summableSourceVector a ha)
  norm_num at hnorm
  rwa [hnorm]

/-- The complete positive source-resolution vector at a point of the open right half-plane. -/
def completeResolutionSourceVector
    (K : ℕ) (rho : ℂ) (hrho : 0 < rho.re) :
    CompleteResolutionSourceSpace :=
  summableSourceVector
    (fun j => completeResolutionMultiplier K j rho)
    (summable_completeResolutionMultiplier K hrho)

@[simp] theorem completeResolutionSourceVector_apply
    (K : ℕ) (rho : ℂ) (hrho : 0 < rho.re) (j : ℕ) :
    completeResolutionSourceVector K rho hrho j =
      completeResolutionMultiplier K j rho :=
  rfl

/-- The source-resolution vector cannot vanish: its coordinate sum is one. -/
theorem completeResolutionSourceVector_ne_zero
    (K : ℕ) {rho : ℂ} (hrho : 0 < rho.re) :
    completeResolutionSourceVector K rho hrho ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_completeResolutionMultiplier_ne_zero K hrho
  intro hzero
  have hjzero := congrArg
    (fun x : CompleteResolutionSourceSpace => x j) hzero
  simp only [completeResolutionSourceVector_apply] at hjzero
  exact hj hjzero

/-- Real exponential character acting diagonally on an arbitrary real vector space. -/
def realExponentialCharacterAction
    (E : Type*) [AddCommGroup E] [Module ℝ E] (nu : ℝ) : E →ₗ[ℝ] E :=
  (Real.exp nu) • LinearMap.id

@[simp] theorem realExponentialCharacterAction_apply
    (E : Type*) [AddCommGroup E] [Module ℝ E] (nu : ℝ) (x : E) :
    realExponentialCharacterAction E nu x = Real.exp nu • x := by
  simp [realExponentialCharacterAction]

/-- **Stable source-character conservation.**  For an arbitrary (not necessarily equivariant)
consumer, the failure to intertwine a real exponential source character with a
norm-conservative target action is at least the character mismatch times the retained source
norm.  Exact erasure-or-neutrality is the zero-defect endpoint of this inequality. -/
theorem normConservative_sourceCharacter_defect_lowerBound
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : F →ₗ[ℝ] F) (T : E →ₗ[ℝ] F)
    (x : E) (nu : ℝ)
    (hconservative : ∀ y : F, ‖V y‖ = ‖y‖) :
    |Real.exp nu - 1| * ‖T x‖ ≤
      ‖T (realExponentialCharacterAction E nu x) - V (T x)‖ := by
  have hreverse :=
    abs_norm_sub_norm_le
      (T (realExponentialCharacterAction E nu x)) (V (T x))
  rw [realExponentialCharacterAction_apply, map_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg nu),
    hconservative] at hreverse
  calc
    |Real.exp nu - 1| * ‖T x‖ =
        |Real.exp nu * ‖T x‖ - ‖T x‖| := by
          calc
            |Real.exp nu - 1| * ‖T x‖ =
                |Real.exp nu - 1| * |‖T x‖| := by
                  rw [abs_of_nonneg (norm_nonneg (T x))]
            _ = |(Real.exp nu - 1) * ‖T x‖| :=
              (abs_mul _ _).symm
            _ = |Real.exp nu * ‖T x‖ - ‖T x‖| := by
              congr 1
              ring
    _ ≤ ‖Real.exp nu • T x - V (T x)‖ := hreverse
    _ = ‖T (realExponentialCharacterAction E nu x) - V (T x)‖ := by
      rw [realExponentialCharacterAction_apply, map_smul]

/-- Uniform source faithfulness turns the stable character budget into a consumer-independent
defect floor. -/
theorem normConservative_sourceCharacter_uniformFaithfulness_defect_lowerBound
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : F →ₗ[ℝ] F) (T : E →ₗ[ℝ] F)
    (x : E) (nu kappa : ℝ)
    (hxnorm : 1 ≤ ‖x‖) (hkappa : 0 ≤ kappa)
    (hfaithful : kappa * ‖x‖ ≤ ‖T x‖)
    (hconservative : ∀ y : F, ‖V y‖ = ‖y‖) :
    kappa * |Real.exp nu - 1| ≤
      ‖T (realExponentialCharacterAction E nu x) - V (T x)‖ := by
  have habs : 0 ≤ |Real.exp nu - 1| := abs_nonneg _
  have hstable :=
    normConservative_sourceCharacter_defect_lowerBound
      V T x nu hconservative
  calc
    kappa * |Real.exp nu - 1| =
        |Real.exp nu - 1| * kappa := by ring
    _ ≤ |Real.exp nu - 1| * (kappa * ‖x‖) := by
      exact mul_le_mul_of_nonneg_left
        (by nlinarith [mul_nonneg hkappa (sub_nonneg.mpr hxnorm)])
        habs
    _ ≤ |Real.exp nu - 1| * ‖T x‖ :=
      mul_le_mul_of_nonneg_left hfaithful habs
    _ ≤ ‖T (realExponentialCharacterAction E nu x) - V (T x)‖ :=
      hstable

/-- Off the neutral character, no uniformly source-faithful sequence of norm-conservative
consumers can converge to exact equivariance. -/
theorem no_uniformlyFaithful_normConservative_approximateIntertwiners
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x : E) (hxnorm : 1 ≤ ‖x‖)
    (nu : ℝ) (hnu : nu ≠ 0)
    (kappa : ℝ) (hkappa : 0 < kappa)
    (V : ℕ → F →ₗ[ℝ] F) (T : ℕ → E →ₗ[ℝ] F)
    (hfaithful : ∀ n, kappa * ‖x‖ ≤ ‖T n x‖)
    (hconservative : ∀ n y, ‖V n y‖ = ‖y‖) :
    ¬ Filter.Tendsto
      (fun n =>
        ‖T n (realExponentialCharacterAction E nu x) -
          V n (T n x)‖)
      Filter.atTop (nhds 0) := by
  have hexp : Real.exp nu ≠ 1 := by
    intro h
    apply hnu
    apply Real.exp_injective
    simpa using h
  have hgap : 0 < kappa * |Real.exp nu - 1| :=
    mul_pos hkappa (abs_pos.mpr (sub_ne_zero.mpr hexp))
  intro htendsto
  have heventually :
      ∀ᶠ n in Filter.atTop,
        ‖T n (realExponentialCharacterAction E nu x) -
          V n (T n x)‖ < kappa * |Real.exp nu - 1| :=
    (tendsto_order.1 htendsto).2 _ hgap
  obtain ⟨n, hn⟩ := heventually.exists
  have hlower :=
    normConservative_sourceCharacter_uniformFaithfulness_defect_lowerBound
      (V n) (T n) x nu kappa hxnorm hkappa.le
      (hfaithful n) (hconservative n)
  exact (not_lt_of_ge hlower) hn

/-- A summable analytic resolution of one is a nonzero `ℓ¹` vector and contains a channel which
preserves the analytic order of every analytic response. -/
theorem summableAnalyticResolution_conormalLanding
    (m : ℕ → ℂ → ℂ) (f : ℂ → ℂ) {rho : ℂ}
    (hsummable : Summable (fun j => m j rho))
    (hsum : HasSum (fun j => m j rho) 1)
    (hanalytic : ∀ j, AnalyticAt ℂ (m j) rho)
    (hf : AnalyticAt ℂ f rho) :
    summableSourceVector (fun j => m j rho) hsummable ≠ 0 ∧
      ∃ j : ℕ, m j rho ≠ 0 ∧
        analyticOrderAt (fun z => f z * m j z) rho =
          analyticOrderAt f rho := by
  have hvector :
      summableSourceVector (fun j => m j rho) hsummable ≠ 0 := by
    intro hzero
    have hcoord : ∀ j, m j rho = 0 := by
      intro j
      have hj := congrArg
        (fun x : CompleteResolutionSourceSpace => x j) hzero
      simpa using hj
    have hfun : (fun j => m j rho) = fun _ => 0 := funext hcoord
    rw [hfun] at hsum
    exact one_ne_zero (hsum.unique hasSum_zero)
  refine ⟨hvector, ?_⟩
  have hexists : ∃ j : ℕ, m j rho ≠ 0 := by
    by_contra h
    push Not at h
    have hfun : (fun j => m j rho) = fun _ => 0 := funext h
    rw [hfun] at hsum
    exact one_ne_zero (hsum.unique hasSum_zero)
  obtain ⟨j, hj⟩ := hexists
  refine ⟨j, hj, ?_⟩
  have hmOrder : analyticOrderAt (m j) rho = 0 :=
    (hanalytic j).analyticOrderAt_eq_zero.mpr hj
  rw [show (fun z => f z * m j z) = f * m j from rfl,
    analyticOrderAt_mul hf (hanalytic j), hmOrder, add_zero]

/-- Stable form of the complete universal law: analytic source landing and the quantitative
character-defect budget hold simultaneously without assuming exact equivariance. -/
theorem summableAnalyticResolution_sourceCharacter_stability
    (m : ℕ → ℂ → ℂ) (f : ℂ → ℂ) {rho : ℂ}
    (hsummable : Summable (fun j => m j rho))
    (hsum : HasSum (fun j => m j rho) 1)
    (hanalytic : ∀ j, AnalyticAt ℂ (m j) rho)
    (hf : AnalyticAt ℂ f rho)
    (nu : ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : F →ₗ[ℝ] F)
    (T : CompleteResolutionSourceSpace →ₗ[ℝ] F)
    (hconservative : ∀ y : F, ‖V y‖ = ‖y‖) :
    summableSourceVector (fun j => m j rho) hsummable ≠ 0 ∧
      (∃ j : ℕ, m j rho ≠ 0 ∧
        analyticOrderAt (fun z => f z * m j z) rho =
          analyticOrderAt f rho) ∧
      |Real.exp nu - 1| *
          ‖T (summableSourceVector (fun j => m j rho) hsummable)‖ ≤
        ‖T
            (realExponentialCharacterAction CompleteResolutionSourceSpace nu
              (summableSourceVector (fun j => m j rho) hsummable)) -
          V (T (summableSourceVector (fun j => m j rho) hsummable))‖ := by
  obtain ⟨hvector, hchannel⟩ :=
    summableAnalyticResolution_conormalLanding
      m f hsummable hsum hanalytic hf
  exact ⟨hvector, hchannel,
    normConservative_sourceCharacter_defect_lowerBound
      V T (summableSourceVector (fun j => m j rho) hsummable)
      nu hconservative⟩

/-- **Summable analytic source-character conservation law.**  An analytic resolution of one
cannot vanish in every channel.  Hence it gives a nonzero `ℓ¹` source vector and, after
multiplication by any analytic response, at least one channel preserves exact analytic order.
For a diagonal real exponential character, every equivariant descent into a norm-conservative
target either erases that actual vector or has neutral character rate. -/
theorem summableAnalyticResolution_sourceCharacter_conservation
    (m : ℕ → ℂ → ℂ) (f : ℂ → ℂ) {rho : ℂ}
    (hsummable : Summable (fun j => m j rho))
    (hsum : HasSum (fun j => m j rho) 1)
    (hanalytic : ∀ j, AnalyticAt ℂ (m j) rho)
    (hf : AnalyticAt ℂ f rho)
    (nu : ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : F →ₗ[ℝ] F)
    (T : CompleteResolutionSourceSpace →ₗ[ℝ] F)
    (hintertwine : ∀ x : CompleteResolutionSourceSpace,
      V (T x) = T
        (realExponentialCharacterAction CompleteResolutionSourceSpace nu x))
    (hconservative : ∀ y : F, ‖V y‖ = ‖y‖) :
    summableSourceVector (fun j => m j rho) hsummable ≠ 0 ∧
      (∃ j : ℕ, m j rho ≠ 0 ∧
        analyticOrderAt (fun z => f z * m j z) rho =
          analyticOrderAt f rho) ∧
      (T (summableSourceVector (fun j => m j rho) hsummable) = 0 ∨
        nu = 0) := by
  obtain ⟨hvector, hchannel⟩ :=
    summableAnalyticResolution_conormalLanding
      m f hsummable hsum hanalytic hf
  refine ⟨hvector, hchannel, ?_⟩
  by_cases herased :
      T (summableSourceVector (fun j => m j rho) hsummable) = 0
  · exact Or.inl herased
  · exact Or.inr
      (normConservative_equivariantDescent_forces_zero
        (realExponentialCharacterAction CompleteResolutionSourceSpace nu)
        V T (summableSourceVector (fun j => m j rho) hsummable)
        herased nu
        (realExponentialCharacterAction_apply
          CompleteResolutionSourceSpace nu
          (summableSourceVector (fun j => m j rho) hsummable))
        hintertwine hconservative)

/-- **Complete source-character selection law.**  The actual `ℓ¹` resolution vector is nonzero
and contains a channel preserving the exact analytic order of `xi`.  If a real-linear consumer
intertwines its centered character with a norm-conservative target action, then the consumer
either erases this predeclared source vector or the base point lies on the critical line. -/
theorem completeResolution_sourceCharacter_selection
    {K : ℕ} (hK : 12 ≤ K) {rho : ℂ}
    (hrho : 1 / 2 ≤ rho.re)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : F →ₗ[ℝ] F)
    (T : CompleteResolutionSourceSpace →ₗ[ℝ] F)
    (hintertwine : ∀ x : CompleteResolutionSourceSpace,
      V (T x) = T
        (realExponentialCharacterAction CompleteResolutionSourceSpace
          (2 * rho.re - 1) x))
    (hconservative : ∀ y : F, ‖V y‖ = ‖y‖) :
    let hrhoPos : 0 < rho.re := by linarith
    Summable (fun j : ℕ => completeResolutionMultiplier K j rho) ∧
      HasSum (fun j : ℕ => completeResolutionMultiplier K j rho) 1 ∧
      completeResolutionSourceVector K rho hrhoPos ≠ 0 ∧
      (∃ j : ℕ,
        completeResolutionMultiplier K j rho ≠ 0 ∧
          analyticOrderAt
              (fun z => xi z * completeResolutionMultiplier K j z) rho =
            analyticOrderAt xi rho) ∧
      (T (completeResolutionSourceVector K rho hrhoPos) = 0 ∨
        rho.re = 1 / 2) := by
  let hrhoPos : 0 < rho.re := by linarith
  obtain ⟨hsummable, hsum, hchannel⟩ :=
    completeResolution_summable_conormalLanding hK hrho
  refine ⟨hsummable, hsum,
    completeResolutionSourceVector_ne_zero K hrhoPos,
    hchannel, ?_⟩
  by_cases herased :
      T (completeResolutionSourceVector K rho hrhoPos) = 0
  · exact Or.inl herased
  · right
    have hrate : 2 * rho.re - 1 = 0 :=
      normConservative_equivariantDescent_forces_zero
        (realExponentialCharacterAction CompleteResolutionSourceSpace
          (2 * rho.re - 1))
        V T (completeResolutionSourceVector K rho hrhoPos)
        herased (2 * rho.re - 1)
        (realExponentialCharacterAction_apply
          CompleteResolutionSourceSpace (2 * rho.re - 1)
          (completeResolutionSourceVector K rho hrhoPos))
        hintertwine hconservative
    linarith

/-- Quantitative form of complete source-character selection.  Every norm-conservative target
action pays at least the centered-character mismatch times the amount of the actual complete
resolution vector retained by the consumer.  No exact intertwining assumption is required. -/
theorem completeResolution_sourceCharacter_defect_lowerBound
    (K : ℕ) {rho : ℂ} (hrho : 0 < rho.re)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : F →ₗ[ℝ] F)
    (T : CompleteResolutionSourceSpace →ₗ[ℝ] F)
    (hconservative : ∀ y : F, ‖V y‖ = ‖y‖) :
    |Real.exp (2 * rho.re - 1) - 1| *
        ‖T (completeResolutionSourceVector K rho hrho)‖ ≤
      ‖T
          (realExponentialCharacterAction CompleteResolutionSourceSpace
            (2 * rho.re - 1)
            (completeResolutionSourceVector K rho hrho)) -
        V (T (completeResolutionSourceVector K rho hrho))‖ :=
  normConservative_sourceCharacter_defect_lowerBound
    V T (completeResolutionSourceVector K rho hrho)
      (2 * rho.re - 1) hconservative

/-- Uniformly source-faithful approximate consumers of the complete Riemann resolution cannot
approach equivariance off the neutral horizon. -/
theorem completeResolution_sourceCharacter_uniformFaithfulness_defect_lowerBound
    (K : ℕ) {rho : ℂ} (hrho : 0 < rho.re)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : F →ₗ[ℝ] F)
    (T : CompleteResolutionSourceSpace →ₗ[ℝ] F)
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hfaithful : ∀ x : CompleteResolutionSourceSpace,
      kappa * ‖x‖ ≤ ‖T x‖)
    (hconservative : ∀ y : F, ‖V y‖ = ‖y‖) :
    kappa * |Real.exp (2 * rho.re - 1) - 1| ≤
      ‖T
          (realExponentialCharacterAction CompleteResolutionSourceSpace
            (2 * rho.re - 1)
            (completeResolutionSourceVector K rho hrho)) -
        V (T (completeResolutionSourceVector K rho hrho))‖ := by
  exact
    normConservative_sourceCharacter_uniformFaithfulness_defect_lowerBound
      V T (completeResolutionSourceVector K rho hrho)
      (2 * rho.re - 1) kappa
      (one_le_norm_summableSourceVector_of_hasSum_one
        (fun j => completeResolutionMultiplier K j rho)
        (summable_completeResolutionMultiplier K hrho)
        (hasSum_completeResolutionMultiplier_one K hrho))
      hkappa
      (hfaithful (completeResolutionSourceVector K rho hrho))
      hconservative

end

end RHTower
