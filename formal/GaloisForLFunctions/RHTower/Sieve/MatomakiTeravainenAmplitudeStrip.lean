import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRaisedAmplitudeCellScheduled

/-!
# Source derivation of the Matomäki--Teräväinen active amplitude strip

The `T₂` pointwise upper bounds force both dyadic amplitude exponents away from zero.  The
large-factor alternative controls whichever exponent is smaller, up to one dyadic logarithmic
step.  The step is uniformly subpower once both factor lengths have a fixed positive height
exponent.
-/

namespace RHTower.Sieve

open Filter Finset

/-- An active cell lying strictly below `M_j^(-tau_j)` has both amplitude exponents strictly above
the corresponding `tau_j`. -/
theorem active_matomakiTeravainenAmplitudeSigma_gt_of_upper
    {α : Type*} [DecidableEq α] {S : Finset α} {F₁ F₂ : α → ℝ}
    {M₁ M₂ V₁ V₂ tau₁ tau₂ : ℝ}
    (hM₁ : 1 < M₁) (hM₂ : 1 < M₂) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    {J₁ J₂ : ℕ}
    (hupper₁ : ∀ q ∈ S, F₁ q < M₁ ^ (-tau₁))
    (hupper₂ : ∀ q ∈ S, F₂ q < M₂ ^ (-tau₂))
    {ij : Fin J₁ × Fin J₂}
    (hij : ij ∈ matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V₁ V₂ J₁ J₂) :
    tau₁ < matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1 ∧
      tau₂ < matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2 := by
  rw [matomakiTeravainenActiveAmplitudeIndices, Finset.mem_filter] at hij
  obtain ⟨q, hqcell⟩ := hij.2
  have hqS : q ∈ S := by
    rw [matomakiTeravainenAmplitudeCell, Finset.mem_filter] at hqcell
    exact hqcell.1
  have hqLower₁ : (2 : ℝ) ^ (ij.1 : ℕ) * V₁ ≤ F₁ q := by
    rw [matomakiTeravainenAmplitudeCell, Finset.mem_filter] at hqcell
    exact hqcell.2.1
  have hqLower₂ : (2 : ℝ) ^ (ij.2 : ℕ) * V₂ ≤ F₂ q := by
    rw [matomakiTeravainenAmplitudeCell, Finset.mem_filter] at hqcell
    exact hqcell.2.2.2.1
  have hpow₁ : M₁ ^ (-matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1) <
      M₁ ^ (-tau₁) := by
    rw [rpow_neg_matomakiTeravainenAmplitudeSigma hM₁ hV₁]
    exact hqLower₁.trans_lt (hupper₁ q hqS)
  have hpow₂ : M₂ ^ (-matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2) <
      M₂ ^ (-tau₂) := by
    rw [rpow_neg_matomakiTeravainenAmplitudeSigma hM₂ hV₂]
    exact hqLower₂.trans_lt (hupper₂ q hqS)
  constructor
  · have := (Real.strictMono_rpow_of_base_gt_one hM₁).lt_iff_lt.mp hpow₁
    linarith
  · have := (Real.strictMono_rpow_of_base_gt_one hM₂).lt_iff_lt.mp hpow₂
    linarith

/-- Left-selected cell exponent inherits the large-factor cap. -/
theorem left_selected_matomakiTeravainenAmplitudeSigma_le
    {α : Type*} [DecidableEq α] {S : Finset α} {F₁ F₂ : α → ℝ}
    {M₁ M₂ V₁ V₂ sigma₀ : ℝ}
    (hM₁ : 1 < M₁) (hM₂ : 1 < M₂) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    {J₁ J₂ : ℕ}
    (hlarge : ∀ q ∈ S, M₁ ^ (-sigma₀) ≤ F₁ q ∨ M₂ ^ (-sigma₀) ≤ F₂ q)
    {ij : Fin J₁ × Fin J₂}
    (hij : ij ∈ matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V₁ V₂ J₁ J₂)
    (hside : matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1 ≤
      matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2) :
    matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1 ≤
      sigma₀ + max (Real.log 2 / Real.log M₁) (Real.log 2 / Real.log M₂) := by
  simpa [min_eq_left hside] using
    (min_matomakiTeravainenAmplitudeSigma_le hM₁ hM₂ hV₁ hV₂ hlarge hij)

/-- Right-selected cell exponent inherits the large-factor cap. -/
theorem right_selected_matomakiTeravainenAmplitudeSigma_le
    {α : Type*} [DecidableEq α] {S : Finset α} {F₁ F₂ : α → ℝ}
    {M₁ M₂ V₁ V₂ sigma₀ : ℝ}
    (hM₁ : 1 < M₁) (hM₂ : 1 < M₂) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    {J₁ J₂ : ℕ}
    (hlarge : ∀ q ∈ S, M₁ ^ (-sigma₀) ≤ F₁ q ∨ M₂ ^ (-sigma₀) ≤ F₂ q)
    {ij : Fin J₁ × Fin J₂}
    (hij : ij ∈ matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V₁ V₂ J₁ J₂)
    (hside : matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2 <
      matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1) :
    matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2 ≤
      sigma₀ + max (Real.log 2 / Real.log M₁) (Real.log 2 / Real.log M₂) := by
  simpa [min_eq_right hside.le] using
    (min_matomakiTeravainenAmplitudeSigma_le hM₁ hM₂ hV₁ hV₂ hlarge hij)

/-- A fixed positive height exponent makes one dyadic logarithmic step uniformly smaller than any
prescribed positive reserve. -/
theorem exists_matomakiTeravainen_dyadic_log_correction
    {mu eta : ℝ} (hmu : 0 < mu) (heta : 0 < eta) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ (T M : ℝ),
      T₀ ≤ T → 1 < M → T ^ mu ≤ M →
      Real.log 2 / Real.log M ≤ eta := by
  have hexp : 0 < mu * eta := mul_pos hmu heta
  have hgrowth : Tendsto (fun T : ℝ => T ^ (mu * eta)) atTop atTop :=
    tendsto_rpow_atTop hexp
  have hevent : ∀ᶠ T : ℝ in atTop, 1 < T ∧ 2 ≤ T ^ (mu * eta) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      hgrowth.eventually_ge_atTop (2 : ℝ)] with T hT htwo
    exact ⟨hT, htwo⟩
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hevent
  refine ⟨max 1 T₀, le_max_left _ _, ?_⟩
  intro T M hT hM hMlower
  have hdata := hT₀ T (le_trans (le_max_right _ _) hT)
  have hT0 : 0 < T := by linarith [hdata.1]
  have hlogM : 0 < Real.log M := Real.log_pos hM
  have hlogLower := Real.log_le_log (Real.rpow_pos_of_pos hT0 _) hMlower
  rw [Real.log_rpow hT0] at hlogLower
  have hlogTwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hdata.2
  rw [Real.log_rpow hT0] at hlogTwo
  have hbound : Real.log 2 ≤ eta * Real.log M := by
    calc
      Real.log 2 ≤ (mu * eta) * Real.log T := hlogTwo
      _ = eta * (mu * Real.log T) := by ring
      _ ≤ eta * Real.log M := mul_le_mul_of_nonneg_left hlogLower heta.le
  exact (div_le_iff₀ hlogM).2 (by simpa [mul_comm] using hbound)

/-- The literal `T₂` inequalities supply exactly the branchwise amplitude-strip hypotheses of the
scheduled actual-cell theorem. -/
theorem matomakiTeravainen_active_amplitude_strip
    {α : Type*} [DecidableEq α] {S : Finset α} {F₁ F₂ : α → ℝ}
    {M₁ M₂ V₁ V₂ tau sigma₀ eps kappa eta : ℝ}
    (hM₁ : 1 < M₁) (hM₂ : 1 < M₂) (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    {J₁ J₂ : ℕ}
    (hupper₁ : ∀ q ∈ S, F₁ q < M₁ ^ (-tau))
    (hupper₂ : ∀ q ∈ S, F₂ q < M₂ ^ (-tau))
    (htau : 5 * eps + kappa ≤ tau)
    (hlarge : ∀ q ∈ S, M₁ ^ (-sigma₀) ≤ F₁ q ∨ M₂ ^ (-sigma₀) ≤ F₂ q)
    (hcorr : max (Real.log 2 / Real.log M₁) (Real.log 2 / Real.log M₂) ≤ eta)
    (hcap : sigma₀ + eta + kappa ≤ 7 / 32 - 5 * eps)
    {ij : Fin J₁ × Fin J₂}
    (hij : ij ∈ matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V₁ V₂ J₁ J₂) :
    (matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1 ≤
        matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2 →
      5 * eps + kappa ≤ matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1 ∧
      matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1 + kappa ≤ 7 / 32 - 5 * eps) ∧
    (matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2 <
        matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1 →
      5 * eps + kappa ≤ matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2 ∧
      matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2 + kappa ≤ 7 / 32 - 5 * eps) := by
  have hlo := active_matomakiTeravainenAmplitudeSigma_gt_of_upper
    hM₁ hM₂ hV₁ hV₂ hupper₁ hupper₂ hij
  constructor
  · intro hside
    have hhi := left_selected_matomakiTeravainenAmplitudeSigma_le
      hM₁ hM₂ hV₁ hV₂ hlarge hij hside
    constructor <;> linarith
  · intro hside
    have hhi := right_selected_matomakiTeravainenAmplitudeSigma_le
      hM₁ hM₂ hV₁ hV₂ hlarge hij hside
    constructor <;> linarith

end RHTower.Sieve
