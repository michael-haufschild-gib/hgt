import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationSourceBound
import GaloisForLFunctions.RHTower.WeilPositiveProducerLindelof
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Finite logarithm endpoints on every positive valuation class

Each fixed prime-power valuation class of the actual source has a literal
logarithmic Dirichlet series with a finite right limit and a linear remainder.
The endpoint is not assigned a canonical value.
-/

open Complex Filter Topology Set
noncomputable section
namespace RHTower.WeilSingularArithmetic

/-- The literal exact-valuation restriction of the normalized arithmetic source. -/
def valuationSourceCoeff (lam : ℕ → ℝ) (p k : ℕ) (n : ℕ) : ℝ :=
  if 2 ≤ n ∧ (p^k ∣ n ∧ ¬p^(k+1) ∣ n) then lam n else 0

private theorem valuationSourceCoeff_cast (lam : ℕ → ℝ) (p k : ℕ) :
    (fun n => (valuationSourceCoeff lam p k n : ℂ)) = valuationPart p k (WeilHerglotz.lamC lam) := by
  funext n
  by_cases hn : 2≤n <;> by_cases he : (p^k ∣ n ∧ ¬p^(k+1) ∣ n) <;>
    simp [valuationSourceCoeff,valuationPart,valuationMask,WeilHerglotz.lamC,hn,he]

private theorem valuationSourceCoeff_summable {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (p k : ℕ) {σ : ℝ} (hσ : 1<σ) :
    Summable fun n : ℕ => |valuationSourceCoeff lam p k n|/(n : ℝ)^σ := by
  refine (WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ).of_nonneg_of_le
    (fun _ => by positivity) fun n => ?_
  unfold valuationSourceCoeff
  split_ifs
  · rfl
  · simp only [abs_zero,zero_div]
    positivity

/-- The valuation logarithmic Dirichlet series, evaluated on its actual half-plane
of absolute convergence. -/
def sourceValuationLogarithm (lam : ℕ → ℝ) (p k : ℕ) (σ : ℝ) : ℝ :=
  (LSeries (logZetaCoeff (valuationSourceCoeff lam p k)) (σ : ℂ)).re

/-- The logarithm is the literal series over the specified valuation class. -/
theorem sourceValuationLogarithm_eq_tsum {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (p k : ℕ) {σ : ℝ} (hσ : 1<σ) :
    sourceValuationLogarithm lam p k σ = ∑' n : ℕ,
      if 2≤n ∧ (p^k ∣ n ∧ ¬p^(k+1) ∣ n) then lam n/(Real.log n*(n : ℝ)^σ) else 0 := by
  have hs := lseriesSummable_logZetaCoeff
    (fun σ hσ => valuationSourceCoeff_summable hW p k hσ) hσ
  rw [sourceValuationLogarithm,LSeries,Complex.re_tsum hs]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · subst n
    simp [LSeries.term]
  · have he : (n : ℂ)^(σ : ℂ) = (((n : ℝ)^σ : ℝ) : ℂ) :=
      (Complex.ofReal_cpow (Nat.cast_nonneg n) σ).symm
    by_cases h : 2≤n ∧ (p^k ∣ n ∧ ¬p^(k+1) ∣ n) <;>
      simp [LSeries.term,logZetaCoeff,valuationSourceCoeff,hn,h,he,← Complex.ofReal_div,div_div]

/-- The valuation logarithmic series is real on its real half-line of convergence. -/
theorem ofReal_sourceValuationLogarithm {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (p k : ℕ) {σ : ℝ} (hσ : 1<σ) :
    (sourceValuationLogarithm lam p k σ : ℂ) =
      LSeries (logZetaCoeff (valuationSourceCoeff lam p k)) (σ : ℂ) := by
  have hs := lseriesSummable_logZetaCoeff
    (fun σ hσ => valuationSourceCoeff_summable hW p k hσ) hσ
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    rw [LSeries,Complex.im_tsum hs]
    symm
    calc
      _ = ∑' _n : ℕ, (0 : ℝ) := by
        apply tsum_congr
        intro n
        by_cases hn : n=0
        · simp [hn,LSeries.term]
        · have he : (n : ℂ)^(σ : ℂ) = (((n : ℝ)^σ : ℝ) : ℂ) :=
            (Complex.ofReal_cpow (Nat.cast_nonneg n) σ).symm
          simp [LSeries.term,logZetaCoeff,hn,he,← Complex.ofReal_div]
      _ = 0 := tsum_zero

private theorem hasDerivAt_sourceValuationLogarithm {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (p k : ℕ) {σ : ℝ} (hσ : 1<σ) :
    HasDerivAt (sourceValuationLogarithm lam p k)
      (-(LSeries (valuationPart p k (WeilHerglotz.lamC lam)) (σ : ℂ)).re) σ := by
  have hd := hasDerivAt_LSeries_logZetaCoeff
    (fun σ hσ => valuationSourceCoeff_summable hW p k hσ)
    (show valuationSourceCoeff lam p k 1=0 by simp [valuationSourceCoeff]) (s := (σ : ℂ)) hσ
  rw [valuationSourceCoeff_cast] at hd
  exact hd.real_of_complex

/-- Full positivity alone gives a finite right limit of the valuation logarithm,
with a Lipschitz remainder. No value for that limit is prescribed. -/
theorem exists_sourceValuationLogarithm_lipschitz_limit {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∃ ell K eta : ℝ, 0≤K ∧ 0<eta ∧
      Tendsto (sourceValuationLogarithm lam p (k + 1)) (𝓝[>] 1) (𝓝 ell) ∧
      ∀ σ : ℝ, 1<σ → σ<1+eta →
      |sourceValuationLogarithm lam p (k + 1) σ-ell|≤K*(σ-1) := by
  obtain ⟨K,hK,hbound⟩ := exists_abs_re_valuation_source_le hW hp k
  obtain ⟨u,hu,hub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hbound
  let C : NNReal := .mk K hK
  have hderiv (σ : ℝ) (hσ : σ∈Ioo 1 u) := hasDerivAt_sourceValuationLogarithm hW p (k + 1) hσ.1
  have hLip : LipschitzOnWith C (sourceValuationLogarithm lam p (k + 1)) (Ioo 1 u) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun σ hσ => (hderiv σ hσ).differentiableAt) _ (convex_Ioo 1 u)
    intro σ hσ
    change ‖deriv (sourceValuationLogarithm lam p (k + 1)) σ‖≤K
    rw [(hderiv σ hσ).deriv,norm_neg,Real.norm_eq_abs]
    exact hub hσ
  obtain ⟨g,hg,heq⟩ := hLip.extend_real
  have ht : Tendsto (sourceValuationLogarithm lam p (k + 1)) (𝓝[>] 1) (𝓝 (g 1)) := by
    have hg' : Tendsto g (𝓝[>] (1 : ℝ)) (𝓝 (g 1)) :=
      (hg.continuous.tendsto 1).mono_left nhdsWithin_le_nhds
    apply hg'.congr'
    have hu' : ∀ᶠ σ : ℝ in 𝓝[>] 1, σ<u :=
      (eventually_lt_nhds hu).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hu'] with σ hσ hσu
    exact (heq ⟨hσ,hσu⟩).symm
  refine ⟨g 1,K,u-1,hK,sub_pos.mpr hu,ht,fun σ hσ hσu => ?_⟩
  have hmem : σ∈Ioo 1 u := ⟨hσ,by linarith⟩
  rw [heq hmem]
  have h := hg.dist_le_mul σ 1
  simpa [Real.dist_eq,C,abs_of_pos (sub_pos.mpr hσ)] using h

end RHTower.WeilSingularArithmetic
