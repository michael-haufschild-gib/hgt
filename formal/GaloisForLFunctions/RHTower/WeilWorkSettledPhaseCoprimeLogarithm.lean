import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeSourceBound
import GaloisForLFunctions.RHTower.WeilPositiveProducerLindelof
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# A finite logarithm for every finite prime deletion

The signed polynomial source bounds its excluded logarithmic derivative.
The real logarithm therefore has a Lipschitz extension to one. Its endpoint
value is retained as an undetermined source constant.
-/

open Complex Filter Topology Set
noncomputable section
namespace RHTower.WeilSingularArithmetic

/-- The literal non-coprime restriction of the normalized arithmetic source. -/
def deletedSourceCoeff (lam : ℕ → ℝ) (Q : ℕ) (n : ℕ) : ℝ :=
  if 2 ≤ n ∧ ¬ n.Coprime Q then lam n else 0

private theorem deletedSourceCoeff_cast (lam : ℕ → ℝ) (Q : ℕ) :
    (fun n => (deletedSourceCoeff lam Q n : ℂ)) = nonCoprimePart Q (WeilHerglotz.lamC lam) := by
  funext n
  by_cases hn : 2≤n <;> by_cases he : ¬ n.Coprime Q <;>
    simp [deletedSourceCoeff,nonCoprimePart,WeilHerglotz.lamC,hn,he]

private theorem deletedSourceCoeff_summable {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (Q : ℕ) [NeZero Q] {σ : ℝ} (hσ : 1<σ) :
    Summable fun n : ℕ => |deletedSourceCoeff lam Q n|/(n : ℝ)^σ := by
  refine (WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ).of_nonneg_of_le
    (fun _ => by positivity) fun n => ?_
  unfold deletedSourceCoeff
  split_ifs
  · rfl
  · simp only [abs_zero,zero_div]
    positivity

/-- The excluded logarithmic Dirichlet series, evaluated on its actual half-plane
of absolute convergence. -/
def sourceDeletedLogarithm (lam : ℕ → ℝ) (Q : ℕ) (σ : ℝ) : ℝ :=
  (LSeries (logZetaCoeff (deletedSourceCoeff lam Q)) (σ : ℂ)).re

/-- The logarithm is the literal series over excluded source indices. -/
theorem sourceDeletedLogarithm_eq_tsum {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (Q : ℕ) [NeZero Q] {σ : ℝ} (hσ : 1<σ) :
    sourceDeletedLogarithm lam Q σ = ∑' n : ℕ,
      if 2≤n ∧ ¬ n.Coprime Q then lam n/(Real.log n*(n : ℝ)^σ) else 0 := by
  have hs := lseriesSummable_logZetaCoeff
    (fun σ hσ => deletedSourceCoeff_summable hW Q hσ) hσ
  rw [sourceDeletedLogarithm,LSeries,Complex.re_tsum hs]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · subst n
    simp [LSeries.term]
  · have he : (n : ℂ)^(σ : ℂ) = (((n : ℝ)^σ : ℝ) : ℂ) :=
      (Complex.ofReal_cpow (Nat.cast_nonneg n) σ).symm
    by_cases h : 2≤n ∧ ¬ n.Coprime Q <;>
      simp [LSeries.term,logZetaCoeff,deletedSourceCoeff,hn,h,he,← Complex.ofReal_div,div_div]

/-- The excluded logarithmic series is real on its real half-line of convergence. -/
theorem ofReal_sourceDeletedLogarithm {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (Q : ℕ) [NeZero Q] {σ : ℝ} (hσ : 1<σ) :
    (sourceDeletedLogarithm lam Q σ : ℂ) =
      LSeries (logZetaCoeff (deletedSourceCoeff lam Q)) (σ : ℂ) := by
  have hs := lseriesSummable_logZetaCoeff
    (fun σ hσ => deletedSourceCoeff_summable hW Q hσ) hσ
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

private theorem hasDerivAt_sourceDeletedLogarithm {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (Q : ℕ) [NeZero Q] {σ : ℝ} (hσ : 1<σ) :
    HasDerivAt (sourceDeletedLogarithm lam Q)
      (-(LSeries (nonCoprimePart Q (WeilHerglotz.lamC lam)) (σ : ℂ)).re) σ := by
  have hd := hasDerivAt_LSeries_logZetaCoeff
    (fun σ hσ => deletedSourceCoeff_summable hW Q hσ)
    (show deletedSourceCoeff lam Q 1=0 by simp [deletedSourceCoeff]) (s := (σ : ℂ)) hσ
  rw [deletedSourceCoeff_cast] at hd
  exact hd.real_of_complex

/-- Full positivity alone gives a finite right limit of the excluded logarithm,
with a Lipschitz remainder. No value for that limit is prescribed. -/
theorem exists_sourceDeletedLogarithm_lipschitz_limit {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (Q : ℕ) [NeZero Q] :
    ∃ ell K eta : ℝ, 0≤K ∧ 0<eta ∧
      Tendsto (sourceDeletedLogarithm lam Q) (𝓝[>] 1) (𝓝 ell) ∧
      ∀ σ : ℝ, 1<σ → σ<1+eta →
      |sourceDeletedLogarithm lam Q σ-ell|≤K*(σ-1) := by
  obtain ⟨K,hK,hbound⟩ := exists_abs_re_nonCoprime_source_le hW Q
  obtain ⟨u,hu,hub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hbound
  let C : NNReal := .mk K hK
  have hderiv (σ : ℝ) (hσ : σ∈Ioo 1 u) := hasDerivAt_sourceDeletedLogarithm hW Q hσ.1
  have hLip : LipschitzOnWith C (sourceDeletedLogarithm lam Q) (Ioo 1 u) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun σ hσ => (hderiv σ hσ).differentiableAt) _ (convex_Ioo 1 u)
    intro σ hσ
    change ‖deriv (sourceDeletedLogarithm lam Q) σ‖≤K
    rw [(hderiv σ hσ).deriv,norm_neg,Real.norm_eq_abs]
    exact hub hσ
  obtain ⟨g,hg,heq⟩ := hLip.extend_real
  have ht : Tendsto (sourceDeletedLogarithm lam Q) (𝓝[>] 1) (𝓝 (g 1)) := by
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
