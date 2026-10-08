import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseDeletionBound
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseDeletionCanonical
import GaloisForLFunctions.RHTower.WeilPositiveProducerLindelof
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# A finite even logarithm at the source pole

The signed polynomial source bounds its even logarithmic derivative.
The real logarithm therefore has a Lipschitz extension to one. Its endpoint
value is retained as an undetermined source constant.
-/

open Complex Filter Topology Set
noncomputable section
namespace RHTower.WeilWorkSettledPhase

/-- The literal even restriction of the normalized arithmetic source. -/
def evenSourceCoeff (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n ∧ 2 ∣ n then lam n else 0

private theorem evenSourceCoeff_cast (lam : ℕ → ℝ) :
    (fun n => (evenSourceCoeff lam n : ℂ)) = evenPart (WeilHerglotz.lamC lam) := by
  funext n
  by_cases hn : 2≤n <;> by_cases he : 2 ∣ n <;>
    simp [evenSourceCoeff,evenPart,WeilHerglotz.lamC,hn,he]

private theorem evenSourceCoeff_summable {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1<σ) :
    Summable fun n : ℕ => |evenSourceCoeff lam n|/(n : ℝ)^σ := by
  refine (WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ).of_nonneg_of_le
    (fun _ => by positivity) fun n => ?_
  unfold evenSourceCoeff
  split_ifs
  · rfl
  · simp only [abs_zero,zero_div]
    positivity

/-- The even logarithmic Dirichlet series, evaluated on its actual half-plane
of absolute convergence. -/
def sourceEvenLogarithm (lam : ℕ → ℝ) (σ : ℝ) : ℝ :=
  (LSeries (logZetaCoeff (evenSourceCoeff lam)) (σ : ℂ)).re

/-- The logarithm is the literal series over positive even source indices. -/
theorem sourceEvenLogarithm_eq_tsum {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1<σ) :
    sourceEvenLogarithm lam σ = ∑' n : ℕ,
      if 2≤n ∧ 2 ∣ n then lam n/(Real.log n*(n : ℝ)^σ) else 0 := by
  have hs := lseriesSummable_logZetaCoeff
    (fun σ hσ => evenSourceCoeff_summable hW hσ) hσ
  rw [sourceEvenLogarithm,LSeries,Complex.re_tsum hs]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · subst n
    simp [LSeries.term]
  · have he : (n : ℂ)^(σ : ℂ) = (((n : ℝ)^σ : ℝ) : ℂ) :=
      (Complex.ofReal_cpow (Nat.cast_nonneg n) σ).symm
    by_cases h : 2≤n ∧ 2 ∣ n <;>
      simp [LSeries.term,logZetaCoeff,evenSourceCoeff,hn,h,he,← Complex.ofReal_div,div_div]

/-- The even logarithmic series is real on its real half-line of convergence. -/
theorem ofReal_sourceEvenLogarithm {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1<σ) :
    (sourceEvenLogarithm lam σ : ℂ) =
      LSeries (logZetaCoeff (evenSourceCoeff lam)) (σ : ℂ) := by
  have hs := lseriesSummable_logZetaCoeff
    (fun σ hσ => evenSourceCoeff_summable hW hσ) hσ
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

private theorem hasDerivAt_sourceEvenLogarithm {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1<σ) :
    HasDerivAt (sourceEvenLogarithm lam)
      (-(LSeries (evenPart (WeilHerglotz.lamC lam)) (σ : ℂ)).re) σ := by
  have hd := hasDerivAt_LSeries_logZetaCoeff
    (fun σ hσ => evenSourceCoeff_summable hW hσ)
    (show evenSourceCoeff lam 1=0 by simp [evenSourceCoeff]) (s := (σ : ℂ)) hσ
  rw [evenSourceCoeff_cast] at hd
  exact hd.real_of_complex

private theorem exists_abs_re_even_source_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ σ : ℝ in 𝓝[>] 1,
      |(LSeries (evenPart (WeilHerglotz.lamC lam)) (σ : ℂ)).re|≤K := by
  obtain ⟨A,hA0,hA⟩ := exists_abs_re_sourceEvenDeviation_le hW
  obtain ⟨C,hC0,hC⟩ := exists_norm_even_vonMangoldt_le
  refine ⟨A+C,add_nonneg hA0 hC0,?_⟩
  filter_upwards [hA,self_mem_nhdsWithin] with σ hA hσ
  change 1<σ at hσ
  have hl := summable_evenPart (WeilHerglotz.summable_term_lamC hW (s := (σ : ℂ)) hσ)
  have hv := summable_evenPart (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) hσ)
  have he : evenPart (WeilHerglotz.lamC lam-fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) =
      evenPart (WeilHerglotz.lamC lam)-evenPart (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    funext n
    by_cases hn : 2 ∣ n <;> simp [evenPart,hn]
  have hid : (LSeries (evenPart (WeilHerglotz.lamC lam)) (σ : ℂ)).re =
      (sourceEvenDeviation lam (σ : ℂ)).re+
        (LSeries (evenPart (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (σ : ℂ)).re := by
    rw [sourceEvenDeviation,he,LSeries_sub hl hv,Complex.sub_re]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hA
    ((Complex.abs_re_le_norm _).trans (hC σ hσ.le)))

/-- Full positivity alone gives a finite right limit of the even logarithm,
with a Lipschitz remainder. No value for that limit is prescribed. -/
theorem exists_sourceEvenLogarithm_lipschitz_limit {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ ell K eta : ℝ, 0≤K ∧ 0<eta ∧
      Tendsto (sourceEvenLogarithm lam) (𝓝[>] 1) (𝓝 ell) ∧
      ∀ σ : ℝ, 1<σ → σ<1+eta →
      |sourceEvenLogarithm lam σ-ell|≤K*(σ-1) := by
  obtain ⟨K,hK,hbound⟩ := exists_abs_re_even_source_le hW
  obtain ⟨u,hu,hub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hbound
  let C : NNReal := .mk K hK
  have hderiv (σ : ℝ) (hσ : σ∈Ioo 1 u) := hasDerivAt_sourceEvenLogarithm hW hσ.1
  have hLip : LipschitzOnWith C (sourceEvenLogarithm lam) (Ioo 1 u) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun σ hσ => (hderiv σ hσ).differentiableAt) _ (convex_Ioo 1 u)
    intro σ hσ
    change ‖deriv (sourceEvenLogarithm lam) σ‖≤K
    rw [(hderiv σ hσ).deriv,norm_neg,Real.norm_eq_abs]
    exact hub hσ
  obtain ⟨g,hg,heq⟩ := hLip.extend_real
  have ht : Tendsto (sourceEvenLogarithm lam) (𝓝[>] 1) (𝓝 (g 1)) := by
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

end RHTower.WeilWorkSettledPhase
