import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeLogarithm
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseThetaTrace

/-!
# A positive finite limit for the actual coprime forward ratio

Coprime restriction commutes with Dirichlet convolution and its exponential.
The ratio is consequently the exponential of the negative excluded logarithm.
Its finite radial limit is not assigned the canonical coprime density.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower.WeilSingularArithmetic
open IntegerMassRigidity WeilWorkSettledPhase

private theorem coprimePart_eq_sub (Q : ℕ) (f : ℕ → ℂ) :
    coprimePart Q f = f - nonCoprimePart Q f := by
  rw [nonCoprimePart_eq_sub]
  abel

private theorem nonCoprimePart_lamLog (lam : ℕ → ℝ) (Q : ℕ) :
    nonCoprimePart Q (lamLog lam) = logZetaCoeff (deletedSourceCoeff lam Q) := by
  funext n
  by_cases hn : 2≤n <;> by_cases he : ¬ n.Coprime Q <;>
    simp [nonCoprimePart,lamLog,logZetaCoeff,deletedSourceCoeff,hn,he]

/-- The literal coprime forward series divided by the full forward series is the
exponential of minus the excluded logarithm. -/
theorem coprime_source_ratio_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (Q : ℕ) [NeZero Q]
    {σ : ℝ} (hσ : 1<σ) :
    LSeries (coprimePart Q (sourceCoeff lam)) (σ : ℂ) / LSeries (sourceCoeff lam) (σ : ℂ) =
      (Real.exp (-sourceDeletedLogarithm lam Q σ) : ℂ) := by
  have hs : 1<(σ : ℂ).re := hσ
  have hl : LSeriesSummable (lamLog lam) (σ : ℂ) :=
    lseriesSummable_of_le (norm_lamLog_le lam)
      (fun _ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ) hs
  have he := (LSeries_dirichletExp
    (show coprimePart Q (lamLog lam) 0=0 by simp [coprimePart,lamLog])
    (show coprimePart Q (lamLog lam) 1=0 by simp [coprimePart,lamLog_one]) (summable_coprimePart Q hl)).2
  rw [show coprimePart Q (sourceCoeff lam) = dirichletExp (coprimePart Q (lamLog lam)) from
      coprimePart_dirichletExp Q (lamLog lam),he,coprimePart_eq_sub,
    LSeries_sub hl (summable_nonCoprimePart Q hl),nonCoprimePart_lamLog,
    ← ofReal_sourceDeletedLogarithm hW Q hσ, (sourceCoeff_LSeries hW hs).2,zetaOf,
    Complex.exp_sub, Complex.ofReal_exp, Complex.ofReal_neg, Complex.exp_neg]
  field_simp [Complex.exp_ne_zero]

/-- The actual coprime-to-full forward ratio has a positive finite radial limit,
with an error bounded linearly by the distance to one. -/
theorem exists_coprime_source_ratio_limit {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (Q : ℕ) [NeZero Q] :
    ∃ r K eta : ℝ, 0<r ∧ 0≤K ∧ 0<eta ∧
      Tendsto (fun σ : ℝ => LSeries (coprimePart Q (sourceCoeff lam)) (σ : ℂ) /
        LSeries (sourceCoeff lam) (σ : ℂ)) (𝓝[>] 1) (𝓝 (r : ℂ)) ∧
      ∀ σ : ℝ, 1<σ → σ<1+eta →
        ‖LSeries (coprimePart Q (sourceCoeff lam)) (σ : ℂ) /
          LSeries (sourceCoeff lam) (σ : ℂ) - (r : ℂ)‖ ≤ K*(σ-1) := by
  obtain ⟨ell,K,eta,hK,heta,ht,herr⟩ := exists_sourceDeletedLogarithm_lipschitz_limit hW Q
  have ht' := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_exp.continuousAt.tendsto.comp ht.neg)
  have htRatio : Tendsto (fun σ : ℝ => LSeries (coprimePart Q (sourceCoeff lam)) (σ : ℂ) /
        LSeries (sourceCoeff lam) (σ : ℂ)) (𝓝[>] 1) (𝓝 (Real.exp (-ell) : ℂ)) := by
    apply ht'.congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (coprime_source_ratio_eq hW Q hσ).symm
  have hnear : ∀ᶠ σ : ℝ in 𝓝[>] 1, |sourceDeletedLogarithm lam Q σ-ell|<1 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp ht) 1 (by norm_num)
  obtain ⟨u,hu,hub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  refine ⟨Real.exp (-ell),2*Real.exp (-ell)*K,min eta (u-1),Real.exp_pos _,
    by positivity,lt_min heta (sub_pos.mpr hu),htRatio,fun σ hσ hσ' => ?_⟩
  have hση : σ<1+eta := by linarith [min_le_left eta (u-1)]
  have hσu : σ<u := by linarith [min_le_right eta (u-1)]
  have hsmall := hub (show σ∈Ioo 1 u from ⟨hσ,hσu⟩)
  rw [coprime_source_ratio_eq hW Q hσ]
  have hn : ‖(-(sourceDeletedLogarithm lam Q σ : ℂ))-(-(ell : ℂ))‖ =
      |sourceDeletedLogarithm lam Q σ-ell| := by
    rw [neg_sub_neg,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
  have h := Complex.locally_lipschitz_exp (r := 1) (by norm_num) le_rfl
    (-(ell : ℂ)) (-(sourceDeletedLogarithm lam Q σ : ℂ)) (by rwa [hn])
  rw [hn] at h
  simp only [← Complex.ofReal_neg,← Complex.ofReal_exp,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at h
  calc
    _ ≤ 2*Real.exp (-ell)*|sourceDeletedLogarithm lam Q σ-ell| := by
      convert h using 1
      norm_num
    _ ≤ 2*Real.exp (-ell)*(K*(σ-1)) :=
      mul_le_mul_of_nonneg_left (herr σ hσ hση) (by positivity)
    _ = _ := by ring

end RHTower.WeilSingularArithmetic
