import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseDeletionLogarithm
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseThetaTrace

/-!
# A positive finite limit for the actual odd forward ratio

Odd restriction commutes with Dirichlet convolution and its exponential.
The ratio is consequently the exponential of the negative even logarithm.
Its finite radial limit is not assigned the canonical value one half.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower.WeilWorkSettledPhase
open IntegerMassRigidity

private theorem evenPart_lamLog (lam : ℕ → ℝ) :
    evenPart (lamLog lam) = logZetaCoeff (evenSourceCoeff lam) := by
  funext n
  by_cases hn : 2≤n <;> by_cases he : 2 ∣ n <;>
    simp [evenPart,lamLog,logZetaCoeff,evenSourceCoeff,hn,he]

/-- The literal odd forward series divided by the full forward series is the
exponential of minus the even logarithm. -/
theorem odd_source_ratio_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1<σ) :
    LSeries (oddPart (sourceCoeff lam)) (σ : ℂ) / LSeries (sourceCoeff lam) (σ : ℂ) =
      (Real.exp (-sourceEvenLogarithm lam σ) : ℂ) := by
  have hs : 1<(σ : ℂ).re := hσ
  have hl : LSeriesSummable (lamLog lam) (σ : ℂ) :=
    lseriesSummable_of_le (norm_lamLog_le lam)
      (fun _ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ) hs
  have he := (LSeries_dirichletExp
    (show oddPart (lamLog lam) 0=0 by simp [oddPart])
    (show oddPart (lamLog lam) 1=0 by simp [oddPart,lamLog_one]) (summable_oddPart hl)).2
  rw [show oddPart (sourceCoeff lam) = dirichletExp (oddPart (lamLog lam)) from
      oddPart_dirichletExp (lamLog lam),he,oddPart_eq_sub,
    LSeries_sub hl (summable_evenPart hl),evenPart_lamLog,
    ← ofReal_sourceEvenLogarithm hW hσ, (sourceCoeff_LSeries hW hs).2,zetaOf,
    Complex.exp_sub, Complex.ofReal_exp, Complex.ofReal_neg, Complex.exp_neg]
  field_simp [Complex.exp_ne_zero]

/-- The actual odd-to-full forward ratio has a positive finite radial limit,
with an error bounded linearly by the distance to one. -/
theorem exists_odd_source_ratio_limit {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ r K eta : ℝ, 0<r ∧ 0≤K ∧ 0<eta ∧
      Tendsto (fun σ : ℝ => LSeries (oddPart (sourceCoeff lam)) (σ : ℂ) /
        LSeries (sourceCoeff lam) (σ : ℂ)) (𝓝[>] 1) (𝓝 (r : ℂ)) ∧
      ∀ σ : ℝ, 1<σ → σ<1+eta →
        ‖LSeries (oddPart (sourceCoeff lam)) (σ : ℂ) /
          LSeries (sourceCoeff lam) (σ : ℂ) - (r : ℂ)‖ ≤ K*(σ-1) := by
  obtain ⟨ell,K,eta,hK,heta,ht,herr⟩ := exists_sourceEvenLogarithm_lipschitz_limit hW
  have ht' := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (Real.continuous_exp.continuousAt.tendsto.comp ht.neg)
  have htRatio : Tendsto (fun σ : ℝ => LSeries (oddPart (sourceCoeff lam)) (σ : ℂ) /
        LSeries (sourceCoeff lam) (σ : ℂ)) (𝓝[>] 1) (𝓝 (Real.exp (-ell) : ℂ)) := by
    apply ht'.congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (odd_source_ratio_eq hW hσ).symm
  have hnear : ∀ᶠ σ : ℝ in 𝓝[>] 1, |sourceEvenLogarithm lam σ-ell|<1 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp ht) 1 (by norm_num)
  obtain ⟨u,hu,hub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  refine ⟨Real.exp (-ell),2*Real.exp (-ell)*K,min eta (u-1),Real.exp_pos _,
    by positivity,lt_min heta (sub_pos.mpr hu),htRatio,fun σ hσ hσ' => ?_⟩
  have hση : σ<1+eta := by linarith [min_le_left eta (u-1)]
  have hσu : σ<u := by linarith [min_le_right eta (u-1)]
  have hsmall := hub (show σ∈Ioo 1 u from ⟨hσ,hσu⟩)
  rw [odd_source_ratio_eq hW hσ]
  have hn : ‖(-(sourceEvenLogarithm lam σ : ℂ))-(-(ell : ℂ))‖ =
      |sourceEvenLogarithm lam σ-ell| := by
    rw [neg_sub_neg,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
  have h := Complex.locally_lipschitz_exp (r := 1) (by norm_num) le_rfl
    (-(ell : ℂ)) (-(sourceEvenLogarithm lam σ : ℂ)) (by rwa [hn])
  rw [hn] at h
  simp only [← Complex.ofReal_neg,← Complex.ofReal_exp,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at h
  calc
    _ ≤ 2*Real.exp (-ell)*|sourceEvenLogarithm lam σ-ell| := by
      convert h using 1
      norm_num
    _ ≤ 2*Real.exp (-ell)*(K*(σ-1)) :=
      mul_le_mul_of_nonneg_left (herr σ hσ hση) (by positivity)
    _ = _ := by ring

end RHTower.WeilWorkSettledPhase
