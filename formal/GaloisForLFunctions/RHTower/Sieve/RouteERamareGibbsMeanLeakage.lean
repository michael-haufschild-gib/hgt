import GaloisForLFunctions.RHTower.Sieve.RouteERamareIncidenceConditionalNegative
import GaloisForLFunctions.RHTower.RouteEGibbsUniformCellComparison

/-!
# Route E: Gibbs mean leakage controls incidence-complement covariance

Conditional negativity removes every centered incidence mode.  Pairwise Gibbs likelihood-ratio
oscillation then controls the only surviving positive mode, the scalar conditional mean.  The
result is a sharp finite-cell covariance bound with defect `2 tanh (eta / 4)`, followed by an
all-order equal-product history specialization.
-/

namespace RHTower.Sieve

open Finset

/-- Complex coefficient carrying normalized physical Gibbs mass and a real observable. -/
noncomputable def routeENormalizedWeightedCoefficient
    {Ω : Type*} [Fintype Ω] (weight observable : Ω → ℝ) (x : Ω) : ℂ :=
  (((weight x * observable x) / (∑ y, weight y) : ℝ) : ℂ)

theorem routeE_sum_normalizedWeightedCoefficient
    {Ω : Type*} [Fintype Ω] (weight observable : Ω → ℝ) :
    ∑ x, routeENormalizedWeightedCoefficient weight observable x =
      (((∑ x, weight x * observable x) / (∑ x, weight x) : ℝ) : ℂ) := by
  simp only [routeENormalizedWeightedCoefficient, ← Complex.ofReal_sum]
  congr 1
  rw [Finset.sum_div]

/--
Sharp Gibbs-to-incidence covariance transfer. The centered complement form is nonpositive, so
only physical conditional-mean leakage from the uniform cell can remain positive.
-/
theorem routeE_incidenceComplement_gibbs_le_tanhMeanLeakage
    {ι Ω : Type*} [DecidableEq ι] [Fintype Ω] [Nonempty Ω]
    (P : Finset ι) (F : Ω → Finset ι) (weight observable : Ω → ℝ) (eta : ℝ)
    (hFsub : ∀ x, F x ⊆ P) (hFne : ∀ x, (F x).Nonempty)
    (hweight : ∀ x, 0 < weight x) (heta : 0 ≤ eta)
    (hlog : ∀ x y, |Real.log (weight x / weight y)| ≤ eta)
    (hobservable : ∀ x, |observable x| ≤ 1) :
    ∑ x, ∑ y,
        routeEIncidenceComplement (F x) (F y) *
          (routeENormalizedWeightedCoefficient weight observable x *
            (starRingEnd ℂ) (routeENormalizedWeightedCoefficient weight observable y)).re ≤
      (|(∑ x, observable x) / (Fintype.card Ω : ℝ)| +
        2 * Real.tanh (eta / 4)) ^ (2 : ℕ) := by
  classical
  let c : Ω → ℂ := routeENormalizedWeightedCoefficient weight observable
  let physicalMean := (∑ x, weight x * observable x) / (∑ x, weight x)
  let uniformMean := (∑ x, observable x) / (Fintype.card Ω : ℝ)
  have hdecomp := routeE_incidenceComplement_decomposition P Finset.univ F c
    (fun x _ => hFsub x) (fun x _ => hFne x)
  have henergy : 0 ≤
      ∑ p ∈ P, Complex.normSq (routeENormalizedIncidenceBlock Finset.univ F c p) :=
    Finset.sum_nonneg fun p hp => Complex.normSq_nonneg _
  have hquad :
      ∑ x, ∑ y,
          routeEIncidenceComplement (F x) (F y) *
            (c x * (starRingEnd ℂ) (c y)).re ≤
        Complex.normSq (∑ x, c x) := by
    rw [hdecomp]
    linarith
  have hsum : ∑ x, c x = (physicalMean : ℂ) := by
    exact routeE_sum_normalizedWeightedCoefficient weight observable
  have hcompare : |physicalMean - uniformMean| ≤ 2 * Real.tanh (eta / 4) := by
    exact routeE_abs_weightedMean_sub_uniformMean_le_tanhDefect
      weight observable eta hweight heta hlog hobservable
  have hdelta : 0 ≤ 2 * Real.tanh (eta / 4) :=
    routeE_two_tanh_quarter_nonneg heta
  have habs : |physicalMean| ≤ |uniformMean| + 2 * Real.tanh (eta / 4) := by
    calc
      |physicalMean| ≤ |uniformMean| + |physicalMean - uniformMean| := by
        linarith [abs_sub_abs_le_abs_sub physicalMean uniformMean]
      _ ≤ _ := by linarith
  have hsquare : physicalMean ^ (2 : ℕ) ≤
      (|uniformMean| + 2 * Real.tanh (eta / 4)) ^ (2 : ℕ) := by
    have hright : 0 ≤ |uniformMean| + 2 * Real.tanh (eta / 4) :=
      add_nonneg (abs_nonneg _) hdelta
    have hsquareAbs := (sq_le_sq₀ (abs_nonneg physicalMean) hright).2 habs
    simpa only [sq_abs] using hsquareAbs
  dsimp [c] at hquad ⊢
  rw [hsum, Complex.normSq_ofReal] at hquad
  have hsquare' : physicalMean * physicalMean ≤
      (|uniformMean| + 2 * Real.tanh (eta / 4)) *
        (|uniformMean| + 2 * Real.tanh (eta / 4)) := by
    simpa only [pow_two] using hsquare
  have hfinal := hquad.trans hsquare'
  dsimp [physicalMean, uniformMean] at hfinal
  simpa only [pow_two] using hfinal

/--
All-order equal-product history consumer. Product curvature supplies the exact log-likelihood
oscillation, while conditional negativity eliminates every centered prime-incidence mode.
-/
theorem routeE_productHistory_incidenceComplement_le_tanhMeanLeakage
    {ι Ω R : Type*} [DecidableEq ι] [Fintype Ω] [Nonempty Ω] [Fintype R]
    (P : Finset ι) (F : Ω → Finset ι) (X H : ℝ)
    (history : Ω → R → ℝ) (observable : Ω → ℝ)
    (hFsub : ∀ x, F x ⊆ P) (hFne : ∀ x, (F x).Nonempty)
    (hX : 0 < X) (hH : 0 ≤ H) (hHX : H < X)
    (haperture : ∀ ω r, history ω r ∈ Set.Icc (X - H) (X + H))
    (hproduct : ∀ ω ξ, ∏ r, history ω r = ∏ r, history ξ r)
    (hobservable : ∀ ω, |observable ω| ≤ 1) :
    ∑ x, ∑ y,
        routeEIncidenceComplement (F x) (F y) *
          (routeENormalizedWeightedCoefficient
              (fun ω => routeEProductHistoryGibbsWeight X (history ω)) observable x *
            (starRingEnd ℂ)
              (routeENormalizedWeightedCoefficient
                (fun ω => routeEProductHistoryGibbsWeight X (history ω)) observable y)).re ≤
      (|(∑ x, observable x) / (Fintype.card Ω : ℝ)| +
        2 * Real.tanh
          (((Fintype.card R : ℝ) * H ^ (2 : ℕ) / (X * (X - H))) / 4)) ^ (2 : ℕ) := by
  let eta := (Fintype.card R : ℝ) * H ^ (2 : ℕ) / (X * (X - H))
  have hXH : 0 < X - H := sub_pos.mpr hHX
  have heta : 0 ≤ eta := by
    dsimp [eta]
    positivity
  apply routeE_incidenceComplement_gibbs_le_tanhMeanLeakage
    P F (fun ω => routeEProductHistoryGibbsWeight X (history ω)) observable eta
    hFsub hFne
  · intro ω
    rw [routeEProductHistoryGibbsWeight_eq_exp_sum]
    exact Real.exp_pos _
  · exact heta
  · intro ω ξ
    exact routeEProductHistory_abs_log_gibbs_ratio_le X H
      (history ω) (history ξ) hX hH hHX
      (haperture ω) (haperture ξ) (hproduct ω ξ)
  · exact hobservable

end RHTower.Sieve
