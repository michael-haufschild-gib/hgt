import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicBlockLevelMoment

/-!
# The measure-times-supremum receiver for the levels of the harmonic level split

On a frequency set of small measure the reciprocal Halasz--Montgomery receiver is the wrong tool:
its `hmMassRecip` carries the term `48 pi N log(2+2T)`, which does not shrink with the set.  What
does shrink is the trivial receiver `∫_E ‖R_D‖² ≤ |E| · (∑_{m ∈ D} ‖a_m‖)²`, and for Menon's
cofactor blocks the supremum `∑_{m ∈ D} 1/m` is `O(1)`.

This file supplies that receiver, applies it level by level, and substitutes the moment budget for
the level measures.  Together with `MenonHarmonicBlockLevelMoment` a schedule may take whichever of
the two is smaller on each level.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The trivial receiver: measure times the square of the coefficient mass.** -/
theorem setIntegral_normSq_logPoly_le_measure_sup
    (a : ℕ → ℂ) (D : Finset ℕ) {W : ℝ} {E : Set ℝ}
    (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W) :
    (∫ w in E, ‖logPoly a D w‖ ^ 2)
      ≤ volume.real E * (∑ n ∈ D, ‖a n‖) ^ 2 := by
  classical
  have hfin : volume E ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hEs)
    simp [Real.volume_Icc]
  have hcont : Continuous fun w : ℝ => ‖logPoly a D w‖ ^ 2 :=
    ((continuous_logPoly a D).norm).pow 2
  have hint1 : IntegrableOn (fun w : ℝ => ‖logPoly a D w‖ ^ 2) E volume :=
    (hcont.integrableOn_Icc (a := -W) (b := W)).mono_set hEs
  have hint2 : IntegrableOn (fun _ : ℝ => (∑ n ∈ D, ‖a n‖) ^ 2) E volume :=
    integrableOn_const (by exact hfin) (by simp)
  have hmono := setIntegral_mono_on hint1 hint2 hEm fun w _ => by
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_logPoly_le a D w) 2
  refine hmono.trans (le_of_eq ?_)
  rw [MeasureTheory.setIntegral_const, smul_eq_mul]

/-- The harmonic cofactor polynomial's coefficient mass is the harmonic mass of its support. -/
theorem sum_norm_harmonicRamareCofactorCoeff_le (P D : Finset ℕ) :
    (∑ n ∈ D, ‖harmonicRamareCofactorCoeff P n‖) ≤ harmonicPrimeMass D := by
  rw [harmonicPrimeMass]
  exact Finset.sum_le_sum fun m _ => norm_harmonicRamareCofactorCoeff_le_inv P m

/-- **One harmonic block product, level split, every level paid by measure times supremum.** -/
theorem setIntegral_normSq_harmonicBlockProduct_levelSplit_trivial
    (P : Finset ℕ) {B : Finset ℕ} (D : Finset ℕ) (hBprime : ∀ p ∈ B, p.Prime) {W : ℝ}
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    {V₀ : ℝ} (hV₀ : 0 < V₀) {J : ℕ} (hJ : harmonicPrimeMass B ≤ 2 ^ J * V₀) :
    (∫ w in E,
      ‖harmonicPrimeBlockPoly B w * logPoly (harmonicRamareCofactorCoeff P) D w‖ ^ 2)
      ≤ V₀ ^ 2 * (volume.real E * harmonicPrimeMass D ^ 2)
        + ∑ i ∈ Finset.range J,
            (2 ^ (i + 1) * V₀) ^ 2 *
              (volume.real (harmonicBlockLevelSet B E (2 ^ i * V₀)) *
                harmonicPrimeMass D ^ 2) := by
  classical
  have hmassD : (0 : ℝ) ≤ harmonicPrimeMass D :=
    Finset.sum_nonneg fun m _ => by positivity
  have hsup : ∀ {S : Set ℝ}, MeasurableSet S → S ⊆ Set.Icc (-W) W →
      (∫ w in S, ‖logPoly (harmonicRamareCofactorCoeff P) D w‖ ^ 2)
        ≤ volume.real S * harmonicPrimeMass D ^ 2 := by
    intro S hSm hSs
    refine (setIntegral_normSq_logPoly_le_measure_sup
      (harmonicRamareCofactorCoeff P) D hSm hSs).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun m _ => norm_nonneg _)
      (sum_norm_harmonicRamareCofactorCoeff_le P D) 2
  have hbase := setIntegral_normSq_harmonicBlockProduct_levelSplit
    (harmonicRamareCofactorCoeff P) D hBprime hEm hEs hV₀ hJ
  refine hbase.trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_left (hsup hEm hEs) (by positivity)
  · refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_left
      (hsup (measurableSet_harmonicBlockLevelSet hEm _)
        (harmonicBlockLevelSet_subset hEs)) (by positivity)

/-- **The same, with every level measure replaced by its moment budget.** -/
theorem setIntegral_normSq_harmonicBlockProduct_levelSplit_trivial_moment
    (P : Finset ℕ) (D : Finset ℕ) {Q eta W : ℝ} (j k : ℕ) (hk : 1 ≤ k)
    (hPprime : ∀ p ∈ P, p.Prime) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    {V₀ : ℝ} (hV₀ : 0 < V₀) {J : ℕ}
    (hJ : harmonicPrimeMass (geomBlock P Q (1 + eta) j) ≤ 2 ^ J * V₀) :
    (∫ w in E,
      ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j) w
        * logPoly (harmonicRamareCofactorCoeff P) D w‖ ^ 2)
      ≤ V₀ ^ 2 * (volume.real E * harmonicPrimeMass D ^ 2)
        + ∑ i ∈ Finset.range J,
            (2 ^ (i + 1) * V₀) ^ 2 *
              ((menonHarmonicLocalBlockMomentCost k Q eta W j / (2 ^ i * V₀) ^ (2 * k)) *
                harmonicPrimeMass D ^ 2) := by
  classical
  have hmassD : (0 : ℝ) ≤ harmonicPrimeMass D :=
    Finset.sum_nonneg fun m _ => by positivity
  have hbase := setIntegral_normSq_harmonicBlockProduct_levelSplit_trivial
    P D (fun p hp => hPprime p (geomBlock_subset P Q (1 + eta) j hp)) hEm hEs hV₀ hJ
  refine hbase.trans (add_le_add le_rfl ?_)
  refine Finset.sum_le_sum fun i _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact volume_harmonicBlockLevelSet_le_localMoment k hk j hPprime hQ heta
    (by linarith) (by positivity) hEs

end

end RHTower.Sieve
