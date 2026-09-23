import GaloisForLFunctions.RHTower.SelbergMaassFourierPartial
import GaloisForLFunctions.RHTower.Sieve.EnergyCauchySchwarz

/-!
# Analytic estimates for the weighted Maass phase-product limit

The unresolved top phase stress is a bounded-coordinate-weighted mixed product of horizontal and
height derivatives.  This file supplies the two exact interval estimates needed to pass its finite
Fourier truncations to a physical limit: Cauchy--Schwarz for the complex unit-interval pairing and
contraction by the coordinate weight.  Their telescoping combination transports the finite
partial products to the physical weighted pairing without introducing any sign claim for the
surviving off-diagonal coefficient sum.
-/

open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.RHTower.SelbergMaassPhaseProductLimit
open GaloisForLFunctions.HTGeometry SelbergMaassCongruenceTrace
noncomputable section

/-- Complex Cauchy--Schwarz for the unit-interval pairing, expressed in the squared norm used by
Fourier partial-sum convergence. -/
theorem norm_l2Pair_le_sqrt_l2NormSq {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    ‖l2Pair f g‖ ≤ Real.sqrt (l2NormSq f) * Real.sqrt (l2NormSq g) := by
  have hnorm : ‖l2Pair f g‖ ≤ ∫ t in (0 : ℝ)..1, ‖f t‖ * ‖g t‖ := by
    rw [l2Pair]
    refine (intervalIntegral.norm_integral_le_integral_norm (μ := volume) (by norm_num)).trans_eq ?_
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [norm_mul, Complex.norm_conj]
  have hcs := RHTower.Sieve.integral_mul_sq_le (a := (0 : ℝ)) (b := 1)
    (by norm_num) hf.norm hg.norm
  have hcs' : (∫ t in (0 : ℝ)..1, ‖f t‖ * ‖g t‖) ^ (2 : ℕ) ≤
      l2NormSq f * l2NormSq g := by
    simpa only [l2NormSq] using hcs
  have hprod : 0 ≤ ∫ t in (0 : ℝ)..1, ‖f t‖ * ‖g t‖ := by
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsquare : (Real.sqrt (l2NormSq f) * Real.sqrt (l2NormSq g)) ^ (2 : ℕ) =
      l2NormSq f * l2NormSq g := by
    rw [mul_pow, Real.sq_sqrt (l2NormSq_nonneg f), Real.sq_sqrt (l2NormSq_nonneg g)]
  apply hnorm.trans
  apply (sq_le_sq₀ hprod (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [hsquare]
  exact hcs'

/-- Multiplication by the unit-interval coordinate is contractive for squared `L²` norm. -/
theorem l2NormSq_unitCoord_mul_le {g : ℝ → ℂ} (hg : Continuous g) :
    l2NormSq (fun t => (t : ℂ) * g t) ≤ l2NormSq g := by
  have hcont : Continuous (fun t : ℝ => (t : ℂ) * g t) :=
    (Complex.continuous_ofReal.comp continuous_id).mul hg
  change (∫ t in (0 : ℝ)..1, ‖(t : ℂ) * g t‖ ^ (2 : ℕ)) ≤
    ∫ t in (0 : ℝ)..1, ‖g t‖ ^ (2 : ℕ)
  refine intervalIntegral.integral_mono_on (μ := volume) (by norm_num)
    ((hcont.norm.pow 2).intervalIntegrable 0 1)
    ((hg.norm.pow 2).intervalIntegrable 0 1) ?_
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  have htsq : t ^ (2 : ℕ) ≤ 1 := by nlinarith [sq_nonneg (1 - t)]
  have hgsq : 0 ≤ ‖g t‖ ^ (2 : ℕ) := sq_nonneg _
  calc
    (t * ‖g t‖) ^ (2 : ℕ) = t ^ (2 : ℕ) * ‖g t‖ ^ (2 : ℕ) := by ring
    _ ≤ 1 * ‖g t‖ ^ (2 : ℕ) := mul_le_mul_of_nonneg_right htsq hgsq
    _ = ‖g t‖ ^ (2 : ℕ) := by ring

private theorem l2NormSq_sub_comm {f g : ℝ → ℂ} :
    l2NormSq (fun t => f t - g t) = l2NormSq (fun t => g t - f t) := by
  unfold l2NormSq
  apply intervalIntegral.integral_congr
  intro t _
  change ‖f t - g t‖ ^ (2 : ℕ) = ‖g t - f t‖ ^ (2 : ℕ)
  have h : f t - g t = -(g t - f t) := by ring
  rw [h, norm_neg]

private theorem continuous_unitCoord_mul (g : ℝ → ℂ) (hg : Continuous g) :
    Continuous (fun t : ℝ => (t : ℂ) * g t) :=
  (Complex.continuous_ofReal.comp continuous_id).mul hg

theorem tendsto_l2Pair_unitCoord_fourierPartialSum {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    Tendsto (fun M : ℕ =>
      l2Pair (fourierPartialSum f M) (fun t => (t : ℂ) * fourierPartialSum g M t)) atTop
      (𝓝 (l2Pair f (fun t => (t : ℂ) * g t))) := by
  have hF0 := tendsto_l2NormSq_sub_fourierPartialSum hf
  have hG0 := tendsto_l2NormSq_sub_fourierPartialSum hg
  have hF : Tendsto (fun M : ℕ =>
      l2NormSq (fun t => fourierPartialSum f M t - f t)) atTop (𝓝 0) := by
    refine hF0.congr' ?_
    filter_upwards with M
    exact l2NormSq_sub_comm
  have hG : Tendsto (fun M : ℕ =>
      l2NormSq (fun t => fourierPartialSum g M t - g t)) atTop (𝓝 0) := by
    refine hG0.congr' ?_
    filter_upwards with M
    exact l2NormSq_sub_comm
  have hGsmall : ∀ᶠ M : ℕ in atTop,
      l2NormSq (fun t => fourierPartialSum g M t - g t) ≤ 1 := by
    filter_upwards [hG.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))] with M hM
    rw [dist_zero_right] at hM
    have hnn := l2NormSq_nonneg (fun t => fourierPartialSum g M t - g t)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn] at hM
    linarith
  let C : ℝ := 2 * l2NormSq g + 2
  have hC : 0 ≤ C := by
    dsimp [C]
    nlinarith [l2NormSq_nonneg g]
  have hPGbound : ∀ᶠ M : ℕ in atTop, l2NormSq (fourierPartialSum g M) ≤ C := by
    filter_upwards [hGsmall] with M hM
    have hcont : Continuous (fun t => fourierPartialSum g M t - g t) :=
      (continuous_fourierPartialSum g M).sub hg
    have hadd := l2NormSq_add_le hg hcont
    have hfun : (fun t => g t + (fourierPartialSum g M t - g t)) =
        fourierPartialSum g M := by
      funext t
      ring
    rw [hfun] at hadd
    dsimp [C]
    linarith
  have hFroot : Tendsto (fun M : ℕ =>
      Real.sqrt (l2NormSq (fun t => fourierPartialSum f M t - f t))) atTop (𝓝 0) := by
    change Tendsto ((fun x : ℝ => Real.sqrt x) ∘
      fun M : ℕ => l2NormSq (fun t => fourierPartialSum f M t - f t)) atTop (𝓝 0)
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hF
  have hGroot : Tendsto (fun M : ℕ =>
      Real.sqrt (l2NormSq (fun t => fourierPartialSum g M t - g t))) atTop (𝓝 0) := by
    change Tendsto ((fun x : ℝ => Real.sqrt x) ∘
      fun M : ℕ => l2NormSq (fun t => fourierPartialSum g M t - g t)) atTop (𝓝 0)
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hG
  have hR : Tendsto (fun M : ℕ =>
      Real.sqrt (l2NormSq (fun t => fourierPartialSum f M t - f t)) * Real.sqrt C +
        Real.sqrt (l2NormSq f) *
          Real.sqrt (l2NormSq (fun t => fourierPartialSum g M t - g t))) atTop (𝓝 0) := by
    have h1 := hFroot.mul_const (Real.sqrt C)
    have h2 := hGroot.const_mul (Real.sqrt (l2NormSq f))
    simpa using h1.add h2
  have hbound : ∀ᶠ M : ℕ in atTop,
      ‖l2Pair (fourierPartialSum f M) (fun t => (t : ℂ) * fourierPartialSum g M t) -
        l2Pair f (fun t => (t : ℂ) * g t)‖ ≤
        Real.sqrt (l2NormSq (fun t => fourierPartialSum f M t - f t)) * Real.sqrt C +
          Real.sqrt (l2NormSq f) *
            Real.sqrt (l2NormSq (fun t => fourierPartialSum g M t - g t)) := by
    filter_upwards [hPGbound] with M hM
    have hPF : Continuous (fourierPartialSum f M) := continuous_fourierPartialSum f M
    have hPG : Continuous (fourierPartialSum g M) := continuous_fourierPartialSum g M
    have hEF : Continuous (fun t => fourierPartialSum f M t - f t) := hPF.sub hf
    have hEG : Continuous (fun t => fourierPartialSum g M t - g t) := hPG.sub hg
    have hWPG := continuous_unitCoord_mul _ hPG
    have hWEG := continuous_unitCoord_mul _ hEG
    have hWG := continuous_unitCoord_mul _ hg
    have hsplit :
        l2Pair (fourierPartialSum f M) (fun t => (t : ℂ) * fourierPartialSum g M t) -
          l2Pair f (fun t => (t : ℂ) * g t) =
        l2Pair (fun t => fourierPartialSum f M t - f t)
          (fun t => (t : ℂ) * fourierPartialSum g M t) +
        l2Pair f (fun t => (t : ℂ) * (fourierPartialSum g M t - g t)) := by
      have hmul : (fun t : ℝ => (t : ℂ) * fourierPartialSum g M t - (t : ℂ) * g t) =
          fun t : ℝ => (t : ℂ) * (fourierPartialSum g M t - g t) := by
        funext t
        ring
      have hright :
          l2Pair f (fun t => (t : ℂ) * fourierPartialSum g M t) -
            l2Pair f (fun t => (t : ℂ) * g t) =
          l2Pair f (fun t => (t : ℂ) * (fourierPartialSum g M t - g t)) := by
        rw [← l2Pair_sub_right hf hWPG hWG, hmul]
      calc
        l2Pair (fourierPartialSum f M) (fun t => (t : ℂ) * fourierPartialSum g M t) -
            l2Pair f (fun t => (t : ℂ) * g t) =
            (l2Pair (fourierPartialSum f M) (fun t => (t : ℂ) * fourierPartialSum g M t) -
              l2Pair f (fun t => (t : ℂ) * fourierPartialSum g M t)) +
              (l2Pair f (fun t => (t : ℂ) * fourierPartialSum g M t) -
                l2Pair f (fun t => (t : ℂ) * g t)) := by ring
        _ = (l2Pair (fourierPartialSum f M) (fun t => (t : ℂ) * fourierPartialSum g M t) -
              l2Pair f (fun t => (t : ℂ) * fourierPartialSum g M t)) +
              l2Pair f (fun t => (t : ℂ) * (fourierPartialSum g M t - g t)) := by rw [hright]
        _ = _ := by rw [← l2Pair_sub_left hPF hf hWPG]
    rw [hsplit]
    calc
      ‖l2Pair (fun t => fourierPartialSum f M t - f t)
          (fun t => (t : ℂ) * fourierPartialSum g M t) +
        l2Pair f (fun t => (t : ℂ) * (fourierPartialSum g M t - g t))‖ ≤
          ‖l2Pair (fun t => fourierPartialSum f M t - f t)
            (fun t => (t : ℂ) * fourierPartialSum g M t)‖ +
          ‖l2Pair f (fun t => (t : ℂ) * (fourierPartialSum g M t - g t))‖ := norm_add_le _ _
      _ ≤ Real.sqrt (l2NormSq (fun t => fourierPartialSum f M t - f t)) *
          Real.sqrt (l2NormSq (fun t => (t : ℂ) * fourierPartialSum g M t)) +
          Real.sqrt (l2NormSq f) *
            Real.sqrt (l2NormSq (fun t => (t : ℂ) * (fourierPartialSum g M t - g t))) := by
        gcongr
        · exact norm_l2Pair_le_sqrt_l2NormSq hEF hWPG
        · exact norm_l2Pair_le_sqrt_l2NormSq hf hWEG
      _ ≤ Real.sqrt (l2NormSq (fun t => fourierPartialSum f M t - f t)) * Real.sqrt C +
          Real.sqrt (l2NormSq f) *
            Real.sqrt (l2NormSq (fun t => fourierPartialSum g M t - g t)) := by
        have hweightPG := l2NormSq_unitCoord_mul_le hPG
        have hweightEG := l2NormSq_unitCoord_mul_le hEG
        have hPGroot : Real.sqrt (l2NormSq (fun t => (t : ℂ) * fourierPartialSum g M t)) ≤
            Real.sqrt C := Real.sqrt_le_sqrt (hweightPG.trans hM)
        have hEGroot : Real.sqrt (l2NormSq (fun t => (t : ℂ) * (fourierPartialSum g M t - g t))) ≤
            Real.sqrt (l2NormSq (fun t => fourierPartialSum g M t - g t)) :=
          Real.sqrt_le_sqrt hweightEG
        gcongr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    hbound hR

/-- The weighted partial-product limit applies directly to any horizontal and height readouts of
one physical Maass source slice. -/
theorem tendsto_unitCoord_sourceReadout_partial_pair
    (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (L H : EuclideanSpace ℂ (Deck N) →L[ℂ] ℂ)
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun M : ℕ =>
      l2Pair
        (fourierPartialSum
          (SelbergMaassFourierPartial.unitRescaledHorizontalReadout N f L y) M)
        (fun t => (t : ℂ) * fourierPartialSum
          (SelbergMaassFourierPartial.unitRescaledVerticalReadout N f H y) M t)) atTop
      (𝓝 (l2Pair
        (SelbergMaassFourierPartial.unitRescaledHorizontalReadout N f L y)
        (fun t => (t : ℂ) *
          SelbergMaassFourierPartial.unitRescaledVerticalReadout N f H y t))) :=
  tendsto_l2Pair_unitCoord_fourierPartialSum
    (SelbergMaassFourierPartial.continuous_unitRescaledHorizontalReadout N f L hy)
    (SelbergMaassFourierPartial.continuous_unitRescaledVerticalReadout N f H hy)


/-- Unweighted unit Fourier partial pairings converge to the physical pairing. -/
theorem tendsto_l2Pair_fourierPartialSum {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    Tendsto (fun M : ℕ =>
      l2Pair (fourierPartialSum f M) (fourierPartialSum g M)) atTop
      (𝓝 (l2Pair f g)) := by
  have hF0 := tendsto_l2NormSq_sub_fourierPartialSum hf
  have hG0 := tendsto_l2NormSq_sub_fourierPartialSum hg
  have hF : Tendsto (fun M : ℕ =>
      l2NormSq (fun t => fourierPartialSum f M t - f t)) atTop (𝓝 0) := by
    refine hF0.congr' ?_
    filter_upwards with M
    exact l2NormSq_sub_comm
  have hG : Tendsto (fun M : ℕ =>
      l2NormSq (fun t => fourierPartialSum g M t - g t)) atTop (𝓝 0) := by
    refine hG0.congr' ?_
    filter_upwards with M
    exact l2NormSq_sub_comm
  have hGsmall : ∀ᶠ M : ℕ in atTop,
      l2NormSq (fun t => fourierPartialSum g M t - g t) ≤ 1 := by
    filter_upwards [hG.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))] with M hM
    rw [dist_zero_right] at hM
    have hnn := l2NormSq_nonneg (fun t => fourierPartialSum g M t - g t)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn] at hM
    linarith
  let C : ℝ := 2 * l2NormSq g + 2
  have hPGbound : ∀ᶠ M : ℕ in atTop, l2NormSq (fourierPartialSum g M) ≤ C := by
    filter_upwards [hGsmall] with M hM
    have hcont : Continuous (fun t => fourierPartialSum g M t - g t) :=
      (continuous_fourierPartialSum g M).sub hg
    have hadd := l2NormSq_add_le hg hcont
    have hfun : (fun t => g t + (fourierPartialSum g M t - g t)) =
        fourierPartialSum g M := by
      funext t
      ring
    rw [hfun] at hadd
    dsimp [C]
    linarith
  have hFroot : Tendsto (fun M : ℕ =>
      Real.sqrt (l2NormSq (fun t => fourierPartialSum f M t - f t))) atTop (𝓝 0) := by
    change Tendsto ((fun x : ℝ => Real.sqrt x) ∘
      fun M : ℕ => l2NormSq (fun t => fourierPartialSum f M t - f t)) atTop (𝓝 0)
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hF
  have hGroot : Tendsto (fun M : ℕ =>
      Real.sqrt (l2NormSq (fun t => fourierPartialSum g M t - g t))) atTop (𝓝 0) := by
    change Tendsto ((fun x : ℝ => Real.sqrt x) ∘
      fun M : ℕ => l2NormSq (fun t => fourierPartialSum g M t - g t)) atTop (𝓝 0)
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hG
  have hR : Tendsto (fun M : ℕ =>
      Real.sqrt (l2NormSq (fun t => fourierPartialSum f M t - f t)) * Real.sqrt C +
        Real.sqrt (l2NormSq f) *
          Real.sqrt (l2NormSq (fun t => fourierPartialSum g M t - g t))) atTop (𝓝 0) := by
    have h1 := hFroot.mul_const (Real.sqrt C)
    have h2 := hGroot.const_mul (Real.sqrt (l2NormSq f))
    simpa using h1.add h2
  have hbound : ∀ᶠ M : ℕ in atTop,
      ‖l2Pair (fourierPartialSum f M) (fourierPartialSum g M) - l2Pair f g‖ ≤
        Real.sqrt (l2NormSq (fun t => fourierPartialSum f M t - f t)) * Real.sqrt C +
          Real.sqrt (l2NormSq f) *
            Real.sqrt (l2NormSq (fun t => fourierPartialSum g M t - g t)) := by
    filter_upwards [hPGbound] with M hM
    have hPF : Continuous (fourierPartialSum f M) := continuous_fourierPartialSum f M
    have hPG : Continuous (fourierPartialSum g M) := continuous_fourierPartialSum g M
    have hEF : Continuous (fun t => fourierPartialSum f M t - f t) := hPF.sub hf
    have hEG : Continuous (fun t => fourierPartialSum g M t - g t) := hPG.sub hg
    have hsplit :
        l2Pair (fourierPartialSum f M) (fourierPartialSum g M) - l2Pair f g =
          l2Pair (fun t => fourierPartialSum f M t - f t) (fourierPartialSum g M) +
            l2Pair f (fun t => fourierPartialSum g M t - g t) := by
      have hright : l2Pair f (fourierPartialSum g M) - l2Pair f g =
          l2Pair f (fun t => fourierPartialSum g M t - g t) := by
        rw [← l2Pair_sub_right hf hPG hg]
      calc
        l2Pair (fourierPartialSum f M) (fourierPartialSum g M) - l2Pair f g =
            (l2Pair (fourierPartialSum f M) (fourierPartialSum g M) -
              l2Pair f (fourierPartialSum g M)) +
              (l2Pair f (fourierPartialSum g M) - l2Pair f g) := by ring
        _ = (l2Pair (fourierPartialSum f M) (fourierPartialSum g M) -
              l2Pair f (fourierPartialSum g M)) +
              l2Pair f (fun t => fourierPartialSum g M t - g t) := by rw [hright]
        _ = _ := by rw [← l2Pair_sub_left hPF hf hPG]
    rw [hsplit]
    calc
      ‖l2Pair (fun t => fourierPartialSum f M t - f t) (fourierPartialSum g M) +
        l2Pair f (fun t => fourierPartialSum g M t - g t)‖ ≤
          ‖l2Pair (fun t => fourierPartialSum f M t - f t) (fourierPartialSum g M)‖ +
          ‖l2Pair f (fun t => fourierPartialSum g M t - g t)‖ := norm_add_le _ _
      _ ≤ Real.sqrt (l2NormSq (fun t => fourierPartialSum f M t - f t)) *
          Real.sqrt (l2NormSq (fourierPartialSum g M)) +
          Real.sqrt (l2NormSq f) *
            Real.sqrt (l2NormSq (fun t => fourierPartialSum g M t - g t)) := by
        gcongr
        · exact norm_l2Pair_le_sqrt_l2NormSq hEF hPG
        · exact norm_l2Pair_le_sqrt_l2NormSq hf hEG
      _ ≤ Real.sqrt (l2NormSq (fun t => fourierPartialSum f M t - f t)) * Real.sqrt C +
          Real.sqrt (l2NormSq f) *
            Real.sqrt (l2NormSq (fun t => fourierPartialSum g M t - g t)) := by
        have hPGroot : Real.sqrt (l2NormSq (fourierPartialSum g M)) ≤ Real.sqrt C :=
          Real.sqrt_le_sqrt hM
        gcongr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound hR


/-- A finite unweighted Fourier pairing contains only equal Fourier indices. -/
theorem l2Pair_fourierPartialSum_eq_diagonal (f g : ℝ → ℂ) (M : ℕ) :
    l2Pair (fourierPartialSum f M) (fourierPartialSum g M) =
      ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        (starRingEnd ℂ) (l2Pair (fourierChar n) f) * l2Pair (fourierChar n) g := by
  set S : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ) with hS
  set cf : ℤ → ℂ := fun n => l2Pair (fourierChar n) f with hcf
  set cg : ℤ → ℂ := fun n => l2Pair (fourierChar n) g with hcg
  have hexp : ∀ x : ℝ, (starRingEnd ℂ) (fourierPartialSum f M x) * fourierPartialSum g M x =
      ∑ i ∈ S, ∑ j ∈ S, ((starRingEnd ℂ) (cf i) * cg j) *
        (fourierChar (-i) x * fourierChar j x) := by
    intro x
    simp only [fourierPartialSum_eq, hS, hcf, hcg, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, fourierChar_conj, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [l2Pair, intervalIntegral.integral_congr (fun x _ => hexp x),
    intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.sum_eq_single i]
      · rw [intervalIntegral.integral_const_mul, integral_fourierChar_orthonormal, if_pos rfl,
          mul_one]
      · intro j _ hji
        rw [intervalIntegral.integral_const_mul, integral_fourierChar_orthonormal,
          if_neg (fun h => hji h.symm), mul_zero]
      · intro h
        exact absurd hi h
    · intro j _
      refine Continuous.intervalIntegrable ?_ _ _
      exact continuous_const.mul ((continuous_fourierChar _).mul (continuous_fourierChar _))
  · intro i _
    refine Continuous.intervalIntegrable ?_ _ _
    refine continuous_finsetSum _ fun j _ => ?_
    exact continuous_const.mul ((continuous_fourierChar _).mul (continuous_fourierChar _))

end
end GaloisForLFunctions.RHTower.SelbergMaassPhaseProductLimit
