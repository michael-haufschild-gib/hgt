import GaloisForLFunctions.BiScaleUncertainty.DistantCopyPolarEnforcement

/-!
# Finite exponential moments do not change the grid energy infimum

A separated copy has small normalized energy cost uniformly in its coefficient. Thus real
exponential moments can be canceled at positive, zero, or negative rates. Successive cancellations
preserve previous zero moments and all normalized correlations on a prescribed bounded interval.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-- Uniform control independent of the coefficient, including exponentially growing copies. -/
theorem normalizedArchEnergy_subtractCopy_uniform_error {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) {D T : ℝ}
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 ≤ T) (a : ℝ) :
    |normalizedArchEnergy (subtractCopy f a T) - normalizedArchEnergy f| ≤
      polarEnergyErrorConstant f D * Real.exp (-T / 2) := by
  have hM : 0 ≤ ∫ x, |autocorr f x| := integral_nonneg (fun _ => abs_nonneg _)
  have hden : 0 < (1 + a ^ 2) * autocorr f 0 := by positivity
  have ha : |a| ≤ 1 + a ^ 2 := by
    apply abs_le.mpr
    constructor
    · nlinarith [sq_nonneg (a + 1 / 2)]
    · nlinarith [sq_nonneg (a - 1 / 2)]
  have hratio : |a / ((1 + a ^ 2) * autocorr f 0)| ≤ 1 / autocorr f 0 := by
    rw [abs_div, abs_of_pos hden]
    calc
      _ ≤ (1 + a ^ 2) / ((1 + a ^ 2) * autocorr f 0) := div_le_div_of_nonneg_right ha hden.le
      _ = _ := by
        have hne : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
        field_simp
  rw [normalizedArchEnergy_subtractCopy_sub hf hfc hR hsupp hT, abs_mul]
  calc
    _ ≤ |a / ((1 + a ^ 2) * autocorr f 0)| *
        (copyTailFactor D T * ∫ x, |autocorr f x|) :=
      mul_le_mul_of_nonneg_left (abs_integral_shifted_autocorr_arch_le hf hfc hsupp hT) (abs_nonneg _)
    _ ≤ 1 / autocorr f 0 * (copyTailFactor D T * ∫ x, |autocorr f x|) :=
      mul_le_mul_of_nonneg_right hratio (mul_nonneg (copyTailFactor_nonneg D T) hM)
    _ = polarEnergyErrorConstant f D * Real.exp (-T / 2) := by
      have he : Real.exp (-(T - D) / 2) = Real.exp (D / 2) * Real.exp (-T / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hd : 0 < 1 - Real.exp (-2) :=
        sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
      unfold copyTailFactor polarEnergyErrorConstant
      rw [he]
      field_simp [hR.ne', hd.ne']

/-- Exact cancellation at any real exponential rate. -/
theorem integral_subtractCopy_cancel_rate {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (β T : ℝ) :
    (∫ u, subtractCopy f (Real.exp (-β * T)) T u * Real.exp (β * u)) = 0 := by
  rw [integral_subtractCopy_mul_exp hf hfc]
  rw [← Real.exp_add, show -β * T + β * T = 0 by ring, Real.exp_zero]
  ring

/-- Cancel one real rate with arbitrarily small energy cost, preserving all existing moment
zeros as well as every normalized correlation value on the requested interval. -/
theorem exists_source_cancel_rate_local_energy_close {f : ℝ → ℝ} {r : WithTop ℕ∞}
    (hr : 2 ≤ r) (hf : ContDiff ℝ r f) (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0)
    (β A : ℝ) (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ r g ∧ HasCompactSupport g ∧ 0 < autocorr g 0 ∧
      (∫ u, g u * Real.exp (β * u)) = 0 ∧
      (∀ s : ℝ, (∫ u, f u * Real.exp (s * u)) = 0 → (∫ u, g u * Real.exp (s * u)) = 0) ∧
      (∀ x, |x| ≤ A → autocorr g x / autocorr g 0 = autocorr f x / autocorr f 0) ∧
      |normalizedArchEnergy g - normalizedArchEnergy f| < ε := by
  obtain ⟨D, _, hsupp⟩ := exists_pos_autocorr_support_radius hfc
  have hf2 : ContDiff ℝ 2 f := hf.of_le hr
  have htend : Tendsto (fun S : ℝ => polarEnergyErrorConstant f D * Real.exp (-S)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (polarEnergyErrorConstant f D)
  obtain ⟨S, hlarge, hsmall⟩ := ((eventually_gt_atTop ((D + max A 1) / 2)).and
    ((tendsto_order.mp htend).2 ε hε)).exists
  let T := 2 * S
  have hTA : D + A < T := by dsimp [T]; linarith [le_max_left A 1]
  have hT1 : D + 1 ≤ T := by dsimp [T]; linarith [le_max_right A 1]
  let a := Real.exp (-β * T)
  refine ⟨subtractCopy f a T, contDiff_subtractCopy hf _ _, hasCompactSupport_subtractCopy hfc _ _,
    ?_, integral_subtractCopy_cancel_rate hf.continuous hfc β T, ?_, ?_, ?_⟩
  · rw [autocorr_subtractCopy_local hf.continuous hfc hsupp hTA (by simpa using hA : |(0 : ℝ)| ≤ A)]
    positivity
  · intro s hs
    rw [integral_subtractCopy_mul_exp hf.continuous hfc, hs, mul_zero]
  · intro x hx
    exact normalized_autocorr_subtractCopy_local hf.continuous hfc hA hsupp hTA hx a
  · have hbound := normalizedArchEnergy_subtractCopy_uniform_error hf2 hfc hR hsupp hT1 a
    have he : -T / 2 = -S := by dsimp [T]; ring
    rw [he] at hbound
    exact hbound.trans_lt hsmall

/-- Simultaneous cancellation of any finite list of real exponential moments while preserving
the local normalized correlation exactly and changing the energy by less than `ε`. -/
theorem exists_source_cancel_rates_local_energy_close (rates : List ℝ) {f : ℝ → ℝ}
    {r : WithTop ℕ∞} (hr : 2 ≤ r) (hf : ContDiff ℝ r f) (hfc : HasCompactSupport f)
    (hR : 0 < autocorr f 0) (A : ℝ) (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ r g ∧ HasCompactSupport g ∧ 0 < autocorr g 0 ∧
      (∀ β ∈ rates, (∫ u, g u * Real.exp (β * u)) = 0) ∧
      (∀ x, |x| ≤ A → autocorr g x / autocorr g 0 = autocorr f x / autocorr f 0) ∧
      |normalizedArchEnergy g - normalizedArchEnergy f| < ε := by
  induction rates generalizing f ε with
  | nil =>
      refine ⟨f, hf, hfc, hR, ?_, ?_, ?_⟩
      · simp
      · intro x _; rfl
      · simpa using hε
  | cons β rates ih =>
      have hh : 0 < ε / 2 := by linarith
      obtain ⟨g, hg, hgc, hRg, hzg, hlocalg, herrorg⟩ := ih hf hfc hR hh
      obtain ⟨k, hk, hkc, hRk, hzk, hpres, hlocalk, herrork⟩ :=
        exists_source_cancel_rate_local_energy_close hr hg hgc hRg β A hA hh
      refine ⟨k, hk, hkc, hRk, ?_, ?_, ?_⟩
      · intro s hs
        rcases List.mem_cons.mp hs with hhead | htail
        · simpa only [hhead] using hzk
        · exact hpres s (hzg s htail)
      · intro x hx
        exact (hlocalk x hx).trans (hlocalg x hx)
      · calc
          _ = |(normalizedArchEnergy k - normalizedArchEnergy g) +
              (normalizedArchEnergy g - normalizedArchEnergy f)| := by congr 1; ring
          _ ≤ |normalizedArchEnergy k - normalizedArchEnergy g| +
              |normalizedArchEnergy g - normalizedArchEnergy f| := abs_add_le _ _
          _ < ε := by linarith

/-- Arbitrary finite exponential moment cancellation leaves the set of valid logarithmic-grid
energy lower bounds unchanged, including at zero and negative rates. -/
theorem finite_moment_log_grid_lower_bound_iff (rates : List ℝ)
    (r : WithTop ℕ∞) (hr : 2 ≤ r) (N : ℕ) (C : ℝ) :
    (∀ (f : ℝ → ℝ), ContDiff ℝ r f → HasCompactSupport f → 0 < autocorr f 0 →
      (∀ n ∈ Finset.Icc 2 N, autocorr f (Real.log (n : ℝ)) = 0) →
      (∀ β ∈ rates, (∫ u, f u * Real.exp (β * u)) = 0) → C ≤ normalizedArchEnergy f) ↔
    (∀ (f : ℝ → ℝ), ContDiff ℝ r f → HasCompactSupport f → 0 < autocorr f 0 →
      (∀ n ∈ Finset.Icc 2 N, autocorr f (Real.log (n : ℝ)) = 0) → C ≤ normalizedArchEnergy f) := by
  constructor
  · intro hmoment f hf hfc hR hgrid
    by_contra hbad
    have hgap : 0 < (C - normalizedArchEnergy f) / 2 := by linarith
    let A := max (Real.log (N : ℝ)) 0
    obtain ⟨g, hg, hgc, hRg, hmg, hlocal, herr⟩ :=
      exists_source_cancel_rates_local_energy_close rates hr hf hfc hR A (le_max_right _ _) hgap
    have hgridg : ∀ n ∈ Finset.Icc 2 N, autocorr g (Real.log (n : ℝ)) = 0 := by
      intro n hn
      have hnrange := Finset.mem_Icc.mp hn
      have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      have hbound : |Real.log (n : ℝ)| ≤ A := by
        rw [abs_of_nonneg hln]
        exact (Real.log_le_log hnp (by exact_mod_cast hnrange.2)).trans (le_max_left _ _)
      have hval := hlocal (Real.log (n : ℝ)) hbound
      rw [hgrid n hn, zero_div] at hval
      exact (div_eq_zero_iff.mp hval).resolve_right hRg.ne'
    have hgC := hmoment g hg hgc hRg hgridg hmg
    have := (le_abs_self (normalizedArchEnergy g - normalizedArchEnergy f)).trans_lt herr
    linarith
  · intro hall f hf hfc hR hgrid _
    exact hall f hf hfc hR hgrid

end

end GaloisForLFunctions.BiScaleUncertainty
