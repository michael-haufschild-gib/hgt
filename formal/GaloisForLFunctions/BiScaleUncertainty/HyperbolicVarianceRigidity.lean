import GaloisForLFunctions.BiScaleUncertainty.LocalFilterLatticeGain

/-!
# Hyperbolic variance rigidity and strict finite-filter gain

A continuous source cannot be supported on a nontrivial hyperbolic level set.
This classifies every zero centered energy and variance, and shows that the
explicit finite-filter gain is strict on exactly the nonzero source domain.
For canonical odd sources, strict plastic improvement is equivalent to failure
of evenness of the original input.
-/

open MeasureTheory Set Filter
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.HyperbolicVarianceRigidity
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicHyperbolicMoment HyperbolicRay SourceLattice SignedCoherentMoment
open CoherentSourceProjection LocalCoherentFilter LocalFilterLatticeGain
noncomputable section

theorem source_energy_eq_zero_iff (f : C_c(ℝ, ℝ)) : autocorr f 0 = 0 ↔ f = 0 := by
  constructor
  · intro h
    rw [← integral_sq_eq_autocorr_zero] at h
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall (fun u => sq_nonneg (f u)))
      (integrable_sq f.continuous f.hasCompactSupport)).mp h
    have he := Measure.eq_of_ae_eq hae (f.continuous.pow 2) continuous_const
    ext u
    exact sq_eq_zero_iff.mp (congrFun he u)
  · intro h
    subst f
    simp [autocorr]

/-- At nonzero scale, no nonzero continuous source is a hyperbolic multiplier eigenvector. -/
theorem centeredSource_eq_zero_iff (f : C_c(ℝ, ℝ)) (α c : ℝ) :
    centeredSource f α c = 0 ↔ f = 0 ∨ (α = 0 ∧ c = 1) := by
  constructor
  · intro hq
    by_cases hf : f = 0
    · exact Or.inl hf
    have hex : ∃ u : ℝ, f u ≠ 0 := by
      by_contra! h
      apply hf
      ext u
      exact h u
    obtain ⟨u, hu⟩ := hex
    have hc (v : ℝ) (hv : f v ≠ 0) : Real.cosh (2 * α * v) = c := by
      have he := congrArg (fun q : C_c(ℝ, ℝ) => q v) hq
      change (Real.cosh (2 * α * v) - c) * f v = 0 at he
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hv)
    by_cases hα : α = 0
    · refine Or.inr ⟨hα, ?_⟩
      simpa only [hα, mul_zero, zero_mul, Real.cosh_zero] using (hc u hu).symm
    · have hlevel (v : ℝ) (hv : f v ≠ 0) : v = u ∨ v = -u := by
        have he : Real.cosh (2 * α * v) = Real.cosh (2 * α * u) := (hc v hv).trans (hc u hu).symm
        have ha : |2 * α * v| = |2 * α * u| :=
          le_antisymm (Real.cosh_le_cosh.mp he.le) (Real.cosh_le_cosh.mp he.symm.le)
        rw [abs_mul (2 * α) v, abs_mul (2 * α) u] at ha
        have hn : |2 * α| ≠ 0 := abs_ne_zero.mpr (mul_ne_zero (by norm_num) hα)
        exact abs_eq_abs.mp (mul_left_cancel₀ hn ha)
      have hae : (f : ℝ → ℝ) =ᵐ[volume] 0 := by
        filter_upwards [volume.ae_ne u, volume.ae_ne (-u)] with v hv hnv
        change f v = 0
        by_contra hfv
        exact (hlevel v hfv).elim hv hnv
      have he := Measure.eq_of_ae_eq hae f.continuous continuous_const
      exact (hf (by ext v; exact congrFun he v)).elim
  · rintro (hf | ⟨hα, hc⟩)
    · subst f
      ext u
      simp [centeredSource]
    · subst α
      subst c
      ext u
      simp [centeredSource]

theorem centered_energy_eq_zero_iff (f : C_c(ℝ, ℝ)) (α c : ℝ) :
    autocorr (centeredSource f α c) 0 = 0 ↔ f = 0 ∨ (α = 0 ∧ c = 1) := by
  rw [source_energy_eq_zero_iff, centeredSource_eq_zero_iff]

/-- Hyperbolic variance degenerates exactly at zero source or zero scale. -/
theorem sourceVariance_eq_zero_iff (f : C_c(ℝ, ℝ)) (α : ℝ) :
    sourceVariance f α = 0 ↔ f = 0 ∨ α = 0 := by
  constructor
  · intro h
    rw [← mean_energy_mul_source_eq_variance, mul_eq_zero] at h
    rcases h with hq | hR
    · rcases (centered_energy_eq_zero_iff f α (sourceMean f α)).mp hq with hf | hα
      · exact Or.inl hf
      · exact Or.inr hα.1
    · exact Or.inl ((source_energy_eq_zero_iff f).mp hR)
  · rintro (hf | hα)
    · have hR := (source_energy_eq_zero_iff f).mpr hf
      rw [← mean_energy_mul_source_eq_variance, hR, mul_zero]
    · subst α
      have hc : coshCompact (2 * 0) f = f := by
        ext u
        change Real.cosh ((2 * 0) * u) * f u = f u
        simp
      unfold sourceVariance coshSquareMass coshMass
      rw [hc]
      simp only [mul_zero, zero_mul, Real.cosh_zero, one_mul]
      rw [integral_sq_eq_autocorr_zero]
      ring

theorem sourceVariance_pos_iff (f : C_c(ℝ, ℝ)) (α : ℝ) :
    0 < sourceVariance f α ↔ f ≠ 0 ∧ α ≠ 0 := by
  constructor
  · intro h
    constructor
    · intro hf
      have hz := (sourceVariance_eq_zero_iff f α).mpr (Or.inl hf)
      linarith only [h, hz]
    · intro hα
      have hz := (sourceVariance_eq_zero_iff f α).mpr (Or.inr hα)
      linarith only [h, hz]
  · rintro ⟨hf, hα⟩
    apply lt_of_le_of_ne (sourceVariance_nonneg f α)
    intro hz
    exact ((sourceVariance_eq_zero_iff f α).mp hz.symm).elim hf hα

/-- The lattice row mass contains the actual positive origin energy. -/
theorem origin_energy_le_correlationMass (f : C_c(ℝ, ℝ)) : autocorr f 0 ≤ correlationMass f := by
  have hs : Summable (fun k : ℤ => |sourceSample f k|) := by
    apply summable_of_hasFiniteSupport
    apply (sourceSample_finite f).subset
    intro k hk
    change |sourceSample f k| ≠ 0 at hk
    change sourceSample f k ≠ 0
    exact fun he => hk (by rw [he, abs_zero])
  have h := hs.le_tsum 0 (fun _ _ => abs_nonneg _)
  simpa only [correlationMass, sourceSample, Int.cast_zero, zero_mul,
    abs_of_nonneg (autocorr_zero_nonneg f)] using h

private theorem centered_zero_energy (α : ℝ) :
    autocorr (centeredSource (0 : C_c(ℝ, ℝ)) α (sourceMean 0 α)) 0 = 0 :=
  (centered_energy_eq_zero_iff _ _ _).mpr (Or.inl rfl)

private theorem gain_zero : latticeGain (0 : C_c(ℝ, ℝ)) = 0 := by
  unfold latticeGain
  rw [centered_zero_energy]
  simp

/-- The constructed finite-filter gain is strictly positive for exactly the nonzero sources. -/
theorem latticeGain_pos_iff (f : C_c(ℝ, ℝ)) : 0 < latticeGain f ↔ f ≠ 0 := by
  constructor
  · intro h hf
    rw [hf, gain_zero] at h
    exact (lt_irrefl 0) h
  · intro hf
    have hR : 0 < autocorr f 0 := by
      apply lt_of_le_of_ne (autocorr_zero_nonneg f)
      intro hz
      exact hf ((source_energy_eq_zero_iff f).mp hz.symm)
    have hΓ : 0 < correlationMass f := hR.trans_le (origin_energy_le_correlationMass f)
    have hQ : 0 < autocorr (centeredSource f (1 / 2) (sourceMean f (1 / 2))) 0 := by
      apply lt_of_le_of_ne (autocorr_zero_nonneg _)
      intro hz
      rcases (centered_energy_eq_zero_iff f (1 / 2) (sourceMean f (1 / 2))).mp hz.symm with h | h
      · exact hf h
      · norm_num at h
    have hD : 0 < projectedEnergy f := by
      have hg := filterEnergy_gap f
      have hH := filterEnergy_nonneg f
      nlinarith only [hg, hH, hΓ]
    have hden : 0 < gainDenominator f :=
      add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (mul_pos hQ hD)) (Real.sqrt_nonneg _)
    exact div_pos (mul_pos (mul_pos (by norm_num) hQ) hΓ) hden

theorem latticeGain_eq_zero_iff (f : C_c(ℝ, ℝ)) : latticeGain f = 0 ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    have hp := (latticeGain_pos_iff f).mpr hf
    linarith only [hp, h]
  · intro hf
    rw [hf, gain_zero]

/-- Strict finite-filter dominance fails only at the zero source. -/
theorem localBudget_lt_projectedBudget_iff (f : C_c(ℝ, ℝ)) :
    localBudget f < projectedBudget f ↔ f ≠ 0 := by
  constructor
  · intro h hf
    subst f
    unfold localBudget projectedBudget at h
    rw [centered_zero_energy] at h
    simp only [zero_mul, Real.sqrt_zero, add_zero] at h
    exact (lt_irrefl _) h
  · intro hf
    have hp := (latticeGain_pos_iff f).mpr hf
    have hg := latticeGain_le_budget_gap f
    linarith only [hp, hg]

theorem odd_source_eq_zero_iff_even (f : C_c(ℝ, ℝ)) :
    oddCompactSource f = 0 ↔ Function.Even (f : ℝ → ℝ) := by
  constructor
  · intro h u
    have he := congrArg (fun q : C_c(ℝ, ℝ) => q u) h
    change (f u - f (-u)) / 2 = 0 at he
    linarith only [he]
  · intro h
    ext u
    change (f u - f (-u)) / 2 = 0
    rw [h u]
    simp

theorem odd_latticeGain_pos_iff_not_even (f : C_c(ℝ, ℝ)) :
    0 < latticeGain (oddCompactSource f) ↔ ¬ Function.Even (f : ℝ → ℝ) := by
  rw [latticeGain_pos_iff, ne_eq, odd_source_eq_zero_iff_even]

theorem odd_latticeGain_eq_zero_iff_even (f : C_c(ℝ, ℝ)) :
    latticeGain (oddCompactSource f) = 0 ↔ Function.Even (f : ℝ → ℝ) := by
  rw [latticeGain_eq_zero_iff, odd_source_eq_zero_iff_even]

/-- The full plastic lower bound improves strictly exactly when the input has a nonzero odd part. -/
theorem odd_plastic_strict_gain_certificate (f : C_c(ℝ, ℝ)) (N : ℕ) :
    let B := (∫ y in (0 : ℝ)..Real.log 2, optimizedCollar (oddCompactSource f) N (-y)) +
      plasticRemainderEnergy (oddCompactSource f) - 2 * Real.log 2 * projectedBudget (oddCompactSource f)
    (B < B + 2 * Real.log 2 * latticeGain (oddCompactSource f) ↔ ¬ Function.Even (f : ℝ → ℝ)) ∧
      B + 2 * Real.log 2 * latticeGain (oddCompactSource f) ≤ plasticCrossover (oddCompactSource f) := by
  dsimp only
  constructor
  · have hd := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    rw [← odd_latticeGain_pos_iff_not_even]
    constructor <;> intro h <;> nlinarith only [h, hd]
  · exact odd_plasticCrossover_ge_latticeGain f N

end
end GaloisForLFunctions.BiScaleUncertainty.HyperbolicVarianceRigidity
