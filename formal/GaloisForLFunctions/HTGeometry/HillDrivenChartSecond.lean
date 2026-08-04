import GaloisForLFunctions.HTGeometry.HillDrivenChart

/-!
# The second-order chart calculus of the driven evolution

Each first partial of the driven chart field is again the chart object of a density family: the time
partial of the velocity density, a spatial partial of the density multiplied by the frequency factor.
Differentiating them once more produces the four second-order objects, and the two mixed ones
coincide.

All the bounds are stated at the weakest weight of the three that occur: since the frequency is at
least one, one weight `⟨ξ⟩⁻ᴷ` with `N = K + 2` dominates every density of the calculus, and `K`
exceeds the dimension exactly when `N` exceeds it by two.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

section Weights

variable {E : Type*} [NormedAddCommGroup E]

theorem kgFreq_pow_mul_inv_pow_le {j K M : ℕ} (h : K + j ≤ M) (ξ : E) :
    kgFreq ξ ^ j * (kgFreq ξ ^ M)⁻¹ ≤ (kgFreq ξ ^ K)⁻¹ := by
  have h1 : (1 : ℝ) ≤ kgFreq ξ := one_le_kgFreq ξ
  have hKpos : (0 : ℝ) < kgFreq ξ ^ K := pow_pos (kgFreq_pos ξ) K
  have hMpos : (0 : ℝ) < kgFreq ξ ^ M := pow_pos (kgFreq_pos ξ) M
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hMpos hKpos]
  calc kgFreq ξ ^ j * kgFreq ξ ^ K = kgFreq ξ ^ (j + K) := by rw [pow_add]
    _ ≤ kgFreq ξ ^ M := pow_le_pow_right₀ h1 (by omega)
    _ = 1 * kgFreq ξ ^ M := by ring

theorem inv_pow_le_inv_pow {K M : ℕ} (h : K ≤ M) (ξ : E) :
    (kgFreq ξ ^ M)⁻¹ ≤ (kgFreq ξ ^ K)⁻¹ := by
  have h0 := kgFreq_pow_mul_inv_pow_le (j := 0) (K := K) (M := M) (by omega) ξ
  simpa using h0

end Weights

section DrivenSecond

variable {d K : ℕ}

/-! ## The bounds at the weakest weight -/

theorem norm_hillDrivenDensitySecond_le_weight (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2))
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) {T t : ℝ} (hT : 0 ≤ T) (ht : |t| ≤ T)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖hillDrivenDensitySecond a b G₀ t ξ‖
      ≤ (kgFreq ξ ^ K)⁻¹ *
        ((a.mass ^ 2 + a.sizeBound ^ 2) * hillFlowSize a b G₀ T + hillSourceSize a b G₀ T) := by
  have hbase := norm_kgChar_mul_hillDrivenDensitySecond_le a b G₀ hT ht 0 ξ
  have hchar : ‖kgChar (0 : EuclideanSpace ℝ (Fin d)) ξ * hillDrivenDensitySecond a b G₀ t ξ‖
      = ‖hillDrivenDensitySecond a b G₀ t ξ‖ := by
    rw [norm_mul, norm_kgChar, one_mul]
  rw [hchar] at hbase
  refine hbase.trans ?_
  have h1 : kgFreq ξ ^ 2 * (kgFreq ξ ^ (K + 2))⁻¹ ≤ (kgFreq ξ ^ K)⁻¹ :=
    kgFreq_pow_mul_inv_pow_le (j := 2) (by omega) ξ
  have h2 : (kgFreq ξ ^ (K + 2))⁻¹ ≤ (kgFreq ξ ^ K)⁻¹ := inv_pow_le_inv_pow (by omega) ξ
  have hA : (0 : ℝ) ≤ (a.mass ^ 2 + a.sizeBound ^ 2) * hillFlowSize a b G₀ T :=
    mul_nonneg (by positivity) (hillFlowSize_nonneg a b G₀ T)
  have hB : (0 : ℝ) ≤ hillSourceSize a b G₀ T := hillSourceSize_nonneg a b G₀ T
  calc kgFreq ξ ^ 2 * (kgFreq ξ ^ (K + 2))⁻¹ *
          ((a.mass ^ 2 + a.sizeBound ^ 2) * hillFlowSize a b G₀ T) +
        (kgFreq ξ ^ (K + 2))⁻¹ * hillSourceSize a b G₀ T
      ≤ (kgFreq ξ ^ K)⁻¹ * ((a.mass ^ 2 + a.sizeBound ^ 2) * hillFlowSize a b G₀ T) +
        (kgFreq ξ ^ K)⁻¹ * hillSourceSize a b G₀ T :=
        add_le_add (mul_le_mul_of_nonneg_right h1 hA) (mul_le_mul_of_nonneg_right h2 hB)
    _ = (kgFreq ξ ^ K)⁻¹ *
        ((a.mass ^ 2 + a.sizeBound ^ 2) * hillFlowSize a b G₀ T + hillSourceSize a b G₀ T) := by
        ring

theorem norm_kgDirDensity_hillDrivenDeriv_le_weight (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2))
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (v : EuclideanSpace ℝ (Fin d)) {T t : ℝ} (hT : 0 ≤ T)
    (ht : |t| ≤ T) (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖kgDirDensity v (hillDrivenDensityDeriv a b G₀ t) ξ‖
      ≤ (kgFreq ξ ^ K)⁻¹ * (2 * Real.pi * ‖v‖ * hillVelocitySize a b G₀ T) := by
  refine (norm_kgDirDensity_le v _ ξ).trans ?_
  have hpiv : (0 : ℝ) ≤ 2 * Real.pi * ‖v‖ := by positivity
  have hstep : kgFreq ξ * ‖hillDrivenDensityDeriv a b G₀ t ξ‖
      ≤ kgFreq ξ * (hillVelocitySize a b G₀ T * (kgFreq ξ ^ (K + 2))⁻¹) :=
    mul_le_mul_of_nonneg_left (norm_hillDrivenDensityDeriv_le_weight a b G₀ hT ht ξ)
      (le_of_lt (kgFreq_pos ξ))
  have hweight : kgFreq ξ ^ 1 * (kgFreq ξ ^ (K + 2))⁻¹ ≤ (kgFreq ξ ^ K)⁻¹ :=
    kgFreq_pow_mul_inv_pow_le (j := 1) (by omega) ξ
  rw [pow_one] at hweight
  have hV : (0 : ℝ) ≤ hillVelocitySize a b G₀ T := by
    have h := norm_hillFlowApplyDeriv_le_window a b G₀ hT ht ξ
    exact le_trans (norm_nonneg _) h
  calc 2 * Real.pi * ‖v‖ * (kgFreq ξ * ‖hillDrivenDensityDeriv a b G₀ t ξ‖)
      ≤ 2 * Real.pi * ‖v‖ * (kgFreq ξ * (hillVelocitySize a b G₀ T * (kgFreq ξ ^ (K + 2))⁻¹)) :=
        mul_le_mul_of_nonneg_left hstep hpiv
    _ = 2 * Real.pi * ‖v‖ * hillVelocitySize a b G₀ T *
          (kgFreq ξ * (kgFreq ξ ^ (K + 2))⁻¹) := by ring
    _ ≤ 2 * Real.pi * ‖v‖ * hillVelocitySize a b G₀ T * (kgFreq ξ ^ K)⁻¹ :=
        mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = (kgFreq ξ ^ K)⁻¹ * (2 * Real.pi * ‖v‖ * hillVelocitySize a b G₀ T) := by ring

theorem norm_kgDirDensity_two_hillDriven_le_weight (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2))
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (v w : EuclideanSpace ℝ (Fin d)) {T t : ℝ} (hT : 0 ≤ T)
    (ht : |t| ≤ T) (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖kgDirDensity w (kgDirDensity v (hillDrivenDensity a b G₀ t)) ξ‖
      ≤ (kgFreq ξ ^ K)⁻¹ *
        (2 * Real.pi * ‖w‖ * (2 * Real.pi * ‖v‖) * hillFlowSize a b G₀ T) := by
  have hpiv : (0 : ℝ) ≤ 2 * Real.pi * ‖v‖ := by positivity
  have hpiw : (0 : ℝ) ≤ 2 * Real.pi * ‖w‖ := by positivity
  have hfreqnn : (0 : ℝ) ≤ kgFreq ξ := le_of_lt (kgFreq_pos ξ)
  have hinner : ‖kgDirDensity v (hillDrivenDensity a b G₀ t) ξ‖
      ≤ 2 * Real.pi * ‖v‖ * (kgFreq ξ * (hillFlowSize a b G₀ T * (kgFreq ξ ^ (K + 2))⁻¹)) :=
    (norm_kgDirDensity_le v _ ξ).trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_hillDrivenDensity_le_weight a b G₀ hT ht ξ) hfreqnn)
        hpiv)
  have hweight : kgFreq ξ ^ 2 * (kgFreq ξ ^ (K + 2))⁻¹ ≤ (kgFreq ξ ^ K)⁻¹ :=
    kgFreq_pow_mul_inv_pow_le (j := 2) (by omega) ξ
  have hS : (0 : ℝ) ≤ hillFlowSize a b G₀ T := hillFlowSize_nonneg a b G₀ T
  calc ‖kgDirDensity w (kgDirDensity v (hillDrivenDensity a b G₀ t)) ξ‖
      ≤ 2 * Real.pi * ‖w‖ * (kgFreq ξ * ‖kgDirDensity v (hillDrivenDensity a b G₀ t) ξ‖) :=
        norm_kgDirDensity_le w _ ξ
    _ ≤ 2 * Real.pi * ‖w‖ *
          (kgFreq ξ * (2 * Real.pi * ‖v‖ *
            (kgFreq ξ * (hillFlowSize a b G₀ T * (kgFreq ξ ^ (K + 2))⁻¹)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hfreqnn) hpiw
    _ = 2 * Real.pi * ‖w‖ * (2 * Real.pi * ‖v‖) * hillFlowSize a b G₀ T *
          (kgFreq ξ ^ 2 * (kgFreq ξ ^ (K + 2))⁻¹) := by ring
    _ ≤ 2 * Real.pi * ‖w‖ * (2 * Real.pi * ‖v‖) * hillFlowSize a b G₀ T *
          (kgFreq ξ ^ K)⁻¹ := mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = (kgFreq ξ ^ K)⁻¹ *
          (2 * Real.pi * ‖w‖ * (2 * Real.pi * ‖v‖) * hillFlowSize a b G₀ T) := by ring

/-! ## Integrability of the first-order densities -/

theorem integrable_hillDrivenDensityDeriv
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2))
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (t : ℝ) :
    Integrable (hillDrivenDensityDeriv a b G₀ t) (volume) := by
  have hT : (0 : ℝ) ≤ |t| := abs_nonneg t
  refine Integrable.mono' ((integrable_kgFreq_inv_pow (E := EuclideanSpace ℝ (Fin d)) hK).mul_const
      (hillVelocitySize a b G₀ |t|))
    (aestronglyMeasurable_hillDrivenDensityDeriv a b G₀ t) ?_
  filter_upwards with ξ
  have hb := norm_hillDrivenDensityDeriv_le_weight a b G₀ hT (le_refl |t|) ξ
  have hweight : (kgFreq ξ ^ (K + 2))⁻¹ ≤ (kgFreq ξ ^ K)⁻¹ := inv_pow_le_inv_pow (by omega) ξ
  have hV : (0 : ℝ) ≤ hillVelocitySize a b G₀ |t| :=
    le_trans (norm_nonneg _) (norm_hillFlowApplyDeriv_le_window a b G₀ hT (le_refl |t|) ξ)
  calc ‖hillDrivenDensityDeriv a b G₀ t ξ‖
      ≤ hillVelocitySize a b G₀ |t| * (kgFreq ξ ^ (K + 2))⁻¹ := hb
    _ ≤ hillVelocitySize a b G₀ |t| * (kgFreq ξ ^ K)⁻¹ :=
        mul_le_mul_of_nonneg_left hweight hV
    _ = (kgFreq ξ ^ K)⁻¹ * hillVelocitySize a b G₀ |t| := by ring

theorem integrable_kgFreq_mul_hillDrivenDensityDeriv
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2))
    (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) (t : ℝ) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin d) =>
      kgFreq ξ * ‖hillDrivenDensityDeriv a b G₀ t ξ‖) (volume) := by
  have hT : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hV : (0 : ℝ) ≤ hillVelocitySize a b G₀ |t| :=
    le_trans (norm_nonneg _)
      (norm_hillFlowApplyDeriv_le_window a b G₀ hT (le_refl |t|) 0)
  refine Integrable.mono' ((integrable_kgFreq_inv_pow (E := EuclideanSpace ℝ (Fin d)) hK).mul_const
      (hillVelocitySize a b G₀ |t|))
    ((continuous_kgFreq.aestronglyMeasurable).mul
      (aestronglyMeasurable_hillDrivenDensityDeriv a b G₀ t).norm) ?_
  filter_upwards with ξ
  have hb := norm_hillDrivenDensityDeriv_le_weight a b G₀ hT (le_refl |t|) ξ
  have hweight : kgFreq ξ ^ 1 * (kgFreq ξ ^ (K + 2))⁻¹ ≤ (kgFreq ξ ^ K)⁻¹ :=
    kgFreq_pow_mul_inv_pow_le (j := 1) (by omega) ξ
  rw [pow_one] at hweight
  have hnn : (0 : ℝ) ≤ kgFreq ξ * ‖hillDrivenDensityDeriv a b G₀ t ξ‖ :=
    mul_nonneg (le_of_lt (kgFreq_pos ξ)) (norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc kgFreq ξ * ‖hillDrivenDensityDeriv a b G₀ t ξ‖
      ≤ kgFreq ξ * (hillVelocitySize a b G₀ |t| * (kgFreq ξ ^ (K + 2))⁻¹) :=
        mul_le_mul_of_nonneg_left hb (le_of_lt (kgFreq_pos ξ))
    _ = hillVelocitySize a b G₀ |t| * (kgFreq ξ * (kgFreq ξ ^ (K + 2))⁻¹) := by ring
    _ ≤ hillVelocitySize a b G₀ |t| * (kgFreq ξ ^ K)⁻¹ :=
        mul_le_mul_of_nonneg_left hweight hV
    _ = (kgFreq ξ ^ K)⁻¹ * hillVelocitySize a b G₀ |t| := by ring


/-! ## The second-order families -/

/-- The partials of the time partial. -/
noncomputable def hillDrivenChartTimeSecond (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (k : Fin (d + 1)) : (Fin (d + 1) → ℝ) → ℝ :=
  Fin.cases (kgChartOf (hillDrivenDensitySecond a b G₀))
    (fun i => kgChartOf (fun t => kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
      (hillDrivenDensityDeriv a b G₀ t))) k

/-- The partials of the `i`-th spatial partial. -/
noncomputable def hillDrivenChartSpaceSecond (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (i : Fin d) (k : Fin (d + 1)) : (Fin (d + 1) → ℝ) → ℝ :=
  Fin.cases (kgChartOf (fun t => kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
      (hillDrivenDensityDeriv a b G₀ t)))
    (fun j => kgChartOf (fun t => kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d j)
      (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (hillDrivenDensity a b G₀ t)))) k

theorem hillDrivenChartTimeSecond_zero (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) :
    hillDrivenChartTimeSecond a b G₀ 0 = kgChartOf (hillDrivenDensitySecond a b G₀) := rfl

theorem hillDrivenChartTimeSecond_succ (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (i : Fin d) :
    hillDrivenChartTimeSecond a b G₀ i.succ
      = kgChartOf (fun t => kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
        (hillDrivenDensityDeriv a b G₀ t)) := by
  rw [hillDrivenChartTimeSecond, Fin.cases_succ]

theorem hillDrivenChartSpaceSecond_zero (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (i : Fin d) :
    hillDrivenChartSpaceSecond a b G₀ i 0
      = kgChartOf (fun t => kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
        (hillDrivenDensityDeriv a b G₀ t)) := rfl

theorem hillDrivenChartSpaceSecond_succ (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (i j : Fin d) :
    hillDrivenChartSpaceSecond a b G₀ i j.succ
      = kgChartOf (fun t => kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d j)
        (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (hillDrivenDensity a b G₀ t))) := by
  rw [hillDrivenChartSpaceSecond, Fin.cases_succ]

/-! ## Integrability of the derived densities -/

theorem integrable_kgDirDensity_hillDriven
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Integrable (kgDirDensity v (hillDrivenDensity a b G₀ t)) (volume) := by
  have hdim1 : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 1 < (K + 2 : ℕ) := by
    push_cast
    linarith
  exact integrable_kgDirDensity (continuous_hillDrivenDensity a b G₀ t).aestronglyMeasurable
    (integrable_kgFreq_mul_hillDrivenDensity hdim1 a b G₀ t) v

theorem integrable_kgFreq_mul_kgDirDensity_hillDriven
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin d) =>
      kgFreq ξ * ‖kgDirDensity v (hillDrivenDensity a b G₀ t) ξ‖) (volume) := by
  have hdim2 : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + (2 : ℕ) < (K + 2 : ℕ) := by
    push_cast
    linarith
  have h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) =>
      kgFreq ξ ^ 2 * ‖hillDrivenDensity a b G₀ t ξ‖) (volume) :=
    integrable_kgFreq_pow_mul_kgWeighted' (E := EuclideanSpace ℝ (Fin d)) (j := 2) hdim2
      (hillPotentialFlow a b G₀ t)
  exact integrable_kgFreq_mul_kgDirDensity h2 v
    (continuous_hillDrivenDensity a b G₀ t).aestronglyMeasurable

/-! ## The derivatives of the first partials -/

theorem hasDerivAt_kgDirDensity_hillDriven (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (v : EuclideanSpace ℝ (Fin d)) (t : ℝ) (ξ : EuclideanSpace ℝ (Fin d)) :
    HasDerivAt (fun r : ℝ => kgDirDensity v (hillDrivenDensity a b G₀ r) ξ)
      (kgDirDensity v (hillDrivenDensityDeriv a b G₀ t) ξ) t := by
  have hbase := (hasDerivAt_hillDrivenDensity a b G₀ ξ t).const_mul
    (2 * Real.pi * Complex.I * ((inner ℝ ξ v : ℝ) : ℂ))
  exact hbase

theorem hasDerivAt_hillDrivenChartTimePartial_zero
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (y : Fin (d + 1) → ℝ) :
    HasDerivAt (fun r : ℝ => hillDrivenChartTimePartial a b G₀ (Function.update y 0 r))
      (hillDrivenChartTimeSecond a b G₀ 0 y) (y 0) := by
  rw [hillDrivenChartTimeSecond_zero, hillDrivenChartTimePartial]
  refine hasDerivAt_kgChartOf_zero (N := K) hK
    (fun t => aestronglyMeasurable_hillDrivenDensityDeriv a b G₀ t)
    (fun t => aestronglyMeasurable_hillDrivenDensitySecond a b G₀ t)
    (fun t ξ => hasDerivAt_hillDrivenDensityDeriv a b G₀ ξ t) ?_
    (fun t => integrable_hillDrivenDensityDeriv hK a b G₀ t) y
  intro T
  rcases le_or_gt 0 T with hT | hT
  · exact ⟨(a.mass ^ 2 + a.sizeBound ^ 2) * hillFlowSize a b G₀ T + hillSourceSize a b G₀ T,
      fun r hr ξ => norm_hillDrivenDensitySecond_le_weight a b G₀ hT hr ξ⟩
  · refine ⟨0, fun r hr ξ => ?_⟩
    exact absurd (le_trans (abs_nonneg r) hr) (not_le.mpr hT)

theorem hasDerivAt_hillDrivenChartTimePartial_succ
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (y : Fin (d + 1) → ℝ) (i : Fin d) :
    HasDerivAt (fun r : ℝ => hillDrivenChartTimePartial a b G₀ (Function.update y i.succ r))
      (hillDrivenChartTimeSecond a b G₀ i.succ y) (y i.succ) := by
  rw [hillDrivenChartTimeSecond_succ, hillDrivenChartTimePartial]
  exact hasDerivAt_kgChartOf_succ
    (fun t => aestronglyMeasurable_hillDrivenDensityDeriv a b G₀ t)
    (fun t => integrable_hillDrivenDensityDeriv hK a b G₀ t)
    (fun t => integrable_kgFreq_mul_hillDrivenDensityDeriv hK a b G₀ t) y i

theorem hasDerivAt_hillDrivenChartSpacePartial_zero
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (y : Fin (d + 1) → ℝ) (i : Fin d) :
    HasDerivAt (fun r : ℝ => hillDrivenChartSpacePartial a b G₀ i (Function.update y 0 r))
      (hillDrivenChartSpaceSecond a b G₀ i 0 y) (y 0) := by
  rw [hillDrivenChartSpaceSecond_zero, hillDrivenChartSpacePartial]
  refine hasDerivAt_kgChartOf_zero (N := K) hK
    (fun t => aestronglyMeasurable_kgDirDensity
      (continuous_hillDrivenDensity a b G₀ t).aestronglyMeasurable _)
    (fun t => aestronglyMeasurable_kgDirDensity
      (aestronglyMeasurable_hillDrivenDensityDeriv a b G₀ t) _)
    (fun t ξ => hasDerivAt_kgDirDensity_hillDriven a b G₀ _ t ξ) ?_
    (fun t => integrable_kgDirDensity_hillDriven hK a b G₀ _ t) y
  intro T
  rcases le_or_gt 0 T with hT | hT
  · exact ⟨2 * Real.pi * ‖((2 * Real.pi)⁻¹ • kgDir d i : EuclideanSpace ℝ (Fin d))‖ *
      hillVelocitySize a b G₀ T,
      fun r hr ξ => norm_kgDirDensity_hillDrivenDeriv_le_weight a b G₀ _ hT hr ξ⟩
  · refine ⟨0, fun r hr ξ => ?_⟩
    exact absurd (le_trans (abs_nonneg r) hr) (not_le.mpr hT)

theorem hasDerivAt_hillDrivenChartSpacePartial_succ
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (y : Fin (d + 1) → ℝ) (i j : Fin d) :
    HasDerivAt (fun r : ℝ => hillDrivenChartSpacePartial a b G₀ i (Function.update y j.succ r))
      (hillDrivenChartSpaceSecond a b G₀ i j.succ y) (y j.succ) := by
  rw [hillDrivenChartSpaceSecond_succ, hillDrivenChartSpacePartial]
  exact hasDerivAt_kgChartOf_succ
    (fun t => aestronglyMeasurable_kgDirDensity
      (continuous_hillDrivenDensity a b G₀ t).aestronglyMeasurable _)
    (fun t => integrable_kgDirDensity_hillDriven hK a b G₀ _ t)
    (fun t => integrable_kgFreq_mul_kgDirDensity_hillDriven hK a b G₀ _ t) y j

/-! ## Continuity of the second-order families -/

theorem continuous_hillDrivenChartTimeSecond
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (k : Fin (d + 1)) : Continuous (hillDrivenChartTimeSecond a b G₀ k) := by
  refine Fin.cases ?_ ?_ k
  · rw [hillDrivenChartTimeSecond_zero]
    refine continuous_kgChartOf_of_bound
      (fun r => aestronglyMeasurable_hillDrivenDensitySecond a b G₀ r)
      (fun ξ => continuous_hillDrivenDensitySecond_time a b G₀ ξ) ?_
      (integrable_kgFreq_inv_pow (E := EuclideanSpace ℝ (Fin d)) hK)
    intro T
    rcases le_or_gt 0 T with hT | hT
    · refine ⟨(a.mass ^ 2 + a.sizeBound ^ 2) * hillFlowSize a b G₀ T + hillSourceSize a b G₀ T,
        fun r hr ξ => ?_⟩
      have h := norm_hillDrivenDensitySecond_le_weight a b G₀ hT hr ξ
      calc ‖hillDrivenDensitySecond a b G₀ r ξ‖
          ≤ (kgFreq ξ ^ K)⁻¹ * ((a.mass ^ 2 + a.sizeBound ^ 2) * hillFlowSize a b G₀ T +
            hillSourceSize a b G₀ T) := h
        _ = ((a.mass ^ 2 + a.sizeBound ^ 2) * hillFlowSize a b G₀ T +
            hillSourceSize a b G₀ T) * (kgFreq ξ ^ K)⁻¹ := by ring
    · refine ⟨0, fun r hr ξ => ?_⟩
      exact absurd (le_trans (abs_nonneg r) hr) (not_le.mpr hT)
  · intro i
    rw [hillDrivenChartTimeSecond_succ]
    refine continuous_kgChartOf_of_bound
      (fun r => aestronglyMeasurable_kgDirDensity
        (aestronglyMeasurable_hillDrivenDensityDeriv a b G₀ r) _)
      (fun ξ => continuous_kgDirDensity_time _ ξ
        (continuous_hillDrivenDensityDeriv_time a b G₀ ξ)) ?_
      (integrable_kgFreq_inv_pow (E := EuclideanSpace ℝ (Fin d)) hK)
    intro T
    rcases le_or_gt 0 T with hT | hT
    · refine ⟨2 * Real.pi * ‖((2 * Real.pi)⁻¹ • kgDir d i : EuclideanSpace ℝ (Fin d))‖ *
        hillVelocitySize a b G₀ T, fun r hr ξ => ?_⟩
      have h := norm_kgDirDensity_hillDrivenDeriv_le_weight a b G₀
        ((2 * Real.pi)⁻¹ • kgDir d i) hT hr ξ
      calc ‖kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (hillDrivenDensityDeriv a b G₀ r) ξ‖
          ≤ (kgFreq ξ ^ K)⁻¹ * (2 * Real.pi *
            ‖((2 * Real.pi)⁻¹ • kgDir d i : EuclideanSpace ℝ (Fin d))‖ *
              hillVelocitySize a b G₀ T) := h
        _ = 2 * Real.pi * ‖((2 * Real.pi)⁻¹ • kgDir d i : EuclideanSpace ℝ (Fin d))‖ *
              hillVelocitySize a b G₀ T * (kgFreq ξ ^ K)⁻¹ := by ring
    · refine ⟨0, fun r hr ξ => ?_⟩
      exact absurd (le_trans (abs_nonneg r) hr) (not_le.mpr hT)

theorem continuous_hillDrivenChartSpaceSecond
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (i : Fin d) (k : Fin (d + 1)) : Continuous (hillDrivenChartSpaceSecond a b G₀ i k) := by
  refine Fin.cases ?_ ?_ k
  · rw [hillDrivenChartSpaceSecond_zero]
    refine continuous_kgChartOf_of_bound
      (fun r => aestronglyMeasurable_kgDirDensity
        (aestronglyMeasurable_hillDrivenDensityDeriv a b G₀ r) _)
      (fun ξ => continuous_kgDirDensity_time _ ξ
        (continuous_hillDrivenDensityDeriv_time a b G₀ ξ)) ?_
      (integrable_kgFreq_inv_pow (E := EuclideanSpace ℝ (Fin d)) hK)
    intro T
    rcases le_or_gt 0 T with hT | hT
    · refine ⟨2 * Real.pi * ‖((2 * Real.pi)⁻¹ • kgDir d i : EuclideanSpace ℝ (Fin d))‖ *
        hillVelocitySize a b G₀ T, fun r hr ξ => ?_⟩
      have h := norm_kgDirDensity_hillDrivenDeriv_le_weight a b G₀
        ((2 * Real.pi)⁻¹ • kgDir d i) hT hr ξ
      calc ‖kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (hillDrivenDensityDeriv a b G₀ r) ξ‖
          ≤ (kgFreq ξ ^ K)⁻¹ * (2 * Real.pi *
            ‖((2 * Real.pi)⁻¹ • kgDir d i : EuclideanSpace ℝ (Fin d))‖ *
              hillVelocitySize a b G₀ T) := h
        _ = 2 * Real.pi * ‖((2 * Real.pi)⁻¹ • kgDir d i : EuclideanSpace ℝ (Fin d))‖ *
              hillVelocitySize a b G₀ T * (kgFreq ξ ^ K)⁻¹ := by ring
    · refine ⟨0, fun r hr ξ => ?_⟩
      exact absurd (le_trans (abs_nonneg r) hr) (not_le.mpr hT)
  · intro j
    rw [hillDrivenChartSpaceSecond_succ]
    refine continuous_kgChartOf_of_bound
      (fun r => aestronglyMeasurable_kgDirDensity (aestronglyMeasurable_kgDirDensity
        (continuous_hillDrivenDensity a b G₀ r).aestronglyMeasurable _) _)
      (fun ξ => continuous_kgDirDensity_time _ ξ
        (continuous_kgDirDensity_time _ ξ (continuous_hillDrivenDensity_time a b G₀ ξ))) ?_
      (integrable_kgFreq_inv_pow (E := EuclideanSpace ℝ (Fin d)) hK)
    intro T
    rcases le_or_gt 0 T with hT | hT
    · refine ⟨2 * Real.pi * ‖((2 * Real.pi)⁻¹ • kgDir d j : EuclideanSpace ℝ (Fin d))‖ *
        (2 * Real.pi * ‖((2 * Real.pi)⁻¹ • kgDir d i : EuclideanSpace ℝ (Fin d))‖) *
        hillFlowSize a b G₀ T, fun r hr ξ => ?_⟩
      have h := norm_kgDirDensity_two_hillDriven_le_weight a b G₀
        ((2 * Real.pi)⁻¹ • kgDir d i) ((2 * Real.pi)⁻¹ • kgDir d j) hT hr ξ
      calc ‖kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d j)
            (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (hillDrivenDensity a b G₀ r)) ξ‖
          ≤ (kgFreq ξ ^ K)⁻¹ * (2 * Real.pi *
            ‖((2 * Real.pi)⁻¹ • kgDir d j : EuclideanSpace ℝ (Fin d))‖ *
              (2 * Real.pi * ‖((2 * Real.pi)⁻¹ • kgDir d i : EuclideanSpace ℝ (Fin d))‖) *
                hillFlowSize a b G₀ T) := h
        _ = 2 * Real.pi * ‖((2 * Real.pi)⁻¹ • kgDir d j : EuclideanSpace ℝ (Fin d))‖ *
              (2 * Real.pi * ‖((2 * Real.pi)⁻¹ • kgDir d i : EuclideanSpace ℝ (Fin d))‖) *
                hillFlowSize a b G₀ T * (kgFreq ξ ^ K)⁻¹ := by ring
    · refine ⟨0, fun r hr ξ => ?_⟩
      exact absurd (le_trans (abs_nonneg r) hr) (not_le.mpr hT)

/-! ## The first partials are differentiable -/

theorem isC1OnPi_hillDrivenChartTimePartial
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ) :
    IsC1OnPi (hillDrivenChartTimePartial a b G₀) (hillDrivenChartTimeSecond a b G₀) Set.univ where
  isOpen := isOpen_univ
  hasDeriv := by
    intro y _ k
    refine Fin.cases ?_ ?_ k
    · exact hasDerivAt_hillDrivenChartTimePartial_zero hK a b G₀ y
    · intro i
      exact hasDerivAt_hillDrivenChartTimePartial_succ hK a b G₀ y i
  cont := fun k => continuous_hillDrivenChartTimeSecond hK a b G₀ k

theorem isC1OnPi_hillDrivenChartSpacePartial
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (i : Fin d) :
    IsC1OnPi (hillDrivenChartSpacePartial a b G₀ i) (hillDrivenChartSpaceSecond a b G₀ i)
      Set.univ where
  isOpen := isOpen_univ
  hasDeriv := by
    intro y _ k
    refine Fin.cases ?_ ?_ k
    · exact hasDerivAt_hillDrivenChartSpacePartial_zero hK a b G₀ y i
    · intro j
      exact hasDerivAt_hillDrivenChartSpacePartial_succ hK a b G₀ y i j
  cont := fun k => continuous_hillDrivenChartSpaceSecond hK a b G₀ i k

/-- **Every first partial of the driven chart field is differentiable.** -/
theorem differentiableAt_hillDrivenChartPartial
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (j : Fin (d + 1)) (y : Fin (d + 1) → ℝ) :
    DifferentiableAt ℝ (hillDrivenChartPartial a b G₀ j) y := by
  refine Fin.cases ?_ ?_ j
  · rw [hillDrivenChartPartial_zero]
    exact (hasFDerivAt_of_isC1OnPi (d + 1) (hillDrivenChartTimePartial a b G₀)
      (hillDrivenChartTimeSecond a b G₀) Set.univ
      (isC1OnPi_hillDrivenChartTimePartial hK a b G₀) y (Set.mem_univ y)).differentiableAt
  · intro i
    rw [hillDrivenChartPartial_succ]
    exact (hasFDerivAt_of_isC1OnPi (d + 1) (hillDrivenChartSpacePartial a b G₀ i)
      (hillDrivenChartSpaceSecond a b G₀ i) Set.univ
      (isC1OnPi_hillDrivenChartSpacePartial hK a b G₀ i) y (Set.mem_univ y)).differentiableAt

/-- **Hence every coordinate partial of the driven chart field is differentiable** — the hypothesis
of the divergence-form d'Alembertian. -/
theorem differentiableAt_coordPartial_hillDrivenChartField
    (hK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) (K + 2)) (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)
    (j : Fin (d + 1)) (y : Fin (d + 1) → ℝ) :
    DifferentiableAt ℝ (coordPartial j (hillDrivenChartField a b G₀)) y := by
  have hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 1 < (K + 2 : ℕ) := by
    push_cast
    linarith
  have hfun : coordPartial j (hillDrivenChartField a b G₀) = hillDrivenChartPartial a b G₀ j := by
    funext z
    exact coordPartial_hillDrivenChartField hN a b G₀ j z
  rw [hfun]
  exact differentiableAt_hillDrivenChartPartial hK a b G₀ j y

end DrivenSecond

end GaloisForLFunctions.HTGeometry
