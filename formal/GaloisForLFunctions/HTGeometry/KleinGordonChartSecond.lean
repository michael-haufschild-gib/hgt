import GaloisForLFunctions.HTGeometry.KleinGordonChartFamilies

/-!
# The second-order chart calculus

Each first partial of the chart field is again a chart object of a density family, so the generic
chart lemmas apply to it and produce its own partials. Those are the four second-order objects: the
second time derivative, the two mixed derivatives — which coincide, the derivation in time and the
multiplication by the frequency commuting — and the mixed spatial derivatives.

With them the first partials are differentiable, which is what the corpus's divergence-form
d'Alembertian asks for.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {d N : ℕ} (a : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
  (G₀ : EuclideanSpace ℝ (Fin d) →ᵇ ℂ)

/-! ## The first partials as chart objects -/

theorem kgChartTimePartial_eq_chartOf
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) :
    kgChartTimePartial a G₀ = kgChartOf (kgFlowDensityDeriv a G₀) := by
  funext y
  exact kgChartTimePartial_eq a G₀ hN y

theorem kgChartSpacePartial_eq_chartOf
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (i : Fin d) :
    kgChartSpacePartial a G₀ i
      = kgChartOf (fun t => kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
        (kgFlowDensity a G₀ t)) := by
  funext y
  exact kgChartSpacePartial_eq a G₀ hN i y

/-! ## The second-order partial families -/

/-- The partials of the time partial. -/
noncomputable def kgChartTimeSecond (k : Fin (d + 1)) : (Fin (d + 1) → ℝ) → ℝ :=
  Fin.cases (kgChartOf (kgFlowDensityDeriv2 a G₀))
    (fun i => kgChartOf (fun t => kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
      (kgFlowDensityDeriv a G₀ t))) k

/-- The partials of the `i`-th spatial partial. -/
noncomputable def kgChartSpaceSecond (i : Fin d) (k : Fin (d + 1)) : (Fin (d + 1) → ℝ) → ℝ :=
  Fin.cases (kgChartOf (fun t => kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i)
      (kgFlowDensityDeriv a G₀ t)))
    (fun j => kgChartOf (fun t => kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d j)
      (kgDirDensity ((2 * Real.pi)⁻¹ • kgDir d i) (kgFlowDensity a G₀ t)))) k

/-! ## The derivatives of the first partials -/

theorem hasDerivAt_kgChartTimePartial_zero
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (y : Fin (d + 1) → ℝ) :
    HasDerivAt (fun r : ℝ => kgChartTimePartial a G₀ (Function.update y 0 r))
      (kgChartTimeSecond a G₀ 0 y) (y 0) := by
  have hdimN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < N := by linarith
  have hN2 : 2 ≤ N := by
    have h0 : (0 : ℝ) ≤ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) := Nat.cast_nonneg _
    have h2 : (2 : ℝ) < N := by linarith
    exact_mod_cast h2.le
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, N = K + 2 := ⟨N - 2, by omega⟩
  have hdimK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K := by
    push_cast at hN
    linarith
  rw [kgChartTimePartial_eq_chartOf a G₀ hN]
  exact hasDerivAt_kgChartOf_zero (N := K) hdimK
    (fun t => (continuous_kgFlowDensityDeriv_freq a G₀ t).aestronglyMeasurable)
    (fun t => (continuous_kgFlowDensityDeriv2 a G₀ t).aestronglyMeasurable)
    (fun t ξ => hasDerivAt_kgFlowDensityDeriv a G₀ ξ t)
    (fun T => ⟨kgFlowSize a G₀ T + kgFlowBoundConst a * kgFlowSize a G₀ T,
      fun t ht ξ => norm_kgFlowDensityDeriv2_le_weight a G₀ rfl ht ξ⟩)
    (fun t => integrable_kgFlowDensityDeriv a G₀ hdimN t) y

theorem hasDerivAt_kgChartTimePartial_succ
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (y : Fin (d + 1) → ℝ)
    (i : Fin d) :
    HasDerivAt (fun r : ℝ => kgChartTimePartial a G₀ (Function.update y i.succ r))
      (kgChartTimeSecond a G₀ i.succ y) (y i.succ) := by
  have hdimN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < N := by linarith
  have hdim1 : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 1 < N := by linarith
  rw [kgChartTimePartial_eq_chartOf a G₀ hN, kgChartTimeSecond, Fin.cases_succ]
  exact hasDerivAt_kgChartOf_succ
    (fun t => (continuous_kgFlowDensityDeriv_freq a G₀ t).aestronglyMeasurable)
    (fun t => integrable_kgFlowDensityDeriv a G₀ hdimN t)
    (fun t => integrable_kgFreq_mul_kgFlowDensityDeriv a G₀ hdim1 t) y i

theorem hasDerivAt_kgChartSpacePartial_zero
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (y : Fin (d + 1) → ℝ)
    (i : Fin d) :
    HasDerivAt (fun r : ℝ => kgChartSpacePartial a G₀ i (Function.update y 0 r))
      (kgChartSpaceSecond a G₀ i 0 y) (y 0) := by
  have hN2 : 2 ≤ N := by
    have h0 : (0 : ℝ) ≤ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) := Nat.cast_nonneg _
    have h2 : (2 : ℝ) < N := by linarith
    exact_mod_cast h2.le
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, N = K + 2 := ⟨N - 2, by omega⟩
  have hdimK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K := by
    push_cast at hN
    linarith
  have hdimK1 : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < (K + 1 : ℕ) := by
    push_cast
    linarith
  set v : EuclideanSpace ℝ (Fin d) := (2 * Real.pi)⁻¹ • kgDir d i with hv
  rw [kgChartSpacePartial_eq_chartOf a G₀ hN]
  refine hasDerivAt_kgChartOf_zero (N := K + 1) hdimK1
    (fun t => aestronglyMeasurable_kgDirDensity
      (continuous_kgFlowDensity a G₀ t).aestronglyMeasurable v)
    (fun t => aestronglyMeasurable_kgDirDensity
      (continuous_kgFlowDensityDeriv_freq a G₀ t).aestronglyMeasurable v)
    (fun t ξ => ?_) (fun T => ⟨2 * Real.pi * ‖v‖
      * (‖G₀‖ + 2 * (kgFlowBoundConst a * kgFlowSize a G₀ T * T)), fun t ht ξ => ?_⟩)
    (fun t => integrable_of_weight_bound (N := K + 1) hdimK1
      (aestronglyMeasurable_kgDirDensity
        (continuous_kgFlowDensity a G₀ t).aestronglyMeasurable v)
      (fun ξ => norm_kgDirDensity_le_weight (N := K + 1) v
        (fun ζ => norm_kgFlowDensity_le_weight a G₀ (le_refl |t|) ζ) ξ)) y
  · show HasDerivAt (fun r : ℝ => 2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ)
        * kgFlowDensity a G₀ r ξ)
      (2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ) * kgFlowDensityDeriv a G₀ t ξ) t
    exact (hasDerivAt_kgFlowDensity a G₀ ξ t).const_mul _
  · exact norm_kgDirDensity_le_weight (N := K + 1) v
      (fun ζ => norm_kgFlowDensityDeriv_le_weight a G₀ ht ζ) ξ

theorem hasDerivAt_kgChartSpacePartial_succ
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (y : Fin (d + 1) → ℝ)
    (i j : Fin d) :
    HasDerivAt (fun r : ℝ => kgChartSpacePartial a G₀ i (Function.update y j.succ r))
      (kgChartSpaceSecond a G₀ i j.succ y) (y j.succ) := by
  have hN2 : 2 ≤ N := by
    have h0 : (0 : ℝ) ≤ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) := Nat.cast_nonneg _
    have h2 : (2 : ℝ) < N := by linarith
    exact_mod_cast h2.le
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, N = K + 2 := ⟨N - 2, by omega⟩
  have hdimK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K := by
    push_cast at hN
    linarith
  have hdimK1 : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < (K + 1 : ℕ) := by
    push_cast
    linarith
  have hdimK1' : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 1 < (K + 1 : ℕ) := by
    push_cast
    linarith
  set v : EuclideanSpace ℝ (Fin d) := (2 * Real.pi)⁻¹ • kgDir d i with hv
  rw [kgChartSpacePartial_eq_chartOf a G₀ hN, kgChartSpaceSecond, Fin.cases_succ]
  exact hasDerivAt_kgChartOf_succ
    (fun t => aestronglyMeasurable_kgDirDensity
      (continuous_kgFlowDensity a G₀ t).aestronglyMeasurable v)
    (fun t => integrable_of_weight_bound (N := K + 1) hdimK1
      (aestronglyMeasurable_kgDirDensity
        (continuous_kgFlowDensity a G₀ t).aestronglyMeasurable v)
      (fun ξ => norm_kgDirDensity_le_weight (N := K + 1) v
        (fun ζ => norm_kgFlowDensity_le_weight a G₀ (le_refl |t|) ζ) ξ))
    (fun t => integrable_kgFreq_mul_of_weight_bound (N := K + 1) hdimK1'
      (aestronglyMeasurable_kgDirDensity
        (continuous_kgFlowDensity a G₀ t).aestronglyMeasurable v)
      (fun ξ => norm_kgDirDensity_le_weight (N := K + 1) v
        (fun ζ => norm_kgFlowDensity_le_weight a G₀ (le_refl |t|) ζ) ξ)) y j

/-! ## Continuity of the second-order partials -/

theorem continuous_kgChartTimeSecond
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (k : Fin (d + 1)) :
    Continuous (kgChartTimeSecond a G₀ k) := by
  have hN2 : 2 ≤ N := by
    have h0 : (0 : ℝ) ≤ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) := Nat.cast_nonneg _
    have h2 : (2 : ℝ) < N := by linarith
    exact_mod_cast h2.le
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, N = K + 2 := ⟨N - 2, by omega⟩
  have hdimK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K := by
    push_cast at hN
    linarith
  have hdimK1 : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < (K + 1 : ℕ) := by
    push_cast
    linarith
  refine Fin.cases ?_ ?_ k
  · rw [kgChartTimeSecond]
    exact continuous_kgChartOf (N := K) hdimK
      (fun t => continuous_kgFlowDensityDeriv2 a G₀ t)
      (fun ξ => continuous_kgFlowDensityDeriv2_time a G₀ ξ)
      (fun T => ⟨kgFlowSize a G₀ T + kgFlowBoundConst a * kgFlowSize a G₀ T,
        fun t ht ξ => norm_kgFlowDensityDeriv2_le_weight a G₀ rfl ht ξ⟩)
  · intro i
    rw [kgChartTimeSecond, Fin.cases_succ]
    refine continuous_kgChartOf (N := K + 1) hdimK1
      (fun t => continuous_kgDirDensity (continuous_kgFlowDensityDeriv_freq a G₀ t) _)
      (fun ξ => continuous_kgDirDensity_time _ ξ (continuous_kgFlowDensityDeriv_time a G₀ ξ))
      (fun T => ⟨2 * Real.pi * ‖(2 * Real.pi)⁻¹ • kgDir d i‖
        * (‖G₀‖ + 2 * (kgFlowBoundConst a * kgFlowSize a G₀ T * T)), fun t ht ξ => ?_⟩)
    exact norm_kgDirDensity_le_weight (N := K + 1) _
      (fun ζ => norm_kgFlowDensityDeriv_le_weight a G₀ ht ζ) ξ

theorem continuous_kgChartSpaceSecond
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (i : Fin d)
    (k : Fin (d + 1)) : Continuous (kgChartSpaceSecond a G₀ i k) := by
  have hN2 : 2 ≤ N := by
    have h0 : (0 : ℝ) ≤ (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) := Nat.cast_nonneg _
    have h2 : (2 : ℝ) < N := by linarith
    exact_mod_cast h2.le
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, N = K + 2 := ⟨N - 2, by omega⟩
  have hdimK : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < K := by
    push_cast at hN
    linarith
  have hdimK1 : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < (K + 1 : ℕ) := by
    push_cast
    linarith
  refine Fin.cases ?_ ?_ k
  · rw [kgChartSpaceSecond]
    refine continuous_kgChartOf (N := K + 1) hdimK1
      (fun t => continuous_kgDirDensity (continuous_kgFlowDensityDeriv_freq a G₀ t) _)
      (fun ξ => continuous_kgDirDensity_time _ ξ (continuous_kgFlowDensityDeriv_time a G₀ ξ))
      (fun T => ⟨2 * Real.pi * ‖(2 * Real.pi)⁻¹ • kgDir d i‖
        * (‖G₀‖ + 2 * (kgFlowBoundConst a * kgFlowSize a G₀ T * T)), fun t ht ξ => ?_⟩)
    exact norm_kgDirDensity_le_weight (N := K + 1) _
      (fun ζ => norm_kgFlowDensityDeriv_le_weight a G₀ ht ζ) ξ
  · intro j
    rw [kgChartSpaceSecond, Fin.cases_succ]
    refine continuous_kgChartOf (N := K) hdimK
      (fun t => continuous_kgDirDensity
        (continuous_kgDirDensity (continuous_kgFlowDensity a G₀ t) _) _)
      (fun ξ => continuous_kgDirDensity_time _ ξ
        (continuous_kgDirDensity_time _ ξ (continuous_kgFlowDensity_time a G₀ ξ)))
      (fun T => ⟨2 * Real.pi * ‖(2 * Real.pi)⁻¹ • kgDir d j‖
        * (2 * Real.pi * ‖(2 * Real.pi)⁻¹ • kgDir d i‖ * kgFlowSize a G₀ T),
        fun t ht ξ => ?_⟩)
    refine norm_kgDirDensity_le_weight (N := K) _ (fun ζ => ?_) ξ
    exact norm_kgDirDensity_le_weight (N := K + 1) _
      (fun η => norm_kgFlowDensity_le_weight a G₀ ht η) ζ

/-! ## The first partials are differentiable -/

theorem isC1OnPi_kgChartTimePartial
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) :
    IsC1OnPi (kgChartTimePartial a G₀) (kgChartTimeSecond a G₀) Set.univ where
  isOpen := isOpen_univ
  hasDeriv := by
    intro y _ k
    refine Fin.cases ?_ ?_ k
    · exact hasDerivAt_kgChartTimePartial_zero a G₀ hN y
    · intro i
      exact hasDerivAt_kgChartTimePartial_succ a G₀ hN y i
  cont := fun k => continuous_kgChartTimeSecond a G₀ hN k

theorem isC1OnPi_kgChartSpacePartial
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (i : Fin d) :
    IsC1OnPi (kgChartSpacePartial a G₀ i) (kgChartSpaceSecond a G₀ i) Set.univ where
  isOpen := isOpen_univ
  hasDeriv := by
    intro y _ k
    refine Fin.cases ?_ ?_ k
    · exact hasDerivAt_kgChartSpacePartial_zero a G₀ hN y i
    · intro j
      exact hasDerivAt_kgChartSpacePartial_succ a G₀ hN y i j
  cont := fun k => continuous_kgChartSpaceSecond a G₀ hN i k

/-- **Every first partial of the chart field is differentiable.** -/
theorem differentiableAt_kgChartPartial
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (j : Fin (d + 1))
    (y : Fin (d + 1) → ℝ) : DifferentiableAt ℝ (kgChartPartial a G₀ j) y := by
  refine Fin.cases ?_ ?_ j
  · rw [kgChartPartial_zero]
    exact (hasFDerivAt_of_isC1OnPi (d + 1) (kgChartTimePartial a G₀)
      (kgChartTimeSecond a G₀) Set.univ (isC1OnPi_kgChartTimePartial a G₀ hN) y
      (Set.mem_univ y)).differentiableAt
  · intro i
    rw [kgChartPartial_succ]
    exact (hasFDerivAt_of_isC1OnPi (d + 1) (kgChartSpacePartial a G₀ i)
      (kgChartSpaceSecond a G₀ i) Set.univ (isC1OnPi_kgChartSpacePartial a G₀ hN i) y
      (Set.mem_univ y)).differentiableAt

/-- **Hence every `coordPartial` of the chart field is differentiable** — the hypothesis of the
divergence-form d'Alembertian. -/
theorem differentiableAt_coordPartial_kgChartField
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N) (j : Fin (d + 1))
    (y : Fin (d + 1) → ℝ) :
    DifferentiableAt ℝ (coordPartial j (kgChartField a G₀)) y := by
  have hfun : coordPartial j (kgChartField a G₀) = kgChartPartial a G₀ j := by
    funext z
    exact coordPartial_kgChartField a G₀ hN j z
  rw [hfun]
  exact differentiableAt_kgChartPartial a G₀ hN j y

end GaloisForLFunctions.HTGeometry
