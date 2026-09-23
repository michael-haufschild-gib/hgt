import GaloisForLFunctions.RHTower.Sieve.GallagherAlmostDiagonal

/-!
# Heath--Brown sparse mean value: finite-frequency basic inequality

Explicit finite-frequency form of the elementary sparse mean-value estimate.  Repeated
multiplicative products remain separate indices, so the right side is the literal collision
count used by Heath--Brown rather than a count of distinct products.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset
open scoped FourierTransform

/-- Finite exponential sum with an arbitrary real frequency attached to every index. -/
noncomputable def finiteFrequencyPoly {ι : Type*} (c : ι → ℂ) (s : Finset ι)
    (x : ι → ℝ) (w : ℝ) : ℂ :=
  ∑ i ∈ s, c i * Complex.exp (((2 * Real.pi * (w * x i) : ℝ) : ℂ) * Complex.I)

theorem continuous_finiteFrequencyPoly {ι : Type*} (c : ι → ℂ) (s : Finset ι)
    (x : ι → ℝ) : Continuous (finiteFrequencyPoly c s x) := by
  refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)

private noncomputable def finiteFrequencyTerm {ι : Type*} (c : ι → ℂ) (x : ι → ℝ)
    (δ : ℝ) (i j : ι) (w : ℝ) : ℂ :=
  (c i * (starRingEnd ℂ) (c j))
    * (Complex.exp (((2 * Real.pi * (w * (x i - x j)) : ℝ) : ℂ) * Complex.I)
        * 𝓕 (triC δ) w)

private theorem integrable_finiteFrequencyTerm {ι : Type*} {δ : ℝ} (hδ : 0 < δ)
    (c : ι → ℂ) (x : ι → ℝ) (i j : ι) :
    Integrable (finiteFrequencyTerm c x δ i j) := by
  refine Integrable.const_mul ?_ _
  refine (integrable_fourier_triC hδ).bdd_mul (c := 1) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)
  · exact Filter.Eventually.of_forall fun w => le_of_eq (Complex.norm_exp_ofReal_mul_I _)

private theorem integral_finiteFrequencyTerm {ι : Type*} {δ : ℝ} (hδ : 0 < δ)
    (c : ι → ℂ) (x : ι → ℝ) (i j : ι) :
    (∫ w : ℝ, finiteFrequencyTerm c x δ i j w)
      = (c i * (starRingEnd ℂ) (c j)) * triC δ (x i - x j) := by
  simp only [finiteFrequencyTerm]
  rw [integral_const_mul, ← triC_eq_integral hδ]

private theorem sum_finiteFrequencyPhase_eq_normSq {ι : Type*} (c : ι → ℂ)
    (s : Finset ι) (x : ι → ℝ) (w : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, (c i * (starRingEnd ℂ) (c j))
        * Complex.exp (((2 * Real.pi * (w * (x i - x j)) : ℝ) : ℂ) * Complex.I))
      = ((‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  have hzc : ((‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = finiteFrequencyPoly c s x w * (starRingEnd ℂ) (finiteFrequencyPoly c s x w) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hzc, finiteFrequencyPoly, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [phase_sub, map_mul]
  ring

private theorem sum_finiteFrequencyTerm {ι : Type*} (c : ι → ℂ) (s : Finset ι)
    (x : ι → ℝ) (δ : ℝ) (w : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, finiteFrequencyTerm c x δ i j w)
      = 𝓕 (triC δ) w * ((‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [← sum_finiteFrequencyPhase_eq_normSq c s x w, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [finiteFrequencyTerm]
  ring

private theorem integrable_finiteFrequencyWeight {ι : Type*} {δ : ℝ} (hδ : 0 < δ)
    (c : ι → ℂ) (s : Finset ι) (x : ι → ℝ) :
    Integrable fun w : ℝ => (𝓕 (triC δ) w).re * ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ) := by
  have hcomplex : Integrable fun w : ℝ =>
      𝓕 (triC δ) w * ((‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    have hsum : Integrable fun w : ℝ =>
        ∑ i ∈ s, ∑ j ∈ s, finiteFrequencyTerm c x δ i j w :=
      integrable_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ => integrable_finiteFrequencyTerm hδ c x i j
    exact hsum.congr (Filter.Eventually.of_forall (sum_finiteFrequencyTerm c s x δ))
  exact hcomplex.re.congr (Filter.Eventually.of_forall fun w => re_mul_ofReal _ _)

/-- Exact triangular quadratic form for an arbitrary finite frequency family. -/
theorem integral_finiteFrequencyWeight_eq {ι : Type*} {δ : ℝ} (hδ : 0 < δ)
    (c : ι → ℂ) (s : Finset ι) (x : ι → ℝ) :
    (∫ w : ℝ, (𝓕 (triC δ) w).re * ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ))
      = ∑ i ∈ s, ∑ j ∈ s,
          (c i * (starRingEnd ℂ) (c j)).re * max (δ - |x i - x j|) 0 := by
  have hcomplex : Integrable fun w : ℝ =>
      𝓕 (triC δ) w * ((‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    have hsum : Integrable fun w : ℝ =>
        ∑ i ∈ s, ∑ j ∈ s, finiteFrequencyTerm c x δ i j w :=
      integrable_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun j _ => integrable_finiteFrequencyTerm hδ c x i j
    exact hsum.congr (Filter.Eventually.of_forall (sum_finiteFrequencyTerm c s x δ))
  have hterm : ∀ i j : ι,
      (c i * (starRingEnd ℂ) (c j)).re * max (δ - |x i - x j|) 0
        = (∫ w : ℝ, finiteFrequencyTerm c x δ i j w).re := by
    intro i j
    rw [integral_finiteFrequencyTerm hδ, triC, tri, re_mul_ofReal]
  calc
    (∫ w : ℝ, (𝓕 (triC δ) w).re * ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ))
        = (∫ w : ℝ,
            𝓕 (triC δ) w * ((‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ) : ℝ) : ℂ)).re := by
          have h := integral_re (μ := volume) hcomplex
          simp only [RCLike.re_to_complex] at h
          rw [← h]
          refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
          exact (re_mul_ofReal _ _).symm
    _ = (∫ w : ℝ, ∑ i ∈ s, ∑ j ∈ s, finiteFrequencyTerm c x δ i j w).re := by
          rw [integral_congr_ae (Filter.Eventually.of_forall (sum_finiteFrequencyTerm c s x δ))]
    _ = (∑ i ∈ s, ∑ j ∈ s, ∫ w : ℝ, finiteFrequencyTerm c x δ i j w).re := by
          rw [integral_finsetSum _ fun i _ =>
            integrable_finsetSum _ fun j _ => integrable_finiteFrequencyTerm hδ c x i j]
          congr 1
          exact Finset.sum_congr rfl fun i _ =>
            integral_finsetSum _ fun j _ => integrable_finiteFrequencyTerm hδ c x i j
    _ = ∑ i ∈ s, ∑ j ∈ s,
          (∫ w : ℝ, finiteFrequencyTerm c x δ i j w).re := by
          rw [Complex.re_sum]
          exact Finset.sum_congr rfl fun i _ => Complex.re_sum _ _
    _ = ∑ i ∈ s, ∑ j ∈ s,
          (c i * (starRingEnd ℂ) (c j)).re * max (δ - |x i - x j|) 0 := by
          exact Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => (hterm i j).symm

/-- Weighted count of near-colliding ordered frequency pairs. -/
noncomputable def finiteFrequencyCollisionWeight {ι : Type*} (c : ι → ℂ) (s : Finset ι)
    (x : ι → ℝ) (δ : ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s,
    if |x i - x j| < δ then ‖c i‖ * ‖c j‖ else 0

private theorem finiteFrequencyQuadraticForm_le_collisionWeight {ι : Type*}
    (c : ι → ℂ) (s : Finset ι) (x : ι → ℝ) (δ : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s,
        (c i * (starRingEnd ℂ) (c j)).re * max (δ - |x i - x j|) 0)
      ≤ δ * finiteFrequencyCollisionWeight c s x δ := by
  rw [finiteFrequencyCollisionWeight, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hre : (c i * (starRingEnd ℂ) (c j)).re ≤ ‖c i‖ * ‖c j‖ := by
    exact (Complex.re_le_norm _).trans_eq (by rw [norm_mul, RCLike.norm_conj])
  have hkernel : 0 ≤ max (δ - |x i - x j|) 0 := le_max_right _ _
  calc
    (c i * (starRingEnd ℂ) (c j)).re * max (δ - |x i - x j|) 0
        ≤ (‖c i‖ * ‖c j‖) * max (δ - |x i - x j|) 0 :=
          mul_le_mul_of_nonneg_right hre hkernel
    _ ≤ (‖c i‖ * ‖c j‖)
          * (δ * (if |x i - x j| < δ then (1 : ℝ) else 0)) :=
          mul_le_mul_of_nonneg_left (max_sub_abs_le_indicator (δ := δ) (x i - x j))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = δ * (if |x i - x j| < δ then ‖c i‖ * ‖c j‖ else 0) := by
          by_cases h : |x i - x j| < δ
          · simp only [if_pos h]
            ring
          · simp [h]

/-- **Finite-frequency sparse mean-value inequality.**  Repeated frequencies stay separate, and
the bound is the actual weighted near-collision sum. -/
theorem integral_Icc_normSq_finiteFrequencyPoly_le_collisionWeight {ι : Type*}
    (c : ι → ℂ) (s : Finset ι) (x : ι → ℝ) {δ W : ℝ}
    (hδ : 0 < δ) (hWδ : 2 * Real.pi * δ * W ≤ 1) :
    (∫ w in Set.Icc (-W) W, ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ))
      ≤ (5 / (4 * δ)) * finiteFrequencyCollisionWeight c s x δ := by
  have hweight := integrable_finiteFrequencyWeight hδ c s x
  have hcont : Continuous fun w : ℝ => ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ) :=
    ((continuous_finiteFrequencyPoly c s x).norm).pow 2
  have hstep : ∀ w ∈ Set.Icc (-W) W,
      ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ)
        ≤ (5 / (4 * δ ^ (2 : ℕ)))
            * ((𝓕 (triC δ) w).re * ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ)) := by
    intro w hw
    have hwabs : |w| ≤ W := by
      rw [abs_le]
      exact ⟨hw.1, hw.2⟩
    have hbound : |2 * Real.pi * δ * w| ≤ 1 := by
      have hpos : (0 : ℝ) < 2 * Real.pi * δ := by positivity
      rw [abs_mul, abs_of_pos hpos]
      exact (mul_le_mul_of_nonneg_left hwabs hpos.le).trans hWδ
    have hlow := le_fourier_triC_re hδ hbound
    have hsq : (0 : ℝ) ≤ ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ) := by positivity
    have hmul : (4 / 5) * δ ^ (2 : ℕ) * ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ)
        ≤ (𝓕 (triC δ) w).re * ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right hlow hsq
    have hc : (0 : ℝ) < 5 / (4 * δ ^ (2 : ℕ)) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hmul hc.le
    have hid : (5 / (4 * δ ^ (2 : ℕ)))
          * ((4 / 5) * δ ^ (2 : ℕ) * ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ))
        = ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ) := by field_simp
    linarith [hscaled, hid.le, hid.ge]
  have hcentral : (∫ w in Set.Icc (-W) W, ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ))
      ≤ (5 / (4 * δ ^ (2 : ℕ)))
          * ∫ w : ℝ, (𝓕 (triC δ) w).re * ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ) := by
    have hlocal : (∫ w in Set.Icc (-W) W, ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ))
        ≤ ∫ w in Set.Icc (-W) W,
            (5 / (4 * δ ^ (2 : ℕ)))
              * ((𝓕 (triC δ) w).re * ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ)) := by
      refine setIntegral_mono_on ?_ ?_ measurableSet_Icc hstep
      · exact hcont.continuousOn.integrableOn_compact isCompact_Icc
      · exact (hweight.const_mul _).integrableOn
    refine hlocal.trans ?_
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_le_integral hweight (Filter.Eventually.of_forall fun w =>
      mul_nonneg (fourier_triC_re_nonneg hδ w) (by positivity))
  calc
    (∫ w in Set.Icc (-W) W, ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ))
        ≤ (5 / (4 * δ ^ (2 : ℕ)))
            * ∫ w : ℝ, (𝓕 (triC δ) w).re * ‖finiteFrequencyPoly c s x w‖ ^ (2 : ℕ) := hcentral
    _ = (5 / (4 * δ ^ (2 : ℕ))) * (∑ i ∈ s, ∑ j ∈ s,
          (c i * (starRingEnd ℂ) (c j)).re * max (δ - |x i - x j|) 0) := by
          rw [integral_finiteFrequencyWeight_eq hδ c s x]
    _ ≤ (5 / (4 * δ ^ (2 : ℕ))) * (δ * finiteFrequencyCollisionWeight c s x δ) :=
          mul_le_mul_of_nonneg_left
            (finiteFrequencyQuadraticForm_le_collisionWeight c s x δ) (by positivity)
    _ = (5 / (4 * δ)) * finiteFrequencyCollisionWeight c s x δ := by field_simp

/-- Heath--Brown's product frequency, normalized to the `e(ux)` convention. -/
noncomputable def heathBrownProductFrequency (p : ℕ × ℕ) : ℝ :=
  -Real.log (p.1 * p.2 : ℕ) / (2 * Real.pi)

/-- Product Dirichlet polynomial with unit phases and coefficients intrinsically in `[0,1]`. -/
noncomputable def heathBrownSparseProductPoly (A B : Finset ℕ) (ε : ℕ → Circle)
    (q : ℕ → Set.Icc (0 : ℝ) 1) (t : ℝ) : ℂ :=
  finiteFrequencyPoly
    (fun p : ℕ × ℕ => (ε p.1 : ℂ) * (((q p.2 : ℝ) : ℂ)))
    (A.product B) heathBrownProductFrequency t

/-- Literal ordered near-product collision count.  Equal products retain every representation. -/
noncomputable def heathBrownProductCollision (A B : Finset ℕ) (T : Set.Ioi (0 : ℝ)) : ℕ :=
  #(((A.product B).product (A.product B)).filter fun z =>
    |Real.log (z.1.1 * z.1.2 : ℕ) - Real.log (z.2.1 * z.2.2 : ℕ)| < ((T : ℝ))⁻¹)

private theorem heathBrownProductFrequency_close_iff (p r : ℕ × ℕ)
    (T : Set.Ioi (0 : ℝ)) :
    |heathBrownProductFrequency p - heathBrownProductFrequency r|
        < 1 / (2 * Real.pi * (T : ℝ)) ↔
      |Real.log (p.1 * p.2 : ℕ) - Real.log (r.1 * r.2 : ℕ)| < ((T : ℝ))⁻¹ := by
  have hden : (0 : ℝ) < 2 * Real.pi := by positivity
  have hT : (0 : ℝ) < (T : ℝ) := T.property
  have hleft :
      |heathBrownProductFrequency p - heathBrownProductFrequency r|
        = |Real.log (p.1 * p.2 : ℕ) - Real.log (r.1 * r.2 : ℕ)| / (2 * Real.pi) := by
    rw [heathBrownProductFrequency, heathBrownProductFrequency]
    rw [show -Real.log (p.1 * p.2 : ℕ) / (2 * Real.pi)
          - -Real.log (r.1 * r.2 : ℕ) / (2 * Real.pi)
        = -(Real.log (p.1 * p.2 : ℕ) - Real.log (r.1 * r.2 : ℕ)) / (2 * Real.pi) by ring,
      abs_div, abs_neg, abs_of_pos hden]
  have hright : 1 / (2 * Real.pi * (T : ℝ)) = ((T : ℝ))⁻¹ / (2 * Real.pi) := by
    field_simp
  rw [hleft, hright, div_lt_div_iff₀ hden hden]
  constructor <;> intro h <;> nlinarith [hden]

private theorem norm_heathBrownCoefficient_le_one (ε : ℕ → Circle)
    (q : ℕ → Set.Icc (0 : ℝ) 1) (p : ℕ × ℕ) :
    ‖(ε p.1 : ℂ) * (((q p.2 : ℝ) : ℂ))‖ ≤ 1 := by
  rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (q p.2).property.1]
  exact (q p.2).property.2

private theorem heathBrownCollisionWeight_le_count (A B : Finset ℕ) (ε : ℕ → Circle)
    (q : ℕ → Set.Icc (0 : ℝ) 1) (T : Set.Ioi (0 : ℝ)) :
    finiteFrequencyCollisionWeight
        (fun p : ℕ × ℕ => (ε p.1 : ℂ) * (((q p.2 : ℝ) : ℂ)))
        (A.product B) heathBrownProductFrequency (1 / (2 * Real.pi * (T : ℝ)))
      ≤ (heathBrownProductCollision A B T : ℝ) := by
  rw [finiteFrequencyCollisionWeight]
  calc
    (∑ p ∈ A.product B, ∑ r ∈ A.product B,
        if |heathBrownProductFrequency p - heathBrownProductFrequency r|
            < 1 / (2 * Real.pi * (T : ℝ)) then
          ‖(ε p.1 : ℂ) * (((q p.2 : ℝ) : ℂ))‖
            * ‖(ε r.1 : ℂ) * (((q r.2 : ℝ) : ℂ))‖ else 0)
      ≤ ∑ p ∈ A.product B, ∑ r ∈ A.product B,
          if |Real.log (p.1 * p.2 : ℕ) - Real.log (r.1 * r.2 : ℕ)| < ((T : ℝ))⁻¹
          then (1 : ℝ) else 0 := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun r _ => ?_
        by_cases hclose : |heathBrownProductFrequency p - heathBrownProductFrequency r|
            < 1 / (2 * Real.pi * (T : ℝ))
        · rw [if_pos hclose, if_pos ((heathBrownProductFrequency_close_iff p r T).mp hclose)]
          have hp := norm_heathBrownCoefficient_le_one ε q p
          have hr := norm_heathBrownCoefficient_le_one ε q r
          nlinarith [norm_nonneg ((ε p.1 : ℂ) * (((q p.2 : ℝ) : ℂ))),
            norm_nonneg ((ε r.1 : ℂ) * (((q r.2 : ℝ) : ℂ)))]
        · rw [if_neg hclose]
          positivity
    _ = (heathBrownProductCollision A B T : ℝ) := by
        let f : (ℕ × ℕ) × (ℕ × ℕ) → ℝ := fun z =>
          if |Real.log (z.1.1 * z.1.2 : ℕ) - Real.log (z.2.1 * z.2.2 : ℕ)| < ((T : ℝ))⁻¹
          then 1 else 0
        calc
          (∑ p ∈ A.product B, ∑ r ∈ A.product B,
              if |Real.log (p.1 * p.2 : ℕ) - Real.log (r.1 * r.2 : ℕ)| < ((T : ℝ))⁻¹
              then (1 : ℝ) else 0)
              = ∑ z ∈ (A.product B).product (A.product B), f z := by
                exact (Finset.sum_product (A.product B) (A.product B) f).symm
          _ = (heathBrownProductCollision A B T : ℝ) := by
                rw [Finset.sum_boole]
                rfl

/-- **Heath--Brown sparse mean value, basic unconditional form.**  For every finite pair of
supports, unit phases, `[0,1]` coefficients, and positive height, the physical mean square is at
most `(5π/2) T` times the literal ordered near-product collision count. -/
theorem integral_Icc_normSq_heathBrownSparseProductPoly_le_collision
    (A B : Finset ℕ) (ε : ℕ → Circle) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖heathBrownSparseProductPoly A B ε q t‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2) * (T : ℝ) * (heathBrownProductCollision A B T : ℝ) := by
  have hδ : (0 : ℝ) < 1 / (2 * Real.pi * (T : ℝ)) := by
    exact one_div_pos.mpr (mul_pos (by positivity) T.property)
  have hscale : 2 * Real.pi * (1 / (2 * Real.pi * (T : ℝ))) * (T : ℝ) ≤ 1 := by
    have hT : (0 : ℝ) < (T : ℝ) := T.property
    field_simp
    exact le_rfl
  have hbase := integral_Icc_normSq_finiteFrequencyPoly_le_collisionWeight
    (fun p : ℕ × ℕ => (ε p.1 : ℂ) * (((q p.2 : ℝ) : ℂ)))
    (A.product B) heathBrownProductFrequency hδ hscale
  have hbase' :
      (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖heathBrownSparseProductPoly A B ε q t‖ ^ (2 : ℕ))
        ≤ (5 / (4 * (1 / (2 * Real.pi * (T : ℝ)))))
            * finiteFrequencyCollisionWeight
                (fun p : ℕ × ℕ => (ε p.1 : ℂ) * (((q p.2 : ℝ) : ℂ)))
                (A.product B) heathBrownProductFrequency (1 / (2 * Real.pi * (T : ℝ))) := by
    simpa [heathBrownSparseProductPoly] using hbase
  refine hbase'.trans ?_
  have hcollision := heathBrownCollisionWeight_le_count A B ε q T
  have hfactor : (0 : ℝ) ≤ 5 / (4 * (1 / (2 * Real.pi * (T : ℝ)))) := by positivity
  calc
    (5 / (4 * (1 / (2 * Real.pi * (T : ℝ)))))
        * finiteFrequencyCollisionWeight
            (fun p : ℕ × ℕ => (ε p.1 : ℂ) * (((q p.2 : ℝ) : ℂ)))
            (A.product B) heathBrownProductFrequency (1 / (2 * Real.pi * (T : ℝ)))
      ≤ (5 / (4 * (1 / (2 * Real.pi * (T : ℝ)))))
          * (heathBrownProductCollision A B T : ℝ) :=
        mul_le_mul_of_nonneg_left hcollision hfactor
    _ = (5 * Real.pi / 2) * (T : ℝ) * (heathBrownProductCollision A B T : ℝ) := by
        field_simp
        ring

/-- Physical phase `n^{-it}` on a positive integer. -/
noncomputable def heathBrownDirichletPhase (n : PNat) (t : ℝ) : ℂ :=
  Complex.exp ((-((t * Real.log (n : ℕ) : ℝ) : ℂ)) * Complex.I)

/-- Sparse physical factor. -/
noncomputable def heathBrownSparseFactor (A : Finset PNat) (ε : ℕ → Circle) (t : ℝ) : ℂ :=
  ∑ m ∈ A, (ε (m : ℕ) : ℂ) * heathBrownDirichletPhase m t

/-- Dense physical factor with coefficients intrinsically in `[0,1]`. -/
noncomputable def heathBrownDenseFactor (B : Finset PNat)
    (q : ℕ → Set.Icc (0 : ℝ) 1) (t : ℝ) : ℂ :=
  ∑ n ∈ B, (((q (n : ℕ) : ℝ) : ℂ)) * heathBrownDirichletPhase n t

/-- Heath--Brown's product frequency on intrinsically positive indices. -/
noncomputable def heathBrownPositiveProductFrequency (p : PNat × PNat) : ℝ :=
  heathBrownProductFrequency ((p.1 : ℕ), (p.2 : ℕ))

/-- Product coefficient on intrinsically positive indices. -/
noncomputable def heathBrownPositiveCoefficient (ε : ℕ → Circle)
    (q : ℕ → Set.Icc (0 : ℝ) 1) (p : PNat × PNat) : ℂ :=
  (ε (p.1 : ℕ) : ℂ) * (((q (p.2 : ℕ) : ℝ) : ℂ))

/-- Positive-support product polynomial; positivity is carried by the index type. -/
noncomputable def heathBrownPositiveProductPoly (A B : Finset PNat) (ε : ℕ → Circle)
    (q : ℕ → Set.Icc (0 : ℝ) 1) (t : ℝ) : ℂ :=
  finiteFrequencyPoly
    (heathBrownPositiveCoefficient ε q)
    (A.product B) heathBrownPositiveProductFrequency t

/-- Positive-support literal collision count. -/
noncomputable def heathBrownPositiveProductCollision (A B : Finset PNat)
    (T : Set.Ioi (0 : ℝ)) : ℕ :=
  #(((A.product B).product (A.product B)).filter fun z =>
    |Real.log ((z.1.1 : ℕ) * (z.1.2 : ℕ) : ℕ)
        - Real.log ((z.2.1 : ℕ) * (z.2.2 : ℕ) : ℕ)| < ((T : ℝ))⁻¹)

private theorem heathBrown_product_phase (m n : PNat) (t : ℝ) :
    Complex.exp (((2 * Real.pi
      * (t * heathBrownPositiveProductFrequency (m, n)) : ℝ) : ℂ) * Complex.I)
      = heathBrownDirichletPhase m t * heathBrownDirichletPhase n t := by
  have hm : (((m : ℕ) : ℝ)) ≠ 0 := by positivity
  have hn : (((n : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [heathBrownDirichletPhase, heathBrownDirichletPhase, ← Complex.exp_add,
    heathBrownPositiveProductFrequency, heathBrownProductFrequency]
  have hcast : ((((m : ℕ) * (n : ℕ) : ℕ) : ℝ))
      = ((m : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by norm_cast
  rw [hcast, Real.log_mul hm hn]
  congr 1
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Real.pi_pos)
  field_simp
  ring

/-- Exact identification of the indexed product polynomial with `M(it)Q(it)`. -/
theorem heathBrownPositiveProductPoly_eq_mul (A B : Finset PNat) (ε : ℕ → Circle)
    (q : ℕ → Set.Icc (0 : ℝ) 1) (t : ℝ) :
    heathBrownPositiveProductPoly A B ε q t
      = heathBrownSparseFactor A ε t * heathBrownDenseFactor B q t := by
  rw [heathBrownPositiveProductPoly, finiteFrequencyPoly]
  calc
    (∑ p ∈ A.product B, heathBrownPositiveCoefficient ε q p
        * Complex.exp (((2 * Real.pi * (t * heathBrownPositiveProductFrequency p) : ℝ) : ℂ)
            * Complex.I))
        = ∑ m ∈ A, ∑ n ∈ B, heathBrownPositiveCoefficient ε q (m, n)
            * Complex.exp (((2 * Real.pi * (t * heathBrownPositiveProductFrequency (m, n)) : ℝ) : ℂ)
                * Complex.I) := Finset.sum_product A B _
    _ = heathBrownSparseFactor A ε t * heathBrownDenseFactor B q t := by
      rw [heathBrownSparseFactor, heathBrownDenseFactor, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
      rw [heathBrownPositiveCoefficient, heathBrown_product_phase]
      ring

private theorem heathBrownPositiveProductFrequency_close_iff (p r : PNat × PNat)
    (T : Set.Ioi (0 : ℝ)) :
    |heathBrownPositiveProductFrequency p - heathBrownPositiveProductFrequency r|
        < 1 / (2 * Real.pi * (T : ℝ)) ↔
      |Real.log ((p.1 : ℕ) * (p.2 : ℕ) : ℕ)
          - Real.log ((r.1 : ℕ) * (r.2 : ℕ) : ℕ)| < ((T : ℝ))⁻¹ := by
  simpa only [heathBrownPositiveProductFrequency]
    using heathBrownProductFrequency_close_iff
      ((p.1 : ℕ), (p.2 : ℕ)) ((r.1 : ℕ), (r.2 : ℕ)) T

private theorem norm_heathBrownPositiveCoefficient_le_one (ε : ℕ → Circle)
    (q : ℕ → Set.Icc (0 : ℝ) 1) (p : PNat × PNat) :
    ‖heathBrownPositiveCoefficient ε q p‖ ≤ 1 := by
  simpa only [heathBrownPositiveCoefficient]
    using norm_heathBrownCoefficient_le_one ε q ((p.1 : ℕ), (p.2 : ℕ))

private theorem heathBrownPositiveCollisionWeight_le_count (A B : Finset PNat)
    (ε : ℕ → Circle) (q : ℕ → Set.Icc (0 : ℝ) 1) (T : Set.Ioi (0 : ℝ)) :
    finiteFrequencyCollisionWeight (heathBrownPositiveCoefficient ε q) (A.product B)
        heathBrownPositiveProductFrequency (1 / (2 * Real.pi * (T : ℝ)))
      ≤ (heathBrownPositiveProductCollision A B T : ℝ) := by
  rw [finiteFrequencyCollisionWeight]
  calc
    (∑ p ∈ A.product B, ∑ r ∈ A.product B,
        if |heathBrownPositiveProductFrequency p - heathBrownPositiveProductFrequency r|
            < 1 / (2 * Real.pi * (T : ℝ)) then
          ‖heathBrownPositiveCoefficient ε q p‖ * ‖heathBrownPositiveCoefficient ε q r‖ else 0)
      ≤ ∑ p ∈ A.product B, ∑ r ∈ A.product B,
          if |Real.log ((p.1 : ℕ) * (p.2 : ℕ) : ℕ)
              - Real.log ((r.1 : ℕ) * (r.2 : ℕ) : ℕ)| < ((T : ℝ))⁻¹
          then (1 : ℝ) else 0 := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun r _ => ?_
        by_cases hclose : |heathBrownPositiveProductFrequency p
              - heathBrownPositiveProductFrequency r| < 1 / (2 * Real.pi * (T : ℝ))
        · rw [if_pos hclose,
            if_pos ((heathBrownPositiveProductFrequency_close_iff p r T).mp hclose)]
          have hp := norm_heathBrownPositiveCoefficient_le_one ε q p
          have hr := norm_heathBrownPositiveCoefficient_le_one ε q r
          nlinarith [norm_nonneg (heathBrownPositiveCoefficient ε q p),
            norm_nonneg (heathBrownPositiveCoefficient ε q r)]
        · rw [if_neg hclose]
          positivity
    _ = (heathBrownPositiveProductCollision A B T : ℝ) := by
        let f : (PNat × PNat) × (PNat × PNat) → ℝ := fun z =>
          if |Real.log ((z.1.1 : ℕ) * (z.1.2 : ℕ) : ℕ)
              - Real.log ((z.2.1 : ℕ) * (z.2.2 : ℕ) : ℕ)| < ((T : ℝ))⁻¹
          then 1 else 0
        calc
          (∑ p ∈ A.product B, ∑ r ∈ A.product B,
              if |Real.log ((p.1 : ℕ) * (p.2 : ℕ) : ℕ)
                  - Real.log ((r.1 : ℕ) * (r.2 : ℕ) : ℕ)| < ((T : ℝ))⁻¹
              then (1 : ℝ) else 0)
              = ∑ z ∈ (A.product B).product (A.product B), f z := by
                exact (Finset.sum_product (A.product B) (A.product B) f).symm
          _ = (heathBrownPositiveProductCollision A B T : ℝ) := by
                rw [Finset.sum_boole]
                rfl

/-- **Heath--Brown Theorem 4(i), explicit positive-support form.**  Exact `M(it)Q(it)` mean square
is bounded by `(5π/2)T` times the literal near-product collision count. -/
theorem integral_Icc_normSq_heathBrown_factors_le_collision
    (A B : Finset PNat) (ε : ℕ → Circle) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A ε t * heathBrownDenseFactor B q t‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2) * (T : ℝ) * (heathBrownPositiveProductCollision A B T : ℝ) := by
  have hδ : (0 : ℝ) < 1 / (2 * Real.pi * (T : ℝ)) := by
    exact one_div_pos.mpr (mul_pos (by positivity) T.property)
  have hscale : 2 * Real.pi * (1 / (2 * Real.pi * (T : ℝ))) * (T : ℝ) ≤ 1 := by
    have hT : (0 : ℝ) < (T : ℝ) := T.property
    field_simp
    exact le_rfl
  have hbase := integral_Icc_normSq_finiteFrequencyPoly_le_collisionWeight
    (heathBrownPositiveCoefficient ε q) (A.product B) heathBrownPositiveProductFrequency
    hδ hscale
  have hbase' :
      (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖heathBrownPositiveProductPoly A B ε q t‖ ^ (2 : ℕ))
        ≤ (5 / (4 * (1 / (2 * Real.pi * (T : ℝ)))))
            * finiteFrequencyCollisionWeight (heathBrownPositiveCoefficient ε q) (A.product B)
                heathBrownPositiveProductFrequency (1 / (2 * Real.pi * (T : ℝ))) := by
    simpa only [heathBrownPositiveProductPoly] using hbase
  have hbase'' :
      (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
          ‖heathBrownSparseFactor A ε t * heathBrownDenseFactor B q t‖ ^ (2 : ℕ))
        ≤ (5 / (4 * (1 / (2 * Real.pi * (T : ℝ)))))
            * finiteFrequencyCollisionWeight (heathBrownPositiveCoefficient ε q) (A.product B)
                heathBrownPositiveProductFrequency (1 / (2 * Real.pi * (T : ℝ))) := by
    simpa only [heathBrownPositiveProductPoly_eq_mul] using hbase'
  refine hbase''.trans ?_
  have hcollision := heathBrownPositiveCollisionWeight_le_count A B ε q T
  have hfactor : (0 : ℝ) ≤ 5 / (4 * (1 / (2 * Real.pi * (T : ℝ)))) := by positivity
  calc
    (5 / (4 * (1 / (2 * Real.pi * (T : ℝ)))))
        * finiteFrequencyCollisionWeight (heathBrownPositiveCoefficient ε q) (A.product B)
            heathBrownPositiveProductFrequency (1 / (2 * Real.pi * (T : ℝ)))
      ≤ (5 / (4 * (1 / (2 * Real.pi * (T : ℝ)))))
          * (heathBrownPositiveProductCollision A B T : ℝ) :=
        mul_le_mul_of_nonneg_left hcollision hfactor
    _ = (5 * Real.pi / 2) * (T : ℝ) * (heathBrownPositiveProductCollision A B T : ℝ) := by
        field_simp
        ring

end RHTower.Sieve
