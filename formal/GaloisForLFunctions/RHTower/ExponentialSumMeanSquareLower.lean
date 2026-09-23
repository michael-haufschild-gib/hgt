import GaloisForLFunctions.RHTower.BohrCesaroMean

/-!
# A finite exponential sum is frequently large

The Bohr--Cesàro mean of the modulus square of a finite exponential sum with distinct real
frequencies is exactly the sum of the squared coefficient moduli: expanding `|P|²` produces the
pair frequencies `ω_i − ω_j`, and only the diagonal survives the mean.

Consequently a nonzero finite exponential sum cannot be eventually smaller than any threshold below
its mean square: it exceeds that threshold along a cofinal set of times.  No frequency separation
or pointwise phase limit is used.
-/

open Filter Topology Complex

namespace RHTower

noncomputable section

variable {ι : Type*}

/-- A finite exponential sum with real frequencies. -/
def expSum_exponentialSumMeanSquareLower (s : Finset ι) (c : ι → ℂ) (om : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ j ∈ s, c j * Complex.exp (-Complex.I * (om j : ℂ) * (t : ℂ))

theorem norm_expSum_le (s : Finset ι) (c : ι → ℂ) (om : ι → ℝ) (t : ℝ) :
    ‖expSum_exponentialSumMeanSquareLower s c om t‖ ≤ ∑ j ∈ s, ‖c j‖ := by
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_mul, norm_char (om j) t, mul_one]

theorem continuous_expSum (s : Finset ι) (c : ι → ℂ) (om : ι → ℝ) :
    Continuous fun t : ℝ => expSum_exponentialSumMeanSquareLower s c om t := by
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))

/-- The modulus square expands into the pair frequencies. -/
theorem normSq_expSum_eq (s : Finset ι) (c : ι → ℂ) (om : ι → ℝ) (t : ℝ) :
    ((‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = ∑ p ∈ s ×ˢ s, (c p.1 * (starRingEnd ℂ) (c p.2))
          * Complex.exp (-Complex.I * ((om p.1 - om p.2 : ℝ) : ℂ) * (t : ℂ)) := by
  have hconj : ((‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ) : ℝ) : ℂ)
      = expSum_exponentialSumMeanSquareLower s c om t * (starRingEnd ℂ) (expSum_exponentialSumMeanSquareLower s c om t) := by
    rw [Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_eq_norm_sq]
  rw [hconj, expSum_exponentialSumMeanSquareLower, map_sum, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun p _ => ?_
  have hconjexp : (starRingEnd ℂ) (Complex.exp (-Complex.I * (om p.2 : ℂ) * (t : ℂ)))
      = Complex.exp (Complex.I * (om p.2 : ℂ) * (t : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I]
  calc c p.1 * Complex.exp (-Complex.I * (om p.1 : ℂ) * (t : ℂ))
        * (starRingEnd ℂ) (c p.2 * Complex.exp (-Complex.I * (om p.2 : ℂ) * (t : ℂ)))
      = (c p.1 * (starRingEnd ℂ) (c p.2))
          * (Complex.exp (-Complex.I * (om p.1 : ℂ) * (t : ℂ))
            * Complex.exp (Complex.I * (om p.2 : ℂ) * (t : ℂ))) := by
        rw [map_mul, hconjexp]
        ring
    _ = (c p.1 * (starRingEnd ℂ) (c p.2))
          * Complex.exp (-Complex.I * ((om p.1 - om p.2 : ℝ) : ℂ) * (t : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring

/-- **The Bohr--Cesàro mean square of a finite exponential sum with distinct frequencies.** -/
theorem tendsto_cesaro_normSq_expSum [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (om : ι → ℝ)
    (hinj : Set.InjOn om (s : Set ι)) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ t in (1 : ℝ)..T, ‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ)) atTop
      (𝓝 (∑ j ∈ s, ‖c j‖ ^ (2 : ℕ))) := by
  classical
  have hcesaro := tendsto_cesaro_expSum (s ×ˢ s)
    (fun p : ι × ι => c p.1 * (starRingEnd ℂ) (c p.2))
    (fun p : ι × ι => om p.1 - om p.2)
  have hdiag : ∑ p ∈ (s ×ˢ s).filter (fun p : ι × ι => om p.1 - om p.2 = 0),
      (c p.1 * (starRingEnd ℂ) (c p.2)) = ((∑ j ∈ s, ‖c j‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [Finset.sum_filter,
      Finset.sum_product' s s
        (fun i j => if om i - om j = 0 then c i * (starRingEnd ℂ) (c j) else 0)]
    have hinner : ∀ i ∈ s,
        (∑ j ∈ s, if om i - om j = 0 then c i * (starRingEnd ℂ) (c j) else 0)
          = ((‖c i‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      intro i hi
      rw [Finset.sum_eq_single i]
      · rw [if_pos (by ring), Complex.mul_conj]
        norm_cast
        rw [Complex.normSq_eq_norm_sq]
      · intro j hj hne
        refine if_neg ?_
        intro hzero
        exact hne (hinj hj hi (by linarith [sub_eq_zero.1 hzero]))
      · intro hcon
        exact absurd hi hcon
    rw [Finset.sum_congr rfl hinner, Complex.ofReal_sum]
  rw [hdiag] at hcesaro
  have hrewrite : ∀ T : ℝ, (1 / (T : ℂ)) *
      ∫ t in (1 : ℝ)..T, ∑ p ∈ s ×ˢ s, (c p.1 * (starRingEnd ℂ) (c p.2))
          * Complex.exp (-Complex.I * ((om p.1 - om p.2 : ℝ) : ℂ) * (t : ℂ))
      = (((1 / T) * ∫ t in (1 : ℝ)..T, ‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro T
    have hint : ∫ t in (1 : ℝ)..T, ∑ p ∈ s ×ˢ s, (c p.1 * (starRingEnd ℂ) (c p.2))
        * Complex.exp (-Complex.I * ((om p.1 - om p.2 : ℝ) : ℂ) * (t : ℂ))
        = ((∫ t in (1 : ℝ)..T, ‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun t _ => ?_
      exact (normSq_expSum_eq s c om t).symm
    rw [hint]
    push_cast
    ring
  have hfinal : Tendsto (fun T : ℝ =>
      (((1 / T) * ∫ t in (1 : ℝ)..T, ‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ) : ℝ) : ℂ)) atTop
      (𝓝 (((∑ j ∈ s, ‖c j‖ ^ (2 : ℕ) : ℝ) : ℂ))) := by
    refine hcesaro.congr fun T => ?_
    exact hrewrite T
  have hre := (Complex.continuous_re.tendsto _).comp hfinal
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  exact hre

/-- **A nonzero finite exponential sum is frequently large.** -/
theorem frequently_lt_norm_expSum [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (om : ι → ℝ)
    (hinj : Set.InjOn om (s : Set ι)) {delta : ℝ}
    (hlt : delta ^ (2 : ℕ) < ∑ j ∈ s, ‖c j‖ ^ (2 : ℕ)) :
    ∃ᶠ t : ℝ in atTop, delta < ‖expSum_exponentialSumMeanSquareLower s c om t‖ := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  simp only [not_lt] at hcon
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hcon
  set M : ℝ := ∑ j ∈ s, ‖c j‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hmean := tendsto_cesaro_normSq_expSum s c om hinj
  have hcontsq : Continuous fun t : ℝ => ‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ) :=
    ((continuous_expSum s c om).norm).pow 2
  have hbound : ∀ᶠ T : ℝ in atTop,
      (1 / T) * ∫ t in (1 : ℝ)..T, ‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ)
        ≤ delta ^ (2 : ℕ) + (M ^ (2 : ℕ) * (|T₀| + 1)) / T := by
    filter_upwards [eventually_ge_atTop (max T₀ 1), eventually_gt_atTop (0 : ℝ)] with T hT hTpos
    set A : ℝ := max T₀ 1 with hA
    have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
    have hAT : A ≤ T := hT
    have hsplit : ∫ t in (1 : ℝ)..T, ‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ)
        = (∫ t in (1 : ℝ)..A, ‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ))
          + ∫ t in A..T, ‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcontsq.intervalIntegrable _ _) (hcontsq.intervalIntegrable _ _)).symm
    have hfirst : ∫ t in (1 : ℝ)..A, ‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ) ≤ (A - 1) * M ^ (2 : ℕ) := by
      have hle : ∀ t ∈ Set.Icc (1 : ℝ) A, ‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
        intro t _
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_expSum_le s c om t) 2
      have hmono := intervalIntegral.integral_mono_on hA1 (hcontsq.intervalIntegrable _ _)
        (intervalIntegrable_const (μ := MeasureTheory.volume) (c := M ^ (2 : ℕ))) hle
      simpa using hmono
    have hsecond : ∫ t in A..T, ‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ) ≤ (T - A) * delta ^ (2 : ℕ) := by
      have hle : ∀ t ∈ Set.Icc A T, ‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ) ≤ delta ^ (2 : ℕ) := by
        intro t ht
        exact pow_le_pow_left₀ (norm_nonneg _) (hT₀ t (le_trans (le_max_left T₀ 1) ht.1)) 2
      have hmono := intervalIntegral.integral_mono_on hAT (hcontsq.intervalIntegrable _ _)
        (intervalIntegrable_const (μ := MeasureTheory.volume) (c := delta ^ (2 : ℕ))) hle
      simpa using hmono
    have hAle : A - 1 ≤ |T₀| + 1 := by
      rcases le_or_gt T₀ 1 with h | h
      · have hAeq : A = 1 := by
          rw [hA]
          exact max_eq_right h
        rw [hAeq]
        have : (0 : ℝ) ≤ |T₀| := abs_nonneg _
        linarith
      · have hAeq : A = T₀ := by
          rw [hA]
          exact max_eq_left h.le
        rw [hAeq]
        have : T₀ ≤ |T₀| := le_abs_self _
        linarith
    have hM2 : (0 : ℝ) ≤ M ^ (2 : ℕ) := by positivity
    have hd2 : (0 : ℝ) ≤ delta ^ (2 : ℕ) := by positivity
    have htotal : ∫ t in (1 : ℝ)..T, ‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ)
        ≤ M ^ (2 : ℕ) * (|T₀| + 1) + delta ^ (2 : ℕ) * T := by
      rw [hsplit]
      have h1 : (A - 1) * M ^ (2 : ℕ) ≤ M ^ (2 : ℕ) * (|T₀| + 1) := by nlinarith [hAle, hM2]
      have h2 : (T - A) * delta ^ (2 : ℕ) ≤ delta ^ (2 : ℕ) * T := by nlinarith [hA1, hd2, hAT]
      linarith
    have h1 : (1 / T) * (∫ t in (1 : ℝ)..T, ‖expSum_exponentialSumMeanSquareLower s c om t‖ ^ (2 : ℕ))
        ≤ (1 / T) * (M ^ (2 : ℕ) * (|T₀| + 1) + delta ^ (2 : ℕ) * T) :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    have h2 : (1 / T) * (M ^ (2 : ℕ) * (|T₀| + 1) + delta ^ (2 : ℕ) * T)
        = delta ^ (2 : ℕ) + (M ^ (2 : ℕ) * (|T₀| + 1)) / T := by
      field_simp
      ring
    linarith [h1, h2]
  have htail : Tendsto (fun T : ℝ => delta ^ (2 : ℕ) + (M ^ (2 : ℕ) * (|T₀| + 1)) / T) atTop
      (𝓝 (delta ^ (2 : ℕ) + 0)) := by
    refine tendsto_const_nhds.add ?_
    exact Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  rw [add_zero] at htail
  have hle := le_of_tendsto_of_tendsto hmean htail hbound
  linarith

end

end RHTower
