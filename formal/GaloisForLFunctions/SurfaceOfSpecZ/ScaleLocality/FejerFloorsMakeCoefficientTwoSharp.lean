import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.WeightedFloorCoefficientOneFails
import GaloisForLFunctions.HTGeometry.FejerKernel

/-!
# Coefficient two is sharp for weighted trace floors

The Fejer kernel minus one has floor minus one. At the `N+1` roots
of unity it takes the values `N,-1,...,-1`, while every active Fourier
sample vanishes. Narrow interval densities turn these discrete samples
into integrable nonnegative weights. The ratio `2N/(N+1)` approaches two.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Equally spaced samples over one period. -/
def rootSampleSites (N : ℕ) (j : Fin (N + 1)) : ℝ := 2 * Real.pi * j / (N + 1)

theorem rootSampleSites_character (N : ℕ) {r : ℕ} (hr : 0 < r) (hrN : r < N + 1) :
    (∑ j, Complex.exp ((((r : ℝ) * rootSampleSites N j : ℝ) : ℂ) * I)) = 0 := by
  have he : (fun j : ℕ => Complex.exp ((((r : ℝ) *
      (2 * Real.pi * j / (N + 1)) : ℝ) : ℂ) * I)) =
      fun j : ℕ => Complex.exp (2 * Real.pi * I * r * j / (N + 1)) := by
    funext j
    congr 1
    push_cast
    ring
  change (∑ j : Fin (N + 1), Complex.exp ((((r : ℝ) *
    (2 * Real.pi * (j : ℕ) / (N + 1)) : ℝ) : ℂ) * I)) = 0
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => Complex.exp ((((r : ℝ) *
    (2 * Real.pi * j / (N + 1)) : ℝ) : ℂ) * I)) (N + 1), he]
  exact _root_.HTGeometry.exp_unit_sum_zero (N + 1) r hr hrN

/-- Every nonzero difference frequency has zero mean over the roots. -/
theorem rootSampleSites_difference_character (N : ℕ) (i j : Fin (N + 1)) (hij : i ≠ j) :
    (∑ k, Complex.exp (((|(i : ℝ) - (j : ℝ)| * rootSampleSites N k : ℝ) : ℂ) * I)) = 0 := by
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · have he : |(i : ℝ) - (j : ℝ)| = ((j.val - i.val : ℕ) : ℝ) := by
      rw [Nat.cast_sub hlt.le, abs_of_neg (sub_neg.mpr (by exact_mod_cast hlt)), neg_sub]
    rw [he]
    exact rootSampleSites_character N (Nat.sub_pos_of_lt hlt)
      ((Nat.sub_le _ _).trans_lt j.isLt)
  · have he : |(i : ℝ) - (j : ℝ)| = ((i.val - j.val : ℕ) : ℝ) := by
      rw [Nat.cast_sub hgt.le, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hgt.le))]
    rw [he]
    exact rootSampleSites_character N (Nat.sub_pos_of_lt hgt)
      ((Nat.sub_le _ _).trans_lt i.isLt)

/-- A finite sum of positive-frequency characters whose real part is Fejer minus one. -/
def fejerPositiveSum (N : ℕ) (t : ℝ) : ℂ :=
  (((N : ℝ) + 1)⁻¹ : ℂ) * ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
    if i = j then 0 else Complex.exp (((|(i : ℝ) - (j : ℝ)| * t : ℝ) : ℂ) * I)

theorem fejerPositiveSum_re (N : ℕ) (t : ℝ) :
    (fejerPositiveSum N t).re = _root_.HTGeometry.fejerKernel N t - 1 := by
  classical
  have hdouble : (∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
      Complex.exp (((n : ℂ) - (m : ℂ)) * t * I)) =
      ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
        Complex.exp ((((i : ℝ) - (j : ℝ)) * t : ℝ) * I) := by
    rw [← Fin.sum_univ_eq_sum_range (fun n : ℕ =>
      ∑ m ∈ Finset.range (N + 1), Complex.exp (((n : ℂ) - (m : ℂ)) * t * I)) (N + 1)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Fin.sum_univ_eq_sum_range (fun m : ℕ =>
      Complex.exp (((i.val : ℂ) - (m : ℂ)) * t * I)) (N + 1)]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    ring
  have he := congrArg Complex.re (_root_.HTGeometry.fejerKernel_eq_double_sum N t)
  rw [hdouble] at he
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.re_sum, Complex.exp_ofReal_mul_I_re] at he
  have hcos (i j : Fin (N + 1)) :
      Real.cos (|(i : ℝ) - (j : ℝ)| * t) = Real.cos (((i : ℝ) - (j : ℝ)) * t) := by
    by_cases h : 0 ≤ (i : ℝ) - (j : ℝ)
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), neg_mul, Real.cos_neg]
  have hrow (i : Fin (N + 1)) :
      (∑ j : Fin (N + 1), Real.cos (((i : ℝ) - (j : ℝ)) * t)) =
        1 + ∑ j : Fin (N + 1), if i = j then 0 else Real.cos (((i : ℝ) - (j : ℝ)) * t) := by
    have ht (j : Fin (N + 1)) : Real.cos (((i : ℝ) - (j : ℝ)) * t) =
        (if j = i then 1 else 0) +
          (if i = j then 0 else Real.cos (((i : ℝ) - (j : ℝ)) * t)) := by
      by_cases h : i = j
      · subst j; simp only [sub_self, zero_mul, Real.cos_zero, if_true, add_zero]
      · simp only [h, h.symm, if_false, zero_add]
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hs : (∑ i : Fin (N + 1), ∑ j : Fin (N + 1), Real.cos (((i : ℝ) - (j : ℝ)) * t)) =
      (N : ℝ) + 1 + ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
        if i = j then 0 else Real.cos (((i : ℝ) - (j : ℝ)) * t) := by
    simp_rw [hrow]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
  rw [hs, mul_add, inv_mul_cancel₀ (show (N : ℝ) + 1 ≠ 0 by positivity)] at he
  have hp : (fejerPositiveSum N t).re = ((N : ℝ) + 1)⁻¹ *
      ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
        if i = j then 0 else Real.cos (((i : ℝ) - (j : ℝ)) * t) := by
    simp only [fejerPositiveSum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.re_sum, apply_ite Complex.re, Complex.zero_re,
      Complex.exp_ofReal_mul_I_re, hcos]
  rw [hp]
  linarith only [he]

theorem fejerPositiveSum_floor (N : ℕ) (t : ℝ) : -1 ≤ (fejerPositiveSum N t).re := by
  rw [fejerPositiveSum_re]
  linarith only [_root_.HTGeometry.fejerKernel_nonneg N t]

theorem fejerKernel_rootSampleSites (N : ℕ) (j : Fin (N + 1)) :
    _root_.HTGeometry.fejerKernel N (rootSampleSites N j) =
      if j = 0 then (N : ℝ) + 1 else 0 := by
  classical
  by_cases hj : j = 0
  · subst j
    rw [if_pos rfl]
    simp only [rootSampleSites, Fin.val_zero, Nat.cast_zero, mul_zero, zero_div]
    have he : _root_.HTGeometry.fejerSum N 0 = (N : ℂ) + 1 := by
      simp [_root_.HTGeometry.fejerSum]
    rw [_root_.HTGeometry.fejerKernel, he]
    have hn : ‖(N : ℂ) + 1‖ = (N : ℝ) + 1 := by
      exact_mod_cast Complex.norm_natCast (N + 1)
    rw [hn]
    field_simp
  · rw [if_neg hj]
    have hj0 : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
    have he : _root_.HTGeometry.fejerSum N (rootSampleSites N j) = 0 := by
      rw [_root_.HTGeometry.fejerSum]
      have h := _root_.HTGeometry.exp_unit_sum_zero (N + 1) j.val hj0 j.isLt
      convert h using 1
      apply Finset.sum_congr rfl
      intro n _
      congr 1
      unfold rootSampleSites
      push_cast
      ring
    rw [_root_.HTGeometry.fejerKernel, he, norm_zero, zero_pow (by norm_num), zero_div]

theorem rootSampleSites_abs_fejerPositiveSum (N : ℕ) :
    (∑ j, |(fejerPositiveSum N (rootSampleSites N j)).re|) = 2 * N := by
  simp_rw [fejerPositiveSum_re, fejerKernel_rootSampleSites]
  rw [Fin.sum_univ_succ]
  simp only [if_pos rfl, add_sub_cancel_right, abs_of_nonneg (Nat.cast_nonneg N),
    Fin.succ_ne_zero, if_false, zero_sub, abs_neg, abs_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- Fourier leakage for the explicit positive-frequency representation, including multiplicity. -/
def fejerFourierLeakage (N : ℕ) (w : ℝ → ℝ) : ℝ :=
  ((N : ℝ) + 1)⁻¹ * ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
    if i = j then 0 else ‖weightFourier w |(i : ℝ) - (j : ℝ)|‖

theorem tendsto_fejerFourierLeakage (N : ℕ) :
    Tendsto (fun ε => fejerFourierLeakage N (finiteSamplingWeight (rootSampleSites N) ε))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  have hterm (i j : Fin (N + 1)) : Tendsto
      (fun ε => if i = j then (0 : ℝ) else
        ‖weightFourier (finiteSamplingWeight (rootSampleSites N) ε) |(i : ℝ) - (j : ℝ)|‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    by_cases hij : i = j
    · simp only [if_pos hij]; exact tendsto_const_nhds
    · simp only [if_neg hij]
      have h := tendsto_finiteSamplingWeight_fourier (rootSampleSites N) |(i : ℝ) - (j : ℝ)|
      rw [rootSampleSites_difference_character N i j hij] at h
      simpa only [norm_zero] using h.norm
  have h := (tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hterm i j).const_mul ((N : ℝ) + 1)⁻¹
  simpa only [fejerFourierLeakage, Finset.sum_const_zero, mul_zero] using h

/-- No constant less than two can replace the floor coefficient, even with positive frequencies. -/
theorem exists_weight_violating_any_floor_coefficient_lt_two {c : ℝ} (hc : c < 2) :
    ∃ (N : ℕ) (w : ℝ → ℝ), 1 ≤ N ∧ Integrable w ∧ (∀ t, 0 ≤ w t) ∧
      (∀ t, -1 ≤ (fejerPositiveSum N t).re) ∧
      c * (∫ t, w t) + fejerFourierLeakage N w <
        ∫ t, w t * |(fejerPositiveSum N t).re| := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (c / (2 - c)))
  have hN1 : 1 ≤ N := by
    exact_mod_cast ((le_max_left 1 (c / (2 - c))).trans hN.le)
  have hgap : c * ((N : ℝ) + 1) < 2 * N := by
    have h := (div_lt_iff₀ (sub_pos.mpr hc)).mp ((le_max_right 1 _).trans_lt hN)
    nlinarith only [h]
  have hmass : Tendsto (fun ε => ∫ t, finiteSamplingWeight (rootSampleSites N) ε t)
      (𝓝[>] (0 : ℝ)) (𝓝 ((N : ℝ) + 1)) := by
    have h := tendsto_finiteSamplingWeight_integral (rootSampleSites N)
      (f := fun _ => (1 : ℝ)) continuous_const
    simpa using h
  have habs : Tendsto
      (fun ε => ∫ t, finiteSamplingWeight (rootSampleSites N) ε t * |(fejerPositiveSum N t).re|)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * N)) := by
    have hcont : Continuous (fun t => |(fejerPositiveSum N t).re|) := by
      simp only [fejerPositiveSum_re]
      exact ((_root_.HTGeometry.continuous_fejerKernel N).sub continuous_const).abs
    simpa only [smul_eq_mul, rootSampleSites_abs_fejerPositiveSum] using
      tendsto_finiteSamplingWeight_integral (rootSampleSites N) hcont
  have hcost : Tendsto (fun ε => c * (∫ t, finiteSamplingWeight (rootSampleSites N) ε t) +
      fejerFourierLeakage N (finiteSamplingWeight (rootSampleSites N) ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (c * ((N : ℝ) + 1))) := by
    simpa only [add_zero] using (hmass.const_mul c).add (tendsto_fejerFourierLeakage N)
  let M : ℝ := (c * ((N : ℝ) + 1) + 2 * N) / 2
  have hlo : c * ((N : ℝ) + 1) < M := by dsimp [M]; linarith only [hgap]
  have hhi : M < 2 * N := by dsimp [M]; linarith only [hgap]
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hlow, hhigh⟩ := (hpos.and
    ((hcost.eventually_lt_const hlo).and (habs.eventually (Ioi_mem_nhds hhi)))).exists
  exact ⟨N, finiteSamplingWeight (rootSampleSites N) ε, hN1,
    integrable_finiteSamplingWeight (rootSampleSites N) ε,
    finiteSamplingWeight_nonneg (rootSampleSites N) hε,
    fejerPositiveSum_floor N, hlow.trans hhigh⟩

#print axioms fejerPositiveSum_floor
#print axioms exists_weight_violating_any_floor_coefficient_lt_two

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
