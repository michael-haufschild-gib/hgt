import GaloisForLFunctions.HTGeometry.ShiftedDigammaExpansionVertical

/-!
# Vertically negligible functions

A function is vertically negligible when, on every vertical tube, it decays faster than any power of
the height.  The negligible functions form a shift-stable module over the functions of polynomial
tube growth, which is exactly the closure structure the Hölder eliminator consumes: a polynomial in
the digamma jets whose value is negligible will be forced to vanish.

This module sets up the notion and its closure properties.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Decay faster than any power of the height, uniformly on every vertical tube. -/
def IsVerticallyNegligible (f : ℂ → ℂ) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ N : ℕ, ∃ C T : ℝ, 0 ≤ C ∧ 2 ≤ T ∧
    ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t → ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / t ^ N

/-- Polynomial growth in the height, uniformly on every vertical tube. -/
def HasTubePolyGrowth (g : ℂ → ℂ) : Prop :=
  ∀ M : ℝ, 0 < M → ∃ (m : ℕ) (C T : ℝ), 0 ≤ C ∧ 2 ≤ T ∧
    ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t → ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * t ^ m

theorem isVerticallyNegligible_zero : IsVerticallyNegligible (fun _ => 0) := by
  intro M _ N
  refine ⟨0, 2, le_rfl, le_rfl, fun σ t _ _ ht => ?_⟩
  simp

theorem IsVerticallyNegligible.add {f g : ℂ → ℂ} (hf : IsVerticallyNegligible f)
    (hg : IsVerticallyNegligible g) : IsVerticallyNegligible (fun z => f z + g z) := by
  intro M hM N
  obtain ⟨C₁, T₁, hC₁, hT₁, hb₁⟩ := hf M hM N
  obtain ⟨C₂, T₂, hC₂, hT₂, hb₂⟩ := hg M hM N
  refine ⟨C₁ + C₂, max T₁ T₂, by positivity, le_trans hT₁ (le_max_left _ _),
    fun σ t hσ hσM ht => ?_⟩
  have ht₁ : T₁ ≤ t := le_trans (le_max_left _ _) ht
  have ht₂ : T₂ ≤ t := le_trans (le_max_right _ _) ht
  calc ‖f ((σ : ℂ) + (t : ℂ) * Complex.I) + g ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ + ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
        norm_add_le _ _
    _ ≤ C₁ / t ^ N + C₂ / t ^ N := add_le_add (hb₁ σ t hσ hσM ht₁) (hb₂ σ t hσ hσM ht₂)
    _ = (C₁ + C₂) / t ^ N := by ring

theorem IsVerticallyNegligible.neg {f : ℂ → ℂ} (hf : IsVerticallyNegligible f) :
    IsVerticallyNegligible (fun z => -f z) := by
  intro M hM N
  obtain ⟨C, T, hC, hT, hb⟩ := hf M hM N
  refine ⟨C, T, hC, hT, fun σ t hσ hσM ht => ?_⟩
  rw [norm_neg]
  exact hb σ t hσ hσM ht

theorem IsVerticallyNegligible.sub {f g : ℂ → ℂ} (hf : IsVerticallyNegligible f)
    (hg : IsVerticallyNegligible g) : IsVerticallyNegligible (fun z => f z - g z) := by
  have := hf.add hg.neg
  refine fun M hM N => ?_
  obtain ⟨C, T, hC, hT, hb⟩ := this M hM N
  refine ⟨C, T, hC, hT, fun σ t hσ hσM ht => ?_⟩
  have hval := hb σ t hσ hσM ht
  simpa [sub_eq_add_neg] using hval

/-- Negligibility is stable under the unit shift. -/
theorem IsVerticallyNegligible.shift {f : ℂ → ℂ} (hf : IsVerticallyNegligible f) :
    IsVerticallyNegligible (fun z => f (z + 1)) := by
  intro M hM N
  obtain ⟨C, T, hC, hT, hb⟩ := hf (M + 1) (by linarith) N
  refine ⟨C, T, hC, hT, fun σ t hσ hσM ht => ?_⟩
  have hpt : ((σ : ℂ) + (t : ℂ) * Complex.I) + 1 = ((σ + 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    push_cast
    ring
  show ‖f (((σ : ℂ) + (t : ℂ) * Complex.I) + 1)‖ ≤ C / t ^ N
  rw [hpt]
  exact hb (σ + 1) t (by linarith) (by linarith) ht

/-- Multiplying a negligible function by one of polynomial tube growth keeps it negligible. -/
theorem IsVerticallyNegligible.mul_polyGrowth {f g : ℂ → ℂ} (hf : IsVerticallyNegligible f)
    (hg : HasTubePolyGrowth g) : IsVerticallyNegligible (fun z => g z * f z) := by
  intro M hM N
  obtain ⟨m, C₁, T₁, hC₁, hT₁, hb₁⟩ := hg M hM
  obtain ⟨C₂, T₂, hC₂, hT₂, hb₂⟩ := hf M hM (N + m)
  refine ⟨C₁ * C₂, max T₁ T₂, by positivity, le_trans hT₁ (le_max_left _ _),
    fun σ t hσ hσM ht => ?_⟩
  have ht₁ : T₁ ≤ t := le_trans (le_max_left _ _) ht
  have ht₂ : T₂ ≤ t := le_trans (le_max_right _ _) ht
  have htpos : (0 : ℝ) < t := by linarith
  have hb₁' := hb₁ σ t hσ hσM ht₁
  have hb₂' := hb₂ σ t hσ hσM ht₂
  rw [norm_mul]
  have hstep : ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * ‖f ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (C₁ * t ^ m) * (C₂ / t ^ (N + m)) := by
    refine mul_le_mul hb₁' hb₂' (norm_nonneg _) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  rw [pow_add]
  field_simp

/-- A polynomial has polynomial tube growth. -/
theorem hasTubePolyGrowth_polyEval (q : Polynomial ℂ) :
    HasTubePolyGrowth (fun z => q.eval z) := by
  intro M hM
  refine ⟨q.natDegree, ∑ i ∈ Finset.range (q.natDegree + 1), ‖q.coeff i‖ * (M + 1) ^ i,
    2, by positivity, le_rfl, fun σ t hσ hσM ht => ?_⟩
  have htpos : (0 : ℝ) < t := by linarith
  have hz : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ (M + 1) * t := by
    have hre : |σ| ≤ M := by
      rw [abs_of_pos hσ]
      exact hσM
    have hnorm := Complex.norm_add_mul_I (σ : ℝ) (t : ℝ)
    rw [hnorm]
    have ht1 : (1 : ℝ) ≤ t := by linarith
    have hM2 : σ ^ 2 ≤ M ^ 2 := by nlinarith
    have ht2sq : (1 : ℝ) ≤ t ^ 2 := by nlinarith
    have h1 : M ^ 2 ≤ M ^ 2 * t ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg M) (sub_nonneg.mpr ht2sq)]
    have h2M : (0 : ℝ) ≤ 2 * M * t ^ 2 := by positivity
    have hsq : σ ^ 2 + t ^ 2 ≤ ((M + 1) * t) ^ 2 := by nlinarith [hM2, h1, h2M]
    calc Real.sqrt (σ ^ 2 + t ^ 2) ≤ Real.sqrt (((M + 1) * t) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = (M + 1) * t := by
          rw [Real.sqrt_sq (by positivity)]
  calc ‖q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ∑ i ∈ Finset.range (q.natDegree + 1),
          ‖q.coeff i‖ * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ i := by
        rw [Polynomial.eval_eq_sum_range]
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, norm_pow]
    _ ≤ ∑ i ∈ Finset.range (q.natDegree + 1), ‖q.coeff i‖ * ((M + 1) ^ i * t ^ q.natDegree) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hile : i ≤ q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hpow : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ i ≤ ((M + 1) * t) ^ i :=
          pow_le_pow_left₀ (norm_nonneg _) hz i
        have hti : ((M + 1) * t) ^ i = (M + 1) ^ i * t ^ i := by rw [mul_pow]
        have htmono : t ^ i ≤ t ^ q.natDegree := pow_le_pow_right₀ (by linarith) hile
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ i ≤ (M + 1) ^ i * t ^ i := by
              rw [← hti]; exact hpow
          _ ≤ (M + 1) ^ i * t ^ q.natDegree := by
              refine mul_le_mul_of_nonneg_left htmono (by positivity)
    _ = (∑ i ∈ Finset.range (q.natDegree + 1), ‖q.coeff i‖ * (M + 1) ^ i) * t ^ q.natDegree := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

end

end GaloisForLFunctions.HTGeometry
