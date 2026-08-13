import GaloisForLFunctions.HTGeometry.VerticallyNegligible
import GaloisForLFunctions.HTGeometry.GammaShiftTubeDatumAlgebra

/-!
# Rational functions on a vertical tube

A nonzero polynomial has an exact leading order on a vertical line, so it is never negligible, and
its modulus is bounded below by a power of the height uniformly on every tube.  Consequently a
rational function has polynomial tube growth, and is negligible only if its numerator vanishes.

These are the growth inputs of the negligible-ideal argument: the eliminator needs the coefficient
field to act by polynomially bounded multipliers and to contain no negligible nonzero element.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The trivial-degree shape has modulus at least one on a vertical line. -/
theorem one_le_norm_shape_natDegree (σ : ℝ) (n : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    1 ≤ ‖gammaShiftShape 0 σ 0 ((n : ℕ) : ℝ) 0 t‖ := by
  have hval : gammaShiftShape 0 σ 0 ((n : ℕ) : ℝ) 0 t
      = ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (((n : ℕ) : ℝ) : ℂ) := by
    rw [gammaShiftShape]
    simp
  rw [hval, norm_cpow_real_vertical]
  have hge : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := norm_vertical_ge_height σ t
  have h1 : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := le_trans ht hge
  rw [Real.rpow_natCast]
  exact one_le_pow₀ h1

/-- Negligibility only depends on the values at large height. -/
theorem IsVerticallyNegligible.congr_eventually {f g : ℂ → ℂ} (hf : IsVerticallyNegligible f)
    (T₀ : ℝ) (hfg : ∀ σ t : ℝ, 0 < σ → T₀ ≤ t →
      g ((σ : ℂ) + (t : ℂ) * Complex.I) = f ((σ : ℂ) + (t : ℂ) * Complex.I)) :
    IsVerticallyNegligible g := by
  intro M hM N
  obtain ⟨C, T, hC, hT, hb⟩ := hf M hM N
  refine ⟨C, max T (max T₀ 2), hC, le_trans hT (le_max_left _ _), fun σ t hσ hσM ht => ?_⟩
  have ht₁ : T ≤ t := le_trans (le_max_left _ _) ht
  have ht₀ : T₀ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  rw [hfg σ t hσ ht₀]
  exact hb σ t hσ hσM ht₁

/-- **A nonzero polynomial is not vertically negligible.** -/
theorem not_isVerticallyNegligible_polyEval {q : Polynomial ℂ} (hq : q ≠ 0) :
    ¬ IsVerticallyNegligible (fun z => q.eval z) := by
  intro hneg
  obtain ⟨hlc, hlim⟩ := hasShiftDatum_poly (lam := 0) (σ := 1) (by norm_num) hq
  obtain ⟨C, T, hC, hT, hb⟩ := hneg 1 (by norm_num) 1
  have hzero : Tendsto (fun t : ℝ => ‖q.eval ((1 : ℂ) + (t : ℂ) * Complex.I)
      / gammaShiftShape 0 1 0 ((q.natDegree : ℕ) : ℝ) 0 t‖) atTop (nhds 0) := by
    refine squeeze_zero' (g := fun t : ℝ => C / t)
      (by filter_upwards with t using norm_nonneg _) ?_ ?_
    · filter_upwards [eventually_ge_atTop (max T 1)] with t ht
      have htT : T ≤ t := le_trans (le_max_left _ _) ht
      have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
      have hshape := one_le_norm_shape_natDegree 1 q.natDegree ht1
      have hnum := hb 1 t (by norm_num) le_rfl htT
      rw [norm_div]
      have hpos : (0 : ℝ) < ‖gammaShiftShape 0 1 0 ((q.natDegree : ℕ) : ℝ) 0 t‖ := by linarith
      rw [div_le_iff₀ hpos]
      have hCt : C / t ^ 1 ≤ C / t ^ 1 := le_rfl
      calc ‖q.eval ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / t ^ 1 := hnum
        _ = C / t := by ring
        _ ≤ (C / t) * ‖gammaShiftShape 0 1 0 ((q.natDegree : ℕ) : ℝ) 0 t‖ := by
            have hCt0 : (0 : ℝ) ≤ C / t := by positivity
            nlinarith
    · have hlimit : Tendsto (fun t : ℝ => C / t) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      exact hlimit
  have hnorm := hlim.norm
  have hval := tendsto_nhds_unique hnorm hzero
  exact hlc (norm_eq_zero.mp hval)


/-- **A nonzero polynomial is bounded below by a power of the height on every tube.** -/
theorem exists_lower_bound_polyEval {M : ℝ} {q : Polynomial ℂ} (hq : q ≠ 0) :
    ∃ c T : ℝ, 0 < c ∧ 2 ≤ T ∧ ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t →
      c * t ^ q.natDegree ≤ ‖q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨hlc, htube⟩ := hasShiftTubeDatum_poly (M := M) (lam := 0) hq
  have hlcpos : (0 : ℝ) < ‖q.leadingCoeff‖ := norm_pos_iff.mpr hlc
  obtain ⟨T, hT⟩ := htube (‖q.leadingCoeff‖ / 2) (by positivity)
  refine ⟨‖q.leadingCoeff‖ / 2, max T 2, by positivity, le_max_right _ _,
    fun σ t hσ hσM ht => ?_⟩
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have ht2 : (2 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hstep := hT σ t hσ hσM htT
  simp only at hstep
  have hshapepos : (0 : ℝ) < ‖gammaShiftShape 0 σ 0 ((q.natDegree : ℕ) : ℝ) 0 t‖ := by
    have := one_le_norm_shape_natDegree σ q.natDegree ht1
    linarith
  have hratio : ‖q.leadingCoeff‖ / 2
      ≤ ‖q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / gammaShiftShape 0 σ 0 ((q.natDegree : ℕ) : ℝ) 0 t‖ := by
    have hrev := norm_sub_norm_le q.leadingCoeff
      (q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        / gammaShiftShape 0 σ 0 ((q.natDegree : ℕ) : ℝ) 0 t)
    rw [norm_sub_rev] at hrev
    linarith
  have hshapege : t ^ q.natDegree ≤ ‖gammaShiftShape 0 σ 0 ((q.natDegree : ℕ) : ℝ) 0 t‖ := by
    have hval : gammaShiftShape 0 σ 0 ((q.natDegree : ℕ) : ℝ) 0 t
        = ((σ : ℂ) + (t : ℂ) * Complex.I) ^ ((((q.natDegree : ℕ) : ℝ)) : ℂ) := by
      rw [gammaShiftShape]
      simp
    rw [hval, norm_cpow_real_vertical, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) (norm_vertical_ge_height σ t) _
  rw [norm_div, le_div_iff₀ hshapepos] at hratio
  calc ‖q.leadingCoeff‖ / 2 * t ^ q.natDegree
      ≤ ‖q.leadingCoeff‖ / 2 * ‖gammaShiftShape 0 σ 0 ((q.natDegree : ℕ) : ℝ) 0 t‖ := by
        refine mul_le_mul_of_nonneg_left hshapege (by positivity)
    _ ≤ ‖q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := hratio

/-- A rational function has polynomial tube growth. -/
theorem hasTubePolyGrowth_ratEval (p : Polynomial ℂ) {q : Polynomial ℂ} (hq : q ≠ 0) :
    HasTubePolyGrowth (fun z => p.eval z / q.eval z) := by
  intro M hM
  obtain ⟨m, C, T₁, hC, hT₁, hb⟩ := hasTubePolyGrowth_polyEval p M hM
  obtain ⟨c, T₂, hc, hT₂, hlow⟩ := exists_lower_bound_polyEval hq
  refine ⟨m, C / c, max T₁ T₂, by positivity, le_trans hT₁ (le_max_left _ _),
    fun σ t hσ hσM ht => ?_⟩
  have ht₁ : T₁ ≤ t := le_trans (le_max_left _ _) ht
  have ht₂ : T₂ ≤ t := le_trans (le_max_right _ _) ht
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hbp := hb σ t hσ hσM ht₁
  have hlowq := hlow σ t hσ hσM ht₂
  have hqpow : (1 : ℝ) ≤ t ^ q.natDegree := one_le_pow₀ ht1
  have hqpos : (0 : ℝ) < ‖q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    have : (0 : ℝ) < c * t ^ q.natDegree := by positivity
    linarith
  rw [norm_div, div_le_iff₀ hqpos]
  have hcle : c ≤ ‖q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    nlinarith
  calc ‖p.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * t ^ m := hbp
    _ = (C / c) * t ^ m * c := by field_simp
    _ ≤ (C / c) * t ^ m * ‖q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
        refine mul_le_mul_of_nonneg_left hcle (by positivity)

/-- Beyond a height a nonzero polynomial has no zeros on any vertical line. -/
theorem exists_height_polyEval_ne_zero {q : Polynomial ℂ} (hq : q ≠ 0) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ σ t : ℝ, T ≤ t → q.eval ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  classical
  have hfin : (Complex.im '' {x : ℂ | q.IsRoot x}).Finite :=
    (Polynomial.finite_setOf_isRoot hq).image _
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨max B 2 + 1, by
      have : (2 : ℝ) ≤ max B 2 := le_max_right _ _
      linarith, fun σ t ht h0 => ?_⟩
  have hroot : q.IsRoot ((σ : ℂ) + (t : ℂ) * Complex.I) := h0
  have hmem : t ∈ Complex.im '' {x : ℂ | q.IsRoot x} := by
    refine ⟨(σ : ℂ) + (t : ℂ) * Complex.I, hroot, ?_⟩
    simp
  have hle : t ≤ B := hB hmem
  have hB2 : B ≤ max B 2 := le_max_left _ _
  linarith

/-- **A rational function with nonzero numerator is not vertically negligible.** -/
theorem not_isVerticallyNegligible_ratEval {p q : Polynomial ℂ} (hp : p ≠ 0) (hq : q ≠ 0) :
    ¬ IsVerticallyNegligible (fun z => p.eval z / q.eval z) := by
  intro hneg
  obtain ⟨T, hT, hne⟩ := exists_height_polyEval_ne_zero hq
  have hmul := hneg.mul_polyGrowth (hasTubePolyGrowth_polyEval q)
  refine not_isVerticallyNegligible_polyEval hp ?_
  refine hmul.congr_eventually T ?_
  intro σ t hσ ht
  have hqne : q.eval ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := hne σ t ht
  field_simp

end

end GaloisForLFunctions.HTGeometry
