import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCompositeHeckeTraceIsInvariantUnderTheModularGroup

/-!
# The composite Hecke trace is a theta-square multiple up to a bounded remainder

`G'_m = Tr_mθ_s − N(m)(2 + 2(p/q)₃)θ_s²` is a bounded remainder of multiplier `κ⁻¹` with `G'_m = O(v^{−7/3})` above
any height (`PrimaryPair.remainder_remainderData`):

* on the standard strip by `norm_remainder_strip`;
* at the ramified cusps every Hecke point of a point is ramified: `A_q^{±1}M = N'U` keeps the column residue modulo
  `3` (`q ≡ 1 mod 3`) and moves the height by `|g|²/|q| ≥ 1/|q|`, and then the prime statement at `p` applies
  (`sourceTheta_hecke_ramified`);
* the trace and `θ_s²` are invariant under `SL₂(ℤ)`, which with `Γ(3)` moves every point to the strip or to a
  ramified cusp.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPair

variable (R : PrimaryPair)

theorem sourceTrace_automorphy (M : levelThree) (w : HyperbolicSpace) :
    R.sourceTrace (complexMatrix M • w) = complexCharacter M ^ 2 * R.sourceTrace w :=
  R.heckeTrace_automorphy sourceTheta sourceTheta_automorphy M w

theorem sourceTrace_rational (r : SL(2, ℤ)) (w : HyperbolicSpace) :
    R.sourceTrace (integralComplexMatrix (rationalEmbedding r) • w) = R.sourceTrace w :=
  R.heckeTrace_rational sourceTheta sourceTheta_automorphy sourceTheta_rational_inv r w

theorem remainder_rationalExtension (G : rationalExtension) (w : HyperbolicSpace) :
    R.remainder (integralComplexMatrix (G : SL(2, O)) • w) = extendedComplexCharacter G ^ 2 * R.remainder w := by
  obtain ⟨n, r, hG⟩ := G.2
  have hρ : extendedComplexCharacter G = complexCharacter n := rationalExtensionValue_of_product G n r hG
  have hw : integralComplexMatrix (G : SL(2, O)) • w =
      complexMatrix n • (integralComplexMatrix (rationalEmbedding r) • w) := by
    rw [← hG, map_mul, mul_smul]
    rfl
  have hθ := cubicSourceResidualFunction_automorphy G w
  unfold remainder
  rw [show sourceTheta (integralComplexMatrix (G : SL(2, O)) • w) = extendedComplexCharacter G * sourceTheta w from hθ,
    hw, R.sourceTrace_automorphy, R.sourceTrace_rational, hρ]
  ring

theorem norm_remainder_rational (G : rationalExtension) (w : HyperbolicSpace) :
    ‖R.remainder (integralComplexMatrix (G : SL(2, O)) • w)‖ = ‖R.remainder w‖ := by
  rw [R.remainder_rationalExtension, norm_mul, norm_pow, norm_extendedComplexCharacter, one_pow, one_mul]

/-! ### The ramified cusps -/

/-- **The composite Hecke points of a ramified point are ramified**: `θ_s` is bounded there. -/
theorem sourceTheta_hecke_ramified (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : SL(2, O)), colRes (M 0 0) (M 1 0) ≠ 0 →
      ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
        ‖sourceTheta (R.dilation • integralComplexMatrix M • upperPoint z v hv)‖ ≤ C ∧
        ‖sourceTheta (R.contraction • integralComplexMatrix M • upperPoint z v hv)‖ ≤ C := by
  have hq := R.Q.norm_pos
  obtain ⟨C, β, hC, hβ, hP⟩ := R.P.sourceTheta_hecke_ramified (a / ‖ringComplex R.Q.p‖) (div_pos ha hq)
  have hex : ∀ v : ℝ, 0 ≤ v → C * Real.exp (-(β / ‖ringComplex R.P.p‖) * v) ≤ C := fun v hv => by
    have : Real.exp (-(β / ‖ringComplex R.P.p‖) * v) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := div_pos hβ R.P.norm_pos
      nlinarith
    nlinarith
  have hlow : ∀ (g : O) (U : SL(2, ℂ)), g ≠ 0 → U 1 0 = 0 →
      ‖U 0 0‖ ^ 2 = ‖ringComplex g‖ ^ 2 / ‖ringComplex R.Q.p‖ → ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ∃ (z' : ℂ) (v' : ℝ) (hv' : 0 < v'), upperPoint z' v' hv' = U • upperPoint z v hv ∧
        a / ‖ringComplex R.Q.p‖ ≤ v' := by
    intro g U hg hU10 hU00 z v hv hav
    have hg1 := one_le_norm_sq_ringComplex hg
    obtain ⟨z', v', hv', hpt⟩ := upperPoint_surjective (U • upperPoint z v hv)
    have hvv : v' = v * (‖ringComplex g‖ ^ 2 / ‖ringComplex R.Q.p‖) := by
      have h := height_upper_triangular_complex U hU10 z v hv
      rw [← hpt, hyperbolicHeight_upperPoint, hU00] at h
      exact h
    refine ⟨z', v', hv', hpt, ?_⟩
    rw [hvv, mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hq.le
  refine ⟨C, hC, fun M hcol z v hv hav => ⟨?_, ?_⟩⟩
  · obtain ⟨N', g, hg, hp, hq', U, hU10, hU00, hfac⟩ := R.Q.dilation_factor M
    have hc : colRes (N' 0 0) (N' 1 0) ≠ 0 :=
      colRes_ne_zero_of_factor hp hq' (by rw [R.Q.colRes_p_left]; exact hcol)
    obtain ⟨z', v', hv', hpt, hav'⟩ := hlow g U hg hU10 hU00 z v hv hav
    rw [dilation, mul_smul, ← mul_smul R.Q.dilation, hfac, mul_smul, ← hpt]
    exact ((hP N' hc z' v' hv' hav').1).trans (hex v' hv'.le)
  · obtain ⟨N', g, hg, hp, hq', U, hU10, hU00, hfac⟩ := R.Q.contraction_factor M
    have hc : colRes (N' 0 0) (N' 1 0) ≠ 0 :=
      colRes_ne_zero_of_factor hp hq' (by rw [R.Q.colRes_p_right]; exact hcol)
    obtain ⟨z', v', hv', hpt, hav'⟩ := hlow g U hg hU10 hU00 z v hv hav
    rw [contraction, mul_smul, ← mul_smul R.Q.contraction, hfac, mul_smul, ← hpt]
    exact ((hP N' hc z' v' hv' hav').2).trans (hex v' hv'.le)

/-- **`G'_m` is bounded at the ramified cusps.** -/
theorem norm_remainder_ramified (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (j : Fin 3), j ≠ 0 → ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), a ≤ v →
      ‖R.remainder (integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)‖ ≤ K := by
  obtain ⟨C, hC, hhecke⟩ := R.sourceTheta_hecke_ramified a ha
  obtain ⟨C', β', hC', hβ', hram⟩ := sourceTheta_ramified_decay a ha
  set N : ℝ := (Fintype.card R.Index : ℝ)
  refine ⟨N * C ^ 2 + ‖R.growth‖ * C' ^ 2, by positivity, fun j hj z v hv hav => ?_⟩
  set x := upperPoint z v hv
  set w := integralComplexMatrix (cuspRepresentative j) • x
  have he' : Real.exp (-β' * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hθ : ‖sourceTheta w‖ ≤ C' := (hram _ (colRes_cuspRepresentative j hj) z v hv hav).trans (by nlinarith)
  have hterm : ∀ ij : R.Index, ‖(complexCharacter (R.rep ij) ^ 2)⁻¹ *
      R.heckeCorrelation sourceTheta (complexMatrix (R.rep ij) • w)‖ ≤ C ^ 2 := by
    intro ij
    have hcol : colRes ((((R.rep ij : levelThree) : SL(2, O)) * cuspRepresentative j) 0 0)
        ((((R.rep ij : levelThree) : SL(2, O)) * cuspRepresentative j) 1 0) ≠ 0 := by
      rw [colRes_levelThree_mul]
      exact colRes_cuspRepresentative j hj
    have hpt : complexMatrix (R.rep ij) • w =
        integralComplexMatrix (((R.rep ij : levelThree) : SL(2, O)) * cuspRepresentative j) • x := by
      rw [map_mul, mul_smul]
      rfl
    obtain ⟨h1, h2⟩ := hhecke _ hcol z v hv hav
    rw [norm_mul, norm_inv, norm_pow, norm_complexCharacter, one_pow, inv_one, one_mul, heckeCorrelation, hpt,
      norm_mul, sq]
    exact mul_le_mul h1 h2 (norm_nonneg _) hC
  have htr : ‖R.sourceTrace w‖ ≤ N * C ^ 2 := by
    rw [sourceTrace, R.heckeTrace_eq_sum sourceTheta sourceTheta_automorphy]
    exact PrimaryPair.norm_sum_le_card _ hterm
  rw [remainder]
  refine (norm_sub_le _ _).trans (add_le_add htr ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hθ 2) (norm_nonneg _)

/-! ### Boundedness and square integrability -/

/-- **`G'_m` is bounded on hyperbolic three-space.** -/
theorem remainder_bounded : ∃ B : ℝ, ∀ w : HyperbolicSpace, ‖R.remainder w‖ ≤ B := by
  set a₀ := Real.sqrt (2 / 3)
  have ha₀ : 0 < a₀ := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨K₀, hK₀, hstrip⟩ := R.norm_remainder_strip a₀ ha₀
  obtain ⟨K₁, hK₁, hram⟩ := R.norm_remainder_ramified a₀ ha₀
  refine ⟨K₀ * a₀ ^ (-(7 : ℝ) / 3) + K₁, fun w => ?_⟩
  obtain ⟨M, z, v, hv, hMw, -, hfloor⟩ := bianchi_reduction_height_floor w
  obtain ⟨G', j, T, hT, -, hu1, hdec'⟩ := three_cusp_decomposition M⁻¹
  have hw : w = integralComplexMatrix (G' : SL(2, O)) •
      (integralComplexMatrix (cuspRepresentative j * T) • upperPoint z v hv) := by
    rw [← mul_smul, ← map_mul, ← mul_assoc, ← hdec', ← hMw, ← mul_smul, ← map_mul, inv_mul_cancel,
      map_one, one_smul]
  rw [hw, R.norm_remainder_rational]
  obtain ⟨z', v', hv', hp⟩ := upperPoint_surjective (integralComplexMatrix T • upperPoint z v hv)
  have hvv : v' = v := by
    have h := height_upperTriangular T hT hu1 z v hv
    rw [← hp, hyperbolicHeight_upperPoint] at h
    exact h
  subst hvv
  rw [map_mul, mul_smul, ← hp]
  by_cases hj : j = 0
  · subst hj
    have hc1 : cuspRepresentative 0 = 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [cuspRepresentative, cuspParameter, lowerCuspMatrix]
    rw [hc1, map_one, one_smul]
    refine (hstrip z' v' hv' hfloor).trans ?_
    have : v' ^ (-(7 : ℝ) / 3) ≤ a₀ ^ (-(7 : ℝ) / 3) := Real.rpow_le_rpow_of_nonpos ha₀ hfloor (by norm_num)
    nlinarith
  · exact (hram j hj z' v' hv' hfloor).trans (by nlinarith [Real.rpow_nonneg ha₀.le (-(7 : ℝ) / 3)])

theorem sourceTrace_continuous : Continuous R.sourceTrace := by
  have h : R.sourceTrace = fun w => ∑ ij : R.Index,
      (complexCharacter (R.rep ij) ^ 2)⁻¹ * R.heckeCorrelation sourceTheta (complexMatrix (R.rep ij) • w) :=
    funext (R.heckeTrace_eq_sum sourceTheta sourceTheta_automorphy)
  rw [h]
  refine continuous_finsetSum _ fun ij _ => continuous_const.mul ?_
  unfold heckeCorrelation
  exact (cubicSourceResidualFunction_continuous.comp
      ((continuous_hyperbolic_action _).comp (continuous_hyperbolic_action _))).mul
    (cubicSourceResidualFunction_continuous.comp
      ((continuous_hyperbolic_action _).comp (continuous_hyperbolic_action _)))

theorem remainder_continuous : Continuous R.remainder :=
  R.sourceTrace_continuous.sub (continuous_const.mul (cubicSourceResidualFunction_continuous.pow 2))

theorem remainder_memLp : MemLp R.remainder 2 (hyperbolicVolume.restrict levelSet) := by
  haveI : IsFiniteMeasure (hyperbolicVolume.restrict levelSet) :=
    isFiniteMeasure_restrict.mpr levelSet_volume_lt_top.ne
  obtain ⟨B, hB⟩ := R.remainder_bounded
  exact MemLp.of_bound R.remainder_continuous.measurable.aestronglyMeasurable B (Eventually.of_forall hB)

theorem remainder_automorphy (M : levelThree) (w : HyperbolicSpace) :
    R.remainder (complexMatrix M • w) = (complexCharacter M)⁻¹ * R.remainder w := by
  rw [remainder, remainder, R.sourceTrace_automorphy, sourceTheta_automorphy, ← complexCharacter_sq_eq_inv]
  ring

/-- **`G'_m` is a bounded remainder.** -/
theorem remainder_remainderData : RemainderData R.remainder where
  automorphy := R.remainder_automorphy
  measurable := R.remainder_continuous.measurable
  bounded := R.remainder_bounded
  high := R.norm_remainder_strip 2 two_pos
  memLp := R.remainder_memLp

end PrimaryPair

end GaloisForLFunctions.OrderSixMetaplecticTheory
