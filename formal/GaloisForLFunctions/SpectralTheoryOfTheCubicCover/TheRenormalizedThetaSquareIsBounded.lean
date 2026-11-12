import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRationalCuspSubtractionScatters
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheMellinTransformOfTheThetaSquareReadsItsDirichletSeries

/-!
# The renormalized theta square is bounded

With `c = 3π r` the constant-term coefficient of `θ_s` (`b(v, 0) = c v^{2/3}`) and
`H = H_{[2,∞)}` the rational cusp subtraction, the function

`G = θ_s² − H`   (`renormalizedThetaSq`)

has the multiplier `κ⁻¹` (`renormalizedThetaSq_automorphy`), is bounded on all of hyperbolic
three-space (`renormalizedThetaSq_bounded`), hence square integrable on `D_Γ`
(`renormalizedThetaSq_memLp`), is `O(v^{−7/3})` high on the standard strip
(`norm_renormalizedThetaSq_high`), and its constant term is
`a₀(G)(v) = |P| (c² v^{4/3} + R(v)) − a₀(H)(v)` (`cuspConstantTerm_renormalized`).

Boundedness: reduce `w` to height `≥ √(2/3)` (Bianchi), split the reducing matrix as
`G' c_j T` (`three_cusp_decomposition`); `|G|` is invariant under the rational extension
(`norm_renormalizedThetaSq_rational`, `κ̃³ = 1`). For `j = 0` the point sits on the standard strip,
where `H = c² f(v)` and `θ_s − c v^{2/3} = O(v^{−3})`; for `j = 1, 2` the theta function is
exponentially small at the ramified cusp and `H` vanishes: every coset lifts the point to height
`≤ 1/v`, because the bottom-left entry of `N r c_j T` (`N ∈ Γ`, `r ∈ SL₂(ℤ)`) is `≢ 0 mod 3`
(`lowerLeft_ramified_ne_zero`: `r₁₀ + r₁₁ ω^j ≡ 0 mod 3` forces `3 ∣ r₁₀, r₁₁`).
-/

noncomputable section

open MeasureTheory Filter Function
open scoped BigOperators Classical MatrixGroups ComplexConjugate

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- The constant-term coefficient `c = 3π r` of `θ_s`. -/
abbrev thetaCoeff : ℂ := 3 * (Real.pi : ℂ) * constantArithmeticResidue

/-- The rational cusp subtraction of `θ_s²`. -/
abbrev thetaSubtraction : HyperbolicSpace → ℂ := cuspSubtraction thetaCoeff (Set.Ici 2)

/-- `G = θ_s² − H`. -/
def renormalizedThetaSq (w : HyperbolicSpace) : ℂ := sourceTheta w ^ 2 - thetaSubtraction w

theorem renormalizedThetaSq_automorphy (M : levelThree) (w : HyperbolicSpace) :
    renormalizedThetaSq (complexMatrix M • w) = (complexCharacter M)⁻¹ * renormalizedThetaSq w := by
  rw [renormalizedThetaSq, renormalizedThetaSq, sourceThetaSq_automorphy]
  dsimp only [thetaSubtraction]
  rw [cuspSubtraction_automorphy]
  ring

theorem renormalizedThetaSq_measurable : Measurable renormalizedThetaSq :=
  (cubicSourceResidualFunction_continuous.measurable.pow_const 2).sub
    (cuspSubtraction_measurable _ _ measurableSet_Ici)

/-! ### Rational equivariance -/

theorem cutoff_T_invariant (F : ℝ → ℂ) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 F (rationalComplex ModularGroup.T • w) = cuspCutoffCorrection 1 F w := by
  have he : rationalUnipotent (1 : ℤ) = ModularGroup.T := by
    simpa only [Nat.cast_one, pow_one] using rationalUnipotent_nat 1
  rw [← he]
  exact cuspCutoffCorrection_unipotent 1 1 F w

/-- `H_S = 4 c² conj(P E_1(· ∣ f_S))` with `P` the rational source projection. -/
theorem cuspSubtraction_eq_projection (c : ℂ) (S : Set ℝ) (w : HyperbolicSpace) :
    cuspSubtraction c S w =
      4 * c ^ 2 * conj (rationalSourceProjection (cuspCutoffCorrection 1 (growthProfile S)) w) := by
  rw [rationalSourceProjection_four_cusps _ (fun n w => cuspCutoffCorrection_automorphy 1 le_rfl _ n w)
    (cutoff_T_invariant _) (cuspCutoffCorrection_S_sq 1 _)]
  have h := fourCuspAverage_eq_sum (cuspCutoffCorrection 1 (growthProfile S)) 1 w
  simp only [one_smul, mul_one] at h
  rw [h, cuspSubtraction, map_mul, map_inv₀, map_sum, map_ofNat]
  field_simp

theorem conj_extendedComplexCharacter (g : rationalExtension) :
    conj (extendedComplexCharacter g) = extendedComplexCharacter g ^ 2 := by
  have h1 := norm_extendedComplexCharacter g
  have h3 := extendedComplexCharacter_cube g
  have hne : extendedComplexCharacter g ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  rw [← Complex.inv_eq_conj h1]
  have hm : extendedComplexCharacter g * extendedComplexCharacter g ^ 2 = 1 := by
    rw [← h3]
    ring
  exact (eq_inv_of_mul_eq_one_right hm).symm

theorem thetaSubtraction_rational (g : rationalExtension) (w : HyperbolicSpace) :
    thetaSubtraction (integralComplexMatrix (g : SL(2, O)) • w) =
      extendedComplexCharacter g ^ 2 * thetaSubtraction w := by
  dsimp only [thetaSubtraction]
  rw [cuspSubtraction_eq_projection, cuspSubtraction_eq_projection,
    rationalSourceProjection_automorphy _ (fun n w => cuspCutoffCorrection_automorphy 1 le_rfl _ n w) g w,
    map_mul, conj_extendedComplexCharacter]
  ring

theorem norm_renormalizedThetaSq_rational (g : rationalExtension) (w : HyperbolicSpace) :
    ‖renormalizedThetaSq (integralComplexMatrix (g : SL(2, O)) • w)‖ = ‖renormalizedThetaSq w‖ := by
  have h : renormalizedThetaSq (integralComplexMatrix (g : SL(2, O)) • w) =
      extendedComplexCharacter g ^ 2 * renormalizedThetaSq w := by
    rw [renormalizedThetaSq, renormalizedThetaSq, sourceTheta, cubicSourceResidualFunction_automorphy,
      thetaSubtraction_rational]
    ring
  rw [h, norm_mul, norm_pow, norm_extendedComplexCharacter, one_pow, one_mul]

/-! ### Heights through the ramified cusps -/

theorem cuspResidue_of_three_dvd {x : O} (h : (3 : O) ∣ x) : cuspResidue x = (0, 0) := by
  obtain ⟨y, rfl⟩ := h
  have h3 : (3 : O) = ((3 : ℤ) : O) := by norm_num
  rw [cuspResidue_mul, h3, cuspResidue_intCast]
  have h30 : (3 : ZMod 3) = 0 := rfl
  simp [cuspResidueMul, h30]

/-- `r₁₀ + r₁₁ ω^j ≢ 0 mod 3` for `j = 1, 2`. -/
theorem cuspResidue_ramified_ne (r : SL(2, ℤ)) (j : Fin 3) (hj : j ≠ 0) :
    cuspResidue (((r 1 0 : ℤ) : O) + ((r 1 1 : ℤ) : O) * cuspParameter j) ≠ (0, 0) := by
  intro h
  rw [cuspResidue_add, cuspResidue_mul, cuspResidue_intCast, cuspResidue_intCast,
    cuspParameter_residue] at h
  have hdet : ((r 0 0 * r 1 1 - r 0 1 * r 1 0 : ℤ) : ZMod 3) = 1 := by
    have hd := r.property
    rw [Matrix.det_fin_two] at hd
    rw [hd, Int.cast_one]
  push_cast at hdet
  fin_cases j
  · exact hj rfl
  · simp only [cuspResidueParameter, cuspResidueMul, Prod.mk.injEq] at h
    norm_num at h
    rw [h.1, h.2] at hdet
    simp at hdet
  · simp only [cuspResidueParameter, cuspResidueMul, Prod.mk.injEq] at h
    norm_num at h
    have h11 : ((r 1 1 : ℤ) : ZMod 3) = 0 := h.2
    have h10 : ((r 1 0 : ℤ) : ZMod 3) = 0 := by linear_combination h.1 + h.2
    rw [h10, h11] at hdet
    simp at hdet

/-- Through a ramified cusp `c_j T`, no coset of `Γ∞\Γ` has bottom-left entry zero. -/
theorem lowerLeft_ramified_ne_zero (N : levelThree) (r : SL(2, ℤ)) (j : Fin 3) (hj : j ≠ 0)
    (T : SL(2, O)) (hT : T 1 0 = 0) (hu : IsUnit (T 0 0)) :
    ((N : SL(2, O)) * (rationalEmbedding r * cuspRepresentative j * T)) 1 0 ≠ 0 := by
  set g := rationalEmbedding r * cuspRepresentative j * T
  have hg10 : g 1 0 = (((r 1 0 : ℤ) : O) + ((r 1 1 : ℤ) : O) * cuspParameter j) * T 0 0 := by
    simp [g, Matrix.mul_apply, Fin.sum_univ_two, cuspRepresentative, lowerCuspMatrix, hT,
      rationalEmbedding]
  have hNg : ((N : SL(2, O)) * g) 1 0 = (N : SL(2, O)) 1 0 * g 0 0 + (N : SL(2, O)) 1 1 * g 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨a, ha⟩ := levelThree_lower N
  have hb' := levelThree_entry N 1 1
  simp only [if_true] at hb'
  obtain ⟨b, hb⟩ := hb'
  intro h0
  rw [hNg] at h0
  have h3 : (3 : O) ∣ g 1 0 := ⟨-(a * g 0 0) - b * g 1 0, by
    linear_combination h0 - g 0 0 * ha - g 1 0 * hb⟩
  obtain ⟨u, hu'⟩ := hu.exists_right_inv
  have h3' : (3 : O) ∣ ((r 1 0 : ℤ) : O) + ((r 1 1 : ℤ) : O) * cuspParameter j := by
    obtain ⟨k, hk⟩ := h3
    refine ⟨k * u, ?_⟩
    rw [hg10] at hk
    calc ((r 1 0 : ℤ) : O) + ((r 1 1 : ℤ) : O) * cuspParameter j
        = (((r 1 0 : ℤ) : O) + ((r 1 1 : ℤ) : O) * cuspParameter j) * (T 0 0 * u) := by rw [hu', mul_one]
      _ = 3 * (k * u) := by rw [← mul_assoc, hk, mul_assoc]
  exact cuspResidue_ramified_ne r j hj (cuspResidue_of_three_dvd h3')

theorem norm_ringComplex_unit {u : O} (hu : IsUnit u) : ‖ringComplex u‖ = 1 := by
  obtain ⟨u', hu'⟩ := hu.exists_right_inv
  have h := congrArg (fun t => Complex.normSq (ringComplex t)) hu'
  simp only [map_mul, map_one] at h
  have h1 := one_le_normSq_embedding u hu.ne_zero
  have h2 := one_le_normSq_embedding u' (right_ne_zero_of_mul_eq_one hu')
  have h3 : Complex.normSq (ringComplex u) = 1 := by nlinarith
  rw [Complex.normSq_eq_norm_sq] at h3
  have hn := norm_nonneg (ringComplex u)
  exact le_antisymm (by nlinarith) (by nlinarith)

theorem height_upperTriangular (T : SL(2, O)) (hT : T 1 0 = 0) (hu : IsUnit (T 1 1)) (z : ℂ) (v : ℝ)
    (hv : 0 < v) : hyperbolicHeight (integralComplexMatrix T • upperPoint z v hv) = v := by
  rw [hyperbolicHeight_action_upperPoint]
  have h10 : (integralComplexMatrix T) 1 0 = 0 := by simp [integralComplexMatrix, hT]
  have h11 : (integralComplexMatrix T) 1 1 = ringComplex (T 1 1) := by simp [integralComplexMatrix]
  rw [h10, h11, zero_mul, zero_add, norm_zero, norm_ringComplex_unit hu]
  simp

/-- **`H` vanishes through the ramified cusps** above height `1/2`. -/
theorem thetaSubtraction_ramified (j : Fin 3) (hj : j ≠ 0) (T : SL(2, O)) (hT : T 1 0 = 0)
    (hu : IsUnit (T 0 0)) (z : ℂ) (v : ℝ) (hv : 0 < v) (hv2 : 1 / 2 < v) :
    thetaSubtraction (integralComplexMatrix (cuspRepresentative j * T) • upperPoint z v hv) = 0 := by
  dsimp only [thetaSubtraction]
  rw [cuspSubtraction]
  convert mul_zero (thetaCoeff ^ 2)
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [map_eq_zero_iff _ (RingHom.injective _)]
  have hsmul : rationalComplex (rationalRep q) •
      (integralComplexMatrix (cuspRepresentative j * T) • upperPoint z v hv) =
      integralComplexMatrix (rationalEmbedding (rationalRep q) * cuspRepresentative j * T) •
        upperPoint z v hv := by
    rw [← mul_smul]
    congr 1
    simp only [map_mul]
    rw [mul_assoc]
    rfl
  rw [hsmul, cuspCutoffCorrection]
  refine (tsum_congr fun x => ?_).trans tsum_zero
  rw [cuspCutoffTerm]
  split_ifs with h1
  · have hc := lowerLeft_ramified_ne_zero (Quotient.out x) (rationalRep q) j hj T hT hu
    have hb := cosetHeight_translate_le _ x z v hv hc
    have hn := one_le_normSq_embedding _ hc
    rw [Complex.normSq_eq_norm_sq] at hn
    have hh0 := (cosetHeight_pos x (integralComplexMatrix (rationalEmbedding (rationalRep q) *
      cuspRepresentative j * T) • upperPoint z v hv)).le
    have hle : cosetHeight x (integralComplexMatrix (rationalEmbedding (rationalRep q) *
        cuspRepresentative j * T) • upperPoint z v hv) ≤ 1 / v :=
      (le_mul_of_one_le_right hh0 hn).trans hb
    have hsmall : 1 / v < 2 := by
      rw [div_lt_iff₀ hv]
      linarith
    rw [growthProfile, Set.indicator_of_notMem (fun h => by linarith [Set.mem_Ici.mp h]), mul_zero]
  · rfl

/-! ### Boundedness -/

/-- **`G = θ_s² − H` is bounded on hyperbolic three-space.** -/
theorem renormalizedThetaSq_bounded : ∃ B : ℝ, ∀ w : HyperbolicSpace, ‖renormalizedThetaSq w‖ ≤ B := by
  set a₀ := Real.sqrt (2 / 3)
  have ha₀ : 0 < a₀ := Real.sqrt_pos.mpr (by norm_num)
  have ha₀2 : 1 / 2 < a₀ := by
    rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  obtain ⟨C₁, hC₁, hdec⟩ := cubicSourceResidualFunction_cusp_decay_from_height a₀ ha₀
  obtain ⟨C₂, hC₂, hr₂⟩ := ramifiedSource_exponential_decay false a₀ ha₀
  obtain ⟨C₃, hC₃, hr₃⟩ := ramifiedSource_exponential_decay true a₀ ha₀
  set D := C₁ / a₀ ^ 3
  set c := ‖thetaCoeff‖
  refine ⟨2 * c * C₁ + D ^ 2 + (2 * c + D) ^ 2 + (C₂ + C₃) ^ 2, fun w => ?_⟩
  have hD0 : 0 ≤ D := by positivity
  obtain ⟨M, z, v, hv, hMw, -, hfloor⟩ := bianchi_reduction_height_floor w
  obtain ⟨G', j, T, hT, hu0, hu1, hdec'⟩ := three_cusp_decomposition M⁻¹
  have hw : w = integralComplexMatrix (G' : SL(2, O)) •
      (integralComplexMatrix (cuspRepresentative j * T) • upperPoint z v hv) := by
    rw [← mul_smul, ← map_mul, ← mul_assoc, ← hdec', ← hMw, ← mul_smul, ← map_mul, inv_mul_cancel,
      map_one, one_smul]
  rw [hw, norm_renormalizedThetaSq_rational]
  have hv2 : 1 / 2 < v := lt_of_lt_of_le ha₀2 hfloor
  obtain ⟨z', v', hv', hp⟩ := upperPoint_surjective (integralComplexMatrix T • upperPoint z v hv)
  have hvv : v' = v := by
    have h := height_upperTriangular T hT hu1 z v hv
    rw [← hp, hyperbolicHeight_upperPoint] at h
    exact h
  subst hvv
  have hsplit : integralComplexMatrix (cuspRepresentative j * T) • upperPoint z v' hv =
      integralComplexMatrix (cuspRepresentative j) • upperPoint z' v' hv' := by
    rw [map_mul, mul_smul, ← hp]
  have hpos : 0 ≤ 2 * c * C₁ + D ^ 2 := by positivity
  by_cases hj : j = 0
  · -- the rational class: the point lies on the standard strip
    subst hj
    have hc1 : cuspRepresentative 0 = 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [cuspRepresentative, cuspParameter, lowerCuspMatrix]
    have hc0 : integralComplexMatrix (cuspRepresentative 0) • upperPoint z' v' hv' = upperPoint z' v' hv' := by
      rw [hc1, map_one, one_smul]
    rw [hsplit, hc0, renormalizedThetaSq]
    dsimp only [thetaSubtraction]
    rw [cuspSubtraction_upper _ _ le_rfl z' v' hv' hv2]
    have hδ := hdec v' hv' hfloor z'
    set δ := sourceTheta (upperPoint z' v' hv') - thetaCoeff * (v' : ℂ) ^ (2 / 3 : ℂ) with hδdef
    have hδD : ‖δ‖ ≤ D := hδ.trans (div_le_div_of_nonneg_left hC₁ (by positivity)
      (pow_le_pow_left₀ ha₀.le hfloor 3))
    have hpow : ‖(v' : ℂ) ^ (2 / 3 : ℂ)‖ = v' ^ ((2 : ℝ) / 3) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hv']
      norm_num
    have hθ : sourceTheta (upperPoint z' v' hv') = thetaCoeff * (v' : ℂ) ^ (2 / 3 : ℂ) + δ := by
      rw [hδdef]; ring
    by_cases h2 : 2 ≤ v'
    · -- high: `θ² − c² v^{4/3} = 2 c v^{2/3} δ + δ²`
      have hc23 : (v' : ℂ) ^ (2 / 3 : ℂ) = ((v' ^ ((2 : ℝ) / 3) : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow hv'.le]
        norm_num
      have hf : growthProfile (Set.Ici 2) v' = ((v' : ℂ) ^ (2 / 3 : ℂ)) ^ 2 := by
        rw [growthProfile, Set.indicator_of_mem (Set.mem_Ici.mpr h2), hc23, ← Complex.ofReal_pow]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hv'.le]
        norm_num
      rw [hθ, hf]
      have he : (thetaCoeff * (v' : ℂ) ^ (2 / 3 : ℂ) + δ) ^ 2 - thetaCoeff ^ 2 * ((v' : ℂ) ^ (2 / 3 : ℂ)) ^ 2 =
          2 * thetaCoeff * (v' : ℂ) ^ (2 / 3 : ℂ) * δ + δ ^ 2 := by ring
      rw [he]
      have hv1 : 1 ≤ v' := by linarith
      have hsmall : v' ^ ((2 : ℝ) / 3) * (C₁ / v' ^ 3) ≤ C₁ := by
        have h3 : v' ^ ((2 : ℝ) / 3) ≤ v' ^ 3 := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
      have hc0 : 0 ≤ c := norm_nonneg _
      calc ‖2 * thetaCoeff * (v' : ℂ) ^ (2 / 3 : ℂ) * δ + δ ^ 2‖
          ≤ ‖2 * thetaCoeff * (v' : ℂ) ^ (2 / 3 : ℂ) * δ‖ + ‖δ ^ 2‖ := norm_add_le _ _
        _ = 2 * c * (v' ^ ((2 : ℝ) / 3) * ‖δ‖) + ‖δ‖ ^ 2 := by
            rw [norm_mul, norm_mul, norm_mul, norm_pow, hpow, h2n]
            ring
        _ ≤ 2 * c * C₁ + D ^ 2 := by
            have h1 : v' ^ ((2 : ℝ) / 3) * ‖δ‖ ≤ C₁ :=
              (mul_le_mul_of_nonneg_left hδ (by positivity)).trans hsmall
            have h2' : ‖δ‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hδD 2
            nlinarith
        _ ≤ _ := by nlinarith [sq_nonneg (2 * c + D), sq_nonneg (C₂ + C₃)]
    · -- low: `f(v) = 0` and `θ` is bounded
      have hf : growthProfile (Set.Ici 2) v' = 0 :=
        Set.indicator_of_notMem (fun h => h2 (Set.mem_Ici.mp h)) _
      rw [hf, mul_zero, sub_zero, hθ, norm_pow]
      have hv23 : v' ^ ((2 : ℝ) / 3) ≤ 2 := by
        have : v' ^ ((2 : ℝ) / 3) ≤ 2 ^ ((2 : ℝ) / 3) :=
          Real.rpow_le_rpow hv'.le (not_le.mp h2).le (by norm_num)
        refine this.trans ?_
        calc (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      have hb : ‖thetaCoeff * (v' : ℂ) ^ (2 / 3 : ℂ) + δ‖ ≤ 2 * c + D := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, hpow]
        nlinarith [norm_nonneg thetaCoeff]
      have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      nlinarith [sq_nonneg (C₂ + C₃)]
  · -- the two ramified classes
    rw [renormalizedThetaSq, thetaSubtraction_ramified j hj T hT hu0 z v' hv hv2, sub_zero, hsplit,
      norm_pow]
    have hθ : ‖sourceTheta (integralComplexMatrix (cuspRepresentative j) • upperPoint z' v' hv')‖ ≤
        C₂ + C₃ := by
      fin_cases j
      · exact absurd rfl hj
      · have h := hr₂ v' hv' hfloor z'
        have hroot : ((ramifiedCuspRoot false : Oˣ) : O) = cuspParameter 1 := by
          simp [ramifiedCuspRoot, cuspOmegaUnit_val, cuspParameter]
        rw [ramifiedSourceFunction, hroot] at h
        have he : Real.exp (-(residualBesselDecayRate / 3) * v') ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          have : 0 ≤ residualBesselDecayRate := by unfold residualBesselDecayRate; positivity
          nlinarith
        calc _ ≤ C₂ * Real.exp (-(residualBesselDecayRate / 3) * v') := h
          _ ≤ C₂ := mul_le_of_le_one_right hC₂ he
          _ ≤ C₂ + C₃ := le_add_of_nonneg_right hC₃
      · have h := hr₃ v' hv' hfloor z'
        have hroot : ((ramifiedCuspRoot true : Oˣ) : O) = cuspParameter 2 := by
          simp [ramifiedCuspRoot, cuspOmegaUnit_val, cuspParameter]
        rw [ramifiedSourceFunction, hroot] at h
        have he : Real.exp (-(residualBesselDecayRate / 3) * v') ≤ 1 := by
          apply Real.exp_le_one_iff.mpr
          have : 0 ≤ residualBesselDecayRate := by unfold residualBesselDecayRate; positivity
          nlinarith
        calc _ ≤ C₃ * Real.exp (-(residualBesselDecayRate / 3) * v') := h
          _ ≤ C₃ := mul_le_of_le_one_right hC₃ he
          _ ≤ C₂ + C₃ := le_add_of_nonneg_left hC₂
    have hθ2 := pow_le_pow_left₀ (norm_nonneg _) hθ 2
    nlinarith [sq_nonneg (2 * c + D)]

/-- `G` is square integrable on `D_Γ`. -/
theorem renormalizedThetaSq_memLp :
    MemLp renormalizedThetaSq 2 (hyperbolicVolume.restrict levelSet) := by
  haveI : IsFiniteMeasure (hyperbolicVolume.restrict levelSet) :=
    isFiniteMeasure_restrict.mpr levelSet_volume_lt_top.ne
  obtain ⟨B, hB⟩ := renormalizedThetaSq_bounded
  exact MemLp.of_bound renormalizedThetaSq_measurable.aestronglyMeasurable B (Eventually.of_forall hB)

/-! ### High on the strip, and the constant term -/

/-- `(v^{2/3})² = v^{4/3}` as complex numbers. -/
theorem cpow_two_thirds_sq (v : ℝ) (hv : 0 < v) :
    ((v : ℂ) ^ (2 / 3 : ℂ)) ^ 2 = ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ) := by
  have hc23 : (v : ℂ) ^ (2 / 3 : ℂ) = ((v ^ ((2 : ℝ) / 3) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hv.le]
    norm_num
  rw [hc23, ← Complex.ofReal_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le]
  norm_num

/-- **`G = O(v^{−7/3})` high on the standard strip.** -/
theorem norm_renormalizedThetaSq_high : ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), 2 ≤ v →
    ‖renormalizedThetaSq (upperPoint z v hv)‖ ≤ C * v ^ (-(7 : ℝ) / 3) := by
  obtain ⟨C₁, hC₁, hdec⟩ := cubicSourceResidualFunction_cusp_decay_from_height 1 one_pos
  set c := ‖thetaCoeff‖
  refine ⟨2 * c * C₁ + C₁ ^ 2, by positivity, fun z v hv h2 => ?_⟩
  have hv1 : 1 ≤ v := by linarith
  set δ := sourceTheta (upperPoint z v hv) - thetaCoeff * (v : ℂ) ^ (2 / 3 : ℂ) with hδdef
  have hδ : ‖δ‖ ≤ C₁ / v ^ 3 := hdec v hv hv1 z
  have hθ : sourceTheta (upperPoint z v hv) = thetaCoeff * (v : ℂ) ^ (2 / 3 : ℂ) + δ := by
    rw [hδdef]; ring
  have hf : growthProfile (Set.Ici 2) v = ((v : ℂ) ^ (2 / 3 : ℂ)) ^ 2 := by
    rw [growthProfile, Set.indicator_of_mem (Set.mem_Ici.mpr h2), cpow_two_thirds_sq v hv]
  rw [renormalizedThetaSq]
  dsimp only [thetaSubtraction]
  rw [cuspSubtraction_upper _ _ le_rfl z v hv (by linarith), hf, hθ]
  have he : (thetaCoeff * (v : ℂ) ^ (2 / 3 : ℂ) + δ) ^ 2 - thetaCoeff ^ 2 * ((v : ℂ) ^ (2 / 3 : ℂ)) ^ 2 =
      2 * thetaCoeff * (v : ℂ) ^ (2 / 3 : ℂ) * δ + δ ^ 2 := by ring
  rw [he]
  have hpow : ‖(v : ℂ) ^ (2 / 3 : ℂ)‖ = v ^ ((2 : ℝ) / 3) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hv]
    norm_num
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hc0 : 0 ≤ c := norm_nonneg _
  have hA : v ^ ((2 : ℝ) / 3) * (C₁ / v ^ 3) = C₁ * v ^ (-(7 : ℝ) / 3) := by
    rw [show -(7 : ℝ) / 3 = (2 : ℝ) / 3 - 3 by norm_num, Real.rpow_sub hv]
    norm_cast
    ring
  have hB : (C₁ / v ^ 3) ^ 2 ≤ C₁ ^ 2 * v ^ (-(7 : ℝ) / 3) := by
    have h6 : (v ^ 3) ^ 2 = v ^ (6 : ℝ) := by
      rw [← pow_mul]
      norm_cast
    rw [div_pow, h6, div_eq_mul_inv, ← Real.rpow_neg hv.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)) (sq_nonneg _)
  calc ‖2 * thetaCoeff * (v : ℂ) ^ (2 / 3 : ℂ) * δ + δ ^ 2‖
      ≤ ‖2 * thetaCoeff * (v : ℂ) ^ (2 / 3 : ℂ) * δ‖ + ‖δ ^ 2‖ := norm_add_le _ _
    _ = 2 * c * (v ^ ((2 : ℝ) / 3) * ‖δ‖) + ‖δ‖ ^ 2 := by
        rw [norm_mul, norm_mul, norm_mul, norm_pow, hpow, h2n]
        ring
    _ ≤ 2 * c * (v ^ ((2 : ℝ) / 3) * (C₁ / v ^ 3)) + (C₁ / v ^ 3) ^ 2 := by
        gcongr
    _ ≤ 2 * c * (C₁ * v ^ (-(7 : ℝ) / 3)) + C₁ ^ 2 * v ^ (-(7 : ℝ) / 3) := by
        rw [hA]
        gcongr
    _ = (2 * c * C₁ + C₁ ^ 2) * v ^ (-(7 : ℝ) / 3) := by ring

theorem thetaSubtraction_integrableOn_periodDomain (v : ℝ) (hv : 0 < v) :
    IntegrableOn (fun z => thetaSubtraction (cuspCoordinateLift (v, z))) periodDomain := by
  have hm : AEStronglyMeasurable (fun z => thetaSubtraction (cuspCoordinateLift (v, z)))
      (volume.restrict periodDomain) :=
    ((cuspSubtraction_measurable _ _ measurableSet_Ici).comp
      (cuspCoordinateLift_measurable.comp measurable_prodMk_left)).aestronglyMeasurable
  have hfin : volume periodDomain < ⊤ := by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_lt_top
  by_cases hv2 : v ≤ 1 / 2
  · refine IntegrableOn.of_bound hfin hm (‖thetaCoeff‖ ^ 2 * (4 * (1 / v) ^ ((4 : ℝ) / 3)))
      (Eventually.of_forall fun z => ?_)
    rw [cuspCoordinateLift_positive v z hv]
    exact norm_cuspSubtraction_small _ _ z v hv hv2
  · refine IntegrableOn.of_bound hfin hm (‖thetaCoeff ^ 2 * growthProfile (Set.Ici 2) v‖)
      (Eventually.of_forall fun z => ?_)
    rw [cuspCoordinateLift_positive v z hv]
    dsimp only [thetaSubtraction]
    rw [cuspSubtraction_upper _ _ le_rfl z v hv (not_le.mp hv2)]

/-- **The constant term of `G`.** `a₀(G)(v) = |P| (c² v^{4/3} + R(v)) − a₀(H)(v)`. -/
theorem cuspConstantTerm_renormalized (v : ℝ) (hv : 0 < v) :
    cuspConstantTerm renormalizedThetaSq v =
      periodArea * (thetaCoeff ^ 2 * ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ) + thetaSqRemainder v) -
        cuspConstantTerm thetaSubtraction v := by
  have hs := rationalSourceModeAmplitude_summable v hv
  have hθ : ∀ z, sourceTheta (cuspCoordinateLift (v, z)) = cuspCharacterSeries (rationalSourceModeAmplitude v) z :=
    fun z => by rw [cuspCoordinateLift_positive v z hv]; exact cubicSourceResidualFunction_fourier_expansion v hv z
  have hI1 : IntegrableOn (fun z => sourceTheta (cuspCoordinateLift (v, z)) ^ 2) periodDomain := by
    simp_rw [hθ]
    exact integrableOn_periodDomain_of_continuous _ ((cuspCharacterSeries_continuous _ hs).pow 2)
  rw [cuspConstantTerm, cuspConstantTerm]
  simp only [renormalizedThetaSq]
  rw [integral_sub hI1 (thetaSubtraction_integrableOn_periodDomain v hv)]
  congr 1
  simp_rw [hθ]
  rw [integral_cuspCharacterSeries_sq _ hs, tsum_amplitude_mul_neg v hv, rationalSourceModeAmplitude_zero,
    mul_pow, cpow_two_thirds_sq v hv]

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
