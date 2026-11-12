import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheRenormalizedThetaSquareIsBounded

/-!
# The theta function has a linear cusp subtraction

`θ_s` itself (not only `θ_s²`) has a cusp subtraction: with `c = 3πr` and the profile `1_{[2,∞)} v^{2/3}`,

`h(w) = c Σ_q E_1(r_q w ∣ 1_{[2,∞)} v^{2/3})`   (`thetaLinear`, `q` over the four rational cusps)

has the multiplier `κ` of `θ_s` (`linearSubtraction_automorphy`), is equivariant under the rational
extension with the character of `θ_s` (`linearSubtraction_rational`, via the four-cusp projection),
equals `c v^{2/3}` on the standard strip above height 2 and vanishes through the ramified cusps
(`linearSubtraction_upper`, `linearSubtraction_ramified`).

Uniform bounds through every cusp (`thetaLinear_bounds`): for every `N ∈ SL₂(ℤ[ω])` and every point
`x = z + jv` with `v ≥ √(2/3)`,

`|θ_s(Nx)|, |h(Nx)| ≤ A (1 + v^{2/3})`,   `|θ_s(Nx) − h(Nx)| (1 + v^{2/3}) ≤ B`.

Reduce `N = G c_j T` (`three_cusp_decomposition`); `G` acts by a unimodular character on both. For
`j = 0` the point is on the standard strip: `θ_s − c v^{2/3} = O(v^{−3})`; for `j = 1, 2` the theta
function is exponentially small at the ramified cusp and `h = 0` there, and
`v^{2/3} e^{−βv} ≤ 1 + 1/β`. So the defect `θ_s − h` decays exactly as fast as `θ_s` grows: products of
two translates of `θ_s` are renormalized by the products of the translates of `h`.
-/

noncomputable section

open MeasureTheory Filter Function
open scoped BigOperators Classical MatrixGroups ComplexConjugate

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- The profile `1_S v^{2/3}` of the constant term of `θ_s`. -/
def thinProfile (S : Set ℝ) (v : ℝ) : ℂ := S.indicator (fun v => ((v ^ ((2 : ℝ) / 3) : ℝ) : ℂ)) v

theorem conj_thinProfile (S : Set ℝ) (v : ℝ) : conj (thinProfile S v) = thinProfile S v := by
  rw [thinProfile]
  by_cases h : v ∈ S
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- `(1_S v^{2/3})² = 1_S v^{4/3}` on `S ⊆ [2, ∞)`. -/
theorem thinProfile_mul_self (S : Set ℝ) (hS : S ⊆ Set.Ici 2) (v : ℝ) :
    thinProfile S v * thinProfile S v = growthProfile S v := by
  by_cases h : v ∈ S
  · have hv : 0 < v := lt_of_lt_of_le two_pos (hS h)
    rw [thinProfile, growthProfile, Set.indicator_of_mem h, Set.indicator_of_mem h, ← Complex.ofReal_mul,
      ← Real.rpow_add hv]
    norm_num
  · rw [thinProfile, growthProfile, Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

/-- `h_S(w) = c Σ_q E_1(r_q w ∣ 1_S v^{2/3})`. -/
def linearSubtraction (c : ℂ) (S : Set ℝ) (w : HyperbolicSpace) : ℂ :=
  c * ∑ q : RationalFourCusp,
    cuspCutoffCorrection 1 (thinProfile S) (rationalComplex (rationalRep q) • w)

/-- Each rational translate of a cutoff series keeps the multiplier `κ`. -/
theorem cutoff_rational_automorphy (F : ℝ → ℂ) (r : SL(2, ℤ)) (M : levelThree) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 F (rationalComplex r • (complexMatrix M • w)) =
      complexCharacter M * cuspCutoffCorrection 1 F (rationalComplex r • w) := by
  have hmove : rationalComplex r • (complexMatrix M • w) =
      complexMatrix (levelThreeConjugate (rationalEmbedding r) M) • (rationalComplex r • w) := by
    rw [← mul_smul, ← mul_smul]
    congr 1
    change integralComplexMatrix (rationalEmbedding r) * integralComplexMatrix (M : SL(2, O)) =
      integralComplexMatrix ((rationalEmbedding r) * (M : SL(2, O)) * (rationalEmbedding r)⁻¹) *
        integralComplexMatrix (rationalEmbedding r)
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [hmove, cuspCutoffCorrection_automorphy 1 le_rfl, complexCharacter_conjugate_rational]

theorem linearSubtraction_automorphy (c : ℂ) (S : Set ℝ) (M : levelThree) (w : HyperbolicSpace) :
    linearSubtraction c S (complexMatrix M • w) = complexCharacter M * linearSubtraction c S w := by
  simp only [linearSubtraction, cutoff_rational_automorphy, ← Finset.mul_sum]
  ring

/-- `h_S = 4c P(E_1(· ∣ 1_S v^{2/3}))`, `P` the rational source projection. -/
theorem linearSubtraction_eq_projection (c : ℂ) (S : Set ℝ) (w : HyperbolicSpace) :
    linearSubtraction c S w =
      4 * c * rationalSourceProjection (cuspCutoffCorrection 1 (thinProfile S)) w := by
  rw [rationalSourceProjection_four_cusps _ (fun n w => cuspCutoffCorrection_automorphy 1 le_rfl _ n w)
    (cutoff_T_invariant _) (cuspCutoffCorrection_S_sq 1 _)]
  have h := fourCuspAverage_eq_sum (cuspCutoffCorrection 1 (thinProfile S)) 1 w
  simp only [one_smul, mul_one] at h
  rw [h, linearSubtraction]
  ring

theorem linearSubtraction_rational (c : ℂ) (S : Set ℝ) (g : rationalExtension) (w : HyperbolicSpace) :
    linearSubtraction c S (integralComplexMatrix (g : SL(2, O)) • w) =
      extendedComplexCharacter g * linearSubtraction c S w := by
  rw [linearSubtraction_eq_projection, linearSubtraction_eq_projection,
    rationalSourceProjection_automorphy _ (fun n w => cuspCutoffCorrection_automorphy 1 le_rfl _ n w) g w]
  ring

/-- For `S ⊆ [2, ∞)` and `v > 1/2`: `h_S(z + jv) = c 1_S(v) v^{2/3}`. -/
theorem linearSubtraction_upper (c : ℂ) (S : Set ℝ) (hS : S ⊆ Set.Ici 2) (z : ℂ) (v : ℝ) (hv : 0 < v)
    (hv2 : 1 / 2 < v) :
    linearSubtraction c S (upperPoint z v hv) = c * thinProfile S v := by
  have hzero : ∀ t : ℝ, t < 2 → thinProfile S t = 0 := fun t ht =>
    Set.indicator_of_notMem (fun h => absurd (hS h) (not_le.mpr ht)) _
  have hsmall : 1 / v < 2 := by
    rw [div_lt_iff₀ hv]
    linarith
  rw [linearSubtraction, Fintype.sum_eq_single (.inl ())]
  · have h1 : rationalComplex (rationalRep (.inl ())) • upperPoint z v hv = upperPoint z v hv := by
      simp [rationalRep, rationalFourCuspRep]
    rw [h1, cuspCutoffCorrection_upper _ z v hv fun t _ ht => hzero t (by
      have : 1 / (9 * v) ≤ 1 / v := by
        apply div_le_div_of_nonneg_left zero_le_one hv
        linarith
      linarith)]
    split_ifs with h
    · rfl
    · rw [hzero v (by linarith [not_lt.mp h])]
  · intro q hq
    obtain ⟨h0, h1⟩ := rationalRep_column q hq
    rw [cuspCutoffCorrection_rational _ _ h0 h1 z v hv fun t _ ht => hzero t (by linarith)]

/-- **`h` vanishes through the ramified cusps** above height `1/2`. -/
theorem linearSubtraction_ramified (c : ℂ) (S : Set ℝ) (hS : S ⊆ Set.Ici 2) (j : Fin 3) (hj : j ≠ 0)
    (T : SL(2, O)) (hT : T 1 0 = 0) (hu : IsUnit (T 0 0)) (z : ℂ) (v : ℝ) (hv : 0 < v)
    (hv2 : 1 / 2 < v) :
    linearSubtraction c S (integralComplexMatrix (cuspRepresentative j * T) • upperPoint z v hv) = 0 := by
  rw [linearSubtraction]
  convert mul_zero c
  refine Finset.sum_eq_zero fun q _ => ?_
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
    rw [thinProfile, Set.indicator_of_notMem (fun h => by linarith [Set.mem_Ici.mp (hS h)]), mul_zero]
  · rfl

/-! ### The subtraction of `θ_s` and its bounds -/

/-- The linear subtraction of `θ_s`: `h = c Σ_q E_1(r_q w ∣ 1_{[2,∞)} v^{2/3})`, `c = 3πr`. -/
abbrev thetaLinear : HyperbolicSpace → ℂ := linearSubtraction thetaCoeff (Set.Ici 2)

theorem thetaLinear_measurable : Measurable thetaLinear := by
  have hF : Measurable (thinProfile (Set.Ici 2)) :=
    (Measurable.indicator (Complex.measurable_ofReal.comp (measurable_id.pow_const _)) measurableSet_Ici)
  refine measurable_const.mul (Finset.measurable_sum _ fun q _ => ?_)
  exact (cuspCutoffCorrection_measurable 1 _ hF).comp (continuous_hyperbolic_action _).measurable

/-- Every translate of a point reduces to a cusp representative at the same height. -/
theorem cusp_reduce (N : SL(2, O)) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    ∃ (G : rationalExtension) (j : Fin 3) (z' : ℂ),
      integralComplexMatrix N • upperPoint z v hv =
        integralComplexMatrix (G : SL(2, O)) •
          (integralComplexMatrix (cuspRepresentative j) • upperPoint z' v hv) := by
  obtain ⟨G, j, T, hT, -, hu1, hdec⟩ := three_cusp_decomposition N
  obtain ⟨z', v', hv', hp⟩ := upperPoint_surjective (integralComplexMatrix T • upperPoint z v hv)
  have hvv : v' = v := by
    have h := height_upperTriangular T hT hu1 z v hv
    rw [← hp, hyperbolicHeight_upperPoint] at h
    exact h
  subst hvv
  refine ⟨G, j, z', ?_⟩
  rw [hdec, map_mul, map_mul, mul_smul, mul_smul, ← hp]

/-- `v^{2/3} e^{−βv} ≤ 1 + 1/β`. -/
theorem rpow_two_thirds_mul_exp_le {β : ℝ} (hβ : 0 < β) {v : ℝ} (hv : 0 ≤ v) :
    v ^ ((2 : ℝ) / 3) * Real.exp (-β * v) ≤ 1 + 1 / β := by
  have h1 : v ^ ((2 : ℝ) / 3) ≤ 1 + v := by
    rcases le_or_gt v 1 with h | h
    · have := Real.rpow_le_one hv h (by norm_num : (0 : ℝ) ≤ 2 / 3)
      linarith
    · have : v ^ ((2 : ℝ) / 3) ≤ v ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h.le (by norm_num)
      rw [Real.rpow_one] at this
      linarith
  have he : Real.exp (-β * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hve : β * v * Real.exp (-β * v) ≤ 1 := by
    have h2 := Real.add_one_le_exp (β * v)
    have h3 : Real.exp (β * v) * Real.exp (-β * v) = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith [Real.exp_pos (-β * v)]
  have hve' : v * Real.exp (-β * v) ≤ 1 / β := by
    rw [le_div_iff₀ hβ]
    linarith
  calc v ^ ((2 : ℝ) / 3) * Real.exp (-β * v) ≤ (1 + v) * Real.exp (-β * v) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (-β * v) + v * Real.exp (-β * v) := by ring
    _ ≤ 1 + 1 / β := add_le_add he hve'

/-- **Uniform bounds through every cusp.** For `N ∈ SL₂(ℤ[ω])` and `x = z + jv` with `v ≥ √(2/3)`:
`|θ_s(Nx)|, |h(Nx)| ≤ A(1 + v^{2/3})` and `|θ_s(Nx) − h(Nx)| (1 + v^{2/3}) ≤ B`. -/
theorem thetaLinear_bounds :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (N : SL(2, O)) (z : ℂ) (v : ℝ) (hv : 0 < v), Real.sqrt (2 / 3) ≤ v →
      ‖sourceTheta (integralComplexMatrix N • upperPoint z v hv)‖ ≤ A * (1 + v ^ ((2 : ℝ) / 3)) ∧
      ‖thetaLinear (integralComplexMatrix N • upperPoint z v hv)‖ ≤ A * (1 + v ^ ((2 : ℝ) / 3)) ∧
      ‖sourceTheta (integralComplexMatrix N • upperPoint z v hv) -
          thetaLinear (integralComplexMatrix N • upperPoint z v hv)‖ * (1 + v ^ ((2 : ℝ) / 3)) ≤ B := by
  set a₀ := Real.sqrt (2 / 3)
  have ha₀ : 0 < a₀ := Real.sqrt_pos.mpr (by norm_num)
  have ha₀2 : 1 / 2 < a₀ := by
    rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  obtain ⟨C₁, hC₁, hdec⟩ := cubicSourceResidualFunction_cusp_decay_from_height a₀ ha₀
  obtain ⟨C₂, hC₂, hr₂⟩ := ramifiedSource_exponential_decay false a₀ ha₀
  obtain ⟨C₃, hC₃, hr₃⟩ := ramifiedSource_exponential_decay true a₀ ha₀
  set β := residualBesselDecayRate / 3 with hβdef
  have hβ : 0 < β := by
    have := residualBesselDecayRate_pos
    positivity
  set D := C₁ / a₀ ^ 3
  set c := ‖thetaCoeff‖
  have hD0 : 0 ≤ D := by positivity
  have hc0 : 0 ≤ c := norm_nonneg _
  refine ⟨c + D + C₂ + C₃, 2 * C₁ + 3 * (2 * c + D) + (C₂ + C₃) * (2 + 1 / β), by positivity,
    by positivity, fun N z v hv hfloor => ?_⟩
  have hv2 : 1 / 2 < v := lt_of_lt_of_le ha₀2 hfloor
  have hp0 : 0 ≤ v ^ ((2 : ℝ) / 3) := by positivity
  obtain ⟨G, j, z', hred⟩ := cusp_reduce N z v hv
  have hθG := cubicSourceResidualFunction_automorphy G
    (integralComplexMatrix (cuspRepresentative j) • upperPoint z' v hv)
  have hhG : thetaLinear (integralComplexMatrix (G : SL(2, O)) •
      (integralComplexMatrix (cuspRepresentative j) • upperPoint z' v hv)) =
        extendedComplexCharacter G * thetaLinear (integralComplexMatrix (cuspRepresentative j) • upperPoint z' v hv) :=
    linearSubtraction_rational thetaCoeff (Set.Ici 2) G _
  have hG1 := norm_extendedComplexCharacter G
  rw [hred]
  change ‖cubicSourceResidualFunction _‖ ≤ _ ∧ ‖thetaLinear _‖ ≤ _ ∧
    ‖cubicSourceResidualFunction _ - thetaLinear _‖ * _ ≤ _
  rw [hθG, hhG, ← mul_sub, norm_mul, norm_mul, norm_mul, hG1, one_mul, one_mul, one_mul]
  set y := integralComplexMatrix (cuspRepresentative j) • upperPoint z' v hv
  by_cases hj : j = 0
  · -- the rational class: the standard strip
    subst hj
    have hc1 : cuspRepresentative 0 = 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [cuspRepresentative, cuspParameter, lowerCuspMatrix]
    have hy : y = upperPoint z' v hv := by
      change integralComplexMatrix (cuspRepresentative 0) • upperPoint z' v hv = _
      rw [hc1, map_one, one_smul]
    rw [hy]
    have hδ := hdec v hv hfloor z'
    set δ := cubicSourceResidualFunction (upperPoint z' v hv) - thetaCoeff * (v : ℂ) ^ (2 / 3 : ℂ) with hδdef
    have hδD : ‖δ‖ ≤ D := hδ.trans (div_le_div_of_nonneg_left hC₁ (by positivity)
      (pow_le_pow_left₀ ha₀.le hfloor 3))
    have hpow : ‖(v : ℂ) ^ (2 / 3 : ℂ)‖ = v ^ ((2 : ℝ) / 3) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hv]
      norm_num
    have hθ : cubicSourceResidualFunction (upperPoint z' v hv) = thetaCoeff * (v : ℂ) ^ (2 / 3 : ℂ) + δ := by
      rw [hδdef]; ring
    have hh : thetaLinear (upperPoint z' v hv) = thetaCoeff * thinProfile (Set.Ici 2) v :=
      linearSubtraction_upper _ _ le_rfl z' v hv hv2
    have hθb : ‖cubicSourceResidualFunction (upperPoint z' v hv)‖ ≤ c * v ^ ((2 : ℝ) / 3) + D := by
      rw [hθ]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, hpow]
      linarith
    have hthin : ‖thinProfile (Set.Ici 2) v‖ ≤ v ^ ((2 : ℝ) / 3) := by
      rw [thinProfile]
      by_cases h2 : v ∈ Set.Ici 2
      · rw [Set.indicator_of_mem h2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
      · rw [Set.indicator_of_notMem h2, norm_zero]
        exact hp0
    refine ⟨by nlinarith, ?_, ?_⟩
    · rw [hh, norm_mul]
      nlinarith [mul_le_mul_of_nonneg_left hthin hc0]
    · by_cases h2 : 2 ≤ v
      · -- high: the defect is `δ = O(v^{−3})`
        have hthin2 : thinProfile (Set.Ici 2) v = ((v ^ ((2 : ℝ) / 3) : ℝ) : ℂ) := by
          rw [thinProfile, Set.indicator_of_mem (Set.mem_Ici.mpr h2)]
        have hc23 : (v : ℂ) ^ (2 / 3 : ℂ) = ((v ^ ((2 : ℝ) / 3) : ℝ) : ℂ) := by
          rw [Complex.ofReal_cpow hv.le]
          norm_num
        have hdef : cubicSourceResidualFunction (upperPoint z' v hv) - thetaLinear (upperPoint z' v hv) = δ := by
          rw [hh, hthin2, hθ, hc23]
          ring
        rw [hdef]
        have hv1 : 1 ≤ v := by linarith
        have hv3 : 1 ≤ v ^ 3 := one_le_pow₀ hv1
        have h23 : v ^ ((2 : ℝ) / 3) ≤ v ^ 3 := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
        have hδ' : ‖δ‖ * v ^ 3 ≤ C₁ := by
          have := (le_div_iff₀ (by positivity)).mp hδ
          linarith
        have hδ0 := norm_nonneg δ
        have e1 := mul_le_mul_of_nonneg_left hv3 hδ0
        have e2 := mul_le_mul_of_nonneg_left h23 hδ0
        have hrest : 0 ≤ 3 * (2 * c + D) + (C₂ + C₃) * (2 + 1 / β) := by positivity
        nlinarith [e1, e2, hδ', hrest]
      · -- low: `h = 0` and `θ_s` is bounded
        have hthin0 : thinProfile (Set.Ici 2) v = 0 :=
          Set.indicator_of_notMem (fun h => h2 (Set.mem_Ici.mp h)) _
        rw [hh, hthin0, mul_zero, sub_zero]
        have hv23 : v ^ ((2 : ℝ) / 3) ≤ 2 := by
          have : v ^ ((2 : ℝ) / 3) ≤ 2 ^ ((2 : ℝ) / 3) :=
            Real.rpow_le_rpow hv.le (not_le.mp h2).le (by norm_num)
          refine this.trans ?_
          calc (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
        have hb : ‖cubicSourceResidualFunction (upperPoint z' v hv)‖ ≤ 2 * c + D := by
          nlinarith
        have hb0 := norm_nonneg (cubicSourceResidualFunction (upperPoint z' v hv))
        have e := mul_le_mul hb (by linarith : 1 + v ^ ((2 : ℝ) / 3) ≤ 3) (by positivity) (by positivity)
        have hrest : 0 ≤ 2 * C₁ + (C₂ + C₃) * (2 + 1 / β) := by positivity
        nlinarith [e, hrest]
  · -- the two ramified classes: `θ_s` is exponentially small and `h = 0`
    have hh : thetaLinear y = 0 := by
      have := linearSubtraction_ramified thetaCoeff (Set.Ici 2) le_rfl j hj 1 (by simp) (by simp) z' v hv hv2
      rwa [mul_one] at this
    have hθ : ‖cubicSourceResidualFunction y‖ ≤ (C₂ + C₃) * Real.exp (-β * v) := by
      fin_cases j
      · exact absurd rfl hj
      · have h := hr₂ v hv hfloor z'
        have hroot : ((ramifiedCuspRoot false : Oˣ) : O) = cuspParameter 1 := by
          simp [ramifiedCuspRoot, cuspOmegaUnit_val, cuspParameter]
        rw [ramifiedSourceFunction, hroot] at h
        refine h.trans ?_
        nlinarith [Real.exp_pos (-β * v)]
      · have h := hr₃ v hv hfloor z'
        have hroot : ((ramifiedCuspRoot true : Oˣ) : O) = cuspParameter 2 := by
          simp [ramifiedCuspRoot, cuspOmegaUnit_val, cuspParameter]
        rw [ramifiedSourceFunction, hroot] at h
        refine h.trans ?_
        nlinarith [Real.exp_pos (-β * v)]
    have he1 : Real.exp (-β * v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hve := rpow_two_thirds_mul_exp_le hβ hv.le
    have hC0 : 0 ≤ C₂ + C₃ := by positivity
    rw [hh, norm_zero, sub_zero]
    refine ⟨by nlinarith [mul_le_mul_of_nonneg_left he1 hC0], by nlinarith, ?_⟩
    calc ‖cubicSourceResidualFunction y‖ * (1 + v ^ ((2 : ℝ) / 3))
        ≤ (C₂ + C₃) * Real.exp (-β * v) * (1 + v ^ ((2 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_right hθ (by positivity)
      _ = (C₂ + C₃) * (Real.exp (-β * v) + v ^ ((2 : ℝ) / 3) * Real.exp (-β * v)) := by ring
      _ ≤ (C₂ + C₃) * (1 + (1 + 1 / β)) := mul_le_mul_of_nonneg_left (add_le_add he1 hve) hC0
      _ ≤ _ := by
          have : 0 ≤ 1 / β := by positivity
          nlinarith

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
