import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheEisensteinPairingContinuesAcrossFourThirds

/-!
# The theta square has a rational cusp subtraction

`θ_s²` grows like `c² v^{4/3}` at the four rational cusps `∞, 0, −1, −2` of the level-three group
(the rational class of `θ_s`), and is small at the two primitive ramified cusp classes. The function

`H_S(w) = c² Σ_q conj(E_1(r_q w ∣ f_S))`,   `r_q ∈ {1, S, ST, ST²}`,   `f_S = 1_S v^{4/3}`, `S ⊆ [2, ∞)`,

(`cuspSubtraction`; `E_1(· ∣ f)` is MMD's cutoff Eisenstein series `cuspCutoffCorrection 1 f`) has the
multiplier `κ⁻¹` of `θ_s²` (`cuspSubtraction_automorphy`) and, at height `v > 1/2` of the standard
strip, equals `c² f_S(v)` exactly (`cuspSubtraction_upper`): every coset other than the identity
lifts `z + jv` to height `≤ 1/(9v)`, and every coset through a rational translate `r_q ≠ 1` to height
`≤ 1/v` (`cosetHeight_translate_le`: a nonzero bottom-left entry `c` of `x·g` caps the height at
`1/(|c|² v)`).

`setIntegral_levelSet_translate`: the integral over `D_Γ` of a `Γ`-invariant function is unchanged by
`w ↦ g w` for every `g ∈ SL₂(ℤ[ω])` (`g D_Γ` is again a fundamental set, `Γ` being normal).
-/

noncomputable section

open MeasureTheory Filter Function
open scoped BigOperators Classical MatrixGroups ComplexConjugate

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-! ### Heights of translated points -/

/-- If the bottom-left entry `c` of `x · g` is nonzero, `v_x(g p) · |c|² ≤ 1/v` for `p = z + jv`. -/
theorem cosetHeight_translate_le (g : SL(2, O)) (x : CuspCosets) (z : ℂ) (v : ℝ) (hv : 0 < v)
    (hc : (((Quotient.out x : levelThree) : SL(2, O)) * g) 1 0 ≠ 0) :
    cosetHeight x (integralComplexMatrix g • upperPoint z v hv) *
      ‖ringComplex ((((Quotient.out x : levelThree) : SL(2, O)) * g) 1 0)‖ ^ 2 ≤ 1 / v := by
  have hM : integralComplexMatrix g⁻¹ • (integralComplexMatrix g • upperPoint z v hv) =
      upperPoint z v hv := by
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  rw [cosetHeight_eq g⁻¹ _ z v hv hM x]
  have hrow : shiftedRow g⁻¹ x = ((Quotient.out x : levelThree) : SL(2, O)) * g := by
    rw [shiftedRow, inv_inv]
  rw [hrow]
  set c := ringComplex ((((Quotient.out x : levelThree) : SL(2, O)) * g) 1 0)
  set d := ringComplex ((((Quotient.out x : levelThree) : SL(2, O)) * g) 1 1)
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr (ringComplex_ne_zero hc)
  have hB : 0 < ‖c‖ ^ 2 * v ^ 2 := by positivity
  calc v / (‖c * z + d‖ ^ 2 + ‖c‖ ^ 2 * v ^ 2) * ‖c‖ ^ 2
      ≤ v / (‖c‖ ^ 2 * v ^ 2) * ‖c‖ ^ 2 := by
        gcongr
        exact le_add_of_nonneg_left (sq_nonneg _)
    _ = 1 / v := by field_simp

/-- The identity class is the only coset with vanishing bottom-left entry. -/
theorem lower_left_ne_zero (x : CuspCosets) (hx : x ≠ cosetOf 1) :
    ((Quotient.out x : levelThree) : SL(2, O)) 1 0 ≠ 0 := by
  intro h
  apply hx
  rw [← Quotient.out_eq x]
  exact Quotient.sound (row_eq_one_of_lower_left_zero _ h)

/-- Away from the identity class, `v_x(z + jv) ≤ 1/(9v)`. -/
theorem cosetHeight_upper_le (x : CuspCosets) (hx : x ≠ cosetOf 1) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    cosetHeight x (upperPoint z v hv) ≤ 1 / (9 * v) := by
  have h1 : integralComplexMatrix 1 • upperPoint z v hv = upperPoint z v hv := by
    rw [map_one, one_smul]
  have hc := lower_left_ne_zero x hx
  have hc' : (((Quotient.out x : levelThree) : SL(2, O)) * 1) 1 0 ≠ 0 := by rwa [mul_one]
  have hb := cosetHeight_translate_le 1 x z v hv hc'
  rw [h1, mul_one] at hb
  obtain ⟨c', hc'⟩ := levelThree_lower (Quotient.out x)
  have hc0 : c' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc'
    exact hc hc'
  have h9 : 9 ≤ ‖ringComplex (((Quotient.out x : levelThree) : SL(2, O)) 1 0)‖ ^ 2 := by
    rw [hc', map_mul, norm_mul, mul_pow]
    have h3 : ‖ringComplex (3 : O)‖ = 3 := by
      rw [map_ofNat ringComplex 3]
      norm_num
    have := one_le_normSq_embedding c' hc0
    rw [Complex.normSq_eq_norm_sq] at this
    rw [h3]
    nlinarith
  have hh0 : 0 ≤ cosetHeight x (upperPoint z v hv) := (cosetHeight_pos x _).le
  have key : cosetHeight x (upperPoint z v hv) * 9 ≤ 1 / v :=
    (mul_le_mul_of_nonneg_left h9 hh0).trans hb
  have key' := (le_div_iff₀ hv).mp key
  rw [le_div_iff₀ (by positivity)]
  calc cosetHeight x (upperPoint z v hv) * (9 * v) = cosetHeight x (upperPoint z v hv) * 9 * v := by
        ring
    _ ≤ 1 := key'

/-- For `g ∈ SL₂(ℤ)` with first column `(0, 1)`, every coset lifts `g p` to height `≤ 1/v`. -/
theorem cosetHeight_rational_le (g : SL(2, ℤ)) (hg0 : g 0 0 = 0) (hg1 : g 1 0 = 1)
    (x : CuspCosets) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    cosetHeight x (rationalComplex g • upperPoint z v hv) ≤ 1 / v := by
  set N : SL(2, O) := ((Quotient.out x : levelThree) : SL(2, O))
  have hentry : (N * rationalEmbedding g) 1 0 = N 1 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp [rationalEmbedding, hg0, hg1]
  have h11 : N 1 1 ≠ 0 := by
    intro h0
    have h3 := levelThree_entry (Quotient.out x) 1 1
    simp only [if_true] at h3
    change (3 : O) ∣ N 1 1 - 1 at h3
    rw [h0, zero_sub] at h3
    obtain ⟨k, hk⟩ := h3
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero, neg_eq_zero] at hk
      exact one_ne_zero hk
    have hn := one_le_normSq_embedding k hk0
    have hc := congrArg (fun t => Complex.normSq (ringComplex t)) hk
    simp only [map_neg, map_one, Complex.normSq_neg, map_mul, map_ofNat ringComplex 3] at hc
    have h9 : Complex.normSq (3 : ℂ) = 9 := by norm_num [Complex.normSq_apply]
    rw [h9] at hc
    linarith
  have hc : (N * rationalEmbedding g) 1 0 ≠ 0 := by rwa [hentry]
  have hb := cosetHeight_translate_le (rationalEmbedding g) x z v hv hc
  have hn := one_le_normSq_embedding _ hc
  rw [Complex.normSq_eq_norm_sq] at hn
  have hh0 : 0 ≤ cosetHeight x (rationalComplex g • upperPoint z v hv) := (cosetHeight_pos x _).le
  calc cosetHeight x (rationalComplex g • upperPoint z v hv)
      ≤ cosetHeight x (rationalComplex g • upperPoint z v hv) *
          ‖ringComplex ((N * rationalEmbedding g) 1 0)‖ ^ 2 := le_mul_of_one_le_right hh0 hn
    _ ≤ 1 / v := hb

/-! ### The cutoff series at the standard strip -/

/-- At `z + jv`, a profile vanishing on `(1, 1/(9v)]` sees only the identity coset. -/
theorem cuspCutoffCorrection_upper (F : ℝ → ℂ) (z : ℂ) (v : ℝ) (hv : 0 < v)
    (hF : ∀ t : ℝ, 1 < t → t ≤ 1 / (9 * v) → F t = 0) :
    cuspCutoffCorrection 1 F (upperPoint z v hv) = if 1 < v then F v else 0 := by
  rw [cuspCutoffCorrection, tsum_eq_single (cosetOf 1)]
  · rw [cuspCutoffTerm, cosetHeight_cosetOf, map_one, one_smul, hyperbolicHeight_upperPoint,
      cosetCharacter_cosetOf, map_one, inv_one, one_mul]
  · intro x hx
    rw [cuspCutoffTerm]
    split_ifs with h
    · rw [hF _ h (cosetHeight_upper_le x hx z v hv), mul_zero]
    · rfl

/-- Through a rational translate with first column `(0, 1)`, a profile vanishing on `(1, 1/v]` gives
zero. -/
theorem cuspCutoffCorrection_rational (F : ℝ → ℂ) (g : SL(2, ℤ)) (hg0 : g 0 0 = 0) (hg1 : g 1 0 = 1)
    (z : ℂ) (v : ℝ) (hv : 0 < v) (hF : ∀ t : ℝ, 1 < t → t ≤ 1 / v → F t = 0) :
    cuspCutoffCorrection 1 F (rationalComplex g • upperPoint z v hv) = 0 := by
  rw [cuspCutoffCorrection]
  refine (tsum_congr fun x => ?_).trans tsum_zero
  rw [cuspCutoffTerm]
  split_ifs with h
  · rw [hF _ h (cosetHeight_rational_le g hg0 hg1 x z v hv), mul_zero]
  · rfl

/-! ### The subtraction -/

/-- The growth profile `f_S = 1_S v^{4/3}`. -/
def growthProfile (S : Set ℝ) (v : ℝ) : ℂ := S.indicator (fun v => ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ)) v

theorem conj_growthProfile (S : Set ℝ) (v : ℝ) : conj (growthProfile S v) = growthProfile S v := by
  rw [growthProfile]
  by_cases h : v ∈ S
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- The rational cusp representatives `1, S, ST, ST²`. -/
abbrev rationalRep : RationalFourCusp → SL(2, ℤ) := rationalFourCuspRep

theorem rationalRep_column (q : RationalFourCusp) (hq : q ≠ .inl ()) :
    rationalRep q 0 0 = 0 ∧ rationalRep q 1 0 = 1 := by
  rcases q with _ | _ | _ | _
  · exact absurd rfl hq
  · simp [rationalRep, rationalFourCuspRep, ModularGroup.coe_S]
  · simp [rationalRep, rationalFourCuspRep, ModularGroup.coe_S, ModularGroup.coe_T,
      Matrix.mul_apply, Fin.sum_univ_two]
  · simp [rationalRep, rationalFourCuspRep, ModularGroup.coe_S, ModularGroup.coe_T, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- `H_S(w) = c² Σ_q conj(E_1(r_q w ∣ f_S))`. -/
def cuspSubtraction (c : ℂ) (S : Set ℝ) (w : HyperbolicSpace) : ℂ :=
  c ^ 2 * ∑ q : RationalFourCusp,
    conj (cuspCutoffCorrection 1 (growthProfile S) (rationalComplex (rationalRep q) • w))

/-- **The subtraction at the standard strip.** For `S ⊆ [2, ∞)` and `v > 1/2`: `H_S(z + jv) = c² f_S(v)`. -/
theorem cuspSubtraction_upper (c : ℂ) (S : Set ℝ) (hS : S ⊆ Set.Ici 2) (z : ℂ) (v : ℝ) (hv : 0 < v)
    (hv2 : 1 / 2 < v) :
    cuspSubtraction c S (upperPoint z v hv) = c ^ 2 * growthProfile S v := by
  have hzero : ∀ t : ℝ, t < 2 → growthProfile S t = 0 := fun t ht =>
    Set.indicator_of_notMem (fun h => absurd (hS h) (not_le.mpr ht)) _
  have hsmall : 1 / v < 2 := by
    rw [div_lt_iff₀ hv]
    linarith
  rw [cuspSubtraction, Fintype.sum_eq_single (.inl ())]
  · have h1 : rationalComplex (rationalRep (.inl ())) • upperPoint z v hv = upperPoint z v hv := by
      simp [rationalRep, rationalFourCuspRep]
    rw [h1, cuspCutoffCorrection_upper _ z v hv fun t _ ht => hzero t (by
      have : 1 / (9 * v) ≤ 1 / v := by
        apply div_le_div_of_nonneg_left zero_le_one hv
        linarith
      linarith)]
    split_ifs with h
    · rw [conj_growthProfile]
    · rw [hzero v (by linarith [not_lt.mp h]), map_zero]
  · intro q hq
    obtain ⟨h0, h1⟩ := rationalRep_column q hq
    rw [cuspCutoffCorrection_rational _ _ h0 h1 z v hv fun t _ ht => hzero t (by linarith),
      map_zero]

/-- `conj κ = κ⁻¹`. -/
theorem conj_complexCharacter (M : levelThree) : conj (complexCharacter M) = (complexCharacter M)⁻¹ :=
  (Complex.inv_eq_conj (norm_complexCharacter M)).symm

/-- Each rational translate of the cutoff series picks up `κ⁻¹` after conjugation. -/
theorem conj_cutoff_rational_automorphy (S : Set ℝ) (r : SL(2, ℤ)) (M : levelThree) (w : HyperbolicSpace) :
    conj (cuspCutoffCorrection 1 (growthProfile S) (rationalComplex r • (complexMatrix M • w))) =
      (complexCharacter M)⁻¹ * conj (cuspCutoffCorrection 1 (growthProfile S) (rationalComplex r • w)) := by
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
  rw [hmove, cuspCutoffCorrection_automorphy 1 le_rfl, complexCharacter_conjugate_rational, map_mul,
    conj_complexCharacter]

/-- `H_S` has the multiplier `κ⁻¹` of `θ_s²`. -/
theorem cuspSubtraction_automorphy (c : ℂ) (S : Set ℝ) (M : levelThree) (w : HyperbolicSpace) :
    cuspSubtraction c S (complexMatrix M • w) = (complexCharacter M)⁻¹ * cuspSubtraction c S w := by
  simp only [cuspSubtraction, conj_cutoff_rational_automorphy, ← Finset.mul_sum]
  ring

/-! ### Translating the fundamental set -/

/-- The action of `g` as a homeomorphism. -/
def actionHomeomorph (g : SL(2, ℂ)) : HyperbolicSpace ≃ₜ HyperbolicSpace where
  toFun w := g • w
  invFun w := g⁻¹ • w
  left_inv w := inv_smul_smul g w
  right_inv w := smul_inv_smul g w
  continuous_toFun := continuous_hyperbolic_action g
  continuous_invFun := continuous_hyperbolic_action g⁻¹

theorem actionHomeomorph_measurePreserving (g : SL(2, ℂ)) :
    MeasurePreserving (actionHomeomorph g) hyperbolicVolume hyperbolicVolume :=
  ⟨(actionHomeomorph g).continuous.measurable, hyperbolicVolume_invariant g⟩

/-- **Translation invariance of `∫_{D_Γ}`.** For `g ∈ SL₂(ℤ[ω])` and `F` invariant under `Γ`:
`∫_{D_Γ} F(g w) dμ = ∫_{D_Γ} F dμ`. -/
theorem setIntegral_levelSet_translate (g : SL(2, O)) (F : HyperbolicSpace → ℂ)
    (hF : ∀ (M : levelThree) (w : HyperbolicSpace), F (complexMatrix M • w) = F w) :
    ∫ w in levelSet, F (integralComplexMatrix g • w) ∂hyperbolicVolume =
      ∫ w in levelSet, F w ∂hyperbolicVolume := by
  set φ := actionHomeomorph (integralComplexMatrix g)
  have hmp := actionHomeomorph_measurePreserving (integralComplexMatrix g)
  have hmp' : MeasurePreserving φ.symm hyperbolicVolume hyperbolicVolume :=
    actionHomeomorph_measurePreserving (integralComplexMatrix g)⁻¹
  have himg := hmp.setIntegral_image_emb φ.measurableEmbedding F levelSet
  change ∫ w in levelSet, F (φ w) ∂hyperbolicVolume = _
  rw [← himg]
  have hD := hyperbolicFundamentalSet_isFundamentalDomain levelThree le_rfl hyperbolicVolume
  let e : levelThree ≃ levelThree :=
    { toFun := levelThreeConjugate g⁻¹
      invFun := levelThreeConjugate g
      left_inv := fun M => by
        rw [← levelThreeConjugate_mul, mul_inv_cancel, levelThreeConjugate_one]
      right_inv := fun M => by
        rw [← levelThreeConjugate_mul, inv_mul_cancel, levelThreeConjugate_one] }
  have hD' : IsFundamentalDomain levelThree (φ '' levelSet) hyperbolicVolume := by
    refine hD.image_of_equiv φ.toEquiv hmp'.quasiMeasurePreserving e fun M => ?_
    intro w
    change integralComplexMatrix g • (integralComplexMatrix (g⁻¹ * (M : SL(2, O)) * g⁻¹⁻¹) • w) =
      integralComplexMatrix (M : SL(2, O)) • (integralComplexMatrix g • w)
    rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul, inv_inv]
    congr 2
    group
  exact hD'.setIntegral_eq hD fun M w => hF M w

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
