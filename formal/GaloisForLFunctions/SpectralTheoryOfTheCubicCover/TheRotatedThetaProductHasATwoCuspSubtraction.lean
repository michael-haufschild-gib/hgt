import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheThetaFunctionHasALinearCuspSubtraction

/-!
# The rotated theta product has a two-cusp subtraction

The rotation `R = diag(ω, ω²)` acts by `z + jv ↦ ω²z + jv`, has order three and normalizes `Γ`;
`S R = R⁻¹ S`. The product

`F_R(w) = θ_s(Rw) θ_s(R⁻¹w)`   (`rotatedThetaProduct`)

has the multiplier `κ⁻¹` of `θ_s²` (`rotatedThetaProduct_automorphy`): the Kubota symbols of the
conjugates `RnR⁻¹ = [[a, ω²b], [ωc, d]]` and `R⁻¹nR = [[a, ωb], [ω²c, d]]` multiply to `(c/a)₃²`
(`complexCharacter_rotation_pair`).

**Two cusps.** With `h` the linear subtraction of `θ_s` (`thetaLinear`), pointwise
(`thetaLinear_rotation_mul`)

`h(Rw) h(R⁻¹w) = c² (conj E_1(w ∣ f) + conj E_1(Sw ∣ f))`,   `f = 1_{[2,∞)} v^{4/3}`   (`rotatedSubtraction`).

The high coset of `Rw` is `RnR⁻¹` when `n` is the high coset of `w`, so
`E_1(Rw ∣ g) E_1(R⁻¹w ∣ g) = conj E_1(w ∣ g²)` (`cutoff_rotation_mul`). The mixed terms
`E_1(r_q Rw) E_1(r_{q'} R⁻¹w)` vanish: two high cosets would make `(r_{q'} R r_q⁻¹)₁₀ = ω c'd − ω² d'c`
divisible by `3` (`rotation_cross_zero`), i.e. `3 ∣ c'd` and `3 ∣ d'c` for the bottom rows `(c, d)`,
`(c', d')` of `r_q, r_{q'}` — only `q = q' ∈ {1, S}`. So `R` keeps the cusps `∞, 0` and sends the
other two rational cusps to the ramified classes.

**Boundedness** (`rotatedRenormalized_bounded`): `F_R − h(R·)h(R⁻¹·) = (θ_s − h)(R·) θ_s(R⁻¹·) +
h(R·)(θ_s − h)(R⁻¹·)`, and through every cusp `|θ_s − h| ≤ B/(1 + v^{2/3})`, `|θ_s|, |h| ≤ A(1 + v^{2/3})`
(`thetaLinear_bounds`, after Bianchi reduction): `G_R = F_R − H_R` is bounded by `2AB`.
-/

noncomputable section

open MeasureTheory Filter Function
open scoped BigOperators Classical MatrixGroups ComplexConjugate

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicEisenstein.RationalSource
  MetaplecticMobiusDescent.CubicJacobi

theorem omega_cube : omega ^ 3 = 1 := omega_primitive.pow_eq_one

/-! ### The rotation -/

/-- The rotation `R = diag(ω, ω²)`. -/
def rotation : SL(2, O) := ⟨!![omega, 0; 0, omega ^ 2], by
  rw [Matrix.det_fin_two_of]
  linear_combination omega_cube⟩

@[simp] theorem rotation_apply_00 : rotation 0 0 = omega := rfl
@[simp] theorem rotation_apply_01 : rotation 0 1 = 0 := rfl
@[simp] theorem rotation_apply_10 : rotation 1 0 = 0 := rfl
@[simp] theorem rotation_apply_11 : rotation 1 1 = omega ^ 2 := rfl

section SL2Inverse
variable {R : Type*} [CommRing R] (A : SL(2, R))
@[simp] theorem SL2_inv_00 : (A⁻¹ : SL(2, R)) 0 0 = A 1 1 := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
@[simp] theorem SL2_inv_01 : (A⁻¹ : SL(2, R)) 0 1 = -A 0 1 := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
@[simp] theorem SL2_inv_10 : (A⁻¹ : SL(2, R)) 1 0 = -A 1 0 := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
@[simp] theorem SL2_inv_11 : (A⁻¹ : SL(2, R)) 1 1 = A 0 0 := by rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; rfl
end SL2Inverse

theorem rotation_cube : rotation * rotation * rotation = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination omega_cube | linear_combination (omega ^ 3 + 1) * omega_cube

theorem rotation_inv_mul_inv : rotation⁻¹ * rotation⁻¹ = rotation := by
  rw [← mul_inv_rev]
  exact (eq_inv_of_mul_eq_one_right rotation_cube).symm

/-- `S R = R⁻¹ S`. -/
theorem S_mul_rotation : rationalEmbedding ModularGroup.S * rotation = rotation⁻¹ * rationalEmbedding ModularGroup.S := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, rationalEmbedding, ModularGroup.coe_S]

/-- `S R⁻¹ = R S`. -/
theorem S_mul_rotation_inv :
    rationalEmbedding ModularGroup.S * rotation⁻¹ = rotation * rationalEmbedding ModularGroup.S := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, rationalEmbedding, ModularGroup.coe_S]

/-- A unit-diagonal upper triangular matrix keeps heights. -/
theorem height_unitDiag (g : SL(2, O)) (h10 : g 1 0 = 0) (hu : IsUnit (g 1 1)) (w : HyperbolicSpace) :
    hyperbolicHeight (integralComplexMatrix g • w) = hyperbolicHeight w := by
  obtain ⟨z, v, hv, rfl⟩ := upperPoint_surjective w
  rw [height_upperTriangular g h10 hu z v hv, hyperbolicHeight_upperPoint]

theorem height_rotation (w : HyperbolicSpace) :
    hyperbolicHeight (integralComplexMatrix rotation • w) = hyperbolicHeight w :=
  height_unitDiag _ rfl ((omega_primitive.isUnit (by decide)).pow 2) w

theorem height_rotation_inv (w : HyperbolicSpace) :
    hyperbolicHeight (integralComplexMatrix rotation⁻¹ • w) = hyperbolicHeight w :=
  height_unitDiag _ (by simp [Matrix.adjugate_fin_two])
    (by simpa [Matrix.adjugate_fin_two] using omega_primitive.isUnit (by decide)) w

/-- Moving a level-three matrix through `g`: `g n w = (g n g⁻¹)(g w)`. -/
theorem conj_smul (g : SL(2, O)) (n : levelThree) (y : HyperbolicSpace) :
    integralComplexMatrix g • (complexMatrix n • y) =
      complexMatrix (levelThreeConjugate g n) • (integralComplexMatrix g • y) := by
  rw [← mul_smul, ← mul_smul]
  congr 1
  change integralComplexMatrix g * integralComplexMatrix (n : SL(2, O)) =
    integralComplexMatrix (g * (n : SL(2, O)) * g⁻¹) * integralComplexMatrix g
  rw [← map_mul, ← map_mul]
  congr 1
  group

/-- `κ(RnR⁻¹) κ(R⁻¹nR) = κ(n)²`: the symbols are `(ωc/a)₃` and `(ω²c/a)₃`. -/
theorem complexCharacter_rotation_pair (n : levelThree) :
    complexCharacter (levelThreeConjugate rotation n) * complexCharacter (levelThreeConjugate rotation⁻¹ n) =
      complexCharacter n ^ 2 := by
  set a := (n : SL(2, O)) 0 0
  set c := (n : SL(2, O)) 1 0
  have h10 : ((levelThreeConjugate rotation n : levelThree) : SL(2, O)) 1 0 = omega ^ 4 * c := by
    change (rotation * (n : SL(2, O)) * rotation⁻¹) 1 0 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, c]
    ring
  have h00 : ((levelThreeConjugate rotation n : levelThree) : SL(2, O)) 0 0 = a := by
    change (rotation * (n : SL(2, O)) * rotation⁻¹) 0 0 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, a]
    linear_combination (n : SL(2, O)) 0 0 * omega_cube
  have h10' : ((levelThreeConjugate rotation⁻¹ n : levelThree) : SL(2, O)) 1 0 = omega ^ 2 * c := by
    change (rotation⁻¹ * (n : SL(2, O)) * rotation⁻¹⁻¹) 1 0 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, c]
    ring
  have h00' : ((levelThreeConjugate rotation⁻¹ n : levelThree) : SL(2, O)) 0 0 = a := by
    change (rotation⁻¹ * (n : SL(2, O)) * rotation⁻¹⁻¹) 0 0 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, a]
    linear_combination (n : SL(2, O)) 0 0 * omega_cube
  change ringComplex (value _) * ringComplex (value _) = ringComplex (value n) ^ 2
  rw [← map_mul, ← map_pow]
  congr 1
  simp only [value]
  rw [h10, h00, h10', h00', ← symbol_mul_numerator, pow_two (symbol c a), ← symbol_mul_numerator]
  congr 1
  linear_combination c ^ 2 * (omega ^ 3 + 1) * omega_cube

/-! ### The rotated product -/

/-- `F_R(w) = θ_s(Rw) θ_s(R⁻¹w)`. -/
def rotatedThetaProduct (w : HyperbolicSpace) : ℂ :=
  sourceTheta (integralComplexMatrix rotation • w) * sourceTheta (integralComplexMatrix rotation⁻¹ • w)

theorem complexCharacter_sq_eq_inv (M : levelThree) : complexCharacter M ^ 2 = (complexCharacter M)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← pow_succ']; exact complexCharacter_cube M)

/-- `F_R` has the multiplier `κ⁻¹`. -/
theorem rotatedThetaProduct_automorphy (M : levelThree) (w : HyperbolicSpace) :
    rotatedThetaProduct (complexMatrix M • w) = (complexCharacter M)⁻¹ * rotatedThetaProduct w := by
  rw [rotatedThetaProduct, rotatedThetaProduct, conj_smul, conj_smul, sourceTheta_automorphy,
    sourceTheta_automorphy, ← complexCharacter_sq_eq_inv, ← complexCharacter_rotation_pair]
  ring

theorem rotatedThetaProduct_continuous : Continuous rotatedThetaProduct :=
  (cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).mul
    (cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _))

/-! ### Cutoff series under the rotation -/

theorem cutoff_eq_zero_of_low (F : ℝ → ℂ) (y : HyperbolicSpace)
    (h : ∀ n : levelThree, ¬ 1 < hyperbolicHeight (complexMatrix n • y)) :
    cuspCutoffCorrection 1 F y = 0 := by
  unfold cuspCutoffCorrection
  refine (tsum_congr fun x => ?_).trans tsum_zero
  obtain ⟨n, rfl⟩ := Quotient.exists_rep x
  rw [cuspCutoffTerm, if_neg]
  change ¬ 1 < cosetHeight (cosetOf n) y
  rw [cosetHeight_cosetOf]
  exact h n

theorem exists_high_of_cutoff_ne_zero (F : ℝ → ℂ) (y : HyperbolicSpace) (h : cuspCutoffCorrection 1 F y ≠ 0) :
    ∃ n : levelThree, 1 < hyperbolicHeight (complexMatrix n • y) := by
  by_contra hno
  push Not at hno
  exact h (cutoff_eq_zero_of_low F y fun n hn => (hno n).not_gt hn)

/-- High cosets move with the rotation: `n` high for `y` ⇔ `g n g⁻¹` high for `g y` (`g` unit diagonal). -/
theorem high_conj (g : SL(2, O)) (hg : ∀ w, hyperbolicHeight (integralComplexMatrix g • w) = hyperbolicHeight w)
    (n : levelThree) (y : HyperbolicSpace) :
    hyperbolicHeight (complexMatrix (levelThreeConjugate g n) • (integralComplexMatrix g • y)) =
      hyperbolicHeight (complexMatrix n • y) := by
  rw [← conj_smul, hg]

/-- `E_1(Ry ∣ g) E_1(R⁻¹y ∣ g) = conj E_1(y ∣ g²)` for real `g`. -/
theorem cutoff_rotation_mul (F : ℝ → ℂ) (hF : ∀ t, conj (F t) = F t) (y : HyperbolicSpace) :
    cuspCutoffCorrection 1 F (integralComplexMatrix rotation • y) *
        cuspCutoffCorrection 1 F (integralComplexMatrix rotation⁻¹ • y) =
      conj (cuspCutoffCorrection 1 (fun t => F t * F t) y) := by
  by_cases hhigh : ∃ n : levelThree, 1 < hyperbolicHeight (complexMatrix n • y)
  · obtain ⟨n, hn⟩ := hhigh
    have h1 : 1 < cosetHeight (cosetOf (levelThreeConjugate rotation n)) (integralComplexMatrix rotation • y) := by
      rw [cosetHeight_cosetOf, high_conj _ height_rotation]
      exact hn
    have h2 : 1 < cosetHeight (cosetOf (levelThreeConjugate rotation⁻¹ n))
        (integralComplexMatrix rotation⁻¹ • y) := by
      rw [cosetHeight_cosetOf, high_conj _ height_rotation_inv]
      exact hn
    have h0 : 1 < cosetHeight (cosetOf n) y := by
      rw [cosetHeight_cosetOf]
      exact hn
    rw [cuspCutoffCorrection_eq 1 le_rfl F _ _ h1, cuspCutoffCorrection_eq 1 le_rfl F _ _ h2,
      cuspCutoffCorrection_eq 1 le_rfl _ _ _ h0]
    simp only [cosetCharacter_cosetOf, cosetHeight_cosetOf, high_conj _ height_rotation,
      high_conj _ height_rotation_inv]
    set t := hyperbolicHeight (complexMatrix n • y)
    have hp := complexCharacter_rotation_pair n
    have hk := complexCharacter_sq_eq_inv n
    have hne : complexCharacter n ≠ 0 := fun h => by
      have := norm_complexCharacter n
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have hc : conj ((complexCharacter n)⁻¹ * (F t * F t)) = complexCharacter n * (F t * F t) := by
      rw [map_mul, map_inv₀, conj_complexCharacter, inv_inv, map_mul, hF]
    rw [hc]
    calc (complexCharacter (levelThreeConjugate rotation n))⁻¹ * F t *
          ((complexCharacter (levelThreeConjugate rotation⁻¹ n))⁻¹ * F t)
        = (complexCharacter (levelThreeConjugate rotation n) *
            complexCharacter (levelThreeConjugate rotation⁻¹ n))⁻¹ * (F t * F t) := by
          rw [mul_inv]
          ring
      _ = complexCharacter n * (F t * F t) := by rw [hp, hk, inv_inv]
  · push Not at hhigh
    have hR : ∀ m : levelThree, ¬ 1 < hyperbolicHeight (complexMatrix m • (integralComplexMatrix rotation • y)) := by
      intro m hm
      have := high_conj rotation⁻¹ height_rotation_inv m (integralComplexMatrix rotation • y)
      rw [map_inv, inv_smul_smul] at this
      exact (hhigh _).not_gt (this ▸ hm)
    have hR' : ∀ m : levelThree, ¬ 1 < hyperbolicHeight (complexMatrix m • (integralComplexMatrix rotation⁻¹ • y)) := by
      intro m hm
      have := high_conj rotation height_rotation m (integralComplexMatrix rotation⁻¹ • y)
      rw [map_inv, smul_inv_smul] at this
      exact (hhigh _).not_gt (this ▸ hm)
    rw [cutoff_eq_zero_of_low F _ hR, cutoff_eq_zero_of_low _ y fun m hm => (hhigh m).not_gt hm,
      zero_mul, map_zero]

/-! ### The mixed terms vanish -/

/-- Conjugating by level-three matrices does not change the bottom-left entry modulo `3`. -/
theorem levelThree_conj_lower (n n' : levelThree) (A : SL(2, O)) :
    ∃ k : O, ((n' : SL(2, O)) * A * (n : SL(2, O))⁻¹) 1 0 = A 1 0 + 3 * k := by
  obtain ⟨p, hp⟩ := levelThree_lower n'
  obtain ⟨q, hq⟩ := levelThree_entry n' 1 1
  obtain ⟨r, hr⟩ := levelThree_entry n⁻¹ 0 0
  obtain ⟨t, ht⟩ := levelThree_lower n⁻¹
  simp only [Fin.isValue, if_true] at hq hr
  have hinv : ((n⁻¹ : levelThree) : SL(2, O)) = (n : SL(2, O))⁻¹ := rfl
  rw [hinv] at hr ht
  set m := (n : SL(2, O))⁻¹
  refine ⟨p * (A 0 0 * m 0 0 + A 0 1 * m 1 0) + q * (A 1 0 * m 0 0 + A 1 1 * m 1 0) + A 1 0 * r +
    A 1 1 * t, ?_⟩
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (A 0 0 * m 0 0 + A 0 1 * m 1 0) * hp +
    (A 1 0 * m 0 0 + A 1 1 * m 1 0) * hq + A 1 0 * hr + A 1 1 * ht

/-- `3 ∣ ω α + ω² β` with `α, β ∈ ℤ` forces `3 ∣ α` and `3 ∣ β`. -/
theorem three_dvd_omega_combination (α β : ℤ) (h : (3 : O) ∣ omega * (α : O) + omega ^ 2 * (β : O)) :
    (3 : ℤ) ∣ α ∧ (3 : ℤ) ∣ β := by
  have hr := cuspResidue_of_three_dvd h
  rw [cuspResidue_add, mul_comm omega, mul_comm (omega ^ 2), cuspResidue_intCast_mul, cuspResidue_intCast_mul,
    cuspResidue_omega, cuspResidue_omega_sq] at hr
  simp only [mul_zero, mul_one, mul_neg, zero_add, Prod.mk.injEq] at hr
  have hβ : ((β : ℤ) : ZMod 3) = 0 := by linear_combination -hr.1
  have hα : ((α : ℤ) : ZMod 3) = 0 := by linear_combination hr.2 - hr.1
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd α 3).mp hα, (ZMod.intCast_zmod_eq_zero_iff_dvd β 3).mp hβ⟩

/-- The two rational cusps `∞, 0` kept by the rotation. -/
def fixedCusps : Finset RationalFourCusp := {.inl (), .inr (.inl ())}

/-- Only `q = q' ∈ {1, S}` have `3 ∣ c'd` and `3 ∣ d'c` (bottom rows of `r_q`, `r_{q'}`). -/
theorem rationalRep_pair_of_dvd (q q' : RationalFourCusp)
    (h : (3 : ℤ) ∣ rationalRep q' 1 0 * rationalRep q 1 1 ∧ (3 : ℤ) ∣ rationalRep q' 1 1 * rationalRep q 1 0) :
    q = q' ∧ q ∈ fixedCusps := by
  rcases q with ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ <;> rcases q' with ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ <;>
    simp [rationalRep, rationalFourCuspRep, ModularGroup.coe_S, ModularGroup.coe_T, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two, fixedCusps] at h ⊢ <;> norm_num at h

/-- **Mixed terms vanish.** Unless `q = q' ∈ {1, S}`, `E_1(r_q R w) E_1(r_{q'} R⁻¹ w) = 0`. -/
theorem rotation_cross_zero (F : ℝ → ℂ) (q q' : RationalFourCusp) (hq : ¬ (q = q' ∧ q ∈ fixedCusps))
    (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 F (rationalComplex (rationalRep q) • (integralComplexMatrix rotation • w)) *
      cuspCutoffCorrection 1 F (rationalComplex (rationalRep q') • (integralComplexMatrix rotation⁻¹ • w)) = 0 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨n, hn⟩ := exists_high_of_cutoff_ne_zero F _ h1
  obtain ⟨n', hn'⟩ := exists_high_of_cutoff_ne_zero F _ h2
  set g₁ : SL(2, O) := (n : SL(2, O)) * rationalEmbedding (rationalRep q) * rotation
  set g₂ : SL(2, O) := (n' : SL(2, O)) * rationalEmbedding (rationalRep q') * rotation⁻¹
  have e1 : complexMatrix n • (rationalComplex (rationalRep q) • (integralComplexMatrix rotation • w)) =
      integralComplexMatrix g₁ • w := by
    rw [← mul_smul, ← mul_smul]
    rfl
  have e2 : complexMatrix n' • (rationalComplex (rationalRep q') • (integralComplexMatrix rotation⁻¹ • w)) =
      integralComplexMatrix g₂ • w := by
    rw [← mul_smul, ← mul_smul]
    rfl
  rw [e1] at hn
  rw [e2] at hn'
  set A : SL(2, O) := rationalEmbedding (rationalRep q') * rotation * rationalEmbedding (rationalRep q)⁻¹
  have hg : g₂ * g₁⁻¹ = (n' : SL(2, O)) * A * (n : SL(2, O))⁻¹ := by
    simp only [g₁, g₂, A, mul_inv_rev, map_inv]
    rw [show (n' : SL(2, O)) * rationalEmbedding (rationalRep q') * rotation⁻¹ *
        (rotation⁻¹ * ((rationalEmbedding (rationalRep q))⁻¹ * (n : SL(2, O))⁻¹)) =
        (n' : SL(2, O)) * rationalEmbedding (rationalRep q') * (rotation⁻¹ * rotation⁻¹) *
          (rationalEmbedding (rationalRep q))⁻¹ * (n : SL(2, O))⁻¹ by group, rotation_inv_mul_inv]
  have h0 : (g₂ * g₁⁻¹) 1 0 = 0 := by
    by_contra hc
    have hp := integral_hyperbolicHeight_mul_le_one (g₂ * g₁⁻¹) hc (integralComplexMatrix g₁ • w)
    rw [map_mul, map_inv, mul_smul, inv_smul_smul] at hp
    nlinarith
  obtain ⟨k, hk⟩ := levelThree_conj_lower n n' A
  rw [← hg, h0] at hk
  have hA : A 1 0 = omega * ((rationalRep q' 1 0 * rationalRep q 1 1 : ℤ) : O) +
      omega ^ 2 * ((-(rationalRep q' 1 1 * rationalRep q 1 0) : ℤ) : O) := by
    simp only [A, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ← map_inv]
    simp [rationalEmbedding]
    ring
  have h3 : (3 : O) ∣ omega * ((rationalRep q' 1 0 * rationalRep q 1 1 : ℤ) : O) +
      omega ^ 2 * ((-(rationalRep q' 1 1 * rationalRep q 1 0) : ℤ) : O) :=
    ⟨-k, by rw [← hA]; linear_combination -hk⟩
  obtain ⟨hα, hβ⟩ := three_dvd_omega_combination _ _ h3
  exact hq (rationalRep_pair_of_dvd q q' ⟨hα, (Int.dvd_neg).mp hβ⟩)

/-! ### The pointwise identity -/

/-- `H_R(w) = c² Σ_{q ∈ {1, S}} conj E_1(r_q w ∣ 1_{[2,∞)} v^{4/3})`. -/
def rotatedSubtraction (w : HyperbolicSpace) : ℂ :=
  thetaCoeff ^ 2 * ∑ q ∈ fixedCusps,
    conj (cuspCutoffCorrection 1 (growthProfile (Set.Ici 2)) (rationalComplex (rationalRep q) • w))

theorem cutoff_thin_rotation_mul (y : HyperbolicSpace) :
    cuspCutoffCorrection 1 (thinProfile (Set.Ici 2)) (integralComplexMatrix rotation • y) *
        cuspCutoffCorrection 1 (thinProfile (Set.Ici 2)) (integralComplexMatrix rotation⁻¹ • y) =
      conj (cuspCutoffCorrection 1 (growthProfile (Set.Ici 2)) y) := by
  rw [cutoff_rotation_mul _ (conj_thinProfile _)]
  congr 2
  funext t
  exact thinProfile_mul_self _ le_rfl t

/-- The diagonal terms. -/
theorem rotation_diag (q : RationalFourCusp) (hq : q ∈ fixedCusps) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 (thinProfile (Set.Ici 2))
        (rationalComplex (rationalRep q) • (integralComplexMatrix rotation • w)) *
      cuspCutoffCorrection 1 (thinProfile (Set.Ici 2))
        (rationalComplex (rationalRep q) • (integralComplexMatrix rotation⁻¹ • w)) =
      conj (cuspCutoffCorrection 1 (growthProfile (Set.Ici 2)) (rationalComplex (rationalRep q) • w)) := by
  simp only [fixedCusps, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · simp only [rationalRep, rationalFourCuspRep, map_one, one_smul]
    exact cutoff_thin_rotation_mul w
  · have e1 : rationalComplex (rationalRep (.inr (.inl ()))) • (integralComplexMatrix rotation • w) =
        integralComplexMatrix rotation⁻¹ • (rationalComplex (rationalRep (.inr (.inl ()))) • w) := by
      change integralComplexMatrix (rationalEmbedding ModularGroup.S) • (integralComplexMatrix rotation • w) =
        integralComplexMatrix rotation⁻¹ • (integralComplexMatrix (rationalEmbedding ModularGroup.S) • w)
      rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul, S_mul_rotation]
    have e2 : rationalComplex (rationalRep (.inr (.inl ()))) • (integralComplexMatrix rotation⁻¹ • w) =
        integralComplexMatrix rotation • (rationalComplex (rationalRep (.inr (.inl ()))) • w) := by
      change integralComplexMatrix (rationalEmbedding ModularGroup.S) • (integralComplexMatrix rotation⁻¹ • w) =
        integralComplexMatrix rotation • (integralComplexMatrix (rationalEmbedding ModularGroup.S) • w)
      rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul, S_mul_rotation_inv]
    rw [e1, e2, mul_comm]
    exact cutoff_thin_rotation_mul _

/-- Every term of `h(Rw) h(R⁻¹w)`: diagonal on `{1, S}`, zero otherwise. -/
theorem rotation_term (q q' : RationalFourCusp) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 (thinProfile (Set.Ici 2))
        (rationalComplex (rationalRep q) • (integralComplexMatrix rotation • w)) *
      cuspCutoffCorrection 1 (thinProfile (Set.Ici 2))
        (rationalComplex (rationalRep q') • (integralComplexMatrix rotation⁻¹ • w)) =
      if q = q' ∧ q ∈ fixedCusps then
        conj (cuspCutoffCorrection 1 (growthProfile (Set.Ici 2)) (rationalComplex (rationalRep q) • w)) else 0 := by
  split_ifs with h
  · obtain ⟨rfl, hq⟩ := h
    exact rotation_diag q hq w
  · exact rotation_cross_zero _ q q' h w

/-- **The rotated subtraction is a product.** `h(Rw) h(R⁻¹w) = H_R(w)`. -/
theorem thetaLinear_rotation_mul (w : HyperbolicSpace) :
    thetaLinear (integralComplexMatrix rotation • w) * thetaLinear (integralComplexMatrix rotation⁻¹ • w) =
      rotatedSubtraction w := by
  simp only [thetaLinear, linearSubtraction, rotatedSubtraction]
  rw [show thetaCoeff * (∑ q : RationalFourCusp, cuspCutoffCorrection 1 (thinProfile (Set.Ici 2))
        (rationalComplex (rationalRep q) • (integralComplexMatrix rotation • w))) *
      (thetaCoeff * ∑ q : RationalFourCusp, cuspCutoffCorrection 1 (thinProfile (Set.Ici 2))
        (rationalComplex (rationalRep q) • (integralComplexMatrix rotation⁻¹ • w))) =
      thetaCoeff ^ 2 * ((∑ q : RationalFourCusp, cuspCutoffCorrection 1 (thinProfile (Set.Ici 2))
        (rationalComplex (rationalRep q) • (integralComplexMatrix rotation • w))) *
      ∑ q : RationalFourCusp, cuspCutoffCorrection 1 (thinProfile (Set.Ici 2))
        (rationalComplex (rationalRep q) • (integralComplexMatrix rotation⁻¹ • w))) by ring]
  congr 1
  rw [Finset.sum_mul_sum]
  simp only [rotation_term, ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem rotatedSubtraction_automorphy (M : levelThree) (w : HyperbolicSpace) :
    rotatedSubtraction (complexMatrix M • w) = (complexCharacter M)⁻¹ * rotatedSubtraction w := by
  simp only [rotatedSubtraction, conj_cutoff_rational_automorphy, ← Finset.mul_sum]
  ring

theorem rotatedSubtraction_measurable : Measurable rotatedSubtraction := by
  unfold rotatedSubtraction
  refine measurable_const.mul (Finset.measurable_sum _ fun q _ => ?_)
  exact Complex.continuous_conj.measurable.comp
    ((cuspCutoffCorrection_measurable 1 _ (growthProfile_measurable _ measurableSet_Ici)).comp
      (continuous_hyperbolic_action _).measurable)

/-! ### The renormalized rotated product -/

/-- `G_R = F_R − H_R`. -/
def rotatedRenormalized (w : HyperbolicSpace) : ℂ := rotatedThetaProduct w - rotatedSubtraction w

theorem rotatedRenormalized_automorphy (M : levelThree) (w : HyperbolicSpace) :
    rotatedRenormalized (complexMatrix M • w) = (complexCharacter M)⁻¹ * rotatedRenormalized w := by
  rw [rotatedRenormalized, rotatedRenormalized, rotatedThetaProduct_automorphy, rotatedSubtraction_automorphy]
  ring

theorem rotatedRenormalized_measurable : Measurable rotatedRenormalized :=
  rotatedThetaProduct_continuous.measurable.sub rotatedSubtraction_measurable

/-- **`G_R = F_R − H_R` is bounded on hyperbolic three-space.** -/
theorem rotatedRenormalized_bounded : ∃ B : ℝ, ∀ w : HyperbolicSpace, ‖rotatedRenormalized w‖ ≤ B := by
  obtain ⟨A, B, hA, hB, hbd⟩ := thetaLinear_bounds
  refine ⟨2 * A * B, fun w => ?_⟩
  obtain ⟨M, z, v, hv, hMw, -, hfloor⟩ := bianchi_reduction_height_floor w
  have hw : w = integralComplexMatrix M⁻¹ • upperPoint z v hv := by
    rw [← hMw, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have e1 : integralComplexMatrix rotation • w = integralComplexMatrix (rotation * M⁻¹) • upperPoint z v hv := by
    rw [hw, ← mul_smul, ← map_mul]
  have e2 : integralComplexMatrix rotation⁻¹ • w =
      integralComplexMatrix (rotation⁻¹ * M⁻¹) • upperPoint z v hv := by
    rw [hw, ← mul_smul, ← map_mul]
  obtain ⟨hθ1, hh1, hd1⟩ := hbd (rotation * M⁻¹) z v hv hfloor
  obtain ⟨hθ2, hh2, hd2⟩ := hbd (rotation⁻¹ * M⁻¹) z v hv hfloor
  rw [rotatedRenormalized, rotatedThetaProduct, ← thetaLinear_rotation_mul, e1, e2]
  set a₁ := sourceTheta (integralComplexMatrix (rotation * M⁻¹) • upperPoint z v hv)
  set b₁ := thetaLinear (integralComplexMatrix (rotation * M⁻¹) • upperPoint z v hv)
  set a₂ := sourceTheta (integralComplexMatrix (rotation⁻¹ * M⁻¹) • upperPoint z v hv)
  set b₂ := thetaLinear (integralComplexMatrix (rotation⁻¹ * M⁻¹) • upperPoint z v hv)
  set p := 1 + v ^ ((2 : ℝ) / 3)
  have hp : 0 < p := by positivity
  have key : a₁ * a₂ - b₁ * b₂ = (a₁ - b₁) * a₂ + b₁ * (a₂ - b₂) := by ring
  have t1 : ‖a₁ - b₁‖ * ‖a₂‖ ≤ A * B := by
    calc ‖a₁ - b₁‖ * ‖a₂‖ ≤ ‖a₁ - b₁‖ * (A * p) := mul_le_mul_of_nonneg_left hθ2 (norm_nonneg _)
      _ = A * (‖a₁ - b₁‖ * p) := by ring
      _ ≤ A * B := mul_le_mul_of_nonneg_left hd1 hA
  have t2 : ‖b₁‖ * ‖a₂ - b₂‖ ≤ A * B := by
    calc ‖b₁‖ * ‖a₂ - b₂‖ ≤ (A * p) * ‖a₂ - b₂‖ := mul_le_mul_of_nonneg_right hh1 (norm_nonneg _)
      _ = A * (‖a₂ - b₂‖ * p) := by ring
      _ ≤ A * B := mul_le_mul_of_nonneg_left hd2 hA
  rw [key]
  calc ‖(a₁ - b₁) * a₂ + b₁ * (a₂ - b₂)‖ ≤ ‖a₁ - b₁‖ * ‖a₂‖ + ‖b₁‖ * ‖a₂ - b₂‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ 2 * A * B := by linarith

/-- `G_R` is square integrable on `D_Γ`. -/
theorem rotatedRenormalized_memLp :
    MemLp rotatedRenormalized 2 (hyperbolicVolume.restrict levelSet) := by
  haveI : IsFiniteMeasure (hyperbolicVolume.restrict levelSet) :=
    isFiniteMeasure_restrict.mpr levelSet_volume_lt_top.ne
  obtain ⟨B, hB⟩ := rotatedRenormalized_bounded
  exact MemLp.of_bound rotatedRenormalized_measurable.aestronglyMeasurable B (Eventually.of_forall hB)

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
