import GaloisForLFunctions.RHTower.FieldOnePadicBruhatFiniteLevel
import GaloisForLFunctions.RHTower.FieldOnePadicFourierNormalization

/-!
# Exact local Plancherel theorem on literal `ℚ_p`

The canonical standard additive character and unit-ball-normalized Haar
measure give an isometric Fourier transform on every compactly supported
locally constant complex function on `ℚ_p`.  The proof derives finite support
and translation depths from the function, proves the exact dual-lattice
support theorem, identifies coefficients with the canonical cyclic DFT, and
cancels the proved Haar Jacobians.  No Fourier isometry is assumed.
-/

namespace GaloisForLFunctions.RHTower
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Pointwise
variable (p : ℕ) [Fact p.Prime]

/-- Standard local Fourier transform on literal p-adic Bruhat functions. -/
def fieldOnePadicBruhatFourier (f : compactlySupportedLocallyConstant ℚ_[p])
    (y : ℚ_[p]) : ℂ :=
  ∫ x, fieldOnePadicStandardAddChar p (-(x * y)) * f.1 x
    ∂fieldOnePadicUnitBallNormalizedHaar p

def fieldOnePadicBruhatScaled (n : ℕ)
    (f : compactlySupportedLocallyConstant ℚ_[p]) : ℤ_[p] → ℂ :=
  fun u => f.1 (fieldOnePadicInvPowIntCoeAddMonoidHom p n u)

 theorem fieldOnePadicBruhatScaled_integrable (n : ℕ)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    Integrable (fieldOnePadicBruhatScaled p n f) (fieldOnePadicIntNormalizedHaar p) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact f.1.continuous.comp
      (fieldOnePadicInvPowIntCoeAddMonoidHom_isOpenEmbedding p n).continuous
  · exact HasCompactSupport.of_compactSpace _

 theorem fieldOnePadicBruhatScaled_normSq_integrable (n : ℕ)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    Integrable (fun u => (Complex.normSq (fieldOnePadicBruhatScaled p n f u) : ℂ))
      (fieldOnePadicIntNormalizedHaar p) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact Complex.continuous_ofReal.comp
      (Complex.continuous_normSq.comp (f.1.continuous.comp
        (fieldOnePadicInvPowIntCoeAddMonoidHom_isOpenEmbedding p n).continuous))
  · exact HasCompactSupport.of_compactSpace _

 theorem fieldOnePadicBruhatScaled_period
    (n m : ℕ) (f : compactlySupportedLocallyConstant ℚ_[p])
    (hperiod : ∀ x : ℚ_[p], ∀ z : ℤ_[p],
      f.1 (x + (p : ℚ_[p]) ^ m * (z : ℚ_[p])) = f.1 x) :
    ∀ u z : ℤ_[p], fieldOnePadicBruhatScaled p n f
      (u + (p : ℤ_[p]) ^ (n + m) * z) = fieldOnePadicBruhatScaled p n f u := by
  intro u z
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have harg : ((p : ℚ_[p]) ^ n)⁻¹ *
      ((u : ℚ_[p]) + (p : ℚ_[p]) ^ (n + m) * (z : ℚ_[p])) =
    ((p : ℚ_[p]) ^ n)⁻¹ * (u : ℚ_[p]) +
      (p : ℚ_[p]) ^ m * (z : ℚ_[p]) := by
    rw [mul_add]
    congr 1
    calc
      ((p : ℚ_[p]) ^ n)⁻¹ *
          ((p : ℚ_[p]) ^ (n + m) * (z : ℚ_[p])) =
          (((p : ℚ_[p]) ^ n)⁻¹ * (p : ℚ_[p]) ^ n) *
            ((p : ℚ_[p]) ^ m * (z : ℚ_[p])) := by rw [pow_add]; ring
      _ = (p : ℚ_[p]) ^ m * (z : ℚ_[p]) := by
        rw [inv_mul_cancel₀ (pow_ne_zero n hp0), one_mul]
  change f.1 ((fieldOnePadicInvPowIntCoeAddMonoidHom p n)
      (u + (p : ℤ_[p]) ^ (n + m) * z)) =
    f.1 ((fieldOnePadicInvPowIntCoeAddMonoidHom p n) u)
  change f.1 ((fieldOnePadicPrimeInvPowUnit p n : ℚ_[p]) *
      ((u + (p : ℤ_[p]) ^ (n + m) * z : ℤ_[p]) : ℚ_[p])) =
    f.1 ((fieldOnePadicPrimeInvPowUnit p n : ℚ_[p]) * (u : ℚ_[p]))
  rw [fieldOnePadicPrimeInvPowUnit_val]
  simp only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow,
    PadicInt.coe_natCast]
  rw [harg]
  exact hperiod _ z

 theorem fieldOnePadicBruhatFourier_invPow_coeff
    (n m : ℕ) (f : compactlySupportedLocallyConstant ℚ_[p])
    (hsupport : tsupport (f.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p n)
    (v : ℤ_[p]) :
    fieldOnePadicBruhatFourier p f
        (fieldOnePadicInvPowIntCoeAddMonoidHom p m v) =
      ((p : ℝ) ^ n : ℂ) *
        fieldOnePadicIntCyclicFourierIntegral p (n + m)
          (fieldOnePadicBruhatScaled p n f) (PadicInt.toZModPow (n + m) v) := by
  let N := n + m
  let h : ℚ_[p] → ℂ := fun x =>
    fieldOnePadicStandardAddChar p
      (-(x * fieldOnePadicInvPowIntCoeAddMonoidHom p m v)) * f.1 x
  have houtside : ∀ x, x ∉ Set.range
      (fieldOnePadicInvPowIntCoeAddMonoidHom p n) → h x = 0 := by
    intro x hx
    have hxstage : x ∉ (fieldOnePadicDenominatorStage p n : Set ℚ_[p]) := by
      simpa only [fieldOnePadicInvPowIntCoeAddMonoidHom_range] using hx
    have hxtsupport : x ∉ tsupport (f.1 : ℚ_[p] → ℂ) :=
      fun hxt => hxstage (hsupport hxt)
    simp [h, image_eq_zero_of_notMem_tsupport hxtsupport]
  rw [show fieldOnePadicBruhatFourier p f
      (fieldOnePadicInvPowIntCoeAddMonoidHom p m v) = ∫ x, h x
        ∂fieldOnePadicUnitBallNormalizedHaar p by rfl]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero houtside]
  rw [fieldOnePadic_setIntegral_invPowIntCoe]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  dsimp [h, fieldOnePadicBruhatScaled, fieldOnePadicInvPowIntCoeAddMonoidHom]
  rw [fieldOnePadicPrimeInvPowUnit_val,
    fieldOnePadicPrimeInvPowUnit_val]
  have hprod :
      -(((p : ℚ_[p]) ^ n)⁻¹ * (u : ℚ_[p]) *
        (((p : ℚ_[p]) ^ m)⁻¹ * (v : ℚ_[p]))) =
      (-((p : ℚ_[p]) ^ N)⁻¹) * ((u * v : ℤ_[p]) : ℚ_[p]) := by
    dsimp [N]
    rw [pow_add, mul_inv_rev]
    ring
  rw [hprod, fieldOnePadicStandardAddChar_neg_invPow_mul_coe]
  rw [map_mul]

 theorem fieldOnePadicStandardAddChar_eq_one_iff (x : ℚ_[p]) :
    fieldOnePadicStandardAddChar p x = 1 ↔
      x ∈ fieldOnePadicIntegralAddSubgroup p := by
  change Circle.coeHom (AddCircle.toCircle
    (fieldOnePadicStandardUnitAddCircleCharacter p x)) = 1 ↔ _
  rw [show Circle.coeHom (AddCircle.toCircle
      (fieldOnePadicStandardUnitAddCircleCharacter p x)) = 1 ↔
      AddCircle.toCircle
        (fieldOnePadicStandardUnitAddCircleCharacter p x) = 1 by
    exact Circle.coe_eq_one]
  rw [show AddCircle.toCircle
      (fieldOnePadicStandardUnitAddCircleCharacter p x) = 1 ↔
      fieldOnePadicStandardUnitAddCircleCharacter p x = 0 by
    rw [← AddCircle.toCircle_zero]
    exact ⟨fun h => AddCircle.injective_toCircle one_ne_zero h,
      fun h => congrArg AddCircle.toCircle h⟩]
  exact fieldOnePadicStandardUnitAddCircleCharacter_eq_zero_iff p x

 theorem fieldOnePadicBruhatFourier_eq_zero_outside_annihilator
    (m : ℕ) (f : compactlySupportedLocallyConstant ℚ_[p])
    (hperiod : ∀ x : ℚ_[p], ∀ z : ℤ_[p],
      f.1 (x + (p : ℚ_[p]) ^ m * (z : ℚ_[p])) = f.1 x)
    {y : ℚ_[p]}
    (hy : y ∉ (fieldOnePadicDenominatorStage p m : Set ℚ_[p])) :
    fieldOnePadicBruhatFourier p f y = 0 := by
  let a : ℚ_[p] := (p : ℚ_[p]) ^ m
  let c : ℂ := fieldOnePadicStandardAddChar p (-(a * y))
  let φ : ℚ_[p] → ℂ := fun x =>
    fieldOnePadicStandardAddChar p (-(x * y)) * f.1 x
  have hc : c ≠ 1 := by
    intro hc1
    have hint : -(a * y) ∈ fieldOnePadicIntegralAddSubgroup p :=
      (fieldOnePadicStandardAddChar_eq_one_iff p (-(a * y))).mp hc1
    have hint' : a * y ∈ fieldOnePadicIntegralAddSubgroup p := by
      exact neg_mem_iff.mp hint
    exact hy hint'
  have hφtrans : ∀ x : ℚ_[p], φ (x + a) = c * φ x := by
    intro x
    change fieldOnePadicStandardAddChar p (-((x + a) * y)) *
        f.1 (x + a) =
      fieldOnePadicStandardAddChar p (-(a * y)) *
        (fieldOnePadicStandardAddChar p (-(x * y)) * f.1 x)
    rw [show -((x + a) * y) = -(a * y) + -(x * y) by ring,
      AddChar.map_add_eq_mul]
    rw [show f.1 (x + a) = f.1 x by
      simpa [a] using hperiod x (1 : ℤ_[p])]
    ring
  have hfixed : fieldOnePadicBruhatFourier p f y = c * fieldOnePadicBruhatFourier p f y := by
    change (∫ x, φ x ∂fieldOnePadicUnitBallNormalizedHaar p) =
      c * ∫ x, φ x ∂fieldOnePadicUnitBallNormalizedHaar p
    calc
      (∫ x, φ x ∂fieldOnePadicUnitBallNormalizedHaar p) =
          ∫ x, φ (x + a) ∂fieldOnePadicUnitBallNormalizedHaar p :=
        (integral_add_right_eq_self φ a).symm
      _ = ∫ x, c * φ x ∂fieldOnePadicUnitBallNormalizedHaar p := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hφtrans x
      _ = c * ∫ x, φ x ∂fieldOnePadicUnitBallNormalizedHaar p :=
        integral_const_mul c φ
  by_contra hne
  apply hc
  apply mul_right_cancel₀ hne
  calc
    c * fieldOnePadicBruhatFourier p f y = fieldOnePadicBruhatFourier p f y := hfixed.symm
    _ = 1 * fieldOnePadicBruhatFourier p f y := by rw [one_mul]

omit [Fact p.Prime] in
private theorem fieldOnePadic_normSq_real_natCast_pow (n : ℕ) :
    Complex.normSq (((p : ℝ) : ℂ) ^ n) = ((p : ℝ) ^ n) ^ 2 := by
  rw [← Complex.ofReal_pow, Complex.normSq_ofReal, pow_two]

private theorem fieldOnePadicBruhatFourier_plancherel_of_finiteLevel
    (n m : ℕ) (f : compactlySupportedLocallyConstant ℚ_[p])
    (hsupport : tsupport (f.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p n)
    (hperiod : ∀ x : ℚ_[p], ∀ z : ℤ_[p],
      f.1 (x + (p : ℚ_[p]) ^ m * (z : ℚ_[p])) = f.1 x) :
    ∫ y, Complex.normSq (fieldOnePadicBruhatFourier p f y)
        ∂fieldOnePadicUnitBallNormalizedHaar p =
      ∫ x, Complex.normSq (f.1 x)
        ∂fieldOnePadicUnitBallNormalizedHaar p := by
  let N := n + m
  let g : ℤ_[p] → ℂ := fieldOnePadicBruhatScaled p n f
  let Q : ℤ_[p] → ℝ := fun v => Complex.normSq
    (fieldOnePadicIntCyclicFourierIntegral p N g
      (PadicInt.toZModPow N v))
  have hg : Integrable g (fieldOnePadicIntNormalizedHaar p) :=
    fieldOnePadicBruhatScaled_integrable p n f
  have hg2 : Integrable (fun u => (Complex.normSq (g u) : ℂ))
      (fieldOnePadicIntNormalizedHaar p) :=
    fieldOnePadicBruhatScaled_normSq_integrable p n f
  have hgperiod : ∀ u z : ℤ_[p],
      g (u + (p : ℤ_[p]) ^ N * z) = g u := by
    simpa only [g, N] using fieldOnePadicBruhatScaled_period p n m f hperiod
  have hQcont : Continuous Q := by
    exact (continuous_of_discreteTopology : Continuous
      (fun k : ZMod (p ^ N) => Complex.normSq
        (fieldOnePadicIntCyclicFourierIntegral p N g k))).comp
      (fieldOnePadicInt_toZModPow_continuous p N)
  have hQcomplex : Integrable (fun v => (Q v : ℂ))
      (fieldOnePadicIntNormalizedHaar p) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact Complex.continuous_ofReal.comp hQcont
    · exact HasCompactSupport.of_compactSpace _
  have hQclass : ∀ {x y : ℤ_[p]},
      PadicInt.toZModPow N x = PadicInt.toZModPow N y →
        (Q x : ℂ) = (Q y : ℂ) := by
    intro x y hxy
    simp only [Q]
    rw [hxy]
  have hquad := fieldOnePadicInt_cyclicSampleSum_eq_nsmul_integral
    p N (fun v => (Q v : ℂ)) hQcomplex hQclass
  rw [integral_complex_ofReal] at hquad
  have hquadR :
      ∑ r : ZMod (p ^ N),
          Complex.normSq (fieldOnePadicIntCyclicFourierIntegral p N g r) =
        (p ^ N : ℝ) *
          ∫ v, Q v ∂fieldOnePadicIntNormalizedHaar p := by
    apply Complex.ofReal_injective
    push_cast
    simpa [nsmul_eq_mul, Q, fieldOnePadicIntResidueRep_spec] using hquad
  have hfinite := fieldOnePadicIntCyclicFourierIntegral_plancherel
    p N g hg hg2 hgperiod
  have hQscale :
      (p ^ N : ℝ) * ∫ v, Q v ∂fieldOnePadicIntNormalizedHaar p =
        ∫ u, Complex.normSq (g u)
          ∂fieldOnePadicIntNormalizedHaar p := by
    rw [← hquadR]
    exact hfinite
  have hfourierOutside : ∀ y,
      y ∉ Set.range (fieldOnePadicInvPowIntCoeAddMonoidHom p m) →
        Complex.normSq (fieldOnePadicBruhatFourier p f y) = 0 := by
    intro y hy
    have hz := fieldOnePadicBruhatFourier_eq_zero_outside_annihilator
      p m f hperiod (y := y) (by
        simpa only [fieldOnePadicInvPowIntCoeAddMonoidHom_range] using hy)
    rw [hz]
    simp
  have hfOutside : ∀ x,
      x ∉ Set.range (fieldOnePadicInvPowIntCoeAddMonoidHom p n) →
        Complex.normSq (f.1 x) = 0 := by
    intro x hx
    have hxstage : x ∉ (fieldOnePadicDenominatorStage p n : Set ℚ_[p]) := by
      simpa only [fieldOnePadicInvPowIntCoeAddMonoidHom_range] using hx
    have hxtsupport : x ∉ tsupport (f.1 : ℚ_[p] → ℂ) :=
      fun hxt => hxstage (hsupport hxt)
    rw [image_eq_zero_of_notMem_tsupport hxtsupport]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hfourierOutside]
  rw [fieldOnePadic_setIntegral_invPowIntCoe_real]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hfOutside]
  rw [fieldOnePadic_setIntegral_invPowIntCoe_real]
  have hcoeff : ∀ v : ℤ_[p],
      Complex.normSq (fieldOnePadicBruhatFourier p f
        (fieldOnePadicInvPowIntCoeAddMonoidHom p m v)) =
      ((p : ℝ) ^ n) ^ 2 * Q v := by
    intro v
    rw [fieldOnePadicBruhatFourier_invPow_coeff p n m f hsupport v]
    rw [Complex.normSq_mul]
    rw [fieldOnePadic_normSq_real_natCast_pow]
  rw [integral_congr_ae (Filter.Eventually.of_forall hcoeff)]
  rw [integral_const_mul]
  change (p : ℝ) ^ m *
      (((p : ℝ) ^ n) ^ 2 *
        ∫ v, Q v ∂fieldOnePadicIntNormalizedHaar p) =
    (p : ℝ) ^ n *
      ∫ u, Complex.normSq (g u) ∂fieldOnePadicIntNormalizedHaar p
  rw [← hQscale]
  dsimp [N]
  rw [pow_add]
  ring

/-- Full local Plancherel theorem for the canonical standard character and
unit-ball-normalized Haar measure on literal `ℚ_p`. -/
theorem fieldOnePadicBruhatFourier_plancherel
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    ∫ y, Complex.normSq (fieldOnePadicBruhatFourier p f y)
        ∂fieldOnePadicUnitBallNormalizedHaar p =
      ∫ x, Complex.normSq (f.1 x)
        ∂fieldOnePadicUnitBallNormalizedHaar p := by
  obtain ⟨n, m, hsupport, hperiod⟩ :=
    fieldOnePadicBruhat_exists_finiteLevel p f
  exact fieldOnePadicBruhatFourier_plancherel_of_finiteLevel p n m f hsupport hperiod

end
end GaloisForLFunctions.RHTower
