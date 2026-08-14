import GaloisForLFunctions.RHTower.FieldOnePadicProductCyclicFourierPlancherel

namespace GaloisForLFunctions.RHTower
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Pointwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) [∀ i, Fact (p i).Prime]

def fieldOnePadicProductStandardAddChar (x : FieldOnePadicProduct p) : ℂ :=
  ∏ i, fieldOnePadicStandardAddChar (p i) (x i)

def fieldOnePadicProductBruhatFourier
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p))
    (y : FieldOnePadicProduct p) : ℂ :=
  ∫ x, fieldOnePadicProductStandardAddChar p (fun i => -(x i * y i)) * f.1 x
    ∂fieldOnePadicProductUnitBallNormalizedHaar p

def fieldOnePadicProductBruhatScaled (n : ι → ℕ)
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p)) :
    FieldOnePadicIntProduct p → ℂ :=
  fun u => f.1 (fieldOnePadicProductInvPowIntCoeAddMonoidHom p n u)

theorem fieldOnePadicProductBruhatScaled_integrable (n : ι → ℕ)
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p)) :
    Integrable (fieldOnePadicProductBruhatScaled p n f)
      (fieldOnePadicIntProductNormalizedHaar p) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact f.1.continuous.comp
      (fieldOnePadicProductInvPowIntCoeAddMonoidHom_isOpenEmbedding
        p n).continuous
  · exact HasCompactSupport.of_compactSpace _

theorem fieldOnePadicProductBruhatScaled_normSq_integrable (n : ι → ℕ)
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p)) :
    Integrable (fun u =>
      (Complex.normSq (fieldOnePadicProductBruhatScaled p n f u) : ℂ))
      (fieldOnePadicIntProductNormalizedHaar p) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact Complex.continuous_ofReal.comp
      (Complex.continuous_normSq.comp (f.1.continuous.comp
        (fieldOnePadicProductInvPowIntCoeAddMonoidHom_isOpenEmbedding
          p n).continuous))
  · exact HasCompactSupport.of_compactSpace _

theorem fieldOnePadicProductBruhatScaled_period
    (n m : ι → ℕ)
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p))
    (hperiod : ∀ x : FieldOnePadicProduct p,
      ∀ z : FieldOnePadicIntProduct p,
        f.1 (x + fun i =>
          (p i : ℚ_[p i]) ^ m i * (z i : ℚ_[p i])) = f.1 x) :
    ∀ u z : FieldOnePadicIntProduct p,
      fieldOnePadicProductBruhatScaled p n f
        (u + fieldOnePadicIntProductLatticePoint p (fun i => n i + m i) z) =
      fieldOnePadicProductBruhatScaled p n f u := by
  intro u z
  change f.1 (fieldOnePadicProductInvPowIntCoeAddMonoidHom p n
      (u + fieldOnePadicIntProductLatticePoint p
        (fun i => n i + m i) z)) =
    f.1 (fieldOnePadicProductInvPowIntCoeAddMonoidHom p n u)
  rw [show fieldOnePadicProductInvPowIntCoeAddMonoidHom p n
      (u + fieldOnePadicIntProductLatticePoint p
        (fun i => n i + m i) z) =
    fieldOnePadicProductInvPowIntCoeAddMonoidHom p n u + fun i =>
      (p i : ℚ_[p i]) ^ m i * (z i : ℚ_[p i]) by
    funext i
    change fieldOnePadicInvPowIntCoeAddMonoidHom (p i) (n i)
        (u i + (p i : ℤ_[p i]) ^ (n i + m i) * z i) =
      fieldOnePadicInvPowIntCoeAddMonoidHom (p i) (n i) (u i) +
        (p i : ℚ_[p i]) ^ m i * (z i : ℚ_[p i])
    change (fieldOnePadicPrimeInvPowUnit (p i) (n i) : ℚ_[p i]) *
        ((u i + (p i : ℤ_[p i]) ^ (n i + m i) * z i : ℤ_[p i]) : ℚ_[p i]) =
      (fieldOnePadicPrimeInvPowUnit (p i) (n i) : ℚ_[p i]) *
          (u i : ℚ_[p i]) +
        (p i : ℚ_[p i]) ^ m i * (z i : ℚ_[p i])
    rw [fieldOnePadicPrimeInvPowUnit_val]
    simp only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_natCast]
    rw [mul_add]
    congr 1
    have hp0 : (p i : ℚ_[p i]) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime (p i)).ne_zero
    calc
      ((p i : ℚ_[p i]) ^ n i)⁻¹ *
          ((p i : ℚ_[p i]) ^ (n i + m i) * (z i : ℚ_[p i])) =
        (((p i : ℚ_[p i]) ^ n i)⁻¹ * (p i : ℚ_[p i]) ^ n i) *
          ((p i : ℚ_[p i]) ^ m i * (z i : ℚ_[p i])) := by
            rw [pow_add]
            ring
      _ = (p i : ℚ_[p i]) ^ m i * (z i : ℚ_[p i]) := by
        rw [inv_mul_cancel₀ (pow_ne_zero (n i) hp0), one_mul]]
  exact hperiod _ z

theorem fieldOnePadicProductBruhatFourier_invPow_coeff
    (n m : ι → ℕ)
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p))
    (hsupport : ∀ x ∈ tsupport
      (f.1 : FieldOnePadicProduct p → ℂ),
        ∀ i, x i ∈ fieldOnePadicDenominatorStage (p i) (n i))
    (v : FieldOnePadicIntProduct p) :
    fieldOnePadicProductBruhatFourier p f
        (fieldOnePadicProductInvPowIntCoeAddMonoidHom p m v) =
      ((∏ i, (p i : ℝ) ^ n i : ℝ) : ℂ) *
        fieldOnePadicIntProductCyclicFourierIntegral p
          (fun i => n i + m i) (fieldOnePadicProductBruhatScaled p n f)
          (fieldOnePadicIntProductToFiniteQuotient p
            (fun i => n i + m i) v) := by
  let N : ι → ℕ := fun i => n i + m i
  let h : FieldOnePadicProduct p → ℂ := fun x =>
    fieldOnePadicProductStandardAddChar p
      (fun i => -(x i *
        fieldOnePadicProductInvPowIntCoeAddMonoidHom p m v i)) * f.1 x
  have houtside : ∀ x,
      x ∉ Set.range (fieldOnePadicProductInvPowIntCoeAddMonoidHom p n) →
        h x = 0 := by
    intro x hx
    have hxtsupport : x ∉ tsupport
        (f.1 : FieldOnePadicProduct p → ℂ) := by
      intro hxt
      apply hx
      rw [fieldOnePadicProductInvPowIntCoeAddMonoidHom_range]
      intro i _
      exact hsupport x hxt i
    simp [h, image_eq_zero_of_notMem_tsupport hxtsupport]
  rw [show fieldOnePadicProductBruhatFourier p f
      (fieldOnePadicProductInvPowIntCoeAddMonoidHom p m v) =
        ∫ x, h x ∂fieldOnePadicProductUnitBallNormalizedHaar p by rfl]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero houtside]
  rw [fieldOnePadicProduct_setIntegral_invPowIntCoe]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  dsimp [h, fieldOnePadicProductBruhatScaled, fieldOnePadicProductStandardAddChar,
    fieldOnePadicProductInvPowIntCoeAddMonoidHom]
  apply congrArg (fun z : ℂ => z * f.1
    (fun i => fieldOnePadicInvPowIntCoeAddMonoidHom (p i) (n i) (u i)))
  apply Finset.prod_congr rfl
  intro i _
  change fieldOnePadicStandardAddChar (p i)
      (-((fieldOnePadicPrimeInvPowUnit (p i) (n i) : ℚ_[p i]) *
        (u i : ℚ_[p i]) *
        ((fieldOnePadicPrimeInvPowUnit (p i) (m i) : ℚ_[p i]) *
          (v i : ℚ_[p i])))) =
    ZMod.stdAddChar (-(PadicInt.toZModPow (N i) (u i) *
      PadicInt.toZModPow (N i) (v i)))
  rw [fieldOnePadicPrimeInvPowUnit_val,
    fieldOnePadicPrimeInvPowUnit_val]
  have hprod :
      -(((p i : ℚ_[p i]) ^ n i)⁻¹ * (u i : ℚ_[p i]) *
        (((p i : ℚ_[p i]) ^ m i)⁻¹ * (v i : ℚ_[p i]))) =
      (-((p i : ℚ_[p i]) ^ N i)⁻¹) *
        ((u i * v i : ℤ_[p i]) : ℚ_[p i]) := by
    dsimp [N]
    rw [pow_add, mul_inv_rev]
    ring
  rw [hprod, fieldOnePadicStandardAddChar_neg_invPow_mul_coe]
  rw [map_mul]

theorem fieldOnePadicProductStandardAddChar_add
    (x y : FieldOnePadicProduct p) :
    fieldOnePadicProductStandardAddChar p (x + y) =
      fieldOnePadicProductStandardAddChar p x *
        fieldOnePadicProductStandardAddChar p y := by
  simp only [fieldOnePadicProductStandardAddChar, Pi.add_apply,
    AddChar.map_add_eq_mul]
  exact Finset.prod_mul_distrib

theorem fieldOnePadicProductBruhatFourier_eq_zero_outside_annihilator
    (m : ι → ℕ)
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p))
    (hperiod : ∀ x : FieldOnePadicProduct p,
      ∀ z : FieldOnePadicIntProduct p,
        f.1 (x + fun i =>
          (p i : ℚ_[p i]) ^ m i * (z i : ℚ_[p i])) = f.1 x)
    {y : FieldOnePadicProduct p}
    (hy : y ∉ Set.range
      (fieldOnePadicProductInvPowIntCoeAddMonoidHom p m)) :
    fieldOnePadicProductBruhatFourier p f y = 0 := by
  rw [fieldOnePadicProductInvPowIntCoeAddMonoidHom_range] at hy
  simp only [Set.mem_pi, Set.mem_univ, forall_const] at hy
  push_neg at hy
  obtain ⟨i, hyi⟩ := hy
  let a : FieldOnePadicProduct p :=
    fieldOnePadicProductSingle p i ((p i : ℚ_[p i]) ^ m i)
  let z0 : FieldOnePadicIntProduct p := Function.update 0 i 1
  let c : ℂ := fieldOnePadicStandardAddChar (p i)
    (-((p i : ℚ_[p i]) ^ m i * y i))
  let φ : FieldOnePadicProduct p → ℂ := fun x =>
    fieldOnePadicProductStandardAddChar p (fun j => -(x j * y j)) * f.1 x
  have hc : c ≠ 1 := by
    intro hc1
    have hint : -((p i : ℚ_[p i]) ^ m i * y i) ∈
        fieldOnePadicIntegralAddSubgroup (p i) :=
      (fieldOnePadicStandardAddChar_eq_one_iff (p i) _).mp hc1
    have hint' : (p i : ℚ_[p i]) ^ m i * y i ∈
        fieldOnePadicIntegralAddSubgroup (p i) := neg_mem_iff.mp hint
    exact hyi hint'
  have hcharA : fieldOnePadicProductStandardAddChar p
      (fun j => -(a j * y j)) = c := by
    rw [fieldOnePadicProductStandardAddChar]
    rw [Finset.prod_eq_single i]
    · simp [a, c, fieldOnePadicProductSingle]
    · intro j _ hji
      simp [a, fieldOnePadicProductSingle, Function.update, hji]
    · simp
  have hfa : ∀ x, f.1 (x + a) = f.1 x := by
    intro x
    rw [show a = fun j =>
        (p j : ℚ_[p j]) ^ m j * (z0 j : ℚ_[p j]) by
      funext j
      by_cases hji : j = i
      · subst j
        simp [a, z0, fieldOnePadicProductSingle]
      · simp [a, z0, fieldOnePadicProductSingle,
          Function.update, hji]]
    exact hperiod x z0
  have hφtrans : ∀ x, φ (x + a) = c * φ x := by
    intro x
    change fieldOnePadicProductStandardAddChar p
          (fun j => -((x j + a j) * y j)) * f.1 (x + a) =
      c * (fieldOnePadicProductStandardAddChar p
          (fun j => -(x j * y j)) * f.1 x)
    rw [show (fun j => -((x j + a j) * y j)) =
        (fun j => -(a j * y j)) + (fun j => -(x j * y j)) by
      funext j
      change -((x j + a j) * y j) = -(a j * y j) + -(x j * y j)
      ring]
    rw [fieldOnePadicProductStandardAddChar_add, hcharA, hfa]
    ring
  have hfixed : fieldOnePadicProductBruhatFourier p f y =
      c * fieldOnePadicProductBruhatFourier p f y := by
    change (∫ x, φ x ∂fieldOnePadicProductUnitBallNormalizedHaar p) =
      c * ∫ x, φ x ∂fieldOnePadicProductUnitBallNormalizedHaar p
    calc
      (∫ x, φ x ∂fieldOnePadicProductUnitBallNormalizedHaar p) =
          ∫ x, φ (x + a)
            ∂fieldOnePadicProductUnitBallNormalizedHaar p :=
        (integral_add_right_eq_self φ a).symm
      _ = ∫ x, c * φ x
            ∂fieldOnePadicProductUnitBallNormalizedHaar p := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hφtrans x
      _ = c * ∫ x, φ x
            ∂fieldOnePadicProductUnitBallNormalizedHaar p :=
        integral_const_mul c φ
  by_contra hne
  apply hc
  apply mul_right_cancel₀ hne
  calc
    c * fieldOnePadicProductBruhatFourier p f y =
        fieldOnePadicProductBruhatFourier p f y := hfixed.symm
    _ = 1 * fieldOnePadicProductBruhatFourier p f y := by rw [one_mul]

private theorem fieldOnePadicProduct_normSq_real_product_pow (n : ι → ℕ) :
    Complex.normSq (((∏ i, (p i : ℝ) ^ n i : ℝ) : ℂ)) =
      (∏ i, (p i : ℝ) ^ n i : ℝ) ^ 2 := by
  rw [Complex.normSq_ofReal]
  ring

private theorem fieldOnePadicProductBruhatFourier_plancherel_of_finiteLevel
    (n m : ι → ℕ)
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p))
    (hsupport : ∀ x ∈ tsupport
      (f.1 : FieldOnePadicProduct p → ℂ),
        ∀ i, x i ∈ fieldOnePadicDenominatorStage (p i) (n i))
    (hperiod : ∀ x : FieldOnePadicProduct p,
      ∀ z : FieldOnePadicIntProduct p,
        f.1 (x + fun i =>
          (p i : ℚ_[p i]) ^ m i * (z i : ℚ_[p i])) = f.1 x) :
    ∫ y, Complex.normSq (fieldOnePadicProductBruhatFourier p f y)
        ∂fieldOnePadicProductUnitBallNormalizedHaar p =
      ∫ x, Complex.normSq (f.1 x)
        ∂fieldOnePadicProductUnitBallNormalizedHaar p := by
  let N : ι → ℕ := fun i => n i + m i
  let g : FieldOnePadicIntProduct p → ℂ :=
    fieldOnePadicProductBruhatScaled p n f
  let Q : FieldOnePadicIntProduct p → ℝ := fun v => Complex.normSq
    (fieldOnePadicIntProductCyclicFourierIntegral p N g
      (fieldOnePadicIntProductToFiniteQuotient p N v))
  have hg : Integrable g (fieldOnePadicIntProductNormalizedHaar p) :=
    fieldOnePadicProductBruhatScaled_integrable p n f
  have hg2 : Integrable (fun u => (Complex.normSq (g u) : ℂ))
      (fieldOnePadicIntProductNormalizedHaar p) :=
    fieldOnePadicProductBruhatScaled_normSq_integrable p n f
  have hgperiod : ∀ u z : FieldOnePadicIntProduct p,
      g (u + fieldOnePadicIntProductLatticePoint p N z) = g u := by
    simpa only [g, N] using
      fieldOnePadicProductBruhatScaled_period p n m f hperiod
  have hQcont : Continuous Q := by
    exact (continuous_of_discreteTopology : Continuous
      (fun k : FieldOneFiniteCyclicProduct (fun i => p i ^ N i) =>
        Complex.normSq
          (fieldOnePadicIntProductCyclicFourierIntegral p N g k))).comp
      (fieldOnePadicIntProductToFiniteQuotient_continuous p N)
  have hQcomplex : Integrable (fun v => (Q v : ℂ))
      (fieldOnePadicIntProductNormalizedHaar p) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact Complex.continuous_ofReal.comp hQcont
    · exact HasCompactSupport.of_compactSpace _
  have hQclass : ∀ {x y : FieldOnePadicIntProduct p},
      fieldOnePadicIntProductToFiniteQuotient p N x =
          fieldOnePadicIntProductToFiniteQuotient p N y →
        (Q x : ℂ) = (Q y : ℂ) := by
    intro x y hxy
    simp only [Q]
    rw [hxy]
  have hquad := fieldOneFiniteQuotient_sampleSum_eq_nsmul_integral
    (fieldOnePadicIntProductNormalizedHaar p)
    (fieldOnePadicIntProductNormalizedHaar_univ p)
    (fieldOnePadicIntProductToFiniteQuotient p N)
    (fieldOnePadicIntProductToFiniteQuotient_surjective p N)
    (fieldOnePadicIntProductResidueRep p N)
    (fieldOnePadicIntProductResidueRep_spec p N)
    (fun v => (Q v : ℂ)) hQcomplex hQclass
  rw [integral_complex_ofReal] at hquad
  have hquadR :
      ∑ r : FieldOneFiniteCyclicProduct (fun i => p i ^ N i),
          Complex.normSq
            (fieldOnePadicIntProductCyclicFourierIntegral p N g r) =
        ((∏ i, p i ^ N i : ℕ) : ℝ) *
          ∫ v, Q v ∂fieldOnePadicIntProductNormalizedHaar p := by
    apply Complex.ofReal_injective
    push_cast
    simpa [nsmul_eq_mul, Q, FieldOneFiniteCyclicProduct,
      fieldOnePadicIntProductResidueRep_spec] using hquad
  have hfinite :=
    fieldOnePadicIntProductCyclicFourierIntegral_plancherel
      p N g hg hg2 hgperiod
  have hQscale :
      ((∏ i, p i ^ N i : ℕ) : ℝ) *
          ∫ v, Q v ∂fieldOnePadicIntProductNormalizedHaar p =
        ∫ u, Complex.normSq (g u)
          ∂fieldOnePadicIntProductNormalizedHaar p := by
    rw [← hquadR]
    exact hfinite
  have hfourierOutside : ∀ y,
      y ∉ Set.range (fieldOnePadicProductInvPowIntCoeAddMonoidHom p m) →
        Complex.normSq (fieldOnePadicProductBruhatFourier p f y) = 0 := by
    intro y hy
    rw [fieldOnePadicProductBruhatFourier_eq_zero_outside_annihilator
      p m f hperiod hy]
    simp
  have hfOutside : ∀ x,
      x ∉ Set.range (fieldOnePadicProductInvPowIntCoeAddMonoidHom p n) →
        Complex.normSq (f.1 x) = 0 := by
    intro x hx
    have hxtsupport : x ∉ tsupport
        (f.1 : FieldOnePadicProduct p → ℂ) := by
      intro hxt
      apply hx
      rw [fieldOnePadicProductInvPowIntCoeAddMonoidHom_range]
      intro i _
      exact hsupport x hxt i
    rw [image_eq_zero_of_notMem_tsupport hxtsupport]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hfourierOutside]
  rw [fieldOnePadicProduct_setIntegral_invPowIntCoe_real]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hfOutside]
  rw [fieldOnePadicProduct_setIntegral_invPowIntCoe_real]
  have hcoeff : ∀ v : FieldOnePadicIntProduct p,
      Complex.normSq (fieldOnePadicProductBruhatFourier p f
        (fieldOnePadicProductInvPowIntCoeAddMonoidHom p m v)) =
      (∏ i, (p i : ℝ) ^ n i : ℝ) ^ 2 * Q v := by
    intro v
    rw [fieldOnePadicProductBruhatFourier_invPow_coeff p n m f hsupport v]
    rw [Complex.normSq_mul]
    rw [fieldOnePadicProduct_normSq_real_product_pow]
  rw [integral_congr_ae (Filter.Eventually.of_forall hcoeff)]
  rw [integral_const_mul]
  change (∏ i, (p i : ℝ) ^ m i : ℝ) *
      ((∏ i, (p i : ℝ) ^ n i : ℝ) ^ 2 *
        ∫ v, Q v ∂fieldOnePadicIntProductNormalizedHaar p) =
    (∏ i, (p i : ℝ) ^ n i : ℝ) *
      ∫ u, Complex.normSq (g u)
        ∂fieldOnePadicIntProductNormalizedHaar p
  rw [← hQscale]
  have hNM : ((∏ i, p i ^ N i : ℕ) : ℝ) =
      (∏ i, (p i : ℝ) ^ n i : ℝ) *
        (∏ i, (p i : ℝ) ^ m i : ℝ) := by
    push_cast
    simp only [N, pow_add, Finset.prod_mul_distrib]
  rw [hNM]
  ring

theorem fieldOnePadicProductBruhatFourier_plancherel
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p)) :
    ∫ y, Complex.normSq (fieldOnePadicProductBruhatFourier p f y)
        ∂fieldOnePadicProductUnitBallNormalizedHaar p =
      ∫ x, Complex.normSq (f.1 x)
        ∂fieldOnePadicProductUnitBallNormalizedHaar p := by
  obtain ⟨n, m, hsupport, hperiod⟩ :=
    fieldOnePadicProductBruhat_exists_finiteLevel p f
  exact fieldOnePadicProductBruhatFourier_plancherel_of_finiteLevel
    p n m f hsupport hperiod

end
end GaloisForLFunctions.RHTower

