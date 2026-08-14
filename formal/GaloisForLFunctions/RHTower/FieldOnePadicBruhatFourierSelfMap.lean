import GaloisForLFunctions.RHTower.FieldOnePadicBruhatFourierPlancherel

/-!
# The standard p-adic Fourier transform preserves the Bruhat space

The literal Fourier integral with source character and unit-ball-normalized
Haar measure maps every compactly supported locally constant function on
`ℚ_p` to another such function.  Compact support and local constancy are
deduced from the two finite depths of the input, not assumed through an
abstract Fourier automorphism.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set TopologicalSpace

variable (p : ℕ) [Fact p.Prime]

/-- Support in `p⁻ⁿℤ_p` forces invariance of the Fourier transform under the
dual lattice `pⁿℤ_p`. -/
theorem fieldOnePadicBruhatFourier_add_primePow
    (n : ℕ) (f : compactlySupportedLocallyConstant ℚ_[p])
    (hsupport : tsupport (f.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p n)
    (y : ℚ_[p]) (z : ℤ_[p]) :
    fieldOnePadicBruhatFourier p f
        (y + (p : ℚ_[p]) ^ n * (z : ℚ_[p])) =
      fieldOnePadicBruhatFourier p f y := by
  let t : ℚ_[p] := (p : ℚ_[p]) ^ n * (z : ℚ_[p])
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hfx : f.1 x = 0
  · simp [hfx]
  · have hxtsupport : x ∈ tsupport (f.1 : ℚ_[p] → ℂ) := by
      exact subset_closure hfx
    have hxstage : x ∈ fieldOnePadicDenominatorStage p n :=
      hsupport hxtsupport
    have hxt : x * t ∈ fieldOnePadicIntegralAddSubgroup p := by
      change ‖x * ((p : ℚ_[p]) ^ n * (z : ℚ_[p]))‖ ≤ 1
      calc
        ‖x * ((p : ℚ_[p]) ^ n * (z : ℚ_[p]))‖ =
            ‖(p : ℚ_[p]) ^ n * x‖ * ‖(z : ℚ_[p])‖ := by
              rw [show x * ((p : ℚ_[p]) ^ n * (z : ℚ_[p])) =
                ((p : ℚ_[p]) ^ n * x) * (z : ℚ_[p]) by ring, norm_mul]
        _ ≤ 1 * 1 :=
          mul_le_mul hxstage z.property (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hchar : fieldOnePadicStandardAddChar p (-(x * t)) = 1 :=
      (fieldOnePadicStandardAddChar_eq_one_iff p (-(x * t))).2
        (neg_mem hxt)
    change fieldOnePadicStandardAddChar p (-(x * (y + t))) * f.1 x =
      fieldOnePadicStandardAddChar p (-(x * y)) * f.1 x
    rw [show -(x * (y + t)) = -(x * y) + -(x * t) by ring,
      AddChar.map_add_eq_mul, hchar, mul_one]

/-- The literal p-adic Fourier transform is locally constant. -/
theorem fieldOnePadicBruhatFourier_isLocallyConstant
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    IsLocallyConstant (fieldOnePadicBruhatFourier p f) := by
  obtain ⟨n, _m, hsupport, _hperiod⟩ :=
    fieldOnePadicBruhat_exists_finiteLevel p f
  let q : ℚ_[p] := (p : ℚ_[p]) ^ n
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact pow_ne_zero n (by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  let U : Set ℚ_[p] :=
    (fun t : ℚ_[p] => q⁻¹ * t) ⁻¹'
      (fieldOnePadicIntegralAddSubgroup p : Set ℚ_[p])
  have hUopen : IsOpen U :=
    (fieldOnePadicIntegralAddSubgroup_isOpen p).preimage
      (continuous_const.mul continuous_id)
  have hUzero : (0 : ℚ_[p]) ∈ U := by
    simp [U]
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  let W : Set ℚ_[p] := {w | w - y ∈ U}
  have hWopen : IsOpen W :=
    hUopen.preimage (continuous_id.sub continuous_const)
  have hyW : y ∈ W := by
    simp [W, hUzero]
  filter_upwards [hWopen.mem_nhds hyW] with w hw
  let z : ℤ_[p] := ⟨q⁻¹ * (w - y), hw⟩
  have hwrep : w = y + (p : ℚ_[p]) ^ n * (z : ℚ_[p]) := by
    change w = y + q * (q⁻¹ * (w - y))
    rw [← mul_assoc, mul_inv_cancel₀ hq0, one_mul]
    abel
  rw [hwrep]
  exact fieldOnePadicBruhatFourier_add_primePow p n f hsupport y z

/-- The literal p-adic Fourier transform has compact support in the dual
denominator stage supplied by the translation depth of the input. -/
theorem fieldOnePadicBruhatFourier_hasCompactSupport
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    HasCompactSupport (fieldOnePadicBruhatFourier p f) := by
  obtain ⟨_n, m, _hsupport, hperiod⟩ :=
    fieldOnePadicBruhat_exists_finiteLevel p f
  have hstageCompact : IsCompact
      (fieldOnePadicDenominatorStage p m : Set ℚ_[p]) := by
    rw [← fieldOnePadicInvPowIntCoeAddMonoidHom_range p m]
    rw [← Set.image_univ]
    exact isCompact_univ.image
      (fieldOnePadicInvPowIntCoeAddMonoidHom_isOpenEmbedding p m).continuous
  apply HasCompactSupport.of_support_subset_isCompact hstageCompact
  intro y hy
  by_contra hyout
  exact hy (fieldOnePadicBruhatFourier_eq_zero_outside_annihilator
    p m f hperiod hyout)

/-- The standard Fourier integral as an endomorphism of the literal p-adic
Bruhat space. -/
def fieldOnePadicBruhatFourierBruhat
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    compactlySupportedLocallyConstant ℚ_[p] :=
  ⟨⟨fieldOnePadicBruhatFourier p f,
      fieldOnePadicBruhatFourier_isLocallyConstant p f⟩,
    fieldOnePadicBruhatFourier_hasCompactSupport p f⟩

@[simp]
theorem fieldOnePadicBruhatFourierBruhat_apply
    (f : compactlySupportedLocallyConstant ℚ_[p]) (y : ℚ_[p]) :
    (fieldOnePadicBruhatFourierBruhat p f).1 y =
      fieldOnePadicBruhatFourier p f y :=
  rfl

/-- Every Fourier integrand attached to a p-adic Bruhat function is
integrable. -/
theorem fieldOnePadicBruhatFourier_integrand_integrable
    (f : compactlySupportedLocallyConstant ℚ_[p]) (y : ℚ_[p]) :
    Integrable
      (fun x => fieldOnePadicStandardAddChar p (-(x * y)) * f.1 x)
      (fieldOnePadicUnitBallNormalizedHaar p) := by
  apply
    (f.1.continuous.integrable_of_hasCompactSupport f.2).bdd_mul (c := 1)
  · exact
      ((fieldOnePadicStandardAddChar_isLocallyConstant p).continuous.comp
        (continuous_neg.comp
          (continuous_id.mul continuous_const))).aestronglyMeasurable
  · filter_upwards [] with x
    simp [fieldOnePadicStandardAddChar]

/-- The literal p-adic Bruhat Fourier self-map is complex-linear. -/
def fieldOnePadicBruhatFourierLinear :
    compactlySupportedLocallyConstant ℚ_[p] →ₗ[ℂ]
      compactlySupportedLocallyConstant ℚ_[p] where
  toFun := fieldOnePadicBruhatFourierBruhat p
  map_add' f g := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    change (∫ x, fieldOnePadicStandardAddChar p (-(x * y)) *
        (f.1 x + g.1 x) ∂fieldOnePadicUnitBallNormalizedHaar p) = _
    simp_rw [mul_add]
    rw [integral_add
      (fieldOnePadicBruhatFourier_integrand_integrable p f y)
      (fieldOnePadicBruhatFourier_integrand_integrable p g y)]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    change (∫ x, fieldOnePadicStandardAddChar p (-(x * y)) *
        (c * f.1 x) ∂fieldOnePadicUnitBallNormalizedHaar p) = _
    simp_rw [show ∀ x : ℚ_[p],
      fieldOnePadicStandardAddChar p (-(x * y)) * (c * f.1 x) =
        c * (fieldOnePadicStandardAddChar p (-(x * y)) * f.1 x) by
          intro x
          ring]
    rw [integral_const_mul]
    rfl

end

end GaloisForLFunctions.RHTower
