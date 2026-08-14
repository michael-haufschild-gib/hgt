import GaloisForLFunctions.RHTower.FieldOnePadicProductBruhatFourierPlancherel

namespace GaloisForLFunctions.RHTower
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) [∀ i, Fact (p i).Prime]

def fieldOnePadicPowIntCoeAddMonoidHom (q n : ℕ) [Fact q.Prime] : ℤ_[q] →+ ℚ_[q] where
  toFun u := (q : ℚ_[q]) ^ n * (u : ℚ_[q])
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

theorem fieldOnePadicPowIntCoeAddMonoidHom_openEmbedding (q n : ℕ) [Fact q.Prime] :
    Topology.IsOpenEmbedding (fieldOnePadicPowIntCoeAddMonoidHom q n) := by
  change Topology.IsOpenEmbedding (fun u : ℤ_[q] =>
    (q : ℚ_[q]) ^ n * (u : ℚ_[q]))
  have hq : (q : ℚ_[q]) ^ n ≠ 0 := by
    exact pow_ne_zero n (by
      exact_mod_cast (Fact.out : Nat.Prime q).ne_zero)
  exact (Homeomorph.mulLeft₀ ((q : ℚ_[q]) ^ n) hq).isOpenEmbedding.comp
    PadicInt.isOpenEmbedding_coe

def fieldOnePadicProductPowIntCoeAddMonoidHom (n : ι → ℕ) :
    FieldOnePadicIntProduct p →+ FieldOnePadicProduct p where
  toFun u i := (p i : ℚ_[p i]) ^ n i * (u i : ℚ_[p i])
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp [mul_add]

theorem fieldOnePadicProductPowIntCoeAddMonoidHom_openEmbedding (n : ι → ℕ) :
    Topology.IsOpenEmbedding (fieldOnePadicProductPowIntCoeAddMonoidHom p n) := by
  change Topology.IsOpenEmbedding
    (Pi.map fun i =>
      (fieldOnePadicPowIntCoeAddMonoidHom (p i) (n i)))
  exact Topology.IsOpenEmbedding.piMap fun i =>
    fieldOnePadicPowIntCoeAddMonoidHom_openEmbedding (p i) (n i)

theorem fieldOnePadicProductBruhatFourier_add_primePow
    (n : ι → ℕ)
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p))
    (hsupport : ∀ x ∈ tsupport
      (f.1 : FieldOnePadicProduct p → ℂ),
        ∀ i, x i ∈ fieldOnePadicDenominatorStage (p i) (n i))
    (y : FieldOnePadicProduct p) (z : FieldOnePadicIntProduct p) :
    fieldOnePadicProductBruhatFourier p f
        (y + fieldOnePadicProductPowIntCoeAddMonoidHom p n z) =
      fieldOnePadicProductBruhatFourier p f y := by
  let t := fieldOnePadicProductPowIntCoeAddMonoidHom p n z
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hfx : f.1 x = 0
  · simp [hfx]
  · have hxtsupport : x ∈ tsupport
        (f.1 : FieldOnePadicProduct p → ℂ) := subset_closure hfx
    have hchar : fieldOnePadicProductStandardAddChar p
        (fun i => -(x i * t i)) = 1 := by
      rw [fieldOnePadicProductStandardAddChar]
      apply Finset.prod_eq_one
      intro i _
      rw [fieldOnePadicStandardAddChar_eq_one_iff]
      apply neg_mem
      change ‖x i * ((p i : ℚ_[p i]) ^ n i * (z i : ℚ_[p i]))‖ ≤ 1
      calc
        ‖x i * ((p i : ℚ_[p i]) ^ n i * (z i : ℚ_[p i]))‖ =
            ‖(p i : ℚ_[p i]) ^ n i * x i‖ * ‖(z i : ℚ_[p i])‖ := by
          rw [show x i * ((p i : ℚ_[p i]) ^ n i * (z i : ℚ_[p i])) =
            ((p i : ℚ_[p i]) ^ n i * x i) * (z i : ℚ_[p i]) by ring,
            norm_mul]
        _ ≤ 1 * 1 := mul_le_mul (hsupport x hxtsupport i) (z i).property
          (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    change fieldOnePadicProductStandardAddChar p
          (fun i => -(x i * (y i + t i))) * f.1 x =
      fieldOnePadicProductStandardAddChar p
          (fun i => -(x i * y i)) * f.1 x
    rw [show (fun i => -(x i * (y i + t i))) =
        (fun i => -(x i * y i)) + (fun i => -(x i * t i)) by
      funext i
      change -(x i * (y i + t i)) = -(x i * y i) + -(x i * t i)
      ring]
    rw [fieldOnePadicProductStandardAddChar_add, hchar, mul_one]

theorem fieldOnePadicProductBruhatFourier_isLocallyConstant
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p)) :
    IsLocallyConstant (fieldOnePadicProductBruhatFourier p f) := by
  obtain ⟨n, _m, hsupport, _hperiod⟩ :=
    fieldOnePadicProductBruhat_exists_finiteLevel p f
  let q := fieldOnePadicProductPowIntCoeAddMonoidHom p n
  have hqopen : IsOpen (Set.range q) :=
    (fieldOnePadicProductPowIntCoeAddMonoidHom_openEmbedding p n).isOpen_range
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  let W : Set (FieldOnePadicProduct p) := {w | w - y ∈ Set.range q}
  have hWopen : IsOpen W :=
    hqopen.preimage (continuous_id.sub continuous_const)
  have hyW : y ∈ W := by
    change y - y ∈ Set.range q
    exact ⟨0, by simp⟩
  filter_upwards [hWopen.mem_nhds hyW] with w hw
  obtain ⟨z, hz⟩ := hw
  have hwrep : w = y + q z := by
    rw [hz]
    abel
  rw [hwrep]
  exact fieldOnePadicProductBruhatFourier_add_primePow p n f hsupport y z

theorem fieldOnePadicProductBruhatFourier_hasCompactSupport
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p)) :
    HasCompactSupport (fieldOnePadicProductBruhatFourier p f) := by
  obtain ⟨_n, m, _hsupport, hperiod⟩ :=
    fieldOnePadicProductBruhat_exists_finiteLevel p f
  have hstageCompact : IsCompact
      (Set.range (fieldOnePadicProductInvPowIntCoeAddMonoidHom p m)) := by
    rw [← Set.image_univ]
    exact isCompact_univ.image
      (fieldOnePadicProductInvPowIntCoeAddMonoidHom_isOpenEmbedding
        p m).continuous
  apply HasCompactSupport.of_support_subset_isCompact hstageCompact
  intro y hy
  by_contra hyout
  exact hy (fieldOnePadicProductBruhatFourier_eq_zero_outside_annihilator
    p m f hperiod hyout)

def fieldOnePadicProductBruhatFourierBruhat
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p)) :
    compactlySupportedLocallyConstant (FieldOnePadicProduct p) :=
  ⟨⟨fieldOnePadicProductBruhatFourier p f,
      fieldOnePadicProductBruhatFourier_isLocallyConstant p f⟩,
    fieldOnePadicProductBruhatFourier_hasCompactSupport p f⟩

@[simp] theorem fieldOnePadicProductBruhatFourierBruhat_apply
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p))
    (y : FieldOnePadicProduct p) :
    (fieldOnePadicProductBruhatFourierBruhat p f).1 y =
      fieldOnePadicProductBruhatFourier p f y := rfl

theorem fieldOnePadicProductBruhatFourier_integrand_integrable
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p))
    (y : FieldOnePadicProduct p) :
    Integrable (fun x => fieldOnePadicProductStandardAddChar p
        (fun i => -(x i * y i)) * f.1 x)
      (fieldOnePadicProductUnitBallNormalizedHaar p) := by
  apply (f.1.continuous.integrable_of_hasCompactSupport f.2).bdd_mul (c := 1)
  · apply Continuous.aestronglyMeasurable
    exact continuous_finsetProd _ fun i _ =>
      (fieldOnePadicStandardAddChar_isLocallyConstant (p i)).continuous.comp
        (continuous_neg.comp ((continuous_apply i).mul continuous_const))
  · filter_upwards [] with x
    rw [fieldOnePadicProductStandardAddChar, norm_prod]
    simp [fieldOnePadicStandardAddChar]

def fieldOnePadicProductBruhatFourierLinear :
    compactlySupportedLocallyConstant (FieldOnePadicProduct p) →ₗ[ℂ]
      compactlySupportedLocallyConstant (FieldOnePadicProduct p) where
  toFun := fieldOnePadicProductBruhatFourierBruhat p
  map_add' f g := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    change (∫ x, fieldOnePadicProductStandardAddChar p
        (fun i => -(x i * y i)) * (f.1 x + g.1 x)
          ∂fieldOnePadicProductUnitBallNormalizedHaar p) = _
    simp_rw [mul_add]
    rw [integral_add (fieldOnePadicProductBruhatFourier_integrand_integrable p f y)
      (fieldOnePadicProductBruhatFourier_integrand_integrable p g y)]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    change (∫ x, fieldOnePadicProductStandardAddChar p
        (fun i => -(x i * y i)) * (c * f.1 x)
          ∂fieldOnePadicProductUnitBallNormalizedHaar p) = _
    simp_rw [show ∀ x : FieldOnePadicProduct p,
      fieldOnePadicProductStandardAddChar p (fun i => -(x i * y i)) *
          (c * f.1 x) =
        c * (fieldOnePadicProductStandardAddChar p
          (fun i => -(x i * y i)) * f.1 x) by
      intro x
      ring]
    rw [integral_const_mul]
    rfl

end
end GaloisForLFunctions.RHTower
