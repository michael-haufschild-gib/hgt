import GaloisForLFunctions.RHTower.FieldOneFiniteCyclicProductFourierInversion
import GaloisForLFunctions.RHTower.FieldOnePadicProductBruhatFourierSelfMap

/-!
# Fourier inversion on finite products of p-adic fields

The product Haar measure normalized by `μ(∏ᵢ ℤ_{pᵢ}) = 1` is self-dual for
the product standard additive character.  This file proves the exact
pointwise Fourier-square identity on every product Bruhat function and
bundles the transform as a linear equivalence.

The proof descends both transforms to one common finite quotient.  The two
Haar Jacobians cancel exactly against the cardinality factor in the
unnormalized finite-product DFT inversion theorem.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Pointwise ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) [∀ i, Fact (p i).Prime]

/-- The transform's topological support lies in the annihilator of every
product-lattice period of the source. -/
theorem fieldOnePadicProductBruhatFourier_tsupport_subset_annihilator
    (m : ι → ℕ)
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p))
    (hperiod : ∀ x : FieldOnePadicProduct p,
      ∀ z : FieldOnePadicIntProduct p,
        f.1 (x + fun i =>
          (p i : ℚ_[p i]) ^ m i * (z i : ℚ_[p i])) = f.1 x) :
    ∀ y ∈ tsupport
        (fieldOnePadicProductBruhatFourier p f),
      ∀ i, y i ∈ fieldOnePadicDenominatorStage (p i) (m i) := by
  let R := Set.range (fieldOnePadicProductInvPowIntCoeAddMonoidHom p m)
  have hRcompact : IsCompact R := by
    change IsCompact (Set.range
      (fieldOnePadicProductInvPowIntCoeAddMonoidHom p m))
    rw [← Set.image_univ]
    exact isCompact_univ.image
      (fieldOnePadicProductInvPowIntCoeAddMonoidHom_isOpenEmbedding
        p m).continuous
  have hsupport : Function.support
      (fieldOnePadicProductBruhatFourier p f) ⊆ R := by
    intro y hy
    by_contra hyout
    exact hy (fieldOnePadicProductBruhatFourier_eq_zero_outside_annihilator
      p m f hperiod hyout)
  have htsupport : tsupport
      (fieldOnePadicProductBruhatFourier p f) ⊆ R := by
    exact closure_minimal hsupport hRcompact.isClosed
  intro y hy i
  have hyR := htsupport hy
  change y ∈ Set.range
    (fieldOnePadicProductInvPowIntCoeAddMonoidHom p m) at hyR
  rw [fieldOnePadicProductInvPowIntCoeAddMonoidHom_range] at hyR
  exact hyR i (Set.mem_univ i)

/-- A denominator-stage support bound becomes the dual product-lattice
period of the Fourier transform. -/
theorem fieldOnePadicProductBruhatFourier_period
    (n : ι → ℕ)
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p))
    (hsupport : ∀ x ∈ tsupport
      (f.1 : FieldOnePadicProduct p → ℂ),
        ∀ i, x i ∈ fieldOnePadicDenominatorStage (p i) (n i)) :
    ∀ y : FieldOnePadicProduct p,
      ∀ z : FieldOnePadicIntProduct p,
        fieldOnePadicProductBruhatFourier p f
            (y + fun i =>
              (p i : ℚ_[p i]) ^ n i * (z i : ℚ_[p i])) =
          fieldOnePadicProductBruhatFourier p f y := by
  intro y z
  change fieldOnePadicProductBruhatFourier p f
      (y + fieldOnePadicProductPowIntCoeAddMonoidHom p n z) =
    fieldOnePadicProductBruhatFourier p f y
  exact fieldOnePadicProductBruhatFourier_add_primePow
    p n f hsupport y z

private theorem fieldOnePadicProductBruhatFourier_fourier_of_finiteLevel
    (n m : ι → ℕ)
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p))
    (hsupport : ∀ x ∈ tsupport
      (f.1 : FieldOnePadicProduct p → ℂ),
        ∀ i, x i ∈ fieldOnePadicDenominatorStage (p i) (n i))
    (hperiod : ∀ x : FieldOnePadicProduct p,
      ∀ z : FieldOnePadicIntProduct p,
        f.1 (x + fun i =>
          (p i : ℚ_[p i]) ^ m i * (z i : ℚ_[p i])) = f.1 x) :
    ∀ y,
      fieldOnePadicProductBruhatFourier p
          (fieldOnePadicProductBruhatFourierBruhat p f) y =
        f.1 (-y) := by
  let d : ι → ℕ := fun i => n i + m i
  let N : ι → ℕ := fun i => d i + d i
  let F := fieldOnePadicProductBruhatFourierBruhat p f
  have hsupportD : ∀ x ∈ tsupport
      (f.1 : FieldOnePadicProduct p → ℂ),
        ∀ i, x i ∈ fieldOnePadicDenominatorStage (p i) (d i) := by
    intro x hx i
    exact fieldOnePadicDenominatorStage_mono (p i)
      (Nat.le_add_right (n i) (m i)) (hsupport x hx i)
  have hperiodD : ∀ x : FieldOnePadicProduct p,
      ∀ z : FieldOnePadicIntProduct p,
        f.1 (x + fun i =>
          (p i : ℚ_[p i]) ^ d i * (z i : ℚ_[p i])) = f.1 x := by
    intro x z
    let z' : FieldOnePadicIntProduct p :=
      fun i => (p i : ℤ_[p i]) ^ n i * z i
    rw [show (fun i => (p i : ℚ_[p i]) ^ d i * (z i : ℚ_[p i])) =
        fun i => (p i : ℚ_[p i]) ^ m i * (z' i : ℚ_[p i]) by
      funext i
      simp only [d, z', PadicInt.coe_mul, PadicInt.coe_pow,
        PadicInt.coe_natCast, pow_add]
      ring]
    exact hperiod x z'
  have hFsupport0 : ∀ y ∈ tsupport (F.1 : FieldOnePadicProduct p → ℂ),
      ∀ i, y i ∈ fieldOnePadicDenominatorStage (p i) (m i) := by
    intro y hy i
    apply fieldOnePadicProductBruhatFourier_tsupport_subset_annihilator
      p m f hperiod y
    exact hy
  have hFperiod0 : ∀ y : FieldOnePadicProduct p,
      ∀ z : FieldOnePadicIntProduct p,
        F.1 (y + fun i =>
          (p i : ℚ_[p i]) ^ n i * (z i : ℚ_[p i])) = F.1 y := by
    simpa only [F, fieldOnePadicProductBruhatFourierBruhat_apply] using
      fieldOnePadicProductBruhatFourier_period p n f hsupport
  have hFsupport : ∀ y ∈ tsupport (F.1 : FieldOnePadicProduct p → ℂ),
      ∀ i, y i ∈ fieldOnePadicDenominatorStage (p i) (d i) := by
    intro y hy i
    exact fieldOnePadicDenominatorStage_mono (p i)
      (Nat.le_add_left (m i) (n i)) (hFsupport0 y hy i)
  have hFperiod : ∀ y : FieldOnePadicProduct p,
      ∀ z : FieldOnePadicIntProduct p,
        F.1 (y + fun i =>
          (p i : ℚ_[p i]) ^ d i * (z i : ℚ_[p i])) = F.1 y := by
    intro y z
    let z' : FieldOnePadicIntProduct p :=
      fun i => (p i : ℤ_[p i]) ^ m i * z i
    rw [show (fun i => (p i : ℚ_[p i]) ^ d i * (z i : ℚ_[p i])) =
        fun i => (p i : ℚ_[p i]) ^ n i * (z' i : ℚ_[p i]) by
      funext i
      simp only [d, z', PadicInt.coe_mul, PadicInt.coe_pow,
        PadicInt.coe_natCast, pow_add]
      ring]
    exact hFperiod0 y z'
  let g : FieldOnePadicIntProduct p → ℂ :=
    fieldOnePadicProductBruhatScaled p d f
  let h : FieldOnePadicIntProduct p → ℂ :=
    fieldOnePadicProductBruhatScaled p d F
  let G : FieldOneFiniteCyclicProduct (fun i => p i ^ N i) → ℂ :=
    fun r => g (fieldOnePadicIntProductResidueRep p N r)
  let H : FieldOneFiniteCyclicProduct (fun i => p i ^ N i) → ℂ :=
    fun r => h (fieldOnePadicIntProductResidueRep p N r)
  let Pd : ℂ := ((∏ i, (p i : ℝ) ^ d i : ℝ) : ℂ)
  let M : ℕ := ∏ i, p i ^ N i
  let q := fieldOnePadicIntProductToFiniteQuotient p N
  have hgint : Integrable g (fieldOnePadicIntProductNormalizedHaar p) := by
    simpa only [g] using fieldOnePadicProductBruhatScaled_integrable p d f
  have hhint : Integrable h (fieldOnePadicIntProductNormalizedHaar p) := by
    simpa only [h] using fieldOnePadicProductBruhatScaled_integrable p d F
  have hgperiod : ∀ u z : FieldOnePadicIntProduct p,
      g (u + fieldOnePadicIntProductLatticePoint p N z) = g u := by
    simpa only [g, N] using
      fieldOnePadicProductBruhatScaled_period p d d f hperiodD
  have hhperiod : ∀ u z : FieldOnePadicIntProduct p,
      h (u + fieldOnePadicIntProductLatticePoint p N z) = h u := by
    simpa only [h, N] using
      fieldOnePadicProductBruhatScaled_period p d d F hFperiod
  have hcoeff (v : FieldOnePadicIntProduct p) :
      h v = Pd *
        fieldOnePadicIntProductCyclicFourierIntegral p N g (q v) := by
    change fieldOnePadicProductBruhatFourier p f
        (fieldOnePadicProductInvPowIntCoeAddMonoidHom p d v) = _
    exact fieldOnePadicProductBruhatFourier_invPow_coeff
      p d d f hsupportD v
  have hGcoeff (k : FieldOneFiniteCyclicProduct (fun i => p i ^ N i)) :
      fieldOnePadicIntProductCyclicFourierIntegral p N g k =
        ((M : ℂ)⁻¹) * fieldOneFiniteCyclicProductDFT
          (fun i => p i ^ N i) G k := by
    rw [fieldOnePadicIntProductCyclicFourierIntegral_eq
      p N g hgint hgperiod k]
    rfl
  have hH (r : FieldOneFiniteCyclicProduct (fun i => p i ^ N i)) :
      H r = (Pd * (M : ℂ)⁻¹) *
        fieldOneFiniteCyclicProductDFT (fun i => p i ^ N i) G r := by
    rw [show H r = h (fieldOnePadicIntProductResidueRep p N r) by rfl]
    rw [hcoeff, hGcoeff]
    rw [fieldOnePadicIntProductResidueRep_spec]
    ring
  have hGneg (u : FieldOnePadicIntProduct p) :
      G (-(q u)) = g (-u) := by
    apply fieldOnePadicIntProduct_classInvariant_of_primePowerInvariant
      p N g hgperiod
    rw [fieldOnePadicIntProductResidueRep_spec]
    exact (q.map_neg u).symm
  have hMfactor : (M : ℂ) = Pd * Pd := by
    dsimp only [M, N, Pd]
    push_cast
    simp only [pow_add, Finset.prod_mul_distrib]
  have hM0 : (M : ℂ) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.mpr fun i _ =>
      pow_ne_zero (N i) (Fact.out : Nat.Prime (p i)).ne_zero
  have hPd0 : Pd ≠ 0 := by
    intro hzero
    apply hM0
    rw [hMfactor, hzero, zero_mul]
  intro y
  by_cases hy : y ∈ Set.range
      (fieldOnePadicProductInvPowIntCoeAddMonoidHom p d)
  · obtain ⟨u, rfl⟩ := hy
    rw [fieldOnePadicProductBruhatFourier_invPow_coeff
      p d d F hFsupport u]
    rw [fieldOnePadicIntProductCyclicFourierIntegral_eq
      p N h hhint hhperiod (q u)]
    change Pd * ((M : ℂ)⁻¹ *
      fieldOneFiniteCyclicProductDFT (fun i => p i ^ N i) H (q u)) = _
    rw [show H = fun r => (Pd * (M : ℂ)⁻¹) *
        fieldOneFiniteCyclicProductDFT (fun i => p i ^ N i) G r from
      funext hH]
    rw [fieldOneFiniteCyclicProductDFT_const_mul]
    change Pd * ((M : ℂ)⁻¹ * ((Pd * (M : ℂ)⁻¹) *
      fieldOneFiniteCyclicProductDFT (fun i => p i ^ N i)
        (fieldOneFiniteCyclicProductDFT (fun i => p i ^ N i) G) (q u))) = _
    rw [show fieldOneFiniteCyclicProductDFT (fun i => p i ^ N i)
          (fieldOneFiniteCyclicProductDFT (fun i => p i ^ N i) G) (q u) =
        (M : ℂ) * G (-(q u)) by
      simpa only [M] using congrFun
        (fieldOneFiniteCyclicProductDFT_dft (fun i => p i ^ N i) G) (q u)]
    rw [hGneg]
    have hgrhs : g (-u) = f.1
        (-(fieldOnePadicProductInvPowIntCoeAddMonoidHom p d u)) := by
      change f.1 (fieldOnePadicProductInvPowIntCoeAddMonoidHom p d (-u)) = _
      rw [map_neg]
    rw [← hgrhs]
    change Pd * ((M : ℂ)⁻¹ * ((Pd * (M : ℂ)⁻¹) *
      ((M : ℂ) * g (-u)))) = g (-u)
    rw [hMfactor]
    field_simp
  · rw [fieldOnePadicProductBruhatFourier_eq_zero_outside_annihilator
      p d F hFperiod hy]
    have hneg : -y ∉ Set.range
        (fieldOnePadicProductInvPowIntCoeAddMonoidHom p d) := by
      intro hny
      apply hy
      obtain ⟨u, hu⟩ := hny
      refine ⟨-u, ?_⟩
      rw [map_neg, hu, neg_neg]
    have hnotSupport : -y ∉ tsupport
        (f.1 : FieldOnePadicProduct p → ℂ) := by
      intro hts
      apply hneg
      rw [fieldOnePadicProductInvPowIntCoeAddMonoidHom_range]
      intro i _
      exact hsupportD (-y) hts i
    rw [image_eq_zero_of_notMem_tsupport hnotSupport]

/-- Exact Fourier inversion for every product p-adic Bruhat function. -/
theorem fieldOnePadicProductBruhatFourier_fourier
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p)) :
    ∀ y,
      fieldOnePadicProductBruhatFourier p
          (fieldOnePadicProductBruhatFourierBruhat p f) y =
        f.1 (-y) := by
  obtain ⟨n, m, hsupport, hperiod⟩ :=
    fieldOnePadicProductBruhat_exists_finiteLevel p f
  exact fieldOnePadicProductBruhatFourier_fourier_of_finiteLevel
    p n m f hsupport hperiod

/-- The product p-adic Bruhat Fourier transform is an algebraic linear
equivalence.  Its inverse is its third power because its square is reflection. -/
def fieldOnePadicProductBruhatFourierLinearEquiv :
    compactlySupportedLocallyConstant (FieldOnePadicProduct p) ≃ₗ[ℂ]
      compactlySupportedLocallyConstant (FieldOnePadicProduct p) where
  toLinearMap := fieldOnePadicProductBruhatFourierLinear p
  invFun f := fieldOnePadicProductBruhatFourierLinear p
    (fieldOnePadicProductBruhatFourierLinear p
      (fieldOnePadicProductBruhatFourierLinear p f))
  left_inv f := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    change fieldOnePadicProductBruhatFourier p
        (fieldOnePadicProductBruhatFourierBruhat p
          (fieldOnePadicProductBruhatFourierBruhat p
            (fieldOnePadicProductBruhatFourierBruhat p f))) y = f.1 y
    rw [fieldOnePadicProductBruhatFourier_fourier]
    change fieldOnePadicProductBruhatFourier p
      (fieldOnePadicProductBruhatFourierBruhat p f) (-y) = f.1 y
    rw [fieldOnePadicProductBruhatFourier_fourier]
    simp
  right_inv f := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    change fieldOnePadicProductBruhatFourier p
        (fieldOnePadicProductBruhatFourierBruhat p
          (fieldOnePadicProductBruhatFourierBruhat p
            (fieldOnePadicProductBruhatFourierBruhat p f))) y = f.1 y
    rw [fieldOnePadicProductBruhatFourier_fourier]
    change fieldOnePadicProductBruhatFourier p
      (fieldOnePadicProductBruhatFourierBruhat p f) (-y) = f.1 y
    rw [fieldOnePadicProductBruhatFourier_fourier]
    simp

@[simp] theorem fieldOnePadicProductBruhatFourierLinearEquiv_apply
    (f : compactlySupportedLocallyConstant (FieldOnePadicProduct p)) :
    fieldOnePadicProductBruhatFourierLinearEquiv p f =
      fieldOnePadicProductBruhatFourierBruhat p f :=
  rfl

end

end GaloisForLFunctions.RHTower
