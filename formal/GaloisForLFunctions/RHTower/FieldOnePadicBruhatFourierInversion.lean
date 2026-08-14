import GaloisForLFunctions.RHTower.FieldOnePadicBruhatFourierSelfMap

/-!
# Fourier inversion on one p-adic field

The unit-ball-normalized Haar measure is self-dual for the canonical additive
character. This file proves the pointwise Fourier-square identity on every
literal `ℚ_p` Bruhat function and bundles the transform as a linear
equivalence.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Pointwise ComplexConjugate

variable (p : ℕ) [Fact p.Prime]

theorem fieldOnePadicBruhatFourier_tsupport_subset_annihilator
    (m : ℕ) (f : compactlySupportedLocallyConstant ℚ_[p])
    (hperiod : ∀ x : ℚ_[p], ∀ z : ℤ_[p],
      f.1 (x + (p : ℚ_[p]) ^ m * (z : ℚ_[p])) = f.1 x) :
    tsupport (fieldOnePadicBruhatFourier p f) ⊆
      fieldOnePadicDenominatorStage p m := by
  let R := Set.range (fieldOnePadicInvPowIntCoeAddMonoidHom p m)
  have hRcompact : IsCompact R := by
    change IsCompact (Set.range
      (fieldOnePadicInvPowIntCoeAddMonoidHom p m))
    rw [← Set.image_univ]
    exact isCompact_univ.image
      (fieldOnePadicInvPowIntCoeAddMonoidHom_isOpenEmbedding p m).continuous
  have hsupport : Function.support (fieldOnePadicBruhatFourier p f) ⊆ R := by
    intro y hy
    by_contra hyout
    have hystage : y ∉ fieldOnePadicDenominatorStage p m := by
      intro hystage
      apply hyout
      change y ∈ Set.range (fieldOnePadicInvPowIntCoeAddMonoidHom p m)
      rw [fieldOnePadicInvPowIntCoeAddMonoidHom_range]
      exact hystage
    exact hy (fieldOnePadicBruhatFourier_eq_zero_outside_annihilator
      p m f hperiod hystage)
  have htop : tsupport (fieldOnePadicBruhatFourier p f) ⊆ R :=
    closure_minimal hsupport hRcompact.isClosed
  intro y hy
  rw [← fieldOnePadicInvPowIntCoeAddMonoidHom_range p m]
  exact htop hy

theorem fieldOnePadicBruhatFourier_period
    (n : ℕ) (f : compactlySupportedLocallyConstant ℚ_[p])
    (hsupport : tsupport (f.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p n) :
    ∀ y : ℚ_[p], ∀ z : ℤ_[p],
      fieldOnePadicBruhatFourier p f
          (y + (p : ℚ_[p]) ^ n * (z : ℚ_[p])) =
        fieldOnePadicBruhatFourier p f y :=
  fieldOnePadicBruhatFourier_add_primePow p n f hsupport

private theorem fieldOnePadicBruhatFourier_fourier_of_finiteLevel
    (n m : ℕ) (f : compactlySupportedLocallyConstant ℚ_[p])
    (hsupport : tsupport (f.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p n)
    (hperiod : ∀ x : ℚ_[p], ∀ z : ℤ_[p],
      f.1 (x + (p : ℚ_[p]) ^ m * (z : ℚ_[p])) = f.1 x) :
    ∀ y,
      fieldOnePadicBruhatFourier p
          (fieldOnePadicBruhatFourierBruhat p f) y = f.1 (-y) := by
  let d := n + m
  let N := d + d
  let F := fieldOnePadicBruhatFourierBruhat p f
  have hsupportD : tsupport (f.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p d := by
    exact hsupport.trans (fieldOnePadicDenominatorStage_mono p
      (Nat.le_add_right n m))
  have hperiodD : ∀ x : ℚ_[p], ∀ z : ℤ_[p],
      f.1 (x + (p : ℚ_[p]) ^ d * (z : ℚ_[p])) = f.1 x := by
    intro x z
    let z' : ℤ_[p] := (p : ℤ_[p]) ^ n * z
    rw [show (p : ℚ_[p]) ^ d * (z : ℚ_[p]) =
        (p : ℚ_[p]) ^ m * (z' : ℚ_[p]) by
      simp only [d, z', PadicInt.coe_mul, PadicInt.coe_pow,
        PadicInt.coe_natCast, pow_add]
      ring]
    exact hperiod x z'
  have hFsupport0 : tsupport (F.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p m := by
    intro y hy
    apply fieldOnePadicBruhatFourier_tsupport_subset_annihilator
      p m f hperiod
    exact hy
  have hFperiod0 : ∀ y : ℚ_[p], ∀ z : ℤ_[p],
      F.1 (y + (p : ℚ_[p]) ^ n * (z : ℚ_[p])) = F.1 y := by
    simpa only [F, fieldOnePadicBruhatFourierBruhat_apply] using
      fieldOnePadicBruhatFourier_period p n f hsupport
  have hFsupport : tsupport (F.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p d := by
    exact hFsupport0.trans (fieldOnePadicDenominatorStage_mono p
      (Nat.le_add_left m n))
  have hFperiod : ∀ y : ℚ_[p], ∀ z : ℤ_[p],
      F.1 (y + (p : ℚ_[p]) ^ d * (z : ℚ_[p])) = F.1 y := by
    intro y z
    let z' : ℤ_[p] := (p : ℤ_[p]) ^ m * z
    rw [show (p : ℚ_[p]) ^ d * (z : ℚ_[p]) =
        (p : ℚ_[p]) ^ n * (z' : ℚ_[p]) by
      simp only [d, z', PadicInt.coe_mul, PadicInt.coe_pow,
        PadicInt.coe_natCast, pow_add]
      ring]
    exact hFperiod0 y z'
  let g : ℤ_[p] → ℂ := fieldOnePadicBruhatScaled p d f
  let h : ℤ_[p] → ℂ := fieldOnePadicBruhatScaled p d F
  let G : ZMod (p ^ N) → ℂ :=
    fun r => g (fieldOnePadicIntResidueRep p N r)
  let H : ZMod (p ^ N) → ℂ :=
    fun r => h (fieldOnePadicIntResidueRep p N r)
  let Pd : ℂ := ((p : ℝ) ^ d : ℂ)
  let M : ℕ := p ^ N
  let q := PadicInt.toZModPow (p := p) N
  have hgint : Integrable g (fieldOnePadicIntNormalizedHaar p) := by
    simpa only [g] using fieldOnePadicBruhatScaled_integrable p d f
  have hhint : Integrable h (fieldOnePadicIntNormalizedHaar p) := by
    simpa only [h] using fieldOnePadicBruhatScaled_integrable p d F
  have hgperiod : ∀ u z : ℤ_[p],
      g (u + (p : ℤ_[p]) ^ N * z) = g u := by
    simpa only [g, N] using
      fieldOnePadicBruhatScaled_period p d d f hperiodD
  have hhperiod : ∀ u z : ℤ_[p],
      h (u + (p : ℤ_[p]) ^ N * z) = h u := by
    simpa only [h, N] using
      fieldOnePadicBruhatScaled_period p d d F hFperiod
  have hcoeff (v : ℤ_[p]) :
      h v = Pd * fieldOnePadicIntCyclicFourierIntegral p N g (q v) := by
    change fieldOnePadicBruhatFourier p f
      (fieldOnePadicInvPowIntCoeAddMonoidHom p d v) = _
    exact fieldOnePadicBruhatFourier_invPow_coeff
      p d d f hsupportD v
  have hGcoeff (k : ZMod (p ^ N)) :
      fieldOnePadicIntCyclicFourierIntegral p N g k =
        ((M : ℂ)⁻¹) * ZMod.dft G k := by
    rw [fieldOnePadicIntCyclicFourierIntegral_eq p N g
      hgint hgperiod k]
    rfl
  have hH (r : ZMod (p ^ N)) :
      H r = (Pd * (M : ℂ)⁻¹) * ZMod.dft G r := by
    rw [show H r = h (fieldOnePadicIntResidueRep p N r) by rfl]
    rw [hcoeff, hGcoeff, fieldOnePadicIntResidueRep_spec]
    ring
  have hGneg (u : ℤ_[p]) : G (-(q u)) = g (-u) := by
    apply fieldOnePadicInt_classInvariant_of_primePowerInvariant
      p N g hgperiod
    rw [fieldOnePadicIntResidueRep_spec]
    exact (q.map_neg u).symm
  have hMfactor : (M : ℂ) = Pd * Pd := by
    dsimp only [M, N, Pd]
    push_cast
    rw [pow_add]
  have hM0 : (M : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero N (Fact.out : Nat.Prime p).ne_zero
  have hPd0 : Pd ≠ 0 := by
    intro hzero
    apply hM0
    rw [hMfactor, hzero, zero_mul]
  intro y
  by_cases hy : y ∈ Set.range
      (fieldOnePadicInvPowIntCoeAddMonoidHom p d)
  · obtain ⟨u, rfl⟩ := hy
    rw [fieldOnePadicBruhatFourier_invPow_coeff
      p d d F hFsupport u]
    rw [fieldOnePadicIntCyclicFourierIntegral_eq
      p N h hhint hhperiod (q u)]
    change Pd * ((M : ℂ)⁻¹ * ZMod.dft H (q u)) = _
    rw [show H = fun r => (Pd * (M : ℂ)⁻¹) * ZMod.dft G r from
      funext hH]
    rw [ZMod.dft_const_mul]
    change Pd * ((M : ℂ)⁻¹ * ((Pd * (M : ℂ)⁻¹) *
      ZMod.dft (ZMod.dft G) (q u))) = _
    rw [show ZMod.dft (ZMod.dft G) (q u) =
        (M : ℂ) * G (-(q u)) by
      simpa only [M, smul_eq_mul] using
        congrFun (ZMod.dft_dft G) (q u)]
    rw [hGneg]
    have hgrhs : g (-u) = f.1
        (-(fieldOnePadicInvPowIntCoeAddMonoidHom p d u)) := by
      change f.1 (fieldOnePadicInvPowIntCoeAddMonoidHom p d (-u)) = _
      rw [map_neg]
    rw [← hgrhs]
    rw [hMfactor]
    field_simp
  · have hystage : y ∉ fieldOnePadicDenominatorStage p d := by
      intro hystage
      apply hy
      rw [fieldOnePadicInvPowIntCoeAddMonoidHom_range]
      exact hystage
    rw [fieldOnePadicBruhatFourier_eq_zero_outside_annihilator
      p d F hFperiod hystage]
    have hneg : -y ∉ Set.range
        (fieldOnePadicInvPowIntCoeAddMonoidHom p d) := by
      intro hny
      apply hy
      obtain ⟨u, hu⟩ := hny
      refine ⟨-u, ?_⟩
      rw [map_neg, hu, neg_neg]
    have hnotSupport : -y ∉ tsupport (f.1 : ℚ_[p] → ℂ) := by
      intro hts
      apply hneg
      rw [fieldOnePadicInvPowIntCoeAddMonoidHom_range]
      exact hsupportD hts
    rw [image_eq_zero_of_notMem_tsupport hnotSupport]

/-- Exact Fourier inversion for every literal p-adic Bruhat function. -/
theorem fieldOnePadicBruhatFourier_fourier
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    ∀ y,
      fieldOnePadicBruhatFourier p
          (fieldOnePadicBruhatFourierBruhat p f) y = f.1 (-y) := by
  obtain ⟨n, m, hsupport, hperiod⟩ :=
    fieldOnePadicBruhat_exists_finiteLevel p f
  exact fieldOnePadicBruhatFourier_fourier_of_finiteLevel
    p n m f hsupport hperiod

/-- The p-adic Bruhat Fourier transform as an algebraic linear equivalence. -/
def fieldOnePadicBruhatFourierLinearEquiv :
    compactlySupportedLocallyConstant ℚ_[p] ≃ₗ[ℂ]
      compactlySupportedLocallyConstant ℚ_[p] where
  toLinearMap := fieldOnePadicBruhatFourierLinear p
  invFun f := fieldOnePadicBruhatFourierLinear p
    (fieldOnePadicBruhatFourierLinear p
      (fieldOnePadicBruhatFourierLinear p f))
  left_inv f := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    change fieldOnePadicBruhatFourier p
        (fieldOnePadicBruhatFourierBruhat p
          (fieldOnePadicBruhatFourierBruhat p
            (fieldOnePadicBruhatFourierBruhat p f))) y = f.1 y
    rw [fieldOnePadicBruhatFourier_fourier]
    change fieldOnePadicBruhatFourier p
      (fieldOnePadicBruhatFourierBruhat p f) (-y) = f.1 y
    rw [fieldOnePadicBruhatFourier_fourier]
    simp
  right_inv f := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    change fieldOnePadicBruhatFourier p
        (fieldOnePadicBruhatFourierBruhat p
          (fieldOnePadicBruhatFourierBruhat p
            (fieldOnePadicBruhatFourierBruhat p f))) y = f.1 y
    rw [fieldOnePadicBruhatFourier_fourier]
    change fieldOnePadicBruhatFourier p
      (fieldOnePadicBruhatFourierBruhat p f) (-y) = f.1 y
    rw [fieldOnePadicBruhatFourier_fourier]
    simp

@[simp] theorem fieldOnePadicBruhatFourierLinearEquiv_apply
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicBruhatFourierLinearEquiv p f =
      fieldOnePadicBruhatFourierBruhat p f :=
  rfl

end

end GaloisForLFunctions.RHTower

