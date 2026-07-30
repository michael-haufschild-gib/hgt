import GaloisForLFunctions.RHTower.XiGuinandWeilSpectralRectangle
import GaloisForLFunctions.HTGeometry.PowerSumTorelli
import GaloisForLFunctions.HTGeometry.CayleyPoleResidueTransport

open Complex Filter intervalIntegral Set
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions

noncomputable section

def xiArithmeticSourceRectangleMoment
    (z₁ z₂ : ℂ) (k : ℕ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    rectIntegral
      (fun z => z ^ k * continuedPrimeArchSourceRelativeTrace z)
      z₁ z₂

def xiZeroCopyClosedRectangleEnumeration
    (z₁ z₂ : ℂ) :
    Fin (xiZeroCopyClosedRectangle z₁ z₂).card → XiZeroCopy :=
  fun i => ((xiZeroCopyClosedRectangle z₁ z₂).equivFin.symm i).1

theorem sum_enumeration_eq_sum_xiZeroCopyClosedRectangle
    (z₁ z₂ : ℂ) (f : XiZeroCopy → ℂ) :
    ∑ i, f (xiZeroCopyClosedRectangleEnumeration z₁ z₂ i) =
      ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂, f q := by
  let t := xiZeroCopyClosedRectangle z₁ z₂
  change ∑ i : Fin t.card, f ((t.equivFin.symm i).1) =
    ∑ q ∈ t, f q
  calc
    ∑ i : Fin t.card, f ((t.equivFin.symm i).1) =
        ∑ q : ↥t, f q.1 :=
      t.equivFin.symm.sum_comp (fun q : ↥t => f q.1)
    _ = ∑ q ∈ t, f q := by
      simp only [Finset.univ_eq_attach, Finset.sum_attach]

theorem xiArithmeticSourceRectangleMoment_eq_zeroPowerSum
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (k : ℕ) :
    xiArithmeticSourceRectangleMoment z₁ z₂ k =
      ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiSpectralPoint q ^ k := by
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => z ^ k) Set.univ := by
    intro z _
    exact analyticAt_id.pow k
  have hcontour :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_xiZeroCopyClosedRectangleSum
      hg hre him hbot htop hright hleft
  rw [xiArithmeticSourceRectangleMoment, hcontour]
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  field_simp [hc]

theorem xiArithmeticSourceRectangleMoment_eq_enumeratedPowerSum
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (k : ℕ) :
    xiArithmeticSourceRectangleMoment z₁ z₂ k =
      ∑ i,
        xiSpectralPoint
          (xiZeroCopyClosedRectangleEnumeration z₁ z₂ i) ^ k := by
  rw [xiArithmeticSourceRectangleMoment_eq_zeroPowerSum
    hre him hbot htop hright hleft]
  symm
  exact sum_enumeration_eq_sum_xiZeroCopyClosedRectangle
    z₁ z₂ (fun q => xiSpectralPoint q ^ k)

/-- The zeroth arithmetic contour moment is the exact number of zero copies
inside the rectangle. Thus the amount of moment data needed by Torelli is
itself source-determined. -/
theorem xiArithmeticSourceRectangleMoment_zero_eq_card
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) :
    xiArithmeticSourceRectangleMoment z₁ z₂ 0 =
      ((xiZeroCopyClosedRectangle z₁ z₂).card : ℂ) := by
  rw [xiArithmeticSourceRectangleMoment_eq_zeroPowerSum
    hre him hbot htop hright hleft]
  simp

theorem xiArithmeticSourceRectangleMoment_torelli
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (f : Fin (xiZeroCopyClosedRectangle z₁ z₂).card → ℂ)
    (hmom : ∀ k ≤ (xiZeroCopyClosedRectangle z₁ z₂).card,
      ∑ i, f i ^ k =
        xiArithmeticSourceRectangleMoment z₁ z₂ k) :
    Finset.univ.val.map f =
      Finset.univ.val.map
        (fun i => xiSpectralPoint
          (xiZeroCopyClosedRectangleEnumeration z₁ z₂ i)) := by
  apply powerSum_torelli_finite
  intro k hk
  have hmoment := hmom k hk
  rw [xiArithmeticSourceRectangleMoment_eq_enumeratedPowerSum
    hre him hbot htop hright hleft] at hmoment
  change
    (Finset.univ.val.map (fun i => f i ^ k)).sum =
      (Finset.univ.val.map
        (fun i => xiSpectralPoint
          (xiZeroCopyClosedRectangleEnumeration z₁ z₂ i) ^ k)).sum
  simpa only [← Finset.sum_eq_multiset_sum] using hmoment

def xiSourceFrequencyFromSpectralPoint (w : ℂ) : ℂ :=
  (I * w - 1 / 2)⁻¹

theorem xiSourceFrequencyFromSpectralPoint_eq
    (q : XiZeroCopy) :
    xiSourceFrequencyFromSpectralPoint (xiSpectralPoint q) =
      ((q.1 : ℂ) - 1)⁻¹ := by
  rw [xiSpectralPoint_eq_support]
  unfold xiSourceFrequencyFromSpectralPoint xiSpectralPointSupport
  congr 1
  ring_nf
  rw [I_sq]
  ring

/-- The source-frequency circle is exactly the critical line. This is
the finite-divisor horizon test after arithmetic moment reconstruction. -/
theorem xiSourceFrequency_shift_norm_one_iff_criticalLine
    (q : XiZeroCopy) :
    ‖1 + xiSourceFrequencyFromSpectralPoint (xiSpectralPoint q)‖ = 1 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have hq1 : (q.1 : ℂ) ≠ 1 := by
    have hs := xi_divisor_support_re_mem_open_unit q.1
    intro h
    rw [h] at hs
    norm_num at hs
  have hb : ((q.1 : ℂ) - 1)⁻¹ ≠ 0 :=
    inv_ne_zero (sub_ne_zero.mpr hq1)
  rw [xiSourceFrequencyFromSpectralPoint_eq]
  rw [← GaloisForLFunctions.HTGeometry.coherentGeneratorDualRate_eq_zero_iff_shift_norm_one
    ((q.1 : ℂ) - 1)⁻¹ hb]
  rw [GaloisForLFunctions.HTGeometry.coherentGeneratorDualRate_sourceCayley]
  have h :=
    GaloisForLFunctions.HTGeometry.sourceCayleyTransverseRate_eq_zero_iff
      (1 : ℂ) (q.1 : ℂ)
  norm_num at h
  exact h

theorem xiArithmeticSourceRectangleMoment_sourceFrequency_torelli
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (f : Fin (xiZeroCopyClosedRectangle z₁ z₂).card → ℂ)
    (hmom : ∀ k ≤ (xiZeroCopyClosedRectangle z₁ z₂).card,
      ∑ i, f i ^ k =
        xiArithmeticSourceRectangleMoment z₁ z₂ k) :
    (Finset.univ.val.map f).map xiSourceFrequencyFromSpectralPoint =
      Finset.univ.val.map
        (fun i => (((
          xiZeroCopyClosedRectangleEnumeration z₁ z₂ i).1 : ℂ) - 1)⁻¹) := by
  rw [xiArithmeticSourceRectangleMoment_torelli
    hre him hbot htop hright hleft f hmom,
    Multiset.map_map]
  simp [Function.comp_apply,
    xiSourceFrequencyFromSpectralPoint_eq]

/-- Exact certificate that the continued prime--archimedean boundary source
generates every finite centered Xi divisor and its Cayley source spectrum. -/
structure XiArithmeticSourceMomentTorelliCertificate : Prop where
  sourceMoments :
    ∀ {z₁ z₂ : ℂ}, z₁.re < z₂.re → z₁.im < z₂.im →
      (∀ x ∈ uIcc z₁.re z₂.re,
        XiExplicitAdmissible ((x : ℂ) + z₁.im * I)) →
      (∀ x ∈ uIcc z₁.re z₂.re,
        XiExplicitAdmissible ((x : ℂ) + z₂.im * I)) →
      (∀ y ∈ uIcc z₁.im z₂.im,
        XiExplicitAdmissible ((z₂.re : ℂ) + y * I)) →
      (∀ y ∈ uIcc z₁.im z₂.im,
        XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) →
      ∀ k : ℕ,
        xiArithmeticSourceRectangleMoment z₁ z₂ k =
          ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
            xiSpectralPoint q ^ k
  sourceCount :
    ∀ {z₁ z₂ : ℂ}, z₁.re < z₂.re → z₁.im < z₂.im →
      (∀ x ∈ uIcc z₁.re z₂.re,
        XiExplicitAdmissible ((x : ℂ) + z₁.im * I)) →
      (∀ x ∈ uIcc z₁.re z₂.re,
        XiExplicitAdmissible ((x : ℂ) + z₂.im * I)) →
      (∀ y ∈ uIcc z₁.im z₂.im,
        XiExplicitAdmissible ((z₂.re : ℂ) + y * I)) →
      (∀ y ∈ uIcc z₁.im z₂.im,
        XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) →
        xiArithmeticSourceRectangleMoment z₁ z₂ 0 =
          ((xiZeroCopyClosedRectangle z₁ z₂).card : ℂ)
  sourceTorelli :
    ∀ {z₁ z₂ : ℂ}, z₁.re < z₂.re → z₁.im < z₂.im →
      (∀ x ∈ uIcc z₁.re z₂.re,
        XiExplicitAdmissible ((x : ℂ) + z₁.im * I)) →
      (∀ x ∈ uIcc z₁.re z₂.re,
        XiExplicitAdmissible ((x : ℂ) + z₂.im * I)) →
      (∀ y ∈ uIcc z₁.im z₂.im,
        XiExplicitAdmissible ((z₂.re : ℂ) + y * I)) →
      (∀ y ∈ uIcc z₁.im z₂.im,
        XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) →
      ∀ (f : Fin (xiZeroCopyClosedRectangle z₁ z₂).card → ℂ),
        (∀ k ≤ (xiZeroCopyClosedRectangle z₁ z₂).card,
          ∑ i, f i ^ k =
            xiArithmeticSourceRectangleMoment z₁ z₂ k) →
        Finset.univ.val.map f =
          Finset.univ.val.map
            (fun i => xiSpectralPoint
              (xiZeroCopyClosedRectangleEnumeration z₁ z₂ i))
  sourceFrequencyTorelli :
    ∀ {z₁ z₂ : ℂ}, z₁.re < z₂.re → z₁.im < z₂.im →
      (∀ x ∈ uIcc z₁.re z₂.re,
        XiExplicitAdmissible ((x : ℂ) + z₁.im * I)) →
      (∀ x ∈ uIcc z₁.re z₂.re,
        XiExplicitAdmissible ((x : ℂ) + z₂.im * I)) →
      (∀ y ∈ uIcc z₁.im z₂.im,
        XiExplicitAdmissible ((z₂.re : ℂ) + y * I)) →
      (∀ y ∈ uIcc z₁.im z₂.im,
        XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) →
      ∀ (f : Fin (xiZeroCopyClosedRectangle z₁ z₂).card → ℂ),
        (∀ k ≤ (xiZeroCopyClosedRectangle z₁ z₂).card,
          ∑ i, f i ^ k =
            xiArithmeticSourceRectangleMoment z₁ z₂ k) →
        (Finset.univ.val.map f).map xiSourceFrequencyFromSpectralPoint =
          Finset.univ.val.map
            (fun i => (((
              xiZeroCopyClosedRectangleEnumeration z₁ z₂ i).1 : ℂ) - 1)⁻¹)
  neutralCircle :
    ∀ q : XiZeroCopy,
      ‖1 + xiSourceFrequencyFromSpectralPoint (xiSpectralPoint q)‖ = 1 ↔
        (q.1 : ℂ).re = 1 / 2

/-- **Arithmetic source-moment Torelli law.** -/
theorem xiArithmeticSourceMomentTorelli_law :
    XiArithmeticSourceMomentTorelliCertificate := by
  exact {
    sourceMoments :=
      xiArithmeticSourceRectangleMoment_eq_zeroPowerSum
    sourceCount :=
      xiArithmeticSourceRectangleMoment_zero_eq_card
    sourceTorelli :=
      xiArithmeticSourceRectangleMoment_torelli
    sourceFrequencyTorelli :=
      xiArithmeticSourceRectangleMoment_sourceFrequency_torelli
    neutralCircle :=
      xiSourceFrequency_shift_norm_one_iff_criticalLine }

end

end RHTower
