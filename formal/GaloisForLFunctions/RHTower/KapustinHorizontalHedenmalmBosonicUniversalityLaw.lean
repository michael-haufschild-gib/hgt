import GaloisForLFunctions.RHTower.KapustinHorizontalMultiplicityUniversalityLaw
import GaloisForLFunctions.RHTower.XiHorizontalMultiplicityOneUniversalityLaw
import GaloisForLFunctions.RHTower.XiHedenmalmSimplicityUniversalityLaw

/-!
# Kapustin--horizontal--Hedenmalm--bosonic universality

A symmetric realization of every Kapustin Xi-divisor spectral point already forces RH.  The
remaining simplicity datum can then be read interchangeably from the horizontal divisor census,
the complete Hedenmalm simplicity certificate, small-circle winding, or every normalized bosonic
jet residue.
-/

open Complex
open Module.End

namespace RHTower

noncomputable section

/-- Analytic order one at every uncentered Xi zero is exactly simplicity in the centered
Hedenmalm coordinate. -/
theorem xiOrderOne_iff_xiZerosSimple :
    (∀ ρ : ℂ, xi ρ = 0 → (analyticOrderAt xi ρ).toNat = 1) ↔
      XiZerosSimple := by
  constructor
  · intro horder alpha hzero
    let ρ : ℂ := 1 / 2 + alpha * I
    have hzeroρ : xi ρ = 0 := by
      simpa only [ρ, XiC] using hzero
    have horderNat := horder ρ hzeroρ
    have horderExact : analyticOrderAt xi ρ = (1 : ℕ∞) := by
      calc
        analyticOrderAt xi ρ =
            ((analyticOrderAt xi ρ).toNat : ℕ∞) :=
          (ENat.coe_toNat (xi_order_ne_top ρ)).symm
        _ = 1 := by simp [horderNat]
    have hderivOrder : analyticOrderAt (deriv xi) ρ = 0 := by
      exact analyticOrderAt_deriv_of_pos
        (xi_analyticOnNhd_univ ρ (Set.mem_univ ρ))
        (n := 0) (by simpa using horderExact)
    have hderiv : deriv xi ρ ≠ 0 :=
      ((xi_analyticOnNhd_univ ρ (Set.mem_univ ρ)).deriv.analyticOrderAt_eq_zero).1
        hderivOrder
    rw [deriv_XiC_eq_deriv_xi_mul_I]
    exact mul_ne_zero hderiv I_ne_zero
  · intro hsimple ρ hzero
    let alpha : ℂ := (ρ - 1 / 2) * (-I)
    have hcoord : 1 / 2 + alpha * I = ρ := by
      dsimp only [alpha]
      rw [mul_assoc, neg_mul, I_mul_I]
      ring
    have hzeroC : XiC alpha = 0 := by
      rw [XiC, hcoord]
      exact hzero
    have hderivC := hsimple hzeroC
    rw [deriv_XiC_eq_deriv_xi_mul_I, hcoord] at hderivC
    have hderiv : deriv xi ρ ≠ 0 := by
      intro hz
      simp only [hz, zero_mul] at hderivC
      exact hderivC rfl
    have horder :=
      (xi_analyticOnNhd_univ ρ (Set.mem_univ ρ))
        |>.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hderiv
    simpa using congrArg ENat.toNat horder

/-- Local unit-multiplicity fingerprint shared by the horizontal divisor census, small-circle
winding, and every normalized bosonic jet residue. -/
def XiUnitHorizontalWindingBosonicFingerprint : Prop :=
  ∀ ρ : ℂ, xi ρ = 0 →
    ∃ R : ℝ, 0 < R ∧ ∃ U : ℂ → ℂ,
      AnalyticAt ℂ U 0 ∧ U 0 ≠ 0 ∧
      (∀ z ∈ Metric.ball 0 R,
        xi (ρ + z) =
          GaloisForLFunctions.multipleZeroSection 1 U z) ∧
      (∀ r : ℝ, 0 < r → r < R →
        windingNumber (fun θ => xi (ρ + ↑r * exp (I * ↑θ))) 0
          (2 * Real.pi) = 1) ∧
      ∀ k : ℕ, k ≤ 1 →
        Filter.Tendsto
          (fun z : ℂ => z ^ k *
            (iteratedDeriv k
                (GaloisForLFunctions.multipleZeroSection 1 U) z /
              GaloisForLFunctions.multipleZeroSection 1 U z))
          (nhdsWithin 0 {0}ᶜ)
          (nhds ((1 : ℕ).descFactorial k : ℂ))

/-- The unit local-factor, winding, and bosonic-residue fingerprint contains exactly the
simplicity information of the Xi divisor.  No spectral realization is needed. -/
theorem xiUnitHorizontalWindingBosonicFingerprint_iff_xiZerosSimple :
    XiUnitHorizontalWindingBosonicFingerprint ↔ XiZerosSimple := by
  rw [← xiOrderOne_iff_xiZerosSimple]
  constructor
  · intro hfingerprint ρ hzero
    obtain ⟨R, hR, _U, _hU, _hU0, _hfactor, hwinding, _hbosonic⟩ :=
      hfingerprint ρ hzero
    obtain ⟨Rw, hRw, hwindOrder⟩ := windingNumber_xi_zero ρ
    let r := min R Rw / 2
    have hr : 0 < r := half_pos (lt_min hR hRw)
    have hrR : r < R := by
      exact (div_lt_self (lt_min hR hRw) (by norm_num : (1 : ℝ) < 2)).trans_le
        (min_le_left R Rw)
    have hrRw : r < Rw := by
      exact (div_lt_self (lt_min hR hRw) (by norm_num : (1 : ℝ) < 2)).trans_le
        (min_le_right R Rw)
    have hunit := hwinding r hr hrR
    have horder := hwindOrder r hr hrRw
    have hcast : ((analyticOrderAt xi ρ).toNat : ℤ) = 1 := horder.symm.trans hunit
    exact_mod_cast hcast
  · intro horder ρ hzero
    obtain ⟨Rp, hRp, h, hhan, hh0, hfact⟩ := xi_peel_ball ρ
    obtain ⟨Rw, hRw, hwind⟩ := windingNumber_xi_zero ρ
    let R := min Rp Rw
    let U : ℂ → ℂ := fun z => h (ρ + z)
    have hR : 0 < R := lt_min hRp hRw
    have hρp : ρ ∈ Metric.ball ρ Rp := Metric.mem_ball_self hRp
    have hU : AnalyticAt ℂ U 0 := by
      have hcomp := AnalyticAt.comp_of_eq (hhan ρ hρp)
        (by fun_prop : AnalyticAt ℂ (fun z : ℂ => ρ + z) 0) (by ring)
      simpa [U, Function.comp_def] using hcomp
    have hU0 : U 0 ≠ 0 := by
      simpa [U] using hh0 ρ hρp
    have hm : (analyticOrderAt xi ρ).toNat = 1 := horder ρ hzero
    refine ⟨R, hR, U, hU, hU0, ?_, ?_, ?_⟩
    · intro z hz
      have hzR : ρ + z ∈ Metric.ball ρ R := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      have hzRp : ρ + z ∈ Metric.ball ρ Rp :=
        Metric.ball_subset_ball (min_le_left Rp Rw) hzR
      have hf := hfact (ρ + z) hzRp
      rw [hm] at hf
      simpa [GaloisForLFunctions.multipleZeroSection, U] using hf
    · intro r hr hrR
      have hrRw : r < Rw := hrR.trans_le (min_le_right Rp Rw)
      simpa [hm] using hwind r hr hrRw
    · intro k hk
      exact GaloisForLFunctions.tendsto_scaled_multipleZeroCorrelator_descFactorial
        1 k hk hU hU0

/-- The complete local winding/bosonic fingerprint is the existing Hedenmalm simplicity
certificate, expressed without its auxiliary universal quantifiers. -/
theorem
    xiUnitHorizontalWindingBosonicFingerprint_iff_hendenmalmSimplicityUniversalCertificate :
    XiUnitHorizontalWindingBosonicFingerprint ↔
      XiHedenmalmSimplicityUniversalCertificate := by
  exact xiUnitHorizontalWindingBosonicFingerprint_iff_xiZerosSimple.trans
    xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate

/-- Horizontal multiplicity one is the complete RH-and-simplicity Hedenmalm certificate. -/
theorem
    xiHorizontalFibersMultiplicityOne_iff_hendenmalmRHSimplicityUniversalCertificate :
    XiHorizontalFibersMultiplicityOne ↔
      XiHedenmalmRHSimplicityUniversalCertificate := by
  rw [xiHorizontalFibersMultiplicityOne_iff_rh_and_orderOne,
    and_congr Iff.rfl xiOrderOne_iff_xiZerosSimple,
    riemannHypothesis_and_xiZerosSimple_iff_hendenmalmUniversalCertificate]

/-- Under a symmetric Kapustin point spectrum, the horizontal mass-one phase is exactly the
Hedenmalm simplicity certificate: the spectral hypothesis has discharged RH. -/
theorem
    kapustin_symmetricPointSpectrum_horizontalMultiplicityOne_iff_hendenmalmSimplicity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hspec : ∀ ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
      HasEigenvalue T (GaloisForLFunctions.kapustinEigenvalue (ρ : ℂ))) :
    XiHorizontalFibersMultiplicityOne ↔
      XiHedenmalmSimplicityUniversalCertificate := by
  have hRH := riemannHypothesis_of_kapustin_symmetric_pointSpectrum T hT hspec
  constructor
  · intro hhorizontal
    exact xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate.1
      (xiOrderOne_iff_xiZerosSimple.1
        ((xiHorizontalFibersMultiplicityOne_iff_rh_and_orderOne.1
          hhorizontal).2))
  · intro hsimplicity
    exact xiHorizontalFibersMultiplicityOne_iff_rh_and_orderOne.2
      ⟨hRH,
        xiOrderOne_iff_xiZerosSimple.2
          (xiZerosSimple_iff_hendenmalmSimplicityUniversalCertificate.2
            hsimplicity)⟩

/-- **Kapustin--horizontal--Hedenmalm--bosonic universality law.** Under one symmetric operator
carrying every Kapustin Xi-divisor spectral value, horizontal mass one is equivalent to the full
RH-and-simplicity Hedenmalm certificate together with the unit local factor, unit winding, and all
unit bosonic normalized-jet residues at every Xi zero. -/
theorem kapustin_horizontalHedenmalmBosonicUniversality
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hspec : ∀ ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
      HasEigenvalue T (GaloisForLFunctions.kapustinEigenvalue (ρ : ℂ))) :
    XiHorizontalFibersMultiplicityOne ↔
      XiHedenmalmRHSimplicityUniversalCertificate ∧
        XiUnitHorizontalWindingBosonicFingerprint := by
  constructor
  · intro hhorizontal
    refine ⟨
      xiHorizontalFibersMultiplicityOne_iff_hendenmalmRHSimplicityUniversalCertificate.1
        hhorizontal,
      ?_⟩
    intro ρ hzero
    obtain ⟨R, hR, U, hU, hU0, hfactor, hwinding, hbosonic⟩ :=
      kapustin_symmetricPointSpectrum_horizontalWindingBosonicFingerprint
        T hT hspec hzero
    have hone : xiHorizontalMultiplicity ρ.im = 1 :=
      hhorizontal ρ hzero
    refine ⟨R, hR, U, hU, hU0, ?_, ?_, ?_⟩
    · simpa only [hone] using hfactor
    · simpa only [hone] using hwinding
    · simpa only [hone] using hbosonic
  · rintro ⟨hcertificate, _hfingerprint⟩
    exact
      xiHorizontalFibersMultiplicityOne_iff_hendenmalmRHSimplicityUniversalCertificate.2
        hcertificate

end

end RHTower
