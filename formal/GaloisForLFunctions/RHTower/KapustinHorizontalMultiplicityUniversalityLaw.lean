import GaloisForLFunctions.RHTower.HorizontalSingletonZeroFiber
import GaloisForLFunctions.RHTower.KapustinHilbertEndpoint
import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import GaloisForLFunctions.RHTower.WindingXi
import GaloisForLFunctions.HTGeometry.MultipleZeroBosonicHorizon

/-!
# Kapustin horizontal-multiplicity universality law

A Hilbert-symmetric realization of every Kapustin Xi-divisor spectral point does more than force
critical-line location.  It makes each exact-height Xi-zero fiber equal, with multiplicity, to the
single local divisor point that generated the spectral value.
-/

open Complex
open Module.End

namespace RHTower

noncomputable section

/-- **Kapustin horizontal-multiplicity universality law.**  Any Hilbert-symmetric operator carrying
all Kapustin Xi-divisor eigenvalues identifies the total horizontal divisor mass through every Xi
zero with that zero's analytic order. -/
theorem kapustin_symmetricPointSpectrum_horizontalMultiplicity_eq_order
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hspec : ∀ ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
      HasEigenvalue T (GaloisForLFunctions.kapustinEigenvalue (ρ : ℂ)))
    {ρ : ℂ} (hzero : xi ρ = 0) :
    xiHorizontalMultiplicity ρ.im = (analyticOrderAt xi ρ).toNat := by
  classical
  have hRH := riemannHypothesis_of_kapustin_symmetric_pointSpectrum T hT hspec
  have hstrip := xi_zero_re_mem_open_unit hzero
  have hρmem : ρ ∈ stripHeightFinset ρ.im := by
    rw [mem_stripHeightFinset]
    exact ⟨hstrip.1, hstrip.2, rfl, hzero⟩
  rw [xiHorizontalMultiplicity, Finset.sum_eq_single ρ]
  · intro z hz hzne
    have hzdata := mem_stripHeightFinset.mp hz
    have hzline := xi_zero_re_eq_half_of_RH hRH hzdata.2.2.2
    have hρline := xi_zero_re_eq_half_of_RH hRH hzero
    have hzr : z = ρ := by
      apply Complex.ext
      · rw [hzline, hρline]
      · exact hzdata.2.2.1
    exact (hzne hzr).elim
  · intro hρnot
    exact (hρnot hρmem).elim

/-- Under the same spectral realization, horizontal multiplicity one is equivalent to analytic
simplicity of every Xi zero; the location half of the general law has been discharged by operator
symmetry. -/
theorem kapustin_symmetricPointSpectrum_horizontalMultiplicityOne_iff_orderOne
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hspec : ∀ ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
      HasEigenvalue T (GaloisForLFunctions.kapustinEigenvalue (ρ : ℂ))) :
    (∀ ρ : ℂ, xi ρ = 0 → xiHorizontalMultiplicity ρ.im = 1) ↔
      ∀ ρ : ℂ, xi ρ = 0 → (analyticOrderAt xi ρ).toNat = 1 := by
  constructor <;> intro h ρ hzero
  · rw [← kapustin_symmetricPointSpectrum_horizontalMultiplicity_eq_order T hT hspec hzero]
    exact h ρ hzero
  · rw [kapustin_symmetricPointSpectrum_horizontalMultiplicity_eq_order T hT hspec hzero]
    exact h ρ hzero

/-- The Hilbert spectral realization, horizontal divisor census, local winding, and every bosonic
normalized-jet residue all read the same integer. -/
theorem kapustin_symmetricPointSpectrum_horizontalWindingBosonicFingerprint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hspec : ∀ ρ : ↥(MeromorphicOn.divisor xi Set.univ).support,
      HasEigenvalue T (GaloisForLFunctions.kapustinEigenvalue (ρ : ℂ)))
    {ρ : ℂ} (hzero : xi ρ = 0) :
    ∃ R : ℝ, 0 < R ∧ ∃ U : ℂ → ℂ,
      AnalyticAt ℂ U 0 ∧ U 0 ≠ 0 ∧
      (∀ z ∈ Metric.ball 0 R,
        xi (ρ + z) = GaloisForLFunctions.multipleZeroSection
          (xiHorizontalMultiplicity ρ.im) U z) ∧
      (∀ r : ℝ, 0 < r → r < R →
        windingNumber (fun θ => xi (ρ + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi) =
          (xiHorizontalMultiplicity ρ.im : ℤ)) ∧
      ∀ k : ℕ, k ≤ xiHorizontalMultiplicity ρ.im →
        Filter.Tendsto
          (fun z : ℂ => z ^ k *
            (iteratedDeriv k
                (GaloisForLFunctions.multipleZeroSection
                  (xiHorizontalMultiplicity ρ.im) U) z /
              GaloisForLFunctions.multipleZeroSection
                (xiHorizontalMultiplicity ρ.im) U z))
          (nhdsWithin 0 {0}ᶜ)
          (nhds (xiHorizontalMultiplicity ρ.im |>.descFactorial k : ℂ)) := by
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
  have hm := kapustin_symmetricPointSpectrum_horizontalMultiplicity_eq_order
    T hT hspec hzero
  refine ⟨R, hR, U, hU, hU0, ?_, ?_, ?_⟩
  · intro z hz
    have hzR : ρ + z ∈ Metric.ball ρ R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hzRp : ρ + z ∈ Metric.ball ρ Rp :=
      Metric.ball_subset_ball (min_le_left Rp Rw) hzR
    have hf := hfact (ρ + z) hzRp
    rw [← hm] at hf
    simpa [GaloisForLFunctions.multipleZeroSection, U] using hf
  · intro r hr hrR
    have hrRw : r < Rw := hrR.trans_le (min_le_right Rp Rw)
    simpa [hm] using hwind r hr hrRw
  · intro k hk
    exact GaloisForLFunctions.tendsto_scaled_multipleZeroCorrelator_descFactorial
      (xiHorizontalMultiplicity ρ.im) k hk hU hU0

end

end RHTower
