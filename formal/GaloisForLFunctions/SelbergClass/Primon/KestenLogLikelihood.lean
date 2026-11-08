import GaloisForLFunctions.SelbergClass.Primon.KestenSquareSufficiency

/-!
# Integrable log-likelihood ratios of prime spectral laws

The positive rational beta weights give continuous log-likelihoods on
the spectral interval. Compact support proves integrability. Their
Radon--Nikodym identities identify every prime-to-prime comparison with
a difference of these logarithms, and every semicircle comparison with
one logarithm or its negative.
-/

open MeasureTheory InformationTheory Set Filter

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Every continuous coordinate observable is integrable under each prime law. -/
theorem integrable_kestenSpectralLaw_continuous (p : Nat.Primes) (f : C(ℝ, ℝ)) :
    Integrable f (kestenSpectralLaw p : Measure ℝ) := by
  have hi : IntegrableOn f (Icc (-2 : ℝ) 2) (kestenSpectralLaw p : Measure ℝ) :=
    f.continuous.continuousOn.integrableOn_Icc
  have ha : ∀ᵐ x ∂(kestenSpectralLaw p : Measure ℝ), x ∈ Icc (-2 : ℝ) 2 := by
    rw [ae_iff]
    exact kestenSpectralLaw_carried p
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ha] at hi
  exact hi

/-- Every continuous coordinate observable is integrable under the semicircle law. -/
theorem integrable_semicircleSpectralLaw_continuous (f : C(ℝ, ℝ)) :
    Integrable f (semicircleSpectralLaw : Measure ℝ) := by
  have hi : IntegrableOn f (Icc (-2 : ℝ) 2) (semicircleSpectralLaw : Measure ℝ) :=
    f.continuous.continuousOn.integrableOn_Icc
  have ha : ∀ᵐ x ∂(semicircleSpectralLaw : Measure ℝ), x ∈ Icc (-2 : ℝ) 2 := by
    rw [ae_iff]
    exact semicircleSpectralLaw_carried
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ha] at hi
  exact hi

/-- Logarithm of the prime-to-semicircle likelihood ratio in the Hecke coordinate. -/
def kestenLogLikelihood (p : Nat.Primes) (x : ℝ) : ℝ :=
  Real.log (kestenBetaWeight p (heckeSquareCoordinate x))

/-- The clamped positive density gives a globally continuous log-likelihood. -/
theorem continuous_kestenLogLikelihood (p : Nat.Primes) : Continuous (kestenLogLikelihood p) :=
  ((continuous_kestenBetaWeight p).comp continuous_heckeSquareCoordinate).log
    (fun x => (kestenBetaWeight_pos p (heckeSquareCoordinate x)).ne')

/-- Every prime log-likelihood is integrable under every prime spectral law. -/
theorem integrable_kestenLogLikelihood (p q : Nat.Primes) :
    Integrable (kestenLogLikelihood p) (kestenSpectralLaw q : Measure ℝ) :=
  integrable_kestenSpectralLaw_continuous q ⟨_, continuous_kestenLogLikelihood p⟩

/-- Every prime log-likelihood is integrable under the semicircle law. -/
theorem integrable_semicircleLogLikelihood (p : Nat.Primes) :
    Integrable (kestenLogLikelihood p) (semicircleSpectralLaw : Measure ℝ) :=
  integrable_semicircleSpectralLaw_continuous ⟨_, continuous_kestenLogLikelihood p⟩

/-- Each prime law is absolutely continuous with respect to the semicircle law. -/
theorem kestenSpectralLaw_ac_semicircle (p : Nat.Primes) :
    (kestenSpectralLaw p : Measure ℝ) ≪ (semicircleSpectralLaw : Measure ℝ) := by
  rw [kestenSpectralLaw_eq_semicircle_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- The positive likelihood also makes the semicircle law absolutely continuous with respect to it. -/
theorem semicircleSpectralLaw_ac_kesten (p : Nat.Primes) :
    (semicircleSpectralLaw : Measure ℝ) ≪ (kestenSpectralLaw p : Measure ℝ) := by
  rw [semicircleSpectralLaw_eq_kesten_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- Every two prime spectral laws are mutually absolutely continuous. -/
theorem kestenSpectralLaw_ac_prime (p q : Nat.Primes) :
    (kestenSpectralLaw p : Measure ℝ) ≪ (kestenSpectralLaw q : Measure ℝ) := by
  rw [kestenSpectralLaw_eq_prime_withDensity p q]
  exact withDensity_absolutelyContinuous _ _

/-- The actual prime-to-semicircle log-likelihood is the continuous rational-weight logarithm. -/
theorem llr_kesten_semicircle (p : Nat.Primes) :
    llr (kestenSpectralLaw p : Measure ℝ) (semicircleSpectralLaw : Measure ℝ) =ᵐ[
      (kestenSpectralLaw p : Measure ℝ)] kestenLogLikelihood p := by
  have hr : (kestenSpectralLaw p : Measure ℝ).rnDeriv (semicircleSpectralLaw : Measure ℝ) =ᵐ[
      (semicircleSpectralLaw : Measure ℝ)]
      (fun u => ENNReal.ofReal (kestenBetaWeight p u)) ∘ heckeSquareCoordinate := by
    rw [kestenSpectralLaw_eq_semicircle_withDensity]
    exact Measure.rnDeriv_withDensity _
      ((continuous_kestenBetaWeight p).measurable.ennreal_ofReal.comp
        continuous_heckeSquareCoordinate.measurable)
  filter_upwards [(kestenSpectralLaw_ac_semicircle p).ae_le hr] with x hx
  rw [llr, hx]
  change Real.log (ENNReal.ofReal (kestenBetaWeight p (heckeSquareCoordinate x))).toReal = _
  rw [ENNReal.toReal_ofReal (kestenBetaWeight_pos p _).le]
  rfl

/-- Reversing the prime-to-semicircle comparison negates its log-likelihood. -/
theorem llr_semicircle_kesten (p : Nat.Primes) :
    llr (semicircleSpectralLaw : Measure ℝ) (kestenSpectralLaw p : Measure ℝ) =ᵐ[
      (semicircleSpectralLaw : Measure ℝ)] fun x => -kestenLogLikelihood p x := by
  have hm : Measurable (fun u : ℝ => ENNReal.ofReal ((kestenBetaWeight p u)⁻¹)) :=
    (continuous_kestenBetaWeight p).measurable.inv.ennreal_ofReal
  have hr : (semicircleSpectralLaw : Measure ℝ).rnDeriv (kestenSpectralLaw p : Measure ℝ) =ᵐ[
      (kestenSpectralLaw p : Measure ℝ)]
      (fun u => ENNReal.ofReal ((kestenBetaWeight p u)⁻¹)) ∘ heckeSquareCoordinate := by
    rw [semicircleSpectralLaw_eq_kesten_withDensity]
    exact Measure.rnDeriv_withDensity _ (hm.comp continuous_heckeSquareCoordinate.measurable)
  filter_upwards [(semicircleSpectralLaw_ac_kesten p).ae_le hr] with x hx
  rw [llr, hx]
  change Real.log (ENNReal.ofReal ((kestenBetaWeight p (heckeSquareCoordinate x))⁻¹)).toReal = _
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (kestenBetaWeight_pos p _).le), Real.log_inv]
  rfl

/-- Every prime-to-prime log-likelihood is the difference of two integrable rational-weight logs. -/
theorem llr_kesten_prime (p q : Nat.Primes) :
    llr (kestenSpectralLaw p : Measure ℝ) (kestenSpectralLaw q : Measure ℝ) =ᵐ[
      (kestenSpectralLaw p : Measure ℝ)] fun x => kestenLogLikelihood p x - kestenLogLikelihood q x := by
  have hm : Measurable (fun u : ℝ =>
      ENNReal.ofReal (kestenBetaWeight p u / kestenBetaWeight q u)) :=
    ((continuous_kestenBetaWeight p).measurable.div (continuous_kestenBetaWeight q).measurable).ennreal_ofReal
  have hr : (kestenSpectralLaw p : Measure ℝ).rnDeriv (kestenSpectralLaw q : Measure ℝ) =ᵐ[
      (kestenSpectralLaw q : Measure ℝ)]
      (fun u => ENNReal.ofReal (kestenBetaWeight p u / kestenBetaWeight q u)) ∘
        heckeSquareCoordinate := by
    rw [kestenSpectralLaw_eq_prime_withDensity p q]
    exact Measure.rnDeriv_withDensity _ (hm.comp continuous_heckeSquareCoordinate.measurable)
  filter_upwards [(kestenSpectralLaw_ac_prime p q).ae_le hr] with x hx
  rw [llr, hx]
  change Real.log (ENNReal.ofReal (kestenBetaWeight p (heckeSquareCoordinate x) /
    kestenBetaWeight q (heckeSquareCoordinate x))).toReal = _
  rw [ENNReal.toReal_ofReal (div_nonneg (kestenBetaWeight_pos p _).le (kestenBetaWeight_pos q _).le),
    Real.log_div (kestenBetaWeight_pos p _).ne' (kestenBetaWeight_pos q _).ne']
  rfl

end
end GaloisForLFunctions.SelbergClass.Primon
