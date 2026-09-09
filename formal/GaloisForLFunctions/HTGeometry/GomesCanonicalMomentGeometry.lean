import GaloisForLFunctions.HTGeometry.GomesMomentFluxReconstruction

/-!
Canonical coverage of every positive moment sequence and recovery from tensor data.
This applies the scalar-versus-tensor observation viewpoint of Gomes,
arXiv:2404.10461 and arXiv:2509.25276v7, to the corpus moment-frame geometry.
The single flux probe restores the mass invisible to monic Jacobi frames.
These are corpus applications, not transcriptions of numbered paper results.
-/

open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- Canonical data-only model extracted from any real moment sequence. -/
def gomesCanonicalMomentModel (s : ℕ → ℝ) : GomesMomentModel :=
  .favard (Real.log (s 0)) (monicOrthoAlpha s) (fun n => Real.log (monicOrthoBeta s (n+1)))

/-- The canonical model represents its input exactly if and only if that input is a positive moment form. -/
theorem gomesCanonicalMomentModel_moments_iff (s : ℕ → ℝ) :
    (gomesCanonicalMomentModel s).moments = s ↔ PositiveMomentForm s := by
  change gomesFavardMoment (Real.log (s 0)) (monicOrthoAlpha s)
    (fun n => Real.log (monicOrthoBeta s (n+1))) = s ↔ _
  rw [eq_comm]
  exact gomesFavard_canonical_reconstruction_iff s

/-- The data-only model interface covers exactly all positive moment sequences. -/
theorem gomesMomentModel_exists_iff (s : ℕ → ℝ) :
    (∃ M : GomesMomentModel, M.moments = s) ↔ PositiveMomentForm s := by
  constructor
  · rintro ⟨M,hm⟩
    rw [← hm]
    exact gomesMomentModel_positive M
  · intro h
    exact ⟨gomesCanonicalMomentModel s,(gomesCanonicalMomentModel_moments_iff s).mpr h⟩

/-- Canonical reconstruction preserves the exact underlying source of every concrete model. -/
theorem gomesCanonicalMomentModel_recovery (M : GomesMomentModel) :
    (gomesCanonicalMomentModel M.moments).moments = M.moments :=
  (gomesCanonicalMomentModel_moments_iff M.moments).mpr (gomesMomentModel_positive M)

/-- Mass plus the full Jacobi coefficient menu determines every positive moment source faithfully. -/
theorem gomesMomentModel_jacobi_reconstruction (M N : GomesMomentModel) :
    M.moments = N.moments ↔ M.moments 0 = N.moments 0 ∧
      (∀ n, monicOrthoAlpha M.moments n = monicOrthoAlpha N.moments n) ∧
      (∀ n, monicOrthoBeta M.moments (n+1) = monicOrthoBeta N.moments (n+1)) := by
  constructor
  · intro h
    rw [h]
    simp
  · rintro ⟨hm,ha,hb⟩
    have hM := (gomesFavard_canonical_reconstruction_iff M.moments).mpr (gomesMomentModel_positive M)
    have hN := (gomesFavard_canonical_reconstruction_iff N.moments).mpr (gomesMomentModel_positive N)
    calc
      M.moments = _ := hM
      _ = gomesFavardMoment (Real.log (N.moments 0)) (monicOrthoAlpha N.moments)
          (fun n => Real.log (monicOrthoBeta N.moments (n+1))) := by
        rw [hm]
        congr 1
        · exact funext ha
        · funext n
          exact congrArg Real.log (hb n)
      _ = N.moments := hN.symm

/-- Canonical data preserve every full complex recurrence frame. -/
theorem gomesCanonicalMomentModel_frame_recovery (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    gomesMomentComplexFrame (gomesCanonicalMomentModel M.moments) n z = gomesMomentComplexFrame M n z := by
  simp only [gomesMomentComplexFrame,gomesCanonicalMomentModel_recovery]

/-- Canonical data preserve every projective quotient. -/
theorem gomesCanonicalMomentModel_quotient_recovery (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    gomesMomentQuotient (gomesCanonicalMomentModel M.moments) n z = gomesMomentQuotient M n z := by
  simp only [gomesMomentQuotient,gomesCanonicalMomentModel_recovery]

/-- Canonical data preserve the complete weighted observation tensor. -/
theorem gomesCanonicalMomentModel_gram_recovery (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    gomesMomentObservationGram (gomesCanonicalMomentModel M.moments) n z = gomesMomentObservationGram M n z := by
  simp only [gomesMomentObservationGram,gomesCanonicalMomentModel_recovery]

/-- Canonical data preserve the entire normalized flux tensor. -/
theorem gomesCanonicalMomentModel_flux_recovery (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    gomesMomentNormalizedFlux (gomesCanonicalMomentModel M.moments) n z = gomesMomentNormalizedFlux M n z := by
  simp only [gomesMomentNormalizedFlux,gomesCanonicalMomentModel_frame_recovery,gomesCanonicalMomentModel_recovery]

/-- One fixed nonreal flux observation directly measures the reciprocal initial mass. -/
theorem gomesMomentNormalizedFlux_mass_probe (M : GomesMomentModel) :
    gomesMomentNormalizedFlux M 0 Complex.I 0 0 = ((2/M.moments 0 : ℝ) : ℂ) := by
  have h := gomesMomentNormalizedFlux_quadratic M 0 Complex.I ![1,0]
  simpa [div_eq_mul_inv,Matrix.mulVec,dotProduct,Fin.sum_univ_two,gomesMomentWaveEnergy,gomesMomentWave_zero,
    momentInner_def,momentFunctional_one] using h

/-- A single flux tensor probe restores exactly the mass missing from the Jacobi menu. -/
theorem gomesMomentModel_tensor_reconstruction (M N : GomesMomentModel) :
    M.moments = N.moments ↔
      (∀ n, monicOrthoAlpha M.moments n = monicOrthoAlpha N.moments n) ∧
      (∀ n, monicOrthoBeta M.moments (n+1) = monicOrthoBeta N.moments (n+1)) ∧
      gomesMomentNormalizedFlux M 0 Complex.I 0 0 = gomesMomentNormalizedFlux N 0 Complex.I 0 0 := by
  constructor
  · intro h
    rw [gomesMomentNormalizedFlux_mass_probe,gomesMomentNormalizedFlux_mass_probe,h]
    simp
  · rintro ⟨ha,hb,hp⟩
    rw [gomesMomentNormalizedFlux_mass_probe,gomesMomentNormalizedFlux_mass_probe] at hp
    have hr := Complex.ofReal_injective hp
    have hm0 : M.moments 0 ≠ 0 := by
      have h := (gomesMomentModel_norm_pos M 0).ne'
      simpa [momentInner_def,momentFunctional_one] using h
    have hn0 : N.moments 0 ≠ 0 := by
      have h := (gomesMomentModel_norm_pos N 0).ne'
      simpa [momentInner_def,momentFunctional_one] using h
    field_simp [hm0,hn0] at hr
    apply (gomesMomentModel_jacobi_reconstruction M N).mpr
    exact ⟨by linarith,ha,hb⟩

end GaloisForLFunctions.HTGeometry
