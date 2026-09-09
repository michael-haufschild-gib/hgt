import GaloisForLFunctions.HTGeometry.GomesFockThresholdPOVM
import GaloisForLFunctions.HTGeometry.GomesFockSpectralCoherentWindow

/-! Completeness removes the state-dependent blind spots of individual spectral
windows. A finite threshold bank detects every nonzero vector. Unreferenced
intensities still retain only scalar modulus, whereas three coherent reference
intensities per cell reconstruct the complex scalar. These are concrete tests of
the reconstruction viewpoint in Gomes, arXiv:2607.24901v1, with closed proofs. -/

open scoped Matrix Classical
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- A complete threshold bank is blind only to the zero observing vector. -/
theorem gomesFockThresholdMass_all_zero_iff {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) (x : Fin (d+1) → ℂ) :
    (∀ bits, gomesFockWindowMass B (gomesFockThresholdCell cuts bits) x = 0) ↔ x = 0 := by
  constructor
  · intro h
    apply (gomesFockVector_mass_zero_iff (gomesCompletedFockGenerators B) x).mp
    rw [← gomesFockThresholdMass_sum B cuts x]
    simp only [h,Finset.sum_const_zero]
  · intro hx
    subst x
    have h0 := (gomesFockSpectralMeasure_zero_iff B 0).mpr rfl
    intro bits
    simp [gomesFockWindowMass,h0]

/-- The common kernel of all threshold effects is trivial. -/
theorem gomesFockThresholdEffect_common_kernel_iff {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) (x : Fin (d+1) → ℂ) :
    (∀ bits, gomesFockThresholdEffect B cuts bits *ᵥ x = 0) ↔ x = 0 := by
  simp only [gomesFockThresholdEffect_eq_window,← gomesFockWindowMass_zero_iff_kernel]
  exact gomesFockThresholdMass_all_zero_iff B cuts x

/-- Some threshold cell detects the state exactly when the state is nonzero. -/
theorem gomesFockThresholdMass_detected_iff {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) (x : Fin (d+1) → ℂ) :
    (∃ bits, gomesFockWindowMass B (gomesFockThresholdCell cuts bits) x ≠ 0) ↔ x ≠ 0 := by
  constructor
  · rintro ⟨bits,hbits⟩ hx
    exact hbits ((gomesFockThresholdMass_all_zero_iff B cuts x).mpr hx bits)
  · intro hx
    by_contra h
    apply hx
    apply (gomesFockThresholdMass_all_zero_iff B cuts x).mp
    intro bits
    by_contra hb
    exact h ⟨bits,hb⟩

/-- Three coherent intensities recorded in every cell of the finite measurement. -/
def gomesFockThresholdCoherentMenu {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (x : Fin (d+1) → ℂ) (c : ℂ) : (Fin n → Bool) → ℝ × ℝ × ℝ :=
  fun bits => gomesFockWindowIntensityMenu B (gomesFockThresholdCell cuts bits) x c

/-- The complete coherent menu recovers the complex scalar at every nonzero state. -/
theorem gomesFockThresholdCoherentMenu_reconstruction {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (x : Fin (d+1) → ℂ) (c e : ℂ) :
    gomesFockThresholdCoherentMenu B cuts x c = gomesFockThresholdCoherentMenu B cuts x e ↔
      c = e ∨ x = 0 := by
  constructor
  · intro h
    by_cases hce : c = e
    · exact Or.inl hce
    · right
      apply (gomesFockThresholdMass_all_zero_iff B cuts x).mp
      intro bits
      exact ((gomesFockWindowIntensityMenu_reconstruction B
        (gomesFockThresholdCell cuts bits) x c e).mp (congrFun h bits)).resolve_left hce
  · rintro (hce | hx)
    · rw [hce]
    · funext bits
      apply (gomesFockWindowIntensityMenu_reconstruction B
        (gomesFockThresholdCell cuts bits) x c e).mpr
      exact Or.inr ((gomesFockThresholdMass_all_zero_iff B cuts x).mpr hx bits)

/-- The coherent finite experiment is injective exactly off the zero state. -/
theorem gomesFockThresholdCoherentMenu_injective_iff {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) (x : Fin (d+1) → ℂ) :
    Function.Injective (gomesFockThresholdCoherentMenu B cuts x) ↔ x ≠ 0 := by
  constructor
  · intro hi hx
    exact one_ne_zero (hi ((gomesFockThresholdCoherentMenu_reconstruction B cuts x 1 0).mpr
      (Or.inr hx)))
  · intro hx c e h
    exact ((gomesFockThresholdCoherentMenu_reconstruction B cuts x c e).mp h).resolve_right hx

/-- The same complete experiment without coherent references. -/
def gomesFockThresholdIntensityMenu {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (x : Fin (d+1) → ℂ) (c : ℂ) : (Fin n → Bool) → ℝ :=
  fun bits => gomesFockWindowMass B (gomesFockThresholdCell cuts bits) (c • x)

/-- Completeness alone does not recover scalar phase: unreferenced records retain precisely modulus. -/
theorem gomesFockThresholdIntensityMenu_reconstruction {d k n : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ)
    (x : Fin (d+1) → ℂ) (c e : ℂ) :
    gomesFockThresholdIntensityMenu B cuts x c = gomesFockThresholdIntensityMenu B cuts x e ↔
      Complex.normSq c = Complex.normSq e ∨ x = 0 := by
  constructor
  · intro h
    have hm := congrArg (fun f : (Fin n → Bool) → ℝ => ∑ bits, f bits) h
    change (∑ bits, gomesFockWindowMass B (gomesFockThresholdCell cuts bits) (c • x)) =
      ∑ bits, gomesFockWindowMass B (gomesFockThresholdCell cuts bits) (e • x) at hm
    rw [gomesFockThresholdMass_sum,gomesFockThresholdMass_sum] at hm
    exact (gomesFockScalar_moments_eq_iff (gomesCompletedFockGenerators B) x c e).mp
      ((gomesFockScalar_record_eq_iff_mass_eq (gomesCompletedFockGenerators B) x c e).mpr hm)
  · intro h
    funext bits
    simp only [gomesFockThresholdIntensityMenu,gomesFockWindowMass_smul]
    rcases h with hce | hx
    · rw [hce]
    · rw [(gomesFockThresholdMass_all_zero_iff B cuts x).mpr hx bits]
      simp

end GaloisForLFunctions.HTGeometry
