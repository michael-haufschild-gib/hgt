import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaRealSpectrum

/-!
# Statistics-independent occupation criticality

An occupation sector may impose arbitrary local or global restrictions on finitely supported
occupation vectors.  If it retains every one-particle state, then its total positive weight is
finite exactly when the one-particle weight is summable.  Thus every such sector has the same
positive-exponent summability spectrum as both the one-particle family and the full bosonic sector.
-/

namespace HTGeometry

open scoped ENNReal

/-- Total weight of an arbitrary sector of finitely supported occupations. -/
noncomputable def restrictedOccupationMass {ι : Type*}
    (u : ι → ℝ≥0∞) (Ω : Set (ι →₀ ℕ)) : ℝ≥0∞ :=
  ∑' ν : Ω, occupationWeight u ν.1

/-- The one-particle sector is a lower bound for every sector retaining all one-particle states. -/
theorem nome_tsum_le_restrictedOccupationMass {ι : Type*}
    (u : ι → ℝ≥0∞) (Ω : Set (ι →₀ ℕ))
    (hΩ : ∀ a, Finsupp.single a 1 ∈ Ω) :
    ∑' a, u a ≤ restrictedOccupationMass u Ω := by
  let e : ι ↪ Ω :=
    ⟨fun a => ⟨Finsupp.single a 1, hΩ a⟩, fun a b hab =>
      Finsupp.single_left_injective one_ne_zero (congrArg Subtype.val hab)⟩
  calc
    ∑' a, u a = ∑' a, occupationWeight u (e a).1 := by
      apply tsum_congr
      intro a
      exact (occupationWeight_single u a).symm
    _ ≤ ∑' ν : Ω, occupationWeight u ν.1 :=
      ENNReal.tsum_comp_le_tsum_of_injective e.injective _
    _ = restrictedOccupationMass u Ω := rfl

/-- Every restricted sector is bounded above by the full bosonic occupation space. -/
theorem restrictedOccupationMass_le_occupationMass {ι : Type*}
    (u : ι → ℝ≥0∞) (Ω : Set (ι →₀ ℕ)) :
    restrictedOccupationMass u Ω ≤
      ∑' ν : ι →₀ ℕ, occupationWeight u ν := by
  exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _

/-- **Statistics-independent threshold law.**  Any occupation sector containing every one-particle
state is finite exactly at the one-particle summability threshold. -/
theorem restrictedOccupationMass_ne_top_iff {ι : Type*}
    (u : ι → NNReal) (hu_lt : ∀ a, u a < 1)
    (Ω : Set (ι →₀ ℕ)) (hΩ : ∀ a, Finsupp.single a 1 ∈ Ω) :
    restrictedOccupationMass (fun a => (u a : ℝ≥0∞)) Ω ≠ ∞ ↔
      Summable (fun a => (u a : ℝ)) := by
  constructor
  · intro hmass
    apply ENNReal.tsum_coe_ne_top_iff_summable_coe.mp
    exact ne_top_of_le_ne_top hmass
      (nome_tsum_le_restrictedOccupationMass
        (fun a => (u a : ℝ≥0∞)) Ω hΩ)
  · intro hu
    have hfull :=
      (occupationMass_ne_top_iff u hu_lt).2 hu
    exact ne_top_of_le_ne_top hfull
      (restrictedOccupationMass_le_occupationMass
        (fun a => (u a : ℝ≥0∞)) Ω)

/-- Every admissible occupation statistics has the same real-power summability threshold as its
nome family.  No factorization, locality, countability, or permutation invariance of the sector is
assumed. -/
theorem summable_restricted_nomeMonomial_rpow_iff {ι : Type*}
    (σ : ℝ) (hσ : 0 < σ) (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1)
    (Ω : Set (ι →₀ ℕ)) (hΩ : ∀ a, Finsupp.single a 1 ∈ Ω) :
    Summable (fun ν : Ω => ‖nomeMonomial p ν.1‖ ^ σ) ↔
      Summable (fun a => ‖p a‖ ^ σ) := by
  let u : ι → NNReal := fun a => ‖p a‖₊ ^ σ
  have hu_lt : ∀ a, u a < 1 := by
    intro a
    exact NNReal.rpow_lt_one (by exact_mod_cast hp_lt a) hσ
  simpa only [NNReal.coe_rpow, coe_nnnorm, u] using
    (show
      Summable
          (fun ν : Ω =>
            ((‖nomeMonomial p ν.1‖₊ ^ σ : NNReal) : ℝ)) ↔
        Summable (fun a => ((u a : NNReal) : ℝ)) by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
      rw [show
          (∑' ν : Ω,
              ((‖nomeMonomial p ν.1‖₊ ^ σ : NNReal) : ℝ≥0∞)) =
            restrictedOccupationMass
              (fun a => (u a : ℝ≥0∞)) Ω by
        apply tsum_congr
        intro ν
        simpa [u] using (occupationWeight_nomeRpow σ p ν.1).symm]
      exact restrictedOccupationMass_ne_top_iff u hu_lt Ω hΩ)

/-- The positive real summability spectrum is invariant under every occupation restriction that
retains the one-particle sector. -/
theorem restrictedOccupationSummabilitySpectrum_eq {ι : Type*}
    (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1)
    (Ω : Set (ι →₀ ℕ)) (hΩ : ∀ a, Finsupp.single a 1 ∈ Ω) :
    {σ : ℝ | 0 < σ ∧
        Summable (fun ν : Ω => ‖nomeMonomial p ν.1‖ ^ σ)} =
      {σ : ℝ | 0 < σ ∧ Summable (fun a => ‖p a‖ ^ σ)} := by
  ext σ
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hσ, hsum⟩
    exact ⟨hσ,
      (summable_restricted_nomeMonomial_rpow_iff
        σ hσ p hp_lt Ω hΩ).1 hsum⟩
  · rintro ⟨hσ, hsum⟩
    exact ⟨hσ,
      (summable_restricted_nomeMonomial_rpow_iff
        σ hσ p hp_lt Ω hΩ).2 hsum⟩

/-- Canonical determinant attached to an arbitrary restricted occupation sector. -/
noncomputable def restrictedOccupationCanonicalProduct {ι : Type*}
    (g : ℕ) (p : ι → ℂ) (Ω : Set (ι →₀ ℕ)) : ℂ → ℂ :=
  canonicalWeightProduct g (fun ν : Ω => nomeMonomial p ν.1)

theorem restrictedOccupationCanonicalProduct_hasProdLocallyUniformlyOn {ι : Type*}
    (g : ℕ) (p : ι → ℂ) (Ω : Set (ι →₀ ℕ))
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) :
    HasProdLocallyUniformlyOn
      (fun ν : Ω => fun x =>
        primaryFactor g (x * nomeMonomial p ν.1))
      (restrictedOccupationCanonicalProduct g p Ω) Set.univ := by
  have hfull :
      Summable (fun ν : ι →₀ ℕ =>
        ‖nomeMonomial p ν‖ ^ (g + 1)) :=
    (summable_nomeMonomial_pow_iff g p hp_lt).2 hsum
  have hrestricted :
      Summable (fun ν : Ω =>
        ‖nomeMonomial p ν.1‖ ^ (g + 1)) := by
    simpa [Function.comp_def] using
      hfull.comp_injective Subtype.val_injective
  exact canonicalWeightProduct_hasProdLocallyUniformlyOn
    g (fun ν : Ω => nomeMonomial p ν.1)
    (fun ν => nomeMonomial_ne_zero p hp_ne ν.1) hrestricted

/-- Every occupation restriction has an entire canonical determinant at every admissible genus. -/
theorem restrictedOccupationCanonicalProduct_analytic {ι : Type*}
    (g : ℕ) (p : ι → ℂ) (Ω : Set (ι →₀ ℕ))
    (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) :
    AnalyticOnNhd ℂ (restrictedOccupationCanonicalProduct g p Ω) Set.univ := by
  have hfull :
      Summable (fun ν : ι →₀ ℕ =>
        ‖nomeMonomial p ν‖ ^ (g + 1)) :=
    (summable_nomeMonomial_pow_iff g p hp_lt).2 hsum
  have hrestricted :
      Summable (fun ν : Ω =>
        ‖nomeMonomial p ν.1‖ ^ (g + 1)) := by
    simpa [Function.comp_def] using
      hfull.comp_injective Subtype.val_injective
  exact canonicalWeightProduct_analytic
    g (fun ν : Ω => nomeMonomial p ν.1)
    (fun ν => nomeMonomial_ne_zero p hp_ne ν.1) hrestricted

end HTGeometry
