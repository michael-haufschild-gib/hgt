import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGamma

/-!
# Exact real-exponent spectrum of infinite nome occupations

The occupation lift preserves every positive real summability exponent, not merely integer
canonical-product genera.  This is the sharp spectral threshold underlying the infinite-order
multiple elliptic gamma construction.
-/

namespace HTGeometry

open scoped BigOperators ENNReal NNReal

theorem occupationWeight_nomeRpow {ι : Type*}
    (σ : ℝ) (p : ι → ℂ) (ν : ι →₀ ℕ) :
    occupationWeight
        (fun a => ((‖p a‖₊ ^ σ : NNReal) : ℝ≥0∞)) ν =
      ((‖nomeMonomial p ν‖₊ ^ σ : NNReal) : ℝ≥0∞) := by
  classical
  rw [occupationWeight, Finsupp.prod]
  simp_rw [← ENNReal.coe_pow]
  rw [← ENNReal.ofNNReal_finsetProd]
  congr 1
  rw [nnnorm_nomeMonomial, Finsupp.prod]
  rw [← NNReal.finsetProd_rpow]
  apply Finset.prod_congr rfl
  intro a _
  rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
  rw [mul_comm, NNReal.rpow_mul, NNReal.rpow_natCast]

theorem nomeOccupationMass_rpow_eq_iSup_finset {ι : Type*}
    (σ : ℝ) (p : ι → ℂ) :
    (∑' ν : ι →₀ ℕ,
        ((‖nomeMonomial p ν‖₊ ^ σ : NNReal) : ℝ≥0∞)) =
      ⨆ S : Finset ι,
        ∏ a ∈ S,
          (1 - ((‖p a‖₊ ^ σ : NNReal) : ℝ≥0∞))⁻¹ := by
  let u : ι → NNReal := fun a => ‖p a‖₊ ^ σ
  rw [show
      (∑' ν : ι →₀ ℕ,
          ((‖nomeMonomial p ν‖₊ ^ σ : NNReal) : ℝ≥0∞)) =
        ∑' ν : ι →₀ ℕ,
          occupationWeight (fun a => (u a : ℝ≥0∞)) ν by
    apply tsum_congr
    intro ν
    rw [occupationWeight_nomeRpow]]
  exact occupationMass_eq_iSup_finset (fun a => (u a : ℝ≥0∞))

theorem summable_nomeMonomial_rpow_iff {ι : Type*}
    (σ : ℝ) (hσ : 0 < σ) (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1) :
    Summable (fun ν : ι →₀ ℕ => ‖nomeMonomial p ν‖ ^ σ) ↔
      Summable (fun a => ‖p a‖ ^ σ) := by
  let u : ι → NNReal := fun a => ‖p a‖₊ ^ σ
  have hu_lt : ∀ a, u a < 1 := by
    intro a
    exact NNReal.rpow_lt_one (by exact_mod_cast hp_lt a) hσ
  simpa only [NNReal.coe_rpow, coe_nnnorm, u] using
    (show
      Summable (fun ν : ι →₀ ℕ => ((‖nomeMonomial p ν‖₊ ^ σ : NNReal) : ℝ)) ↔
        Summable (fun a => ((u a : NNReal) : ℝ)) by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
      rw [show
          (∑' ν : ι →₀ ℕ,
              ((‖nomeMonomial p ν‖₊ ^ σ : NNReal) : ℝ≥0∞)) =
            ∑' ν : ι →₀ ℕ,
              occupationWeight (fun a => (u a : ℝ≥0∞)) ν by
        apply tsum_congr
        intro ν
        rw [occupationWeight_nomeRpow]]
      exact occupationMass_ne_top_iff u hu_lt)

/-- The positive real summability spectrum is unchanged by passing from nomes to all finite
occupations. -/
theorem nomeOccupationSummabilitySpectrum_eq {ι : Type*}
    (p : ι → ℂ) (hp_lt : ∀ a, ‖p a‖ < 1) :
    {σ : ℝ | 0 < σ ∧
        Summable (fun ν : ι →₀ ℕ => ‖nomeMonomial p ν‖ ^ σ)} =
      {σ : ℝ | 0 < σ ∧ Summable (fun a => ‖p a‖ ^ σ)} := by
  ext σ
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hσ, hsum⟩
    exact ⟨hσ, (summable_nomeMonomial_rpow_iff σ hσ p hp_lt).1 hsum⟩
  · rintro ⟨hσ, hsum⟩
    exact ⟨hσ, (summable_nomeMonomial_rpow_iff σ hσ p hp_lt).2 hsum⟩

/-- Once a nonzero nome family is summable at one positive exponent, it is summable at every
larger exponent. -/
theorem summable_nome_rpow_mono {ι : Type*}
    (p : ι → ℂ) (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    {σ τ : ℝ} (hστ : σ ≤ τ)
    (hsum : Summable (fun a => ‖p a‖ ^ σ)) :
    Summable (fun a => ‖p a‖ ^ τ) := by
  apply hsum.of_nonneg_of_le
  · intro a
    positivity
  · intro a
    exact Real.rpow_le_rpow_of_exponent_ge
      (norm_pos_iff.mpr (hp_ne a)) (le_of_lt (hp_lt a)) hστ

/-- The occupation summability spectrum is upward closed. -/
theorem summable_nomeMonomial_rpow_mono {ι : Type*}
    (p : ι → ℂ) (hp_ne : ∀ a, p a ≠ 0) (hp_lt : ∀ a, ‖p a‖ < 1)
    {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (hστ : σ ≤ τ)
    (hsum : Summable (fun ν : ι →₀ ℕ => ‖nomeMonomial p ν‖ ^ σ)) :
    Summable (fun ν : ι →₀ ℕ => ‖nomeMonomial p ν‖ ^ τ) := by
  apply (summable_nomeMonomial_rpow_iff τ hτ p hp_lt).2
  apply summable_nome_rpow_mono p hp_ne hp_lt hστ
  exact (summable_nomeMonomial_rpow_iff σ hσ p hp_lt).1 hsum

end HTGeometry
