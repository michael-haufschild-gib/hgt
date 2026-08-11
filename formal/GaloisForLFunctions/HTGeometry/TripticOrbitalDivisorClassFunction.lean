import GaloisForLFunctions.HTGeometry.TripticOrbitalDivisorLinearity
import GaloisForLFunctions.HTGeometry.TripticBoundaryPoleClasses

/-!
# The orbital divisor is a class function

Moving the base point along the orbit reindexes the unrestricted sum, and moving it by `1` or by `τ`
moves no negative Laurent coefficient of the boundary function of a mixed-constraint source.  So the
orbital divisor depends only on the class of the base point in `ℂ / (ℤ + ℤτ + ℤσ)`.

This is what lets a correction be prescribed one class at a time: the value to be cancelled is
attached to the class, not to a representative.

* `additiveOrbitalDivisorAt_shift_sigma`, `..._shift_one`, `..._shift_tau`;
* `additiveOrbitalDivisorAt_classFunction`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Moving the base point along its own orbit reindexes the sum. -/
theorem additiveOrbitalDivisorAt_shift_sigma (F : ℂ → ℂ) (σ p : ℂ) (ℓ : ℤ) (k : ℤ) :
    additiveOrbitalDivisorAt F σ (p + (k : ℂ) * σ) ℓ = additiveOrbitalDivisorAt F σ p ℓ := by
  have hre : ∀ m : ℤ,
      laurentCoeff (fun z ↦ F (z + σ) - F z) (p + (k : ℂ) * σ + (m : ℂ) * σ) ℓ
        = laurentCoeff (fun z ↦ F (z + σ) - F z) (p + ((m + k : ℤ) : ℂ) * σ) ℓ := by
    intro m
    congr 1
    push_cast
    ring
  rw [additiveOrbitalDivisorAt, additiveOrbitalDivisorAt, finsum_congr hre]
  exact finsum_comp_equiv (Equiv.addRight k)
    (f := fun m : ℤ ↦ laurentCoeff (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ)

/-- Moving the base point by an integer moves no coefficient of the boundary function. -/
theorem additiveOrbitalDivisorAt_shift_one {F : ℂ → ℂ} {σ : ℂ}
    (hF : MeromorphicOn F (Set.univ : Set ℂ)) (hper : PeriodicOneGerm F)
    (p : ℂ) {ℓ : ℤ} (hℓ : ℓ < 0) (k : ℤ) :
    additiveOrbitalDivisorAt F σ (p + (k : ℂ) * 1) ℓ = additiveOrbitalDivisorAt F σ p ℓ := by
  have hinv : ∀ ℓ' : ℤ, ℓ' < 0 → ∀ z : ℂ,
      laurentCoeff (fun w ↦ F (w + σ) - F w) (z + 1) ℓ'
        = laurentCoeff (fun w ↦ F (w + σ) - F w) z ℓ' :=
    fun ℓ' _ z ↦ laurentCoeff_boundary_periodic_one hF hper ℓ' z
  have hterm : ∀ m : ℤ,
      laurentCoeff (fun z ↦ F (z + σ) - F z) (p + (k : ℂ) * 1 + (m : ℂ) * σ) ℓ
        = laurentCoeff (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ := by
    intro m
    have hpt : p + (k : ℂ) * 1 + (m : ℂ) * σ = (p + (m : ℂ) * σ) + (k : ℂ) * 1 := by ring
    rw [hpt]
    exact laurentCoeff_invariant_zsmul hinv k hℓ _
  rw [additiveOrbitalDivisorAt, additiveOrbitalDivisorAt, finsum_congr hterm]

/-- Moving the base point by a `τ`-step moves no negative coefficient of the boundary function. -/
theorem additiveOrbitalDivisorAt_shift_tau {F : ℂ → ℂ} {τ σ : ℂ}
    (hF : MeromorphicOn F (Set.univ : Set ℂ))
    {Cst : ℂ} (hmixed : MixedConstGerm F τ σ Cst)
    (p : ℂ) {ℓ : ℤ} (hℓ : ℓ < 0) (k : ℤ) :
    additiveOrbitalDivisorAt F σ (p + (k : ℂ) * τ) ℓ = additiveOrbitalDivisorAt F σ p ℓ := by
  have hinv : ∀ ℓ' : ℤ, ℓ' < 0 → ∀ z : ℂ,
      laurentCoeff (fun w ↦ F (w + σ) - F w) (z + τ) ℓ'
        = laurentCoeff (fun w ↦ F (w + σ) - F w) z ℓ' :=
    fun ℓ' hℓ' z ↦ laurentCoeff_boundary_periodic_tau hF hmixed hℓ' z
  have hterm : ∀ m : ℤ,
      laurentCoeff (fun z ↦ F (z + σ) - F z) (p + (k : ℂ) * τ + (m : ℂ) * σ) ℓ
        = laurentCoeff (fun z ↦ F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ := by
    intro m
    have hpt : p + (k : ℂ) * τ + (m : ℂ) * σ = (p + (m : ℂ) * σ) + (k : ℂ) * τ := by ring
    rw [hpt]
    exact laurentCoeff_invariant_zsmul hinv k hℓ _
  rw [additiveOrbitalDivisorAt, additiveOrbitalDivisorAt, finsum_congr hterm]

/-- **The orbital divisor is a class function on `ℂ / (ℤ + ℤτ + ℤσ)`.** -/
theorem additiveOrbitalDivisorAt_classFunction {F : ℂ → ℂ} {τ σ : ℂ}
    (hF : MeromorphicOn F (Set.univ : Set ℂ)) (hper : PeriodicOneGerm F)
    {Cst : ℂ} (hmixed : MixedConstGerm F τ σ Cst)
    (p : ℂ) {ℓ : ℤ} (hℓ : ℓ < 0) (u v k : ℤ) :
    additiveOrbitalDivisorAt F σ (p + (u : ℂ) * 1 + (v : ℂ) * τ + (k : ℂ) * σ) ℓ
      = additiveOrbitalDivisorAt F σ p ℓ := by
  rw [additiveOrbitalDivisorAt_shift_sigma F σ _ ℓ k,
    additiveOrbitalDivisorAt_shift_tau hF hmixed _ hℓ v,
    additiveOrbitalDivisorAt_shift_one hF hper p hℓ u]

end

end GaloisForLFunctions.HTGeometry
