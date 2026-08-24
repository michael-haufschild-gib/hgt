import GaloisForLFunctions.HTGeometry.ABHN.FiniteSupportProfile
import GaloisForLFunctions.HTGeometry.TripticOrbitalDivisorLinearity
import GaloisForLFunctions.HTGeometry.TripticOrbitResidueReciprocity

/-!
# Hasse support rigidity for triptic orbital residues

Triptic orbit-residue reciprocity equates two finite orbital sums.  We package the first orbit with
positive sign and the second with negative sign into one finite-support balance profile.  Its global
sum vanishes, so a nonzero Laurent coefficient on either boundary cannot occur alone: it must be
accompanied by another coefficient on the same orbit or by a coefficient on the transverse orbit.
-/

namespace GaloisForLFunctions.HTGeometry

open Function
open GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

noncomputable local instance : DecidableEq (ℤ ⊕ ℤ) := Classical.decEq _

/-- Embed the `σ`-orbit into the two-boundary residue index. -/
def tripticSigmaOrbitResidueEmbedding : ℤ ↪ (ℤ ⊕ ℤ) :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- Embed the `τ`-orbit into the two-boundary residue index. -/
def tripticTauOrbitResidueEmbedding : ℤ ↪ (ℤ ⊕ ℤ) :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- Signed two-boundary orbital residue profile attached to a triptic source. -/
noncomputable def tripticOrbitResidueBalanceProfile
    {F : ℂ → ℂ} {τ σ Cst p : ℂ} {ℓ : ℤ}
    (hF : MeromorphicOn F Set.univ) (hper : PeriodicOneGerm F)
    (hmixed : MixedConstGerm F τ σ Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ,
      (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (hℓ : ℓ < 0) : (ℤ ⊕ ℤ) →₀ ℂ := by
  classical
  let left : ℤ → ℂ := fun m =>
    laurentCoeff (fun z => F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ
  let right : ℤ → ℂ := fun n =>
    laurentCoeff (fun z => F (z + τ) - F z) (p + (n : ℂ) * τ) ℓ
  have hindepSwap : ∀ m n j : ℤ,
      (m : ℂ) * σ + (n : ℂ) * τ + (j : ℂ) = 0 → m = 0 ∧ n = 0 ∧ j = 0 := by
    intro m n j h
    obtain ⟨hn, hm, hj⟩ := hindep n m j (by linear_combination h)
    exact ⟨hm, hn, hj⟩
  have hmixedSwap : MixedConstGerm F σ τ Cst := by
    intro z
    filter_upwards [hmixed z] with w hw
    rw [show w + σ + τ = w + τ + σ from by ring]
    linear_combination hw
  have hleft : HasFiniteSupport left :=
    finite_support_orbitalDivisorTerm hF hper hmixed hτ hindepSwap p hℓ
  have hright : HasFiniteSupport right :=
    finite_support_orbitalDivisorTerm hF hper hmixedSwap hσ hindep p hℓ
  exact
    Finsupp.embDomain tripticSigmaOrbitResidueEmbedding
        (finsuppOfFiniteSupport left hleft) -
      Finsupp.embDomain tripticTauOrbitResidueEmbedding
        (finsuppOfFiniteSupport right hright)

@[simp]
theorem tripticOrbitResidueBalanceProfile_sigma
    {F : ℂ → ℂ} {τ σ Cst p : ℂ} {ℓ : ℤ}
    (hF : MeromorphicOn F Set.univ) (hper : PeriodicOneGerm F)
    (hmixed : MixedConstGerm F τ σ Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ,
      (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (hℓ : ℓ < 0) (m : ℤ) :
    tripticOrbitResidueBalanceProfile (p := p)
        hF hper hmixed hτ hσ hindep hℓ (Sum.inl m) =
      laurentCoeff (fun z => F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ := by
  classical
  simp [tripticOrbitResidueBalanceProfile, Finsupp.embDomain_apply,
    tripticSigmaOrbitResidueEmbedding, tripticTauOrbitResidueEmbedding]

@[simp]
theorem tripticOrbitResidueBalanceProfile_tau
    {F : ℂ → ℂ} {τ σ Cst p : ℂ} {ℓ : ℤ}
    (hF : MeromorphicOn F Set.univ) (hper : PeriodicOneGerm F)
    (hmixed : MixedConstGerm F τ σ Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ,
      (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (hℓ : ℓ < 0) (n : ℤ) :
    tripticOrbitResidueBalanceProfile (p := p)
        hF hper hmixed hτ hσ hindep hℓ (Sum.inr n) =
      -laurentCoeff (fun z => F (z + τ) - F z) (p + (n : ℂ) * τ) ℓ := by
  classical
  simp [tripticOrbitResidueBalanceProfile, Finsupp.embDomain_apply,
    tripticSigmaOrbitResidueEmbedding, tripticTauOrbitResidueEmbedding]

/-- Triptic reciprocity is vanishing of the signed two-boundary profile sum. -/
theorem tripticOrbitResidueBalanceProfile_sum_eq_zero
    {F : ℂ → ℂ} {τ σ Cst p : ℂ} {ℓ : ℤ}
    (hF : MeromorphicOn F Set.univ) (hper : PeriodicOneGerm F)
    (hmixed : MixedConstGerm F τ σ Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ,
      (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (hℓ : ℓ < 0) :
    (tripticOrbitResidueBalanceProfile (p := p)
      hF hper hmixed hτ hσ hindep hℓ).sum (fun _ z => z) = 0 := by
  rw [tripticOrbitResidueBalanceProfile, Finsupp.sum_sub_index (by intros; rfl),
    Finsupp.sum_embDomain, Finsupp.sum_embDomain,
    finsuppOfFiniteSupport_sum_eq_finsum, finsuppOfFiniteSupport_sum_eq_finsum,
    triptic_orbit_residue_reciprocity hF hper hmixed hτ hσ hindep p hℓ,
    sub_self]

/-- One nonzero `σ`-boundary coefficient forces at least two active balance coordinates. -/
theorem tripticOrbitResidueBalanceProfile_two_le_support_card_of_sigma_ne_zero
    {F : ℂ → ℂ} {τ σ Cst p : ℂ} {ℓ : ℤ}
    (hF : MeromorphicOn F Set.univ) (hper : PeriodicOneGerm F)
    (hmixed : MixedConstGerm F τ σ Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ,
      (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (hℓ : ℓ < 0) {m : ℤ}
    (hm : laurentCoeff (fun z => F (z + σ) - F z)
      (p + (m : ℂ) * σ) ℓ ≠ 0) :
    2 ≤ (tripticOrbitResidueBalanceProfile (p := p)
      hF hper hmixed hτ hσ hindep hℓ).support.card := by
  apply finsupp_two_le_support_card_of_sum_eq_zero
    (tripticOrbitResidueBalanceProfile (p := p)
      hF hper hmixed hτ hσ hindep hℓ)
    (tripticOrbitResidueBalanceProfile_sum_eq_zero
      hF hper hmixed hτ hσ hindep hℓ)
  intro hzero
  have hcoord := Finsupp.ext_iff.mp hzero (Sum.inl m)
  exact hm (by simpa using hcoord)

/-- A nonzero `σ`-boundary residue has a same-orbit or transverse-orbit companion. -/
theorem tripticOrbitResidueBalanceProfile_exists_companion_of_sigma_ne_zero
    {F : ℂ → ℂ} {τ σ Cst p : ℂ} {ℓ : ℤ}
    (hF : MeromorphicOn F Set.univ) (hper : PeriodicOneGerm F)
    (hmixed : MixedConstGerm F τ σ Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ,
      (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (hℓ : ℓ < 0) {m : ℤ}
    (hm : laurentCoeff (fun z => F (z + σ) - F z)
      (p + (m : ℂ) * σ) ℓ ≠ 0) :
    (∃ k : ℤ, k ≠ m ∧
      laurentCoeff (fun z => F (z + σ) - F z)
        (p + (k : ℂ) * σ) ℓ ≠ 0) ∨
    (∃ n : ℤ, laurentCoeff (fun z => F (z + τ) - F z)
      (p + (n : ℂ) * τ) ℓ ≠ 0) := by
  obtain ⟨w, hwne, hw⟩ := finsupp_exists_other_nonzero_place_of_sum_eq_zero
    (tripticOrbitResidueBalanceProfile (p := p)
      hF hper hmixed hτ hσ hindep hℓ)
    (tripticOrbitResidueBalanceProfile_sum_eq_zero
      hF hper hmixed hτ hσ hindep hℓ)
    (i := Sum.inl m) (by simpa using hm)
  cases w with
  | inl k => exact Or.inl ⟨k, fun h => hwne (by simp [h]), by simpa using hw⟩
  | inr n => exact Or.inr ⟨n, by simpa using neg_ne_zero.mp (by simpa using hw)⟩

/-- A nonzero `τ`-boundary residue has a transverse-orbit or same-orbit companion. -/
theorem tripticOrbitResidueBalanceProfile_exists_companion_of_tau_ne_zero
    {F : ℂ → ℂ} {τ σ Cst p : ℂ} {ℓ : ℤ}
    (hF : MeromorphicOn F Set.univ) (hper : PeriodicOneGerm F)
    (hmixed : MixedConstGerm F τ σ Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ,
      (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (hℓ : ℓ < 0) {n : ℤ}
    (hn : laurentCoeff (fun z => F (z + τ) - F z)
      (p + (n : ℂ) * τ) ℓ ≠ 0) :
    (∃ m : ℤ, laurentCoeff (fun z => F (z + σ) - F z)
      (p + (m : ℂ) * σ) ℓ ≠ 0) ∨
    (∃ k : ℤ, k ≠ n ∧
      laurentCoeff (fun z => F (z + τ) - F z)
        (p + (k : ℂ) * τ) ℓ ≠ 0) := by
  obtain ⟨w, hwne, hw⟩ := finsupp_exists_other_nonzero_place_of_sum_eq_zero
    (tripticOrbitResidueBalanceProfile (p := p)
      hF hper hmixed hτ hσ hindep hℓ)
    (tripticOrbitResidueBalanceProfile_sum_eq_zero
      hF hper hmixed hτ hσ hindep hℓ)
    (i := Sum.inr n) (by simpa using neg_ne_zero.mpr hn)
  cases w with
  | inl m => exact Or.inl ⟨m, by simpa using hw⟩
  | inr k =>
      exact Or.inr ⟨k, fun h => hwne (by simp [h]),
        by simpa using neg_ne_zero.mp (by simpa using hw)⟩

end

end GaloisForLFunctions.HTGeometry
