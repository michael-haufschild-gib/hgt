import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FrobeniusPowerOnTameInertia
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitPlaceOrder

/-! At a place with residue field of size (p), arithmetic Frobenius
conjugates tame inertia by the (p)-th power. Prime-to-(p) radicals detect
the equality modulo wild inertia. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open ReciprocityTheory.Gal

namespace GlobalTheory.TameKummer

/-- The difference between Frobenius conjugation and the (p)-th power
acts trivially on every prime-to-(p) radical, hence belongs to wild inertia. -/
theorem frobenius_conj_div_wild {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) {p : ℕ} [Fact p.Prime] (hp : A.valuation (p : Ω) < 1)
    {τ φ : G E Ω} (hτ : τ ∈ Ine (F := E) A) (hφ : IsFrob A p φ) :
    let δ := (τ ^ p)⁻¹ * (φ * τ * φ⁻¹)
    δ ∈ Ine (F := E) A ∧ ∀ y : Ω, y ≠ 0 → A.valuation (δ y / y - 1) < 1 := by
  frobenius_conj_div_wild_of_card A hp hτ hφ

/-- At each designated split place, an arithmetic Frobenius satisfies the tame
conjugation relation in every representation that kills wild inertia. -/
theorem exists_frobenius_conj_of_wild_trivial (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    {M : Type*} [Group M] (ρ : G D.host.E D.nd.Om →* M)
    (hρ : ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
      (∀ y : D.nd.Om, y ≠ 0 → (D.nd.plOm.1 (D.naut.plGw k v)).valuation (s y / y - 1) < 1) →
      ρ s = 1) :
    ∃ φ, ρ (φ * D.ntypes.tg k v * φ⁻¹) = ρ (D.ntypes.tg k v) ^ D.host.g k := by
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  letI := D.nd.acOm
  let w := D.naut.plGw k v
  let A := D.nd.plOm.1 w
  have hw := D.naut.plGw_over k v
  have hp : A.valuation (D.host.g k : D.nd.Om) < 1 := by
    simpa using (D.nd.plOm.2 w (D.host.g k : 𝓞 D.host.E)).mpr hw
  obtain ⟨φ, hφ⟩ := exists_isFrob (D.nd.plOm.2 w)
  rw [(normV_and_notMem_sq_of_split (D.host.g_prime k) (D.nd.g_split k) w hw).1] at hφ
  obtain ⟨hI, hW⟩ := frobenius_conj_div_wild A hp (D.ntypes.tg_mem k v) hφ
  have he := hρ _ hI hW
  change ρ ((D.ntypes.tg k v ^ D.host.g k)⁻¹ * (φ * D.ntypes.tg k v * φ⁻¹)) = 1 at he
  rw [map_mul ρ _ _, map_inv, map_pow] at he
  refine ⟨φ, ?_⟩
  have h := congrArg (fun z => ρ (D.ntypes.tg k v) ^ D.host.g k * z) he
  simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] using h

end GlobalTheory.TameKummer
