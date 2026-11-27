import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InertiaPolynomialDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameInertiaFiniteImageOrder
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FrobeniusOnTameInertia

/-! A representation with open inertia kernel and trivial wild inertia
has its tame characteristic polynomial labelled over the prime field. -/

noncomputable section

open NumberField IsLocalRing Polynomial
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open WindowedLandauTheory.CyclotomicNorms WindowedLandauTheory.NormalizedTypes
open GlobalTheory.TeichPlace

namespace GlobalTheory.TameKummer

/-- The tame characteristic polynomial of an inertia element has a unique
prime-field label for a smooth tame action containing arithmetic Frobenius. -/
theorem existsUnique_label_of_smooth_tame_inertia {E Ω K : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Field K] [IsAlgClosed K]
    (A : ValuationSubring Ω) {p N : ℕ} [Fact p.Prime] (hp : A.valuation (p : Ω) < 1)
    {B : ValuationSubring K} {κ : ResidueField B ≃+* Fbar p} {t : Fbar p →* K}
    (ht : IsTeich B κ t)
    (W : Subgroup (G E Ω)) (hIW : Ine (F := E) A ≤ W) (ρ : W →* GL (Fin N) K)
    {U : Set (G E Ω)} (hU : IsOpen U)
    (hK : ∀ s : W, (s : G E Ω) ∈ Ine (F := E) A → ((s : G E Ω) ∈ U ↔ ρ s = 1))
    (hW : ∀ s : W, (s : G E Ω) ∈ Ine (F := E) A →
      (∀ y : Ω, y ≠ 0 → A.valuation ((s : G E Ω) y / y - 1) < 1) → ρ s = 1)
    (τ φ : W) (hτ : (τ : G E Ω) ∈ Ine (F := E) A) (hφ : IsFrob A p (φ : G E Ω)) :
    ∃! f : (ZMod p)[X], f.Monic ∧
      (ρ τ : Matrix (Fin N) (Fin N) K).charpoly =
        ((rootsBar f).map fun x => X - C (t x)).prod := by
  obtain ⟨m, hm, hpm, hpow⟩ := exists_primeTo_pow_mem_of_wild_mem A hp hU (fun s hs hratio =>
    (hK ⟨s, hIW hs⟩ hs).mpr (hW ⟨s, hIW hs⟩ hs hratio))
  have hmτ : ρ τ ^ m = 1 := by
    rw [← map_pow]
    exact (hK (τ ^ m) (pow_mem hτ m)).mp (hpow _ hτ)
  obtain ⟨hδI, hδW⟩ := frobenius_conj_div_wild A hp hτ hφ
  have he := hW ((τ ^ p)⁻¹ * (φ * τ * φ⁻¹)) hδI hδW
  rw [map_mul ρ _ _, map_inv, map_pow] at he
  have hconj : ρ φ * ρ τ * (ρ φ)⁻¹ = (ρ τ) ^ p := by
    have h := congrArg (fun z => ρ τ ^ p * z) he
    simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one, map_mul, map_inv] using h
  exact existsUnique_label_of_tame_matrix ht hm hpm (ρ τ) (ρ φ) hmτ hconj

end GlobalTheory.TameKummer
