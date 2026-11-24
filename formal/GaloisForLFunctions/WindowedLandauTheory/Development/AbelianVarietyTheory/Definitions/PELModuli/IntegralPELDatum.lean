import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.GlobalPELDatum

/-! PEL data at a prime and the base ring conditions for integral models. -/

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT

/-- A PEL datum with split, unramified quadratic data at `p`, a split
order at `p`, and a pairing perfect after localization at `p`. -/
structure Datum (p : ℕ) [Fact p.Prime] extends Gen.GDatum where
  disc_p : ¬ (p : ℤ) ∣ tr ^ 2 - 4 * nm
  split : ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - tr * r + nm
  splitP : Nonempty ((O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 F] Matrix (Fin m) (Fin m) (𝓞 F ⊗[ℤ] ℤ_[p]))
  perfP : ∃ e : ℕ, e.Coprime p ∧ ∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f

variable {p : ℕ} [Fact p.Prime]

abbrev Datum.toG (D : Datum p) : Gen.GDatum := D.toGDatum

/-- An integral base supplies prime-to-`p` units and separates the
chosen embeddings on every characteristic-`p` field point. -/
structure Base (D : Datum p) (R : Type) [CommRing R] where
  unit : ∀ k : ℕ, k.Coprime p → IsUnit (k : R)
  ρ : R
  ρ_root : ρ ^ 2 - D.tr * ρ + D.nm = 0
  t : Fin D.a → (𝓞 D.F →+* R)
  t_ω : ∀ i, t i D.ω = ρ
  comax : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤
  apart : ∀ i j, i ≠ j → ∀ (k : Type) [Field k] [CharP k p] (β : R →+* k),
    RingHom.ker (β.comp (t i)) ≠ RingHom.ker (β.comp (t j))

variable {D : Datum p} {R : Type} [CommRing R] [Algebra ℚ R]

/-- A rational base has prime-to-`p` units and no characteristic-`p` points. -/
def Base.ofGeneric (gb : Gen.GBase D.toG R) : Base D R where
  unit k hk := by
    have hk0 : (k : ℚ) ≠ 0 := by
      rintro h
      have : k = 0 := by exact_mod_cast h
      subst k
      exact (Fact.out : p.Prime).one_lt.ne' ((Nat.coprime_zero_left p).1 hk)
    simpa using (IsUnit.mk0 _ hk0).map (algebraMap ℚ R)
  ρ := gb.ρ
  ρ_root := gb.ρ_root
  t := gb.t
  t_ω := gb.t_ω
  comax := gb.comax
  apart i j _ k _ _ β := by
    exfalso
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hp := ((IsUnit.mk0 _ hp0).map (β.comp (algebraMap ℚ R))).ne_zero
    simp at hp

def Base.toGeneric (b : Base D R) : Gen.GBase D.toG R :=
  ⟨b.ρ, b.ρ_root, b.t, b.t_ω, b.comax⟩

end GlobalTheory.UPel.HT
