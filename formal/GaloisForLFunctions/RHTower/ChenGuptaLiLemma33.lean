/-
# Chen--Gupta--Li Lemma 3.3

This module formalizes the source character-subdivision lemma.  A certified
positive divisor of a certified positive ambient modulus defines an injective
change-of-level map.  Representatives of its finite character quotient give
the bounded factor set required in the source statement.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiRamanujanFourier
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.GroupTheory.Coset.Card

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Certified CGL data `q₁ ∣ q` for Lemma 3.3. -/
structure CGLLemma33Subdivision where
  ambient : CGLPositiveModulus
  divisor : CGLPositiveModulus
  divides : divisor.value ∣ ambient.value

/-- Change a character from the source divisor modulus to the ambient modulus. -/
noncomputable def cglLemma33Lift (P : CGLLemma33Subdivision) :
    DirichletCharacter ℂ P.divisor.value →* DirichletCharacter ℂ P.ambient.value :=
  DirichletCharacter.changeLevel P.divides

/-- The subgroup of ambient characters induced from the source divisor modulus. -/
noncomputable def cglLemma33LiftRange (P : CGLLemma33Subdivision) :
    Subgroup (DirichletCharacter ℂ P.ambient.value) :=
  (cglLemma33Lift P).range

/-- Quotient of the ambient character group by the induced divisor-level characters. -/
abbrev CGLLemma33Quotient (P : CGLLemma33Subdivision) :=
  DirichletCharacter ℂ P.ambient.value ⧸ cglLemma33LiftRange P

noncomputable instance (P : CGLLemma33Subdivision) : Fintype (CGLLemma33Quotient P) :=
  Fintype.ofFinite _

/-- A fixed representative of each character quotient class. -/
noncomputable def cglLemma33Representative (P : CGLLemma33Subdivision) :
    CGLLemma33Quotient P → DirichletCharacter ℂ P.ambient.value :=
  fun c => Classical.choose (QuotientGroup.mk_surjective c)

theorem cglLemma33Representative_spec (P : CGLLemma33Subdivision)
    (c : CGLLemma33Quotient P) :
    QuotientGroup.mk (cglLemma33Representative P c) = c := by
  exact Classical.choose_spec (QuotientGroup.mk_surjective c)

/-- The finite source factor set `S`, represented here by ambient Dirichlet characters. -/
noncomputable def cglLemma33RepresentativeSet (P : CGLLemma33Subdivision) :
    Finset (DirichletCharacter ℂ P.ambient.value) :=
  Finset.univ.image (cglLemma33Representative P)

/-- A member of the finite source factor set. -/
abbrev CGLLemma33Representative (P : CGLLemma33Subdivision) :=
  ↑(cglLemma33RepresentativeSet P)

/-- The CGL factor set has cardinality at most `φ(q) / φ(q₁)`. -/
theorem cglLemma33RepresentativeSet_card_le (P : CGLLemma33Subdivision) :
    (cglLemma33RepresentativeSet P).card ≤
      P.ambient.value.totient / P.divisor.value.totient := by
  classical
  have h_range_card : Nat.card (cglLemma33LiftRange P) = P.divisor.value.totient := by
    calc
      Nat.card (cglLemma33LiftRange P) =
          Nat.card (DirichletCharacter ℂ P.divisor.value) := by
        exact Nat.card_congr
          (MonoidHom.ofInjective
            (f := cglLemma33Lift P)
            (DirichletCharacter.changeLevel_injective P.divides)).toEquiv.symm
      _ = P.divisor.value.totient :=
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ P.divisor.value
  have h_quotient_card : Nat.card (CGLLemma33Quotient P) ≤
      P.ambient.value.totient / P.divisor.value.totient := by
    have h_product : P.ambient.value.totient =
        Nat.card (CGLLemma33Quotient P) * P.divisor.value.totient := by
      calc
        P.ambient.value.totient = Nat.card (DirichletCharacter ℂ P.ambient.value) :=
          (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ P.ambient.value).symm
        _ = Nat.card (CGLLemma33Quotient P) * Nat.card (cglLemma33LiftRange P) :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup (cglLemma33LiftRange P)
        _ = Nat.card (CGLLemma33Quotient P) * P.divisor.value.totient := by
          rw [h_range_card]
    apply (Nat.le_div_iff_mul_le (Nat.totient_pos.mpr P.divisor.positive)).mpr
    exact h_product.symm.le
  calc
    (cglLemma33RepresentativeSet P).card =
        (Finset.univ.image (cglLemma33Representative P)).card := by
      rfl
    _ ≤ Fintype.card (CGLLemma33Quotient P) := by
      simpa using
        (Finset.card_image_le (s := Finset.univ) (f := cglLemma33Representative P))
    _ = Nat.card (CGLLemma33Quotient P) := Nat.card_eq_fintype_card.symm
    _ ≤ P.ambient.value.totient / P.divisor.value.totient := h_quotient_card

/-- Every source factor is pointwise `1`-bounded. -/
theorem cglLemma33Representative_norm_le_one (P : CGLLemma33Subdivision)
    (f : CGLLemma33Representative P) (a : ZMod P.ambient.value) :
    ‖f.1 a‖ ≤ 1 := by
  exact f.1.norm_le_one a

/-- **CGL Lemma 3.3.** Every ambient character factors through a character at
the divisor modulus and one member of the finite `1`-bounded source factor set. -/
theorem cglLemma33_source_factor (P : CGLLemma33Subdivision)
    (χ : DirichletCharacter ℂ P.ambient.value) :
    ∃ χ₁ : DirichletCharacter ℂ P.divisor.value,
      ∃ f : CGLLemma33Representative P, χ = cglLemma33Lift P χ₁ * f.1 := by
  classical
  let f : DirichletCharacter ℂ P.ambient.value :=
    cglLemma33Representative P (QuotientGroup.mk χ)
  have hf : f ∈ cglLemma33RepresentativeSet P := by
    refine Finset.mem_image.mpr ?_
    exact ⟨QuotientGroup.mk χ, Finset.mem_univ _, rfl⟩
  have hquotient : (f : CGLLemma33Quotient P) = (χ : CGLLemma33Quotient P) := by
    simpa only [f] using cglLemma33Representative_spec P (QuotientGroup.mk χ)
  have hmem : f⁻¹ * χ ∈ cglLemma33LiftRange P :=
    QuotientGroup.eq.mp hquotient
  rcases hmem with ⟨χ₁, hχ₁⟩
  refine ⟨χ₁, ⟨f, hf⟩, ?_⟩
  symm
  calc
    cglLemma33Lift P χ₁ * f = (f⁻¹ * χ) * f := by rw [hχ₁]
    _ = χ := by
      rw [mul_assoc, mul_comm χ f, ← mul_assoc, inv_mul_cancel, one_mul]

end RHTower
