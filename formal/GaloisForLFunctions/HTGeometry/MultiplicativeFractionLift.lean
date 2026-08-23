import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Basic

/-!
# Extending a pointed multiplicative map to the fraction field

A multiplicative map from a domain into a field which sends `1` to `1`, `0` to `0` and nothing
else to `0` extends uniquely to the fraction field by `a / b ↦ Q a / Q b`.  Well-definedness is
cross-multiplication: `a / b = a' / b'` forces `a b' = a' b` in the domain, hence
`Q a · Q b' = Q a' · Q b`, and the denominators have nonzero image.

Uniqueness holds for any pointed multiplicative map on the fraction field which vanishes only at
zero, since it is determined on numerators and denominators.
-/

namespace HTGeometry

universe u

variable {D : Type u} [CommRing D] [IsDomain D] {O : Type u} [Field O]
variable (κ : Type u) [Field κ] [Algebra D κ] [IsFractionRing D κ]

/-- Every element of the fraction field is a quotient with nonzero denominator. -/
theorem exists_fraction_rep (z : κ) :
    ∃ ab : D × D, ab.2 ≠ 0 ∧ algebraMap D κ ab.1 / algebraMap D κ ab.2 = z := by
  obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective (A := D) z
  exact ⟨(a, b), mem_nonZeroDivisors_iff_ne_zero.mp hb, hz⟩

/-- The underlying function of the extension of a pointed multiplicative map to the fraction
field. -/
noncomputable def multiplicativeFracLiftFun (Q : D →*₀ O) (z : κ) : O :=
  Q (exists_fraction_rep (D := D) κ z).choose.1 / Q (exists_fraction_rep (D := D) κ z).choose.2

variable {κ}

theorem multiplicativeFracLiftFun_eq (Q : D →*₀ O) (hQ : ∀ d : D, Q d = 0 ↔ d = 0)
    (a b : D) (hb : b ≠ 0) :
    multiplicativeFracLiftFun κ Q (algebraMap D κ a / algebraMap D κ b) = Q a / Q b := by
  set z : κ := algebraMap D κ a / algebraMap D κ b with hz
  set r : D × D := (exists_fraction_rep (D := D) κ z).choose with hr
  obtain ⟨hb', hrep⟩ := (exists_fraction_rep (D := D) κ z).choose_spec
  have hinj := IsFractionRing.injective D κ
  have hbz : algebraMap D κ b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
  have hb'z : algebraMap D κ r.2 ≠ 0 := fun h => hb' (hinj (by rw [h, map_zero]))
  have hcross : algebraMap D κ r.1 * algebraMap D κ b
      = algebraMap D κ a * algebraMap D κ r.2 := by
    rw [← div_eq_div_iff hb'z hbz, hrep, hz]
  have hD : r.1 * b = a * r.2 := hinj (by rw [map_mul, map_mul]; exact hcross)
  have hQb : Q b ≠ 0 := fun h => hb ((hQ b).1 h)
  have hQb' : Q r.2 ≠ 0 := fun h => hb' ((hQ _).1 h)
  have hQD : Q r.1 * Q b = Q a * Q r.2 := by rw [← map_mul, ← map_mul, hD]
  show Q r.1 / Q r.2 = Q a / Q b
  rw [div_eq_div_iff hQb' hQb]
  exact hQD

/-- **The extension of a pointed multiplicative map to the fraction field.**  A multiplicative map
from a domain into a field which vanishes only at zero extends to the fraction field by
`a / b ↦ Q a / Q b`. -/
noncomputable def multiplicativeFracLift (Q : D →*₀ O) (hQ : ∀ d : D, Q d = 0 ↔ d = 0) :
    κ →*₀ O where
  toFun := multiplicativeFracLiftFun κ Q
  map_zero' := by
    have h := multiplicativeFracLiftFun_eq (κ := κ) Q hQ 0 1 one_ne_zero
    simpa using h
  map_one' := by
    have h := multiplicativeFracLiftFun_eq (κ := κ) Q hQ 1 1 one_ne_zero
    simpa using h
  map_mul' z₁ z₂ := by
    obtain ⟨⟨a₁, b₁⟩, hb₁, rfl⟩ := exists_fraction_rep (D := D) κ z₁
    obtain ⟨⟨a₂, b₂⟩, hb₂, rfl⟩ := exists_fraction_rep (D := D) κ z₂
    rw [div_mul_div_comm, ← map_mul, ← map_mul,
      multiplicativeFracLiftFun_eq Q hQ _ _ (mul_ne_zero hb₁ hb₂),
      multiplicativeFracLiftFun_eq Q hQ _ _ hb₁,
      multiplicativeFracLiftFun_eq Q hQ _ _ hb₂,
      map_mul, map_mul, div_mul_div_comm]

/-- The extension restricts to the original map. -/
theorem multiplicativeFracLift_algebraMap (Q : D →*₀ O) (hQ : ∀ d : D, Q d = 0 ↔ d = 0)
    (d : D) :
    multiplicativeFracLift (κ := κ) Q hQ (algebraMap D κ d) = Q d := by
  show multiplicativeFracLiftFun κ Q (algebraMap D κ d) = Q d
  have h := multiplicativeFracLiftFun_eq (κ := κ) Q hQ d 1 one_ne_zero
  simpa using h

/-- A pointed multiplicative map on the fraction field which vanishes only at zero is determined
by its restriction to the domain. -/
theorem multiplicativeFrac_ext (F₁ F₂ : κ →*₀ O)
    (h : ∀ d : D, F₁ (algebraMap D κ d) = F₂ (algebraMap D κ d))
    (h₁ : ∀ z : κ, F₁ z = 0 → z = 0) : F₁ = F₂ := by
  refine DFunLike.ext _ _ fun z => ?_
  obtain ⟨⟨a, b⟩, hb, rfl⟩ := exists_fraction_rep (D := D) κ z
  have hbz : algebraMap D κ b ≠ 0 := fun hz =>
    hb (IsFractionRing.injective D κ (by rw [hz, map_zero]))
  have hF₁b : F₁ (algebraMap D κ b) ≠ 0 := fun hz => hbz (h₁ _ hz)
  have hF₂b : F₂ (algebraMap D κ b) ≠ 0 := by rw [← h b]; exact hF₁b
  rw [map_div₀, map_div₀, h a, h b]

end HTGeometry

namespace HTGeometry


/-- **Deninger, Proposition 13.9, the uniqueness of `P_y`.**  A pointed multiplicative map on a
localization is determined by its restriction to the ring, as soon as the inverted elements have
unit image: `Q (a / s) · Q (s) = Q (a)`. -/
theorem localization_monoidWithZeroHom_ext {R O : Type*} [CommRing R] [CommRing O]
    (M : Submonoid R) (Rₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ] [IsLocalization M Rₘ]
    (Q₁ Q₂ : Rₘ →*₀ O)
    (h : ∀ a : R, Q₁ (algebraMap R Rₘ a) = Q₂ (algebraMap R Rₘ a))
    (hunit : ∀ s : M, IsUnit (Q₁ (algebraMap R Rₘ (s : R)))) :
    Q₁ = Q₂ := by
  refine DFunLike.ext _ _ fun x => ?_
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Rₘ) M x
  have hspec : IsLocalization.mk' Rₘ a s * algebraMap R Rₘ (s : R) = algebraMap R Rₘ a :=
    IsLocalization.mk'_spec Rₘ a s
  have h1 : Q₁ (IsLocalization.mk' Rₘ a s) * Q₁ (algebraMap R Rₘ (s : R))
      = Q₁ (algebraMap R Rₘ a) := by rw [← map_mul, hspec]
  have h2 : Q₂ (IsLocalization.mk' Rₘ a s) * Q₂ (algebraMap R Rₘ (s : R))
      = Q₂ (algebraMap R Rₘ a) := by rw [← map_mul, hspec]
  have hs := hunit s
  refine hs.mul_left_cancel ?_
  rw [mul_comm _ (Q₁ (IsLocalization.mk' Rₘ a s)), h1, h a, ← h2, h (s : R)]
  ring

end HTGeometry
