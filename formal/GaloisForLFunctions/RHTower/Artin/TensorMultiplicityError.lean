import GaloisForLFunctions.RHTower.Artin.ArtinCharacterMultiplicity
import GaloisForLFunctions.RHTower.GaussTripleDefectCap

/-!
# Identity contribution and cubic error for tensor multiplicities

The identity term of the character formula is the product of the three degrees
divided by the group order. Cubic mass away from the identity bounds the error.
This is the finite-group mechanism behind Slonim's Kronecker asymptotics,
arXiv:2611.11593, Section 3.2, applied to the concrete Artin character carriers.
-/

noncomputable section

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace GaloisForLFunctions

variable (G : Type*) [Group G] [Fintype G]

/-- Tensor multiplication stays inside the genuine-character monoid. -/
def GenuineCharacter.tensorProduct (χ ψ : GenuineCharacter G) : GenuineCharacter G := by
  refine ⟨χ.val * ψ.val, ?_⟩
  refine AddSubmonoid.closure_induction (motive := fun f _ =>
    ∀ ψ : GenuineCharacter G, f * ψ.val ∈ genuineCharacterMonoid G) ?_ ?_ ?_ χ.property ψ
  · intro f hf ψ
    obtain ⟨V, rfl⟩ := hf
    refine AddSubmonoid.closure_induction (motive := fun f _ =>
      V.character * f ∈ genuineCharacterMonoid G) ?_ ?_ ?_ ψ.property
    · intro f hf
      obtain ⟨W, rfl⟩ := hf
      apply AddSubmonoid.subset_closure
      exact ⟨V ⊗ W, FDRep.char_tensor V W⟩
    · simpa only [mul_zero] using (genuineCharacterMonoid G).zero_mem
    · intro f g _ _ hf hg
      rw [mul_add]
      exact (genuineCharacterMonoid G).add_mem hf hg
  · intro ψ
    simpa only [zero_mul] using (genuineCharacterMonoid G).zero_mem
  · intro f g _ _ hf hg ψ
    rw [add_mul]
    exact (genuineCharacterMonoid G).add_mem (hf ψ) (hg ψ)

omit [Fintype G] in
@[simp] theorem GenuineCharacter.tensorProduct_apply (χ ψ : GenuineCharacter G) (g : G) :
    (GenuineCharacter.tensorProduct G χ ψ).val g = χ.val g * ψ.val g := rfl

/-- Pairing with a tensor product; for an irreducible first character,
this is its multiplicity. -/
def tensorMultiplicity (χ ψ θ : GenuineCharacter G) : ℕ :=
  genuineMultiplicity G χ (GenuineCharacter.tensorProduct G ψ θ)

variable [DecidableEq G]

/-- The unnormalized cubic character mass off the identity. -/
def offIdentityCubicMass (χ : G → ℂ) : ℝ :=
  ∑ g ∈ Finset.univ.erase (1 : G), ‖χ g‖ ^ 3

private theorem offIdentityCubicMass_inv (χ : G → ℂ) :
    (∑ g ∈ Finset.univ.erase (1 : G), ‖χ g⁻¹‖ ^ 3) = offIdentityCubicMass G χ := by
  classical
  unfold offIdentityCubicMass
  apply Finset.sum_bij (fun g _ => g⁻¹)
  · intro g hg
    simpa only [Finset.mem_erase, Finset.mem_univ, and_true, inv_ne_one] using hg
  · intro a ha b hb hab
    exact inv_injective hab
  · intro b hb
    refine ⟨b⁻¹, ?_, inv_inv b⟩
    simpa only [Finset.mem_erase, Finset.mem_univ, and_true, inv_ne_one] using hb
  · intro g hg
    rfl

/-- Exact identity contribution, valid for reducible and zero characters as well. -/
theorem tensorMultiplicity_identity_term (χ ψ θ : GenuineCharacter G) :
    (Nat.card G : ℂ) * (tensorMultiplicity G χ ψ θ : ℂ) -
      χ.val 1 * ψ.val 1 * θ.val 1 =
      ∑ g ∈ Finset.univ.erase (1 : G), ψ.val g * θ.val g * χ.val g⁻¹ := by
  classical
  have hcard : (Nat.card G : ℂ) ≠ 0 := NeZero.ne _
  rw [tensorMultiplicity, genuineMultiplicity_cast, characterPairing,
    ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  simp only [GenuineCharacter.tensorProduct_apply]
  have hs := Finset.sum_erase_add Finset.univ
    (fun g : G => ψ.val g * θ.val g * χ.val g⁻¹) (Finset.mem_univ (1 : G))
  simp only [inv_one] at hs
  linear_combination -hs

/-- Cubic off-identity mass controls the tensor multiplicity's deviation from
its degree-product main term. Cubic AM–GM supplies the estimate. -/
theorem tensorMultiplicity_cubic_error (χ ψ θ : GenuineCharacter G) :
    3 * ‖(Nat.card G : ℂ) * (tensorMultiplicity G χ ψ θ : ℂ) -
      χ.val 1 * ψ.val 1 * θ.val 1‖ ≤
      offIdentityCubicMass G χ.val + offIdentityCubicMass G ψ.val +
        offIdentityCubicMass G θ.val := by
  classical
  rw [tensorMultiplicity_identity_term]
  calc
    _ ≤ 3 * ∑ g ∈ Finset.univ.erase (1 : G),
        ‖ψ.val g * θ.val g * χ.val g⁻¹‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
    _ = ∑ g ∈ Finset.univ.erase (1 : G),
        3 * ‖χ.val g⁻¹‖ * ‖ψ.val g‖ * ‖θ.val g‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      simp only [norm_mul]
      ring
    _ ≤ ∑ g ∈ Finset.univ.erase (1 : G),
        (‖χ.val g⁻¹‖ ^ 3 + ‖ψ.val g‖ ^ 3 + ‖θ.val g‖ ^ 3) :=
      Finset.sum_le_sum fun g _ => RHTower.three_mul_mul_mul_le_sum_cubes
        (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, offIdentityCubicMass_inv]
      rfl

/-- Either the tensor multiplicity is positive, or cubic mass is at least three
times the identity contribution. This is an unconditional nonvanishing certificate. -/
theorem tensorMultiplicity_positive_or_cubic_mass_large (χ ψ θ : GenuineCharacter G) :
    0 < tensorMultiplicity G χ ψ θ ∨
      3 * ‖χ.val 1 * ψ.val 1 * θ.val 1‖ ≤
        offIdentityCubicMass G χ.val + offIdentityCubicMass G ψ.val +
          offIdentityCubicMass G θ.val := by
  by_cases h : 0 < tensorMultiplicity G χ ψ θ
  · exact Or.inl h
  · right
    have hz := Nat.eq_zero_of_not_pos h
    simpa only [hz, Nat.cast_zero, mul_zero, zero_sub, norm_neg] using
      tensorMultiplicity_cubic_error G χ ψ θ

/-- The relative tensor-multiplicity error is bounded by the three normalized
cubic masses. Zero degree is recorded explicitly, without a nonvanishing premise. -/
theorem tensorMultiplicity_normalized_cubic_error (χ ψ θ : GenuineCharacter G) :
    χ.val 1 * ψ.val 1 * θ.val 1 = 0 ∨
      ‖(Nat.card G : ℂ) * (tensorMultiplicity G χ ψ θ : ℂ) /
          (χ.val 1 * ψ.val 1 * θ.val 1) - 1‖ ≤
        (offIdentityCubicMass G χ.val / ‖χ.val 1‖ ^ 3 +
          offIdentityCubicMass G ψ.val / ‖ψ.val 1‖ ^ 3 +
            offIdentityCubicMass G θ.val / ‖θ.val 1‖ ^ 3) / 3 := by
  classical
  by_cases hD : χ.val 1 * ψ.val 1 * θ.val 1 = 0
  · exact Or.inl hD
  · right
    rw [div_sub_one hD, tensorMultiplicity_identity_term, Finset.sum_div]
    have hb : 3 * ‖∑ g ∈ Finset.univ.erase (1 : G),
        (ψ.val g * θ.val g * χ.val g⁻¹) / (χ.val 1 * ψ.val 1 * θ.val 1)‖ ≤
        offIdentityCubicMass G χ.val / ‖χ.val 1‖ ^ 3 +
          offIdentityCubicMass G ψ.val / ‖ψ.val 1‖ ^ 3 +
            offIdentityCubicMass G θ.val / ‖θ.val 1‖ ^ 3 := by
      calc
        _ ≤ 3 * ∑ g ∈ Finset.univ.erase (1 : G),
            ‖(ψ.val g * θ.val g * χ.val g⁻¹) / (χ.val 1 * ψ.val 1 * θ.val 1)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
        _ = ∑ g ∈ Finset.univ.erase (1 : G),
            3 * (‖χ.val g⁻¹‖ / ‖χ.val 1‖) * (‖ψ.val g‖ / ‖ψ.val 1‖) *
              (‖θ.val g‖ / ‖θ.val 1‖) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro g hg
          simp only [norm_mul, norm_inv, div_eq_mul_inv, mul_inv_rev]
          ring
        _ ≤ ∑ g ∈ Finset.univ.erase (1 : G),
            ((‖χ.val g⁻¹‖ / ‖χ.val 1‖) ^ 3 + (‖ψ.val g‖ / ‖ψ.val 1‖) ^ 3 +
              (‖θ.val g‖ / ‖θ.val 1‖) ^ 3) :=
          Finset.sum_le_sum fun g _ => RHTower.three_mul_mul_mul_le_sum_cubes
            (div_nonneg (norm_nonneg _) (norm_nonneg _))
            (div_nonneg (norm_nonneg _) (norm_nonneg _))
            (div_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = _ := by
          simp only [div_pow, Finset.sum_add_distrib, ← Finset.sum_div]
          rw [offIdentityCubicMass_inv]
          rfl
    linarith only [hb]

end GaloisForLFunctions
