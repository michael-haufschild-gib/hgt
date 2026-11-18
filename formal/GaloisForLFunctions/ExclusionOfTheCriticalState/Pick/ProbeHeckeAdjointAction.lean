import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeHeckeSpecialization

/-!
# Adjoint discriminant on the probe Hecke algebra

Finkelberg–Kazhdan, Lemma 3.3.1 (arXiv:2610.38371), computes the
two transverse weights of torus conjugation. The same calculation on the
reflection hull works at singular parameters by using the additive
commutator. Its square is the squared eigenvalue gap times the projection
onto the maps exchanging reflection sectors.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
variable {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})
local notation "A" => Module.End ℂ (reflectionHull p)
local notation "R" => hullReflection p

/-- Part of an observable exchanging the two reflection sectors. -/
def hullMixedPart (X : A) : A := (2 : ℂ)⁻¹ • (X - R * X * R)

/-- Additive adjoint action of the probe Hecke generator. -/
def hullHeckeCommutator (q : ℂ) (X : A) : A := hullHecke p q * X - X * hullHecke p q

private theorem reflection_mul_cancel (X : A) : R * (R * X) = X := by
  rw [← mul_assoc, hullReflection_sq, one_mul]

private theorem mul_reflection_cancel (X : A) : X * R * R = X := by
  rw [mul_assoc, hullReflection_sq, mul_one]

private theorem hecke_affine (q : ℂ) :
    hullHecke p q = ((q^2 - 1)/2) • (1 : A) + ((q^2 + 1)/2) • R := by
  simp only [hullHecke, hullPositive, hullNegative, smul_add, smul_sub, smul_smul]
  module

/-- The scalar component drops out of the adjoint action, leaving exactly half the eigenvalue gap. -/
theorem hullHeckeCommutator_eq (q : ℂ) (X : A) :
    hullHeckeCommutator p q X = ((q ^ 2 + 1)/2) • (R * X - X * R) := by
  simp only [hullHeckeCommutator, hecke_affine, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, smul_sub]
  abel

/-- Averaging against the sign character gives a projection on the endomorphism algebra. -/
theorem hullMixedPart_twice (X : A) : hullMixedPart p (hullMixedPart p X) = hullMixedPart p X := by
  have h : R * (R * X * R) * R = X := by
    rw [← mul_assoc R (R * X) R, reflection_mul_cancel, mul_reflection_cancel]
  simp only [hullMixedPart, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, h]
  module

/-- The mixed part vanishes precisely on the commutant of the actual zero reflection. -/
theorem hullMixedPart_zero_iff (X : A) : hullMixedPart p X = 0 ↔ Commute R X := by
  change (2 : ℂ)⁻¹ • (X - R * X * R) = 0 ↔ R * X = X * R
  rw [smul_eq_zero, or_iff_right (inv_ne_zero (by norm_num)), sub_eq_zero]
  constructor
  · intro h
    simpa only [mul_reflection_cancel] using (congrArg (fun T : A => T * R) h).symm
  · intro h
    rw [h, mul_reflection_cancel]

/-- The entire commutant appears at q²=-1. At every other parameter it is reflection-preserving. -/
theorem hullHecke_commute_iff (q : ℂ) (X : A) :
    Commute (hullHecke p q) X ↔ q ^ 2 = -1 ∨ Commute R X := by
  change hullHecke p q * X = X * hullHecke p q ↔ _ ∨ R * X = X * R
  rw [← sub_eq_zero, ← hullHeckeCommutator, hullHeckeCommutator_eq, smul_eq_zero,
    div_eq_zero_iff, or_iff_left (by norm_num : (2 : ℂ) ≠ 0), sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- The square of the adjoint action is the squared eigenvalue gap on sector-exchanging maps. -/
theorem hullHeckeCommutator_square (q : ℂ) (X : A) :
    hullHeckeCommutator p q (hullHeckeCommutator p q X) = (q^2 + 1)^2 • hullMixedPart p X := by
  simp only [hullHeckeCommutator_eq, hullMixedPart, mul_smul_comm, smul_mul_assoc, mul_sub,
    sub_mul, reflection_mul_cancel, mul_reflection_cancel, ← mul_assoc R X R,
    smul_sub, smul_smul]
  module

/-- No nilpotent Jordan part survives on the zero adjoint eigenspace, even when the parameter collides. -/
theorem hullHeckeCommutator_square_zero_iff (q : ℂ) (X : A) :
    hullHeckeCommutator p q (hullHeckeCommutator p q X) = 0 ↔ Commute (hullHecke p q) X := by
  rw [hullHeckeCommutator_square, smul_eq_zero, sq_eq_zero_iff, add_eq_zero_iff_eq_neg,
    hullMixedPart_zero_iff, hullHecke_commute_iff]

/-- Every commutator exchanges sectors. -/
theorem hullMixedPart_commutator (q : ℂ) (X : A) :
    hullMixedPart p (hullHeckeCommutator p q X) = hullHeckeCommutator p q X := by
  have h : R * (X * R) * R = R * X := by rw [← mul_assoc R X R, mul_reflection_cancel]
  simp only [hullHeckeCommutator_eq, hullMixedPart, mul_smul_comm, smul_mul_assoc, mul_sub,
    sub_mul, reflection_mul_cancel, h, smul_sub, smul_smul]
  module

/-- The exact cubic adjoint polynomial holds on all endomorphisms of every finite probe hull. -/
theorem hullHeckeCommutator_cubic (q : ℂ) (X : A) :
    hullHeckeCommutator p q (hullHeckeCommutator p q (hullHeckeCommutator p q X)) =
      (q^2 + 1)^2 • hullHeckeCommutator p q X := by
  rw [hullHeckeCommutator_square, hullMixedPart_commutator]

private theorem commutator_smul (q c : ℂ) (Y : A) :
    hullHeckeCommutator p q (c • Y) = c • hullHeckeCommutator p q Y := by
  change hullHecke p q * (c • Y) - (c • Y) * hullHecke p q =
    c • (hullHecke p q * Y - Y * hullHecke p q)
  rw [mul_smul_comm, smul_mul_assoc, smul_sub]

/-- A mixed observable is a commutator exactly away from the spectral collision or when it vanishes. -/
theorem hullHeckeCommutator_range_iff (q : ℂ) (X : A) :
    (∃ Y, hullHeckeCommutator p q Y = X) ↔
      hullMixedPart p X = X ∧ (q^2 ≠ -1 ∨ X = 0) := by
  constructor
  · rintro ⟨Y, rfl⟩
    refine ⟨hullMixedPart_commutator p q Y, ?_⟩
    by_cases h : q^2 = -1
    · right
      rw [hullHeckeCommutator_eq, h, neg_add_cancel, zero_div, zero_smul]
    · exact Or.inl h
  · rintro ⟨hX, h | rfl⟩
    · have hn : (q^2 + 1)^2 ≠ 0 := pow_ne_zero _ (by simpa only [ne_eq, add_eq_zero_iff_eq_neg] using h)
      refine ⟨((q^2 + 1)^2)⁻¹ • hullHeckeCommutator p q X, ?_⟩
      calc
        _ = ((q^2 + 1)^2)⁻¹ • hullHeckeCommutator p q (hullHeckeCommutator p q X) :=
          commutator_smul p q _ _
        _ = X := by rw [hullHeckeCommutator_square, hX, smul_smul, inv_mul_cancel₀ hn, one_smul]
    · exact ⟨0, by rw [hullHeckeCommutator, mul_zero, zero_mul, sub_self]⟩

#print axioms hullHeckeCommutator_eq
#print axioms hullMixedPart_twice
#print axioms hullMixedPart_zero_iff
#print axioms hullHecke_commute_iff
#print axioms hullHeckeCommutator_square
#print axioms hullHeckeCommutator_square_zero_iff
#print axioms hullMixedPart_commutator
#print axioms hullHeckeCommutator_cubic
#print axioms hullHeckeCommutator_range_iff

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
