import GaloisForLFunctions.HTGeometry.ToricIsogenyTailLaw
import GaloisForLFunctions.HTGeometry.TorusDiagonalDeck

/-!
# Coordinatewise expanding diagonal torus tails

An autonomous diagonal torus isogeny may use a different degree in every coordinate.  If every
degree is at least two, its iterated deck groups separate all character vectors.  The stable tail
is therefore exactly the logarithmic-velocity field, and each velocity transforms with its own
coordinate degree.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u

/-- Character matrix of a coordinatewise power isogeny. -/
def diagonalPowerMatrix (r : ℕ) (D : Fin r → ℕ) : Matrix (Fin r) (Fin r) ℤ :=
  Matrix.diagonal fun i => (D i : ℤ)

/-- A constant diagonal protocol accumulates the coordinatewise powers. -/
theorem prefixMatrix_const_diagonalPowerMatrix {r : ℕ} (D : Fin r → ℕ) (i n : ℕ) :
    prefixMatrix (fun _ => diagonalPowerMatrix r D) i n =
      Matrix.diagonal fun k => ((D k) ^ n : ℤ) := by
  induction n generalizing i with
  | zero =>
      rw [prefixMatrix_zero]
      simp
  | succ n ih =>
      rw [prefixMatrix_succ, ih (i + 1), diagonalPowerMatrix,
        Matrix.diagonal_mul_diagonal]
      simp [pow_succ]

/-- Every coordinatewise expanding diagonal matrix is nonsingular. -/
theorem det_diagonalPowerMatrix_ne_zero {r : ℕ} {D : Fin r → ℕ}
    (hD : ∀ i, 2 ≤ D i) : (diagonalPowerMatrix r D).det ≠ 0 := by
  rw [diagonalPowerMatrix, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    Int.natCast_ne_zero.mpr (by have hi := hD i; omega)

/-- Iterated deck kernels of a coordinatewise expanding diagonal isogeny separate every pair of
distinct torus characters. -/
theorem diagonalPowerProtocol_separates
    {C : Type u} [Field C] [IsAlgClosed C] [CharZero C] {r : ℕ}
    {D : Fin r → ℕ} (hD : ∀ i, 2 ≤ D i) (e d : Fin r →₀ ℕ)
    (h : ∀ u ∈ erasedSector
        (torusProtocolGroup C fun _ => diagonalPowerMatrix r D) 0,
      (∏ k, ((u k : C)) ^ e k) = ∏ k, ((u k : C)) ^ d k) :
    e = d := by
  classical
  ext k
  by_contra hk
  let B := max (e k) (d k)
  have hpow : 2 ^ B ≤ (D k) ^ B := Nat.pow_le_pow_left (hD k) B
  have hn : B < (D k) ^ B := (Nat.lt_two_pow_self).trans_le hpow
  set N : ℕ := (D k) ^ B with hN
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hn
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosed C hNpos
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hNpos.ne'
  set u : Fin r → Cˣ := fun l => if l = k then Units.mk0 ζ hζ0 else 1 with hu
  have hmemker : u ∈ (torusPowerHom C (fun l : Fin r => (((D l) ^ B : ℕ) : ℤ))).ker := by
    rw [mem_ker_torusPowerHom_iff]
    intro l
    by_cases hl : l = k
    · subst l
      apply Units.ext
      simp only [hu, if_pos rfl, Units.val_one, zpow_natCast]
      exact hζ.pow_eq_one
    · simp [hu, if_neg hl]
  have hmem : u ∈ erasedSector
      (torusProtocolGroup C fun _ => diagonalPowerMatrix r D) 0 := by
    rw [mem_erasedSector_iff]
    refine ⟨B, ?_⟩
    rw [prefixHom_torusProtocolGroup,
      prefixMatrix_const_diagonalPowerMatrix D 0 B, torusMonomialHom_diagonal]
    exact hmemker
  have hval := h u hmem
  have hprod : ∀ g : Fin r →₀ ℕ, (∏ l, ((u l : C)) ^ g l) = ζ ^ g k := by
    intro g
    rw [Finset.prod_eq_single k]
    · simp only [hu, if_pos rfl, Units.val_mk0]
    · intro l _ hlk
      simp only [hu, if_neg hlk, Units.val_one, one_pow]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  rw [hprod e, hprod d] at hval
  exact hk (hζ.pow_inj (lt_of_le_of_lt (le_max_left _ _) hn)
    (lt_of_le_of_lt (le_max_right _ _) hn) hval)

section Tail

variable {C E : Type u} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E] [CharZero E] [CharZero C] [IsAlgClosed C]

variable {r : ℕ} {x : Fin r → E} (hx : DifferentialIndependent C x)
  (hgen : differentialAdjoin C (Set.range x) = ⊤)

/-- The stable tail of a coordinatewise expanding diagonal torus isogeny is exactly its velocity
field. -/
theorem torusDiagonalEndo_stableRangeCore_eq_torusVelocityField
    (hconst : ∀ c : C, c′ = 0) {D : Fin r → ℕ} (hD : ∀ i, 2 ≤ D i) :
    stableRangeCore (torusEndo hx hgen (det_diagonalPowerMatrix_ne_zero hD)) =
      torusVelocityField C x := by
  apply torusEndo_stableRangeCore_eq_torusVelocityField hx hgen hconst
    (det_diagonalPowerMatrix_ne_zero hD)
  exact diagonalPowerProtocol_separates hD

omit [CharZero C] [IsAlgClosed C] in
/-- A coordinatewise diagonal isogeny scales each logarithmic velocity by its own degree. -/
theorem torusDiagonalEndo_logDeriv {D : Fin r → ℕ} (hD : ∀ i, 2 ≤ D i) (i : Fin r) :
    torusEndo hx hgen (det_diagonalPowerMatrix_ne_zero hD)
        (Differential.logDeriv (x i)) =
      (D i : E) * Differential.logDeriv (x i) := by
  rw [torusEndo_logDeriv hx hgen (det_diagonalPowerMatrix_ne_zero hD) i]
  rw [Finset.sum_eq_single i]
  · rw [diagonalPowerMatrix, Matrix.diagonal_apply_eq]
    norm_cast
  · intro j _ hji
    rw [diagonalPowerMatrix, Matrix.diagonal_apply_ne _ (Ne.symm hji)]
    norm_num
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Coordinatewise expanding diagonal version of the toric position-to-velocity transmutation
law. -/
theorem toricDiagonalIsogenyTail (hconst : ∀ c : C, c′ = 0)
    {D : Fin r → ℕ} (hD : ∀ i, 2 ≤ D i) :
    stableRangeCore (torusEndo hx hgen (det_diagonalPowerMatrix_ne_zero hD)) =
        torusVelocityField C x
      ∧ DifferentialIndependent C (fun k => Differential.logDeriv (x k))
      ∧ torusVelocityField C x ⊓ IntermediateField.adjoin C (Set.range x) =
          (⊥ : IntermediateField C E)
      ∧ ∀ i, torusEndo hx hgen (det_diagonalPowerMatrix_ne_zero hD)
          (Differential.logDeriv (x i)) =
            (D i : E) * Differential.logDeriv (x i) :=
  ⟨torusDiagonalEndo_stableRangeCore_eq_torusVelocityField hx hgen hconst hD,
    differentialIndependent_logDeriv hx,
    torusVelocityField_inf_adjoin_eq_bot hx hgen hconst,
    torusDiagonalEndo_logDeriv hx hgen hD⟩

end Tail

end

end GaloisForLFunctions.HTGeometry
