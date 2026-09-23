import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic

/-!
# Nonlinear addition from the integer theta lattice

The rotation of the integer square lattice splits into two disjoint sectors,
with integer and half-integer output frequencies. Their Gaussian atoms obey
exact product identities. Absolute convergence then gives the analytic
Jacobi theta addition law, including both sectors and arbitrary complex
spatial arguments, throughout the upper half-plane.

This is the classical theta addition mechanism (see DLMF 20.7), not a
zero-selection theorem. No zeta divisor or deformation hypothesis is used.
The coefficient-space rigidity statement is separate from this analytic law;
Fourier-coefficient extraction is not asserted here.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- The two parity sectors of the integer square lattice. -/
def thetaLatticeParityEquiv : (ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun := Sum.elim (fun p => (p.1 + p.2, p.1 - p.2))
    (fun p => (p.1 + p.2 + 1, p.1 - p.2))
  invFun := fun p => if (p.1 + p.2) % 2 = 0 then
    Sum.inl ((p.1 + p.2) / 2, (p.1 - p.2) / 2)
    else Sum.inr ((p.1 + p.2 - 1) / 2, (p.1 - p.2 - 1) / 2)
  left_inv := by
    rintro (⟨i, j⟩ | ⟨i, j⟩)
    · simp only [Sum.elim_inl]
      rw [if_pos (by omega)]
      congr 2 <;> omega
    · simp only [Sum.elim_inr]
      rw [if_neg (by omega)]
      congr 2 <;> omega
  right_inv := by
    rintro ⟨m, n⟩
    dsimp only
    split <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> ext <;> omega

/-- A Gaussian theta atom at an arbitrary complex frequency. -/
def thetaLatticeAtom (q z τ : ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * I * q * z + Real.pi * I * q ^ (2 : ℕ) * τ)

/-- The half-integer-frequency sector, with its Gaussian coefficients unchanged. -/
def thetaLatticeHalf (z τ : ℂ) : ℂ :=
  ∑' n : ℤ, thetaLatticeAtom ((n : ℂ) + 1 / 2) z τ

theorem thetaLatticeHalf_atom_shift (n : ℤ) (z τ : ℂ) :
    thetaLatticeAtom ((n : ℂ) + 1 / 2) z τ =
      Complex.exp (Real.pi * I * z + Real.pi * I * τ / 4) *
        jacobiTheta₂_term n (z + τ / 2) τ := by
  unfold thetaLatticeAtom jacobiTheta₂_term
  rw [← Complex.exp_add]
  congr 1
  ring

theorem thetaLatticeHalf_eq_shift (z τ : ℂ) :
    thetaLatticeHalf z τ =
      Complex.exp (Real.pi * I * z + Real.pi * I * τ / 4) *
        jacobiTheta₂ (z + τ / 2) τ := by
  simp only [thetaLatticeHalf, thetaLatticeHalf_atom_shift, tsum_mul_left, jacobiTheta₂]

theorem summable_thetaLatticeHalf (z : ℂ) (τ : UpperHalfPlane) :
    Summable (fun n : ℤ => thetaLatticeAtom ((n : ℂ) + 1 / 2) z τ) := by
  simp_rw [thetaLatticeHalf_atom_shift]
  exact ((summable_jacobiTheta₂_term_iff (z + (τ : ℂ) / 2) τ).mpr
    τ.im_pos).mul_left _

/-- Exact atom identity on the even sector of the rotated square lattice. -/
theorem thetaLattice_integer_atom_sewing (i j : ℤ) (z w τ : ℂ) :
    jacobiTheta₂_term (i + j) (z + w) τ *
        jacobiTheta₂_term (i - j) (z - w) τ =
      jacobiTheta₂_term i (2 * z) (2 * τ) *
        jacobiTheta₂_term j (2 * w) (2 * τ) := by
  unfold jacobiTheta₂_term
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact atom identity on the odd sector; neither half-integer leg may be omitted. -/
theorem thetaLattice_half_atom_sewing (i j : ℤ) (z w τ : ℂ) :
    jacobiTheta₂_term (i + j + 1) (z + w) τ *
        jacobiTheta₂_term (i - j) (z - w) τ =
      thetaLatticeAtom ((i : ℂ) + 1 / 2) (2 * z) (2 * τ) *
        thetaLatticeAtom ((j : ℂ) + 1 / 2) (2 * w) (2 * τ) := by
  unfold jacobiTheta₂_term thetaLatticeAtom
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem thetaLattice_integer_product_hasSum (z w : ℂ) (τ : UpperHalfPlane) :
    HasSum (fun p : ℤ × ℤ => jacobiTheta₂_term p.1 z τ * jacobiTheta₂_term p.2 w τ)
      (jacobiTheta₂ z τ * jacobiTheta₂ w τ) := by
  have hz := (summable_jacobiTheta₂_term_iff z τ).mpr τ.im_pos
  have hw := (summable_jacobiTheta₂_term_iff w τ).mpr τ.im_pos
  have hnz : Summable (fun n : ℤ => ‖jacobiTheta₂_term n z τ‖) := hz.norm
  have hnw : Summable (fun n : ℤ => ‖jacobiTheta₂_term n w τ‖) := hw.norm
  have hp : Summable (fun p : ℤ × ℤ =>
      jacobiTheta₂_term p.1 z τ * jacobiTheta₂_term p.2 w τ) :=
    summable_mul_of_summable_norm (f := fun n : ℤ => jacobiTheta₂_term n z τ)
      (g := fun n : ℤ => jacobiTheta₂_term n w τ) hnz hnw
  exact HasSum.mul (f := fun n : ℤ => jacobiTheta₂_term n z τ)
    (g := fun n : ℤ => jacobiTheta₂_term n w τ)
    (hasSum_jacobiTheta₂_term z τ.im_pos) (hasSum_jacobiTheta₂_term w τ.im_pos) hp

private theorem thetaLattice_half_product_hasSum (z w : ℂ) (τ : UpperHalfPlane) :
    HasSum (fun p : ℤ × ℤ =>
      thetaLatticeAtom ((p.1 : ℂ) + 1 / 2) z τ *
        thetaLatticeAtom ((p.2 : ℂ) + 1 / 2) w τ)
      (thetaLatticeHalf z τ * thetaLatticeHalf w τ) := by
  have hz := summable_thetaLatticeHalf z τ
  have hw := summable_thetaLatticeHalf w τ
  have hnz : Summable (fun n : ℤ => ‖thetaLatticeAtom ((n : ℂ) + 1 / 2) z τ‖) := hz.norm
  have hnw : Summable (fun n : ℤ => ‖thetaLatticeAtom ((n : ℂ) + 1 / 2) w τ‖) := hw.norm
  have hp : Summable (fun p : ℤ × ℤ =>
      thetaLatticeAtom ((p.1 : ℂ) + 1 / 2) z τ *
        thetaLatticeAtom ((p.2 : ℂ) + 1 / 2) w τ) :=
    summable_mul_of_summable_norm (f := fun n : ℤ => thetaLatticeAtom ((n : ℂ) + 1 / 2) z τ)
      (g := fun n : ℤ => thetaLatticeAtom ((n : ℂ) + 1 / 2) w τ) hnz hnw
  exact HasSum.mul (f := fun n : ℤ => thetaLatticeAtom ((n : ℂ) + 1 / 2) z τ)
    (g := fun n : ℤ => thetaLatticeAtom ((n : ℂ) + 1 / 2) w τ) hz.hasSum hw.hasSum hp

/-- The nonlinear addition law comes from a bijection of the literal integer lattice.
All rearrangements are of absolutely convergent series. -/
theorem thetaLattice_addition (z w : ℂ) (τ : UpperHalfPlane) :
    jacobiTheta₂ (z + w) τ * jacobiTheta₂ (z - w) τ =
      jacobiTheta₂ (2 * z) (2 * (τ : ℂ)) * jacobiTheta₂ (2 * w) (2 * (τ : ℂ)) +
        thetaLatticeHalf (2 * z) (2 * (τ : ℂ)) *
          thetaLatticeHalf (2 * w) (2 * (τ : ℂ)) := by
  let τ₂ : UpperHalfPlane := ⟨2 * (τ : ℂ), by
    simpa using mul_pos (by norm_num : (0 : ℝ) < 2) τ.im_pos⟩
  let f : ℤ × ℤ → ℂ := fun p =>
    jacobiTheta₂_term p.1 (z + w) τ * jacobiTheta₂_term p.2 (z - w) τ
  have hf : HasSum f (jacobiTheta₂ (z + w) τ * jacobiTheta₂ (z - w) τ) :=
    thetaLattice_integer_product_hasSum (z + w) (z - w) τ
  have he : HasSum ((f ∘ thetaLatticeParityEquiv) ∘ Sum.inl)
      (jacobiTheta₂ (2 * z) (2 * (τ : ℂ)) *
        jacobiTheta₂ (2 * w) (2 * (τ : ℂ))) := by
    change HasSum (fun p : ℤ × ℤ =>
      jacobiTheta₂_term (p.1 + p.2) (z + w) τ *
        jacobiTheta₂_term (p.1 - p.2) (z - w) τ) _
    exact (thetaLattice_integer_product_hasSum (2 * z) (2 * w) τ₂).congr_fun
      (fun p => thetaLattice_integer_atom_sewing p.1 p.2 z w τ)
  have ho : HasSum ((f ∘ thetaLatticeParityEquiv) ∘ Sum.inr)
      (thetaLatticeHalf (2 * z) (2 * (τ : ℂ)) *
        thetaLatticeHalf (2 * w) (2 * (τ : ℂ))) := by
    change HasSum (fun p : ℤ × ℤ =>
      jacobiTheta₂_term (p.1 + p.2 + 1) (z + w) τ *
        jacobiTheta₂_term (p.1 - p.2) (z - w) τ) _
    exact (thetaLattice_half_product_hasSum (2 * z) (2 * w) τ₂).congr_fun
      (fun p => thetaLattice_half_atom_sewing p.1 p.2 z w τ)
  calc
    _ = ∑' p, f p := hf.tsum_eq.symm
    _ = ∑' p, f (thetaLatticeParityEquiv p) :=
      (thetaLatticeParityEquiv.tsum_eq f).symm
    _ = _ := (HasSum.sum (f := f ∘ thetaLatticeParityEquiv) he ho).tsum_eq

/-- Duplication retains both parity sectors of the actual theta function. -/
theorem thetaLattice_duplication (z : ℂ) (τ : UpperHalfPlane) :
    jacobiTheta₂ z τ ^ (2 : ℕ) =
      jacobiTheta₂ (2 * z) (2 * (τ : ℂ)) * jacobiTheta₂ 0 (2 * (τ : ℂ)) +
        thetaLatticeHalf (2 * z) (2 * (τ : ℂ)) *
          thetaLatticeHalf 0 (2 * (τ : ℂ)) := by
  simpa only [add_zero, sub_zero, mul_zero, pow_two] using thetaLattice_addition z 0 τ

end GaloisForLFunctions.HTGeometry

