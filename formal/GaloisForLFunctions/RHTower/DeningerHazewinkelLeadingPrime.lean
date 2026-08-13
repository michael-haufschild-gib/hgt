import GaloisForLFunctions.HTGeometry.DualRectangularSection
import GaloisForLFunctions.HTGeometry.MvPolynomialGaussAscent
import GaloisForLFunctions.RHTower.DeningerHazewinkelHankelStraightening

/-!
# Primeness of Hazewinkel's leading Hankel determinant

Hazewinkel's saturation argument uses that the leading `n × n` Hankel determinant is prime over
the integers.  This module supplies the omitted proof.

After reversing columns, the determinant is a rectangular Schur--Toeplitz determinant.  Existing
Schur irreducibility over `ℚ` therefore proves primeness after scalar extension.  To descend to
`ℤ`, we prove primitivity without computing coefficients: specialize the universal sequence at
`a₀ = a_{n-1} = 1` and every other coefficient at zero.  The reversed Hankel matrix is upper
triangular with diagonal one, so the determinant specializes to a unit.  Every integer content
divisor must consequently be a unit.  Gauss descent then gives integral irreducibility and hence
primeness.

The unconditional capstone covers every size: for `n ≥ 2` the determinant is prime; at the two
degenerate sizes it is a unit.
-/

namespace RHTower

open MvPolynomial

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

/-- Injective renaming preserves prime multivariate polynomials. -/
theorem deningerMvPolynomial_prime_rename_of_injective
    {R α β : Type*} [CommRing R]
    (f : α → β) (hf : Function.Injective f) {p : MvPolynomial α R} (hp : Prime p) :
    Prime (MvPolynomial.rename f p) := by
  let e : α ≃ Set.range f := Equiv.ofInjective f hf
  have he : MvPolynomial.rename f p =
      MvPolynomial.rename (fun x : Set.range f => x.1)
        (MvPolynomial.rename e p) := by
    rw [MvPolynomial.rename_rename]
    rfl
  rw [he, MvPolynomial.prime_rename_iff]
  exact (MulEquiv.prime_iff (MvPolynomial.renameEquiv R e).toMulEquiv).2 hp

/-- Reverse the finite Schur coordinates into the universal coefficient coordinates. -/
def deningerHazewinkelLeadingRename (L : ℕ) : Fin L → ℕ := fun i => i.rev.val

theorem deningerHazewinkelLeadingRename_injective (L : ℕ) :
    Function.Injective (deningerHazewinkelLeadingRename L) := by
  intro i j h
  apply Fin.rev_injective
  apply Fin.ext
  exact h

/-- Universal Hazewinkel coefficients over `ℚ`. -/
def deningerHazewinkelUniversalCoeffQ : ℕ → MvPolynomial ℕ ℚ
  | 0 => 1
  | s + 1 => MvPolynomial.X s

theorem deningerHazewinkel_rename_schurVar {L s : ℕ} (hs : s ≤ L) :
    MvPolynomial.rename (deningerHazewinkelLeadingRename L)
        (GaloisForLFunctions.HTGeometry.schurVar ℚ L s) =
      deningerHazewinkelUniversalCoeffQ s := by
  rw [GaloisForLFunctions.HTGeometry.schurVar]
  by_cases h0 : s = 0
  · subst s
    simp [deningerHazewinkelUniversalCoeffQ]
  · rw [if_neg h0, dif_pos (by omega : L - s < L), MvPolynomial.rename_X]
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    rw [deningerHazewinkelUniversalCoeffQ]
    congr 1
    simp [deningerHazewinkelLeadingRename]
    omega

/-- Rectangular Schur determinant corresponding to the leading Hankel determinant. -/
def deningerHazewinkelSchurLeading (n : ℕ) :
    MvPolynomial (Fin (2 * n - 2)) ℚ :=
  (GaloisForLFunctions.HTGeometry.rectangularSchurToeplitz
    (GaloisForLFunctions.HTGeometry.schurVar ℚ (2 * n - 2)) (n - 1) n).det

theorem deningerHazewinkelSchurLeading_prime (n : ℕ) (hn : 2 ≤ n) :
    Prime (deningerHazewinkelSchurLeading n) := by
  let hL : n - 1 + n - 1 = 2 * n - 2 := by omega
  have hp : Prime
      ((GaloisForLFunctions.HTGeometry.rectangularSchurToeplitz
        (GaloisForLFunctions.HTGeometry.schurVar ℚ (n - 1 + n - 1)) (n - 1) n).det) :=
    (GaloisForLFunctions.HTGeometry.irreducible_det_rectangularSchurToeplitz
      (K := ℚ) (n := n - 1) (m := n) (by omega) (by omega)).prime
  have hpmap : Prime (MvPolynomial.rename (finCongr hL)
      ((GaloisForLFunctions.HTGeometry.rectangularSchurToeplitz
        (GaloisForLFunctions.HTGeometry.schurVar ℚ (n - 1 + n - 1)) (n - 1) n).det)) :=
    (MulEquiv.prime_iff (MvPolynomial.renameEquiv ℚ (finCongr hL)).toMulEquiv).2 hp
  rw [GaloisForLFunctions.HTGeometry.rename_finCongr_det_rectangularSchurToeplitz]
    at hpmap
  exact hpmap

/-- Leading Hankel determinant after scalar extension to `ℚ`. -/
def deningerHazewinkelLeadingQ (n : ℕ) : MvPolynomial ℕ ℚ :=
  Matrix.det fun i j : Fin n => deningerHazewinkelUniversalCoeffQ (i.val + j.val)

theorem deningerHazewinkelLeadingQ_eq_sign_mul_rename_schurLeading
    (n : ℕ) (hn : 2 ≤ n) :
    deningerHazewinkelLeadingQ n =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) :
        MvPolynomial ℕ ℚ) *
      MvPolynomial.rename (deningerHazewinkelLeadingRename (2 * n - 2))
        (deningerHazewinkelSchurLeading n) := by
  let M : Matrix (Fin n) (Fin n) (MvPolynomial ℕ ℚ) :=
    (MvPolynomial.rename (deningerHazewinkelLeadingRename (2 * n - 2))).mapMatrix
      (GaloisForLFunctions.HTGeometry.rectangularSchurToeplitz
        (GaloisForLFunctions.HTGeometry.schurVar ℚ (2 * n - 2)) (n - 1) n)
  have hM : (fun i j : Fin n => deningerHazewinkelUniversalCoeffQ (i.val + j.val)) =
      M.submatrix id Fin.revPerm := by
    apply Matrix.ext
    intro i j
    change deningerHazewinkelUniversalCoeffQ (i.val + j.val) =
      MvPolynomial.rename (deningerHazewinkelLeadingRename (2 * n - 2))
        (if (Fin.rev j : ℕ) ≤ n - 1 + (i : ℕ) then
          GaloisForLFunctions.HTGeometry.schurVar ℚ (2 * n - 2)
            (n - 1 + (i : ℕ) - (Fin.rev j : ℕ)) else 0)
    rw [if_pos (by omega : (Fin.rev j : ℕ) ≤ n - 1 + (i : ℕ))]
    rw [deningerHazewinkel_rename_schurVar
      (by omega : n - 1 + (i : ℕ) - (Fin.rev j : ℕ) ≤ 2 * n - 2)]
    congr 1
    simp
    omega
  rw [deningerHazewinkelLeadingQ, hM, Matrix.det_permute']
  congr 1
  rw [deningerHazewinkelSchurLeading]
  exact ((MvPolynomial.rename (R := ℚ)
    (deningerHazewinkelLeadingRename (2 * n - 2))).map_det
      (GaloisForLFunctions.HTGeometry.rectangularSchurToeplitz
        (GaloisForLFunctions.HTGeometry.schurVar ℚ (2 * n - 2)) (n - 1) n)).symm

theorem deningerHazewinkelLeadingQ_prime (n : ℕ) (hn : 2 ≤ n) :
    Prime (deningerHazewinkelLeadingQ n) := by
  rw [deningerHazewinkelLeadingQ_eq_sign_mul_rename_schurLeading n hn]
  let u : (MvPolynomial ℕ ℚ)ˣ := Units.map
    (MvPolynomial.C : ℚ →+* MvPolynomial ℕ ℚ)
    (Units.map (Int.castRingHom ℚ).toMonoidHom
      (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))))
  have hu : (u : MvPolynomial ℕ ℚ) =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) :
        MvPolynomial ℕ ℚ) := by rfl
  rw [← hu, prime_units_mul]
  exact deningerMvPolynomial_prime_rename_of_injective _
    (deningerHazewinkelLeadingRename_injective _)
    (deningerHazewinkelSchurLeading_prime n hn)

theorem deningerHazewinkel_map_universalCoeff (s : ℕ) :
    MvPolynomial.map (Int.castRingHom ℚ) (deningerHazewinkelUniversalCoeff s) =
      deningerHazewinkelUniversalCoeffQ s := by
  cases s <;>
    simp [deningerHazewinkelUniversalCoeff, deningerHazewinkelUniversalCoeffQ]

theorem deningerHazewinkel_map_leading_eq_leadingQ (n : ℕ) :
    MvPolynomial.map (Int.castRingHom ℚ) (deningerHazewinkelLeadingDeterminant n) =
      deningerHazewinkelLeadingQ n := by
  rw [deningerHazewinkelLeadingDeterminant]
  change MvPolynomial.map (Int.castRingHom ℚ)
      ((Matrix.of fun i j : Fin n =>
        deningerHazewinkelUniversalCoeff (i.val + j.val)).det) =
    deningerHazewinkelLeadingQ n
  rw [(MvPolynomial.map (σ := ℕ) (Int.castRingHom ℚ)).map_det,
    deningerHazewinkelLeadingQ]
  congr 1
  funext i j
  exact deningerHazewinkel_map_universalCoeff _

/-- Integer specialization used to certify content one. -/
def deningerHazewinkelAntiDiagonalEval (n : ℕ) : MvPolynomial ℕ ℤ →+* ℤ :=
  MvPolynomial.eval₂Hom (RingHom.id ℤ) fun k => if k + 1 = n - 1 then 1 else 0

theorem deningerHazewinkelAntiDiagonalEval_coeff (n s : ℕ) :
    deningerHazewinkelAntiDiagonalEval n (deningerHazewinkelUniversalCoeff s) =
      if s = 0 ∨ s = n - 1 then 1 else 0 := by
  cases s <;>
    simp [deningerHazewinkelAntiDiagonalEval, deningerHazewinkelUniversalCoeff]

theorem deningerHazewinkelAntiDiagonalEval_leading_isUnit
    (n : ℕ) (hn : 2 ≤ n) :
    IsUnit (deningerHazewinkelAntiDiagonalEval n
      (deningerHazewinkelLeadingDeterminant n)) := by
  let H : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    deningerHazewinkelAntiDiagonalEval n
      (deningerHazewinkelUniversalCoeff (i.val + j.val))
  let M := H.submatrix id Fin.revPerm
  have hupper : ∀ i j : Fin n, j < i → M i j = 0 := by
    intro i j hji
    change deningerHazewinkelAntiDiagonalEval n
      (deningerHazewinkelUniversalCoeff (i.val + (Fin.rev j).val)) = 0
    rw [deningerHazewinkelAntiDiagonalEval_coeff]
    split_ifs with h
    · rcases h with h | h <;> simp at h <;> omega
    · rfl
  have hdiag : ∀ i : Fin n, M i i = 1 := by
    intro i
    change deningerHazewinkelAntiDiagonalEval n
      (deningerHazewinkelUniversalCoeff (i.val + (Fin.rev i).val)) = 1
    rw [deningerHazewinkelAntiDiagonalEval_coeff, if_pos]
    exact Or.inr (by simp; omega)
  have hdetM : M.det = 1 := by
    rw [Matrix.det_of_upperTriangular hupper]
    exact Finset.prod_eq_one fun i hi => hdiag i
  have hmap : deningerHazewinkelAntiDiagonalEval n
      (deningerHazewinkelLeadingDeterminant n) = H.det := by
    rw [deningerHazewinkelLeadingDeterminant]
    change deningerHazewinkelAntiDiagonalEval n
        ((Matrix.of fun i j : Fin n =>
          deningerHazewinkelUniversalCoeff (i.val + j.val)).det) = H.det
    rw [(deningerHazewinkelAntiDiagonalEval n).map_det]
    congr 1
  have hperm := Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin n)) H
  change M.det = _ at hperm
  rw [hdetM] at hperm
  rw [hmap]
  refine ⟨⟨H.det,
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ)), ?_, ?_⟩, rfl⟩
  · rw [mul_comm]
    simpa using hperm.symm
  · simpa using hperm.symm

theorem deningerHazewinkelLeadingDeterminant_primitive
    (n : ℕ) (hn : 2 ≤ n) :
    GaloisForLFunctions.MvPolynomialPrimitive
      (deningerHazewinkelLeadingDeterminant n) := by
  intro r hr
  have hdvd := map_dvd (deningerHazewinkelAntiDiagonalEval n) hr
  exact isUnit_of_dvd_unit
    (by simpa [deningerHazewinkelAntiDiagonalEval] using hdvd)
    (deningerHazewinkelAntiDiagonalEval_leading_isUnit n hn)

/-- Gauss descent from fraction-field irreducibility, specialized to integer multivariate
polynomials. -/
theorem deningerMvPolynomial_irreducible_of_primitive_and_map_irreducible
    {σ : Type*} {P : MvPolynomial σ ℤ}
    (hprim : GaloisForLFunctions.MvPolynomialPrimitive P)
    (hirr : Irreducible (MvPolynomial.map (Int.castRingHom ℚ) P)) :
    Irreducible P := by
  refine ⟨?_, ?_⟩
  · intro hunit
    exact hirr.not_isUnit (hunit.map (MvPolynomial.map (Int.castRingHom ℚ)))
  · intro a b hab
    have habQ : MvPolynomial.map (Int.castRingHom ℚ) P =
        MvPolynomial.map (Int.castRingHom ℚ) a *
          MvPolynomial.map (Int.castRingHom ℚ) b := by rw [← map_mul, hab]
    rcases hirr.isUnit_or_isUnit habQ with ha | hb
    · left
      obtain ⟨u, hu, haC⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp ha
      have haconst := GaloisForLFunctions.eq_C_of_map_eq_C haC
      rw [haconst]
      apply IsUnit.map MvPolynomial.C
      apply hprim
      rw [← haconst]
      exact ⟨b, hab⟩
    · right
      obtain ⟨u, hu, hbC⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hb
      have hbconst := GaloisForLFunctions.eq_C_of_map_eq_C hbC
      rw [hbconst]
      apply IsUnit.map MvPolynomial.C
      apply hprim
      rw [← hbconst]
      exact ⟨a, by rw [mul_comm]; exact hab⟩

/-- For every nondegenerate size, the integral leading Hankel determinant is prime. -/
theorem deningerHazewinkelLeadingDeterminant_prime_of_two_le
    (n : ℕ) (hn : 2 ≤ n) :
    Prime (deningerHazewinkelLeadingDeterminant n) := by
  apply Irreducible.prime
  apply deningerMvPolynomial_irreducible_of_primitive_and_map_irreducible
    (deningerHazewinkelLeadingDeterminant_primitive n hn)
  rw [deningerHazewinkel_map_leading_eq_leadingQ]
  exact (deningerHazewinkelLeadingQ_prime n hn).irreducible

/-- Unconditional integral classification: each leading determinant is prime or a unit.

This statement has no mathematical premises.  The prime branch holds at every `n ≥ 2`; the unit
branch is exactly the degenerate sizes `0` and `1`. -/
theorem deningerHazewinkelLeadingDeterminant_prime_or_isUnit (n : ℕ) :
    Prime (deningerHazewinkelLeadingDeterminant n) ∨
      IsUnit (deningerHazewinkelLeadingDeterminant n) := by
  by_cases hn : 2 ≤ n
  · exact Or.inl (deningerHazewinkelLeadingDeterminant_prime_of_two_le n hn)
  · have hn' : n ≤ 1 := by omega
    interval_cases n <;>
      simp [deningerHazewinkelLeadingDeterminant, deningerHazewinkelUniversalCoeff]

end
end RHTower
