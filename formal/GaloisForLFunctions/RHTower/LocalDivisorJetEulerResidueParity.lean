import GaloisForLFunctions.RHTower.SymplecticMultiplicity
import Mathlib.Data.Fin.Rev

/-!
# Euler--residue parity on a local divisor jet

For the length-`m` local algebra `ℂ[t]/(t^m)`, identify the monomial basis with
`Fin m → ℂ`.  Frobenius residue pairs `t^i` with `t^(m - 1 - i)`.  Commuting one input
with the Euler operator `t d/dt` and antisymmetrising gives the canonical form

`ω_m(t^i, t^j) = (j - i)` when `i + j = m - 1`, and zero otherwise.

Its anti-diagonal coefficient at `i` is `m - 1 - 2i`.  Consequently `ω_m` is
nondegenerate exactly when `m` is even.  For `m = 2r + 1`, the middle monomial `t^r`
lies in the radical.

Applied to the local divisor jet of ξ at a zero, nondegeneracy of this canonical form is
equivalent to the base multiplicity-parity rung.  Thus Euler--residue/Kramers language gives
an exact local detector, but not an independent source of parity: proving nondegeneracy is
precisely the missing RH-bearing statement.
-/

open Complex Module

namespace RHTower

/-- Anti-diagonal Euler--residue coefficient on the `i`th local divisor jet coordinate. -/
noncomputable def localDivisorJetEulerCoefficient (m : ℕ) (i : Fin m) : ℂ :=
  (i.rev.val : ℂ) - (i.val : ℂ)

/-- Matrix of the Euler--residue form in the local monomial basis. -/
noncomputable def localDivisorJetEulerResidueMatrix (m : ℕ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if j = i.rev then localDivisorJetEulerCoefficient m i else 0

/-- Canonical alternating Euler--residue form on the length-`m` local divisor jet. -/
noncomputable def localDivisorJetEulerResidueForm (m : ℕ) :
    LinearMap.BilinForm ℂ (Fin m → ℂ) :=
  Matrix.toBilin' (localDivisorJetEulerResidueMatrix m)

@[simp] theorem localDivisorJetEulerCoefficient_rev (m : ℕ) (i : Fin m) :
    localDivisorJetEulerCoefficient m i.rev = -localDivisorJetEulerCoefficient m i := by
  simp [localDivisorJetEulerCoefficient]

/-- Even jet length removes every zero anti-diagonal coefficient. -/
theorem localDivisorJetEulerCoefficient_ne_zero_of_even {m : ℕ} (hm : Even m)
    (i : Fin m) : localDivisorJetEulerCoefficient m i ≠ 0 := by
  intro hzero
  have hcast : (i.rev.val : ℂ) = (i.val : ℂ) := sub_eq_zero.mp hzero
  have hval : i.rev.val = i.val := Nat.cast_injective hcast
  simp only [Fin.rev] at hval
  obtain ⟨k, hk⟩ := hm
  omega

@[simp] theorem localDivisorJetEulerResidueForm_single (m : ℕ) (i j : Fin m) :
    localDivisorJetEulerResidueForm m (Pi.single i 1) (Pi.single j 1) =
      localDivisorJetEulerResidueMatrix m i j := by
  simp [localDivisorJetEulerResidueForm]

/-- Coordinate formula for the canonical form. -/
theorem localDivisorJetEulerResidueForm_apply (m : ℕ) (x y : Fin m → ℂ) :
    localDivisorJetEulerResidueForm m x y =
      ∑ i, x i * localDivisorJetEulerCoefficient m i * y i.rev := by
  rw [localDivisorJetEulerResidueForm, Matrix.toBilin'_apply]
  simp [localDivisorJetEulerResidueMatrix]

/-- Testing against the reversed coordinate vector reads one weighted coordinate. -/
theorem localDivisorJetEulerResidueForm_apply_single_rev (m : ℕ) (x : Fin m → ℂ)
    (i : Fin m) :
    localDivisorJetEulerResidueForm m x (Pi.single i.rev 1) =
      localDivisorJetEulerCoefficient m i * x i := by
  rw [localDivisorJetEulerResidueForm, Matrix.toBilin'_apply]
  simp [localDivisorJetEulerResidueMatrix, Pi.single_apply, Fin.rev_eq_iff]
  ring

/-- Euler--residue form is alternating at every jet length. -/
theorem localDivisorJetEulerResidueForm_isAlt (m : ℕ) :
    (localDivisorJetEulerResidueForm m).IsAlt := by
  apply LinearMap.isAlt_iff_eq_neg_flip.mpr
  apply LinearMap.BilinForm.toMatrix'.injective
  ext i j
  simp only [localDivisorJetEulerResidueForm, LinearMap.BilinForm.toMatrix'_apply,
    LinearMap.neg_apply, LinearMap.flip_apply, Matrix.toBilin'_single]
  change localDivisorJetEulerResidueMatrix m i j =
    -localDivisorJetEulerResidueMatrix m j i
  have hiff : j = i.rev ↔ i = j.rev := by
    constructor
    · intro h
      subst j
      simp
    · intro h
      subst i
      simp
  by_cases h : j = i.rev
  · have h' : i = j.rev := hiff.mp h
    subst j
    simp [localDivisorJetEulerResidueMatrix]
  · have h' : i ≠ j.rev := fun hij => h (hiff.mpr hij)
    simp [localDivisorJetEulerResidueMatrix, h, h']

/-- Constructive direction: even jet length makes Euler--residue pairing nondegenerate. -/
theorem localDivisorJetEulerResidueForm_nondegenerate_of_even {m : ℕ} (hm : Even m) :
    (localDivisorJetEulerResidueForm m).Nondegenerate := by
  refine (localDivisorJetEulerResidueForm_isAlt m).isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  intro x hx
  funext i
  have h := hx (Pi.single i.rev 1)
  rw [localDivisorJetEulerResidueForm_apply_single_rev] at h
  exact (mul_eq_zero.mp h).resolve_left
    (localDivisorJetEulerCoefficient_ne_zero_of_even hm i)

/-- Exact local classification: canonical Euler--residue pairing is nondegenerate iff jet
length is even. -/
theorem localDivisorJetEulerResidueForm_nondegenerate_iff_even (m : ℕ) :
    (localDivisorJetEulerResidueForm m).Nondegenerate ↔ Even m := by
  constructor
  · intro hnd
    simpa using even_finrank_of_nondegenerate_isAlt hnd
      (localDivisorJetEulerResidueForm_isAlt m)
  · exact localDivisorJetEulerResidueForm_nondegenerate_of_even

/-- Middle coordinate of an odd-length local divisor jet. -/
def localDivisorJetMiddle (r : ℕ) : Fin (2 * r + 1) := ⟨r, by omega⟩

@[simp] theorem localDivisorJetEulerCoefficient_middle (r : ℕ) :
    localDivisorJetEulerCoefficient (2 * r + 1) (localDivisorJetMiddle r) = 0 := by
  simp [localDivisorJetEulerCoefficient, localDivisorJetMiddle, Fin.rev,
    show 2 * r - r = r by omega]

/-- Odd jet length has a concrete radical vector: its middle monomial. -/
theorem localDivisorJetEulerResidueForm_middle_mem_leftRadical (r : ℕ) :
    ∀ y, localDivisorJetEulerResidueForm (2 * r + 1)
      (Pi.single (localDivisorJetMiddle r) 1) y = 0 := by
  intro y
  rw [localDivisorJetEulerResidueForm_apply]
  simp [Pi.single_apply, localDivisorJetEulerCoefficient_middle]

/-- Away from the middle coordinate, every odd-length anti-diagonal coefficient is nonzero. -/
theorem localDivisorJetEulerCoefficient_ne_zero_of_ne_middle (r : ℕ)
    (i : Fin (2 * r + 1)) (hi : i ≠ localDivisorJetMiddle r) :
    localDivisorJetEulerCoefficient (2 * r + 1) i ≠ 0 := by
  intro hzero
  have hcast : (i.rev.val : ℂ) = (i.val : ℂ) := sub_eq_zero.mp hzero
  have hval : i.rev.val = i.val := Nat.cast_injective hcast
  simp only [Fin.rev] at hval
  apply hi
  apply Fin.ext
  simp [localDivisorJetMiddle]
  omega

/-- Exact odd radical: it is the line spanned by the middle monomial. -/
theorem localDivisorJetEulerResidueForm_odd_leftRadical_iff (r : ℕ)
    (x : Fin (2 * r + 1) → ℂ) :
    (∀ y, localDivisorJetEulerResidueForm (2 * r + 1) x y = 0) ↔
      x = x (localDivisorJetMiddle r) • Pi.single (localDivisorJetMiddle r) 1 := by
  constructor
  · intro hx
    funext i
    by_cases hi : i = localDivisorJetMiddle r
    · subst i
      simp
    · have h := hx (Pi.single i.rev 1)
      rw [localDivisorJetEulerResidueForm_apply_single_rev] at h
      have hxi : x i = 0 :=
        (mul_eq_zero.mp h).resolve_left
          (localDivisorJetEulerCoefficient_ne_zero_of_ne_middle r i hi)
      simp [hxi, hi]
  · intro hx y
    rw [hx, map_smul]
    simp [localDivisorJetEulerResidueForm_middle_mem_leftRadical]

/-- For ξ, nondegeneracy of the canonical local Euler--residue form is exactly the base rung.
It is therefore a detector/equivalent formulation, not an unconditional parity producer. -/
theorem rhLadder_one_iff_localDivisorJetEulerResidueForm_nondegenerate :
    RHLadder 1 ↔ ∀ ρ ∈ rightHalf, xi ρ = 0 →
      (localDivisorJetEulerResidueForm (analyticOrderAt xi ρ).toNat).Nondegenerate := by
  rw [rhLadder_iff_toNat_dvd]
  constructor
  · intro h ρ hρ hzero
    rw [localDivisorJetEulerResidueForm_nondegenerate_iff_even]
    exact even_iff_two_dvd.mpr (by simpa using h ρ hρ hzero)
  · intro h ρ hρ hzero
    have heven := (localDivisorJetEulerResidueForm_nondegenerate_iff_even _).mp
      (h ρ hρ hzero)
    simpa using heven.two_dvd

end RHTower
