import GaloisForLFunctions.HTGeometry.CoeffSubInjective
import GaloisForLFunctions.HTGeometry.CenteredCoeffIndependent

/-!
# The coefficients of the centered generic polynomial are algebraically independent

The universal centered coefficients are algebraically independent, and the specialisation to the
generic coefficients is injective, so their images stay independent.

Those images are the coefficients of the centered generic polynomial, together with the
next-to-leading coefficient of the uncentered one; dropping the latter leaves the `d - 1`
coefficients of the centered polynomial, which are therefore independent as well.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

/-- The next-to-leading coefficient of the generic polynomial together with the coefficients of the
centered one. -/
noncomputable def centeredCoeffFamily (K : Type*) [Field K] (d : ℕ) (j : Fin d) :
    SymmetricRationalField K d :=
  if (j : ℕ) = d - 1 then (genericMonicF K d).coeff (d - 1)
  else (centeredMonicF K d).coeff (j : ℕ)

omit [CharZero K] in
theorem coeffSub_centeredFamily (hd : 0 < d) (j : Fin d) :
    coeffSub K d (centeredFamily K d hd j) = centeredCoeffFamily K d j := by
  rw [centeredFamily, centeredCoeffFamily]
  by_cases h : (j : ℕ) = d - 1
  · rw [if_pos h, if_pos h, coeffSub_X, h]
  · rw [if_neg h, if_neg h, coeffSub_universalCenteredCoeff]

/-- **The centering coefficients of the generic polynomial are algebraically independent.** -/
theorem algebraicIndependent_centeredCoeffFamily (hd : 0 < d) :
    AlgebraicIndependent K (centeredCoeffFamily K d) := by
  have h := (algebraicIndependent_centeredFamily (K := K) hd).map
    (f := coeffSub K d) (coeffSub_injective.injOn)
  have hfun : (⇑(coeffSub K d) ∘ centeredFamily K d hd) = centeredCoeffFamily K d :=
    funext fun j => coeffSub_centeredFamily hd j
  rwa [hfun] at h

/-- The coefficients of the centered generic polynomial. -/
noncomputable def centeredCoeff (K : Type*) [Field K] (d : ℕ) (k : Fin (d - 1)) :
    SymmetricRationalField K d :=
  (centeredMonicF K d).coeff (k : ℕ)

/-- Reading a coefficient index of the centered polynomial as an index of the full family. -/
def centeredIndex (d : ℕ) (k : Fin (d - 1)) : Fin d :=
  ⟨(k : ℕ), by have := k.isLt; omega⟩

theorem centeredIndex_injective : Function.Injective (centeredIndex d) := by
  intro a b h
  have hval : (a : ℕ) = (b : ℕ) := congrArg Fin.val h
  exact Fin.ext hval

omit [CharZero K] in
theorem centeredCoeffFamily_centeredIndex (k : Fin (d - 1)) :
    centeredCoeffFamily K d (centeredIndex d k) = centeredCoeff K d k := by
  have hk : ((centeredIndex d k : Fin d) : ℕ) ≠ d - 1 := by
    have := k.isLt
    show (k : ℕ) ≠ d - 1
    omega
  rw [centeredCoeffFamily, if_neg hk, centeredCoeff]
  rfl

/-- **The coefficients of the centered generic polynomial are algebraically independent.** -/
theorem algebraicIndependent_centeredCoeff (hd : 0 < d) :
    AlgebraicIndependent K (centeredCoeff K d) := by
  have h := (algebraicIndependent_centeredCoeffFamily (K := K) hd).comp
    (centeredIndex d) centeredIndex_injective
  have hfun : (centeredCoeffFamily K d ∘ centeredIndex d) = centeredCoeff K d :=
    funext fun k => centeredCoeffFamily_centeredIndex k
  rwa [hfun] at h

end GaloisForLFunctions.HTGeometry
