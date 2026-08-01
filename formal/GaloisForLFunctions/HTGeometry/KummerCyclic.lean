import GaloisForLFunctions.HTGeometry.KummerDegreeBound
import GaloisForLFunctions.HTGeometry.RootFieldTransport
import Mathlib.FieldTheory.KummerExtension

/-!
# Irreducibility and cyclicity of a radical polynomial

An element whose `n`-th power lies in the base generates an extension of degree at most `n`; if the
degree is exactly `n` then the minimal polynomial, which divides the radical polynomial and has its
degree, is that polynomial.  So the radical polynomial is irreducible.

Over a base containing a primitive `n`-th root of unity an irreducible radical polynomial has cyclic
Galois group, and that is the cyclicity the base change step asks of its second factor.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **A radical polynomial of full degree is irreducible.** -/
theorem irreducible_X_pow_sub_C_of_finrank {α : L} {c : F} {n : ℕ} (hn : 0 < n)
    (hα : α ^ n = algebraMap F L c) (hdeg : n ≤ Module.finrank F F⟮α⟯) :
    Irreducible (Polynomial.X ^ n - Polynomial.C c : Polynomial F) := by
  have hint : IsIntegral F α := isIntegral_of_pow_mem hn hα
  have hroot : Polynomial.aeval α (Polynomial.X ^ n - Polynomial.C c : Polynomial F) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hα, sub_self]
  have hqmonic : (Polynomial.X ^ n - Polynomial.C c : Polynomial F).Monic :=
    Polynomial.monic_X_pow_sub_C c (by omega)
  have hqdeg : (Polynomial.X ^ n - Polynomial.C c : Polynomial F).natDegree = n :=
    Polynomial.natDegree_X_pow_sub_C
  have hmdeg : (minpoly F α).natDegree = n := by
    have hle : (minpoly F α).natDegree ≤ n := by
      have h := minpoly.min F α hqmonic hroot
      rw [Polynomial.degree_X_pow_sub_C hn c] at h
      exact Polynomial.natDegree_le_iff_degree_le.2 h
    have hge : n ≤ (minpoly F α).natDegree := by
      rwa [IntermediateField.adjoin.finrank hint] at hdeg
    omega
  obtain ⟨r, hr⟩ := minpoly.dvd F α hroot
  have hrne : r ≠ 0 := by
    intro hcon
    rw [hcon, mul_zero] at hr
    exact hqmonic.ne_zero hr
  have hrdeg : r.natDegree = 0 := by
    have h := congrArg Polynomial.natDegree hr
    rw [Polynomial.natDegree_mul (minpoly.ne_zero hint) hrne, hmdeg, hqdeg] at h
    omega
  have hrone : r = 1 := by
    have hlead : (minpoly F α).leadingCoeff * r.leadingCoeff = 1 := by
      have h := congrArg Polynomial.leadingCoeff hr
      rw [Polynomial.leadingCoeff_mul, hqmonic.leadingCoeff] at h
      exact h.symm
    rw [(minpoly.monic hint).leadingCoeff, one_mul] at hlead
    have hc := Polynomial.eq_C_of_natDegree_eq_zero hrdeg
    rw [hc]
    rw [hc, Polynomial.leadingCoeff_C] at hlead
    rw [hlead, map_one]
  rw [hr, hrone, mul_one]
  exact minpoly.irreducible hint

/-- **The Galois group of an irreducible radical polynomial is cyclic.** -/
theorem isCyclic_rootField_X_pow_sub_C {c : F} {n : ℕ} [NeZero n]
    (hζ : (primitiveRoots n F).Nonempty)
    (hirr : Irreducible (Polynomial.X ^ n - Polynomial.C c : Polynomial F))
    (hsplit : (((Polynomial.X ^ n - Polynomial.C c : Polynomial F)).map
      (algebraMap F L)).Splits) :
    IsCyclic (rootField F (L := L) (Polynomial.X ^ n - Polynomial.C c) ≃ₐ[F]
      rootField F (L := L) (Polynomial.X ^ n - Polynomial.C c)) := by
  haveI := isSplittingField_rootField (F := F)
    (p := (Polynomial.X ^ n - Polynomial.C c : Polynomial F)) (L := L) hsplit
  exact isCyclic_of_isSplittingField_X_pow_sub_C hζ hirr _

end GaloisForLFunctions.HTGeometry
