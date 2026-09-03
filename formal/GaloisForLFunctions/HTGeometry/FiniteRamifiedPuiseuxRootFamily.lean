import GaloisForLFunctions.HTGeometry.RamifiedMultiGradedNewtonModelBase

/-!
# Finite Puiseux root families admit one ramification

The full relative algebraic closure cannot map to one integer-valued Hahn field: it contains roots
of unbounded order.  Finite branch data has the opposite sharp behavior.  For every finite family
of positive root orders, the coordinatewise product is one common finite ramification, and the
corresponding Hahn monomials are literal roots of every requested order.

This is the positive survivor of the full-closure obstruction.  It supplies the exact target-side
representation needed by a replacement analytic selection theorem over the finite field generated
by the selected velocity branches.
-/

open HahnSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical coordinatewise ramification absorbing a finite family of positive root orders. -/
def finiteRootRamification {N T : ℕ} (m : Fin N → Fin T → ℕ+) (j : Fin N) : ℕ :=
  ∏ a, (m j a : ℕ)

theorem finiteRootRamification_pos {N T : ℕ} (m : Fin N → Fin T → ℕ+) (j : Fin N) :
    0 < finiteRootRamification m j := by
  exact Finset.prod_pos fun a _ => (m j a).2

theorem finiteRootOrder_dvd_ramification {N T : ℕ} (m : Fin N → Fin T → ℕ+)
    (j : Fin N) (a : Fin T) :
    (m j a : ℕ) ∣ finiteRootRamification m j := by
  exact Finset.dvd_prod_of_mem (fun b => (m j b : ℕ)) (Finset.mem_univ a)

/-- Degree of the canonical `m_{j,a}`-th root of the `j`-th coordinate. -/
def mgFiniteRootDegree {N T : ℕ} (m : Fin N → Fin T → ℕ+)
    (j : Fin N) (a : Fin T) : mgDeg N :=
  toLex (Pi.single j
    (-((finiteRootRamification m j / (m j a : ℕ) : ℕ) : ℤ)))

theorem nsmul_mgFiniteRootDegree {N T : ℕ} (m : Fin N → Fin T → ℕ+)
    (j : Fin N) (a : Fin T) :
    (m j a : ℕ) • mgFiniteRootDegree m j a =
      mgRamUnit (finiteRootRamification m) j := by
  apply ofLex.injective
  funext l
  simp only [mgFiniteRootDegree, mgRamUnit]
  change (m j a : ℕ) •
      ((Pi.single j
        (-((finiteRootRamification m j / (m j a : ℕ) : ℕ) : ℤ)) : Fin N → ℤ) l) =
    ((Pi.single j (-(finiteRootRamification m j : ℤ)) : Fin N → ℤ) l)
  by_cases hlj : l = j
  · subst l
    rw [Pi.single_eq_same, Pi.single_eq_same, nsmul_eq_mul]
    have hnat : (m j a : ℕ) * (finiteRootRamification m j / (m j a : ℕ)) =
        finiteRootRamification m j :=
      Nat.mul_div_cancel' (finiteRootOrder_dvd_ramification m j a)
    have hint : ((m j a : ℕ) : ℤ) *
        ((finiteRootRamification m j / (m j a : ℕ) : ℕ) : ℤ) =
          (finiteRootRamification m j : ℤ) := by
      exact_mod_cast hnat
    rw [mul_neg, hint]
  · rw [Pi.single_eq_of_ne hlj, Pi.single_eq_of_ne hlj]
    simp

/-- Canonical Hahn monomial realizing one member of a finite root-order family. -/
def hahnFractionFiniteCoordinateRootBase
    (K : Type*) [Field K] {N T : ℕ} (m : Fin N → Fin T → ℕ+)
    (j : Fin N) (a : Fin T) : HahnFraction (mgDeg N) K :=
  algebraMap (HahnSeries (mgDeg N) K) (HahnFraction (mgDeg N) K)
    (HahnSeries.single (mgFiniteRootDegree m j a) 1)

/-- Every finite family of positive coordinate-root orders fits one common finite ramification. -/
theorem hahnFractionFiniteCoordinateRootBase_pow
    (K : Type*) [Field K] {N T : ℕ} (m : Fin N → Fin T → ℕ+)
    (j : Fin N) (a : Fin T) :
    hahnFractionFiniteCoordinateRootBase K m j a ^ (m j a : ℕ) =
      hahnFractionRamCoordinateBase K (finiteRootRamification m) j := by
  rw [hahnFractionFiniteCoordinateRootBase, hahnFractionRamCoordinateBase, ← map_pow,
    HahnSeries.single_pow, nsmul_mgFiniteRootDegree]
  simp

end

end GaloisForLFunctions.HTGeometry
