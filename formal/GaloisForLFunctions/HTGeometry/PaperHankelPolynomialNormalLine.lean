import GaloisForLFunctions.HTGeometry.PaperHankelNormalDirection
import GaloisForLFunctions.HTGeometry.PaperHomogeneousIdealNormalLine

/-!
# Polynomial normal lines in all finite Hankel moment windows

Populate the general source Rees/weight bridge with actual native Hankel
determinants. Every window of size `2*r+1+extra` admits a polynomial normal
line over every field. The original minimal-window polynomial-map API is
retained as the specialization `extra=0`.
-/

namespace GaloisForLFunctions.HTGeometry

open RHTower MvPolynomial

noncomputable section

variable (K : Type*) [Field K]

/-- Native Hankel results discharge every homogeneous normal-line obligation. -/
def paperHankelNormalData (r extra : ℕ) :
    PaperHomogeneousNormalData K (Fin (2 * r + 1 + extra))
      (finiteHankelSecantIdeal K (2 * r + 1 + extra) r) where
  generator := paperHankelPrincipalMinor K r extra
  degree := r + 1
  degree_pos := Nat.succ_pos r
  generator_mem := paperHankelPrincipalMinor_mem K r extra
  generator_ne_zero := paperHankelPrincipalMinor_ne_zero K r extra
  homogeneous := paperHankelPrincipalMinor_homogeneous K r extra
  order_bound := paperHankelIdeal_weightOrder K _ r

/-- A scalar determinant power gains an ideal order exactly when the scalar vanishes. -/
theorem paperHankel_scalar_pow_mem_succ_iff (r n : ℕ) (c : K) (extra : ℕ := 0) :
    C c * paperHankelPrincipalMinor K r extra ^ n ∈
      finiteHankelSecantIdeal K (2 * r + 1 + extra) r ^ (n + 1) ↔ c = 0 :=
  (paperHankelNormalData K r extra).scalar_pow_mem_succ_iff n c

/-- No finite scalar relation between powers of the canonical normal direction is possible. -/
theorem paperHankelNormalDirection_sum_eq_zero_iff (r : ℕ) (s : Finset ℕ) (a : ℕ → K)
    (extra : ℕ := 0) :
    (∑ n ∈ s,
      algebraMap (MvPolynomial (Fin (2 * r + 1 + extra)) K)
        (PaperIdealAssociatedGraded (finiteHankelSecantIdeal K (2 * r + 1 + extra) r)) (C (a n)) *
          paperHankelNormalDirection K r extra ^ n) = 0 ↔ ∀ n ∈ s, a n = 0 :=
  (paperHankelNormalData K r extra).sum_eq_zero_iff s a

/-- Polynomial substitution into any larger Hankel window's associated graded ring. -/
def paperHankelWindowNormalPolynomialMap (r extra : ℕ) :
    Polynomial K →+* PaperIdealAssociatedGraded (finiteHankelSecantIdeal K (2 * r + 1 + extra) r) :=
  (paperHankelNormalData K r extra).polynomialMap

/-- The larger-window polynomial map has zero kernel. -/
theorem paperHankelWindowNormalPolynomialMap_eq_zero_iff (r extra : ℕ) (p : Polynomial K) :
    paperHankelWindowNormalPolynomialMap K r extra p = 0 ↔ p = 0 :=
  (paperHankelNormalData K r extra).polynomialMap_eq_zero_iff p

/-- A polynomial ring embeds into the full Hankel associated graded ring of every larger window. -/
theorem paperHankelWindowNormalPolynomialMap_injective (r extra : ℕ) :
    Function.Injective (paperHankelWindowNormalPolynomialMap K r extra) :=
  (paperHankelNormalData K r extra).polynomialMap_injective

/-- Original minimal-window polynomial map, retained with its original argument order. -/
def paperHankelNormalPolynomialMap (r : ℕ) :
    Polynomial K →+* PaperIdealAssociatedGraded (finiteHankelSecantIdeal K (2 * r + 1) r) :=
  paperHankelWindowNormalPolynomialMap K r 0

/-- The original polynomial map has zero kernel. -/
theorem paperHankelNormalPolynomialMap_eq_zero_iff (r : ℕ) (p : Polynomial K) :
    paperHankelNormalPolynomialMap K r p = 0 ↔ p = 0 :=
  paperHankelWindowNormalPolynomialMap_eq_zero_iff K r 0 p

/-- The original canonical normal-direction substitution is injective. -/
theorem paperHankelNormalPolynomialMap_injective (r : ℕ) :
    Function.Injective (paperHankelNormalPolynomialMap K r) :=
  paperHankelWindowNormalPolynomialMap_injective K r 0

end

end GaloisForLFunctions.HTGeometry
