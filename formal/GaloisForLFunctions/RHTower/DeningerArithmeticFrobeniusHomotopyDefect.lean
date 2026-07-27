import Mathlib.Tactic.NoncommRing

/-!
# Local Frobenius homotopy defects

This module formalizes the unconditional algebraic core of
`DAC_LOCAL_FROBENIUS_HOMOTOPY_DEFECT`.  If multiplicative Frobenius
operators are locally homotopic to multiplicative scalar weights, the
failure of the chosen homotopies to multiply coherently is closed and
satisfies a two-cocycle identity.

No arithmetic-cohomology existence, zeta-zero, spectral, positivity, or
Riemann-hypothesis premise occurs.
-/

namespace GaloisForLFunctions.RHTower

/-- The odd endomorphism-complex boundary `d h + h d`. -/
def deningerHomotopyBoundary
    {A : Type*} [Ring A] (d h : A) : A :=
  d * h + h * d

/-- Failure of chosen scalar Frobenius homotopies to respect a product. -/
def deningerFrobeniusHomotopyDefect
    {M A : Type*} [Mul M] [Ring A]
    (F scalar homotopy : M → A) (m n : M) : A :=
  homotopy (m * n) -
    F m * homotopy n -
    scalar n * homotopy m

/--
The multiplicative composite of two scalar homotopies has the expected
boundary.  The hypotheses saying that `scalar n` commutes with `d` and
`F m` are the abstract form of central scalar multiplication.
-/
theorem deningerCompositeHomotopy_boundary
    {A : Type*} [Ring A]
    (d Fm Fn Fmn am an amn hm hn : A)
    (hdFm : d * Fm = Fm * d)
    (hdan : d * an = an * d)
    (hanFm : an * Fm = Fm * an)
    (hanam : an * am = am * an)
    (hFmn : Fmn = Fm * Fn)
    (hamn : amn = am * an)
    (hhm : deningerHomotopyBoundary d hm = Fm - am)
    (hhn : deningerHomotopyBoundary d hn = Fn - an) :
    deningerHomotopyBoundary d (Fm * hn + an * hm) =
      Fmn - amn := by
  unfold deningerHomotopyBoundary at hhm hhn ⊢
  calc
    d * (Fm * hn + an * hm) + (Fm * hn + an * hm) * d =
        Fm * (d * hn + hn * d) + an * (d * hm + hm * d) := by
      simp only [mul_add, add_mul]
      rw [← mul_assoc d Fm hn, hdFm, mul_assoc Fm d hn,
        ← mul_assoc d an hm, hdan, mul_assoc an d hm,
        mul_assoc Fm hn d, mul_assoc an hm d]
      abel
    _ = Fm * (Fn - an) + an * (Fm - am) := by rw [hhm, hhn]
    _ = Fm * Fn - am * an := by
      rw [mul_sub, mul_sub, hanFm, hanam]
      noncomm_ring
    _ = Fmn - amn := by rw [hFmn, hamn]

/-- The factorization defect is closed in the endomorphism complex. -/
theorem deningerFrobeniusHomotopyDefect_boundary
    {M A : Type*} [Mul M] [Ring A]
    (d : A) (F scalar homotopy : M → A) (m n : M)
    (hdFm : d * F m = F m * d)
    (hdan : d * scalar n = scalar n * d)
    (hanFm : scalar n * F m = F m * scalar n)
    (hanam : scalar n * scalar m = scalar m * scalar n)
    (hFmn : F (m * n) = F m * F n)
    (hamn : scalar (m * n) = scalar m * scalar n)
    (hhm :
      deningerHomotopyBoundary d (homotopy m) =
        F m - scalar m)
    (hhn :
      deningerHomotopyBoundary d (homotopy n) =
        F n - scalar n)
    (hhmn :
      deningerHomotopyBoundary d (homotopy (m * n)) =
        F (m * n) - scalar (m * n)) :
    deningerHomotopyBoundary d
        (deningerFrobeniusHomotopyDefect
          F scalar homotopy m n) = 0 := by
  have hcomposite :
      deningerHomotopyBoundary d
          (F m * homotopy n + scalar n * homotopy m) =
        F (m * n) - scalar (m * n) :=
    deningerCompositeHomotopy_boundary
      d (F m) (F n) (F (m * n))
      (scalar m) (scalar n) (scalar (m * n))
      (homotopy m) (homotopy n)
      hdFm hdan hanFm hanam hFmn hamn hhm hhn
  unfold deningerFrobeniusHomotopyDefect
  unfold deningerHomotopyBoundary at hhmn hcomposite ⊢
  calc
    d * (homotopy (m * n) -
          F m * homotopy n - scalar n * homotopy m) +
        (homotopy (m * n) -
          F m * homotopy n - scalar n * homotopy m) * d =
      (d * homotopy (m * n) + homotopy (m * n) * d) -
        (d * (F m * homotopy n + scalar n * homotopy m) +
          (F m * homotopy n + scalar n * homotopy m) * d) := by
            noncomm_ring
    _ = 0 := by rw [hhmn, hcomposite, sub_self]

/-- The defects obey the multiplicative two-cocycle identity. -/
theorem deningerFrobeniusHomotopyDefect_cocycle
    {M A : Type*} [Semigroup M] [Ring A]
    (F scalar homotopy : M → A) (l m n : M)
    (hFlm : F (l * m) = F l * F m)
    (hasmn : scalar (m * n) = scalar m * scalar n)
    (hanFl : scalar n * F l = F l * scalar n)
    (hanam : scalar n * scalar m = scalar m * scalar n) :
    deningerFrobeniusHomotopyDefect
          F scalar homotopy (l * m) n +
        scalar n *
          deningerFrobeniusHomotopyDefect
            F scalar homotopy l m =
      deningerFrobeniusHomotopyDefect
          F scalar homotopy l (m * n) +
        F l *
          deningerFrobeniusHomotopyDefect
            F scalar homotopy m n := by
  unfold deningerFrobeniusHomotopyDefect
  rw [mul_assoc, hFlm, hasmn]
  have hcommF :
      scalar n * (F l * homotopy m) =
        F l * (scalar n * homotopy m) := by
    rw [← mul_assoc, hanFl, mul_assoc]
  have hcommScalar :
      scalar n * (scalar m * homotopy l) =
        scalar m * (scalar n * homotopy l) := by
    rw [← mul_assoc, hanam, mul_assoc]
  simp only [mul_sub]
  rw [hcommF, hcommScalar]
  noncomm_ring

end GaloisForLFunctions.RHTower
