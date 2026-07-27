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
    (hFmn : Fmn = Fm * Fn)
    (hamn : amn = am * an)
    (hhm : deningerHomotopyBoundary d hm = Fm - am)
    (hhn : deningerHomotopyBoundary d hn = Fn - an) :
    deningerHomotopyBoundary d (Fm * hn + an * hm) =
      Fmn - amn := by
  unfold deningerHomotopyBoundary at hhm hhn ⊢
  noncomm_ring [hdFm, hdan, hanFm, hFmn, hamn, hhm, hhn]

/-- The factorization defect is closed in the endomorphism complex. -/
theorem deningerFrobeniusHomotopyDefect_boundary
    {M A : Type*} [Mul M] [Ring A]
    (d : A) (F scalar homotopy : M → A) (m n : M)
    (hdFm : d * F m = F m * d)
    (hdan : d * scalar n = scalar n * d)
    (hanFm : scalar n * F m = F m * scalar n)
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
      hdFm hdan hanFm hFmn hamn hhm hhn
  unfold deningerFrobeniusHomotopyDefect
  unfold deningerHomotopyBoundary at hhmn hcomposite ⊢
  noncomm_ring [hhmn, hcomposite]

/-- The defects obey the multiplicative two-cocycle identity. -/
theorem deningerFrobeniusHomotopyDefect_cocycle
    {M A : Type*} [Semigroup M] [Ring A]
    (F scalar homotopy : M → A) (l m n : M)
    (hFlm : F (l * m) = F l * F m)
    (hasmn : scalar (m * n) = scalar m * scalar n) :
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
  noncomm_ring

end GaloisForLFunctions.RHTower
