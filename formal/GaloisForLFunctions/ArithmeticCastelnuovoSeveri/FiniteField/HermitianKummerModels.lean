import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTracePolynomials
import Mathlib.RingTheory.AdjoinRoot

/-!
# Trace maps from Hermitian equations to Kummer equations

For `q=p^e`, `Q=q^(r*m)` and `R=1+q+⋯+q^(r-1)`, the substitutions
`y=(Σ j<m, x^(q^(r*j)))^R` and `z=v^R` carry `v^(Q+1)=c(x-x^Q)`
to `z^(Q+1)=c^R y(1-y^(q-1))^R`. The construction is a homomorphism
of the literal coordinate rings, with no assumed geometric covering theorem.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open Polynomial
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

variable {K : Type*} [CommRing K]

/-- The Hermitian-form equation, with the outer variable denoting `v`. -/
def hermitianEquation (c : K) (p e r m : ℕ) : K[X][X] :=
  X ^ (p ^ (e * r * m) + 1) - C (C c * (X - X ^ p ^ (e * r * m)))

/-- The Kummer equation, with the inner variable denoting `y`. -/
def traceKummerEquation (c : K) (p e r m : ℕ) : K[X][X] :=
  X ^ (p ^ (e * r * m) + 1) -
    C (C (c ^ kummerExponent (p ^ e) r) * X *
      (1 - X ^ (p ^ e - 1)) ^ kummerExponent (p ^ e) r)

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The trace substitution identity is valid as a polynomial identity over every
commutative ring of characteristic `p`. -/
theorem trace_kummer_identity (e r m : ℕ) (c x : K) :
    (c * (x - x ^ p ^ (e * r * m))) ^ kummerExponent (p ^ e) r =
      c ^ kummerExponent (p ^ e) r *
        (frobeniusTraceSum p (e * r) m x) ^ kummerExponent (p ^ e) r *
        (1 - ((frobeniusTraceSum p (e * r) m x) ^ kummerExponent (p ^ e) r) ^
          (p ^ e - 1)) ^ kummerExponent (p ^ e) r := by
  have hq : p ^ e - 1 + 1 = p ^ e :=
    Nat.sub_add_cancel (Nat.one_le_pow e p (Fact.out : p.Prime).pos)
  have hs := kummer_substitution (p ^ e - 1) r (frobeniusTraceSum p (e * r) m x)
  rw [hq, ← pow_mul] at hs
  rw [mul_pow, ← frobeniusTraceSum_sub_pow p (e * r) m x, hs, mul_assoc]

/-- Pullback of the `y` coordinate along the trace substitution. -/
def traceCoordinateMap (c : K) (e r m : ℕ) :
    K[X] →+* AdjoinRoot (hermitianEquation c p e r m) :=
  Polynomial.eval₂RingHom
    ((AdjoinRoot.of (hermitianEquation c p e r m)).comp Polynomial.C)
    (AdjoinRoot.of (hermitianEquation c p e r m)
      ((frobeniusTraceSum p (e * r) m (X : K[X])) ^ kummerExponent (p ^ e) r))

/-- The canonical Hermitian coordinates satisfy the substituted Kummer equation. -/
theorem traceCoordinateMap_equation (c : K) (e r m : ℕ) :
    (traceKummerEquation c p e r m).eval₂ (traceCoordinateMap p c e r m)
      ((AdjoinRoot.root (hermitianEquation c p e r m)) ^ kummerExponent (p ^ e) r) = 0 := by
  let H := hermitianEquation c p e r m
  let ι := AdjoinRoot.of H
  let v := AdjoinRoot.root H
  have hv : v ^ (p ^ (e * r * m) + 1) =
      ι (C c * (X - X ^ p ^ (e * r * m))) := by
    have h := AdjoinRoot.eval₂_root H
    change (X ^ (p ^ (e * r * m) + 1) -
      C (C c * (X - X ^ p ^ (e * r * m)))).eval₂ ι v = 0 at h
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero] at h
    exact h
  have ht := congrArg ι (trace_kummer_identity (K := K[X]) p e r m (C c) X)
  simp only [map_mul, map_pow, map_sub, map_one] at ht
  simp only [traceKummerEquation, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, traceCoordinateMap, map_mul, map_pow,
    map_sub, map_one, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul,
    RingHom.comp_apply, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_pow]
  change (v ^ kummerExponent (p ^ e) r) ^ (p ^ (e * r * m) + 1) - _ = 0
  rw [← pow_mul, Nat.mul_comm (kummerExponent (p ^ e) r), pow_mul, hv]
  apply sub_eq_zero.mpr
  simpa only [map_mul, map_pow, map_sub] using ht

/-- The trace substitution induces an actual homomorphism of coordinate rings. -/
def hermitianKummerTraceMap (c : K) (e r m : ℕ) :
    AdjoinRoot (traceKummerEquation c p e r m) →+*
      AdjoinRoot (hermitianEquation c p e r m) :=
  AdjoinRoot.lift (traceCoordinateMap p c e r m)
    ((AdjoinRoot.root (hermitianEquation c p e r m)) ^ kummerExponent (p ^ e) r)
    (traceCoordinateMap_equation p c e r m)

/-- The outer coordinate pulls back to `v^R`. -/
theorem hermitianKummerTraceMap_root (c : K) (e r m : ℕ) :
    hermitianKummerTraceMap p c e r m (AdjoinRoot.root (traceKummerEquation c p e r m)) =
      (AdjoinRoot.root (hermitianEquation c p e r m)) ^ kummerExponent (p ^ e) r := by
  exact AdjoinRoot.lift_root _

/-- The inner coordinate pulls back to the `R`-th power of the trace polynomial. -/
theorem hermitianKummerTraceMap_y (c : K) (e r m : ℕ) :
    hermitianKummerTraceMap p c e r m
      (AdjoinRoot.of (traceKummerEquation c p e r m) X) =
    AdjoinRoot.of (hermitianEquation c p e r m)
      ((frobeniusTraceSum p (e * r) m (X : K[X])) ^ kummerExponent (p ^ e) r) := by
  simp only [hermitianKummerTraceMap, AdjoinRoot.lift_of, traceCoordinateMap,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
