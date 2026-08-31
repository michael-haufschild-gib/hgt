import GaloisForLFunctions.HTGeometry.RittCyclicNormalForm
import GaloisForLFunctions.HTGeometry.ScalarDifferentialTorsor

/-!
# Substitution composes, and the derivative obeys the chain rule

Substitution by a nonconstant rational function is the unique algebra endomorphism of the rational
function field carrying the coordinate to that function, so substituting twice is substituting once
by the composite.  The derivative of a substituted function is the substituted derivative times the
derivative of the substituted map: the identity holds on the image of the polynomial ring by
induction on monomials, and the quotient rule carries it to all of the field.

Together the two make a conjugation transport: if a Möbius change of coordinate carries one map to
another, it carries a rational `k`-differential invariant under the first to one invariant under the
second, with the same scalar.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K] [CharZero K]

noncomputable section

/-- The quotient rule for the derivative of a rational function. -/
theorem ratFuncDeriv_div_general {u v : RatFunc K} (hv : v ≠ 0) :
    ratFuncDeriv (u / v) = (ratFuncDeriv u * v - u * ratFuncDeriv v) / v ^ 2 := by
  have h3 : (u / v) * v = u := div_mul_cancel₀ u hv
  have h2 : (u / v) * ratFuncDeriv v + v * ratFuncDeriv (u / v) = ratFuncDeriv u := by
    have h := congrArg ratFuncDeriv h3
    rwa [ratFuncDeriv_mul] at h
  rw [eq_div_iff (pow_ne_zero 2 hv)]
  calc ratFuncDeriv (u / v) * v ^ 2 = (v * ratFuncDeriv (u / v)) * v := by ring
    _ = (ratFuncDeriv u - (u / v) * ratFuncDeriv v) * v := by rw [← h2]; ring
    _ = ratFuncDeriv u * v - ((u / v) * v) * ratFuncDeriv v := by ring
    _ = ratFuncDeriv u * v - u * ratFuncDeriv v := by rw [h3]

omit [CharZero K] in
/-- **Substitution composes.** -/
theorem ratFuncSubstitutionAlgHom_comp {P Q : RatFunc K}
    (hP : ¬ ∃ c : K, P = RatFunc.C c) (hQ : ¬ ∃ c : K, Q = RatFunc.C c)
    (hPQ : ¬ ∃ c : K, ratFuncSubstitutionAlgHom P hP Q = RatFunc.C c) (R : RatFunc K) :
    ratFuncSubstitutionAlgHom P hP (ratFuncSubstitutionAlgHom Q hQ R)
      = ratFuncSubstitutionAlgHom (ratFuncSubstitutionAlgHom P hP Q) hPQ R := by
  have hext : (ratFuncSubstitutionAlgHom P hP).comp (ratFuncSubstitutionAlgHom Q hQ)
      = ratFuncSubstitutionAlgHom (ratFuncSubstitutionAlgHom P hP Q) hPQ := by
    refine ratFunc_algHom_ext ?_
    simp
  exact AlgHom.congr_fun hext R

/-- The chain rule on the image of the polynomial ring. -/
theorem ratFuncDeriv_substitution_algebraMap {P : RatFunc K} (hP : ¬ ∃ c : K, P = RatFunc.C c)
    (N : K[X]) :
    ratFuncDeriv (ratFuncSubstitutionAlgHom P hP (algebraMap K[X] (RatFunc K) N))
      = ratFuncSubstitutionAlgHom P hP (algebraMap K[X] (RatFunc K) (derivative N))
        * ratFuncDeriv P := by
  induction N using Polynomial.induction_on with
  | C a =>
      rw [RatFunc.algebraMap_C, ratFuncSubstitutionAlgHom_C, ratFuncDeriv_C,
        Polynomial.derivative_C, map_zero]
      simp
  | add p q hp hq =>
      rw [map_add, map_add, ratFuncDeriv_add, hp, hq, Polynomial.derivative_add, map_add, map_add]
      ring
  | monomial n a ih =>
      have hfac : (C a * X ^ (n + 1) : K[X]) = (C a * X ^ n) * X := by ring
      have hder : derivative ((C a * X ^ n) * X)
          = derivative (C a * X ^ n) * X + (C a * X ^ n) := by
        rw [Polynomial.derivative_mul, Polynomial.derivative_X, mul_one]
      rw [hfac, map_mul, map_mul, RatFunc.algebraMap_X, ratFuncSubstitutionAlgHom_X,
        ratFuncDeriv_mul, ih, hder]
      simp only [map_add, map_mul, RatFunc.algebraMap_X, ratFuncSubstitutionAlgHom_X]
      ring

/-- **The chain rule.** -/
theorem ratFuncDeriv_substitution {P : RatFunc K} (hP : ¬ ∃ c : K, P = RatFunc.C c)
    (Q : RatFunc K) :
    ratFuncDeriv (ratFuncSubstitutionAlgHom P hP Q)
      = ratFuncSubstitutionAlgHom P hP (ratFuncDeriv Q) * ratFuncDeriv P := by
  rcases eq_or_ne Q 0 with rfl | hQ0
  · have hz : ratFuncDeriv (0 : RatFunc K) = 0 := by
      rw [← ratFuncDerivation_apply, map_zero]
    rw [map_zero, hz, map_zero, zero_mul]
  · have hden : Q.denom ≠ 0 := RatFunc.denom_ne_zero Q
    have hdenR : algebraMap K[X] (RatFunc K) Q.denom ≠ 0 := algebraMap_ne_zero_of_ne_zero hden
    have hSden : ratFuncSubstitutionAlgHom P hP (algebraMap K[X] (RatFunc K) Q.denom) ≠ 0 := by
      intro h
      exact hdenR ((ratFuncSubstitutionAlgHom P hP).toRingHom.injective (by simpa using h))
    have hQeq : Q = algebraMap K[X] (RatFunc K) Q.num / algebraMap K[X] (RatFunc K) Q.denom :=
      (RatFunc.num_div_denom Q).symm
    have hDQ : ratFuncDeriv Q
        = algebraMap K[X] (RatFunc K) (derivative Q.num * Q.denom - Q.num * derivative Q.denom)
          / algebraMap K[X] (RatFunc K) (Q.denom ^ 2) := by
      conv_lhs => rw [hQeq]
      exact ratFuncDeriv_div hden
    conv_lhs => rw [hQeq]
    rw [map_div₀, ratFuncDeriv_div_general hSden, ratFuncDeriv_substitution_algebraMap,
      ratFuncDeriv_substitution_algebraMap, hDQ, map_sub, map_mul, map_mul, map_pow, map_div₀,
      map_sub, map_mul, map_mul, map_pow]
    field_simp

/-! ## Conjugation transport -/

omit [CharZero K] in
/-- Substitution by equal maps agrees. -/
theorem ratFuncSubstitutionAlgHom_congr {P Q : RatFunc K} (hP : ¬ ∃ c : K, P = RatFunc.C c)
    (hQ : ¬ ∃ c : K, Q = RatFunc.C c) (hPQ : P = Q) (F : RatFunc K) :
    ratFuncSubstitutionAlgHom P hP F = ratFuncSubstitutionAlgHom Q hQ F := by
  subst hPQ
  rfl

/-- **A semiconjugacy carries an invariant differential.**  If `Ψ ∘ R = h ∘ Ψ` and `F` is a rational
`k`-differential invariant for `h` up to the constant `b`, then `(F ∘ Ψ)·(Ψ′)^k` is one for `R`,
with the same constant. -/
theorem isRatAffineTransport_of_semiconj {R h Psi : RatFunc K}
    (hR : ¬ ∃ c : K, R = RatFunc.C c) (hh : ¬ ∃ c : K, h = RatFunc.C c)
    (hPsi : ¬ ∃ c : K, Psi = RatFunc.C c)
    (hcomp : ¬ ∃ c : K, ratFuncSubstitutionAlgHom Psi hPsi h = RatFunc.C c)
    (hsemi : ratFuncSubstitutionAlgHom R hR Psi = ratFuncSubstitutionAlgHom Psi hPsi h)
    {k : ℤ} {b : K} {F : RatFunc K}
    (heq : IsRatAffineTransport h hh k (RatFunc.C b) 0 F) :
    IsRatAffineTransport R hR k (RatFunc.C b) 0
      (ratFuncSubstitutionAlgHom Psi hPsi F * (ratFuncDeriv Psi) ^ k) := by
  have hcomp' : ¬ ∃ c : K, ratFuncSubstitutionAlgHom R hR Psi = RatFunc.C c := by
    rw [hsemi]; exact hcomp
  -- the two ways of substituting agree
  have hswap : ratFuncSubstitutionAlgHom R hR (ratFuncSubstitutionAlgHom Psi hPsi F)
      = ratFuncSubstitutionAlgHom Psi hPsi (ratFuncSubstitutionAlgHom h hh F) := by
    rw [ratFuncSubstitutionAlgHom_comp hR hPsi hcomp' F,
      ratFuncSubstitutionAlgHom_comp hPsi hh hcomp F]
    exact ratFuncSubstitutionAlgHom_congr hcomp' hcomp hsemi F
  -- the chain rule applied to the semiconjugacy
  have hchain : ratFuncSubstitutionAlgHom R hR (ratFuncDeriv Psi) * ratFuncDeriv R
      = ratFuncSubstitutionAlgHom Psi hPsi (ratFuncDeriv h) * ratFuncDeriv Psi := by
    have h1 := ratFuncDeriv_substitution hR Psi
    have h2 := ratFuncDeriv_substitution hPsi h
    rw [hsemi] at h1
    rw [← h1, ← h2]
  have heq' : ratFuncSubstitutionAlgHom h hh F * (ratFuncDeriv h) ^ k = RatFunc.C b * F := by
    have := heq
    rw [IsRatAffineTransport, add_zero] at this
    exact this
  rw [IsRatAffineTransport, add_zero, map_mul, map_zpow₀, hswap]
  calc ratFuncSubstitutionAlgHom Psi hPsi (ratFuncSubstitutionAlgHom h hh F)
        * (ratFuncSubstitutionAlgHom R hR (ratFuncDeriv Psi)) ^ k * ratFuncDeriv R ^ k
      = ratFuncSubstitutionAlgHom Psi hPsi (ratFuncSubstitutionAlgHom h hh F)
        * (ratFuncSubstitutionAlgHom R hR (ratFuncDeriv Psi) * ratFuncDeriv R) ^ k := by
        rw [mul_zpow]; ring
    _ = ratFuncSubstitutionAlgHom Psi hPsi (ratFuncSubstitutionAlgHom h hh F)
        * (ratFuncSubstitutionAlgHom Psi hPsi (ratFuncDeriv h) * ratFuncDeriv Psi) ^ k := by
        rw [hchain]
    _ = ratFuncSubstitutionAlgHom Psi hPsi
          (ratFuncSubstitutionAlgHom h hh F * (ratFuncDeriv h) ^ k) * ratFuncDeriv Psi ^ k := by
        rw [map_mul, map_zpow₀, mul_zpow]; ring
    _ = RatFunc.C b * (ratFuncSubstitutionAlgHom Psi hPsi F * ratFuncDeriv Psi ^ k) := by
        rw [heq', map_mul, ratFuncSubstitutionAlgHom_C]
        ring

/-- The transported differential is nonzero. -/
theorem transport_ne_zero {Psi : RatFunc K} (hPsi : ¬ ∃ c : K, Psi = RatFunc.C c)
    (hd : ratFuncDeriv Psi ≠ 0) {k : ℤ} {F : RatFunc K} (hF : F ≠ 0) :
    ratFuncSubstitutionAlgHom Psi hPsi F * (ratFuncDeriv Psi) ^ k ≠ 0 := by
  refine mul_ne_zero ?_ (zpow_ne_zero k hd)
  intro h
  exact hF ((ratFuncSubstitutionAlgHom Psi hPsi).toRingHom.injective (by simpa using h))

end

end GaloisForLFunctions.HTGeometry
