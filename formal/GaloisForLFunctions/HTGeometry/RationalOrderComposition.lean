import GaloisForLFunctions.HTGeometry.RationalOrder
import GaloisForLFunctions.HTGeometry.RatFuncCompositionDegree

/-!
# How the order transforms under a polynomial substitution

Composing with a nonconstant polynomial multiplies the order at a point by the local multiplicity
of the map there:

`ord_a (Q ∘ R) = ord_{R(a)}(Q) · ord_a (R − R(a))`.

The proof is the local factorization `P = (X − b)^m · N` with `N(b) ≠ 0`: composition carries it to
`P ∘ R = (R − b)^m · (N ∘ R)`, and the second factor does not vanish at `a`.

Consequently an invariance relation of the shape `Q ∘ R · (R')^k = λ Q` reads on orders as a
transport law along the map, which is what turns a single nonzero order into an infinite family of
them along an orbit.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-! ## Multiplicity under composition -/

theorem rootMultiplicity_pow {p : K[X]} (hp : p ≠ 0) (n : ℕ) (a : K) :
    rootMultiplicity a (p ^ n) = n * rootMultiplicity a p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hp) hp), ih]
      ring

/-- **Multiplicity under a polynomial substitution.** -/
theorem rootMultiplicity_comp {P R : K[X]} (hP : P ≠ 0) (hR : R.natDegree ≠ 0) (a : K) :
    rootMultiplicity a (P.comp R)
      = rootMultiplicity (R.eval a) P * rootMultiplicity a (R - Polynomial.C (R.eval a)) := by
  set b : K := R.eval a with hb
  set m : ℕ := rootMultiplicity b P with hm
  set N : K[X] := P /ₘ (Polynomial.X - Polynomial.C b) ^ m with hN
  have hfac : (Polynomial.X - Polynomial.C b) ^ m * N = P :=
    pow_mul_divByMonic_rootMultiplicity_eq P b
  have hNval : N.eval b ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero b hP
  have hN0 : N ≠ 0 := by
    intro h
    apply hNval
    rw [h, eval_zero]
  have hRb : R - Polynomial.C b ≠ 0 := by
    intro h
    have hRC : R = Polynomial.C b := by
      have := sub_eq_zero.mp h
      exact this
    exact hR (by rw [hRC, natDegree_C])
  have hNcompval : (N.comp R).eval a ≠ 0 := by
    rw [eval_comp, ← hb]
    exact hNval
  have hNcomp0 : N.comp R ≠ 0 := by
    intro h
    apply hNcompval
    rw [h, eval_zero]
  have hcomp : P.comp R = (R - Polynomial.C b) ^ m * (N.comp R) := by
    conv_lhs => rw [← hfac]
    rw [mul_comp, pow_comp, sub_comp, X_comp, C_comp]
  rw [hcomp, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero m hRb) hNcomp0),
    rootMultiplicity_pow hRb, rootMultiplicity_eq_zero hNcompval, add_zero]

/-! ## Substitution of a polynomial map on rational functions -/

theorem ratFuncSubstitution_algebraMap {R : K[X]}
    (hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c) (P : K[X]) :
    ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR
        (algebraMap K[X] (RatFunc K) P)
      = algebraMap K[X] (RatFunc K) (P.comp R) := by
  induction P using Polynomial.induction_on with
  | C a =>
      rw [RatFunc.algebraMap_C, ratFuncSubstitutionAlgHom_C, C_comp, RatFunc.algebraMap_C]
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq, add_comp, map_add]
  | monomial n a ih =>
      rw [map_mul, map_mul, map_pow, map_pow, RatFunc.algebraMap_X,
        ratFuncSubstitutionAlgHom_X, mul_comp, pow_comp, X_comp, map_mul, map_pow,
        RatFunc.algebraMap_C, ratFuncSubstitutionAlgHom_C, C_comp, RatFunc.algebraMap_C]

/-- **The transport law for the order.**  Composing with a nonconstant polynomial multiplies the
order at a point by the local multiplicity of the map there. -/
theorem ratOrder_ratFuncSubstitution {R : K[X]} (hRdeg : R.natDegree ≠ 0)
    (hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c)
    {Q : RatFunc K} (hQ : Q ≠ 0) (a : K) :
    ratOrder (ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR Q) a
      = ratOrder Q (R.eval a)
          * (rootMultiplicity a (R - Polynomial.C (R.eval a)) : ℤ) := by
  have hQn : Q.num ≠ 0 := RatFunc.num_ne_zero hQ
  have hQd : Q.denom ≠ 0 := RatFunc.denom_ne_zero Q
  have hAn : algebraMap K[X] (RatFunc K) Q.num ≠ 0 :=
    fun h => hQn ((RatFunc.algebraMap_injective K) (by rw [h, map_zero]))
  have hAd : algebraMap K[X] (RatFunc K) Q.denom ≠ 0 :=
    fun h => hQd ((RatFunc.algebraMap_injective K) (by rw [h, map_zero]))
  have hQeq : Q = algebraMap K[X] (RatFunc K) Q.num * (algebraMap K[X] (RatFunc K) Q.denom)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (RatFunc.num_div_denom Q).symm
  have hsubst : ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR Q
      = algebraMap K[X] (RatFunc K) (Q.num.comp R)
        * (algebraMap K[X] (RatFunc K) (Q.denom.comp R))⁻¹ := by
    conv_lhs => rw [hQeq]
    rw [map_mul, map_inv₀, ratFuncSubstitution_algebraMap, ratFuncSubstitution_algebraMap]
  have hcompne : ∀ P : K[X], P ≠ 0 → P.comp R ≠ 0 := by
    intro P hP hc
    rcases Polynomial.comp_eq_zero_iff.mp hc with h | ⟨-, h2⟩
    · exact hP h
    · exact hRdeg (by rw [h2, natDegree_C])
  have hcn : Q.num.comp R ≠ 0 := hcompne _ hQn
  have hcd : Q.denom.comp R ≠ 0 := hcompne _ hQd
  have hAcn : algebraMap K[X] (RatFunc K) (Q.num.comp R) ≠ 0 :=
    fun h => hcn ((RatFunc.algebraMap_injective K) (by rw [h, map_zero]))
  have hAcd : algebraMap K[X] (RatFunc K) (Q.denom.comp R) ≠ 0 :=
    fun h => hcd ((RatFunc.algebraMap_injective K) (by rw [h, map_zero]))
  rw [hsubst, ratOrder_mul hAcn (inv_ne_zero hAcd), ratOrder_inv hAcd,
    ratOrder_algebraMap, ratOrder_algebraMap,
    rootMultiplicity_comp hQn hRdeg a, rootMultiplicity_comp hQd hRdeg a, ratOrder]
  push_cast
  ring

end

end GaloisForLFunctions.HTGeometry
