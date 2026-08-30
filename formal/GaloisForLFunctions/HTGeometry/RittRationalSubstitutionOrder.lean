import GaloisForLFunctions.HTGeometry.RittRationalOrderAeval
import GaloisForLFunctions.HTGeometry.RationalOrderComposition

/-!
# The order under substitution by a *rational* map

The corpus's substitution law for the signed order is stated for a polynomial map.  The step-scaling
maps of rational dynamics are genuinely rational, so the law is needed in that generality.

At a point `a` where the map `P` is regular — its denominator does not vanish — write `b` for its
value there.  Then `P − b` vanishes at `a`, and its order is the *local multiplicity* of the map:

`e = ord_a (P − b) = mult_a (num P − b · denom P) ≥ 1`.

Factoring an outer polynomial as `M = (X − b)^m · N` with `N(b) ≠ 0` carries through the
substitution, `M(P) = (P − b)^m · N(P)`, and the cofactor is a unit at `a` because `P − b` vanishes
there and the Taylor expansion of `N` at `b` has nonzero constant term.  So

`ord_a (M(P)) = mult_b M · e`,

the same shape as in the polynomial case, with the local multiplicity taken in the rational sense.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The value of a rational map at a point where it is regular. -/
noncomputable def ratValue (P : RatFunc K) (a : K) : K := P.num.eval a / P.denom.eval a

omit [CharZero K] in
/-- At a point of regularity the map minus its value is a difference of polynomial images. -/
theorem sub_ratValue_eq (P : RatFunc K) (a : K) :
    P - RatFunc.C (ratValue P a)
      = algebraMap K[X] (RatFunc K) (P.num - Polynomial.C (ratValue P a) * P.denom)
        * (algebraMap K[X] (RatFunc K) P.denom)⁻¹ := by
  have hden : algebraMap K[X] (RatFunc K) P.denom ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (RatFunc.denom_ne_zero P)
  have hnum := algebraMap_num_eq P
  rw [map_sub, map_mul, RatFunc.algebraMap_C, sub_mul, hnum]
  field_simp

omit [CharZero K] in
/-- **The local multiplicity is positive at a point of regularity.** -/
theorem ratOrder_sub_ratValue_pos {P : RatFunc K} (hP : ¬ ∃ c : K, P = RatFunc.C c) {a : K}
    (hden : P.denom.eval a ≠ 0) : 0 < ratOrder (P - RatFunc.C (ratValue P a)) a := by
  have hdenne : P.denom ≠ 0 := RatFunc.denom_ne_zero P
  have hne : P.num - Polynomial.C (ratValue P a) * P.denom ≠ 0 := by
    intro h
    refine hP ⟨ratValue P a, ?_⟩
    have hh := sub_ratValue_eq P a
    rw [h, map_zero, zero_mul] at hh
    linear_combination hh
  have hroot : (P.num - Polynomial.C (ratValue P a) * P.denom).eval a = 0 := by
    rw [eval_sub, eval_mul, eval_C, ratValue]
    field_simp [hden]
    ring
  have hmult : 1 ≤ rootMultiplicity a (P.num - Polynomial.C (ratValue P a) * P.denom) :=
    (Polynomial.le_rootMultiplicity_iff hne (n := 1)).mpr
      (by simpa using (dvd_iff_isRoot.mpr hroot))
  have hdm : rootMultiplicity a P.denom = 0 :=
    Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using hden)
  have hAn : algebraMap K[X] (RatFunc K) (P.num - Polynomial.C (ratValue P a) * P.denom) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero hne
  have hAd : algebraMap K[X] (RatFunc K) P.denom ≠ 0 := algebraMap_ne_zero_of_ne_zero hdenne
  rw [sub_ratValue_eq P a, ratOrder_mul hAn (inv_ne_zero hAd), ratOrder_inv hAd,
    ratOrder_algebraMap, ratOrder_algebraMap, hdm]
  omega

/-- **The substitution law for the order, for a rational map.** -/
theorem ratOrder_aeval_ratFunc {P : RatFunc K} (hP : ¬ ∃ c : K, P = RatFunc.C c) {a : K}
    (hden : P.denom.eval a ≠ 0) {M : K[X]} (hM : M ≠ 0) :
    ratOrder (Polynomial.aeval P M) a
      = (rootMultiplicity (ratValue P a) M : ℤ)
        * ratOrder (P - RatFunc.C (ratValue P a)) a := by
  classical
  set b : K := ratValue P a with hb
  set u : RatFunc K := P - RatFunc.C b with hu
  have hupos : 0 < ratOrder u a := ratOrder_sub_ratValue_pos hP hden
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, ratOrder_zero] at hupos
    omega
  set m : ℕ := rootMultiplicity b M with hm
  set N : K[X] := M /ₘ (Polynomial.X - Polynomial.C b) ^ m with hN
  have hfac : (Polynomial.X - Polynomial.C b) ^ m * N = M :=
    pow_mul_divByMonic_rootMultiplicity_eq M b
  have hNval : N.eval b ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero b hM
  have hNexp : Polynomial.aeval P N = Polynomial.aeval u (Polynomial.taylor b N) := by
    have hcomp : N = (Polynomial.taylor b N).comp (Polynomial.X - Polynomial.C b) := by
      rw [Polynomial.taylor_apply, Polynomial.comp_assoc]
      simp
    conv_lhs => rw [hcomp]
    rw [Polynomial.aeval_comp]
    congr 1
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hu]
    rfl
  have hNunit : ratOrder (Polynomial.aeval P N) a = 0 := by
    rw [hNexp]
    refine ratOrder_aeval_eq_zero hupos ?_
    rw [Polynomial.taylor_coeff_zero]
    exact hNval
  have hMexp : Polynomial.aeval P M = u ^ m * Polynomial.aeval P N := by
    conv_lhs => rw [← hfac]
    rw [map_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hu]
    rfl
  have htr : Transcendental K P := P.transcendental_of_ne_C hP
  have hinj : Function.Injective (Polynomial.aeval P : K[X] →ₐ[K] RatFunc K) :=
    transcendental_iff_injective.mp htr
  have hM0 : Polynomial.aeval P M ≠ 0 := fun h => hM (hinj (by simpa using h))
  have hN0 : Polynomial.aeval P N ≠ 0 := by
    intro h
    rw [hMexp, h, mul_zero] at hM0
    exact hM0 rfl
  rw [hMexp, ratOrder_mul (pow_ne_zero _ hu0) hN0, ratOrder_pow hu0, hNunit, add_zero]



omit [CharZero K] in
/-- The image of a polynomial in the rational function field is its evaluation at the generator. -/
theorem algebraMap_eq_aeval_X (M : K[X]) :
    algebraMap K[X] (RatFunc K) M = Polynomial.aeval (RatFunc.X : RatFunc K) M := by
  have hext : (IsScalarTower.toAlgHom K K[X] (RatFunc K))
      = (Polynomial.aeval (RatFunc.X : RatFunc K)) := by
    refine Polynomial.algHom_ext ?_
    simp
  exact AlgHom.congr_fun hext M

omit [CharZero K] in
/-- Substitution sends the image of a polynomial to its evaluation at the map. -/
theorem ratFuncSubstitutionAlgHom_aeval {P : RatFunc K} (hP : ¬ ∃ c : K, P = RatFunc.C c)
    (M : K[X]) :
    ratFuncSubstitutionAlgHom P hP (algebraMap K[X] (RatFunc K) M) = Polynomial.aeval P M := by
  rw [algebraMap_eq_aeval_X, ← Polynomial.aeval_algHom_apply, ratFuncSubstitutionAlgHom_X]

/-- **The substitution law for the order, for a rational map and a rational argument.** -/
theorem ratOrder_ratFuncSubstitution_ratFunc {P : RatFunc K}
    (hP : ¬ ∃ c : K, P = RatFunc.C c) {a : K} (hden : P.denom.eval a ≠ 0)
    {Q : RatFunc K} (hQ : Q ≠ 0) :
    ratOrder (ratFuncSubstitutionAlgHom P hP Q) a
      = ratOrder Q (ratValue P a) * ratOrder (P - RatFunc.C (ratValue P a)) a := by
  classical
  have hnum : Q.num ≠ 0 := RatFunc.num_ne_zero hQ
  have hden' : Q.denom ≠ 0 := RatFunc.denom_ne_zero Q
  have htr : Transcendental K P := P.transcendental_of_ne_C hP
  have hinj : Function.Injective (Polynomial.aeval P : K[X] →ₐ[K] RatFunc K) :=
    transcendental_iff_injective.mp htr
  have hAn : Polynomial.aeval P Q.num ≠ 0 := fun h => hnum (hinj (by simpa using h))
  have hAd : Polynomial.aeval P Q.denom ≠ 0 := fun h => hden' (hinj (by simpa using h))
  have hQeq : Q = algebraMap K[X] (RatFunc K) Q.num
      * (algebraMap K[X] (RatFunc K) Q.denom)⁻¹ := eq_num_div_denom Q
  have hsub : ratFuncSubstitutionAlgHom P hP Q
      = Polynomial.aeval P Q.num * (Polynomial.aeval P Q.denom)⁻¹ := by
    conv_lhs => rw [hQeq]
    rw [map_mul, map_inv₀, ratFuncSubstitutionAlgHom_aeval, ratFuncSubstitutionAlgHom_aeval]
  have hQb : ratOrder Q (ratValue P a)
      = (rootMultiplicity (ratValue P a) Q.num : ℤ)
        - (rootMultiplicity (ratValue P a) Q.denom : ℤ) := rfl
  rw [hsub, ratOrder_mul hAn (inv_ne_zero hAd), ratOrder_inv hAd,
    ratOrder_aeval_ratFunc hP hden hnum, ratOrder_aeval_ratFunc hP hden hden', hQb]
  ring

end GaloisForLFunctions.HTGeometry
