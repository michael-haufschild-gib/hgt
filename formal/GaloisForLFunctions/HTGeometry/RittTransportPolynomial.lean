import GaloisForLFunctions.HTGeometry.RittTransportConstant

/-!
# A pole-free solution is a polynomial, and its degree is pinned

Over an algebraically closed field a rational function whose signed order is everywhere non-negative
is a polynomial: the numerator and denominator of the reduced representation are coprime, so a root
of the denominator would be a pole, and a denominator without roots is a constant.

Substitution by a polynomial `R` sends the image of a polynomial `A` to the image of the composite
`A ∘ R`, so a polynomial solution of the transport equation is an identity in `K[X]`:

`A(R) · (R′)^J = b · A + C`.

Comparing degrees pins `deg C`: for `deg R ≥ 2` and `deg A ≥ 1` the left side has degree
`deg A · deg R + J·(deg R − 1)`, strictly larger than `deg A`, so the inhomogeneity must have exactly
that degree.  An inhomogeneity of any other degree therefore admits no non-constant polynomial
solution, and the constant ones are pinned by `isAffineTransport_C_iff`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-- **A pole-free rational function is a polynomial.** -/
theorem exists_polynomial_of_ratOrder_nonneg [IsAlgClosed K] {a : RatFunc K} (ha : a ≠ 0)
    (h : ∀ p : K, 0 ≤ ratOrder a p) :
    ∃ A : K[X], A ≠ 0 ∧ a = algebraMap K[X] (RatFunc K) A := by
  classical
  have hnum : a.num ≠ 0 := RatFunc.num_ne_zero ha
  have hden : a.denom ≠ 0 := RatFunc.denom_ne_zero a
  have hcop : IsCoprime a.num a.denom := RatFunc.isCoprime_num_denom a
  have hnoroot : ∀ p : K, ¬ a.denom.IsRoot p := by
    intro p hp
    have hdvdden : (X - C p : K[X]) ∣ a.denom := dvd_iff_isRoot.mpr hp
    have hmden : 1 ≤ rootMultiplicity p a.denom :=
      (Polynomial.le_rootMultiplicity_iff hden).mpr (by simpa using hdvdden)
    have hord := h p
    rw [ratOrder] at hord
    have hmnum : 1 ≤ rootMultiplicity p a.num := by omega
    have hdvdnum : (X - C p : K[X]) ∣ a.num := by
      have hd := (Polynomial.le_rootMultiplicity_iff hnum).mp hmnum
      simpa using hd
    have hunit := hcop.isUnit_of_dvd' hdvdnum hdvdden
    have hdeg := Polynomial.degree_eq_zero_of_isUnit hunit
    rw [degree_X_sub_C] at hdeg
    exact absurd hdeg (by norm_num)
  have hdegden : a.denom.natDegree = 0 := by
    by_contra hd
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root a.denom (by
      intro h0
      exact hd (natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h0)))
    exact hnoroot z hz
  obtain ⟨β, hβ⟩ : ∃ β : K, a.denom = C β := ⟨a.denom.coeff 0, eq_C_of_natDegree_eq_zero hdegden⟩
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hβ
    exact hden hβ
  refine ⟨C β⁻¹ * a.num, mul_ne_zero (Polynomial.C_ne_zero.mpr (inv_ne_zero hβ0)) hnum, ?_⟩
  rw [map_mul, RatFunc.algebraMap_C, algebraMap_num_eq a, hβ, RatFunc.algebraMap_C,
    show (RatFunc.C β⁻¹ : RatFunc K) * (a * RatFunc.C β) = (RatFunc.C β⁻¹ * RatFunc.C β) * a
      from by ring, ← map_mul, inv_mul_cancel₀ hβ0, map_one, one_mul]



variable [CharZero K]

omit [CharZero K] in
/-- Substitution by a polynomial sends the image of `A` to the image of the composite `A ∘ R`. -/
theorem ratFuncSubstitutionAlgHom_algebraMap {R : K[X]}
    (hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c) (A : K[X]) :
    ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR
        (algebraMap K[X] (RatFunc K) A)
      = algebraMap K[X] (RatFunc K) (A.comp R) := by
  have key : (ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR).comp
      (IsScalarTower.toAlgHom K K[X] (RatFunc K))
      = (IsScalarTower.toAlgHom K K[X] (RatFunc K)).comp (Polynomial.aeval R) := by
    refine Polynomial.algHom_ext ?_
    simp [ratFuncSubstitutionAlgHom_X]
  have h := AlgHom.congr_fun key A
  simpa [Polynomial.aeval_def, Polynomial.comp] using h

omit [CharZero K] in
/-- **A polynomial solution of the transport equation is a polynomial identity.** -/
theorem polynomial_identity_of_isAffineTransport {R : K[X]}
    {hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c}
    {J : ℕ} {β : K} {A Cp : K[X]}
    (heq : IsAffineTransport R hR (J : ℤ) (RatFunc.C β)
      (algebraMap K[X] (RatFunc K) Cp) (algebraMap K[X] (RatFunc K) A)) :
    A.comp R * (derivative R) ^ J = Polynomial.C β * A + Cp := by
  refine (RatFunc.algebraMap_injective K) ?_
  rw [map_mul, map_pow, map_add, map_mul, RatFunc.algebraMap_C,
    ← ratFuncSubstitutionAlgHom_algebraMap hR A]
  rw [IsAffineTransport] at heq
  rw [← zpow_natCast (algebraMap K[X] (RatFunc K) (derivative R)) J]
  exact heq

end GaloisForLFunctions.HTGeometry
