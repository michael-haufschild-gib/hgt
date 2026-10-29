import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticInfinityValuation

/-!
# The infinity pole semigroup of the elliptic affine ring

The basis weights are even and odd, respectively. Thus a function with pole
order at most one is constant, while powers of `x` and products `x^j y` realize
every pole order at least two. Thus the affine pole semigroup has exactly
one positive gap, at order one.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

open Polynomial
open scoped WithZero

noncomputable section

/-- No nonconstant affine function has only a simple pole at infinity. -/
theorem poleDegree_le_one_iff (a : A) :
    poleDegree a ≤ 1 ↔ ∃ c : Constants, a = algebraMap Constants A c := by
  constructor
  · intro h
    obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
    simp only [← yA_eq, poleDegree_basis, max_le_iff] at h ⊢
    have hq : q = 0 := by
      by_contra hq
      have hh := h.2
      rw [degree_eq_natDegree hq] at hh
      simp only [two_nsmul] at hh
      have hnat : q.natDegree + q.natDegree + 3 ≤ 1 := by exact_mod_cast hh
      omega
    have hp : p.degree ≤ 0 := by
      by_cases hp : p = 0
      · simp only [hp, degree_zero, bot_le]
      · have hh := h.1
        rw [degree_eq_natDegree hp] at hh ⊢
        simp only [two_nsmul] at hh
        have hnat : p.natDegree + p.natDegree ≤ 1 := by exact_mod_cast hh
        have hp0 : p.natDegree = 0 := by omega
        simp only [hp0, Nat.cast_zero, le_refl]
    refine ⟨p.coeff 0, ?_⟩
    rw [degree_le_zero_iff.mp hp, hq, ← scalar_eq_basis]
    simp only [coeff_C_zero]
  · rintro ⟨c, rfl⟩
    exact (poleDegree_scalar c).trans (by norm_num)

theorem poleDegree_pow (a : A) (n : ℕ) : poleDegree (a ^ n) = n • poleDegree a := by
  simp only [poleDegree, map_pow, degree_pow]

/-- The two affine monomial strings realize precisely all pole orders beyond the gap. -/
theorem exists_affine_poleDegree (n : ℕ) (hn : 2 ≤ n) :
    ∃ a : A, poleDegree a = (n : WithBot ℕ) := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, rfl⟩ := he
    refine ⟨xA ^ k, ?_⟩
    rw [poleDegree_pow, poleDegree_xA]
    change k • ((2 : ℕ) : WithBot ℕ) = ((k + k : ℕ) : WithBot ℕ)
    calc
      _ = ((k • (2 : ℕ) : ℕ) : WithBot ℕ) := (WithBot.coe_nsmul (2 : ℕ) k).symm
      _ = _ := by simp [mul_two]
  · obtain ⟨k, hk⟩ := ho
    have hkpos : 0 < k := by omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
    refine ⟨xA ^ j * yA, ?_⟩
    rw [poleDegree_mul, poleDegree_pow, poleDegree_xA, poleDegree_yA]
    change j • ((2 : ℕ) : WithBot ℕ) + ((3 : ℕ) : WithBot ℕ) = (n : WithBot ℕ)
    calc
      _ = ((j • (2 : ℕ) : ℕ) : WithBot ℕ) + ((3 : ℕ) : WithBot ℕ) :=
        congrArg (fun z : WithBot ℕ => z + (3 : WithBot ℕ))
          (WithBot.coe_nsmul (2 : ℕ) j).symm
      _ = ((j * 2 + 3 : ℕ) : WithBot ℕ) := by simp
      _ = (n : WithBot ℕ) := by congr 1; omega

/-- Pole order and the actual infinity valuation have the same integer exponent. -/
theorem infinityValuation_of_poleDegree (a : A) (n : ℕ)
    (ha : poleDegree a = (n : WithBot ℕ)) :
    infinityValuation (algebraMap A K a) = WithZero.exp (n : ℤ) := by
  rw [infinityValuation_algebraMap]
  change (poleDegree a).map (Nat.castAddMonoidHom ℤ) = (↑(n : ℤ) : WithBot ℤ)
  rw [ha]
  rfl

theorem exists_affine_infinity_valuation (n : ℕ) (hn : 2 ≤ n) :
    ∃ a : A, infinityValuation (algebraMap A K a) = WithZero.exp (n : ℤ) := by
  obtain ⟨a, ha⟩ := exists_affine_poleDegree n hn
  exact ⟨a, infinityValuation_of_poleDegree a n ha⟩

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
