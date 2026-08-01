import GaloisForLFunctions.HTGeometry.TruncatedCompatibilityFibre

/-!
# The fibre over a monomial-tail observation is the set of factorizations

At a monomial-tail observation the completed jet is a scalar multiple of a monic divisor of
`1 + c d X^(m+n)` of degree `m`, and every such divisor arises from exactly one point of the fibre.
So the fibre of the observation map is counted by the critical binomial multiplicity, at the level of
the fibre itself and not only of the divisors.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

section

variable {m n : ℕ} {c d : K}

omit [CharZero K] [IsAlgClosed K] in
/-- The exact factorization satisfied by a point of a monomial-tail fibre. -/
theorem criticalFibre_mul_eq (hm : 0 < m) (hn : 0 < n)
    (p : criticalFibre K m n (C c * X ^ m) (C d * X ^ n)) :
    (p.1.1 + C c * X ^ m) * (p.1.2 + C d * X ^ n) = 1 + C (c * d) * X ^ (m + n) := by
  obtain ⟨⟨A, B⟩, hA, hB, hdvd⟩ := p
  have hU : (C c * X ^ m : K[X]).degree ≤ (m : ℕ) :=
    le_trans (Polynomial.degree_C_mul_X_pow_le _ _) le_rfl
  have hV : (C d * X ^ n : K[X]).degree ≤ (n : ℕ) :=
    le_trans (Polynomial.degree_C_mul_X_pow_le _ _) le_rfl
  have hdeg := degree_criticalLowProduct_lt hA hB hU hV
  have hsub : (criticalLowProduct (C c * X ^ m) (C d * X ^ n) A B - 1).degree
      < ((m + n : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hdeg ?_)
    refine lt_of_le_of_lt Polynomial.degree_one_le ?_
    exact_mod_cast (by omega : (0 : ℕ) < m + n)
  have heq : criticalLowProduct (C c * X ^ m) (C d * X ^ n) A B = 1 :=
    (dvd_sub_one_iff_eq_one hsub).1 hdvd
  have hfac := (criticalLowProduct_factorization_iff (C c * X ^ m) (C d * X ^ n) A B).1 heq
  rw [hfac]
  congr 1
  rw [map_mul, pow_add]
  ring

omit [CharZero K] [IsAlgClosed K] in
/-- The completed jet has degree the first depth and leading coefficient the observed one. -/
theorem degree_leadingCoeff_add_monomial (hc : c ≠ 0) {A : K[X]} (hA : A.degree < (m : ℕ)) :
    (A + C c * X ^ m).degree = ((m : ℕ) : WithBot ℕ) ∧
      (A + C c * X ^ m).leadingCoeff = c := by
  have hU : (C c * X ^ m : K[X]).degree = (m : ℕ) := degree_C_mul_X_pow m hc
  refine ⟨?_, ?_⟩
  · rw [Polynomial.degree_add_eq_right_of_degree_lt (by rw [hU]; exact hA), hU]
  · rw [Polynomial.leadingCoeff_add_of_degree_lt (by rw [hU]; exact hA),
      Polynomial.leadingCoeff_C_mul_X_pow]

omit [CharZero K] [IsAlgClosed K] in
/-- The target of the factorization has degree the horizon and leading coefficient the product of the
two observed scalars. -/
theorem degree_leadingCoeff_target (hcd : c * d ≠ 0) (hL : 0 < m + n) :
    (1 + C (c * d) * X ^ (m + n) : K[X]).degree = ((m + n : ℕ) : WithBot ℕ) ∧
      (1 + C (c * d) * X ^ (m + n) : K[X]).leadingCoeff = c * d := by
  have hU : (C (c * d) * X ^ (m + n) : K[X]).degree = ((m + n : ℕ) : WithBot ℕ) :=
    degree_C_mul_X_pow _ hcd
  have hlt : (1 : K[X]).degree < (C (c * d) * X ^ (m + n) : K[X]).degree := by
    rw [hU, Polynomial.degree_one]
    exact_mod_cast hL
  exact ⟨by rw [Polynomial.degree_add_eq_right_of_degree_lt hlt, hU],
    by rw [Polynomial.leadingCoeff_add_of_degree_lt hlt, Polynomial.leadingCoeff_C_mul_X_pow]⟩

/-! ## The correspondence -/

/-- The monic divisor attached to a point of the fibre. -/
noncomputable def fibreToDivisor (hc : c ≠ 0) (hm : 0 < m) (hn : 0 < n)
    (p : criticalFibre K m n (C c * X ^ m) (C d * X ^ n)) :
    {A : K[X] // A.Monic ∧ A ∣ (1 + C (c * d) * X ^ (m + n)) ∧ A.natDegree = m} := by
  refine ⟨C c⁻¹ * (p.1.1 + C c * X ^ m), ?_, ?_, ?_⟩
  · obtain ⟨hdeg, hlc⟩ := degree_leadingCoeff_add_monomial (m := m) hc p.2.1
    show (C c⁻¹ * (p.1.1 + C c * X ^ m)).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hlc, inv_mul_cancel₀ hc]
  · refine dvd_trans ⟨C c, ?_⟩ ⟨p.1.2 + C d * X ^ n, (criticalFibre_mul_eq hm hn p).symm⟩
    rw [mul_comm (C c⁻¹ * (p.1.1 + C c * X ^ m)) (C c), ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hc, map_one, one_mul]
  · obtain ⟨hdeg, -⟩ := degree_leadingCoeff_add_monomial (m := m) hc p.2.1
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hc)]
    exact Polynomial.natDegree_eq_of_degree_eq_some hdeg

omit [CharZero K] [IsAlgClosed K] in
/-- **The fibre over a monomial-tail observation is the set of monic divisors of the target of the
prescribed degree.** -/
theorem fibreToDivisor_bijective (hc : c ≠ 0) (hd : d ≠ 0) (hm : 0 < m) (hn : 0 < n) :
    Function.Bijective (fibreToDivisor (K := K) (m := m) (n := n) (d := d) hc hm hn) := by
  have hcd : c * d ≠ 0 := mul_ne_zero hc hd
  have hL : 0 < m + n := by omega
  constructor
  · rintro ⟨⟨A, B⟩, hA, hB, hdvd⟩ ⟨⟨A', B'⟩, hA', hB', hdvd'⟩ heq
    have hAA : A = A' := by
      have h := congrArg Subtype.val heq
      simp only [fibreToDivisor] at h
      have hcancel := mul_left_cancel₀ (a := (C c⁻¹ : K[X]))
        (Polynomial.C_ne_zero.2 (inv_ne_zero hc)) h
      exact add_right_cancel hcancel
    subst hAA
    have hU0 : (C c * X ^ m : K[X]).coeff 0 = 0 := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega : ¬ (0 : ℕ) = m),
        mul_zero]
    have hV0 : (C d * X ^ n : K[X]).coeff 0 = 0 := by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega : ¬ (0 : ℕ) = n),
        mul_zero]
    have hA0 := coeff_zero_add_ne_zero_of_dvd hL hU0 hV0 hdvd
    have hBB : B = B' := by
      refine criticalLowProduct_right_unique hA0 hdvd hdvd' ?_
      refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_lt_of_le hB (by exact_mod_cast (by omega : n ≤ m + n))
      · exact lt_of_lt_of_le hB' (by exact_mod_cast (by omega : n ≤ m + n))
    subst hBB
    rfl
  · rintro ⟨M, hMmonic, hMdvd, hMdeg⟩
    obtain ⟨G₀, hG₀⟩ := hMdvd
    obtain ⟨hPdeg, hPlc⟩ := degree_leadingCoeff_target (m := m) (n := n) hcd hL
    have hM0 : M ≠ 0 := hMmonic.ne_zero
    have hP0 : (1 + C (c * d) * X ^ (m + n) : K[X]) ≠ 0 := by
      intro h
      rw [h, Polynomial.leadingCoeff_zero] at hPlc
      exact hcd hPlc.symm
    have hG00 : G₀ ≠ 0 := by
      intro h
      rw [h, mul_zero] at hG₀
      exact hP0 hG₀
    have hPnat : (1 + C (c * d) * X ^ (m + n) : K[X]).natDegree = m + n :=
      Polynomial.natDegree_eq_of_degree_eq_some hPdeg
    have hG0nat : G₀.natDegree = n := by
      have hmul := Polynomial.natDegree_mul hM0 hG00
      rw [← hG₀, hPnat, hMdeg] at hmul
      omega
    have hG0lc : G₀.leadingCoeff = c * d := by
      have hmul := Polynomial.leadingCoeff_mul M G₀
      rw [← hG₀, hPlc, hMmonic.leadingCoeff, one_mul] at hmul
      exact hmul.symm
    have hMd : M.degree = (m : ℕ) := by
      rw [Polynomial.degree_eq_natDegree hM0, hMdeg]
    have hGd : (C c⁻¹ * G₀).degree = (n : ℕ) := by
      rw [Polynomial.degree_C_mul (inv_ne_zero hc), Polynomial.degree_eq_natDegree hG00, hG0nat]
    have hGlc : (C c⁻¹ * G₀).leadingCoeff = d := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hG0lc, ← mul_assoc,
        inv_mul_cancel₀ hc, one_mul]
    refine ⟨⟨(C c * (M - X ^ m), C c⁻¹ * G₀ - C d * X ^ n), ?_, ?_, ?_⟩, ?_⟩
    · rw [Polynomial.degree_C_mul hc]
      refine lt_of_lt_of_le (Polynomial.degree_sub_lt ?_ hM0 ?_) (le_of_eq hMd)
      · rw [hMd, Polynomial.degree_X_pow]
      · rw [hMmonic.leadingCoeff, (Polynomial.monic_X_pow (R := K) m).leadingCoeff]
    · refine lt_of_lt_of_le (Polynomial.degree_sub_lt ?_ ?_ ?_) (le_of_eq hGd)
      · rw [hGd, degree_C_mul_X_pow n hd]
      · intro h
        rw [h, Polynomial.leadingCoeff_zero] at hGlc
        exact hd hGlc.symm
      · rw [hGlc, Polynomial.leadingCoeff_C_mul_X_pow]
    · have hfac : (C c * (M - X ^ m) + C c * X ^ m) * ((C c⁻¹ * G₀ - C d * X ^ n) + C d * X ^ n)
          = 1 + C (c * d) * X ^ (m + n) := by
        rw [show C c * (M - X ^ m) + C c * X ^ m = C c * M from by ring,
          show C c⁻¹ * G₀ - C d * X ^ n + C d * X ^ n = C c⁻¹ * G₀ from by ring,
          show C c * M * (C c⁻¹ * G₀) = (C c * C c⁻¹) * (M * G₀) from by ring,
          ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul, ← hG₀]
      have hUV : (C c * X ^ m : K[X]) * (C d * X ^ n) = C (c * d) * X ^ (m + n) := by
        rw [map_mul, pow_add]
        ring
      rw [criticalLowProduct_sub_one, hfac, hUV]
      simp
    · refine Subtype.ext ?_
      show C c⁻¹ * (C c * (M - X ^ m) + C c * X ^ m) = M
      rw [show C c * (M - X ^ m) + C c * X ^ m = C c * M from by ring, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ hc, map_one, one_mul]

/-- **The fibre over a monomial-tail observation has exactly the critical binomial multiplicity of
points.** -/
theorem nat_card_criticalFibre_monomialTail (hc : c ≠ 0) (hd : d ≠ 0) (hm : 0 < m) (hn : 0 < n) :
    Nat.card (criticalFibre K m n (C c * X ^ m) (C d * X ^ n))
      = criticalHorizonMultiplicity m n := by
  classical
  rw [Nat.card_congr (Equiv.ofBijective _ (fibreToDivisor_bijective (K := K) hc hd hm hn))]
  exact nat_card_monic_divisors_monomialTail (by omega) hc hd

end

end GaloisForLFunctions.HTGeometry
