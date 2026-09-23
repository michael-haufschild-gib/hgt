import GaloisForLFunctions.HTGeometry.TruncatedCompatibilityFibre
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCriticalMultiplicity
import GaloisForLFunctions.HTGeometry.SeparableSplitDivisorCount

/-!
# The count at both depths two, for a general observed packet

At both depths two the horizon is four, so an observed packet has two coefficients below it and the
compatibility equation is four scalar equations in four unknowns.  Eliminating the two reciprocal
unknowns leaves

```text
v₂ a₀³ - a₁² + u₂ a₀ = 0,      v₃ a₀³ + v₂ a₁ a₀² - u₂ a₁ + u₃ a₀ = 0,
```

and eliminating `a₁` between them leaves a single sextic in `a₀` with leading coefficient `v₂³`.
Its degree is exactly the critical binomial multiplicity `choose(4,2) = 6`.

This is the first case of the count with both depths above one and with the observed packets
unrestricted: the packets here carry both of their coefficients, not only the lowest.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-! ## The eliminated equations -/

section Equations

/-- **The four scalar equations of a fibre point at both depths two.** -/
theorem fibre_two_two_coeffs {U V : K[X]} (hU : (X : K[X]) ^ (2 : ℕ) ∣ U) (hV : (X : K[X]) ^ (2 : ℕ) ∣ V)
    (p : criticalFibre K 2 2 U V) :
    p.1.1.coeff 0 * p.1.2.coeff 0 = 1 ∧
    p.1.1.coeff 0 * p.1.2.coeff 1 + p.1.1.coeff 1 * p.1.2.coeff 0 = 0 ∧
    p.1.1.coeff 0 * V.coeff 2 + p.1.1.coeff 1 * p.1.2.coeff 1
      + U.coeff 2 * p.1.2.coeff 0 = 0 ∧
    p.1.1.coeff 0 * V.coeff 3 + p.1.1.coeff 1 * V.coeff 2 + U.coeff 2 * p.1.2.coeff 1
      + U.coeff 3 * p.1.2.coeff 0 = 0 := by
  classical
  have hdvd : (X : K[X]) ^ (2 + 2) ∣ ((p.1.1 + U) * (p.1.2 + V) - 1) :=
    (dvd_criticalLowProduct_sub_one_iff_mul_sub_one hU hV _ _).1 p.2.2.2
  have hU0 : U.coeff 0 = 0 := by
    have := Polynomial.X_pow_dvd_iff.1 hU 0 (by omega)
    exact this
  have hU1 : U.coeff 1 = 0 := Polynomial.X_pow_dvd_iff.1 hU 1 (by omega)
  have hV0 : V.coeff 0 = 0 := Polynomial.X_pow_dvd_iff.1 hV 0 (by omega)
  have hV1 : V.coeff 1 = 0 := Polynomial.X_pow_dvd_iff.1 hV 1 (by omega)
  have hA2 : p.1.1.coeff 2 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le p.2.1 (by exact_mod_cast (by omega : 2 ≤ 2)))
  have hA3 : p.1.1.coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le p.2.1 (by exact_mod_cast (by omega : 2 ≤ 3)))
  have hB2 : p.1.2.coeff 2 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le p.2.2.1 (by exact_mod_cast (by omega : 2 ≤ 2)))
  have hB3 : p.1.2.coeff 3 = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le p.2.2.1 (by exact_mod_cast (by omega : 2 ≤ 3)))
  have hcoeff : ∀ k < 4, ((p.1.1 + U) * (p.1.2 + V)).coeff k = (1 : K[X]).coeff k := by
    intro k hk
    have := Polynomial.X_pow_dvd_iff.1 hdvd k (by omega)
    rw [Polynomial.coeff_sub, sub_eq_zero] at this
    exact this
  have h0 := hcoeff 0 (by omega)
  have h1 := hcoeff 1 (by omega)
  have h2 := hcoeff 2 (by omega)
  have h3 := hcoeff 3 (by omega)
  rw [coeff_mul_range] at h0 h1 h2 h3
  simp [Finset.sum_range_succ, Polynomial.coeff_one, hU0, hU1, hV0, hV1, hA2, hA3, hB2,
    hB3] at h0 h1 h2 h3
  exact ⟨by linear_combination h0, by linear_combination h1, by linear_combination h2,
    by linear_combination h3⟩

/-- **The two equations left after eliminating the reciprocal.** -/
theorem fibre_two_two_eliminated {U V : K[X]} (hU : (X : K[X]) ^ (2 : ℕ) ∣ U) (hV : (X : K[X]) ^ (2 : ℕ) ∣ V)
    (p : criticalFibre K 2 2 U V) :
    V.coeff 2 * p.1.1.coeff 0 ^ (3 : ℕ) - p.1.1.coeff 1 ^ (2 : ℕ)
        + U.coeff 2 * p.1.1.coeff 0 = 0 ∧
      V.coeff 3 * p.1.1.coeff 0 ^ (3 : ℕ) + V.coeff 2 * p.1.1.coeff 1 * p.1.1.coeff 0 ^ (2 : ℕ)
        - U.coeff 2 * p.1.1.coeff 1 + U.coeff 3 * p.1.1.coeff 0 = 0 := by
  obtain ⟨e0, e1, e2, e3⟩ := fibre_two_two_coeffs hU hV p
  constructor
  · linear_combination p.1.1.coeff 0 ^ (2 : ℕ) * e2 - p.1.1.coeff 1 * p.1.1.coeff 0 * e1
      + (p.1.1.coeff 1 ^ (2 : ℕ) - U.coeff 2 * p.1.1.coeff 0) * e0
  · linear_combination p.1.1.coeff 0 ^ (2 : ℕ) * e3 - U.coeff 2 * p.1.1.coeff 0 * e1
      + (U.coeff 2 * p.1.1.coeff 1 - U.coeff 3 * p.1.1.coeff 0) * e0

end Equations

/-! ## The sextic -/

section Sextic

/-- **The eliminant of the depth-two system**: a sextic in the first jet coefficient. -/
noncomputable def criticalSextic (u₂ u₃ v₂ v₃ : K) : K[X] :=
  (C v₂ * X ^ (2 : ℕ) + C u₂) * (C v₂ * X ^ (2 : ℕ) - C u₂) ^ (2 : ℕ) - X * (C v₃ * X ^ (2 : ℕ) + C u₃) ^ (2 : ℕ)

theorem natDegree_criticalSextic {u₂ u₃ v₂ v₃ : K} (hv₂ : v₂ ≠ 0) :
    (criticalSextic u₂ u₃ v₂ v₃).natDegree = 6 := by
  have hq : ∀ c d : K, c ≠ 0 → (C c * X ^ (2 : ℕ) + C d : K[X]).natDegree = 2 := by
    intro c d hc
    rw [Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul_X_pow 2 c hc]
  have hq0 : ∀ c d : K, c ≠ 0 → (C c * X ^ (2 : ℕ) + C d : K[X]) ≠ 0 := by
    intro c d hc h0
    have := hq c d hc
    rw [h0, Polynomial.natDegree_zero] at this
    omega
  have hsub : (C v₂ * X ^ (2 : ℕ) - C u₂ : K[X]) = C v₂ * X ^ (2 : ℕ) + C (-u₂) := by
    rw [map_neg]
    ring
  have hleft : ((C v₂ * X ^ (2 : ℕ) + C u₂) * (C v₂ * X ^ (2 : ℕ) - C u₂) ^ (2 : ℕ) : K[X]).natDegree = 6 := by
    rw [hsub, Polynomial.natDegree_mul (hq0 v₂ u₂ hv₂) (pow_ne_zero _ (hq0 v₂ (-u₂) hv₂)),
      Polynomial.natDegree_pow, hq v₂ u₂ hv₂, hq v₂ (-u₂) hv₂]
  have hright : (X * (C v₃ * X ^ (2 : ℕ) + C u₃) ^ (2 : ℕ) : K[X]).natDegree ≤ 5 := by
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    have : ((C v₃ * X ^ (2 : ℕ) + C u₃ : K[X]) ^ (2 : ℕ)).natDegree ≤ 4 := by
      refine le_trans (Polynomial.natDegree_pow_le) ?_
      have h1 : (C v₃ * X ^ (2 : ℕ) + C u₃ : K[X]).natDegree ≤ 2 := by
        refine le_trans (Polynomial.natDegree_add_le _ _) ?_
        simp only [max_le_iff]
        exact ⟨le_trans (Polynomial.natDegree_mul_le) (by simp), by simp⟩
      omega
    simp only [Polynomial.natDegree_X]
    omega
  rw [criticalSextic, Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by omega), hleft]

theorem criticalSextic_ne_zero {u₂ u₃ v₂ v₃ : K} (hv₂ : v₂ ≠ 0) :
    criticalSextic u₂ u₃ v₂ v₃ ≠ 0 := by
  intro h0
  have := natDegree_criticalSextic (u₂ := u₂) (u₃ := u₃) (v₃ := v₃) hv₂
  rw [h0, Polynomial.natDegree_zero] at this
  omega

/-- **The first jet coefficient of a fibre point is a root of the sextic.** -/
theorem isRoot_criticalSextic {U V : K[X]} (hU : (X : K[X]) ^ (2 : ℕ) ∣ U) (hV : (X : K[X]) ^ (2 : ℕ) ∣ V)
    (p : criticalFibre K 2 2 U V) :
    (criticalSextic (U.coeff 2) (U.coeff 3) (V.coeff 2) (V.coeff 3)).IsRoot
      (p.1.1.coeff 0) := by
  obtain ⟨E1, E2⟩ := fibre_two_two_eliminated hU hV p
  have ha₀ : p.1.1.coeff 0 ≠ 0 := by
    have hU0 : U.coeff 0 = 0 := Polynomial.X_pow_dvd_iff.1 hU 0 (by omega)
    have hV0 : V.coeff 0 = 0 := Polynomial.X_pow_dvd_iff.1 hV 0 (by omega)
    have := coeff_zero_add_ne_zero_of_dvd (L := 2 + 2) (by omega) hU0 hV0 p.2.2.2
    rw [Polynomial.coeff_add, hU0, add_zero] at this
    exact this
  have hmul : p.1.1.coeff 0 *
      (criticalSextic (U.coeff 2) (U.coeff 3) (V.coeff 2) (V.coeff 3)).eval
        (p.1.1.coeff 0) = 0 := by
    simp only [criticalSextic, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    linear_combination (V.coeff 2 * p.1.1.coeff 0 ^ (2 : ℕ) - U.coeff 2) ^ (2 : ℕ) * E1
      + (p.1.1.coeff 1 * (V.coeff 2 * p.1.1.coeff 0 ^ (2 : ℕ) - U.coeff 2)
          - p.1.1.coeff 0 * (V.coeff 3 * p.1.1.coeff 0 ^ (2 : ℕ) + U.coeff 3)) * E2
  rcases mul_eq_zero.1 hmul with h | h
  · exact absurd h ha₀
  · exact h

end Sextic

/-! ## The first jet coefficient determines the point -/

section Injective

/-- **At both depths two the first jet coefficient determines the fibre point**, away from the
locus where the second equation degenerates in the second jet coefficient. -/
theorem coeff_zero_injective_two_two {U V : K[X]} (hU : (X : K[X]) ^ (2 : ℕ) ∣ U)
    (hV : (X : K[X]) ^ (2 : ℕ) ∣ V)
    (hgen : U.coeff 2 * V.coeff 3 + U.coeff 3 * V.coeff 2 ≠ 0) :
    Function.Injective (fun p : criticalFibre K 2 2 U V => p.1.1.coeff 0) := by
  intro p q hpq
  have h0 : p.1.1.coeff 0 = q.1.1.coeff 0 := hpq
  have hU0 : U.coeff 0 = 0 := Polynomial.X_pow_dvd_iff.1 hU 0 (by omega)
  have hV0 : V.coeff 0 = 0 := Polynomial.X_pow_dvd_iff.1 hV 0 (by omega)
  obtain ⟨E1p, E2p⟩ := fibre_two_two_eliminated hU hV p
  obtain ⟨E1q, E2q⟩ := fibre_two_two_eliminated hU hV q
  have ha₀ : p.1.1.coeff 0 ≠ 0 := by
    have hne := coeff_zero_add_ne_zero_of_dvd (L := 2 + 2) (by omega) hU0 hV0 p.2.2.2
    rw [Polynomial.coeff_add, hU0, add_zero] at hne
    exact hne
  have hlead : V.coeff 2 * p.1.1.coeff 0 ^ (2 : ℕ) - U.coeff 2 ≠ 0 := by
    intro hz
    have hz3 : p.1.1.coeff 0 * (V.coeff 3 * p.1.1.coeff 0 ^ (2 : ℕ) + U.coeff 3) = 0 := by
      linear_combination E2p - p.1.1.coeff 1 * hz
    have hz3' : V.coeff 3 * p.1.1.coeff 0 ^ (2 : ℕ) + U.coeff 3 = 0 := by
      rcases mul_eq_zero.1 hz3 with h | h
      · exact absurd h ha₀
      · exact h
    refine hgen ?_
    linear_combination -V.coeff 3 * hz + V.coeff 2 * hz3'
  have h1 : p.1.1.coeff 1 = q.1.1.coeff 1 := by
    have hdiff : (p.1.1.coeff 1 - q.1.1.coeff 1)
        * (V.coeff 2 * p.1.1.coeff 0 ^ (2 : ℕ) - U.coeff 2) = 0 := by
      linear_combination E2p - E2q
        - (V.coeff 3 * (p.1.1.coeff 0 ^ (2 : ℕ) + p.1.1.coeff 0 * q.1.1.coeff 0
            + q.1.1.coeff 0 ^ (2 : ℕ)) + U.coeff 3) * h0
        - q.1.1.coeff 1 * V.coeff 2 * (p.1.1.coeff 0 + q.1.1.coeff 0) * h0
    rcases mul_eq_zero.1 hdiff with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hlead
  refine criticalFibre_fst_injective (by omega) (by omega) hU0 hV0 ?_
  show p.1.1 = q.1.1
  refine Polynomial.ext fun i => ?_
  match i with
  | 0 => exact h0
  | 1 => exact h1
  | (k + 2) =>
    rw [Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le p.2.1 (by exact_mod_cast (by omega : 2 ≤ k + 2))),
      Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le q.2.1 (by exact_mod_cast (by omega : 2 ≤ k + 2)))]

end Injective

/-! ## The bound -/

section Bound

/-- **At both depths two, with unrestricted observed packets, the fibre has at most the critical
binomial multiplicity of points.**  The genericity condition rules out the locus where the second
equation degenerates in the second jet coefficient. -/
theorem nat_card_criticalFibre_two_two_le {U V : K[X]}
    (hU : (X : K[X]) ^ (2 : ℕ) ∣ U) (hV : (X : K[X]) ^ (2 : ℕ) ∣ V) (hv₂ : V.coeff 2 ≠ 0)
    (hgen : U.coeff 2 * V.coeff 3 + U.coeff 3 * V.coeff 2 ≠ 0) :
    Nat.card (criticalFibre K 2 2 U V) ≤ criticalHorizonMultiplicity 2 2 := by
  classical
  set S : K[X] := criticalSextic (U.coeff 2) (U.coeff 3) (V.coeff 2) (V.coeff 3) with hS
  have hS0 : S ≠ 0 := criticalSextic_ne_zero hv₂
  have hmem : ∀ p : criticalFibre K 2 2 U V, p.1.1.coeff 0 ∈ S.roots.toFinset := fun p =>
    Multiset.mem_toFinset.2 ((Polynomial.mem_roots hS0).2 (isRoot_criticalSextic hU hV p))
  have hinj : Function.Injective
      (fun p : criticalFibre K 2 2 U V => (⟨p.1.1.coeff 0, hmem p⟩ : S.roots.toFinset)) :=
    fun p q h => coeff_zero_injective_two_two hU hV hgen (congrArg Subtype.val h)
  calc Nat.card (criticalFibre K 2 2 U V)
      ≤ Nat.card S.roots.toFinset := Nat.card_le_card_of_injective _ hinj
    _ = S.roots.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Multiset.card S.roots := Multiset.toFinset_card_le _
    _ ≤ S.natDegree := Polynomial.card_roots' S
    _ = 6 := by rw [hS, natDegree_criticalSextic hv₂]
    _ = criticalHorizonMultiplicity 2 2 := by
        rw [criticalHorizonMultiplicity]
        norm_num [Nat.choose]

end Bound


/-! ## Every root of the sextic is attained -/

section Surjective

/-- **A solution of the four scalar equations is a fibre point.** -/
theorem exists_criticalFibre_two_two_of_coeffs {U V : K[X]} (hU : (X : K[X]) ^ (2 : ℕ) ∣ U)
    (hV : (X : K[X]) ^ (2 : ℕ) ∣ V) {a₀ a₁ b₀ b₁ : K}
    (e0 : a₀ * b₀ = 1) (e1 : a₀ * b₁ + a₁ * b₀ = 0)
    (e2 : a₀ * V.coeff 2 + a₁ * b₁ + U.coeff 2 * b₀ = 0)
    (e3 : a₀ * V.coeff 3 + a₁ * V.coeff 2 + U.coeff 2 * b₁ + U.coeff 3 * b₀ = 0) :
    ∃ p : criticalFibre K 2 2 U V, p.1.1.coeff 0 = a₀ := by
  classical
  have hU0 : U.coeff 0 = 0 := Polynomial.X_pow_dvd_iff.1 hU 0 (by omega)
  have hU1 : U.coeff 1 = 0 := Polynomial.X_pow_dvd_iff.1 hU 1 (by omega)
  have hV0 : V.coeff 0 = 0 := Polynomial.X_pow_dvd_iff.1 hV 0 (by omega)
  have hV1 : V.coeff 1 = 0 := Polynomial.X_pow_dvd_iff.1 hV 1 (by omega)
  set A : K[X] := C a₁ * X + C a₀ with hA
  set B : K[X] := C b₁ * X + C b₀ with hB
  have hdegA : A.degree < ((2 : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_linear_le) (by exact_mod_cast one_lt_two)
  have hdegB : B.degree < ((2 : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_linear_le) (by exact_mod_cast one_lt_two)
  have hAU0 : (A + U).coeff 0 = a₀ := by simp [hA, hU0]
  have hAU1 : (A + U).coeff 1 = a₁ := by simp [hA, hU1]
  have hAU2 : (A + U).coeff 2 = U.coeff 2 := by simp [hA]
  have hAU3 : (A + U).coeff 3 = U.coeff 3 := by simp [hA]
  have hBV0 : (B + V).coeff 0 = b₀ := by simp [hB, hV0]
  have hBV1 : (B + V).coeff 1 = b₁ := by simp [hB, hV1]
  have hBV2 : (B + V).coeff 2 = V.coeff 2 := by simp [hB]
  have hBV3 : (B + V).coeff 3 = V.coeff 3 := by simp [hB]
  have hdvd : (X : K[X]) ^ (2 + 2) ∣ ((A + U) * (B + V) - 1) := by
    refine Polynomial.X_pow_dvd_iff.2 fun k hk => ?_
    rw [Polynomial.coeff_sub, coeff_mul_range]
    interval_cases k
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hAU0, hBV0,
        Polynomial.coeff_one_zero]
      linear_combination e0
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hAU0, hAU1, hBV0, hBV1,
        Polynomial.coeff_one]
      norm_num
      linear_combination e1
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hAU0, hAU1, hAU2,
        hBV0, hBV1, hBV2, Polynomial.coeff_one]
      norm_num
      linear_combination e2
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hAU0, hAU1, hAU2, hAU3,
        hBV0, hBV1, hBV2, hBV3, Polynomial.coeff_one]
      norm_num
      linear_combination e3
  refine ⟨⟨(A, B), hdegA, hdegB,
    (dvd_criticalLowProduct_sub_one_iff_mul_sub_one hU hV A B).2 hdvd⟩, ?_⟩
  simp [hA]

/-- **Every root of the sextic is the first jet coefficient of a fibre point.** -/
theorem exists_criticalFibre_of_isRoot {U V : K[X]} (hU : (X : K[X]) ^ (2 : ℕ) ∣ U)
    (hV : (X : K[X]) ^ (2 : ℕ) ∣ V) (hu₂ : U.coeff 2 ≠ 0)
    (hgen : U.coeff 2 * V.coeff 3 + U.coeff 3 * V.coeff 2 ≠ 0) {a₀ : K}
    (hroot : (criticalSextic (U.coeff 2) (U.coeff 3) (V.coeff 2) (V.coeff 3)).IsRoot a₀) :
    ∃ p : criticalFibre K 2 2 U V, p.1.1.coeff 0 = a₀ := by
  have hev : (V.coeff 2 * a₀ ^ (2 : ℕ) + U.coeff 2) * (V.coeff 2 * a₀ ^ (2 : ℕ) - U.coeff 2) ^ (2 : ℕ)
      - a₀ * (V.coeff 3 * a₀ ^ (2 : ℕ) + U.coeff 3) ^ (2 : ℕ) = 0 := by
    have := hroot
    simp only [Polynomial.IsRoot, criticalSextic, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] at this
    linear_combination this
  have ha₀ : a₀ ≠ 0 := by
    intro h0
    rw [h0] at hev
    refine hu₂ ?_
    have hcube : U.coeff 2 ^ (3 : ℕ) = 0 := by linear_combination hev
    exact pow_eq_zero_iff (n := 3) (by omega) |>.1 hcube
  have hD : V.coeff 2 * a₀ ^ (2 : ℕ) - U.coeff 2 ≠ 0 := by
    intro hz
    have hW : a₀ * (V.coeff 3 * a₀ ^ (2 : ℕ) + U.coeff 3) ^ (2 : ℕ) = 0 := by
      linear_combination -hev + (V.coeff 2 * a₀ ^ (2 : ℕ) + U.coeff 2)
        * (V.coeff 2 * a₀ ^ (2 : ℕ) - U.coeff 2) * hz
    have hW2 : (V.coeff 3 * a₀ ^ (2 : ℕ) + U.coeff 3) ^ (2 : ℕ) = 0 := by
      rcases mul_eq_zero.1 hW with h | h
      · exact absurd h ha₀
      · exact h
    have hW0 : V.coeff 3 * a₀ ^ (2 : ℕ) + U.coeff 3 = 0 := pow_eq_zero_iff (n := 2) (by omega) |>.1 hW2
    refine hgen ?_
    linear_combination -V.coeff 3 * hz + V.coeff 2 * hW0
  set D : K := V.coeff 2 * a₀ ^ (2 : ℕ) - U.coeff 2 with hDdef
  set a₁ : K := -a₀ * (V.coeff 3 * a₀ ^ (2 : ℕ) + U.coeff 3) / D with ha₁
  have hE2 : a₁ * D = -(a₀ * (V.coeff 3 * a₀ ^ (2 : ℕ) + U.coeff 3)) := by
    rw [ha₁]
    field_simp
  have hWD : a₀ * (V.coeff 3 * a₀ ^ (2 : ℕ) + U.coeff 3) ^ (2 : ℕ)
      = (V.coeff 2 * a₀ ^ (2 : ℕ) + U.coeff 2) * D ^ (2 : ℕ) := by
    linear_combination -hev
  have hE1 : a₁ ^ (2 : ℕ) = a₀ * (V.coeff 2 * a₀ ^ (2 : ℕ) + U.coeff 2) := by
    refine mul_right_cancel₀ (pow_ne_zero 2 hD) ?_
    calc a₁ ^ (2 : ℕ) * D ^ (2 : ℕ) = (a₁ * D) ^ (2 : ℕ) := by ring
      _ = a₀ ^ (2 : ℕ) * (V.coeff 3 * a₀ ^ (2 : ℕ) + U.coeff 3) ^ (2 : ℕ) := by rw [hE2]; ring
      _ = a₀ * (a₀ * (V.coeff 3 * a₀ ^ (2 : ℕ) + U.coeff 3) ^ (2 : ℕ)) := by ring
      _ = a₀ * ((V.coeff 2 * a₀ ^ (2 : ℕ) + U.coeff 2) * D ^ (2 : ℕ)) := by rw [hWD]
      _ = a₀ * (V.coeff 2 * a₀ ^ (2 : ℕ) + U.coeff 2) * D ^ (2 : ℕ) := by ring
  have hE2' : a₁ * (V.coeff 2 * a₀ ^ (2 : ℕ) - U.coeff 2)
      = -(a₀ * (V.coeff 3 * a₀ ^ (2 : ℕ) + U.coeff 3)) := by
    rw [← hDdef]
    exact hE2
  clear_value a₁ D
  refine exists_criticalFibre_two_two_of_coeffs hU hV (a₁ := a₁) (b₀ := a₀⁻¹)
    (b₁ := -a₁ / a₀ ^ (2 : ℕ)) ?_ ?_ ?_ ?_
  · field_simp
  · field_simp
    ring
  · field_simp
    linear_combination -hE1
  · field_simp
    linear_combination hE2'

end Surjective

/-! ## The exact count -/

section Exact

variable [IsAlgClosed K]

omit [IsAlgClosed K] in
/-- **The fibre at both depths two is in bijection with the distinct roots of the sextic.**  No
separability is assumed: the count is the number of distinct roots, whatever the sextic's
multiplicities. -/
theorem nat_card_criticalFibre_two_two_eq_card_roots [DecidableEq K] {U V : K[X]}
    (hU : (X : K[X]) ^ (2 : ℕ) ∣ U) (hV : (X : K[X]) ^ (2 : ℕ) ∣ V)
    (hu₂ : U.coeff 2 ≠ 0) (hv₂ : V.coeff 2 ≠ 0)
    (hgen : U.coeff 2 * V.coeff 3 + U.coeff 3 * V.coeff 2 ≠ 0) :
    Nat.card (criticalFibre K 2 2 U V)
      = ((criticalSextic (U.coeff 2) (U.coeff 3) (V.coeff 2) (V.coeff 3)).roots).toFinset.card := by
  set S : K[X] := criticalSextic (U.coeff 2) (U.coeff 3) (V.coeff 2) (V.coeff 3) with hS
  have hS0 : S ≠ 0 := criticalSextic_ne_zero hv₂
  have hmem : ∀ p : criticalFibre K 2 2 U V, p.1.1.coeff 0 ∈ S.roots.toFinset := fun p =>
    Multiset.mem_toFinset.2 ((Polynomial.mem_roots hS0).2 (isRoot_criticalSextic hU hV p))
  have hbij : Function.Bijective
      (fun p : criticalFibre K 2 2 U V => (⟨p.1.1.coeff 0, hmem p⟩ : S.roots.toFinset)) := by
    constructor
    · exact fun p q h => coeff_zero_injective_two_two hU hV hgen (congrArg Subtype.val h)
    · rintro ⟨a₀, ha₀⟩
      obtain ⟨p, hp⟩ := exists_criticalFibre_of_isRoot hU hV hu₂ hgen
        ((Polynomial.mem_roots hS0).1 (Multiset.mem_toFinset.1 ha₀))
      exact ⟨p, Subtype.ext hp⟩
  rw [Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- **The exact count at both depths two, for a general observed packet.**  The fibre is in
bijection with the roots of the sextic, and a separable sextic of degree six has six of them. -/
theorem nat_card_criticalFibre_two_two {U V : K[X]}
    (hU : (X : K[X]) ^ (2 : ℕ) ∣ U) (hV : (X : K[X]) ^ (2 : ℕ) ∣ V)
    (hu₂ : U.coeff 2 ≠ 0) (hv₂ : V.coeff 2 ≠ 0)
    (hgen : U.coeff 2 * V.coeff 3 + U.coeff 3 * V.coeff 2 ≠ 0)
    (hsep : (criticalSextic (U.coeff 2) (U.coeff 3) (V.coeff 2) (V.coeff 3)).Separable) :
    Nat.card (criticalFibre K 2 2 U V) = criticalHorizonMultiplicity 2 2 := by
  classical
  calc Nat.card (criticalFibre K 2 2 U V)
      = ((criticalSextic (U.coeff 2) (U.coeff 3) (V.coeff 2) (V.coeff 3)).roots).toFinset.card :=
        nat_card_criticalFibre_two_two_eq_card_roots hU hV hu₂ hv₂ hgen
    _ = (criticalSextic (U.coeff 2) (U.coeff 3) (V.coeff 2) (V.coeff 3)).natDegree :=
        card_roots_toFinset hsep (IsAlgClosed.splits _)
    _ = 6 := natDegree_criticalSextic hv₂
    _ = criticalHorizonMultiplicity 2 2 := by
        rw [criticalHorizonMultiplicity]
        norm_num [Nat.choose]


/-- **The exactness criterion at both depths two.**  The fibre attains the critical binomial
multiplicity exactly when the sextic has no repeated root — the count of distinct roots reaches the
degree precisely then. -/
theorem nat_card_criticalFibre_two_two_eq_iff [DecidableEq K] {U V : K[X]}
    (hU : (X : K[X]) ^ (2 : ℕ) ∣ U) (hV : (X : K[X]) ^ (2 : ℕ) ∣ V)
    (hu₂ : U.coeff 2 ≠ 0) (hv₂ : V.coeff 2 ≠ 0)
    (hgen : U.coeff 2 * V.coeff 3 + U.coeff 3 * V.coeff 2 ≠ 0) :
    Nat.card (criticalFibre K 2 2 U V) = criticalHorizonMultiplicity 2 2 ↔
      (criticalSextic (U.coeff 2) (U.coeff 3) (V.coeff 2) (V.coeff 3)).roots.Nodup := by
  set S : K[X] := criticalSextic (U.coeff 2) (U.coeff 3) (V.coeff 2) (V.coeff 3) with hS
  have hcard : Multiset.card S.roots = 6 := by
    rw [← (IsAlgClosed.splits S).natDegree_eq_card_roots]
    exact natDegree_criticalSextic hv₂
  have hmult : criticalHorizonMultiplicity 2 2 = 6 := by
    rw [criticalHorizonMultiplicity]
    norm_num [Nat.choose]
  rw [nat_card_criticalFibre_two_two_eq_card_roots hU hV hu₂ hv₂ hgen, hmult,
    ← hcard, Multiset.toFinset_card_eq_card_iff_nodup]


/-- **The depth-two exactness criterion in the separability phrasing.** -/
theorem nat_card_criticalFibre_two_two_eq_iff_separable [DecidableEq K] {U V : K[X]}
    (hU : (X : K[X]) ^ (2 : ℕ) ∣ U) (hV : (X : K[X]) ^ (2 : ℕ) ∣ V)
    (hu₂ : U.coeff 2 ≠ 0) (hv₂ : V.coeff 2 ≠ 0)
    (hgen : U.coeff 2 * V.coeff 3 + U.coeff 3 * V.coeff 2 ≠ 0) :
    Nat.card (criticalFibre K 2 2 U V) = criticalHorizonMultiplicity 2 2 ↔
      (criticalSextic (U.coeff 2) (U.coeff 3) (V.coeff 2) (V.coeff 3)).Separable := by
  rw [nat_card_criticalFibre_two_two_eq_iff hU hV hu₂ hv₂ hgen,
    Polynomial.nodup_roots_iff_of_splits (criticalSextic_ne_zero hv₂) (IsAlgClosed.splits _)]


/-- **A degenerate sextic strictly loses jets at both depths two.** -/
theorem nat_card_criticalFibre_two_two_lt_of_not_separable [DecidableEq K] {U V : K[X]}
    (hU : (X : K[X]) ^ (2 : ℕ) ∣ U) (hV : (X : K[X]) ^ (2 : ℕ) ∣ V)
    (hu₂ : U.coeff 2 ≠ 0) (hv₂ : V.coeff 2 ≠ 0)
    (hgen : U.coeff 2 * V.coeff 3 + U.coeff 3 * V.coeff 2 ≠ 0)
    (hsep : ¬ (criticalSextic (U.coeff 2) (U.coeff 3) (V.coeff 2) (V.coeff 3)).Separable) :
    Nat.card (criticalFibre K 2 2 U V) < criticalHorizonMultiplicity 2 2 := by
  have hle := nat_card_criticalFibre_two_two_le hU hV hv₂ hgen
  have hne : Nat.card (criticalFibre K 2 2 U V) ≠ criticalHorizonMultiplicity 2 2 := fun h =>
    hsep ((nat_card_criticalFibre_two_two_eq_iff_separable hU hV hu₂ hv₂ hgen).1 h)
  omega

end Exact


/-! ## Finiteness at both depths two, with no genericity at all -/

section Unconditional

/-- **At both depths two the fibre is finite for every critical observation.**  The first jet
coefficient is a root of the sextic, and the first equation determines the second coefficient up to
sign, so the fibre injects into a set of at most twelve pairs.  No genericity condition is used
beyond criticality of the observed reciprocal packet. -/
theorem nat_card_criticalFibre_two_two_le_of_critical {U V : K[X]}
    (hU : (X : K[X]) ^ (2 : ℕ) ∣ U) (hV : (X : K[X]) ^ (2 : ℕ) ∣ V) (hv₂ : V.coeff 2 ≠ 0) :
    Nat.card (criticalFibre K 2 2 U V) ≤ 12 := by
  classical
  set S : K[X] := criticalSextic (U.coeff 2) (U.coeff 3) (V.coeff 2) (V.coeff 3) with hS
  have hS0 : S ≠ 0 := criticalSextic_ne_zero hv₂
  have hU0 : U.coeff 0 = 0 := Polynomial.X_pow_dvd_iff.1 hU 0 (by omega)
  have hV0 : V.coeff 0 = 0 := Polynomial.X_pow_dvd_iff.1 hV 0 (by omega)
  set R : Finset K := S.roots.toFinset with hR
  set Q : K → K[X] := fun a => X ^ (2 : ℕ) - C (V.coeff 2 * a ^ (3 : ℕ) + U.coeff 2 * a) with hQ
  have hQ0 : ∀ a : K, Q a ≠ 0 := by
    intro a h0
    have hdeg : (Q a).natDegree = 2 := by
      have hlt : (C (V.coeff 2 * a ^ (3 : ℕ) + U.coeff 2 * a) : K[X]).natDegree
          < ((X : K[X]) ^ (2 : ℕ)).natDegree := by
        rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
        omega
      rw [hQ, Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  set T : Finset (K × K) :=
    R.biUnion (fun a => ((Q a).roots.toFinset).image (fun b => (a, b))) with hT
  have hmem : ∀ q : criticalFibre K 2 2 U V, (q.1.1.coeff 0, q.1.1.coeff 1) ∈ T := by
    intro q
    obtain ⟨E1, -⟩ := fibre_two_two_eliminated hU hV q
    refine Finset.mem_biUnion.2 ⟨q.1.1.coeff 0, ?_, Finset.mem_image.2 ⟨q.1.1.coeff 1, ?_, rfl⟩⟩
    · exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots hS0).2 (isRoot_criticalSextic hU hV q))
    · refine Multiset.mem_toFinset.2 ((Polynomial.mem_roots (hQ0 _)).2 ?_)
      simp only [hQ, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      linear_combination -E1
  have hinj : Function.Injective
      (fun q : criticalFibre K 2 2 U V => (⟨(q.1.1.coeff 0, q.1.1.coeff 1), hmem q⟩ : T)) := by
    intro q r hqr
    have hpair : (q.1.1.coeff 0, q.1.1.coeff 1) = (r.1.1.coeff 0, r.1.1.coeff 1) :=
      congrArg Subtype.val hqr
    refine criticalFibre_fst_injective (by omega) (by omega) hU0 hV0 ?_
    show q.1.1 = r.1.1
    refine Polynomial.ext fun i => ?_
    match i with
    | 0 => exact congrArg Prod.fst hpair
    | 1 => exact congrArg Prod.snd hpair
    | (k + 2) =>
      rw [Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le q.2.1 (by exact_mod_cast (by omega : 2 ≤ k + 2))),
        Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le r.2.1 (by exact_mod_cast (by omega : 2 ≤ k + 2)))]
  have hRcard : R.card ≤ 6 := by
    calc R.card ≤ Multiset.card S.roots := Multiset.toFinset_card_le _
      _ ≤ S.natDegree := Polynomial.card_roots' _
      _ = 6 := by rw [hS, natDegree_criticalSextic hv₂]
  have hTcard : T.card ≤ 12 := by
    refine le_trans (Finset.card_biUnion_le) ?_
    calc ∑ a ∈ R, (((Q a).roots.toFinset).image (fun b => (a, b))).card
        ≤ ∑ _a ∈ R, 2 := by
          refine Finset.sum_le_sum fun a _ => ?_
          refine le_trans (Finset.card_image_le) ?_
          calc ((Q a).roots.toFinset).card ≤ Multiset.card (Q a).roots :=
                Multiset.toFinset_card_le _
            _ ≤ (Q a).natDegree := Polynomial.card_roots' _
            _ ≤ 2 := by
                rw [hQ]
                refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
                rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
                simp
      _ = 2 * R.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 12 := by omega
  calc Nat.card (criticalFibre K 2 2 U V)
      ≤ Nat.card T := Nat.card_le_card_of_injective _ hinj
    _ = T.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 12 := hTcard

end Unconditional

end GaloisForLFunctions.HTGeometry
