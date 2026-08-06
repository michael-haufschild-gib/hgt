import GaloisForLFunctions.HTGeometry.HorizonTruncationCancel

/-!
# The fibre over a reciprocal is a rank drop

Fix the reciprocal `Q` of an observation.  The truncated compatibility equation is *linear* in the
unknown low part of the jet, so a compatible jet exists exactly when the `m + 1` elements

`Q, t Q, ..., t^(m-1) Q, 1 - U Q`

of `K[t]/t^L` are linearly dependent: a dependency whose last coefficient is nonzero normalises to
the compatibility equation itself, and a dependency whose last coefficient vanishes would divide the
horizon by a unit.

This turns the fibre count into the count of the points of the reciprocal space at which a matrix
with entries linear in the reciprocal drops rank, which is the form in which the expected count is a
determinantal degree rather than a Bezout number.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] {m L : ℕ}

/-- The coefficients of a polynomial written in the monomial basis. -/
theorem coeff_sum_range_C_mul_X_pow (c : ℕ → K) (N i : ℕ) :
    (∑ j ∈ Finset.range N, C (c j) * X ^ j).coeff i = if i < N then c i else 0 := by
  rw [Polynomial.finsetSum_coeff]
  by_cases hi : i < N
  · rw [if_pos hi, Finset.sum_eq_single i]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hb), mul_zero]
    · intro hmem
      exact absurd (Finset.mem_range.2 hi) hmem
  · rw [if_neg hi, Finset.sum_eq_zero]
    intro j hj
    have hij : i ≠ j := fun h => hi (h ▸ Finset.mem_range.1 hj)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hij, mul_zero]

/-- A polynomial written in the monomial basis below a degree has degree below it. -/
theorem degree_sum_range_C_mul_X_pow_lt (c : ℕ → K) (N : ℕ) :
    (∑ j ∈ Finset.range N, C (c j) * X ^ j).degree < ((N : ℕ) : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe N)).2 fun i hi => ?_
  calc (C (c i) * X ^ i).degree ≤ (X ^ i : K[X]).degree := by
        rw [← Polynomial.smul_eq_C_mul]
        exact Polynomial.degree_smul_le _ _
    _ = ((i : ℕ) : WithBot ℕ) := Polynomial.degree_X_pow i
    _ < ((N : ℕ) : WithBot ℕ) := by exact_mod_cast Finset.mem_range.1 hi

/-- A polynomial below a degree is the sum of its low monomials. -/
theorem sum_range_C_coeff_mul_X_pow {Λ : K[X]} (hΛ : Λ.degree < (m : ℕ)) :
    (∑ i ∈ Finset.range m, C (Λ.coeff i) * X ^ i) = Λ := by
  rcases eq_or_ne Λ 0 with h0 | h0
  · simp [h0]
  · have hnat : Λ.natDegree < m := (Polynomial.natDegree_lt_iff_degree_lt h0).2 hΛ
    rw [show (∑ i ∈ Finset.range m, C (Λ.coeff i) * X ^ i)
        = ∑ i ∈ Finset.range m, Polynomial.monomial i (Λ.coeff i) from
      Finset.sum_congr rfl fun i _ => Polynomial.C_mul_X_pow_eq_monomial]
    exact (Polynomial.as_sum_range' Λ m hnat).symm

/-- **A compatible jet is exactly a dependency of the shifted reciprocals with the correction.**
The forward direction takes the compatibility equation itself as the dependency, with last
coefficient `-1`; the backward direction divides by that coefficient, which cannot vanish because
the reciprocal is invertible at the origin. -/
theorem exists_fibre_iff_dependent (hmL : m ≤ L) {U Q : K[X]} (hQ : Q.coeff 0 ≠ 0) :
    (∃ A : K[X], A.degree < (m : ℕ) ∧ (X : K[X]) ^ L ∣ ((A + U) * Q - 1)) ↔
      (∃ (Λ : K[X]) (μ : K), Λ.degree < (m : ℕ) ∧ (Λ ≠ 0 ∨ μ ≠ 0) ∧
        (X : K[X]) ^ L ∣ (Λ * Q + C μ * (1 - U * Q))) := by
  constructor
  · rintro ⟨A, hA, hdvd⟩
    refine ⟨A, -1, hA, Or.inr (by simp), ?_⟩
    have hid : A * Q + C (-1 : K) * (1 - U * Q) = (A + U) * Q - 1 := by
      rw [map_neg, map_one]
      ring
    rw [hid]
    exact hdvd
  · rintro ⟨Λ, μ, hΛ, hne, hdvd⟩
    have hμ : μ ≠ 0 := by
      rcases hne with hΛ0 | hμ0
      · by_contra hμ0
        rw [hμ0, map_zero, zero_mul, add_zero] at hdvd
        have hdvdΛ : (X : K[X]) ^ L ∣ Λ :=
          dvd_of_mul_dvd_of_coeff_zero_ne_zero hQ (by rwa [mul_comm] at hdvd)
        have hmLb : ((m : ℕ) : WithBot ℕ) ≤ ((L : ℕ) : WithBot ℕ) := by exact_mod_cast hmL
        refine hΛ0 (Polynomial.eq_zero_of_dvd_of_degree_lt hdvdΛ ?_)
        rw [Polynomial.degree_X_pow]
        exact lt_of_lt_of_le hΛ hmLb
      · exact hμ0
    refine ⟨C (-μ⁻¹) * Λ, ?_, ?_⟩
    · refine lt_of_le_of_lt ?_ hΛ
      rw [← Polynomial.smul_eq_C_mul]
      exact Polynomial.degree_smul_le _ _
    · have hid : (C (-μ⁻¹) * Λ + U) * Q - 1
          = C (-μ⁻¹) * (Λ * Q + C μ * (1 - U * Q)) := by
        have hcc : (C (-μ⁻¹) : K[X]) * C μ = -1 := by
          have hval : (-μ⁻¹) * μ = -1 := by rw [neg_mul, inv_mul_cancel₀ hμ]
          rw [← C_mul, hval, map_neg, map_one]
        calc (C (-μ⁻¹) * Λ + U) * Q - 1
            = C (-μ⁻¹) * (Λ * Q) + (U * Q - 1) := by ring
          _ = C (-μ⁻¹) * (Λ * Q) + (C (-μ⁻¹) * C μ) * (1 - U * Q) := by
              rw [hcc]; ring
          _ = C (-μ⁻¹) * (Λ * Q + C μ * (1 - U * Q)) := by ring
      rw [hid]
      exact Dvd.dvd.mul_left hdvd _

/-- **The dependency written in coordinates.**  The `m` shifts of the reciprocal and the correction
term are `m + 1` explicit elements below the horizon, and the criterion is the vanishing of a
nontrivial linear combination of them. -/
theorem exists_fibre_iff_dependent_coeffs (hmL : m ≤ L) {U Q : K[X]} (hQ : Q.coeff 0 ≠ 0) :
    (∃ A : K[X], A.degree < (m : ℕ) ∧ (X : K[X]) ^ L ∣ ((A + U) * Q - 1)) ↔
      (∃ (lam : ℕ → K) (μ : K), ((∃ i, i < m ∧ lam i ≠ 0) ∨ μ ≠ 0) ∧
        (X : K[X]) ^ L ∣
          ((∑ i ∈ Finset.range m, C (lam i) * X ^ i) * Q + C μ * (1 - U * Q))) := by
  rw [exists_fibre_iff_dependent hmL hQ]
  constructor
  · rintro ⟨Λ, μ, hΛ, hne, hdvd⟩
    refine ⟨fun i => Λ.coeff i, μ, ?_, ?_⟩
    · rcases hne with hΛ0 | hμ0
      · refine Or.inl ?_
        by_contra hall
        push Not at hall
        refine hΛ0 (Polynomial.ext fun i => ?_)
        rcases lt_or_ge i m with hi | hi
        · rw [hall i hi, Polynomial.coeff_zero]
        · rw [Polynomial.coeff_eq_zero_of_degree_lt
            (lt_of_lt_of_le hΛ (by exact_mod_cast hi)), Polynomial.coeff_zero]
      · exact Or.inr hμ0
    · rwa [sum_range_C_coeff_mul_X_pow hΛ]
  · rintro ⟨lam, μ, hne, hdvd⟩
    refine ⟨∑ i ∈ Finset.range m, C (lam i) * X ^ i, μ, ?_, ?_, hdvd⟩
    · exact degree_sum_range_C_mul_X_pow_lt lam m
    · rcases hne with ⟨i, him, hlam⟩ | hμ0
      · refine Or.inl fun h0 => hlam ?_
        have := congrArg (fun p => Polynomial.coeff p i) h0
        simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          Finset.sum_ite_eq' (Finset.range m) i, Finset.mem_range, him] using this
      · exact Or.inr hμ0

end GaloisForLFunctions.HTGeometry
