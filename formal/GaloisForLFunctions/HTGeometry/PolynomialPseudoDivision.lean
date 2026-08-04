import Mathlib.Algebra.Polynomial.Div

/-!
# Pseudo-division of polynomials over a domain

Division with remainder needs the leading coefficient of the divisor to be invertible.  Over a domain
one multiplies the dividend by a power of that leading coefficient instead: for every `A` and every
nonzero `B` there are `k`, `Q`, `S` with

`B.leadingCoeff ^ k • A = Q * B + S`,  `deg S < deg B`.

mathlib divides only by monic polynomials, so this is new.  It is the engine of reduction algorithms
in differential algebra, where the divisor's leading coefficient — the initial of a differential
polynomial — is a polynomial rather than a unit.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Pseudo-division.**  Multiplying by a power of the divisor's leading coefficient makes division
with remainder possible over any domain. -/
theorem exists_pseudo_div (B : R[X]) (hB : B ≠ 0) (A : R[X]) :
    ∃ (k : ℕ) (Q S : R[X]), B.leadingCoeff ^ k • A = Q * B + S ∧ S.degree < B.degree := by
  classical
  have hb : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hB
  have hBbot : B.degree ≠ ⊥ := fun h => hB (degree_eq_bot.1 h)
  suffices H : ∀ n : ℕ, ∀ A : R[X], A.natDegree < n →
      ∃ (k : ℕ) (Q S : R[X]), B.leadingCoeff ^ k • A = Q * B + S ∧ S.degree < B.degree by
    exact H (A.natDegree + 1) A (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => exact fun A hA => absurd hA (Nat.not_lt_zero _)
  | succ n ih =>
      intro A hA
      by_cases hlt : A.degree < B.degree
      · exact ⟨0, 0, A, by simp, hlt⟩
      push Not at hlt
      have hA0 : A ≠ 0 := by
        intro h0
        rw [h0, degree_zero] at hlt
        exact hBbot (le_bot_iff.1 hlt)
      have ha : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hA0
      have hBdeg : B.degree = (B.natDegree : WithBot ℕ) := degree_eq_natDegree hB
      have hAdeg : A.degree = (A.natDegree : WithBot ℕ) := degree_eq_natDegree hA0
      have hle : B.natDegree ≤ A.natDegree := by
        rw [hBdeg, hAdeg] at hlt
        exact_mod_cast hlt
      set m := A.natDegree - B.natDegree with hm
      set C : R[X] := B.leadingCoeff • A - A.leadingCoeff • (X ^ m * B) with hC
      have hmul : (X ^ m * B).degree = (A.natDegree : WithBot ℕ) := by
        rw [degree_mul, degree_X_pow, hBdeg, hm, ← Nat.cast_add, Nat.sub_add_cancel hle]
      have hdeg1 : (B.leadingCoeff • A).degree = (A.natDegree : WithBot ℕ) := by
        rw [smul_eq_C_mul, degree_mul, degree_C hb, zero_add, hAdeg]
      have hdeg2 : (A.leadingCoeff • (X ^ m * B)).degree = (A.natDegree : WithBot ℕ) := by
        rw [smul_eq_C_mul, degree_mul, degree_C ha, zero_add, hmul]
      have hlead1 : (B.leadingCoeff • A).leadingCoeff = B.leadingCoeff * A.leadingCoeff := by
        rw [smul_eq_C_mul, leadingCoeff_mul, leadingCoeff_C]
      have hlead2 : (A.leadingCoeff • (X ^ m * B)).leadingCoeff
          = B.leadingCoeff * A.leadingCoeff := by
        rw [smul_eq_C_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_mul,
          leadingCoeff_X_pow, one_mul]
        ring
      by_cases hC0 : C = 0
      · refine ⟨1, A.leadingCoeff • X ^ m, 0, ?_, ?_⟩
        · have := sub_eq_zero.1 hC0
          rw [pow_one, this]
          simp [smul_eq_C_mul]
          ring
        · simpa using Ne.bot_lt hBbot
      · have hCdeg : C.degree < (A.natDegree : WithBot ℕ) := by
          rw [hC]
          have hsub := degree_sub_lt (hdeg1.trans hdeg2.symm) (smul_ne_zero hb hA0)
            (hlead1.trans hlead2.symm)
          rwa [hdeg1] at hsub
        have hCnat : C.natDegree < A.natDegree := by
          have hCd : C.degree = (C.natDegree : WithBot ℕ) := degree_eq_natDegree hC0
          rw [hCd] at hCdeg
          exact_mod_cast hCdeg
        obtain ⟨k, Q', S', hQS, hS⟩ := ih C (lt_of_lt_of_le hCnat (Nat.lt_succ_iff.1 hA))
        refine ⟨k + 1, Q' + (B.leadingCoeff ^ k * A.leadingCoeff) • X ^ m, S', ?_, hS⟩
        have hCA : B.leadingCoeff • A = C + A.leadingCoeff • (X ^ m * B) := by
          rw [hC]
          ring
        calc B.leadingCoeff ^ (k + 1) • A
            = B.leadingCoeff ^ k • (B.leadingCoeff • A) := by
              rw [pow_succ, mul_smul]
          _ = B.leadingCoeff ^ k • C
              + B.leadingCoeff ^ k • (A.leadingCoeff • (X ^ m * B)) := by
              rw [hCA, smul_add]
          _ = (Q' * B + S') + (B.leadingCoeff ^ k * A.leadingCoeff) • (X ^ m * B) := by
              rw [hQS, smul_smul]
          _ = (Q' + (B.leadingCoeff ^ k * A.leadingCoeff) • X ^ m) * B + S' := by
              rw [smul_eq_C_mul, smul_eq_C_mul]
              ring

end

end GaloisForLFunctions.HTGeometry
