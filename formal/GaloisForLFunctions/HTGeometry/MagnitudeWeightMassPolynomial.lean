import GaloisForLFunctions.HTGeometry.MagnitudeAtomGrading
import GaloisForLFunctions.HTGeometry.MagnitudeMonomialSurvival

/-!
# Polynomial mass bound for magnitude-grouped Taylor coefficients

This module bounds the total norm mass of the grouped Leibniz weights attached
to a differential polynomial by a fixed polynomial in the coefficient level.
The single-power form is designed for comparison with superlacunary valuation
gaps in magnitude-survival arguments.
-/

open PowerSeries MvPolynomial Finset

namespace GaloisForLFunctions

noncomputable section

/-- Largest number of dependent-variable factors in a monomial of `Q`. -/
def magnitudeMaxJetDegree (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) : ℕ :=
  Q.support.sup fun m => ∑ j : Fin (n + 1), m j.succ

/-- Largest total derivative order in a monomial of `Q`. -/
def magnitudeMaxJetOrder (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) : ℕ :=
  Q.support.sup fun m => ∑ j : Fin (n + 1), (j : ℕ) * m j.succ

/-- Total norm mass of the polynomial coefficients of `Q`. -/
def magnitudeCoefficientMass {n : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ) : ℝ :=
  ∑ m ∈ Q.support, ‖MvPolynomial.coeff m Q‖

theorem jetDegree_le_magnitudeMaxJetDegree {n : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {m : Fin (n + 2) →₀ ℕ}
    (hm : m ∈ Q.support) :
    (∑ j : Fin (n + 1), m j.succ) ≤ magnitudeMaxJetDegree n Q := by
  exact Finset.le_sup (f := fun m => ∑ j : Fin (n + 1), m j.succ) hm

theorem jetOrder_le_magnitudeMaxJetOrder {n : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {m : Fin (n + 2) →₀ ℕ}
    (hm : m ∈ Q.support) :
    (∑ j : Fin (n + 1), (j : ℕ) * m j.succ) ≤ magnitudeMaxJetOrder n Q := by
  exact Finset.le_sup (f := fun m => ∑ j : Fin (n + 1), (j : ℕ) * m j.succ) hm

theorem flatOrder_le_magnitudeMaxJetOrder {n : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {m : Fin (n + 2) →₀ ℕ}
    (hm : m ∈ Q.support) (t : Fin (∑ j : Fin (n + 1), m j.succ)) :
    flatOrder (fun j => m j.succ) t ≤ magnitudeMaxJetOrder n Q := by
  calc
    flatOrder (fun j => m j.succ) t
        ≤ ∑ i, flatOrder (fun j => m j.succ) i :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    _ = ∑ j : Fin (n + 1), (j : ℕ) * m j.succ := flatOrder_sum _
    _ ≤ magnitudeMaxJetOrder n Q := jetOrder_le_magnitudeMaxJetOrder Q hm

theorem atomDescProd_norm_le {n N : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (x : Σ m : Fin (n + 2) →₀ ℕ, Fin (∑ j : Fin (n + 1), m j.succ) →₀ ℕ)
    (hx : x ∈ sigmaIdx n N Q) :
    ‖atomDescProd n x‖ ≤
      (((N + magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ) := by
  classical
  rw [sigmaIdx, Finset.mem_sigma] at hx
  obtain ⟨hm, hl⟩ := hx
  have hmQ : x.1 ∈ Q.support := (Finset.mem_filter.mp hm).1
  have hlsum := (Finset.mem_finsuppAntidiag.mp hl).1
  have hleN : ∀ t, x.2 t ≤ N := by
    intro t
    calc
      x.2 t ≤ ∑ i, x.2 i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      _ = N - x.1 0 := hlsum
      _ ≤ N := Nat.sub_le _ _
  rw [atomDescProd, norm_prod]
  have hfactor : ∀ t,
      ‖(((x.2 t + flatOrder (fun j => x.1 j.succ) t).descFactorial
          (flatOrder (fun j => x.1 j.succ) t) : ℂ))‖ ≤
        (((N + magnitudeMaxJetOrder n Q + 1) ^
          (flatOrder (fun j => x.1 j.succ) t) : ℕ) : ℝ) := by
    intro t
    rw [Complex.norm_natCast]
    exact_mod_cast calc
      (x.2 t + flatOrder (fun j => x.1 j.succ) t).descFactorial
          (flatOrder (fun j => x.1 j.succ) t)
          ≤ (x.2 t + flatOrder (fun j => x.1 j.succ) t) ^
              (flatOrder (fun j => x.1 j.succ) t) := Nat.descFactorial_le_pow _ _
      _ ≤ (N + magnitudeMaxJetOrder n Q + 1) ^
              (flatOrder (fun j => x.1 j.succ) t) := by
            apply Nat.pow_le_pow_left
            exact (Nat.add_le_add (hleN t)
              (flatOrder_le_magnitudeMaxJetOrder Q hmQ t)).trans (Nat.le_succ _)
  calc
    ∏ t, ‖(((x.2 t + flatOrder (fun j => x.1 j.succ) t).descFactorial
          (flatOrder (fun j => x.1 j.succ) t) : ℂ))‖
        ≤ ∏ t, (((N + magnitudeMaxJetOrder n Q + 1) ^
          (flatOrder (fun j => x.1 j.succ) t) : ℕ) : ℝ) :=
            Finset.prod_le_prod (fun t _ => norm_nonneg _) (fun t _ => hfactor t)
    _ = (((N + magnitudeMaxJetOrder n Q + 1) ^
          (∑ t, flatOrder (fun j => x.1 j.succ) t) : ℕ) : ℝ) := by
            push_cast
            rw [← Finset.prod_pow_eq_pow_sum]
    _ ≤ (((N + magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ) := by
          exact_mod_cast Nat.pow_le_pow_right (by omega)
            (by rw [flatOrder_sum]; exact jetOrder_le_magnitudeMaxJetOrder Q hmQ)

theorem sigmaIdx_card_le {n N : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    (sigmaIdx n N Q).card ≤
      Q.support.card * (N + 1) ^ magnitudeMaxJetDegree n Q := by
  classical
  rw [sigmaIdx, Finset.card_sigma]
  calc
    ∑ m ∈ Q.support.filter (fun m => m 0 ≤ N),
          ((Finset.univ : Finset (Fin (∑ j : Fin (n + 1), m j.succ))).finsuppAntidiag
            (N - m 0)).card
        ≤ ∑ _m ∈ Q.support.filter (fun m => m 0 ≤ N),
            (N + 1) ^ magnitudeMaxJetDegree n Q := by
          apply Finset.sum_le_sum
          intro m hm
          have hmQ := (Finset.mem_filter.mp hm).1
          calc
            ((Finset.univ : Finset (Fin (∑ j : Fin (n + 1), m j.succ))).finsuppAntidiag
              (N - m 0)).card
                ≤ (N - m 0 + 1) ^ (∑ j : Fin (n + 1), m j.succ) := antidiag_card_le
            _ ≤ (N + 1) ^ (∑ j : Fin (n + 1), m j.succ) := by
                exact Nat.pow_le_pow_left
                  (Nat.add_le_add_right (Nat.sub_le N (m 0)) 1) _
            _ ≤ (N + 1) ^ magnitudeMaxJetDegree n Q := by
                exact Nat.pow_le_pow_right (by omega)
                  (jetDegree_le_magnitudeMaxJetDegree Q hmQ)
    _ = (Q.support.filter (fun m => m 0 ≤ N)).card *
          (N + 1) ^ magnitudeMaxJetDegree n Q := by simp
    _ ≤ Q.support.card * (N + 1) ^ magnitudeMaxJetDegree n Q := by
          exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)

/-- The total grouped Leibniz-weight mass grows at most polynomially with the coefficient level. -/
theorem aevalWeight_mass_le_polynomial (n : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (N : ℕ) :
    (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖)
      ≤ magnitudeCoefficientMass Q *
        (((N + 1) ^ magnitudeMaxJetDegree n Q : ℕ) : ℝ) *
        (((N + magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ) := by
  classical
  refine (aevalWeight_mass_le n N Q).trans ?_
  rw [sigmaIdx, Finset.sum_sigma]
  calc
    ∑ m ∈ Q.support.filter (fun m => m 0 ≤ N),
        ∑ l ∈ (Finset.univ : Finset (Fin (∑ j : Fin (n + 1), m j.succ))).finsuppAntidiag
            (N - m 0),
          ‖MvPolynomial.coeff m Q‖ *
            ‖atomDescProd n ⟨m, l⟩‖
      ≤ ∑ m ∈ Q.support.filter (fun m => m 0 ≤ N),
          ‖MvPolynomial.coeff m Q‖ *
            ((((N + 1) ^ magnitudeMaxJetDegree n Q : ℕ) : ℝ) *
              (((N + magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro m hm
        have hmQ := (Finset.mem_filter.mp hm).1
        calc
          ∑ l ∈ (Finset.univ : Finset (Fin (∑ j : Fin (n + 1), m j.succ))).finsuppAntidiag
              (N - m 0),
            ‖MvPolynomial.coeff m Q‖ * ‖atomDescProd n ⟨m, l⟩‖
            ≤ ∑ _l ∈ (Finset.univ : Finset (Fin (∑ j : Fin (n + 1), m j.succ))).finsuppAntidiag
                (N - m 0),
              ‖MvPolynomial.coeff m Q‖ *
                (((N + magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ) := by
                  apply Finset.sum_le_sum
                  intro l hl
                  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
                  apply atomDescProd_norm_le Q ⟨m, l⟩
                  rw [sigmaIdx, Finset.mem_sigma]
                  exact ⟨hm, hl⟩
          _ = (((Finset.univ : Finset (Fin (∑ j : Fin (n + 1), m j.succ))).finsuppAntidiag
                (N - m 0)).card : ℝ) *
              (‖MvPolynomial.coeff m Q‖ *
                (((N + magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ)) := by
                  simp
          _ ≤ (((N + 1) ^ magnitudeMaxJetDegree n Q : ℕ) : ℝ) *
              (‖MvPolynomial.coeff m Q‖ *
                (((N + magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ)) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact_mod_cast calc
                    ((Finset.univ : Finset (Fin (∑ j : Fin (n + 1), m j.succ))).finsuppAntidiag
                        (N - m 0)).card
                      ≤ (N - m 0 + 1) ^ (∑ j : Fin (n + 1), m j.succ) := antidiag_card_le
                    _ ≤ (N + 1) ^ (∑ j : Fin (n + 1), m j.succ) :=
                      Nat.pow_le_pow_left
                        (Nat.add_le_add_right (Nat.sub_le N (m 0)) 1) _
                    _ ≤ (N + 1) ^ magnitudeMaxJetDegree n Q :=
                      Nat.pow_le_pow_right (by omega) (jetDegree_le_magnitudeMaxJetDegree Q hmQ)
          _ = ‖MvPolynomial.coeff m Q‖ *
              ((((N + 1) ^ magnitudeMaxJetDegree n Q : ℕ) : ℝ) *
                (((N + magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ)) := by
                  ring
    _ ≤ ∑ m ∈ Q.support,
          ‖MvPolynomial.coeff m Q‖ *
            ((((N + 1) ^ magnitudeMaxJetDegree n Q : ℕ) : ℝ) *
              (((N + magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro m _ _
        positivity
    _ = magnitudeCoefficientMass Q *
        (((N + 1) ^ magnitudeMaxJetDegree n Q : ℕ) : ℝ) *
        (((N + magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ) := by
          rw [magnitudeCoefficientMass]
          simp_rw [mul_assoc]
          rw [← Finset.sum_mul]

/-- A single-power version of `aevalWeight_mass_le_polynomial`, convenient for logarithmic
domination: the total mass is bounded by a fixed constant times
`(N+1)^(maxJetDegree+maxJetOrder)`. -/
theorem aevalWeight_mass_le_singlePolynomial (n : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (N : ℕ) :
    (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖)
      ≤ magnitudeCoefficientMass Q *
          (((magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ) *
          (((N + 1) ^ (magnitudeMaxJetDegree n Q + magnitudeMaxJetOrder n Q) : ℕ) : ℝ) := by
  have hbase : N + magnitudeMaxJetOrder n Q + 1 ≤
      (magnitudeMaxJetOrder n Q + 1) * (N + 1) := by
    nlinarith [Nat.zero_le N, Nat.zero_le (magnitudeMaxJetOrder n Q)]
  refine (aevalWeight_mass_le_polynomial n Q N).trans ?_
  have hpow : (N + magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q ≤
      ((magnitudeMaxJetOrder n Q + 1) * (N + 1)) ^ magnitudeMaxJetOrder n Q :=
    Nat.pow_le_pow_left hbase _
  have hcoeff : 0 ≤ magnitudeCoefficientMass Q := by
    rw [magnitudeCoefficientMass]
    positivity
  have hcast :
      ((((N + magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ)) ≤
        (((((magnitudeMaxJetOrder n Q + 1) * (N + 1)) ^
          magnitudeMaxJetOrder n Q : ℕ) : ℝ)) := by
    exact_mod_cast hpow
  calc
    magnitudeCoefficientMass Q *
          (((N + 1) ^ magnitudeMaxJetDegree n Q : ℕ) : ℝ) *
          (((N + magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ)
      ≤ magnitudeCoefficientMass Q *
          (((N + 1) ^ magnitudeMaxJetDegree n Q : ℕ) : ℝ) *
          (((((magnitudeMaxJetOrder n Q + 1) * (N + 1)) ^
            magnitudeMaxJetOrder n Q : ℕ) : ℝ)) := by
        gcongr
    _ = magnitudeCoefficientMass Q *
          (((magnitudeMaxJetOrder n Q + 1) ^ magnitudeMaxJetOrder n Q : ℕ) : ℝ) *
          (((N + 1) ^ (magnitudeMaxJetDegree n Q + magnitudeMaxJetOrder n Q) : ℕ) : ℝ) := by
        push_cast
        rw [mul_pow, pow_add]
        ring

end

end GaloisForLFunctions

