import GaloisForLFunctions.RHTower.Sieve.MaynardCanonicalHuxley
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedRaise

/-!
# Canonical Huxley estimate on one aggregate-selection fibre

This composes finite-label robust selection, common bounded raising, weighted coefficient energy,
canonical Huxley scheduling, and sigma-uniform absorption.  For one nonempty color fibre, only the
explicit sigma-free energy scale inequality remains.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- The raised lower edge automatically dominates the complete Huxley height. -/
theorem maynard_huxley_square_height_of_raise
    {T0 Y : ℝ} (hT0 : 1 < T0)
    (hY : T0 ^ (9 / 16 : ℝ) ≤ Y) :
    T0 ≤ 8 * Real.pi * Y ^ 2 := by
  have hpow : T0 ≤ T0 ^ (9 / 8 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hT0.le (by norm_num : (1 : ℝ) ≤ 9 / 8)
    simpa using this
  have hleft0 : 0 ≤ T0 ^ (9 / 16 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hsquare : (T0 ^ (9 / 16 : ℝ)) ^ 2 ≤ Y ^ 2 :=
    pow_le_pow_left₀ hleft0 hY 2
  have hcollapse : (T0 ^ (9 / 16 : ℝ)) ^ 2 = T0 ^ (9 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ T0)]
    congr 1
    norm_num
  rw [hcollapse] at hsquare
  have hTY : T0 ≤ Y ^ 2 := hpow.trans hsquare
  have hYsq0 : 0 ≤ Y ^ 2 := sq_nonneg Y
  nlinarith [Real.pi_gt_three]

/-- Exact raw coefficient energy of one selected group raised to `ell`. -/
def heathBrownSelectedRaisedEnergy {L X k : ℕ}
    (label : HeathBrownSelectionLabel L X k) (ell : ℕ) : ℝ :=
  ∑ j : Fin ((groupedDyadicUpper (heathBrownSelectedExponent label)) ^ ell),
    ‖convPow (groupedDyadicUpper (heathBrownSelectedExponent label)) ell
      (groupedDyadicCoeffVector
        (fun i : HeathBrownSelectedFactor label =>
          heathBrownFactorBase L X (heathBrownSelectedKind label i))
        (heathBrownSelectedExponent label)) j‖ ^ 2

theorem heathBrownSelectedRaisedEnergy_nonneg
    {L X k : ℕ} (label : HeathBrownSelectionLabel L X k) (ell : ℕ) :
    0 ≤ heathBrownSelectedRaisedEnergy label ell := by
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- **One color fibre reaches canonical weighted Huxley.**  Every schedule, raising, and
sigma-dependent absorption parameter is constructed internally. -/
theorem huxley_maynardEligibleSelection_fibre_canonical
    (L X k K : ℕ) {T0 t e mu sigma delta : ℝ}
    (hT0 : 1 < T0) (hsigma : 0 ≤ sigma)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (he : e = 1 - sigma)
    (label : HeathBrownSelectionLabel L X k)
    (S : Finset ℕ) (hSne : S.Nonempty) (hS : S ⊆ Finset.range K)
    (lam : ℕ → ℝ) (hdelta : 0 < delta)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T0)
    (hselection : ∀ r ∈ S,
      IsHeathBrownEligibleSelection L X k
        (T0 := T0) (t := t) (e := e)
        ((sigma : ℂ) + (lam r : ℝ) * Complex.I) label)
    (hscale : ∀ ell : ℕ, 0 < ell → ell ≤ 51 →
      T0 ^ (9 / 16 : ℝ) ≤
        ((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) →
      2 * ((Fintype.card (HeathBrownSelectedFactor label) * ell + 1 : ℕ) : ℝ) ^ 2 *
          heathBrownSelectedRaisedEnergy label ell *
          (1 + 256 * (Real.sqrt T0 +
            8 * Real.sqrt
              ((((groupedDyadicUpper (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ≤
        ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)) ^ 2) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 51 ∧
      T0 ^ (9 / 16 : ℝ) ≤
        ((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) ∧
      (((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ≤
        T0 ^ (1367 / 2160 : ℝ) ∧
      (S.card : ℝ) *
          (((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^
            (1 - sigma)) ^ 2) ≤
        2 * ((Fintype.card (HeathBrownSelectedFactor label) * ell + 1 : ℕ) : ℝ) *
          ∑ r : Fin (Fintype.card (HeathBrownSelectedFactor label) * ell + 1),
            ((((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                2 ^ (r : ℕ) : ℕ) : ℝ)) ^ (-sigma)) ^ 2 *
              heathBrownSelectedRaisedEnergy label ell *
              (((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                  2 ^ (r : ℕ) : ℕ) : ℝ)) +
                (12 * Real.pi *
                  ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                    2 ^ (r : ℕ) : ℕ) : ℝ)) / delta) *
                  ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))) := by
  obtain ⟨ell, hell, hell51, hYlo, hYhi, hlarge⟩ :=
    exists_maynardEligibleSelection_raise L X k hT0 hmu_lo hmu_hi ht he
      label S hSne (fun r => (sigma : ℂ) + (lam r : ℝ) * Complex.I) hselection
  refine ⟨ell, hell, hell51, hYlo, hYhi, ?_⟩
  apply huxley_heathBrown_grouped_large_values_finset_canonical
    (sigma := sigma) (S := S) (lam := lam) (delta := delta) (T := T0)
    L X ell K (heathBrownSelectedKind label) (heathBrownSelectedExponent label)
    hsigma (heathBrownSelectedRaisedEnergy label ell)
    (heathBrownSelectedRaisedEnergy_nonneg label ell)
  · exact le_rfl
  · exact hS
  · exact hdelta
  · linarith
  · exact hgap
  · exact hdiam
  · exact maynard_huxley_square_height_of_raise hT0 hYlo
  · exact hlarge
  · exact hscale ell hell hell51 hYlo

end RHTower.Sieve
