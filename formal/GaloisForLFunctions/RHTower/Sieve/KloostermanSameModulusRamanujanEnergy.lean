import GaloisForLFunctions.RHTower.Sieve.KloostermanSameModulusRamanujanQuadratic

/-!
# Square-energy form of the same-modulus Ramanujan main

Complete-column correlation is already a Kloosterman Gram. This module lifts that observation to
the source quadratic and all modulus weights, proving the Ramanujan main is an exact nonnegative
real sum of complete-column transform square energies.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Source coefficients transformed by all complete Kloosterman columns of one modulus. -/
def kloostermanCompleteColumnTransform
    (q : ℕ) [NeZero q] (B : Finset ℕ) (b : ℕ → ℂ) (m : ZMod q) : ℂ :=
  ∑ n ∈ B, b n * kloostermanSum q m (n : ZMod q)

/-- A complete-column correlation quadratic is exactly complete Kloosterman transform square
energy. -/
theorem kloostermanCompleteColumnCorrelationQuadratic_eq_transformEnergy
    (q : ℕ) [NeZero q] (B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
      kloostermanCompleteColumnCorrelation q (n : ZMod q) (k : ZMod q)) =
      ((∑ m : ZMod q, ‖kloostermanCompleteColumnTransform q B b m‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  simp_rw [← conj_mul_self]
  unfold kloostermanCompleteColumnCorrelation kloostermanCompleteColumnTransform
  simp_rw [map_sum, map_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Complex.star_def]
  ring

/-- One stored-modulus Ramanujan main term is its complete-column correlation times interval
density. -/
theorem kloostermanSameModulusRamanujanMainTerm_eq_density_mul_completeCorrelation
    (M q n k : ℕ) :
    kloostermanSameModulusRamanujanMainTerm M q n k =
      (((M : ℝ) / ((q + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
        kloostermanCompleteColumnCorrelation (q + 1)
          (n : ZMod (q + 1)) (k : ZMod (q + 1)) := by
  unfold kloostermanSameModulusRamanujanMainTerm
  rw [kloostermanCompleteColumnCorrelation_eq_cglRamanujan]
  simp
  ring

/-- One modulus's Ramanujan source quadratic is a nonnegative complete-column square energy times
the exact interval density. -/
theorem kloostermanSameModulusRamanujanMainTermQuadratic_eq_transformEnergy
    (M q : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
      kloostermanSameModulusRamanujanMainTerm M q n k) =
      ((((M : ℝ) / ((q + 1 : ℕ) : ℝ)) *
        ∑ m : ZMod (q + 1),
          ‖kloostermanCompleteColumnTransform (q + 1) B b m‖ ^ 2 : ℝ) : ℂ) := by
  let d : ℝ := (M : ℝ) / ((q + 1 : ℕ) : ℝ)
  calc
    (∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
        kloostermanSameModulusRamanujanMainTerm M q n k) =
        (d : ℂ) * ∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
          kloostermanCompleteColumnCorrelation (q + 1)
            (n : ZMod (q + 1)) (k : ZMod (q + 1)) := by
      simp_rw [kloostermanSameModulusRamanujanMainTerm_eq_density_mul_completeCorrelation]
      unfold d
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [show (((M : ℝ) / ((q + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          (star (b n) * ∑ k ∈ B, b k *
            kloostermanCompleteColumnCorrelation (q + 1)
              (n : ZMod (q + 1)) (k : ZMod (q + 1))) =
          star (b n) *
            ((((M : ℝ) / ((q + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
              ∑ k ∈ B, b k * kloostermanCompleteColumnCorrelation (q + 1)
                (n : ZMod (q + 1)) (k : ZMod (q + 1))) by ring,
        Finset.mul_sum]
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (d : ℂ) *
        ((∑ m : ZMod (q + 1),
          ‖kloostermanCompleteColumnTransform (q + 1) B b m‖ ^ 2 : ℝ) : ℂ) := by
      rw [kloostermanCompleteColumnCorrelationQuadratic_eq_transformEnergy]
    _ = ((((M : ℝ) / ((q + 1 : ℕ) : ℝ)) *
        ∑ m : ZMod (q + 1),
          ‖kloostermanCompleteColumnTransform (q + 1) B b m‖ ^ 2 : ℝ) : ℂ) := by
      unfold d
      push_cast
      ring

/-- The entire weighted Ramanujan-main quadratic is a manifestly nonnegative sum of complete
Kloosterman column-transform energies. -/
theorem kloostermanSameModulusRamanujanMainQuadratic_eq_transformEnergy
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanSameModulusRamanujanMainQuadratic M Q w B b =
      ((∑ q ∈ Q, ‖w q‖ ^ 2 *
        ((M : ℝ) / ((q + 1 : ℕ) : ℝ)) *
          ∑ m : ZMod (q + 1),
            ‖kloostermanCompleteColumnTransform (q + 1) B b m‖ ^ 2 : ℝ) : ℂ) := by
  unfold kloostermanSameModulusRamanujanMainQuadratic
    kloostermanSameModulusRamanujanGramMain
  calc
    (∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
        ∑ q ∈ Q, star (w q) *
          (w q * kloostermanSameModulusRamanujanMainTerm M q n k)) =
        ∑ n ∈ B, ∑ k ∈ B, ∑ q ∈ Q,
          star (b n) * (b k * (star (w q) *
            (w q * kloostermanSameModulusRamanujanMainTerm M q n k))) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [show star (b n) * (b k * ∑ q ∈ Q, star (w q) *
          (w q * kloostermanSameModulusRamanujanMainTerm M q n k)) =
          (star (b n) * b k) * ∑ q ∈ Q, star (w q) *
            (w q * kloostermanSameModulusRamanujanMainTerm M q n k) by ring,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = ∑ n ∈ B, ∑ q ∈ Q, ∑ k ∈ B,
          star (b n) * (b k * (star (w q) *
            (w q * kloostermanSameModulusRamanujanMainTerm M q n k))) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
    _ = ∑ q ∈ Q, ∑ n ∈ B, ∑ k ∈ B,
          star (b n) * (b k * (star (w q) *
            (w q * kloostermanSameModulusRamanujanMainTerm M q n k))) := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ Q, star (w q) * w q *
          (∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
            kloostermanSameModulusRamanujanMainTerm M q n k) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [show star (w q) * w q *
          (star (b n) * ∑ k ∈ B, b k *
            kloostermanSameModulusRamanujanMainTerm M q n k) =
          star (b n) * ((star (w q) * w q) *
            ∑ k ∈ B, b k *
              kloostermanSameModulusRamanujanMainTerm M q n k) by ring,
        Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ q ∈ Q, star (w q) * w q *
          ((((M : ℝ) / ((q + 1 : ℕ) : ℝ)) *
            ∑ m : ZMod (q + 1),
              ‖kloostermanCompleteColumnTransform (q + 1) B b m‖ ^ 2 : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [kloostermanSameModulusRamanujanMainTermQuadratic_eq_transformEnergy]
    _ = ((∑ q ∈ Q, ‖w q‖ ^ 2 *
        ((M : ℝ) / ((q + 1 : ℕ) : ℝ)) *
          ∑ m : ZMod (q + 1),
            ‖kloostermanCompleteColumnTransform (q + 1) B b m‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [Complex.star_def]
      rw [conj_mul_self]
      push_cast
      ring

/-- The weighted Ramanujan-main quadratic is real. -/
theorem kloostermanSameModulusRamanujanMainQuadratic_im
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    (kloostermanSameModulusRamanujanMainQuadratic M Q w B b).im = 0 := by
  let E : ℝ := ∑ q ∈ Q, ‖w q‖ ^ 2 *
    ((M : ℝ) / ((q + 1 : ℕ) : ℝ)) *
      ∑ m : ZMod (q + 1),
        ‖kloostermanCompleteColumnTransform (q + 1) B b m‖ ^ 2
  have h : kloostermanSameModulusRamanujanMainQuadratic M Q w B b = (E : ℂ) := by
    simpa [E] using
      kloostermanSameModulusRamanujanMainQuadratic_eq_transformEnergy M Q w B b
  rw [h]
  exact ofReal_im E

/-- The weighted Ramanujan-main quadratic has nonnegative real part. -/
theorem kloostermanSameModulusRamanujanMainQuadratic_re_nonneg
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    0 ≤ (kloostermanSameModulusRamanujanMainQuadratic M Q w B b).re := by
  let E : ℝ := ∑ q ∈ Q, ‖w q‖ ^ 2 *
    ((M : ℝ) / ((q + 1 : ℕ) : ℝ)) *
      ∑ m : ZMod (q + 1),
        ‖kloostermanCompleteColumnTransform (q + 1) B b m‖ ^ 2
  have h : kloostermanSameModulusRamanujanMainQuadratic M Q w B b = (E : ℂ) := by
    simpa [E] using
      kloostermanSameModulusRamanujanMainQuadratic_eq_transformEnergy M Q w B b
  rw [h]
  change 0 ≤ E
  unfold E
  positivity

end

end RHTower.Sieve
