import GaloisForLFunctions.RHTower.Sieve.KloostermanBilinear

/-!
# Signed Kloosterman bilinear forms across moduli

Spectral cancellation acts on a signed sum of Kloosterman bilinear forms before absolute values
or square energies are taken.  This file defines that direct-sum object, expands it into the
classical threefold sum, and records the sharp baseline inherited from the complete fixed-modulus
transform.  Unlike `normalizedKloostermanHybridModulusEnergy`, this object retains the relative
phases between distinct moduli.
-/

open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Signed finite sum of complete Kloosterman bilinear forms.  Modulus `q + 1` keeps every fibre
nonzero without a side condition on the finite index set. -/
def kloostermanModulusBilinear
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (a b : (q : ℕ) → ZMod (q + 1) → ℂ) : ℂ :=
  ∑ q ∈ Q, w q * kloostermanBilinear (q + 1) (a q) (b q)

/-- Expansion as the literal signed sum over moduli and both Kloosterman frequencies. -/
theorem kloostermanModulusBilinear_eq
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (a b : (q : ℕ) → ZMod (q + 1) → ℂ) :
    kloostermanModulusBilinear Q w a b =
      ∑ q ∈ Q, w q *
        ∑ m : ZMod (q + 1), a q m *
          ∑ n : ZMod (q + 1), b q n * kloostermanSum (q + 1) m n := by
  unfold kloostermanModulusBilinear
  apply Finset.sum_congr rfl
  intro q _hq
  rw [kloostermanBilinear_eq]

/-- Fixed-modulus operator bound in unsquared form. -/
theorem norm_kloostermanBilinear_le
    (q : ℕ) [NeZero q] (a b : ZMod q → ℂ) :
    ‖kloostermanBilinear q a b‖ ≤
      (q : ℝ) * Real.sqrt (∑ m : ZMod q, ‖a m‖ ^ (2 : ℕ)) *
        Real.sqrt (∑ n : ZMod q, ‖b n‖ ^ (2 : ℕ)) := by
  let A : ℝ := ∑ m : ZMod q, ‖a m‖ ^ (2 : ℕ)
  let B : ℝ := ∑ n : ZMod q, ‖b n‖ ^ (2 : ℕ)
  have hA : 0 ≤ A := Finset.sum_nonneg fun m _ => sq_nonneg ‖a m‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun n _ => sq_nonneg ‖b n‖
  have hq : 0 ≤ (q : ℝ) := by positivity
  have hsq := norm_kloostermanBilinear_sq_le q a b
  have hrhs :
      ((q : ℝ) * Real.sqrt A * Real.sqrt B) ^ (2 : ℕ) =
        (q : ℝ) ^ (2 : ℕ) * A * B := by
    rw [show ((q : ℝ) * Real.sqrt A * Real.sqrt B) ^ (2 : ℕ) =
      (q : ℝ) ^ (2 : ℕ) * (Real.sqrt A) ^ (2 : ℕ) * (Real.sqrt B) ^ (2 : ℕ) by ring,
      Real.sq_sqrt hA, Real.sq_sqrt hB]
  have hrhs0 : 0 ≤ (q : ℝ) * Real.sqrt A * Real.sqrt B := by positivity
  rw [show (∑ m : ZMod q, ‖a m‖ ^ (2 : ℕ)) = A by rfl,
    show (∑ n : ZMod q, ‖b n‖ ^ (2 : ℕ)) = B by rfl] at hsq ⊢
  nlinarith [sq_nonneg
    (‖kloostermanBilinear q a b‖ -
      ((q : ℝ) * Real.sqrt A * Real.sqrt B))]

/-- Elementary modulus-sum baseline.  Every relative modulus phase is retained on the left; the
right is exactly the loss incurred by taking absolute values before any spectral averaging. -/
theorem norm_kloostermanModulusBilinear_le_baseline
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (a b : (q : ℕ) → ZMod (q + 1) → ℂ) :
    ‖kloostermanModulusBilinear Q w a b‖ ≤
      ∑ q ∈ Q, ‖w q‖ * ((q + 1 : ℕ) : ℝ) *
        Real.sqrt (∑ m : ZMod (q + 1), ‖a q m‖ ^ (2 : ℕ)) *
        Real.sqrt (∑ n : ZMod (q + 1), ‖b q n‖ ^ (2 : ℕ)) := by
  unfold kloostermanModulusBilinear
  calc
    ‖∑ q ∈ Q, w q * kloostermanBilinear (q + 1) (a q) (b q)‖ ≤
        ∑ q ∈ Q, ‖w q * kloostermanBilinear (q + 1) (a q) (b q)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, ‖w q‖ * ((q + 1 : ℕ) : ℝ) *
        Real.sqrt (∑ m : ZMod (q + 1), ‖a q m‖ ^ (2 : ℕ)) *
        Real.sqrt (∑ n : ZMod (q + 1), ‖b q n‖ ^ (2 : ℕ)) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [norm_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (norm_kloostermanBilinear_le (q + 1) (a q) (b q)) (norm_nonneg (w q))

/-- Direct-sum square bound after Cauchy--Schwarz in the modulus variable.  A spectral large sieve
must improve this fixed-modulus operator baseline by using the shared arithmetic structure of the
fibres, rather than discarding their relative phases. -/
theorem norm_kloostermanModulusBilinear_sq_le_baseline
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (a b : (q : ℕ) → ZMod (q + 1) → ℂ) :
    ‖kloostermanModulusBilinear Q w a b‖ ^ (2 : ℕ) ≤
      (∑ q ∈ Q,
        (‖w q‖ * ((q + 1 : ℕ) : ℝ) *
          Real.sqrt (∑ m : ZMod (q + 1), ‖a q m‖ ^ (2 : ℕ))) ^ (2 : ℕ)) *
      ∑ q ∈ Q,
        (Real.sqrt (∑ n : ZMod (q + 1), ‖b q n‖ ^ (2 : ℕ))) ^ (2 : ℕ) := by
  let x : ℕ → ℝ := fun q =>
    ‖w q‖ * ((q + 1 : ℕ) : ℝ) *
      Real.sqrt (∑ m : ZMod (q + 1), ‖a q m‖ ^ (2 : ℕ))
  let y : ℕ → ℝ := fun q =>
    Real.sqrt (∑ n : ZMod (q + 1), ‖b q n‖ ^ (2 : ℕ))
  have hbase := norm_kloostermanModulusBilinear_le_baseline Q w a b
  have hsum0 : 0 ≤ ∑ q ∈ Q, x q * y q :=
    Finset.sum_nonneg fun q _ => mul_nonneg (by dsimp only [x]; positivity) (by
      dsimp only [y]
      positivity)
  have hsq : ‖kloostermanModulusBilinear Q w a b‖ ^ (2 : ℕ) ≤
      (∑ q ∈ Q, x q * y q) ^ (2 : ℕ) := by
    have hnorm0 : 0 ≤ ‖kloostermanModulusBilinear Q w a b‖ := norm_nonneg _
    change ‖kloostermanModulusBilinear Q w a b‖ ≤ ∑ q ∈ Q, x q * y q at hbase
    nlinarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Q x y
  change _ ≤ (∑ q ∈ Q, x q ^ (2 : ℕ)) * ∑ q ∈ Q, y q ^ (2 : ℕ)
  exact hsq.trans hcs

end

end RHTower.Sieve
