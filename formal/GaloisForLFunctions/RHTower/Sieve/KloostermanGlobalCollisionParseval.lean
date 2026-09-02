import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalFrequencyParseval
import GaloisForLFunctions.RHTower.FieldOneFiniteCyclicFourierParseval

/-!
# Exact time-frequency Parseval law for global Kloosterman collisions

The signed global frequency coefficients admit an exact cyclic Fourier transform.  Parseval
identifies their collision energy with the normalized squared energy of that transform over the
minimal common period.  This is an equality, not a spectral estimate, and introduces no analytic
premise.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Cyclic Fourier transform of the signed global Kloosterman frequency coefficients. -/
def kloostermanGlobalCollisionTimeTransform
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ)
    (k : ZMod (kloostermanGlobalPeriod Q)) : ℂ :=
  ZMod.dft (kloostermanGlobalFrequencyCoefficient Q w B b) k

private theorem sum_stdAddChar_mul_globalPairFrequencyCoefficient
    (Q : Finset ℕ) (q r : ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ)
    (k : ZMod (kloostermanGlobalPeriod Q)) :
    (∑ z : ZMod (kloostermanGlobalPeriod Q),
      ZMod.stdAddChar (-(z * k)) *
        kloostermanGlobalPairFrequencyCoefficient Q q r w B b z) =
      ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
        (star (w q) * w r *
          (star (kloostermanSourceFourier (q + 1) B b x) *
            kloostermanSourceFourier (r + 1) B b y)) *
          ZMod.stdAddChar
            (-(kloostermanGlobalCrossPhaseFrequency Q q r x y * k)) := by
  classical
  unfold kloostermanGlobalPairFrequencyCoefficient
  calc
    (∑ z : ZMod (kloostermanGlobalPeriod Q),
        ZMod.stdAddChar (-(z * k)) *
          ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
            if kloostermanGlobalCrossPhaseFrequency Q q r x y = z then
              star (w q) * w r *
                (star (kloostermanSourceFourier (q + 1) B b x) *
                  kloostermanSourceFourier (r + 1) B b y)
            else 0) =
        ∑ z : ZMod (kloostermanGlobalPeriod Q),
          ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
            if kloostermanGlobalCrossPhaseFrequency Q q r x y = z then
              ZMod.stdAddChar (-(z * k)) *
                (star (w q) * w r *
                  (star (kloostermanSourceFourier (q + 1) B b x) *
                    kloostermanSourceFourier (r + 1) B b y))
            else 0 := by
      apply Fintype.sum_congr
      intro z
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro x
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro y
      split_ifs <;> simp
    _ = ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
        ∑ z : ZMod (kloostermanGlobalPeriod Q),
          if kloostermanGlobalCrossPhaseFrequency Q q r x y = z then
            ZMod.stdAddChar (-(z * k)) *
              (star (w q) * w r *
                (star (kloostermanSourceFourier (q + 1) B b x) *
                  kloostermanSourceFourier (r + 1) B b y))
          else 0 := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro x
      rw [Finset.sum_comm]
    _ = _ := by
      apply Fintype.sum_congr
      intro x
      apply Fintype.sum_congr
      intro y
      simp
      ring

/-- The collision time transform is the literal signed off-diagonal modulus/source sum with its
global additive phase.  No frequency coefficient remains hidden in this expansion. -/
theorem kloostermanGlobalCollisionTimeTransform_eq_explicit
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ)
    (k : ZMod (kloostermanGlobalPeriod Q)) :
    kloostermanGlobalCollisionTimeTransform Q w B b k =
      ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
          (star (w q) * w r *
            (star (kloostermanSourceFourier (q + 1) B b x) *
              kloostermanSourceFourier (r + 1) B b y)) *
            ZMod.stdAddChar
              (-(kloostermanGlobalCrossPhaseFrequency Q q r x y * k)) := by
  classical
  unfold kloostermanGlobalCollisionTimeTransform
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  unfold kloostermanGlobalFrequencyCoefficient
  calc
    (∑ z : ZMod (kloostermanGlobalPeriod Q),
        ZMod.stdAddChar (-(z * k)) *
          ∑ q ∈ Q, ∑ r ∈ Q.erase q,
            kloostermanGlobalPairFrequencyCoefficient Q q r w B b z) =
        ∑ z : ZMod (kloostermanGlobalPeriod Q),
          ∑ q ∈ Q, ∑ r ∈ Q.erase q,
            ZMod.stdAddChar (-(z * k)) *
              kloostermanGlobalPairFrequencyCoefficient Q q r w B b z := by
      apply Fintype.sum_congr
      intro z
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
    _ = ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        ∑ z : ZMod (kloostermanGlobalPeriod Q),
          ZMod.stdAddChar (-(z * k)) *
            kloostermanGlobalPairFrequencyCoefficient Q q r w B b z := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r hr
      exact sum_stdAddChar_mul_globalPairFrequencyCoefficient Q q r w B b k

/-- Unnormalized Parseval: time-transform energy is the minimal common period times collision
energy. -/
theorem sum_normSq_kloostermanGlobalCollisionTimeTransform_eq
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ k : ZMod (kloostermanGlobalPeriod Q),
      ‖kloostermanGlobalCollisionTimeTransform Q w B b k‖ ^ 2) =
      (kloostermanGlobalPeriod Q : ℝ) *
        kloostermanGlobalFrequencyCollisionEnergy Q w B b := by
  unfold kloostermanGlobalCollisionTimeTransform
  unfold kloostermanGlobalFrequencyCollisionEnergy
  simpa only [Complex.normSq_eq_norm_sq] using
    (GaloisForLFunctions.RHTower.fieldOneFiniteCyclicFourier_parseval
      (kloostermanGlobalPeriod Q)
      (kloostermanGlobalFrequencyCoefficient Q w B b))

/-- The signed collision energy is exactly the average squared time-transform energy over the
minimal common period. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_eq_average_timeTransform
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b =
      (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          ‖kloostermanGlobalCollisionTimeTransform Q w B b k‖ ^ 2 := by
  have hparseval :=
    sum_normSq_kloostermanGlobalCollisionTimeTransform_eq Q w B b
  have hperiod : (kloostermanGlobalPeriod Q : ℝ) ≠ 0 := by
    exact_mod_cast (kloostermanGlobalPeriod_pos Q).ne'
  calc
    kloostermanGlobalFrequencyCollisionEnergy Q w B b =
        (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
          ((kloostermanGlobalPeriod Q : ℝ) *
            kloostermanGlobalFrequencyCollisionEnergy Q w B b) := by
      field_simp
    _ = (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          ‖kloostermanGlobalCollisionTimeTransform Q w B b k‖ ^ 2 := by
      rw [hparseval]

end

end RHTower.Sieve
