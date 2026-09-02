import GaloisForLFunctions.RHTower.Sieve.KloostermanTerminalGeometricCancellation
import GaloisForLFunctions.RHTower.Sieve.KloostermanDistinctModulusTerminalQuadratic

/-!
# Source-Fourier factorization of terminal Kloosterman correlations

The exact terminal cross-modulus carrier is reorganized before taking absolute values. Source
quadratic summation turns each cross-phase coefficient into a product of finite additive Fourier
transforms. Reordering the remaining finite modulus sums gives an exact factorization of the full
weighted distinct-modulus terminal Gram quadratic. No cancellation estimate is assumed.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Additive source transform at one inverse unit frequency. -/
def kloostermanSourceFourier
    (q : ℕ) [NeZero q] (B : Finset ℕ) (b : ℕ → ℂ) (x : (ZMod q)ˣ) : ℂ :=
  ∑ n ∈ B, b n * ZMod.stdAddChar
    ((n : ZMod q) * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))

/-- Terminal geometric orbit attached to two modulus-unit frequencies. -/
def kloostermanTerminalOrbit
    (M q r : ℕ) [NeZero q] [NeZero r]
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) : ℂ :=
  ∑ i ∈ Finset.range (M % Nat.lcm q r),
    (kloostermanCrossPhaseRatio q r x y) ^ (i + 1)

/-- Source quadratic summation of one cross-phase coefficient factors into two source Fourier
transforms. -/
theorem sourceQuadratic_crossPhaseCoefficient_eq_fourier
    (q r : ℕ) [NeZero q] [NeZero r]
    (B : Finset ℕ) (b : ℕ → ℂ)
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) :
    (∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
      kloostermanCrossPhaseCoefficient q r (n : ZMod q) (k : ZMod r) x y) =
      star (kloostermanSourceFourier q B b x) *
        kloostermanSourceFourier r B b y := by
  classical
  unfold kloostermanCrossPhaseCoefficient kloostermanSourceFourier
  have hstar :
      star (∑ n ∈ B, b n * ZMod.stdAddChar
        ((n : ZMod q) * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) =
        ∑ n ∈ B, star (b n) * star (ZMod.stdAddChar
          ((n : ZMod q) * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) := by
    change (starRingEnd ℂ) (∑ n ∈ B, b n * ZMod.stdAddChar
      ((n : ZMod q) * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [map_mul]
    rfl
  rw [hstar]
  have hinner (n : ℕ) :
      (∑ k ∈ B, b k *
        (star (ZMod.stdAddChar
          ((n : ZMod q) * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) *
          ZMod.stdAddChar
            ((k : ZMod r) * ((y⁻¹ : (ZMod r)ˣ) : ZMod r)))) =
        star (ZMod.stdAddChar
          ((n : ZMod q) * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))) *
          ∑ k ∈ B, b k * ZMod.stdAddChar
            ((k : ZMod r) * ((y⁻¹ : (ZMod r)ˣ) : ZMod r)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [hinner]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  ring

private theorem sum_four_comm
    {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ]
    (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (f : α → β → γ → δ → ℂ) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d) =
      ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
  calc
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d) =
        ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, ∑ d ∈ D, f a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ D, f a b c d := by
      rw [Finset.sum_comm]
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ d ∈ D, ∑ b ∈ B, f a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_comm]

private theorem sum_four_dependent_comm
    {α β γ δ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] [DecidableEq δ]
    (A : Finset α) (B : Finset β) (C : Finset γ) (D : γ → Finset δ)
    (f : α → β → γ → δ → ℂ) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D c, f a b c d) =
      ∑ c ∈ C, ∑ d ∈ D c, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
  calc
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D c, f a b c d) =
        ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, ∑ d ∈ D c, f a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ D c, f a b c d := by
      rw [Finset.sum_comm]
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ d ∈ D c, ∑ b ∈ B, f a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ c ∈ C, ∑ d ∈ D c, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_comm]

/-- A terminal cross-modulus block is the sum of its phase coefficients times terminal geometric
orbits. -/
theorem kloostermanNaturalCrossIntervalTerminalBlock_eq_sourceOrbits
    (M q r : ℕ) [NeZero q] [NeZero r]
    (n : ZMod q) (k : ZMod r) :
    kloostermanNaturalCrossIntervalTerminalBlock M q r n k =
      ∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
        kloostermanCrossPhaseCoefficient q r n k x y *
          kloostermanTerminalOrbit M q r x y := by
  simpa [kloostermanTerminalOrbit] using
    kloostermanNaturalCrossIntervalTerminalBlock_eq_phaseOrbits M q r n k

/-- Source quadratic summation of one terminal block is an exact sum of source Fourier products
against terminal geometric orbits. -/
theorem sourceQuadratic_terminalBlock_eq_fourierOrbits
    (M q r : ℕ) [NeZero q] [NeZero r]
    (B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
      kloostermanNaturalCrossIntervalTerminalBlock M q r
        (n : ZMod q) (k : ZMod r)) =
      ∑ x : (ZMod q)ˣ, ∑ y : (ZMod r)ˣ,
        star (kloostermanSourceFourier q B b x) *
          kloostermanSourceFourier r B b y *
            kloostermanTerminalOrbit M q r x y := by
  classical
  simp_rw [kloostermanNaturalCrossIntervalTerminalBlock_eq_sourceOrbits]
  simp only [Finset.mul_sum]
  rw [sum_four_comm B B Finset.univ Finset.univ]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  calc
    (∑ n ∈ B, ∑ k ∈ B,
        star (b n) *
          (b k * (kloostermanCrossPhaseCoefficient q r (n : ZMod q) (k : ZMod r) x y *
            kloostermanTerminalOrbit M q r x y))) =
        (∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
          kloostermanCrossPhaseCoefficient q r (n : ZMod q) (k : ZMod r) x y) *
            kloostermanTerminalOrbit M q r x y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      calc
        (∑ k ∈ B,
            star (b n) *
              (b k * (kloostermanCrossPhaseCoefficient q r (n : ZMod q) (k : ZMod r) x y *
                kloostermanTerminalOrbit M q r x y))) =
            ∑ k ∈ B,
              (star (b n) *
                (b k * kloostermanCrossPhaseCoefficient q r (n : ZMod q) (k : ZMod r) x y)) *
                  kloostermanTerminalOrbit M q r x y := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = (∑ k ∈ B,
              star (b n) *
                (b k * kloostermanCrossPhaseCoefficient q r (n : ZMod q) (k : ZMod r) x y)) *
              kloostermanTerminalOrbit M q r x y := by
          rw [Finset.sum_mul]
        _ = (star (b n) * ∑ k ∈ B,
              b k * kloostermanCrossPhaseCoefficient q r (n : ZMod q) (k : ZMod r) x y) *
              kloostermanTerminalOrbit M q r x y := by
          rw [Finset.mul_sum]
    _ = star (kloostermanSourceFourier q B b x) *
          kloostermanSourceFourier r B b y *
            kloostermanTerminalOrbit M q r x y := by
      rw [sourceQuadratic_crossPhaseCoefficient_eq_fourier]

/-- The full distinct-modulus terminal Gram quadratic is exactly a weighted sum of source
Fourier products against terminal geometric orbits. -/
theorem kloostermanDistinctModulusTerminalGramQuadratic_eq_sourceFourierOrbits
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanDistinctModulusTerminalGramQuadratic M Q w B b =
      ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        star (w q) * w r *
          ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
            star (kloostermanSourceFourier (q + 1) B b x) *
              kloostermanSourceFourier (r + 1) B b y *
                kloostermanTerminalOrbit M (q + 1) (r + 1) x y := by
  classical
  unfold kloostermanDistinctModulusTerminalGramQuadratic
    kloostermanDistinctModulusTerminalGram
  conv_lhs => simp only [Finset.mul_sum]
  rw [sum_four_dependent_comm B B Q (fun q => Q.erase q)]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  calc
    (∑ n ∈ B, ∑ k ∈ B,
        star (b n) *
          (b k * (star (w q) *
            (w r * kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
              (Int.cast (n : ℤ)) (Int.cast (k : ℤ)))))) =
        ∑ n ∈ B, ∑ k ∈ B,
          (star (w q) * w r) *
            (star (b n) * b k *
              kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
                (n : ZMod (q + 1)) (k : ZMod (r + 1))) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Int.cast_natCast]
      ring
    _ = (star (w q) * w r) *
        (∑ n ∈ B, ∑ k ∈ B,
          star (b n) * b k *
            kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
              (n : ZMod (q + 1)) (k : ZMod (r + 1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
    _ = (star (w q) * w r) *
        (∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
          kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
            (n : ZMod (q + 1)) (k : ZMod (r + 1))) := by
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = star (w q) * w r *
        ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
          star (kloostermanSourceFourier (q + 1) B b x) *
            kloostermanSourceFourier (r + 1) B b y *
              kloostermanTerminalOrbit M (q + 1) (r + 1) x y := by
      rw [sourceQuadratic_terminalBlock_eq_fourierOrbits]

end

end RHTower.Sieve
