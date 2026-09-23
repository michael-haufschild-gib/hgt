import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalPeriodFrequency

/-!
# Signed global-frequency Parseval receiver for terminal Kloosterman Gram forms

All off-diagonal modulus pairs are grouped inside one common cyclic frequency
space before a norm is taken.  The coefficient at a frequency is the signed
sum of every modulus/source-Fourier tuple landing in that fibre.  The full
terminal Gram form is exactly the pairing of these coefficients with the
global terminal orbits.

Finite Cauchy--Schwarz and exact additive-character Parseval then bound the
Gram energy by the squared energy of these already-aggregated coefficients.
Thus cancellation within every global frequency fibre is retained.  Bounding
that collision energy at paper scale is the remaining spectral problem; it is
not assumed here.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Signed source/modulus coefficient contributed by one modulus pair to one global frequency. -/
def kloostermanGlobalPairFrequencyCoefficient
    (Q : Finset ℕ) (q r : ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ)
    (z : ZMod (kloostermanGlobalPeriod Q)) : ℂ :=
  ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
    if kloostermanGlobalCrossPhaseFrequency Q q r x y = z then
      star (w q) * w r *
        (star (kloostermanSourceFourier (q + 1) B b x) *
          kloostermanSourceFourier (r + 1) B b y)
    else 0

/-- Complete signed coefficient after grouping every off-diagonal modulus pair by one common
frequency. -/
def kloostermanGlobalFrequencyCoefficient
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ)
    (z : ZMod (kloostermanGlobalPeriod Q)) : ℂ :=
  ∑ q ∈ Q, ∑ r ∈ Q.erase q,
    kloostermanGlobalPairFrequencyCoefficient Q q r w B b z

/-- Squared energy of the signed global frequency coefficients. -/
def kloostermanGlobalFrequencyCollisionEnergy
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ z : ZMod (kloostermanGlobalPeriod Q),
    ‖kloostermanGlobalFrequencyCoefficient Q w B b z‖ ^ 2

private theorem pair_sum_eq_global_frequency_sum
    (M : ℕ) (Q : Finset ℕ) (q r : ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
      (star (w q) * w r *
        (star (kloostermanSourceFourier (q + 1) B b x) *
          kloostermanSourceFourier (r + 1) B b y)) *
        kloostermanGlobalTerminalOrbit M Q
          (kloostermanGlobalCrossPhaseFrequency Q q r x y)) =
      ∑ z : ZMod (kloostermanGlobalPeriod Q),
        kloostermanGlobalPairFrequencyCoefficient Q q r w B b z *
          kloostermanGlobalTerminalOrbit M Q z := by
  classical
  unfold kloostermanGlobalPairFrequencyCoefficient
  symm
  calc
    (∑ z : ZMod (kloostermanGlobalPeriod Q),
        (∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
          if kloostermanGlobalCrossPhaseFrequency Q q r x y = z then
            star (w q) * w r *
              (star (kloostermanSourceFourier (q + 1) B b x) *
                kloostermanSourceFourier (r + 1) B b y)
          else 0) * kloostermanGlobalTerminalOrbit M Q z) =
        ∑ z : ZMod (kloostermanGlobalPeriod Q),
          ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
            if kloostermanGlobalCrossPhaseFrequency Q q r x y = z then
              (star (w q) * w r *
                (star (kloostermanSourceFourier (q + 1) B b x) *
                  kloostermanSourceFourier (r + 1) B b y)) *
                    kloostermanGlobalTerminalOrbit M Q z
            else 0 := by
      apply Fintype.sum_congr
      intro z
      rw [Finset.sum_mul]
      apply Fintype.sum_congr
      intro x
      rw [Finset.sum_mul]
      apply Fintype.sum_congr
      intro y
      split_ifs <;> simp
    _ = ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
        ∑ z : ZMod (kloostermanGlobalPeriod Q),
          if kloostermanGlobalCrossPhaseFrequency Q q r x y = z then
            (star (w q) * w r *
              (star (kloostermanSourceFourier (q + 1) B b x) *
                kloostermanSourceFourier (r + 1) B b y)) *
                  kloostermanGlobalTerminalOrbit M Q z
          else 0 := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro x
      rw [Finset.sum_comm]
    _ = ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
      (star (w q) * w r *
        (star (kloostermanSourceFourier (q + 1) B b x) *
          kloostermanSourceFourier (r + 1) B b y)) *
        kloostermanGlobalTerminalOrbit M Q
          (kloostermanGlobalCrossPhaseFrequency Q q r x y) := by
      apply Fintype.sum_congr
      intro x
      apply Fintype.sum_congr
      intro y
      simp

private theorem sum_three_dependent_comm_global
    {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (A : Finset α) (D : α → Finset β) (C : Finset γ)
    (f : α → β → γ → ℂ) :
    (∑ a ∈ A, ∑ b ∈ D a, ∑ c ∈ C, f a b c) =
      ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ D a, f a b c := by
  calc
    (∑ a ∈ A, ∑ b ∈ D a, ∑ c ∈ C, f a b c) =
        ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ D a, f a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ D a, f a b c := by
      rw [Finset.sum_comm]

/-- Exact global-frequency decomposition of the full signed terminal Gram quadratic. -/
theorem kloostermanDistinctModulusTerminalGramQuadratic_eq_globalFrequency
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanDistinctModulusTerminalGramQuadratic M Q w B b =
      ∑ z : ZMod (kloostermanGlobalPeriod Q),
        kloostermanGlobalFrequencyCoefficient Q w B b z *
          kloostermanGlobalTerminalOrbit M Q z := by
  classical
  calc
    kloostermanDistinctModulusTerminalGramQuadratic M Q w B b =
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
            (star (w q) * w r *
              (star (kloostermanSourceFourier (q + 1) B b x) *
                kloostermanSourceFourier (r + 1) B b y)) *
              kloostermanGlobalTerminalOrbit M Q
                (kloostermanGlobalCrossPhaseFrequency Q q r x y) := by
      rw [kloostermanDistinctModulusTerminalGramQuadratic_eq_sourceFourierOrbits]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r hr
      have hrQ : r ∈ Q := Finset.mem_of_mem_erase hr
      have hqr : q ≠ r := Ne.symm (Finset.mem_erase.mp hr).1
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro x
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro y
      rw [kloostermanTerminalOrbit_eq_globalTerminalOrbit
        M Q q r hq hrQ hqr x y]
      ring
    _ = ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        ∑ z : ZMod (kloostermanGlobalPeriod Q),
          kloostermanGlobalPairFrequencyCoefficient Q q r w B b z *
            kloostermanGlobalTerminalOrbit M Q z := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r hr
      exact pair_sum_eq_global_frequency_sum M Q q r w B b
    _ = ∑ z : ZMod (kloostermanGlobalPeriod Q),
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanGlobalPairFrequencyCoefficient Q q r w B b z *
            kloostermanGlobalTerminalOrbit M Q z := by
      exact sum_three_dependent_comm_global Q (fun q => Q.erase q) Finset.univ
        (fun q r z => kloostermanGlobalPairFrequencyCoefficient Q q r w B b z *
          kloostermanGlobalTerminalOrbit M Q z)
    _ = ∑ z : ZMod (kloostermanGlobalPeriod Q),
        kloostermanGlobalFrequencyCoefficient Q w B b z *
          kloostermanGlobalTerminalOrbit M Q z := by
      apply Fintype.sum_congr
      intro z
      unfold kloostermanGlobalFrequencyCoefficient
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_mul]

/-- The zero global frequency receives no off-diagonal Kloosterman coefficient. -/
theorem kloostermanGlobalFrequencyCoefficient_zero
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCoefficient Q w B b 0 = 0 := by
  classical
  unfold kloostermanGlobalFrequencyCoefficient
  apply Finset.sum_eq_zero
  intro q hq
  apply Finset.sum_eq_zero
  intro r hr
  unfold kloostermanGlobalPairFrequencyCoefficient
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have hrQ : r ∈ Q := Finset.mem_of_mem_erase hr
  have hqr : q ≠ r := Ne.symm (Finset.mem_erase.mp hr).1
  rw [if_neg (kloostermanGlobalCrossPhaseFrequency_ne_zero
    Q q r hq hrQ hqr x y)]

private theorem norm_sum_mul_sq_le_sq_mul_sq_global
    {α : Type*} [DecidableEq α] (S : Finset α) (a c : α → ℂ) :
    ‖∑ z ∈ S, a z * c z‖ ^ 2 ≤
      (∑ z ∈ S, ‖a z‖ ^ 2) * ∑ z ∈ S, ‖c z‖ ^ 2 := by
  have htri :
      ‖∑ z ∈ S, a z * c z‖ ≤ ∑ z ∈ S, ‖a z‖ * ‖c z‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro z hz
    rw [norm_mul]
  have hsum0 : 0 ≤ ∑ z ∈ S, ‖a z‖ * ‖c z‖ := by positivity
  calc
    ‖∑ z ∈ S, a z * c z‖ ^ 2 ≤
        (∑ z ∈ S, ‖a z‖ * ‖c z‖) ^ 2 := by
      nlinarith [norm_nonneg (∑ z ∈ S, a z * c z)]
    _ ≤ (∑ z ∈ S, ‖a z‖ ^ 2) * ∑ z ∈ S, ‖c z‖ ^ 2 := by
      exact Finset.sum_mul_sq_le_sq_mul_sq S (fun z => ‖a z‖) (fun z => ‖c z‖)

/-- Exact global-orbit Parseval energy over all common-period frequencies. -/
theorem sum_normSq_kloostermanGlobalTerminalOrbit_eq
    (M : ℕ) (Q : Finset ℕ) :
    (∑ z : ZMod (kloostermanGlobalPeriod Q),
      ‖kloostermanGlobalTerminalOrbit M Q z‖ ^ 2) =
      (kloostermanGlobalPeriod Q : ℝ) *
        (M % kloostermanGlobalPeriod Q : ℕ) := by
  unfold kloostermanGlobalTerminalOrbit
  exact sum_normSq_stdAddChar_pow_range_eq
    (kloostermanGlobalPeriod Q) (M % kloostermanGlobalPeriod Q)
      (Nat.le_of_lt (Nat.mod_lt M (kloostermanGlobalPeriod_pos Q)))

/-- The zero-frequency global terminal orbit is the residual length itself. -/
theorem kloostermanGlobalTerminalOrbit_zero
    (M : ℕ) (Q : Finset ℕ) :
    kloostermanGlobalTerminalOrbit M Q 0 =
      ((M % kloostermanGlobalPeriod Q : ℕ) : ℂ) := by
  simp [kloostermanGlobalTerminalOrbit]

/-- Exact Parseval energy after deleting the zero global frequency.  The removed square is the
square of the residual length, so no zero-mode orbit loss remains. -/
theorem sum_normSq_kloostermanGlobalTerminalOrbit_erase_zero_eq
    (M : ℕ) (Q : Finset ℕ) :
    (∑ z ∈ (Finset.univ : Finset (ZMod (kloostermanGlobalPeriod Q))).erase 0,
      ‖kloostermanGlobalTerminalOrbit M Q z‖ ^ 2) =
      (kloostermanGlobalPeriod Q : ℝ) *
          (M % kloostermanGlobalPeriod Q : ℕ) -
        ((M % kloostermanGlobalPeriod Q : ℕ) : ℝ) ^ 2 := by
  have hsplit := Finset.sum_erase_add
    (Finset.univ : Finset (ZMod (kloostermanGlobalPeriod Q)))
    (fun z => ‖kloostermanGlobalTerminalOrbit M Q z‖ ^ 2)
    (Finset.mem_univ (0 : ZMod (kloostermanGlobalPeriod Q)))
  have hall := sum_normSq_kloostermanGlobalTerminalOrbit_eq M Q
  have hzero : ‖kloostermanGlobalTerminalOrbit M Q 0‖ ^ 2 =
      ((M % kloostermanGlobalPeriod Q : ℕ) : ℝ) ^ 2 := by
    rw [kloostermanGlobalTerminalOrbit_zero]
    simp
  rw [hzero, hall] at hsplit
  linarith

/-- Full terminal Gram energy bounded by the signed global frequency-collision energy times exact
common-period Parseval.  Cancellation inside every frequency fibre is retained. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_globalFrequencyCollisionEnergy
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ^ 2 ≤
      kloostermanGlobalFrequencyCollisionEnergy Q w B b *
        ((kloostermanGlobalPeriod Q : ℝ) *
          (M % kloostermanGlobalPeriod Q : ℕ)) := by
  classical
  rw [kloostermanDistinctModulusTerminalGramQuadratic_eq_globalFrequency]
  let S : Finset (ZMod (kloostermanGlobalPeriod Q)) := Finset.univ.erase 0
  have hzero := kloostermanGlobalFrequencyCoefficient_zero Q w B b
  have herase :
      (∑ z : ZMod (kloostermanGlobalPeriod Q),
        kloostermanGlobalFrequencyCoefficient Q w B b z *
          kloostermanGlobalTerminalOrbit M Q z) =
        ∑ z ∈ S,
          kloostermanGlobalFrequencyCoefficient Q w B b z *
            kloostermanGlobalTerminalOrbit M Q z := by
    rw [← Finset.sum_erase Finset.univ (by rw [hzero, zero_mul])]
  rw [herase]
  have hcs := norm_sum_mul_sq_le_sq_mul_sq_global S
    (kloostermanGlobalFrequencyCoefficient Q w B b)
    (kloostermanGlobalTerminalOrbit M Q)
  calc
    ‖∑ z ∈ S,
        kloostermanGlobalFrequencyCoefficient Q w B b z *
          kloostermanGlobalTerminalOrbit M Q z‖ ^ 2 ≤
        (∑ z ∈ S, ‖kloostermanGlobalFrequencyCoefficient Q w B b z‖ ^ 2) *
          ∑ z ∈ S, ‖kloostermanGlobalTerminalOrbit M Q z‖ ^ 2 := hcs
    _ ≤ kloostermanGlobalFrequencyCollisionEnergy Q w B b *
        ((kloostermanGlobalPeriod Q : ℝ) *
          (M % kloostermanGlobalPeriod Q : ℕ)) := by
      apply mul_le_mul
      · unfold kloostermanGlobalFrequencyCollisionEnergy S
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun i hi hni => by positivity)
      · unfold S
        calc
          (∑ z ∈ Finset.univ.erase 0,
              ‖kloostermanGlobalTerminalOrbit M Q z‖ ^ 2) ≤
              ∑ z : ZMod (kloostermanGlobalPeriod Q),
                ‖kloostermanGlobalTerminalOrbit M Q z‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun i hi hni => by positivity)
          _ = (kloostermanGlobalPeriod Q : ℝ) *
              (M % kloostermanGlobalPeriod Q : ℕ) :=
            sum_normSq_kloostermanGlobalTerminalOrbit_eq M Q
      · exact Finset.sum_nonneg fun z hz => by positivity
      · unfold kloostermanGlobalFrequencyCollisionEnergy
        exact Finset.sum_nonneg fun z hz => by positivity

/-- Zero-mode-exact version of the global-frequency terminal receiver.  Since the signed global
coefficient vanishes at frequency zero, Cauchy--Schwarz is charged only to the nonzero terminal
orbits, whose exact energy is `P * (M % P) - (M % P)^(2 : ℕ)`. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_globalFrequencyCollisionEnergy_erase_zero
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ^ 2 ≤
      kloostermanGlobalFrequencyCollisionEnergy Q w B b *
        ((kloostermanGlobalPeriod Q : ℝ) *
            (M % kloostermanGlobalPeriod Q : ℕ) -
          ((M % kloostermanGlobalPeriod Q : ℕ) : ℝ) ^ 2) := by
  classical
  rw [kloostermanDistinctModulusTerminalGramQuadratic_eq_globalFrequency]
  let S : Finset (ZMod (kloostermanGlobalPeriod Q)) := Finset.univ.erase 0
  have hzero := kloostermanGlobalFrequencyCoefficient_zero Q w B b
  have herase :
      (∑ z : ZMod (kloostermanGlobalPeriod Q),
        kloostermanGlobalFrequencyCoefficient Q w B b z *
          kloostermanGlobalTerminalOrbit M Q z) =
        ∑ z ∈ S,
          kloostermanGlobalFrequencyCoefficient Q w B b z *
            kloostermanGlobalTerminalOrbit M Q z := by
    rw [← Finset.sum_erase Finset.univ (by rw [hzero, zero_mul])]
  rw [herase]
  have hcs := norm_sum_mul_sq_le_sq_mul_sq_global S
    (kloostermanGlobalFrequencyCoefficient Q w B b)
    (kloostermanGlobalTerminalOrbit M Q)
  calc
    ‖∑ z ∈ S,
        kloostermanGlobalFrequencyCoefficient Q w B b z *
          kloostermanGlobalTerminalOrbit M Q z‖ ^ 2 ≤
        (∑ z ∈ S, ‖kloostermanGlobalFrequencyCoefficient Q w B b z‖ ^ 2) *
          ∑ z ∈ S, ‖kloostermanGlobalTerminalOrbit M Q z‖ ^ 2 := hcs
    _ = kloostermanGlobalFrequencyCollisionEnergy Q w B b *
        ((kloostermanGlobalPeriod Q : ℝ) *
            (M % kloostermanGlobalPeriod Q : ℕ) -
          ((M % kloostermanGlobalPeriod Q : ℕ) : ℝ) ^ 2) := by
      congr 1
      · unfold kloostermanGlobalFrequencyCollisionEnergy S
        exact Finset.sum_erase Finset.univ (by simp [hzero])
      · exact sum_normSq_kloostermanGlobalTerminalOrbit_erase_zero_eq M Q

end

end RHTower.Sieve
