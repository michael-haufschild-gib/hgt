import GaloisForLFunctions.RHTower.Sieve.KloostermanTerminalSourceFourierEnergy
import GaloisForLFunctions.RHTower.Sieve.KloostermanProductHarmonicQuadratic

/-!
# Hybrid squared-energy budget for terminal Kloosterman orbits

Each terminal geometric orbit is bounded both by its exact residual length and, for unequal
moduli, by its reciprocal phase chord. Squaring and summing over the erased modulus-pair family
gives a no-premise aggregate Hilbert--Schmidt budget. A dependent-pair Cauchy--Schwarz inequality
then controls the full weighted terminal Gram quadratic without an extra modulus-cardinality loss.
Finally, length--frequency interpolation connects the hybrid energy to the existing shared-gcd-safe
product-harmonic budget. These evaluate the kernel term exposed by
`KloostermanTerminalSourceFourierEnergy` without asserting any collective spectral saving.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Pointwise squared terminal-orbit budget: residual-length square versus reciprocal-chord
square. -/
def kloostermanTerminalOrbitHybridSqBudget
    (M q r : ℕ)
    (x : (ZMod (q + 1))ˣ) (y : (ZMod (r + 1))ˣ) : ℝ :=
  min
    (((M % Nat.lcm (q + 1) (r + 1) : ℕ) : ℝ) ^ 2)
    ((2 / ‖1 - kloostermanCrossPhaseRatio (q + 1) (r + 1) x y‖) ^ 2)

/-- Exact Parseval source-energy budget at one stored modulus index. -/
def kloostermanSourceResidueEnergy
    (q : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  ((q + 1 : ℕ) : ℝ) *
    ∑ z : ZMod (q + 1), Complex.normSq
      (kloostermanSourceResidue (q + 1) B b z)

/-- Total pointwise hybrid squared-orbit budget for one stored modulus pair. -/
def kloostermanTerminalOrbitHybridEnergy
    (M q r : ℕ) : ℝ :=
  ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
    kloostermanTerminalOrbitHybridSqBudget M q r x y

/-- Length--frequency interpolation budget for one stored unequal-modulus pair. -/
def kloostermanTerminalOrbitInterpolatedBudget
    (M q r : ℕ) : ℝ :=
  ((M % Nat.lcm (q + 1) (r + 1) : ℕ) : ℝ) *
    kloostermanProductHarmonicPairBudget q r

private theorem norm_kloostermanTerminalOrbit_sq_le_min
    (M q r : ℕ) [NeZero q] [NeZero r] (hqr : q ≠ r)
    (x : (ZMod q)ˣ) (y : (ZMod r)ˣ) :
    ‖kloostermanTerminalOrbit M q r x y‖ ^ 2 ≤
      min
        (((M % Nat.lcm q r : ℕ) : ℝ) ^ 2)
        ((2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖) ^ 2) := by
  have hcard : ‖kloostermanTerminalOrbit M q r x y‖ ≤
      ((M % Nat.lcm q r : ℕ) : ℝ) := by
    unfold kloostermanTerminalOrbit
    calc
      ‖∑ i ∈ Finset.range (M % Nat.lcm q r),
          (kloostermanCrossPhaseRatio q r x y) ^ (i + 1)‖ ≤
          ∑ i ∈ Finset.range (M % Nat.lcm q r),
            ‖(kloostermanCrossPhaseRatio q r x y) ^ (i + 1)‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range (M % Nat.lcm q r), 1 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_pow, norm_kloostermanCrossPhaseRatio, one_pow]
      _ = ((M % Nat.lcm q r : ℕ) : ℝ) := by simp
  have hgeom : ‖kloostermanTerminalOrbit M q r x y‖ ≤
      2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖ := by
    unfold kloostermanTerminalOrbit
    rw [show (∑ i ∈ Finset.range (M % Nat.lcm q r),
        (kloostermanCrossPhaseRatio q r x y) ^ (i + 1)) =
        kloostermanCrossPhaseRatio q r x y *
          ∑ i ∈ Finset.range (M % Nat.lcm q r),
            (kloostermanCrossPhaseRatio q r x y) ^ i by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ']]
    rw [norm_mul, norm_kloostermanCrossPhaseRatio, one_mul]
    exact norm_sum_range_kloostermanCrossPhaseRatio_pow_le
      (M % Nat.lcm q r) q r hqr x y
  have hlength : (0 : ℝ) ≤ ((M % Nat.lcm q r : ℕ) : ℝ) := by positivity
  have hchord : (0 : ℝ) ≤
      2 / ‖1 - kloostermanCrossPhaseRatio q r x y‖ := by positivity
  apply le_min
  · nlinarith [norm_nonneg (kloostermanTerminalOrbit M q r x y)]
  · nlinarith [norm_nonneg (kloostermanTerminalOrbit M q r x y)]

/-- No-premise aggregate terminal-orbit energy bound over every erased modulus pair. -/
theorem sum_kloostermanTerminalOrbit_sq_le_hybridBudget
    (M : ℕ) (Q : Finset ℕ) :
    (∑ q ∈ Q, ∑ r ∈ Q.erase q,
      ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
        ‖kloostermanTerminalOrbit M (q + 1) (r + 1) x y‖ ^ 2) ≤
      ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
          kloostermanTerminalOrbitHybridSqBudget M q r x y := by
  classical
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro x hx
  apply Finset.sum_le_sum
  intro y hy
  unfold kloostermanTerminalOrbitHybridSqBudget
  have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
  have hsucc : q + 1 ≠ r + 1 := by omega
  exact norm_kloostermanTerminalOrbit_sq_le_min
    M (q + 1) (r + 1) hsucc x y

private theorem kloostermanTerminalOrbitHybridEnergy_le_interpolated_of_ne
    (M q r : ℕ) (hqr : q ≠ r) :
    kloostermanTerminalOrbitHybridEnergy M q r ≤
      kloostermanTerminalOrbitInterpolatedBudget M q r := by
  let L : ℝ := ((M % Nat.lcm (q + 1) (r + 1) : ℕ) : ℝ)
  let C : (ZMod (q + 1))ˣ → (ZMod (r + 1))ˣ → ℝ := fun x y =>
    2 / ‖1 - kloostermanCrossPhaseRatio (q + 1) (r + 1) x y‖
  have hpoint (x : (ZMod (q + 1))ˣ) (y : (ZMod (r + 1))ˣ) :
      min (L ^ 2) (C x y ^ 2) ≤ L * C x y := by
    have hL : 0 ≤ L := by
      dsimp [L]
      positivity
    have hC : 0 ≤ C x y := by
      dsimp [C]
      positivity
    by_cases h : L ≤ C x y
    · exact (min_le_left _ _).trans (by nlinarith)
    · have h' : C x y ≤ L := le_of_not_ge h
      exact (min_le_right _ _).trans (by nlinarith)
  have hsum :
      kloostermanTerminalOrbitHybridEnergy M q r ≤
        L * ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ, C x y := by
    unfold kloostermanTerminalOrbitHybridEnergy kloostermanTerminalOrbitHybridSqBudget
    change (∑ x, ∑ y, min (L ^ 2) (C x y ^ 2)) ≤ _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun y hy => hpoint x y
  calc
    kloostermanTerminalOrbitHybridEnergy M q r ≤
        L * ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ, C x y := hsum
    _ ≤ L * kloostermanProductHarmonicPairBudget q r := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [L]; positivity)
      simpa [C, kloostermanProductHarmonicPairBudget, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one] using
          sum_kloostermanCrossPhaseRatio_reciprocalChord_le_productHarmonic_min
            (q + 1) (r + 1) (Nat.succ_ne_succ_iff.mpr hqr)
    _ = kloostermanTerminalOrbitInterpolatedBudget M q r := by
      rfl

/-- One stored unequal-modulus source quadratic is controlled by exact source-residue energies
and the pointwise hybrid terminal-orbit energy. -/
theorem norm_sourceQuadratic_terminalBlock_succ_sq_le_residue_hybridEnergy_of_ne
    (M q r : ℕ) (hqr : q ≠ r)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
      kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
        (n : ZMod (q + 1)) (k : ZMod (r + 1))‖ ^ 2 ≤
      kloostermanSourceResidueEnergy q B b *
        kloostermanSourceResidueEnergy r B b *
          kloostermanTerminalOrbitHybridEnergy M q r := by
  have hsucc : q + 1 ≠ r + 1 := by omega
  have horbit :
      (∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
        ‖kloostermanTerminalOrbit M (q + 1) (r + 1) x y‖ ^ 2) ≤
        kloostermanTerminalOrbitHybridEnergy M q r := by
    unfold kloostermanTerminalOrbitHybridEnergy
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro y hy
    unfold kloostermanTerminalOrbitHybridSqBudget
    exact norm_kloostermanTerminalOrbit_sq_le_min
      M (q + 1) (r + 1) hsucc x y
  have hsource : 0 ≤
      kloostermanSourceResidueEnergy q B b *
        kloostermanSourceResidueEnergy r B b := by
    unfold kloostermanSourceResidueEnergy
    apply mul_nonneg
    · exact mul_nonneg (by positivity) <|
        Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _
    · exact mul_nonneg (by positivity) <|
        Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _
  calc
    _ ≤ (((q + 1 : ℕ) : ℝ) * ∑ z : ZMod (q + 1),
          Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) *
        (((r + 1 : ℕ) : ℝ) * ∑ z : ZMod (r + 1),
          Complex.normSq (kloostermanSourceResidue (r + 1) B b z)) *
          ∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
            ‖kloostermanTerminalOrbit M (q + 1) (r + 1) x y‖ ^ 2 :=
      norm_sourceQuadratic_terminalBlock_sq_le_residue_hilbertSchmidt
        M (q + 1) (r + 1) B b
    _ ≤ kloostermanSourceResidueEnergy q B b *
        kloostermanSourceResidueEnergy r B b *
          kloostermanTerminalOrbitHybridEnergy M q r := by
      change kloostermanSourceResidueEnergy q B b *
          kloostermanSourceResidueEnergy r B b * _ ≤ _
      exact mul_le_mul_of_nonneg_left horbit hsource

/-- One stored unequal-modulus source quadratic, with the hybrid orbit energy replaced by the
explicit residual-length/product-harmonic interpolation budget. -/
theorem norm_sourceQuadratic_terminalBlock_succ_sq_le_residue_interpolated_of_ne
    (M q r : ℕ) (hqr : q ≠ r)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
      kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
        (n : ZMod (q + 1)) (k : ZMod (r + 1))‖ ^ 2 ≤
      kloostermanSourceResidueEnergy q B b *
        kloostermanSourceResidueEnergy r B b *
          kloostermanTerminalOrbitInterpolatedBudget M q r := by
  calc
    _ ≤ kloostermanSourceResidueEnergy q B b *
        kloostermanSourceResidueEnergy r B b *
          kloostermanTerminalOrbitHybridEnergy M q r :=
      norm_sourceQuadratic_terminalBlock_succ_sq_le_residue_hybridEnergy_of_ne
        M q r hqr B b
    _ ≤ kloostermanSourceResidueEnergy q B b *
        kloostermanSourceResidueEnergy r B b *
          kloostermanTerminalOrbitInterpolatedBudget M q r := by
      apply mul_le_mul_of_nonneg_left
        (kloostermanTerminalOrbitHybridEnergy_le_interpolated_of_ne M q r hqr)
      unfold kloostermanSourceResidueEnergy
      exact mul_nonneg
        (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _))
        (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _))

/-- No-premise erased-modulus sum of terminal source-quadratic energies, bounded by exact source
residue energies and pointwise hybrid terminal-orbit budgets. -/
theorem sum_norm_sourceQuadratic_terminalBlock_succ_sq_le_residue_hybridEnergy
    (M : ℕ) (Q B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ q ∈ Q, ∑ r ∈ Q.erase q,
      ‖∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
        kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
          (n : ZMod (q + 1)) (k : ZMod (r + 1))‖ ^ 2) ≤
      ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        kloostermanSourceResidueEnergy q B b *
          kloostermanSourceResidueEnergy r B b *
            kloostermanTerminalOrbitHybridEnergy M q r := by
  classical
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro r hr
  exact norm_sourceQuadratic_terminalBlock_succ_sq_le_residue_hybridEnergy_of_ne
    M q r (Ne.symm (Finset.mem_erase.mp hr).1) B b

/-- No-premise interpolation of the erased-pair hybrid receiver by residual length times the
shared-gcd-safe product-harmonic budget. -/
theorem sum_kloostermanSourceResidue_hybridEnergy_le_interpolatedBudget
    (M : ℕ) (Q B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ q ∈ Q, ∑ r ∈ Q.erase q,
      kloostermanSourceResidueEnergy q B b *
        kloostermanSourceResidueEnergy r B b *
          kloostermanTerminalOrbitHybridEnergy M q r) ≤
      ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        kloostermanSourceResidueEnergy q B b *
          kloostermanSourceResidueEnergy r B b *
            kloostermanTerminalOrbitInterpolatedBudget M q r := by
  classical
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro r hr
  apply mul_le_mul_of_nonneg_left
    (kloostermanTerminalOrbitHybridEnergy_le_interpolated_of_ne
      M q r (Ne.symm (Finset.mem_erase.mp hr).1))
  unfold kloostermanSourceResidueEnergy
  apply mul_nonneg
  · exact mul_nonneg (by positivity) <|
      Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _
  · exact mul_nonneg (by positivity) <|
      Finset.sum_nonneg fun z hz => Complex.normSq_nonneg _

private theorem norm_dependent_sum_mul_sq_le_sq_mul_sq
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (D : α → Finset β)
    (a s : α → β → ℂ) :
    ‖∑ i ∈ A, ∑ j ∈ D i, a i j * s i j‖ ^ 2 ≤
      (∑ i ∈ A, ∑ j ∈ D i, ‖a i j‖ ^ 2) *
        ∑ i ∈ A, ∑ j ∈ D i, ‖s i j‖ ^ 2 := by
  have htri :
      ‖∑ i ∈ A, ∑ j ∈ D i, a i j * s i j‖ ≤
        ∑ i ∈ A, ∑ j ∈ D i, ‖a i j‖ * ‖s i j‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro i hi
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_mul]
  have hsum0 : 0 ≤ ∑ i ∈ A, ∑ j ∈ D i, ‖a i j‖ * ‖s i j‖ := by
    positivity
  calc
    ‖∑ i ∈ A, ∑ j ∈ D i, a i j * s i j‖ ^ 2 ≤
        (∑ i ∈ A, ∑ j ∈ D i, ‖a i j‖ * ‖s i j‖) ^ 2 := by
      nlinarith [norm_nonneg (∑ i ∈ A, ∑ j ∈ D i, a i j * s i j)]
    _ ≤ (∑ i ∈ A, ∑ j ∈ D i, ‖a i j‖ ^ 2) *
        ∑ i ∈ A, ∑ j ∈ D i, ‖s i j‖ ^ 2 := by
      rw [Finset.sum_sigma' A D (fun i j => ‖a i j‖ * ‖s i j‖)]
      rw [Finset.sum_sigma' A D (fun i j => ‖a i j‖ ^ 2)]
      rw [Finset.sum_sigma' A D (fun i j => ‖s i j‖ ^ 2)]
      exact Finset.sum_mul_sq_le_sq_mul_sq (A.sigma D)
        (fun p => ‖a p.1 p.2‖) (fun p => ‖s p.1 p.2‖)

/-- Exact squared `ℓ²` energy of ordered unequal-modulus weight pairs. -/
def kloostermanDistinctModulusWeightPairEnergy
    (Q : Finset ℕ) (w : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, ∑ r ∈ Q.erase q, ‖w q‖ ^ 2 * ‖w r‖ ^ 2

/-- Full weighted terminal Gram quadratic bounded by the ordered weight-pair energy times the
source-residue/orbit hybrid receiver. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_weightPair_residue_hybridEnergy
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ^ 2 ≤
      kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanSourceResidueEnergy q B b *
            kloostermanSourceResidueEnergy r B b *
              kloostermanTerminalOrbitHybridEnergy M q r := by
  classical
  rw [kloostermanDistinctModulusTerminalGramQuadratic_eq_sourceFourierOrbits]
  simp_rw [← sourceQuadratic_terminalBlock_eq_fourierOrbits]
  calc
    ‖∑ q ∈ Q, ∑ r ∈ Q.erase q,
        star (w q) * w r *
          (∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
            kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
              (n : ZMod (q + 1)) (k : ZMod (r + 1)))‖ ^ 2 ≤
        (∑ q ∈ Q, ∑ r ∈ Q.erase q, ‖star (w q) * w r‖ ^ 2) *
          ∑ q ∈ Q, ∑ r ∈ Q.erase q,
            ‖∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
              kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
                (n : ZMod (q + 1)) (k : ZMod (r + 1))‖ ^ 2 :=
      norm_dependent_sum_mul_sq_le_sq_mul_sq Q (fun q => Q.erase q)
        (fun q r => star (w q) * w r)
        (fun q r => ∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
          kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
            (n : ZMod (q + 1)) (k : ZMod (r + 1)))
    _ ≤ kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanSourceResidueEnergy q B b *
            kloostermanSourceResidueEnergy r B b *
              kloostermanTerminalOrbitHybridEnergy M q r := by
      unfold kloostermanDistinctModulusWeightPairEnergy
      simp_rw [norm_mul, norm_star, mul_pow]
      exact mul_le_mul_of_nonneg_left
        (sum_norm_sourceQuadratic_terminalBlock_succ_sq_le_residue_hybridEnergy M Q B b)
        (Finset.sum_nonneg fun q hq => Finset.sum_nonneg fun r hr => by positivity)

/-- Fully explicit no-premise weighted terminal Gram receiver using residual-length/product-
harmonic interpolation for every erased modulus pair. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_weightPair_residue_interpolated
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ^ 2 ≤
      kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanSourceResidueEnergy q B b *
            kloostermanSourceResidueEnergy r B b *
              kloostermanTerminalOrbitInterpolatedBudget M q r := by
  calc
    _ ≤ kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanSourceResidueEnergy q B b *
            kloostermanSourceResidueEnergy r B b *
              kloostermanTerminalOrbitHybridEnergy M q r :=
      norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_weightPair_residue_hybridEnergy
        M Q w B b
    _ ≤ kloostermanDistinctModulusWeightPairEnergy Q w *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          kloostermanSourceResidueEnergy q B b *
            kloostermanSourceResidueEnergy r B b *
              kloostermanTerminalOrbitInterpolatedBudget M q r := by
      apply mul_le_mul_of_nonneg_left
        (sum_kloostermanSourceResidue_hybridEnergy_le_interpolatedBudget M Q B b)
      unfold kloostermanDistinctModulusWeightPairEnergy
      positivity

/-! ### Exact Schur-row receiver -/

/-- Square-root pair kernel obtained from exact source-residue energies and the interpolated
terminal-orbit budget. -/
def kloostermanTerminalSchurPairBudget
    (M q r : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  Real.sqrt
    (kloostermanSourceResidueEnergy q B b *
      kloostermanSourceResidueEnergy r B b *
        kloostermanTerminalOrbitInterpolatedBudget M q r)

private theorem kloostermanProductHarmonicPairBudget_comm (q r : ℕ) :
    kloostermanProductHarmonicPairBudget q r =
      kloostermanProductHarmonicPairBudget r q := by
  unfold kloostermanProductHarmonicPairBudget
  rw [Nat.mul_comm (q + 1) (r + 1)]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [mul_comm ((q : ℝ) + 1) ((r : ℝ) + 1), min_comm]

private theorem kloostermanTerminalOrbitInterpolatedBudget_comm (M q r : ℕ) :
    kloostermanTerminalOrbitInterpolatedBudget M q r =
      kloostermanTerminalOrbitInterpolatedBudget M r q := by
  unfold kloostermanTerminalOrbitInterpolatedBudget
  rw [Nat.lcm_comm (q + 1) (r + 1), kloostermanProductHarmonicPairBudget_comm]

private theorem kloostermanTerminalSchurPairBudget_comm
    (M q r : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanTerminalSchurPairBudget M q r B b =
      kloostermanTerminalSchurPairBudget M r q B b := by
  unfold kloostermanTerminalSchurPairBudget
  rw [kloostermanTerminalOrbitInterpolatedBudget_comm M q r]
  congr 1
  ring

private theorem kloostermanTerminalSchurPairBudget_nonneg
    (M q r : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) :
    0 ≤ kloostermanTerminalSchurPairBudget M q r B b := by
  unfold kloostermanTerminalSchurPairBudget
  exact Real.sqrt_nonneg _

/-- Symmetric off-diagonal Schur kernel, zero on the modulus diagonal. -/
def kloostermanTerminalSchurKernel
    (M : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) (q r : ℕ) : ℝ :=
  if q = r then 0 else kloostermanTerminalSchurPairBudget M q r B b

/-- Exact row mass of the terminal Schur kernel over the stored modulus family. -/
def kloostermanTerminalSchurRowBudget
    (M : ℕ) (Q B : Finset ℕ) (b : ℕ → ℂ) (q : ℕ) : ℝ :=
  ∑ r ∈ Q, kloostermanTerminalSchurKernel M B b q r

/-- Modulus-weight energy charged row-by-row against the terminal Schur kernel. -/
def kloostermanTerminalSchurWeightEnergy
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ q ∈ Q, ‖w q‖ ^ 2 * kloostermanTerminalSchurRowBudget M Q B b q

private theorem kloostermanTerminalSchurKernel_comm
    (M : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) (q r : ℕ) :
    kloostermanTerminalSchurKernel M B b q r =
      kloostermanTerminalSchurKernel M B b r q := by
  unfold kloostermanTerminalSchurKernel
  by_cases h : q = r
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h), kloostermanTerminalSchurPairBudget_comm]

private theorem kloostermanTerminalSchurKernel_nonneg
    (M : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) (q r : ℕ) :
    0 ≤ kloostermanTerminalSchurKernel M B b q r := by
  unfold kloostermanTerminalSchurKernel
  split_ifs
  · exact le_rfl
  · exact kloostermanTerminalSchurPairBudget_nonneg M q r B b

private theorem norm_sourceQuadratic_terminalBlock_succ_le_schurPair_of_ne
    (M q r : ℕ) (hqr : q ≠ r)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
      kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
        (n : ZMod (q + 1)) (k : ZMod (r + 1))‖ ≤
      kloostermanTerminalSchurPairBudget M q r B b := by
  rw [kloostermanTerminalSchurPairBudget]
  rw [show ‖∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
      kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
        (n : ZMod (q + 1)) (k : ZMod (r + 1))‖ =
      Real.sqrt (‖∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
        kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
          (n : ZMod (q + 1)) (k : ZMod (r + 1))‖ ^ 2) by
    rw [Real.sqrt_sq (norm_nonneg _)]]
  exact Real.sqrt_le_sqrt
    (norm_sourceQuadratic_terminalBlock_succ_sq_le_residue_interpolated_of_ne
      M q r hqr B b)

private theorem symmetric_schur_rows
    {α : Type*} [DecidableEq α]
    (S : Finset α) (a : α → ℝ) (K : α → α → ℝ)
    (hKsymm : ∀ i j, K i j = K j i)
    (hKnn : ∀ i j, 0 ≤ K i j) :
    (∑ i ∈ S, ∑ j ∈ S, |a i| * |a j| * K i j) ≤
      ∑ i ∈ S, (a i) ^ 2 * ∑ j ∈ S, K i j := by
  have hamgm : ∀ i j, |a i| * |a j| * K i j ≤
      ((a i) ^ 2 / 2 + (a j) ^ 2 / 2) * K i j := by
    intro i j
    apply mul_le_mul_of_nonneg_right _ (hKnn i j)
    nlinarith [sq_nonneg (|a i| - |a j|), sq_abs (a i), sq_abs (a j)]
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S,
        ((a i) ^ 2 / 2 + (a j) ^ 2 / 2) * K i j := by
      exact Finset.sum_le_sum fun i hi =>
        Finset.sum_le_sum fun j hj => hamgm i j
    _ = (∑ i ∈ S, (a i) ^ 2 / 2 * ∑ j ∈ S, K i j) +
        ∑ i ∈ S, ∑ j ∈ S, (a j) ^ 2 / 2 * K i j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ i ∈ S, (a i) ^ 2 / 2 * ∑ j ∈ S, K i j) +
        ∑ j ∈ S, (a j) ^ 2 / 2 * ∑ i ∈ S, K j i := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hKsymm i j]
    _ = ∑ i ∈ S, (a i) ^ 2 * ∑ j ∈ S, K i j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Full terminal Gram quadratic controlled by exact symmetric Schur rows.  This avoids the
global product of modulus-pair weight energy and source/orbit energy: each squared modulus weight
is charged only against its own terminal-kernel row.  No spectral cancellation is assumed. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_le_schurWeightEnergy
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ≤
      kloostermanTerminalSchurWeightEnergy M Q w B b := by
  classical
  rw [kloostermanDistinctModulusTerminalGramQuadratic_eq_sourceFourierOrbits]
  simp_rw [← sourceQuadratic_terminalBlock_eq_fourierOrbits]
  let S : ℕ → ℕ → ℂ := fun q r =>
    ∑ n ∈ B, star (b n) * ∑ k ∈ B, b k *
      kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
        (n : ZMod (q + 1)) (k : ZMod (r + 1))
  calc
    ‖∑ q ∈ Q, ∑ r ∈ Q.erase q, star (w q) * w r * S q r‖ ≤
        ∑ q ∈ Q, ∑ r ∈ Q.erase q, ‖star (w q) * w r * S q r‖ := by
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro q hq
      exact norm_sum_le _ _
    _ = ∑ q ∈ Q, ∑ r ∈ Q.erase q, ‖w q‖ * ‖w r‖ * ‖S q r‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r hr
      rw [norm_mul, norm_mul, norm_star]
    _ ≤ ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        ‖w q‖ * ‖w r‖ * kloostermanTerminalSchurPairBudget M q r B b := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left
      · dsimp only [S]
        exact norm_sourceQuadratic_terminalBlock_succ_le_schurPair_of_ne
          M q r (Ne.symm (Finset.mem_erase.mp hr).1) B b
      · positivity
    _ = ∑ q ∈ Q, ∑ r ∈ Q,
        ‖w q‖ * ‖w r‖ * kloostermanTerminalSchurKernel M B b q r := by
      apply Finset.sum_congr rfl
      intro q hq
      let f : ℕ → ℝ := fun r =>
        ‖w q‖ * ‖w r‖ * kloostermanTerminalSchurKernel M B b q r
      have hfq : f q = 0 := by simp [f, kloostermanTerminalSchurKernel]
      rw [← Finset.sum_erase Q hfq]
      apply Finset.sum_congr rfl
      intro r hr
      have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
      simp only [f, kloostermanTerminalSchurKernel, if_neg (Ne.symm hrq)]
    _ ≤ ∑ q ∈ Q, ‖w q‖ ^ 2 * ∑ r ∈ Q,
        kloostermanTerminalSchurKernel M B b q r := by
      simpa only [abs_norm] using
        symmetric_schur_rows Q (fun q => ‖w q‖)
          (kloostermanTerminalSchurKernel M B b)
          (kloostermanTerminalSchurKernel_comm M B b)
          (kloostermanTerminalSchurKernel_nonneg M B b)
    _ = kloostermanTerminalSchurWeightEnergy M Q w B b := by
      rfl

end

end RHTower.Sieve
