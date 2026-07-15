import GaloisForLFunctions.HTGeometry.PrimeWalshDifferentialRank
import Mathlib.Analysis.Subadditive
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Prefix complexity and entropy of the Prime-Walsh rank profile

This file packages the cofinal finite-coordinate rank law.  For an orientation family indexed by
`ℕ`, the length-`n` recurring-pattern chamber is the prefix language of the compact tail
constraint.  Its cardinality is the prefix covering number for the standard Boolean prefix
ultrametric.  The exact differential basis from `PrimeWalshDifferentialRank` has one generator for
every prefix pattern and every chosen shift.

The normalized logarithmic upper and lower growth rates are expressed in `ℝ≥0∞`.  Multiplying all
prefix complexities by the fixed nonzero number of shifts adds a constant logarithm, whose
normalized contribution tends to zero.  Thus both box-growth rates, and hence the entropy rate
when the upper and lower rates agree, are exactly unchanged by passing to differential rank.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter
open scoped Topology

noncomputable section

/-- Length-`n` restriction of a countable Boolean prime orientation family. -/
def primePrefixOrientation
    (ε : ℕ → Nat.Primes → Bool) (n : ℕ) : Fin n → Nat.Primes → Bool :=
  fun i p => ε i.1 p

/-- The number of length-`n` Boolean patterns recurring arbitrarily far out in the prime
enumeration.  This is the prefix-cylinder covering number of the compact prime-tail constraint. -/
noncomputable def primePrefixPatternComplexity
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool) (n : ℕ) : ℕ :=
  Nat.card (primeRecurringPatternChamber e (primePrefixOrientation ε n))

theorem primePrefixPatternComplexity_pos
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool) (n : ℕ) :
    0 < primePrefixPatternComplexity e ε n := by
  letI : Nonempty
      (primeRecurringPatternChamber e (primePrefixOrientation ε n)) :=
    (primeOrientationTailClusterSet_nonempty
      (fun k i => primePrefixOrientation ε n i (e k))).to_subtype
  exact Nat.card_pos

/-- The labelled differential rank supplied by a finite nonempty shift family at prefix length
`n`.  The basis theorem below proves that this number is realized by the Prime-Walsh field. -/
noncomputable def primeWalshPrefixDifferentialRank
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool) (A : Type*) (n : ℕ) : ℕ :=
  Nat.card A * primePrefixPatternComplexity e ε n

/-- Every prefix rank is realized by an explicit differentially independent recurring-pattern
delta basis generating the complete finite Prime-Walsh palette. -/
theorem primeWalshPrefixDifferentialBasis
    {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool)
    (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re)) (n : ℕ) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (primeTailPatternDeltaShiftPalette e (primePrefixOrientation ε n) alpha) ∧
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range
            (primeTailPatternDeltaShiftPalette e (primePrefixOrientation ε n) alpha)) =
        GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (primeWalshShiftPalette (primePrefixOrientation ε n) alpha)) :=
  primeWalshShiftPalette_differentialBasis
    e (primePrefixOrientation ε n) alpha hdistinct

/-- The explicit basis index has exactly the declared prefix differential rank. -/
theorem primeWalshPrefixDifferentialBasis_card
    {A : Type*} [Finite A]
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool) (n : ℕ) :
    Nat.card
        (primeRecurringPatternChamber e (primePrefixOrientation ε n) × A) =
      primeWalshPrefixDifferentialRank e ε A n := by
  rw [Nat.card_prod, primeWalshPrefixDifferentialRank,
    primePrefixPatternComplexity, Nat.mul_comm]

/-- Normalized natural logarithm of a finite cardinality. -/
noncomputable def normalizedLogCard (m n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.log (m : ℝ)) / n

theorem normalizedLogCard_mul
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k) (n : ℕ) :
    normalizedLogCard (m * k) n =
      normalizedLogCard m n + normalizedLogCard k n := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [normalizedLogCard, normalizedLogCard, normalizedLogCard,
    Nat.cast_mul, Real.log_mul hm0 hk0,
    ENNReal.ofReal_add (Real.log_nonneg hm1) (Real.log_nonneg hk1),
    ENNReal.add_div]

/-- Upper normalized logarithmic growth of an integer complexity sequence. -/
noncomputable def upperNormalizedLogGrowth (C : ℕ → ℕ) : ℝ≥0∞ :=
  limsup (fun n => normalizedLogCard (C n) n) atTop

/-- Lower normalized logarithmic growth of an integer complexity sequence. -/
noncomputable def lowerNormalizedLogGrowth (C : ℕ → ℕ) : ℝ≥0∞ :=
  liminf (fun n => normalizedLogCard (C n) n) atTop

/-- A fixed positive multiplicative factor does not change upper normalized logarithmic growth. -/
theorem upperNormalizedLogGrowth_mul_const
    (A : ℕ) (hA : 0 < A) (C : ℕ → ℕ) (hC : ∀ n, 0 < C n) :
    upperNormalizedLogGrowth (fun n => A * C n) = upperNormalizedLogGrowth C := by
  have hpoint : ∀ n, normalizedLogCard (A * C n) n =
      normalizedLogCard (C n) n + normalizedLogCard A n := by
    intro n
    rw [normalizedLogCard_mul hA (hC n), add_comm]
  have hzero : Tendsto (fun n => normalizedLogCard A n) atTop (𝓝 0) := by
    exact tendsto_const_div_atTop_nhds_zero_nat _
  rw [upperNormalizedLogGrowth, upperNormalizedLogGrowth]
  calc
    limsup (fun n => normalizedLogCard (A * C n) n) atTop =
        limsup (fun n => normalizedLogCard (C n) n + normalizedLogCard A n) atTop :=
      limsup_congr (Eventually.of_forall hpoint)
    _ = limsup (fun n => normalizedLogCard (C n) n) atTop := by
      simpa only [Pi.add_apply] using
        (limsup_add_of_right_tendsto_zero hzero
          (fun n => normalizedLogCard (C n) n))

/-- A fixed positive multiplicative factor does not change lower normalized logarithmic growth. -/
theorem lowerNormalizedLogGrowth_mul_const
    (A : ℕ) (hA : 0 < A) (C : ℕ → ℕ) (hC : ∀ n, 0 < C n) :
    lowerNormalizedLogGrowth (fun n => A * C n) = lowerNormalizedLogGrowth C := by
  have hpoint : ∀ n, normalizedLogCard (A * C n) n =
      normalizedLogCard (C n) n + normalizedLogCard A n := by
    intro n
    rw [normalizedLogCard_mul hA (hC n), add_comm]
  have hzero : Tendsto (fun n => normalizedLogCard A n) atTop (𝓝 0) := by
    exact tendsto_const_div_atTop_nhds_zero_nat _
  rw [lowerNormalizedLogGrowth, lowerNormalizedLogGrowth]
  calc
    liminf (fun n => normalizedLogCard (A * C n) n) atTop =
        liminf (fun n => normalizedLogCard (C n) n + normalizedLogCard A n) atTop :=
      liminf_congr (Eventually.of_forall hpoint)
    _ = liminf (fun n => normalizedLogCard (C n) n) atTop := by
      simpa only [Pi.add_apply] using
        (liminf_add_of_right_tendsto_zero hzero
          (fun n => normalizedLogCard (C n) n))

/-- Real-valued normalized logarithm, used for the convergent entropy-rate statement. -/
noncomputable def realNormalizedLogCard (m n : ℕ) : ℝ :=
  Real.log (m : ℝ) / n

theorem realNormalizedLogCard_mul
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k) (n : ℕ) :
    realNormalizedLogCard (m * k) n =
      realNormalizedLogCard m n + realNormalizedLogCard k n := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [realNormalizedLogCard, realNormalizedLogCard, realNormalizedLogCard,
    Nat.cast_mul, Real.log_mul hm0 hk0, add_div]

/-- Fekete's lemma gives an actual normalized logarithmic limit whenever the log-complexity is
subadditive. -/
theorem realNormalizedLogCard_tendsto_of_subadditive
    (C : ℕ → ℕ) (hC : ∀ n, 0 < C n)
    (hsub : Subadditive (fun n => Real.log (C n : ℝ))) :
    ∃ h : ℝ, Tendsto (fun n => realNormalizedLogCard (C n) n) atTop (𝓝 h) := by
  let u : ℕ → ℝ := fun n => Real.log (C n : ℝ)
  have hbdd : BddBelow (Set.range fun n => u n / n) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast hC n)) (Nat.cast_nonneg n)
  exact ⟨hsub.lim, by
    simpa only [u, realNormalizedLogCard] using hsub.tendsto_lim hbdd⟩

/-- The same Fekete limit is obtained after multiplying every complexity by a fixed positive
shift count. -/
theorem realNormalizedLogRank_tendsto_of_subadditive
    (A : ℕ) (hA : 0 < A) (C : ℕ → ℕ) (hC : ∀ n, 0 < C n)
    (hsub : Subadditive (fun n => Real.log (C n : ℝ))) :
    ∃ h : ℝ,
      Tendsto (fun n => realNormalizedLogCard (C n) n) atTop (𝓝 h) ∧
      Tendsto (fun n => realNormalizedLogCard (A * C n) n) atTop (𝓝 h) := by
  obtain ⟨h, hlim⟩ := realNormalizedLogCard_tendsto_of_subadditive C hC hsub
  have hconst : Tendsto (fun n => realNormalizedLogCard A n) atTop (𝓝 0) := by
    exact tendsto_const_div_atTop_nhds_zero_nat _
  refine ⟨h, hlim, ?_⟩
  have hadd := hlim.add hconst
  simpa only [add_zero] using hadd.congr' (Eventually.of_forall fun n => by
    rw [realNormalizedLogCard_mul hA (hC n)])

/-- Upper prefix box dimension, expressed through the exact prefix-cylinder cover numbers. -/
noncomputable def primeTailUpperPrefixBoxDimension
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool) : ℝ≥0∞ :=
  upperNormalizedLogGrowth (primePrefixPatternComplexity e ε) /
    ENNReal.ofReal (Real.log 2)

/-- Lower prefix box dimension, expressed through the exact prefix-cylinder cover numbers. -/
noncomputable def primeTailLowerPrefixBoxDimension
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool) : ℝ≥0∞ :=
  lowerNormalizedLogGrowth (primePrefixPatternComplexity e ε) /
    ENNReal.ofReal (Real.log 2)

/-- Upper normalized differential-rank growth in base two. -/
noncomputable def primeWalshUpperRankBoxGrowth
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool) (A : Type*) : ℝ≥0∞ :=
  upperNormalizedLogGrowth (primeWalshPrefixDifferentialRank e ε A) /
    ENNReal.ofReal (Real.log 2)

/-- Lower normalized differential-rank growth in base two. -/
noncomputable def primeWalshLowerRankBoxGrowth
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool) (A : Type*) : ℝ≥0∞ :=
  lowerNormalizedLogGrowth (primeWalshPrefixDifferentialRank e ε A) /
    ENNReal.ofReal (Real.log 2)

/-- **Upper HT--Stone box-dimension law.**  The upper prefix box dimension of the nonlinear tail
constraint is exactly the upper normalized differential-rank growth of every finite nonempty shift
palette. -/
theorem primeWalshUpperRankBoxGrowth_eq_tailDimension
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool)
    (A : Type*) [Finite A] [Nonempty A] :
    primeWalshUpperRankBoxGrowth e ε A = primeTailUpperPrefixBoxDimension e ε := by
  rw [primeWalshUpperRankBoxGrowth, primeTailUpperPrefixBoxDimension,
    primeWalshPrefixDifferentialRank,
    upperNormalizedLogGrowth_mul_const (Nat.card A) Nat.card_pos
      (primePrefixPatternComplexity e ε) (primePrefixPatternComplexity_pos e ε)]

/-- **Lower HT--Stone box-dimension law.**  The lower prefix box dimension of the nonlinear tail
constraint is exactly the lower normalized differential-rank growth. -/
theorem primeWalshLowerRankBoxGrowth_eq_tailDimension
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool)
    (A : Type*) [Finite A] [Nonempty A] :
    primeWalshLowerRankBoxGrowth e ε A = primeTailLowerPrefixBoxDimension e ε := by
  rw [primeWalshLowerRankBoxGrowth, primeTailLowerPrefixBoxDimension,
    primeWalshPrefixDifferentialRank,
    lowerNormalizedLogGrowth_mul_const (Nat.card A) Nat.card_pos
      (primePrefixPatternComplexity e ε) (primePrefixPatternComplexity_pos e ε)]

/-- Prefix entropy is the natural-log normalized growth of the recurring finite language. -/
noncomputable def primeTailPrefixEntropy
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool) : ℝ≥0∞ :=
  upperNormalizedLogGrowth (primePrefixPatternComplexity e ε)

/-- **HT--Stone entropy law.**  Differential-rank growth has exactly the same entropy rate as the
complete recurring prefix language. -/
theorem primeWalshRankEntropy_eq_tailEntropy
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool)
    (A : Type*) [Finite A] [Nonempty A] :
    upperNormalizedLogGrowth (primeWalshPrefixDifferentialRank e ε A) =
      primeTailPrefixEntropy e ε := by
  rw [primeTailPrefixEntropy, primeWalshPrefixDifferentialRank,
    upperNormalizedLogGrowth_mul_const (Nat.card A) Nat.card_pos
      (primePrefixPatternComplexity e ε) (primePrefixPatternComplexity_pos e ε)]

/-- If the prefix log-complexity is subadditive—as it is for a shift-invariant prefix language—
then the normalized prefix complexity and the exact Prime-Walsh differential rank converge to the
same entropy rate. -/
theorem primeWalshRankEntropy_tendsto_of_subadditive
    (e : ℕ ≃ Nat.Primes) (ε : ℕ → Nat.Primes → Bool)
    (A : Type*) [Finite A] [Nonempty A]
    (hsub : Subadditive
      (fun n => Real.log (primePrefixPatternComplexity e ε n : ℝ))) :
    ∃ h : ℝ,
      Tendsto
          (fun n => realNormalizedLogCard (primePrefixPatternComplexity e ε n) n)
          atTop (𝓝 h) ∧
      Tendsto
          (fun n => realNormalizedLogCard
            (primeWalshPrefixDifferentialRank e ε A n) n)
          atTop (𝓝 h) := by
  simpa only [primeWalshPrefixDifferentialRank] using
    realNormalizedLogRank_tendsto_of_subadditive
      (Nat.card A) Nat.card_pos (primePrefixPatternComplexity e ε)
      (primePrefixPatternComplexity_pos e ε) hsub

end

end GaloisForLFunctions.HTGeometry
