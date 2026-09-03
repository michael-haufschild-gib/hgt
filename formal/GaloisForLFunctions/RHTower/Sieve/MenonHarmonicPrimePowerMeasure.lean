import GaloisForLFunctions.RHTower.Sieve.DirichletPowerMeasure
import GaloisForLFunctions.RHTower.Sieve.LogPolyRestrict
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareBlockSplit
import GaloisForLFunctions.RHTower.Sieve.LadderErrorBudget
import GaloisForLFunctions.RHTower.Sieve.GeomBlockPrimesRange

/-!
# Adapted moments for Menon's harmonic prime blocks

The harmonic prime factor in Menon's Ramaré ladder is already a prime-supported Dirichlet
polynomial.  Its coefficient at a prime `p` has norm exactly `1 / p`.  Consequently the free-power
prime-support estimate applies directly, without reverse Abel summation, sharp interval smoothing,
or a Heath--Brown decomposition.

For a block above `q`, the coefficient energy is at most `#B / q²`.  On a geometric ladder step
this is at most `(q η + 1) / q²`, preserving the decisive power of the relative block width.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- A harmonic prime block is the corresponding zero-extended Dirichlet polynomial. -/
theorem harmonicPrimeBlockPoly_eq_dirPoly (B : Finset ℕ) (N : ℕ)
    (hB : B ⊆ Finset.Icc 1 N) (w : ℝ) :
    harmonicPrimeBlockPoly B w =
      dirPoly N
        (fun n : Fin N => restrictCoeff B harmonicMoebiusC ((n : ℕ) + 1))
        (2 * Real.pi * w) := by
  rw [harmonicPrimeBlockPoly, ← logPoly_harmonicMoebius_eq_sum_phase,
    logPoly_subset_eq_dirPoly harmonicMoebiusC hB]

/-- The zero-extended harmonic coefficient remains supported on primes. -/
theorem harmonicPrimeBlockCoeff_primeSupport (B : Finset ℕ) (N : ℕ)
    (hBprime : ∀ p ∈ B, p.Prime) :
    ∀ n : Fin N,
      restrictCoeff B harmonicMoebiusC ((n : ℕ) + 1) ≠ 0 →
        Nat.Prime ((n : ℕ) + 1) := by
  intro n hn
  by_cases hmem : (n : ℕ) + 1 ∈ B
  · exact hBprime _ hmem
  · simp [restrictCoeff, hmem] at hn

/-- At a prime, the harmonic Möbius coefficient has norm `1 / p`. -/
theorem norm_harmonicMoebiusC_prime {p : ℕ} (hp : p.Prime) :
    ‖harmonicMoebiusC p‖ = 1 / (p : ℝ) := by
  simpa [harmonicMoebiusPhase, harmonicMoebiusC, moebiusPhase, unitLogPhase] using
    norm_harmonicMoebiusPhase_prime hp 0

/-- The harmonic coefficient energy of a prime block above `q` is at most `#B / q²`. -/
theorem sum_normSq_harmonicPrimeBlockCoeff_le
    {B : Finset ℕ} {N : ℕ} {q : ℝ}
    (hB : B ⊆ Finset.Icc 1 N) (hBprime : ∀ p ∈ B, p.Prime)
    (hq : 0 < q) (hlower : ∀ p ∈ B, q < (p : ℝ)) :
    ∑ n : Fin N, ‖restrictCoeff B harmonicMoebiusC ((n : ℕ) + 1)‖ ^ 2
      ≤ (B.card : ℝ) / q ^ 2 := by
  rw [show
    (∑ n : Fin N, ‖restrictCoeff B harmonicMoebiusC ((n : ℕ) + 1)‖ ^ 2) =
      ∑ k ∈ Finset.Icc 1 N, ‖restrictCoeff B harmonicMoebiusC k‖ ^ 2 from
        sum_fin_eq_sum_Icc N
          (fun k => ‖restrictCoeff B harmonicMoebiusC k‖ ^ 2)]
  have hsum :
      ∑ k ∈ Finset.Icc 1 N, ‖restrictCoeff B harmonicMoebiusC k‖ ^ 2 =
        ∑ k ∈ B, ‖harmonicMoebiusC k‖ ^ 2 := by
    calc
      ∑ k ∈ Finset.Icc 1 N, ‖restrictCoeff B harmonicMoebiusC k‖ ^ 2 =
          ∑ k ∈ B, ‖restrictCoeff B harmonicMoebiusC k‖ ^ 2 := by
            symm
            exact Finset.sum_subset hB (by
              intro k hkIcc hkB
              simp [restrictCoeff, hkB])
      _ = ∑ k ∈ B, ‖harmonicMoebiusC k‖ ^ 2 := by
        refine Finset.sum_congr rfl fun k hk => ?_
        simp [restrictCoeff, hk]
  rw [hsum]
  calc
    ∑ k ∈ B, ‖harmonicMoebiusC k‖ ^ 2
        = ∑ k ∈ B, (1 / (k : ℝ)) ^ 2 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [norm_harmonicMoebiusC_prime (hBprime k hk)]
    _ ≤ ∑ _k ∈ B, (1 / q) ^ 2 := by
      gcongr with k hk
      exact (hlower k hk).le
    _ = (B.card : ℝ) / q ^ 2 := by
      simp [Finset.sum_const, div_eq_mul_inv]

/-- The adapted `2k`-th-moment bound for the actual harmonic prime block, in Menon's reflected
physical frequency. -/
theorem volume_harmonicPrimeBlock_largeValues_pow_le
    (k N : ℕ) (hk : 1 ≤ k) {B : Finset ℕ} {q T V : ℝ}
    (hB : B ⊆ Finset.Icc 1 N) (hBprime : ∀ p ∈ B, p.Prime)
    (hq : 0 < q) (hlower : ∀ p ∈ B, q < (p : ℝ))
    (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ (2 * k) * volume.real
        {x ∈ Set.Icc (-T) T |
          V ≤ ‖harmonicPrimeBlockPoly B (-x / (2 * Real.pi))‖} ≤
      2 * ((T + 4 * ((N ^ k : ℕ) : ℝ) *
              (1 + Real.log ((N ^ k : ℕ) : ℝ))) *
        ((k : ℝ) ^ k * ((B.card : ℝ) / q ^ 2) ^ k)) := by
  let c : Fin N → ℂ :=
    fun n => restrictCoeff B harmonicMoebiusC ((n : ℕ) + 1)
  let cstar : Fin N → ℂ := fun n => (starRingEnd ℂ) (c n)
  have hsupp : ∀ n : Fin N, cstar n ≠ 0 → Nat.Prime ((n : ℕ) + 1) := by
    intro n hn
    have hcn : c n ≠ 0 := by
      intro hc
      apply hn
      simp [cstar, hc]
    apply harmonicPrimeBlockCoeff_primeSupport B N hBprime n
    simpa only [c] using hcn
  have hpoly : ∀ x : ℝ,
      ‖harmonicPrimeBlockPoly B (-x / (2 * Real.pi))‖ =
        ‖dirPoly N cstar x‖ := by
    intro x
    rw [harmonicPrimeBlockPoly_eq_dirPoly B N hB]
    have harg : 2 * Real.pi * (-x / (2 * Real.pi)) = -x := by
      field_simp [Real.pi_ne_zero]
    rw [harg]
    calc
      ‖dirPoly N c (-x)‖ = ‖(starRingEnd ℂ) (dirPoly N c (-x))‖ := by
        rw [RCLike.norm_conj]
      _ = ‖dirPoly N cstar x‖ := by
        rw [← dirPoly_conj_neg]
  have hset :
      {x ∈ Set.Icc (-T) T |
          V ≤ ‖harmonicPrimeBlockPoly B (-x / (2 * Real.pi))‖} =
        {x ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N cstar x‖} := by
    ext x
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    intro _
    rw [hpoly x]
  rw [hset]
  have hbase := volume_largeValues_pow_symm_le_of_prime_support
    k N hk cstar hsupp hT hV
  refine hbase.trans ?_
  have henergy : ∑ n : Fin N, ‖cstar n‖ ^ 2 ≤ (B.card : ℝ) / q ^ 2 := by
    simpa only [cstar, RCLike.norm_conj, c] using
      sum_normSq_harmonicPrimeBlockCoeff_le hB hBprime hq hlower
  gcongr

/-- On one geometric Ramaré step, the adapted moment retains the full relative-width saving. -/
theorem volume_harmonicGeomPrimeBlock_largeValues_pow_le
    (k N : ℕ) (hk : 1 ≤ k) {P : Finset ℕ} {Q eta T V : ℝ} (j : ℕ)
    (hP : P ⊆ Finset.Icc 1 N) (hPprime : ∀ p ∈ P, p.Prime)
    (hQ : 0 < Q) (heta : 0 ≤ eta) (hT : 0 ≤ T) (hV : 0 ≤ V) :
    let Qj : ℝ := Q * (1 + eta) ^ j
    V ^ (2 * k) * volume.real
        {x ∈ Set.Icc (-T) T |
          V ≤ ‖harmonicPrimeBlockPoly (geomBlock P Q (1 + eta) j)
            (-x / (2 * Real.pi))‖} ≤
      2 * ((T + 4 * ((N ^ k : ℕ) : ℝ) *
              (1 + Real.log ((N ^ k : ℕ) : ℝ))) *
        ((k : ℝ) ^ k * ((Qj * eta + 1) / Qj ^ 2) ^ k)) := by
  dsimp only
  let Qj : ℝ := Q * (1 + eta) ^ j
  have hQj : 0 < Qj := by
    dsimp only [Qj]
    positivity
  have hB : geomBlock P Q (1 + eta) j ⊆ Finset.Icc 1 N :=
    (geomBlock_subset P Q (1 + eta) j).trans hP
  have hBprime : ∀ p ∈ geomBlock P Q (1 + eta) j, p.Prime := by
    intro p hp
    exact hPprime p (geomBlock_subset P Q (1 + eta) j hp)
  have hlower : ∀ p ∈ geomBlock P Q (1 + eta) j, Qj < (p : ℝ) := by
    intro p hp
    exact (Finset.mem_filter.1 hp).2.1
  have hbase := volume_harmonicPrimeBlock_largeValues_pow_le
    k N hk hB hBprime hQj hlower hT hV
  refine hbase.trans ?_
  have hcard := card_geomBlock_le P hQ heta j
  dsimp only [Qj]
  gcongr

/-- A prime interval `(a, X]` has at most its literal integer width many elements. -/
theorem card_primesRange_le_sub (a X : ℕ) :
    (primesRange a X).card ≤ X - a := by
  classical
  have hsub : primesRange a X ⊆ Finset.Ioc a X := by
    intro p hp
    exact Finset.mem_Ioc.2 ⟨(mem_primesRange.1 hp).2.1, (mem_primesRange.1 hp).2.2⟩
  exact (Finset.card_le_card hsub).trans_eq (by simp)

/-- Sixth-moment estimate for the actual complete prime interval selected in Menon's Case II. -/
theorem volume_harmonicPrimesRange_largeValues_sixth_le
    {a X : ℕ} {T V : ℝ} (ha : 0 < a) (hX : 1 ≤ X) (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ 6 * volume.real
        {x ∈ Set.Icc (-T) T |
          V ≤ ‖harmonicPrimeBlockPoly (primesRange a X)
            (-x / (2 * Real.pi))‖} ≤
      2 * ((T + 4 * ((X ^ 3 : ℕ) : ℝ) *
              (1 + Real.log ((X ^ 3 : ℕ) : ℝ))) *
        (27 * (((X - a : ℕ) : ℝ) / (a : ℝ) ^ 2) ^ 3)) := by
  have hB : primesRange a X ⊆ Finset.Icc 1 X := by
    intro p hp
    have hmem := mem_primesRange.1 hp
    exact Finset.mem_Icc.2 ⟨hmem.1.one_le, hmem.2.2⟩
  have hBprime : ∀ p ∈ primesRange a X, p.Prime := by
    intro p hp
    exact (mem_primesRange.1 hp).1
  have hlower : ∀ p ∈ primesRange a X, (a : ℝ) < (p : ℝ) := by
    intro p hp
    exact_mod_cast (mem_primesRange.1 hp).2.1
  have hbase := volume_harmonicPrimeBlock_largeValues_pow_le
    3 X (by norm_num) hB hBprime (by exact_mod_cast ha) hlower hT hV
  norm_num only [Nat.cast_ofNat, mul_eq_mul_left_iff, OfNat.ofNat] at hbase ⊢
  refine hbase.trans ?_
  have hcard : ((primesRange a X).card : ℝ) ≤ ((X - a : ℕ) : ℝ) := by
    exact_mod_cast card_primesRange_le_sub a X
  gcongr

/-- Eighth-moment form.  This spare moment lets the narrow block width absorb the harmless
logarithm in the mean-value factor using only `log X ≤ X`. -/
theorem volume_harmonicPrimesRange_largeValues_eighth_le
    {a X : ℕ} {T V : ℝ} (ha : 0 < a) (hX : 1 ≤ X) (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ 8 * volume.real
        {x ∈ Set.Icc (-T) T |
          V ≤ ‖harmonicPrimeBlockPoly (primesRange a X)
            (-x / (2 * Real.pi))‖} ≤
      2 * ((T + 4 * ((X ^ 4 : ℕ) : ℝ) *
              (1 + Real.log ((X ^ 4 : ℕ) : ℝ))) *
        (256 * (((X - a : ℕ) : ℝ) / (a : ℝ) ^ 2) ^ 4)) := by
  have hB : primesRange a X ⊆ Finset.Icc 1 X := by
    intro p hp
    have hmem := mem_primesRange.1 hp
    exact Finset.mem_Icc.2 ⟨hmem.1.one_le, hmem.2.2⟩
  have hBprime : ∀ p ∈ primesRange a X, p.Prime := by
    intro p hp
    exact (mem_primesRange.1 hp).1
  have hlower : ∀ p ∈ primesRange a X, (a : ℝ) < (p : ℝ) := by
    intro p hp
    exact_mod_cast (mem_primesRange.1 hp).2.1
  have hbase := volume_harmonicPrimeBlock_largeValues_pow_le
    4 X (by norm_num) hB hBprime (by exact_mod_cast ha) hlower hT hV
  norm_num only [Nat.cast_ofNat, mul_eq_mul_left_iff, OfNat.ofNat] at hbase ⊢
  refine hbase.trans ?_
  have hcard : ((primesRange a X).card : ℝ) ≤ ((X - a : ℕ) : ℝ) := by
    exact_mod_cast card_primesRange_le_sub a X
  gcongr

end

end RHTower.Sieve
