import GaloisForLFunctions.RHTower.DeningerFloquetLatticeMeasure
import GaloisForLFunctions.RHTower.DeningerFloquetMeasureEnergy
import GaloisForLFunctions.HTGeometry.PhotonicTimeCrystalDynamicChirality
import Mathlib.SetTheory.Cardinal.Pigeonhole

/-!
# Prime-indexed photonic clocks: exact lattice realization and single-clock no-go

## PTR proof-chain position

PTR needs a physical Maxwell/time-crystal source whose transfer has the arithmetic
return response before the existing parabolic-return receiver can imply RH.  A
single globally periodic Floquet source, or a finite disjoint array of such
clocks, is a tempting but false source class: it cannot contain first nonzero
nodes from every prime Floquet lattice.  This file closes that subroute without
claiming that the remaining prime-indexed source is already a Maxwell
realization.

The positive survivor is exact.  The prime-indexed drive with angular frequency
`1 / log q` has its Floquet sidebands exactly at `m / log q`, the nodes of the
literal Deninger arithmetic Floquet measure.  Its full direct-sum sideband
measure is that literal arithmetic Floquet measure.  Thus any physical PTR
source must retain the prime-indexed infinite family or use a genuinely
cross-clock frequency module; a global clock or finite disjoint clock array
cannot be its source.

The no-go uses the corpus's unconditional rational independence of prime
logarithms through `deningerFloquetNode_eq_iff`.  It does not use RH, a
numerical experiment, or a target-fitted zero ordinate.
-/

namespace RHTower

open MeasureTheory
open GaloisForLFunctions.HTGeometry

/-- Prime-specific Floquet angular frequency of the arithmetic circle of length `log q`. -/
noncomputable def photonicPrimeClockRate (q : Nat.Primes) : ℝ :=
  (Real.log ((q : ℕ) : ℝ))⁻¹

theorem photonicPrimeClockRate_pos (q : Nat.Primes) :
    0 < photonicPrimeClockRate q := by
  exact inv_pos.mpr (deningerPrimeLog_pos q)

/-- Physical sideband of the `q`-clock at Floquet grade `m`. -/
noncomputable def photonicPrimeClockSideband (q : Nat.Primes) (m : ℤ) : ℝ :=
  floquetSidebandFrequency 0 (photonicPrimeClockRate q) m

/-- The literal prime-indexed Floquet source realizes every arithmetic lattice node. -/
theorem photonicPrimeClockSideband_eq_deningerFloquetNode
    (q : Nat.Primes) (m : ℤ) :
    photonicPrimeClockSideband q m = deningerFloquetNode (q : ℕ) m := by
  simp [photonicPrimeClockSideband, photonicPrimeClockRate,
    floquetSidebandFrequency, deningerFloquetNode, div_eq_mul_inv]

/-- Sideband counting measure of the literal prime-indexed Floquet clock. -/
noncomputable def photonicPrimeClockLattice (q : Nat.Primes) : Measure ℝ :=
  Measure.sum fun m : ℤ => Measure.dirac (photonicPrimeClockSideband q m)

/-- Weighted direct sum of all prime-indexed photonic sideband measures. -/
noncomputable def photonicPrimeClockMeasure : Measure ℝ :=
  Measure.sum fun q : Nat.Primes =>
    deningerFloquetWeight (q : ℕ) • photonicPrimeClockLattice q

/-- Each physical prime-clock lattice is exactly its arithmetic Deninger lattice. -/
theorem photonicPrimeClockLattice_eq_deningerFloquetLattice (q : Nat.Primes) :
    photonicPrimeClockLattice q = deningerFloquetLattice (q : ℕ) := by
  unfold photonicPrimeClockLattice deningerFloquetLattice
  congr 1
  funext m
  rw [photonicPrimeClockSideband_eq_deningerFloquetNode]

/-- The prime-indexed photonic source has exactly the literal arithmetic Floquet measure. -/
theorem photonicPrimeClockMeasure_eq_deningerFloquetMeasure :
    photonicPrimeClockMeasure = deningerFloquetMeasure := by
  unfold photonicPrimeClockMeasure deningerFloquetMeasure
  congr 1
  funext q
  rw [photonicPrimeClockLattice_eq_deningerFloquetLattice]

/-- Prime-indexed photonic sideband energy is the literal arithmetic Floquet energy. -/
theorem lintegral_photonicPrimeClockMeasure_sample_normSq (h : DeningerExpSchwartz) :
    ∫⁻ ξ, ENNReal.ofReal (‖deningerFloquetSample h ξ‖ ^ 2) ∂photonicPrimeClockMeasure
      = ENNReal.ofReal (deningerHalfDensityFloquetEnergy h) := by
  rw [photonicPrimeClockMeasure_eq_deningerFloquetMeasure]
  exact lintegral_deningerFloquetSample_normSq h

/-- A one-frequency drive contains the first nonzero node of a prime Floquet lattice. -/
def PhotonicSingleClockCarriesPrime (Ω : ℝ) (q : Nat.Primes) : Prop :=
  ∃ m : ℤ, m ≠ 0 ∧
    floquetSidebandFrequency 0 Ω m = deningerFloquetNode (q : ℕ) 1

/-- A single Floquet frequency cannot carry first nonzero nodes of two primes. -/
theorem photonicSingleClockCarriesPrime_unique
    {Ω : ℝ} {p q : Nat.Primes}
    (hp : PhotonicSingleClockCarriesPrime Ω p)
    (hq : PhotonicSingleClockCarriesPrime Ω q) : p = q := by
  rcases hp with ⟨m, hm, hpm⟩
  rcases hq with ⟨n, hn, hqn⟩
  have hpm' : (m : ℝ) * Ω = 1 / Real.log ((p : ℕ) : ℝ) := by
    simpa [floquetSidebandFrequency, deningerFloquetNode] using hpm
  have hqn' : (n : ℝ) * Ω = 1 / Real.log ((q : ℕ) : ℝ) := by
    simpa [floquetSidebandFrequency, deningerFloquetNode] using hqn
  have hpLog : Real.log ((p : ℕ) : ℝ) ≠ 0 := (deningerPrimeLog_pos p).ne'
  have hqLog : Real.log ((q : ℕ) : ℝ) ≠ 0 := (deningerPrimeLog_pos q).ne'
  have hΩ : Ω ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hpm'
    exact (one_div_ne_zero hpLog) hpm'.symm
  have hpUnit : (m : ℝ) * Ω * Real.log ((p : ℕ) : ℝ) = 1 := by
    rw [hpm']
    field_simp
  have hqUnit : (n : ℝ) * Ω * Real.log ((q : ℕ) : ℝ) = 1 := by
    rw [hqn']
    field_simp
  have hcross : (n : ℝ) * Real.log ((q : ℕ) : ℝ) =
      (m : ℝ) * Real.log ((p : ℕ) : ℝ) := by
    apply (mul_left_cancel₀ hΩ)
    calc
      Ω * ((n : ℝ) * Real.log ((q : ℕ) : ℝ)) =
          (n : ℝ) * Ω * Real.log ((q : ℕ) : ℝ) := by ring
      _ = 1 := hqUnit
      _ = (m : ℝ) * Ω * Real.log ((p : ℕ) : ℝ) := hpUnit.symm
      _ = Ω * ((m : ℝ) * Real.log ((p : ℕ) : ℝ)) := by ring
  have hnodes : deningerFloquetNode (p : ℕ) n =
      deningerFloquetNode (q : ℕ) m := by
    rw [deningerFloquetNode, deningerFloquetNode]
    field_simp
    linarith
  exact (deningerFloquetNode_eq_iff hnodes hn).1

/-- A global one-clock source cannot even seed all arithmetic prime lattices. -/
theorem not_photonicSingleClockCarries_two_distinct_primes
    (Ω : ℝ) {p q : Nat.Primes} (hpq : p ≠ q) :
    ¬ (PhotonicSingleClockCarriesPrime Ω p ∧
      PhotonicSingleClockCarriesPrime Ω q) := by
  rintro ⟨hp, hq⟩
  exact hpq (photonicSingleClockCarriesPrime_unique hp hq)

/-- A finite disjoint array carries a prime node if one component clock carries it. -/
def PhotonicFiniteClockCarriesPrime {ι : Type*} (clock : ι → ℝ)
    (q : Nat.Primes) : Prop :=
  ∃ i : ι, PhotonicSingleClockCarriesPrime (clock i) q

/-- No finite union of independent one-clock ladders carries first nodes of all primes. -/
theorem not_photonicFiniteClockCarries_all_prime_first_nodes
    {ι : Type*} [Fintype ι] (clock : ι → ℝ) :
    ¬ ∀ q : Nat.Primes, PhotonicFiniteClockCarriesPrime clock q := by
  classical
  intro h
  choose carrier hcarrier using h
  have hinfinite : (Set.univ : Set Nat.Primes).Infinite := Set.infinite_univ
  obtain ⟨p, -, q, -, hpq, hcollision⟩ :=
    Set.Infinite.exists_ne_map_eq_of_mapsTo hinfinite (by simp)
      (Set.finite_univ : (Set.univ : Set ι).Finite)
  apply hpq
  refine photonicSingleClockCarriesPrime_unique (Ω := clock (carrier q)) ?_ (hcarrier q)
  have hclock : clock (carrier p) = clock (carrier q) := congrArg clock hcollision
  rw [← hclock]
  exact hcarrier p

/-- The killed PTR source class: one global Floquet clock cannot realize all prime first nodes. -/
theorem not_exists_photonicSingleClockCarries_all_prime_first_nodes :
    ¬ ∃ Ω : ℝ, ∀ q : Nat.Primes, PhotonicSingleClockCarriesPrime Ω q := by
  rintro ⟨Ω, hΩ⟩
  let p : Nat.Primes := ⟨2, by norm_num⟩
  let q : Nat.Primes := ⟨3, by norm_num⟩
  have hpq : p ≠ q := by
    intro h
    have hval : (p : ℕ) = (q : ℕ) := congrArg Subtype.val h
    norm_num [p, q] at hval
  exact hpq (photonicSingleClockCarriesPrime_unique (hΩ p) (hΩ q))

end RHTower
