import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSieveClassesHaveExactPrimeGrams
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSievedLogarithmHasTheSameQuadraticDivergence
import GaloisForLFunctions.ArithmeticIntersectionTheory.ThePrimeKernelIsASumOfTransverseTowers

/-!
# The tower finite part of a finite prime sieve

The actual class Gram has one diagonal polar counterterm per supported order.
After removing it, the normalized diagonal is the shared sieve Euler constant;
the off-diagonal entries are the original prime kernel on the supported orders.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.HTGeometry
  GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

/-- Prime divisors of a supported order belong to the sieve. -/
theorem SieveSupported.prime_dvd_mem {Q : Finset Nat.Primes} {d : ℕ}
    (hd : SieveSupported Q d) {p : Nat.Primes} (hpd : (p : ℕ) ∣ d) : p ∈ Q := by
  obtain ⟨r, hr⟩ := hd
  have hpQ : (p : ℕ) ∣ sievePrimorial Q := p.2.dvd_of_dvd_pow (hpd.trans hr)
  by_contra hp
  exact (p.2.coprime_iff_not_dvd.mp (coprime_sievePrimorial hp)) hpQ

/-- On supported orders the transverse-tower decomposition uses exactly the
primes of the sieve. -/
theorem weilPrimeKernel_sieve_sum {Q : Finset Nat.Primes} {d e : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e) :
    weilPrimeKernel d e =
      ∑ p ∈ Q, ArithmeticIntersectionTheory.ladderKernel (p : ℕ) d e := by
  classical
  have hsub : (d * e).primeFactors ⊆ Q.image (fun p : Nat.Primes => (p : ℕ)) := by
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    exact mem_image.mpr ⟨⟨p, hp'.1⟩, (hd.mul he).prime_dvd_mem hp'.2.1, rfl⟩
  rw [ArithmeticIntersectionTheory.weilPrimeKernel_eq_sum_ladderKernel hd.pos.ne' he.pos.ne']
  calc
    (∑ p ∈ (d * e).primeFactors, ArithmeticIntersectionTheory.ladderKernel p d e) =
        ∑ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)),
          ArithmeticIntersectionTheory.ladderKernel p d e := by
      exact sum_subset hsub fun p _ hp =>
        ArithmeticIntersectionTheory.ladderKernel_eq_zero_of_not_mem hd.pos.ne' he.pos.ne' hp
    _ = _ := sum_image (fun a _ b _ h => Subtype.ext h)

/-- The complete affine harmonic law of a supported-order class. -/
theorem tendsto_sieveClassMass_sub (Q : Finset Nat.Primes) {d : ℕ} (hd : 0 < d) :
    Tendsto (fun M : ℕ => sieveClassMass Q d M -
      sieveClassDensity Q d * (Real.log M - Real.log d + sieveEuler Q)) atTop (𝓝 0) := by
  have hH := (tendsto_sievedHarmonic_sub_sieveEuler Q).comp (tendsto_natDiv_atTop hd)
  have hlog := (tendsto_log_natDiv_sub_log hd).const_mul (sieveDensity Q)
  have h := ((hH.add hlog).div_const (d : ℝ)).sub_const
    ((sieveDensity Q * sieveEuler Q + sieveDensity Q * -Real.log d) / d)
  rw [sub_self] at h
  refine h.congr fun M => ?_
  dsimp only [Function.comp, sieveClassMass, sieveClassDensity]
  ring

/-- An ordered mixed entry is exactly its prime-power logarithm times the
mass of the larger supported order. -/
theorem primeBilinear_sieveClassPole_cross_vonMangoldt
    {Q : Finset Nat.Primes} {d e : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e) (hde : d < e) (M : ℕ) :
    primeBilinear M (sieveClassPole Q d) (sieveClassPole Q e) =
      if d ∣ e then ArithmeticFunction.vonMangoldt (e / d) * sieveClassMass Q e M else 0 := by
  have hnot : ¬ e ∣ d := fun h => (Nat.le_of_dvd hd.pos h).not_gt hde
  have hkernel := poleWeighted_primeKernel_eq hd.pos he.pos
  rw [if_neg hnot, add_zero] at hkernel
  rw [primeBilinear_sieveClassPole_cross hd he hde, hkernel]
  split_ifs
  · dsimp only [sieveClassMass]
    ring
  · ring

/-- A nonzero mixed class entry changes the exponent of one prime in the sieve. -/
theorem exists_sieve_prime_power_of_cross_ne_zero
    {Q : Finset Nat.Primes} {d e M : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e) (hde : d < e)
    (hB : primeBilinear M (sieveClassPole Q d) (sieveClassPole Q e) ≠ 0) :
    ∃ p ∈ Q, ∃ r : ℕ, 0 < r ∧ e = d * (p : ℕ) ^ r := by
  rw [primeBilinear_sieveClassPole_cross_vonMangoldt hd he hde] at hB
  by_cases hdiv : d ∣ e
  · rw [if_pos hdiv] at hB
    have hΛ : ArithmeticFunction.vonMangoldt (e / d) ≠ 0 := by
      intro hzero
      exact hB (by rw [hzero, zero_mul])
    obtain ⟨p, r, hp, hr, hpow⟩ :=
      (isPrimePow_nat_iff _).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hpdiv : p ∣ e := (dvd_pow_self p hr.ne').trans
      (by rw [hpow]; exact Nat.div_dvd_of_dvd hdiv)
    refine ⟨⟨p, hp⟩, he.prime_dvd_mem hpdiv, r, hr, ?_⟩
    change e = d * p ^ r
    rw [hpow, Nat.mul_div_cancel' hdiv]
  · exact (hB (by rw [if_neg hdiv])).elim

/-- Decimating a finite-sieve harmonic sum does not change its logarithmic density. -/
theorem tendsto_sievedHarmonic_decimated_div_log (Q : Finset Nat.Primes)
    {d : ℕ} (hd : 0 < d) :
    Tendsto (fun M : ℕ => sievedHarmonic Q (M / d) / Real.log M) atTop
      (𝓝 (sieveDensity Q)) := by
  have htop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have herror := ((tendsto_sievedHarmonic_sub_sieveEuler Q).comp
    (tendsto_natDiv_atTop hd)).div_atTop htop
  have hmain := (tendsto_decimated_log_ratio hd).const_mul (sieveDensity Q)
  have h := hmain.add herror
  simp only [mul_one, add_zero] at h
  refine h.congr fun M => ?_
  dsimp only [Function.comp]
  ring

/-- The squared norm of each class has its expected logarithmic density. -/
theorem tendsto_sieveClassMass_div_log (Q : Finset Nat.Primes) {d : ℕ} (hd : 0 < d) :
    Tendsto (fun M : ℕ => sieveClassMass Q d M / Real.log M) atTop
      (𝓝 (sieveClassDensity Q d)) := by
  have h := (tendsto_sievedHarmonic_decimated_div_log Q hd).div_const (d : ℝ)
  refine h.congr fun M => ?_
  simp only [sieveClassMass]
  ring

/-- The diagonal finite part is minus twice the shared sieve Euler constant,
weighted by the density of its class. -/
theorem tendsto_sieveClassGram_self_finitePart
    {Q : Finset Nat.Primes} {d : ℕ} (hd : SieveSupported Q d) :
    Tendsto (fun M : ℕ =>
      (primeBilinear M (sieveClassPole Q d) (sieveClassPole Q d) -
        sieveClassMass Q d M ^ 2 / sieveClassDensity Q d) / Real.log M) atTop
      (𝓝 (-2 * sieveEuler Q * sieveClassDensity Q d)) := by
  have hL := tendsto_decimated_log_error
    (tendsto_sievedLogarithmicHarmonic_sub_div_log Q) hd.pos
  have hE := (tendsto_sievedHarmonic_sub_sieveEuler Q).comp (tendsto_natDiv_atTop hd.pos)
  have hS := (tendsto_sievedHarmonic_decimated_div_log Q hd.pos).add
    ((tendsto_decimated_log_ratio hd.pos).const_mul (sieveDensity Q))
  have h := (hL.div_const (d : ℝ)).sub
    ((hE.mul hS).div_const (sieveDensity Q * d))
  have hδ : sieveDensity Q ≠ 0 := (sieveDensity_pos Q).ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.pos.ne'
  have hvalue : (0 : ℝ) / d -
      (sieveDensity Q * sieveEuler Q * (sieveDensity Q + sieveDensity Q * 1)) /
        (sieveDensity Q * d) = -2 * sieveEuler Q * sieveClassDensity Q d := by
    rw [sieveClassDensity]
    field_simp
    ring
  rw [hvalue] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with M hM
  have hlog : Real.log M ≠ 0 := (Real.log_pos (by exact_mod_cast hM)).ne'
  rw [primeBilinear_sieveClassPole_self hd.pos]
  rw [show (∑ n ∈ sieveUnits Q (M / d), Real.log n / (n : ℝ)) =
    sievedLogarithmicHarmonic Q (M / d) from rfl]
  dsimp only [Function.comp, sieveClassMass, sieveClassDensity]
  field_simp
  ring

/-- Exact mixed Grams converge to the supported prime kernel, with the two
class density factors kept explicit. -/
theorem tendsto_sieveClassGram_cross
    {Q : Finset Nat.Primes} {d e : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e) (hde : d ≠ e) :
    Tendsto (fun M : ℕ =>
      primeBilinear M (sieveClassPole Q d) (sieveClassPole Q e) / Real.log M) atTop
      (𝓝 (poleVector d * poleVector e * weilPrimeKernel d e * sieveDensity Q)) := by
  rcases lt_or_gt_of_ne hde with hlt | hgt
  · have h := (tendsto_sievedHarmonic_decimated_div_log Q he.pos).const_mul
      (poleVector d * poleVector e * weilPrimeKernel d e)
    refine h.congr fun M => ?_
    rw [primeBilinear_sieveClassPole_cross hd he hlt]
    ring
  · have h := (tendsto_sievedHarmonic_decimated_div_log Q hd.pos).const_mul
      (poleVector d * poleVector e * weilPrimeKernel d e)
    refine h.congr fun M => ?_
    rw [primeBilinear_comm, primeBilinear_sieveClassPole_cross he hd hgt,
      weilPrimeKernel_comm e d]
    ring

/-- Every entry of the actual renormalized finite-sieve Gram has its tower limit. -/
theorem tendsto_sieveClassGram_finitePart
    {Q : Finset Nat.Primes} {d e : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e) :
    Tendsto (fun M : ℕ =>
      (primeBilinear M (sieveClassPole Q d) (sieveClassPole Q e) -
        if d = e then sieveClassMass Q d M ^ 2 / sieveClassDensity Q d else 0) /
          Real.log M) atTop
      (𝓝 ((if d = e then -2 * sieveEuler Q * sieveClassDensity Q d else 0) +
        poleVector d * poleVector e * weilPrimeKernel d e * sieveDensity Q)) := by
  by_cases hde : d = e
  · subst e
    simpa only [↓reduceIte, weilPrimeKernel_self, mul_zero, zero_mul, add_zero] using
      tendsto_sieveClassGram_self_finitePart hd
  · simpa only [if_neg hde, sub_zero, zero_add] using
      tendsto_sieveClassGram_cross hd he hde

/-- Density normalization is the common sieve density times the pole weights. -/
theorem sqrt_sieveClassDensity_mul (Q : Finset Nat.Primes) (d e : ℕ) :
    Real.sqrt (sieveClassDensity Q d) * Real.sqrt (sieveClassDensity Q e) =
      sieveDensity Q * poleVector d * poleVector e := by
  have hs : ∀ n : ℕ, Real.sqrt (sieveClassDensity Q n) =
      Real.sqrt (sieveDensity Q) * poleVector n := by
    intro n
    have hden : sieveClassDensity Q n = sieveDensity Q * poleVector n ^ 2 := by
      rw [sieveClassDensity, poleVector_sq]
      ring
    rw [hden, Real.sqrt_mul (sieveDensity_pos Q).le,
      Real.sqrt_sq (by unfold poleVector; positivity)]
  rw [hs, hs]
  calc Real.sqrt (sieveDensity Q) * poleVector d *
      (Real.sqrt (sieveDensity Q) * poleVector e) =
        (Real.sqrt (sieveDensity Q) * Real.sqrt (sieveDensity Q)) *
          poleVector d * poleVector e := by ring
    _ = _ := by rw [Real.mul_self_sqrt (sieveDensity_pos Q).le]

/-- In density-normalized coordinates the finite matrix is the prime kernel
minus twice the shared sieve Euler constant on the diagonal. -/
theorem tendsto_normalizedSieveClassGram_finitePart
    {Q : Finset Nat.Primes} {d e : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e) :
    Tendsto (fun M : ℕ =>
      (primeBilinear M (sieveClassPole Q d) (sieveClassPole Q e) -
        if d = e then sieveClassMass Q d M ^ 2 / sieveClassDensity Q d else 0) /
          (Real.sqrt (sieveClassDensity Q d) * Real.sqrt (sieveClassDensity Q e) * Real.log M))
      atTop (𝓝 ((if d = e then -2 * sieveEuler Q else 0) + weilPrimeKernel d e)) := by
  have h := (tendsto_sieveClassGram_finitePart hd he).div_const
    (Real.sqrt (sieveClassDensity Q d) * Real.sqrt (sieveClassDensity Q e))
  have hnorm : Real.sqrt (sieveClassDensity Q d) * Real.sqrt (sieveClassDensity Q e) ≠ 0 :=
    mul_ne_zero (Real.sqrt_pos.mpr (sieveClassDensity_pos hd)).ne'
      (Real.sqrt_pos.mpr (sieveClassDensity_pos he)).ne'
  have hvalue :
      ((if d = e then -2 * sieveEuler Q * sieveClassDensity Q d else 0) +
        poleVector d * poleVector e * weilPrimeKernel d e * sieveDensity Q) /
        (Real.sqrt (sieveClassDensity Q d) * Real.sqrt (sieveClassDensity Q e)) =
          (if d = e then -2 * sieveEuler Q else 0) + weilPrimeKernel d e := by
    by_cases hde : d = e
    · subst e
      simp only [↓reduceIte, weilPrimeKernel_self, mul_zero, zero_mul, add_zero]
      rw [Real.mul_self_sqrt (sieveClassDensity_pos hd).le]
      exact mul_div_cancel_right₀ _ (sieveClassDensity_pos hd).ne'
    · simp only [if_neg hde, zero_add]
      have hnum : poleVector d * poleVector e * weilPrimeKernel d e * sieveDensity Q =
          weilPrimeKernel d e *
            (Real.sqrt (sieveClassDensity Q d) * Real.sqrt (sieveClassDensity Q e)) := by
        rw [sqrt_sieveClassDensity_mul]
        ring
      rw [hnum, mul_div_cancel_right₀ _ hnorm]
  rw [hvalue] at h
  refine h.congr fun M => ?_
  ring

/-- The pole functional restricted to one supported-order class. -/
def sieveClassPolar (Q : Finset Nat.Primes) (d M : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 M, x n * sieveClassPole Q d n

/-- The tensor polar counterterm on a finite collection of classes. -/
def sieveTensorCounterterm {ι : Type*} [Fintype ι]
    (Q : Finset Nat.Primes) (d : ι → ℕ) (M : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i, sieveClassPolar Q (d i) M x ^ 2 / sieveClassDensity Q (d i)

/-- A signed profile in class coordinates normalized by their natural densities. -/
def normalizedSieveProfile {ι : Type*} [Fintype ι]
    (Q : Finset Nat.Primes) (d : ι → ℕ) (b : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i, (b i / Real.sqrt (sieveClassDensity Q (d i))) * sieveClassPole Q (d i) n

theorem sieveClassPolar_classPole {Q : Finset Nat.Primes} {d e : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e) (M : ℕ) :
    sieveClassPolar Q d M (sieveClassPole Q e) =
      if d = e then sieveClassMass Q d M else 0 := by
  by_cases hde : d = e
  · subst e
    rw [if_pos rfl, sieveClassPolar, sieveClassMass_eq_sum hd.pos]
    exact sum_congr rfl fun n _ => by ring
  · rw [if_neg hde, sieveClassPolar]
    exact sum_eq_zero fun n _ => sieveClassPole_mul_eq_zero he hd (Ne.symm hde) n

theorem sieveClassPolar_fintype_sum {ι : Type*} [Fintype ι]
    (Q : Finset Nat.Primes) (d M : ℕ) (c : ι → ℝ) (x : ι → ℕ → ℝ) :
    sieveClassPolar Q d M (fun n => ∑ i, c i * x i n) =
      ∑ i, c i * sieveClassPolar Q d M (x i) := by
  unfold sieveClassPolar
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun n _ => by ring

/-- Disjoint classes make the polar coordinates exactly the weighted class masses. -/
theorem sieveClassPolar_normalizedSieveProfile {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → ℕ}
    (hd : ∀ i, SieveSupported Q (d i)) (hinj : Function.Injective d)
    (b : ι → ℝ) (M : ℕ) (i : ι) :
    sieveClassPolar Q (d i) M (normalizedSieveProfile Q d b) =
      b i * sieveClassMass Q (d i) M / Real.sqrt (sieveClassDensity Q (d i)) := by
  classical
  change sieveClassPolar Q (d i) M (fun n =>
    ∑ j, (b j / Real.sqrt (sieveClassDensity Q (d j))) * sieveClassPole Q (d j) n) = _
  rw [sieveClassPolar_fintype_sum]
  have hentry : ∀ j, sieveClassPolar Q (d i) M (sieveClassPole Q (d j)) =
      if j = i then sieveClassMass Q (d i) M else 0 := by
    intro j
    rw [sieveClassPolar_classPole (hd i) (hd j)]
    by_cases hji : j = i
    · subst j
      simp
    · rw [if_neg (fun h => hji (hinj h).symm), if_neg hji]
  simp only [hentry, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
  ring

theorem sieveTensorCounterterm_normalizedSieveProfile {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → ℕ}
    (hd : ∀ i, SieveSupported Q (d i)) (hinj : Function.Injective d)
    (b : ι → ℝ) (M : ℕ) :
    sieveTensorCounterterm Q d M (normalizedSieveProfile Q d b) =
      ∑ i, (b i * sieveClassMass Q (d i) M / sieveClassDensity Q (d i)) ^ 2 := by
  unfold sieveTensorCounterterm
  refine sum_congr rfl fun i _ => ?_
  rw [sieveClassPolar_normalizedSieveProfile hd hinj, div_pow,
    Real.sq_sqrt (sieveClassDensity_pos (hd i)).le]
  ring

/-- The actual finite-sieve prime form, with its actual tensor polar counterterm,
converges on every fixed signed finite class profile to the tower matrix with one
shared Euler constant. -/
theorem tendsto_sieveProfile_finitePart {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → ℕ}
    (hd : ∀ i, SieveSupported Q (d i)) (hinj : Function.Injective d) (b : ι → ℝ) :
    Tendsto (fun M : ℕ =>
      (primeBilinear M (normalizedSieveProfile Q d b) (normalizedSieveProfile Q d b) -
        sieveTensorCounterterm Q d M (normalizedSieveProfile Q d b)) / Real.log M)
      atTop (𝓝 (-2 * sieveEuler Q * ∑ i, b i ^ 2 +
        ∑ i, ∑ j, b i * b j * weilPrimeKernel (d i) (d j))) := by
  classical
  have h := tendsto_finsetSum univ fun i _ => tendsto_finsetSum univ fun j _ =>
    (tendsto_normalizedSieveClassGram_finitePart (hd i) (hd j)).const_mul (b i * b j)
  have hvalue :
      (∑ i, ∑ j, b i * b j *
        ((if d i = d j then -2 * sieveEuler Q else 0) + weilPrimeKernel (d i) (d j))) =
      -2 * sieveEuler Q * ∑ i, b i ^ 2 +
        ∑ i, ∑ j, b i * b j * weilPrimeKernel (d i) (d j) := by
    simp_rw [mul_add, sum_add_distrib]
    congr 1
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have hids : ∀ j, (d i = d j) ↔ j = i := fun j =>
      ⟨fun h => (hinj h).symm, fun h => by rw [h]⟩
    simp only [hids, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
    ring
  rw [hvalue] at h
  refine h.congr fun M => ?_
  let c : ι → ℝ := fun i => b i / Real.sqrt (sieveClassDensity Q (d i))
  let A : ι → ι → ℝ := fun i j =>
    if d i = d j then sieveClassMass Q (d i) M ^ 2 / sieveClassDensity Q (d i) else 0
  have hbil :
      primeBilinear M (normalizedSieveProfile Q d b) (normalizedSieveProfile Q d b) =
        ∑ i, ∑ j, c i * c j * primeBilinear M (sieveClassPole Q (d i)) (sieveClassPole Q (d j)) := by
    have hlinear : ∀ y, primeBilinear M (normalizedSieveProfile Q d b) y =
        ∑ i, c i * primeBilinear M (sieveClassPole Q (d i)) y := fun y =>
      primeBilinear_fintype_sum_left M c (fun i => sieveClassPole Q (d i)) y
    rw [hlinear]
    refine sum_congr rfl fun i _ => ?_
    rw [primeBilinear_comm, hlinear, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [primeBilinear_comm]
    dsimp only [c]
    ring
  have hcounter :
      (∑ i, ∑ j, b i * b j * (A i j /
        (Real.sqrt (sieveClassDensity Q (d i)) * Real.sqrt (sieveClassDensity Q (d j))))) =
        sieveTensorCounterterm Q d M (normalizedSieveProfile Q d b) := by
    rw [sieveTensorCounterterm_normalizedSieveProfile hd hinj]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single i]
    · dsimp only [A]
      rw [if_pos rfl, Real.mul_self_sqrt (sieveClassDensity_pos (hd i)).le]
      ring
    · intro j _ hji
      dsimp only [A]
      rw [if_neg (fun h => hji (hinj h).symm), zero_div, mul_zero]
    · simp
  calc
    (∑ i, ∑ j, b i * b j *
        ((primeBilinear M (sieveClassPole Q (d i)) (sieveClassPole Q (d j)) - A i j) /
          (Real.sqrt (sieveClassDensity Q (d i)) *
            Real.sqrt (sieveClassDensity Q (d j)) * Real.log M))) =
      ((∑ i, ∑ j, c i * c j * primeBilinear M (sieveClassPole Q (d i)) (sieveClassPole Q (d j))) -
        ∑ i, ∑ j, b i * b j * (A i j /
          (Real.sqrt (sieveClassDensity Q (d i)) * Real.sqrt (sieveClassDensity Q (d j))))) /
            Real.log M := by
      rw [sub_div]
      simp_rw [sum_div]
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      dsimp only [c]
      ring
    _ = _ := by rw [← hbil, hcounter]

/-- The finite part is the sum of the local tower forms, with the sieve Euler
constant subtracted once for the whole profile. -/
theorem tendsto_sieveProfile_sum_towers {ι : Type*} [Fintype ι]
    {Q : Finset Nat.Primes} {d : ι → ℕ}
    (hd : ∀ i, SieveSupported Q (d i)) (hinj : Function.Injective d) (b : ι → ℝ) :
    Tendsto (fun M : ℕ =>
      (primeBilinear M (normalizedSieveProfile Q d b) (normalizedSieveProfile Q d b) -
        sieveTensorCounterterm Q d M (normalizedSieveProfile Q d b)) / Real.log M)
      atTop (𝓝 (-2 * sieveEuler Q * ∑ i, b i ^ 2 +
        ∑ p ∈ Q, ∑ i, ∑ j,
          b i * b j * ArithmeticIntersectionTheory.ladderKernel (p : ℕ) (d i) (d j))) := by
  have hsum : (∑ i, ∑ j, b i * b j * weilPrimeKernel (d i) (d j)) =
      ∑ p ∈ Q, ∑ i, ∑ j,
        b i * b j * ArithmeticIntersectionTheory.ladderKernel (p : ℕ) (d i) (d j) := by
    simp_rw [weilPrimeKernel_sieve_sum (hd _) (hd _), mul_sum]
    calc
      (∑ i, ∑ j, ∑ p ∈ Q,
        b i * b j * ArithmeticIntersectionTheory.ladderKernel (p : ℕ) (d i) (d j)) =
        ∑ i, ∑ p ∈ Q, ∑ j,
          b i * b j * ArithmeticIntersectionTheory.ladderKernel (p : ℕ) (d i) (d j) :=
        sum_congr rfl fun i _ => sum_comm
      _ = _ := sum_comm
  simpa only [hsum] using tendsto_sieveProfile_finitePart hd hinj b

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
