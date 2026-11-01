import GaloisForLFunctions.RHTower.MobiusMertensLittlewood
import GaloisForLFunctions.RHTower.FareyDiscrepancyOmega
import GaloisForLFunctions.RHTower.MertensSquareRootOmega

/-!
# The nerve of the star cover

The stars of the primes `p ≤ N` (the multiples of `p` in `[1, N]`) cover `[2, N]`. A set `S` of
primes has a common star vertex iff `∏_{p ∈ S} p ≤ N` (`exists_common_star_iff`): the common
multiples of `S` are the multiples of its product. The **nerve** of the cover is therefore the
simplicial complex of sets of primes with product `≤ N`, i.e. the squarefree integers `≤ N`
(`squarefreeNerve`). Its faces are exactly the stars of squarefree `n`, which are copies of the
lower horizons `⌊N/n⌋` (`StarsAreLowerHorizons`): the nerve indexes the Čech/inclusion–exclusion
structure by which any local-to-global argument over stars must glue.

* **Euler characteristic** (`nerveEulerChar_eq_mertens`): `Σ_{faces} (−1)^{|S|} = M(N)`, so the
  reduced Euler characteristic of the nerve is `−M(N)`, minus the Mertens function.
* **RH is a growth bound on the topology of the nerve** (`riemannHypothesis_iff_nerveEulerChar`):
  RH holds iff `|χ̃| = O(N^{1/2+δ})` for every `δ > 0` (Littlewood).
* **The nerve is unconditionally large** (`nerveEulerChar_omega_pm_sqrt`): `χ̃` exceeds `c√N` and
  falls below `−c√N` for arbitrarily large `N`.

So the topology of the star cover carries exactly the square-root precision count: Euler
characteristics are counts, and the count wall reappears as a bound on Betti numbers. A
Hodge-theoretic gluing over this nerve is the quadratic refinement of a statement that is
itself RH at the level of Euler characteristics.
-/

noncomputable section

open Finset Filter ArithmeticFunction

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-- The **nerve of the star cover**: sets of primes `≤ N` with product `≤ N`. -/
def squarefreeNerve (N : ℕ) : Finset (Finset ℕ) :=
  ((range (N + 1)).filter Nat.Prime).powerset.filter fun S => ∏ p ∈ S, p ≤ N

theorem mem_squarefreeNerve {N : ℕ} {S : Finset ℕ} :
    S ∈ squarefreeNerve N ↔ (∀ p ∈ S, p.Prime) ∧ ∏ p ∈ S, p ≤ N := by
  simp only [squarefreeNerve, mem_filter, mem_powerset]
  constructor
  · rintro ⟨hS, hprod⟩
    exact ⟨fun p hp => (mem_filter.mp (hS hp)).2, hprod⟩
  · rintro ⟨hp, hprod⟩
    refine ⟨fun p hpS => mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ?_), hp p hpS⟩, hprod⟩
    exact (Nat.le_of_dvd (Finset.prod_pos fun q hq => (hp q hq).pos) (dvd_prod_of_mem _ hpS)).trans
      hprod

/-- **The nerve is the intersection pattern of the stars**: a set of primes has a common vertex in
`[1, N]` iff its product is `≤ N`. -/
theorem exists_common_star_iff {N : ℕ} {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    (∃ n ∈ Icc 1 N, ∀ p ∈ S, p ∣ n) ↔ ∏ p ∈ S, p ≤ N := by
  constructor
  · rintro ⟨n, hn, hdvd⟩
    have hprod : (∏ p ∈ S, p) ∣ n :=
      Finset.prod_primes_dvd n (fun p hp => (hS p hp).prime) hdvd
    exact (Nat.le_of_dvd (mem_Icc.mp hn).1 hprod).trans (mem_Icc.mp hn).2
  · intro h
    exact ⟨∏ p ∈ S, p, mem_Icc.mpr ⟨Finset.prod_pos fun p hp => (hS p hp).pos, h⟩,
      fun p hp => dvd_prod_of_mem _ hp⟩

/-- The signed face count `Σ_{S} (−1)^{|S|}` of the nerve (the empty face included); the reduced
Euler characteristic is its negative. -/
def nerveEulerChar (N : ℕ) : ℤ := ∑ S ∈ squarefreeNerve N, (-1) ^ S.card

/-- `μ` of a product of distinct primes is `(−1)^{#primes}`. -/
theorem moebius_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ArithmeticFunction.moebius (∏ p ∈ S, p) = (-1) ^ S.card := by
  rw [isMultiplicative_moebius.map_prod_of_prime S hS,
    prod_congr rfl fun p hp => moebius_apply_prime (hS p hp), prod_const]

/-- **The Euler characteristic of the nerve is the Mertens function**:
`Σ_{S ∈ nerve} (−1)^{|S|} = Σ_{n ≤ N} μ(n)`. -/
theorem nerveEulerChar_eq_mertens (N : ℕ) :
    nerveEulerChar N = ∑ n ∈ Icc 1 N, ArithmeticFunction.moebius n := by
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) (squarefreeNerve N) := by
    intro S hS T hT hST
    have h1 := Nat.primeFactors_prod (mem_squarefreeNerve.mp hS).1
    have h2 := Nat.primeFactors_prod (mem_squarefreeNerve.mp hT).1
    simp only at hST
    rw [← h1, ← h2, hST]
  have hsub : (squarefreeNerve N).image (fun S => ∏ p ∈ S, p) ⊆ Icc 1 N := by
    intro n hn
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hn
    obtain ⟨hp, hle⟩ := mem_squarefreeNerve.mp hS
    exact mem_Icc.mpr ⟨Finset.prod_pos fun q hq => (hp q hq).pos, hle⟩
  rw [nerveEulerChar, ← sum_subset hsub, sum_image hinj]
  · exact sum_congr rfl fun S hS => (moebius_prod_primes (mem_squarefreeNerve.mp hS).1).symm
  · intro n hn hnot
    by_contra hμ
    have hsq : Squarefree n := by
      by_contra h
      exact hμ (moebius_eq_zero_of_not_squarefree h)
    apply hnot
    refine mem_image.mpr ⟨n.primeFactors, mem_squarefreeNerve.mpr
      ⟨fun p hp => Nat.prime_of_mem_primeFactors hp, ?_⟩, Nat.prod_primeFactors_of_squarefree hsq⟩
    rw [Nat.prod_primeFactors_of_squarefree hsq]
    exact (mem_Icc.mp hn).2

theorem abs_nerveEulerChar_eq (N : ℕ) :
    |(nerveEulerChar N : ℝ)| = ‖RHTower.mobiusMertensPartialSum N‖ := by
  rw [RHTower.norm_mobiusMertensPartialSum_eq_abs_mertensFunctionReal,
    RHTower.mertensFunctionReal, Nat.floor_natCast, nerveEulerChar_eq_mertens]
  push_cast
  rfl

/-- **RH is a growth bound on the Euler characteristic of the nerve.** -/
theorem riemannHypothesis_iff_nerveEulerChar :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |(nerveEulerChar N : ℝ)| ≤ C * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := by
  rw [← RHTower.mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis,
    RHTower.MobiusMertensAllStrictHalfPowerBound]
  simp only [abs_nerveEulerChar_eq]

/-- **The nerve is unconditionally large**: its Euler characteristic exceeds `c√N` and falls below
`−c√N` for arbitrarily large `N`. -/
theorem nerveEulerChar_omega_pm_sqrt :
    ∃ c : ℝ, 0 < c ∧ (∀ N₀ : ℕ, ∃ N ≥ N₀, c * Real.sqrt N < nerveEulerChar N) ∧
      ∀ N₀ : ℕ, ∃ N ≥ N₀, (nerveEulerChar N : ℝ) < -(c * Real.sqrt N) := by
  obtain ⟨c, hc, hplus, hminus⟩ := RHTower.mertens_omega_pm_sqrt
  have hM : ∀ x : ℝ, RHTower.mertensFunctionReal x = nerveEulerChar ⌊x⌋₊ := fun x => by
    rw [RHTower.mertensFunctionReal, nerveEulerChar_eq_mertens]
    push_cast
    rfl
  refine ⟨c, hc, fun N₀ => ?_, fun N₀ => ?_⟩
  · obtain ⟨x, hx, hlt⟩ := (hplus.and_eventually (eventually_ge_atTop ((N₀ : ℝ) + 1))).exists
    refine ⟨⌊x⌋₊, Nat.le_floor (by linarith), ?_⟩
    rw [hM] at hx
    have hx0 : 0 ≤ x := by have : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _; linarith
    have : Real.sqrt ⌊x⌋₊ ≤ Real.sqrt x := Real.sqrt_le_sqrt (Nat.floor_le hx0)
    nlinarith
  · obtain ⟨x, hx, hlt⟩ := (hminus.and_eventually (eventually_ge_atTop ((N₀ : ℝ) + 1))).exists
    refine ⟨⌊x⌋₊, Nat.le_floor (by linarith), ?_⟩
    rw [hM] at hx
    have hx0 : 0 ≤ x := by have : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _; linarith
    have : Real.sqrt ⌊x⌋₊ ≤ Real.sqrt x := Real.sqrt_le_sqrt (Nat.floor_le hx0)
    nlinarith

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
