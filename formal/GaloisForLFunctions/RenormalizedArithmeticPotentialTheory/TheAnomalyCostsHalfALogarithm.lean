import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCovariantCountertermIsTheAnomaly
import GaloisForLFunctions.ArithmeticElectrostatics.TheTorsionCountertermIsLogarithmic
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheDifferentOfATorsionOrbit

/-!
# The anomaly costs half a logarithm

The torsion pairing keeps the self-intersection of every orbit on its diagonal,
`I(n, n)/φ(n) = c(n) = log n − Σ_{p ∣ n} log p/(p − 1)`; its Hecke variation is the anomaly cocycle
(AIT). Weil's prime sum drops it, and the result is covariant (`TheCovariantCountertermIsTheAnomaly`).
This file measures what the anomaly costs in counterterm.

* **The torsion pairing dominates Weil's kernel** (`totient_mul_le`, `poleVector_mul_kernel_le`):
  `φ(mt) ≤ t φ(m)`, so the normalized intersection `I(m, mt)/√(φ(m)φ(mt)) = Λ(t)√(φ(m)/φ(mt))` is at
  least `P(m, mt) = Λ(t)/√t`.
* **The torsion pairing on the pole vector** (`torsionPairing_torsionTest_ge`, `selfMass_torsionTest`):
  with charges `y_n = (n φ(n))^{−1/2}` (unit mass `1/n` per orbit),
  `Σ y_m y_n I(m, n) ≥ P_N(u) + Σ_{n ≤ N} c(n)/n` against the mass `H_N = Σ_{n ≤ N} 1/n`.
* **The self-intersection on average** (`sum_log_div_ge`, `sum_tameDifferent_div_le`):
  `Σ_{n ≤ N} log n/n ≥ ½ log²(N + 1) − 1` (telescoping `log²`), and the tame part averages to at most
  a constant times `H_N` (each prime `p` contributes `log p/(p(p − 1)) ≤ 4 p^{−3/2}`).
* **The torsion counterterm is at least `(3/2) log N − C`** (`torsionCounterterm_ge`): every `κ` that
  renormalizes the torsion pairing on the orders `≤ N` (AES `RenormalizesAt`) satisfies it.
* **The anomaly cost** (`anomaly_cost`): every torsion counterterm exceeds the covariant one
  `log N + log 4 + 4` by at least `½ log N − C`.

So the anomaly is not free: the self-intersection `c(n) ≈ log n`, the potential of the cocycle `β`,
raises the counterterm of the prime place from `log N + O(1)` (covariant, constant one) to at least
`(3/2) log N − O(1)`. Removing the diagonal — what Weil's prime sum does — is the anomaly
cancellation, and it saves at least half a logarithm. (The continuum model of the torsion pairing,
`𝟙 ⊗ 𝟙 + (multiplication by log n)` on `L²[0, log N]`, predicts the constant `e/(e − 1)`.)
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.ArithmeticIntersectionTheory

/-! ### Harmonic sums -/

/-- The harmonic sum `H_N = Σ_{n ≤ N} 1/n`, the mass of the pole vector. -/
def harmonicSum (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, 1 / (n : ℝ)

theorem harmonicSum_le (N : ℕ) : harmonicSum N ≤ 1 + Real.log N := by
  have h := harmonic_le_one_add_log N
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  simpa [harmonicSum, one_div] using h

theorem one_le_harmonicSum {N : ℕ} (hN : 1 ≤ N) : 1 ≤ harmonicSum N := by
  unfold harmonicSum
  calc (1 : ℝ) = 1 / ((1 : ℕ) : ℝ) := by norm_num
    _ ≤ ∑ n ∈ Icc 1 N, 1 / (n : ℝ) :=
        single_le_sum (f := fun n : ℕ => 1 / (n : ℝ)) (fun n _ => by positivity)
          (mem_Icc.mpr ⟨le_rfl, hN⟩)

theorem sum_poleVector_sq (N : ℕ) : ∑ n ∈ Icc 1 N, poleVector n ^ 2 = harmonicSum N := by
  simp only [poleVector_sq, harmonicSum]

/-! ### The torsion pairing dominates Weil's kernel -/

/-- `φ(mt) ≤ t φ(m)`. -/
theorem totient_mul_le (m : ℕ) : ∀ t : ℕ, Nat.totient (m * t) ≤ t * Nat.totient m := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases Nat.lt_or_ge t 2 with ht | ht
    · interval_cases t <;> simp
    · obtain ⟨p, hp, s, rfl⟩ := Nat.exists_prime_and_dvd (show t ≠ 1 by omega)
      have hs0 : 0 < s := Nat.pos_of_ne_zero fun h => by simp [h] at ht
      have hs : s < p * s := lt_mul_left hs0 hp.one_lt
      have h2 : Nat.totient (p * (m * s)) ≤ p * Nat.totient (m * s) := by
        by_cases hdvd : p ∣ m * s
        · rw [Nat.totient_mul_of_prime_of_dvd hp hdvd]
        · rw [Nat.totient_mul_of_prime_of_not_dvd hp hdvd]
          exact Nat.mul_le_mul_right _ (Nat.sub_le p 1)
      calc Nat.totient (m * (p * s)) = Nat.totient (p * (m * s)) := by ring_nf
        _ ≤ p * Nat.totient (m * s) := h2
        _ ≤ p * (s * Nat.totient m) := Nat.mul_le_mul_left p (ih s hs)
        _ = p * s * Nat.totient m := by ring

/-- `a/√(ab) = √(a/b)` for `a, b > 0`. -/
theorem div_sqrt_mul_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a / Real.sqrt (a * b) = Real.sqrt (a / b) := by
  rw [Real.sqrt_mul ha.le, Real.sqrt_div' _ hb.le]
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  field_simp
  rw [Real.sq_sqrt ha.le]

/-- **The normalized intersection dominates Weil's kernel on a Hecke pair**:
`1/√t ≤ φ(m)/√(φ(m)φ(mt))`. -/
theorem inv_sqrt_le_normalizedIntersection {m t : ℕ} (hm : 0 < m) (ht : 0 < t) :
    1 / Real.sqrt t ≤ (Nat.totient m : ℝ) / Real.sqrt ((Nat.totient m : ℝ) * Nat.totient (m * t)) := by
  have hφm : (0 : ℝ) < Nat.totient m := by exact_mod_cast Nat.totient_pos.mpr hm
  have hφmt : (0 : ℝ) < Nat.totient (m * t) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hm ht)
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  rw [div_sqrt_mul_eq hφm hφmt, ← Real.sqrt_one, ← Real.sqrt_div' _ ht'.le, Real.sqrt_one]
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_div_iff₀ ht' hφmt, one_mul]
  have := totient_mul_le m t
  exact_mod_cast (by linarith [show (Nat.totient (m * t) : ℝ) ≤ t * Nat.totient m by
    exact_mod_cast this] : (Nat.totient (m * t) : ℝ) ≤ Nat.totient m * t)

/-- The **torsion test charges** `y_n = (n φ(n))^{−1/2}`: the pole vector `u_n = n^{−1/2}` spread over
the `φ(n)` points of `O_n`. -/
def torsionTest (n : ℕ) : ℝ := 1 / Real.sqrt ((n : ℝ) * Nat.totient n)

theorem torsionTest_eq {n : ℕ} (hn : 0 < n) :
    torsionTest n = poleVector n * (1 / Real.sqrt (Nat.totient n)) := by
  rw [torsionTest, poleVector, Real.sqrt_mul (Nat.cast_nonneg n)]
  ring

theorem torsionTest_sq {n : ℕ} (hn : 0 < n) :
    torsionTest n ^ 2 = 1 / ((n : ℝ) * Nat.totient n) := by
  rw [torsionTest, div_pow, one_pow, Real.sq_sqrt (by positivity)]

/-- On a Hecke pair `n = mt` the torsion charges see at least Weil's kernel:
`u_m u_n P(m, n) ≤ y_m y_n I(m, n)`. -/
theorem poleVector_mul_kernel_le_of_dvd {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n)
    (hdvd : m ∣ n) :
    poleVector m * poleVector n * weilPrimeKernel m n ≤
      torsionTest m * torsionTest n * orbitIntersection m n := by
  obtain ⟨t, rfl⟩ := hdvd
  have ht : 0 < t := Nat.pos_of_ne_zero fun h => by simp [h] at hn
  have hnm : ¬ m * t ∣ m := fun h => hmn (Nat.dvd_antisymm (dvd_mul_right m t) h)
  rw [orbitIntersection_eq hm hn hmn, if_neg hnm, if_pos (dvd_mul_right m t),
    Nat.mul_div_cancel_left t hm, weilPrimeKernel, if_pos ⟨dvd_mul_right m t, hmn⟩,
    Nat.mul_div_cancel_left t hm, torsionTest_eq hm, torsionTest_eq hn]
  have hu : 0 ≤ poleVector m * poleVector (m * t) := by unfold poleVector; positivity
  have hΛ : 0 ≤ Λ t := vonMangoldt_nonneg
  have hφm : (0 : ℝ) < Nat.totient m := by exact_mod_cast Nat.totient_pos.mpr hm
  have hφn : (0 : ℝ) < Nat.totient (m * t) := by exact_mod_cast Nat.totient_pos.mpr hn
  have key := inv_sqrt_le_normalizedIntersection hm ht
  have hsq : (1 / Real.sqrt (Nat.totient m)) * (1 / Real.sqrt (Nat.totient (m * t))) *
      (Nat.totient m : ℝ) = (Nat.totient m : ℝ) /
        Real.sqrt ((Nat.totient m : ℝ) * Nat.totient (m * t)) := by
    rw [Real.sqrt_mul hφm.le]
    field_simp
  calc poleVector m * poleVector (m * t) * (Λ t / Real.sqrt t)
      = poleVector m * poleVector (m * t) * Λ t * (1 / Real.sqrt t) := by ring
    _ ≤ poleVector m * poleVector (m * t) * Λ t *
          ((Nat.totient m : ℝ) / Real.sqrt ((Nat.totient m : ℝ) * Nat.totient (m * t))) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg hu hΛ)
    _ = poleVector m * (1 / Real.sqrt (Nat.totient m)) *
          (poleVector (m * t) * (1 / Real.sqrt (Nat.totient (m * t)))) *
            ((Nat.totient m : ℝ) * Λ t) := by
        rw [← hsq]; ring

/-- Off the diagonal the torsion charges see at least Weil's kernel. -/
theorem poleVector_mul_kernel_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    poleVector m * poleVector n * weilPrimeKernel m n ≤
      torsionTest m * torsionTest n * orbitIntersection m n := by
  by_cases h1 : m ∣ n
  · exact poleVector_mul_kernel_le_of_dvd hm hn hmn h1
  · by_cases h2 : n ∣ m
    · have := poleVector_mul_kernel_le_of_dvd hn hm (Ne.symm hmn) h2
      rw [weilPrimeKernel_comm, orbitIntersection_comm]
      linarith [this]
    · rw [weilPrimeKernel, if_neg (fun h => h1 h.1), if_neg (fun h => h2 h.1),
        orbitIntersection_eq hm hn hmn, if_neg h2, if_neg h1]
      simp

/-- On the diagonal the torsion charges see the self-intersection per unit mass, `c(n)/n`. -/
theorem torsionTest_diag {n : ℕ} (hn : 0 < n) :
    torsionTest n * torsionTest n * orbitIntersection n n = selfIntersection n / n := by
  have hφ : (0 : ℝ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.mpr hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← sq, torsionTest_sq hn, selfIntersection]
  field_simp

/-- **The torsion pairing on the pole charges**: `Σ y_m y_n I(m, n) ≥ P_N(u) + Σ_{n ≤ N} c(n)/n`. -/
theorem torsionPairing_torsionTest_ge (N : ℕ) :
    atomicWeilForm N poleVector + ∑ n ∈ Icc 1 N, selfIntersection n / n ≤
      torsionPairing N torsionTest := by
  have hdiag : ∑ n ∈ Icc 1 N, selfIntersection n / n =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (if m = n then selfIntersection n / n else 0) := by
    refine sum_congr rfl fun m hm => ?_
    rw [sum_ite_eq]
    simp [hm]
  rw [hdiag, atomicWeilForm, ← sum_add_distrib, torsionPairing]
  refine sum_le_sum fun m hm => ?_
  rw [← sum_add_distrib]
  refine sum_le_sum fun n hn => ?_
  have hm0 := (mem_Icc.mp hm).1
  have hn0 := (mem_Icc.mp hn).1
  by_cases hmn : m = n
  · subst hmn
    rw [if_pos rfl, weilPrimeKernel_self, mul_zero, zero_add, torsionTest_diag hm0]
  · rw [if_neg hmn, add_zero]
    exact poleVector_mul_kernel_le hm0 hn0 hmn

/-- The torsion charges have mass `H_N`: `Σ φ(n) y_n² = Σ 1/n`. -/
theorem selfMass_torsionTest (N : ℕ) : selfMass N torsionTest = harmonicSum N := by
  unfold selfMass harmonicSum
  refine sum_congr rfl fun n hn => ?_
  have hn0 := (mem_Icc.mp hn).1
  have hφ : (0 : ℝ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.mpr hn0
  rw [torsionTest_sq hn0]
  field_simp

/-! ### The self-intersection on average -/

/-- One step of the telescope: `log²(n + 1) − log² n ≤ 2 log n/n + 1/n²`. -/
theorem log_sq_succ_sub_le {n : ℕ} (hn : 0 < n) :
    Real.log (n + 1) ^ 2 - Real.log n ^ 2 ≤ 2 * (Real.log n / n) + 1 / (n : ℝ) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hd : Real.log (n + 1) - Real.log n ≤ 1 / n := by
    rw [← Real.log_div (by positivity) hn'.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n + 1) / n by positivity)
    have h1 : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  have hd0 : 0 ≤ Real.log (n + 1) - Real.log n :=
    sub_nonneg.mpr (Real.log_le_log hn' (by linarith))
  have hfac : Real.log (n + 1) ^ 2 - Real.log n ^ 2 =
      (Real.log (n + 1) - Real.log n) * (Real.log (n + 1) - Real.log n + 2 * Real.log n) := by
    ring
  rw [hfac]
  have hb : 0 ≤ Real.log (n + 1) - Real.log n + 2 * Real.log n := by linarith
  calc (Real.log (n + 1) - Real.log n) * (Real.log (n + 1) - Real.log n + 2 * Real.log n)
      ≤ (1 / n) * (1 / n + 2 * Real.log n) := by
        apply mul_le_mul hd (by linarith) hb (by positivity)
    _ = 2 * (Real.log n / n) + 1 / (n : ℝ) ^ 2 := by field_simp; ring

/-- `Σ_{n ≤ N} 1/n² ≤ 2 − 1/N`. -/
theorem sum_inv_sq_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, 1 / (n : ℝ) ^ 2 ≤ 2 - 1 / N := by
  induction N with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · rw [sum_Icc_succ_top (by omega), Nat.cast_succ]
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have h := ih hk
      have : 1 / ((k : ℝ) + 1) ^ 2 ≤ 1 / k - 1 / (k + 1) := by
        rw [div_le_iff₀ (by positivity)]
        field_simp
        nlinarith
      linarith

/-- **The degree on average**: `Σ_{n ≤ N} log n/n ≥ ½ log²(N + 1) − 1`. -/
theorem sum_log_div_ge {N : ℕ} (hN : 1 ≤ N) :
    Real.log (N + 1) ^ 2 / 2 - 1 ≤ ∑ n ∈ Icc 1 N, Real.log n / n := by
  have htel : ∑ n ∈ Icc 1 N, (Real.log ((n : ℝ) + 1) ^ 2 - Real.log n ^ 2) =
      Real.log (N + 1) ^ 2 := by
    induction N with
    | zero => simp
    | succ k ih =>
      rw [sum_Icc_succ_top (by omega)]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [ih hk]
        push_cast
        ring
  have hsum := sum_le_sum fun n (hn : n ∈ Icc 1 N) => log_sq_succ_sub_le (mem_Icc.mp hn).1
  rw [htel, sum_add_distrib, ← mul_sum] at hsum
  have h2 := sum_inv_sq_le hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have : 0 ≤ 1 / (N : ℝ) := by positivity
  linarith

/-- `log p/(p(p − 1)) ≤ 4 (p^{3/2})^{−1}` for `p ≥ 2`. -/
theorem log_div_mul_le {p : ℕ} (hp : 2 ≤ p) :
    Real.log p / ((p : ℝ) - 1) / p ≤ 4 * ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog := RHTower.Mertens.log_le_rpow hp0 (show (0 : ℝ) < 1 / 2 by norm_num)
  have h32 : (p : ℝ) ^ ((3 : ℝ) / 2) = p * (p : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hp0, Real.rpow_one]
  have hs : 0 < (p : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  rw [h32, div_div, div_le_iff₀ (by nlinarith)]
  have hlog' : Real.log p ≤ 2 * (p : ℝ) ^ ((1 : ℝ) / 2) := by
    have := hlog; rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num] at this; exact this
  have hinv : 4 * (p * (p : ℝ) ^ ((1 : ℝ) / 2))⁻¹ * ((p - 1) * p) =
      4 * (p - 1) / (p : ℝ) ^ ((1 : ℝ) / 2) := by
    field_simp
  rw [hinv, le_div_iff₀ hs]
  -- `log p · √p ≤ 2p ≤ 4(p − 1)`.
  have hsq : (p : ℝ) ^ ((1 : ℝ) / 2) * (p : ℝ) ^ ((1 : ℝ) / 2) = p := by
    rw [← Real.rpow_add hp0]; norm_num
  nlinarith

/-- The constant `K = Σ_n 4 n^{−3/2}` bounding the tame part on average. -/
def tameConstant : ℝ := ∑' n : ℕ, 4 * ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹

theorem summable_tame : Summable fun n : ℕ => 4 * ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹ :=
  (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4

theorem tameConstant_nonneg : 0 ≤ tameConstant :=
  tsum_nonneg fun n => by positivity

/-- **The tame part on average**: `Σ_{n ≤ N} d(n)/n ≤ K · H_N`, `d(n) = Σ_{p ∣ n} log p/(p − 1)`. -/
theorem sum_tameDifferent_div_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, tameDifferent n / n ≤ tameConstant * harmonicSum N := by
  -- swap the sums over `n` and over the primes `p ∣ n`
  have hswap : ∑ n ∈ Icc 1 N, tameDifferent n / n =
      ∑ p ∈ (Icc 1 N).filter Nat.Prime,
        Real.log p / ((p : ℝ) - 1) * ∑ n ∈ (Icc 1 N).filter (p ∣ ·), 1 / (n : ℝ) := by
    simp only [tameDifferent, sum_div, mul_sum]
    refine sum_comm' fun n p => ?_
    simp only [mem_Icc, mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp, hpn, -⟩
      exact ⟨⟨⟨h1, h2⟩, hpn⟩, ⟨hp.one_lt.le, (Nat.le_of_dvd h1 hpn).trans h2⟩, hp⟩
    · rintro ⟨⟨⟨h1, h2⟩, hpn⟩, -, hp⟩
      exact ⟨⟨h1, h2⟩, hp, hpn, by omega⟩
    -- the summand
  have hterm : ∀ p ∈ (Icc 1 N).filter Nat.Prime,
      Real.log p / ((p : ℝ) - 1) * ∑ n ∈ (Icc 1 N).filter (p ∣ ·), 1 / (n : ℝ) ≤
        4 * ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹ * harmonicSum N := by
    intro p hp
    have hpr := (mem_filter.mp hp).2
    have hp0 : 0 < p := hpr.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpr.one_lt
    -- the multiples of `p` up to `N` carry `(1/p) H_{N/p} ≤ H_N/p`
    have hinner : ∑ n ∈ (Icc 1 N).filter (p ∣ ·), 1 / (n : ℝ) ≤ harmonicSum N / p := by
      rw [filter_dvd_Icc_eq_image hp0,
        sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp0 h]
      have hsub : ∑ t ∈ Icc 1 (N / p), 1 / ((p * t : ℕ) : ℝ) =
          (∑ t ∈ Icc 1 (N / p), 1 / (t : ℝ)) / p := by
        rw [sum_div]
        refine sum_congr rfl fun t _ => ?_
        push_cast
        field_simp
      rw [hsub]
      refine div_le_div_of_nonneg_right ?_ (by linarith)
      exact sum_le_sum_of_subset_of_nonneg
        (Icc_subset_Icc le_rfl (Nat.div_le_self N p)) fun t _ _ => by positivity
    have hlog0 : 0 ≤ Real.log p / ((p : ℝ) - 1) :=
      div_nonneg (Real.log_nonneg hp1.le) (by linarith)
    calc Real.log p / ((p : ℝ) - 1) * ∑ n ∈ (Icc 1 N).filter (p ∣ ·), 1 / (n : ℝ)
        ≤ Real.log p / ((p : ℝ) - 1) * (harmonicSum N / p) :=
          mul_le_mul_of_nonneg_left hinner hlog0
      _ = Real.log p / ((p : ℝ) - 1) / p * harmonicSum N := by ring
      _ ≤ 4 * ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹ * harmonicSum N :=
          mul_le_mul_of_nonneg_right (log_div_mul_le hpr.two_le)
            (sum_nonneg fun n _ => by positivity)
  rw [hswap]
  calc ∑ p ∈ (Icc 1 N).filter Nat.Prime,
        Real.log p / ((p : ℝ) - 1) * ∑ n ∈ (Icc 1 N).filter (p ∣ ·), 1 / (n : ℝ)
      ≤ ∑ p ∈ (Icc 1 N).filter Nat.Prime, 4 * ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹ * harmonicSum N :=
        sum_le_sum hterm
    _ = (∑ p ∈ (Icc 1 N).filter Nat.Prime, 4 * ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹) * harmonicSum N :=
        (sum_mul _ _ _).symm
    _ ≤ tameConstant * harmonicSum N := by
        refine mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun n _ => by positivity)
        exact summable_tame.sum_le_tsum _ fun n _ => by positivity

/-! ### The torsion counterterm -/

/-- **The torsion counterterm is at least `(3/2) log N − C`.** Every `κ` renormalizing the torsion
pairing on the orders `≤ N` satisfies `κ ≥ (3/2) log N − (log 8 + 4 + K + 3/2)`. -/
theorem torsionCounterterm_ge {N : ℕ} (hN : 1 ≤ N) {κ : ℝ} (hκ : RenormalizesAt N κ) :
    3 / 2 * Real.log N - (Real.log 8 + 4 + tameConstant + 3 / 2) ≤ κ := by
  set H := harmonicSum N with hH
  have hH1 : 1 ≤ H := one_le_harmonicSum hN
  have hHle : H ≤ 1 + Real.log N := harmonicSum_le N
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  -- the pairing of the torsion charges against their mass
  have h1 := hκ torsionTest
  rw [selfMass_torsionTest] at h1
  have h2 := torsionPairing_torsionTest_ge N
  have h3 := atomicWeilForm_poleVector_ge N
  rw [sum_poleVector_sq] at h3
  -- the self-intersection on average
  have hc : ∑ n ∈ Icc 1 N, selfIntersection n / n =
      ∑ n ∈ Icc 1 N, Real.log n / n - ∑ n ∈ Icc 1 N, tameDifferent n / n := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [selfIntersection_eq (mem_Icc.mp hn).1, sub_div]
  have h4 := sum_log_div_ge hN
  have h5 := sum_tameDifferent_div_le N
  have hlogN1 : Real.log N ≤ Real.log (N + 1) :=
    Real.log_le_log (by exact_mod_cast hN) (by linarith)
  -- `κ H ≥ (log N − C) H + ½ log² N − 1 − K H` and `½ log² N ≥ (½ log N − ½) H`
  have hmain : (Real.log N - (Real.log 8 + 4)) * H + (Real.log N ^ 2 / 2 - 1) - tameConstant * H
      ≤ κ * H := by
    have : Real.log N ^ 2 ≤ Real.log (N + 1) ^ 2 := pow_le_pow_left₀ hlogN hlogN1 2
    linarith
  have hsq : (Real.log N / 2 - 1 / 2) * H ≤ Real.log N ^ 2 / 2 := by nlinarith
  have hfin : (3 / 2 * Real.log N - (Real.log 8 + 4 + tameConstant + 3 / 2)) * H ≤ κ * H := by
    nlinarith
  exact le_of_mul_le_mul_right hfin (by linarith)

/-- **The anomaly cost.** The covariant scalar `log N + log 4 + 4` renormalizes Weil's prime form
(`atomicWeilForm_le_log`), while every counterterm of the torsion pairing exceeds it by at least
`½ log N − C`: the self-intersection, the potential of the anomaly cocycle, costs half a logarithm. -/
theorem anomaly_cost {N : ℕ} (hN : 1 ≤ N) {κ : ℝ} (hκ : RenormalizesAt N κ) :
    (∀ x : ℕ → ℝ, atomicWeilForm N x ≤ (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2) ∧
      (Real.log N + (Real.log 4 + 4)) + (1 / 2 * Real.log N -
        (Real.log 8 + Real.log 4 + 8 + tameConstant + 3 / 2)) ≤ κ := by
  refine ⟨atomicWeilForm_le_log N, ?_⟩
  have := torsionCounterterm_ge hN hκ
  linarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
