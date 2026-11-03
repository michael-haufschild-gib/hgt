import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheBulkSecondOrderOfThePoleIsAStieltjesConstant
import GaloisForLFunctions.CompletedArithmeticForms.RamanujanConductorFrames

/-!
# The bulk entries are read by the Stieltjes constants

The conductor packets `R_e(n) = c_e(n)/(√φ(e) √n)`, `n ≤ N`, are quasimodes of the prime matrix
`P(n, j) = Λ(j/n)/√(j/n)` (`n ∣ j`, symmetric) with energies `ρ_e = γ + log e + τ(e)` (RAPT). This
file computes the second order of every bulk entry `⟨P R_e, R_{e'}⟩` exactly.

* **The divisor collapse** (`sum_divisors_ramanujanLag_mul_vonMangoldt`): since `Λ ∗ 1 = log`,
  `(c_e ∗ Λ)(j) = Σ_{d ∣ (e, j)} μ(e/d) d (log j − log d)`. The prime pairing of two conductor
  packets contains no prime sum: no prime in a progression survives.
* **The prime pairing is a double Möbius transform of harmonic sums**
  (`inner_fullPrimeMatrix_ramanujan`, `conductorPrimePairing_eq`): with `L = lcm(d, t)`,
  `Σ_{j ≤ N} c_b(j)(c_a ∗ Λ)(j)/j = Σ_{d ∣ a, t ∣ b} μ(a/d) μ(b/t) (d, t)
  ((log L − log d) H_{⌊N/L⌋} + Σ_{i ≤ N/L} log i/i)`.
* **The second order of every bulk entry** (`tendsto_bulkPrimeResidual`):
  `⟨P R_e, R_{e'}⟩ − (log N − ρ_e) ⟨R_e, R_{e'}⟩ → D(e, e')`, an explicit polynomial in `γ`, the first
  Stieltjes constant `γ₁` and the logarithms of the divisors of `e` and `e'` (`bulkSecondOrder`);
  normalized, `log N (⟨P r_e, r_{e'}⟩ − (log N − ρ_e)⟨r_e, r_{e'}⟩) → D(e, e')`.
* **Primes** (`bulkSecondOrder_prime`): `D(p, p) = 2γ₁ + γ² + p log²p/(p − 1)²`; the excess over the
  pole is `Σ_{k ≥ 1} Λ(p^k) log(p^k)/p^k`, the `p`-part of `Σ Λ(n) log n/n`.

The quadratic and linear terms in `log N` cancel against the Gram matrix because the residual of the
quasimode is `o(log N)` (`tendsto_of_sub_isQuadratic`); only the constant term is computed.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace ArithmeticFunction.Moebius

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open ArithmeticFunction (vonMangoldt)
open RenormalizedArithmeticPotentialTheory ArithmeticEffectivityTheory BezoutValuationIncidence
  CompletedArithmeticForms ArithmeticIntersectionTheory

/-! ### The divisor collapse -/

/-- Over the multiples of `d`: `Σ_{n ∣ j, d ∣ n} Λ(j/n) = log j − log d` for `d ∣ j`. -/
theorem sum_divisors_dvd_vonMangoldt {d j : ℕ} (hd : 0 < d) (hj : 0 < j) (hdj : d ∣ j) :
    ∑ n ∈ j.divisors, (if d ∣ n then vonMangoldt (j / n) else 0) =
      Real.log j - Real.log d := by
  obtain ⟨J, rfl⟩ := hdj
  have hJ : 0 < J := Nat.pos_of_ne_zero fun h => by simp [h] at hj
  rw [← Finset.sum_filter]
  have hbij : ∑ n ∈ (d * J).divisors with d ∣ n, vonMangoldt (d * J / n) =
      ∑ m ∈ J.divisors, vonMangoldt (J / m) := by
    symm
    refine Finset.sum_nbij' (fun m => d * m) (fun n => n / d) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_filter, Nat.mem_divisors] at hm ⊢
      exact ⟨⟨Nat.mul_dvd_mul_left d hm.1, (Nat.mul_pos hd hJ).ne'⟩, dvd_mul_right d m⟩
    · intro n hn
      simp only [Finset.mem_filter, Nat.mem_divisors] at hn ⊢
      obtain ⟨⟨hnJ, _⟩, k, rfl⟩ := hn
      rw [Nat.mul_div_cancel_left k hd]
      exact ⟨Nat.dvd_of_mul_dvd_mul_left hd hnJ, hJ.ne'⟩
    · intro m _
      exact Nat.mul_div_cancel_left m hd
    · intro n hn
      simp only [Finset.mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro m _
      rw [Nat.mul_div_mul_left J m hd]
  rw [hbij, show ∑ m ∈ J.divisors, vonMangoldt (J / m) = ∑ m ∈ J.divisors, vonMangoldt m from
    Nat.sum_div_divisors J _, ArithmeticFunction.vonMangoldt_sum]
  have hd0 : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd).ne'
  have hJ0 : (J : ℝ) ≠ 0 := (Nat.cast_pos.mpr hJ).ne'
  push_cast
  rw [Real.log_mul hd0 hJ0]
  ring

/-- **The divisor collapse**: `(c_e ∗ Λ)(j) = Σ_{d ∣ e, d ∣ j} μ(e/d) d (log j − log d)`. -/
theorem sum_divisors_ramanujanLag_mul_vonMangoldt (e : ℕ) {j : ℕ} (hj : 0 < j) :
    ∑ n ∈ j.divisors, ramanujanLagCoefficient e n * vonMangoldt (j / n) =
      ∑ d ∈ e.divisors, moebiusReal (e / d) *
        (if d ∣ j then (d : ℝ) * (Real.log j - Real.log d) else 0) := by
  simp only [ramanujanLagCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hrw : ∀ n ∈ j.divisors,
      moebiusReal (e / d) * (if d ∣ n then (d : ℝ) else 0) * vonMangoldt (j / n) =
        moebiusReal (e / d) * (d : ℝ) * (if d ∣ n then vonMangoldt (j / n) else 0) :=
    fun n _ => by split_ifs <;> ring
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  split_ifs with hdj
  · rw [sum_divisors_dvd_vonMangoldt hd0 hj hdj]
    ring
  · rw [Finset.sum_eq_zero fun n hn =>
      if_neg fun hdn => hdj (hdn.trans (Nat.dvd_of_mem_divisors hn))]
    ring

/-! ### The prime pairing of two conductor packets -/

/-- The upper half of the prime kernel against two profiles `f(n)/√n`, `g(j)/√j`:
`Σ_{n, j ≤ N} U(n, j) (g(j)/√j)(f(n)/√n) = Σ_{j ≤ N} g(j) (f ∗ Λ)(j)/j`. -/
theorem sum_primeKernelUp_profiles (N : ℕ) (f g : ℕ → ℝ) :
    ∑ j ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        primeKernelUp n j * (g j / Real.sqrt j * (f n / Real.sqrt n)) =
      ∑ j ∈ Icc 1 N, g j * (∑ n ∈ j.divisors, f n * vonMangoldt (j / n)) / j := by
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjN : j ≤ N := (Finset.mem_Icc.mp hj).2
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hsupp : ∀ n ∈ Icc 1 N, n ∉ j.divisors →
      primeKernelUp n j * (g j / Real.sqrt j * (f n / Real.sqrt n)) = 0 := fun n _ hn => by
    unfold primeKernelUp
    rw [if_neg fun h => hn (Nat.mem_divisors.mpr ⟨h.1, by omega⟩), zero_mul]
  rw [← Finset.sum_subset (fun n hn => Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hn,
      (Nat.divisor_le hn).trans hjN⟩) hsupp, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnj : n ∣ j := Nat.dvd_of_mem_divisors hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_mem_divisors hn
  unfold primeKernelUp
  by_cases hne : n = j
  · rw [if_neg (fun h => h.2 hne), hne, Nat.div_self (by omega : 0 < j),
      ArithmeticFunction.vonMangoldt_apply_one]
    ring
  · rw [if_pos ⟨hnj, hne⟩]
    have hq : ((j / n : ℕ) : ℝ) = (j : ℝ) / n := Nat.cast_div hnj hn0.ne'
    rw [hq, Real.sqrt_div' _ hn0.le]
    obtain ⟨r, hr0, hr⟩ : ∃ r, 0 < r ∧ Real.sqrt j = r := ⟨_, Real.sqrt_pos.mpr hj0, rfl⟩
    obtain ⟨s, hs0, hs⟩ : ∃ s, 0 < s ∧ Real.sqrt n = s := ⟨_, Real.sqrt_pos.mpr hn0, rfl⟩
    have hjr : (j : ℝ) = r ^ 2 := by rw [← hr, Real.sq_sqrt hj0.le]
    have hr0' := hr0.ne'
    have hs0' := hs0.ne'
    rw [hr, hs, hjr]
    field_simp

/-- The pole-gauge Ramanujan profile: `R_e(n) = c_e(n)/(√φ(e) √n)`. -/
theorem ramanujanPoleProfile_eq {e : ℕ} (he : 0 < e) (n : ℕ) :
    ramanujanPoleProfile e n =
      ramanujanLagCoefficient e n / Real.sqrt e.totient / Real.sqrt n := by
  rw [ramanujanPoleProfile, normalizedRamanujanMode_eq_coefficient he]

/-- The prime convolution pairing `Σ_{j ≤ N} c_b(j) (c_a ∗ Λ)(j)/j`. -/
def conductorPrimePairing (a b N : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 N, ramanujanLagCoefficient b j *
    (∑ n ∈ j.divisors, ramanujanLagCoefficient a n * vonMangoldt (j / n)) / j

/-- **The prime pairing of two conductor packets**: `⟨P R_e, R_{e'}⟩` is
`(Σ_{j ≤ N} c_{e'}(j)(c_e ∗ Λ)(j)/j + Σ_{j ≤ N} c_e(j)(c_{e'} ∗ Λ)(j)/j)/√(φ(e)φ(e'))`. -/
theorem inner_fullPrimeMatrix_ramanujan {e e' : ℕ} (he : 0 < e) (he' : 0 < e') (N : ℕ) :
    ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector e N),
      ramanujanHorizonVector e' N⟫ =
      (conductorPrimePairing e e' N + conductorPrimePairing e' e N) /
        (Real.sqrt e.totient * Real.sqrt e'.totient) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change ∑ n : PrimeHorizonIndex N, ramanujanPoleProfile e' n *
    (Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector e N)) n = _
  simp only [fullPrimeMatrix_apply_ramanujanHorizonVector]
  rw [Finset.sum_coe_sort (Icc 1 N) (fun n => ramanujanPoleProfile e' n *
    ∑ j ∈ Icc 1 N, weilPrimeKernel n j * ramanujanPoleProfile e j)]
  simp only [weilPrimeKernel_eq_up_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  have hA : ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      ramanujanPoleProfile e' n * (primeKernelUp n j * ramanujanPoleProfile e j) =
      conductorPrimePairing e' e N / (Real.sqrt e.totient * Real.sqrt e'.totient) := by
    rw [conductorPrimePairing, ← sum_primeKernelUp_profiles N (ramanujanLagCoefficient e')
      (ramanujanLagCoefficient e), Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ramanujanPoleProfile_eq he, ramanujanPoleProfile_eq he']
    ring
  have hB : ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      ramanujanPoleProfile e' n * (primeKernelUp j n * ramanujanPoleProfile e j) =
      conductorPrimePairing e e' N / (Real.sqrt e.totient * Real.sqrt e'.totient) := by
    rw [conductorPrimePairing, ← sum_primeKernelUp_profiles N (ramanujanLagCoefficient e)
      (ramanujanLagCoefficient e'), Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ramanujanPoleProfile_eq he, ramanujanPoleProfile_eq he']
    ring
  rw [hA, hB]
  ring

/-! ### The pairing as a double Möbius transform of harmonic sums -/

/-- Multiples of `L` in `[1, N]`: `Σ_{n ≤ N, L ∣ n} F(n/L) = Σ_{i ≤ N/L} F(i)`. -/
theorem sum_Icc_dvd_eq (N : ℕ) {L : ℕ} (hL : 0 < L) (F : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, (if L ∣ n then F (n / L) else 0) = ∑ i ∈ Icc 1 (N / L), F i := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun i => L * i) (fun n => n / L) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hL.ne' (by have := hi.1; omega)), ?_⟩,
      dvd_mul_right L i⟩
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le hL).mp hi.2
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨hn1, hnN⟩, k, rfl⟩ := hn
    rw [Nat.mul_div_cancel_left k hL]
    refine ⟨Nat.one_le_iff_ne_zero.mpr fun h => by simp [h] at hn1, ?_⟩
    rw [Nat.le_div_iff_mul_le hL, mul_comm]
    exact hnN
  · intro i _
    exact Nat.mul_div_cancel_left i hL
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro i _
    rw [Nat.mul_div_cancel_left i hL]

/-- `H_M = Σ_{i ≤ M} 1/i`. -/
theorem harmonic_eq_sum_Icc_real (M : ℕ) :
    (harmonic M : ℝ) = ∑ i ∈ Icc 1 M, (i : ℝ)⁻¹ := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  rfl

/-- One divisor pair: `Σ_{j ≤ N} [t ∣ j] t [d ∣ j] d (log j − log d)/j
= (d, t) ((log L − log d) H_{⌊N/L⌋} + Σ_{i ≤ N/L} log i/i)`, `L = lcm(d, t)`. -/
theorem sum_Icc_dvd_dvd_log (N : ℕ) {d t : ℕ} (hd : 0 < d) (ht : 0 < t) :
    ∑ j ∈ Icc 1 N, (if t ∣ j then (t : ℝ) else 0) *
        (if d ∣ j then (d : ℝ) * (Real.log j - Real.log d) else 0) / j =
      (Nat.gcd d t : ℝ) * ((Real.log (Nat.lcm d t) - Real.log d) *
        (harmonic (N / Nat.lcm d t) : ℝ) + logHarmonic (N / Nat.lcm d t)) := by
  set L := Nat.lcm d t with hLdef
  have hL : 0 < L := Nat.lcm_pos hd ht
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hgL : (Nat.gcd d t : ℝ) * L = d * t := by exact_mod_cast Nat.gcd_mul_lcm d t
  have htd : (t : ℝ) * d = (Nat.gcd d t : ℝ) * L := by rw [hgL]; ring
  set F : ℕ → ℝ := fun i => (t : ℝ) * d * (Real.log ((L * i : ℕ) : ℝ) - Real.log d) /
    ((L * i : ℕ) : ℝ) with hF
  have hterm : ∀ j ∈ Icc 1 N, (if t ∣ j then (t : ℝ) else 0) *
      (if d ∣ j then (d : ℝ) * (Real.log j - Real.log d) else 0) / j =
      if L ∣ j then F (j / L) else 0 := fun j _ => by
    by_cases hLj : L ∣ j
    · have hdj : d ∣ j := (Nat.dvd_lcm_left d t).trans hLj
      have htj : t ∣ j := (Nat.dvd_lcm_right d t).trans hLj
      rw [if_pos htj, if_pos hdj, if_pos hLj, hF]
      beta_reduce
      rw [Nat.mul_div_cancel' hLj]
      ring
    · have : ¬(d ∣ j ∧ t ∣ j) := fun h => hLj (Nat.lcm_dvd h.1 h.2)
      rw [if_neg hLj]
      by_cases hdj : d ∣ j
      · rw [if_neg fun htj => this ⟨hdj, htj⟩]; ring
      · rw [if_neg hdj]; ring
  rw [Finset.sum_congr rfl hterm, sum_Icc_dvd_eq N hL F]
  calc ∑ i ∈ Icc 1 (N / L), F i
      = ∑ i ∈ Icc 1 (N / L), ((Nat.gcd d t : ℝ) * (Real.log L - Real.log d) * (i : ℝ)⁻¹ +
          (Nat.gcd d t : ℝ) * (Real.log i / i)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi0 : (0 : ℝ) < i := by exact_mod_cast (Finset.mem_Icc.mp hi).1
        have hi0' := hi0.ne'
        have hL0' := hL0.ne'
        rw [hF]
        beta_reduce
        push_cast
        rw [Real.log_mul hL0' hi0', htd]
        field_simp
        ring
    _ = (Nat.gcd d t : ℝ) * (Real.log L - Real.log d) * ∑ i ∈ Icc 1 (N / L), (i : ℝ)⁻¹ +
          (Nat.gcd d t : ℝ) * ∑ i ∈ Icc 1 (N / L), Real.log i / i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = _ := by
        rw [harmonic_eq_sum_Icc_real, logHarmonic]
        ring

/-- **The prime pairing as a double Möbius transform**:
`Σ_{j ≤ N} c_b(j)(c_a ∗ Λ)(j)/j = Σ_{d ∣ a} μ(a/d) Σ_{t ∣ b} μ(b/t) (d, t)
((log L − log d) H_{⌊N/L⌋} + Σ_{i ≤ N/L} log i/i)`. -/
theorem conductorPrimePairing_eq (a b N : ℕ) :
    conductorPrimePairing a b N = doubleMoebius b a (fun t d =>
      (Nat.gcd d t : ℝ) * ((Real.log (Nat.lcm d t) - Real.log d) *
        (harmonic (N / Nat.lcm d t) : ℝ) + logHarmonic (N / Nat.lcm d t))) := by
  have hj : ∀ j ∈ Icc 1 N, ramanujanLagCoefficient b j *
      (∑ n ∈ j.divisors, ramanujanLagCoefficient a n * vonMangoldt (j / n)) / j =
      ∑ d ∈ a.divisors, (μ (a / d) : ℝ) * ∑ t ∈ b.divisors, (μ (b / t) : ℝ) *
        ((if t ∣ j then (t : ℝ) else 0) *
          (if d ∣ j then (d : ℝ) * (Real.log j - Real.log d) else 0) / j) := fun j hj => by
    rw [sum_divisors_ramanujanLag_mul_vonMangoldt a (Finset.mem_Icc.mp hj).1,
      ramanujanLagCoefficient, Finset.sum_mul, Finset.sum_div]
    simp only [moebiusReal, Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [conductorPrimePairing, Finset.sum_congr rfl hj, Finset.sum_comm]
  unfold doubleMoebius
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [← Finset.mul_sum, sum_Icc_dvd_dvd_log N (Nat.pos_of_mem_divisors hd)
    (Nat.pos_of_mem_divisors ht)]

/-! ### Limits of the harmonic pieces -/

/-- The logarithmic harmonic sum at `⌊N/L⌋`: `Σ_{i ≤ N/L} log i/i − (log N − log L)²/2 → γ₁`. -/
theorem abs_log_div_sq_sub_le {N L : ℕ} (hL : 0 < L) (hLN : L ≤ N) :
    |Real.log ((N / L : ℕ) : ℝ) ^ 2 / 2 - (Real.log N - Real.log L) ^ 2 / 2| ≤
      2 * L * (Real.log N / N) := by
  obtain ⟨h0, h1⟩ := RenormalizedArithmeticPotentialTheory.roundoff_le hL hLN
  have hq1 : 1 ≤ N / L := Nat.div_pos hLN hL
  have hqR : (1 : ℝ) ≤ ((N / L : ℕ) : ℝ) := by exact_mod_cast hq1
  have hb : 0 ≤ Real.log ((N / L : ℕ) : ℝ) := Real.log_nonneg hqR
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (hL.trans_le hLN)
  have hlogL : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast hL)
  have hNle : (N : ℝ) ≤ 2 * ((N / L : ℕ) : ℝ) * L := by
    have hmod := Nat.mod_lt N hL
    have hdiv := Nat.div_add_mod N L
    have : N ≤ 2 * (N / L) * L := by nlinarith
    exact_mod_cast this
  set q : ℝ := ((N / L : ℕ) : ℝ)
  set a := Real.log N - Real.log L
  set b := Real.log q
  have hq0 : 0 < q := by linarith
  have hab : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  have hδ : a - b = Real.log N - b - Real.log L := by ring
  have hsum : 0 ≤ a + b := by linarith
  have hsum' : a + b ≤ 2 * Real.log N := by linarith
  have e1 : (a - b) * (a + b) ≤ 1 / q * (2 * Real.log N) :=
    mul_le_mul (by linarith) hsum' hsum (by positivity)
  have e2 : 0 ≤ (a - b) * (a + b) := mul_nonneg (by linarith) hsum
  have e3 : 1 / q ≤ 2 * L / N := by
    rw [div_le_div_iff₀ hq0 hN0]
    linarith
  have hlogN : 0 ≤ Real.log N := by linarith
  rw [abs_le]
  constructor
  · have : 1 / q * (2 * Real.log N) ≤ 2 * L / N * (2 * Real.log N) :=
      mul_le_mul_of_nonneg_right e3 (by linarith)
    have h2 : 2 * L / N * (2 * Real.log N) = 2 * (2 * L * (Real.log N / N)) := by ring
    nlinarith
  · have hR : 0 ≤ 2 * L * (Real.log N / N) :=
      mul_nonneg (by positivity) (div_nonneg hlogN hN0.le)
    nlinarith

theorem tendsto_logHarmonic_div_sub {L : ℕ} (hL : 0 < L) :
    Tendsto (fun N : ℕ => logHarmonic (N / L) - (Real.log N - Real.log L) ^ 2 / 2) atTop
      (𝓝 stieltjesOne) := by
  have h1 := tendsto_logHarmonic_sub.comp (Nat.tendsto_div_const_atTop hL.ne')
  have hlog : Tendsto (fun N : ℕ => 2 * L * (Real.log N / N)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    have h' := h.const_mul (2 * (L : ℝ))
    rw [mul_zero] at h'
    refine h'.congr fun N => ?_
    simp only [Function.comp_apply, pow_one, one_mul, add_zero]
  have h2 : Tendsto (fun N : ℕ => Real.log ((N / L : ℕ) : ℝ) ^ 2 / 2 -
      (Real.log N - Real.log L) ^ 2 / 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlog
    filter_upwards [eventually_ge_atTop L] with N hN
    rw [Real.norm_eq_abs]
    exact abs_log_div_sq_sub_le hL hN
  have := h1.add h2
  rw [add_zero] at this
  refine this.congr fun N => ?_
  simp only [Function.comp_apply]
  ring

/-- `log N · (H_{⌊N/L⌋} − (log N + γ − log L)) → 0`. -/
theorem tendsto_log_mul_harmonicFloorError {L : ℕ} (hL : 0 < L) :
    Tendsto (fun N : ℕ => Real.log N * harmonicFloorError N L) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => 4 * L * (Real.log N / N)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    have h' := h.const_mul (4 * (L : ℝ))
    rw [mul_zero] at h'
    refine h'.congr fun N => ?_
    simp only [Function.comp_apply, pow_one, one_mul, add_zero]
  refine squeeze_zero_norm' ?_ hlog
  filter_upwards [eventually_ge_atTop (max L 1)] with N hN
  have hLN : L ≤ N := le_of_max_le_left hN
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlogN]
  calc Real.log N * |harmonicFloorError N L| ≤ Real.log N * (4 * L / N) :=
        mul_le_mul_of_nonneg_left (abs_harmonicFloorError_le hL hLN) hlogN
    _ = 4 * L * (Real.log N / N) := by ring

theorem tendsto_harmonicFloorError {L : ℕ} (hL : 0 < L) :
    Tendsto (fun N : ℕ => harmonicFloorError N L) atTop (𝓝 0) := by
  have hc := tendsto_const_div_atTop_nhds_zero_nat (4 * (L : ℝ))
  refine squeeze_zero_norm' ?_ hc
  filter_upwards [eventually_ge_atTop L] with N hN
  rw [Real.norm_eq_abs]
  exact abs_harmonicFloorError_le hL hN

/-! ### Double Möbius transforms of limits -/

theorem doubleMoebius_sub (m n : ℕ) (X Y : ℕ → ℕ → ℝ) :
    doubleMoebius m n (fun a b => X a b - Y a b) = doubleMoebius m n X - doubleMoebius m n Y := by
  simp only [doubleMoebius, mul_sub, Finset.sum_sub_distrib]

theorem tendsto_doubleMoebius {m n : ℕ} {X : ℕ → ℕ → ℕ → ℝ} {Y : ℕ → ℕ → ℝ}
    (h : ∀ a ∈ m.divisors, ∀ b ∈ n.divisors, Tendsto (fun N => X N a b) atTop (𝓝 (Y a b))) :
    Tendsto (fun N => doubleMoebius m n (X N)) atTop (𝓝 (doubleMoebius m n Y)) := by
  unfold doubleMoebius
  exact tendsto_finsetSum _ fun b hb =>
    (tendsto_finsetSum _ fun a ha => (h a ha b hb).const_mul _).const_mul _

theorem tendsto_doubleMoebius_zero {m n : ℕ} {X : ℕ → ℕ → ℕ → ℝ}
    (h : ∀ a ∈ m.divisors, ∀ b ∈ n.divisors, Tendsto (fun N => X N a b) atTop (𝓝 0)) :
    Tendsto (fun N => doubleMoebius m n (X N)) atTop (𝓝 0) := by
  have h0 : doubleMoebius m n (fun _ _ => (0 : ℝ)) = 0 := by simp [doubleMoebius]
  have := tendsto_doubleMoebius (Y := fun _ _ => (0 : ℝ)) h
  rwa [h0] at this

theorem doubleMoebius_mul_const (m n : ℕ) (X : ℕ → ℕ → ℝ) (c : ℝ) :
    doubleMoebius m n (fun a b => c * X a b) = c * doubleMoebius m n X := by
  simp only [doubleMoebius, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

/-! ### The Stieltjes polynomial of a conductor pair -/

/-- The Stieltjes summand of the divisor pair `t ∣ b`, `d ∣ a` at `ℓ = log N`, `L = lcm(d, t)`:
`(d, t)((log L − log d)(ℓ − log L + γ) + (ℓ − log L)²/2 + γ₁)`. -/
def bulkStieltjesTerm (ℓ : ℝ) (t d : ℕ) : ℝ :=
  (Nat.gcd d t : ℝ) * ((Real.log (Nat.lcm d t) - Real.log d) *
      (ℓ - Real.log (Nat.lcm d t) + Real.eulerMascheroniConstant) +
    (ℓ - Real.log (Nat.lcm d t)) ^ 2 / 2 + stieltjesOne)

/-- The Stieltjes polynomial `Φ_{a,b}(ℓ) = Σ_{d ∣ a} μ(a/d) Σ_{t ∣ b} μ(b/t) T_ℓ(t, d)`. -/
def bulkStieltjesPoly (a b : ℕ) (ℓ : ℝ) : ℝ := doubleMoebius b a (bulkStieltjesTerm ℓ)

/-- The prime pairing is its Stieltjes polynomial at `log N` up to `o(1)`. -/
theorem tendsto_conductorPrimePairing_sub {a b : ℕ} :
    Tendsto (fun N : ℕ => conductorPrimePairing a b N - bulkStieltjesPoly a b (Real.log N))
      atTop (𝓝 0) := by
  have hdiff : ∀ N : ℕ, conductorPrimePairing a b N - bulkStieltjesPoly a b (Real.log N) =
      doubleMoebius b a (fun t d => (Nat.gcd d t : ℝ) *
        ((Real.log (Nat.lcm d t) - Real.log d) * harmonicFloorError N (Nat.lcm d t) +
          (logHarmonic (N / Nat.lcm d t) -
            (Real.log N - Real.log (Nat.lcm d t)) ^ 2 / 2 - stieltjesOne))) := fun N => by
    rw [conductorPrimePairing_eq, bulkStieltjesPoly, ← doubleMoebius_sub]
    refine doubleMoebius_congr fun t _ d _ => ?_
    unfold bulkStieltjesTerm harmonicFloorError
    ring
  simp only [hdiff]
  refine tendsto_doubleMoebius_zero fun t ht d hd => ?_
  have hL : 0 < Nat.lcm d t := Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors ht)
  have h1 := (tendsto_harmonicFloorError hL).const_mul (Real.log (Nat.lcm d t) - Real.log d)
  have h2 := (tendsto_logHarmonic_div_sub hL).sub_const stieltjesOne
  have := (h1.add h2).const_mul (Nat.gcd d t : ℝ)
  simp only [mul_zero, sub_self, add_zero] at this
  exact this

/-! ### Quadratic expansions -/

/-- A real function of the form `a ℓ² + b ℓ + c`. -/
def IsQuadratic (f : ℝ → ℝ) : Prop := ∃ a b c : ℝ, ∀ ℓ, f ℓ = a * ℓ ^ 2 + b * ℓ + c

theorem IsQuadratic.add {f g : ℝ → ℝ} (hf : IsQuadratic f) (hg : IsQuadratic g) :
    IsQuadratic fun ℓ => f ℓ + g ℓ := by
  obtain ⟨a, b, c, hf⟩ := hf
  obtain ⟨a', b', c', hg⟩ := hg
  exact ⟨a + a', b + b', c + c', fun ℓ => by beta_reduce; rw [hf, hg]; ring⟩

theorem IsQuadratic.sub {f g : ℝ → ℝ} (hf : IsQuadratic f) (hg : IsQuadratic g) :
    IsQuadratic fun ℓ => f ℓ - g ℓ := by
  obtain ⟨a, b, c, hf⟩ := hf
  obtain ⟨a', b', c', hg⟩ := hg
  exact ⟨a - a', b - b', c - c', fun ℓ => by beta_reduce; rw [hf, hg]; ring⟩

theorem IsQuadratic.div_const {f : ℝ → ℝ} (hf : IsQuadratic f) (k : ℝ) :
    IsQuadratic fun ℓ => f ℓ / k := by
  obtain ⟨a, b, c, hf⟩ := hf
  exact ⟨a / k, b / k, c / k, fun ℓ => by beta_reduce; rw [hf]; ring⟩

theorem isQuadratic_linear_mul_linear (p q r w : ℝ) :
    IsQuadratic fun ℓ => (p * ℓ + q) * (r * ℓ + w) :=
  ⟨p * r, p * w + q * r, q * w, fun ℓ => by ring⟩

theorem isQuadratic_doubleMoebius (m n : ℕ) {X : ℝ → ℕ → ℕ → ℝ}
    (h : ∀ a b, IsQuadratic fun ℓ => X ℓ a b) :
    IsQuadratic fun ℓ => doubleMoebius m n (X ℓ) := by
  choose A B C hX using h
  refine ⟨doubleMoebius m n A, doubleMoebius m n B, doubleMoebius m n C, fun ℓ => ?_⟩
  simp only [doubleMoebius, hX, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem isQuadratic_bulkStieltjesPoly (a b : ℕ) : IsQuadratic (bulkStieltjesPoly a b) := by
  show IsQuadratic fun ℓ => doubleMoebius b a (bulkStieltjesTerm ℓ)
  refine isQuadratic_doubleMoebius b a fun t d => ?_
  refine ⟨(Nat.gcd d t : ℝ) / 2,
    (Nat.gcd d t : ℝ) * (Real.log (Nat.lcm d t) - Real.log d - Real.log (Nat.lcm d t)),
    (Nat.gcd d t : ℝ) * ((Real.log (Nat.lcm d t) - Real.log d) *
      (Real.eulerMascheroniConstant - Real.log (Nat.lcm d t)) +
      Real.log (Nat.lcm d t) ^ 2 / 2 + stieltjesOne), fun ℓ => ?_⟩
  unfold bulkStieltjesTerm
  ring

/-- **Only the constant term survives**: if `u_N − Ψ(ℓ_N) → 0` for a quadratic `Ψ`, `ℓ_N → ∞` and
`u_N = o(ℓ_N)`, then the quadratic and linear coefficients of `Ψ` vanish and `u_N → Ψ(0)`. -/
theorem tendsto_of_sub_isQuadratic {u ℓ : ℕ → ℝ} {Ψ : ℝ → ℝ} (hΨ : IsQuadratic Ψ)
    (hℓ : Tendsto ℓ atTop atTop) (hu : Tendsto (fun N => u N - Ψ (ℓ N)) atTop (𝓝 0))
    (ho : Tendsto (fun N => u N / ℓ N) atTop (𝓝 0)) : Tendsto u atTop (𝓝 (Ψ 0)) := by
  obtain ⟨a, b, c, hΨ⟩ := hΨ
  have hc : Ψ 0 = c := by rw [hΨ]; ring
  have hinv : Tendsto (fun N => (ℓ N)⁻¹) atTop (𝓝 0) := hℓ.inv_tendsto_atTop
  have h1 : Tendsto (fun N => a * ℓ N + b) atTop (𝓝 0) := by
    have hc' : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
    have := ho.sub ((hc'.add hu).mul hinv)
    rw [show (0 : ℝ) - (c + 0) * 0 = 0 by ring] at this
    refine this.congr' ?_
    filter_upwards [hℓ.eventually_gt_atTop 0] with N hN
    have hN' := hN.ne'
    rw [hΨ]
    field_simp
    ring
  have ha : a = 0 := by
    have h2 := h1.mul hinv
    rw [zero_mul] at h2
    have h3 : Tendsto (fun N => (a * ℓ N + b) * (ℓ N)⁻¹) atTop (𝓝 a) := by
      have ha' : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
      have := ha'.add (hinv.const_mul b)
      rw [mul_zero, add_zero] at this
      refine this.congr' ?_
      filter_upwards [hℓ.eventually_gt_atTop 0] with N hN
      rw [add_mul, mul_assoc, mul_inv_cancel₀ hN.ne', mul_one]
    exact tendsto_nhds_unique h3 h2
  have hb : b = 0 := by
    rw [ha] at h1
    simp only [zero_mul, zero_add] at h1
    exact tendsto_nhds_unique tendsto_const_nhds h1
  rw [hc]
  have := hu.const_add c
  rw [add_zero] at this
  refine this.congr fun N => ?_
  rw [hΨ, ha, hb]
  ring

/-! ### The second order of every bulk entry -/

/-- The Gram entry `⟨R_e, R_{e'}⟩ = Σ_{n ≤ N} c_e(n) c_{e'}(n)/n / √(φ(e)φ(e'))`. -/
theorem inner_ramanujanHorizonVector_eq {e e' : ℕ} (he : 0 < e) (he' : 0 < e') (N : ℕ) :
    ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫ =
      (∑ n ∈ Icc 1 N, ramanujanLagCoefficient e n * ramanujanLagCoefficient e' n / (n : ℝ)) /
        (Real.sqrt e.totient * Real.sqrt e'.totient) := by
  rw [ramanujanHorizonVector_inner, Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ramanujanPoleProfile_eq he, ramanujanPoleProfile_eq he']
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨s, hs⟩ : ∃ s, Real.sqrt n = s := ⟨_, rfl⟩
  have hns : (n : ℝ) = s ^ 2 := by rw [← hs, Real.sq_sqrt hn0]
  rw [hs, hns]
  ring

/-- The residual of the quasimode is `o(log N)` against every packet:
`(⟨P R_e, R_{e'}⟩ − (log N − ρ_e)⟨R_e, R_{e'}⟩)/log N → 0`. -/
theorem tendsto_bulkPrimeResidual_div_log {e e' : ℕ} (he : 0 < e) (he' : 0 < e') :
    Tendsto (fun N : ℕ =>
      (⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector e N),
          ramanujanHorizonVector e' N⟫ -
        (Real.log N - ramanujanAdjunctionEnergy e) *
          ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫) / Real.log N)
      atTop (𝓝 0) := by
  have hres := tendsto_normalizedRamanujanHorizonVector_residual_norm he
  have hnorm : Tendsto (fun N : ℕ => ‖normalizedRamanujanHorizonVector e' N‖) atTop (𝓝 1) := by
    have h := (tendsto_normalizedRamanujanHorizonVector_norm_sq he').sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using h
  have hprod := hres.mul hnorm
  rw [zero_mul] at hprod
  refine squeeze_zero_norm' ?_ hprod
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  obtain ⟨r, hr0, hr⟩ : ∃ r, 0 < r ∧ Real.sqrt (Real.log N) = r :=
    ⟨_, Real.sqrt_pos.mpr hlog, rfl⟩
  have hlr : Real.log N = r ^ 2 := by rw [← hr, Real.sq_sqrt hlog.le]
  have hid : (⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector e N),
          ramanujanHorizonVector e' N⟫ -
        (Real.log N - ramanujanAdjunctionEnergy e) *
          ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫) / Real.log N =
      ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector e N) -
          (Real.log N - ramanujanAdjunctionEnergy e) • normalizedRamanujanHorizonVector e N,
        normalizedRamanujanHorizonVector e' N⟫ := by
    have hr0' := hr0.ne'
    unfold normalizedRamanujanHorizonVector
    simp only [map_smul, inner_sub_left, real_inner_smul_left, real_inner_smul_right]
    rw [hr, hlr]
    field_simp
  rw [hid, Real.norm_eq_abs]
  exact abs_real_inner_le_norm _ _

/-- The constant `D(e, e')` of the bulk entry: `(Φ_{e,e'}(0) + Φ_{e',e}(0)
+ ρ_e([e = e'] φ(e) γ − I(e, e')))/√(φ(e)φ(e'))`, with `I` the orbit intersection. -/
def bulkSecondOrder (e e' : ℕ) : ℝ :=
  (bulkStieltjesPoly e e' 0 + bulkStieltjesPoly e' e 0 +
      ramanujanAdjunctionEnergy e * ((if e = e' then (e.totient : ℝ) else 0) *
        Real.eulerMascheroniConstant - orbitIntersection e e')) /
    (Real.sqrt e.totient * Real.sqrt e'.totient)

/-- **The second order of every bulk entry**:
`⟨P R_e, R_{e'}⟩ − (log N − ρ_e)⟨R_e, R_{e'}⟩ → D(e, e')`. -/
theorem tendsto_bulkPrimeResidual {e e' : ℕ} (he : 0 < e) (he' : 0 < e') :
    Tendsto (fun N : ℕ =>
      ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector e N),
          ramanujanHorizonVector e' N⟫ -
        (Real.log N - ramanujanAdjunctionEnergy e) *
          ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫)
      atTop (𝓝 (bulkSecondOrder e e')) := by
  -- the Gram entry, exactly, once `e e' ≤ N`
  have hgram : ∀ N : ℕ, e * e' ≤ N →
      ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫ =
        ((if e = e' then (e.totient : ℝ) else 0) * (Real.log N + Real.eulerMascheroniConstant) -
          orbitIntersection e e' + doubleMoebius e e' (fun d t =>
            (Nat.gcd d t : ℝ) * harmonicFloorError N (Nat.lcm d t))) /
        (Real.sqrt e.totient * Real.sqrt e'.totient) := fun N hN => by
    rw [inner_ramanujanHorizonVector_eq he he', sum_ramanujanLagCoefficient_mul_div_eq he he' hN]
    split_ifs <;> ring
  -- the floor errors of the Gram entry are `o(1/log N)`
  have hG : Tendsto (fun N : ℕ => doubleMoebius e e' (fun d t => (Nat.gcd d t : ℝ) *
      ((Real.log N - ramanujanAdjunctionEnergy e) * harmonicFloorError N (Nat.lcm d t))))
      atTop (𝓝 0) := by
    refine tendsto_doubleMoebius_zero fun d hd t ht => ?_
    have hL : 0 < Nat.lcm d t :=
      Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors ht)
    have := ((tendsto_log_mul_harmonicFloorError hL).sub
      ((tendsto_harmonicFloorError hL).const_mul (ramanujanAdjunctionEnergy e))).const_mul
      (Nat.gcd d t : ℝ)
    rw [mul_zero, sub_zero, mul_zero] at this
    exact this.congr fun N => by ring
  have hG' : ∀ N : ℕ, doubleMoebius e e' (fun d t => (Nat.gcd d t : ℝ) *
      ((Real.log N - ramanujanAdjunctionEnergy e) * harmonicFloorError N (Nat.lcm d t))) =
      (Real.log N - ramanujanAdjunctionEnergy e) * doubleMoebius e e' (fun d t =>
        (Nat.gcd d t : ℝ) * harmonicFloorError N (Nat.lcm d t)) := fun N => by
    rw [← doubleMoebius_mul_const]
    exact doubleMoebius_congr fun d _ t _ => by ring
  -- the entry minus its quadratic model tends to zero
  have hu : Tendsto (fun N : ℕ =>
      (⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector e N),
          ramanujanHorizonVector e' N⟫ -
        (Real.log N - ramanujanAdjunctionEnergy e) *
          ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫) -
      ((bulkStieltjesPoly e e' (Real.log N) + bulkStieltjesPoly e' e (Real.log N)) /
          (Real.sqrt e.totient * Real.sqrt e'.totient) -
        (1 * Real.log N + -ramanujanAdjunctionEnergy e) *
          ((if e = e' then (e.totient : ℝ) else 0) * Real.log N +
            ((if e = e' then (e.totient : ℝ) else 0) * Real.eulerMascheroniConstant -
              orbitIntersection e e')) / (Real.sqrt e.totient * Real.sqrt e'.totient)))
      atTop (𝓝 0) := by
    have hA := (tendsto_conductorPrimePairing_sub (a := e) (b := e')).div_const
      (Real.sqrt e.totient * Real.sqrt e'.totient)
    have hB := (tendsto_conductorPrimePairing_sub (a := e') (b := e)).div_const
      (Real.sqrt e.totient * Real.sqrt e'.totient)
    have hC := hG.div_const (Real.sqrt e.totient * Real.sqrt e'.totient)
    have := (hA.add hB).sub hC
    rw [zero_div, add_zero, sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (e * e')] with N hN
    rw [inner_fullPrimeMatrix_ramanujan he he', hgram N hN, hG' N]
    ring
  have hΨq : IsQuadratic fun ℓ =>
      (bulkStieltjesPoly e e' ℓ + bulkStieltjesPoly e' e ℓ) /
          (Real.sqrt e.totient * Real.sqrt e'.totient) -
        (1 * ℓ + -ramanujanAdjunctionEnergy e) *
          ((if e = e' then (e.totient : ℝ) else 0) * ℓ +
            ((if e = e' then (e.totient : ℝ) else 0) * Real.eulerMascheroniConstant -
              orbitIntersection e e')) / (Real.sqrt e.totient * Real.sqrt e'.totient) :=
    (((isQuadratic_bulkStieltjesPoly e e').add
      (isQuadratic_bulkStieltjesPoly e' e)).div_const _).sub
      ((isQuadratic_linear_mul_linear _ _ _ _).div_const _)
  have key := tendsto_of_sub_isQuadratic hΨq
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) hu
    (tendsto_bulkPrimeResidual_div_log he he')
  convert key using 2
  unfold bulkSecondOrder
  ring

/-- **Normalized**: `log N · (⟨P r_e, r_{e'}⟩ − (log N − ρ_e)⟨r_e, r_{e'}⟩) → D(e, e')`. -/
theorem tendsto_log_mul_bulkPrimeResidual {e e' : ℕ} (he : 0 < e) (he' : 0 < e') :
    Tendsto (fun N : ℕ => Real.log N *
      (⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector e N),
          normalizedRamanujanHorizonVector e' N⟫ -
        (Real.log N - ramanujanAdjunctionEnergy e) *
          ⟪normalizedRamanujanHorizonVector e N, normalizedRamanujanHorizonVector e' N⟫))
      atTop (𝓝 (bulkSecondOrder e e')) := by
  refine (tendsto_bulkPrimeResidual he he').congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  obtain ⟨r, hr0, hr⟩ : ∃ r, 0 < r ∧ Real.sqrt (Real.log N) = r :=
    ⟨_, Real.sqrt_pos.mpr hlog, rfl⟩
  have hlr : Real.log N = r ^ 2 := by rw [← hr, Real.sq_sqrt hlog.le]
  have hr0' := hr0.ne'
  unfold normalizedRamanujanHorizonVector
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  rw [hr, hlr]
  field_simp

/-- **The bulk second order at a prime**: `D(p, p) = 2γ₁ + γ² + p log²p/(p − 1)²`. -/
theorem bulkSecondOrder_prime {p : ℕ} (hp : p.Prime) :
    bulkSecondOrder p p = 2 * stieltjesOne + Real.eulerMascheroniConstant ^ 2 +
      p * Real.log p ^ 2 / ((p : ℝ) - 1) ^ 2 := by
  have h1p : (1 : ℕ) ≠ p := hp.one_lt.ne
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hφ : ((p.totient : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  have hτ : tameDifferent p = Real.log p / ((p : ℝ) - 1) := by
    simpa using tameDifferent_prime_pow hp one_ne_zero
  have hO : orbitIntersection p p = ((p : ℝ) - 1) * Real.log p - Real.log p := by
    rw [ArithmeticElectrostatics.orbitIntersection_self_eq hp.pos,
      ArithmeticElectrostatics.localCorrection_eq_totient_mul_tameDifferent, hτ, hφ]
    field_simp
  have hs : Real.sqrt ((p.totient : ℕ) : ℝ) * Real.sqrt ((p.totient : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Real.mul_self_sqrt (by rw [hφ]; linarith), hφ]
  unfold bulkSecondOrder bulkStieltjesPoly doubleMoebius
  rw [hp.divisors, hs, hO, if_pos rfl, hφ]
  simp only [Finset.sum_pair h1p, Nat.div_one, Nat.div_self hp.pos,
    ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_one,
    Int.cast_neg, Int.cast_one, bulkStieltjesTerm, Nat.gcd_one_left, Nat.gcd_one_right,
    Nat.gcd_self, Nat.lcm_one_left, Nat.lcm_one_right, Nat.lcm_self, Nat.cast_one, Real.log_one,
    ramanujanAdjunctionEnergy, hτ]
  field_simp
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
