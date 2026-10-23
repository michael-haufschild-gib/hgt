import GaloisForLFunctions.RHTower.MobiusSquareResidueShortBilinear
import GaloisForLFunctions.TransHorizonIncidenceMechanics.GlobalRenormalizedDefectSignAtLargeHorizons
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MoebiusResponseWhiteNoiseLaw
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SuccessorReserveHorizonLawAndPrimeDissipation
import GaloisForLFunctions.TransHorizonIncidenceMechanics.BuchstabFermiCovarianceAndQuotientChainBridge

/-!
# Joint Principal Counterterm and High-Product Bilinear Remainder, Cutoff Drift, and Reserve Obstructions

This module establishes the exact algebraic and asymptotic laws governing the short Möbius bilinear
reconstruction up to `N²` and the structural boundaries of the renormalized Bézout–Möbius defect:

1. **Joint Principal Counterterm, Low-Product Sum, and High-Product Remainder
   (`sum_moebius_weight_eq_counterterm_sub_low_sub_high`,
   `shortMobiusBilinearForm_eq_subHorizon_add_transHorizon_sieveSeq`,
   `sum_moebius_transHorizon_eq_neg_transHorizon_sieveSeq_bilinear`,
   `lowProduct_and_highProduct_at_transHorizon_semiprime`)**:
   - The short bilinear form `∑_{a,b ≤ N} μ(a)μ(b) ∑_{k ≤ N²/(ab)} w(abk)` splits into the
     low-product sum (`a * b ≤ N`) and the high-product remainder (`N < a * b`).
   - Grouping the inner factors by the cofactor `m = b * k` identifies the inner sum with the
     truncated sieve response `sieveSeq N moebiusReal m`. Sub-horizon Möbius inversion (`m ≤ N`)
     cancels half of the principal counterterm `2 ∑_{n ≤ N} μ(n) w(n)`, reducing the trans-horizon
     Möbius sum `∑_{N < n ≤ N²} μ(n) w(n)` to `-∑_{a ≤ N} μ(a) ∑_{N < m ≤ N²/a} s_{N,μ}(m) w(am)`.
   - At any trans-horizon semiprime `p * q > N` formed by distinct primes `p, q ≤ N`, the principal
     counterterm vanishes (`0`), the low-product sum contributes `-3` (so `-lowProduct = +3`), and
     the high-product remainder contributes `+2` (so `-highProduct = -2`), proving that only their
     joint signed combination `0 - (-3) - 2 = +1 = μ(pq)` recovers the true Möbius value.

2. **Exact Single-Step Cutoff Drift and Inherited-History Coupling
   (`sieveSeq_succ_horizon_mul_succ_sub_eq`, `sieveRenormalizedPrefixDefect_succ_horizon_sub_eq`,
   `sieveCombinedPrefixDefect_succ_horizon_sub_eq`,
   `moebiusCombinedPrefixDefect_subHorizon_cutoff_drift`,
   `sieveRenormalizedPrefixDefect_moebius_at_succ_horizon_step`)**:
   - Because `gcd(k, k + 1) = 1`, no horizon `N + 1 ≥ 2` divides both `k` and `k + 1`. Thus the
     cutoff step `N ↦ N + 1` of the Bézout successor correlation has zero quadratic `c(N + 1)²`
     diagonal and couples `c(N + 1)` purely to the inherited history `sieveSeq N c` at predecessors
     and successors of multiples of `N + 1`.
   - On `1 ≤ M ≤ N` (`N ≥ 2`), `sieveRenormalizedPrefixDefect` is stationary at `-1` while
     `moebiusCombinedPrefixDefect` drifts by `M * (R_{N+1}(μ) - R_N(μ))`. At `M = N + 1`, advancing
     the cutoff from `N` to `N + 1` shifts `sieveRenormalizedPrefixDefect` by
     `μ(N + 1)² - μ(N + 1) μ(N + 2)`.

3. **Eventual All-Prefix Nonpositivity Coexists with Unbounded Positive Reserve and Diagonal Growth
   (`eventually_all_prefix_renormalized_nonpos_with_unbounded_reserve`)**:
   For all sufficiently large horizons `N`, `sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0`
   holds at every prefix `M`, while simultaneously `sieveSuccessorReserve N moebiusReal ≥ 1 / 576`,
   the reserve budget `M * R_N(μ) ≥ M / 576` grows linearly with `M`, and the diagonal combined
   defect satisfies `moebiusCombinedPrefixDefect N N ≥ N / 576 - 1`.

4. **Sign-Blindness of First-Octave Renormalized Defect Nonpositivity to Scale-Dependent Targets
   (`firstOctaveDefectFunctional_nonpos_of_sq_eq_abs`,
   `firstOctaveDefectFunctional_signBlind_comparison`)**:
   In the first octave `N ≤ M ≤ 2N - 1`, the step inequality `f(k)f(k + 1) - f(k)² ≤ 0` holds for
   every sequence satisfying `f(k)² = |f(k)|`, including the unsigned squarefree indicator `μ(k)²`
   and the constant unit sequence `1`, whose cumulative sums grow without sign cancellation.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Joint Principal Counterterm, Low-Product Sum, and High-Product Bilinear Remainder -/

/-- The principal short Möbius counterterm `2 ∑_{n=1}^N μ(n) w(n)`. -/
def principalMobiusCounterterm (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  2 * ∑ n ∈ Icc 1 N, moebiusReal n * w n

/-- The complete short Möbius bilinear form `∑_{a=1}^N ∑_{b=1}^N μ(a)μ(b) ∑_{k=1}^{⌊N²/(ab)⌋} w(abk)`. -/
def shortMobiusBilinearForm (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
    moebiusReal a * moebiusReal b * ∑ k ∈ Icc 1 (N ^ 2 / (a * b)), w (a * b * k)

/-- The low-product part (`a * b ≤ N`) of the short Möbius bilinear form. -/
def lowProductBilinearSum (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (Icc 1 N ×ˢ Icc 1 N).filter (fun p => p.1 * p.2 ≤ N),
    moebiusReal p.1 * moebiusReal p.2 * ∑ k ∈ Icc 1 (N ^ 2 / (p.1 * p.2)), w (p.1 * p.2 * k)

/-- The high-product remainder (`N < a * b`) of the short Möbius bilinear form. -/
def highProductBilinearRemainder (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (Icc 1 N ×ˢ Icc 1 N).filter (fun p => N < p.1 * p.2),
    moebiusReal p.1 * moebiusReal p.2 * ∑ k ∈ Icc 1 (N ^ 2 / (p.1 * p.2)), w (p.1 * p.2 * k)

/-- Splitting the short Möbius bilinear form into its low-product sum (`a * b ≤ N`) and
high-product remainder (`N < a * b`). -/
theorem shortMobiusBilinearForm_eq_lowProduct_add_highProduct (N : ℕ) (w : ℕ → ℝ) :
    shortMobiusBilinearForm N w =
      lowProductBilinearSum N w + highProductBilinearRemainder N w := by
  unfold shortMobiusBilinearForm lowProductBilinearSum highProductBilinearRemainder
  rw [← Finset.sum_product']
  have hnot : (Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => N < p.1 * p.2) =
      (Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => ¬ (p.1 * p.2 ≤ N)) := by
    ext p
    simp only [mem_filter, not_le]
  rw [hnot, Finset.sum_filter_add_sum_filter_not]

/-- **Joint Principal Counterterm + Low-Product + High-Product Identity:**
For every cutoff `N : ℕ` and weight `w : ℕ → ℝ`, the Möbius sum up to `N²` equals the principal
counterterm minus the low-product bilinear sum and the high-product bilinear remainder. -/
theorem sum_moebius_weight_eq_counterterm_sub_low_sub_high (N : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ Icc 1 (N ^ 2), moebiusReal n * w n) =
      principalMobiusCounterterm N w -
        lowProductBilinearSum N w -
        highProductBilinearRemainder N w := by
  have hcast : ∀ n : ℕ, ((moebius n : ℤ) : ℝ) = moebiusReal n := fun _ => rfl
  have hshort := RHTower.sum_moebius_weight_eq_short_bilinear N w
  simp_rw [hcast] at hshort
  change (∑ n ∈ Icc 1 (N ^ 2), moebiusReal n * w n) =
    principalMobiusCounterterm N w - shortMobiusBilinearForm N w at hshort
  rw [hshort, shortMobiusBilinearForm_eq_lowProduct_add_highProduct]
  ring

/-- Swapping a divisor sum `b ∈ Icc 1 N` with its multiple `m = b * k ∈ Icc 1 X` yields the
`sieveSeq N c`-weighted sum over `m ∈ Icc 1 X`. -/
theorem sum_Icc_mul_sum_div_eq_sum_sieveSeq (N X : ℕ) (c w : ℕ → ℝ) :
    (∑ b ∈ Icc 1 N, c b * ∑ k ∈ Icc 1 (X / b), w (b * k)) =
      ∑ m ∈ Icc 1 X, sieveSeq N c m * w m := by
  have hrhs : (∑ m ∈ Icc 1 X, sieveSeq N c m * w m) =
      ∑ b ∈ Icc 1 N, ∑ m ∈ (Icc 1 X).filter (fun m => b ∣ m), c b * w m := by
    unfold sieveSeq
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm' (t' := Icc 1 N) (s' := fun b => (Icc 1 X).filter (fun m => b ∣ m))]
    intro m b
    simp only [mem_filter, mem_Icc]
    tauto
  rw [hrhs]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hb0 : 0 < b := (mem_Icc.mp hb).1
  rw [sum_Icc_filter_dvd_eq_sum_Icc_div hb0 X (fun m => c b * w m), ← Finset.mul_sum]

/-- **Cofactor / Inherited-History Decomposition of `shortMobiusBilinearForm`:**
Grouping `m = b * k` identifies the inner sum with `sieveSeq N moebiusReal m`. Because
`sieveSeq N moebiusReal m = δ_{m,1}` for `1 ≤ m ≤ N`, the sub-horizon cofactor range `1 ≤ m ≤ N`
contributes `∑_{a=1}^N μ(a) w(a)` (half of the principal counterterm), while `2 ≤ m ≤ N` vanishes. -/
theorem shortMobiusBilinearForm_eq_subHorizon_add_transHorizon_sieveSeq (N : ℕ) (w : ℕ → ℝ) :
    shortMobiusBilinearForm N w =
      (∑ a ∈ Icc 1 N, moebiusReal a * w a) +
        ∑ a ∈ Icc 1 N, moebiusReal a *
          ∑ m ∈ Icc (N + 1) (N ^ 2 / a), sieveSeq N moebiusReal m * w (a * m) := by
  unfold shortMobiusBilinearForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨ha1, haN⟩ := mem_Icc.mp ha
  have hinner :
      (∑ b ∈ Icc 1 N, moebiusReal b * ∑ k ∈ Icc 1 (N ^ 2 / (a * b)), w (a * b * k)) =
        ∑ m ∈ Icc 1 (N ^ 2 / a), sieveSeq N moebiusReal m * w (a * m) := by
    have hdiv : ∀ b : ℕ, N ^ 2 / (a * b) = (N ^ 2 / a) / b :=
      fun b => (Nat.div_div_eq_div_mul (N ^ 2) a b).symm
    simp_rw [hdiv, Nat.mul_assoc]
    exact sum_Icc_mul_sum_div_eq_sum_sieveSeq N (N ^ 2 / a) moebiusReal (fun m => w (a * m))
  have hmul : (∑ b ∈ Icc 1 N,
      moebiusReal a * moebiusReal b * ∑ k ∈ Icc 1 (N ^ 2 / (a * b)), w (a * b * k)) =
      moebiusReal a * ∑ b ∈ Icc 1 N,
        moebiusReal b * ∑ k ∈ Icc 1 (N ^ 2 / (a * b)), w (a * b * k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hmul, hinner]
  have hN_le : N ≤ N ^ 2 / a := by
    rw [Nat.le_div_iff_mul_le ha1]
    nlinarith
  have hsplit : Icc 1 (N ^ 2 / a) = Icc 1 N ∪ Icc (N + 1) (N ^ 2 / a) := by
    ext m; simp only [mem_union, mem_Icc]; omega
  have hdisj : Disjoint (Icc 1 N) (Icc (N + 1) (N ^ 2 / a)) := by
    rw [disjoint_left]; intro m hm1 hm2; simp only [mem_Icc] at hm1 hm2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have hsub : (∑ m ∈ Icc 1 N, sieveSeq N moebiusReal m * w (a * m)) = w a := by
    have h1 : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_rfl, ha1.trans haN⟩
    rw [Finset.sum_eq_single_of_mem 1 h1]
    · rw [sieveSeq_moebiusReal_eq_ite_of_le le_rfl (ha1.trans haN), if_pos rfl, one_mul, mul_one]
    · intro m hm hm1
      obtain ⟨hm_ge, hm_le⟩ := mem_Icc.mp hm
      rw [sieveSeq_moebiusReal_eq_ite_of_le hm_ge hm_le, if_neg hm1, zero_mul]
  rw [hsub]
  ring

/-- **Trans-Horizon Cofactor Identity:**
Canceling the sub-horizon prefix `∑_{n=1}^N μ(n) w(n)` against the reduced principal counterterm
expresses the trans-horizon Möbius sum `∑_{n=N+1}^{N²} μ(n) w(n)` purely in terms of the
trans-horizon inherited-history responses `sieveSeq N moebiusReal m` (`m ≥ N + 1`). -/
theorem sum_moebius_transHorizon_eq_neg_transHorizon_sieveSeq_bilinear (N : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ Icc (N + 1) (N ^ 2), moebiusReal n * w n) =
      -∑ a ∈ Icc 1 N, moebiusReal a *
        ∑ m ∈ Icc (N + 1) (N ^ 2 / a), sieveSeq N moebiusReal m * w (a * m) := by
  have hNN : N ≤ N ^ 2 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · nlinarith
  have hsplit : Icc 1 (N ^ 2) = Icc 1 N ∪ Icc (N + 1) (N ^ 2) := by
    ext n; simp only [mem_union, mem_Icc]; omega
  have hdisj : Disjoint (Icc 1 N) (Icc (N + 1) (N ^ 2)) := by
    rw [disjoint_left]; intro n hn1 hn2; simp only [mem_Icc] at hn1 hn2; omega
  have htot := sum_moebius_weight_eq_counterterm_sub_low_sub_high N w
  have hbilin : principalMobiusCounterterm N w - lowProductBilinearSum N w -
      highProductBilinearRemainder N w =
      principalMobiusCounterterm N w - shortMobiusBilinearForm N w := by
    rw [shortMobiusBilinearForm_eq_lowProduct_add_highProduct]
    ring
  rw [hbilin, shortMobiusBilinearForm_eq_subHorizon_add_transHorizon_sieveSeq,
    principalMobiusCounterterm, hsplit, Finset.sum_union hdisj] at htot
  linarith

/-- Any sub-horizon divisor `a ≤ N` of a trans-horizon semiprime `p * q > N` (`p, q` primes) is
`1`, `p`, or `q`. -/
private theorem dvd_semiprime_of_le_horizon {N p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (haN : a ≤ N) (hgt : N < p * q) (hdvd : a ∣ p * q) :
    a = 1 ∨ a = p ∨ a = q := by
  by_cases hpa : p ∣ a
  · obtain ⟨k, rfl⟩ := hpa
    have hkq : k ∣ q := Nat.dvd_of_mul_dvd_mul_left hp.pos hdvd
    rcases (Nat.dvd_prime hq).mp hkq with rfl | rfl
    · exact Or.inr (Or.inl (mul_one p))
    · omega
  · have hcop : Nat.Coprime a p := (hp.coprime_iff_not_dvd.mpr hpa).symm
    have haq : a ∣ q := hcop.dvd_of_dvd_mul_left hdvd
    rcases (Nat.dvd_prime hq).mp haq with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)

/-- For a divisor pair `(a, b) ∈ Icc 1 N ×ˢ Icc 1 N` of a semiprime `p * q` (`p, q ≤ N` distinct
primes with `N < p * q`), `N < a * b` holds if and only if `(a, b) = (p, q)` or `(a, b) = (q, p)`. -/
private theorem filter_highProduct_dvd_semiprime_eq_pair {N p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpN : p ≤ N) (hqN : q ≤ N) (hgt : N < p * q) :
    ((Icc 1 N ×ˢ Icc 1 N).filter (fun x : ℕ × ℕ => N < x.1 * x.2 ∧ x.1 * x.2 ∣ p * q)) =
      {(p, q), (q, p)} := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_product, mem_Icc, mem_insert, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, habN, hdvd⟩
    have ha_dvd : a ∣ p * q := dvd_trans (dvd_mul_right a b) hdvd
    have hb_dvd : b ∣ p * q := dvd_trans (dvd_mul_left b a) hdvd
    have ha_cases := dvd_semiprime_of_le_horizon hp hq haN hgt ha_dvd
    have hb_cases := dvd_semiprime_of_le_horizon hp hq hbN hgt hb_dvd
    rcases ha_cases with ha_eq | ha_eq | ha_eq <;> subst a
    · omega
    · rcases hb_cases with hb_eq | hb_eq | hb_eq <;> subst b
      · omega
      · exfalso
        have hp_dvd_q : p ∣ q := Nat.dvd_of_mul_dvd_mul_left hp.pos hdvd
        exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hp_dvd_q)
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases hb_cases with hb_eq | hb_eq | hb_eq <;> subst b
      · omega
      · exact Or.inr ⟨rfl, rfl⟩
      · exfalso
        have hq_dvd_p : q ∣ p := by
          rw [mul_comm p q] at hdvd
          exact Nat.dvd_of_mul_dvd_mul_left hq.pos hdvd
        exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hq_dvd_p).symm
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨⟨⟨hp.pos, hpN⟩, ⟨hq.pos, hqN⟩⟩, hgt, dvd_rfl⟩
    · refine ⟨⟨⟨hq.pos, hqN⟩, ⟨hp.pos, hpN⟩⟩, ?_, ?_⟩
      · rwa [mul_comm]
      · rw [mul_comm]

/-- **Trans-Horizon Semiprime Parity Obstruction (`lowProduct_and_highProduct_at_transHorizon_semiprime`):**
For any distinct primes `p, q ≤ N` with `N < p * q`, let `w = δ_{p*q}` be the point-mass weight at
the trans-horizon semiprime `p * q ≤ N²`. Then:
1. The principal counterterm vanishes (`principalMobiusCounterterm N w = 0`),
2. The low-product bilinear sum equals `-3` (so `-lowProductBilinearSum N w = +3`, overcounting
   `μ(p * q) = +1` by `+2`),
3. The high-product bilinear remainder equals `+2` (so `-highProductBilinearRemainder N w = -2`),
4. And only their joint signed combination `0 - (-3) - 2 = +1 = μ(p * q)` recovers the true sum. -/
theorem lowProduct_and_highProduct_at_transHorizon_semiprime {N p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpN : p ≤ N) (hqN : q ≤ N) (hgt : N < p * q) :
    let w : ℕ → ℝ := fun n => if n = p * q then 1 else 0
    principalMobiusCounterterm N w = 0 ∧
      lowProductBilinearSum N w = -3 ∧
      highProductBilinearRemainder N w = 2 ∧
      (∑ n ∈ Icc 1 (N ^ 2), moebiusReal n * w n) = 1 := by
  intro w
  have hpq_pos : 1 ≤ p * q := Nat.mul_pos hp.pos hq.pos
  have hpq_le : p * q ≤ N ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul hpN hqN
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hμp : moebiusReal p = -1 := by
    unfold moebiusReal; rw [moebius_apply_prime hp]; norm_num
  have hμq : moebiusReal q = -1 := by
    unfold moebiusReal; rw [moebius_apply_prime hq]; norm_num
  have hμpq : moebiusReal (p * q) = 1 := by
    unfold moebiusReal
    rw [isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_apply_prime hp,
      moebius_apply_prime hq]
    norm_num
  have htot : (∑ n ∈ Icc 1 (N ^ 2), moebiusReal n * w n) = 1 := by
    rw [Finset.sum_eq_single_of_mem (p * q) (mem_Icc.mpr ⟨hpq_pos, hpq_le⟩)]
    · simp [w, hμpq]
    · intro n _ hne
      simp [w, hne]
  have hprin : principalMobiusCounterterm N w = 0 := by
    unfold principalMobiusCounterterm
    rw [Finset.sum_eq_zero]
    · ring
    · intro n hn
      have hnN : n ≤ N := (mem_Icc.mp hn).2
      have hne : n ≠ p * q := by omega
      simp [w, hne]
  have hhigh : highProductBilinearRemainder N w = 2 := by
    unfold highProductBilinearRemainder
    have hinner : ∀ x ∈ (Icc 1 N ×ˢ Icc 1 N).filter (fun x : ℕ × ℕ => N < x.1 * x.2),
        moebiusReal x.1 * moebiusReal x.2 *
          (∑ k ∈ Icc 1 (N ^ 2 / (x.1 * x.2)), w (x.1 * x.2 * k)) =
        if x.1 * x.2 ∣ p * q then moebiusReal x.1 * moebiusReal x.2 else 0 := by
      intro x hx
      have hx_pos : 0 < x.1 * x.2 := by
        have := (mem_filter.mp hx).1
        simp only [mem_product, mem_Icc] at this
        exact Nat.mul_pos this.1.1 this.2.1
      by_cases hdvd : x.1 * x.2 ∣ p * q
      · rw [if_pos hdvd]
        obtain ⟨k₀, hk₀⟩ := hdvd
        have hk₀_pos : 1 ≤ k₀ := by
          rcases Nat.eq_zero_or_pos k₀ with rfl | hpos
          · rw [mul_zero] at hk₀
            omega
          · exact hpos
        have hk₀_le : k₀ ≤ N ^ 2 / (x.1 * x.2) := by
          rw [Nat.le_div_iff_mul_le hx_pos, mul_comm, ← hk₀]
          exact hpq_le
        have hsum_k : (∑ k ∈ Icc 1 (N ^ 2 / (x.1 * x.2)), w (x.1 * x.2 * k)) = 1 := by
          rw [Finset.sum_eq_single_of_mem k₀ (mem_Icc.mpr ⟨hk₀_pos, hk₀_le⟩)]
          · simp [w, hk₀.symm]
          · intro k _ hkne
            have hmul_ne : x.1 * x.2 * k ≠ p * q := by
              intro heq
              exact hkne (Nat.eq_of_mul_eq_mul_left hx_pos (heq.trans hk₀))
            simp [w, hmul_ne]
        rw [hsum_k, mul_one]
      · rw [if_neg hdvd]
        have hsum_k : (∑ k ∈ Icc 1 (N ^ 2 / (x.1 * x.2)), w (x.1 * x.2 * k)) = 0 := by
          refine Finset.sum_eq_zero fun k _ => ?_
          have hmul_ne : x.1 * x.2 * k ≠ p * q := fun heq => hdvd ⟨k, heq.symm⟩
          simp [w, hmul_ne]
        rw [hsum_k, mul_zero]
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, filter_filter,
      filter_highProduct_dvd_semiprime_eq_pair hp hq hpq hpN hqN hgt]
    have hpair_ne : (p, q) ≠ (q, p) := fun h => hpq (Prod.mk.inj h).1
    rw [Finset.sum_pair hpair_ne]
    simp [hμp, hμq]
    ring
  have hrel := sum_moebius_weight_eq_counterterm_sub_low_sub_high N w
  exact ⟨hprin, by linarith, hhigh, htot⟩

/-! ## §2. Exact Single-Step Cutoff Drift and Inherited-History Coupling (`N ↦ N + 1`) -/

/-- No integer `m ≥ 2` divides two consecutive integers `k` and `k + 1`. -/
theorem not_dvd_self_and_succ_of_two_le {m : ℕ} (hm : 2 ≤ m) (k : ℕ) :
    ¬ (m ∣ k ∧ m ∣ (k + 1)) := by
  rintro ⟨h1, h2⟩
  have hcop : Nat.Coprime m m := coprime_of_dvd_self_succ h1 h2
  rw [Nat.Coprime, Nat.gcd_self] at hcop
  omega

/-- **Pointwise Cutoff-Step Identity for Successor Products (`sieveSeq_succ_horizon_mul_succ_sub_eq`):**
For every `N ≥ 1`, weight `c : ℕ → ℝ`, and `k : ℕ`, because `N + 1 ≥ 2` cannot divide both `k` and
`k + 1`, the quadratic `c (N + 1) ^ 2` term vanishes identically and the cutoff step of
`sieveSeq N c k * sieveSeq N c (k + 1)` is purely linear in `c (N + 1)`. -/
theorem sieveSeq_succ_horizon_mul_succ_sub_eq {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (k : ℕ) :
    sieveSeq (N + 1) c k * sieveSeq (N + 1) c (k + 1) -
      sieveSeq N c k * sieveSeq N c (k + 1) =
      c (N + 1) * ((if N + 1 ∣ k then sieveSeq N c (k + 1) else 0) +
        (if N + 1 ∣ (k + 1) then sieveSeq N c k else 0)) := by
  rw [sieveSeq_succ_horizon_eq_add_ite N c k, sieveSeq_succ_horizon_eq_add_ite N c (k + 1)]
  have hnot := not_dvd_self_and_succ_of_two_le (by omega : 2 ≤ N + 1) k
  by_cases h1 : N + 1 ∣ k
  · have h2 : ¬ (N + 1 ∣ (k + 1)) := fun h => hnot ⟨h1, h⟩
    simp only [h1, h2, ↓reduceIte]
    ring
  · simp only [h1, ↓reduceIte]
    split_ifs <;> ring

/-- **Single-Step Cutoff Drift of Successor Correlation Sums
(`sum_sieveSeq_mul_succ_horizon_sub_eq`):**
For every `N ≥ 1`, prefix `M : ℕ`, and weight `c : ℕ → ℝ`, advancing the sieve cutoff from `N` to
`N + 1` couples `c (N + 1)` linearly to the inherited history `sieveSeq N c` at successors and
predecessors of multiples of `N + 1`. -/
theorem sum_sieveSeq_mul_succ_horizon_sub_eq {N : ℕ} (hN : 1 ≤ N)
    (M : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Icc 1 M, sieveSeq (N + 1) c k * sieveSeq (N + 1) c (k + 1)) -
      (∑ k ∈ Icc 1 M, sieveSeq N c k * sieveSeq N c (k + 1)) =
      c (N + 1) * ∑ k ∈ Icc 1 M,
        ((if N + 1 ∣ k then sieveSeq N c (k + 1) else 0) +
          (if N + 1 ∣ (k + 1) then sieveSeq N c k else 0)) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact sieveSeq_succ_horizon_mul_succ_sub_eq hN c k

/-- **Single-Step Cutoff Drift of `sieveRenormalizedPrefixDefect`
(`sieveRenormalizedPrefixDefect_succ_horizon_sub_eq`):**
For every `N ≥ 1`, prefix `M : ℕ`, and weight `c : ℕ → ℝ`, the cutoff drift of
`sieveRenormalizedPrefixDefect` across `N ↦ N + 1` decomposes into the negative diagonal jump
`-c(N + 1)² ⌊M / (N + 1)⌋` plus the linear bilinear coupling to the inherited history `sieveSeq N c`. -/
theorem sieveRenormalizedPrefixDefect_succ_horizon_sub_eq {N : ℕ} (hN : 1 ≤ N)
    (M : ℕ) (c : ℕ → ℝ) :
    sieveRenormalizedPrefixDefect (N + 1) M c - sieveRenormalizedPrefixDefect N M c =
      -(c (N + 1) ^ (2 : ℕ) * ((M / (N + 1) : ℕ) : ℝ)) -
        2 * c (N + 1) * (∑ j ∈ Icc 1 (M / (N + 1)), sieveSeq N c ((N + 1) * j)) +
        c (N + 1) * ∑ k ∈ Icc 1 M,
          ((if N + 1 ∣ k then sieveSeq N c (k + 1) else 0) +
            (if N + 1 ∣ (k + 1) then sieveSeq N c k else 0)) := by
  rw [sieveRenormalizedPrefixDefect_eq_succ_sub_sq, sieveRenormalizedPrefixDefect_eq_succ_sub_sq]
  have hE := sieveL2PrefixEnergy_succ_horizon_sub_eq N M c
  unfold sieveL2PrefixEnergy at hE
  have hC := sum_sieveSeq_mul_succ_horizon_sub_eq hN M c
  linarith

/-- **Single-Step Cutoff Drift of `sieveCombinedPrefixDefect`
(`sieveCombinedPrefixDefect_succ_horizon_sub_eq`):**
For every `N, M : ℕ` and weight `c : ℕ → ℝ`, the cutoff drift of `sieveCombinedPrefixDefect`
equals the cutoff drift of `sieveRenormalizedPrefixDefect` plus `M` times the successor-reserve step. -/
theorem sieveCombinedPrefixDefect_succ_horizon_sub_eq (N M : ℕ) (c : ℕ → ℝ) :
    sieveCombinedPrefixDefect (N + 1) M c - sieveCombinedPrefixDefect N M c =
      (sieveRenormalizedPrefixDefect (N + 1) M c - sieveRenormalizedPrefixDefect N M c) +
        (M : ℝ) * (sieveSuccessorReserve (N + 1) c - sieveSuccessorReserve N c) := by
  unfold sieveRenormalizedPrefixDefect
  ring

/-- **Sub-Horizon Cutoff Drift of `moebiusCombinedPrefixDefect`
(`moebiusCombinedPrefixDefect_subHorizon_cutoff_drift`):**
For `N ≥ 2` and `1 ≤ M ≤ N`, `sieveRenormalizedPrefixDefect` is stationary at `-1` across `N ↦ N + 1`
while `moebiusCombinedPrefixDefect` drifts by `M * (sieveSuccessorReserve (N + 1) μ - sieveSuccessorReserve N μ)`. -/
theorem moebiusCombinedPrefixDefect_subHorizon_cutoff_drift {N M : ℕ}
    (hN : 2 ≤ N) (hM1 : 1 ≤ M) (hMN : M ≤ N) :
    moebiusCombinedPrefixDefect (N + 1) M - moebiusCombinedPrefixDefect N M =
      (M : ℝ) * (sieveSuccessorReserve (N + 1) moebiusReal -
        sieveSuccessorReserve N moebiusReal) ∧
    sieveRenormalizedPrefixDefect (N + 1) M moebiusReal -
      sieveRenormalizedPrefixDefect N M moebiusReal = 0 := by
  have h1 := moebiusCombinedPrefixDefect_eq (by omega : 2 ≤ N + 1) hM1 (by omega : M ≤ N + 1)
  have h2 := moebiusCombinedPrefixDefect_eq hN hM1 hMN
  constructor
  · linarith
  · unfold sieveRenormalizedPrefixDefect
    rw [sieveCombinedPrefixDefect_moebiusReal_eq, sieveCombinedPrefixDefect_moebiusReal_eq, h1, h2]
    ring

/-- **Cutoff Jump of `sieveRenormalizedPrefixDefect` at the Next Horizon Node `M = N + 1`
(`sieveRenormalizedPrefixDefect_moebius_at_succ_horizon_step`):**
For `N ≥ 2`, advancing the sieve cutoff from `N` to `N + 1` at prefix `M = N + 1` shifts
`sieveRenormalizedPrefixDefect` from `-1 + μ(N + 1) μ(N + 2) - μ(N + 1)²` to `-1`, producing the
cutoff jump `μ(N + 1)² - μ(N + 1) μ(N + 2) ≥ 0`. -/
theorem sieveRenormalizedPrefixDefect_moebius_at_succ_horizon_step {N : ℕ} (hN : 2 ≤ N) :
    sieveRenormalizedPrefixDefect (N + 1) (N + 1) moebiusReal -
      sieveRenormalizedPrefixDefect N (N + 1) moebiusReal =
      moebiusReal (N + 1) ^ (2 : ℕ) - moebiusReal (N + 1) * moebiusReal (N + 2) ∧
    0 ≤ sieveRenormalizedPrefixDefect (N + 1) (N + 1) moebiusReal -
      sieveRenormalizedPrefixDefect N (N + 1) moebiusReal := by
  have h1 : sieveRenormalizedPrefixDefect (N + 1) (N + 1) moebiusReal = -1 := by
    unfold sieveRenormalizedPrefixDefect
    rw [sieveCombinedPrefixDefect_moebiusReal_eq,
      moebiusCombinedPrefixDefect_eq (by omega : 2 ≤ N + 1) (by omega) le_rfl]
    ring
  have h2 : sieveRenormalizedPrefixDefect N (N + 1) moebiusReal =
      -1 + (moebiusReal (N + 1) * moebiusReal (N + 2) - moebiusReal (N + 1) ^ (2 : ℕ)) := by
    unfold sieveRenormalizedPrefixDefect
    rw [sieveCombinedPrefixDefect_moebiusReal_eq,
      moebiusCombinedPrefixDefect_first_octave_eq hN (by omega) (by omega),
      Finset.Icc_self, Finset.sum_singleton]
    ring
  have hdiff : sieveRenormalizedPrefixDefect (N + 1) (N + 1) moebiusReal -
      sieveRenormalizedPrefixDefect N (N + 1) moebiusReal =
      moebiusReal (N + 1) ^ (2 : ℕ) - moebiusReal (N + 1) * moebiusReal (N + 2) := by
    rw [h1, h2]
    ring
  refine ⟨hdiff, ?_⟩
  rw [hdiff]
  have hb := (moebiusReal_mul_succ_sub_sq_bounds (N + 1)).2
  linarith

/-! ## §3. Eventual All-Prefix Nonpositivity Coexists with Unbounded Reserve & Diagonal Growth -/

/-- **Eventual All-Prefix Nonpositivity Does Not Bound Successor Reserve or Diagonal Defect
(`eventually_all_prefix_renormalized_nonpos_with_unbounded_reserve`):**
For all sufficiently large horizons `N`:
1. `sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0` for **every** prefix `M : ℕ`,
2. `1 / 576 ≤ sieveSuccessorReserve N moebiusReal` and
   `sievePrimeTailMass N ≤ sieveSuccessorReserve N moebiusReal`,
3. `(M : ℝ) / 576 ≤ (M : ℝ) * sieveSuccessorReserve N moebiusReal` for every `M : ℕ`,
4. `(N : ℝ) / 576 - 1 ≤ moebiusCombinedPrefixDefect N N` (linear diagonal growth), and
5. At every factorial return time `M = q * N!`, `sieveCombinedPrefixDefect = 0` while
   `sieveRenormalizedPrefixDefect ≤ -(q * N!) / 576`. -/
theorem eventually_all_prefix_renormalized_nonpos_with_unbounded_reserve :
    ∀ᶠ N : ℕ in atTop,
      (∀ M : ℕ, sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0) ∧
      1 / 576 ≤ sieveSuccessorReserve N moebiusReal ∧
      sievePrimeTailMass N ≤ sieveSuccessorReserve N moebiusReal ∧
      (∀ M : ℕ, (M : ℝ) / 576 ≤ (M : ℝ) * sieveSuccessorReserve N moebiusReal) ∧
      (N : ℝ) / 576 - 1 ≤ moebiusCombinedPrefixDefect N N ∧
      (∀ q : ℕ,
        sieveCombinedPrefixDefect N (q * N.factorial) moebiusReal = 0 ∧
        sieveRenormalizedPrefixDefect N (q * N.factorial) moebiusReal ≤
          -((q * N.factorial : ℕ) : ℝ) / 576) := by
  filter_upwards [eventually_moebius_renormalizedDefect_nonpos_all,
    eventually_sieveSuccessorReserve_moebius_ge,
    eventually_ge_atTop 2] with N hnonpos hres hN2
  have htail : sievePrimeTailMass N ≤ sieveSuccessorReserve N moebiusReal :=
    sievePrimeTailMass_le_moebius_successorReserve (by omega)
  have hM_res : ∀ M : ℕ, (M : ℝ) / 576 ≤ (M : ℝ) * sieveSuccessorReserve N moebiusReal := by
    intro M
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hmul := mul_le_mul_of_nonneg_left hres hM0
    linarith
  have hdiag : (N : ℝ) / 576 - 1 ≤ moebiusCombinedPrefixDefect N N := by
    have hcomb := moebiusCombinedPrefixDefect_eq hN2 (by omega) le_rfl
    have hN_res := hM_res N
    linarith
  refine ⟨hnonpos, hres, htail, hM_res, hdiag, fun q => ?_⟩
  have hperiod : ∀ d ∈ Icc 1 N, d ∣ q * N.factorial := fun d hd =>
    dvd_mul_of_dvd_right (Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2) q
  obtain ⟨hcomb0, hren_eq⟩ := sieveCombinedPrefixDefect_eq_zero_of_common_return moebiusReal hperiod
  have hq_res := hM_res (q * N.factorial)
  exact ⟨hcomb0, by linarith⟩

/-! ## §4. Sign-Blindness of First-Octave Renormalized Defect Nonpositivity to Cumulative Drift -/

/-- The first-octave renormalized defect functional
`-1 + ∑_{k=N+1}^M (f(k) f(k + 1) - f(k)²)` for an arbitrary sequence `f : ℕ → ℝ`. -/
def firstOctaveDefectFunctional (N M : ℕ) (f : ℕ → ℝ) : ℝ :=
  -1 + ∑ k ∈ Icc (N + 1) M, (f k * f (k + 1) - f k ^ (2 : ℕ))

/-- On the first trans-horizon octave `N ≤ M ≤ 2N - 1` (`N ≥ 2`),
`sieveRenormalizedPrefixDefect N M moebiusReal` coincides with
`firstOctaveDefectFunctional N M moebiusReal`. -/
theorem sieveRenormalizedPrefixDefect_moebius_eq_firstOctaveDefectFunctional {N M : ℕ}
    (hN : 2 ≤ N) (hM1 : N ≤ M) (hM2 : M + 1 ≤ 2 * N) :
    sieveRenormalizedPrefixDefect N M moebiusReal =
      firstOctaveDefectFunctional N M moebiusReal := by
  unfold sieveRenormalizedPrefixDefect firstOctaveDefectFunctional
  rw [sieveCombinedPrefixDefect_moebiusReal_eq,
    moebiusCombinedPrefixDefect_first_octave_eq hN hM1 hM2]
  ring

/-- For any real numbers `a, b` with `a² = |a|` (`a ∈ {-1, 0, 1}`) and `|b| ≤ 1`,
`a * b - a² ≤ 0` regardless of the signs of `a` and `b`. -/
theorem step_defect_nonpos_of_sq_eq_abs {a b : ℝ} (ha : a ^ (2 : ℕ) = |a|) (hb : |b| ≤ 1) :
    a * b - a ^ (2 : ℕ) ≤ 0 := by
  have hprod : a * b ≤ |a| * |b| := by
    rw [← abs_mul]
    exact le_abs_self (a * b)
  have hle : |a| * |b| ≤ |a| * 1 :=
    mul_le_mul_of_nonneg_left hb (abs_nonneg a)
  linarith

/-- **Universal First-Octave Nonpositivity for `{−1, 0, 1}`-Valued Sequences
(`firstOctaveDefectFunctional_nonpos_of_sq_eq_abs`):**
For **every** sequence `f : ℕ → ℝ` satisfying `f(k)² = |f(k)|` (hence `|f(k)| ≤ 1`),
`firstOctaveDefectFunctional N M f ≤ -1` holds at every `N, M : ℕ` regardless of whether the
cumulative sum `∑_{k=N+1}^M f(k)` cancels or drifts linearly. -/
theorem firstOctaveDefectFunctional_nonpos_of_sq_eq_abs (N M : ℕ) {f : ℕ → ℝ}
    (hf : ∀ k : ℕ, f k ^ (2 : ℕ) = |f k|) :
    firstOctaveDefectFunctional N M f ≤ -1 := by
  unfold firstOctaveDefectFunctional
  have hle_one : ∀ k : ℕ, |f k| ≤ 1 := by
    intro k
    have hk := hf k
    have h0 : 0 ≤ |f k| := abs_nonneg (f k)
    have hsq : |f k| ^ (2 : ℕ) = |f k| := by rw [sq_abs, hk]
    nlinarith [sq_nonneg (|f k| - 1)]
  have hsum : ∑ k ∈ Icc (N + 1) M, (f k * f (k + 1) - f k ^ (2 : ℕ)) ≤ 0 :=
    Finset.sum_nonpos fun k _ => step_defect_nonpos_of_sq_eq_abs (hf k) (hle_one (k + 1))
  linarith

/-- **Sign-Blindness of the First-Octave Defect to Cumulative Mertens Targets
(`firstOctaveDefectFunctional_signBlind_comparison`):**
For every `N ≤ M`, the signed Möbius sequence `moebiusReal`, its unsigned squarefree indicator
`fun k => moebiusReal k ^ 2`, and the constant positive sequence `fun _ => 1` all satisfy
`firstOctaveDefectFunctional N M f ≤ -1`, while the cumulative sum of the unsigned squarefree
indicator dominates `|∑_{k=N+1}^M μ(k)|` and the constant sequence has cumulative sum `M - N`. -/
theorem firstOctaveDefectFunctional_signBlind_comparison {N M : ℕ} (hNM : N ≤ M) :
    firstOctaveDefectFunctional N M moebiusReal ≤ -1 ∧
      firstOctaveDefectFunctional N M (fun k => moebiusReal k ^ (2 : ℕ)) ≤ -1 ∧
      firstOctaveDefectFunctional N M (fun _ => (1 : ℝ)) = -1 ∧
      |∑ k ∈ Icc (N + 1) M, moebiusReal k| ≤
        ∑ k ∈ Icc (N + 1) M, moebiusReal k ^ (2 : ℕ) ∧
      (∑ _k ∈ Icc (N + 1) M, (1 : ℝ)) = ((M - N : ℕ) : ℝ) := by
  have hμ_sq_abs : ∀ k : ℕ, moebiusReal k ^ (2 : ℕ) = |moebiusReal k| := by
    intro k
    unfold moebiusReal
    rcases ArithmeticFunction.moebius_eq_or k with h0 | h1 | hm1
    · rw [h0]; norm_num
    · rw [h1]; norm_num
    · rw [hm1]; norm_num
  have hsqf_sq_abs : ∀ k : ℕ, (moebiusReal k ^ (2 : ℕ)) ^ (2 : ℕ) = |moebiusReal k ^ (2 : ℕ)| := by
    intro k
    rw [hμ_sq_abs k, abs_abs]
    unfold moebiusReal
    rcases ArithmeticFunction.moebius_eq_or k with h0 | h1 | hm1
    · rw [h0]; norm_num
    · rw [h1]; norm_num
    · rw [hm1]; norm_num
  refine ⟨firstOctaveDefectFunctional_nonpos_of_sq_eq_abs N M hμ_sq_abs,
    firstOctaveDefectFunctional_nonpos_of_sq_eq_abs N M hsqf_sq_abs, ?_, ?_, ?_⟩
  · unfold firstOctaveDefectFunctional
    simp
  · refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [hμ_sq_abs k]
  · simp [Nat.card_Icc, show M + 1 - (N + 1) = M - N by omega]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
