import GaloisForLFunctions.BezoutValuationIncidence.CofinalLinearWindowMobiusEnergyAndDefectBounds
import GaloisForLFunctions.BezoutValuationIncidence.UniformCofinalMobiusPrefixDiscrepancy
import GaloisForLFunctions.RHTower.Sieve.TypeIICoefficientEnergy

/-!
# Vaughan Type-II Short-Side Coefficients and All-Horizon Möbius `L²` Energy

This module establishes the exact two-way algebraic and analytic bridge between the literal
truncated Möbius divisor sums `sieveSeq N moebiusReal` studied in `BezoutValuationIncidence` and
`TransHorizonIncidenceMechanics` and the Vaughan Type-II short-side coefficients
`RHTower.Sieve.typeIIShort N = 1 - ζ * truncAF μ N` studied in `RHTower/Sieve/`:

1. **Exact Pointwise Dictionary (`zeta_mul_truncAF_moebius_eq_sieveSeq`,
   `typeIIShort_eq_ite_sub_sieveSeq`, `typeIIShort_eq_neg_sieveSeq_of_two_le`):**
   For every cutoff `N : ℕ` and every `k ≥ 1`,
   `((zeta : ArithmeticFunction ℝ) * truncAF (moebius : ArithmeticFunction ℝ) N) k = sieveSeq N moebiusReal k`
   and `typeIIShort N k = (if k = 1 then 1 else 0) - sieveSeq N moebiusReal k`. In particular, for
   all `k ≥ 2`, `typeIIShort N k = -sieveSeq N moebiusReal k` and
   `(typeIIShort N k)^2 = (sieveSeq N moebiusReal k)^2`.

2. **Exact Prefix `L²` Energy Identity (`sieveL2PrefixEnergy_moebiusReal_eq_one_add_sum_typeIIShort_sq`):**
   For all `N ≥ 1` and `M ≥ 1`, the prefix `L²` energy `sieveL2PrefixEnergy N M moebiusReal` is
   identically `1` plus the Vaughan Type-II short-side coefficient energy
   `∑ m ∈ Finset.Icc 1 M, ‖((typeIIShort N m : ℝ) : ℂ)‖ ^ 2`.

3. **Two-Way Analytic Energy Transfer:**
   - **From `RHTower.Sieve` to `BezoutValuationIncidence` (All-Horizon `L²`, Gradient, and Defect Bounds):**
     Using `sum_card_divisors_sq_le` and `sum_typeIIShort_sq_le`, we obtain unconditional upper bounds
     on `sieveL2PrefixEnergy N M moebiusReal`, on the unsigned Möbius gradient energy, and on
     `|sieveRenormalizedPrefixDefect N M moebiusReal|` valid across **all** horizons `N, M` with no
     linear-window restriction `M ≤ (B + 1) * N`.
   - **From `BezoutValuationIncidence` to `RHTower.Sieve` (Log-Free Linear-Window Type-II Short Energy):**
     Using complementary-quotient compression (`abs_sieveSeq_moebiusReal_le_band_width`), on every
     linear horizon window `L ≤ (B + 1) * V` (`V, B ≥ 1`), the Vaughan Type-II short-side coefficient
     energy satisfies `∑ m ∈ Finset.Icc 1 L, ‖((typeIIShort V m : ℝ) : ℂ)‖ ^ 2 ≤ B^2 * (L - V)`,
     removing the `invSum L ^ 3` (`(log L)^3`) factor of `sum_typeIIShort_sq_le` on linear windows.

4. **Möbius Vaughan Identity and Trans-Horizon Quotient-Window Decomposition
   (`moebius_vaughan_identity`, `sum_Ioc_moebiusReal_eq_vaughan_typeI_add_typeII`):**
   Decomposes `moebius : ArithmeticFunction ℝ` and each trans-horizon quotient window
   `∑ d ∈ Finset.Ioc N (M / q), moebiusReal d` of `sum_sieveSeq_moebiusReal_eq_one_sub_quotient_windows`
   into explicit Type-I and Type-II bilinear sums.
-/

open Finset Filter ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open RHTower RHTower.Sieve
open scoped BigOperators Topology

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Pointwise Bridge Between `truncAF`, `typeIIShort`, and `sieveSeq N moebiusReal` -/

/-- The arithmetic-function truncation `truncAF (moebius : ArithmeticFunction ℝ) N` agrees
pointwise with the cutoff indicator of `moebiusReal`. -/
theorem truncAF_moebius_eq_ite_moebiusReal (N n : ℕ) :
    truncAF (moebius : ArithmeticFunction ℝ) N n = if n ≤ N then moebiusReal n else 0 := by
  rw [truncAF_apply]
  rfl

/-- For every `k ≥ 1`, Dirichlet convolution of `zeta` with `truncAF moebius N` is literally
`sieveSeq N moebiusReal k`. -/
theorem zeta_mul_truncAF_moebius_eq_sieveSeq (N : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ((zeta : ArithmeticFunction ℝ) * truncAF (moebius : ArithmeticFunction ℝ) N) k =
      sieveSeq N moebiusReal k := by
  classical
  rw [coe_zeta_mul_apply]
  unfold sieveSeq
  rw [filter_dvd_Icc_eq_divisors_filter_le N hk, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [truncAF_moebius_eq_ite_moebiusReal]

/-- For every `k ≥ 1`, the Vaughan Type-II short-side coefficient `typeIIShort N k` equals
`(if k = 1 then 1 else 0) - sieveSeq N moebiusReal k`. -/
theorem typeIIShort_eq_ite_sub_sieveSeq (N : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    typeIIShort N k = (if k = 1 then 1 else 0) - sieveSeq N moebiusReal k := by
  change (1 : ArithmeticFunction ℝ) k -
      ((zeta : ArithmeticFunction ℝ) * truncAF (moebius : ArithmeticFunction ℝ) N) k = _
  rw [ArithmeticFunction.one_apply, zeta_mul_truncAF_moebius_eq_sieveSeq N hk]

/-- For every `k ≥ 2`, `typeIIShort N k = -sieveSeq N moebiusReal k`. -/
theorem typeIIShort_eq_neg_sieveSeq_of_two_le (N : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    typeIIShort N k = -sieveSeq N moebiusReal k := by
  rw [typeIIShort_eq_ite_sub_sieveSeq N (by omega : 1 ≤ k), if_neg (by omega : k ≠ 1), zero_sub]

/-- For every `k ≥ 2`, `(typeIIShort N k)^2 = (sieveSeq N moebiusReal k)^2`. -/
theorem typeIIShort_sq_eq_sieveSeq_sq_of_two_le (N : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    (typeIIShort N k) ^ (2 : ℕ) = (sieveSeq N moebiusReal k) ^ (2 : ℕ) := by
  rw [typeIIShort_eq_neg_sieveSeq_of_two_le N hk, neg_sq]

/-- Sub-horizon vanishing of `typeIIShort`: for `1 ≤ k ≤ N`, `typeIIShort N k = 0`. -/
theorem typeIIShort_apply_eq_zero_of_le {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    typeIIShort N k = 0 :=
  one_sub_zeta_mul_truncAF_moebius_apply_eq_zero hk hkN

/-! ## §2. Exact Prefix `L²` Energy Identity and Two-Way Analytic Bounds -/

/-- **Exact Prefix `L²` Energy Identity (`sieveL2PrefixEnergy_moebiusReal_eq_one_add_sum_typeIIShort_sq`):**
For every `N ≥ 1` and `M ≥ 1`, `sieveL2PrefixEnergy N M moebiusReal` equals `1` plus the Vaughan
Type-II short-side coefficient energy on `[1, M]`. -/
theorem sieveL2PrefixEnergy_moebiusReal_eq_one_add_sum_typeIIShort_sq {N M : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    sieveL2PrefixEnergy N M moebiusReal =
      1 + ∑ m ∈ Finset.Icc 1 M, ‖((typeIIShort N m : ℝ) : ℂ)‖ ^ (2 : ℕ) := by
  unfold sieveL2PrefixEnergy
  have hsplit : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : (1 : ℕ) ∉ Finset.Icc 2 M := by
    simp only [Finset.mem_Icc]
    omega
  rw [hsplit, Finset.sum_insert hnot, Finset.sum_insert hnot]
  have hs1 : sieveSeq N moebiusReal 1 = 1 := by
    rw [sieveSeq_moebiusReal_eq_ite_of_le le_rfl hN, if_pos rfl]
  have ht1 : typeIIShort N 1 = 0 := typeIIShort_apply_eq_zero_of_le le_rfl hN
  have hrest :
      (∑ m ∈ Finset.Icc 2 M, sieveSeq N moebiusReal m ^ (2 : ℕ)) =
        ∑ m ∈ Finset.Icc 2 M, ‖((typeIIShort N m : ℝ) : ℂ)‖ ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm2, _⟩ := Finset.mem_Icc.mp hm
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs,
      typeIIShort_sq_eq_sieveSeq_sq_of_two_le N hm2]
  rw [hs1, ht1, hrest]
  simp

/-- The Vaughan Type-II short-side coefficient energy on `[1, L]` is supported strictly above `V`
and equals `∑ m ∈ Finset.Ioc V L, (sieveSeq V moebiusReal m)^2`. -/
theorem sum_typeIIShort_sq_eq_sum_Ioc_sieveSeq_sq {V L : ℕ} (hV : 1 ≤ V) :
    (∑ m ∈ Finset.Icc 1 L, ‖((typeIIShort V m : ℝ) : ℂ)‖ ^ (2 : ℕ)) =
      ∑ m ∈ Finset.Ioc V L, (sieveSeq V moebiusReal m) ^ (2 : ℕ) := by
  by_cases hVL : V ≤ L
  · have hsplit : Finset.Icc 1 L = Finset.Icc 1 V ∪ Finset.Ioc V L := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Finset.Icc 1 V) (Finset.Ioc V L) := by
      rw [Finset.disjoint_left]
      intro m hm1 hm2
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at hm1 hm2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hzero : (∑ m ∈ Finset.Icc 1 V, ‖((typeIIShort V m : ℝ) : ℂ)‖ ^ (2 : ℕ)) = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      obtain ⟨hm1, hmV⟩ := Finset.mem_Icc.mp hm
      rw [typeIIShort_apply_eq_zero_of_le hm1 hmV]
      simp
    rw [hzero, zero_add]
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hmV, _⟩ := Finset.mem_Ioc.mp hm
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs,
      typeIIShort_sq_eq_sieveSeq_sq_of_two_le V (by omega : 2 ≤ m)]
  · have hempty : Finset.Ioc V L = ∅ := by
      ext m
      simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]
      omega
    rw [hempty, Finset.sum_empty]
    refine Finset.sum_eq_zero fun m hm => ?_
    obtain ⟨hm1, hmL⟩ := Finset.mem_Icc.mp hm
    rw [typeIIShort_apply_eq_zero_of_le hm1 (by omega : m ≤ V)]
    simp

/-- **Log-Free Linear-Window Bound on Vaughan Type-II Short-Side Energy
(`sum_typeIIShort_sq_le_band_width_sq`):**
For every `V, B ≥ 1` and `L ≤ (B + 1) * V`, complementary-quotient compression bounds the Vaughan
Type-II short-side coefficient energy by `B^2 * (L - V)`, eliminating the `invSum L ^ 3` factor of
`sum_typeIIShort_sq_le` on every linear horizon window. -/
theorem sum_typeIIShort_sq_le_band_width_sq {V B L : ℕ}
    (hV : 1 ≤ V) (hB : 1 ≤ B) (hhi : L ≤ (B + 1) * V) :
    (∑ m ∈ Finset.Icc 1 L, ‖((typeIIShort V m : ℝ) : ℂ)‖ ^ (2 : ℕ)) ≤
      (B : ℝ) ^ (2 : ℕ) * ((L - V : ℕ) : ℝ) := by
  rw [sum_typeIIShort_sq_eq_sum_Ioc_sieveSeq_sq hV]
  calc
    (∑ m ∈ Finset.Ioc V L, (sieveSeq V moebiusReal m) ^ (2 : ℕ))
      ≤ ∑ _m ∈ Finset.Ioc V L, (B : ℝ) ^ (2 : ℕ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        obtain ⟨hmV, hmL⟩ := Finset.mem_Ioc.mp hm
        have habs := abs_sieveSeq_moebiusReal_le_band_width hV hB (by omega : 1 ≤ m)
          (hmL.trans hhi)
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = (B : ℝ) ^ (2 : ℕ) * ((L - V : ℕ) : ℝ) := by
      simp [Nat.card_Ioc, mul_comm]

/-- **All-Horizon Divisor-Moment Bound on Möbius Prefix `L²` Energy
(`sieveL2PrefixEnergy_moebiusReal_le_invSum_cube`):**
For **every** cutoff `N : ℕ` and **every** horizon `M : ℕ` (with no linear-window restriction
`M ≤ (B + 1) * N`), `sieveL2PrefixEnergy N M moebiusReal ≤ M * (invSum M)^3`. -/
theorem sieveL2PrefixEnergy_moebiusReal_le_invSum_cube (N M : ℕ) :
    sieveL2PrefixEnergy N M moebiusReal ≤ (M : ℝ) * invSum M ^ (3 : ℕ) := by
  unfold sieveL2PrefixEnergy
  refine le_trans (Finset.sum_le_sum fun k hk => ?_) (sum_card_divisors_sq_le M)
  obtain ⟨hk1, _⟩ := Finset.mem_Icc.mp hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have habs := abs_sieveSeq_moebiusReal_succ_le_divisor_card N n
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- **All-Horizon Vaughan Type-II Short-Side Bound on Möbius Prefix `L²` Energy
(`sieveL2PrefixEnergy_moebiusReal_le_one_add_typeIIShort_bound`):**
Direct transfer of `RHTower.Sieve.sum_typeIIShort_sq_le` to `sieveL2PrefixEnergy N M moebiusReal`. -/
theorem sieveL2PrefixEnergy_moebiusReal_le_one_add_typeIIShort_bound {N M : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    sieveL2PrefixEnergy N M moebiusReal ≤
      1 + 2 * (M : ℝ) + 2 * ((M : ℝ) * invSum M ^ (3 : ℕ)) := by
  rw [sieveL2PrefixEnergy_moebiusReal_eq_one_add_sum_typeIIShort_sq hN hM]
  linarith [sum_typeIIShort_sq_le N M]

/-- **All-Horizon Bound on Unsigned Möbius Gradient Energy
(`moebius_gradient_energy_le_four_mul_invSum_cube`):**
For **every** cutoff `N : ℕ` and **every** horizon `M : ℕ`, the accumulated Möbius gradient energy
is bounded by `4 * (M + 1) * (invSum (M + 1))^3` independently of the band ratio `M / N`. -/
theorem moebius_gradient_energy_le_four_mul_invSum_cube (N M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M,
      (sieveSeq N moebiusReal (k + 1) - sieveSeq N moebiusReal k) ^ (2 : ℕ)) ≤
      4 * ((M + 1 : ℕ) : ℝ) * invSum (M + 1) ^ (3 : ℕ) := by
  have hpoint : ∀ k ∈ Finset.Icc 1 M,
      (sieveSeq N moebiusReal (k + 1) - sieveSeq N moebiusReal k) ^ (2 : ℕ) ≤
        2 * sieveSeq N moebiusReal (k + 1) ^ (2 : ℕ) +
          2 * sieveSeq N moebiusReal k ^ (2 : ℕ) := by
    intro k _
    nlinarith [sq_nonneg (sieveSeq N moebiusReal (k + 1) + sieveSeq N moebiusReal k)]
  have hsum1 :
      (∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k ^ (2 : ℕ)) ≤
        sieveL2PrefixEnergy N (M + 1) moebiusReal := by
    unfold sieveL2PrefixEnergy
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right (Nat.le_succ M)) fun _ _ _ => sq_nonneg _
  have hsum2 :
      (∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal (k + 1) ^ (2 : ℕ)) ≤
        sieveL2PrefixEnergy N (M + 1) moebiusReal := by
    unfold sieveL2PrefixEnergy
    have hmap :
        (∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal (k + 1) ^ (2 : ℕ)) =
          ∑ j ∈ Finset.Icc 2 (M + 1), sieveSeq N moebiusReal j ^ (2 : ℕ) := by
      refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
      · intro k hk
        obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro _ _ _ _ h; omega
      · intro j hj
        obtain ⟨hj2, hjM⟩ := Finset.mem_Icc.mp hj
        exact ⟨j - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro _ _; rfl
    rw [hmap]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_left (by omega : 1 ≤ 2)) fun _ _ _ => sq_nonneg _
  have hstep := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hstep
  have hE := sieveL2PrefixEnergy_moebiusReal_le_invSum_cube N (M + 1)
  linarith

/-- **All-Horizon Bound on Renormalized Möbius Prefix Defect
(`abs_moebiusRenormalizedDefect_le_two_mul_invSum_cube`):**
For **every** cutoff `N : ℕ` and **every** horizon `M : ℕ`, the renormalized Möbius defect satisfies
`|sieveRenormalizedPrefixDefect N M moebiusReal| ≤ 2 * (M + 1) * (invSum (M + 1))^3` with no
restriction on `M / N`. -/
theorem abs_moebiusRenormalizedDefect_le_two_mul_invSum_cube (N M : ℕ) :
    |sieveRenormalizedPrefixDefect N M moebiusReal| ≤
      2 * ((M + 1 : ℕ) : ℝ) * invSum (M + 1) ^ (3 : ℕ) := by
  rw [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
  have hpoint : ∀ k ∈ Finset.Icc 1 M,
      |sieveSeq N moebiusReal k *
        (sieveSeq N moebiusReal (k + 1) - sieveSeq N moebiusReal k)| ≤
        (3 / 2 : ℝ) * sieveSeq N moebiusReal k ^ (2 : ℕ) +
          (1 / 2 : ℝ) * sieveSeq N moebiusReal (k + 1) ^ (2 : ℕ) := by
    intro k _
    have h1 :
        sieveSeq N moebiusReal k *
          (sieveSeq N moebiusReal (k + 1) - sieveSeq N moebiusReal k) ≤
          (3 / 2 : ℝ) * sieveSeq N moebiusReal k ^ (2 : ℕ) +
            (1 / 2 : ℝ) * sieveSeq N moebiusReal (k + 1) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (sieveSeq N moebiusReal k - sieveSeq N moebiusReal (k + 1)),
        sq_nonneg (sieveSeq N moebiusReal k)]
    have h2 :
        -((3 / 2 : ℝ) * sieveSeq N moebiusReal k ^ (2 : ℕ) +
          (1 / 2 : ℝ) * sieveSeq N moebiusReal (k + 1) ^ (2 : ℕ)) ≤
          sieveSeq N moebiusReal k *
            (sieveSeq N moebiusReal (k + 1) - sieveSeq N moebiusReal k) := by
      nlinarith [sq_nonneg (sieveSeq N moebiusReal k + sieveSeq N moebiusReal (k + 1)),
        sq_nonneg (sieveSeq N moebiusReal k)]
    exact abs_le.mpr ⟨h2, h1⟩
  have hsum1 :
      (∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k ^ (2 : ℕ)) ≤
        sieveL2PrefixEnergy N (M + 1) moebiusReal := by
    unfold sieveL2PrefixEnergy
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right (Nat.le_succ M)) fun _ _ _ => sq_nonneg _
  have hsum2 :
      (∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal (k + 1) ^ (2 : ℕ)) ≤
        sieveL2PrefixEnergy N (M + 1) moebiusReal := by
    unfold sieveL2PrefixEnergy
    have hmap :
        (∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal (k + 1) ^ (2 : ℕ)) =
          ∑ j ∈ Finset.Icc 2 (M + 1), sieveSeq N moebiusReal j ^ (2 : ℕ) := by
      refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
      · intro k hk
        obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro _ _ _ _ h; omega
      · intro j hj
        obtain ⟨hj2, hjM⟩ := Finset.mem_Icc.mp hj
        exact ⟨j - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro _ _; rfl
    rw [hmap]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_left (by omega : 1 ≤ 2)) fun _ _ _ => sq_nonneg _
  have habs := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hpoint)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at habs
  have hE := sieveL2PrefixEnergy_moebiusReal_le_invSum_cube N (M + 1)
  linarith

/-! ## §3. Möbius Vaughan Identity and Trans-Horizon Quotient-Window Decomposition -/

/-- **Vaughan's Identity for the Möbius Function (`moebius_vaughan_identity`):**
In the ring `ArithmeticFunction ℝ`, `moebius * zeta = 1` implies the exact two-cutoff identity
`μ = μ_U + μ_V - ζ * μ_U * μ_V + (μ - μ_U) * (1 - ζ * μ_V)`. -/
theorem moebius_vaughan_identity (U V : ℕ) :
    (moebius : ArithmeticFunction ℝ) =
      truncAF (moebius : ArithmeticFunction ℝ) U +
        truncAF (moebius : ArithmeticFunction ℝ) V -
        (zeta : ArithmeticFunction ℝ) * truncAF (moebius : ArithmeticFunction ℝ) U *
          truncAF (moebius : ArithmeticFunction ℝ) V +
        ((moebius : ArithmeticFunction ℝ) - truncAF (moebius : ArithmeticFunction ℝ) U) *
          typeIIShort V := by
  unfold typeIIShort
  have hkey : (moebius : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ) = 1 :=
    coe_moebius_mul_coe_zeta
  linear_combination (truncAF (moebius : ArithmeticFunction ℝ) V) * hkey

/-- Above both cutoffs (`U < n` and `V < n`), `moebius n` decomposes into its Type-I and Type-II
bilinear pieces. -/
theorem moebius_vaughan_apply_of_gt {U V n : ℕ} (hU : U < n) (hV : V < n) :
    (moebius : ArithmeticFunction ℝ) n =
      -((zeta : ArithmeticFunction ℝ) * truncAF (moebius : ArithmeticFunction ℝ) U *
          truncAF (moebius : ArithmeticFunction ℝ) V) n +
        (((moebius : ArithmeticFunction ℝ) - truncAF (moebius : ArithmeticFunction ℝ) U) *
          typeIIShort V) n := by
  have h := congrArg (fun g : ArithmeticFunction ℝ => g n) (moebius_vaughan_identity U V)
  change (moebius : ArithmeticFunction ℝ) n =
    truncAF (moebius : ArithmeticFunction ℝ) U n +
      truncAF (moebius : ArithmeticFunction ℝ) V n -
      ((zeta : ArithmeticFunction ℝ) * truncAF (moebius : ArithmeticFunction ℝ) U *
        truncAF (moebius : ArithmeticFunction ℝ) V) n +
      (((moebius : ArithmeticFunction ℝ) - truncAF (moebius : ArithmeticFunction ℝ) U) *
        typeIIShort V) n at h
  rw [truncAF_apply_of_gt hU, truncAF_apply_of_gt hV] at h
  linarith

/-- Every trans-horizon Möbius quotient window `∑ d ∈ Finset.Ioc N Q, moebiusReal d` (`V ≤ N`)
decomposes into a Type-I sum (convolution of `sieveSeq N moebiusReal` with `truncAF moebius V`)
and a Type-II bilinear sum (supported strictly above `N` and `V`). -/
theorem sum_Ioc_moebiusReal_eq_vaughan_typeI_add_typeII {N V Q : ℕ} (hVN : V ≤ N) :
    (∑ d ∈ Finset.Ioc N Q, moebiusReal d) =
      -(∑ d ∈ Finset.Ioc N Q,
          ((zeta : ArithmeticFunction ℝ) * truncAF (moebius : ArithmeticFunction ℝ) N *
            truncAF (moebius : ArithmeticFunction ℝ) V) d) +
        ∑ d ∈ Finset.Ioc N Q,
          (((moebius : ArithmeticFunction ℝ) - truncAF (moebius : ArithmeticFunction ℝ) N) *
            typeIIShort V) d := by
  have hpoint : ∀ d ∈ Finset.Ioc N Q,
      moebiusReal d =
        -((zeta : ArithmeticFunction ℝ) * truncAF (moebius : ArithmeticFunction ℝ) N *
            truncAF (moebius : ArithmeticFunction ℝ) V) d +
          (((moebius : ArithmeticFunction ℝ) - truncAF (moebius : ArithmeticFunction ℝ) N) *
            typeIIShort V) d := by
    intro d hd
    obtain ⟨hdN, _⟩ := Finset.mem_Ioc.mp hd
    exact moebius_vaughan_apply_of_gt hdN (lt_of_le_of_lt hVN hdN)
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, Finset.sum_neg_distrib]

/-- **Vaughan Decomposition of the Literal Möbius Source Prefix
(`sum_sieveSeq_moebiusReal_eq_one_sub_vaughan_quotient_windows`):**
Combines complementary-quotient compression (`sum_sieveSeq_moebiusReal_eq_one_sub_quotient_windows`)
with the Möbius Vaughan decomposition on each trans-horizon quotient window `(N, M / q]`. -/
theorem sum_sieveSeq_moebiusReal_eq_one_sub_vaughan_quotient_windows {N V B M : ℕ}
    (hVN : V ≤ N) (hM : 1 ≤ M) (hhi : M ≤ (B + 1) * N) :
    (∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k) =
      1 - ∑ q ∈ Finset.Icc 1 B,
        (-(∑ d ∈ Finset.Ioc N (M / q),
            ((zeta : ArithmeticFunction ℝ) * truncAF (moebius : ArithmeticFunction ℝ) N *
              truncAF (moebius : ArithmeticFunction ℝ) V) d) +
          ∑ d ∈ Finset.Ioc N (M / q),
            (((moebius : ArithmeticFunction ℝ) - truncAF (moebius : ArithmeticFunction ℝ) N) *
              typeIIShort V) d) := by
  rw [sum_sieveSeq_moebiusReal_eq_one_sub_quotient_windows hM hhi]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  exact sum_Ioc_moebiusReal_eq_vaughan_typeI_add_typeII hVN

end

end GaloisForLFunctions.BezoutValuationIncidence
