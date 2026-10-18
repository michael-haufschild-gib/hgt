import GaloisForLFunctions.BezoutValuationIncidence.RenormalizedMobiusDefectAndFirstOctaveCancellation
import GaloisForLFunctions.RHTower.DivisorBound
import GaloisForLFunctions.RHTower.Sieve.CoprimeSquarefreeDyadic


/-!
# Cofinal Möbius gradient coercivity and renormalized discrepancy

Let `s_N(k)` be the divisor sum truncated at `N`, with literal Möbius weights, and let
`R_N(M)` be its renormalized combined prefix defect. Every odd squarefree integer in
`(N, 2N]` selects a distinct adjacent edge ending at a multiple of four. Its gradient
square is one, regardless of the Möbius sign. Consequently the accumulated gradient
energy dominates the odd-squarefree count at every horizon at least `2N`.

The exact polarization identity leaves only a divisor-bounded endpoint correction.
Combining the density `4 / pi^2` with the elementary subpower divisor bound gives,
for every fixed integer `A >= 2`, eventually uniformly on `2N <= M <= N^A`,
`R_N(M) <= -N / (2 * pi^2)`. This is a signed coercivity estimate for the actual
arithmetic source; it assumes no receiver budget and asserts no upper bound for
its accumulated gradient energy.
-/

open Finset Filter
open GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators Topology


namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- Every truncated Möbius divisor sum at a positive argument is bounded by its divisor count, uniformly in the cutoff. -/
theorem abs_sieveSeq_moebiusReal_succ_le_divisor_card (N n : ℕ) :
    |sieveSeq N moebiusReal (n + 1)| ≤ ((n + 1).divisors.card : ℝ) := by
  classical
  unfold sieveSeq
  rw [filter_dvd_Icc_eq_divisors_filter_le N (by omega)]
  calc
    _ ≤ ∑ d ∈ (n + 1).divisors.filter (fun d => d ≤ N), |moebiusReal d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ (n + 1).divisors.filter (fun d => d ≤ N), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      unfold moebiusReal
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    _ = (((n + 1).divisors.filter (fun d => d ≤ N)).card : ℝ) := by simp
    _ ≤ ((n + 1).divisors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun d => d ≤ N) _)

/-- Exact polarization including the empty prefix: renormalized defect plus gradient energy is an endpoint difference. -/
theorem two_mul_sieveRenormalizedPrefixDefect_add_gradient_eq_boundary
    (N M : ℕ) (c : ℕ → ℝ) :
    2 * sieveRenormalizedPrefixDefect N M c +
        (∑ k ∈ Finset.Icc 1 M, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ 2) =
      sieveSeq N c (M + 1) ^ 2 - sieveSeq N c 1 ^ 2 := by
  rcases M with _ | M
  · simp [sieveRenormalizedPrefixDefect_eq_succ_sub_sq]
  · have h := two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary
      N (Nat.succ_pos M) c
    linarith only [h]

/-- The endpoint correction for the literal Möbius source has a cutoff-independent divisor-square bound. -/
theorem abs_two_mul_moebiusRenormalizedDefect_add_gradient_le (N M : ℕ) :
    |2 * sieveRenormalizedPrefixDefect N M moebiusReal +
      (∑ k ∈ Finset.Icc 1 M,
        (sieveSeq N moebiusReal (k + 1) - sieveSeq N moebiusReal k) ^ 2)| ≤
      ((M + 1).divisors.card : ℝ) ^ 2 + 1 := by
  rw [two_mul_sieveRenormalizedPrefixDefect_add_gradient_eq_boundary]
  have hM := abs_sieveSeq_moebiusReal_succ_le_divisor_card N M
  have h1 := abs_sieveSeq_moebiusReal_succ_le_divisor_card N 0
  simp only [Nat.zero_add, Nat.divisors_one, Finset.card_singleton, Nat.cast_one] at h1
  have hsM : sieveSeq N moebiusReal (M + 1) ^ 2 ≤
      ((M + 1).divisors.card : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hM 2
  have hs1 : sieveSeq N moebiusReal 1 ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (sieveSeq N moebiusReal 1),
    sq_nonneg (sieveSeq N moebiusReal (M + 1))]

/-- Positive excursions of the renormalized Möbius defect are bounded by half the terminal divisor square. -/
theorem moebiusRenormalizedDefect_positive_part_le (N M : ℕ) :
    max 0 (sieveRenormalizedPrefixDefect N M moebiusReal) ≤
      ((M + 1).divisors.card : ℝ) ^ 2 / 2 := by
  have heq := two_mul_sieveRenormalizedPrefixDefect_add_gradient_eq_boundary N M moebiusReal
  have hb := abs_sieveSeq_moebiusReal_succ_le_divisor_card N M
  have hs : sieveSeq N moebiusReal (M + 1) ^ 2 ≤
      ((M + 1).divisors.card : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hg : 0 ≤ ∑ k ∈ Finset.Icc 1 M,
      (sieveSeq N moebiusReal (k + 1) - sieveSeq N moebiusReal k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply max_le
  · positivity
  · linarith [sq_nonneg (sieveSeq N moebiusReal 1)]

/-- Divisor squares plus one admit every reciprocal-integer power bound, with a constant independent of the argument. -/
theorem exists_uniform_divisor_square_subpower_bound (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ,
      ((M + 1).divisors.card : ℝ) ^ 2 + 1 ≤
        C * ((M : ℝ) + 1) ^ (1 / ((r : ℝ) + 1)) := by
  have ha : 0 < 1 / ((r : ℝ) + 1) := by positivity
  obtain ⟨C, hC, hbound⟩ := RHTower.card_divisors_le_const_mul_rpow (half_pos ha)
  refine ⟨C ^ 2 + 1, by positivity, fun M => ?_⟩
  have hx : 0 < (M : ℝ) + 1 := by positivity
  have hb := pow_le_pow_left₀ (Nat.cast_nonneg ((M + 1).divisors.card))
    (hbound (M + 1) (by omega)) 2
  rw [mul_pow] at hb
  simp only [Nat.cast_add, Nat.cast_one] at hb
  rw [← Real.rpow_natCast (((M : ℝ) + 1) ^ (1 / ((r : ℝ) + 1) / 2)) 2,
    ← Real.rpow_mul hx.le] at hb
  simp only [Nat.cast_ofNat] at hb
  have hexp : 1 / ((r : ℝ) + 1) / 2 * 2 = 1 / ((r : ℝ) + 1) := by ring
  rw [hexp] at hb
  have hp : 1 ≤ ((M : ℝ) + 1) ^ (1 / ((r : ℝ) + 1)) :=
    Real.one_le_rpow (by linarith [show (0 : ℝ) ≤ M from Nat.cast_nonneg M]) ha.le
  nlinarith

/-- The defect-energy correction admits arbitrarily small power bounds simultaneously for every cutoff and horizon. -/
theorem exists_uniform_moebiusRenormalizedDefect_subpower_bound (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N M : ℕ,
      |2 * sieveRenormalizedPrefixDefect N M moebiusReal +
        (∑ k ∈ Finset.Icc 1 M,
          (sieveSeq N moebiusReal (k + 1) - sieveSeq N moebiusReal k) ^ 2)| ≤
        C * ((M : ℝ) + 1) ^ (1 / ((r : ℝ) + 1)) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_divisor_square_subpower_bound r
  exact ⟨C, hC, fun N M =>
    (abs_two_mul_moebiusRenormalizedDefect_add_gradient_le N M).trans (hbound M)⟩


/-- Odd squarefree integers in the first trans-horizon dyadic interval. -/
def oddSquarefreeWindow (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc N (2 * N)).filter (fun k => ¬ 2 ∣ k ∧ Squarefree k)

private def squarefreeZeroEdge (k : ℕ) : ℕ :=
  if k % 4 = 1 then k - 1 else k

/-- The odd-squarefree count is the prime-two-deleted Möbius-square sum. -/
theorem oddSquarefreeWindow_card_eq_weighted_sum (N : ℕ) :
    ((oddSquarefreeWindow N).card : ℝ) =
      ∑ k ∈ Finset.Ioc N (2 * N),
        (if 2 ∣ k then 0 else ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2) := by
  classical
  calc
    _ = ∑ _k ∈ oddSquarefreeWindow N, (1 : ℝ) := by simp
    _ = _ := by
      rw [oddSquarefreeWindow, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      have hm : ((ArithmeticFunction.moebius k : ℤ) : ℝ) ^ 2 =
          if Squarefree k then (1 : ℝ) else 0 := by
        exact_mod_cast (ArithmeticFunction.moebius_sq (n := k))
      by_cases htwo : 2 ∣ k <;> simp [htwo, hm]

private theorem sieveSeq_moebiusReal_eq_zero_of_four_dvd {N k : ℕ}
    (hN : 2 ≤ N) (hlo : N ≤ k) (hhi : k ≤ 2 * N) (hfour : 4 ∣ k) :
    sieveSeq N moebiusReal k = 0 := by
  by_cases hkN : k ≤ N
  · rw [sieveSeq_moebiusReal_eq_ite_of_le (by omega) hkN, if_neg (by omega)]
  · rw [sieveSeq_moebiusReal_first_octave (by omega) hhi]
    have hsq : ¬ Squarefree k := by
      intro h
      exact (Nat.squarefree_iff_prime_squarefree.mp h 2 Nat.prime_two)
        (by simpa using hfour)
    simp [moebiusReal, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]

private theorem squarefreeZeroEdge_spec {N k : ℕ} (hN : 2 ≤ N)
    (hk : k ∈ oddSquarefreeWindow N) :
    N ≤ squarefreeZeroEdge k ∧ squarefreeZeroEdge k < 2 * N ∧
      (sieveSeq N moebiusReal (squarefreeZeroEdge k + 1) -
        sieveSeq N moebiusReal (squarefreeZeroEdge k)) ^ 2 = 1 := by
  obtain ⟨hkI, htwo, hsq⟩ := Finset.mem_filter.mp hk
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hkI
  have hodd : k % 2 = 1 := by
    have hmod : k % 2 ≠ 0 := fun h => htwo (Nat.dvd_of_mod_eq_zero h)
    omega
  have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by omega
  have hsk : sieveSeq N moebiusReal k ^ 2 = 1 := by
    rw [sieveSeq_moebiusReal_sq_first_octave (by omega) hhi]
    have hm : ArithmeticFunction.moebius k ^ 2 = 1 := by
      rw [ArithmeticFunction.moebius_sq, if_pos hsq]
    unfold moebiusReal
    exact_mod_cast hm
  rcases hk4 with hk4 | hk4
  · have he : squarefreeZeroEdge k = k - 1 := by simp [squarefreeZeroEdge, hk4]
    have hz := sieveSeq_moebiusReal_eq_zero_of_four_dvd hN
      (show N ≤ k - 1 by omega) (show k - 1 ≤ 2 * N by omega)
      (Nat.dvd_of_mod_eq_zero (by omega : (k - 1) % 4 = 0))
    rw [he]
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.sub_add_cancel (by omega), hz, sub_zero]
    exact hsk
  · have he : squarefreeZeroEdge k = k := by simp [squarefreeZeroEdge, hk4]
    have hz := sieveSeq_moebiusReal_eq_zero_of_four_dvd hN
      (show N ≤ k + 1 by omega) (show k + 1 ≤ 2 * N by omega)
      (Nat.dvd_of_mod_eq_zero (by omega : (k + 1) % 4 = 0))
    rw [he]
    refine ⟨by omega, by omega, ?_⟩
    rw [hz, zero_sub, neg_sq]
    exact hsk

private theorem squarefreeZeroEdge_injOn (N : ℕ) :
    Set.InjOn squarefreeZeroEdge (oddSquarefreeWindow N) := by
  intro k hk l hl heq
  obtain ⟨hkI, htwoK, _⟩ := Finset.mem_filter.mp hk
  obtain ⟨hlI, htwoL, _⟩ := Finset.mem_filter.mp hl
  have hkLo := (Finset.mem_Ioc.mp hkI).1
  have hlLo := (Finset.mem_Ioc.mp hlI).1
  have hkodd : k % 2 = 1 := by
    have : k % 2 ≠ 0 := fun h => htwoK (Nat.dvd_of_mod_eq_zero h)
    omega
  have hlodd : l % 2 = 1 := by
    have : l % 2 ≠ 0 := fun h => htwoL (Nat.dvd_of_mod_eq_zero h)
    omega
  unfold squarefreeZeroEdge at heq
  split_ifs at heq <;> omega

/-- Distinct odd squarefree integers select distinct unit-energy edges; their count bounds every longer prefix energy from below. -/
theorem odd_squarefree_count_le_moebius_gradient_energy (N M : ℕ) :
    ((oddSquarefreeWindow (N + 2)).card : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 (2 * (N + 2) + M),
        (sieveSeq (N + 2) moebiusReal (k + 1) -
          sieveSeq (N + 2) moebiusReal k) ^ 2 := by
  classical
  let P := oddSquarefreeWindow (N + 2)
  let f : ℕ → ℝ := fun k =>
    (sieveSeq (N + 2) moebiusReal (k + 1) - sieveSeq (N + 2) moebiusReal k) ^ 2
  have hsub : P.image squarefreeZeroEdge ⊆ Finset.Icc 1 (2 * (N + 2) + M) := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hlo, hhi, _⟩ := squarefreeZeroEdge_spec (by omega : 2 ≤ N + 2) hp
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  calc
    (P.card : ℝ) = ∑ _p ∈ P, (1 : ℝ) := by simp
    _ = ∑ p ∈ P, f (squarefreeZeroEdge p) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (squarefreeZeroEdge_spec (by omega : 2 ≤ N + 2) hp).2.2.symm
    _ = ∑ k ∈ P.image squarefreeZeroEdge, f k :=
      (Finset.sum_image (squarefreeZeroEdge_injOn (N + 2))).symm
    _ ≤ ∑ k ∈ Finset.Icc 1 (2 * (N + 2) + M), f k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)


/-- A finite arithmetic budget at every trans-horizon prefix: the odd-squarefree edge
count and the initial unit are paid by the renormalized defect and the endpoint divisor square. -/
theorem moebiusRenormalizedDefect_oddSquarefree_budget (N M : ℕ) :
    2 * sieveRenormalizedPrefixDefect (N + 2) (2 * (N + 2) + M) moebiusReal +
        ((oddSquarefreeWindow (N + 2)).card : ℝ) + 1 ≤
      ((2 * (N + 2) + M + 1).divisors.card : ℝ) ^ 2 := by
  have he := odd_squarefree_count_le_moebius_gradient_energy N M
  have hid := two_mul_sieveRenormalizedPrefixDefect_add_gradient_eq_boundary
    (N + 2) (2 * (N + 2) + M) moebiusReal
  have h1 : sieveSeq (N + 2) moebiusReal 1 = 1 := by
    rw [sieveSeq_moebiusReal_eq_ite_of_le (by omega) (by omega), if_pos rfl]
  rw [h1, one_pow] at hid
  have hs : sieveSeq (N + 2) moebiusReal (2 * (N + 2) + M + 1) ^ 2 ≤
      ((2 * (N + 2) + M + 1).divisors.card : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
      (abs_sieveSeq_moebiusReal_succ_le_divisor_card (N + 2) (2 * (N + 2) + M)) 2
  linarith only [he, hid, hs]

/-- The odd-squarefree dyadic count has density two thirds of the squarefree density, namely `4 / pi^2`. -/
theorem tendsto_oddSquarefreeWindow_card_div :
    Tendsto (fun N : ℕ => ((oddSquarefreeWindow N).card : ℝ) / N)
      atTop (𝓝 (squarefreeDensity * 2 / 3)) := by
  have h := (tendsto_window_coprime_squarefree_density Nat.prime_two).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hcast (N : ℕ) : (2 : ℝ) * (N : ℝ) = ((2 * N : ℕ) : ℝ) := by push_cast; rfl
  simpa only [Function.comp_def, hcast, Nat.floor_natCast, Nat.cast_ofNat,
    show (2 : ℝ) + 1 = 3 by norm_num, oddSquarefreeWindow_card_eq_weighted_sum] using h

/-- The literal truncated Möbius source has a linear gradient-energy floor, uniform over every horizon at least twice the cutoff. -/
theorem eventually_moebius_gradient_energy_ge_linear :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, 2 * N ≤ M →
      squarefreeDensity / 3 * N ≤
        ∑ k ∈ Finset.Icc 1 M,
          (sieveSeq N moebiusReal (k + 1) - sieveSeq N moebiusReal k) ^ 2 := by
  have hD : 0 < squarefreeDensity := by rw [squarefreeDensity_eq]; positivity
  have hc := tendsto_oddSquarefreeWindow_card_div.eventually
    (eventually_gt_nhds (show squarefreeDensity / 3 < squarefreeDensity * 2 / 3 by linarith))
  filter_upwards [hc, eventually_ge_atTop (2 : ℕ)] with N hcount hN
  intro M hM
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcount' := (lt_div_iff₀ hn).mp hcount
  have he := odd_squarefree_count_le_moebius_gradient_energy (N - 2) (M - 2 * N)
  rw [Nat.sub_add_cancel hN, show 2 * N + (M - 2 * N) = M by omega] at he
  exact hcount'.le.trans he


/-- Every fixed polynomial trans-horizon window eventually has a uniform negative linear renormalized defect. No analytic budget is assumed. -/
theorem eventually_moebiusRenormalizedDefect_polynomial_cofinal_bound (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ M ∈ Finset.Icc (2 * N) (N ^ (r + 2)),
      sieveRenormalizedPrefixDefect N M moebiusReal ≤
        -(N : ℝ) / (2 * Real.pi ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_moebiusRenormalizedDefect_subpower_bound (2 * r + 3)
  let a : ℝ := 1 / ((2 * r + 3 : ℕ) + 1 : ℝ)
  let D : ℝ := C * (2 : ℝ) ^ a
  have ha : 0 < a := by dsimp [a]; positivity
  have hδ : 0 < squarefreeDensity := by rw [squarefreeDensity_eq]; positivity
  have hlim : Tendsto (fun N : ℕ => D * (N : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (𝓝 0) := by
    have hpowlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (y := (1 / 2 : ℝ)) (by norm_num)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [mul_zero] using hpowlim.const_mul D
  filter_upwards [eventually_moebius_gradient_energy_ge_linear,
    hlim.eventually (eventually_lt_nhds (show (0 : ℝ) < squarefreeDensity / 6 by positivity)),
    eventually_ge_atTop (2 : ℕ)] with N henergy hsmall hN
  intro M hM
  obtain ⟨hMlo, hMhi⟩ := Finset.mem_Icc.mp hM
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpow : (1 : ℝ) ≤ (N : ℝ) ^ (r + 2) := one_le_pow₀ hn1.le
  have hMN : (M : ℝ) + 1 ≤ 2 * (N : ℝ) ^ (r + 2) := by
    have hc : (M : ℝ) ≤ (N : ℝ) ^ (r + 2) := by exact_mod_cast hMhi
    linarith
  have hpow : ((M : ℝ) + 1) ^ a ≤ (2 : ℝ) ^ a * (N : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (2 * (N : ℝ) ^ (r + 2)) ^ a :=
        Real.rpow_le_rpow (by positivity) hMN ha.le
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (by positivity),
          ← Real.rpow_natCast (N : ℝ) (r + 2), ← Real.rpow_mul hn.le]
        congr 2
        dsimp [a]
        push_cast
        field_simp
        ring
  have hb := (le_abs_self _).trans (hbound N M)
  have hbd : 2 * sieveRenormalizedPrefixDefect N M moebiusReal +
      (∑ k ∈ Finset.Icc 1 M,
        (sieveSeq N moebiusReal (k + 1) - sieveSeq N moebiusReal k) ^ 2) ≤
      D * (N : ℝ) ^ (1 / 2 : ℝ) := by
    exact hb.trans ((mul_le_mul_of_nonneg_left hpow hC.le).trans_eq (by dsimp [D]; ring))
  have hs : D * (N : ℝ) ^ (1 / 2 : ℝ) < squarefreeDensity / 6 * N := by
    have heq : (N : ℝ) ^ (-(1 / 2 : ℝ)) * N = (N : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        _ = (N : ℝ) ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hn]; norm_num
    have hmul := mul_lt_mul_of_pos_right hsmall hn
    simpa only [mul_assoc, heq] using hmul
  have he := henergy M hMlo
  have hout : sieveRenormalizedPrefixDefect N M moebiusReal ≤
      -(squarefreeDensity / 12 * N) := by linarith only [hbd, hs, he]
  have hconst : -(squarefreeDensity / 12 * N) = -(N : ℝ) / (2 * Real.pi ^ 2) := by
    rw [squarefreeDensity_eq]
    ring
  rwa [hconst] at hout


end
end GaloisForLFunctions.BezoutValuationIncidence
