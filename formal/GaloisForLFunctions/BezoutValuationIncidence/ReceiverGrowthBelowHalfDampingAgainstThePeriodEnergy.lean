import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheVinogradovKorobovBand
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedDiscrepancyEnergyGrowthLaw

/-!
# The receiver below half damping grows slower than the period energy

At a fixed damping `ε ∈ [1/4, 1/2)` two energies of the damped Möbius row grow at the exponent
`1 - 2ε`:

* the **period energy** `E_prim(N)`, the mean square over a full period of the centred discrepancy,
  satisfies `E_prim(N) ≥ N^{1-2ε}/10368` (`eventually_sievePrimitiveEnergy_pmPowerDamped_growth`): on
  the period torus the top octave of moduli acts as `N^{1-2ε}` independent unit steps;
* the **receiver** `E_T(ε)`, the pronic energy of the prefix below the first period, satisfies

  `E_T(ε) ≤ C_ε T^{1-2ε} e^{-κσ(T)/270}`,   `σ = vkScale`, `κ = vkKappa`,

  for all large `T` (`eventually_receiver_le_growth`).

Hence `E_N(ε)/E_prim(N) ≤ C e^{-κσ(N)/270} → 0` (`eventually_receiver_le_mul_periodEnergy`): the
pronic weighting of the arguments below the first period carries a cancellation that the period
torus does not have, and its unconditional size is exactly the Vinogradov–Korobov factor. The proof
splits the horizon at `√T`: below it the trivial exponent `(1 - 2ε)/2` suffices; above it every
prefix carries the saving at a scale comparable to `T` (`σ(n) ≥ (4/9) σ(T)` for `n ≥ √T`). A growth
exponent below `1 - 2ε` at one fixed `ε < 1/2` would be a zero-free strip; this bound does not give one.
-/

open Finset Filter Topology RHTower.Sieve
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- `σ(x)/log x = 1/((log x)^{2/5} (log log x)^{5/3}) → 0`. -/
theorem tendsto_vkScale_div_log : Tendsto (fun x : ℝ => vkScale x / Real.log x) atTop (𝓝 0) := by
  have hL : Tendsto (fun x : ℝ => Real.log x) atTop atTop := Real.tendsto_log_atTop
  have hLL : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hden : Tendsto (fun x : ℝ => Real.log x ^ ((2 : ℝ) / 5) *
      Real.log (Real.log x) ^ ((5 : ℝ) / 3)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num)).comp hL).atTop_mul_atTop₀
      ((tendsto_rpow_atTop (by norm_num)).comp hLL)
  refine (tendsto_inv_atTop_zero.comp hden).congr' ?_
  filter_upwards [hL.eventually_gt_atTop 0, hLL.eventually_gt_atTop 0] with x h1 h2
  simp only [Function.comp_apply]
  rw [vkScale_eq h1 h2, div_div_cancel_left' h1.ne']

theorem vkScale_nonneg {x : ℝ} (hx : 1 ≤ Real.log x) : 0 ≤ vkScale x :=
  mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (Real.log_nonneg hx) _)

theorem one_le_log_of_three_le {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have he := Real.exp_one_lt_d9
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by linarith)

/-! ## Cells of the receiver -/

/-- The receiver cell `A_ε(n)²/(n(n+1))`. -/
def receiverCell (ε : ℝ) (n : ℕ) : ℝ :=
  weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 /
    ((n : ℝ) * ((n : ℝ) + 1))

theorem pmPowerDampedDivisorDiscreteEnergy_eq_sum_receiverCell (ε : ℝ) (T : ℕ) :
    RHTower.pmPowerDampedDivisorDiscreteEnergy ε T = ∑ n ∈ Icc 1 T, receiverCell ε n := by
  rw [← weightPronicEnergy_pmPowerDamped, weightPronicEnergy]; rfl

theorem receiverCell_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ receiverCell ε n := by
  unfold receiverCell; positivity

/-- A prefix bound `|A_ε(n)| ≤ K n^{1-ε} e^{-u}` gives `A_ε(n)²/(n(n+1)) ≤ K² n^{-2ε} e^{-2u}`. -/
theorem receiverCell_le_of_abs_le {ε K u : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hA : |weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n| ≤
      K * (n : ℝ) ^ (1 - ε) * Real.exp (-u)) :
    receiverCell ε n ≤ K ^ 2 * ((n : ℝ) ^ (-(2 * ε)) * Real.exp (-(2 * u))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hA2 : weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 ≤
      (K * (n : ℝ) ^ (1 - ε) * Real.exp (-u)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
  have hp : ((n : ℝ) ^ (1 - ε)) ^ 2 = (n : ℝ) ^ (-(2 * ε)) * ((n : ℝ) * (n : ℝ)) := by
    have h2 : (n : ℝ) ^ (-(2 * ε)) * ((n : ℝ) * (n : ℝ)) = (n : ℝ) ^ (-(2 * ε) + 1 + 1) := by
      rw [Real.rpow_add_one hn0.ne', Real.rpow_add_one hn0.ne']; ring
    rw [h2, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1; push_cast; ring
  have he : Real.exp (-u) ^ 2 = Real.exp (-(2 * u)) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hid : (K * (n : ℝ) ^ (1 - ε) * Real.exp (-u)) ^ 2 / ((n : ℝ) * (n : ℝ)) =
      K ^ 2 * ((n : ℝ) ^ (-(2 * ε)) * Real.exp (-(2 * u))) := by
    rw [mul_pow, mul_pow, hp, he]; field_simp
  unfold receiverCell
  calc _ ≤ (K * (n : ℝ) ^ (1 - ε) * Real.exp (-u)) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
        div_le_div_of_nonneg_right hA2 (by positivity)
    _ ≤ (K * (n : ℝ) ^ (1 - ε) * Real.exp (-u)) ^ 2 / ((n : ℝ) * (n : ℝ)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
    _ = _ := hid

/-- Cells below `N` carry at most `N (3 + 31N)²` in total (trivial prefix bound). -/
theorem sum_receiverCell_lt_le {ε : ℝ} (hε4 : 1 / 4 ≤ ε) (hε2 : ε ≤ 1 / 2) (T N : ℕ) :
    ∑ n ∈ Icc 1 T with n < N, receiverCell ε n ≤ (N : ℝ) * (3 + 31 * N) ^ 2 := by
  have hsub : (Icc 1 T).filter (fun n => n < N) ⊆ range N := fun n hn => by
    simp only [mem_filter, mem_range] at hn ⊢; exact hn.2
  have hterm : ∀ n ∈ (Icc 1 T).filter (fun n => n < N), receiverCell ε n ≤ (3 + 31 * N) ^ 2 := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    have hA := abs_weightCenteredPrefix_pmPowerDamped_le_trivial hε4 hε2 hn.1.1
    have hA2 : weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n ^ 2 ≤
        (3 + 31 * N) ^ 2 := by
      rw [← sq_abs]
      refine pow_le_pow_left₀ (abs_nonneg _) (hA.trans ?_) 2
      have : (n : ℝ) ≤ N := by exact_mod_cast hn.2.le
      linarith
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1.1
    unfold receiverCell
    rw [div_le_iff₀ (by positivity)]
    exact hA2.trans (le_mul_of_one_le_right (sq_nonneg _) (by nlinarith))
  calc ∑ n ∈ Icc 1 T with n < N, receiverCell ε n
      ≤ ∑ n ∈ Icc 1 T with n < N, (3 + 31 * (N : ℝ)) ^ 2 := sum_le_sum hterm
    _ = (((Icc 1 T).filter (fun n => n < N)).card : ℝ) * (3 + 31 * N) ^ 2 := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (3 + 31 * N) ^ 2 := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (card_le_card hsub).trans (card_range N).le) (sq_nonneg _)

theorem sum_Icc_rpow_neg_two_mul_le {ε : ℝ} (hε4 : 1 / 4 ≤ ε) (hε2 : ε < 1 / 2) (X : ℕ) :
    ∑ n ∈ Icc 1 X, (n : ℝ) ^ (-(2 * ε)) ≤ 1 + (X : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) := by
  have h := RHTower.sum_rpow_neg_head_le (c := 2 * ε) (by linarith) (by linarith) X
  exact h

theorem natSqrt_rpow_le {a : ℝ} (ha : 0 ≤ a) (T : ℕ) :
    ((Nat.sqrt T : ℕ) : ℝ) ^ a ≤ (T : ℝ) ^ (a / 2) := by
  have hs : ((Nat.sqrt T : ℕ) : ℝ) ≤ Real.sqrt T := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast Nat.sqrt_le' T
  calc ((Nat.sqrt T : ℕ) : ℝ) ^ a ≤ (Real.sqrt T) ^ a :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hs ha
    _ = (T : ℝ) ^ (a / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg _)]; ring_nf

/-- **Cells up to `√T`.** If every cell from `N` on is at most `K² n^{-2ε}`, the cells
`N ≤ n ≤ √T` carry at most `K² (1 + T^{(1-2ε)/2}/(1-2ε))`. -/
theorem sum_receiverCell_mid_le {ε K : ℝ} (hε4 : 1 / 4 ≤ ε) (hε2 : ε < 1 / 2) {N T : ℕ}
    (hcell : ∀ n, N ≤ n → receiverCell ε n ≤ K ^ 2 * (n : ℝ) ^ (-(2 * ε))) :
    ∑ n ∈ (Icc 1 T).filter (fun n => ¬ n < N) with n * n ≤ T, receiverCell ε n ≤
      K ^ 2 * (1 + (T : ℝ) ^ ((1 - 2 * ε) / 2) / (1 - 2 * ε)) := by
  have ha0 : 0 < 1 - 2 * ε := by linarith
  have hsub : ((Icc 1 T).filter (fun n => ¬ n < N)).filter (fun n => n * n ≤ T) ⊆
      Icc 1 (Nat.sqrt T) := fun n hn => by
    simp only [mem_filter, mem_Icc] at hn ⊢
    exact ⟨hn.1.1.1, Nat.le_sqrt.mpr hn.2⟩
  calc _ ≤ ∑ n ∈ ((Icc 1 T).filter (fun n => ¬ n < N)).filter (fun n => n * n ≤ T),
          K ^ 2 * (n : ℝ) ^ (-(2 * ε)) :=
        sum_le_sum fun n hn => hcell n (not_lt.mp (mem_filter.mp (mem_filter.mp hn).1).2)
    _ ≤ ∑ n ∈ Icc 1 (Nat.sqrt T), K ^ 2 * (n : ℝ) ^ (-(2 * ε)) :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ = K ^ 2 * ∑ n ∈ Icc 1 (Nat.sqrt T), (n : ℝ) ^ (-(2 * ε)) := by rw [mul_sum]
    _ ≤ K ^ 2 * (1 + (T : ℝ) ^ ((1 - 2 * ε) / 2) / (1 - 2 * ε)) := by
        refine mul_le_mul_of_nonneg_left ((sum_Icc_rpow_neg_two_mul_le hε4 hε2 _).trans ?_)
          (sq_nonneg K)
        have := div_le_div_of_nonneg_right (natSqrt_rpow_le ha0.le T) ha0.le
        linarith

/-- **Cells beyond `√T`.** If every cell `n > √T` with `N ≤ n ≤ T` is at most
`K² n^{-2ε} e^{-s}`, these cells carry at most `K² e^{-s} (1 + T^{1-2ε}/(1-2ε))`. -/
theorem sum_receiverCell_top_le {ε K s : ℝ} (hε4 : 1 / 4 ≤ ε) (hε2 : ε < 1 / 2) {N T : ℕ}
    (hcell : ∀ n, N ≤ n → n ≤ T → T < n * n →
      receiverCell ε n ≤ K ^ 2 * ((n : ℝ) ^ (-(2 * ε)) * Real.exp (-s))) :
    ∑ n ∈ (Icc 1 T).filter (fun n => ¬ n < N) with ¬ n * n ≤ T, receiverCell ε n ≤
      K ^ 2 * Real.exp (-s) * (1 + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) := by
  calc _ ≤ ∑ n ∈ ((Icc 1 T).filter (fun n => ¬ n < N)).filter (fun n => ¬ n * n ≤ T),
          K ^ 2 * ((n : ℝ) ^ (-(2 * ε)) * Real.exp (-s)) := by
        refine sum_le_sum fun n hn => ?_
        simp only [mem_filter, mem_Icc, not_lt, not_le] at hn
        exact hcell n hn.1.2 hn.1.1.2 hn.2
    _ ≤ ∑ n ∈ Icc 1 T, K ^ 2 * ((n : ℝ) ^ (-(2 * ε)) * Real.exp (-s)) :=
        sum_le_sum_of_subset_of_nonneg (fun n hn => (mem_filter.mp (mem_filter.mp hn).1).1)
          fun n _ _ => by positivity
    _ = K ^ 2 * Real.exp (-s) * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 * ε)) := by
        rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_two_mul_le hε4 hε2 T) (by positivity)

/-- `n > √T`, `n ≤ T` and `log T ≥ 3` give the saving at scale `T`:
`(4/9) κσ(T) ≤ κσ(n)`. -/
theorem vkScale_comparable_of_sq_gt {n T : ℕ} (hn1 : 1 ≤ n) (hnT : n ≤ T) (hsq : T < n * n)
    (hT3 : 3 ≤ Real.log T) : 4 / 9 * vkScale T ≤ vkScale n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hsqR : (T : ℝ) < (n : ℝ) * n := by exact_mod_cast hsq
  have hlog := Real.log_lt_log hT0 hsqR
  rw [Real.log_mul hn0.ne' hn0.ne'] at hlog
  exact four_ninths_mul_vkScale_le (by linarith) (by linarith)
    (Real.log_le_log hn0 (by exact_mod_cast hnT))

/-! ## Growth below half damping -/

/-- **Growth of the receiver below half damping.** For `1/4 ≤ ε < 1/2` there is `C` with
`E_T(ε) ≤ C T^{1-2ε} e^{-κσ(T)/270}` for all large `T`. -/
theorem eventually_receiver_le_growth {ε : ℝ} (hε4 : 1 / 4 ≤ ε) (hε2 : ε < 1 / 2) :
    ∃ C : ℝ, ∀ᶠ T : ℕ in atTop, RHTower.pmPowerDampedDivisorDiscreteEnergy ε T ≤
      C * (T : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale T / 270)) := by
  obtain ⟨K, hK, N₀, hpre₀⟩ := exists_abs_weightCenteredPrefix_pmPowerDamped_le_vk
  set N := max N₀ 3 with hNdef
  have hN3 : 3 ≤ N := le_max_right _ _
  have hκ := vkKappa_pos
  -- the cell bound from `N` on
  have hcell : ∀ n, N ≤ n → receiverCell ε n ≤
      K ^ 2 * ((n : ℝ) ^ (-(2 * ε)) * Real.exp (-(2 * (vkKappa * vkScale n / 240)))) :=
    fun n hn => receiverCell_le_of_abs_le (by omega)
      (hpre₀ ε hε4 hε2.le n (le_trans (le_max_left _ _) hn))
  have hcell' : ∀ n, N ≤ n → receiverCell ε n ≤ K ^ 2 * (n : ℝ) ^ (-(2 * ε)) := by
    intro n hn
    have hvk := vkScale_nonneg (one_le_log_of_three_le (n := n) (hN3.trans hn))
    refine (hcell n hn).trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg K))
    exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.exp_le_one_iff.mpr (by nlinarith))
  set a := 1 - 2 * ε with hadef
  have ha0 : 0 < a := by rw [hadef]; linarith
  set C₀ := (N : ℝ) * (3 + 31 * N) ^ 2
  have hC₀ : 0 ≤ C₀ := by positivity
  refine ⟨C₀ + 2 * K ^ 2 + 2 * K ^ 2 / a, ?_⟩
  have hratio := (tendsto_vkScale_div_log.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_le_nhds (show (0 : ℝ) < a * 270 / (2 * vkKappa) by positivity))
  have hlog : Tendsto (fun T : ℕ => Real.log T) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hratio, hlog.eventually_ge_atTop 3,
    (tendsto_natCast_atTop_atTop.eventually (eventually_vk_conditions one_pos 0))]
    with T hTr hT3 hvkT
  obtain ⟨-, -, -, -, hsqT, -⟩ := hvkT
  rw [log_vkHeight] at hsqT
  simp only [Function.comp_apply] at hTr
  have hT0 : (0 : ℝ) < T := by
    by_contra h
    have : (T : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg T)
    rw [this, Real.log_zero] at hT3; linarith
  set s := vkKappa * vkScale T / 270 with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; have := Real.sqrt_nonneg (Real.log T); nlinarith
  -- the saving at the horizon stays below `(a/2) log T`
  have hsa : s ≤ a / 2 * Real.log T := by
    have hσ' : vkScale T ≤ a * 270 / (2 * vkKappa) * Real.log T := by
      rwa [div_le_iff₀ (by linarith)] at hTr
    rw [hsdef]
    calc vkKappa * vkScale T / 270 ≤ vkKappa * (a * 270 / (2 * vkKappa) * Real.log T) / 270 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hσ' hκ.le) (by norm_num)
      _ = a / 2 * Real.log T := by field_simp
  set G := (T : ℝ) ^ a * Real.exp (-s) with hGdef
  have hGsq : (T : ℝ) ^ (a / 2) ≤ G := by
    rw [hGdef, Real.rpow_def_of_pos hT0, Real.rpow_def_of_pos hT0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hG1 : 1 ≤ G := le_trans (Real.one_le_rpow (by
    have := Real.add_one_le_exp (Real.log T)
    rw [Real.exp_log hT0] at this; linarith) (by positivity)) hGsq
  -- the three ranges
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_receiverCell, ← sum_filter_add_sum_filter_not _
    (fun n => n < N), ← sum_filter_add_sum_filter_not _ (fun n => n * n ≤ T)]
  have h1 : ∑ n ∈ Icc 1 T with n < N, receiverCell ε n ≤ C₀ := sum_receiverCell_lt_le hε4 hε2.le T N
  have h2 := sum_receiverCell_mid_le hε4 hε2 (T := T) hcell'
  have h3 := sum_receiverCell_top_le (s := s) hε4 hε2 (N := N) (T := T) fun n hn hnT hsq => by
    refine (hcell n hn).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (sq_nonneg K))
    have := vkScale_comparable_of_sq_gt (by omega) hnT hsq hT3
    rw [hsdef]; nlinarith
  rw [← hadef] at h2 h3
  have hmid : K ^ 2 * (1 + (T : ℝ) ^ (a / 2) / a) ≤ K ^ 2 * (1 + G / a) :=
    mul_le_mul_of_nonneg_left (by have := div_le_div_of_nonneg_right hGsq ha0.le; linarith)
      (sq_nonneg K)
  have htop : K ^ 2 * Real.exp (-s) * (1 + (T : ℝ) ^ a / a) ≤ K ^ 2 * (1 + G / a) := by
    have hes : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hGe : Real.exp (-s) * ((T : ℝ) ^ a / a) = G / a := by rw [hGdef]; ring
    calc K ^ 2 * Real.exp (-s) * (1 + (T : ℝ) ^ a / a)
        = K ^ 2 * Real.exp (-s) + K ^ 2 * (Real.exp (-s) * ((T : ℝ) ^ a / a)) := by ring
      _ = K ^ 2 * Real.exp (-s) + K ^ 2 * (G / a) := by rw [hGe]
      _ ≤ K ^ 2 * 1 + K ^ 2 * (G / a) :=
          add_le_add (mul_le_mul_of_nonneg_left hes (sq_nonneg K)) le_rfl
      _ = K ^ 2 * (1 + G / a) := by ring
  have hdiff : (C₀ + 2 * K ^ 2 + 2 * K ^ 2 / a) * G -
      (C₀ + K ^ 2 * (1 + G / a) + K ^ 2 * (1 + G / a)) = (C₀ + 2 * K ^ 2) * (G - 1) := by
    field_simp; ring
  have hpos := mul_nonneg (add_nonneg hC₀ (by positivity : (0 : ℝ) ≤ 2 * K ^ 2))
    (sub_nonneg.mpr hG1)
  have hfin : (C₀ + 2 * K ^ 2 + 2 * K ^ 2 / a) * G =
      (C₀ + 2 * K ^ 2 + 2 * K ^ 2 / a) * (T : ℝ) ^ a * Real.exp (-s) := by rw [hGdef]; ring
  rw [← hadef, ← hsdef]
  linarith

/-- **The receiver against the period energy.** For `1/4 ≤ ε < 1/2` there is `C` with
`E_N(ε) ≤ C e^{-κσ(N)/270} E_prim(N)` for all large `N`. -/
theorem eventually_receiver_le_mul_periodEnergy {ε : ℝ} (hε4 : 1 / 4 ≤ ε) (hε2 : ε < 1 / 2) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, RHTower.pmPowerDampedDivisorDiscreteEnergy ε N ≤
      C * Real.exp (-(vkKappa * vkScale N / 270)) *
        sievePrimitiveEnergy N (pmPowerDampedRealWeight ε) := by
  obtain ⟨C, hC⟩ := eventually_receiver_le_growth hε4 hε2
  refine ⟨10368 * max C 0, ?_⟩
  filter_upwards [hC, eventually_sievePrimitiveEnergy_pmPowerDamped_growth (by linarith) hε2]
    with N hN hP
  have hlow := hP.1
  have he : 0 ≤ Real.exp (-(vkKappa * vkScale N / 270)) := (Real.exp_pos _).le
  have hC' : C * (N : ℝ) ^ (1 - 2 * ε) ≤ max C 0 * (N : ℝ) ^ (1 - 2 * ε) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc _ ≤ C * (N : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale N / 270)) := hN
    _ ≤ max C 0 * (N : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale N / 270)) :=
        mul_le_mul_of_nonneg_right hC' he
    _ ≤ max C 0 * (10368 * sievePrimitiveEnergy N (pmPowerDampedRealWeight ε)) *
          Real.exp (-(vkKappa * vkScale N / 270)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (le_max_right C 0)) he
    _ = _ := by ring

end

end GaloisForLFunctions.BezoutValuationIncidence
