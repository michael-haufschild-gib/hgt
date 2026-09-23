import GaloisForLFunctions.RHTower.SuzukiPositiveSharedPlaneOrderedProductNoGo

/-!
# Positive shared-plane Suzuki window-permutation no-go

The positive shared-plane obstruction is not an artifact of increasing order.  At every cutoff,
allow an adversary to permute all literal source labels in the macroscopic window `(2n,5n]`.
The prime block still supplies the same order-free paired cross-path floor, while the complementary
proper-prime-power logarithmic loss is permutation invariant and `o(sqrt n)`.  Canonical prefix and
suffix concatenation only increase cross surplus.  Thus the exactly completed observable tends to
positive infinity uniformly for every cutoff-dependent family of such permutations.

This kills within-scale adaptive reordering as CCM-FU's missing nonlocal producer.  Any
permutation-based survivor must transport a macroscopic portion of source mass across scale strata;
phase-twisted or indefinite cells remain outside this theorem.
-/

open scoped BigOperators
open Matrix
open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

def suzukiPositiveSharedPlaneTwentyWindowOrderedFullCellList
    (n : ℕ) (order : List ℕ) : List ℝ :=
  (suzukiPositiveSharedPlaneTwentyPrefixLabelList n).map
      (suzukiCenterStokesCartanCell (20 * n)) ++
    order.map (suzukiCenterStokesCartanCell (20 * n)) ++
      (suzukiPositiveSharedPlaneTwentySuffixLabelList n).map
        (suzukiCenterStokesCartanCell (20 * n))

def suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable
    (n : ℕ) (order : List ℕ) : ℝ :=
  suzukiCompletedStokesCartanWardObservable (20 * n) +
    2 * positiveSharedPlaneCrossSurplus
      (suzukiPositiveSharedPlaneTwentyWindowOrderedFullCellList n order)

theorem suzukiPositiveSharedPlaneTwentyWindowOrder_cell_nonneg
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) {order : List ℕ}
    (horder : order.Perm (suzukiPositiveSharedPlaneTwentyWindowLabelList n))
    {k : ℕ} (hk : k ∈ order) :
    0 ≤ suzukiCenterStokesCartanCell (20 * n) k := by
  have hk' : k ∈ suzukiPositiveSharedPlaneTwentyWindowLabelList n :=
    horder.mem_iff.mp hk
  apply suzukiCenterStokesCartanCell_twenty_mul_nonneg_of_mem hn
  simp [suzukiPositiveSharedPlaneTwentyWindowLabelList] at hk' ⊢
  omega

theorem suzukiPositiveSharedPlaneTwentyWindowOrderedFullCellList_perm
    (n : ℕ) {order : List ℕ}
    (horder : order.Perm (suzukiPositiveSharedPlaneTwentyWindowLabelList n)) :
    (suzukiPositiveSharedPlaneTwentyWindowOrderedFullCellList n order).Perm
      (suzukiPositiveSharedPlaneTwentyFullCellList n) := by
  let f := suzukiCenterStokesCartanCell (20 * n)
  have hm : (order.map f).Perm
      ((suzukiPositiveSharedPlaneTwentyWindowLabelList n).map f) := horder.map f
  have hp := hm.append_left ((suzukiPositiveSharedPlaneTwentyPrefixLabelList n).map f)
  have hs := hp.append_right ((suzukiPositiveSharedPlaneTwentySuffixLabelList n).map f)
  simpa [suzukiPositiveSharedPlaneTwentyWindowOrderedFullCellList,
    suzukiPositiveSharedPlaneTwentyFullCellList,
    suzukiPositiveSharedPlaneTwentyFullLabelList, List.map_append, f] using hs

theorem positiveSharedPlaneLogMass_windowOrderedFull_eq
    (n : ℕ) {order : List ℕ}
    (horder : order.Perm (suzukiPositiveSharedPlaneTwentyWindowLabelList n)) :
    positiveSharedPlaneLogMass
        (suzukiPositiveSharedPlaneTwentyWindowOrderedFullCellList n order) =
      suzukiStokesCartanLogMass (20 * n) := by
  have hp := suzukiPositiveSharedPlaneTwentyWindowOrderedFullCellList_perm n horder
  have hs := (hp.map (fun x : ℝ => Real.log (1 + x))).sum_eq
  calc
    positiveSharedPlaneLogMass
        (suzukiPositiveSharedPlaneTwentyWindowOrderedFullCellList n order) =
      positiveSharedPlaneLogMass (suzukiPositiveSharedPlaneTwentyFullCellList n) := by
        simpa [positiveSharedPlaneLogMass] using hs
    _ = suzukiStokesCartanLogMass (20 * n) :=
      positiveSharedPlaneLogMass_twentyFullCellList_eq n

theorem suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable_eq
    (n : ℕ) {order : List ℕ}
    (horder : order.Perm (suzukiPositiveSharedPlaneTwentyWindowLabelList n)) :
    suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable n order =
      2 * Real.log
        (positiveSharedPlaneWord
          (suzukiPositiveSharedPlaneTwentyWindowOrderedFullCellList n order) 0 0) +
        suzukiStokesCartanQuadraticCounterterm (20 * n) -
          suzukiUnitRieszRegularWardMass (Real.log ((20 * n : ℕ) : ℝ)) := by
  rw [suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable,
    suzukiCompletedStokesCartanWardObservable,
    positiveSharedPlaneCrossSurplus,
    positiveSharedPlaneLogMass_windowOrderedFull_eq n horder]
  ring

theorem suzukiPositiveSharedPlaneTwentyPrimePairFloor_sqrt_lower
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    Real.sqrt (n : ℝ) / (1024 * Real.sqrt 20) ≤
      (((_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card / 2 : ℕ) : ℝ) *
        (suzukiPositiveSharedPlaneTwentyPrimeFloor n / 8) := by
  let m := (_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card
  let q := m / 2
  let L2 := Real.log (2 * (n : ℝ))
  let L5 := Real.log (5 * (n : ℝ))
  have hnPos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
  have hL2 : 0 < L2 := Real.log_pos (by
    have hnNat : 0 < n := by exact_mod_cast hnPos
    exact_mod_cast (show 1 < 2 * n by omega))
  have hL5 : 0 < L5 := Real.log_pos (by
    have hnNat : 0 < n := by exact_mod_cast hnPos
    exact_mod_cast (show 1 < 5 * n by omega))
  have hm := suzukiMangoldtFivePrimeBlock_card_lower hn
  have hq := suzukiMangoldtFivePrimeBlock_card_quarter_le_div_two hn
  have hqLower : (n : ℝ) / (16 * L5) ≤ (q : ℝ) := by
    dsimp [m, q, L5] at hm hq ⊢
    calc
      (n : ℝ) / (16 * Real.log (5 * (n : ℝ))) =
          ((n : ℝ) / (4 * Real.log (5 * (n : ℝ)))) / 4 := by ring
      _ ≤ ((_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card : ℝ) / 4 :=
        div_le_div_of_nonneg_right hm (by norm_num)
      _ ≤ _ := hq
  have hsquare : 5 * (n : ℝ) ≤ (2 * (n : ℝ)) ^ (2 : ℕ) := by
    have hnFive : (5 : ℝ) ≤ n := by
      nlinarith [Real.add_one_le_exp (20 : ℝ)]
    nlinarith
  have hlogRatio : (1 / 2 : ℝ) ≤ L2 / L5 := by
    have hlog : L5 ≤ 2 * L2 := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < 5 * n) hsquare
      dsimp [L2, L5]
      rw [Real.log_pow] at h
      norm_num at h ⊢
      exact h
    rw [le_div_iff₀ hL5]
    nlinarith
  have hdelta0 := suzukiPositiveSharedPlaneTwentyPrimeFloor_nonneg hn
  have hqdelta : ((n : ℝ) / (16 * L5)) *
      (suzukiPositiveSharedPlaneTwentyPrimeFloor n / 8) ≤
        (q : ℝ) * (suzukiPositiveSharedPlaneTwentyPrimeFloor n / 8) :=
    mul_le_mul_of_nonneg_right hqLower (div_nonneg hdelta0 (by norm_num))
  have hsqrtN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnPos
  have hsqrt20 : 0 < Real.sqrt (20 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtMul : Real.sqrt (20 * (n : ℝ)) =
      Real.sqrt 20 * Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 20)]
  have hrewrite : ((n : ℝ) / (16 * L5)) *
      (suzukiPositiveSharedPlaneTwentyPrimeFloor n / 8) =
        (Real.sqrt (n : ℝ) / (512 * Real.sqrt 20)) * (L2 / L5) := by
    rw [suzukiPositiveSharedPlaneTwentyPrimeFloor]
    dsimp [L2]
    rw [hsqrtMul]
    field_simp [hL5.ne', hsqrtN.ne', hsqrt20.ne']
    rw [Real.sq_sqrt hnPos.le]
    ring
  have hscale0 : 0 ≤ Real.sqrt (n : ℝ) / (512 * Real.sqrt 20) := by positivity
  have hmain : Real.sqrt (n : ℝ) / (1024 * Real.sqrt 20) ≤
      (Real.sqrt (n : ℝ) / (512 * Real.sqrt 20)) * (L2 / L5) := by
    have h := mul_le_mul_of_nonneg_left hlogRatio hscale0
    calc
      Real.sqrt (n : ℝ) / (1024 * Real.sqrt 20) =
          (Real.sqrt (n : ℝ) / (512 * Real.sqrt 20)) * (1 / 2) := by ring
      _ ≤ _ := h
  rw [hrewrite] at hqdelta
  dsimp [q, m] at hqdelta ⊢
  exact hmain.trans hqdelta

theorem suzukiPositiveSharedPlaneTwentyPrimeCrossSurplus_sqrt_lower_of_perm
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) {xs : List ℝ}
    (hxs : xs.Perm (suzukiPositiveSharedPlaneTwentyPrimeCellList n)) :
    Real.sqrt (n : ℝ) / (1024 * Real.sqrt 20) ≤
      positiveSharedPlaneCrossSurplus xs := by
  have hdelta := suzukiPositiveSharedPlaneTwentyPrimeFloor_nonneg hn
  have hlower : ∀ x ∈ xs, suzukiPositiveSharedPlaneTwentyPrimeFloor n ≤ x := by
    intro x hx
    exact suzukiPositiveSharedPlaneTwentyPrimeCellList_lower hn
      (hxs.mem_iff.mp hx)
  have hupper : ∀ x ∈ xs, x ≤ 1 := by
    intro x hx
    exact suzukiPositiveSharedPlaneTwentyPrimeCellList_upper hn
      (hxs.mem_iff.mp hx)
  have hpair := positiveSharedPlaneCrossSurplus_pair_lower hdelta hlower hupper
  have hlog := half_mul_le_log_one_add_quarter hdelta
    ((suzukiPositiveSharedPlaneTwentyPrimeFloor_le_one hn).trans (by norm_num))
  have hlen := hxs.length_eq
  rw [hlen, suzukiPositiveSharedPlaneTwentyPrimeCellList_length] at hpair
  have hcount : (0 : ℝ) ≤
      (((_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card / 2 : ℕ) : ℝ) := by
    positivity
  have hfloor :
      (((_root_.RHTower.suzukiMangoldtFivePrimeBlock n).card / 2 : ℕ) : ℝ) *
          (suzukiPositiveSharedPlaneTwentyPrimeFloor n / 8) ≤
        positiveSharedPlaneCrossSurplus xs := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hcount]
  exact (suzukiPositiveSharedPlaneTwentyPrimePairFloor_sqrt_lower hn).trans hfloor

theorem suzukiPositiveSharedPlaneTwentyWindowOrderedCrossSurplus_lower
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) {order : List ℕ}
    (horder : order.Perm (suzukiPositiveSharedPlaneTwentyWindowLabelList n)) :
    Real.sqrt (n : ℝ) / (1024 * Real.sqrt 20) -
        suzukiPositiveSharedPlaneTwentyPrimePowerLoss n ≤
      positiveSharedPlaneCrossSurplus
        (order.map (suzukiCenterStokesCartanCell (20 * n))) := by
  let f := suzukiCenterStokesCartanCell (20 * n)
  have hf : ∀ k ∈ order, 0 ≤ f k := by
    intro k hk
    exact suzukiPositiveSharedPlaneTwentyWindowOrder_cell_nonneg hn horder hk
  have hpartition := positiveSharedPlaneCrossSurplus_map_ge_filter_sub_complementLogMass
    (fun k : ℕ => decide k.Prime) f hf
  have hprimeLabels := horder.filter (fun k : ℕ => decide k.Prime)
  have hprimeCells := hprimeLabels.map f
  have hprime : Real.sqrt (n : ℝ) / (1024 * Real.sqrt 20) ≤
      positiveSharedPlaneCrossSurplus
        ((order.filter fun k => decide k.Prime).map f) := by
    apply suzukiPositiveSharedPlaneTwentyPrimeCrossSurplus_sqrt_lower_of_perm hn
    simpa [suzukiPositiveSharedPlaneTwentyPrimeCellList,
      suzukiPositiveSharedPlaneTwentyPrimeLabelList] using hprimeCells
  have hnonprimeLabels := horder.filter (fun k : ℕ => decide (¬ k.Prime))
  have hnonprimeCells := hnonprimeLabels.map f
  have hnonprimeLog :
      positiveSharedPlaneLogMass
          ((order.filter fun k => decide (¬ k.Prime)).map f) =
        positiveSharedPlaneLogMass
          (suzukiPositiveSharedPlaneTwentyNonprimeCellList n) := by
    have hs := (hnonprimeCells.map (fun x : ℝ => Real.log (1 + x))).sum_eq
    simpa [positiveSharedPlaneLogMass,
      suzukiPositiveSharedPlaneTwentyNonprimeCellList,
      suzukiPositiveSharedPlaneTwentyWindowLabelList] using hs
  have hnonprime := suzukiPositiveSharedPlaneTwentyNonprimeLogMass_le hn
  have hpartition' :
      positiveSharedPlaneCrossSurplus
          ((order.filter fun k => decide k.Prime).map f) -
        positiveSharedPlaneLogMass
          ((order.filter fun k => decide (¬ k.Prime)).map f) ≤
      positiveSharedPlaneCrossSurplus (order.map f) := by
    simpa only [decide_not] using hpartition
  dsimp [f] at hpartition' hprime hnonprimeLog ⊢
  rw [hnonprimeLog] at hpartition'
  linarith

theorem suzukiPositiveSharedPlaneTwentyWindowOrderedFullCrossSurplus_lower
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) {order : List ℕ}
    (horder : order.Perm (suzukiPositiveSharedPlaneTwentyWindowLabelList n)) :
    Real.sqrt (n : ℝ) / (1024 * Real.sqrt 20) -
        suzukiPositiveSharedPlaneTwentyPrimePowerLoss n ≤
      positiveSharedPlaneCrossSurplus
        (suzukiPositiveSharedPlaneTwentyWindowOrderedFullCellList n order) := by
  let f := suzukiCenterStokesCartanCell (20 * n)
  have hprefix : ∀ x ∈ (suzukiPositiveSharedPlaneTwentyPrefixLabelList n).map f,
      0 ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    apply suzukiCenterStokesCartanCell_twenty_mul_nonneg_of_mem hn
    simp [suzukiPositiveSharedPlaneTwentyPrefixLabelList] at hk ⊢
    constructor
    · exact hk.1
    · omega
  have hmiddle : ∀ x ∈ order.map f, 0 ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact suzukiPositiveSharedPlaneTwentyWindowOrder_cell_nonneg hn horder hk
  have hsuffix : ∀ x ∈ (suzukiPositiveSharedPlaneTwentySuffixLabelList n).map f,
      0 ≤ x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    apply suzukiCenterStokesCartanCell_twenty_mul_nonneg_of_mem hn
    simp [suzukiPositiveSharedPlaneTwentySuffixLabelList] at hk ⊢
    omega
  have hmid := suzukiPositiveSharedPlaneTwentyWindowOrderedCrossSurplus_lower hn horder
  have hfull := positiveSharedPlaneCrossSurplus_middle_le
    ((suzukiPositiveSharedPlaneTwentyPrefixLabelList n).map f)
    (order.map f)
    ((suzukiPositiveSharedPlaneTwentySuffixLabelList n).map f)
    hprefix hmiddle hsuffix
  simpa [suzukiPositiveSharedPlaneTwentyWindowOrderedFullCellList, f] using hmid.trans hfull

theorem suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable_lower
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) {order : List ℕ}
    (horder : order.Perm (suzukiPositiveSharedPlaneTwentyWindowLabelList n)) :
    _root_.RHTower.unitRieszSuzukiGreen (Real.log ((20 * n : ℕ) : ℝ)) +
        2 * (Real.sqrt (n : ℝ) / (1024 * Real.sqrt 20) -
          suzukiPositiveSharedPlaneTwentyPrimePowerLoss n) ≤
      suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable n order := by
  have hnPos : 0 < n := by exact_mod_cast (Real.exp_pos 20).trans_le hn
  have hA : 2 ≤ 20 * n := by omega
  have hcompleted := suzukiCompletedStokesCartanWardObservable_eq_green_add_remainder
    (20 * n - 2)
  rw [Nat.sub_add_cancel hA] at hcompleted
  have hremainder := suzukiStokesCartanCubicRemainderMass_nonneg hA
  have hcross := suzukiPositiveSharedPlaneTwentyWindowOrderedFullCrossSurplus_lower hn horder
  rw [suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable, hcompleted]
  linarith

theorem suzukiPositiveSharedPlaneTwentyNormalizedLower_le_windowOrderedObservable_div_sqrt
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) {order : List ℕ}
    (horder : order.Perm (suzukiPositiveSharedPlaneTwentyWindowLabelList n)) :
    suzukiPositiveSharedPlaneTwentyNormalizedLower n ≤
      suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable n order /
        Real.sqrt (n : ℝ) := by
  have hnPos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnPos
  have hobs := suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable_lower hn horder
  have hdiv := div_le_div_of_nonneg_right hobs hsqrt.le
  rw [suzukiPositiveSharedPlaneTwentyNormalizedLower]
  calc
    _root_.RHTower.unitRieszSuzukiGreen (Real.log ((20 * n : ℕ) : ℝ)) /
        Real.sqrt (n : ℝ) +
          1 / (512 * Real.sqrt 20) -
        2 * (suzukiPositiveSharedPlaneTwentyPrimePowerLoss n /
          Real.sqrt (n : ℝ)) =
      (_root_.RHTower.unitRieszSuzukiGreen (Real.log ((20 * n : ℕ) : ℝ)) +
        2 * (Real.sqrt (n : ℝ) / (1024 * Real.sqrt 20) -
          suzukiPositiveSharedPlaneTwentyPrimePowerLoss n)) /
            Real.sqrt (n : ℝ) := by
      field_simp [hsqrt.ne']
      ring
    _ ≤ _ := hdiv

theorem tendsto_suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable_atTop
    (order : ℕ → List ℕ)
    (horder : ∀ n, (order n).Perm
      (suzukiPositiveSharedPlaneTwentyWindowLabelList n)) :
    Tendsto (fun n =>
      suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable n (order n))
      atTop atTop := by
  let c : ℝ := 1 / (512 * Real.sqrt 20)
  have hc : 0 < c := by dsimp [c]; positivity
  have hlower : ∀ᶠ n : ℕ in atTop,
      c / 2 < suzukiPositiveSharedPlaneTwentyNormalizedLower n :=
    (tendsto_order.1 tendsto_suzukiPositiveSharedPlaneTwentyNormalizedLower).1
      (c / 2) (by linarith)
  rw [tendsto_atTop]
  intro B
  have hsqrtTop : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlower,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (Real.exp 20),
    hsqrtTop.eventually_ge_atTop (2 * B / c)] with n hnLower hnLarge hnSqrt
  have hnorm :=
    suzukiPositiveSharedPlaneTwentyNormalizedLower_le_windowOrderedObservable_div_sqrt
      hnLarge (horder n)
  have hnPos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hnLarge
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnPos
  have hobs : (c / 2) * Real.sqrt (n : ℝ) <
      suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable n (order n) := by
    have hratio : c / 2 <
        suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable n (order n) /
          Real.sqrt (n : ℝ) := hnLower.trans_le hnorm
    rwa [lt_div_iff₀ hsqrtPos] at hratio
  have hB : B ≤ (c / 2) * Real.sqrt (n : ℝ) := by
    have hcne : c ≠ 0 := hc.ne'
    calc
      B = (c / 2) * (2 * B / c) := by field_simp
      _ ≤ (c / 2) * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_left hnSqrt (by linarith)
  exact hB.trans hobs.le

def SuzukiPositiveSharedPlaneWindowPermutationRouteKilled : Prop :=
  ∀ order : ℕ → List ℕ,
    (∀ n, (order n).Perm (suzukiPositiveSharedPlaneTwentyWindowLabelList n)) →
      ¬ ∃ B : ℝ, ∀ n : ℕ,
        |suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable n (order n)| ≤ B

theorem no_bounded_suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable :
    SuzukiPositiveSharedPlaneWindowPermutationRouteKilled := by
  intro order horder
  rintro ⟨B, hB⟩
  have hevent :=
    (tendsto_suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable_atTop
      order horder).eventually_ge_atTop (B + 1)
  rcases hevent.exists with ⟨n, hn⟩
  have habs := hB n
  have hself := le_abs_self
    (suzukiPositiveSharedPlaneTwentyWindowOrderedCompletedObservable n (order n))
  linarith

end GaloisForLFunctions.RHTower
