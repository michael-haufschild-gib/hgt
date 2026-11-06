import GaloisForLFunctions.IncommensurableGaborPinching.CriticalLineZeroProportion
import GaloisForLFunctions.RHTower.HorizontalSingletonFiberCharging
import Mathlib.Data.Finset.Sort

/-!
# Consecutive simple critical zeros

A non-singleton ordinate consumes at least two zero copies outside the simple critical
census. If it also carries a simple critical zero, its total multiplicity is at least three.
Writing `C` for singleton ordinates, `S` for simple critical zeros and `N` for all zero copies,
five consecutive singleton ordinates occur at least `C + 2S − 2N − 4` times.
The unconditional singleton and simple-critical densities make this at least `N/5000`
for every sufficiently large height. Every counted block skips no zero ordinate.
-/

open Complex Finset Filter
open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.IncommensurableGaborPinching
open _root_.RHTower

/-- Starting indices of `k + 1` consecutive members of `G` among `n` ordered sites. -/
def runStarts (k n : ℕ) (G : Finset ℕ) : Finset ℕ :=
  (range (n - k)).filter fun i => ∀ j ∈ range (k + 1), i + j ∈ G

abbrev fourRunStarts := runStarts 3

/-- Each bad site spoils at most `k + 1` starts; at most `k` starts meet the right edge. -/
theorem runStarts_card_bound (k n : ℕ) (G : Finset ℕ) (hG : G ⊆ range n) :
    (k + 1) * G.card ≤ (runStarts k n G).card + k * n + k := by
  classical
  let B := range n \ G
  let E := B.biUnion fun b => (range (k + 1)).image fun j => b - j
  have hcover : range (n - k) ⊆ runStarts k n G ∪ E := by
    intro i hi
    by_cases h : ∀ j ∈ range (k + 1), i + j ∈ G
    · exact mem_union_left _ (mem_filter.mpr ⟨hi, h⟩)
    · push Not at h
      obtain ⟨j, hj, hij⟩ := h
      have hi' := mem_range.mp hi
      have hj' := mem_range.mp hj
      have hb : i + j ∈ B := mem_sdiff.mpr ⟨mem_range.mpr (by omega), hij⟩
      exact mem_union_right _ (mem_biUnion.mpr ⟨i + j, hb,
        mem_image.mpr ⟨j, hj, Nat.add_sub_cancel i j⟩⟩)
  have hE : E.card ≤ (k + 1) * B.card := by
    calc E.card ≤ ∑ b ∈ B, ((range (k + 1)).image fun j => b - j).card := card_biUnion_le
      _ ≤ ∑ _b ∈ B, (k + 1) := sum_le_sum fun _ _ => (card_image_le).trans (by simp)
      _ = (k + 1) * B.card := by simp [mul_comm]
  have hB : B.card + G.card = n := by
    simpa only [card_range] using card_sdiff_add_card_eq_card hG
  have hc := (card_le_card hcover).trans (card_union_le _ _)
  rw [card_range] at hc
  have hn : n ≤ (runStarts k n G).card + (k + 1) * B.card + k := by omega
  have hmul := congrArg (fun m => (k + 1) * m) hB
  nlinarith only [hn, hmul]

theorem fourRunStarts_card_bound (n : ℕ) (G : Finset ℕ) (hG : G ⊆ range n) :
    4 * G.card ≤ (fourRunStarts n G).card + 3 * n + 3 := runStarts_card_bound 3 n G hG

/-- All occupied positive ordinates up to height `T`. -/
def xiOrdinateSet (T : ℝ) : Finset ℝ := (stripFinsetPos T).image Complex.im

/-- Ordinates carrying exactly one zero copy. -/
def xiCleanOrdinates (T : ℝ) : Finset ℝ :=
  (xiOrdinateSet T).filter fun t => xiHorizontalMultiplicity t = 1

private theorem fiber_eq_filter {T t : ℝ} (ht : t ∈ xiOrdinateSet T) :
    (stripFinsetPos T).filter (fun z => z.im = t) = stripHeightFinset t := by
  obtain ⟨z, hz, rfl⟩ := mem_image.mp ht
  obtain ⟨-, -, hz0, hzT, -⟩ := mem_stripFinsetPos.mp hz
  ext w
  simp only [mem_filter, mem_stripFinsetPos, mem_stripHeightFinset]
  constructor
  · rintro ⟨⟨h1, h2, -, -, h0⟩, him⟩
    exact ⟨h1, h2, him, h0⟩
  · rintro ⟨h1, h2, him, h0⟩
    exact ⟨⟨h1, h2, by simpa [him] using hz0, by simpa [him] using hzT, h0⟩, him⟩

private theorem fiber_simple_card_le_one (t : ℝ) :
    ((stripHeightFinset t).filter fun z =>
      z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1).card ≤ 1 := by
  apply card_le_one.mpr
  intro z hz w hw
  obtain ⟨hz, hzre, -⟩ := mem_filter.mp hz
  obtain ⟨hw, hwre, -⟩ := mem_filter.mp hw
  exact Complex.ext (hzre.trans hwre.symm)
    ((mem_stripHeightFinset.mp hz).2.2.1.trans (mem_stripHeightFinset.mp hw).2.2.1.symm)

/-- A spoiled simple critical ordinate has a reflected off-line pair as well. -/
private theorem fiber_census {T t : ℝ} (ht : t ∈ xiOrdinateSet T) :
    2 + ((stripHeightFinset t).filter fun z =>
      z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1).card ≤
      xiHorizontalMultiplicity t + 2 * (if xiHorizontalMultiplicity t = 1 then 1 else 0) := by
  classical
  have hcard := fiber_simple_card_le_one t
  by_cases hm : xiHorizontalMultiplicity t = 1
  · simp only [hm, if_true]
    omega
  simp only [if_neg hm, mul_zero, add_zero]
  obtain ⟨w, hw, hwim⟩ := mem_image.mp ht
  have hwf : w ∈ stripHeightFinset t := by
    rw [← fiber_eq_filter ht]
    exact mem_filter.mpr ⟨hw, hwim⟩
  have hp : 1 ≤ xiHorizontalMultiplicity t := by
    have hp := Nat.one_le_iff_ne_zero.mpr
      (xi_order_toNat_ne_zero (mem_stripHeightFinset.mp hwf).2.2.2)
    exact hp.trans (single_le_sum (f := fun u => (analyticOrderAt xi u).toNat)
      (fun _ _ => Nat.zero_le _) hwf)
  by_cases hs : ((stripHeightFinset t).filter fun z =>
      z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1).Nonempty
  · obtain ⟨z, hz⟩ := hs
    obtain ⟨hz, hzre, hzsimple⟩ := mem_filter.mp hz
    have hzim := (mem_stripHeightFinset.mp hz).2.2.1
    have hz' : z ∈ stripHeightFinset z.im := by simpa only [hzim] using hz
    have htwo := two_le_offLineFiber_sum hz' hzre hzsimple (by simpa only [hzim] using hm)
    have hsplit := sum_filter_add_sum_filter_not (stripHeightFinset z.im)
      (fun u => u.re = 1 / 2) (fun u => (analyticOrderAt xi u).toNat)
    rw [criticalFiber_eq_singleton hz' hzre, sum_singleton, hzsimple] at hsplit
    change 1 + (∑ u ∈ offLineFiber z.im, (analyticOrderAt xi u).toNat) =
      xiHorizontalMultiplicity z.im at hsplit
    rw [hzim] at hsplit htwo
    omega
  · rw [not_nonempty_iff_eq_empty.mp hs, card_empty]
    omega

/-- Reflection charges every non-singleton ordinate twice outside the simple critical census. -/
theorem xi_ordinate_census (T : ℝ) :
    2 * (xiOrdinateSet T).card + xiSimpleCriticalZeroCount T ≤
      xiPosZeroCount T + 2 * (xiCleanOrdinates T).card := by
  classical
  have hN : (∑ t ∈ xiOrdinateSet T, xiHorizontalMultiplicity t) = xiPosZeroCount T := by
    unfold xiPosZeroCount
    rw [← sum_fiberwise_of_maps_to
      (show Set.MapsTo Complex.im (stripFinsetPos T) (xiOrdinateSet T) from
        fun z hz => mem_image.mpr ⟨z, hz, rfl⟩) (fun z => (analyticOrderAt xi z).toNat)]
    exact sum_congr rfl fun t ht => by rw [fiber_eq_filter ht]; rfl
  have hS : (∑ t ∈ xiOrdinateSet T, ((stripHeightFinset t).filter fun z =>
      z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1).card) = xiSimpleCriticalZeroCount T := by
    unfold xiSimpleCriticalZeroCount
    rw [card_eq_sum_card_fiberwise
      (show Set.MapsTo Complex.im
        ((stripFinsetPos T).filter fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1)
        (xiOrdinateSet T) from fun z hz => mem_image.mpr ⟨z, (mem_filter.mp hz).1, rfl⟩)]
    apply sum_congr rfl
    intro t ht
    rw [← fiber_eq_filter ht, filter_filter, filter_filter]
    congr 2
    funext z
    exact propext and_comm
  have h := sum_le_sum (s := xiOrdinateSet T) (fun t ht => fiber_census ht)
  simp only [sum_add_distrib, sum_const, smul_eq_mul, ← mul_sum, sum_boole] at h
  rw [hN, hS] at h
  simpa only [xiCleanOrdinates, mul_comm, Nat.cast_id] using h

/-- The simple critical census injects into the occupied ordinates. -/
theorem xi_simple_le_ordinates (T : ℝ) :
    xiSimpleCriticalZeroCount T ≤ (xiOrdinateSet T).card := by
  classical
  apply card_le_card_of_injOn Complex.im
  · intro z hz
    exact mem_image.mpr ⟨z, (mem_filter.mp hz).1, rfl⟩
  · intro z hz w hw him
    exact Complex.ext ((mem_filter.mp hz).2.1.trans (mem_filter.mp hw).2.1.symm) him

/-- Counting singleton fibres by zeros or by ordinates gives the same number. -/
theorem card_xiCleanOrdinates (T : ℝ) :
    (xiCleanOrdinates T).card = xiSingletonFiberCount T := by
  classical
  have heq : xiCleanOrdinates T =
      ((stripFinsetPos T).filter fun z => xiHorizontalMultiplicity z.im = 1).image Complex.im := by
    ext t
    simp only [xiCleanOrdinates, xiOrdinateSet, mem_filter, mem_image]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, h⟩
      exact ⟨z, ⟨hz, h⟩, rfl⟩
    · rintro ⟨z, ⟨hz, h⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, h⟩
  rw [heq, xiSingletonFiberCount]
  apply card_image_of_injOn
  intro z hz w hw him
  have hline : ∀ u ∈ (stripFinsetPos T).filter (fun z => xiHorizontalMultiplicity z.im = 1),
      u.re = 1 / 2 := by
    intro u hu
    obtain ⟨hu, hm⟩ := mem_filter.mp hu
    obtain ⟨h1, h2, -, -, h0⟩ := mem_stripFinsetPos.mp hu
    exact xiHorizontalSingletonZero_re_eq_half ⟨mem_stripHeightFinset.mpr ⟨h1, h2, rfl, h0⟩, hm⟩
  exact Complex.ext ((hline z hz).trans (hline w hw).symm) him

/-- Ranks of the singleton ordinates in the increasing list of all occupied ordinates. -/
def xiCleanRanks (T : ℝ) : Finset ℕ :=
  ((univ : Finset (Fin (xiOrdinateSet T).card)).filter fun i =>
    xiHorizontalMultiplicity ((xiOrdinateSet T).orderEmbOfFin rfl i) = 1).image Fin.val

theorem xiCleanRanks_subset (T : ℝ) : xiCleanRanks T ⊆ range (xiOrdinateSet T).card := by
  intro i hi
  obtain ⟨j, -, rfl⟩ := mem_image.mp hi
  exact mem_range.mpr j.isLt

theorem card_xiCleanRanks (T : ℝ) : (xiCleanRanks T).card = (xiCleanOrdinates T).card := by
  classical
  rw [xiCleanRanks, card_image_of_injective _ Fin.val_injective, card_filter,
    xiCleanOrdinates, card_filter]
  have h := (Equiv.sum_comp ((xiOrdinateSet T).orderIsoOfFin rfl).toEquiv
    (fun t : xiOrdinateSet T => if xiHorizontalMultiplicity t = 1 then (1 : ℕ) else 0))
  exact h.trans (sum_coe_sort (xiOrdinateSet T)
    (fun t => if xiHorizontalMultiplicity t = 1 then (1 : ℕ) else 0))

theorem mem_xiCleanRanks_iff (T : ℝ) (j : Fin (xiOrdinateSet T).card) :
    j.val ∈ xiCleanRanks T ↔
      xiHorizontalMultiplicity ((xiOrdinateSet T).orderEmbOfFin rfl j) = 1 := by
  classical
  constructor
  · intro h
    obtain ⟨k, hk, hkj⟩ := mem_image.mp h
    have : k = j := Fin.val_injective hkj
    subst k
    exact (mem_filter.mp hk).2
  · intro h
    exact mem_image.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, h⟩, rfl⟩

/-- A block contains `k + 1` strictly ordered singleton ordinates and skips no zero ordinate. -/
def IsSingletonBlock (k : ℕ) (T : ℝ) (γ : Fin (k + 1) → ℝ) : Prop :=
  StrictMono γ ∧
    (∀ j, γ j ∈ xiOrdinateSet T ∧ xiHorizontalMultiplicity (γ j) = 1) ∧
    ∀ t ∈ xiOrdinateSet T, γ 0 ≤ t → t ≤ γ (Fin.last k) → ∃ j, γ j = t

abbrev IsFourSingletonBlock := IsSingletonBlock 3

/-- Every counted start produces a consecutive block of singleton ordinates. -/
theorem runStart_has_block {k : ℕ} {T : ℝ} {i : ℕ}
    (hi : i ∈ runStarts k (xiOrdinateSet T).card (xiCleanRanks T)) :
    ∃ γ, IsSingletonBlock k T γ := by
  classical
  obtain ⟨hi, hg⟩ := mem_filter.mp hi
  have hi' := mem_range.mp hi
  let idx : Fin (k + 1) → Fin (xiOrdinateSet T).card := fun j => ⟨i + j.val, by omega⟩
  let e := (xiOrdinateSet T).orderEmbOfFin rfl
  let γ : Fin (k + 1) → ℝ := fun j => e (idx j)
  refine ⟨γ, ?_, ?_, ?_⟩
  · apply e.strictMono.comp
    intro j k hjk
    change i + j.val < i + k.val
    exact Nat.add_lt_add_left hjk i
  · intro j
    refine ⟨orderEmbOfFin_mem _ _ _, ?_⟩
    exact (mem_xiCleanRanks_iff T (idx j)).mp (hg j.val (mem_range.mpr j.isLt))
  · intro t ht hlo hhi
    let r := (xiOrdinateSet T).orderIsoOfFin rfl |>.symm ⟨t, ht⟩
    have hr : e r = t := congrArg Subtype.val
      ((xiOrdinateSet T).orderIsoOfFin rfl |>.apply_symm_apply ⟨t, ht⟩)
    rw [← hr] at hlo hhi
    have hleft : idx 0 ≤ r := e.le_iff_le.mp hlo
    have hright : r ≤ idx (Fin.last k) := e.le_iff_le.mp hhi
    have hleft' : i ≤ r.val := hleft
    have hright' : r.val ≤ i + k := hright
    let j : Fin (k + 1) := ⟨r.val - i, by omega⟩
    refine ⟨j, ?_⟩
    have heq : idx j = r := Fin.ext (by dsimp [idx, j]; omega)
    change e (idx j) = t
    rw [heq, hr]

/-- Every ordinate in a singleton block carries a simple critical zero of ξ. -/
theorem IsSingletonBlock.simple_critical {k : ℕ} {T : ℝ} {γ : Fin (k + 1) → ℝ}
    (hγ : IsSingletonBlock k T γ) (j : Fin (k + 1)) :
    ∃ ρ ∈ stripFinsetPos T, ρ.im = γ j ∧ ρ.re = 1 / 2 ∧
      (analyticOrderAt xi ρ).toNat = 1 := by
  obtain ⟨ρ, hρ, him⟩ := mem_image.mp (hγ.2.1 j).1
  have hρf : ρ ∈ stripHeightFinset ρ.im := by
    obtain ⟨h1, h2, -, -, h0⟩ := mem_stripFinsetPos.mp hρ
    exact mem_stripHeightFinset.mpr ⟨h1, h2, rfl, h0⟩
  have hsingle : XiHorizontalSingletonZero ρ := ⟨hρf, by rw [him]; exact (hγ.2.1 j).2⟩
  exact ⟨ρ, hρ, him, xiHorizontalSingletonZero_re_eq_half hsingle,
    xiHorizontalSingletonZero_order_eq_one hsingle⟩

/-- The same block consists of simple zeros of ζ on the critical line. -/
theorem IsSingletonBlock.simple_zeta {k : ℕ} {T : ℝ} {γ : Fin (k + 1) → ℝ}
    (hγ : IsSingletonBlock k T γ) (j : Fin (k + 1)) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ ρ.im = γ j ∧
      (analyticOrderAt riemannZeta ρ).toNat = 1 := by
  obtain ⟨ρ, hρ, him, hre, hord⟩ := hγ.simple_critical j
  obtain ⟨h0, h1, -, -, hxi⟩ := mem_stripFinsetPos.mp hρ
  refine ⟨ρ, (xi_zero_iff_zeta_zero_of_mem_strip h0 h1).mp hxi, hre, him, ?_⟩
  rwa [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨h0, h1⟩] at hord

/-- Number of four-blocks of consecutive occupied ordinates, each of total multiplicity one. -/
def xiFourRunCount (T : ℝ) : ℕ :=
  (fourRunStarts (xiOrdinateSet T).card (xiCleanRanks T)).card

/-- The finite four-run bound, including the endpoint loss. -/
theorem xi_four_runs_finite (T : ℝ) :
    3 * xiSimpleCriticalZeroCount T ≤ xiFourRunCount T + 2 * xiPosZeroCount T + 3 := by
  have h := fourRunStarts_card_bound _ _ (xiCleanRanks_subset T)
  rw [card_xiCleanRanks] at h
  have hc := xi_ordinate_census T
  have hs := xi_simple_le_ordinates T
  change 4 * (xiCleanOrdinates T).card ≤ xiFourRunCount T + 3 * (xiOrdinateSet T).card + 3 at h
  omega

/-- Unconditionally, at least `0.01750213 − ε` times the full zero census are starts of
four consecutive singleton ordinates, apart from the fixed endpoint loss of three. -/
theorem xi_four_runs_positive_proportion :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1750213 / 100000000 - ε) * (xiPosZeroCount T : ℝ) ≤ xiFourRunCount T + 3 := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := simple_critical_proportion_ge_67250071 (ε / 3) (by positivity)
  refine ⟨T₀, fun T hT => ?_⟩
  have hs := hT₀ T hT
  rw [zeta23_Ncount_zero_eq_xiPosZeroCount, zeta23_N0simple_zero_eq_xiSimpleCriticalZeroCount] at hs
  have hf : (3 : ℝ) * xiSimpleCriticalZeroCount T ≤
      xiFourRunCount T + 2 * xiPosZeroCount T + 3 := by exact_mod_cast xi_four_runs_finite T
  linarith

/-- Number of five consecutive occupied ordinates, all singleton fibres. -/
def xiFiveRunCount (T : ℝ) : ℕ :=
  (runStarts 4 (xiOrdinateSet T).card (xiCleanRanks T)).card

/-- The singleton census improves the five-run bound beyond a proportion-only union bound. -/
theorem xi_five_runs_finite (T : ℝ) :
    xiSingletonFiberCount T + 2 * xiSimpleCriticalZeroCount T ≤
      xiFiveRunCount T + 2 * xiPosZeroCount T + 4 := by
  have h := runStarts_card_bound 4 _ _ (xiCleanRanks_subset T)
  rw [card_xiCleanRanks, card_xiCleanOrdinates] at h
  have hc := xi_ordinate_census T
  rw [card_xiCleanOrdinates] at hc
  change 5 * xiSingletonFiberCount T ≤ xiFiveRunCount T + 4 * (xiOrdinateSet T).card + 4 at h
  omega

/-- The exact lower density furnished by the singleton and simple-critical censuses. -/
theorem xi_five_runs_positive_proportion :
    ∀ ε > 0, ∀ᶠ T : ℝ in atTop,
      (3 * Zeta23.ThmD.HD 1 - 2 - 11 * Real.pi / 2000 - ε) *
        (xiPosZeroCount T : ℝ) ≤ xiFiveRunCount T + 4 := by
  intro ε hε
  have hbdd : IsBoundedUnder (fun x y : ℝ => x ≥ y) atTop xiSingletonFiberRatio :=
    isBoundedUnder_of ⟨0, fun T => xiSingletonFiberRatio_nonneg T⟩
  have hlim : Zeta23.ThmD.HD 1 - 11 * Real.pi / 2000 - ε / 3 <
      liminf xiSingletonFiberRatio atTop := by
    linarith only [horizontalSingleton_density_montgomeryTaylor, hε]
  have hc := eventually_lt_of_lt_liminf hlim hbdd
  obtain ⟨T₀, hs⟩ := lamzouri_montgomeryTaylor_simpleCritical_epsilon (ε / 3) (by positivity)
  filter_upwards [hc, eventually_ge_atTop T₀, eventually_pos_xiPosZeroCount_of_zeta23]
    with T hC hT hN
  rw [xiSingletonFiberRatio, lt_div_iff₀ hN] at hC
  have hS := hs T hT
  have hF : (xiSingletonFiberCount T : ℝ) + 2 * xiSimpleCriticalZeroCount T ≤
      xiFiveRunCount T + 2 * xiPosZeroCount T + 4 := by exact_mod_cast xi_five_runs_finite T
  linarith

/-- At every sufficiently large height, five-block starts number at least `N(T)/5000`. -/
theorem xi_five_runs_one_five_thousandth :
    ∀ᶠ T : ℝ in atTop, (xiPosZeroCount T : ℝ) / 5000 ≤ xiFiveRunCount T := by
  let δ := 3 * Zeta23.ThmD.HD 1 - 2 - 11 * Real.pi / 2000 - 1 / 5000
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith only [HD_one_ge_67250070, Real.pi_lt_d4]
  have hlarge : ∀ᶠ T : ℝ in atTop, 8 / δ ≤ (xiPosZeroCount T : ℝ) := by
    have h := (Zeta23.tendsto_Ncount_zero_atTop Zeta23.zetaSeam
      Zeta23.paperInputs_zeta.RvM).eventually_ge_atTop (8 / δ)
    simpa only [zeta23_Ncount_zero_eq_xiPosZeroCount] using h
  filter_upwards [xi_five_runs_positive_proportion (δ / 2) (by positivity), hlarge]
    with T hR hN
  have hpay : 8 ≤ δ * (xiPosZeroCount T : ℝ) := (div_le_iff₀ hδ).mp hN |>.trans_eq (mul_comm _ _)
  dsimp [δ] at hpay hR
  nlinarith only [hR, hpay]

/-- Unconditionally, every sufficiently large census contains a consecutive five-block of
simple critical zeros, with no other zero sharing any of its ordinates. -/
theorem eventually_exists_five_simple_critical_block :
    ∀ᶠ T : ℝ in atTop, ∃ γ : Fin 5 → ℝ, IsSingletonBlock 4 T γ := by
  filter_upwards [xi_five_runs_one_five_thousandth, eventually_pos_xiPosZeroCount_of_zeta23]
    with T hR hN
  have hpos : 0 < xiFiveRunCount T := by
    have : (0 : ℝ) < xiFiveRunCount T := lt_of_lt_of_le (div_pos hN (by norm_num)) hR
    exact_mod_cast this
  obtain ⟨i, hi⟩ := card_pos.mp hpos
  exact runStart_has_block hi

end GaloisForLFunctions.IncommensurableGaborPinching
