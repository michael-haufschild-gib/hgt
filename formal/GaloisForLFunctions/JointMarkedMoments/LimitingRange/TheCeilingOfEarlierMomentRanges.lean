import GaloisForLFunctions.JointMarkedMoments.LimitingRange.TheMomentRecursionStaysBelowTheLimit
import Mathlib.Order.Monotone.Union
import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.Convex.Slope

/-!
# A ceiling for every earlier joint moment range

Proposition 6.3 allows arbitrary reuse of proved moment rectangles, every positive step
`0 < u < 1/6`, every cutoff and the mark cap `1/6`. Every available rectangle `(R, S)` then obeys
`S ≤ Ŝ(R)` for the ceiling
```
Ŝ(R) = (1 − R)/2 (R ≤ 2/3),  1/6 (2/3 < R ≤ R_c),  M_ref − R (R_c < R ≤ R₊),
       (1 − R)/2 + G(R) (R₊ < R ≤ 7/9),  (1 − R)/2 (R > 7/9),
```
with `M_ref = (48 + √909)/90` (the root of `180M² − 192M + 31 = 0`), `R_c = M_ref − 1/6` and `R₊`
the end of the sublevel set `{F_G ≤ M_ref}` of `F_G(R) = (1 + R)/2 + G(R)` on `[R_c, 7/9]`.

* `stage_total_le_of_class`: the envelope argument. If `A_ν R + ν F(R) ≥ 5/6`,
  `A_ν = 5/4 − 3ν/2`, then the short and long counts of the amplitude class `(ν, ν)` force
  `r + S′ ≤ H F(R) + u(1 + 1/ν)` for every cutoff `w`.
* `referenceCutoff_identity`, `one_add_inv_referenceCutoff`: `A_ν R_c + ν M_ref = 5/6` and
  `1 + 1/ν = 6M_ref` at `ν_ref = 1/(6M_ref − 1)`.
* `monotone_ceilingTotal`, `antitone_markCeiling`: `R + Ŝ(R)` is nondecreasing and `Ŝ` is
  nonincreasing.
* `admitted_stage_le_markCeiling`: one admitted stage from a rectangle below the ceiling stays
  below the ceiling.
* `available_le_markCeiling`: every rectangle in the least set closed under initial rectangles,
  truncation and admitted stages lies below the ceiling.
* `markCeiling_eq_limit`: on `[0.734, 7/9]` the ceiling is the limiting range `(1 − R)/2 + G(R)`.
-/

namespace GaloisForLFunctions.JointMarkedMoments

open Real Set Filter

noncomputable section

/-! ### The envelope argument -/

/-- The long-sum slope `A_ν = 5/4 − 3ν/2 = (3/2)(5/6 − ν)`. -/
def longSlope (ν : ℝ) : ℝ := 5 / 4 - 3 * ν / 2

/-- The short-sum count `H − νHw − e min(s, Hσ)` of an amplitude class `(ν, e)` with cutoff `w`
and reference marked length `σ`. -/
def shortCount (H ν e w σ s : ℝ) : ℝ := H - ν * H * w - e * min s (H * σ)

/-- The long-sum count `H/6 + (5/6 − ν)H(3w/2 + τ)`. -/
def longCount (H ν w τ : ℝ) : ℝ := H / 6 + (5 / 6 - ν) * H * (3 * w / 2 + τ)

/-- The envelope argument: a controlled amplitude class `(ν, ν)` gives
`r + S′ ≤ H F(R) + u(1 + 1/ν)` whenever `A_ν R + ν F(R) ≥ 5/6`. -/
theorem stage_total_le_of_class {ν H u FR R r S' w σ τ : ℝ} (hν : 0 < ν) (hν' : ν ≤ 3 / 4)
    (hH : 0 ≤ H) (hτ : 0 ≤ τ) (h30 : 5 / 6 ≤ longSlope ν * R + ν * FR)
    (hshort : shortCount H ν ν w σ (S' - u) + ν * r + ν * (S' - u) ≤ H + u)
    (hlong : longCount H ν w τ + ν * r + ν * (S' - u) ≤ H + u)
    (href : w ≤ R → w + σ ≤ FR) :
    r + S' ≤ H * FR + u * (1 + 1 / ν) := by
  have e : ν * (H * FR + u * (1 + 1 / ν)) = ν * H * FR + ν * u + u := by
    field_simp; ring
  refine le_of_mul_le_mul_left ?_ hν
  rw [e]
  rcases le_or_gt w R with hw | hw
  · -- a short cutoff: the reference rectangle at `w` lies below `F(R)`
    have hmin : min (S' - u) (H * σ) ≤ H * σ := min_le_right _ _
    have href' := mul_le_mul_of_nonneg_left (href hw) (mul_nonneg hν.le hH)
    unfold shortCount at hshort
    nlinarith [mul_le_mul_of_nonneg_left hmin hν.le]
  · -- a long cutoff: `A_ν w > A_ν R` and the supporting inequality `(30)`
    unfold longCount at hlong
    have hA : 0 ≤ longSlope ν := by unfold longSlope; linarith
    have h1 : 0 ≤ (5 / 6 - ν) * H * τ := by
      have : 0 ≤ 5 / 6 - ν := by linarith
      positivity
    have h2 : longSlope ν * H * R ≤ longSlope ν * H * w :=
      mul_le_mul_of_nonneg_left hw.le (mul_nonneg hA hH)
    have h3 := mul_le_mul_of_nonneg_left h30 hH
    unfold longSlope at h2 h3
    nlinarith

/-! ### Monotonicity and continuity of `G` -/

theorem limitSlope_nonpos {y : ℝ} (hy : 2 / 3 < y) (hy' : y ≤ 7 / 9) : limitSlope y ≤ 0 := by
  rcases eq_or_lt_of_le hy' with h | h
  · rw [h, limitSlope_seven_ninths]
  have h1 := limitImprovement_tangent_le (R := y) (r := 7 / 9) hy (by norm_num)
  have h2 := limitImprovement_tangent_le (R := 7 / 9) (r := y) (by norm_num) hy.le
  rw [limitImprovement_seven_ninths] at h1
  rw [limitImprovement_seven_ninths, limitSlope_seven_ninths] at h2
  nlinarith

theorem limitImprovement_antitoneOn : AntitoneOn limitImprovement (Ioc (2 / 3) (7 / 9)) := by
  intro x hx y hy hxy
  have h1 := limitImprovement_tangent_le hy.1 hx.1.le
  have h2 := limitSlope_nonpos hy.1 hy.2
  nlinarith

theorem continuousOn_limitImprovement : ContinuousOn limitImprovement (Ioi (2 / 3)) :=
  fun _ hx => (hasDerivAt_limitImprovement hx).continuousAt.continuousWithinAt

theorem le_limitCore_of_pow_le {R p : ℝ} (hp : 0 ≤ p) (h : p ^ 5 ≤ 7 * R ^ 4 * (R - 2 / 3)) :
    p ≤ limitCore R := by
  have e : (p ^ 5) ^ (1 / 5 : ℝ) = p := by
    rw [show (1 / 5 : ℝ) = ((5 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast hp (by norm_num)
  calc p = (p ^ 5) ^ (1 / 5 : ℝ) := e.symm
    _ ≤ limitCore R := Real.rpow_le_rpow (by positivity) h (by norm_num)

theorem limitCore_le_of_le_pow {R q : ℝ} (hq : 0 ≤ q) (hb : 0 ≤ 7 * R ^ 4 * (R - 2 / 3))
    (h : 7 * R ^ 4 * (R - 2 / 3) ≤ q ^ 5) : limitCore R ≤ q := by
  have e : (q ^ 5) ^ (1 / 5 : ℝ) = q := by
    rw [show (1 / 5 : ℝ) = ((5 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast hq (by norm_num)
  calc limitCore R ≤ (q ^ 5) ^ (1 / 5 : ℝ) := Real.rpow_le_rpow hb h (by norm_num)
    _ = q := e

/-! ### The reference constants -/

/-- `M_ref = (48 + √909)/90`. -/
def referenceTotal : ℝ := (48 + √909) / 90

/-- `ν_ref = 1/(6M_ref − 1)`. -/
def referenceCutoff : ℝ := 1 / (6 * referenceTotal - 1)

/-- `R_c = M_ref − 1/6`. -/
def ceilingStart : ℝ := referenceTotal - 1 / 6

/-- The total length `F_G(R) = (1 + R)/2 + G(R)` of the limiting moment range. -/
def limitTotal (R : ℝ) : ℝ := (1 + R) / 2 + limitImprovement R

theorem sqrt_909_bounds : (301496 / 10000 : ℝ) < √909 ∧ √909 < 301497 / 10000 :=
  ⟨(Real.lt_sqrt (by norm_num)).2 (by norm_num), (Real.sqrt_lt' (by norm_num)).2 (by norm_num)⟩

theorem referenceTotal_bounds :
    (868328 / 1000000 : ℝ) < referenceTotal ∧ referenceTotal < 868331 / 1000000 := by
  obtain ⟨h1, h2⟩ := sqrt_909_bounds
  unfold referenceTotal
  constructor <;> linarith

theorem ceilingStart_bounds : (7016 / 10000 : ℝ) < ceilingStart ∧ ceilingStart < 7017 / 10000 := by
  obtain ⟨h1, h2⟩ := referenceTotal_bounds
  unfold ceilingStart
  constructor <;> linarith

/-- `180 M_ref² − 192 M_ref + 31 = 0`. -/
theorem referenceTotal_quadratic : 180 * referenceTotal ^ 2 - 192 * referenceTotal + 31 = 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 909 by norm_num)
  unfold referenceTotal
  linear_combination (1 / 45 : ℝ) * hs

/-- Identity `(29)`: `A_{ν_ref} R_c + ν_ref M_ref = 5/6`. -/
theorem referenceCutoff_identity :
    longSlope referenceCutoff * ceilingStart + referenceCutoff * referenceTotal = 5 / 6 := by
  have hq := referenceTotal_quadratic
  have hM := referenceTotal_bounds
  unfold referenceCutoff ceilingStart longSlope
  generalize referenceTotal = M at hq hM ⊢
  obtain ⟨D, rfl⟩ : ∃ D, M = (1 + D) / 6 := ⟨6 * M - 1, by ring⟩
  have hD : D ≠ 0 := by rintro rfl; norm_num at hM
  have key : (5 / 4 - 3 * (1 / (6 * ((1 + D) / 6) - 1)) / 2) * ((1 + D) / 6 - 1 / 6) +
      1 / (6 * ((1 + D) / 6) - 1) * ((1 + D) / 6) =
        5 / 6 + (5 * D ^ 2 - 22 * D + 4) / (24 * D) := by
    rw [show 6 * ((1 + D) / 6) - 1 = D by ring]
    field_simp
    ring
  have hq' : 5 * D ^ 2 - 22 * D + 4 = 0 := by linear_combination hq
  rw [key, hq', zero_div, add_zero]

/-- Identity `(29)`: `1 + 1/ν_ref = 6 M_ref`. -/
theorem one_add_inv_referenceCutoff : 1 + 1 / referenceCutoff = 6 * referenceTotal := by
  unfold referenceCutoff; rw [one_div_one_div]; ring

theorem referenceCutoff_bounds : 0 < referenceCutoff ∧ referenceCutoff ≤ 1 / 4 := by
  have hM := referenceTotal_bounds
  unfold referenceCutoff
  refine ⟨div_pos one_pos (by linarith), ?_⟩
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- `F_G(R_c) < M_ref`: `G` decreases on `(2/3, 7/9]` and `H(0.7016) ≥ 0.568`. -/
theorem limitTotal_ceilingStart_lt : limitTotal ceilingStart < referenceTotal := by
  obtain ⟨h1, h2⟩ := ceilingStart_bounds
  have h3 := referenceTotal_bounds.1
  have hG : limitImprovement ceilingStart ≤ limitImprovement (7016 / 10000) :=
    limitImprovement_antitoneOn ⟨by norm_num, by norm_num⟩ ⟨by linarith, by linarith⟩ h1.le
  have hH : (568 / 1000 : ℝ) ≤ limitCore (7016 / 10000) :=
    le_limitCore_of_pow_le (by norm_num) (by norm_num)
  unfold limitImprovement at hG
  unfold limitTotal limitImprovement
  linarith

theorem limitTotal_seven_ninths : limitTotal (7 / 9) = 8 / 9 := by
  unfold limitTotal; rw [limitImprovement_seven_ninths]; norm_num

/-- `F_G(0.734) > M_ref`, from `H(0.734) ≤ 0.6719`. -/
theorem referenceTotal_lt_limitTotal_734 : referenceTotal < limitTotal (734 / 1000) := by
  have h3 := referenceTotal_bounds.2
  have hH : limitCore (734 / 1000) ≤ 6719 / 10000 :=
    limitCore_le_of_le_pow (by norm_num) (by norm_num) (by norm_num)
  unfold limitTotal limitImprovement
  linarith

/-! ### The join point `R₊` -/

/-- The sublevel set `{R ∈ [R_c, 7/9] : F_G(R) ≤ M_ref}`. -/
def joinSet : Set ℝ := {R | ceilingStart ≤ R ∧ R ≤ 7 / 9 ∧ limitTotal R ≤ referenceTotal}

/-- `R₊ = sup {R ∈ [R_c, 7/9] : F_G(R) ≤ M_ref}`. -/
def ceilingJoin : ℝ := sSup joinSet

theorem joinSet_nonempty : joinSet.Nonempty :=
  ⟨ceilingStart, le_rfl, by linarith [ceilingStart_bounds.2], limitTotal_ceilingStart_lt.le⟩

theorem joinSet_bddAbove : BddAbove joinSet := ⟨7 / 9, fun _ hx => hx.2.1⟩

theorem continuousOn_limitTotal {a : ℝ} (ha : 2 / 3 < a) : ContinuousOn limitTotal (Ici a) := by
  have h1 : ContinuousOn limitImprovement (Ici a) :=
    continuousOn_limitImprovement.mono fun x hx => lt_of_lt_of_le ha hx
  have h0 : ContinuousOn (fun R : ℝ => (1 + R) / 2) (Ici a) :=
    ((continuousOn_const.add continuousOn_id).div_const 2)
  exact h0.add h1

theorem isClosed_joinSet : IsClosed joinSet := by
  have hc : ContinuousOn limitTotal (Icc ceilingStart (7 / 9)) :=
    (continuousOn_limitTotal (a := ceilingStart) (by linarith [ceilingStart_bounds.1])).mono
      Icc_subset_Ici_self
  have := hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := referenceTotal))
  convert this using 1
  ext x
  simp only [joinSet, mem_setOf_eq, mem_inter_iff, mem_Icc, mem_preimage, mem_Iic, and_assoc]

theorem ceilingJoin_mem : ceilingJoin ∈ joinSet :=
  isClosed_joinSet.csSup_mem joinSet_nonempty joinSet_bddAbove

theorem ceilingStart_le_ceilingJoin : ceilingStart ≤ ceilingJoin := ceilingJoin_mem.1

/-- `F_G ≤ M_ref` on `[R_c, R₊]`. -/
theorem limitTotal_le_of_mem {x : ℝ} (hx : ceilingStart ≤ x) (hx' : x ≤ ceilingJoin) :
    limitTotal x ≤ referenceTotal := by
  have hJ := ceilingJoin_mem.2.2
  have hS := limitTotal_ceilingStart_lt
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]; exact hS.le
  have hlt : ceilingStart < ceilingJoin := lt_of_lt_of_le h hx'
  have hden : 0 < ceilingJoin - ceilingStart := by linarith
  set a := (ceilingJoin - x) / (ceilingJoin - ceilingStart)
  set b := (x - ceilingStart) / (ceilingJoin - ceilingStart)
  have ha : 0 ≤ a := div_nonneg (by linarith) hden.le
  have hb : 0 ≤ b := div_nonneg (by linarith) hden.le
  have hab : a + b = 1 := by simp only [a, b]; field_simp; ring
  have hpt : a * ceilingStart + b * ceilingJoin = x := by simp only [a, b]; field_simp; ring
  have hconv := (convexOn_limitImprovement).2 (x := ceilingStart) (y := ceilingJoin)
    (by simp only [mem_Ioi]; linarith [ceilingStart_bounds.1])
    (by simp only [mem_Ioi]; linarith [ceilingStart_bounds.1]) ha hb hab
  simp only [smul_eq_mul, hpt] at hconv
  unfold limitTotal at hJ hS ⊢
  have h1 := mul_le_mul_of_nonneg_left hS.le ha
  have h2 := mul_le_mul_of_nonneg_left hJ hb
  have hM : a * referenceTotal + b * referenceTotal = referenceTotal := by
    rw [← add_mul, hab, one_mul]
  nlinarith

theorem ceilingJoin_lt_734 : ceilingJoin < 734 / 1000 := by
  by_contra h
  have := limitTotal_le_of_mem (x := 734 / 1000) (by linarith [ceilingStart_bounds.2])
    (le_of_not_gt h)
  linarith [referenceTotal_lt_limitTotal_734]

theorem ceilingJoin_lt_seven_ninths : ceilingJoin < 7 / 9 := by
  linarith [ceilingJoin_lt_734]

theorem referenceTotal_lt_limitTotal {x : ℝ} (hx : ceilingJoin < x) (hx' : x ≤ 7 / 9) :
    referenceTotal < limitTotal x := by
  by_contra h
  have hmem : x ∈ joinSet := ⟨by linarith [ceilingStart_le_ceilingJoin], hx', le_of_not_gt h⟩
  exact absurd (le_csSup joinSet_bddAbove hmem) (not_le.2 hx)

/-- `F_G` increases on `(R₊, 7/9]`: its slope from `R_c` is positive there. -/
theorem limitTotal_le_limitTotal {x y : ℝ} (hx : ceilingJoin < x) (hxy : x ≤ y) (hy : y ≤ 7 / 9) :
    limitTotal x ≤ limitTotal y := by
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  have hc := ceilingStart_bounds.1
  have hS := limitTotal_ceilingStart_lt
  have hX := referenceTotal_lt_limitTotal hx (h.le.trans hy)
  have hcx : ceilingStart < x := lt_of_le_of_lt ceilingStart_le_ceilingJoin hx
  have hslope := (convexOn_limitImprovement).slope_mono_adjacent (x := ceilingStart) (y := x) (z := y)
    (by simp only [mem_Ioi]; linarith) (by simp only [mem_Ioi]; linarith) hcx h
  have hd1 : 0 < x - ceilingStart := by linarith
  have hd2 : 0 < y - x := by linarith
  rw [div_le_div_iff₀ hd1 hd2] at hslope
  unfold limitTotal at hS hX ⊢
  nlinarith

/-! ### The ceiling -/

/-- The ceiling `Ŝ` of all available joint marked lengths. -/
def markCeiling (R : ℝ) : ℝ :=
  if R ≤ 2 / 3 then (1 - R) / 2
  else if R ≤ ceilingStart then 1 / 6
  else if R ≤ ceilingJoin then referenceTotal - R
  else if R ≤ 7 / 9 then (1 - R) / 2 + limitImprovement R
  else (1 - R) / 2

/-- The total length `R + Ŝ(R)`. -/
def ceilingTotal (R : ℝ) : ℝ := R + markCeiling R

theorem markCeiling_of_le {R : ℝ} (h : R ≤ 2 / 3) : markCeiling R = (1 - R) / 2 := by
  unfold markCeiling; rw [if_pos h]

theorem markCeiling_of_start {R : ℝ} (h1 : 2 / 3 < R) (h2 : R ≤ ceilingStart) :
    markCeiling R = 1 / 6 := by
  unfold markCeiling; rw [if_neg (not_le.2 h1), if_pos h2]

theorem markCeiling_of_join {R : ℝ} (h1 : ceilingStart < R) (h2 : R ≤ ceilingJoin) :
    markCeiling R = referenceTotal - R := by
  have : 2 / 3 < R := by linarith [ceilingStart_bounds.1]
  unfold markCeiling; rw [if_neg (not_le.2 this), if_neg (not_le.2 h1), if_pos h2]

theorem markCeiling_of_limit {R : ℝ} (h1 : ceilingJoin < R) (h2 : R ≤ 7 / 9) :
    markCeiling R = (1 - R) / 2 + limitImprovement R := by
  have h0 : ceilingStart < R := lt_of_le_of_lt ceilingStart_le_ceilingJoin h1
  have : 2 / 3 < R := by linarith [ceilingStart_bounds.1]
  unfold markCeiling
  rw [if_neg (not_le.2 this), if_neg (not_le.2 h0), if_neg (not_le.2 h1), if_pos h2]

theorem markCeiling_of_gt {R : ℝ} (h : 7 / 9 < R) : markCeiling R = (1 - R) / 2 := by
  have h1 : ceilingJoin < R := lt_trans ceilingJoin_lt_seven_ninths h
  have h0 : ceilingStart < R := lt_of_le_of_lt ceilingStart_le_ceilingJoin h1
  have : 2 / 3 < R := by linarith [ceilingStart_bounds.1]
  unfold markCeiling
  rw [if_neg (not_le.2 this), if_neg (not_le.2 h0), if_neg (not_le.2 h1), if_neg (not_le.2 h)]

/-- On the critical interval `[0.734, 7/9]` the ceiling is the limiting moment range. -/
theorem markCeiling_eq_limit {R : ℝ} (h1 : 734 / 1000 ≤ R) (h2 : R ≤ 7 / 9) :
    markCeiling R = (1 - R) / 2 + limitImprovement R :=
  markCeiling_of_limit (lt_of_lt_of_le ceilingJoin_lt_734 h1) h2

/-- On `[R_c, R₊]` the total length is the constant `M_ref`. -/
theorem ceilingTotal_of_mem {R : ℝ} (h1 : ceilingStart ≤ R) (h2 : R ≤ ceilingJoin) :
    ceilingTotal R = referenceTotal := by
  unfold ceilingTotal
  rcases eq_or_lt_of_le h1 with h | h
  · rw [← h, markCeiling_of_start (by linarith [ceilingStart_bounds.1]) le_rfl]
    unfold ceilingStart; ring
  · rw [markCeiling_of_join h h2]; ring

theorem ceilingJoin_le_twice : ceilingJoin ≤ 2 * referenceTotal - 1 := by
  have hG := limitImprovement_nonneg (r := ceilingJoin)
    (by linarith [ceilingStart_le_ceilingJoin, ceilingStart_bounds.1])
  have hJ3 := ceilingJoin_mem.2.2
  unfold limitTotal at hJ3
  linarith

/-- `Ŝ(R) ≥ (1 − R)/2` everywhere. -/
theorem half_le_markCeiling (R : ℝ) : (1 - R) / 2 ≤ markCeiling R := by
  have hc := ceilingStart_bounds
  rcases le_or_gt R (2 / 3) with h1 | h1
  · rw [markCeiling_of_le h1]
  rcases le_or_gt R ceilingStart with h2 | h2
  · rw [markCeiling_of_start h1 h2]; linarith
  rcases le_or_gt R ceilingJoin with h3 | h3
  · rw [markCeiling_of_join h2 h3]; linarith [ceilingJoin_le_twice]
  rcases le_or_gt R (7 / 9) with h4 | h4
  · rw [markCeiling_of_limit h3 h4]; linarith [limitImprovement_nonneg (r := R) h1.le]
  · rw [markCeiling_of_gt h4]

/-- `Ŝ(R) ≥ 1/6` up to `R_c`. -/
theorem one_sixth_le_markCeiling {R : ℝ} (h : R ≤ ceilingStart) : 1 / 6 ≤ markCeiling R := by
  rcases le_or_gt R (2 / 3) with h1 | h1
  · rw [markCeiling_of_le h1]; linarith
  · rw [markCeiling_of_start h1 h]

theorem monotone_ceilingTotal : Monotone ceilingTotal := by
  have hc := ceilingStart_bounds
  have hJ := ceilingStart_le_ceilingJoin
  have hJ7 := ceilingJoin_lt_seven_ninths
  have p1 : MonotoneOn ceilingTotal (Iic (2 / 3)) := by
    intro a ha b hb hab
    simp only [ceilingTotal, markCeiling_of_le (mem_Iic.1 ha), markCeiling_of_le (mem_Iic.1 hb)]
    linarith
  have e2 : ∀ x ∈ Icc (2 / 3) ceilingStart, ceilingTotal x = x + 1 / 6 := by
    intro x hx
    unfold ceilingTotal
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h, markCeiling_of_le le_rfl]; norm_num
    · rw [markCeiling_of_start h hx.2]
  have p2 : MonotoneOn ceilingTotal (Icc (2 / 3) ceilingStart) := by
    intro a ha b hb hab; rw [e2 a ha, e2 b hb]; linarith
  have p3 : MonotoneOn ceilingTotal (Icc ceilingStart ceilingJoin) := by
    intro a ha b hb _; rw [ceilingTotal_of_mem ha.1 ha.2, ceilingTotal_of_mem hb.1 hb.2]
  have e4 : ∀ x, ceilingJoin < x → x ≤ 7 / 9 → ceilingTotal x = limitTotal x := by
    intro x h1 h2; unfold ceilingTotal limitTotal; rw [markCeiling_of_limit h1 h2]; ring
  have p4 : MonotoneOn ceilingTotal (Icc ceilingJoin (7 / 9)) := by
    intro a ha b hb hab
    rcases eq_or_lt_of_le ha.1 with h | h
    · rw [← h, ceilingTotal_of_mem hJ le_rfl]
      rcases eq_or_lt_of_le hb.1 with h' | h'
      · rw [← h', ceilingTotal_of_mem hJ le_rfl]
      · rw [e4 b h' hb.2]; exact (referenceTotal_lt_limitTotal h' hb.2).le
    · rw [e4 a h ha.2, e4 b (lt_of_lt_of_le h hab) hb.2]
      exact limitTotal_le_limitTotal h hab hb.2
  have e5 : ∀ x ∈ Ici (7 / 9 : ℝ), ceilingTotal x = (1 + x) / 2 := by
    intro x hx
    rcases eq_or_lt_of_le (mem_Ici.1 hx) with h | h
    · rw [← h, e4 _ hJ7 le_rfl, limitTotal_seven_ninths]; norm_num
    · unfold ceilingTotal; rw [markCeiling_of_gt h]; ring
  have p5 : MonotoneOn ceilingTotal (Ici (7 / 9)) := by
    intro a ha b hb hab; rw [e5 a ha, e5 b hb]; linarith
  have q2 := p1.union_right p2 ⟨self_mem_Iic, fun _ h => h⟩ (isLeast_Icc (by linarith))
  rw [Iic_union_Icc_eq_Iic (by linarith)] at q2
  have q3 := q2.union_right p3 ⟨self_mem_Iic, fun _ h => h⟩ (isLeast_Icc hJ)
  rw [Iic_union_Icc_eq_Iic hJ] at q3
  have q4 := q3.union_right p4 ⟨self_mem_Iic, fun _ h => h⟩ (isLeast_Icc hJ7.le)
  rw [Iic_union_Icc_eq_Iic hJ7.le] at q4
  exact q4.Iic_union_Ici p5

theorem antitone_markCeiling : Antitone markCeiling := by
  have hc := ceilingStart_bounds
  have hJ := ceilingStart_le_ceilingJoin
  have hJ7 := ceilingJoin_lt_seven_ninths
  have hJm := ceilingJoin_mem
  have p1 : AntitoneOn markCeiling (Iic (2 / 3)) := by
    intro a ha b hb hab
    simp only [markCeiling_of_le (mem_Iic.1 ha), markCeiling_of_le (mem_Iic.1 hb)]
    linarith
  have e2 : ∀ x ∈ Icc (2 / 3) ceilingStart, markCeiling x = 1 / 6 := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h, markCeiling_of_le le_rfl]; norm_num
    · rw [markCeiling_of_start h hx.2]
  have p2 : AntitoneOn markCeiling (Icc (2 / 3) ceilingStart) := by
    intro a ha b hb _; rw [e2 a ha, e2 b hb]
  have e3 : ∀ x ∈ Icc ceilingStart ceilingJoin, markCeiling x = referenceTotal - x := by
    intro x hx
    have := ceilingTotal_of_mem hx.1 hx.2
    unfold ceilingTotal at this; linarith
  have p3 : AntitoneOn markCeiling (Icc ceilingStart ceilingJoin) := by
    intro a ha b hb hab; rw [e3 a ha, e3 b hb]; linarith
  have hlim : ∀ a b, ceilingJoin ≤ a → a ≤ b → b ≤ 7 / 9 →
      (1 - b) / 2 + limitImprovement b ≤ (1 - a) / 2 + limitImprovement a := by
    intro a b ha hab hb
    have h23 : 2 / 3 < a := by linarith
    have := limitImprovement_antitoneOn ⟨h23, hab.trans hb⟩ ⟨by linarith, hb⟩ hab
    linarith
  have p4 : AntitoneOn markCeiling (Icc ceilingJoin (7 / 9)) := by
    intro a ha b hb hab
    rcases eq_or_lt_of_le hb.1 with h' | h'
    · have : a = ceilingJoin := le_antisymm (h' ▸ hab) ha.1
      rw [this, ← h']
    rw [markCeiling_of_limit h' hb.2]
    rcases eq_or_lt_of_le ha.1 with h | h
    · rw [← h, e3 _ ⟨hJ, le_rfl⟩]
      have := hlim _ _ le_rfl (h ▸ hab) hb.2
      have hJ3 := hJm.2.2
      unfold limitTotal at hJ3
      linarith
    · rw [markCeiling_of_limit h ha.2]
      exact hlim _ _ h.le hab hb.2
  have e5 : ∀ x ∈ Ici (7 / 9 : ℝ), markCeiling x = (1 - x) / 2 := by
    intro x hx
    rcases eq_or_lt_of_le (mem_Ici.1 hx) with h | h
    · rw [← h, markCeiling_of_limit hJ7 le_rfl, limitImprovement_seven_ninths]; ring
    · rw [markCeiling_of_gt h]
  have p5 : AntitoneOn markCeiling (Ici (7 / 9)) := by
    intro a ha b hb hab; rw [e5 a ha, e5 b hb]; linarith
  have q2 := p1.union_right p2 ⟨self_mem_Iic, fun _ h => h⟩ (isLeast_Icc (by linarith))
  rw [Iic_union_Icc_eq_Iic (by linarith)] at q2
  have q3 := q2.union_right p3 ⟨self_mem_Iic, fun _ h => h⟩ (isLeast_Icc hJ)
  rw [Iic_union_Icc_eq_Iic hJ] at q3
  have q4 := q3.union_right p4 ⟨self_mem_Iic, fun _ h => h⟩ (isLeast_Icc hJ7.le)
  rw [Iic_union_Icc_eq_Iic hJ7.le] at q4
  exact q4.Iic_union_Ici p5

/-! ### Admitted stages stay below the ceiling -/

/-- The control of an admitted stage `(R, S_R) ↦ (r, S′)` with step `u` and cutoff `k`: either the
new marked length is below `u` (the initial domain), or it is propagated from `S_R` and every
amplitude class `(ν, ν)`, `k ≤ ν ≤ 3/4`, is controlled by a reference length `σ` at its cutoff
`w` (`ref w σ`) in both the short and the long count. -/
def StageControl (ref : ℝ → ℝ → Prop) (SR r S' u k : ℝ) : Prop :=
  S' < u ∨ (S' - u ≤ (1 - 6 * u) * SR + u / k ∧
    ∀ ν ∈ Icc k (3 / 4), ∃ w σ τ, ref w σ ∧ 0 ≤ τ ∧
      shortCount (1 - 6 * u) ν ν w σ (S' - u) + ν * r + ν * (S' - u) ≤ 1 - 6 * u + u ∧
      longCount (1 - 6 * u) ν w τ + ν * r + ν * (S' - u) ≤ 1 - 6 * u + u)

theorem StageControl.mono {ref ref' : ℝ → ℝ → Prop} (h : ∀ w σ, ref w σ → ref' w σ)
    {SR r S' u k : ℝ} (hc : StageControl ref SR r S' u k) : StageControl ref' SR r S' u k := by
  rcases hc with hc | ⟨hp, hcls⟩
  · exact Or.inl hc
  · refine Or.inr ⟨hp, fun ν hν => ?_⟩
    obtain ⟨w, σ, τ, hr, hτ, hs, hl⟩ := hcls ν hν
    exact ⟨w, σ, τ, h w σ hr, hτ, hs, hl⟩

/-- The common bound of an admitted stage at a supporting cutoff `ν₀` satisfying `(30)`. -/
theorem stage_total_le {R SR r S' u k ν₀ : ℝ} (hu : 0 < u) (hu' : u < 1 / 6)
    (hr : r = (1 - 6 * u) * R) (hν : 0 < ν₀) (hν' : ν₀ ≤ 3 / 4)
    (hSR : SR ≤ markCeiling R)
    (h30 : 5 / 6 ≤ longSlope ν₀ * R + ν₀ * ceilingTotal R)
    (hprop : S' - u ≤ (1 - 6 * u) * SR + u / k)
    (hcls : ∀ ν ∈ Icc k (3 / 4), ∃ w σ τ, σ ≤ markCeiling w ∧ 0 ≤ τ ∧
      shortCount (1 - 6 * u) ν ν w σ (S' - u) + ν * r + ν * (S' - u) ≤ 1 - 6 * u + u ∧
      longCount (1 - 6 * u) ν w τ + ν * r + ν * (S' - u) ≤ 1 - 6 * u + u) :
    r + S' ≤ (1 - 6 * u) * ceilingTotal R + u * (1 + 1 / ν₀) := by
  have hH : 0 ≤ 1 - 6 * u := by linarith
  rcases lt_or_ge ν₀ k with hlt | hle
  · -- a cutoff above `ν₀`: propagation alone suffices
    have h1 : u / k ≤ u / ν₀ := div_le_div_of_nonneg_left hu.le hν hlt.le
    have h2 := mul_le_mul_of_nonneg_left hSR hH
    have e : u * (1 + 1 / ν₀) = u + u / ν₀ := by ring
    rw [e, hr]
    unfold ceilingTotal
    nlinarith
  · obtain ⟨w, σ, τ, hσ, hτ, hs, hl⟩ := hcls ν₀ ⟨hle, hν'⟩
    exact stage_total_le_of_class hν hν' hH hτ h30 hs hl fun hw =>
      (show w + σ ≤ ceilingTotal w by unfold ceilingTotal; linarith).trans
        (monotone_ceilingTotal hw)

/-- The threshold cutoff `k∗(R, G(R))` satisfies `1 + 1/k∗ = 6(F_G(R) − R F_G′(R))`. -/
theorem one_add_inv_thresholdCutoff {R : ℝ} (hR : 2 / 3 < R)
    (hD : limitImprovement R < R - 1 / 2) :
    1 + 1 / thresholdCutoff R (limitImprovement R) =
      6 * (limitTotal R - R * (1 / 2 + limitSlope R)) := by
  have hR0 : R ≠ 0 := by linarith
  have hc : 5 * R / 4 - 5 / 6 ≠ 0 := by linarith
  have hU : 45 * R - 30 ≠ 0 := by linarith
  rw [limitSlope_eq_recursionSlope hR]
  unfold thresholdCutoff limitTotal recursionSlope
  have hD' : R - 1 / 2 - limitImprovement R ≠ 0 := by linarith
  generalize limitImprovement R = g at hD hD' ⊢
  generalize hc' : 5 * R / 4 - 5 / 6 = c at hc ⊢
  generalize hU' : 45 * R - 30 = U at hU ⊢
  generalize hd' : R - 1 / 2 - g = d at hD' ⊢
  field_simp
  rw [← hc', ← hU', ← hd']
  ring

/-- Proposition 6.3, one stage: an admitted stage from a rectangle below the ceiling produces a
rectangle below the ceiling. -/
theorem admitted_stage_le_markCeiling {R SR r S' u k : ℝ} (hR1 : R ≤ 1)
    (hSR : SR ≤ markCeiling R) (hu : 0 < u) (hu' : u < 1 / 6) (hr : r = (1 - 6 * u) * R)
    (hcap : S' ≤ 1 / 6)
    (hctl : StageControl (fun w σ => σ ≤ markCeiling w) SR r S' u k) :
    S' ≤ markCeiling r := by
  have hH : 0 < 1 - 6 * u := by linarith
  have hc := ceilingStart_bounds
  have hMb := referenceTotal_bounds
  rcases hctl with hsmall | ⟨hprop, hcls⟩
  · -- below the selection length the initial domain applies
    have : u ≤ (1 - r) / 2 := by rw [hr]; nlinarith
    linarith [half_le_markCeiling r]
  rcases le_or_gt r ceilingStart with hr0 | hr0
  · exact hcap.trans (one_sixth_le_markCeiling hr0)
  have hrR : r < R := by
    by_contra h
    have : R ≤ r := le_of_not_gt h
    have hR0 : 0 < R := by nlinarith
    nlinarith
  rcases le_or_gt R ceilingJoin with hR2 | hR2
  · -- `R_c < R ≤ R₊`: the reference cutoff `ν_ref`
    have hRc : ceilingStart ≤ R := by linarith
    have hT : ceilingTotal R = referenceTotal := ceilingTotal_of_mem hRc hR2
    obtain ⟨hν0, hν1⟩ := referenceCutoff_bounds
    have h30 : 5 / 6 ≤ longSlope referenceCutoff * R + referenceCutoff * ceilingTotal R := by
      rw [hT, ← referenceCutoff_identity]
      have : 0 ≤ longSlope referenceCutoff := by unfold longSlope; linarith
      nlinarith
    have h := stage_total_le hu hu' hr hν0 (by linarith) hSR h30 hprop hcls
    rw [hT, one_add_inv_referenceCutoff] at h
    rw [markCeiling_of_join hr0 (by linarith)]
    nlinarith
  rcases le_or_gt R (7 / 9) with hR3 | hR3
  · -- `R₊ < R ≤ 7/9`: the threshold cutoff of the limiting range
    have hR23 : 2 / 3 < R := by linarith
    have hT : ceilingTotal R = limitTotal R := by
      unfold ceilingTotal limitTotal; rw [markCeiling_of_limit hR2 hR3]; ring
    have hF : limitTotal R ≤ 8 / 9 := by
      rw [← limitTotal_seven_ninths]; exact limitTotal_le_limitTotal hR2 hR3 le_rfl
    have hGlt : limitImprovement R < R - 1 / 2 := by unfold limitTotal at hF; linarith
    obtain ⟨ν₀, hν₀⟩ : ∃ ν₀, ν₀ = thresholdCutoff R (limitImprovement R) := ⟨_, rfl⟩
    have hDpos : 0 < R - 1 / 2 - limitImprovement R := by linarith
    have hν0 : 0 < ν₀ := by rw [hν₀]; exact div_pos (by linarith) hDpos
    have hν1 : ν₀ ≤ 1 / 2 := by
      rw [hν₀]
      unfold thresholdCutoff
      rw [div_le_iff₀ hDpos]
      unfold limitTotal at hF
      linarith
    have h30 : 5 / 6 ≤ longSlope ν₀ * R + ν₀ * ceilingTotal R := by
      have hkD : ν₀ * (R - 1 / 2 - limitImprovement R) = 5 * R / 4 - 5 / 6 := by
        rw [hν₀]; unfold thresholdCutoff; exact div_mul_cancel₀ _ hDpos.ne'
      rw [hT]
      unfold longSlope limitTotal
      nlinarith
    have h := stage_total_le hu hu' hr hν0 (by linarith) hSR h30 hprop hcls
    rw [hT, hν₀, one_add_inv_thresholdCutoff hR23 hGlt] at h
    have htan := limitImprovement_tangent_le hR23 (r := r) (by linarith)
    have hstep : r + S' ≤ limitTotal r := by
      unfold limitTotal at h ⊢
      rw [hr] at h htan ⊢
      nlinarith
    rcases le_or_gt r ceilingJoin with hr1 | hr1
    · rw [markCeiling_of_join hr0 hr1]
      linarith [limitTotal_le_of_mem hr0.le hr1]
    · rw [markCeiling_of_limit hr1 (by linarith)]
      unfold limitTotal at hstep
      linarith
  · -- `R > 7/9`: the cutoff `1/2`
    have hT : ceilingTotal R = (1 + R) / 2 := by
      unfold ceilingTotal; rw [markCeiling_of_gt hR3]; ring
    have h30 : 5 / 6 ≤ longSlope (1 / 2) * R + 1 / 2 * ceilingTotal R := by
      rw [hT]; unfold longSlope; linarith
    have h := stage_total_le hu hu' hr (by norm_num) (by norm_num) hSR h30 hprop hcls
    rw [hT] at h
    have : S' ≤ (1 - r) / 2 := by rw [hr] at h ⊢; nlinarith
    linarith [half_le_markCeiling r]

/-! ### All available rectangles -/

/-- A set of rectangles `(R, S)` (polynomial length `R`, marked length `S`) closed under initial
rectangles, free-width truncation and admitted stages whose references lie in the set. -/
structure IsStageClosed (P : Set (ℝ × ℝ)) : Prop where
  initial : ∀ R S, 0 < R → R ≤ 1 → S ≤ (1 - R) / 2 → (R, S) ∈ P
  truncate : ∀ R S R' S', (R, S) ∈ P → 0 < R' → R' ≤ R → S' ≤ S → (R', S') ∈ P
  stage : ∀ R SR r S' u k, (R, SR) ∈ P → 0 < u → u < 1 / 6 → r = (1 - 6 * u) * R → 0 < k →
    k ≤ 3 / 4 → S' ≤ 1 / 6 →
    StageControl (fun w σ => ∃ Sw, (w, Sw) ∈ P ∧ σ ≤ max 0 Sw) SR r S' u k → (r, S') ∈ P

/-- The available joint moment rectangles: the least stage-closed set. -/
def availableRectangles : Set (ℝ × ℝ) := ⋂₀ {P | IsStageClosed P}

/-- The rectangles below the ceiling form a stage-closed set. -/
theorem isStageClosed_markCeiling :
    IsStageClosed {p : ℝ × ℝ | 0 < p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ markCeiling p.1} where
  initial R S h0 h1 hS := ⟨h0, h1, hS.trans (half_le_markCeiling R)⟩
  truncate R S R' S' h h0 h1 hS := ⟨h0, h1.trans h.2.1, hS.trans (h.2.2.trans (antitone_markCeiling h1))⟩
  stage R SR r S' u k h hu hu' hr _ _ hcap hctl := by
    have hH : 0 < 1 - 6 * u := by linarith
    refine ⟨by rw [hr]; exact mul_pos hH h.1, by rw [hr]; nlinarith [h.1, h.2.1], ?_⟩
    refine admitted_stage_le_markCeiling h.2.1 h.2.2 hu hu' hr hcap (hctl.mono ?_)
    rintro w σ ⟨Sw, hw, hσ⟩
    exact hσ.trans (max_le (by linarith [half_le_markCeiling w, hw.2.1]) hw.2.2)

/-- Proposition 6.3: every available joint marked length is at most `Ŝ(R)`. -/
theorem available_le_markCeiling {R S : ℝ} (h : (R, S) ∈ availableRectangles) :
    S ≤ markCeiling R :=
  (Set.sInter_subset_of_mem (t := {p : ℝ × ℝ | 0 < p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ markCeiling p.1})
    isStageClosed_markCeiling h).2.2

end

end GaloisForLFunctions.JointMarkedMoments
