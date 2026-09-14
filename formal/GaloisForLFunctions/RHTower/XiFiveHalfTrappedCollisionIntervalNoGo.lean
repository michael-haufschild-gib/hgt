import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Thinness of perpetually trapped five-half Xi collisions

The remaining literal HB angular-source obstruction is the factor `ξ(5ρ/2 - 1)` below
`Re ρ = 4/5`. The corpus reduces a failure to escape that factor to a collision orbit trapped in
the real band `[8/15, 2/3]`, apart from the explicit `3/5` landing.

This file determines two sharp properties of that survivor. On either side of `3/5`, one
collision step expands horizontal distance by `5/2`; the point `3/5` itself immediately leaves
the band. Hence no nondegenerate interval can remain trapped under every iterate. More strongly,
the two inverse branches each contract Lebesgue measure by `2/5`, so finite trapped approximations
decay by `4/5` and the complete trapped set is null. These results kill the chains

`horizontally robust five-half collision trapping -> universal literal HB source extinction ->
BM darkness -> HB/FZZ-P/RBH/PW-B -> RH`

and

`Lebesgue-regular five-half collision source -> literal HB source extinction -> BM darkness ->
HB/FZZ-P/RBH/PW-B -> RH`.

The surviving collision mechanism must therefore be singular in horizontal real part. This does
not exclude atomic or singular-Cantor Xi-zero configurations.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace RHTower

noncomputable section

/-- Real-part dynamics induced by the five-half collision step. -/
def xiFiveHalfRealStep (x : ℝ) : ℝ :=
  if 3 / 5 < x then 5 * x / 2 - 1 else 2 - 5 * x / 2

/-- Real-part orbit induced by repeated five-half collision. -/
def xiFiveHalfRealOrbit (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => xiFiveHalfRealStep (xiFiveHalfRealOrbit x n)

/-- Starting real parts whose complete five-half collision orbit stays in the unresolved band. -/
def xiFiveHalfRealTrappedSet : Set ℝ :=
  {x | ∀ n, 8 / 15 ≤ xiFiveHalfRealOrbit x n ∧
    xiFiveHalfRealOrbit x n ≤ 2 / 3}

theorem xiFiveHalfRealOrbit_step (x : ℝ) (n : ℕ) :
    xiFiveHalfRealOrbit (xiFiveHalfRealStep x) n = xiFiveHalfRealOrbit x (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [xiFiveHalfRealOrbit, xiFiveHalfRealOrbit, ih]

theorem xiFiveHalfRealTrappedSet_forward {x : ℝ}
    (hx : x ∈ xiFiveHalfRealTrappedSet) :
    xiFiveHalfRealStep x ∈ xiFiveHalfRealTrappedSet := by
  intro n
  rw [xiFiveHalfRealOrbit_step]
  exact hx (n + 1)

theorem three_fifths_not_mem_xiFiveHalfRealTrappedSet :
    (3 / 5 : ℝ) ∉ xiFiveHalfRealTrappedSet := by
  intro h
  have h1 := (h 1).1
  norm_num [xiFiveHalfRealOrbit, xiFiveHalfRealStep] at h1

private theorem xiFiveHalfRealTrappedSet_interval_expansion
    {a b : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ xiFiveHalfRealTrappedSet) :
    ∃ a' b' : ℝ, a' < b' ∧ Icc a' b' ⊆ xiFiveHalfRealTrappedSet ∧
      b' - a' = (5 / 2) * (b - a) := by
  have hmid : (3 / 5 : ℝ) ∉ Icc a b := fun hm =>
    three_fifths_not_mem_xiFiveHalfRealTrappedSet (hI hm)
  have hside : (3 / 5 : ℝ) < a ∨ b < 3 / 5 := by
    simpa only [mem_Icc, not_and_or, not_le] using hmid
  rcases hside with hupper | hlower
  · refine ⟨5 * a / 2 - 1, 5 * b / 2 - 1, by linarith, ?_, by ring⟩
    intro y hy
    let x : ℝ := 2 * (y + 1) / 5
    have hxa : a ≤ x := by dsimp only [x]; linarith [hy.1]
    have hxb : x ≤ b := by dsimp only [x]; linarith [hy.2]
    have hx := xiFiveHalfRealTrappedSet_forward (hI ⟨hxa, hxb⟩)
    have hxupper : (3 / 5 : ℝ) < x := hupper.trans_le hxa
    have hstep : xiFiveHalfRealStep x = y := by
      rw [xiFiveHalfRealStep, if_pos hxupper]
      dsimp only [x]
      ring
    rwa [hstep] at hx
  · refine ⟨2 - 5 * b / 2, 2 - 5 * a / 2, by linarith, ?_, by ring⟩
    intro y hy
    let x : ℝ := 2 * (2 - y) / 5
    have hxa : a ≤ x := by dsimp only [x]; linarith [hy.2]
    have hxb : x ≤ b := by dsimp only [x]; linarith [hy.1]
    have hx := xiFiveHalfRealTrappedSet_forward (hI ⟨hxa, hxb⟩)
    have hxlower : ¬ (3 / 5 : ℝ) < x := not_lt.mpr (le_of_lt (hxb.trans_lt hlower))
    have hstep : xiFiveHalfRealStep x = y := by
      rw [xiFiveHalfRealStep, if_neg hxlower]
      dsimp only [x]
      ring
    rwa [hstep] at hx

private theorem exists_xiFiveHalfRealTrappedSet_interval_expansion_pow
    {a b : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ xiFiveHalfRealTrappedSet) (n : ℕ) :
    ∃ a' b' : ℝ, a' < b' ∧ Icc a' b' ⊆ xiFiveHalfRealTrappedSet ∧
      b' - a' = (5 / 2) ^ n * (b - a) := by
  induction n with
  | zero =>
      exact ⟨a, b, hab, hI, by simp⟩
  | succ n ih =>
      obtain ⟨a', b', hab', hI', hw⟩ := ih
      obtain ⟨a'', b'', hab'', hI'', hw'⟩ :=
        xiFiveHalfRealTrappedSet_interval_expansion hab' hI'
      refine ⟨a'', b'', hab'', hI'', ?_⟩
      rw [hw', hw, pow_succ]
      ring

/-- The unresolved five-half collision survivor contains no horizontal interval. -/
theorem not_Icc_subset_xiFiveHalfRealTrappedSet
    {a b : ℝ} (hab : a < b) :
    ¬ Icc a b ⊆ xiFiveHalfRealTrappedSet := by
  intro hI
  have hgap : 0 < b - a := sub_pos.mpr hab
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    ((2 / 15) / (b - a)) (by norm_num : (1 : ℝ) < 5 / 2)
  obtain ⟨a', b', hab', hI', hw⟩ :=
    exists_xiFiveHalfRealTrappedSet_interval_expansion_pow hab hI n
  have ha := hI' ⟨le_rfl, hab'.le⟩ 0
  have hb := hI' ⟨hab'.le, le_rfl⟩ 0
  have hwidth : b' - a' ≤ 2 / 15 := by
    simp only [xiFiveHalfRealOrbit] at ha hb
    linarith [ha.1, hb.2]
  have hlarge : 2 / 15 < (5 / 2 : ℝ) ^ n * (b - a) :=
    (div_lt_iff₀ hgap).mp hn
  rw [← hw] at hlarge
  exact (not_lt_of_ge hwidth) hlarge

/-- A horizontally robust family of perpetually trapped five-half collision sources. -/
def HBXiFiveHalfHorizontallyRobustTrappedCollisionProducer : Prop :=
  ∃ a b : ℝ, a < b ∧ Icc a b ⊆ xiFiveHalfRealTrappedSet

/-- Premise-free no-go: perpetual five-half collision trapping cannot persist across any
nondegenerate horizontal source band. -/
theorem hbXiFiveHalfHorizontallyRobustTrappedCollisionProducerRouteKilled :
    ¬ HBXiFiveHalfHorizontallyRobustTrappedCollisionProducer := by
  rintro ⟨a, b, hab, hI⟩
  exact not_Icc_subset_xiFiveHalfRealTrappedSet hab hI

/-! ## Lebesgue-nullity of the complete trapped set -/

/-- Points surviving the first `n + 1` five-half collision band tests. -/
def xiFiveHalfRealTrappedApprox : ℕ → Set ℝ
  | 0 => Icc (8 / 15) (2 / 3)
  | n + 1 => Icc (8 / 15) (2 / 3) ∩
      xiFiveHalfRealStep ⁻¹' xiFiveHalfRealTrappedApprox n

theorem xiFiveHalfRealTrappedSet_subset_approx (n : ℕ) :
    xiFiveHalfRealTrappedSet ⊆ xiFiveHalfRealTrappedApprox n := by
  induction n with
  | zero =>
      intro x hx
      exact hx 0
  | succ n ih =>
      intro x hx
      exact ⟨hx 0, ih (xiFiveHalfRealTrappedSet_forward hx)⟩

private theorem volume_preimage_xiFiveHalfRealStep_le (S : Set ℝ) :
    volume (xiFiveHalfRealStep ⁻¹' S) ≤
      ENNReal.ofReal (4 / 5 : ℝ) * volume S := by
  let U : Set ℝ := (fun x : ℝ => 5 * x / 2 - 1) ⁻¹' S
  let L : Set ℝ := (fun x : ℝ => 2 - 5 * x / 2) ⁻¹' S
  have hsub : xiFiveHalfRealStep ⁻¹' S ⊆ U ∪ L := by
    intro x hx
    by_cases h : 3 / 5 < x
    · left
      simpa [U, xiFiveHalfRealStep, h] using hx
    · right
      simpa [L, xiFiveHalfRealStep, h] using hx
  have hU : volume U = ENNReal.ofReal (2 / 5 : ℝ) * volume S := by
    have hUset : U = (fun x : ℝ => (5 / 2 : ℝ) * x) ⁻¹'
        ((fun y : ℝ => -1 + y) ⁻¹' S) := by
      ext x
      simp only [U, mem_preimage]
      rw [show 5 * x / 2 - 1 = -1 + (5 / 2 : ℝ) * x by ring]
    rw [hUset]
    rw [Real.volume_preimage_mul_left (by norm_num : (5 / 2 : ℝ) ≠ 0),
      measure_preimage_add]
    congr 1
    norm_num
  have hL : volume L = ENNReal.ofReal (2 / 5 : ℝ) * volume S := by
    have hLset : L = (fun x : ℝ => (-5 / 2 : ℝ) * x) ⁻¹'
        ((fun y : ℝ => 2 + y) ⁻¹' S) := by
      ext x
      simp only [L, mem_preimage]
      rw [show 2 - 5 * x / 2 = 2 + (-5 / 2 : ℝ) * x by ring]
    rw [hLset]
    rw [Real.volume_preimage_mul_left (by norm_num : (-5 / 2 : ℝ) ≠ 0),
      measure_preimage_add]
    congr 1
    norm_num
  calc
    volume (xiFiveHalfRealStep ⁻¹' S) ≤ volume (U ∪ L) := measure_mono hsub
    _ ≤ volume U + volume L := measure_union_le U L
    _ = ENNReal.ofReal (4 / 5 : ℝ) * volume S := by
      rw [hU, hL]
      have hq : ENNReal.ofReal (4 / 5 : ℝ) =
          2 * ENNReal.ofReal (2 / 5 : ℝ) := by
        calc
          ENNReal.ofReal (4 / 5 : ℝ) =
              ENNReal.ofReal ((2 : ℝ) * (2 / 5)) := by norm_num
          _ = ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (2 / 5 : ℝ) :=
            ENNReal.ofReal_mul (by norm_num)
          _ = _ := by norm_num
      rw [hq, two_mul, add_mul]

theorem volume_xiFiveHalfRealTrappedApprox_succ_le (n : ℕ) :
    volume (xiFiveHalfRealTrappedApprox (n + 1)) ≤
      ENNReal.ofReal (4 / 5 : ℝ) * volume (xiFiveHalfRealTrappedApprox n) := by
  calc
    volume (xiFiveHalfRealTrappedApprox (n + 1)) ≤
        volume (xiFiveHalfRealStep ⁻¹' xiFiveHalfRealTrappedApprox n) := by
      apply measure_mono
      intro x hx
      exact hx.2
    _ ≤ _ := volume_preimage_xiFiveHalfRealStep_le _

private lemma tendsto_zero_of_geometric_bound
    {u : ℕ → ℝ≥0∞} {q : ℝ≥0∞} (hq : q < 1) (hu0 : u 0 < ⊤)
    (hdecay : ∀ n : ℕ, u (n + 1) ≤ q * u n) :
    Tendsto u atTop (nhds 0) := by
  have hbound : ∀ n : ℕ, u n ≤ q ^ n * u 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        u (n + 1) ≤ q * u n := hdecay n
        _ ≤ q * (q ^ n * u 0) := mul_le_mul_right ih q
        _ = q ^ (n + 1) * u 0 := by rw [pow_succ', mul_assoc]
  have hqpow : Tendsto (fun n : ℕ => q ^ n) atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq
  have hmul : Tendsto (fun n : ℕ => u 0 * q ^ n) atTop (nhds (u 0 * 0)) :=
    ENNReal.Tendsto.const_mul hqpow (Or.inr (ne_of_lt hu0))
  have hmul0 : Tendsto (fun n : ℕ => q ^ n * u 0) atTop (nhds 0) := by
    simpa [mul_comm] using hmul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul0
    (fun _ => bot_le) hbound

/-- The complete five-half collision trapped set has zero Lebesgue measure. -/
theorem volume_xiFiveHalfRealTrappedSet_eq_zero :
    volume xiFiveHalfRealTrappedSet = 0 := by
  have hlim : Tendsto (fun n : ℕ => volume (xiFiveHalfRealTrappedApprox n))
      atTop (nhds 0) := by
    apply tendsto_zero_of_geometric_bound
        (q := ENNReal.ofReal (4 / 5 : ℝ))
    · norm_num
    · change volume (Icc (8 / 15 : ℝ) (2 / 3)) < ⊤
      rw [Real.volume_Icc]
      norm_num
    · exact volume_xiFiveHalfRealTrappedApprox_succ_le
  have hle : (fun _ : ℕ => volume xiFiveHalfRealTrappedSet) ≤ᶠ[atTop]
      fun n : ℕ => volume (xiFiveHalfRealTrappedApprox n) :=
    Filter.Eventually.of_forall fun n =>
      measure_mono (xiFiveHalfRealTrappedSet_subset_approx n)
  exact le_antisymm
    (le_of_tendsto_of_tendsto tendsto_const_nhds hlim hle) bot_le

/-- A nonzero regular horizontal source law supported on perpetual five-half collisions. -/
def HBXiFiveHalfRegularTrappedCollisionProducer : Prop :=
  ∃ μ : Measure ℝ, μ ≪ volume ∧ μ xiFiveHalfRealTrappedSet ≠ 0

/-- Premise-free no-go: every Lebesgue-regular horizontal producer assigns zero mass to the
perpetually trapped five-half collision survivor. -/
theorem hbXiFiveHalfRegularTrappedCollisionProducerRouteKilled :
    ¬ HBXiFiveHalfRegularTrappedCollisionProducer := by
  rintro ⟨μ, hμ, hnonzero⟩
  exact hnonzero (hμ volume_xiFiveHalfRealTrappedSet_eq_zero)

end

end RHTower
