import GaloisForLFunctions.RHTower.ModulusSlopeField
import GaloisForLFunctions.RHTower.Reflection

/-!
# The zero-counting functions of `ξ`

`N(T)` counts the zeros of `ξ` with ordinate in `[0, T]` and `N₀(T)` those additionally on the
critical line, both with multiplicity.  Both are divisor masses of `ξ` over a compact region, so
their finiteness and nonnegativity come from local finiteness of the `ξ`-divisor.

The counting functions are used through one property: a strict increase across a band produces a
zero in that band.  That is proved here by comparing the two divisor functions directly — if no zero
has ordinate in the band, the two divisors agree as functions, so the masses agree.  Together with
the reflection `ξ(s̄) = conj ξ(s)` this turns a counting statement into a conjugate pair of zeros
with prescribed ordinates.

Since `ξ` has no real zeros in the strip, counting on `[0, T]` and on `(0, T]` agree; the closed
band is used because it is compact.
-/

noncomputable section

namespace RHTower

open Complex Metric Set

/-! ## The divisor of `ξ` over an arbitrary region -/

/-- On its domain, the divisor of `ξ` is the (finite) local vanishing order. -/
theorem xi_divisor_apply_of_mem {S : Set ℂ} {u : ℂ} (hu : u ∈ S) :
    MeromorphicOn.divisor xi S u = ((analyticOrderAt xi u).toNat : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (xi_analyticOnNhd _) hu,
    ← ENat.coe_toNat (xi_orderAt_ne_top u)]
  simp

/-- Outside its domain, the divisor of `ξ` vanishes. -/
theorem xi_divisor_apply_of_notMem {S : Set ℂ} {u : ℂ} (hu : u ∉ S) :
    MeromorphicOn.divisor xi S u = 0 := by
  by_contra h
  exact hu ((MeromorphicOn.divisor xi S).supportWithinDomain (Function.mem_support.mpr h))

/-- The total `ξ`-divisor mass of a region. -/
def xiRegionOrderSum (S : Set ℂ) : ℤ := ∑ᶠ u, MeromorphicOn.divisor xi S u

/-- The mass of a region is nonnegative. -/
theorem xiRegionOrderSum_nonneg {S : Set ℂ} (hS : IsCompact S) : 0 ≤ xiRegionOrderSum S := by
  rw [xiRegionOrderSum, finsum_eq_sum_of_support_subset _
    (by rw [Set.Finite.coe_toFinset] :
      Function.support ⇑(MeromorphicOn.divisor xi S) ⊆
        ↑((MeromorphicOn.divisor xi S).finiteSupport hS).toFinset)]
  refine Finset.sum_nonneg fun u hu => ?_
  have hudom : u ∈ S :=
    (MeromorphicOn.divisor xi S).supportWithinDomain (by rwa [Set.Finite.mem_toFinset] at hu)
  rw [xi_divisor_apply_of_mem hudom]
  positivity

/-- Two regions carrying the same `ξ`-zeros have the same mass. -/
theorem xiRegionOrderSum_congr {S S' : Set ℂ}
    (h : ∀ u : ℂ, xi u = 0 → (u ∈ S ↔ u ∈ S')) :
    xiRegionOrderSum S = xiRegionOrderSum S' := by
  refine finsum_congr fun u => ?_
  by_cases hzero : xi u = 0
  · by_cases hu : u ∈ S
    · rw [xi_divisor_apply_of_mem hu, xi_divisor_apply_of_mem ((h u hzero).mp hu)]
    · rw [xi_divisor_apply_of_notMem hu,
        xi_divisor_apply_of_notMem (fun hc => hu ((h u hzero).mpr hc))]
  · have horder : ((analyticOrderAt xi u).toNat : ℤ) = 0 := by
      have : analyticOrderAt xi u = 0 :=
        (xi_analyticOnNhd Set.univ u (Set.mem_univ u)).analyticOrderAt_eq_zero.mpr hzero
      rw [this]
      simp
    by_cases hu : u ∈ S
    · rw [xi_divisor_apply_of_mem hu, horder]
      by_cases hu' : u ∈ S'
      · rw [xi_divisor_apply_of_mem hu', horder]
      · rw [xi_divisor_apply_of_notMem hu']
    · rw [xi_divisor_apply_of_notMem hu]
      by_cases hu' : u ∈ S'
      · rw [xi_divisor_apply_of_mem hu', horder]
      · rw [xi_divisor_apply_of_notMem hu']

/-! ## The counting boxes -/

/-- The closed counting box: the part of the critical strip with ordinate in `[0, T]`. -/
def xiCountingBox (T : ℝ) : Set ℂ := {s : ℂ | s.re ∈ Icc (0 : ℝ) 1 ∧ s.im ∈ Icc (0 : ℝ) T}

/-- The critical-line counting segment. -/
def xiCriticalCountingBox (T : ℝ) : Set ℂ :=
  {s : ℂ | s.re = 1 / 2 ∧ s.im ∈ Icc (0 : ℝ) T}

theorem isCompact_xiCountingBox (T : ℝ) : IsCompact (xiCountingBox T) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have hset : xiCountingBox T
        = (Complex.re ⁻¹' Icc (0 : ℝ) 1) ∩ (Complex.im ⁻¹' Icc (0 : ℝ) T) := rfl
    rw [hset]
    exact (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + |T|)).subset fun s hs => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : |s.re| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1.1], hs.1.2⟩
    have h2 : |s.im| ≤ |T| := by
      rw [abs_of_nonneg hs.2.1]
      exact le_trans hs.2.2 (le_abs_self T)
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 1 + |T| := by linarith

theorem isCompact_xiCriticalCountingBox (T : ℝ) : IsCompact (xiCriticalCountingBox T) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have hset : xiCriticalCountingBox T
        = (Complex.re ⁻¹' {(1 : ℝ) / 2}) ∩ (Complex.im ⁻¹' Icc (0 : ℝ) T) := rfl
    rw [hset]
    exact (isClosed_singleton.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + |T|)).subset fun s hs => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : |s.re| ≤ 1 := by
      rw [hs.1]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num
    have h2 : |s.im| ≤ |T| := by
      rw [abs_of_nonneg hs.2.1]
      exact le_trans hs.2.2 (le_abs_self T)
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 1 + |T| := by linarith

/-- **The zero-counting function.**  `ξ`-zeros with ordinate in `[0, T]`, with multiplicity. -/
def xiZeroCount (T : ℝ) : ℤ := xiRegionOrderSum (xiCountingBox T)

/-- **The critical-line counting function.** -/
def xiCriticalZeroCount (T : ℝ) : ℤ := xiRegionOrderSum (xiCriticalCountingBox T)

theorem xiZeroCount_nonneg (T : ℝ) : 0 ≤ xiZeroCount T :=
  xiRegionOrderSum_nonneg (isCompact_xiCountingBox T)

theorem xiCriticalZeroCount_nonneg (T : ℝ) : 0 ≤ xiCriticalZeroCount T :=
  xiRegionOrderSum_nonneg (isCompact_xiCriticalCountingBox T)

/-! ## Monotonicity -/

/-- The mass of a region grows with the region. -/
theorem xiRegionOrderSum_mono {S S' : Set ℂ} (hS' : IsCompact S') (hsub : S ⊆ S') :
    xiRegionOrderSum S ≤ xiRegionOrderSum S' := by
  classical
  set F := ((MeromorphicOn.divisor xi S').finiteSupport hS').toFinset with hF
  have hterm : ∀ u : ℂ, MeromorphicOn.divisor xi S u ≤ MeromorphicOn.divisor xi S' u := by
    intro u
    by_cases hu : u ∈ S
    · rw [xi_divisor_apply_of_mem hu, xi_divisor_apply_of_mem (hsub hu)]
    · rw [xi_divisor_apply_of_notMem hu]
      by_cases hu' : u ∈ S'
      · rw [xi_divisor_apply_of_mem hu']
        positivity
      · rw [xi_divisor_apply_of_notMem hu']
  have hsuppS' : Function.support ⇑(MeromorphicOn.divisor xi S') ⊆ ↑F := by
    rw [hF, Set.Finite.coe_toFinset]
  have hsuppS : Function.support ⇑(MeromorphicOn.divisor xi S) ⊆ ↑F := by
    intro u hu
    have hune : MeromorphicOn.divisor xi S u ≠ 0 := hu
    have huS : u ∈ S := (MeromorphicOn.divisor xi S).supportWithinDomain hu
    have hpos : 0 < MeromorphicOn.divisor xi S u := by
      rw [xi_divisor_apply_of_mem huS] at hune ⊢
      omega
    refine hsuppS' ?_
    have := lt_of_lt_of_le hpos (hterm u)
    exact Function.mem_support.mpr (ne_of_gt this)
  rw [xiRegionOrderSum, xiRegionOrderSum, finsum_eq_sum_of_support_subset _ hsuppS,
    finsum_eq_sum_of_support_subset _ hsuppS']
  exact Finset.sum_le_sum fun u _ => hterm u

theorem xiZeroCount_mono {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) : xiZeroCount T₁ ≤ xiZeroCount T₂ := by
  refine xiRegionOrderSum_mono (isCompact_xiCountingBox T₂) fun s hs => ?_
  exact ⟨hs.1, hs.2.1, le_trans hs.2.2 hT⟩

theorem xiCriticalZeroCount_mono {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    xiCriticalZeroCount T₁ ≤ xiCriticalZeroCount T₂ := by
  refine xiRegionOrderSum_mono (isCompact_xiCriticalCountingBox T₂) fun s hs => ?_
  exact ⟨hs.1, hs.2.1, le_trans hs.2.2 hT⟩

/-- The critical-line count never exceeds the total count. -/
theorem xiCriticalZeroCount_le_xiZeroCount (T : ℝ) : xiCriticalZeroCount T ≤ xiZeroCount T := by
  refine xiRegionOrderSum_mono (isCompact_xiCountingBox T) fun s hs => ?_
  refine ⟨?_, hs.2⟩
  rw [hs.1]
  constructor <;> norm_num

/-! ## A strict increase produces a zero in the band -/

/-- **A band with no zero contributes nothing.**  Contrapositively, a strict increase of the count
across `(T₁, T₂]` produces a `ξ`-zero with ordinate in that band. -/
theorem exists_xi_zero_im_mem_Ioc_of_lt {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (h : xiZeroCount T₁ < xiZeroCount T₂) :
    ∃ ρ : ℂ, xi ρ = 0 ∧ ρ.re ∈ Icc (0 : ℝ) 1 ∧ ρ.im ∈ Ioc T₁ T₂ := by
  by_contra hcon
  have hno : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ∈ Icc (0 : ℝ) 1 → ρ.im ∈ Ioc T₁ T₂ → False :=
    fun ρ h1 h2 h3 => hcon ⟨ρ, h1, h2, h3⟩
  refine absurd (xiRegionOrderSum_congr (S := xiCountingBox T₁) (S' := xiCountingBox T₂) ?_)
    (ne_of_lt h)
  intro u hzero
  constructor
  · intro hu
    refine ⟨hu.1, ?_⟩
    exact ⟨hu.2.1, le_trans hu.2.2 hT⟩
  · intro hu
    refine ⟨hu.1, ?_⟩
    refine ⟨hu.2.1, ?_⟩
    by_contra hlt
    exact hno u hzero hu.1 ⟨lt_of_not_ge hlt, hu.2.2⟩

/-- The same statement on the critical line. -/
theorem exists_xi_criticalLine_zero_im_mem_Ioc_of_lt {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (h : xiCriticalZeroCount T₁ < xiCriticalZeroCount T₂) :
    ∃ ρ : ℂ, xi ρ = 0 ∧ ρ.re = 1 / 2 ∧ ρ.im ∈ Ioc T₁ T₂ := by
  by_contra hcon
  have hno : ∀ ρ : ℂ, xi ρ = 0 → ρ.re = 1 / 2 → ρ.im ∈ Ioc T₁ T₂ → False :=
    fun ρ h1 h2 h3 => hcon ⟨ρ, h1, h2, h3⟩
  refine absurd (xiRegionOrderSum_congr (S := xiCriticalCountingBox T₁)
    (S' := xiCriticalCountingBox T₂) ?_) (ne_of_lt h)
  intro u hzero
  constructor
  · intro hu
    refine ⟨hu.1, ?_⟩
    exact ⟨hu.2.1, le_trans hu.2.2 hT⟩
  · intro hu
    refine ⟨hu.1, ?_⟩
    refine ⟨hu.2.1, ?_⟩
    by_contra hlt
    exact hno u hzero hu.1 ⟨lt_of_not_ge hlt, hu.2.2⟩

/-! ## The conjugate copy -/

/-- **Schwarz symmetry.**  A `ξ`-zero on the critical line with positive ordinate has a distinct
critical-line partner with the opposite ordinate. -/
theorem exists_conj_pair_of_xi_zero {ρ : ℂ} (hzero : xi ρ = 0) (hre : ρ.re = 1 / 2)
    (him : 0 < ρ.im) :
    ∃ ρ' : ℂ, xi ρ' = 0 ∧ ρ'.re = 1 / 2 ∧ ρ'.im = -ρ.im ∧ ρ' ≠ ρ := by
  refine ⟨(starRingEnd ℂ) ρ, ?_, ?_, ?_, ?_⟩
  · rw [xi_conj, hzero, map_zero]
  · simpa using hre
  · simp
  · intro hcon
    have := congrArg Complex.im hcon
    simp at this
    linarith

/-- The conjugate pair has the same squared ordinate. -/
theorem conj_pair_im_sq {ρ ρ' : ℂ} (h : ρ'.im = -ρ.im) : ρ'.im ^ (2 : ℕ) = ρ.im ^ (2 : ℕ) := by
  rw [h]
  ring

end RHTower
