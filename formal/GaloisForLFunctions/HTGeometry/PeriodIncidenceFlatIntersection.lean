import GaloisForLFunctions.HTGeometry.PeriodIncidenceMultiplier

/-!
# The flat intersection of powered period-incidence ranges

The bounded period realization is not separated by its powered incidence ranges.  Every finite
power remains algebraically distinct for a nondiscrete period module, but the positive section

`exp (-1 / ‖w‖)`

lies in the range of multiplication by `w^r` for every finite `r`.  Thus the inverse tower of
finite powered quotients has a nonzero kernel.  This is the classical flat-function failure of
Krull intersection in a non-Noetherian function algebra, specialized here to the natural period
symbol; it is a structural no-go for identifying this bounded tower with a separated formal
adic filtration.
-/

open Filter
open scoped Topology ENNReal

namespace GaloisForLFunctions

noncomputable section

/-- The canonical positive section flat to every finite order in the atomic period symbol. -/
def periodIncidenceFlatTarget (L : Submodule ℤ ℂ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ⟨fun q ↦ ((Real.exp (-‖regularizedPeriodWeight q.1.1‖⁻¹) : ℝ) : ℂ),
    memℓp_infty ⟨1, by
      rintro _ ⟨q, rfl⟩
      change ‖((Real.exp (-‖regularizedPeriodWeight q.1.1‖⁻¹) : ℝ) : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (inv_nonneg.mpr (norm_nonneg _)))⟩⟩

@[simp] theorem periodIncidenceFlatTarget_apply
    (L : Submodule ℤ ℂ) (q : NonzeroPeriod L) :
    periodIncidenceFlatTarget L q =
      ((Real.exp (-‖regularizedPeriodWeight q.1.1‖⁻¹) : ℝ) : ℂ) := rfl

/-- The elementary exponential estimate making the all-power inverse bounded. -/
theorem exp_neg_inv_mul_inv_pow_le_factorial (t : ℝ) (ht : 0 < t) (r : ℕ) :
    Real.exp (-t⁻¹) * (t⁻¹) ^ r ≤ (r.factorial : ℝ) := by
  have hfac : (0 : ℝ) < r.factorial := by positivity
  have hpow := Real.pow_div_factorial_le_exp t⁻¹ (inv_nonneg.mpr ht.le) r
  have hpow' : (t⁻¹) ^ r ≤ Real.exp t⁻¹ * (r.factorial : ℝ) :=
    (div_le_iff₀ hfac).mp hpow
  calc
    Real.exp (-t⁻¹) * (t⁻¹) ^ r ≤
        Real.exp (-t⁻¹) * (Real.exp t⁻¹ * (r.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow' (Real.exp_pos _).le
    _ = (r.factorial : ℝ) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp

/-- A bounded inverse of the flat target through the order-`r` multiplier. -/
def periodIncidenceFlatPreimage (L : Submodule ℤ ℂ) (r : ℕ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ⟨fun q ↦ periodIncidenceFlatTarget L q /
      regularizedPeriodWeight q.1.1 ^ r,
    memℓp_infty ⟨(r.factorial : ℝ), by
      rintro _ ⟨q, rfl⟩
      change ‖periodIncidenceFlatTarget L q /
        regularizedPeriodWeight q.1.1 ^ r‖ ≤ (r.factorial : ℝ)
      rw [norm_div, periodIncidenceFlatTarget_apply, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, norm_pow, div_eq_mul_inv, ← inv_pow]
      exact exp_neg_inv_mul_inv_pow_le_factorial _
        (norm_pos_iff.mpr (regularizedPeriodWeight_ne_zero q.2)) r⟩⟩

/-- The displayed bounded inverse maps exactly to the flat target. -/
theorem poweredPeriodIncidenceMultiplier_flatPreimage
    (L : Submodule ℤ ℂ) (r : ℕ) :
    poweredPeriodIncidenceMultiplier L r (periodIncidenceFlatPreimage L r) =
      periodIncidenceFlatTarget L := by
  apply lp.ext
  funext q
  rw [poweredPeriodIncidenceMultiplier_apply]
  change regularizedPeriodWeight q.1.1 ^ r *
      (periodIncidenceFlatTarget L q / regularizedPeriodWeight q.1.1 ^ r) =
    periodIncidenceFlatTarget L q
  field_simp [pow_ne_zero r (regularizedPeriodWeight_ne_zero q.2)]

/-- The positive flat section belongs to every finite powered incidence range. -/
theorem periodIncidenceFlatTarget_mem_all_poweredRanges
    (L : Submodule ℤ ℂ) (r : ℕ) :
    periodIncidenceFlatTarget L ∈ Set.range (poweredPeriodIncidenceMultiplier L r) :=
  ⟨periodIncidenceFlatPreimage L r,
    poweredPeriodIncidenceMultiplier_flatPreimage L r⟩

/-- Consecutive powered ranges remain distinct for every nondiscrete period source. -/
theorem exists_mem_poweredPeriodRange_not_mem_succRange
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L) (r : ℕ) :
    ∃ y : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞,
      y ∈ Set.range (poweredPeriodIncidenceMultiplier L r) ∧
      y ∉ Set.range (poweredPeriodIncidenceMultiplier L (r + 1)) := by
  let β : ℝ := (r : ℝ) + 1 / 2
  have hβ : 0 < β := by
    dsimp [β]
    positivity
  have hrβ : (r : ℝ) ≤ β := by
    dsimp [β]
    norm_num
  have hβr : β < ((r + 1 : ℕ) : ℝ) := by
    dsimp [β]
    push_cast
    linarith
  exact ⟨periodIncidencePowerTarget L β hβ.le,
    periodIncidencePowerTarget_mem_range_of_natCast_le L r β hβ.le hrβ,
    periodIncidencePowerTarget_not_mem_range_of_lt_natCast
      L hL (r + 1) β hβ hβr⟩

/-- Nondiscreteness makes the all-power flat section a genuine nonzero inverse-limit kernel
witness, rather than a vacuous function on an empty mode set. -/
theorem periodIncidenceFlatTarget_ne_zero_of_not_discrete
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L) :
    periodIncidenceFlatTarget L ≠ 0 := by
  obtain ⟨p, hpL, hpne, _hp0⟩ :=
    exists_small_nonzero_of_not_discrete_intSubmodule L hL
  let q : NonzeroPeriod L := ⟨⟨p 0, hpL 0⟩, hpne 0⟩
  intro hzero
  have hcoord := congrArg
    (fun x : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ ↦ x q) hzero
  change ((Real.exp (-‖regularizedPeriodWeight q.1.1‖⁻¹) : ℝ) : ℂ) = 0 at hcoord
  exact (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hcoord

/-! ## Hausdorff closure collapses all positive incidence orders -/

/-- A cutoff inverse which lifts an atomic incidence output through the order-`r` multiplier away
from the small-period boundary. -/
def periodIncidenceAtomicToPowerCutoffPreimage
    (L : Submodule ℤ ℂ) (r : ℕ)
    (x : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞)
    (δ : ℝ) (hδ : 0 < δ) :
    lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ :=
  ⟨fun q ↦ if δ ≤ ‖regularizedPeriodWeight q.1.1‖ then
      (regularizedPeriodWeight q.1.1 * x q) /
        regularizedPeriodWeight q.1.1 ^ r
    else 0,
    memℓp_infty ⟨‖x‖ * (δ⁻¹ ^ r), by
      rintro _ ⟨q, rfl⟩
      by_cases hq : δ ≤ ‖regularizedPeriodWeight q.1.1‖
      · simp only [if_pos hq]
        rw [norm_div, norm_mul, norm_pow, div_eq_mul_inv, ← inv_pow]
        have hwinv : ‖regularizedPeriodWeight q.1.1‖⁻¹ ≤ δ⁻¹ := by
          simpa only [one_div] using one_div_le_one_div_of_le hδ hq
        have hxq : ‖x q‖ ≤ ‖x‖ :=
          lp.norm_apply_le_norm ENNReal.top_ne_zero x q
        have hwone : ‖regularizedPeriodWeight q.1.1‖ ≤ 1 :=
          norm_regularizedPeriodWeight_le_one q.1.1
        have hinvpow : ‖regularizedPeriodWeight q.1.1‖⁻¹ ^ r ≤ δ⁻¹ ^ r :=
          pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) hwinv r
        calc
          ‖regularizedPeriodWeight q.1.1‖ * ‖x q‖ *
              ‖regularizedPeriodWeight q.1.1‖⁻¹ ^ r ≤
            1 * ‖x‖ * (δ⁻¹ ^ r) := by gcongr
          _ = ‖x‖ * (δ⁻¹ ^ r) := by ring
      · simp only [if_neg hq, norm_zero]
        positivity⟩⟩

theorem poweredPeriodIncidenceMultiplier_atomicToPowerCutoff_apply
    (L : Submodule ℤ ℂ) (r : ℕ)
    (x : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞)
    (δ : ℝ) (hδ : 0 < δ) (q : NonzeroPeriod L) :
    poweredPeriodIncidenceMultiplier L r
        (periodIncidenceAtomicToPowerCutoffPreimage L r x δ hδ) q =
      if δ ≤ ‖regularizedPeriodWeight q.1.1‖ then
        periodIncidenceMultiplier L x q
      else 0 := by
  by_cases hq : δ ≤ ‖regularizedPeriodWeight q.1.1‖
  · rw [poweredPeriodIncidenceMultiplier_apply, periodIncidenceMultiplier_apply]
    simp only [periodIncidenceAtomicToPowerCutoffPreimage, if_pos hq]
    field_simp [pow_ne_zero r (regularizedPeriodWeight_ne_zero q.2)]
  · simp [poweredPeriodIncidenceMultiplier_apply,
      periodIncidenceAtomicToPowerCutoffPreimage, hq]

/-- The cutoff lift misses the atomic target only on modes whose symbol is smaller than `δ`. -/
theorem norm_poweredPeriodIncidenceMultiplier_atomicToPowerCutoff_sub_le
    (L : Submodule ℤ ℂ) (r : ℕ)
    (x : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞)
    (δ : ℝ) (hδ : 0 < δ) :
    ‖poweredPeriodIncidenceMultiplier L r
          (periodIncidenceAtomicToPowerCutoffPreimage L r x δ hδ) -
        periodIncidenceMultiplier L x‖ ≤ δ * ‖x‖ := by
  apply lp.norm_le_of_forall_le (mul_nonneg hδ.le (norm_nonneg x))
  intro q
  change ‖poweredPeriodIncidenceMultiplier L r
      (periodIncidenceAtomicToPowerCutoffPreimage L r x δ hδ) q -
        periodIncidenceMultiplier L x q‖ ≤ δ * ‖x‖
  by_cases hq : δ ≤ ‖regularizedPeriodWeight q.1.1‖
  · rw [poweredPeriodIncidenceMultiplier_atomicToPowerCutoff_apply, if_pos hq]
    simpa using mul_nonneg hδ.le (norm_nonneg x)
  · rw [poweredPeriodIncidenceMultiplier_atomicToPowerCutoff_apply, if_neg hq]
    simp only [zero_sub, norm_neg, periodIncidenceMultiplier_apply, norm_mul]
    exact mul_le_mul (le_of_not_ge hq)
      (lp.norm_apply_le_norm ENNReal.top_ne_zero x q)
      (norm_nonneg _) hδ.le

/-- Every atomic incidence output is a norm limit of order-`r` incidence outputs. -/
theorem periodIncidenceMultiplier_apply_mem_closure_poweredRange
    (L : Submodule ℤ ℂ) (r : ℕ)
    (x : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞) :
    periodIncidenceMultiplier L x ∈
      closure (Set.range (poweredPeriodIncidenceMultiplier L r)) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := ε / (‖x‖ + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨poweredPeriodIncidenceMultiplier L r
      (periodIncidenceAtomicToPowerCutoffPreimage L r x δ hδ),
    Set.mem_range_self _, ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  apply (norm_poweredPeriodIncidenceMultiplier_atomicToPowerCutoff_sub_le
    L r x δ hδ).trans_lt
  dsimp [δ]
  rw [div_mul_eq_mul_div]
  exact (div_lt_iff₀ (by positivity : 0 < ‖x‖ + 1)).2
    (by nlinarith [norm_nonneg x])

/-- **Hausdorff order collapse.** Although consecutive powered ranges are algebraically distinct,
their norm closures are identical for every positive order. -/
theorem closure_range_poweredPeriodIncidenceMultiplier_eq_atomic
    (L : Submodule ℤ ℂ) (r : ℕ) (hr : 1 ≤ r) :
    closure (Set.range (poweredPeriodIncidenceMultiplier L r)) =
      closure (Set.range (periodIncidenceMultiplier L)) := by
  apply Set.Subset.antisymm
  · exact closure_mono (poweredPeriodIncidenceMultiplier_range_subset L r hr)
  · apply closure_minimal
    · rintro _ ⟨x, rfl⟩
      exact periodIncidenceMultiplier_apply_mem_closure_poweredRange L r x
    · exact isClosed_closure

/-- **Exact-order/Hausdorff-order fracture.** On a nondiscrete period source, consecutive positive
orders have genuinely different exact ranges but identical norm closures.  Hausdorffization
therefore repairs neither the exact lifting problem nor the physical multiplicity: it erases the
latter. -/
theorem poweredPeriodIncidence_strictBeforeClosure_equalAfterClosure
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (r : ℕ) (hr : 1 ≤ r) :
    (∃ y : lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞,
        y ∈ Set.range (poweredPeriodIncidenceMultiplier L r) ∧
        y ∉ Set.range (poweredPeriodIncidenceMultiplier L (r + 1))) ∧
      closure (Set.range (poweredPeriodIncidenceMultiplier L r)) =
        closure (Set.range (poweredPeriodIncidenceMultiplier L (r + 1)) ) := by
  refine ⟨exists_mem_poweredPeriodRange_not_mem_succRange L hL r, ?_⟩
  rw [closure_range_poweredPeriodIncidenceMultiplier_eq_atomic L r hr,
    closure_range_poweredPeriodIncidenceMultiplier_eq_atomic L (r + 1) (by omega)]

end

end GaloisForLFunctions
