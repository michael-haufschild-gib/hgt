import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant
import GaloisForLFunctions.RHTower.ChebyshevThetaPowerLog

/-!
# Causal localization of the CCM--FU Mertens tail

The critical FU arithmetic remainder is normally written as an endpoint Chebyshev error minus
an improper Mertens tail.  In the exact Chebyshev--factorial flux, those tails do not require an
estimate: their coefficients telescope into finite, causal unit slabs.  This file proves that
identity for every integrable real source, then specializes it to `chebyshevError t / t^(2 : ℕ)`.

The resulting local-slab expression deliberately retains its signed source.  It does not claim
positivity or a uniform bound.
-/

open scoped BigOperators
open Set MeasureTheory

namespace RHTower

noncomputable section

/-- A weighted chain of future tails is exactly a finite causal slab ledger.  The terminal tail
cancels before any absolute value or source estimate is introduced. -/
theorem ccmFUSuzuki_tailTelescope_to_localSlabs
    {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 2) volume) (N : ℕ) :
    3 * (∫ t in Ioi (2 : ℝ), f t) +
        (∑ j ∈ Finset.range N, (∫ t in Ioi (j + 3 : ℝ), f t)) -
      (N + 3 : ℝ) * (∫ t in Ioi (N + 3 : ℝ), f t) =
    3 * (∫ t in (2 : ℝ)..3, f t) +
      (∑ j ∈ Finset.range N, ((j + 4 : ℕ) : ℝ) *
        (∫ t in (j + 3 : ℝ)..(j + 4 : ℝ), f t)) := by
  induction N with
  | zero =>
      norm_num
      have hstep := intervalIntegral.integral_Ioi_sub_Ioi hf
        (by norm_num : (2 : ℝ) ≤ 3)
      linear_combination 3 * hstep
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hN3 : (2 : ℝ) ≤ (N + 3 : ℝ) := by
        exact_mod_cast (by omega : 2 ≤ N + 3)
      have hN34 : (N + 3 : ℝ) ≤ (N + 4 : ℝ) := by
        exact_mod_cast (by omega : N + 3 ≤ N + 4)
      have hstep := intervalIntegral.integral_Ioi_sub_Ioi
        (f := f) (hf.mono_set (Ioi_subset_Ioi hN3)) hN34
      have hNsucc : ((N + 1 : ℕ) : ℝ) + 3 = (N + 4 : ℝ) := by
        push_cast
        ring
      rw [hNsucc]
      push_cast at hstep ih ⊢
      linear_combination ih + ((N : ℝ) + 4) * hstep

/-- The literal compensated-Chebyshev tails in the CCM--FU flux have the same finite causal
slab ledger.  No future tail remains on the right-hand side. -/
theorem ccmFUSuzuki_chebyshevTailTelescope_to_localSlabs (N : ℕ) :
    3 * (∫ t in Ioi (2 : ℝ), chebyshevError t / t ^ (2 : ℕ)) +
        (∑ j ∈ Finset.range N,
          (∫ t in Ioi (j + 3 : ℝ), chebyshevError t / t ^ (2 : ℕ))) -
      (N + 3 : ℝ) *
        (∫ t in Ioi (N + 3 : ℝ), chebyshevError t / t ^ (2 : ℕ)) =
    3 * (∫ t in (2 : ℝ)..3, chebyshevError t / t ^ (2 : ℕ)) +
      (∑ j ∈ Finset.range N, ((j + 4 : ℕ) : ℝ) *
        (∫ t in (j + 3 : ℝ)..(j + 4 : ℝ), chebyshevError t / t ^ (2 : ℕ))) := by
  apply ccmFUSuzuki_tailTelescope_to_localSlabs
  exact integrableOn_chebyshevError_div_sq.mono_set (Ioi_subset_Ioi (by norm_num))

/-- On a unit slab, the real Chebyshev function is constant almost everywhere.  The resulting
compensated-error integral therefore has an elementary antiderivative with the literal arithmetic
value `chebyshevPsi m` retained. -/
theorem ccmFUSuzuki_chebyshevError_unitSlab
    (m : ℕ) (hm : 1 ≤ m) :
    (∫ t in (m : ℝ)..(m + 1 : ℝ), chebyshevError t / t ^ (2 : ℕ)) =
      chebyshevPsi m * (1 / (m : ℝ) - 1 / (m + 1 : ℝ)) -
        (Real.log (m + 1 : ℝ) - Real.log (m : ℝ)) := by
  let c : ℝ := chebyshevPsi m
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < m))
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (by omega : 0 < m)
  have hmp1pos : (0 : ℝ) < m + 1 := by linarith
  have hfloor : ∀ t ∈ Ioo (m : ℝ) (m + 1 : ℝ), ⌊t⌋₊ = m := by
    intro t ht
    apply (Nat.floor_eq_iff (le_trans hmpos.le ht.1.le)).mpr
    constructor
    · exact ht.1.le
    · simpa only [Nat.cast_add, Nat.cast_one] using ht.2
  have hpsi : ∀ t ∈ Ioo (m : ℝ) (m + 1 : ℝ), Chebyshev.psi t = c := by
    intro t ht
    rw [psi_eq_chebyshevPsi_floor, hfloor t ht]
  have hsource :
      (∫ t in (m : ℝ)..(m + 1 : ℝ), chebyshevError t / t ^ (2 : ℕ)) =
        ∫ t in (m : ℝ)..(m + 1 : ℝ), (c - t) / t ^ (2 : ℕ) := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le (by linarith : (m : ℝ) ≤ m + 1)]
    intro t ht
    unfold chebyshevError
    change (Chebyshev.psi t - t) / t ^ (2 : ℕ) = (c - t) / t ^ (2 : ℕ)
    rw [hpsi t ht]
  have hint : IntervalIntegrable (fun t : ℝ => (c - t) / t ^ (2 : ℕ)) volume
      (m : ℝ) (m + 1 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le (by linarith : (m : ℝ) ≤ m + 1)] at ht
    exact (continuousAt_const.sub continuousAt_id).div
      (continuousAt_id.pow 2)
        (pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hmpos ht.1))) |>.continuousWithinAt
  let P : ℝ → ℝ := fun t => -c / t - Real.log t
  have hderiv : ∀ t ∈ uIcc (m : ℝ) (m + 1 : ℝ),
      HasDerivAt P ((c - t) / t ^ (2 : ℕ)) t := by
    intro t ht
    rw [uIcc_of_le (by linarith : (m : ℝ) ≤ m + 1)] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hmpos ht.1)
    have hdiv := (hasDerivAt_const (x := t) (c := -c)).div (hasDerivAt_id t) ht0
    simp only [id_eq] at hdiv
    have hlog := Real.hasDerivAt_log ht0
    change HasDerivAt (fun x => -c / x - Real.log x) ((c - t) / t ^ (2 : ℕ)) t
    apply (hdiv.sub hlog).congr_deriv
    field_simp [ht0]
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hsource, hftc]
  dsimp only [P, c]
  field_simp [hm0, hmp1pos.ne']
  ring

/-- The literal slab weighted by its upper endpoint cancels its Chebyshev value exactly against
the corresponding endpoint error.  Thus causal tail localization does not leave distributed
prime mass in the interior slabs: it moves all arithmetic information to the terminal endpoint.
-/
theorem ccmFUSuzuki_chebyshevError_unitSlab_endpointCancel
    (m : ℕ) (hm : 1 ≤ m) :
    (m + 1 : ℝ) *
        (∫ t in (m : ℝ)..(m + 1 : ℝ), chebyshevError t / t ^ (2 : ℕ)) -
      chebyshevError (m : ℝ) / (m : ℝ) =
    1 - (m + 1 : ℝ) * (Real.log (m + 1 : ℝ) - Real.log (m : ℝ)) := by
  rw [ccmFUSuzuki_chebyshevError_unitSlab m hm]
  unfold chebyshevError
  rw [psi_eq_chebyshevPsi_floor, Nat.floor_natCast]
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < m))
  have hmp1 : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hm0, hmp1]
  ring

end

end RHTower
