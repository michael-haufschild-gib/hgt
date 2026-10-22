import GaloisForLFunctions.ScaleSignedIncidenceCriticality.ThePrimeConeIsAPointAndTheGateIsIndexwise
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheFloorTheorem

/-!
# The prime-window ladder converges

The prime face had a qualitative unit (the failure apertures, with its universal floor) and an
indexwise gate, but no quantitative ladder: nothing that improves as the radius grows. This module
supplies one, and the pattern is the same as on the incidence face
(`FinitelyManyMembershipBitsHaveAnExactLimit`).

The **defect scale** of a weight is `weightDefectScale lam = sup {1/m : m ≥ 2, lam m ≠ Λ m}`, a
number in `[0, ½]` which vanishes exactly when the weight is `Λ` on every index the Weil functional
sees (`weightDefectScale_eq_zero_iff`) — that is, exactly on the full Weil cone, by the rigidity of
`ThePrimeConeIsAPointAndTheGateIsIndexwise`.

Reading the amplitudes inside the window `log m < 2R` leaves every index outside it free. The worst
case is to perturb the **smallest index outside the window** (`leastOutsideWindow`), so

`resolutionLimit weightDefectScale (windowReading R) Λ = 1 / m₀(R)`
(`resolutionLimit_weightDefectScale_windowReading`),

and the radius-`R` certificate, being a function of that window
(`SquareRootThreshold.radiusReading_congr_of_agree_below`), inherits the same bound. As `R` grows,
`m₀(R)` grows past every bound and the limit decreases to `0`
(`primeWindowLadderConverges`): **the prime-window ladder is a progress measure.**

So the prime face is quantitative after all, and its progress is measured by the reciprocal of the
first prime power the window does not reach. With the height ladder, the level ladder and the
incidence bits, the field now has four convergent ladders and one flat one — the aperture ladder in
the width unit.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The defect scale of a weight -/

/-- The indices at which a weight differs from the von Mangoldt weight. -/
def defectIndices (lam : ℕ → ℝ) : Set ℕ :=
  {m : ℕ | 2 ≤ m ∧ lam m ≠ (ArithmeticFunction.vonMangoldt m : ℝ)}

/-- The **defect scale**: the largest reciprocal index at which the weight deviates from `Λ`. -/
noncomputable def weightDefectScale (lam : ℕ → ℝ) : ℝ :=
  sSup ((fun m : ℕ => ((m : ℝ))⁻¹) '' defectIndices lam)

theorem weightDefectScale_le_half (lam : ℕ → ℝ) : weightDefectScale lam ≤ 1 / 2 := by
  refine Real.sSup_le ?_ (by norm_num)
  rintro x ⟨m, ⟨hm, -⟩, rfl⟩
  have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num]
  exact (inv_le_inv₀ (by linarith) (by norm_num)).mpr h2

theorem weightDefectScale_nonneg (lam : ℕ → ℝ) : 0 ≤ weightDefectScale lam := by
  refine Real.sSup_nonneg ?_
  rintro x ⟨m, ⟨hm, -⟩, rfl⟩
  have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  exact (inv_pos.mpr (by linarith)).le

/-- **The defect scale vanishes exactly on the cone's index condition.** -/
theorem weightDefectScale_eq_zero_iff (lam : ℕ → ℝ) :
    weightDefectScale lam = 0 ↔
      ∀ m : ℕ, 2 ≤ m → lam m = (ArithmeticFunction.vonMangoldt m : ℝ) := by
  constructor
  · intro h m hm
    by_contra hne
    have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hpos : (0 : ℝ) < ((m : ℝ))⁻¹ := inv_pos.mpr (by linarith)
    have hbdd : BddAbove ((fun k : ℕ => ((k : ℝ))⁻¹) '' defectIndices lam) := by
      refine ⟨1 / 2, ?_⟩
      rintro x ⟨k, ⟨hk, -⟩, rfl⟩
      have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num]
      exact (inv_le_inv₀ (by linarith) (by norm_num)).mpr hk2
    have hle : ((m : ℝ))⁻¹ ≤ weightDefectScale lam := le_csSup hbdd ⟨m, ⟨hm, hne⟩, rfl⟩
    rw [h] at hle
    exact absurd hle (not_le.mpr hpos)
  · intro h
    have hempty : defectIndices lam = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun m hm => hm.2 (h m hm.1)
    unfold weightDefectScale
    rw [hempty, Set.image_empty, Real.sSup_empty]

/-! ### 2. The smallest index outside the window -/

theorem exists_index_outside_window (R : ℝ) : ∃ m : ℕ, 2 ≤ m ∧ 2 * R ≤ Real.log m := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp (2 * R))
  refine ⟨n + 2, by omega, ?_⟩
  have hpos : (0 : ℝ) < ((n : ℝ) + 2) := by positivity
  have hle : Real.exp (2 * R) ≤ ((n : ℝ) + 2) := by linarith
  have := (Real.le_log_iff_exp_le hpos).mpr hle
  push_cast
  exact this

/-- The smallest index the window `log m < 2R` does not reach. -/
noncomputable def leastOutsideWindow (R : ℝ) : ℕ := Nat.find (exists_index_outside_window R)

theorem leastOutsideWindow_spec (R : ℝ) :
    2 ≤ leastOutsideWindow R ∧ 2 * R ≤ Real.log (leastOutsideWindow R) :=
  Nat.find_spec (exists_index_outside_window R)

theorem leastOutsideWindow_le {R : ℝ} {m : ℕ} (hm : 2 ≤ m) (hlog : 2 * R ≤ Real.log m) :
    leastOutsideWindow R ≤ m :=
  Nat.find_le ⟨hm, hlog⟩

/-! ### 3. The window reading and its exact limit -/

/-- The amplitudes inside the window: the finite prime data a radius-`R` certificate reads. -/
def windowReading (R : ℝ) (lam : ℕ → ℝ) :
    {m : ℕ // 2 ≤ m ∧ Real.log m < 2 * R} → ℝ := fun m => lam m.1

/-- Perturbing an index outside the window leaves the window reading unchanged. -/
theorem windowReading_perturb {R : ℝ} {m : ℕ} (_hm : 2 ≤ m) (hlog : 2 * R ≤ Real.log m) (c : ℝ) :
    windowReading R (perturbVonMangoldt m c) =
      windowReading R (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) := by
  funext k
  have hne : k.1 ≠ m := fun h => absurd k.2.2 (not_lt.mpr (h ▸ hlog))
  simp only [windowReading, perturbVonMangoldt, Function.update_apply, hne, if_false]

/-- The defect scale of a single-index perturbation is the reciprocal of that index. -/
theorem weightDefectScale_perturb {m : ℕ} (hm : 2 ≤ m) {c : ℝ}
    (hc : c ≠ (ArithmeticFunction.vonMangoldt m : ℝ)) :
    weightDefectScale (perturbVonMangoldt m c) = ((m : ℝ))⁻¹ := by
  have hset : defectIndices (perturbVonMangoldt m c) = {m} := by
    ext k
    simp only [defectIndices, mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hk, hne⟩
      by_contra hkm
      exact hne (by
        simp only [perturbVonMangoldt, Function.update_apply, hkm, if_false])
    · rintro rfl
      exact ⟨hm, by rw [perturbVonMangoldt_self]; exact hc⟩
  unfold weightDefectScale
  rw [hset, Set.image_singleton, csSup_singleton]

/-- **The exact limit of the window reading.** -/
theorem resolutionLimit_weightDefectScale_windowReading (R : ℝ) :
    resolutionLimit weightDefectScale (windowReading R)
        (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) =
      ((leastOutsideWindow R : ℝ))⁻¹ := by
  obtain ⟨hm0, hlog0⟩ := leastOutsideWindow_spec R
  have hm02 : (2 : ℝ) ≤ (leastOutsideWindow R : ℝ) := by exact_mod_cast hm0
  have hm00 : (0 : ℝ) < (leastOutsideWindow R : ℝ) := by linarith
  have hub : ∀ lam ∈ shadow (windowReading R)
      (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)),
      weightDefectScale lam ≤ ((leastOutsideWindow R : ℝ))⁻¹ := by
    intro lam hlam
    refine Real.sSup_le ?_ (by positivity)
    rintro y ⟨m, ⟨hm, hne⟩, rfl⟩
    have hlog : 2 * R ≤ Real.log m := by
      by_contra hcon
      exact hne (congrFun (mem_shadow_iff.mp hlam) ⟨m, hm, not_le.mp hcon⟩)
    have hle : leastOutsideWindow R ≤ m := leastOutsideWindow_le hm hlog
    have hle' : (leastOutsideWindow R : ℝ) ≤ (m : ℝ) := by exact_mod_cast hle
    exact (inv_le_inv₀ (by linarith) hm00).mpr hle'
  have hbdd : BddAbove (weightDefectScale '' shadow (windowReading R)
      (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))) :=
    ⟨((leastOutsideWindow R : ℝ))⁻¹, by rintro x ⟨lam, hlam, rfl⟩; exact hub lam hlam⟩
  set c : ℝ := (ArithmeticFunction.vonMangoldt (leastOutsideWindow R) : ℝ) + 1 with hc
  have hcne : c ≠ (ArithmeticFunction.vonMangoldt (leastOutsideWindow R) : ℝ) := by
    simp only [hc]; linarith
  refine le_antisymm (csSup_le (shadow_image_nonempty weightDefectScale (windowReading R) _) ?_) ?_
  · rintro x ⟨lam, hlam, rfl⟩
    exact hub lam hlam
  · have hmem : perturbVonMangoldt (leastOutsideWindow R) c ∈
        shadow (windowReading R) (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) :=
      windowReading_perturb hm0 hlog0 c
    have hle := le_csSup hbdd ⟨_, hmem, rfl⟩
    rwa [weightDefectScale_perturb hm0 hcne] at hle

/-! ### 4. The ladder converges -/

/-- **The prime-window ladder is a progress measure.** Every tolerance is reached at a finite
radius. -/
theorem primeWindowLadderConverges {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, resolutionLimit weightDefectScale (windowReading R)
      (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)) < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨Real.log (N + 2), ?_⟩
  rw [resolutionLimit_weightDefectScale_windowReading]
  obtain ⟨hm0, hlog0⟩ := leastOutsideWindow_spec (Real.log (N + 2))
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans (by positivity) hN
  have hgt : (N : ℝ) < (leastOutsideWindow (Real.log ((N : ℝ) + 2)) : ℝ) := by
    by_contra hcon
    have hle : (leastOutsideWindow (Real.log ((N : ℝ) + 2)) : ℝ) ≤ (N : ℝ) := not_lt.mp hcon
    have hpos : (0 : ℝ) < (leastOutsideWindow (Real.log ((N : ℝ) + 2)) : ℝ) := by
      have h2 : (2 : ℝ) ≤ (leastOutsideWindow (Real.log ((N : ℝ) + 2)) : ℝ) := by
        exact_mod_cast hm0
      linarith
    have hmono : Real.log (leastOutsideWindow (Real.log ((N : ℝ) + 2))) ≤ Real.log (N : ℝ) :=
      Real.log_le_log hpos hle
    have hstep : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 2) :=
      Real.log_le_log hNpos (by linarith)
    have hlogpos : 0 < Real.log ((N : ℝ) + 2) := Real.log_pos (by linarith)
    linarith [hlog0, hmono, hstep, hlogpos]
  have hq0 : (0 : ℝ) < (leastOutsideWindow (Real.log ((N : ℝ) + 2)) : ℝ) := by linarith
  rw [inv_eq_one_div, div_lt_iff₀ hq0]
  rw [div_lt_iff₀ hε] at hN
  nlinarith [hgt, hN, mul_lt_mul_of_pos_right hgt hε]

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
