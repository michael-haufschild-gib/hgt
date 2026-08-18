import GaloisForLFunctions.RHTower.CCMUnitRieszVolterraLaplace
import GaloisForLFunctions.RHTower.CCMUnitRieszCompletedSourceWeld

/-!
# The Laplace transform of the unit-Riesz Stirling correction

The source-free correction of the unit-Riesz completed-source weld is the finite-floor Stirling
defect

```text
a(t) = exp(-t) [ N(t) t - log(N(t)!) ] - 1 - exp(-t),   N(t) = floor(exp t).
```

Its positive head `exp(-t) Σ_{n ≤ exp t} (t - log n)` is a sum of logarithmic atoms, one per
integer, switched on at `t = log n`, and each atom integrates in closed form against the Laplace
kernel.  Summing the resulting Dirichlet series gives

```text
L[a](z) = zeta(1+z)/(1+z)^2 - 1/z - 1/(z+1),     Re z > 0,
```

which is exactly the source-free factor `A` of the completed-source weld.

Unconditional; no zero-free input.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-! ## The Stirling head and its atoms -/

/-- Positive head of the Stirling correction. -/
def unitRieszStirlingHead (t : ℝ) : ℝ :=
  Real.exp (-t) * ((⌊Real.exp t⌋₊ : ℝ) * t - unitRieszStirlingLogHead t)

theorem unitRieszStirlingCorrection_eq_head (t : ℝ) :
    unitRieszStirlingCorrection t = unitRieszStirlingHead t - 1 - Real.exp (-t) := by
  rw [unitRieszStirlingCorrection, unitRieszStirlingHead]

/-- The `r+1`-st logarithmic atom of the Stirling head. -/
def unitRieszStirlingAtom (r : ℕ) (t : ℝ) : ℝ :=
  if Real.log ((r : ℝ) + 1) ≤ t then Real.exp (-t) * (t - Real.log ((r : ℝ) + 1)) else 0

theorem unitRieszStirlingAtom_eq_of_le {r : ℕ} {t : ℝ} (ht : Real.log ((r : ℝ) + 1) ≤ t) :
    unitRieszStirlingAtom r t = Real.exp (-t) * (t - Real.log ((r : ℝ) + 1)) := by
  rw [unitRieszStirlingAtom, if_pos ht]

theorem unitRieszStirlingAtom_eq_zero {r : ℕ} {t : ℝ} (ht : t < Real.log ((r : ℝ) + 1)) :
    unitRieszStirlingAtom r t = 0 := by
  rw [unitRieszStirlingAtom, if_neg (not_le.2 ht)]

theorem unitRieszStirlingAtom_nonneg (r : ℕ) (t : ℝ) : 0 ≤ unitRieszStirlingAtom r t := by
  rcases lt_or_ge t (Real.log ((r : ℝ) + 1)) with h | h
  · rw [unitRieszStirlingAtom_eq_zero h]
  · rw [unitRieszStirlingAtom_eq_of_le h]
    have : (0 : ℝ) ≤ t - Real.log ((r : ℝ) + 1) := by linarith
    positivity

theorem unitRieszStirlingHead_eq_tsum {t : ℝ} (ht : 0 ≤ t) :
    unitRieszStirlingHead t = ∑' r : ℕ, unitRieszStirlingAtom r t := by
  classical
  set N : ℕ := ⌊Real.exp t⌋₊ with hN
  have hMle : (N : ℝ) ≤ Real.exp t := Nat.floor_le (Real.exp_nonneg t)
  have hltM : Real.exp t < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsupp : ∀ r : ℕ, r ∉ Finset.range N → unitRieszStirlingAtom r t = 0 := by
    intro r hr
    have hrM : N ≤ r := by simpa using Finset.mem_range.not.1 hr
    have hlt : Real.exp t < (r : ℝ) + 1 := by
      have : (N : ℝ) + 1 ≤ (r : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hrM 1
      linarith
    refine unitRieszStirlingAtom_eq_zero ?_
    have hlog := Real.log_lt_log (Real.exp_pos t) hlt
    rwa [Real.log_exp] at hlog
  have hterm : ∀ r ∈ Finset.range N,
      unitRieszStirlingAtom r t = Real.exp (-t) * (t - Real.log ((r : ℝ) + 1)) := by
    intro r hr
    refine unitRieszStirlingAtom_eq_of_le ?_
    have hrM : r + 1 ≤ N := Finset.mem_range.1 hr
    have hle : ((r : ℝ) + 1) ≤ Real.exp t := by
      have : ((r : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast hrM
      linarith
    have hpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    have hlog := Real.log_le_log hpos hle
    rwa [Real.log_exp] at hlog
  have hsum : ∑' r : ℕ, unitRieszStirlingAtom r t =
      ∑ r ∈ Finset.range N, unitRieszStirlingAtom r t := tsum_eq_sum hsupp
  have hreindex : unitRieszStirlingLogHead t = ∑ r ∈ Finset.range N, Real.log ((r : ℝ) + 1) := by
    rw [unitRieszStirlingLogHead, ← hN, ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl ?_
    intro r _
    congr 1
    push_cast
    ring
  rw [hsum, Finset.sum_congr rfl hterm, unitRieszStirlingHead, hreindex, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hN]

/-! ## Measurability and elementary bounds -/

theorem measurable_unitRieszStirlingLogHead : Measurable unitRieszStirlingLogHead := by
  have h : unitRieszStirlingLogHead =
      (fun k : ℕ => ∑ n ∈ Finset.Icc 1 k, Real.log n) ∘ (fun t : ℝ => ⌊Real.exp t⌋₊) := rfl
  rw [h]
  exact measurable_from_top.comp (Nat.measurable_floor.comp Real.measurable_exp)

theorem measurable_unitRieszStirlingHead : Measurable unitRieszStirlingHead := by
  have hfloor : Measurable fun t : ℝ => ((⌊Real.exp t⌋₊ : ℕ) : ℝ) :=
    measurable_from_top.comp (Nat.measurable_floor.comp Real.measurable_exp)
  exact (Real.measurable_exp.comp measurable_neg).mul
    ((hfloor.mul measurable_id).sub measurable_unitRieszStirlingLogHead)

theorem measurable_unitRieszStirlingCorrection : Measurable unitRieszStirlingCorrection := by
  have h : unitRieszStirlingCorrection =
      fun t => unitRieszStirlingHead t - 1 - Real.exp (-t) :=
    funext unitRieszStirlingCorrection_eq_head
  rw [h]
  exact (measurable_unitRieszStirlingHead.sub measurable_const).sub
    (Real.measurable_exp.comp measurable_neg)

theorem unitRieszStirlingHead_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ unitRieszStirlingHead t := by
  rw [unitRieszStirlingHead_eq_tsum ht]
  exact tsum_nonneg fun r => unitRieszStirlingAtom_nonneg r t

theorem unitRieszStirlingHead_le_one {t : ℝ} (ht : 0 ≤ t) : unitRieszStirlingHead t ≤ 1 := by
  have h := unitRieszStirlingCorrection_le ht
  rw [unitRieszStirlingCorrection_eq_head] at h
  have hpos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  linarith

theorem abs_unitRieszStirlingCorrection_le {t : ℝ} (ht : 0 ≤ t) :
    |unitRieszStirlingCorrection t| ≤ 4 * (1 + t) := by
  have h1 := unitRieszStirlingCorrection_le ht
  have h2 := unitRieszStirlingCorrection_lower ht
  have he : Real.exp (-t) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have he0 : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  rw [abs_le]
  constructor <;> nlinarith

end GaloisForLFunctions.RHTower
