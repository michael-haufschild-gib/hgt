/-
# The carrier soft-min law for accessibility surprisal

The source-relative accessibility surprisal `Q(ν) = −log ∫ h dν` is a soft minimum: the *mass*
`e^{−Q}` is linear in the endpoint law, so a mixture pays the softmin of its components' surprisals,
and a rare easy component pays its rarity only through `log(1/w)`.  This is the exact quantitative
replacement for an informal "remove the exceptional carrier" instruction: a carrier is negligible at
exponent `κ` for depth-`s` circuits exactly when its weight is below `exp(−s log(M/a) − κ + Q_B)`.

Main results:
* `accessMass`, `accessSurprisal` — the first-entrance mass of an endpoint law and its surprisal.
* `accessMass_mixture` — **`(11al)`**: the mass of a mixture is the mixture of the masses.
* `accessSurprisal_le_of_component` — **`(11am)`, upper**: `Q(ν) ≤ Q_j + log(1/w_j)`.
* `le_accessSurprisal_of_forall_le` — **`(11am)`, lower**: `Q(ν) ≥ min_i Q_i`.
* `accessMass_twoCell` — **`(11an)`**: the carrier/good two-cell specialization.
* `carrier_negligible_iff` — **`(11ao)`**: the exact carrier-weight threshold.
-/
import Mathlib

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [Fintype X]

/-- The first-entrance mass an endpoint law puts on the discounted hitting potential. -/
def accessMass (h nu : X → ℝ) : ℝ := ∑ x, nu x * h x

/-- The source-relative accessibility surprisal `(11ak)` of an endpoint law. -/
def accessSurprisal (h nu : X → ℝ) : ℝ := -Real.log (accessMass h nu)

theorem accessMass_nonneg {h nu : X → ℝ} (hh : ∀ x, 0 ≤ h x) (hnu : ∀ x, 0 ≤ nu x) :
    0 ≤ accessMass h nu :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hnu x) (hh x)

theorem exp_neg_accessSurprisal {h nu : X → ℝ} (hpos : 0 < accessMass h nu) :
    Real.exp (-accessSurprisal h nu) = accessMass h nu := by
  rw [accessSurprisal, neg_neg, Real.exp_log hpos]

/-- **`(11al)`.  The first-entrance mass of a mixture is the mixture of the masses.** -/
theorem accessMass_mixture {ι : Type*} [Fintype ι] (h : X → ℝ) (w : ι → ℝ) (nu : ι → X → ℝ) :
    accessMass h (fun x => ∑ i, w i * nu i x) = ∑ i, w i * accessMass h (nu i) := by
  classical
  simp only [accessMass, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

/-- **`(11am)`, upper half.**  A mixture's surprisal is at most any component's surprisal plus the
logarithm of the reciprocal of that component's weight. -/
theorem accessSurprisal_le_of_component {ι : Type*} [Fintype ι] {h : X → ℝ} {w : ι → ℝ}
    {nu : ι → X → ℝ} (hh : ∀ x, 0 ≤ h x) (hnu : ∀ i x, 0 ≤ nu i x) (hw : ∀ i, 0 ≤ w i)
    (j : ι) (hwj : 0 < w j) (hmj : 0 < accessMass h (nu j)) :
    accessSurprisal h (fun x => ∑ i, w i * nu i x)
      ≤ accessSurprisal h (nu j) + Real.log (1 / w j) := by
  classical
  have hterm : ∀ i, 0 ≤ w i * accessMass h (nu i) := fun i =>
    mul_nonneg (hw i) (accessMass_nonneg hh (hnu i))
  have hge : w j * accessMass h (nu j)
      ≤ accessMass h (fun x => ∑ i, w i * nu i x) := by
    rw [accessMass_mixture]
    exact Finset.single_le_sum (fun i _ => hterm i) (Finset.mem_univ j)
  have hposj : 0 < w j * accessMass h (nu j) := mul_pos hwj hmj
  have hlog : Real.log (w j * accessMass h (nu j))
      ≤ Real.log (accessMass h (fun x => ∑ i, w i * nu i x)) :=
    Real.log_le_log hposj hge
  rw [Real.log_mul (ne_of_gt hwj) (ne_of_gt hmj)] at hlog
  rw [accessSurprisal, accessSurprisal, Real.log_div one_ne_zero (ne_of_gt hwj), Real.log_one]
  linarith

/-- **`(11am)`, lower half.**  A mixture's surprisal is at least the smallest component surprisal:
if every component mass is at most `m`, the mixture's surprisal is at least `−log m`. -/
theorem le_accessSurprisal_of_forall_le {ι : Type*} [Fintype ι] {h : X → ℝ} {w : ι → ℝ}
    {nu : ι → X → ℝ} {m : ℝ} (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hpos : 0 < accessMass h (fun x => ∑ i, w i * nu i x))
    (hle : ∀ i, accessMass h (nu i) ≤ m) :
    -Real.log m ≤ accessSurprisal h (fun x => ∑ i, w i * nu i x) := by
  classical
  have hbound : accessMass h (fun x => ∑ i, w i * nu i x) ≤ m := by
    rw [accessMass_mixture]
    calc (∑ i, w i * accessMass h (nu i)) ≤ ∑ i, w i * m :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (hw i)
      _ = m := by rw [← Finset.sum_mul, hwsum, one_mul]
  rw [accessSurprisal, neg_le_neg_iff]
  exact Real.log_le_log hpos hbound

/-- **`(11an)`.  The carrier/good two-cell specialization.** -/
theorem accessMass_twoCell (h : X → ℝ) (w : ℝ) (nuB nuG : X → ℝ) :
    accessMass h (fun x => w * nuB x + (1 - w) * nuG x)
      = w * accessMass h nuB + (1 - w) * accessMass h nuG := by
  simp only [accessMass, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun x _ => by ring

/-- **`(11ao)`.  The exact carrier-weight threshold.**  With `Q_B` the carrier's own surprisal and
`(M/a)^s` the depth-`s` circuit factor, the carrier's contribution to the complete-union bound is
below `e^{−κ}` exactly when its weight is below `exp(−s log(M/a) − κ + Q_B)`. -/
theorem carrier_negligible_iff {Ma kappa QB w : ℝ} (s : ℕ) (hMa : 0 < Ma) :
    Ma ^ s * (w * Real.exp (-QB)) ≤ Real.exp (-kappa)
      ↔ w ≤ Real.exp (-((s : ℝ) * Real.log Ma) - kappa + QB) := by
  have hQB : Real.exp QB ≠ 0 := (Real.exp_pos _).ne'
  have hpow : Ma ^ s = Real.exp ((s : ℝ) * Real.log Ma) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hA : (0 : ℝ) < Real.exp ((s : ℝ) * Real.log Ma - QB) := Real.exp_pos _
  have hkey : Ma ^ s * (w * Real.exp (-QB))
      = w * Real.exp ((s : ℝ) * Real.log Ma - QB) := by
    rw [hpow, Real.exp_sub, Real.exp_neg]
    field_simp
  have hrhs : Real.exp (-((s : ℝ) * Real.log Ma) - kappa + QB)
      = Real.exp (-kappa) / Real.exp ((s : ℝ) * Real.log Ma - QB) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hkey, hrhs]
  exact (le_div_iff₀ hA).symm

end

end GaloisForLFunctions.HTGeometry
