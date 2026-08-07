import GaloisForLFunctions.RHTower.EulerHellingerLocalGrowthBounds

/-!
# The first-order shape of the local sewing logarithm

The first prime power of the local sewing series is `p^(2c-1)` up to three lower abscissae, and all
higher prime powers are dominated by the geometric tail of `q = p^(2c-1)`:

```text
|localSewingLog p c - p^(2c-1)| ≤ K_c p^(α-1),        α = max (4c-1) c < 2c.
```
-/

open Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The exponent controlling every correction to the leading prime power. -/
def sewingErrorExponent (c : ℝ) : ℝ := max (4 * c - 1) c

theorem sewingErrorExponent_pos {c : ℝ} (hc0 : 0 < c) : 0 < sewingErrorExponent c :=
  lt_of_lt_of_le hc0 (le_max_right _ _)

theorem sewingErrorExponent_lt {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) :
    sewingErrorExponent c < 2 * c :=
  max_lt (by linarith) (by linarith)

theorem sewingErrorExponent_lt_one {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) :
    sewingErrorExponent c < 1 :=
  lt_trans (sewingErrorExponent_lt hc0 hc) (by linarith)

/-- The constant in the first-order comparison. -/
def sewingFirstOrderConst (c : ℝ) : ℝ := 5 + (1 - sewingAbscissaMass c)⁻¹

theorem sewingFirstOrderConst_nonneg {c : ℝ} (hc : c < 1 / 2) : 0 ≤ sewingFirstOrderConst c := by
  have h := sewingAbscissaMass_lt_one hc
  have : (0 : ℝ) < (1 - sewingAbscissaMass c)⁻¹ := inv_pos.mpr (by linarith)
  rw [sewingFirstOrderConst]
  linarith

/-! ## The prime-power series in power coordinates -/

private theorem localSewingTerm_eq {p : ℕ} (hp : p.Prime) (c : ℝ) (j : ℕ) :
    2 * ((p : ℝ) ^ (-((j : ℝ) + 1)) / ((j : ℝ) + 1)) *
        (Real.sinh (2 * (c * ((j : ℝ) + 1) * Real.log (p : ℝ)))
          - 2 * Real.sinh (c * ((j : ℝ) + 1) * Real.log (p : ℝ)))
      = ((p : ℝ) ^ (-((j : ℝ) + 1)) / ((j : ℝ) + 1)) *
        ((p : ℝ) ^ (2 * c * ((j : ℝ) + 1)) - (p : ℝ) ^ (-(2 * c * ((j : ℝ) + 1)))
          - 2 * ((p : ℝ) ^ (c * ((j : ℝ) + 1)) - (p : ℝ) ^ (-(c * ((j : ℝ) + 1))))) := by
  have h2c := rpow_sub_rpow_neg_eq_two_sinh hp (2 * c * ((j : ℝ) + 1))
  have h1c := rpow_sub_rpow_neg_eq_two_sinh hp (c * ((j : ℝ) + 1))
  have harg : 2 * c * ((j : ℝ) + 1) * Real.log (p : ℝ)
      = 2 * (c * ((j : ℝ) + 1) * Real.log (p : ℝ)) := by ring
  rw [harg] at h2c
  linear_combination (-((p : ℝ) ^ (-((j : ℝ) + 1)) / ((j : ℝ) + 1))) * h2c
    + (2 * ((p : ℝ) ^ (-((j : ℝ) + 1)) / ((j : ℝ) + 1))) * h1c

/-- Every prime power of the local series is dominated by the geometric ratio `p^(2c-1)`. -/
theorem localSewingTerm_le {p : ℕ} (hp : p.Prime) {c : ℝ} (hc0 : 0 < c) (j : ℕ) :
    2 * ((p : ℝ) ^ (-((j : ℝ) + 1)) / ((j : ℝ) + 1)) *
        (Real.sinh (2 * (c * ((j : ℝ) + 1) * Real.log (p : ℝ)))
          - 2 * Real.sinh (c * ((j : ℝ) + 1) * Real.log (p : ℝ)))
      ≤ ((p : ℝ) ^ (2 * c - 1)) ^ (j + 1) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hmass : (0 : ℝ) < (p : ℝ) ^ (-((j : ℝ) + 1)) := Real.rpow_pos_of_pos hp0 _
  have hlow : (p : ℝ) ^ (-(c * ((j : ℝ) + 1))) ≤ (p : ℝ) ^ (c * ((j : ℝ) + 1)) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by nlinarith)
  have hneg : (0 : ℝ) < (p : ℝ) ^ (-(2 * c * ((j : ℝ) + 1))) := Real.rpow_pos_of_pos hp0 _
  rw [localSewingTerm_eq hp c j]
  have hinner : (p : ℝ) ^ (2 * c * ((j : ℝ) + 1)) - (p : ℝ) ^ (-(2 * c * ((j : ℝ) + 1)))
      - 2 * ((p : ℝ) ^ (c * ((j : ℝ) + 1)) - (p : ℝ) ^ (-(c * ((j : ℝ) + 1))))
      ≤ (p : ℝ) ^ (2 * c * ((j : ℝ) + 1)) := by
    nlinarith [hlow, hneg]
  have hpos : (0 : ℝ) ≤ (p : ℝ) ^ (-((j : ℝ) + 1)) / ((j : ℝ) + 1) := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left hinner hpos) ?_
  have hdrop : ((p : ℝ) ^ (-((j : ℝ) + 1)) / ((j : ℝ) + 1)) * (p : ℝ) ^ (2 * c * ((j : ℝ) + 1))
      ≤ (p : ℝ) ^ (-((j : ℝ) + 1)) * (p : ℝ) ^ (2 * c * ((j : ℝ) + 1)) := by
    have hnn : (0 : ℝ) < (p : ℝ) ^ (2 * c * ((j : ℝ) + 1)) := Real.rpow_pos_of_pos hp0 _
    have hdiv : (p : ℝ) ^ (-((j : ℝ) + 1)) / ((j : ℝ) + 1) ≤ (p : ℝ) ^ (-((j : ℝ) + 1)) := by
      rw [div_le_iff₀ hj]
      nlinarith [hmass]
    exact mul_le_mul_of_nonneg_right hdiv hnn.le
  refine le_trans hdrop (le_of_eq ?_)
  rw [← Real.rpow_add hp0, ← Real.rpow_natCast ((p : ℝ) ^ (2 * c - 1)) (j + 1),
    ← Real.rpow_mul hp0.le]
  congr 1
  push_cast
  ring

/-! ## The first prime power -/

/-- The first prime power of the local sewing series. -/
def localFirstPower (p : ℕ) (c : ℝ) : ℝ :=
  (p : ℝ) ^ (-(1 : ℝ)) *
    ((p : ℝ) ^ (2 * c) - (p : ℝ) ^ (-(2 * c)) - 2 * (p : ℝ) ^ c + 2 * (p : ℝ) ^ (-c))

private theorem localSewingTerm_zero {p : ℕ} (hp : p.Prime) (c : ℝ) :
    2 * ((p : ℝ) ^ (-(((0 : ℕ) : ℝ) + 1)) / (((0 : ℕ) : ℝ) + 1)) *
        (Real.sinh (2 * (c * (((0 : ℕ) : ℝ) + 1) * Real.log (p : ℝ)))
          - 2 * Real.sinh (c * (((0 : ℕ) : ℝ) + 1) * Real.log (p : ℝ)))
      = localFirstPower p c := by
  have h2c : (p : ℝ) ^ (2 * c) - (p : ℝ) ^ (-(2 * c))
      = 2 * Real.sinh (2 * c * Real.log (p : ℝ)) := rpow_sub_rpow_neg_eq_two_sinh hp _
  have h1c : (p : ℝ) ^ c - (p : ℝ) ^ (-c)
      = 2 * Real.sinh (c * Real.log (p : ℝ)) := rpow_sub_rpow_neg_eq_two_sinh hp _
  have hcast0 : ((0 : ℕ) : ℝ) = 0 := by norm_num
  rw [hcast0, localFirstPower]
  have harg1 : 2 * (c * (0 + 1) * Real.log (p : ℝ)) = 2 * c * Real.log (p : ℝ) := by ring
  have harg2 : c * (0 + 1) * Real.log (p : ℝ) = c * Real.log (p : ℝ) := by ring
  have hexp : -((0 : ℝ) + 1) = -(1 : ℝ) := by ring
  rw [harg1, harg2, hexp]
  linear_combination (-((p : ℝ) ^ (-(1 : ℝ)))) * h2c + (2 * (p : ℝ) ^ (-(1 : ℝ))) * h1c

/-! ## The abscissa comparisons -/

private theorem rpow_shift {p : ℕ} (hp : p.Prime) (r : ℝ) :
    (p : ℝ) ^ (-(1 : ℝ)) * (p : ℝ) ^ r = (p : ℝ) ^ (r - 1) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  rw [← Real.rpow_add hp0]
  congr 1
  ring

private theorem rpow_le_error {p : ℕ} (hp : p.Prime) {c r : ℝ}
    (hr : r ≤ sewingErrorExponent c) :
    (p : ℝ) ^ (r - 1) ≤ (p : ℝ) ^ (sewingErrorExponent c - 1) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)

/-- The first prime power differs from `p^(2c-1)` by three lower abscissae. -/
theorem abs_localFirstPower_sub_rpow_le {p : ℕ} (hp : p.Prime) {c : ℝ} (hc0 : 0 < c) :
    |localFirstPower p c - (p : ℝ) ^ (2 * c - 1)| ≤
      5 * (p : ℝ) ^ (sewingErrorExponent c - 1) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hα : 0 < sewingErrorExponent c := sewingErrorExponent_pos hc0
  have hcα : c ≤ sewingErrorExponent c := le_max_right _ _
  have hdiff : localFirstPower p c - (p : ℝ) ^ (2 * c - 1)
      = -(p : ℝ) ^ (-(2 * c) - 1) - 2 * (p : ℝ) ^ (c - 1) + 2 * (p : ℝ) ^ (-c - 1) := by
    rw [localFirstPower]
    linear_combination rpow_shift hp (2 * c) - rpow_shift hp (-(2 * c))
      - 2 * rpow_shift hp c + 2 * rpow_shift hp (-c)
  have h1 : (p : ℝ) ^ (-(2 * c) - 1) ≤ (p : ℝ) ^ (sewingErrorExponent c - 1) :=
    rpow_le_error hp (by linarith)
  have h2 : (p : ℝ) ^ (c - 1) ≤ (p : ℝ) ^ (sewingErrorExponent c - 1) :=
    rpow_le_error hp hcα
  have h3 : (p : ℝ) ^ (-c - 1) ≤ (p : ℝ) ^ (sewingErrorExponent c - 1) :=
    rpow_le_error hp (by linarith)
  have p1 : (0 : ℝ) < (p : ℝ) ^ (-(2 * c) - 1) := Real.rpow_pos_of_pos hp0 _
  have p2 : (0 : ℝ) < (p : ℝ) ^ (c - 1) := Real.rpow_pos_of_pos hp0 _
  have p3 : (0 : ℝ) < (p : ℝ) ^ (-c - 1) := Real.rpow_pos_of_pos hp0 _
  rw [hdiff, abs_le]
  constructor
  · linarith
  · linarith

/-! ## The geometric tail -/

theorem localSewingLog_sub_firstPower_nonneg {p : ℕ} (hp : p.Prime) {c : ℝ} (hc0 : 0 < c)
    (hc : c < 1 / 2) : 0 ≤ localSewingLog p c - localFirstPower p c := by
  have habs : |c| < 1 / 2 := by
    rw [abs_of_pos hc0]
    exact hc
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hsum := hasSum_localSewingLog hp habs
  have hterm : ∀ k : ℕ,
      0 ≤ 2 * ((p : ℝ) ^ (-((k : ℝ) + 1)) / ((k : ℝ) + 1)) *
        (Real.sinh (2 * (c * ((k : ℝ) + 1) * Real.log (p : ℝ)))
          - 2 * Real.sinh (c * ((k : ℝ) + 1) * Real.log (p : ℝ))) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hmass : (0 : ℝ) < (p : ℝ) ^ (-((k : ℝ) + 1)) := Real.rpow_pos_of_pos hp0 _
    have hu : 0 < c * ((k : ℝ) + 1) * Real.log (p : ℝ) := by positivity
    have hstep := sinh_two_mul_sub_two_sinh_pos hu
    have hcoef : 0 < 2 * ((p : ℝ) ^ (-((k : ℝ) + 1)) / ((k : ℝ) + 1)) := by positivity
    exact (mul_pos hcoef hstep).le
  have hle := le_hasSum hsum 0 (fun j _ => hterm j)
  rw [localSewingTerm_zero hp c] at hle
  linarith

private theorem rpow_geometric_lt_one {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : c < 1 / 2) :
    (p : ℝ) ^ (2 * c - 1) ≤ sewingAbscissaMass c := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have h : (2 : ℝ) ^ (1 - 2 * c) ≤ (p : ℝ) ^ (1 - 2 * c) := by
    refine Real.rpow_le_rpow (by norm_num) ?_ (by linarith)
    exact_mod_cast hp.two_le
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (1 - 2 * c) := Real.rpow_pos_of_pos (by norm_num) _
  have hinv : ((p : ℝ) ^ (1 - 2 * c))⁻¹ ≤ ((2 : ℝ) ^ (1 - 2 * c))⁻¹ :=
    (inv_le_inv₀ (Real.rpow_pos_of_pos hp0 _) h2).mpr h
  have hpe : (p : ℝ) ^ (2 * c - 1) = ((p : ℝ) ^ (1 - 2 * c))⁻¹ := by
    rw [← Real.rpow_neg hp0.le]
    congr 1
    ring
  have hme : sewingAbscissaMass c = ((2 : ℝ) ^ (1 - 2 * c))⁻¹ := by
    rw [sewingAbscissaMass, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  rw [hpe, hme]
  exact hinv

theorem localSewingLog_sub_firstPower_le {p : ℕ} (hp : p.Prime) {c : ℝ} (hc0 : 0 < c)
    (hc : c < 1 / 2) :
    localSewingLog p c - localFirstPower p c ≤
      (1 - sewingAbscissaMass c)⁻¹ * ((p : ℝ) ^ (2 * c - 1)) ^ 2 := by
  have habs : |c| < 1 / 2 := by
    rw [abs_of_pos hc0]
    exact hc
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hq0 : (0 : ℝ) < (p : ℝ) ^ (2 * c - 1) := Real.rpow_pos_of_pos hp0 _
  have hqm := rpow_geometric_lt_one hp hc
  have hmlt := sewingAbscissaMass_lt_one hc
  have hq1 : (p : ℝ) ^ (2 * c - 1) < 1 := lt_of_le_of_lt hqm hmlt
  have hsum := hasSum_localSewingLog hp habs
  have htail : HasSum (fun k : ℕ =>
      2 * ((p : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) + 1)) / (((k + 1 : ℕ) : ℝ) + 1)) *
        (Real.sinh (2 * (c * (((k + 1 : ℕ) : ℝ) + 1) * Real.log (p : ℝ)))
          - 2 * Real.sinh (c * (((k + 1 : ℕ) : ℝ) + 1) * Real.log (p : ℝ))))
      (localSewingLog p c - localFirstPower p c) := by
    refine (hasSum_nat_add_iff (f := fun k : ℕ =>
      2 * ((p : ℝ) ^ (-((k : ℝ) + 1)) / ((k : ℝ) + 1)) *
        (Real.sinh (2 * (c * ((k : ℝ) + 1) * Real.log (p : ℝ)))
          - 2 * Real.sinh (c * ((k : ℝ) + 1) * Real.log (p : ℝ)))) 1).mpr ?_
    rw [Finset.sum_range_one, localSewingTerm_zero hp c, sub_add_cancel]
    exact hsum
  have hgeom := (hasSum_geometric_of_lt_one hq0.le hq1).mul_left (((p : ℝ) ^ (2 * c - 1)) ^ 2)
  have hcmp := hasSum_le (fun k : ℕ => by
      refine le_trans (localSewingTerm_le hp hc0 (k + 1)) (le_of_eq ?_)
      rw [pow_add]
      ring) htail hgeom
  refine le_trans hcmp ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact (inv_le_inv₀ (by linarith) (by linarith)).mpr (by linarith)

/-! ## The first-order comparison -/

/-- **The local sewing logarithm is `p^(2c-1)` to first order.** -/
theorem abs_localSewingLog_sub_rpow_le {p : ℕ} (hp : p.Prime) {c : ℝ} (hc0 : 0 < c)
    (hc : c < 1 / 2) :
    |localSewingLog p c - (p : ℝ) ^ (2 * c - 1)| ≤
      sewingFirstOrderConst c * (p : ℝ) ^ (sewingErrorExponent c - 1) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hmlt := sewingAbscissaMass_lt_one hc
  have hinvpos : (0 : ℝ) < (1 - sewingAbscissaMass c)⁻¹ := inv_pos.mpr (by linarith)
  have hlow := localSewingLog_sub_firstPower_nonneg hp hc0 hc
  have hhigh := localSewingLog_sub_firstPower_le hp hc0 hc
  have hfirst := abs_localFirstPower_sub_rpow_le hp hc0
  have hsq : ((p : ℝ) ^ (2 * c - 1)) ^ 2 = (p : ℝ) ^ (4 * c - 2) := by
    rw [← Real.rpow_natCast ((p : ℝ) ^ (2 * c - 1)) 2, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  have hsqle : (p : ℝ) ^ (4 * c - 2) ≤ (p : ℝ) ^ (sewingErrorExponent c - 1) := by
    have h := rpow_le_error hp (c := c) (r := 4 * c - 1) (le_max_left _ _)
    rw [show 4 * c - 1 - 1 = 4 * c - 2 by ring] at h
    exact h
  have hepos : (0 : ℝ) < (p : ℝ) ^ (sewingErrorExponent c - 1) := Real.rpow_pos_of_pos hp0 _
  rw [hsq] at hhigh
  have htailbound : localSewingLog p c - localFirstPower p c ≤
      (1 - sewingAbscissaMass c)⁻¹ * (p : ℝ) ^ (sewingErrorExponent c - 1) :=
    le_trans hhigh (mul_le_mul_of_nonneg_left hsqle hinvpos.le)
  rw [abs_le] at hfirst ⊢
  rw [sewingFirstOrderConst, add_mul]
  constructor
  · linarith [hfirst.1]
  · linarith [hfirst.2]

end

end RHTower
