import GaloisForLFunctions.RHTower.EulerHellingerDyadicSignSeries

/-!
# Two-sided growth bounds for the local sewing logarithm

For `0 < c < 1/2` the local sewing logarithm at a prime is comparable to `p^(2c-1)`:

```text
localSewingLog p c ≤ K_c p^(2c-1)                        (all primes),
localSewingLog p c ≥ (1/2) p^(2c-1)                      (p^c ≥ 6).
```

The upper bound drops the two negative Euler logarithms and applies `-log(1-x) ≤ x/(1-x)`.  The
lower bound keeps the first prime power of the positive series and compares `p^(2c)` with the two
lower hyperbolic terms.
-/

open Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Elementary logarithm bounds -/

theorem neg_log_one_sub_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ -Real.log (1 - x) := by
  have h : Real.log (1 - x) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  linarith

theorem neg_log_one_sub_le_of_le {x q : ℝ} (hx0 : 0 ≤ x) (hxq : x ≤ q) (hq : q < 1) :
    -Real.log (1 - x) ≤ (1 - q)⁻¹ * x := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hqpos : (0 : ℝ) < 1 - q := by linarith
  have hne : (1 : ℝ) - x ≠ 0 := ne_of_gt hpos
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have hval : (1 - x)⁻¹ - 1 = (1 - x)⁻¹ * x := by
    field_simp
    ring
  rw [hval] at h
  have hinv : (1 - x)⁻¹ ≤ (1 - q)⁻¹ := (inv_le_inv₀ hpos hqpos).mpr (by linarith)
  have hmul : (1 - x)⁻¹ * x ≤ (1 - q)⁻¹ * x := mul_le_mul_of_nonneg_right hinv hx0
  linarith

/-! ## The prime abscissa estimates -/

private theorem rpow_neg_le {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 < a) :
    (p : ℝ) ^ (-a) ≤ (2 : ℝ) ^ (-a) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hbase : (2 : ℝ) ^ a ≤ (p : ℝ) ^ a := Real.rpow_le_rpow (by norm_num) hp2 ha.le
  have h2 : (0 : ℝ) < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by positivity)]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos (by positivity) a) h2).mpr hbase

private theorem two_rpow_neg_lt_one {a : ℝ} (ha : 0 < a) : (2 : ℝ) ^ (-a) < 1 := by
  rw [Real.rpow_neg (by norm_num), inv_lt_one_iff₀]
  right
  exact Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, ha⟩)

/-- The dyadic upper abscissa mass at the leading exponent. -/
def sewingAbscissaMass (c : ℝ) : ℝ := (2 : ℝ) ^ (-(1 - 2 * c))

theorem sewingAbscissaMass_lt_one {c : ℝ} (hc : c < 1 / 2) : sewingAbscissaMass c < 1 :=
  two_rpow_neg_lt_one (by linarith)

theorem sewingAbscissaMass_nonneg (c : ℝ) : 0 ≤ sewingAbscissaMass c :=
  (Real.rpow_pos_of_pos (by norm_num) _).le

/-- The comparison constant in the upper growth bound. -/
def sewingGrowthConst (c : ℝ) : ℝ := (1 - sewingAbscissaMass c)⁻¹ + 4

theorem sewingGrowthConst_pos {c : ℝ} (hc : c < 1 / 2) : 0 < sewingGrowthConst c := by
  have h := sewingAbscissaMass_lt_one hc
  have : (0 : ℝ) < (1 - sewingAbscissaMass c)⁻¹ := inv_pos.mpr (by linarith)
  rw [sewingGrowthConst]
  linarith

/-- **The local sewing logarithm grows at most like `p^(2c-1)`.** -/
theorem localSewingLog_le {p : ℕ} (hp : p.Prime) {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) :
    localSewingLog p c ≤ sewingGrowthConst c * (p : ℝ) ^ (2 * c - 1) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hq := sewingAbscissaMass_lt_one hc
  have h3 : (p : ℝ) ^ (-(1 - 2 * c)) = (p : ℝ) ^ (2 * c - 1) := by
    congr 1
    ring
  have hx1pos : (0 : ℝ) < (p : ℝ) ^ (2 * c - 1) := Real.rpow_pos_of_pos hp0 _
  have hx2pos : (0 : ℝ) < (p : ℝ) ^ (-(1 + 2 * c)) := Real.rpow_pos_of_pos hp0 _
  have hx3pos : (0 : ℝ) < (p : ℝ) ^ (-(1 - c)) := Real.rpow_pos_of_pos hp0 _
  have hx4pos : (0 : ℝ) < (p : ℝ) ^ (-(1 + c)) := Real.rpow_pos_of_pos hp0 _
  have hx1le : (p : ℝ) ^ (2 * c - 1) ≤ sewingAbscissaMass c := by
    rw [← h3]
    exact rpow_neg_le hp (by linarith)
  have hx2lt : (p : ℝ) ^ (-(1 + 2 * c)) < 1 :=
    lt_of_le_of_lt (rpow_neg_le hp (by linarith)) (two_rpow_neg_lt_one (by linarith))
  have hx3lt : (p : ℝ) ^ (-(1 - c)) < 1 :=
    lt_of_le_of_lt (rpow_neg_le hp (by linarith)) (two_rpow_neg_lt_one (by linarith))
  have htwo : (2 : ℝ) ^ (-(1 + c)) ≤ 1 / 2 := by
    have h1 : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ (1 + c) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rw [Real.rpow_one] at h1
    rw [Real.rpow_neg (by norm_num), one_div]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)).mpr h1
  have hx4half : (p : ℝ) ^ (-(1 + c)) ≤ 1 / 2 := le_trans (rpow_neg_le hp (by linarith)) htwo
  have hdrop2 : 0 ≤ -Real.log (1 - (p : ℝ) ^ (-(1 + 2 * c))) :=
    neg_log_one_sub_nonneg hx2pos.le hx2lt
  have hdrop3 : 0 ≤ -Real.log (1 - (p : ℝ) ^ (-(1 - c))) :=
    neg_log_one_sub_nonneg hx3pos.le hx3lt
  have hlead : -Real.log (1 - (p : ℝ) ^ (2 * c - 1)) ≤
      (1 - sewingAbscissaMass c)⁻¹ * (p : ℝ) ^ (2 * c - 1) :=
    neg_log_one_sub_le_of_le hx1pos.le hx1le hq
  have htrail : -Real.log (1 - (p : ℝ) ^ (-(1 + c))) ≤ 2 * (p : ℝ) ^ (2 * c - 1) := by
    have h1 := neg_log_one_sub_le_of_le hx4pos.le hx4half (by norm_num : (1 : ℝ) / 2 < 1)
    have h2 : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
    rw [h2] at h1
    have h4 : (p : ℝ) ^ (-(1 + c)) ≤ (p : ℝ) ^ (2 * c - 1) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    linarith
  have hexpand : sewingGrowthConst c * (p : ℝ) ^ (2 * c - 1) =
      (1 - sewingAbscissaMass c)⁻¹ * (p : ℝ) ^ (2 * c - 1) + 4 * (p : ℝ) ^ (2 * c - 1) := by
    rw [sewingGrowthConst]
    ring
  rw [localSewingLog, h3, hexpand]
  linarith

/-! ## The lower bound -/

private theorem localSewingLog_ge_firstPower {p : ℕ} (hp : p.Prime) {c : ℝ} (hc0 : 0 < c)
    (hc : c < 1 / 2) :
    (p : ℝ) ^ (-(1 : ℝ)) *
        ((p : ℝ) ^ (2 * c) - (p : ℝ) ^ (-(2 * c)) - 2 * (p : ℝ) ^ c + 2 * (p : ℝ) ^ (-c))
      ≤ localSewingLog p c := by
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
  have h2c : (p : ℝ) ^ (2 * c) - (p : ℝ) ^ (-(2 * c))
      = 2 * Real.sinh (2 * c * Real.log (p : ℝ)) := rpow_sub_rpow_neg_eq_two_sinh hp _
  have h1c : (p : ℝ) ^ c - (p : ℝ) ^ (-c)
      = 2 * Real.sinh (c * Real.log (p : ℝ)) := rpow_sub_rpow_neg_eq_two_sinh hp _
  refine le_trans (le_of_eq ?_) hle
  have hcast0 : ((0 : ℕ) : ℝ) = 0 := by norm_num
  rw [hcast0]
  have harg1 : 2 * (c * (0 + 1) * Real.log (p : ℝ)) = 2 * c * Real.log (p : ℝ) := by ring
  have harg2 : c * (0 + 1) * Real.log (p : ℝ) = c * Real.log (p : ℝ) := by ring
  have hexp : -((0 : ℝ) + 1) = -(1 : ℝ) := by ring
  rw [harg1, harg2, hexp]
  linear_combination ((p : ℝ) ^ (-(1 : ℝ))) * h2c - (2 * (p : ℝ) ^ (-(1 : ℝ))) * h1c

/-- **The local sewing logarithm dominates `(1/2) p^(2c-1)` above the activation threshold.** -/
theorem localSewingLog_ge {p : ℕ} (hp : p.Prime) {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2)
    (hact : (6 : ℝ) ≤ (p : ℝ) ^ c) :
    (1 / 2) * (p : ℝ) ^ (2 * c - 1) ≤ localSewingLog p c := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  set w : ℝ := (p : ℝ) ^ c with hw
  have hw6 : (6 : ℝ) ≤ w := hact
  have hwpos : (0 : ℝ) < w := by linarith
  have hsq : (p : ℝ) ^ (2 * c) = w * w := by
    rw [hw, ← Real.rpow_add hp0]
    congr 1
    ring
  have hinvsq : (p : ℝ) ^ (-(2 * c)) = (w * w)⁻¹ := by
    rw [Real.rpow_neg hp0.le, hsq]
  have hinv : (p : ℝ) ^ (-c) = w⁻¹ := by
    rw [Real.rpow_neg hp0.le]
  have hshift : (p : ℝ) ^ (2 * c - 1) = (p : ℝ) ^ (-(1 : ℝ)) * (w * w) := by
    rw [← hsq, ← Real.rpow_add hp0]
    congr 1
    ring
  have hmass : (0 : ℝ) < (p : ℝ) ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos hp0 _
  refine le_trans ?_ (localSewingLog_ge_firstPower hp hc0 hc)
  rw [hshift, hsq, hinvsq, hinv]
  have hkey : (1 / 2) * (w * w) ≤ w * w - (w * w)⁻¹ - 2 * w + 2 * w⁻¹ := by
    have hinvle : (w * w)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      nlinarith
    have hinvnn : (0 : ℝ) ≤ w⁻¹ := by positivity
    nlinarith
  nlinarith

end

end RHTower
