import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateOddProfileCoordinates

/-!
# No odd profile is a folded supersolution near the origin

Let `ω` be odd, continuous, nonnegative on `[0, ∞)` with `ω(log 2) > 0`, Lipschitz on `[−1, 1]`, and
let its test coordinate `g = Φ ω` be dominated on the half line by a shifted kernel,
`g(y) ≤ C Φ(y − b)`. Then `ω` is a strict folded subsolution on a right neighbourhood of `0`.

The mechanism is profile independent. Write the folded generator at `x` as the archimedean integral,
the prime `2` term and the remaining prime terms. Since `ω(0) = 0`:

* the prime `2` term tends to `−2 Λ(2) 2^{−1/2} Φ(0) Φ(log 2) ω(log 2) < 0`;
* for `t ≤ x` the shift integrand is `O(t)` by the Lipschitz bound, for `t > x` it is at most
  `Φ(x) ω(x) (Φ(x+t) + Φ(t−x))` because the terms `−Φ(x±t) ω(·)` are nonpositive; against the Lévy
  density this gives an archimedean contribution at most `K √x`;
* the remaining prime terms are at most `Φ(x) ω(x) · primeKernelSum x`, and `primeKernelSum` is
  bounded near `0` by the theta harmonic identity;
* the potential `Φ(x) cosh(x/2) ω(x)` is nonnegative.

All of these except the prime `2` term vanish as `x → 0⁺`. This settles the folded supersolution
question at the origin for every signed superposition of shifted ground states that is positive on
the half line, not only for nonnegative ones.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.ThetaSourceWard

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)]
  have h := Real.exp_one_lt_d9
  have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (1 / 2 : ℝ)]

theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
  have h := Real.exp_one_lt_d9
  norm_num at h ⊢
  linarith

/-! ### Pointwise bounds on the folded shift integrand -/

/-- Short shifts: the shift integrand is `O(t)` by the Lipschitz bound. -/
theorem foldedShiftGenerator_le_lipschitz {ω : ℝ → ℝ} {L : ℝ}
    (hL : ∀ y ∈ Icc (-1 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1, |ω z - ω y| ≤ L * |z - y|)
    {t x : ℝ} (ht0 : 0 < t) (htx : t ≤ x) (hx : x ≤ 1 / 2) :
    foldedShiftGenerator ω t x ≤ 2 * riemannKernelReal 0 ^ 2 * L * t := by
  unfold foldedShiftGenerator
  have hx0 : 0 < x := lt_of_lt_of_le ht0 htx
  have hmem : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hmem1 : x + t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hmem2 : x - t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h1 := hL (x + t) hmem1 x hmem
  have h2 := hL (x - t) hmem2 x hmem
  rw [show x - (x + t) = -t by ring, abs_neg, abs_of_pos ht0] at h1
  rw [show x - (x - t) = t by ring, abs_of_pos ht0] at h2
  rw [abs_of_nonneg (by linarith : 0 ≤ x - t)]
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hLt : 0 ≤ L * t := le_trans (abs_nonneg _) h1
  have e1 : ω x - ω (x + t) ≤ L * t := (abs_le.mp h1).2
  have e2 : ω x - ω (x - t) ≤ L * t := (abs_le.mp h2).2
  have p1 := (riemannKernelReal_pos (x + t)).le
  have p2 := (riemannKernelReal_pos (x - t)).le
  have px := (riemannKernelReal_pos x).le
  have q1 := riemannKernelReal_le_zero_point (x + t)
  have q2 := riemannKernelReal_le_zero_point (x - t)
  have qx := riemannKernelReal_le_zero_point x
  calc riemannKernelReal x * (riemannKernelReal (x + t) * (ω x - ω (x + t)) +
        riemannKernelReal (x - t) * (ω x - ω (x - t)))
      ≤ riemannKernelReal x * (riemannKernelReal (x + t) * (L * t) +
          riemannKernelReal (x - t) * (L * t)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left e1 p1) (mul_le_mul_of_nonneg_left e2 p2)) px
    _ ≤ riemannKernelReal 0 * (riemannKernelReal 0 * (L * t) + riemannKernelReal 0 * (L * t)) :=
        mul_le_mul qx
          (add_le_add (mul_le_mul_of_nonneg_right q1 hLt) (mul_le_mul_of_nonneg_right q2 hLt))
          (add_nonneg (mul_nonneg p1 hLt) (mul_nonneg p2 hLt)) hΘ0
    _ = 2 * riemannKernelReal 0 ^ 2 * L * t := by ring

/-- Long shifts: dropping the nonpositive terms `−Φ(x±t) ω(·)`. -/
theorem foldedShiftGenerator_le_of_lt {ω : ℝ → ℝ} (hnn : ∀ y, 0 ≤ y → 0 ≤ ω y) {t x : ℝ}
    (hx0 : 0 ≤ x) (hxt : x < t) :
    foldedShiftGenerator ω t x ≤
      riemannKernelReal x * ω x * (riemannKernelReal (x + t) + riemannKernelReal (t - x)) := by
  unfold foldedShiftGenerator
  rw [show x - t = -(t - x) by ring, riemannKernelReal_neg', abs_neg,
    abs_of_pos (by linarith : 0 < t - x)]
  have h1 := mul_nonneg (riemannKernelReal_pos (x + t)).le (hnn (x + t) (by linarith))
  have h2 := mul_nonneg (riemannKernelReal_pos (t - x)).le (hnn (t - x) (by linarith))
  have px := (riemannKernelReal_pos x).le
  have := mul_nonneg px (add_nonneg h1 h2)
  linarith

theorem foldedShiftGenerator_le_of_lt' {ω : ℝ → ℝ} (hnn : ∀ y, 0 ≤ y → 0 ≤ ω y) {t x : ℝ}
    (hx0 : 0 ≤ x) (hxt : x < t) :
    foldedShiftGenerator ω t x ≤ 2 * riemannKernelReal 0 ^ 2 * ω x := by
  refine (foldedShiftGenerator_le_of_lt hnn hx0 hxt).trans ?_
  have hω := hnn x hx0
  have hΘ0 := (riemannKernelReal_pos 0).le
  have q1 := riemannKernelReal_le_zero_point (x + t)
  have q2 := riemannKernelReal_le_zero_point (t - x)
  have qx := riemannKernelReal_le_zero_point x
  have px := (riemannKernelReal_pos x).le
  calc riemannKernelReal x * ω x * (riemannKernelReal (x + t) + riemannKernelReal (t - x))
      ≤ riemannKernelReal 0 * ω x * (riemannKernelReal 0 + riemannKernelReal 0) :=
        mul_le_mul (mul_le_mul_of_nonneg_right qx hω) (add_le_add q1 q2)
          (add_nonneg (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le)
          (mul_nonneg hΘ0 hω)
    _ = 2 * riemannKernelReal 0 ^ 2 * ω x := by ring

/-! ### The archimedean majorant -/

/-- `t^{−1/2}` on `(0, 1]`, `e^{−t/2}` beyond. -/
def originMajorant (t : ℝ) : ℝ := if t ≤ 1 then (Real.sqrt t)⁻¹ else Real.exp (-t / 2)

theorem originMajorant_nonneg (t : ℝ) : 0 ≤ originMajorant t := by
  unfold originMajorant
  split_ifs
  · exact inv_nonneg.mpr (Real.sqrt_nonneg t)
  · exact (Real.exp_pos _).le

theorem integrableOn_originMajorant : IntegrableOn originMajorant (Ioi 0) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  have h1' : IntegrableOn originMajorant (Ioc 0 1) := by
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioc
    show t ^ (-(1 / 2 : ℝ)) = originMajorant t
    unfold originMajorant
    rw [if_pos ht.2, Real.rpow_neg ht.1.le, ← Real.sqrt_eq_rpow]
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2) * t)) (Ioi 1) :=
    exp_neg_integrableOn_Ioi 1 (by norm_num)
  have h2' : IntegrableOn originMajorant (Ioi 1) := by
    refine h2.congr_fun (fun t ht => ?_) measurableSet_Ioi
    show Real.exp (-(1 / 2) * t) = originMajorant t
    unfold originMajorant
    rw [if_neg (not_le.mpr (mem_Ioi.mp ht)), show -(1 / 2 : ℝ) * t = -t / 2 by ring]
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact h1'.union h2'

/-- The archimedean integrand is dominated by `3Φ(0)² L √x · originMajorant`. -/
theorem archLevy_mul_foldedShiftGenerator_le {ω : ℝ → ℝ} {L : ℝ}
    (hL : ∀ y ∈ Icc (-1 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1, |ω z - ω y| ≤ L * |z - y|)
    (hnn : ∀ y, 0 ≤ y → 0 ≤ ω y) {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) (hωx : ω x ≤ L * x)
    {t : ℝ} (ht : 0 < t) :
    archLevyDensity t * foldedShiftGenerator ω t x ≤
      3 * riemannKernelReal 0 ^ 2 * L * Real.sqrt x * originMajorant t := by
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hL0 : 0 ≤ L := by
    have h := hL 0 ⟨by norm_num, by norm_num⟩ 1 ⟨by norm_num, by norm_num⟩
    rw [sub_zero, abs_one, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hLev := archLevyDensity_pos ht
  have hsx := Real.sqrt_pos.mpr hx0
  have hst := Real.sqrt_pos.mpr ht
  unfold originMajorant
  rcases le_or_gt t x with htx | htx
  · -- short shifts
    have ht1 : t ≤ 1 := by linarith
    rw [if_pos ht1]
    have hf := foldedShiftGenerator_le_lipschitz hL ht htx hx
    have hLe := archLevyDensity_le_of_le_one ht ht1
    have hb : 0 ≤ 2 * riemannKernelReal 0 ^ 2 * L * t := by positivity
    have hsq : Real.sqrt t ≤ Real.sqrt x := Real.sqrt_le_sqrt htx
    have hone : 1 ≤ Real.sqrt x * (Real.sqrt t)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hst, one_mul]
      exact hsq
    calc archLevyDensity t * foldedShiftGenerator ω t x
        ≤ archLevyDensity t * (2 * riemannKernelReal 0 ^ 2 * L * t) :=
          mul_le_mul_of_nonneg_left hf hLev.le
      _ ≤ 3 / 2 / t * (2 * riemannKernelReal 0 ^ 2 * L * t) := mul_le_mul_of_nonneg_right hLe hb
      _ = 3 * riemannKernelReal 0 ^ 2 * L := by field_simp
      _ = 3 * riemannKernelReal 0 ^ 2 * L * 1 := (mul_one _).symm
      _ ≤ 3 * riemannKernelReal 0 ^ 2 * L * (Real.sqrt x * (Real.sqrt t)⁻¹) :=
          mul_le_mul_of_nonneg_left hone (by positivity)
      _ = _ := by ring
  · have hf := foldedShiftGenerator_le_of_lt' hnn hx0.le htx
    have hf' : foldedShiftGenerator ω t x ≤ 2 * riemannKernelReal 0 ^ 2 * (L * x) :=
      hf.trans (mul_le_mul_of_nonneg_left hωx (by positivity))
    have hb : 0 ≤ 2 * riemannKernelReal 0 ^ 2 * (L * x) := by positivity
    rcases le_or_gt t 1 with ht1 | ht1
    · rw [if_pos ht1]
      have hLe := archLevyDensity_le_of_le_one ht ht1
      have hsq : Real.sqrt x ≤ Real.sqrt t := Real.sqrt_le_sqrt htx.le
      have hdiv : x / t ≤ Real.sqrt x * (Real.sqrt t)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ ht hst]
        have e1 : Real.sqrt t * Real.sqrt x ^ 2 = Real.sqrt t * x := by rw [Real.sq_sqrt hx0.le]
        have e2 : Real.sqrt x * Real.sqrt t ^ 2 = Real.sqrt x * t := by rw [Real.sq_sqrt ht.le]
        have h := mul_nonneg (mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg t))
          (sub_nonneg.mpr hsq)
        nlinarith [h, e1, e2]
      calc archLevyDensity t * foldedShiftGenerator ω t x
          ≤ archLevyDensity t * (2 * riemannKernelReal 0 ^ 2 * (L * x)) :=
            mul_le_mul_of_nonneg_left hf' hLev.le
        _ ≤ 3 / 2 / t * (2 * riemannKernelReal 0 ^ 2 * (L * x)) :=
            mul_le_mul_of_nonneg_right hLe hb
        _ = 3 * riemannKernelReal 0 ^ 2 * L * (x / t) := by field_simp
        _ ≤ 3 * riemannKernelReal 0 ^ 2 * L * (Real.sqrt x * (Real.sqrt t)⁻¹) :=
            mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = _ := by ring
    · rw [if_neg (not_le.mpr ht1)]
      have hLe := archLevyDensity_le_of_one_le ht1.le
      have hxs : x ≤ Real.sqrt x := by
        rw [Real.le_sqrt hx0.le hx0.le]
        nlinarith
      have hE := (Real.exp_pos (-t / 2)).le
      calc archLevyDensity t * foldedShiftGenerator ω t x
          ≤ archLevyDensity t * (2 * riemannKernelReal 0 ^ 2 * (L * x)) :=
            mul_le_mul_of_nonneg_left hf' hLev.le
        _ ≤ 3 / 2 * Real.exp (-t / 2) * (2 * riemannKernelReal 0 ^ 2 * (L * x)) :=
            mul_le_mul_of_nonneg_right hLe hb
        _ = 3 * riemannKernelReal 0 ^ 2 * L * x * Real.exp (-t / 2) := by ring
        _ ≤ 3 * riemannKernelReal 0 ^ 2 * L * Real.sqrt x * Real.exp (-t / 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxs (by positivity)) hE

/-- The archimedean part of the folded generator is at most `K √x` near the origin. -/
theorem integral_archLevy_foldedShiftGenerator_le_sqrt {ω : ℝ → ℝ} {L : ℝ}
    (hL : ∀ y ∈ Icc (-1 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1, |ω z - ω y| ≤ L * |z - y|)
    (hnn : ∀ y, 0 ≤ y → 0 ≤ ω y) {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) (hωx : ω x ≤ L * x) :
    (∫ t in Ioi (0 : ℝ), archLevyDensity t * foldedShiftGenerator ω t x) ≤
      3 * riemannKernelReal 0 ^ 2 * L * Real.sqrt x * ∫ t in Ioi (0 : ℝ), originMajorant t := by
  have hL0 : 0 ≤ L := by
    have h := hL 0 ⟨by norm_num, by norm_num⟩ 1 ⟨by norm_num, by norm_num⟩
    rw [sub_zero, abs_one, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hK : 0 ≤ 3 * riemannKernelReal 0 ^ 2 * L * Real.sqrt x := by positivity
  have hmaj : IntegrableOn (fun t => 3 * riemannKernelReal 0 ^ 2 * L * Real.sqrt x * originMajorant t)
      (Ioi 0) := integrableOn_originMajorant.const_mul _
  rw [← integral_const_mul]
  by_cases hint : IntegrableOn (fun t => archLevyDensity t * foldedShiftGenerator ω t x) (Ioi 0)
  · exact setIntegral_mono_on hint hmaj measurableSet_Ioi fun t ht =>
      archLevy_mul_foldedShiftGenerator_le hL hnn hx0 hx hωx (mem_Ioi.mp ht)
  · rw [integral_undef hint]
    exact setIntegral_nonneg measurableSet_Ioi fun t _ => mul_nonneg hK (originMajorant_nonneg t)

/-! ### The prime part -/

/-- Summability of the prime series of the folded generator for dominated profiles. -/
theorem summable_atom_foldedShiftGenerator_of_dominated {ω : ℝ → ℝ} {C b : ℝ} (hC : 0 ≤ C)
    (hnn : ∀ y, 0 ≤ y → 0 ≤ ω y)
    (hdom : ∀ y, 0 ≤ y → riemannKernelReal y * ω y ≤ C * riemannKernelReal (y - b))
    {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    Summable fun n : ℕ => vonMangoldtAtom n * foldedShiftGenerator ω (Real.log n) x := by
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hωx := hnn x hx0.le
  have hS1 := (summable_primeKernelSum x).mul_left (riemannKernelReal 0 * ω x)
  have hS2 := ((summable_primeShift_right (x - b)).add (summable_primeShift_left (x + b))).mul_left
    (riemannKernelReal 0 * C)
  refine (hS1.add hS2).of_norm_bounded fun n => ?_
  have hΛ := vonMangoldtAtom_nonneg n
  rcases lt_or_ge n 2 with hn | hn
  · rw [vonMangoldtAtom_eq_zero_of_lt_two hn]
    simp
  · have hlog : x < Real.log n := by
      have h2 : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      linarith [half_lt_log_two]
    set t := Real.log n with ht
    have hg1 : 0 ≤ riemannKernelReal (x + t) * ω (x + t) :=
      mul_nonneg (riemannKernelReal_pos _).le (hnn _ (by linarith))
    have hg2 : 0 ≤ riemannKernelReal (t - x) * ω (t - x) :=
      mul_nonneg (riemannKernelReal_pos _).le (hnn _ (by linarith))
    have hd1 := hdom (x + t) (by linarith)
    have hd2 := hdom (t - x) (by linarith)
    have hfsg : |foldedShiftGenerator ω t x| ≤ riemannKernelReal 0 * ω x *
        (riemannKernelReal (x + t) + riemannKernelReal (t - x)) +
        riemannKernelReal 0 * C * (riemannKernelReal (x - b + t) + riemannKernelReal (x + b - t)) := by
      unfold foldedShiftGenerator
      rw [show x - t = -(t - x) by ring, riemannKernelReal_neg', abs_neg,
        abs_of_pos (by linarith : 0 < t - x)]
      have px := (riemannKernelReal_pos x).le
      have qx := riemannKernelReal_le_zero_point x
      have e1 : riemannKernelReal (x + t - b) = riemannKernelReal (x - b + t) := by ring_nf
      have e2 : riemannKernelReal (t - x - b) = riemannKernelReal (x + b - t) := by
        rw [show t - x - b = -(x + b - t) by ring, riemannKernelReal_neg']
      rw [e1] at hd1
      rw [e2] at hd2
      have hA : riemannKernelReal x * (riemannKernelReal (x + t) * (ω x - ω (x + t)) +
          riemannKernelReal (t - x) * (ω x - ω (t - x))) =
          riemannKernelReal x * ω x * (riemannKernelReal (x + t) + riemannKernelReal (t - x)) -
          riemannKernelReal x * (riemannKernelReal (x + t) * ω (x + t) +
            riemannKernelReal (t - x) * ω (t - x)) := by ring
      rw [hA, abs_le]
      have hsum : riemannKernelReal x * (riemannKernelReal (x + t) * ω (x + t) +
          riemannKernelReal (t - x) * ω (t - x)) ≤
          riemannKernelReal 0 * C * (riemannKernelReal (x - b + t) + riemannKernelReal (x + b - t)) := by
        calc riemannKernelReal x * (riemannKernelReal (x + t) * ω (x + t) +
              riemannKernelReal (t - x) * ω (t - x))
            ≤ riemannKernelReal 0 * (C * riemannKernelReal (x - b + t) +
                C * riemannKernelReal (x + b - t)) :=
              mul_le_mul qx (add_le_add hd1 hd2) (add_nonneg hg1 hg2) hΘ0
          _ = _ := by ring
      have hpos1 : 0 ≤ riemannKernelReal x * ω x *
          (riemannKernelReal (x + t) + riemannKernelReal (t - x)) :=
        mul_nonneg (mul_nonneg px hωx)
          (add_nonneg (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le)
      have hpos2 : 0 ≤ riemannKernelReal x * (riemannKernelReal (x + t) * ω (x + t) +
          riemannKernelReal (t - x) * ω (t - x)) := mul_nonneg px (add_nonneg hg1 hg2)
      have hup : riemannKernelReal x * ω x *
          (riemannKernelReal (x + t) + riemannKernelReal (t - x)) ≤
          riemannKernelReal 0 * ω x * (riemannKernelReal (x + t) + riemannKernelReal (t - x)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right qx hωx)
          (add_nonneg (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le)
      have hC0 : 0 ≤ riemannKernelReal 0 * C *
          (riemannKernelReal (x - b + t) + riemannKernelReal (x + b - t)) :=
        mul_nonneg (mul_nonneg hΘ0 hC)
          (add_nonneg (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le)
      constructor <;> linarith
    have e3 : riemannKernelReal (t - x) = riemannKernelReal (x - t) := by
      rw [show t - x = -(x - t) by ring, riemannKernelReal_neg']
    rw [e3] at hfsg
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hΛ]
    calc vonMangoldtAtom n * |foldedShiftGenerator ω t x|
        ≤ vonMangoldtAtom n * (riemannKernelReal 0 * ω x *
            (riemannKernelReal (x + t) + riemannKernelReal (x - t)) +
          riemannKernelReal 0 * C *
            (riemannKernelReal (x - b + t) + riemannKernelReal (x + b - t))) :=
          mul_le_mul_of_nonneg_left hfsg hΛ
      _ = _ := by ring

/-- The prime part of the folded generator is the prime `2` term plus at most
`Φ(x) ω(x) · primeKernelSum x`. -/
theorem tsum_atom_foldedShiftGenerator_le {ω : ℝ → ℝ} (hnn : ∀ y, 0 ≤ y → 0 ≤ ω y) {x : ℝ}
    (hx0 : 0 < x) (hx : x ≤ 1 / 2)
    (hs : Summable fun n : ℕ => vonMangoldtAtom n * foldedShiftGenerator ω (Real.log n) x) :
    (∑' n : ℕ, vonMangoldtAtom n * foldedShiftGenerator ω (Real.log n) x) ≤
      vonMangoldtAtom 2 * foldedShiftGenerator ω (Real.log 2) x +
        riemannKernelReal x * ω x * primeKernelSum x := by
  rw [hs.tsum_eq_add_tsum_ite 2]
  refine add_le_add le_rfl ?_
  unfold primeKernelSum
  rw [← tsum_mul_left]
  have hωx := hnn x hx0.le
  have px := (riemannKernelReal_pos x).le
  refine Summable.tsum_le_tsum (fun n => ?_) ?_ ((summable_primeKernelSum x).mul_left _)
  · split_ifs with h2
    · exact mul_nonneg (mul_nonneg px hωx) (mul_nonneg (vonMangoldtAtom_nonneg n)
        (add_nonneg (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le))
    · rcases lt_or_ge n 2 with hn | hn
      · rw [vonMangoldtAtom_eq_zero_of_lt_two hn]
        simp
      · have hn3 : 3 ≤ n := by omega
        have hlog : x < Real.log n := by
          have h3 : Real.log 3 ≤ Real.log n :=
            Real.log_le_log (by norm_num) (by exact_mod_cast hn3)
          linarith [one_lt_log_three]
        have hf := foldedShiftGenerator_le_of_lt hnn hx0.le hlog
        rw [show Real.log n - x = -(x - Real.log n) by ring, riemannKernelReal_neg'] at hf
        calc vonMangoldtAtom n * foldedShiftGenerator ω (Real.log n) x
            ≤ vonMangoldtAtom n * (riemannKernelReal x * ω x *
                (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n))) :=
              mul_le_mul_of_nonneg_left hf (vonMangoldtAtom_nonneg n)
          _ = _ := by ring
  · have := hs.update 2 0
    refine this.congr fun n => ?_
    rw [Function.update_apply]

/-! ### The origin window -/

/-- `primeKernelSum` is bounded by `cosh(x/2) + 2|c|Φ(0) + 2 ∫ gammaSourceBound`. -/
theorem primeKernelSum_le (x : ℝ) :
    primeKernelSum x ≤ Real.cosh (x / 2) + 2 * |archConstantReal| * riemannKernelReal 0 +
      2 * gammaSourceBoundMass := by
  rw [theta_harmonic_identity]
  have h1 := (abs_le.mp (abs_integral_symArchTerm_le x)).2
  have h2 : -(2 * archConstantReal * riemannKernelReal x) ≤
      2 * |archConstantReal| * riemannKernelReal 0 := by
    have hx := riemannKernelReal_pos x
    have hx' := riemannKernelReal_le_zero_point x
    have := neg_abs_le archConstantReal
    have := le_abs_self archConstantReal
    nlinarith [abs_nonneg archConstantReal]
  linarith

/-- **Origin failure for every dominated odd profile.** If `ω` is odd, continuous, nonnegative on
`[0, ∞)` with `ω(log 2) > 0`, Lipschitz on `[−1, 1]`, and `Φ ω ≤ C Φ(· − b)` on `[0, ∞)`, then `ω`
is a strict folded subsolution on a right neighbourhood of `0`. -/
theorem exists_origin_window_foldedGenerator_lt_potential_of_profile {ω : ℝ → ℝ} {L C b : ℝ}
    (hc : Continuous ω) (hodd : ∀ x, ω (-x) = -ω x) (hnn : ∀ y, 0 ≤ y → 0 ≤ ω y)
    (hω2 : 0 < ω (Real.log 2))
    (hL : ∀ y ∈ Icc (-1 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1, |ω z - ω y| ≤ L * |z - y|) (hC : 0 ≤ C)
    (hdom : ∀ y, 0 ≤ y → riemannKernelReal y * ω y ≤ C * riemannKernelReal (y - b)) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x, 0 < x → x < x₀ →
      foldedGenerator ω x < riemannKernelReal x * Real.cosh (x / 2) * ω x := by
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hL0 : 0 ≤ L := by
    have h := hL 0 ⟨by norm_num, by norm_num⟩ 1 ⟨by norm_num, by norm_num⟩
    rw [sub_zero, abs_one, mul_one] at h
    exact le_trans (abs_nonneg _) h
  have hω0 : ω 0 = 0 := odd_apply_zero hodd
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 3 * riemannKernelReal 0 ^ 2 * L *
      ∫ t in Ioi (0 : ℝ), originMajorant t := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * |archConstantReal| * riemannKernelReal 0 +
      2 * gammaSourceBoundMass := ⟨_, rfl⟩
  -- the comparison function
  set F : ℝ → ℝ := fun x => vonMangoldtAtom 2 * foldedShiftGenerator ω (Real.log 2) x +
    K * Real.sqrt x + riemannKernelReal 0 * (L * x) * (Real.cosh (x / 2) + B) with hF
  have hFc : Continuous F := by
    refine ((continuous_const.mul (continuous_foldedShiftGenerator hc _)).add
      (continuous_const.mul Real.continuous_sqrt)).add
      ((continuous_const.mul (continuous_const.mul continuous_id)).mul
        ((Real.continuous_cosh.comp (continuous_id.div_const 2)).add continuous_const))
  have hF0 : F 0 < 0 := by
    simp only [hF, Real.sqrt_zero, mul_zero, zero_mul, add_zero]
    unfold foldedShiftGenerator
    rw [zero_add, zero_sub, abs_neg, abs_of_pos (Real.log_pos one_lt_two), riemannKernelReal_neg',
      hω0, zero_sub]
    have := vonMangoldtAtom_two_pos
    have := riemannKernelReal_pos 0
    have := riemannKernelReal_pos (Real.log 2)
    have h : riemannKernelReal (Real.log 2) * -ω (Real.log 2) +
        riemannKernelReal (Real.log 2) * -ω (Real.log 2) =
        -(2 * riemannKernelReal (Real.log 2) * ω (Real.log 2)) := by ring
    rw [h]
    have hP : 0 < 2 * riemannKernelReal (Real.log 2) * ω (Real.log 2) := by positivity
    have := mul_pos (mul_pos vonMangoldtAtom_two_pos (riemannKernelReal_pos 0)) hP
    linarith
  have hev := ContinuousAt.eventually_lt hFc.continuousAt continuousAt_const hF0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min ε (1 / 2), lt_min hε (by norm_num), fun x hx hxε => ?_⟩
  have hx12 : x ≤ 1 / 2 := le_trans hxε.le (min_le_right _ _)
  have hxε' : x < ε := lt_of_lt_of_le hxε (min_le_left _ _)
  have hFx : F x < 0 := hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hx]; exact hxε')
  have hωx : ω x ≤ L * x := by
    have h := hL 0 ⟨by norm_num, by norm_num⟩ x ⟨by linarith, by linarith⟩
    rw [hω0, sub_zero, sub_zero, abs_of_pos hx] at h
    exact (abs_le.mp h).2
  have hA := integral_archLevy_foldedShiftGenerator_le_sqrt hL hnn hx hx12 hωx
  have hs := summable_atom_foldedShiftGenerator_of_dominated hC hnn hdom hx hx12
  have hP := tsum_atom_foldedShiftGenerator_le hnn hx hx12 hs
  have hpks := primeKernelSum_le x
  have hpot : 0 ≤ riemannKernelReal x * Real.cosh (x / 2) * ω x :=
    mul_nonneg (mul_nonneg (riemannKernelReal_pos x).le (Real.cosh_pos _).le) (hnn x hx.le)
  have hΘω : riemannKernelReal x * ω x * primeKernelSum x ≤
      riemannKernelReal 0 * (L * x) * (Real.cosh (x / 2) + B) := by
    have h1 : riemannKernelReal x * ω x ≤ riemannKernelReal 0 * (L * x) :=
      mul_le_mul (riemannKernelReal_le_zero_point x) hωx (hnn x hx.le) hΘ0
    have h2 : 0 ≤ riemannKernelReal x * ω x :=
      mul_nonneg (riemannKernelReal_pos x).le (hnn x hx.le)
    rw [hB]
    have hpks' : primeKernelSum x ≤ Real.cosh (x / 2) +
        (2 * |archConstantReal| * riemannKernelReal 0 + 2 * gammaSourceBoundMass) := by
      linarith
    rcases le_or_gt 0 (primeKernelSum x) with hp | hp
    · exact mul_le_mul h1 hpks' hp (by positivity)
    · have : riemannKernelReal x * ω x * primeKernelSum x ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos h2 hp.le
      have hpos : 0 ≤ riemannKernelReal 0 * (L * x) * (Real.cosh (x / 2) +
          (2 * |archConstantReal| * riemannKernelReal 0 + 2 * gammaSourceBoundMass)) := by
        have := (Real.cosh_pos (x / 2)).le
        have hG : 0 ≤ gammaSourceBoundMass :=
          setIntegral_nonneg measurableSet_Ioi fun u hu => by
            have := abs_gammaSourceTerm_le_bound 0 (mem_Ioi.mp hu)
            exact le_trans (abs_nonneg _) this
        positivity
      linarith
  unfold foldedGenerator
  have hFx' : vonMangoldtAtom 2 * foldedShiftGenerator ω (Real.log 2) x + K * Real.sqrt x +
      riemannKernelReal 0 * (L * x) * (Real.cosh (x / 2) + B) < 0 := hFx
  rw [hK] at hFx'
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
