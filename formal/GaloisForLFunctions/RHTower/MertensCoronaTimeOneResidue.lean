import GaloisForLFunctions.RHTower.MertensCoronaShiftConormal
import GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona

/-!
# The time-one boundary residue and the factorial transgression of the Mertens conormal

The time-one Gamma--Meixner weight `w_1(p) = cosh(2 log p)^{-1/2}` has the exact factorization
`w_1(p) = √2 · p^{-1} · (1+p^{-4})^{-1/2}`, so the prime--Laplace source

```text
M_{1,b}(s) = ∑_p w_1(p) (log p) b_p p^{-s}
```

differs from the Gamma-shape Abel functional `L_s(b)` only by two weight factors, each within
`p^{-4}`, respectively `2^{s/2}-1`, of one.  Both errors vanish after multiplication by `s`, so

```text
lim_{s ↓ 0} s · M_{1,b}(s) = √2 · q_M(b)          (equation (15)).
```

The polar germ `r_c(z) = √2 c / z` has raw derivatives `r_c^{(N)}(x₀) = √2 c (−1)^N N!/x₀^{N+1}`,
and the corpus Gamma adjacent-clock curvature is the rank-one outer product of the highest raw
derivative with the factorial-tail boundary vector — equations (18)--(19), with the nonvanishing
(21).
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The `(1 + n^{-4})^{-1/2}` correction of the time-one Gamma--Meixner weight. -/
def timeOneCorrection (n : ℕ) : ℝ := (1 + ((n : ℝ)) ^ (-(4 : ℝ))) ^ (-(1 / 2) : ℝ)

/-- The `2^{s/2}(1+n^{-4})^{-s/2}` shape factor of the Abel family. -/
def abelShapeFactor (s : ℝ) (n : ℕ) : ℝ :=
  2 ^ (s / 2) * (1 + ((n : ℝ)) ^ (-(4 : ℝ))) ^ (-s / 2)

/-- The common Abel-weighted coefficient. -/
def abelWeighted (b : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  mertensPrimeWeight n * b n * ((n : ℝ)) ^ (-s)

theorem timeOneCorrection_pos (n : ℕ) : 0 < timeOneCorrection n := by
  rw [timeOneCorrection]
  have : (0 : ℝ) < 1 + ((n : ℝ)) ^ (-(4 : ℝ)) := by positivity
  exact Real.rpow_pos_of_pos this _

theorem timeOneCorrection_le_one (n : ℕ) : timeOneCorrection n ≤ 1 := by
  rw [timeOneCorrection]
  refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by norm_num)
  have : (0 : ℝ) ≤ ((n : ℝ)) ^ (-(4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  linarith

/-- The time-one correction differs from one by at most `n^{-4}`. -/
theorem abs_timeOneCorrection_sub_one_le (n : ℕ) :
    |timeOneCorrection n - 1| ≤ ((n : ℝ)) ^ (-(4 : ℝ)) := by
  have hx : (0 : ℝ) ≤ ((n : ℝ)) ^ (-(4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hbase : (1 : ℝ) ≤ 1 + ((n : ℝ)) ^ (-(4 : ℝ)) := by linarith
  have hpos : (0 : ℝ) < 1 + ((n : ℝ)) ^ (-(4 : ℝ)) := by linarith
  have hle : timeOneCorrection n ≤ 1 := timeOneCorrection_le_one n
  have hge : (1 + ((n : ℝ)) ^ (-(4 : ℝ)))⁻¹ ≤ timeOneCorrection n := by
    rw [timeOneCorrection]
    have hstep : (1 + ((n : ℝ)) ^ (-(4 : ℝ))) ^ (-(1 : ℝ))
        ≤ (1 + ((n : ℝ)) ^ (-(4 : ℝ))) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
    rwa [Real.rpow_neg_one] at hstep
  have hinv : (1 : ℝ) - ((n : ℝ)) ^ (-(4 : ℝ)) ≤ (1 + ((n : ℝ)) ^ (-(4 : ℝ)))⁻¹ := by
    have hprod : (1 - ((n : ℝ)) ^ (-(4 : ℝ))) * (1 + ((n : ℝ)) ^ (-(4 : ℝ))) ≤ 1 := by
      nlinarith [sq_nonneg (((n : ℝ)) ^ (-(4 : ℝ)))]
    have hinvpos : (0 : ℝ) ≤ (1 + ((n : ℝ)) ^ (-(4 : ℝ)))⁻¹ := by positivity
    calc (1 : ℝ) - ((n : ℝ)) ^ (-(4 : ℝ))
        = ((1 - ((n : ℝ)) ^ (-(4 : ℝ))) * (1 + ((n : ℝ)) ^ (-(4 : ℝ))))
            * (1 + ((n : ℝ)) ^ (-(4 : ℝ)))⁻¹ := by field_simp
      _ ≤ 1 * (1 + ((n : ℝ)) ^ (-(4 : ℝ)))⁻¹ :=
          mul_le_mul_of_nonneg_right hprod hinvpos
      _ = (1 + ((n : ℝ)) ^ (-(4 : ℝ)))⁻¹ := by ring
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- The Abel shape factor lies between `1` and `2^{s/2}` on every positive index. -/
theorem abs_abelShapeFactor_sub_one_le {s : ℝ} (hs : 0 < s) {n : ℕ} (hn : 1 ≤ n) :
    |abelShapeFactor s n - 1| ≤ 2 ^ (s / 2) - 1 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hx : (0 : ℝ) < ((n : ℝ)) ^ (-(4 : ℝ)) := Real.rpow_pos_of_pos hn0 _
  have hxle : ((n : ℝ)) ^ (-(4 : ℝ)) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hbase : (1 : ℝ) ≤ 1 + ((n : ℝ)) ^ (-(4 : ℝ)) := by linarith
  have hbase2 : (1 : ℝ) + ((n : ℝ)) ^ (-(4 : ℝ)) ≤ 2 := by linarith
  have h2pos : (0 : ℝ) < 2 ^ (s / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hupper : abelShapeFactor s n ≤ 2 ^ (s / 2) := by
    rw [abelShapeFactor]
    have hone : (1 + ((n : ℝ)) ^ (-(4 : ℝ))) ^ (-s / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
    nlinarith [h2pos.le]
  have hlower : (1 : ℝ) ≤ abelShapeFactor s n := by
    rw [abelShapeFactor]
    have hmono : (2 : ℝ) ^ (-s / 2) ≤ (1 + ((n : ℝ)) ^ (-(4 : ℝ))) ^ (-s / 2) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hbase2 (by linarith)
    have hcancel : (2 : ℝ) ^ (s / 2) * (2 : ℝ) ^ (-s / 2) = 1 := by
      rw [← Real.rpow_add (by norm_num), show s / 2 + -s / 2 = (0 : ℝ) by ring]
      exact Real.rpow_zero 2
    nlinarith [h2pos.le, hmono, hcancel]
  rw [abs_of_nonneg (by linarith)]
  linarith


/-! ## The time-one prime--Laplace source and its boundary residue -/

/-- The time-one prime--Laplace source `M_{1,b}(s) = ∑_p w_1(p)(log p) b_p p^{-s}`,
equation (14). -/
def timeOnePrimeLaplace (b : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, meixnerShape 1 n * ((n : ℝ) * mertensPrimeWeight n) * b n * ((n : ℝ)) ^ (-s)

theorem abelWeighted_zero (b : ℕ → ℝ) (s : ℝ) : abelWeighted b s 0 = 0 := by
  simp [abelWeighted, mertensPrimeWeight]

theorem abs_abelWeighted (b : ℕ → ℝ) (s : ℝ) (n : ℕ) :
    |abelWeighted b s n| = primeLogAbsWeight b n * ((n : ℝ)) ^ (-s) := by
  have hw : 0 ≤ mertensPrimeWeight n := mertensPrimeWeight_nonneg n
  have hr : (0 : ℝ) ≤ ((n : ℝ)) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [abelWeighted, abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg hr, primeLogAbsWeight]

theorem timeOnePrimeLaplace_term (b : ℕ → ℝ) (s : ℝ) (n : ℕ) :
    meixnerShape 1 n * ((n : ℝ) * mertensPrimeWeight n) * b n * ((n : ℝ)) ^ (-s)
      = Real.sqrt 2 * (timeOneCorrection n * abelWeighted b s n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [mertensPrimeWeight, abelWeighted]
  · have hn1 : 1 ≤ n := hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [meixnerShape_factorization 1 hn1]
    have hinv : ((n : ℝ)) ^ (-(1 : ℝ)) * (n : ℝ) = 1 := by
      rw [Real.rpow_neg_one]
      exact inv_mul_cancel₀ (ne_of_gt hn0)
    have hsqrt : (2 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 2 := by
      rw [Real.sqrt_eq_rpow]
    have hexp : (-(1 : ℝ)) / 2 = -(1 / 2 : ℝ) := by ring
    rw [hexp, hsqrt, ← timeOneCorrection, abelWeighted]
    calc Real.sqrt 2 * ((n : ℝ)) ^ (-(1 : ℝ)) * timeOneCorrection n
          * ((n : ℝ) * mertensPrimeWeight n) * b n * ((n : ℝ)) ^ (-s)
        = Real.sqrt 2 * (timeOneCorrection n
            * (((n : ℝ)) ^ (-(1 : ℝ)) * (n : ℝ)) * mertensPrimeWeight n * b n
            * ((n : ℝ)) ^ (-s)) := by ring
      _ = Real.sqrt 2 * (timeOneCorrection n
            * (mertensPrimeWeight n * b n * ((n : ℝ)) ^ (-s))) := by
          rw [hinv]
          ring

theorem timeOnePrimeLaplace_eq (b : ℕ → ℝ) (s : ℝ) :
    timeOnePrimeLaplace b s
      = Real.sqrt 2 * ∑' n : ℕ, timeOneCorrection n * abelWeighted b s n := by
  rw [timeOnePrimeLaplace, ← tsum_mul_left]
  exact tsum_congr fun n => timeOnePrimeLaplace_term b s n

theorem gammaShapeAbelFunctional_eq_abelWeighted (s : ℝ) (b : ℕ → ℝ) :
    gammaShapeAbelFunctional s b = s * ∑' n : ℕ, abelShapeFactor s n * abelWeighted b s n := by
  rw [gammaShapeAbelFunctional]
  congr 1
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [mertensPrimeWeight, abelWeighted]
  · rw [meixnerShape_factorization s hn, abelShapeFactor, abelWeighted]
    ring


theorem summable_weight_abelWeighted {b : ℕ → ℝ} {C s : ℝ} (hs : 0 < s)
    (hC : ∀ X : ℕ, 2 ≤ X → marcinkiewiczLogQuotient b X ≤ C)
    {w : ℕ → ℝ} (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) :
    Summable (fun n : ℕ => w n * abelWeighted b s n) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_primeLogAbsWeight_rpow hs hC)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 n), abs_abelWeighted]
  have hnn : (0 : ℝ) ≤ primeLogAbsWeight b n * ((n : ℝ)) ^ (-s) :=
    mul_nonneg (primeLogAbsWeight_nonneg b n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  nlinarith [hw1 n, hnn]

theorem abelShapeFactor_nonneg (s : ℝ) (n : ℕ) : 0 ≤ abelShapeFactor s n := by
  rw [abelShapeFactor]
  have h1 : (0 : ℝ) < 2 ^ (s / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have h2 : (0 : ℝ) ≤ 1 + ((n : ℝ)) ^ (-(4 : ℝ)) := by positivity
  positivity

theorem abelShapeFactor_le_one_scaled {s : ℝ} (hs : 0 < s) (n : ℕ) :
    abelShapeFactor s n ≤ 2 ^ (s / 2) := by
  rw [abelShapeFactor]
  have hx : (0 : ℝ) ≤ ((n : ℝ)) ^ (-(4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hbase : (1 : ℝ) ≤ 1 + ((n : ℝ)) ^ (-(4 : ℝ)) := by linarith
  have hone : (1 + ((n : ℝ)) ^ (-(4 : ℝ))) ^ (-s / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  have h2pos : (0 : ℝ) < 2 ^ (s / 2) := Real.rpow_pos_of_pos (by norm_num) _
  nlinarith [h2pos.le]

/-- **Equation (15), the quantitative step.** -/
theorem abs_timeOne_sub_abel_le {b : ℕ → ℝ} {C s : ℝ} (hs : 0 < s)
    (hC : ∀ X : ℕ, 2 ≤ X → marcinkiewiczLogQuotient b X ≤ C) :
    |s * timeOnePrimeLaplace b s - Real.sqrt 2 * gammaShapeAbelFunctional s b|
      ≤ Real.sqrt 2 * (s * (∑' n : ℕ, primeLogAbsWeight b n * ((n : ℝ)) ^ (-(4 : ℝ)))
          + (2 ^ (s / 2) - 1) * (max C 0 * (1 + s))) := by
  have h2s : (1 : ℝ) ≤ 2 ^ (s / 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (show (0 : ℝ) ≤ s / 2 by linarith)
    rwa [Real.rpow_zero] at h
  have hcorr : Summable (fun n : ℕ => timeOneCorrection n * abelWeighted b s n) :=
    summable_weight_abelWeighted hs hC (fun n => (timeOneCorrection_pos n).le)
      timeOneCorrection_le_one
  have hshape : Summable (fun n : ℕ => abelShapeFactor s n * abelWeighted b s n) := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_primeLogAbsWeight_rpow hs hC).mul_left (2 ^ (s / 2)))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (abelShapeFactor_nonneg s n), abs_abelWeighted]
    have hnn : (0 : ℝ) ≤ primeLogAbsWeight b n * ((n : ℝ)) ^ (-s) :=
      mul_nonneg (primeLogAbsWeight_nonneg b n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    nlinarith [abelShapeFactor_le_one_scaled hs n, hnn]
  have hsplit : s * timeOnePrimeLaplace b s - Real.sqrt 2 * gammaShapeAbelFunctional s b
      = Real.sqrt 2 * (s * ∑' n : ℕ,
          (timeOneCorrection n * abelWeighted b s n - abelShapeFactor s n * abelWeighted b s n)) := by
    rw [timeOnePrimeLaplace_eq, gammaShapeAbelFunctional_eq_abelWeighted, hcorr.tsum_sub hshape]
    ring
  rw [hsplit, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hsqrt2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  refine mul_le_mul_of_nonneg_left ?_ hsqrt2
  -- bound the inner sum
  have hmaj1 : Summable (fun n : ℕ => primeLogAbsWeight b n * ((n : ℝ)) ^ (-(4 : ℝ))) :=
    summable_primeLogAbsWeight_rpow (by norm_num) hC
  have hmaj2 : Summable (fun n : ℕ =>
      (2 ^ (s / 2) - 1) * (primeLogAbsWeight b n * ((n : ℝ)) ^ (-s))) :=
    (summable_primeLogAbsWeight_rpow hs hC).mul_left _
  have hterm : ∀ n : ℕ,
      ‖timeOneCorrection n * abelWeighted b s n - abelShapeFactor s n * abelWeighted b s n‖
        ≤ primeLogAbsWeight b n * ((n : ℝ)) ^ (-(4 : ℝ))
          + (2 ^ (s / 2) - 1) * (primeLogAbsWeight b n * ((n : ℝ)) ^ (-s)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hz : abelWeighted b s 0 = 0 := abelWeighted_zero b s
      rw [hz]
      simp only [mul_zero, sub_zero, norm_zero]
      have h1 : (0 : ℝ) ≤ primeLogAbsWeight b 0 * ((0 : ℕ) : ℝ) ^ (-(4 : ℝ)) :=
        mul_nonneg (primeLogAbsWeight_nonneg b 0) (Real.rpow_nonneg (by norm_num) _)
      have h2 : (0 : ℝ) ≤ (2 ^ (s / 2) - 1) * (primeLogAbsWeight b 0 * ((0 : ℕ) : ℝ) ^ (-s)) := by
        have hnn : (0 : ℝ) ≤ primeLogAbsWeight b 0 * ((0 : ℕ) : ℝ) ^ (-s) :=
          mul_nonneg (primeLogAbsWeight_nonneg b 0) (Real.rpow_nonneg (by norm_num) _)
        exact mul_nonneg (by linarith) hnn
      linarith
    · have hn1 : 1 ≤ n := hn
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hrs : ((n : ℝ)) ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith)
      have hrpos : (0 : ℝ) ≤ ((n : ℝ)) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      have hwnn : (0 : ℝ) ≤ primeLogAbsWeight b n := primeLogAbsWeight_nonneg b n
      have hdiff : |timeOneCorrection n - abelShapeFactor s n|
          ≤ ((n : ℝ)) ^ (-(4 : ℝ)) + (2 ^ (s / 2) - 1) := by
        have h1 := abs_timeOneCorrection_sub_one_le n
        have h2 := abs_abelShapeFactor_sub_one_le hs hn1
        calc |timeOneCorrection n - abelShapeFactor s n|
            = |(timeOneCorrection n - 1) + (1 - abelShapeFactor s n)| := by ring_nf
          _ ≤ |timeOneCorrection n - 1| + |1 - abelShapeFactor s n| := abs_add_le _ _
          _ ≤ ((n : ℝ)) ^ (-(4 : ℝ)) + (2 ^ (s / 2) - 1) := by
              rw [abs_sub_comm 1 (abelShapeFactor s n)]
              linarith
      have hfac : timeOneCorrection n * abelWeighted b s n - abelShapeFactor s n * abelWeighted b s n
          = (timeOneCorrection n - abelShapeFactor s n) * abelWeighted b s n := by ring
      rw [hfac, Real.norm_eq_abs, abs_mul, abs_abelWeighted]
      have hmulle : |timeOneCorrection n - abelShapeFactor s n|
            * (primeLogAbsWeight b n * ((n : ℝ)) ^ (-s))
          ≤ (((n : ℝ)) ^ (-(4 : ℝ)) + (2 ^ (s / 2) - 1))
            * (primeLogAbsWeight b n * ((n : ℝ)) ^ (-s)) := by
        refine mul_le_mul_of_nonneg_right hdiff (mul_nonneg hwnn hrpos)
      refine le_trans hmulle ?_
      have hnn4 : (0 : ℝ) ≤ ((n : ℝ)) ^ (-(4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      have hkey : primeLogAbsWeight b n * ((n : ℝ)) ^ (-(4 : ℝ)) * ((n : ℝ)) ^ (-s)
          ≤ primeLogAbsWeight b n * ((n : ℝ)) ^ (-(4 : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hrs (mul_nonneg hwnn hnn4)
      nlinarith [hkey]
  have hbound := norm_tsum_le_tsum_norm (f := fun n : ℕ =>
      timeOneCorrection n * abelWeighted b s n - abelShapeFactor s n * abelWeighted b s n)
    (by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hmaj1.add hmaj2))
  have hcompare : ∑' n : ℕ,
      ‖timeOneCorrection n * abelWeighted b s n - abelShapeFactor s n * abelWeighted b s n‖
      ≤ (∑' n : ℕ, primeLogAbsWeight b n * ((n : ℝ)) ^ (-(4 : ℝ)))
        + (2 ^ (s / 2) - 1) * ∑' n : ℕ, primeLogAbsWeight b n * ((n : ℝ)) ^ (-s) := by
    have h := Summable.tsum_le_tsum hterm
      (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hmaj1.add hmaj2))
      (hmaj1.add hmaj2)
    rwa [hmaj1.tsum_add hmaj2, tsum_mul_left] at h
  have habs : |∑' n : ℕ,
      (timeOneCorrection n * abelWeighted b s n - abelShapeFactor s n * abelWeighted b s n)|
      ≤ (∑' n : ℕ, primeLogAbsWeight b n * ((n : ℝ)) ^ (-(4 : ℝ)))
        + (2 ^ (s / 2) - 1) * ∑' n : ℕ, primeLogAbsWeight b n * ((n : ℝ)) ^ (-s) := by
    rw [← Real.norm_eq_abs]
    exact le_trans hbound hcompare
  have hAbel := mul_tsum_primeLogAbsWeight_rpow_le hs hC
  rw [abs_mul, abs_of_pos hs]
  have hnnK : (0 : ℝ) ≤ ∑' n : ℕ, primeLogAbsWeight b n * ((n : ℝ)) ^ (-(4 : ℝ)) :=
    tsum_nonneg fun n => mul_nonneg (primeLogAbsWeight_nonneg b n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  nlinarith [habs, hAbel, hs.le, h2s, hnnK]


/-- **Equation (15).**  The simple pole of the time-one prime--Laplace source is exactly the
analytic residue of the Mertens conormal: `lim_{s ↓ 0} s M_{1,b}(s) = √2 · q_M(b)`. -/
theorem tendsto_timeOnePrimeLaplace {b : ℕ → ℝ} {c : ℝ}
    (hc : MemVanishingTailLayer fun n => b n - c) :
    Tendsto (fun s : ℝ => s * timeOnePrimeLaplace b s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt 2 * c)) := by
  obtain ⟨C, hC⟩ := memMarcinkiewiczLogLayer_of_actual (x := b) ⟨c, hc⟩
  set K : ℝ := ∑' n : ℕ, primeLogAbsWeight b n * ((n : ℝ)) ^ (-(4 : ℝ)) with hKdef
  have h2 : Tendsto (fun s : ℝ => (2 : ℝ) ^ (s / 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h := tendsto_const_rpow_half (by norm_num : (0 : ℝ) < 2) (1 / 2)
    have h' : (fun θ : ℝ => (2 : ℝ) ^ ((1 / 2 : ℝ) * θ)) = fun θ : ℝ => (2 : ℝ) ^ (θ / 2) := by
      funext θ
      congr 1
      ring
    rw [h'] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hmaj : Tendsto (fun s : ℝ =>
      Real.sqrt 2 * (s * K + (2 ^ (s / 2) - 1) * (max C 0 * (1 + s))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 : Tendsto (fun s : ℝ => s * K) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hcont : Tendsto (fun s : ℝ => s * K) (nhds 0) (nhds (0 * K)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun s : ℝ => max C 0 * (1 + s)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (max C 0 * (1 + 0))) :=
      ((continuous_const.mul (continuous_const.add continuous_id)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have h4 : Tendsto (fun s : ℝ => (2 : ℝ) ^ (s / 2) - 1) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have := h2.sub (tendsto_const_nhds (x := (1 : ℝ)))
      simpa using this
    have hprod := h4.mul h3
    rw [zero_mul] at hprod
    have hsum := h1.add hprod
    rw [add_zero] at hsum
    have := hsum.const_mul (Real.sqrt 2)
    rw [mul_zero] at this
    exact this
  have hdiff : Tendsto (fun s : ℝ => s * timeOnePrimeLaplace b s
      - Real.sqrt 2 * gammaShapeAbelFunctional s b) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Real.norm_eq_abs]
    exact abs_timeOne_sub_abel_le hs hC
  have hL := (tendsto_gammaShapeAbelFunctional_actual hc).const_mul (Real.sqrt 2)
  have hsum := hdiff.add hL
  rw [zero_add] at hsum
  refine hsum.congr fun s => ?_
  ring

/-! ## Equation (19): the rank-one factorial transgression of the polar germ -/

open GaloisForLFunctions.HTGeometry in
/-- **Equation (19).**  The Gamma adjacent-clock curvature of the polar-germ jet is the rank-one
outer product of the highest raw derivative with the factorial-tail boundary vector. -/
theorem gammaClockCurvature_coronaPolarGermJet (c : ℝ) (N : ℕ) (x₀ : ℝ) :
    gammaClockCurvature N (fun i : Fin (N + 1) => ((coronaPolarGermJet c (i : ℕ) x₀ : ℝ) : ℂ))
      = ((coronaPolarGermJet c N x₀ : ℝ) : ℂ) • gammaClockBoundaryVector N := by
  rw [gammaClockCurvature_eq_outerProduct]
  congr 2

open GaloisForLFunctions.HTGeometry in
/-- **Equation (21).**  For a nonzero conormal coefficient the transgression is nonzero at every
clock resolution. -/
theorem gammaClockCurvature_coronaPolarGermJet_ne_zero {c : ℝ} (hc : c ≠ 0) (N : ℕ) {x₀ : ℝ}
    (hx : x₀ ≠ 0) :
    gammaClockCurvature (N + 1)
        (fun i : Fin (N + 2) => ((coronaPolarGermJet c (i : ℕ) x₀ : ℝ) : ℂ)) ≠ 0 := by
  rw [gammaClockCurvature_coronaPolarGermJet]
  refine smul_ne_zero ?_ (gammaClockBoundaryVector_ne_zero N)
  simpa using coronaPolarGermJet_ne_zero hc (N + 1) hx

end

end RHTower
