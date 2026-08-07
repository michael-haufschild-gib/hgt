import GaloisForLFunctions.RHTower.HedenmalmHilbertSchmidtNorm

/-!
# The integer-shift anomaly is an exact theta interval

The rank-one anomaly of the normalized integer shift integrates to a literal interval mass of the
source:

`r_n(x) = i n^{-1/2} ∫_x^{x + log n} k(t) dt`.

Consequently the anomaly obeys the exact multiplicative Wess--Zumino law

`r_{mn} = n^{-1/2} r_m + T_m r_n`,

so the finite integer-shift anomaly is a flat, exact monoid cocycle: its curvature vanishes and
cannot by itself carry an extension class.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmIntervalAnomaly

open HedenmalmQuantile HedenmalmPrimeTranslation

variable (S : PositiveDensitySource)

/-- The source mass of a bounded interval. -/
def intervalMass (a b : ℝ) : ℝ := ∫ t in Ioc a b, S.k t

theorem mass_mul_cdfFun_sub {a b : ℝ} (hab : a ≤ b) :
    S.mass * (S.cdfFun b - S.cdfFun a) = intervalMass S a b := by
  have hsplit : (∫ t in Iic a, S.k t) + ∫ t in Ioc a b, S.k t = ∫ t in Iic b, S.k t := by
    rw [← MeasureTheory.setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
      S.integrable_k.integrableOn S.integrable_k.integrableOn, Iic_union_Ioc_eq_Iic hab]
  have hM : S.mass ≠ 0 := S.mass_ne_zero
  rw [intervalMass]
  show S.mass * ((∫ t in Iic b, S.k t) / S.mass - (∫ t in Iic a, S.k t) / S.mass)
    = ∫ t in Ioc a b, S.k t
  rw [← hsplit]
  field_simp
  ring

/-- **The anomaly is an exact theta interval.**  The rank-one anomaly of the normalized integer
shift is `i n^{-1/2}` times the source mass of the interval `[x, x + log n]`. -/
theorem integerAnomaly_eq_intervalMass {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    integerAnomaly S n x
      = Complex.I * ((((n : ℝ) ^ (-(1 / 2 : ℝ)) * intervalMass S x (x + Real.log n) : ℝ)) : ℂ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hab : x ≤ x + Real.log n := by linarith
  rw [integerAnomaly_eq]
  congr 2
  rw [mul_assoc, mass_mul_cdfFun_sub S hab]

/-- **The multiplicative Wess--Zumino law.**  The interval anomalies compose as an exact monoid
cocycle. -/
theorem intervalMass_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    intervalMass S a b + intervalMass S b c = intervalMass S a c := by
  have hdisj : Disjoint (Ioc a b) (Ioc b c) := by
    rw [Set.disjoint_left]
    rintro u ⟨_, hu⟩ ⟨hu', _⟩
    exact absurd hu (not_le.mpr hu')
  rw [intervalMass, intervalMass, intervalMass,
    ← MeasureTheory.setIntegral_union hdisj measurableSet_Ioc
      S.integrable_k.integrableOn S.integrable_k.integrableOn,
    Ioc_union_Ioc_eq_Ioc hab hbc]

theorem integerAnomaly_mul {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (x : ℝ) :
    integerAnomaly S (m * n) x
      = ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * integerAnomaly S m x
        + ((((m : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * integerAnomaly S n (x + Real.log m) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hlogmul : Real.log ((m * n : ℕ) : ℝ) = Real.log m + Real.log n := by
    push_cast
    exact Real.log_mul hmpos.ne' hnpos.ne'
  have hpow : (((m * n : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))
      = ((m : ℝ) ^ (-(1 / 2 : ℝ))) * ((n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    push_cast
    exact Real.mul_rpow hmpos.le hnpos.le
  rw [integerAnomaly_eq_intervalMass S (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hm) (Nat.one_le_iff_ne_zero.mp hn))) x,
    integerAnomaly_eq_intervalMass S hm x,
    integerAnomaly_eq_intervalMass S hn (x + Real.log m), hlogmul, hpow]
  have hsplit : intervalMass S x (x + Real.log m)
      + intervalMass S (x + Real.log m) (x + (Real.log m + Real.log n))
      = intervalMass S x (x + (Real.log m + Real.log n)) :=
    intervalMass_add S (by linarith) (by linarith)
  rw [← hsplit]
  push_cast
  rw [show x + Real.log m + Real.log n = x + (Real.log m + Real.log n) by ring]
  ring


/-! ### The centered positive window -/

theorem intervalMass_pos {a b : ℝ} (hab : a < b) : 0 < intervalMass S a b := by
  rw [← mass_mul_cdfFun_sub S hab.le]
  have := S.strictMono_cdfFun hab
  have hM := S.mass_pos
  nlinarith

/-- The centered window `c_n(x) = n^{-1/2} ∫_{x - log n / 2}^{x + log n / 2} k`. -/
def centeredWindow (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) ^ (-(1 / 2 : ℝ))
    * intervalMass S (x - Real.log n / 2) (x + Real.log n / 2)

/-- **The centered window is the shifted anomaly.**  `c_n = -i S_{log n / 2} r_n`. -/
theorem centeredWindow_eq {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    ((centeredWindow S n x : ℝ) : ℂ)
      = -Complex.I * integerAnomaly S n (x - Real.log n / 2) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [integerAnomaly_eq_intervalMass S hn, centeredWindow,
    show x - Real.log n / 2 + Real.log n = x + Real.log n / 2 by ring]
  push_cast
  linear_combination ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    * ((intervalMass S (x - Real.log n / 2) (x + Real.log n / 2) : ℝ) : ℂ)) * hI

/-- **The centered window is strictly positive** for every integer beyond one. -/
theorem centeredWindow_pos {n : ℕ} (hn : 2 ≤ n) (x : ℝ) : 0 < centeredWindow S n x := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hlt : x - Real.log n / 2 < x + Real.log n / 2 := by linarith
  have hpow : (0 : ℝ) < (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  exact mul_pos hpow (intervalMass_pos S hlt)


end HedenmalmIntervalAnomaly

end

end RHTower
