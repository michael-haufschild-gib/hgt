import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmHilbertSchmidtNorm

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



/-! ### Evenness of the centered window -/

theorem cdfFun_neg (hk : ∀ x, S.k (-x) = S.k x) (x : ℝ) :
    S.cdfFun (-x) = 1 - S.cdfFun x := by
  have hkC : Integrable (fun y => (S.k y : ℂ)) (volume : Measure ℝ) := S.integrable_k.ofReal
  have hrefl : (∫ y in Iic (-x), (S.k y : ℂ)) = ∫ u in Ici x, (S.k u : ℂ) := by
    rw [setIntegral_Iic_comp_neg (fun y => (S.k y : ℂ)) x]
    refine setIntegral_congr_fun measurableSet_Ici fun u _ => ?_
    rw [hk u]
  have hsub : (∫ y in Iic (-x), (S.k y : ℂ))
      = (∫ u, (S.k u : ℂ)) - ∫ u in Iic x, (S.k u : ℂ) := by
    rw [hrefl, setIntegral_Ici_eq_sub hkC x]
  have hreal : (∫ y in Iic (-x), S.k y) = S.mass - ∫ u in Iic x, S.k u := by
    have h := hsub
    rw [integral_complex_ofReal, integral_complex_ofReal, integral_complex_ofReal,
      ← Complex.ofReal_sub] at h
    exact_mod_cast h
  have hM : S.mass ≠ 0 := S.mass_ne_zero
  show (∫ y in Iic (-x), S.k y) / S.mass = 1 - (∫ y in Iic x, S.k y) / S.mass
  rw [hreal]
  field_simp

theorem intervalMass_neg (hk : ∀ x, S.k (-x) = S.k x) {a b : ℝ} (hab : a ≤ b) :
    intervalMass S (-b) (-a) = intervalMass S a b := by
  rw [← mass_mul_cdfFun_sub S (neg_le_neg hab), ← mass_mul_cdfFun_sub S hab,
    cdfFun_neg S hk a, cdfFun_neg S hk b]
  ring

/-- **The centered window is even** for an even source. -/
theorem centeredWindow_neg (hk : ∀ x, S.k (-x) = S.k x) {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    centeredWindow S n (-x) = centeredWindow S n x := by
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hle : x - Real.log n / 2 ≤ x + Real.log n / 2 := by linarith
  rw [centeredWindow, centeredWindow]
  congr 1
  rw [show -x - Real.log n / 2 = -(x + Real.log n / 2) by ring,
    show -x + Real.log n / 2 = -(x - Real.log n / 2) by ring,
    intervalMass_neg S hk hle]



/-! ### The interval multiplier and its zero set -/

/-- The interval multiplier `q_n(z) = n^{-1/2}(1 - e^{-i z log n})/z`. -/
def shiftMultiplier (n : ℕ) (z : ℂ) : ℂ :=
  ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)
    * (1 - Complex.exp (-(Complex.I * z * ((Real.log n : ℝ) : ℂ)))) / z

/-- **The zero set of the interval multiplier.**  Away from the origin the multiplier vanishes
exactly on the arithmetic progression `z log n ∈ 2π ℤ`. -/
theorem shiftMultiplier_eq_zero_iff {n : ℕ} (hn : 2 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    shiftMultiplier n z = 0 ↔ ∃ j : ℤ, z * ((Real.log n : ℝ) : ℂ) = 2 * Real.pi * j := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hpow : ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hnpos _
    exact_mod_cast this.ne'
  rw [shiftMultiplier, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 hpow
      · have hexp : Complex.exp (-(Complex.I * z * ((Real.log n : ℝ) : ℂ))) = 1 := by
          linear_combination -h1
        obtain ⟨j, hj⟩ := Complex.exp_eq_one_iff.mp hexp
        refine ⟨-j, ?_⟩
        have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
        have : Complex.I * (z * ((Real.log n : ℝ) : ℂ))
            = Complex.I * (2 * (Real.pi : ℂ) * (-j : ℤ)) := by
          push_cast
          push_cast at hj
          linear_combination -hj
        exact mul_left_cancel₀ hI this
    · exact absurd h hz
  · rintro ⟨j, hj⟩
    left
    have hexp : Complex.exp (-(Complex.I * z * ((Real.log n : ℝ) : ℂ))) = 1 := by
      refine Complex.exp_eq_one_iff.mpr ⟨-j, ?_⟩
      push_cast
      push_cast at hj
      linear_combination -Complex.I * hj
    rw [hexp]
    ring




/-- The trivial shift carries no anomaly: the interval degenerates. -/
@[simp] theorem intervalMass_self (a : ℝ) : intervalMass S a a = 0 := by
  rw [intervalMass, Set.Ioc_self, MeasureTheory.setIntegral_empty]

@[simp] theorem centeredWindow_one (x : ℝ) : centeredWindow S 1 x = 0 := by
  rw [centeredWindow]
  simp [Real.log_one]

@[simp] theorem shiftMultiplier_one (z : ℂ) : shiftMultiplier 1 z = 0 := by
  rw [shiftMultiplier]
  simp [Real.log_one]

/-! ### The two-prime no-common-zero theorem -/

private theorem pow_three_ne_pow_two {a b : ℕ} (ha : 0 < a)
    (hab : (a : ℝ) * Real.log 3 = (b : ℝ) * Real.log 2) : False := by
  have h3 : Real.log ((3 : ℝ) ^ a) = Real.log ((2 : ℝ) ^ b) := by
    rw [Real.log_pow, Real.log_pow]
    exact_mod_cast hab
  have hpow : ((3 : ℝ)) ^ a = ((2 : ℝ)) ^ b := by
    have h3pos : (0 : ℝ) < (3 : ℝ) ^ a := by positivity
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
    have := congrArg Real.exp h3
    rwa [Real.exp_log h3pos, Real.exp_log h2pos] at this
  have hnat : (3 : ℕ) ^ a = (2 : ℕ) ^ b := by
    have : ((3 ^ a : ℕ) : ℝ) = ((2 ^ b : ℕ) : ℝ) := by push_cast; exact hpow
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos b with hb | hb
  · rw [hb, pow_zero] at hnat
    have : (3 : ℕ) ^ a ≠ 1 := by
      have : 1 < (3 : ℕ) ^ a := Nat.one_lt_pow ha.ne' (by norm_num)
      omega
    exact this hnat
  · have hdvd : (2 : ℕ) ∣ (3 : ℕ) ^ a := by
      rw [hnat]
      exact dvd_pow_self 2 hb.ne'
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd)
    omega

/-- **The logarithms of two and three are incommensurable.** -/
theorem eq_zero_of_log_three_eq_log_two {j k : ℤ}
    (h : (j : ℝ) * Real.log 3 = (k : ℝ) * Real.log 2) : j = 0 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rcases lt_trichotomy j 0 with hj | hj | hj
  · exfalso
    have hjR : ((-j : ℤ) : ℝ) > 0 := by
      have : ((j : ℤ) : ℝ) < 0 := by exact_mod_cast hj
      push_cast
      linarith
    have hjr : ((j : ℤ) : ℝ) < 0 := by exact_mod_cast hj
    have hkneg : ((k : ℤ) : ℝ) < 0 := by nlinarith
    have hk : 0 < -k := by
      have : (k : ℤ) < 0 := by exact_mod_cast hkneg
      omega
    have hjpos : 0 < -j := by omega
    have hcj : (((-j).toNat : ℕ) : ℝ) = ((-j : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hjpos.le]
    have hck : (((-k).toNat : ℕ) : ℝ) = ((-k : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hk.le]
    have hcast : (((-j).toNat : ℕ) : ℝ) * Real.log 3
        = (((-k).toNat : ℕ) : ℝ) * Real.log 2 := by
      rw [hcj, hck]
      push_cast
      linarith [h]
    exact pow_three_ne_pow_two (by omega) hcast
  · exact hj
  · exfalso
    have hjR : ((j : ℤ) : ℝ) > 0 := by exact_mod_cast hj
    have hkR : ((k : ℤ) : ℝ) > 0 := by nlinarith
    have hk : 0 < k := by exact_mod_cast hkR
    have hcj : ((j.toNat : ℕ) : ℝ) = ((j : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hj.le]
    have hck : ((k.toNat : ℕ) : ℝ) = ((k : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hk.le]
    have hcast : ((j.toNat : ℕ) : ℝ) * Real.log 3 = ((k.toNat : ℕ) : ℝ) * Real.log 2 := by
      rw [hcj, hck]
      exact h
    exact pow_three_ne_pow_two (by omega) hcast

/-- **The prime-two and prime-three interval multipliers have no common zero.** -/
theorem no_common_zero_two_three {z : ℂ}
    (h2 : shiftMultiplier 2 z = 0) (h3 : shiftMultiplier 3 z = 0) : z = 0 := by
  by_contra hz
  obtain ⟨j, hj⟩ := (shiftMultiplier_eq_zero_iff (by norm_num) hz).mp h2
  obtain ⟨k, hk⟩ := (shiftMultiplier_eq_zero_iff (by norm_num) hz).mp h3
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hcross : ((j : ℤ) : ℂ) * ((Real.log 3 : ℝ) : ℂ)
      = ((k : ℤ) : ℂ) * ((Real.log 2 : ℝ) : ℂ) := by
    have e1 : z * ((Real.log ((2 : ℕ) : ℝ) : ℝ) : ℂ) * ((Real.log ((3 : ℕ) : ℝ) : ℝ) : ℂ)
        = 2 * (Real.pi : ℂ) * (j : ℤ) * ((Real.log ((3 : ℕ) : ℝ) : ℝ) : ℂ) := by
      rw [hj]
    have e2 : z * ((Real.log ((3 : ℕ) : ℝ) : ℝ) : ℂ) * ((Real.log ((2 : ℕ) : ℝ) : ℝ) : ℂ)
        = 2 * (Real.pi : ℂ) * (k : ℤ) * ((Real.log ((2 : ℕ) : ℝ) : ℝ) : ℂ) := by
      rw [hk]
    have e3 : 2 * (Real.pi : ℂ) * (j : ℤ) * ((Real.log ((3 : ℕ) : ℝ) : ℝ) : ℂ)
        = 2 * (Real.pi : ℂ) * (k : ℤ) * ((Real.log ((2 : ℕ) : ℝ) : ℝ) : ℂ) := by
      rw [← e1, ← e2]
      ring
    have h2ne : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 := by
      exact mul_ne_zero two_ne_zero hpi
    have := mul_left_cancel₀ h2ne (by linear_combination e3 :
      (2 : ℂ) * (Real.pi : ℂ) * (((j : ℤ) : ℂ) * ((Real.log ((3 : ℕ) : ℝ) : ℝ) : ℂ))
        = (2 : ℂ) * (Real.pi : ℂ) * (((k : ℤ) : ℂ) * ((Real.log ((2 : ℕ) : ℝ) : ℝ) : ℂ)))
    exact this
  have hreal : (j : ℝ) * Real.log 3 = (k : ℝ) * Real.log 2 := by
    have hc : ((((j : ℤ) : ℝ) * Real.log ((3 : ℕ) : ℝ) : ℝ) : ℂ)
        = ((((k : ℤ) : ℝ) * Real.log ((2 : ℕ) : ℝ) : ℝ) : ℂ) := by
      push_cast
      exact hcross
    have h' := Complex.ofReal_inj.mp hc
    simp at h'
    exact h'
  have hj0 : j = 0 := eq_zero_of_log_three_eq_log_two hreal
  rw [hj0] at hj
  have hl2 : ((Real.log ((2 : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
    have : Real.log ((2 : ℕ) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < Real.log ((2 : ℕ) : ℝ) := by
        rw [Nat.cast_ofNat]
        exact Real.log_pos (by norm_num)
      exact this.ne'
    exact_mod_cast this
  have : z * ((Real.log ((2 : ℕ) : ℝ) : ℝ) : ℂ) = 0 := by
    rw [hj]
    push_cast
    ring
  rcases mul_eq_zero.mp this with h | h
  · exact hz h
  · exact hl2 h



/-! ### The centered multiplier -/

/-- The centered interval multiplier `a_n(z) = n^{-1/2} · 2 sin(z log n / 2) / z`, written with
the exponential form of the sine. -/
def centeredMultiplier (n : ℕ) (z : ℂ) : ℂ :=
  ((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)
    * (Complex.exp (Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ))
      - Complex.exp (-(Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ)))) / (Complex.I * z)

/-- **The centered multiplier is the shifted interval multiplier.** -/
theorem centeredMultiplier_eq {n : ℕ} {z : ℂ} (hz : z ≠ 0) :
    centeredMultiplier n z
      = -Complex.I * Complex.exp (Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ))
        * shiftMultiplier n z := by
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hexp : Complex.exp (Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ))
      * Complex.exp (-(Complex.I * z * ((Real.log n : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [centeredMultiplier, shiftMultiplier,
    show Complex.exp (-(Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ)))
        = Complex.exp (Complex.I * z * ((Real.log n / 2 : ℝ) : ℂ))
          * Complex.exp (-(Complex.I * z * ((Real.log n : ℝ) : ℂ))) from hexp.symm]
  field_simp
  linear_combination (((((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)
    * (1 - Complex.exp (-(Complex.I * z * ((Real.log n : ℝ) : ℂ))))) * hII

/-- **The centered multiplier has the same zero set as the interval multiplier.** -/
theorem centeredMultiplier_eq_zero_iff {n : ℕ} {z : ℂ} (hz : z ≠ 0) :
    centeredMultiplier n z = 0 ↔ shiftMultiplier n z = 0 := by
  rw [centeredMultiplier_eq hz]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd (neg_eq_zero.mp h2) Complex.I_ne_zero
      · exact absurd h2 (Complex.exp_ne_zero _)
    · exact h1
  · intro h
    rw [h, mul_zero]

/-- **The centered prime-2 and prime-3 multipliers have no common zero.** -/
theorem no_common_zero_centered_two_three {z : ℂ}
    (h2 : centeredMultiplier 2 z = 0) (h3 : centeredMultiplier 3 z = 0) : z = 0 := by
  by_contra hz
  exact hz (no_common_zero_two_three ((centeredMultiplier_eq_zero_iff hz).mp h2)
    ((centeredMultiplier_eq_zero_iff hz).mp h3))



/-! ### Uniform bounds on the window -/

theorem intervalMass_le_mass {a b : ℝ} (hab : a ≤ b) : intervalMass S a b ≤ S.mass := by
  rw [← mass_mul_cdfFun_sub S hab]
  have hb := (S.cdfFun_mem_Ioo b).2
  have ha := (S.cdfFun_mem_Ioo a).1
  have hM := S.mass_pos
  nlinarith

/-- The centered window is uniformly bounded by the normalized total mass. -/
theorem centeredWindow_le {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    centeredWindow S n x ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * S.mass := by
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hle : x - Real.log n / 2 ≤ x + Real.log n / 2 := by linarith
  have hpow : (0 : ℝ) < (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have : (0 : ℝ) < (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact Real.rpow_pos_of_pos this _
  rw [centeredWindow]
  exact mul_le_mul_of_nonneg_left (intervalMass_le_mass S hle) hpow.le


end HedenmalmIntervalAnomaly

end

end RHTower
