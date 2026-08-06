import GaloisForLFunctions.RHTower.EulerHellingerDyadicSignSeries
import GaloisForLFunctions.RHTower.MertensPrimeWindowWeakConvergence
import GaloisForLFunctions.RHTower.PrimeClockFiniteScaling
import GaloisForLFunctions.HTGeometry.ZetaVerticalAlmostPeriodic

/-!
# The oriented shrinking-window profile of the reflected Hellinger sewing cost

In the critical window `c = t / log x` the reflected Hellinger sewing cost has a universal limit

```text
L_x(t / log x) → Ψ(t) := 2 ∫₀¹ (sinh(2tu) - 2 sinh(tu)) / u du.
```

The first prime power contributes the Mertens prime window of the continuous test function
`u ↦ 2 (sinh(2tu) - 2 sinh(tu)) / u`, and all higher prime powers contribute `O(1 / log x)`.  The
limit profile is odd, has the sign of `t`, and its cubic jet is the confluence order:

```text
|Ψ(t) - (2/3) t³| ≤ 2 |t|⁵      (|t| ≤ 1/2).
```
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The oriented dyadic test function -/

/-- The oriented dyadic sinh test function, extended by zero at the origin. -/
def dyadicSinhWindowTest (t u : ℝ) : ℝ :=
  2 * (Real.sinh (2 * (t * u)) - 2 * Real.sinh (t * u)) / u

theorem dyadicSinhWindowTest_zero (t : ℝ) : dyadicSinhWindowTest t 0 = 0 := by
  simp [dyadicSinhWindowTest]

theorem continuous_dyadicSinhWindowTest (t : ℝ) : Continuous (dyadicSinhWindowTest t) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst u
    set F : ℝ → ℝ := fun x => 2 * (Real.sinh (2 * (t * x)) - 2 * Real.sinh (t * x)) with hF
    set q : ℝ → ℝ := fun x => x⁻¹ * (F (0 + x) - F 0) with hq
    have hz : HasDerivAt (fun x : ℝ => t * x) t 0 := by
      simpa using (hasDerivAt_id (x := (0 : ℝ))).const_mul t
    have hz2 : HasDerivAt (fun x : ℝ => 2 * (t * x)) (2 * t) 0 := by
      simpa using hz.const_mul (2 : ℝ)
    have hFderiv : HasDerivAt F 0 0 := by
      have h := ((hz2.sinh.sub ((hz.sinh).const_mul 2)).const_mul 2)
      have hval : (2 : ℝ) * (Real.cosh (2 * (t * 0)) * (2 * t) -
          2 * (Real.cosh (t * 0) * t)) = 0 := by
        simp
      rw [hval] at h
      exact h
    have hupdate : ContinuousAt (Function.update q 0 0) 0 :=
      continuousAt_update_same.mpr (by simpa [hq] using hFderiv.tendsto_slope_zero)
    convert hupdate using 1
    funext x
    by_cases hx : x = 0
    · subst x
      simp [dyadicSinhWindowTest, hq, hF]
    · simp only [hx, ne_eq, not_false_eq_true, Function.update_of_ne, dyadicSinhWindowTest, hq, hF]
      have hz0 : (2 : ℝ) * (Real.sinh (2 * (t * 0)) - 2 * Real.sinh (t * 0)) = 0 := by simp
      simp only [zero_add, hz0, sub_zero]
      field_simp
  · unfold dyadicSinhWindowTest
    fun_prop (disch := assumption)

/-- The oriented shrinking-window profile. -/
def orientedHellingerDyadicProfile (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, dyadicSinhWindowTest t u

/-- The profile is odd. -/
theorem orientedHellingerDyadicProfile_neg (t : ℝ) :
    orientedHellingerDyadicProfile (-t) = -orientedHellingerDyadicProfile t := by
  rw [orientedHellingerDyadicProfile, orientedHellingerDyadicProfile,
    ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [dyadicSinhWindowTest]
  rw [show 2 * (-t * u) = -(2 * (t * u)) by ring, show -t * u = -(t * u) by ring,
    Real.sinh_neg, Real.sinh_neg]
  ring

/-- The profile has the sign of the drift. -/
theorem orientedHellingerDyadicProfile_pos {t : ℝ} (ht : 0 < t) :
    0 < orientedHellingerDyadicProfile t := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_dyadicSinhWindowTest t).intervalIntegrable 0 1) (fun u hu => ?_) one_pos
  have hu0 : 0 < u := hu.1
  have hstep : 0 < Real.sinh (2 * (t * u)) - 2 * Real.sinh (t * u) :=
    sinh_two_mul_sub_two_sinh_pos (by positivity)
  rw [dyadicSinhWindowTest]
  positivity

/-! ## The cubic jet of the profile -/

private theorem abs_exp_sub_taylor_six {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120)| ≤
      |x| ^ 6 * (7 / 4320) := by
  have h := Real.exp_bound hx (n := 6) (by norm_num)
  have hsum : (∑ m ∈ Finset.range 6, x ^ m / (m.factorial : ℝ)) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  calc |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120)|
      ≤ |x| ^ 6 * ((Nat.succ 6 : ℝ) / ((Nat.factorial 6 : ℝ) * 6)) := h
    _ = |x| ^ 6 * (7 / 4320) := by norm_num [Nat.factorial]

/-- **The cubic contact of the dyadic sinh step.** -/
theorem abs_dyadicSinhStep_sub_cube_le {v : ℝ} (hv : |v| ≤ 1 / 2) :
    |Real.sinh (2 * v) - 2 * Real.sinh v - v ^ 3| ≤ |v| ^ 5 := by
  have habs2 : |2 * v| ≤ 1 := by
    rw [abs_mul, abs_two]
    linarith
  have habsn2 : |(-(2 * v))| ≤ 1 := by rwa [abs_neg]
  have habs1 : |v| ≤ 1 := by linarith
  have habsn1 : |(-v)| ≤ 1 := by rwa [abs_neg]
  have hA := abs_exp_sub_taylor_six habs2
  have hB := abs_exp_sub_taylor_six habsn2
  have hC := abs_exp_sub_taylor_six habs1
  have hD := abs_exp_sub_taylor_six habsn1
  rw [abs_neg] at hB hD
  have h2v : |2 * v| ^ 6 = 64 * |v| ^ 6 := by
    rw [abs_mul, abs_two, mul_pow]
    norm_num
  rw [h2v] at hA hB
  have hpow : |v| ^ 6 ≤ |v| ^ 5 * (1 / 2) := by
    have h5 : (0 : ℝ) ≤ |v| ^ 5 := by positivity
    calc |v| ^ 6 = |v| ^ 5 * |v| := by ring
      _ ≤ |v| ^ 5 * (1 / 2) := by nlinarith [abs_nonneg v]
  have hsinh2 : Real.sinh (2 * v) = (Real.exp (2 * v) - Real.exp (-(2 * v))) / 2 :=
    Real.sinh_eq (2 * v)
  have hsinh1 : Real.sinh v = (Real.exp v - Real.exp (-v)) / 2 := Real.sinh_eq v
  rw [hsinh2, hsinh1]
  obtain ⟨hA1, hA2⟩ := abs_le.mp hA
  obtain ⟨hB1, hB2⟩ := abs_le.mp hB
  obtain ⟨hC1, hC2⟩ := abs_le.mp hC
  obtain ⟨hD1, hD2⟩ := abs_le.mp hD
  have hv5 : (0 : ℝ) ≤ |v| ^ 5 := by positivity
  have hquint : v ^ 5 ≤ |v| ^ 5 := by
    calc v ^ 5 ≤ |v ^ 5| := le_abs_self _
      _ = |v| ^ 5 := by rw [abs_pow]
  have hquint' : -(|v| ^ 5) ≤ v ^ 5 := by
    have : |v ^ 5| ≤ |v| ^ 5 := by rw [abs_pow]
    linarith [neg_abs_le (v ^ 5)]
  rw [abs_le]
  constructor <;> nlinarith [hA1, hA2, hB1, hB2, hC1, hC2, hD1, hD2, hpow, hv5, hquint, hquint']

/-- **The cubic jet of the profile.**  `Ψ(t) = (2/3) t³ + O(t⁵)`. -/
theorem abs_orientedHellingerDyadicProfile_sub_cube_le {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |orientedHellingerDyadicProfile t - 2 / 3 * t ^ 3| ≤ 2 * |t| ^ 5 := by
  have hcube : (∫ u in (0 : ℝ)..1, 2 * t ^ 3 * u ^ 2) = 2 / 3 * t ^ 3 := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  have hint1 : IntervalIntegrable (dyadicSinhWindowTest t) volume 0 1 :=
    (continuous_dyadicSinhWindowTest t).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun u : ℝ => 2 * t ^ 3 * u ^ 2) volume 0 1 :=
    (by fun_prop : Continuous (fun u : ℝ => 2 * t ^ 3 * u ^ 2)).intervalIntegrable 0 1
  rw [orientedHellingerDyadicProfile, ← hcube, ← intervalIntegral.integral_sub hint1 hint2]
  have hbound : ∀ u ∈ uIoc (0 : ℝ) 1,
      ‖dyadicSinhWindowTest t u - 2 * t ^ 3 * u ^ 2‖ ≤ 2 * |t| ^ 5 := by
    intro u hu
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    have hu0 : 0 < u := hu.1
    have hu1 : u ≤ 1 := hu.2
    have hvu : |t * u| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos hu0]
      nlinarith [abs_nonneg t]
    have hstep := abs_dyadicSinhStep_sub_cube_le hvu
    have hrw : dyadicSinhWindowTest t u - 2 * t ^ 3 * u ^ 2 =
        2 * (Real.sinh (2 * (t * u)) - 2 * Real.sinh (t * u) - (t * u) ^ 3) / u := by
      rw [dyadicSinhWindowTest]
      field_simp
    rw [Real.norm_eq_abs, hrw, abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
    have habs : |2 * (Real.sinh (2 * (t * u)) - 2 * Real.sinh (t * u) - (t * u) ^ 3)| ≤
        2 * |t * u| ^ 5 := by
      rw [abs_mul, abs_two]
      linarith
    have hpow : |t * u| ^ 5 = |t| ^ 5 * u ^ 5 := by
      rw [abs_mul, abs_of_pos hu0, mul_pow]
    rw [hpow] at habs
    have hu5 : u ^ 5 ≤ u := by nlinarith [pow_le_one₀ hu0.le hu1 (n := 4)]
    have ht5 : (0 : ℝ) ≤ |t| ^ 5 := by positivity
    nlinarith
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa using this

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators

/-! ## The first prime power and the higher-power tail -/

/-- The first-prime-power part of the local reflected sewing cost. -/
def localSewingLogHead (p : ℕ) (c : ℝ) : ℝ :=
  2 * (p : ℝ)⁻¹ * (Real.sinh (2 * (c * Real.log p)) - 2 * Real.sinh (c * Real.log p))

private def sewingSeriesTerm (p : ℕ) (c : ℝ) (k : ℕ) : ℝ :=
  2 * ((p : ℝ) ^ (-((k : ℝ) + 1)) / ((k : ℝ) + 1)) *
    (Real.sinh (2 * (c * ((k : ℝ) + 1) * Real.log (p : ℝ)))
      - 2 * Real.sinh (c * ((k : ℝ) + 1) * Real.log (p : ℝ)))

private theorem hasSum_sewingSeriesTerm {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : |c| < 1 / 2) :
    HasSum (sewingSeriesTerm p c) (localSewingLog p c) :=
  hasSum_localSewingLog hp hc

private theorem sewingSeriesTerm_zero (p : ℕ) (c : ℝ) :
    sewingSeriesTerm p c 0 = localSewingLogHead p c := by
  rw [sewingSeriesTerm, localSewingLogHead]
  norm_num [Real.rpow_neg_one]

private theorem hasSum_sewingSeriesTerm_tail {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : |c| < 1 / 2) :
    HasSum (fun j : ℕ => sewingSeriesTerm p c (j + 1))
      (localSewingLog p c - localSewingLogHead p c) := by
  rw [hasSum_nat_add_iff 1, Finset.sum_range_one, sewingSeriesTerm_zero, sub_add_cancel]
  exact hasSum_sewingSeriesTerm hp hc

/-! ## Uniform decay of the higher-power tail -/

/-- The fixed geometric ratio controlling all higher prime powers. -/
def dyadicTailRatio : ℝ := Real.exp (-(3 / 4) * Real.log 2)

theorem dyadicTailRatio_pos : 0 < dyadicTailRatio := Real.exp_pos _

theorem dyadicTailRatio_lt_one : dyadicTailRatio < 1 := by
  rw [dyadicTailRatio, ← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- The reciprocal geometric mass of all higher prime powers. -/
def dyadicTailConst : ℝ := (1 - dyadicTailRatio)⁻¹

theorem dyadicTailConst_pos : 0 < dyadicTailConst := by
  rw [dyadicTailConst]
  have := dyadicTailRatio_lt_one
  positivity

private theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

private theorem abs_dyadicSinhStep_le (v : ℝ) :
    |Real.sinh (2 * v) - 2 * Real.sinh v| ≤ 4 * |v| * Real.exp (2 * |v|) := by
  have habs2 : |2 * v| = 2 * |v| := by rw [abs_mul, abs_two]
  have hv0 : (0 : ℝ) ≤ |v| := abs_nonneg v
  have h1 : |Real.sinh (2 * v)| ≤ 2 * |v| * Real.cosh (2 * |v|) := by
    have h' := abs_sinh_le_abs_mul_cosh (x := 2 * v) (C := |2 * v|) (abs_nonneg _) le_rfl
    rw [habs2] at h'
    exact h'
  have h2 : |Real.sinh v| ≤ |v| * Real.cosh |v| :=
    abs_sinh_le_abs_mul_cosh (abs_nonneg _) le_rfl
  have hc1 : Real.cosh (2 * |v|) ≤ Real.exp (2 * |v|) := by
    have h := cosh_le_exp_abs (2 * |v|)
    rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * |v|)] at h
  have hc2 : Real.cosh |v| ≤ Real.exp (2 * |v|) := by
    have h := cosh_le_exp_abs |v|
    rw [abs_abs] at h
    exact h.trans (Real.exp_le_exp.mpr (by linarith))
  have hstep1 : 2 * |v| * Real.cosh (2 * |v|) ≤ 2 * |v| * Real.exp (2 * |v|) :=
    mul_le_mul_of_nonneg_left hc1 (by positivity)
  have hstep2 : |v| * Real.cosh |v| ≤ |v| * Real.exp (2 * |v|) :=
    mul_le_mul_of_nonneg_left hc2 hv0
  calc |Real.sinh (2 * v) - 2 * Real.sinh v|
      ≤ |Real.sinh (2 * v)| + |2 * Real.sinh v| := abs_sub _ _
    _ = |Real.sinh (2 * v)| + 2 * |Real.sinh v| := by rw [abs_mul, abs_two]
    _ ≤ 4 * |v| * Real.exp (2 * |v|) := by linarith

private theorem rpow_neg_eq_exp {p : ℕ} (hp : p.Prime) (x : ℝ) :
    (p : ℝ) ^ x = Real.exp (x * Real.log (p : ℝ)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  rw [Real.rpow_def_of_pos hp0]
  ring_nf

private theorem tailTermBound {A L c : ℝ} (hA : 2 ≤ A) (hL : 0 < L) (hc : |c| ≤ 1 / 8) :
    2 * (Real.exp (-(A * L)) / A) *
        |Real.sinh (2 * (c * A * L)) - 2 * Real.sinh (c * A * L)| ≤
      8 * |c| * L * Real.exp (-(3 / 4) * (A * L)) := by
  have hApos : (0 : ℝ) < A := by linarith
  have hAL : (0 : ℝ) < A * L := mul_pos hApos hL
  have habsv : |c * A * L| = |c| * A * L := by
    rw [abs_mul, abs_mul, abs_of_pos hApos, abs_of_pos hL]
  have hstep := abs_dyadicSinhStep_le (c * A * L)
  rw [habsv] at hstep
  have hexpmono : Real.exp (2 * (|c| * A * L)) ≤ Real.exp (1 / 4 * (A * L)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 4 - 2 * |c|) hAL.le]
  have hchain : |Real.sinh (2 * (c * A * L)) - 2 * Real.sinh (c * A * L)| ≤
      4 * (|c| * A * L) * Real.exp (1 / 4 * (A * L)) :=
    hstep.trans (mul_le_mul_of_nonneg_left hexpmono (by positivity))
  have hexpadd : Real.exp (-(A * L)) * Real.exp (1 / 4 * (A * L)) =
      Real.exp (-(3 / 4) * (A * L)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc 2 * (Real.exp (-(A * L)) / A) *
        |Real.sinh (2 * (c * A * L)) - 2 * Real.sinh (c * A * L)|
      ≤ 2 * (Real.exp (-(A * L)) / A) *
          (4 * (|c| * A * L) * Real.exp (1 / 4 * (A * L))) :=
        mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = 8 * |c| * L * (Real.exp (-(A * L)) * Real.exp (1 / 4 * (A * L))) := by
        field_simp
        ring
    _ = 8 * |c| * L * Real.exp (-(3 / 4) * (A * L)) := by rw [hexpadd]

private theorem expSplit {L : ℝ} (j : ℕ) (hL2 : Real.log 2 ≤ L) :
    Real.exp (-(3 / 4) * (((j : ℝ) + 2) * L)) ≤
      Real.exp (-(3 / 2) * L) * dyadicTailRatio ^ j := by
  have hpowj : dyadicTailRatio ^ j = Real.exp ((j : ℝ) * (-(3 / 4) * Real.log 2)) := by
    rw [dyadicTailRatio, ← Real.exp_nat_mul]
  rw [hpowj, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hjL : (j : ℝ) * Real.log 2 ≤ (j : ℝ) * L :=
    mul_le_mul_of_nonneg_left hL2 (Nat.cast_nonneg j)
  nlinarith

private theorem abs_sewingSeriesTerm_succ_le {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : |c| ≤ 1 / 8)
    (j : ℕ) :
    |sewingSeriesTerm p c (j + 1)| ≤
      8 * |c| * (Real.log (p : ℝ) * Real.exp (-(3 / 2) * Real.log (p : ℝ))) *
        dyadicTailRatio ^ j := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hL2 : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have hcast : (((j + 1 : ℕ) : ℝ) + 1) = (j : ℝ) + 2 := by push_cast; ring
  have hmass : (p : ℝ) ^ (-((j : ℝ) + 2)) =
      Real.exp (-(((j : ℝ) + 2) * Real.log (p : ℝ))) := by
    rw [rpow_neg_eq_exp hp]
    congr 1
    ring
  have hterm : sewingSeriesTerm p c (j + 1) =
      2 * (Real.exp (-(((j : ℝ) + 2) * Real.log (p : ℝ))) / ((j : ℝ) + 2)) *
        (Real.sinh (2 * (c * ((j : ℝ) + 2) * Real.log (p : ℝ))) -
          2 * Real.sinh (c * ((j : ℝ) + 2) * Real.log (p : ℝ))) := by
    rw [sewingSeriesTerm, hcast, hmass]
  have hA : (2 : ℝ) ≤ (j : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  rw [hterm, abs_mul,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ 2 * (Real.exp (-(((j : ℝ) + 2) * Real.log (p : ℝ))) / ((j : ℝ) + 2)))]
  have hbound := tailTermBound (A := (j : ℝ) + 2) (L := Real.log (p : ℝ)) (c := c) hA hL hc
  refine hbound.trans ?_
  have hsplit := expSplit (L := Real.log (p : ℝ)) j hL2
  have hpos : (0 : ℝ) ≤ 8 * |c| * Real.log (p : ℝ) := by positivity
  calc 8 * |c| * Real.log (p : ℝ) *
        Real.exp (-(3 / 4) * (((j : ℝ) + 2) * Real.log (p : ℝ)))
      ≤ 8 * |c| * Real.log (p : ℝ) *
          (Real.exp (-(3 / 2) * Real.log (p : ℝ)) * dyadicTailRatio ^ j) :=
        mul_le_mul_of_nonneg_left hsplit hpos
    _ = 8 * |c| * (Real.log (p : ℝ) * Real.exp (-(3 / 2) * Real.log (p : ℝ))) *
          dyadicTailRatio ^ j := by ring

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators

/-! ## The total higher-power mass -/

/-- The convergent prime-power tail mass `∑_n (log n) n^(-3/2)`. -/
def primeLogTailMass : ℝ :=
  ∑' n : ℕ, Real.log (n : ℝ) * Real.exp (-(3 / 2) * Real.log (n : ℝ))

theorem summable_primeLogTailMass :
    Summable (fun n : ℕ => Real.log (n : ℝ) * Real.exp (-(3 / 2) * Real.log (n : ℝ))) := by
  have h := HTGeometry.summable_log_pow_div_nat_rpow 1 (by norm_num : (1 : ℝ) < 3 / 2)
  refine h.congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [pow_one, Real.rpow_def_of_pos hn0,
      show -(3 / 2 : ℝ) * Real.log (n : ℝ) = -(Real.log (n : ℝ) * (3 / 2)) by ring,
      Real.exp_neg, div_eq_mul_inv]

theorem primeLogTailTerm_nonneg (n : ℕ) :
    0 ≤ Real.log (n : ℝ) * Real.exp (-(3 / 2) * Real.log (n : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have := Real.log_nonneg h1
    positivity

theorem sum_primesBelow_le_primeLogTailMass (N : ℕ) :
    ∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ) * Real.exp (-(3 / 2) * Real.log (p : ℝ)) ≤
      primeLogTailMass :=
  summable_primeLogTailMass.sum_le_tsum _ (fun n _ => primeLogTailTerm_nonneg n)

theorem primeLogTailMass_nonneg : 0 ≤ primeLogTailMass :=
  tsum_nonneg primeLogTailTerm_nonneg

/-! ## The uniform tail bound -/

theorem abs_localSewingLog_sub_head_le {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : |c| ≤ 1 / 8) :
    |localSewingLog p c - localSewingLogHead p c| ≤
      8 * |c| * dyadicTailConst *
        (Real.log (p : ℝ) * Real.exp (-(3 / 2) * Real.log (p : ℝ))) := by
  have hc' : |c| < 1 / 2 := by linarith
  have hsum := hasSum_sewingSeriesTerm_tail hp hc'
  have hgeo : HasSum
      (fun j : ℕ => 8 * |c| * (Real.log (p : ℝ) * Real.exp (-(3 / 2) * Real.log (p : ℝ))) *
        dyadicTailRatio ^ j)
      (8 * |c| * (Real.log (p : ℝ) * Real.exp (-(3 / 2) * Real.log (p : ℝ))) *
        dyadicTailConst) := by
    have hg := hasSum_geometric_of_lt_one dyadicTailRatio_pos.le dyadicTailRatio_lt_one
    have := hg.mul_left
      (8 * |c| * (Real.log (p : ℝ) * Real.exp (-(3 / 2) * Real.log (p : ℝ))))
    simpa [dyadicTailConst] using this
  have hle : ∀ j : ℕ, ‖sewingSeriesTerm p c (j + 1)‖ ≤
      8 * |c| * (Real.log (p : ℝ) * Real.exp (-(3 / 2) * Real.log (p : ℝ))) *
        dyadicTailRatio ^ j := by
    intro j
    rw [Real.norm_eq_abs]
    exact abs_sewingSeriesTerm_succ_le hp hc j
  have hnorm := hsum.norm_le_of_bounded hgeo hle
  rw [Real.norm_eq_abs] at hnorm
  calc |localSewingLog p c - localSewingLogHead p c|
      ≤ 8 * |c| * (Real.log (p : ℝ) * Real.exp (-(3 / 2) * Real.log (p : ℝ))) *
          dyadicTailConst := hnorm
    _ = 8 * |c| * dyadicTailConst *
          (Real.log (p : ℝ) * Real.exp (-(3 / 2) * Real.log (p : ℝ))) := by ring

theorem abs_logReflectedSewing_sub_headSum_le {c : ℝ} (hc : |c| ≤ 1 / 8) (N : ℕ) :
    |logReflectedSewingBelow c N - ∑ p ∈ Nat.primesBelow N, localSewingLogHead p c| ≤
      8 * |c| * dyadicTailConst * primeLogTailMass := by
  have hc' : |c| < 1 / 2 := by linarith
  rw [logReflectedSewingBelow_eq_sum_localSewingLog hc' N, ← Finset.sum_sub_distrib]
  have hK : 0 ≤ 8 * |c| * dyadicTailConst := by
    have := dyadicTailConst_pos
    positivity
  calc |∑ p ∈ Nat.primesBelow N, (localSewingLog p c - localSewingLogHead p c)|
      ≤ ∑ p ∈ Nat.primesBelow N, |localSewingLog p c - localSewingLogHead p c| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Nat.primesBelow N, 8 * |c| * dyadicTailConst *
          (Real.log (p : ℝ) * Real.exp (-(3 / 2) * Real.log (p : ℝ))) :=
        Finset.sum_le_sum fun p hp =>
          abs_localSewingLog_sub_head_le (Nat.prime_of_mem_primesBelow hp) hc
    _ = 8 * |c| * dyadicTailConst *
          ∑ p ∈ Nat.primesBelow N,
            Real.log (p : ℝ) * Real.exp (-(3 / 2) * Real.log (p : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ 8 * |c| * dyadicTailConst * primeLogTailMass :=
        mul_le_mul_of_nonneg_left (sum_primesBelow_le_primeLogTailMass N) hK

/-! ## The first prime power is the Mertens window of the dyadic test -/

theorem mertensPrimeWindowBelow_dyadicSinhWindowTest (t : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    mertensPrimeWindowBelow (dyadicSinhWindowTest t) N =
      Real.log (N : ℝ) * ∑ p ∈ Nat.primesBelow N, localSewingLogHead p (t / Real.log N) := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  rw [mertensPrimeWindowBelow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesBelow hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.one_lt
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have harg : t * (Real.log (p : ℝ) / Real.log (N : ℝ)) =
      t / Real.log (N : ℝ) * Real.log (p : ℝ) := by ring
  rw [dyadicSinhWindowTest, localSewingLogHead, harg]
  field_simp

/-! ## The shrinking-window limit -/

/-- **The oriented shrinking-window profile law.**  In the critical window `c = t / log N` the
reflected Hellinger sewing cost converges to the universal oriented dyadic profile. -/
theorem tendsto_logReflectedSewing_criticalWindow (t : ℝ) :
    Tendsto (fun N : ℕ => logReflectedSewingBelow (t / Real.log N) N) atTop
      (nhds (orientedHellingerDyadicProfile t)) := by
  have hcont : ContinuousOn (dyadicSinhWindowTest t) (Icc (0 : ℝ) 1) :=
    (continuous_dyadicSinhWindowTest t).continuousOn
  have hhead := tendsto_mertensPrimeWindowBelow_div_log hcont
  have hlogtop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr : Tendsto
      (fun N : ℕ => logReflectedSewingBelow (t / Real.log N) N -
        mertensPrimeWindowBelow (dyadicSinhWindowTest t) N / Real.log N) atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ᶠ N : ℕ in atTop,
        ‖(logReflectedSewingBelow (t / Real.log N) N -
            mertensPrimeWindowBelow (dyadicSinhWindowTest t) N / Real.log N) - 0‖ ≤
          8 * |t| * dyadicTailConst * primeLogTailMass / Real.log N := by
      filter_upwards [Filter.eventually_ge_atTop 2,
        hlogtop.eventually_ge_atTop (8 * |t|)] with N hN hlog
      have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
      have hc : |t / Real.log (N : ℝ)| ≤ 1 / 8 := by
        rw [abs_div, abs_of_pos hlogN, div_le_iff₀ hlogN]
        linarith
      have hbound := abs_logReflectedSewing_sub_headSum_le hc N
      rw [sub_zero, Real.norm_eq_abs,
        mertensPrimeWindowBelow_dyadicSinhWindowTest t hN]
      rw [show Real.log (N : ℝ) *
          (∑ p ∈ Nat.primesBelow N, localSewingLogHead p (t / Real.log N)) / Real.log N =
          ∑ p ∈ Nat.primesBelow N, localSewingLogHead p (t / Real.log N) by
        field_simp]
      refine hbound.trans (le_of_eq ?_)
      rw [abs_div, abs_of_pos hlogN]
      field_simp
    refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) hb ?_
    exact Tendsto.div_atTop tendsto_const_nhds hlogtop
  have hsum := herr.add hhead
  rw [zero_add] at hsum
  refine hsum.congr fun N => ?_
  ring

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators

/-! ## The measure-valued law at every confluence order -/

/-- The complete prime-power mass of one prime at confluence order `n`. -/
def confluenceWindowMass (n p : ℕ) : ℝ :=
  ∑' k : ℕ, ((k : ℝ) + 1) ^ (n - 1) * Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ (k + 1)

/-- The first prime power of that mass. -/
def confluenceHeadMass (n p : ℕ) : ℝ := Real.log (p : ℝ) ^ n * (p : ℝ)⁻¹

/-- The fixed polynomial-geometric constant bounding all higher prime powers. -/
def confluenceTailConst (n : ℕ) : ℝ := ∑' j : ℕ, ((j : ℝ) + 2) ^ (n - 1) * (1 / 2 : ℝ) ^ j

/-- The convergent prime mass `∑_p (log p)^n p^(-2)`. -/
def primeLogPowTailMass (n : ℕ) : ℝ := ∑' p : ℕ, Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2

private theorem summable_shifted_pow_geometric (m : ℕ) {r : ℝ} (hr0 : 0 < r) (hr : r < 1) :
    Summable (fun j : ℕ => ((j : ℝ) + 2) ^ m * r ^ j) := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0.le]
  have hrne : r ≠ 0 := hr0.ne'
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) m hnorm
  have h2 := (summable_nat_add_iff 2).mpr h
  refine (h2.mul_left (r⁻¹ ^ 2)).congr fun j => ?_
  push_cast
  field_simp
  ring

theorem summable_confluenceTail (n : ℕ) :
    Summable (fun j : ℕ => ((j : ℝ) + 2) ^ (n - 1) * (1 / 2 : ℝ) ^ j) :=
  summable_shifted_pow_geometric (n - 1) (by norm_num) (by norm_num)

theorem confluenceTailConst_nonneg (n : ℕ) : 0 ≤ confluenceTailConst n :=
  tsum_nonneg fun j => by positivity

theorem summable_primeLogPowTailMass (n : ℕ) :
    Summable (fun p : ℕ => Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2) := by
  have h := HTGeometry.summable_log_pow_div_nat_rpow n (by norm_num : (1 : ℝ) < 2)
  refine h.congr fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp

theorem primeLogPowTailTerm_nonneg (n m : ℕ) :
    0 ≤ Real.log (m : ℝ) ^ n * ((m : ℝ)⁻¹) ^ 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have := Real.log_nonneg h1
    positivity

theorem primeLogPowTailMass_nonneg (n : ℕ) : 0 ≤ primeLogPowTailMass n :=
  tsum_nonneg (primeLogPowTailTerm_nonneg n)

/-! ## Head/tail split of the confluence mass -/

private theorem summable_confluenceWindowTerm {n p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ =>
      ((k : ℝ) + 1) ^ (n - 1) * Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ (k + 1)) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hr : (p : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr hp1
  have hnorm : ‖(p : ℝ)⁻¹‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) (n - 1) hnorm
  have h1 := (summable_nat_add_iff 1).mpr h
  refine (h1.mul_left (Real.log (p : ℝ) ^ n)).congr fun k => ?_
  push_cast
  ring

theorem confluenceWindowMass_nonneg {n p : ℕ} (hp : p.Prime) : 0 ≤ confluenceWindowMass n p := by
  refine tsum_nonneg fun k => ?_
  have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have := Real.log_nonneg h1
  positivity

theorem confluenceWindowMass_sub_head_le {n p : ℕ} (hp : p.Prime) :
    confluenceWindowMass n p - confluenceHeadMass n p ≤
      confluenceTailConst n * (Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    linarith
  have hinv0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  have hsummable := summable_confluenceWindowTerm (n := n) hp
  have hshift := (summable_nat_add_iff (f := fun k : ℕ =>
    ((k : ℝ) + 1) ^ (n - 1) * Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ (k + 1)) 1).mpr hsummable
  have hhead : ∑ i ∈ Finset.range 1,
      ((i : ℝ) + 1) ^ (n - 1) * Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ (i + 1) =
      confluenceHeadMass n p := by
    simp [confluenceHeadMass]
  have hsplit : confluenceWindowMass n p - confluenceHeadMass n p =
      ∑' j : ℕ, ((j : ℝ) + 2) ^ (n - 1) * Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ (j + 2) := by
    rw [confluenceWindowMass, ← hhead, ← hsummable.sum_add_tsum_nat_add 1]
    simp only [add_sub_cancel_left]
    refine tsum_congr fun j => ?_
    push_cast
    ring
  rw [hsplit]
  have hmajor : Summable (fun j : ℕ =>
      confluenceTailConst n * (Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2) * 0 + 0) := by
    simp
  have hbound : ∀ j : ℕ,
      ((j : ℝ) + 2) ^ (n - 1) * Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ (j + 2) ≤
        (Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2) *
          (((j : ℝ) + 2) ^ (n - 1) * (1 / 2 : ℝ) ^ j) := by
    intro j
    have hpow : ((p : ℝ)⁻¹) ^ (j + 2) = ((p : ℝ)⁻¹) ^ 2 * ((p : ℝ)⁻¹) ^ j := by
      rw [← pow_add]
      ring_nf
    have hgeo : ((p : ℝ)⁻¹) ^ j ≤ (1 / 2 : ℝ) ^ j := pow_le_pow_left₀ hinv0 hinv j
    rw [hpow]
    have hcoef : (0 : ℝ) ≤ ((j : ℝ) + 2) ^ (n - 1) * Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2 := by
      positivity
    calc ((j : ℝ) + 2) ^ (n - 1) * Real.log (p : ℝ) ^ n * (((p : ℝ)⁻¹) ^ 2 * ((p : ℝ)⁻¹) ^ j)
        = (((j : ℝ) + 2) ^ (n - 1) * Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2) *
            ((p : ℝ)⁻¹) ^ j := by ring
      _ ≤ (((j : ℝ) + 2) ^ (n - 1) * Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2) *
            (1 / 2 : ℝ) ^ j := mul_le_mul_of_nonneg_left hgeo hcoef
      _ = (Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2) *
            (((j : ℝ) + 2) ^ (n - 1) * (1 / 2 : ℝ) ^ j) := by ring
  have hsum2 := (summable_confluenceTail n).mul_left
    (Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2)
  have hsum1 : Summable (fun j : ℕ =>
      ((j : ℝ) + 2) ^ (n - 1) * Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ (j + 2)) :=
    hsum2.of_nonneg_of_le (fun j => by positivity) hbound
  calc (∑' j : ℕ, ((j : ℝ) + 2) ^ (n - 1) * Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ (j + 2))
      ≤ ∑' j : ℕ, (Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2) *
          (((j : ℝ) + 2) ^ (n - 1) * (1 / 2 : ℝ) ^ j) :=
        hsum1.tsum_le_tsum hbound hsum2
    _ = confluenceTailConst n * (Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2) := by
        rw [tsum_mul_left, confluenceTailConst]
        ring

theorem confluenceHeadMass_le {n p : ℕ} (hp : p.Prime) :
    confluenceHeadMass n p ≤ confluenceWindowMass n p := by
  have hsummable := summable_confluenceWindowTerm (n := n) hp
  have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hlog := Real.log_nonneg h1
  rw [confluenceWindowMass, confluenceHeadMass]
  have := hsummable.sum_le_tsum (Finset.range 1) (fun i _ => by positivity)
  simpa using this

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators

/-! ## The confluence-order window pairing -/

/-- The complete confluence-order window pairing at cutoff `N`. -/
def confluenceWindowPairing (n : ℕ) (φ : ℝ → ℝ) (N : ℕ) : ℝ :=
  2 * ((2 : ℝ) ^ n - 2) / Real.log (N : ℝ) ^ n *
    ∑ p ∈ Nat.primesBelow N, confluenceWindowMass n p * φ (Real.log p / Real.log N)

/-- Its first-prime-power part. -/
def confluenceHeadPairing (n : ℕ) (φ : ℝ → ℝ) (N : ℕ) : ℝ :=
  2 * ((2 : ℝ) ^ n - 2) / Real.log (N : ℝ) ^ n *
    ∑ p ∈ Nat.primesBelow N, confluenceHeadMass n p * φ (Real.log p / Real.log N)

theorem confluenceHeadPairing_eq {n : ℕ} (hn : 1 ≤ n) (φ : ℝ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    confluenceHeadPairing n φ N =
      2 * ((2 : ℝ) ^ n - 2) *
        (mertensPrimeWindowBelow (fun u => u ^ (n - 1) * φ u) N / Real.log N) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  simp only [Nat.add_sub_cancel]
  have key : ∑ p ∈ Nat.primesBelow N,
      confluenceHeadMass (m + 1) p * φ (Real.log p / Real.log N) =
      Real.log (N : ℝ) ^ m * mertensPrimeWindowBelow (fun u => u ^ m * φ u) N := by
    rw [mertensPrimeWindowBelow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hprime := Nat.prime_of_mem_primesBelow hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
    rw [confluenceHeadMass, div_pow]
    field_simp
    ring
  rw [confluenceHeadPairing, key]
  field_simp
  ring

theorem abs_confluenceWindowPairing_sub_head_le {n : ℕ} (hn : 1 ≤ n) {φ : ℝ → ℝ} {M : ℝ}
    (hM : ∀ u ∈ Icc (0 : ℝ) 1, |φ u| ≤ M) {N : ℕ} (hN : 2 ≤ N) :
    |confluenceWindowPairing n φ N - confluenceHeadPairing n φ N| ≤
      2 * ((2 : ℝ) ^ n - 2) / Real.log (N : ℝ) ^ n *
        (M * (confluenceTailConst n * primeLogPowTailMass n)) := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 ⟨le_rfl, by norm_num⟩)
  have hcoef : 0 ≤ 2 * ((2 : ℝ) ^ n - 2) / Real.log (N : ℝ) ^ n := by
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := by
            apply pow_le_pow_right₀ (by norm_num) hn
    have : (0 : ℝ) < Real.log (N : ℝ) ^ n := by positivity
    have h3 : (0 : ℝ) ≤ 2 * ((2 : ℝ) ^ n - 2) := by linarith
    positivity
  rw [confluenceWindowPairing, confluenceHeadPairing, ← mul_sub, ← Finset.sum_sub_distrib,
    abs_mul, abs_of_nonneg hcoef]
  refine mul_le_mul_of_nonneg_left ?_ hcoef
  have hterm : ∀ p ∈ Nat.primesBelow N,
      |confluenceWindowMass n p * φ (Real.log p / Real.log N) -
        confluenceHeadMass n p * φ (Real.log p / Real.log N)| ≤
      M * (confluenceTailConst n * (Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2)) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesBelow hp
    have hpN : p ≤ N := le_of_lt (Nat.lt_of_mem_primesBelow hp)
    have hmem := logRatio_mem_Icc hprime hpN
    have hphi := hM _ hmem
    have hdiff := confluenceWindowMass_sub_head_le (n := n) hprime
    have hdiff0 : 0 ≤ confluenceWindowMass n p - confluenceHeadMass n p :=
      sub_nonneg.mpr (confluenceHeadMass_le hprime)
    rw [← sub_mul, abs_mul, abs_of_nonneg hdiff0]
    calc (confluenceWindowMass n p - confluenceHeadMass n p) *
          |φ (Real.log p / Real.log N)|
        ≤ (confluenceTailConst n * (Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2)) * M :=
          mul_le_mul hdiff hphi (abs_nonneg _)
            (mul_nonneg (confluenceTailConst_nonneg n) (primeLogPowTailTerm_nonneg n p))
      _ = M * (confluenceTailConst n * (Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2)) := by ring
  calc |∑ p ∈ Nat.primesBelow N,
        (confluenceWindowMass n p * φ (Real.log p / Real.log N) -
          confluenceHeadMass n p * φ (Real.log p / Real.log N))|
      ≤ ∑ p ∈ Nat.primesBelow N,
          |confluenceWindowMass n p * φ (Real.log p / Real.log N) -
            confluenceHeadMass n p * φ (Real.log p / Real.log N)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Nat.primesBelow N,
          M * (confluenceTailConst n * (Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2)) :=
        Finset.sum_le_sum hterm
    _ = M * confluenceTailConst n *
          ∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ) ^ n * ((p : ℝ)⁻¹) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => by ring
    _ ≤ M * confluenceTailConst n * primeLogPowTailMass n := by
        refine mul_le_mul_of_nonneg_left
          ((summable_primeLogPowTailMass n).sum_le_tsum _
            (fun q _ => primeLogPowTailTerm_nonneg n q)) ?_
        exact mul_nonneg hM0 (confluenceTailConst_nonneg n)
    _ = M * (confluenceTailConst n * primeLogPowTailMass n) := by ring

/-- **The measure-valued confluence law.**  For every confluence order `n ≥ 1` the prime-power
window measures converge weakly to `2(2ⁿ - 2) u^(n-1) du` on the unit interval. -/
theorem tendsto_confluenceWindowPairing {n : ℕ} (hn : 1 ≤ n) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => confluenceWindowPairing n φ N) atTop
      (nhds (2 * ((2 : ℝ) ^ n - 2) * ∫ u in (0 : ℝ)..1, u ^ (n - 1) * φ u)) := by
  obtain ⟨M, hMbound⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hφ
  have hM : ∀ u ∈ Icc (0 : ℝ) 1, |φ u| ≤ M := by
    intro u hu
    simpa [Real.norm_eq_abs] using hMbound u hu
  have hψ : ContinuousOn (fun u : ℝ => u ^ (n - 1) * φ u) (Icc (0 : ℝ) 1) :=
    (continuousOn_pow _).mul hφ
  have hhead0 := tendsto_mertensPrimeWindowBelow_div_log hψ
  have hhead : Tendsto (fun N : ℕ => confluenceHeadPairing n φ N) atTop
      (nhds (2 * ((2 : ℝ) ^ n - 2) * ∫ u in (0 : ℝ)..1, u ^ (n - 1) * φ u)) := by
    refine (hhead0.const_mul (2 * ((2 : ℝ) ^ n - 2))).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    exact (confluenceHeadPairing_eq hn φ hN).symm
  have hlogtop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpowtop : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ n) atTop atTop :=
    (tendsto_pow_atTop (by omega : n ≠ 0)).comp hlogtop
  have herr : Tendsto
      (fun N : ℕ => confluenceWindowPairing n φ N - confluenceHeadPairing n φ N)
      atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ᶠ N : ℕ in atTop,
        ‖(confluenceWindowPairing n φ N - confluenceHeadPairing n φ N) - 0‖ ≤
          2 * ((2 : ℝ) ^ n - 2) * (M * (confluenceTailConst n * primeLogPowTailMass n)) /
            Real.log (N : ℝ) ^ n := by
      filter_upwards [Filter.eventually_ge_atTop 2] with N hN
      rw [sub_zero, Real.norm_eq_abs]
      have h := abs_confluenceWindowPairing_sub_head_le hn hM hN
      refine h.trans (le_of_eq ?_)
      ring
    refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) hb ?_
    exact Tendsto.div_atTop tendsto_const_nhds hpowtop
  have hsum := herr.add hhead
  rw [zero_add] at hsum
  refine hsum.congr fun N => ?_
  ring

end

end RHTower
