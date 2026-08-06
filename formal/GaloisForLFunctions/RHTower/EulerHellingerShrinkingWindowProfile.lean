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
    have h := abs_sinh_le_abs_mul_cosh (x := 2 * v) (C := 2 * v) (le_of_eq rfl) le_rfl
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
