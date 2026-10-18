import GaloisForLFunctions.RHTower.ThetaJensenPolynomialWard

/-!
# Coercivity at the theta moment saddle

The global squared-height score bound controls every centered moment. Near
the saddle its coefficient improves by a factor proportional to the saddle
height. Both estimates concern the literal leading theta source.
-/

open Real Set Filter Topology

noncomputable section

namespace RHTower

theorem thetaJensenScore_eq (x : ℝ) :
    thetaJensenScore x = x * (Real.pi * Real.exp (2 * x) - 9 / 4) := by
  simp only [thetaJensenScore, thetaCuspGaussianApertureExactTailSaddleDegree, zero_mul, sub_zero]
  ring

theorem thetaJensenScore_pos {x : ℝ} (hx : 0 < x) : 0 < thetaJensenScore x := by
  have he : 1 ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
  have hpi : 9 / 4 < Real.pi * Real.exp (2 * x) := by nlinarith [Real.pi_gt_three]
  rw [thetaJensenScore_eq]
  exact mul_pos hx (sub_pos.mpr hpi)

def thetaJensenSaddle (n : ℕ) : ℝ :=
  thetaCuspGaussianApertureResponseCenteredSaddleHeight 0 (by rfl) n

theorem thetaJensenSaddle_pos (n : ℕ) : 0 < thetaJensenSaddle n :=
  thetaCuspGaussianApertureResponseCenteredSaddleHeight_pos (by rfl) n

theorem thetaJensenSaddle_score (n : ℕ) :
    thetaJensenScore (thetaJensenSaddle n) = (n : ℝ) + 1 / 2 :=
  thetaCuspGaussianApertureResponseCenteredSaddleHeight_score (by rfl) n

theorem tendsto_thetaJensenSaddle : Tendsto thetaJensenSaddle atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hcast := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  filter_upwards [hcast.eventually (eventually_ge_atTop (thetaJensenScore (max b 1) + 1))] with n hn
  by_contra hb
  have hsmall : thetaJensenSaddle n ≤ max b 1 := (lt_of_not_ge hb).le.trans (le_max_left _ _)
  have hs :=
    (thetaCuspGaussianApertureExactTailSaddleDegree_strictMonoOn_Ici_zero (by rfl)).monotoneOn
      (thetaJensenSaddle_pos n).le
      (show 0 ≤ max b 1 by linarith [le_max_right b 1]) hsmall
  change thetaJensenScore (thetaJensenSaddle n) ≤ thetaJensenScore (max b 1) at hs
  rw [thetaJensenSaddle_score] at hs
  linarith

theorem tendsto_thetaJensenSaddle_sq_div_shape :
    Tendsto (fun n : ℕ => thetaJensenSaddle n ^ 2 / ((n : ℝ) + 1 / 2)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => thetaJensenSaddle n * Real.exp (-thetaJensenSaddle n))
      atTop (𝓝 0) := by
    apply ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp tendsto_thetaJensenSaddle).congr
    intro n
    simp only [pow_one, Function.comp_apply]
  refine squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ hlim
  filter_upwards [tendsto_thetaJensenSaddle.eventually (eventually_ge_atTop 1)] with n hn
  let s := thetaJensenSaddle n
  have hs : 0 < s := thetaJensenSaddle_pos n
  have he : 3 ≤ Real.exp (2 * s) := by
    have h := Real.add_one_le_exp (2 * s)
    dsimp [s] at *
    linarith
  have hA : Real.exp (2 * s) ≤ Real.pi * Real.exp (2 * s) - 9 / 4 := by
    nlinarith [Real.pi_gt_three]
  have he' : Real.exp s ≤ Real.exp (2 * s) := Real.exp_le_exp.mpr (by linarith)
  have hden : s * Real.exp s ≤ (n : ℝ) + 1 / 2 := by
    rw [← thetaJensenSaddle_score, thetaJensenScore_eq]
    exact mul_le_mul_of_nonneg_left (he'.trans hA) hs.le
  calc
    s ^ 2 / ((n : ℝ) + 1 / 2) ≤ s ^ 2 / (s * Real.exp s) :=
      div_le_div_of_nonneg_left (sq_nonneg s) (by positivity) hden
    _ = s * Real.exp (-s) := by
      rw [Real.exp_neg]
      field_simp

/-- A global score bound whose strength grows with the moment index. -/
theorem thetaJensenScore_global_coercivity {s x : ℝ} (hs : 1 ≤ s) (hx : 0 ≤ x) :
    thetaJensenScore s * (x ^ 2 - s ^ 2) ^ 2 ≤
      2 * s ^ 2 * (x ^ 2 - s ^ 2) * (thetaJensenScore x - thetaJensenScore s) := by
  have hs0 : 0 < s := by linarith
  have hS := thetaJensenScore_pos hs0
  rcases le_total x s with hxs | hsx
  · have he : Real.exp (2 * x) ≤ Real.exp (2 * s) := Real.exp_le_exp.mpr (by linarith)
    have hlin : 0 ≤ x * thetaJensenScore s - s * thetaJensenScore x := by
      calc
        0 ≤ s * x * Real.pi * (Real.exp (2 * s) - Real.exp (2 * x)) :=
          mul_nonneg (by positivity) (sub_nonneg.mpr he)
        _ = x * thetaJensenScore s - s * thetaJensenScore x := by
          rw [thetaJensenScore_eq, thetaJensenScore_eq]
          ring
    have hgap : 0 ≤ 2 * s ^ 2 * (thetaJensenScore s - thetaJensenScore x) -
        thetaJensenScore s * (s ^ 2 - x ^ 2) := by
      calc
        0 ≤ thetaJensenScore s * (s - x) ^ 2 +
            2 * s * (x * thetaJensenScore s - s * thetaJensenScore x) := by positivity
        _ = _ := by ring
    have hD : 0 ≤ s ^ 2 - x ^ 2 := by nlinarith
    nlinarith [mul_nonneg hgap hD]
  · have he : Real.exp (2 * s) * (1 + 2 * (x - s)) ≤ Real.exp (2 * x) := by
      have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2 * (x - s)))
        (Real.exp_pos (2 * s)).le
      rw [← Real.exp_add, show 2 * s + 2 * (x - s) = 2 * x by ring] at h
      simpa only [add_comm] using h
    have hlin : 0 ≤ s * (Real.pi * Real.exp (2 * x) - 9 / 4) -
        x * (Real.pi * Real.exp (2 * s) - 9 / 4) := by
      have hprod := mul_le_mul_of_nonneg_left he (mul_nonneg Real.pi_pos.le hs0.le)
      have hpos : 0 ≤ (x - s) * (Real.pi * Real.exp (2 * s) * (2 * s - 1) + 9 / 4) := by
        apply mul_nonneg (sub_nonneg.mpr hsx)
        have : 0 ≤ 2 * s - 1 := by linarith
        positivity
      nlinarith
    have hratio : 0 ≤ s ^ 2 * thetaJensenScore x - x ^ 2 * thetaJensenScore s := by
      calc
        0 ≤ s * x *
            (s * (Real.pi * Real.exp (2 * x) - 9 / 4) -
              x * (Real.pi * Real.exp (2 * s) - 9 / 4)) := mul_nonneg (by positivity) hlin
        _ = _ := by
          rw [thetaJensenScore_eq, thetaJensenScore_eq]
          ring
    have hmono : thetaJensenScore s ≤ thetaJensenScore x :=
      (thetaCuspGaussianApertureExactTailSaddleDegree_strictMonoOn_Ici_zero (by rfl)).monotoneOn
        hs0.le hx hsx
    have hgap : 0 ≤ 2 * s ^ 2 * (thetaJensenScore x - thetaJensenScore s) -
        thetaJensenScore s * (x ^ 2 - s ^ 2) := by
      have hp := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hmono)
      nlinarith
    have hD : 0 ≤ x ^ 2 - s ^ 2 := by nlinarith
    nlinarith [mul_nonneg hgap hD]

private theorem thetaJensenScore_local_slope {s u : ℝ} (hs : 2 ≤ s)
    (hu : u ∈ Icc (s - 1) (s + 1)) :
    thetaJensenScore s ≤ Real.exp 2 * thetaCuspGaussianApertureExactTailSaddleDegreeSlope 0 u := by
  have hs0 : 0 < s := by linarith
  have hu1 : 1 ≤ u := by linarith [hu.1]
  have hu0 : 0 < u := by linarith
  have hE : Real.exp (2 * s) ≤ Real.exp 2 * Real.exp (2 * u) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hu.1])
  have hfloor : 9 / 4 ≤ Real.pi * Real.exp (2 * u) := by
    have he := Real.one_le_exp (show 0 ≤ 2 * u by linarith)
    nlinarith [Real.pi_gt_three]
  have hderiv : 2 * Real.pi * u * Real.exp (2 * u) ≤
      thetaCuspGaussianApertureExactTailSaddleDegreeSlope 0 u := by
    simp only [thetaCuspGaussianApertureExactTailSaddleDegreeSlope, mul_zero, zero_mul, sub_zero]
    nlinarith
  calc
    thetaJensenScore s ≤ Real.pi * s * Real.exp (2 * s) := by
      rw [thetaJensenScore_eq]
      nlinarith
    _ ≤ Real.pi * s * (Real.exp 2 * Real.exp (2 * u)) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ Real.exp 2 * (2 * Real.pi * u * Real.exp (2 * u)) := by
      have hsu : s ≤ 2 * u := by linarith [hu.1]
      nlinarith [mul_nonneg (sub_nonneg.mpr hsu)
        (show 0 ≤ Real.pi * Real.exp 2 * Real.exp (2 * u) by positivity)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hderiv (Real.exp_pos 2).le

/-- Inside a fixed height window, the global coercivity gains a factor of `s`. -/
theorem thetaJensenScore_local_coercivity {s x : ℝ} (hs : 2 ≤ s) (hx : |x - s| ≤ 1) :
    thetaJensenScore s * (x ^ 2 - s ^ 2) ^ 2 ≤
      8 * Real.exp 2 * s * (x ^ 2 - s ^ 2) * (thetaJensenScore x - thetaJensenScore s) := by
  let R : ℝ → ℝ := fun u => 8 * Real.exp 2 * s * thetaJensenScore u - thetaJensenScore s * u ^ 2
  have hs0 : 0 < s := by linarith
  have hS : 0 < thetaJensenScore s := thetaJensenScore_pos hs0
  have hderiv (u : ℝ) : HasDerivAt R
      (8 * Real.exp 2 * s * thetaCuspGaussianApertureExactTailSaddleDegreeSlope 0 u -
        2 * thetaJensenScore s * u) u := by
    have hSderiv : HasDerivAt thetaJensenScore
        (thetaCuspGaussianApertureExactTailSaddleDegreeSlope 0 u) u :=
      hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegree 0 u
    have h := (hSderiv.const_mul (8 * Real.exp 2 * s)).sub
      (((hasDerivAt_id u).pow 2).const_mul (thetaJensenScore s))
    exact h.congr_deriv (by simp only [id_eq, Nat.cast_ofNat, mul_one]; ring)
  have hmono : StrictMonoOn R (Icc (s - 1) (s + 1)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro u hu
      exact (hderiv u).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Icc, mem_Ioo] at hu
      rw [(hderiv u).deriv]
      have hsl := thetaJensenScore_local_slope hs ⟨hu.1.le, hu.2.le⟩
      have hm := mul_le_mul_of_nonneg_left hsl (show 0 ≤ 8 * s by positivity)
      have hp : 0 < (8 * s - 2 * u) * thetaJensenScore s := by
        apply mul_pos _ hS
        linarith [hu.2]
      nlinarith
  have hxwin : x ∈ Icc (s - 1) (s + 1) := by
    have hb := abs_le.mp hx
    constructor <;> linarith
  have hswin : s ∈ Icc (s - 1) (s + 1) := ⟨by linarith, by linarith⟩
  have hx0 : 0 < x := by linarith [hxwin.1]
  have hres : 0 ≤ (x ^ 2 - s ^ 2) * (R x - R s) := by
    rcases le_total x s with hxs | hsx
    · exact mul_nonneg_of_nonpos_of_nonpos (by nlinarith)
        (sub_nonpos.mpr (hmono.monotoneOn hxwin hswin hxs))
    · exact mul_nonneg (by nlinarith)
        (sub_nonneg.mpr (hmono.monotoneOn hswin hxwin hsx))
  dsimp only [R] at hres
  nlinarith

end RHTower
