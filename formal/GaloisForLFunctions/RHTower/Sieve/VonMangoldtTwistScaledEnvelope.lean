import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistScaledWidth
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistPrimeEnvelope

/-!
# The Route-T twisted prime sum at a free smoothing width

Balancing the smoothing width against the contour saving inflates the height term of the twisted
prime sum by a power of the cutoff, which destroys every application in which the frequency is only
polylogarithmically large.  Keeping the width free — and taking it polylogarithmic — leaves the
height term with the pure decay `1/|τ|` at the cost of a polylogarithmic factor, which is what the
short-interval argument consumes.
-/

namespace RHTower.Sieve

open ArithmeticFunction

noncomputable section

/-- The height cost of the Route-T width, in the scaled form. -/
def scaledHeightFactor (A τ : ℝ) : ℝ :=
  1 / |τ| + Real.log (3 * |τ| / 2) / routeTZeroFreeWidth A (3 * |τ| / 2 + 1)

theorem scaledHeightFactor_nonneg {A τ : ℝ} (hτ : 1 ≤ |τ|) : 0 ≤ scaledHeightFactor A τ := by
  have hW : 0 < routeTZeroFreeWidth A (3 * |τ| / 2 + 1) := routeTZeroFreeWidth_pos _ _
  have hlog : (0 : ℝ) ≤ Real.log (3 * |τ| / 2) := Real.log_nonneg (by linarith)
  have h1 : (0 : ℝ) ≤ 1 / |τ| := by positivity
  rw [scaledHeightFactor]
  have := div_nonneg hlog hW.le
  linarith

/-- The monotone envelope of the twisted prime sum at a free smoothing width. -/
def scaledTwistEnvelope (A delta Ctot D τ x : ℝ) : ℝ :=
  Ctot * D ^ 2
      * (x * (Real.log x) ^ 2 / |τ|
        + scaledHeightFactor A τ
            * ((3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
                * x ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2))
              + x / |τ| ^ 2))
      / (2 * Real.pi)
    + Real.log (2 * x) * (x / D)
    + 2 * Real.sqrt x * Real.log x

theorem routeTUniformRegWidth_le_one {A delta τ : ℝ} :
    routeTUniformRegWidth A delta (3 * |τ| / 2) ≤ 1 := by
  have hwle : routeTUniformRegWidth A delta (3 * |τ| / 2)
      ≤ routeTZeroFreeWidth A (3 * |τ| / 2 + 1) / 2 := routeTUniformRegWidth_le_half
  have hw160 : routeTZeroFreeWidth A (3 * |τ| / 2 + 1) ≤ 1 / 160 :=
    routeTZeroFreeWidth_le_one_sixtieth _ _
  linarith

theorem scaledTwistEnvelope_nonneg {A delta Ctot D τ : ℝ} (hCtot : 0 ≤ Ctot) (hD : 0 < D)
    (hτ : 1 ≤ |τ|) {x : ℝ} (hx : 1 ≤ x) : 0 ≤ scaledTwistEnvelope A delta Ctot D τ x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hlog2x : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hH := scaledHeightFactor_nonneg (A := A) (τ := τ) hτ
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  have hr1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) :=
    Real.rpow_nonneg (by norm_num) _
  have hr2 : (0 : ℝ) ≤ x ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2)) :=
    Real.rpow_nonneg hx0.le _
  have hbracket : (0 : ℝ) ≤ x * (Real.log x) ^ 2 / |τ|
      + scaledHeightFactor A τ
          * ((3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
              * x ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2)) + x / |τ| ^ 2) := by
    have h1 : (0 : ℝ) ≤ x * (Real.log x) ^ 2 / |τ| := by positivity
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
        * x ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2)) + x / |τ| ^ 2 := by positivity
    have := mul_nonneg hH h2
    linarith
  rw [scaledTwistEnvelope]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hA : (0 : ℝ) ≤ Ctot * D ^ 2
      * (x * (Real.log x) ^ 2 / |τ|
        + scaledHeightFactor A τ
            * ((3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
                * x ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2)) + x / |τ| ^ 2))
      / (2 * Real.pi) := by
    refine div_nonneg (mul_nonneg (mul_nonneg hCtot (by positivity)) hbracket) hpi.le
  have hB : (0 : ℝ) ≤ Real.log (2 * x) * (x / D) := by positivity
  have hC : (0 : ℝ) ≤ 2 * Real.sqrt x * Real.log x := by positivity
  linarith

/-- **The scaled envelope is monotone in the cutoff.** -/
theorem scaledTwistEnvelope_mono {A delta Ctot D τ : ℝ} (hCtot : 0 ≤ Ctot) (hD : 0 < D)
    (hτ : 1 ≤ |τ|) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    scaledTwistEnvelope A delta Ctot D τ x ≤ scaledTwistEnvelope A delta Ctot D τ y := by
  have hy : (1 : ℝ) ≤ y := le_trans hx hxy
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hlogy : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy
  have hlogxy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hH := scaledHeightFactor_nonneg (A := A) (τ := τ) hτ
  have hwpos : (0 : ℝ) ≤ 1 - routeTUniformRegWidth A delta (3 * |τ| / 2) := by
    have := routeTUniformRegWidth_le_one (A := A) (delta := delta) (τ := τ)
    linarith
  have hrx : x ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2))
      ≤ y ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2)) :=
    Real.rpow_le_rpow hx0.le hxy hwpos
  have hr1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) :=
    Real.rpow_nonneg (by norm_num) _
  have hsq : (Real.log x) ^ 2 ≤ (Real.log y) ^ 2 := pow_le_pow_left₀ hlogx hlogxy 2
  have hterm1 : x * (Real.log x) ^ 2 / |τ| ≤ y * (Real.log y) ^ 2 / |τ| := by
    have hnum : x * (Real.log x) ^ 2 ≤ y * (Real.log y) ^ 2 :=
      mul_le_mul hxy hsq (by positivity) (by linarith)
    exact div_le_div_of_nonneg_right hnum hτ0.le
  have hterm2 : (3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
        * x ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2)) + x / |τ| ^ 2
      ≤ (3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
        * y ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2)) + y / |τ| ^ 2 := by
    have ha : (3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
        * x ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2))
        ≤ (3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
          * y ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2)) :=
      mul_le_mul_of_nonneg_left hrx hr1
    have hb : x / |τ| ^ 2 ≤ y / |τ| ^ 2 := div_le_div_of_nonneg_right hxy (by positivity)
    linarith
  have hbrack : x * (Real.log x) ^ 2 / |τ|
        + scaledHeightFactor A τ
            * ((3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
                * x ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2)) + x / |τ| ^ 2)
      ≤ y * (Real.log y) ^ 2 / |τ|
        + scaledHeightFactor A τ
            * ((3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
                * y ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2)) + y / |τ| ^ 2) := by
    have := mul_le_mul_of_nonneg_left hterm2 hH
    linarith
  have hmain : Ctot * D ^ 2
        * (x * (Real.log x) ^ 2 / |τ|
          + scaledHeightFactor A τ
              * ((3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
                  * x ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2)) + x / |τ| ^ 2))
        / (2 * Real.pi)
      ≤ Ctot * D ^ 2
        * (y * (Real.log y) ^ 2 / |τ|
          + scaledHeightFactor A τ
              * ((3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
                  * y ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2)) + y / |τ| ^ 2))
        / (2 * Real.pi) := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hbrack (by positivity)
  have hsecond : Real.log (2 * x) * (x / D) ≤ Real.log (2 * y) * (y / D) := by
    have hl : Real.log (2 * x) ≤ Real.log (2 * y) :=
      Real.log_le_log (by linarith) (by linarith)
    have hd : x / D ≤ y / D := div_le_div_of_nonneg_right hxy hD.le
    have hl0 : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
    have hd0 : (0 : ℝ) ≤ x / D := by positivity
    exact mul_le_mul hl hd hd0 (by linarith)
  have hthird : 2 * Real.sqrt x * Real.log x ≤ 2 * Real.sqrt y * Real.log y := by
    have hs : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
    have h := mul_le_mul hs hlogxy hlogx (Real.sqrt_nonneg y)
    linarith
  rw [scaledTwistEnvelope, scaledTwistEnvelope]
  linarith

/-- The scaled envelope, relative to the cutoff. -/
def relScaledEnvelope (A delta Ctot D τ x : ℝ) : ℝ :=
  Ctot * D ^ 2
      * ((Real.log x) ^ 2 / |τ|
        + scaledHeightFactor A τ
            * ((3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
                * x ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
              + 1 / |τ| ^ 2))
      / (2 * Real.pi)
    + Real.log (2 * x) / D
    + 2 * Real.log x / Real.sqrt x

/-- **The scaled envelope is the cutoff times its relative size.** -/
theorem scaledTwistEnvelope_eq_mul {A delta Ctot D τ x : ℝ} (hx : 0 < x) :
    scaledTwistEnvelope A delta Ctot D τ x = x * relScaledEnvelope A delta Ctot D τ x := by
  set w : ℝ := routeTUniformRegWidth A delta (3 * |τ| / 2) with hw
  have hxne : x ≠ 0 := ne_of_gt hx
  have hpow : x * x ^ (-w) = x ^ (1 - w) := by
    rw [show (1 : ℝ) - w = 1 + -w by ring, Real.rpow_add hx, Real.rpow_one]
  have hsqrt : x / Real.sqrt x = Real.sqrt x := Real.div_sqrt
  have hlast' : 2 * Real.sqrt x * Real.log x = x * (2 * Real.log x / Real.sqrt x) := by
    rw [show 2 * Real.log x / Real.sqrt x = 2 * Real.log x * (1 / Real.sqrt x) by ring]
    rw [show x * (2 * Real.log x * (1 / Real.sqrt x))
        = (x / Real.sqrt x) * (2 * Real.log x) by ring, hsqrt]
    ring
  rw [scaledTwistEnvelope, relScaledEnvelope, ← hw, ← hpow, hlast']
  ring

/-- A negative real power is an exponential of the logarithm. -/
theorem rpow_neg_le_exp_neg {x w μ q : ℝ} (hx : 1 ≤ x) (hμ0 : 0 ≤ μ) (hμ : μ ≤ w)
    (hq0 : 0 ≤ q) (hq : q ≤ Real.log x) :
    x ^ (-w) ≤ Real.exp (-(μ * q)) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hid : x ^ (-w) = Real.exp (-w * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0]
    ring_nf
  rw [hid]
  refine Real.exp_le_exp.2 ?_
  nlinarith [hμ, hμ0, hq, hq0, hlog]

set_option maxHeartbeats 1000000 in
/-- **Lemma 2.3 at a free smoothing width, prime form.**  The height term carries the pure decay
`1/|τ|` times the smoothing factor `D²`, and the desmoothing costs `K log(2K)/D`. -/
theorem exists_norm_sum_primeTwist_scaled_le :
    ∃ A delta Ctot τ₀ : ℝ, 0 < delta ∧ 0 < Ctot ∧ 2 ≤ τ₀ ∧
      ∀ (N : ℕ) (D τ : ℝ), 1 ≤ D → τ₀ ≤ |τ| →
        ‖∑ n ∈ Finset.range (N + 1), primeTwist τ n‖
          ≤ (scaledTwistEnvelope A delta Ctot D τ (max (N : ℝ) 1) + 7 * Real.exp 9)
              * (1 / Real.log 2 + 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  obtain ⟨A, Creg, delta, Ctot, τ₀, hCreg, hdelta, hCtot, hτ₀, hbound⟩ :=
    exists_norm_partialSum_vonMangoldtTwist_routeT_scaled
  refine ⟨A, delta, Ctot, τ₀, hdelta, hCtot, hτ₀, ?_⟩
  intro N D τ hD hτ
  have hτ1 : (1 : ℝ) ≤ |τ| := by linarith
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  have hD0 : (0 : ℝ) < D := by linarith
  have hexp9 : (10 : ℝ) ≤ Real.exp 9 := by
    have := Real.add_one_le_exp (9 : ℝ)
    linarith
  set w : ℝ := routeTUniformRegWidth A delta (3 * |τ| / 2) with hw
  have hdom : ∀ K : ℕ, Real.exp 9 ≤ (K : ℝ) →
      ‖∑ n ∈ Finset.range (K + 1), vonMangoldtPrimeTwist τ n‖
        ≤ scaledTwistEnvelope A delta Ctot D τ (K : ℝ) := by
    intro K hK
    have hK10 : (10 : ℝ) ≤ (K : ℝ) := le_trans hexp9 hK
    have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
    have hK1 : (1 : ℕ) ≤ K := by exact_mod_cast le_trans (by norm_num : (1:ℝ) ≤ 10) hK10
    have hpp := primePowerDefect_le hK1
    have hstep := norm_partialSum_vonMangoldtPrimeTwist_le τ K (hbound K D τ hK hD hτ)
    have hid : (K : ℝ) * ((3 * (K : ℝ)) ^ (-w)) = (3 : ℝ) ^ (-w) * (K : ℝ) ^ (1 - w) := by
      have h1 : (3 * (K : ℝ)) ^ (-w) = (3 : ℝ) ^ (-w) * (K : ℝ) ^ (-w) :=
        Real.mul_rpow (by norm_num) hK0.le
      have h2 : (K : ℝ) * (K : ℝ) ^ (-w) = (K : ℝ) ^ (1 - w) := by
        rw [show (1 : ℝ) - w = 1 + -w by ring, Real.rpow_add hK0, Real.rpow_one]
      rw [h1, ← h2]
      ring
    have hEq : Ctot * (K : ℝ) * D ^ 2
          * ((Real.log (K : ℝ)) ^ 2 / |τ|
              + (1 / |τ| + Real.log (3 * |τ| / 2)
                  / routeTZeroFreeWidth A (3 * |τ| / 2 + 1))
                * ((3 * (K : ℝ)) ^ (-w) + 1 / |τ| ^ 2))
          / (2 * Real.pi)
        = Ctot * D ^ 2
          * ((K : ℝ) * (Real.log (K : ℝ)) ^ 2 / |τ|
            + scaledHeightFactor A τ
                * ((3 : ℝ) ^ (-w) * (K : ℝ) ^ (1 - w) + (K : ℝ) / |τ| ^ 2))
          / (2 * Real.pi) := by
      rw [scaledHeightFactor, ← hid]
      ring
    rw [scaledTwistEnvelope, ← hw, ← hEq]
    linarith [hstep, hpp]
  refine norm_sum_primeTwist_le_of_monotone_bound τ N
    (fun m => scaledTwistEnvelope A delta Ctot D τ (max (m : ℝ) 1) + 7 * Real.exp 9) ?_ ?_
  · intro m _
    have hmax1 : (1 : ℝ) ≤ max (m : ℝ) 1 := le_max_right _ _
    have hnn : (0 : ℝ) ≤ scaledTwistEnvelope A delta Ctot D τ (max (m : ℝ) 1) :=
      scaledTwistEnvelope_nonneg hCtot.le hD0 hτ1 hmax1
    rcases le_or_gt (Real.exp 9) (m : ℝ) with hcase | hcase
    · have hmax : max (m : ℝ) 1 = (m : ℝ) := max_eq_left (by linarith [hexp9])
      rw [hmax]
      have hd := hdom m hcase
      have hpos : (0 : ℝ) ≤ 7 * Real.exp 9 := by positivity
      linarith
    · have hcr := norm_partialSum_vonMangoldtPrimeTwist_le_crude τ m
      have h7 : (7 : ℝ) * (m : ℝ) ≤ 7 * Real.exp 9 := by linarith
      linarith
  · intro m hm
    have hmax1 : (1 : ℝ) ≤ max (m : ℝ) 1 := le_max_right _ _
    have hmm : max (m : ℝ) 1 ≤ max (N : ℝ) 1 := by
      have hcast : ((m : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hm
      exact max_le_max hcast le_rfl
    have hmono := scaledTwistEnvelope_mono (A := A) (delta := delta) (Ctot := Ctot) (D := D)
      (τ := τ) hCtot.le hD0 hτ1 hmax1 hmm
    linarith

end

end RHTower.Sieve
