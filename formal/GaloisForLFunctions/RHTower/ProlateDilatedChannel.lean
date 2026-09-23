import GaloisForLFunctions.RHTower.ExteriorXiPrimitive
import GaloisForLFunctions.RHTower.AmpFourthDecay
import GaloisForLFunctions.RHTower.ProlateDunsterBesselOffDiagonal

/-!
# The dilated exterior channel

The radial channels beyond the first carry the phase `xi_s(k x)` rather than `xi_s(x)`.  Written
with the frequency `c k` and the normalized phase `xi_s(k x)/k`, the dilated speed is `xi_s'(k x)`,
which is again at least one, and the reciprocal speed's variation is *improved* by the dilation: the
chain rule contributes a factor `k` while the argument `k x` contributes `k^{-2}`.

So each channel satisfies the same hypotheses as the first, with frequency `c k` in place of `c`.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- The normalized dilated phase of the `k`-th channel. -/
def dilatedPhase (s k t : ℝ) : ℝ := xiEndpointPhase s (k * t) / k

theorem hasDerivAt_dilatedPhase {s k t : ℝ} (hs0 : 0 ≤ s) (hk : 1 ≤ k) (ht : 1 < k * t) :
    HasDerivAt (dilatedPhase s k) (xiSpeed s (k * t)) t := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have h := hasDerivAt_xiEndpointPhase_dilate (s := s) (r := k) (x := t) hs0 ht
  have hval : k * Real.sqrt ((k ^ (2 : ℕ) * t ^ (2 : ℕ) - s) / (k ^ (2 : ℕ) * t ^ (2 : ℕ) - 1))
      = k * xiSpeed s (k * t) := by
    rw [xiSpeed]
    ring_nf
  rw [hval] at h
  have hdiv := h.div_const k
  have hres : k * xiSpeed s (k * t) / k = xiSpeed s (k * t) := by
    field_simp
  rwa [hres] at hdiv

theorem hasDerivAt_inv_dilatedSpeed {s k t : ℝ} (hs1 : s ≤ 1) (ht : 1 < k * t) :
    HasDerivAt (fun u : ℝ => (xiSpeed s (k * u))⁻¹) (k * xiInvSpeedDeriv s (k * t)) t := by
  have hinner : HasDerivAt (fun u : ℝ => k * u) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have h := (hasDerivAt_xiInvSpeedDeriv hs1 ht).comp t hinner
  have hval : xiInvSpeedDeriv s (k * t) * k = k * xiInvSpeedDeriv s (k * t) := by ring
  rw [hval] at h
  exact h

/-- **The dilation improves the reciprocal-speed variation.** -/
theorem abs_dilated_inv_speed_deriv_le {s k t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hk : 1 ≤ k)
    (ht : 2 ≤ t) : |k * xiInvSpeedDeriv s (k * t)| ≤ 1 / t ^ (2 : ℕ) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have ht0 : (0 : ℝ) < t := by linarith
  have hkt : (2 : ℝ) ≤ k * t := by nlinarith
  have hbase : |xiInvSpeedDeriv s (k * t)| ≤ 1 / (k * t) ^ (2 : ℕ) :=
    abs_deriv_inv_xiSpeed_le hs0 hs1 hkt
  rw [abs_mul, abs_of_pos hk0]
  have hstep : k * |xiInvSpeedDeriv s (k * t)| ≤ k * (1 / (k * t) ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hbase hk0.le
  refine le_trans hstep ?_
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hk, ht0, hk0]

/-- **The dilated exterior channel bound.**  The `k`-th channel obeys the exterior estimate with
frequency `c k`, so its primitive gains a full factor `k` over the first channel. -/
theorem norm_integral_exterior_dilated_le
    {X C c k eps s : ℝ} (hX : 2 ≤ X) (hc : 0 < c) (hk : 1 ≤ k) (heps : |eps| = 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) {a a' : ℝ → ℂ}
    (ha : ∀ x ∈ Set.uIcc (2 : ℝ) X, HasDerivAt a (a' x) x)
    (hac : ContinuousOn a (Set.uIcc (2 : ℝ) X))
    (ha'c : ContinuousOn a' (Set.uIcc (2 : ℝ) X))
    (haB : ∀ x ∈ Set.uIcc (2 : ℝ) X, ‖a x‖ ≤ C / Real.sqrt x)
    (ha'B : ∀ x ∈ Set.uIcc (2 : ℝ) X, ‖a' x‖ ≤ C / (x * Real.sqrt x)) :
    ‖∫ t in (2 : ℝ)..X, (a t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((eps * (c * k) * dilatedPhase s k t : ℝ) : ℂ))‖
      ≤ 3 * (3 * max C 1 / 2 + (max C 1) ^ (2 : ℕ) / 2) / (2 * (c * k)) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hck : (0 : ℝ) < c * k := mul_pos hc hk0
  have hx2 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (2 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  have hkx : ∀ x ∈ Set.uIcc (2 : ℝ) X, (1 : ℝ) < k * x := by
    intro x hx
    nlinarith [hx2 x hx, hk]
  have hmaps : Set.MapsTo (fun t : ℝ => k * t) (Set.uIcc (2 : ℝ) X) (Set.Ioi 1) :=
    fun x hx => hkx x hx
  have hlin : ContinuousOn (fun t : ℝ => k * t) (Set.uIcc (2 : ℝ) X) :=
    continuousOn_const.mul continuousOn_id
  have hCmax : C ≤ max C 1 := le_max_left _ _
  have hC1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
  have hC0 : (0 : ℝ) ≤ max C 1 := le_trans zero_le_one hC1
  refine _root_.RHTower.norm_integral_exterior_le (C := max C 1) hX hC0 hck heps
    (fun x hx => hasDerivAt_dilatedPhase hs0 hk (hkx x hx))
    (fun x hx => hasDerivAt_inv_dilatedSpeed (by linarith) (hkx x hx))
    ha hac ha'c
    ((continuousOn_xiSpeed s).comp hlin hmaps)
    ((continuousOn_const.mul ((continuousOn_xiInvSpeedDeriv (by linarith)).comp hlin hmaps)))
    (fun x hx => one_le_xiSpeed (by linarith) (hkx x hx)) ?_ ?_ ?_
  · intro x hx
    refine le_trans (haB x hx) ?_
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr (by linarith [hx2 x hx])
    gcongr
  · intro x hx
    refine le_trans (ha'B x hx) ?_
    have hx0 : (0 : ℝ) < x := by linarith [hx2 x hx]
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
    gcongr
  · intro x hx
    refine le_trans (abs_dilated_inv_speed_deriv_le hs0 (by linarith) hk (hx2 x hx)) ?_
    have hx0 : (0 : ℝ) < x := by linarith [hx2 x hx]
    gcongr


/-- The dilated leading amplitude carries the channel's `1/k`. -/
theorem ampFourth_dilate_le {s k x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 ≤ k)
    (hx : 2 ≤ x) : ampFourth s (k * x) ≤ 2 / (k * x) := by
  have hkx : (2 : ℝ) ≤ k * x := by nlinarith [hk, hx]
  exact ampFourth_le_two_div hs0 hs1 hkx

/-- Its derivative carries the same `1/k`, on top of the `x^{-2}` decay. -/
theorem abs_deriv_ampFourth_dilate_le {s k x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 ≤ k)
    (hx : 2 ≤ x) :
    |k * (-(2 * (k * x) * (2 * (k * x) ^ (2 : ℕ) - s - 1))
        / (4 * (((k * x) ^ (2 : ℕ) - 1) * ((k * x) ^ (2 : ℕ) - s))) * ampFourth s (k * x))|
      ≤ 32 / (k * x ^ (2 : ℕ)) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hx0 : (0 : ℝ) < x := by linarith
  have hkx : (2 : ℝ) ≤ k * x := by nlinarith [hk, hx]
  have hbase := abs_deriv_ampFourth_le hs0 hs1 hkx
  rw [abs_mul, abs_of_pos hk0]
  have hstep : k * |-(2 * (k * x) * (2 * (k * x) ^ (2 : ℕ) - s - 1))
      / (4 * (((k * x) ^ (2 : ℕ) - 1) * ((k * x) ^ (2 : ℕ) - s))) * ampFourth s (k * x)|
      ≤ k * (32 / (k * x) ^ (2 : ℕ)) := mul_le_mul_of_nonneg_left hbase hk0.le
  refine le_trans hstep (le_of_eq ?_)
  field_simp


/-- **`(16)`'s estimate: the dilated channel with the amplitude constant preserved.**  The
reciprocal-speed variation constant is `1` for every `k`, so the bound is linear in the amplitude
constant and the frequency is `c k`. -/
theorem norm_integral_exterior_dilated_sharp_le
    {X Ca c k eps s : ℝ} (hX : 2 ≤ X) (hCa : 0 ≤ Ca) (hc : 0 < c) (hk : 1 ≤ k)
    (heps : |eps| = 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) {a a' : ℝ → ℂ}
    (ha : ∀ x ∈ Set.uIcc (2 : ℝ) X, HasDerivAt a (a' x) x)
    (hac : ContinuousOn a (Set.uIcc (2 : ℝ) X))
    (ha'c : ContinuousOn a' (Set.uIcc (2 : ℝ) X))
    (haB : ∀ x ∈ Set.uIcc (2 : ℝ) X, ‖a x‖ ≤ Ca / Real.sqrt x)
    (ha'B : ∀ x ∈ Set.uIcc (2 : ℝ) X, ‖a' x‖ ≤ Ca / (x * Real.sqrt x)) :
    ‖∫ t in (2 : ℝ)..X, (a t * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((eps * (c * k) * dilatedPhase s k t : ℝ) : ℂ))‖
      ≤ 3 * Ca / (c * k) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have hck : (0 : ℝ) < c * k := mul_pos hc hk0
  have hx2 : ∀ x ∈ Set.uIcc (2 : ℝ) X, (2 : ℝ) ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hX] at hx
    exact hx.1
  have hkx : ∀ x ∈ Set.uIcc (2 : ℝ) X, (1 : ℝ) < k * x := by
    intro x hx
    nlinarith [hx2 x hx, hk]
  have hmaps : Set.MapsTo (fun t : ℝ => k * t) (Set.uIcc (2 : ℝ) X) (Set.Ioi 1) :=
    fun x hx => hkx x hx
  have hlin : ContinuousOn (fun t : ℝ => k * t) (Set.uIcc (2 : ℝ) X) :=
    continuousOn_const.mul continuousOn_id
  have hmain := _root_.RHTower.norm_integral_exterior_two_const_le (Ca := Ca) (Cr := 1)
    hX hCa zero_le_one hck heps
    (fun x hx => hasDerivAt_dilatedPhase hs0 hk (hkx x hx))
    (fun x hx => hasDerivAt_inv_dilatedSpeed (by linarith) (hkx x hx))
    ha hac ha'c
    ((continuousOn_xiSpeed s).comp hlin hmaps)
    ((continuousOn_const.mul ((continuousOn_xiInvSpeedDeriv (by linarith)).comp hlin hmaps)))
    (fun x hx => one_le_xiSpeed (by linarith) (hkx x hx)) haB ha'B
    (fun x hx => by
      refine le_trans (abs_dilated_inv_speed_deriv_le hs0 (by linarith) hk (hx2 x hx)) ?_
      have hx0 : (0 : ℝ) < x := by linarith [hx2 x hx]
      exact le_of_eq (by field_simp))
  refine le_trans hmain (le_of_eq ?_)
  field_simp
  ring


/-- The concrete leading amplitude of the `k`-th channel, in the normalization the exterior estimate
uses. -/
def leadingAmp (s k t : ℝ) : ℝ :=
  Real.sqrt t * (Real.sqrt (2 / Real.pi) * ampFourth s (k * t))

/-- Its derivative. -/
def leadingAmpDeriv (s k t : ℝ) : ℝ :=
  1 / (2 * Real.sqrt t) * (Real.sqrt (2 / Real.pi) * ampFourth s (k * t))
    + Real.sqrt t * (Real.sqrt (2 / Real.pi) *
        (k * (-(2 * (k * t) * (2 * (k * t) ^ (2 : ℕ) - s - 1))
            / (4 * (((k * t) ^ (2 : ℕ) - 1) * ((k * t) ^ (2 : ℕ) - s))) * ampFourth s (k * t))))

theorem sqrt_two_div_pi_le_one : Real.sqrt (2 / Real.pi) ≤ 1 := by
  refine Real.sqrt_le_one.mpr ?_
  rw [div_le_one Real.pi_pos]
  linarith [Real.pi_gt_three]

theorem hasDerivAt_leadingAmp {s k t : ℝ} (hs1 : s ≤ 1 / 2) (hk : 1 ≤ k) (ht : 2 ≤ t) :
    HasDerivAt (leadingAmp s k) (leadingAmpDeriv s k t) t := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have ht0 : (0 : ℝ) < t := by linarith
  have hkt : (1 : ℝ) < k * t := by nlinarith [hk, ht]
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt t)) t := Real.hasDerivAt_sqrt (ne_of_gt ht0)
  have hlin : HasDerivAt (fun u : ℝ => k * u) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have hamp : HasDerivAt (fun u : ℝ => ampFourth s (k * u))
      (k * (-(2 * (k * t) * (2 * (k * t) ^ (2 : ℕ) - s - 1))
        / (4 * (((k * t) ^ (2 : ℕ) - 1) * ((k * t) ^ (2 : ℕ) - s))) * ampFourth s (k * t))) t := by
    have h := (hasDerivAt_ampFourth hs1 hkt).comp t hlin
    have hv : -(2 * (k * t) * (2 * (k * t) ^ (2 : ℕ) - s - 1))
        / (4 * (((k * t) ^ (2 : ℕ) - 1) * ((k * t) ^ (2 : ℕ) - s))) * ampFourth s (k * t) * k
        = k * (-(2 * (k * t) * (2 * (k * t) ^ (2 : ℕ) - s - 1))
          / (4 * (((k * t) ^ (2 : ℕ) - 1) * ((k * t) ^ (2 : ℕ) - s))) * ampFourth s (k * t)) := by ring
    rwa [hv] at h
  exact hsq.mul (hamp.const_mul (Real.sqrt (2 / Real.pi)))

theorem abs_leadingAmp_le {s k t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 ≤ k)
    (ht : 2 ≤ t) : ‖((leadingAmp s k t : ℝ) : ℂ)‖ ≤ 2 / k / Real.sqrt t := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have ht0 : (0 : ℝ) < t := by linarith
  have hst : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have hkt : (1 : ℝ) < k * t := by nlinarith [hk, ht]
  have hamp := ampFourth_dilate_le hs0 hs1 hk ht
  have hamp0 : (0 : ℝ) < ampFourth s (k * t) := ampFourth_pos hs1 hkt
  have hc1 := sqrt_two_div_pi_le_one
  have hc0 : (0 : ℝ) ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  rw [Complex.norm_real, Real.norm_eq_abs, leadingAmp,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt t *
      (Real.sqrt (2 / Real.pi) * ampFourth s (k * t)))]
  have hstep : Real.sqrt t * (Real.sqrt (2 / Real.pi) * ampFourth s (k * t))
      ≤ Real.sqrt t * (1 * (2 / (k * t))) := by
    refine mul_le_mul_of_nonneg_left ?_ hst.le
    exact mul_le_mul hc1 hamp hamp0.le zero_le_one
  refine le_trans hstep (le_of_eq ?_)
  field_simp
  linarith [hss]


theorem abs_leadingAmpDeriv_le {s k t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hk : 1 ≤ k)
    (ht : 2 ≤ t) : ‖((leadingAmpDeriv s k t : ℝ) : ℂ)‖ ≤ 33 / k / (t * Real.sqrt t) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have ht0 : (0 : ℝ) < t := by linarith
  have hst : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have hsq2 : Real.sqrt t ^ (2 : ℕ) = t := Real.sq_sqrt ht0.le
  have hkt : (1 : ℝ) < k * t := by nlinarith [hk, ht]
  have hamp := ampFourth_dilate_le hs0 hs1 hk ht
  have hamp0 : (0 : ℝ) < ampFourth s (k * t) := ampFourth_pos hs1 hkt
  have hder := abs_deriv_ampFourth_dilate_le hs0 hs1 hk ht
  have hc1 := sqrt_two_div_pi_le_one
  have hc0 : (0 : ℝ) ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  rw [Complex.norm_real, Real.norm_eq_abs, leadingAmpDeriv]
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |1 / (2 * Real.sqrt t) * (Real.sqrt (2 / Real.pi) * ampFourth s (k * t))|
      ≤ 1 / k / (t * Real.sqrt t) := by
    rw [abs_of_nonneg (by positivity)]
    have hstep : 1 / (2 * Real.sqrt t) * (Real.sqrt (2 / Real.pi) * ampFourth s (k * t))
        ≤ 1 / (2 * Real.sqrt t) * (1 * (2 / (k * t))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul hc1 hamp hamp0.le zero_le_one
    refine le_trans hstep (le_of_eq ?_)
    field_simp
  have h2 : |Real.sqrt t * (Real.sqrt (2 / Real.pi) *
        (k * (-(2 * (k * t) * (2 * (k * t) ^ (2 : ℕ) - s - 1))
          / (4 * (((k * t) ^ (2 : ℕ) - 1) * ((k * t) ^ (2 : ℕ) - s))) * ampFourth s (k * t))))|
      ≤ 32 / k / (t * Real.sqrt t) := by
    rw [abs_mul, abs_of_pos hst, abs_mul, abs_of_nonneg hc0]
    have hstep : Real.sqrt t * (Real.sqrt (2 / Real.pi) *
        |k * (-(2 * (k * t) * (2 * (k * t) ^ (2 : ℕ) - s - 1))
          / (4 * (((k * t) ^ (2 : ℕ) - 1) * ((k * t) ^ (2 : ℕ) - s))) * ampFourth s (k * t))|)
        ≤ Real.sqrt t * (1 * (32 / (k * t ^ (2 : ℕ)))) := by
      refine mul_le_mul_of_nonneg_left ?_ hst.le
      exact mul_le_mul hc1 hder (abs_nonneg _) zero_le_one
    refine le_trans hstep (le_of_eq ?_)
    field_simp
    linear_combination hsq2
  have hsum : 1 / k / (t * Real.sqrt t) + 32 / k / (t * Real.sqrt t)
      = 33 / k / (t * Real.sqrt t) := by
    field_simp
    ring
  linarith [h1, h2, hsum]


theorem continuousOn_ampFourth_comp {s k X : ℝ} (hs1 : s ≤ 1 / 2) (hk : 1 ≤ k) (hX : 2 ≤ X) :
    ContinuousOn (fun t : ℝ => ampFourth s (k * t)) (Set.uIcc (2 : ℝ) X) := by
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := by
    rw [Set.uIcc_of_le hX] at ht
    exact ht.1
  have hkt : (1 : ℝ) < k * t := by nlinarith [hk, ht2]
  have hlin : HasDerivAt (fun u : ℝ => k * u) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  exact (((hasDerivAt_ampFourth hs1 hkt).comp t hlin).continuousAt).continuousWithinAt

theorem continuousOn_leadingAmpDeriv {s k X : ℝ} (hs1 : s ≤ 1 / 2) (hk : 1 ≤ k) (hX : 2 ≤ X) :
    ContinuousOn (leadingAmpDeriv s k) (Set.uIcc (2 : ℝ) X) := by
  intro t ht
  have ht2 : (2 : ℝ) ≤ t := by
    rw [Set.uIcc_of_le hX] at ht
    exact ht.1
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have ht0 : (0 : ℝ) < t := by linarith
  have hkt : (1 : ℝ) < k * t := by nlinarith [hk, ht2]
  have hlin : HasDerivAt (fun u : ℝ => k * u) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have hamp : ContinuousAt (fun u : ℝ => ampFourth s (k * u)) t :=
    ((hasDerivAt_ampFourth hs1 hkt).comp t hlin).continuousAt
  have hsq : ContinuousAt (fun u : ℝ => 1 / (2 * Real.sqrt u)) t := by
    have hs : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
    exact ContinuousAt.div continuousAt_const
      (continuousAt_const.mul (Real.continuous_sqrt.continuousAt)) (by positivity)
  have hsq2 : ContinuousAt Real.sqrt t := Real.continuous_sqrt.continuousAt
  have hd1 : (0 : ℝ) < (k * t) ^ (2 : ℕ) - 1 := by nlinarith [hkt]
  have hd2 : (0 : ℝ) < (k * t) ^ (2 : ℕ) - s := by nlinarith [hkt, hs1]
  have hrat : ContinuousAt (fun u : ℝ =>
      -(2 * (k * u) * (2 * (k * u) ^ (2 : ℕ) - s - 1))
        / (4 * (((k * u) ^ (2 : ℕ) - 1) * ((k * u) ^ (2 : ℕ) - s)))) t := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    positivity
  exact (((hsq.mul (continuousAt_const.mul hamp)).add
    (hsq2.mul (continuousAt_const.mul
      (continuousAt_const.mul (hrat.mul hamp))))).continuousWithinAt)

/-- **`(16)`: the `k`-th channel's exterior primitive.**  Everything is concrete: the amplitude is
the leading Liouville–Green amplitude of the channel, the phase is the dilated exterior phase, and
the bound carries an explicit constant with the full `k^{-2}`. -/
theorem norm_integral_leading_channel_le {s c k X eps : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hk : 1 ≤ k) (heps : |eps| = 1) (hX : 2 ≤ X) :
    ‖∫ t in (2 : ℝ)..X, (((leadingAmp s k t : ℝ) : ℂ) * (((Real.sqrt t)⁻¹ : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((eps * (c * k) * dilatedPhase s k t : ℝ) : ℂ))‖
      ≤ 99 / (c * k ^ (2 : ℕ)) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk
  have ht2 : ∀ t ∈ Set.uIcc (2 : ℝ) X, (2 : ℝ) ≤ t := by
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    exact ht.1
  have hCa : (0 : ℝ) ≤ 33 / k := by positivity
  have hac : ContinuousOn (fun t : ℝ => ((leadingAmp s k t : ℝ) : ℂ)) (Set.uIcc (2 : ℝ) X) := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    intro t ht
    exact ((hasDerivAt_leadingAmp hs1 hk (ht2 t ht)).continuousAt).continuousWithinAt
  have ha'c : ContinuousOn (fun t : ℝ => ((leadingAmpDeriv s k t : ℝ) : ℂ))
      (Set.uIcc (2 : ℝ) X) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_leadingAmpDeriv hs1 hk hX)
  have hmain := norm_integral_exterior_dilated_sharp_le (Ca := 33 / k)
    (a := fun t : ℝ => ((leadingAmp s k t : ℝ) : ℂ))
    (a' := fun t : ℝ => ((leadingAmpDeriv s k t : ℝ) : ℂ))
    hX hCa hc hk heps hs0 hs1
    (fun t ht => ((hasDerivAt_leadingAmp hs1 hk (ht2 t ht)).ofReal_comp))
    hac ha'c
    (fun t ht => by
      refine le_trans (abs_leadingAmp_le hs0 hs1 hk (ht2 t ht)) ?_
      have hst : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr (by linarith [ht2 t ht])
      gcongr
      linarith)
    (fun t ht => by
      refine le_trans (abs_leadingAmpDeriv_le hs0 hs1 hk (ht2 t ht)) ?_
      have ht0 : (0 : ℝ) < t := by linarith [ht2 t ht]
      have hst : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
      gcongr)
  refine le_trans hmain (le_of_eq ?_)
  field_simp
  ring


/-- **The corpus's leading-form bridge dilates.**  The bridge is pointwise in its argument, so
substituting `k t` gives the `k`-th channel's leading form with no new hypothesis beyond
`a <= k t`. -/
theorem abs_radialProlateBesselProfile_dilate_sub_leading_le
    {s c k a t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (ha : 1 < a)
    (hat : a ≤ k * t) (hcxi : 1 ≤ c * xiEndpointPhase s a) :
    |radialProlateBesselProfile s c (k * t) -
        Real.sqrt (2 / Real.pi) * ampFourth s (k * t) *
          Real.cos (c * xiEndpointPhase s (k * t) - Real.pi / 4)|
      ≤ compactBesselProfileError s c a :=
  abs_radialProlateBesselProfile_sub_leading_le hs0 hs1 hc ha hat hcxi


end GaloisForLFunctions.RHTower
