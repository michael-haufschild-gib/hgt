import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCayleyMobius
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The contour shift of the Cayley phase integral

The Cayley phase

`P_m(z) = exp(m·M(z))`,   `M(z) = (1 - e^{iz})/(1 + e^{iz})`,

is `2π`-periodic, holomorphic off the real axis, of modulus one on the axis, and of modulus at most
`e^{-m(e^σ-1)/(e^σ+1)}` at depth `σ`.  Against any entire `2π`-periodic amplitude `F` the rectangle
Cauchy theorem therefore moves the integration line `[-π, π]` downwards at no cost — the vertical
sides cancel by periodicity — and a dominated limit returns it to the axis.  Hence

`‖∫_{-π}^{π} F(θ)·e^{-im·tan(θ/2)} dθ‖ ≤ 2π·B·e^{-m(e^σ-1)/(e^σ+1)}`

whenever `‖F‖ ≤ B` on the strip of depth `σ`.  This is the rational hard-edge information cone: a
bounded amplitude aperture against exponential decay in the product of mass and prime logarithm.
The essential singularity of `M` at `θ = ±π` never enters the interior of any rectangle.
-/

open Complex Filter MeasureTheory Set Topology

noncomputable section

namespace RHTower

theorem im_ofReal_add_ofReal_mul_I (x d : ℝ) :
    ((x : ℂ) + ((d : ℝ) : ℂ) * Complex.I).im = d := by simp

/-- The Cayley phase of the rational hard-edge Fourier transform. -/
def routeUCayleyPhase (m : ℝ) (z : ℂ) : ℂ := Complex.exp ((m : ℂ) * routeUCayleyMobius z)

theorem norm_routeUCayleyPhase (m : ℝ) (z : ℂ) :
    ‖routeUCayleyPhase m z‖ = Real.exp (m * (routeUCayleyMobius z).re) := by
  rw [routeUCayleyPhase, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem differentiableAt_routeUCayleyMobius {z : ℂ} (hz : 1 + routeUCayleyCircle z ≠ 0) :
    DifferentiableAt ℂ routeUCayleyMobius z := by
  have hcirc : DifferentiableAt ℂ routeUCayleyCircle z := by
    have h : DifferentiableAt ℂ (fun w : ℂ => w * Complex.I) z :=
      (differentiableAt_id).mul_const _
    exact Complex.differentiableAt_exp.comp z h
  exact ((differentiableAt_const 1).sub hcirc).div ((differentiableAt_const 1).add hcirc) hz

theorem differentiableAt_routeUCayleyPhase {m : ℝ} {z : ℂ}
    (hz : 1 + routeUCayleyCircle z ≠ 0) : DifferentiableAt ℂ (routeUCayleyPhase m) z :=
  Complex.differentiableAt_exp.comp z
    ((differentiableAt_const _).mul (differentiableAt_routeUCayleyMobius hz))

theorem routeUCayleyCircle_periodic (z : ℂ) :
    routeUCayleyCircle (z + ((2 * Real.pi : ℝ) : ℂ)) = routeUCayleyCircle z := by
  rw [routeUCayleyCircle, routeUCayleyCircle, add_mul, Complex.exp_add]
  have h : ((2 * Real.pi : ℝ) : ℂ) * Complex.I = (1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem routeUCayleyPhase_periodic (m : ℝ) (z : ℂ) :
    routeUCayleyPhase m (z + ((2 * Real.pi : ℝ) : ℂ)) = routeUCayleyPhase m z := by
  rw [routeUCayleyPhase, routeUCayleyPhase, routeUCayleyMobius, routeUCayleyMobius,
    routeUCayleyCircle_periodic]

/-- On the principal interval the Cayley denominator does not vanish. -/
theorem one_add_routeUCayleyCircle_ofReal_ne_zero {x : ℝ}
    (hx : x ∈ Set.Ioo (-Real.pi) Real.pi) : 1 + routeUCayleyCircle (x : ℂ) ≠ 0 := by
  have hcos : 0 < Real.cos (x / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hre : (1 + routeUCayleyCircle (x : ℂ)).re = 1 + Real.cos x := by
    rw [routeUCayleyCircle, Complex.exp_mul_I]
    simp [Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  have hpos : 0 < 1 + Real.cos x := by
    have h := Real.cos_sq (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h
    nlinarith [hcos]
  intro h0
  rw [h0] at hre
  simp only [Complex.zero_re] at hre
  linarith

/-! ## The shift of a periodic amplitude against the Cayley phase -/

section

variable {F : ℂ → ℂ}

/-- **The rectangle shift.**  Between two depths in the open lower half plane the periodic Cayley
integral is unchanged. -/
theorem integral_cayleyPhase_shift (hF : Differentiable ℂ F)
    (hper : ∀ z : ℂ, F (z + ((2 * Real.pi : ℝ) : ℂ)) = F z) (m : ℝ) {ε σ : ℝ}
    (hε : 0 < ε) (hεσ : ε ≤ σ) :
    (∫ x in (-Real.pi)..Real.pi,
        F ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I)
          * routeUCayleyPhase m ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I))
      = ∫ x in (-Real.pi)..Real.pi,
          F ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I)
            * routeUCayleyPhase m ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) := by
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fun z => F z * routeUCayleyPhase m z)
    ((-Real.pi : ℝ) + ((-σ : ℝ) : ℂ) * Complex.I)
    ((Real.pi : ℝ) + ((-ε : ℝ) : ℂ) * Complex.I) ?_
  · have hre1 : (((-Real.pi : ℝ) : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I).re = -Real.pi := by simp
    have him1 : (((-Real.pi : ℝ) : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I).im = -σ := by simp
    have hre2 : (((Real.pi : ℝ) : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I).re = Real.pi := by simp
    have him2 : (((Real.pi : ℝ) : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I).im = -ε := by simp
    rw [hre1, him1, hre2, him2] at hrect
    have hvert : (∫ y in (-σ)..(-ε),
        F ((Real.pi : ℂ) + (y : ℂ) * Complex.I)
          * routeUCayleyPhase m ((Real.pi : ℂ) + (y : ℂ) * Complex.I))
        = ∫ y in (-σ)..(-ε),
          F (((-Real.pi : ℝ) : ℂ) + (y : ℂ) * Complex.I)
            * routeUCayleyPhase m (((-Real.pi : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      have hshift : ((Real.pi : ℂ) + (y : ℂ) * Complex.I)
          = (((-Real.pi : ℝ) : ℂ) + (y : ℂ) * Complex.I) + ((2 * Real.pi : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hshift, hper, routeUCayleyPhase_periodic]
    rw [hvert] at hrect
    simp only [smul_eq_mul] at hrect
    linear_combination hrect
  · intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (hF z).mul (differentiableAt_routeUCayleyPhase ?_)
    refine one_add_routeUCayleyCircle_ne_zero ?_
    have him : z.im ∈ Set.uIcc (-σ) (-ε) := by
      have h2 := hz.2
      simp only [Set.mem_preimage] at h2
      simpa using h2
    rw [Set.uIcc_of_le (by linarith : (-σ : ℝ) ≤ -ε)] at him
    linarith [him.2]

theorem continuous_cayleyPhase_line (hF : Differentiable ℂ F) (m : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun x : ℝ =>
      F ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I)
        * routeUCayleyPhase m ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hmapc : Continuous fun y : ℝ => ((y : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal).add continuous_const
  have hmap : ContinuousAt (fun y : ℝ => ((y : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I)) x :=
    hmapc.continuousAt
  have him : ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I).im = -ε := by simp
  have hne : 1 + routeUCayleyCircle ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) ≠ 0 :=
    one_add_routeUCayleyCircle_ne_zero (by rw [him]; linarith)
  have hphi : ContinuousAt (fun z : ℂ => F z * routeUCayleyPhase m z)
      ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) :=
    ((hF _).continuousAt).mul ((differentiableAt_routeUCayleyPhase hne).continuousAt)
  have hcomp := ContinuousAt.comp (g := fun z : ℂ => F z * routeUCayleyPhase m z)
    (f := fun y : ℝ => ((y : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I)) hphi hmap
  simpa [Function.comp_def] using hcomp

/-- **The Cayley integral is its own contour shift.**  A dominated limit returns the shifted line to
the axis. -/
theorem integral_cayleyPhase_eq_shift (hF : Differentiable ℂ F)
    (hper : ∀ z : ℂ, F (z + ((2 * Real.pi : ℝ) : ℂ)) = F z) {m σ B : ℝ}
    (hm : 0 ≤ m) (hσ : 0 < σ)
    (hB : ∀ z : ℂ, -σ ≤ z.im → z.im ≤ 0 → ‖F z‖ ≤ B) :
    (∫ x in (-Real.pi)..Real.pi, F (x : ℂ) * routeUCayleyPhase m (x : ℂ))
      = ∫ x in (-Real.pi)..Real.pi,
          F ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I)
            * routeUCayleyPhase m ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I) := by
  have hle : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simp; linarith) (by simp))
  have heps_pos : ∀ n : ℕ, 0 < σ / ((n : ℝ) + 1) := fun n => div_pos hσ (by positivity)
  have heps_le : ∀ n : ℕ, σ / ((n : ℝ) + 1) ≤ σ := by
    intro n
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    calc σ / ((n : ℝ) + 1) ≤ σ / 1 := div_le_div_of_nonneg_left hσ.le (by norm_num) hn
      _ = σ := by ring
  have hconst : ∀ n : ℕ, (∫ x in Set.Ioo (-Real.pi) Real.pi,
      F ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)
        * routeUCayleyPhase m ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I))
      = ∫ x in Set.Ioo (-Real.pi) Real.pi,
        F ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I)
          * routeUCayleyPhase m ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I) := by
    intro n
    have h := integral_cayleyPhase_shift hF hper m (heps_pos n) (heps_le n)
    rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo] at h
    exact h.symm
  have hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun x : ℝ =>
        F ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)
          * routeUCayleyPhase m ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I))
      (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) :=
    fun n => (continuous_cayleyPhase_line hF m (heps_pos n)).aestronglyMeasurable
  have hbdd : MeasureTheory.Integrable (fun _ : ℝ => B)
      (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) := by
    refine MeasureTheory.integrableOn_const ?_ (by simp)
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hbound : ∀ n : ℕ, ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioo (-Real.pi) Real.pi)),
      ‖F ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)
        * routeUCayleyPhase m ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)‖
        ≤ B := by
    intro n
    refine Filter.Eventually.of_forall fun x => ?_
    have him : ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I).im
        = -(σ / ((n : ℝ) + 1)) := im_ofReal_add_ofReal_mul_I x (-(σ / ((n : ℝ) + 1)))
    have hphase : ‖routeUCayleyPhase m
        ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
      rw [norm_routeUCayleyPhase]
      refine Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hm ?_)
      exact re_routeUCayleyMobius_nonpos (by rw [him]; linarith [heps_pos n])
    have hFb : ‖F ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)‖ ≤ B :=
      hB _ (by rw [him]; linarith [heps_le n]) (by rw [him]; linarith [heps_pos n])
    rw [norm_mul]
    calc ‖F ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)‖
        * ‖routeUCayleyPhase m ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)‖
        ≤ B * 1 := mul_le_mul hFb hphase (norm_nonneg _) hB0
      _ = B := mul_one B
  have hlim : ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioo (-Real.pi) Real.pi)), Filter.Tendsto
      (fun n : ℕ =>
        F ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)
          * routeUCayleyPhase m ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I))
      Filter.atTop (nhds (F (x : ℂ) * routeUCayleyPhase m (x : ℂ))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    have hne : 1 + routeUCayleyCircle (x : ℂ) ≠ 0 :=
      one_add_routeUCayleyCircle_ofReal_ne_zero hx
    have hphi : ContinuousAt (fun z : ℂ => F z * routeUCayleyPhase m z) ((x : ℂ)) :=
      ((hF _).continuousAt).mul ((differentiableAt_routeUCayleyPhase hne).continuousAt)
    have hbase : Filter.Tendsto (fun n : ℕ => σ / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      exact Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    have hr : Filter.Tendsto (fun n : ℕ => (-(σ / ((n : ℝ) + 1)) : ℝ))
        Filter.atTop (nhds 0) := by
      simpa using hbase.neg
    have hc : Filter.Tendsto (fun n : ℕ => ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ))
        Filter.atTop (nhds 0) := by
      have hstep := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hr
      rw [Complex.ofReal_zero] at hstep
      simpa [Function.comp_def] using hstep
    have hz : Filter.Tendsto
        (fun n : ℕ => ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)
        Filter.atTop (nhds 0) := by
      simpa using hc.mul_const Complex.I
    have harg : Filter.Tendsto
        (fun n : ℕ => ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I))
        Filter.atTop (nhds ((x : ℂ))) := by
      simpa using (tendsto_const_nhds (x := ((x : ℂ))) (f := (Filter.atTop : Filter ℕ))).add hz
    exact hphi.tendsto.comp harg
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioo (-Real.pi) Real.pi))
    (F := fun n : ℕ => fun x : ℝ =>
      F ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I)
        * routeUCayleyPhase m ((x : ℂ) + ((-(σ / ((n : ℝ) + 1)) : ℝ) : ℂ) * Complex.I))
    (f := fun x : ℝ => F (x : ℂ) * routeUCayleyPhase m (x : ℂ))
    (bound := fun _ : ℝ => B) hmeas hbdd hbound hlim
  rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine tendsto_nhds_unique hdct ?_
  exact Filter.Tendsto.congr (fun n => (hconst n).symm) tendsto_const_nhds

/-- **The Cayley information cone.**  A periodic entire amplitude bounded by `B` on the strip of
depth `σ` integrates against the Cayley phase with the exponential saving
`e^{-m(e^σ-1)/(e^σ+1)}`. -/
theorem norm_integral_cayleyPhase_le (hF : Differentiable ℂ F)
    (hper : ∀ z : ℂ, F (z + ((2 * Real.pi : ℝ) : ℂ)) = F z) {m σ B : ℝ}
    (hm : 0 ≤ m) (hσ : 0 < σ)
    (hB : ∀ z : ℂ, -σ ≤ z.im → z.im ≤ 0 → ‖F z‖ ≤ B) :
    ‖∫ x in (-Real.pi)..Real.pi, F (x : ℂ) * routeUCayleyPhase m (x : ℂ)‖
      ≤ (2 * Real.pi) * (B * Real.exp (-(m * routeUCayleyDecayRate σ))) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simp; linarith) (by simp))
  rw [integral_cayleyPhase_eq_shift hF hper hm hσ hB]
  have hpt : ∀ x : ℝ,
      ‖F ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I)
        * routeUCayleyPhase m ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I)‖
        ≤ B * Real.exp (-(m * routeUCayleyDecayRate σ)) := by
    intro x
    have him : ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I).im = -σ := by simp
    have hFb : ‖F ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I)‖ ≤ B :=
      hB _ (by rw [him]) (by rw [him]; linarith)
    have hphase : ‖routeUCayleyPhase m ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I)‖
        ≤ Real.exp (-(m * routeUCayleyDecayRate σ)) := by
      rw [norm_routeUCayleyPhase]
      refine Real.exp_le_exp.2 ?_
      have hre := re_routeUCayleyMobius_le (z := (x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I) hσ him
      nlinarith [hre, hm]
    rw [norm_mul]
    exact mul_le_mul hFb hphase (norm_nonneg _) hB0
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -Real.pi) (b := Real.pi)
    (f := fun x : ℝ => F ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I)
      * routeUCayleyPhase m ((x : ℂ) + ((-σ : ℝ) : ℂ) * Complex.I))
    (C := B * Real.exp (-(m * routeUCayleyDecayRate σ))) (fun x _ => hpt x)
  refine le_trans hbound (le_of_eq ?_)
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring, abs_of_pos (by linarith [Real.pi_pos])]
  ring

end

end RHTower

end
