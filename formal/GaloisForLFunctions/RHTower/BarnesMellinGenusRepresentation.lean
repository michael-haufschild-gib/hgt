import GaloisForLFunctions.HTGeometry.BarnesKernelMellin
import GaloisForLFunctions.RHTower.BarnesMellinRemainder
import Mathlib.Analysis.MellinInversion

/-!
# The Mellin representation at arbitrary genus

The model factor of a genus-`g` canonical product is `t ↦ t^{g+1}/(1+t)`, whose Mellin transform is
the reflection kernel translated by `g+1`:

```text
mellin (barnesModel g) w = (-1)^g · (-π / sin (π w)) ,   -(g+1) < Re w < -g .
```

The parity sign cancels against the sign `(-1)^g` carried by the logarithmic derivative of the
Weierstrass factor of genus `g`, so summing the inverted transform over the scales `n^s` produces
the *same* integrand

```text
F(w) = x^{-w} ζ(-sw) (-π / sin (π w))
```

as at genus zero, only on the strip `-(g+1) < σ < -g` instead of `-1 < σ < 0`.  The Dirichlet
series converges there because `σ < -1/s`, and `-1/s` lies in that strip whenever `g = ⌊1/s⌋`.
-/

open Complex Filter Set MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {g : ℕ}

/-! ### The transform of the model factor -/

/-- An abscissa strictly between two consecutive integers is off the zeros of the sine. -/
theorem sin_pi_ne_zero_of_mem_gap {σ : ℝ} {n : ℤ} (h1 : (n : ℝ) < σ) (h2 : σ < (n : ℝ) + 1) :
    Real.sin (Real.pi * σ) ≠ 0 := by
  intro hcon
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hcon
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hval : (k : ℝ) = σ := by
    have hmul : (k : ℝ) * Real.pi = σ * Real.pi := by rw [hk]; ring
    exact mul_right_cancel₀ hpi hmul
  rw [← hval] at h1 h2
  have h1' : ((n : ℤ) : ℝ) < ((k : ℤ) : ℝ) := h1
  have h2' : ((k : ℤ) : ℝ) < ((n + 1 : ℤ) : ℝ) := by push_cast; linarith
  have hz1 : n < k := by exact_mod_cast h1'
  have hz2 : k < n + 1 := by exact_mod_cast h2'
  omega

/-- The genus strip lies between the integers `-(g+1)` and `-g`. -/
theorem sin_pi_ne_zero_of_genus_strip {σ : ℝ} (h1 : -((g : ℝ) + 1) < σ) (h2 : σ < -(g : ℝ)) :
    Real.sin (Real.pi * σ) ≠ 0 :=
  sin_pi_ne_zero_of_mem_gap (n := -(g : ℤ) - 1) (by push_cast; linarith)
    (by push_cast; linarith)

/-- **The transform of the model factor is the reflection kernel with the genus parity.** -/
theorem mellin_barnesModel_eq {w : ℂ} (h1 : -((g : ℝ) + 1) < w.re) (h2 : w.re < -(g : ℝ)) :
    mellin (barnesModel g) w
      = ((-1) ^ g : ℂ) * -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w)) := by
  have hre : (w + ((g + 1 : ℕ) : ℂ)).re = w.re + ((g : ℝ) + 1) := by
    push_cast
    simp
  have hw0 : 0 < (w + ((g + 1 : ℕ) : ℂ)).re := by rw [hre]; linarith
  have hw1 : (w + ((g + 1 : ℕ) : ℂ)).re < 1 := by rw [hre]; linarith
  rw [mellin_barnesModel g hw0 hw1, sin_pi_mul_add_nat w (g + 1)]
  have hpar : ((-1 : ℂ)) ^ (g + 1) = -((-1 : ℂ)) ^ g := by rw [pow_succ]; ring
  rw [hpar]
  set S := Complex.sin ((Real.pi : ℂ) * w) with hS
  set e : ℂ := ((-1 : ℂ)) ^ g with he
  have hee : e * e = 1 := by
    rw [he, ← pow_add, ← two_mul, pow_mul]
    norm_num
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  rw [div_eq_mul_inv, mul_inv, inv_neg, heinv, div_eq_mul_inv]
  ring

/-! ### The inverse transform of the model factor -/

theorem continuous_reflection_vertical_genus {σ : ℝ} (h1 : -((g : ℝ) + 1) < σ)
    (h2 : σ < -(g : ℝ)) :
    Continuous fun y : ℝ => mellin (barnesModel g) ((σ : ℂ) + (y : ℂ) * I) := by
  have hsin : Real.sin (Real.pi * σ) ≠ 0 := sin_pi_ne_zero_of_genus_strip h1 h2
  have hrw : (fun y : ℝ => mellin (barnesModel g) ((σ : ℂ) + (y : ℂ) * I))
      = fun y : ℝ => ((-1) ^ g : ℂ)
        * -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (y : ℂ) * I))) := by
    funext y
    have hre : ((σ : ℂ) + (y : ℂ) * I).re = σ := by simp
    exact mellin_barnesModel_eq (by rw [hre]; exact h1) (by rw [hre]; exact h2)
  rw [hrw]
  exact continuous_const.mul (continuous_reflectionKernel_vertical hsin)

/-- The transform of the model factor is integrable on every line of its strip. -/
theorem verticalIntegrable_mellin_barnesModel {σ : ℝ} (h1 : -((g : ℝ) + 1) < σ)
    (h2 : σ < -(g : ℝ)) :
    Complex.VerticalIntegrable (mellin (barnesModel g)) σ := by
  have hsin : Real.sin (Real.pi * σ) ≠ 0 := sin_pi_ne_zero_of_genus_strip h1 h2
  have hbase : Complex.VerticalIntegrable
      (fun w : ℂ => -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w))) σ :=
    verticalIntegrable_reflectionKernel hsin
  rw [Complex.VerticalIntegrable] at hbase ⊢
  refine (hbase.const_mul ((-1) ^ g : ℂ)).congr (Filter.Eventually.of_forall fun y => ?_)
  have hre : ((σ : ℂ) + (y : ℂ) * I).re = σ := by simp
  exact (mellin_barnesModel_eq (by rw [hre]; exact h1) (by rw [hre]; exact h2)).symm

/-- **The Mellin representation of the model factor.** -/
theorem mellinInv_mellin_barnesModel {σ : ℝ} (h1 : -((g : ℝ) + 1) < σ) (h2 : σ < -(g : ℝ))
    {r : ℝ} (hr : 0 < r) :
    mellinInv σ (mellin (barnesModel g)) r = barnesModel g r := by
  refine mellinInv_mellin_eq σ (barnesModel g) hr ?_
    (verticalIntegrable_mellin_barnesModel h1 h2) ?_
  · exact mellinConvergent_barnesModel (by simpa using h1) (by simpa using h2)
  · exact continuousOn_barnesModel.continuousAt (isOpen_Ioi.mem_nhds hr)

/-! ### The envelope of the inverse-transform integrand -/

/-- A uniform envelope for the inverse-Mellin integrand of the model factor. -/
theorem norm_barnesModelInv_integrand_le {σ : ℝ} (h1 : -((g : ℝ) + 1) < σ) (h2 : σ < -(g : ℝ))
    {r : ℝ} (hr : 0 < r) (y : ℝ) :
    ‖((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * I))
        * mellin (barnesModel g) ((σ : ℂ) + (y : ℂ) * I)‖
      ≤ (r ^ (-σ) * (Real.pi * max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32)) * (1 + y ^ 2)⁻¹ := by
  have hsin : Real.sin (Real.pi * σ) ≠ 0 := sin_pi_ne_zero_of_genus_strip h1 h2
  have hre : ((σ : ℂ) + (y : ℂ) * I).re = σ := by simp
  have hpow : ‖((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * I))‖ = r ^ (-σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
    congr 1
    rw [Complex.neg_re, hre]
  have hmel := mellin_barnesModel_eq (g := g) (w := (σ : ℂ) + (y : ℂ) * I)
    (by rw [hre]; exact h1) (by rw [hre]; exact h2)
  have hsign : ‖((-1) ^ g : ℂ)‖ = 1 := by
    rw [norm_pow, norm_neg, norm_one, one_pow]
  have hker : ‖-((Real.pi : ℂ)
      / Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (y : ℂ) * I)))‖
      ≤ Real.pi * (max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32 * (1 + y ^ 2)⁻¹) := by
    have hnorm : ‖-((Real.pi : ℂ)
        / Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (y : ℂ) * I)))‖
        = Real.pi * ‖(Complex.sin ((Real.pi : ℂ)
            * ((σ : ℂ) + (y : ℂ) * I)))⁻¹‖ := by
      rw [norm_neg, div_eq_mul_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (norm_inv_sin_vertical_le hsin y) (le_of_lt Real.pi_pos)
  rw [norm_mul, hpow, hmel, norm_mul, hsign, one_mul]
  have hrnn : (0 : ℝ) ≤ r ^ (-σ) := le_of_lt (Real.rpow_pos_of_pos hr _)
  calc r ^ (-σ) * ‖-((Real.pi : ℂ)
        / Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + (y : ℂ) * I)))‖
      ≤ r ^ (-σ) * (Real.pi * (max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32 * (1 + y ^ 2)⁻¹)) :=
        mul_le_mul_of_nonneg_left hker hrnn
    _ = (r ^ (-σ) * (Real.pi * max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32)) * (1 + y ^ 2)⁻¹ := by
        ring

theorem continuous_barnesModelInv_integrand {σ : ℝ} (h1 : -((g : ℝ) + 1) < σ) (h2 : σ < -(g : ℝ))
    {r : ℝ} (hr : 0 < r) :
    Continuous fun y : ℝ => ((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * I))
      * mellin (barnesModel g) ((σ : ℂ) + (y : ℂ) * I) := by
  have hline : Continuous fun y : ℝ => ((σ : ℂ) + (y : ℂ) * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hcpow : Continuous fun y : ℝ => ((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * I)) := by
    refine Continuous.const_cpow hline.neg (Or.inl ?_)
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  exact hcpow.mul (continuous_reflection_vertical_genus h1 h2)

theorem integrable_barnesModelInv_integrand {σ : ℝ} (h1 : -((g : ℝ) + 1) < σ) (h2 : σ < -(g : ℝ))
    {r : ℝ} (hr : 0 < r) :
    MeasureTheory.Integrable fun y : ℝ => ((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * I))
      * mellin (barnesModel g) ((σ : ℂ) + (y : ℂ) * I) := by
  refine MeasureTheory.Integrable.mono'
    (g := fun y : ℝ =>
      (r ^ (-σ) * (Real.pi * max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32)) * (1 + y ^ 2)⁻¹) ?_ ?_ ?_
  · exact (integrable_inv_one_add_sq).const_mul _
  · exact (continuous_barnesModelInv_integrand h1 h2 hr).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => norm_barnesModelInv_integrand_le h1 h2 hr y

theorem integral_norm_barnesModelInv_integrand_le {σ : ℝ} (h1 : -((g : ℝ) + 1) < σ)
    (h2 : σ < -(g : ℝ)) {r : ℝ} (hr : 0 < r) :
    (∫ y : ℝ, ‖((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * I))
        * mellin (barnesModel g) ((σ : ℂ) + (y : ℂ) * I)‖)
      ≤ (r ^ (-σ) * (Real.pi * max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32))
        * ∫ y : ℝ, (1 + y ^ 2)⁻¹ := by
  have hint := (integrable_barnesModelInv_integrand h1 h2 hr).norm
  have henv : MeasureTheory.Integrable
      fun y : ℝ => (r ^ (-σ) * (Real.pi * max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32))
        * (1 + y ^ 2)⁻¹ := (integrable_inv_one_add_sq).const_mul _
  have hmono := MeasureTheory.integral_mono hint henv
    (fun y => norm_barnesModelInv_integrand_le h1 h2 hr y)
  rw [MeasureTheory.integral_const_mul] at hmono
  exact hmono

/-! ### The vertical integral of a single scaled term -/

/-- The vertical integral of the scaled integrand is `2π` times the model factor. -/
theorem integral_barnesModelInv_integrand_eq {σ : ℝ} (h1 : -((g : ℝ) + 1) < σ) (h2 : σ < -(g : ℝ))
    {r : ℝ} (hr : 0 < r) :
    (∫ y : ℝ, ((r : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * I))
        * mellin (barnesModel g) ((σ : ℂ) + (y : ℂ) * I))
      = (2 * Real.pi : ℝ) • barnesModel g r := by
  have h := mellinInv_mellin_barnesModel h1 h2 hr
  rw [mellinInv] at h
  have hsmul := congrArg (fun z : ℂ => (2 * Real.pi : ℝ) • z) h
  simp only [smul_smul] at hsmul
  rw [show (2 * Real.pi : ℝ) * (1 / (2 * Real.pi)) = 1 by field_simp, one_smul] at hsmul
  rw [← hsmul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul]

/-! ### Summing over the scales -/

/-- **The second hypothesis of the interchange.**  The integrals of the norms of the scaled
integrands are summable on the strip, because `s σ < -1`. -/
theorem summable_integral_norm_barnesModelInv {s σ : ℝ} (h1 : -((g : ℝ) + 1) < σ)
    (h2 : σ < -(g : ℝ)) (hsσ : s * σ < -1) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ =>
      ∫ y : ℝ, ‖((((x / ((n : ℝ) + 1) ^ s) : ℝ) : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * I))
        * mellin (barnesModel g) ((σ : ℂ) + (y : ℂ) * I)‖ := by
  classical
  set K : ℝ := (Real.pi * max (2 * |Real.sin (Real.pi * σ)|⁻¹) 32)
    * ∫ y : ℝ, (1 + y ^ 2)⁻¹ with hK
  have hpos : ∀ n : ℕ, (0 : ℝ) < x / ((n : ℝ) + 1) ^ s := by
    intro n
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact div_pos hx (Real.rpow_pos_of_pos hnpos s)
  have hinj : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b h
    simpa using h
  have hshift : Summable fun n : ℕ => (x ^ (-σ) * K) * ((n : ℝ) + 1) ^ (s * σ) := by
    have hbase := (summable_scaledEnvelope (s := s) (σ := σ) hsσ (x ^ (-σ) * K)).comp_injective hinj
    refine hbase.congr fun n => ?_
    simp only [Function.comp_apply]
    push_cast
    ring_nf
  have hmaj : Summable fun n : ℕ => (x / ((n : ℝ) + 1) ^ s) ^ (-σ) * K := by
    refine hshift.congr fun n => ?_
    have hnpos : (0 : ℕ) < n + 1 := Nat.succ_pos n
    have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, rpow_scaled_eq hx hnpos]
    ring
  refine Summable.of_nonneg_of_le
    (fun n => MeasureTheory.integral_nonneg fun y => norm_nonneg _) (fun n => ?_) hmaj
  refine le_trans (integral_norm_barnesModelInv_integrand_le h1 h2 (hpos n)) (le_of_eq ?_)
  rw [hK]
  ring

/-- **The sum over the scales passes inside the vertical integral.** -/
theorem hasSum_integral_barnesModelInv_scaled {s σ : ℝ} (h1 : -((g : ℝ) + 1) < σ)
    (h2 : σ < -(g : ℝ)) (hsσ : s * σ < -1) {x : ℝ} (hx : 0 < x) :
    HasSum
      (fun n : ℕ => ∫ y : ℝ, ((((x / ((n : ℝ) + 1) ^ s) : ℝ) : ℂ))
          ^ (-((σ : ℂ) + (y : ℂ) * I))
        * mellin (barnesModel g) ((σ : ℂ) + (y : ℂ) * I))
      (∫ y : ℝ, ∑' n : ℕ, ((((x / ((n : ℝ) + 1) ^ s) : ℝ) : ℂ))
          ^ (-((σ : ℂ) + (y : ℂ) * I))
        * mellin (barnesModel g) ((σ : ℂ) + (y : ℂ) * I)) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < x / ((n : ℝ) + 1) ^ s := by
    intro n
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact div_pos hx (Real.rpow_pos_of_pos hnpos s)
  exact MeasureTheory.hasSum_integral_of_summable_integral_norm
    (fun n => integrable_barnesModelInv_integrand h1 h2 (hpos n))
    (summable_integral_norm_barnesModelInv h1 h2 hsσ hx)

/-- The inner sum of the inverted integral is the Barnes integrand up to the genus parity. -/
theorem tsum_barnesModelInv_eq {s x σ : ℝ} (hx : 0 < x) (h1 : -((g : ℝ) + 1) < σ)
    (h2 : σ < -(g : ℝ)) (hsσ : s * σ < -1) (y : ℝ) :
    (∑' n : ℕ, ((((x / ((n : ℝ) + 1) ^ s) : ℝ)) : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I))
        * mellin (barnesModel g) ((σ : ℂ) + (y : ℂ) * I))
      = ((-1) ^ g : ℂ) * barnesIntegrand s x ((σ : ℂ) + (y : ℂ) * I) := by
  have hre : ((σ : ℂ) + (y : ℂ) * I).re = σ := by simp
  have hzre : (-(s : ℂ) * ((σ : ℂ) + (y : ℂ) * I)).re = -(s * σ) := by
    simp [Complex.mul_re]
  have hw : 1 < (-(s : ℂ) * ((σ : ℂ) + (y : ℂ) * I)).re := by
    rw [hzre]; linarith
  rw [tsum_mul_right, tsum_scaled_eq_zeta hx hw,
    mellin_barnesModel_eq (g := g) (by rw [hre]; exact h1) (by rw [hre]; exact h2)]
  rw [barnesIntegrand]
  ring

/-- **The Mellin representation of the genus-`g` canonical-product sum.**  On the strip
`-(g+1) < σ < -g` with `s σ < -1`, the sum of the rescaled model factors is the normalized
vertical integral of the Barnes integrand. -/
theorem hasSum_barnesModel_verticalIntegral' {s x σ : ℝ} (hx : 0 < x)
    (h1 : -((g : ℝ) + 1) < σ) (h2 : σ < -(g : ℝ)) (hsσ : s * σ < -1) :
    HasSum (fun n : ℕ => ((-1) ^ g : ℂ) * barnesModel g (x / ((n : ℝ) + 1) ^ s))
      (VerticalIntegral' (barnesIntegrand s x) σ) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < x / ((n : ℝ) + 1) ^ s := by
    intro n
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact div_pos hx (Real.rpow_pos_of_pos hnpos s)
  have hterm : ∀ n : ℕ,
      (∫ y : ℝ, ((((x / ((n : ℝ) + 1) ^ s) : ℝ) : ℂ)) ^ (-((σ : ℂ) + (y : ℂ) * I))
        * mellin (barnesModel g) ((σ : ℂ) + (y : ℂ) * I))
      = (2 * Real.pi : ℝ) • barnesModel g (x / ((n : ℝ) + 1) ^ s) := fun n =>
    integral_barnesModelInv_integrand_eq h1 h2 (hpos n)
  have hsum := hasSum_integral_barnesModelInv_scaled (g := g) h1 h2 hsσ hx
  have hinner : (∫ y : ℝ, ∑' n : ℕ, ((((x / ((n : ℝ) + 1) ^ s) : ℝ) : ℂ))
          ^ (-((σ : ℂ) + (y : ℂ) * I))
        * mellin (barnesModel g) ((σ : ℂ) + (y : ℂ) * I))
      = ((-1) ^ g : ℂ) * ∫ y : ℝ, barnesIntegrand s x ((σ : ℂ) + (y : ℂ) * I) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun y => tsum_barnesModelInv_eq hx h1 h2 hsσ y)
  rw [hinner] at hsum
  simp only [hterm] at hsum
  set J : ℂ := ∫ y : ℝ, barnesIntegrand s x ((σ : ℂ) + (y : ℂ) * I) with hJ
  set c : ℂ := ((-1) ^ g : ℂ) * (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) with hc
  have hee : ((-1 : ℂ)) ^ g * ((-1 : ℂ)) ^ g = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hinv : ((((2 * Real.pi : ℝ)⁻¹ : ℝ)) : ℂ) * (((2 * Real.pi : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0),
      Complex.ofReal_one]
  have hL : ∀ n : ℕ, c * ((2 * Real.pi : ℝ) • barnesModel g (x / ((n : ℝ) + 1) ^ s))
      = ((-1) ^ g : ℂ) * barnesModel g (x / ((n : ℝ) + 1) ^ s) := by
    intro n
    rw [hc, Complex.real_smul]
    calc ((-1) ^ g : ℂ) * (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ)
          * ((((2 * Real.pi : ℝ)) : ℂ) * barnesModel g (x / ((n : ℝ) + 1) ^ s))
        = (((((2 * Real.pi : ℝ)⁻¹ : ℝ)) : ℂ) * ((((2 * Real.pi : ℝ)) : ℂ)))
            * (((-1) ^ g : ℂ) * barnesModel g (x / ((n : ℝ) + 1) ^ s)) := by ring
      _ = ((-1) ^ g : ℂ) * barnesModel g (x / ((n : ℝ) + 1) ^ s) := by rw [hinv, one_mul]
  have hcc : c * ((-1) ^ g : ℂ) = (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [hc]
    calc ((-1) ^ g : ℂ) * (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) * ((-1) ^ g : ℂ)
        = (((-1) ^ g : ℂ) * ((-1) ^ g : ℂ)) * (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) := by ring
      _ = (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) := by rw [hee, one_mul]
  have hR : c * (((-1) ^ g : ℂ) * J) = VerticalIntegral' (barnesIntegrand s x) σ := by
    rw [verticalIntegral'_eq_smul, ← hJ, Complex.real_smul, ← mul_assoc, hcc]
  have hfinal := hsum.mul_left c
  simp only [hL] at hfinal
  rw [hR] at hfinal
  exact hfinal

end

end RHTower
