import GaloisForLFunctions.RHTower.CHMDLightConePrimeKernelDecomposition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# CHMD: the pole-density law and the Chebyshev-discrepancy transport of the prime wave

The Klein–Gordon prime wave of the CHMD causal wave is `chmdPrimeWave y = Σ_n (Λ(n)/√n) K_y(log n)`
with the prime kernel `K_y(u) = (1/π) ∫ cos(y√(r²+2)) sech²(r/2) cos(ru) dr`, whose light-cone form is
`K_y(u) = D(u+y) + D(u−y) − (y²/2) ∫_{−1}^{1} B(2y²(1−t²)) (D(u+yt) + D(u−yt)) dt` with the
d'Alembert kernel `D(v) = 2v/sinh(πv)`.  The pole wave is `chmdPoleWave y = (2/cos²(1/4)) cos(y√(7/4))`.

This module proves that the Klein–Gordon propagation of the prime-number-theorem density `e^{s/2} ds`
through the sech² kernel is exactly the pole wave, and hence that the prime wave minus the pole wave
is the Klein–Gordon transport of the exact `√`-weighted Chebyshev discrepancy measure
`Σ_n (Λ(n)/√n) δ_{log n} − e^{s/2} ds` on `(0, ∞)`.

1. **Cosecant-square partial fractions at a real point** (`pi_sq_div_sin_sq_eq_tsum`): for `0 < x < 1`,
   `π²/sin²(πx) = 1/x² + Σ_{n≥0} (1/(x−(n+1))² + 1/(x+(n+1))²)`, by termwise differentiation of the
   cotangent Mittag-Leffler series on a complex ball around `x`.
2. **The pole constant** (`integral_dAlembertReal_mul_exp_half`): `∫ D(u) e^{u/2} du = 1/cos²(1/4)`.
   The geometric expansion `1/sinh(πu) = 2 Σ_k e^{−(2k+1)πu}` and the Gamma integral
   `∫_0^∞ u e^{−bu} du = 1/b²` reduce the integral to the rate series
   `Σ_k (1/((2k+1)π − 1/2)² + 1/((2k+1)π + 1/2)²)`, which the partial fractions at
   `x₀ = 1/2 + 1/(4π)` evaluate to `1/(4 cos²(1/4))`, since `sin(πx₀) = cos(1/4)`.
3. **Massless pole law** (`integral_dAlembert_pair_mul_exp_half`,
   `masslessPrimeWave_eq_pole_add_massless_transport`):
   `∫ (D(s+v) + D(s−v)) e^{s/2} ds = (2/cos²(1/4)) cosh(v/2)`, so the d'Alembert prime wave is the
   massless pole wave plus the d'Alembert transport of the discrepancy measure.
4. **Klein–Gordon pole law** (`integral_chmdPrimeKernel_mul_exp_half`, spatial form
   `integral_chmdPrimeKernel_sub_mul_exp_half`): `∫ K_y(s) e^{s/2} ds = chmdPoleWave y` and
   `∫ K_y(s−u) e^{s/2} ds = e^{u/2} chmdPoleWave y`, by Fubini on the light-cone tail and the
   light-cone identity `cos(y√(7/4)) = L[cosh(·/2)](y)`.  The ζ-pole is the spatial mode `e^{u/2}` of
   the Klein–Gordon prime field, oscillating in time at the frequency `√(7/4) = √(2 − 1/4)`.
5. **Chebyshev-discrepancy transport law** (`chmdPrimeWave_eq_chmdPoleWave_add_transport`):
   `chmdPrimeWave y = chmdPoleWave y + chebyshevDiscrepancyTransport y − poleShadow y`, where
   `chebyshevDiscrepancyTransport y = Σ_n (Λ(n)/√n) K_y(log n) − ∫_0^∞ K_y(s) e^{s/2} ds` is the
   transported discrepancy measure and `poleShadow y = ∫_0^∞ K_y(s) e^{−s/2} ds` is bounded by `8/π`
   (`abs_poleShadow_le`, from `|K_y| ≤ 4/π`).  Consequently
   (`riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddBelow`, `…_bddAbove`) the Riemann
   hypothesis holds iff the transported Chebyshev discrepancy is bounded below (equivalently above)
   on `[0, ∞)`: once the pole density is transported exactly, no object of exact growth `e^{y/2}`
   remains in the prime wave, and the whole content of the one-sided bound is carried by the
   arithmetic discrepancy measure.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace RHTower.CHMDChebyshevTransport

open RHTower.CHMDLightCone RHTower.CHMDStage22 GaloisForLFunctions.HTGeometry

noncomputable section


/-- A complex number whose real part lies strictly between `0` and `1` is not an integer. -/
theorem mem_integerComplement_of_re_mem_Ioo {z : ℂ} (hz : z.re ∈ Ioo (0 : ℝ) 1) :
    z ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨m, hm⟩
  have hre : (m : ℝ) = z.re := by rw [← hm]; simp
  rcases hz with ⟨h0, h1⟩
  rw [← hre] at h0 h1
  have h0' : (0 : ℤ) < m := by exact_mod_cast h0
  have h1' : m < (1 : ℤ) := by exact_mod_cast h1
  omega

theorem summable_one_div_nat_add_sq {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Summable fun n : ℕ => 1 / ((n : ℝ) + c) ^ 2 := by
  have hbase : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine h.congr fun n => ?_
    push_cast
    ring
  refine (hbase.mul_left (1 / c ^ 2)).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcn : c * ((n : ℝ) + 1) ≤ (n : ℝ) + c := by nlinarith
  have hpos : 0 < c * ((n : ℝ) + 1) := by positivity
  rw [show 1 / c ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) = 1 / (c * ((n : ℝ) + 1)) ^ 2 by
    field_simp]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos.le hcn 2)

/-- **Cosecant-square partial fractions at a real point of `(0,1)`**:
`π² / sin²(πx) = 1/x² + Σ_{n≥0} (1/(x−(n+1))² + 1/(x+(n+1))²)`.  Obtained by differentiating the
cotangent Mittag-Leffler series termwise on a complex ball around `x`. -/
theorem pi_sq_div_sin_sq_eq_tsum {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    π ^ 2 / Real.sin (π * x) ^ 2 =
      1 / x ^ 2 + ∑' n : ℕ, (1 / (x - ((n : ℝ) + 1)) ^ 2 + 1 / (x + ((n : ℝ) + 1)) ^ 2) := by
  obtain ⟨hx0, hx1⟩ := hx
  set δ : ℝ := min x (1 - x) / 2 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; exact half_pos (lt_min hx0 (by linarith))
  have hδx : δ ≤ x / 2 := by rw [hδ]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδx' : δ ≤ (1 - x) / 2 := by
    rw [hδ]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  set t : Set ℂ := Metric.ball (x : ℂ) δ with ht
  -- real parts on the ball lie in `(0,1)`
  have hre_mem : ∀ z ∈ t, z.re ∈ Ioo (0 : ℝ) 1 := by
    intro z hz
    rw [ht, Metric.mem_ball, Complex.dist_eq] at hz
    have h1 : |(z - (x : ℂ)).re| ≤ ‖z - (x : ℂ)‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    have h2 : |z.re - x| < δ := lt_of_le_of_lt h1 hz
    rw [abs_lt] at h2
    constructor <;> linarith
  have hmem : ∀ z ∈ t, z ∈ Complex.integerComplement :=
    fun z hz => mem_integerComplement_of_re_mem_Ioo (hre_mem z hz)
  have hxt : (x : ℂ) ∈ t := by rw [ht]; exact Metric.mem_ball_self hδpos
  -- lower bounds for the shifted moduli on the ball
  have hlow1 : ∀ z ∈ t, ∀ n : ℕ, (n : ℝ) + (1 - x) / 2 ≤ ‖z - ((n : ℂ) + 1)‖ := by
    intro z hz n
    rw [ht, Metric.mem_ball, Complex.dist_eq] at hz
    have hz' : ‖z‖ ≤ x + δ := by
      have := norm_sub_norm_le z (x : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] at this
      linarith
    have h1 : ‖((n : ℂ) + 1)‖ - ‖z‖ ≤ ‖z - ((n : ℂ) + 1)‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le _ _
    have h2 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h2] at h1
    linarith
  have hlow2 : ∀ z ∈ t, ∀ n : ℕ, (n : ℝ) + 1 ≤ ‖z + ((n : ℂ) + 1)‖ := by
    intro z hz n
    have hre := hre_mem z hz
    have h1 : (z + ((n : ℂ) + 1)).re ≤ ‖z + ((n : ℂ) + 1)‖ := Complex.re_le_norm _
    rw [Complex.add_re, Complex.add_re, Complex.natCast_re, Complex.one_re] at h1
    linarith [hre.1]
  -- the series terms, their derivatives and the summable bound
  set g : ℕ → ℂ → ℂ := fun n z => 1 / (z - ((n : ℂ) + 1)) + 1 / (z + ((n : ℂ) + 1)) with hg
  set g' : ℕ → ℂ → ℂ := fun n z =>
    -(1 / (z - ((n : ℂ) + 1)) ^ 2 + 1 / (z + ((n : ℂ) + 1)) ^ 2) with hg'
  set u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + (1 - x) / 2) ^ 2 + 1 / ((n : ℝ) + 1) ^ 2 with hu
  have hu_sum : Summable u :=
    (summable_one_div_nat_add_sq (by linarith) (by linarith)).add
      (summable_one_div_nat_add_sq one_pos le_rfl)
  have hderiv : ∀ n : ℕ, ∀ z ∈ t, HasDerivAt (g n) (g' n z) z := by
    intro n z hz
    have hz1 : z - ((n : ℂ) + 1) ≠ 0 := by
      have := hlow1 z hz n
      intro h0
      rw [h0, norm_zero] at this
      have : (0 : ℝ) < (n : ℝ) + (1 - x) / 2 := by positivity
      linarith
    have hz2 : z + ((n : ℂ) + 1) ≠ 0 := by
      have := hlow2 z hz n
      intro h0
      rw [h0, norm_zero] at this
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      linarith
    have h1 : HasDerivAt (fun w : ℂ => (w - ((n : ℂ) + 1))⁻¹) (-(1 : ℂ) / (z - ((n : ℂ) + 1)) ^ 2) z :=
      ((hasDerivAt_id z).sub_const _).inv hz1
    have h2 : HasDerivAt (fun w : ℂ => (w + ((n : ℂ) + 1))⁻¹) (-(1 : ℂ) / (z + ((n : ℂ) + 1)) ^ 2) z :=
      ((hasDerivAt_id z).add_const _).inv hz2
    have hfun : g n = fun w : ℂ => (w - ((n : ℂ) + 1))⁻¹ + (w + ((n : ℂ) + 1))⁻¹ := by
      funext w; simp only [hg, one_div]
    rw [hfun]
    refine (h1.add h2).congr_deriv ?_
    simp only [hg']
    ring
  have hbound : ∀ n : ℕ, ∀ z ∈ t, ‖g' n z‖ ≤ u n := by
    intro n z hz
    have h1 := hlow1 z hz n
    have h2 := hlow2 z hz n
    have hp1 : (0 : ℝ) < (n : ℝ) + (1 - x) / 2 := by
      have : 0 < 1 - x := by linarith
      positivity
    have hp2 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simp only [hg', hu, norm_neg]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_div, norm_one, norm_pow]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hp1.le h1 2)
    · rw [norm_div, norm_one, norm_pow]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hp2.le h2 2)
  have hsum0 : Summable fun n => g n (x : ℂ) := by
    have := summable_cotTerm (hmem _ hxt)
    exact this
  have hD : HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n (x : ℂ)) (x : ℂ) :=
    hasDerivAt_tsum_of_isPreconnected hu_sum Metric.isOpen_ball Metric.isPreconnected_ball
      hderiv hbound hxt hsum0 hxt
  -- the series equals `π cot(πz) − 1/z` on the ball
  have hEq : (fun z : ℂ => (π : ℂ) * Complex.cot (π * z) - 1 / z) =ᶠ[𝓝 (x : ℂ)]
      fun z => ∑' n, g n z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hxt] with z hz
    exact cot_series_rep' (hmem z hz)
  have hD' : HasDerivAt (fun z : ℂ => (π : ℂ) * Complex.cot (π * z) - 1 / z)
      (∑' n, g' n (x : ℂ)) (x : ℂ) := hD.congr_of_eventuallyEq hEq
  -- direct derivative of `π cot(πz) − 1/z`
  have hsin : Complex.sin (π * (x : ℂ)) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hkx : (k : ℂ) = (x : ℂ) := by
      have : (π : ℂ) * (x : ℂ) = (π : ℂ) * (k : ℂ) := by rw [hk]; ring
      exact (mul_left_cancel₀ hpi this).symm
    have hmem' := hmem _ hxt
    rw [Complex.mem_integerComplement_iff] at hmem'
    exact hmem' ⟨k, hkx⟩
  have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have harg : HasDerivAt (fun w : ℂ => (π : ℂ) * w) (π : ℂ) (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_mul (π : ℂ)
  have hcos : HasDerivAt (fun w : ℂ => Complex.cos (π * w))
      (-(π : ℂ) * Complex.sin (π * (x : ℂ))) (x : ℂ) := by
    apply ((Complex.hasDerivAt_cos (π * (x : ℂ))).comp (x : ℂ) harg).congr_deriv
    ring
  have hsine : HasDerivAt (fun w : ℂ => Complex.sin (π * w))
      ((π : ℂ) * Complex.cos (π * (x : ℂ))) (x : ℂ) := by
    apply ((Complex.hasDerivAt_sin (π * (x : ℂ))).comp (x : ℂ) harg).congr_deriv
    ring
  have hcot : HasDerivAt (fun w : ℂ => (π : ℂ) * Complex.cot (π * w))
      (-(π : ℂ) ^ 2 / Complex.sin (π * (x : ℂ)) ^ 2) (x : ℂ) := by
    have h := ((hcos.div hsine hsin).const_mul (π : ℂ))
    refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Eventually.of_forall fun w => by simp only [Pi.div_apply, Complex.cot_eq_cos_div_sin]
    · field_simp
      rw [← Complex.sin_sq_add_cos_sq (π * (x : ℂ))]
      ring
  have hinv : HasDerivAt (fun w : ℂ => 1 / w) (-(1 : ℂ) / (x : ℂ) ^ 2) (x : ℂ) := by
    have := hasDerivAt_inv hx0'
    refine (this.congr_of_eventuallyEq (Eventually.of_forall fun w => by simp [one_div])).congr_deriv ?_
    ring
  have hD'' : HasDerivAt (fun z : ℂ => (π : ℂ) * Complex.cot (π * z) - 1 / z)
      (-(π : ℂ) ^ 2 / Complex.sin (π * (x : ℂ)) ^ 2 - -(1 : ℂ) / (x : ℂ) ^ 2) (x : ℂ) :=
    hcot.sub hinv
  have hkey := hD'.unique hD''
  -- rearrange in `ℂ`
  have hsumC : Summable fun n => g' n (x : ℂ) := by
    refine Summable.of_norm_bounded hu_sum fun n => hbound n _ hxt
  have hC : ((π : ℂ) ^ 2 / Complex.sin (π * (x : ℂ)) ^ 2) =
      1 / (x : ℂ) ^ 2 + ∑' n : ℕ, (1 / ((x : ℂ) - ((n : ℂ) + 1)) ^ 2 + 1 / ((x : ℂ) + ((n : ℂ) + 1)) ^ 2) := by
    have hneg : ∑' n, g' n (x : ℂ) =
        -∑' n : ℕ, (1 / ((x : ℂ) - ((n : ℂ) + 1)) ^ 2 + 1 / ((x : ℂ) + ((n : ℂ) + 1)) ^ 2) := by
      rw [← tsum_neg]
    rw [hneg, neg_eq_iff_eq_neg] at hkey
    rw [hkey]
    ring
  -- descend to `ℝ`
  apply Complex.ofReal_injective
  push_cast
  exact hC


/-! ## Section 2: the Laplace transform of the d'Alembert kernel at the pole frequency -/

/-- Geometric expansion of the hyperbolic cosecant on the positive axis:
`1 / sinh(πu) = Σ_{k≥0} 2 e^{−(2k+1)πu}` for `u > 0`. -/
theorem one_div_sinh_pi_mul_eq_tsum {u : ℝ} (hu : 0 < u) :
    1 / Real.sinh (π * u) = ∑' k : ℕ, 2 * Real.exp (-((2 * (k : ℝ) + 1) * π * u)) := by
  have hq0 : 0 ≤ Real.exp (-(2 * π * u)) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(2 * π * u)) < 1 := Real.exp_lt_one_iff.mpr (by
    have : 0 < 2 * π * u := by positivity
    linarith)
  have hgeom := tsum_geometric_of_lt_one hq0 hq1
  have hterm : ∀ k : ℕ, 2 * Real.exp (-((2 * (k : ℝ) + 1) * π * u)) =
      2 * Real.exp (-(π * u)) * Real.exp (-(2 * π * u)) ^ k := by
    intro k
    have : Real.exp (-((2 * (k : ℝ) + 1) * π * u)) =
        Real.exp (-(π * u)) * Real.exp (-(2 * π * u)) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [this]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, hgeom, Real.sinh_eq]
  have he : 0 < Real.exp (π * u) := Real.exp_pos _
  have hne : Real.exp (π * u) - Real.exp (-(π * u)) ≠ 0 := by
    have : Real.exp (-(π * u)) < Real.exp (π * u) := Real.exp_lt_exp.mpr (by
      have : 0 < π * u := by positivity
      linarith)
    linarith
  have h2 : Real.exp (-(2 * π * u)) = Real.exp (-(π * u)) * Real.exp (-(π * u)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (π * u) * Real.exp (-(π * u)) = 1 := by
    rw [← Real.exp_add]; simp
  have hbpos : 0 < Real.exp (-(π * u)) := Real.exp_pos _
  have hb1 : Real.exp (-(π * u)) < 1 := Real.exp_lt_one_iff.mpr (by
    have : 0 < π * u := by positivity
    linarith)
  have hden : 1 - Real.exp (-(π * u)) * Real.exp (-(π * u)) ≠ 0 := by nlinarith
  have hden' : 1 - Real.exp (-(π * u)) ^ 2 ≠ 0 := by nlinarith
  rw [h2]
  field_simp
  nlinarith [h3]

/-- `∫_0^∞ u e^{−bu} du = 1/b²` for `b > 0`. -/
theorem integral_Ioi_mul_exp_neg_mul {b : ℝ} (hb : 0 < b) :
    ∫ u in Ioi (0 : ℝ), u * Real.exp (-(b * u)) = 1 / b ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := b) (by norm_num) hb
  rw [Real.Gamma_two, mul_one, Real.rpow_two, one_div_pow] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]

theorem integrableOn_Ioi_mul_exp_neg_mul {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => u * Real.exp (-(b * u))) (Ioi (0 : ℝ)) := by
  have h := (HTGeometry.integrable_abs_pow_mul_exp_neg_abs 1 hb).integrableOn (s := Ioi (0 : ℝ))
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
  simp only [pow_one]
  rw [abs_of_pos hu]
  ring_nf

/-- The two exponential rates `(2k+1)π ∓ 1/2` are positive. -/
theorem rate_sub_pos (k : ℕ) : 0 < (2 * (k : ℝ) + 1) * π - 1 / 2 := by
  have := Real.pi_gt_three
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

theorem rate_add_pos (k : ℕ) : 0 < (2 * (k : ℝ) + 1) * π + 1 / 2 := by
  have := rate_sub_pos k
  linarith

/-- The `k`-th term of the expanded Laplace integrand. -/
def laplaceTerm (k : ℕ) (u : ℝ) : ℝ :=
  u * Real.exp (-(((2 * (k : ℝ) + 1) * π - 1 / 2) * u)) +
    u * Real.exp (-(((2 * (k : ℝ) + 1) * π + 1 / 2) * u))

theorem laplaceTerm_eq (k : ℕ) (u : ℝ) :
    laplaceTerm k u = u * Real.cosh (u / 2) * (2 * Real.exp (-((2 * (k : ℝ) + 1) * π * u))) := by
  unfold laplaceTerm
  rw [Real.cosh_eq]
  have h1 : Real.exp (-(((2 * (k : ℝ) + 1) * π - 1 / 2) * u)) =
      Real.exp (u / 2) * Real.exp (-((2 * (k : ℝ) + 1) * π * u)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-(((2 * (k : ℝ) + 1) * π + 1 / 2) * u)) =
      Real.exp (-(u / 2)) * Real.exp (-((2 * (k : ℝ) + 1) * π * u)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h1, h2]
  ring

theorem laplaceTerm_nonneg (k : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ laplaceTerm k u := by
  unfold laplaceTerm
  positivity

theorem integrableOn_laplaceTerm (k : ℕ) : IntegrableOn (laplaceTerm k) (Ioi (0 : ℝ)) :=
  (integrableOn_Ioi_mul_exp_neg_mul (rate_sub_pos k)).add
    (integrableOn_Ioi_mul_exp_neg_mul (rate_add_pos k))

theorem integral_laplaceTerm (k : ℕ) :
    ∫ u in Ioi (0 : ℝ), laplaceTerm k u =
      1 / ((2 * (k : ℝ) + 1) * π - 1 / 2) ^ 2 + 1 / ((2 * (k : ℝ) + 1) * π + 1 / 2) ^ 2 := by
  unfold laplaceTerm
  rw [integral_add (integrableOn_Ioi_mul_exp_neg_mul (rate_sub_pos k))
    (integrableOn_Ioi_mul_exp_neg_mul (rate_add_pos k)),
    integral_Ioi_mul_exp_neg_mul (rate_sub_pos k), integral_Ioi_mul_exp_neg_mul (rate_add_pos k)]

/-- The pole abscissa `x₀ = 1/2 + 1/(4π)` of the cosecant series. -/
def poleAbscissa : ℝ := 1 / 2 + 1 / (4 * π)

theorem poleAbscissa_mem_Ioo : poleAbscissa ∈ Ioo (0 : ℝ) 1 := by
  unfold poleAbscissa
  have := Real.pi_gt_three
  constructor
  · positivity
  · have h : 1 / (4 * π) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith

theorem sin_pi_mul_poleAbscissa : Real.sin (π * poleAbscissa) = Real.cos (1 / 4) := by
  unfold poleAbscissa
  have hpi : π ≠ 0 := Real.pi_ne_zero
  rw [show π * (1 / 2 + 1 / (4 * π)) = 1 / 4 + π / 2 by field_simp; ring,
    Real.sin_add_pi_div_two]

/-- Summation of the rate series through the cosecant partial fractions:
`Σ_k (1/((2k+1)π − 1/2)² + 1/((2k+1)π + 1/2)²) = 1 / (4 cos²(1/4))`. -/
theorem tsum_rate_sq_inv :
    ∑' k : ℕ, (1 / ((2 * (k : ℝ) + 1) * π - 1 / 2) ^ 2 + 1 / ((2 * (k : ℝ) + 1) * π + 1 / 2) ^ 2) =
      1 / (4 * Real.cos (1 / 4) ^ 2) := by
  set x₀ : ℝ := poleAbscissa with hx₀
  have hx₀mem := poleAbscissa_mem_Ioo
  rw [← hx₀] at hx₀mem
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hsub : ∀ k : ℕ, (2 * (k : ℝ) + 1) * π - 1 / 2 = 2 * π * ((k : ℝ) + (1 - x₀)) := by
    intro k; rw [hx₀]; unfold poleAbscissa; field_simp; ring
  have hadd : ∀ k : ℕ, (2 * (k : ℝ) + 1) * π + 1 / 2 = 2 * π * ((k : ℝ) + x₀) := by
    intro k; rw [hx₀]; unfold poleAbscissa; field_simp; ring
  have hsum1 : Summable fun k : ℕ => 1 / ((k : ℝ) + (1 - x₀)) ^ 2 :=
    summable_one_div_nat_add_sq (by linarith [hx₀mem.2]) (by linarith [hx₀mem.1])
  have hsum2 : Summable fun k : ℕ => 1 / ((k : ℝ) + x₀) ^ 2 :=
    summable_one_div_nat_add_sq hx₀mem.1 hx₀mem.2.le
  have hterm : ∀ k : ℕ,
      1 / ((2 * (k : ℝ) + 1) * π - 1 / 2) ^ 2 + 1 / ((2 * (k : ℝ) + 1) * π + 1 / 2) ^ 2 =
        1 / (4 * π ^ 2) * (1 / ((k : ℝ) + (1 - x₀)) ^ 2 + 1 / ((k : ℝ) + x₀) ^ 2) := by
    intro k
    rw [hsub k, hadd k]
    have h1 : (k : ℝ) + (1 - x₀) ≠ 0 := by linarith [hx₀mem.2, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have h2 : (k : ℝ) + x₀ ≠ 0 := by linarith [hx₀mem.1, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    field_simp
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, hsum1.tsum_add hsum2, hsum2.tsum_eq_zero_add]
  have hre : ∀ k : ℕ, 1 / ((k : ℝ) + (1 - x₀)) ^ 2 = 1 / (x₀ - ((k : ℝ) + 1)) ^ 2 := by
    intro k
    rw [show x₀ - ((k : ℝ) + 1) = -((k : ℝ) + (1 - x₀)) by ring, neg_sq]
  simp_rw [hre]
  have hcsc := pi_sq_div_sin_sq_eq_tsum hx₀mem
  rw [sin_pi_mul_poleAbscissa] at hcsc
  have hsum3 : Summable fun k : ℕ => 1 / (x₀ - ((k : ℝ) + 1)) ^ 2 := by
    refine hsum1.congr fun k => ?_
    exact hre k
  have hsum4 : Summable fun k : ℕ => 1 / (x₀ + ((k : ℝ) + 1)) ^ 2 := by
    have := (summable_nat_add_iff (f := fun k : ℕ => 1 / ((k : ℝ) + x₀) ^ 2) 1).mpr hsum2
    refine this.congr fun k => ?_
    show 1 / (((k + 1 : ℕ) : ℝ) + x₀) ^ 2 = 1 / (x₀ + ((k : ℝ) + 1)) ^ 2
    push_cast
    ring_nf
  have hcos : Real.cos (1 / 4) ≠ 0 := by
    have := Real.cos_pos_of_mem_Ioo (x := 1 / 4) ⟨by linarith [Real.pi_gt_three], by
      linarith [Real.pi_gt_three]⟩
    exact this.ne'
  have hx0 : x₀ ≠ 0 := hx₀mem.1.ne'
  have hsplit : ∑' k : ℕ, (1 / (x₀ - ((k : ℝ) + 1)) ^ 2 + 1 / (x₀ + ((k : ℝ) + 1)) ^ 2) =
      (∑' k : ℕ, 1 / (x₀ - ((k : ℝ) + 1)) ^ 2) + ∑' k : ℕ, 1 / (x₀ + ((k : ℝ) + 1)) ^ 2 :=
    hsum3.tsum_add hsum4
  have hshift : ∑' k : ℕ, 1 / (((k + 1 : ℕ) : ℝ) + x₀) ^ 2 =
      ∑' k : ℕ, 1 / (x₀ + ((k : ℝ) + 1)) ^ 2 := by
    refine tsum_congr fun k => ?_
    push_cast
    ring_nf
  rw [hshift]
  have hπ2 : π ^ 2 ≠ 0 := pow_ne_zero 2 hpi
  have hkey : (∑' k : ℕ, 1 / (x₀ - ((k : ℝ) + 1)) ^ 2) + ∑' k : ℕ, 1 / (x₀ + ((k : ℝ) + 1)) ^ 2 =
      π ^ 2 / Real.cos (1 / 4) ^ 2 - 1 / x₀ ^ 2 := by
    rw [← hsplit]; linarith [hcsc]
  calc 1 / (4 * π ^ 2) * ((∑' k : ℕ, 1 / (x₀ - ((k : ℝ) + 1)) ^ 2) +
        (1 / (((0 : ℕ) : ℝ) + x₀) ^ 2 + ∑' k : ℕ, 1 / (x₀ + ((k : ℝ) + 1)) ^ 2))
      = 1 / (4 * π ^ 2) * (1 / x₀ ^ 2 + ((∑' k : ℕ, 1 / (x₀ - ((k : ℝ) + 1)) ^ 2) +
          ∑' k : ℕ, 1 / (x₀ + ((k : ℝ) + 1)) ^ 2)) := by
        simp only [Nat.cast_zero, zero_add]; ring
    _ = 1 / (4 * π ^ 2) * (π ^ 2 / Real.cos (1 / 4) ^ 2) := by rw [hkey]; ring
    _ = 1 / (4 * Real.cos (1 / 4) ^ 2) := by field_simp

/-- **Laplace transform of the d'Alembert kernel at the pole frequency** (half-line form):
`∫_0^∞ u cosh(u/2) / sinh(πu) du = 1 / (4 cos²(1/4))`. -/
theorem integral_Ioi_mul_cosh_half_div_sinh :
    ∫ u in Ioi (0 : ℝ), u * Real.cosh (u / 2) / Real.sinh (π * u) = 1 / (4 * Real.cos (1 / 4) ^ 2) := by
  have hpt : ∀ u ∈ Ioi (0 : ℝ), u * Real.cosh (u / 2) / Real.sinh (π * u) =
      ∑' k : ℕ, laplaceTerm k u := by
    intro u hu
    simp_rw [laplaceTerm_eq]
    rw [tsum_mul_left, ← one_div_sinh_pi_mul_eq_tsum hu]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hint : ∀ k : ℕ, Integrable (laplaceTerm k) (volume.restrict (Ioi (0 : ℝ))) :=
    fun k => integrableOn_laplaceTerm k
  have hnorm : ∀ k : ℕ, ∫ u in Ioi (0 : ℝ), ‖laplaceTerm k u‖ =
      1 / ((2 * (k : ℝ) + 1) * π - 1 / 2) ^ 2 + 1 / ((2 * (k : ℝ) + 1) * π + 1 / 2) ^ 2 := by
    intro k
    rw [← integral_laplaceTerm k]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (laplaceTerm_nonneg k (le_of_lt hu))]
  have hsum : Summable fun k : ℕ => ∫ u in Ioi (0 : ℝ), ‖laplaceTerm k u‖ := by
    simp_rw [hnorm]
    have h1 := summable_one_div_nat_add_sq (c := 1 - poleAbscissa)
      (by linarith [poleAbscissa_mem_Ioo.2]) (by linarith [poleAbscissa_mem_Ioo.1])
    have h2 := summable_one_div_nat_add_sq (c := poleAbscissa) poleAbscissa_mem_Ioo.1
      poleAbscissa_mem_Ioo.2.le
    refine ((h1.add h2).mul_left (1 / (4 * π ^ 2))).congr fun k => ?_
    have hpi : π ≠ 0 := Real.pi_ne_zero
    have hsub : (2 * (k : ℝ) + 1) * π - 1 / 2 = 2 * π * ((k : ℝ) + (1 - poleAbscissa)) := by
      unfold poleAbscissa; field_simp; ring
    have hadd : (2 * (k : ℝ) + 1) * π + 1 / 2 = 2 * π * ((k : ℝ) + poleAbscissa) := by
      unfold poleAbscissa; field_simp; ring
    have h1' : (k : ℝ) + (1 - poleAbscissa) ≠ 0 := by
      linarith [poleAbscissa_mem_Ioo.2, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have h2' : (k : ℝ) + poleAbscissa ≠ 0 := by
      linarith [poleAbscissa_mem_Ioo.1, (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    rw [hsub, hadd]
    field_simp
    ring
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [integral_laplaceTerm]
  exact tsum_rate_sq_inv


/-! ## Section 3: the pole constant `∫ D(u) e^{u/2} du = sec²(1/4)` -/

/-- Exponential domination of the pole-weighted d'Alembert kernel. -/
theorem dAlembertReal_mul_exp_half_le (u : ℝ) :
    dAlembertReal u * Real.exp (u / 2) ≤ 8 * Real.exp (-((π - 3 / 2) * |0 - u|)) := by
  have hD := dAlembertReal_le u
  have h1 : 1 + |u| ≤ Real.exp |u| := by linarith [Real.add_one_le_exp |u|]
  have h2 : Real.exp (u / 2) ≤ Real.exp (|u| / 2) :=
    Real.exp_le_exp.mpr (by linarith [le_abs_self u])
  have hDpos := dAlembertReal_pos u
  calc dAlembertReal u * Real.exp (u / 2)
      ≤ 8 * (1 + |u|) * Real.exp (-(π * |u|)) * Real.exp (|u| / 2) :=
        mul_le_mul hD h2 (Real.exp_pos _).le (by positivity)
    _ ≤ 8 * Real.exp |u| * Real.exp (-(π * |u|)) * Real.exp (|u| / 2) := by
        gcongr
    _ = 8 * Real.exp (-((π - 3 / 2) * |0 - u|)) := by
        rw [zero_sub, abs_neg, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

theorem integrable_dAlembertReal_mul_exp_half :
    Integrable fun u : ℝ => dAlembertReal u * Real.exp (u / 2) := by
  have hβ : 0 < π - 3 / 2 := by linarith [Real.pi_gt_three]
  refine ((integrable_exp_neg_mul_abs_sub hβ 0).const_mul 8).mono'
    ((continuous_dAlembertReal.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (dAlembertReal_pos u) (Real.exp_pos _))]
  exact dAlembertReal_mul_exp_half_le u

/-- **The pole constant.**  The Laplace transform of the d'Alembert kernel at the ζ-pole frequency:
`∫ D(u) e^{u/2} du = 1 / cos²(1/4)`. -/
theorem integral_dAlembertReal_mul_exp_half :
    ∫ u : ℝ, dAlembertReal u * Real.exp (u / 2) = 1 / Real.cos (1 / 4) ^ 2 := by
  -- symmetrize to `cosh`
  have hneg : ∫ u : ℝ, dAlembertReal u * Real.exp (u / 2) =
      ∫ u : ℝ, dAlembertReal u * Real.exp (-(u / 2)) := by
    rw [← integral_neg_eq_self (fun u => dAlembertReal u * Real.exp (u / 2)) volume]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [dAlembertReal_neg]
    ring_nf
  have hint := integrable_dAlembertReal_mul_exp_half
  have hint' : Integrable fun u : ℝ => dAlembertReal u * Real.exp (-(u / 2)) := by
    refine hint.comp_neg.congr (Eventually.of_forall fun u => ?_)
    simp only [dAlembertReal_neg]
    ring_nf
  have hcosh : ∫ u : ℝ, dAlembertReal u * Real.exp (u / 2) =
      ∫ u : ℝ, dAlembertReal u * Real.cosh (u / 2) := by
    have h := integral_add hint hint'
    rw [← hneg] at h
    have h2 : (∫ u : ℝ, (dAlembertReal u * Real.exp (u / 2) + dAlembertReal u * Real.exp (-(u / 2)))) =
        2 * ∫ u : ℝ, dAlembertReal u * Real.cosh (u / 2) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only [Real.cosh_eq]
      ring
    linarith
  -- fold to the half-line
  have hfold : ∫ u : ℝ, dAlembertReal u * Real.cosh (u / 2) =
      2 * ∫ u in Ioi (0 : ℝ), dAlembertReal u * Real.cosh (u / 2) := by
    rw [← integral_comp_abs (f := fun u => dAlembertReal u * Real.cosh (u / 2))]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [show |u| / 2 = |u / 2| by rw [abs_div, abs_two], Real.cosh_abs]
    rcases le_or_gt 0 u with hu | hu
    · rw [abs_of_nonneg hu]
    · rw [abs_of_neg hu, dAlembertReal_neg]
  have hhalf : ∫ u in Ioi (0 : ℝ), dAlembertReal u * Real.cosh (u / 2) =
      2 * ∫ u in Ioi (0 : ℝ), u * Real.cosh (u / 2) / Real.sinh (π * u) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    rw [dAlembertReal_of_ne (ne_of_gt hu)]
    ring
  rw [hcosh, hfold, hhalf, integral_Ioi_mul_cosh_half_div_sinh]
  have hcos : Real.cos (1 / 4) ≠ 0 := by
    have := Real.cos_pos_of_mem_Ioo (x := 1 / 4) ⟨by linarith [Real.pi_gt_three], by
      linarith [Real.pi_gt_three]⟩
    exact this.ne'
  field_simp
  norm_num

/-! ## Section 4: the massless pole law -/

theorem integrable_dAlembertReal_sub_mul_exp_half (v : ℝ) :
    Integrable fun s : ℝ => dAlembertReal (s - v) * Real.exp (s / 2) := by
  have h := (integrable_dAlembertReal_mul_exp_half.mul_const (Real.exp (v / 2))).comp_sub_right v
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp only
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem integrable_dAlembertReal_add_mul_exp_half (v : ℝ) :
    Integrable fun s : ℝ => dAlembertReal (s + v) * Real.exp (s / 2) := by
  have h := (integrable_dAlembertReal_mul_exp_half.mul_const (Real.exp (-(v / 2)))).comp_add_right v
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp only
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The d'Alembert kernel translated to `v` and paired with the pole density `e^{s/2}`. -/
theorem integral_dAlembertReal_sub_mul_exp_half (v : ℝ) :
    ∫ s : ℝ, dAlembertReal (s - v) * Real.exp (s / 2) = Real.exp (v / 2) / Real.cos (1 / 4) ^ 2 := by
  have h := integral_sub_right_eq_self (μ := volume)
    (fun u : ℝ => dAlembertReal u * Real.exp (u / 2) * Real.exp (v / 2)) v
  have hl : ∫ s : ℝ, dAlembertReal (s - v) * Real.exp (s / 2) =
      ∫ s : ℝ, dAlembertReal (s - v) * Real.exp ((s - v) / 2) * Real.exp (v / 2) := by
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hl, h, integral_mul_const, integral_dAlembertReal_mul_exp_half]
  ring

theorem integral_dAlembertReal_add_mul_exp_half (v : ℝ) :
    ∫ s : ℝ, dAlembertReal (s + v) * Real.exp (s / 2) = Real.exp (-(v / 2)) / Real.cos (1 / 4) ^ 2 := by
  have h := integral_add_right_eq_self (μ := volume)
    (fun u : ℝ => dAlembertReal u * Real.exp (u / 2) * Real.exp (-(v / 2))) v
  have hl : ∫ s : ℝ, dAlembertReal (s + v) * Real.exp (s / 2) =
      ∫ s : ℝ, dAlembertReal (s + v) * Real.exp ((s + v) / 2) * Real.exp (-(v / 2)) := by
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hl, h, integral_mul_const, integral_dAlembertReal_mul_exp_half]
  ring

/-- **Massless pole law.**  The d'Alembert propagation of the prime-number-theorem density
`e^{s/2} ds` is exactly the massless pole wave: `∫ (D(s+v) + D(s−v)) e^{s/2} ds = (2/cos²(1/4)) cosh(v/2)`. -/
theorem integral_dAlembert_pair_mul_exp_half (v : ℝ) :
    ∫ s : ℝ, (dAlembertReal (s + v) + dAlembertReal (s - v)) * Real.exp (s / 2) =
      2 / Real.cos (1 / 4) ^ 2 * Real.cosh (v / 2) := by
  have hsplit : ∫ s : ℝ, (dAlembertReal (s + v) + dAlembertReal (s - v)) * Real.exp (s / 2) =
      (∫ s : ℝ, dAlembertReal (s + v) * Real.exp (s / 2)) +
        ∫ s : ℝ, dAlembertReal (s - v) * Real.exp (s / 2) := by
    rw [← integral_add (integrable_dAlembertReal_add_mul_exp_half v)
      (integrable_dAlembertReal_sub_mul_exp_half v)]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    ring
  rw [hsplit, integral_dAlembertReal_add_mul_exp_half, integral_dAlembertReal_sub_mul_exp_half,
    Real.cosh_eq]
  ring



/-- **Massless transport law.**  The d'Alembert prime wave is the massless pole wave plus the
d'Alembert transport of the `√`-weighted Chebyshev discrepancy measure. -/
theorem masslessPrimeWave_eq_pole_add_massless_transport (y : ℝ) :
    masslessPrimeWave y = 2 / Real.cos (1 / 4) ^ 2 * Real.cosh (y / 2) +
      ((∑' n : ℕ, chmdPrimeWeight n *
          (dAlembertReal (Real.log n + y) + dAlembertReal (Real.log n - y))) -
        ∫ s : ℝ, (dAlembertReal (s + y) + dAlembertReal (s - y)) * Real.exp (s / 2)) := by
  unfold masslessPrimeWave
  rw [integral_dAlembert_pair_mul_exp_half]
  ring

/-! ## Section 5: the Klein–Gordon pole law -/

/-- Uniform domination of the shifted d'Alembert pair inside the light cone `|t| ≤ 1`. -/
theorem dAlembert_pair_shift_le (y : ℝ) {t : ℝ} (ht : |t| ≤ 1) (s : ℝ) :
    dAlembertReal (s + y * t) + dAlembertReal (s - y * t) ≤
      16 * (1 + |y|) * Real.exp (π * |y|) * Real.exp (-((π - 1) * |s|)) := by
  have key : ∀ a : ℝ, |a| ≤ |y| → dAlembertReal (s + a) ≤
      8 * (1 + |y|) * Real.exp (π * |y|) * Real.exp (-((π - 1) * |s|)) := by
    intro a ha
    have hD := dAlembertReal_le (s + a)
    have h1 : |s + a| ≤ |s| + |y| := (abs_add_le s a).trans (by linarith)
    have h2 : |s| ≤ |s + a| + |y| := by
      have := abs_add_le (s + a) (-a)
      simp only [add_neg_cancel_right, abs_neg] at this
      linarith
    have hexp : Real.exp (-(π * |s + a|)) ≤ Real.exp (π * |y|) * Real.exp (-(π * |s|)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hlin : 1 + |s + a| ≤ (1 + |y|) * Real.exp |s| := by
      have h3 : 1 + |s| ≤ Real.exp |s| := by linarith [Real.add_one_le_exp |s|]
      have h4 : 1 + |s + a| ≤ (1 + |y|) * (1 + |s|) := by nlinarith [abs_nonneg y, abs_nonneg s]
      calc 1 + |s + a| ≤ (1 + |y|) * (1 + |s|) := h4
        _ ≤ (1 + |y|) * Real.exp |s| := mul_le_mul_of_nonneg_left h3 (by positivity)
    calc dAlembertReal (s + a) ≤ 8 * (1 + |s + a|) * Real.exp (-(π * |s + a|)) := hD
      _ ≤ 8 * ((1 + |y|) * Real.exp |s|) * (Real.exp (π * |y|) * Real.exp (-(π * |s|))) := by
          gcongr
      _ = 8 * (1 + |y|) * Real.exp (π * |y|) * Real.exp (-((π - 1) * |s|)) := by
          rw [show 8 * ((1 + |y|) * Real.exp |s|) * (Real.exp (π * |y|) * Real.exp (-(π * |s|))) =
            8 * (1 + |y|) * Real.exp (π * |y|) * (Real.exp |s| * Real.exp (-(π * |s|))) by ring,
            ← Real.exp_add]
          congr 2
          ring
  have hyt : |y * t| ≤ |y| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg y) ht
  have hyt' : |-(y * t)| ≤ |y| := by rwa [abs_neg]
  have e1 := key (y * t) hyt
  have e2 := key (-(y * t)) hyt'
  rw [← sub_eq_add_neg] at e2
  linarith

/-- The clamp of `t` to `[-1, 1]`. -/
def clampUnit (t : ℝ) : ℝ := max (-1) (min t 1)

theorem abs_clampUnit_le (t : ℝ) : |clampUnit t| ≤ 1 := by
  unfold clampUnit
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

theorem clampUnit_of_mem {t : ℝ} (ht : t ∈ uIcc (-1 : ℝ) 1) : clampUnit t = t := by
  rw [uIcc_of_le (by norm_num)] at ht
  unfold clampUnit
  rw [min_eq_left ht.2, max_eq_right ht.1]

@[fun_prop] theorem continuous_clampUnit : Continuous clampUnit :=
  continuous_const.max (continuous_id.min continuous_const)

/-- Exponential domination of the pole-weighted light-cone pair integrand. -/
theorem lightCone_pair_exp_half_le (y : ℝ) {t : ℝ} (ht : |t| ≤ 1) (s : ℝ) :
    ‖lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        ((dAlembertReal (s + y * t) + dAlembertReal (s - y * t)) * Real.exp (s / 2))‖ ≤
      Real.exp (y ^ 2 / 2) *
        (16 * (1 + |y|) * Real.exp (π * |y|) * Real.exp (-((π - 3 / 2) * |0 - s|))) := by
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  have hB := abs_lightConeBesselReal_light_cone_le y ht
  have hpair := dAlembert_pair_shift_le y ht s
  have hpos : 0 < dAlembertReal (s + y * t) + dAlembertReal (s - y * t) :=
    add_pos (dAlembertReal_pos _) (dAlembertReal_pos _)
  rw [abs_of_pos hpos, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (s / 2) ≤ Real.exp (|s| / 2) :=
    Real.exp_le_exp.mpr (by linarith [le_abs_self s])
  calc |lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2))| *
        ((dAlembertReal (s + y * t) + dAlembertReal (s - y * t)) * Real.exp (s / 2))
      ≤ Real.exp (y ^ 2 / 2) *
          ((16 * (1 + |y|) * Real.exp (π * |y|) * Real.exp (-((π - 1) * |s|))) * Real.exp (|s| / 2)) := by
        gcongr
    _ = Real.exp (y ^ 2 / 2) *
          (16 * (1 + |y|) * Real.exp (π * |y|) * Real.exp (-((π - 3 / 2) * |0 - s|))) := by
        rw [zero_sub, abs_neg, mul_assoc (16 * (1 + |y|) * Real.exp (π * |y|)), ← Real.exp_add]
        congr 3
        ring

/-- The integrable dominator of the pole-weighted light-cone channel. -/
theorem integrable_poleDominator (y : ℝ) :
    Integrable fun s : ℝ =>
      16 * (1 + |y|) * Real.exp (π * |y|) * Real.exp (-((π - 3 / 2) * |0 - s|)) := by
  have hβ : 0 < π - 3 / 2 := by linarith [Real.pi_gt_three]
  exact (integrable_exp_neg_mul_abs_sub hβ 0).const_mul _

/-- The d'Alembert pair `D(s+y) + D(s−y)` weighted by the pole density is integrable. -/
theorem integrable_dAlembert_pair_mul_exp_half (y : ℝ) :
    Integrable fun s : ℝ => (dAlembertReal (s + y) + dAlembertReal (s - y)) * Real.exp (s / 2) := by
  refine ((integrable_dAlembertReal_add_mul_exp_half y).add
    (integrable_dAlembertReal_sub_mul_exp_half y)).congr (Eventually.of_forall fun s => ?_)
  simp only [Pi.add_apply]
  ring

/-- The light-cone tail of the prime kernel, as a function of the space variable. -/
def lightConeTail (y s : ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
    (dAlembertReal (s + y * t) + dAlembertReal (s - y * t))

theorem chmdPrimeKernel_eq_pair_sub_tail (y s : ℝ) :
    chmdPrimeKernel y s = (dAlembertReal (s + y) + dAlembertReal (s - y)) - y ^ 2 / 2 * lightConeTail y s := by
  rw [chmdPrimeKernel_eq_lightCone]
  rfl

theorem continuous_lightConeTail (y : ℝ) : Continuous (lightConeTail y) := by
  unfold lightConeTail
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun s t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
      (dAlembertReal (s + y * t) + dAlembertReal (s - y * t)))
    ((continuous_lightConeBesselReal.comp (by fun_prop)).mul
      ((continuous_dAlembertReal.comp (by fun_prop)).add (continuous_dAlembertReal.comp (by fun_prop))))
    _ _

theorem continuous_chmdPrimeKernel_right (y : ℝ) : Continuous fun s => chmdPrimeKernel y s := by
  have h : (fun s => chmdPrimeKernel y s) = fun s =>
      (dAlembertReal (s + y) + dAlembertReal (s - y)) - y ^ 2 / 2 * lightConeTail y s :=
    funext fun s => chmdPrimeKernel_eq_pair_sub_tail y s
  rw [h]
  exact ((continuous_dAlembertReal.comp (by fun_prop)).add (continuous_dAlembertReal.comp (by fun_prop))).sub
    (continuous_const.mul (continuous_lightConeTail y))

theorem abs_lightConeTail_mul_exp_half_le (y s : ℝ) :
    |lightConeTail y s * Real.exp (s / 2)| ≤ 2 * (Real.exp (y ^ 2 / 2) *
      (16 * (1 + |y|) * Real.exp (π * |y|) * Real.exp (-((π - 3 / 2) * |0 - s|)))) := by
  unfold lightConeTail
  rw [← intervalIntegral.integral_mul_const]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
    (C := Real.exp (y ^ 2 / 2) *
      (16 * (1 + |y|) * Real.exp (π * |y|) * Real.exp (-((π - 3 / 2) * |0 - s|))))
    (f := fun t => lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
      (dAlembertReal (s + y * t) + dAlembertReal (s - y * t)) * Real.exp (s / 2)) fun t ht => by
      rw [mul_assoc]
      exact lightCone_pair_exp_half_le y (mem_uIoc_neg_one_one_abs_le ht) s
  rw [Real.norm_eq_abs] at h
  simpa [abs_of_pos (by norm_num : (0 : ℝ) < 1 - -1), show (1 : ℝ) - -1 = 2 by norm_num,
    mul_comm] using h

theorem integrable_lightConeTail_mul_exp_half (y : ℝ) :
    Integrable fun s : ℝ => lightConeTail y s * Real.exp (s / 2) := by
  refine (((integrable_poleDominator y).const_mul (Real.exp (y ^ 2 / 2))).const_mul 2).mono'
    ((continuous_lightConeTail y).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs]
  exact abs_lightConeTail_mul_exp_half_le y s

/-- The pole-weighted prime kernel is integrable on the whole line. -/
theorem integrable_chmdPrimeKernel_mul_exp_half (y : ℝ) :
    Integrable fun s : ℝ => chmdPrimeKernel y s * Real.exp (s / 2) := by
  have h := (integrable_dAlembert_pair_mul_exp_half y).sub
    ((integrable_lightConeTail_mul_exp_half y).const_mul (y ^ 2 / 2))
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp only [Pi.sub_apply]
  rw [chmdPrimeKernel_eq_pair_sub_tail]
  ring

/-- Fubini for the pole-weighted light-cone tail:
`∫ T_y(s) e^{s/2} ds = ∫_{-1}^{1} B(2y²(1−t²)) (2/cos²(1/4)) cosh(yt/2) dt`. -/
theorem integral_lightConeTail_mul_exp_half (y : ℝ) :
    ∫ s : ℝ, lightConeTail y s * Real.exp (s / 2) =
      ∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
        (2 / Real.cos (1 / 4) ^ 2 * Real.cosh (y * t / 2)) := by
  set Bc : ℝ → ℝ := fun t => lightConeBesselReal (2 * y ^ 2 * (1 - clampUnit t ^ 2)) with hBc
  have hBc_cont : Continuous Bc := continuous_lightConeBesselReal.comp (by fun_prop)
  set F : ℝ → ℝ → ℝ := fun t s => Bc t *
    ((dAlembertReal (s + y * clampUnit t) + dAlembertReal (s - y * clampUnit t)) * Real.exp (s / 2))
    with hF
  have hprod : Integrable (Function.uncurry F) ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod volume) := by
    refine (Integrable.mul_prod (f := fun _ : ℝ => Real.exp (y ^ 2 / 2))
      (g := fun s => 16 * (1 + |y|) * Real.exp (π * |y|) * Real.exp (-((π - 3 / 2) * |0 - s|)))
      continuous_const.integrableOn_uIoc (integrable_poleDominator y)).mono' ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      exact (hBc_cont.comp continuous_fst).mul
        (((continuous_dAlembertReal.comp (by fun_prop)).add
          (continuous_dAlembertReal.comp (by fun_prop))).mul (by fun_prop))
    · refine Eventually.of_forall fun p => ?_
      rcases p with ⟨t, s⟩
      simp only [Function.uncurry_apply_pair, hF, hBc]
      exact lightCone_pair_exp_half_le y (abs_clampUnit_le t) s
  have hswap := MeasureTheory.intervalIntegral_integral_swap hprod
  -- left side: pull the exponential inside and unclamp
  have hleft : ∫ s : ℝ, lightConeTail y s * Real.exp (s / 2) =
      ∫ s : ℝ, ∫ t in (-1 : ℝ)..1, F t s := by
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [lightConeTail]
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun t ht => ?_
    simp only [hF, hBc, clampUnit_of_mem ht]
    ring
  -- right side: evaluate the inner integral by the massless pole law
  have hright : ∀ t : ℝ, ∫ s : ℝ, F t s =
      Bc t * (2 / Real.cos (1 / 4) ^ 2 * Real.cosh (y * clampUnit t / 2)) := by
    intro t
    simp only [hF]
    rw [integral_const_mul, integral_dAlembert_pair_mul_exp_half]
  rw [hleft, ← hswap]
  simp_rw [hright]
  refine intervalIntegral.integral_congr fun t ht => ?_
  simp only [hBc, clampUnit_of_mem ht]

/-- **Klein–Gordon pole law.**  The Klein–Gordon propagation of the prime-number-theorem density
`e^{s/2} ds` through the sech² kernel is exactly the ζ-pole wave:
`∫ K_y(s) e^{s/2} ds = chmdPoleWave y = (2/cos²(1/4)) cos(y √(7/4))`. -/
theorem integral_chmdPrimeKernel_mul_exp_half (y : ℝ) :
    ∫ s : ℝ, chmdPrimeKernel y s * Real.exp (s / 2) = chmdPoleWave y := by
  have hsplit : ∫ s : ℝ, chmdPrimeKernel y s * Real.exp (s / 2) =
      (∫ s : ℝ, (dAlembertReal (s + y) + dAlembertReal (s - y)) * Real.exp (s / 2)) -
        y ^ 2 / 2 * ∫ s : ℝ, lightConeTail y s * Real.exp (s / 2) := by
    rw [← integral_const_mul, ← integral_sub (integrable_dAlembert_pair_mul_exp_half y)
      ((integrable_lightConeTail_mul_exp_half y).const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only
    rw [chmdPrimeKernel_eq_pair_sub_tail]
    ring
  rw [hsplit, integral_dAlembert_pair_mul_exp_half, integral_lightConeTail_mul_exp_half,
    chmdPoleWave_eq, cos_mul_sqrt_seven_fourths_eq_lightCone]
  have hc : ∫ t in (-1 : ℝ)..1, lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) *
      (2 / Real.cos (1 / 4) ^ 2 * Real.cosh (y * t / 2)) =
      2 / Real.cos (1 / 4) ^ 2 * ∫ t in (-1 : ℝ)..1,
        lightConeBesselReal (2 * y ^ 2 * (1 - t ^ 2)) * Real.cosh (y * t / 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [hc]
  ring

/-- Spatial form of the pole law: at the space point `u` the pole density propagates to the
Klein–Gordon mode `e^{u/2} · chmdPoleWave y`. -/
theorem integral_chmdPrimeKernel_sub_mul_exp_half (y u : ℝ) :
    ∫ s : ℝ, chmdPrimeKernel y (s - u) * Real.exp (s / 2) = Real.exp (u / 2) * chmdPoleWave y := by
  have h := integral_sub_right_eq_self (μ := volume)
    (fun s : ℝ => chmdPrimeKernel y s * Real.exp (s / 2) * Real.exp (u / 2)) u
  have hl : ∫ s : ℝ, chmdPrimeKernel y (s - u) * Real.exp (s / 2) =
      ∫ s : ℝ, chmdPrimeKernel y (s - u) * Real.exp ((s - u) / 2) * Real.exp (u / 2) := by
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hl, h, integral_mul_const, integral_chmdPrimeKernel_mul_exp_half]
  ring

/-! ## Section 6: the Chebyshev-discrepancy transport law -/

theorem chmdPrimeKernel_neg_right (y s : ℝ) : chmdPrimeKernel y (-s) = chmdPrimeKernel y s := by
  unfold chmdPrimeKernel
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only [mul_neg, Real.cos_neg]

/-- The prime kernel is uniformly bounded by the total sech² mass `4/π`. -/
theorem abs_chmdPrimeKernel_le (y u : ℝ) : |chmdPrimeKernel y u| ≤ 4 / π := by
  unfold chmdPrimeKernel
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
  have h : ‖∫ r : ℝ, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * u)‖ ≤
      ∫ r : ℝ, sechSqHalf r := by
    refine norm_integral_le_of_norm_le integrable_sechSqHalf (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (sechSqHalf_pos r)]
    have hc1 := Real.abs_cos_le_one (y * Real.sqrt (r ^ 2 + 2))
    have hc2 := Real.abs_cos_le_one (r * u)
    have hs := (sechSqHalf_pos r).le
    calc |Real.cos (y * Real.sqrt (r ^ 2 + 2))| * sechSqHalf r * |Real.cos (r * u)|
        ≤ 1 * sechSqHalf r * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hc1 hs) hc2 (abs_nonneg _) (by positivity)
      _ = sechSqHalf r := by ring
  rw [integral_sechSqHalf, Real.norm_eq_abs] at h
  calc 1 / π * |∫ r : ℝ, Real.cos (y * Real.sqrt (r ^ 2 + 2)) * sechSqHalf r * Real.cos (r * u)|
      ≤ 1 / π * 4 := mul_le_mul_of_nonneg_left h (by positivity)
    _ = 4 / π := by ring

theorem integrable_chmdPrimeKernel_mul_exp_neg_half (y : ℝ) :
    Integrable fun s : ℝ => chmdPrimeKernel y s * Real.exp (-(s / 2)) := by
  refine (integrable_chmdPrimeKernel_mul_exp_half y).comp_neg.congr (Eventually.of_forall fun s => ?_)
  simp only [chmdPrimeKernel_neg_right]
  ring_nf

/-- The pole shadow `∫_0^∞ K_y(s) e^{−s/2} ds`: the pole density on the prime-free half-line,
transported to the origin. -/
def poleShadow (y : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), chmdPrimeKernel y s * Real.exp (-(s / 2))

/-- The Klein–Gordon transport of the `√`-weighted Chebyshev discrepancy measure
`Σ_{n} (Λ(n)/√n) δ_{log n} − e^{s/2} ds` on `(0, ∞)`:
`Σ_n (Λ(n)/√n) K_y(log n) − ∫_0^∞ K_y(s) e^{s/2} ds`. -/
def chebyshevDiscrepancyTransport (y : ℝ) : ℝ :=
  (∑' n : ℕ, chmdPrimeWeight n * chmdPrimeKernel y (Real.log n)) -
    ∫ s in Ioi (0 : ℝ), chmdPrimeKernel y s * Real.exp (s / 2)

/-- Half-line split of the pole law: `chmdPoleWave y = ∫_0^∞ K_y e^{s/2} + poleShadow y`. -/
theorem chmdPoleWave_eq_integral_Ioi_add_poleShadow (y : ℝ) :
    chmdPoleWave y = (∫ s in Ioi (0 : ℝ), chmdPrimeKernel y s * Real.exp (s / 2)) + poleShadow y := by
  have hint := integrable_chmdPrimeKernel_mul_exp_half y
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ)) hint.integrableOn hint.integrableOn
  have hrefl : ∫ s in Iic (0 : ℝ), chmdPrimeKernel y s * Real.exp (s / 2) = poleShadow y := by
    unfold poleShadow
    have h := integral_comp_neg_Iic (0 : ℝ) (fun s => chmdPrimeKernel y s * Real.exp (-(s / 2)))
    rw [neg_zero] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Iic fun s _ => ?_
    simp only [chmdPrimeKernel_neg_right, neg_div, neg_neg]
  rw [← integral_chmdPrimeKernel_mul_exp_half, ← hsplit, hrefl, add_comm]

/-- **The Chebyshev-discrepancy transport law.**  The Klein–Gordon prime wave is the pole wave plus
the transported `√`-weighted Chebyshev discrepancy, minus the bounded pole shadow:
`chmdPrimeWave y = chmdPoleWave y + chebyshevDiscrepancyTransport y − poleShadow y`. -/
theorem chmdPrimeWave_eq_chmdPoleWave_add_transport (y : ℝ) :
    chmdPrimeWave y = chmdPoleWave y + chebyshevDiscrepancyTransport y - poleShadow y := by
  rw [chmdPrimeWave_eq_tsum_kernel, chmdPoleWave_eq_integral_Ioi_add_poleShadow]
  unfold chebyshevDiscrepancyTransport
  ring

theorem integral_Ioi_exp_neg_half : ∫ s in Ioi (0 : ℝ), Real.exp (-(s / 2)) = 2 := by
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 0 (by norm_num : (0 : ℝ) < 1 / 2)
  simp only [mul_zero, integral_exp_neg_Ioi, neg_zero, Real.exp_zero, smul_eq_mul, mul_one] at h
  have h2 : ∫ s in Ioi (0 : ℝ), Real.exp (-(s / 2)) = ∫ x in Ioi (0 : ℝ), Real.exp (-(1 / 2 * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    congr 1
    ring
  rw [h2, h]
  norm_num

/-- The pole shadow is uniformly bounded by `8/π`. -/
theorem abs_poleShadow_le (y : ℝ) : |poleShadow y| ≤ 8 / π := by
  unfold poleShadow
  have hint : IntegrableOn (fun s : ℝ => 4 / π * Real.exp (-(s / 2))) (Ioi (0 : ℝ)) := by
    have h : IntegrableOn (fun x : ℝ => 4 / π * Real.exp (-(1 / 2) * x)) (Ioi (0 : ℝ)) :=
      (exp_neg_integrableOn_Ioi (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (4 / π)
    refine MeasureTheory.IntegrableOn.congr_fun h (fun s _ => ?_) measurableSet_Ioi
    congr 2
    ring
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun s => chmdPrimeKernel y s * Real.exp (-(s / 2))) hint
    (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (abs_chmdPrimeKernel_le y s) (Real.exp_pos _).le)
  rw [Real.norm_eq_abs, integral_const_mul, integral_Ioi_exp_neg_half] at h
  calc |∫ s in Ioi (0 : ℝ), chmdPrimeKernel y s * Real.exp (-(s / 2))| ≤ 4 / π * 2 := h
    _ = 8 / π := by ring

/-- **Riemann hypothesis through the transported Chebyshev discrepancy (lower form).** -/
theorem riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddBelow :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ y : ℝ, 0 ≤ y → -M ≤ chebyshevDiscrepancyTransport y := by
  rw [riemannHypothesis_iff_chmdPrimeWave_bddBelow]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M + 2 / Real.cos (1 / 4) ^ 2 + 8 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_chmdPoleWave_le y
    have h3 := abs_poleShadow_le y
    have h4 := chmdPrimeWave_eq_chmdPoleWave_add_transport y
    rw [abs_le] at h2 h3
    linarith
  · rintro ⟨M, hM⟩
    refine ⟨M + 2 / Real.cos (1 / 4) ^ 2 + 8 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_chmdPoleWave_le y
    have h3 := abs_poleShadow_le y
    have h4 := chmdPrimeWave_eq_chmdPoleWave_add_transport y
    rw [abs_le] at h2 h3
    linarith

/-- **Riemann hypothesis through the transported Chebyshev discrepancy (upper form).** -/
theorem riemannHypothesis_iff_chebyshevDiscrepancyTransport_bddAbove :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ y : ℝ, 0 ≤ y → chebyshevDiscrepancyTransport y ≤ M := by
  rw [riemannHypothesis_iff_chmdPrimeWave_bddAbove]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M + 2 / Real.cos (1 / 4) ^ 2 + 8 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_chmdPoleWave_le y
    have h3 := abs_poleShadow_le y
    have h4 := chmdPrimeWave_eq_chmdPoleWave_add_transport y
    rw [abs_le] at h2 h3
    linarith
  · rintro ⟨M, hM⟩
    refine ⟨M + 2 / Real.cos (1 / 4) ^ 2 + 8 / π, fun y hy => ?_⟩
    have h1 := hM y hy
    have h2 := abs_chmdPoleWave_le y
    have h3 := abs_poleShadow_le y
    have h4 := chmdPrimeWave_eq_chmdPoleWave_add_transport y
    rw [abs_le] at h2 h3
    linarith

end

end RHTower.CHMDChebyshevTransport
