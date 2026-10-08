import GaloisForLFunctions.RHTower.WeilWorkPBAPJointMiddleCutoff

/-!
# Low and high frequencies of the actual cutoff-grid error

The full logarithmic quadrature bound pays endpoint coverage and the
literal fixed-cutoff derivatives. Low frequencies have an eventually
nonnegative sublinear loss after the exact two-pole factor. At high
frequencies, nonnegative cutoff mass preserves the exact plateau integral;
all remaining terms are paid, leaving three quarters of L in the logarithmic
symbol above the growing ceiling. Global finite bounds justify subsequent
integration against source Fourier densities.

This completes the scalar frequency-band estimates, not the two-source
energy identity or the PBAP positivity goal.
-/

open Real Set Filter Topology MeasureTheory
noncomputable section
namespace RHTower.WeilWorkPBAP

private theorem cutoff_fourier_interval (L t a z : ℝ) {W : ℝ} (hW : 0 < W)
    (ha : a ≤ -2*W) (hz : 2*W ≤ z) :
    (∫ y in a..z, (jointFixedCutoff L W y:ℂ)*Complex.exp (((t*y:ℝ):ℂ)*Complex.I)) =
      ∫ y : ℝ, (jointFixedCutoff L W y:ℂ)*Complex.exp (((t*y:ℝ):ℂ)*Complex.I) := by
  have haz : a ≤ z := by linarith
  rw [intervalIntegral.integral_of_le haz, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hv : jointFixedCutoff L W y = 0 := by
    by_contra h
    have hs := jointFixedCutoff_tsupport hW
      (subset_closure (show y ∈ Function.support (jointFixedCutoff L W) from h))
    exact hy ⟨ha.trans hs.1, hs.2.trans hz⟩
  simp only [hv, Complex.ofReal_zero, zero_mul]

/-- Every frequency has the literal complex quadrature bound on the actual interval. -/
theorem eventually_jointCutoffFourierError_quadrature :
    ∃ C > 0, ∀ b : ℝ, 0 < b → ∀ᶠ L : ℝ in atTop, ∀ t : ℝ,
      ‖jointCutoffFourierError L (jointUniformWidth b L) t‖ ≤
        C*(1+(1+|t|)*jointUniformWidth b L)/exp L := by
  obtain ⟨C, hC, hcut⟩ := jointFixedCutoff_uniform_bounds
  let G : ℝ := 4*exp 1+3
  have hG : 0 < G := by dsimp only [G]; positivity
  refine ⟨4*G*C, by positivity, ?_⟩
  intro b hb
  filter_upwards [eventually_jointUniformWidth_grid_geometry hb,
    eventually_jointUniformWidth_grid_bounds hb,
    eventually_jointUniformWidth_log_cover hb] with L hg hbds hcover
  intro t
  let W := jointUniformWidth b L
  let n := ⌊exp L*exp (-2*W)⌋₊
  let m := ⌈exp L*exp (2*W)⌉₊+1
  have hW : 0 < W := hbds.2.1
  have hW1 : W ≤ 1 := hbds.2.2.1.trans (by norm_num)
  have hn : 1 ≤ n := (by norm_num : (1:ℕ) ≤ 2).trans hg.1
  have hnm : n ≤ m := hg.2.2.2.1.le
  have hq := joint_log_fourier_quadrature (jointFixedCutoff L W) L t hn hnm
    ((jointFixedCutoff_contDiff L W).differentiable (by simp)) hC.le (by positivity)
    (fun y => (hcut L W hW hW1 y).1) (fun y => (hcut L W hW hW1 y).2.1)
  rw [cutoff_fourier_interval L t _ _ hW hcover.1 hcover.2] at hq
  have hq' : ‖jointCutoffFourierError L W t‖ ≤
      ((m-n:ℕ):ℝ)*((C/W+(1+|t|)*C)/(n:ℝ)^2) := by
    simpa only [jointCutoffFourierError, jointCutoffGridFourier,
      Complex.ofReal_div, Complex.ofReal_natCast] using hq
  calc
    _ ≤ ((m-n:ℕ):ℝ)*((C/W+(1+|t|)*C)/(n:ℝ)^2) := hq'
    _ ≤ (G*exp L*W)*((C/W+(1+|t|)*C)/(exp L/2)^2) := by
      gcongr
      · exact hg.2.2.2.2.2.2
      · exact hg.2.1
    _ = _ := by field_simp; ring

/-- Low frequencies pay only the width divided by sqrt(L), plus exponential quadrature error. -/
theorem eventually_jointCutoffFourierError_low :
    ∃ C > 0, ∀ b : ℝ, 0 < b → ∀ᶠ L : ℝ in atTop, ∀ t : ℝ,
      |t| ≤ exp L/sqrt L →
        ‖jointCutoffFourierError L (jointUniformWidth b L) t‖ ≤
          C*(2*exp (-L)+jointUniformWidth b L/sqrt L) := by
  obtain ⟨C, hC, hquad⟩ := eventually_jointCutoffFourierError_quadrature
  refine ⟨C, hC, ?_⟩
  intro b hb
  filter_upwards [hquad b hb, eventually_jointUniformWidth_grid_bounds hb,
    eventually_gt_atTop (0:ℝ)] with L hq hbds hL
  intro t ht
  let W := jointUniformWidth b L
  have hW : 0 < W := hbds.2.1
  have hW1 : W ≤ 1 := hbds.2.2.1.trans (by norm_num)
  calc
    _ ≤ C*(1+(1+|t|)*W)/exp L := hq t
    _ ≤ C*(2+(exp L/sqrt L)*W)/exp L := by
      apply div_le_div_of_nonneg_right _ (exp_pos L).le
      apply mul_le_mul_of_nonneg_left _ hC.le
      nlinarith [mul_le_mul_of_nonneg_right ht hW.le]
    _ = _ := by rw [exp_neg]; field_simp; ring

private theorem tendsto_loglog_div_sqrt :
    Tendsto (fun L : ℝ => log (log L)/sqrt L) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun L : ℝ => log L/sqrt L) atTop (𝓝 0) := by
    simpa only [sqrt_eq_rpow, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop 1 (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [(tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop (0:ℝ)]
      with L hL
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
    exact div_le_div_of_nonneg_right (log_le_self (log_nonneg hL)) (sqrt_nonneg L)

theorem tendsto_jointCutoff_low_error_scale (b : ℝ) :
    Tendsto (fun L : ℝ => exp (L/2)*
      (2*exp (-L)+jointUniformWidth b L/sqrt L)/L) atTop (𝓝 0) := by
  have htail : Tendsto (fun L : ℝ => exp (-L/2)/L) atTop (𝓝 0) := by
    have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-1) (1/2) (by norm_num)
    convert ht using 1
    funext L
    rw [Real.rpow_neg_one, show -(1/2:ℝ)*L = -L/2 by ring]
    ring
  have ht := (htail.const_mul 2).add (tendsto_loglog_div_sqrt.const_mul b)
  simp only [mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  have he1 : exp (L/2)*exp (-L) = exp (-L/2) := by
    rw [← exp_add]
    congr 1
    ring
  have he2 : exp (L/2)*exp (-L/2) = 1 := by
    rw [← exp_add, show L/2+ -L/2 = 0 by ring, exp_zero]
  have hw : exp (L/2)*jointUniformWidth b L = b*L*log (log L) := by
    unfold jointUniformWidth
    calc
      _ = (b*L*log (log L))*(exp (L/2)*exp (-L/2)) := by ring
      _ = _ := by rw [he2, mul_one]
  symm
  calc
    _ = (2*(exp (L/2)*exp (-L))+(exp (L/2)*jointUniformWidth b L)/sqrt L)/L := by ring
    _ = _ := by rw [he1, hw]; field_simp

theorem tendsto_jointCutoff_low_pole_scale {b : ℝ} (hb : 0 < b) :
    Tendsto (fun L : ℝ => 2*cosh (L/2)*
      (2*exp (-L)+jointUniformWidth b L/sqrt L)/L) atTop (𝓝 0) := by
  have hmajor := (tendsto_jointCutoff_low_error_scale b).const_mul 2
  simp only [mul_zero] at hmajor
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [eventually_jointUniformWidth_grid_bounds hb,
      eventually_gt_atTop (0:ℝ)] with L hw hL
    have hW := hw.2.1
    have hp := cosh_pos (L/2)
    positivity
  · filter_upwards [eventually_jointUniformWidth_grid_bounds hb,
      eventually_gt_atTop (0:ℝ)] with L hw hL
    have hW := hw.2.1
    have hh : cosh (L/2) ≤ exp (L/2) := by
      rw [Real.cosh_eq]
      have he : exp (-(L/2)) ≤ exp (L/2) := exp_le_exp.mpr (by linarith)
      linarith
    calc
      _ ≤ 2*exp (L/2)*(2*exp (-L)+jointUniformWidth b L/sqrt L)/L := by gcongr
      _ = _ := by ring

theorem exists_jointCutoff_low_loss {b : ℝ} (hb : 0 < b) :
    ∃ r : ℝ → ℝ, Tendsto (fun L => r L/L) atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, 0 ≤ r L ∧ ∀ t : ℝ, |t| ≤ exp L/sqrt L →
        2*cosh (L/2)*‖jointCutoffFourierError L (jointUniformWidth b L) t‖ ≤ r L := by
  obtain ⟨C, hC, herror⟩ := eventually_jointCutoffFourierError_low
  let r : ℝ → ℝ := fun L => C*(2*cosh (L/2)*
    (2*exp (-L)+jointUniformWidth b L/sqrt L))
  refine ⟨r, ?_, ?_⟩
  · have ht := (tendsto_jointCutoff_low_pole_scale hb).const_mul C
    simpa only [r, mul_div_assoc, mul_zero] using ht
  · filter_upwards [herror b hb, eventually_jointUniformWidth_grid_bounds hb] with L he hw
    have hW := hw.2.1
    have hp := cosh_pos (L/2)
    refine ⟨by dsimp only [r]; positivity, ?_⟩
    intro t ht
    exact (mul_le_mul_of_nonneg_left (he t ht) (by positivity)).trans_eq (by dsimp only [r]; ring)

/-- The nonnegative literal cutoff bounds every grid frequency by its zero-frequency mass. -/
theorem norm_jointCutoffGridFourier_le_zero (L W t : ℝ) :
    ‖jointCutoffGridFourier L W t‖ ≤ ‖jointCutoffGridFourier L W 0‖ := by
  let s := Finset.Ico ⌊exp L*exp (-2*W)⌋₊ (⌈exp L*exp (2*W)⌉₊+1)
  let w : ℕ → ℝ := fun j => jointFixedCutoff L W (log j-L)/(j:ℝ)
  have hw (j : ℕ) : 0 ≤ w j := div_nonneg (jointFixedCutoff_nonneg L W _) (Nat.cast_nonneg j)
  have he : jointCutoffGridFourier L W 0 = ((∑ j ∈ s, w j : ℝ):ℂ) := by
    change (∑ j ∈ s, (w j:ℂ)*Complex.exp (((0*(log j-L):ℝ):ℂ)*Complex.I)) = _
    simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one]
    push_cast
    rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun j _ => hw j))]
  change ‖∑ j ∈ s, (w j:ℂ)*Complex.exp (((t*(log j-L):ℝ):ℂ)*Complex.I)‖ ≤ _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _hj
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw j),
    Complex.norm_exp_ofReal_mul_I, mul_one]

private theorem grid_zero_mass_bound (L W : ℝ) :
    ‖jointCutoffGridFourier L W 0‖ ≤
      ‖jointCutoffFourierError L W 0‖+∫ y : ℝ, jointFixedCutoff L W y := by
  have he : jointCutoffFourierError L W 0 =
      jointCutoffGridFourier L W 0-((∫ y : ℝ, jointFixedCutoff L W y):ℝ) := by
    simp only [jointCutoffFourierError, zero_mul, Complex.ofReal_zero,
      Complex.exp_zero, mul_one, integral_complex_ofReal]
  have hi : 0 ≤ ∫ y : ℝ, jointFixedCutoff L W y := integral_nonneg (jointFixedCutoff_nonneg L W)
  calc
    _ = ‖jointCutoffFourierError L W 0+(((∫ y : ℝ, jointFixedCutoff L W y):ℝ):ℂ)‖ := by
      rw [he, sub_add_cancel]
    _ ≤ ‖jointCutoffFourierError L W 0‖+‖(((∫ y : ℝ, jointFixedCutoff L W y):ℝ):ℂ)‖ := norm_add_le _ _
    _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hi]

/-- The high-frequency envelope retains the exact leading plateau mass. -/
theorem eventually_jointCutoffFourierError_high_mass :
    ∃ C > 0, ∀ b : ℝ, 0 < b → ∀ᶠ L : ℝ in atTop, ∀ t : ℝ,
      exp L/sqrt L ≤ |t| →
        ‖jointCutoffFourierError L (jointUniformWidth b L) t‖ ≤
          (∫ y : ℝ, jointPlateau y)*jointUniformWidth b L+
            C*((jointUniformWidth b L)^2+exp (-L)) := by
  obtain ⟨C₁, hC₁, hquad⟩ := eventually_jointCutoffFourierError_quadrature
  obtain ⟨C₂, hC₂, hfour⟩ := eventually_jointFixedCutoff_fourier_middle
  refine ⟨4*exp 1+2*C₁+C₂, by positivity, ?_⟩
  intro b hb
  filter_upwards [hquad b hb, hfour b hb,
    eventually_jointUniformWidth_grid_bounds hb] with L hq hf hbds
  intro t ht
  let W := jointUniformWidth b L
  have hW : 0 < W := hbds.2.1
  have hW1 : W ≤ 1 := hbds.2.2.1.trans (by norm_num)
  have hzero : ‖jointCutoffFourierError L W 0‖ ≤ 2*C₁*exp (-L) := by
    calc
      _ ≤ C₁*(1+(1+|(0:ℝ)|)*W)/exp L := hq 0
      _ ≤ C₁*2/exp L := by simp only [abs_zero, add_zero, one_mul]; gcongr; linarith
      _ = _ := by rw [exp_neg]; ring
  have hmass : (∫ y : ℝ, jointFixedCutoff L W y) ≤
      W*(∫ y : ℝ, jointPlateau y)+4*exp 1*W^2 := by
    have h := (le_abs_self _).trans (jointFixedCutoff_integral_error L hW hW1)
    linarith
  have hg : ‖jointCutoffGridFourier L W t‖ ≤
      (∫ y : ℝ, jointPlateau y)*W+4*exp 1*W^2+2*C₁*exp (-L) := by
    have h := (norm_jointCutoffGridFourier_le_zero L W t).trans (grid_zero_mass_bound L W)
    linarith
  calc
    _ ≤ ‖jointCutoffGridFourier L W t‖+
        ‖∫ y : ℝ, (jointFixedCutoff L W y:ℂ)*Complex.exp (((t*y:ℝ):ℂ)*Complex.I)‖ := norm_sub_le _ _
    _ ≤ ((∫ y : ℝ, jointPlateau y)*W+4*exp 1*W^2+2*C₁*exp (-L))+C₂*exp (-L) :=
      add_le_add hg (hf t ht)
    _ = (∫ y : ℝ, jointPlateau y)*W+(4*exp 1)*W^2+(2*C₁+C₂)*exp (-L) := by ring
    _ ≤ (∫ y : ℝ, jointPlateau y)*W+(4*exp 1+2*C₁+C₂)*W^2+
        (4*exp 1+2*C₁+C₂)*exp (-L) := by gcongr <;> linarith [exp_pos (1:ℝ)]
    _ = _ := by ring

private theorem tendsto_loglog_mul_exp_neg :
    Tendsto (fun L : ℝ => log (log L)*exp (-L)) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun L : ℝ => L*exp (-L)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, neg_mul, one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 one_pos
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [(tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop (0:ℝ)]
      with L hL
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
    have hh := (log_le_self (log_nonneg hL)).trans (log_le_self (by linarith : (0:ℝ) ≤ L))
    exact mul_le_mul_of_nonneg_right hh (exp_pos _).le

/-- Quadratic cutoff-mass and exponential quadrature errors stay sublinear after both poles. -/
theorem tendsto_jointCutoff_high_remainder_scale (b : ℝ) :
    Tendsto (fun L : ℝ => 2*cosh (L/2)*
      ((jointUniformWidth b L)^2+exp (-L))/L) atTop (𝓝 0) := by
  have ht : Tendsto (fun L : ℝ => 2*exp (-L/2)/L) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-1) (1/2)
      (by norm_num)).const_mul 2
    simp only [mul_zero] at h
    convert h using 1
    funext L
    rw [Real.rpow_neg_one, show -(1/2:ℝ)*L = -L/2 by ring]
    ring
  have hp : Tendsto (fun L : ℝ => 2*b^2*L^3*exp (-L/2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3:ℕ) (1/2)
      (by norm_num)).const_mul (2*b^2)
    have he (L : ℝ) : -(1/2:ℝ)*L = -L/2 := by ring
    simpa only [Real.rpow_natCast, he, mul_zero, mul_assoc] using h
  have hmajor := hp.add ht
  simp only [add_zero] at hmajor
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    have hc := cosh_pos (L/2)
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ),
      (tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop (0:ℝ)] with L hL hll0
    change 0 ≤ log (log L) at hll0
    have hL0 : 0 < L := by linarith
    have hll : log (log L) ≤ L :=
      (log_le_self (log_nonneg hL)).trans (log_le_self hL0.le)
    have hh : cosh (L/2) ≤ exp (L/2) := by
      rw [Real.cosh_eq]
      have he : exp (-(L/2)) ≤ exp (L/2) := exp_le_exp.mpr (by linarith)
      linarith
    have he1 : exp (L/2)*exp (-L) = exp (-L/2) := by
      rw [← exp_add]
      congr 1
      ring
    have he2 : exp (L/2)*exp (-L/2) = 1 := by
      rw [← exp_add, show L/2+ -L/2 = 0 by ring, exp_zero]
    have hs : exp (L/2)*(jointUniformWidth b L)^2/L =
        b^2*L*(log (log L))^2*exp (-L/2) := by
      unfold jointUniformWidth
      calc
        _ = b^2*L*(log (log L))^2*(exp (L/2)*exp (-L/2))*exp (-L/2) := by
          field_simp
        _ = _ := by rw [he2, mul_one]
    calc
      _ ≤ 2*exp (L/2)*((jointUniformWidth b L)^2+exp (-L))/L := by gcongr
      _ = 2*(exp (L/2)*(jointUniformWidth b L)^2/L)+2*(exp (L/2)*exp (-L)/L) := by ring
      _ = 2*(b^2*L*(log (log L))^2*exp (-L/2))+2*(exp (-L/2)/L) := by rw [hs, he1]
      _ ≤ 2*(b^2*L*L^2*exp (-L/2))+2*(exp (-L/2)/L) := by gcongr
      _ = _ := by ring

private theorem width_exact_pole_scale (b L : ℝ) :
    2*cosh (L/2)*jointUniformWidth b L =
      b*L*log (log L)+b*L*log (log L)*exp (-L) := by
  have he1 : exp (L/2)*exp (-L/2) = 1 := by
    rw [← exp_add, show L/2+ -L/2 = 0 by ring, exp_zero]
  have he2 : exp (-L/2)*exp (-L/2) = exp (-L) := by
    rw [← exp_add]
    congr 1
    ring
  rw [Real.cosh_eq, jointUniformWidth, show -(L/2) = -L/2 by ring]
  calc
    _ = b*L*log (log L)*(exp (L/2)*exp (-L/2))+
        b*L*log (log L)*(exp (-L/2)*exp (-L/2)) := by ring
    _ = _ := by rw [he1, he2, mul_one]

/-- The high envelope has its exact leading coefficient and a paid sublinear remainder. -/
theorem exists_jointCutoff_high_loss {b : ℝ} (hb : 0 < b) :
    ∃ r : ℝ → ℝ, Tendsto (fun L => r L/L) atTop (𝓝 0) ∧
      ∀ᶠ L : ℝ in atTop, 0 ≤ r L ∧ ∀ t : ℝ, exp L/sqrt L ≤ |t| →
        2*cosh (L/2)*‖jointCutoffFourierError L (jointUniformWidth b L) t‖ ≤
          (∫ y : ℝ, jointPlateau y)*b*L*log (log L)+r L := by
  obtain ⟨C, hC, herror⟩ := eventually_jointCutoffFourierError_high_mass
  let A : ℝ := ∫ y : ℝ, jointPlateau y
  have hA : 0 < A := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) jointPlateau_integral_bounds.1
  let r : ℝ → ℝ := fun L => A*b*L*log (log L)*exp (-L)+
    C*(2*cosh (L/2)*((jointUniformWidth b L)^2+exp (-L)))
  have hlead : Tendsto (fun L : ℝ => A*b*L*log (log L)*exp (-L)/L) atTop (𝓝 0) := by
    have ht := tendsto_loglog_mul_exp_neg.const_mul (A*b)
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    field_simp
  refine ⟨r, ?_, ?_⟩
  · have ht := hlead.add ((tendsto_jointCutoff_high_remainder_scale b).const_mul C)
    simp only [mul_zero, add_zero] at ht
    convert ht using 1
    funext L
    dsimp only [r]
    ring
  · filter_upwards [herror b hb, eventually_gt_atTop (0:ℝ),
      (tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop (0:ℝ)] with L he hL hll
    change 0 ≤ log (log L) at hll
    have hp := cosh_pos (L/2)
    refine ⟨by dsimp only [r]; positivity, ?_⟩
    intro t ht
    calc
      _ ≤ 2*cosh (L/2)*(A*jointUniformWidth b L+C*((jointUniformWidth b L)^2+exp (-L))) :=
        mul_le_mul_of_nonneg_left (he t ht) (by positivity)
      _ = A*(2*cosh (L/2)*jointUniformWidth b L)+
          C*(2*cosh (L/2)*((jointUniformWidth b L)^2+exp (-L))) := by ring
      _ = _ := by rw [width_exact_pole_scale]; dsimp only [r, A]; ring

/-- Above the actual growing ceiling the error leaves three quarters of L in the log symbol. -/
theorem eventually_jointCutoffFourierError_high {b : ℝ} (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop, ∀ t : ℝ,
      exp (((∫ y : ℝ, jointPlateau y)*b*log (log L)+1)*L) ≤ |t| →
        2*cosh (L/2)*‖jointCutoffFourierError L (jointUniformWidth b L) t‖ ≤ log |t|-3*L/4 := by
  obtain ⟨r, hr, hbound⟩ := exists_jointCutoff_high_loss hb
  have hs := hr.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4))
  filter_upwards [hbound, hs, eventually_ge_atTop (1:ℝ),
    (tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop (0:ℝ)] with L h hs hL hll
  change 0 ≤ log (log L) at hll
  intro t ht
  have hL0 : 0 < L := by linarith
  have hR : 0 < sqrt L := sqrt_pos.mpr hL0
  have hR1 : 1 ≤ sqrt L := by nlinarith [sq_sqrt hL0.le, sqrt_nonneg L]
  have hA : 0 ≤ ∫ y : ℝ, jointPlateau y := le_trans (by norm_num : (0:ℝ) ≤ 2) jointPlateau_integral_bounds.1
  have hmid : exp L/sqrt L ≤ |t| := by
    calc
      _ ≤ exp L := (div_le_iff₀ hR).mpr (by nlinarith [exp_pos L])
      _ ≤ exp (((∫ y : ℝ, jointPlateau y)*b*log (log L)+1)*L) := by
        apply exp_le_exp.mpr
        have hp : 0 ≤ (∫ y : ℝ, jointPlateau y)*b*log (log L)*L := by positivity
        nlinarith
      _ ≤ _ := ht
  have hlog := log_le_log (exp_pos (((∫ y : ℝ, jointPlateau y)*b*log (log L)+1)*L)) ht
  rw [log_exp] at hlog
  have hsmall := (div_lt_iff₀ hL0).mp hs
  have he := h.2 t hmid
  nlinarith

theorem norm_jointFixedCutoff_fourier_le_mass (L W t : ℝ) :
    ‖∫ y : ℝ, (jointFixedCutoff L W y:ℂ)*Complex.exp (((t*y:ℝ):ℂ)*Complex.I)‖ ≤
      ∫ y : ℝ, jointFixedCutoff L W y := by
  calc
    _ ≤ ∫ y : ℝ, ‖(jointFixedCutoff L W y:ℂ)*Complex.exp (((t*y:ℝ):ℂ)*Complex.I)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (jointFixedCutoff_nonneg L W y), Complex.norm_exp_ofReal_mul_I, mul_one]

/-- A finite bound for every frequency, used to justify source-density integration. -/
theorem norm_jointCutoffFourierError_le_mass (L W t : ℝ) :
    ‖jointCutoffFourierError L W t‖ ≤
      ‖jointCutoffGridFourier L W 0‖+∫ y : ℝ, jointFixedCutoff L W y := by
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_jointCutoffGridFourier_le_zero L W t) (norm_jointFixedCutoff_fourier_le_mass L W t))

end RHTower.WeilWorkPBAP
