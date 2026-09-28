import GaloisForLFunctions.RHTower.ThetaRenewalResonanceDivisor
import GaloisForLFunctions.RHTower.ThetaHalfPortStieltjesSpectral
import GaloisForLFunctions.RHTower.ThetaHalfLinePortCrossings
import GaloisForLFunctions.RHTower.XiHorizontalStripDecay
import GaloisForLFunctions.HTGeometry.DiagonallyDominantPosDef

/-!
# The theta renewal feedback loop: exponential closure and infinite Pick index

With `A(λ) = (a + λ) D(λ)`, `B(λ) = (a - λ) D(-λ)`, `a = 1/4`, the two-ended renewal identity is
`Ξ(2iλ) = A(λ) + B(λ) = A(λ) [1 + K(λ)]`, `K = B/A`, with `D(±λ) ≠ 0` for `|Re λ| < a` (9).

* **(10), (11), (11a).** `B(x + iy) = conj A(-x + iy)`, `Re A(iy) = Ξ(2y)/2`, and
  `A(iy) = icy + H(-2y)`, `B(iy) = -icy + H(2y)` with `H` the one-sided theta connection; since
  `‖H(u)‖ ≤ 2k(0)/|u|`, the charge `v(y) = Im A(iy)` satisfies `v(y) - cy → 0`, `v(y)/y → c`, and
  `v > 0` on `(0, ∞)` by the quadrant law.
* **(11b).** For `b < a`, `κ < π/2`: `sup_{|x| ≤ b} |1 + K(x + iy)| ≤ C e^{-κ|y|}/(1 + |y|)`,
  from the horizontal decay of `Ξ` and the `1/|z|` decay of `N`.
* **(12).** At a critical zero, `∂_x g(0, y₀) = -2 v(y₀) X'(y₀)` for
  `g = |A|² - |B|²`, `X(y) = Ξ(2y)`; simple zeros of both slope signs above every height give
  `|K| > 1` and `|K| < 1` just right of the axis.
* **(13), (14).** The Pick-defect kernel `P_K(λ, μ) = (1 - K(λ) conj K(μ))/(λ + conj μ)` has
  boundary values `P_K(iy_j, iy_k) = 0` and diagonal limits `-X'(y_j)/v(y_j)`; by diagonal
  dominance, for each sign and every `n` some `n`-point Gram matrix is definite: infinite positive
  and negative index.
-/

open Complex Filter Topology Set MeasureTheory HurwitzZeta
open scoped ComplexConjugate ComplexOrder

namespace RHTower

noncomputable section

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## The feedback loop -/

/-- The seam-renormalized channel `A(λ) = (a + λ) D(λ)`, `a = 1/4`. -/
def thetaLoopA (lam : ℂ) : ℂ := (1 / 4 + lam) * thetaRenewalDenominator lam

/-- The reflected channel `B(λ) = (a - λ) D(-λ)`. -/
def thetaLoopB (lam : ℂ) : ℂ := (1 / 4 - lam) * thetaRenewalDenominator (-lam)

/-- The feedback loop `K(λ) = B(λ)/A(λ)`. -/
def thetaLoopK (lam : ℂ) : ℂ := thetaLoopB lam / thetaLoopA lam

theorem differentiable_thetaLoopA : Differentiable ℂ thetaLoopA := by
  unfold thetaLoopA
  exact (differentiable_const _).add differentiable_id |>.mul differentiable_thetaRenewalDenominator

/-- **(9), two-ended identity.** `Ξ(2iλ) = A(λ) + B(λ)` for every `λ`. -/
theorem XiC_two_I_mul_eq_thetaLoop (lam : ℂ) :
    XiC (2 * I * lam) = thetaLoopA lam + thetaLoopB lam := by
  have h := thetaRenewal_two_ended (-(I * lam))
  rw [show I * -(I * lam) = lam by linear_combination (-lam) * I_sq,
    show 2 * -(I * lam) = -(2 * I * lam) by ring, XiC_even] at h
  rw [← h, thetaLoopA, thetaLoopB]
  ring_nf

theorem thetaLoopA_ne_zero {lam : ℂ} (hlam : |lam.re| < 1 / 4) : thetaLoopA lam ≠ 0 := by
  have h1 : (1 / 4 : ℂ) + lam ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; rw [abs_lt] at hlam; linarith
  exact mul_ne_zero h1 (thetaRenewalDenominator_ne_zero (by rw [abs_lt] at hlam; linarith))

theorem thetaLoopB_ne_zero {lam : ℂ} (hlam : |lam.re| < 1 / 4) : thetaLoopB lam ≠ 0 := by
  have h1 : (1 / 4 : ℂ) - lam ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; rw [abs_lt] at hlam; linarith
  exact mul_ne_zero h1 (thetaRenewalDenominator_ne_zero (by
    simp only [neg_re]; rw [abs_lt] at hlam; linarith))

/-- **(9).** Throughout `|Re λ| < a`, `Ξ(2iλ) = (a + λ) D(λ) [1 + K(λ)]` with `D(±λ) ≠ 0`. -/
theorem XiC_two_I_mul_eq_loop {lam : ℂ} (hlam : |lam.re| < 1 / 4) :
    XiC (2 * I * lam) = thetaLoopA lam * (1 + thetaLoopK lam) := by
  rw [XiC_two_I_mul_eq_thetaLoop, thetaLoopK, mul_add, mul_one,
    mul_div_cancel₀ _ (thetaLoopA_ne_zero hlam)]

/-- **(10), realness.** `B(x + iy) = conj A(-x + iy)`. -/
theorem thetaLoopB_eq_conj (x y : ℝ) :
    thetaLoopB (x + y * I) = conj (thetaLoopA (-x + y * I)) := by
  rw [thetaLoopB, thetaLoopA, map_mul, ← thetaRenewalDenominator_conj]
  congr 1
  · apply Complex.ext
    · simp; ring
    · simp
  · congr 1; apply Complex.ext <;> simp

theorem thetaLoopB_I_mul (y : ℝ) : thetaLoopB (y * I) = conj (thetaLoopA (y * I)) := by
  simpa using thetaLoopB_eq_conj 0 y

/-- **(10).** `u(y) = Re A(iy) = Ξ(2y)/2`. -/
theorem re_thetaLoopA_I_mul (y : ℝ) : (thetaLoopA (y * I)).re = Xi (2 * y) / 2 := by
  have h := XiC_two_I_mul_eq_thetaLoop (y * I)
  rw [thetaLoopB_I_mul, show 2 * I * ((y : ℂ) * I) = -((2 * y : ℝ) : ℂ) by
    push_cast; linear_combination (2 * (y : ℂ)) * I_sq, XiC_even, XiC_ofReal] at h
  have := congrArg Complex.re h
  simp only [ofReal_re, add_re, conj_re] at this
  linarith

/-- The imaginary seam charge `v(y) = Im A(iy)`. -/
def thetaLoopCharge (y : ℝ) : ℝ := (thetaLoopA (y * I)).im

/-- **(11a).** `A(iy) = icy + H(-2y)` and `B(iy) = -icy + H(2y)`, `H` the one-sided connection. -/
theorem thetaLoopA_I_mul_eq (y : ℝ) :
    thetaLoopA (y * I) = I * (Θ 1 : ℂ) * y + thetaOneSidedConnection (-(2 * y) : ℝ) := by
  have h := thetaOneSidedConnection_two_mul_eq_denominator (-(y : ℂ))
  rw [show 2 * -(y : ℂ) = ((-(2 * y) : ℝ) : ℂ) by push_cast; ring,
    show -(I * -(y : ℂ)) = (y : ℂ) * I by ring] at h
  rw [h, thetaLoopA]
  ring

theorem thetaLoopB_I_mul_eq (y : ℝ) :
    thetaLoopB (y * I) = -(I * (Θ 1 : ℂ) * y) + thetaOneSidedConnection (2 * y : ℝ) := by
  have h := thetaOneSidedConnection_two_mul_eq_denominator (y : ℂ)
  rw [show 2 * (y : ℂ) = ((2 * y : ℝ) : ℂ) by push_cast; ring] at h
  rw [h, thetaLoopB, show -((y : ℂ) * I) = -(I * y) by ring]
  ring

/-- `v(y) = cy + Im H(-2y)`. -/
theorem thetaLoopCharge_eq (y : ℝ) :
    thetaLoopCharge y = Θ 1 * y + (thetaOneSidedConnection (-(2 * y) : ℝ)).im := by
  rw [thetaLoopCharge, thetaLoopA_I_mul_eq]
  simp

/-- **`v > 0` on the positive axis.** `v(y) = a Im D(iy) + y Re D(iy) > 0`. -/
theorem thetaLoopCharge_pos {y : ℝ} (hy : 0 < y) : 0 < thetaLoopCharge y := by
  have hq := thetaRenewalDenominator_quadrant (s := (y : ℂ) * I) (by simp) (by simpa using hy)
  rw [thetaLoopCharge, thetaLoopA]
  simp only [mul_im, add_re, add_im, div_ofNat_re, div_ofNat_im, one_re, one_im, mul_re,
    ofReal_re, ofReal_im, I_re, I_im, mul_zero, sub_zero, mul_one, add_zero]
  nlinarith [hq.1, hq.2.1]

/-! ## High-frequency behaviour (11), (11b) -/

/-- `‖H(u)‖ ≤ 2k(0)/|u|` on the real axis. -/
theorem norm_thetaOneSidedConnection_ofReal_le {u : ℝ} (hu : u ≠ 0) :
    ‖thetaOneSidedConnection u‖ ≤ 2 * thetaCuspFullSource 0 / |u| := by
  have hk := onePortSource_thetaCuspFullSource
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  rw [← onePortConnection_thetaCuspFullSource, hk.onePortConnection_eq (by simp) hu0, norm_mul,
    norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_div_mul_eq_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg u)
  rw [← hk.integral_neg_deriv, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on ?_
    (hk.integrableOn_deriv.neg.const_mul 2) measurableSet_Ioi fun x hx => ?_)
  · exact (hk.integrableOn_neg_deriv_mul (g := fun x : ℝ => 1 - cexp (I * u * x)) (by fun_prop)
      (C := 2) fun x hx => by
        calc ‖1 - cexp (I * u * x)‖ ≤ ‖(1 : ℂ)‖ + ‖cexp (I * u * x)‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by
              gcongr
              · simp
              · exact GaloisForLFunctions.HTGeometry.OnePortSource.norm_cexp_I_mul_le u
                  (by simp) hx.le
          _ = 2 := by norm_num).norm
  · have hω := neg_nonneg.mpr (hk.deriv_nonpos hx)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hω, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hω
    calc ‖1 - cexp (I * u * x)‖ ≤ ‖(1 : ℂ)‖ + ‖cexp (I * u * x)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
          gcongr
          · simp
          · exact GaloisForLFunctions.HTGeometry.OnePortSource.norm_cexp_I_mul_le u (by simp)
              (le_of_lt hx)
      _ = 2 := by norm_num

/-- **(11a).** `v(y) - cy → 0`: the seam charges cancel exactly. -/
theorem tendsto_thetaLoopCharge_sub :
    Tendsto (fun y => thetaLoopCharge y - Θ 1 * y) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun y => thetaCuspFullSource 0 / y) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with y hy
    rw [thetaLoopCharge_eq, add_sub_cancel_left, Real.norm_eq_abs]
    refine (abs_im_le_norm _).trans ((norm_thetaOneSidedConnection_ofReal_le
      (by linarith : -(2 * y) ≠ 0)).trans (le_of_eq ?_))
    rw [abs_neg, abs_of_pos (by linarith)]; field_simp
  · exact tendsto_const_nhds.div_atTop tendsto_id

/-- **(11).** `v(y)/y → c`. -/
theorem tendsto_thetaLoopCharge_div :
    Tendsto (fun y => thetaLoopCharge y / y) atTop (𝓝 (Θ 1)) := by
  have h := (tendsto_thetaLoopCharge_sub.div_atTop tendsto_id).const_add (Θ 1)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  simp only [id]
  field_simp
  ring

/-- **(11b).** On every closed inner strip the loop is `-1` to exponential accuracy: for
`b < 1/4` and `0 ≤ κ < π/2`, `sup_{|x| ≤ b} |1 + K(x + iy)| ≤ C e^{-κ|y|}/(1 + |y|)` for
large `|y|`. -/
theorem exists_norm_one_add_thetaLoopK_le {b κ : ℝ} (hb4 : b < 1 / 4) (hκ : 0 ≤ κ)
    (hκ2 : κ < Real.pi / 2) :
    ∃ C Y : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, |x| ≤ b → Y ≤ |y| →
      ‖1 + thetaLoopK (x + y * I)‖ ≤ C * Real.exp (-(κ * |y|)) / (1 + |y|) := by
  have hc := thetaSeam_pos
  obtain ⟨C₁, hC₁, hXi⟩ := exists_norm_XiC_horizontal_le (A := 2 * b) (δ := κ / 2) (by linarith)
    (by linarith) (by linarith)
  set M := thetaRenewalDecayConst b
  refine ⟨4 * C₁ / Θ 1, max 1 (2 * M / Θ 1), by positivity, fun x y hx hy => ?_⟩
  have hy1 : 1 ≤ |y| := le_trans (le_max_left _ _) hy
  have hyM : 2 * M / Θ 1 ≤ |y| := le_trans (le_max_right _ _) hy
  set lam : ℂ := x + y * I
  have hlre : lam.re = x := by simp [lam]
  have hlim : lam.im = y := by simp [lam]
  have hstrip : |lam.re| < 1 / 4 := by rw [hlre]; linarith
  have hA := thetaLoopA_ne_zero hstrip
  have hloop : 1 + thetaLoopK lam = XiC (2 * I * lam) / thetaLoopA lam := by
    rw [XiC_two_I_mul_eq_loop hstrip, mul_div_cancel_left₀ _ hA]
  have hX : ‖XiC (2 * I * lam)‖ ≤ C₁ * Real.exp (-(κ * |y|)) := by
    have h := hXi (-(2 * y)) (2 * x) (by rw [abs_mul, abs_two]; linarith)
    rw [show (((-(2 * y) : ℝ) : ℂ) + ((2 * x : ℝ) : ℂ) * I) = 2 * I * lam by
      simp only [lam]; push_cast; linear_combination (-2 * (y : ℂ)) * I_sq] at h
    refine h.trans (le_of_eq ?_)
    congr 2
    rw [abs_neg, abs_mul, abs_two]; ring
  have hN : ‖thetaRenewalLaplace lam‖ ≤ Θ 1 / 2 := by
    have hre : -b ≤ lam.re := by rw [hlre]; exact (abs_le.mp hx).1
    have h : ‖lam‖ * ‖thetaRenewalLaplace lam‖ ≤ M := norm_mul_thetaRenewalLaplace_le hre
    have hnorm : |y| ≤ ‖lam‖ := by rw [← hlim]; exact abs_im_le_norm lam
    have hlpos : 0 < ‖lam‖ := by linarith
    rw [div_le_iff₀ hc] at hyM
    have h2 : ‖thetaRenewalLaplace lam‖ ≤ M / ‖lam‖ := by
      rw [le_div_iff₀ hlpos]; linarith
    calc ‖thetaRenewalLaplace lam‖ ≤ M / ‖lam‖ := h2
      _ ≤ M / |y| := by
          have hM0 : 0 ≤ M :=
            le_trans (mul_nonneg hlpos.le (norm_nonneg (thetaRenewalLaplace lam))) h
          exact div_le_div_of_nonneg_left hM0 (by linarith) hnorm
      _ ≤ Θ 1 / 2 := by
          rw [div_le_div_iff₀ (by linarith) two_pos]; linarith
  have hD : Θ 1 / 2 ≤ ‖thetaRenewalDenominator lam‖ := by
    have h := norm_sub_norm_le (((Θ 1 : ℝ) : ℂ)) (thetaRenewalLaplace lam)
    rw [Complex.norm_real, Real.norm_of_nonneg hc.le] at h
    rw [thetaRenewalDenominator]; linarith
  have hAnorm : Θ 1 / 4 * (1 + |y|) ≤ ‖thetaLoopA lam‖ := by
    rw [thetaLoopA, norm_mul]
    have h1 : |y| ≤ ‖(1 / 4 : ℂ) + lam‖ := by
      have := abs_im_le_norm ((1 / 4 : ℂ) + lam)
      simpa [hlim] using this
    calc Θ 1 / 4 * (1 + |y|) ≤ |y| * (Θ 1 / 2) := by nlinarith
      _ ≤ ‖(1 / 4 : ℂ) + lam‖ * ‖thetaRenewalDenominator lam‖ :=
          mul_le_mul h1 hD (by positivity) (norm_nonneg _)
  rw [hloop, norm_div, div_le_div_iff₀ (norm_pos_iff.mpr hA) (by positivity)]
  calc ‖XiC (2 * I * lam)‖ * (1 + |y|) ≤ C₁ * Real.exp (-(κ * |y|)) * (1 + |y|) := by gcongr
    _ = 4 * C₁ / Θ 1 * Real.exp (-(κ * |y|)) * (Θ 1 / 4 * (1 + |y|)) := by field_simp
    _ ≤ 4 * C₁ / Θ 1 * Real.exp (-(κ * |y|)) * ‖thetaLoopA lam‖ := by gcongr

/-! ## The normal energy crossing (12) -/

/-- The loop energy `g(x, y) = |A(x + iy)|² - |B(x + iy)|²`. -/
def thetaLoopEnergy (x y : ℝ) : ℝ :=
  Complex.normSq (thetaLoopA (x + y * I)) - Complex.normSq (thetaLoopB (x + y * I))

/-- The critical slope `X'(y) = d/dy Ξ(2y)`. -/
def thetaLoopSlope (y : ℝ) : ℝ := deriv (fun y : ℝ => Xi (2 * y)) y

theorem thetaLoopEnergy_eq (x y : ℝ) :
    thetaLoopEnergy x y =
      Complex.normSq (thetaLoopA (x + y * I)) - Complex.normSq (thetaLoopA (-x + y * I)) := by
  rw [thetaLoopEnergy, thetaLoopB_eq_conj, Complex.normSq_conj]

theorem thetaLoopEnergy_zero (y : ℝ) : thetaLoopEnergy 0 y = 0 := by
  rw [thetaLoopEnergy_eq]; simp

theorem hasDerivAt_re_comp {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => (f t).re) f'.re x := by
  have := reCLM.hasFDerivAt.comp_hasDerivAt x hf
  simpa [Function.comp_def] using this

theorem hasDerivAt_im_comp {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => (f t).im) f'.im x := by
  have := imCLM.hasFDerivAt.comp_hasDerivAt x hf
  simpa [Function.comp_def] using this

theorem hasDerivAt_complexNormSq_comp {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun t => Complex.normSq (f t))
      (2 * ((f x).re * f'.re + (f x).im * f'.im)) x := by
  have hre := hasDerivAt_re_comp hf
  have him := hasDerivAt_im_comp hf
  have h := (hre.fun_mul hre).fun_add (him.fun_mul him)
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp [Complex.normSq_apply]

theorem hasDerivAt_thetaLoopA_shift (y : ℝ) (s : ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => thetaLoopA (s * t + y * I))
      (deriv thetaLoopA (s * x + y * I) * s) x := by
  have h := (differentiable_thetaLoopA (s * x + y * I)).hasDerivAt
  have hl : HasDerivAt (fun t : ℝ => (s : ℂ) * t + y * I) (s : ℂ) x := by
    have := ((hasDerivAt_id (x : ℂ)).const_mul (s : ℂ)).add_const ((y : ℂ) * I)
    simpa using this.comp_ofReal
  exact h.comp x hl

/-- The critical slope through the channel: `X'(y) = -2 Im A'(iy)`. -/
theorem thetaLoopSlope_eq (y : ℝ) : thetaLoopSlope y = -2 * (deriv thetaLoopA (y * I)).im := by
  have hl : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I y := by
    have := (hasDerivAt_id (y : ℂ)).mul_const I
    simpa using this.comp_ofReal
  have hA := (differentiable_thetaLoopA (y * I)).hasDerivAt.comp y hl
  have hX : HasDerivAt (fun t : ℝ => Xi (2 * t)) (2 * (deriv thetaLoopA (y * I) * I).re) y := by
    refine ((hasDerivAt_re_comp hA).const_mul 2).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    show Xi (2 * t) = 2 * (thetaLoopA (t * I)).re
    rw [re_thetaLoopA_I_mul]; ring
  rw [thetaLoopSlope, hX.deriv]
  simp

/-- **(12).** At a critical zero `Ξ(2y₀) = 0`: `∂_x g(0, y₀) = -2 v(y₀) X'(y₀)`. -/
theorem hasDerivAt_thetaLoopEnergy {y₀ : ℝ} (hy₀ : Xi (2 * y₀) = 0) :
    HasDerivAt (fun x => thetaLoopEnergy x y₀)
      (-2 * thetaLoopCharge y₀ * thetaLoopSlope y₀) 0 := by
  have h1 := hasDerivAt_complexNormSq_comp (hasDerivAt_thetaLoopA_shift y₀ 1 0)
  have h2 := hasDerivAt_complexNormSq_comp (hasDerivAt_thetaLoopA_shift y₀ (-1) 0)
  have hu : (thetaLoopA (y₀ * I)).re = 0 := by rw [re_thetaLoopA_I_mul, hy₀]; ring
  have h := h1.fun_sub h2
  simp only [ofReal_one, one_mul, ofReal_neg, neg_mul, mul_zero, ofReal_zero, zero_add,
    mul_one, mul_neg] at h
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  · rw [thetaLoopSlope_eq, thetaLoopCharge, hu]
    simp only [neg_re, neg_im, zero_mul, zero_add]
    ring
  · simp only [thetaLoopEnergy_eq]

theorem thetaLoopSlope_eq_deriv (y : ℝ) : thetaLoopSlope y = 2 * deriv Xi (2 * y) := by
  have h := (hasDerivAt_Xi_deriv (2 * y)).comp y ((hasDerivAt_id y).const_mul 2)
  rw [thetaLoopSlope]
  have h' : HasDerivAt (fun y : ℝ => Xi (2 * y)) (deriv Xi (2 * y) * 2) y := by
    simpa [Function.comp_def] using h
  rw [h'.deriv]; ring

/-- A negative derivative at a zero forces negativity just to the right. -/
theorem exists_Ioo_neg_of_hasDerivAt_neg {g : ℝ → ℝ} {g' : ℝ} (hg : HasDerivAt g g' 0)
    (hg0 : g 0 = 0) (hneg : g' < 0) : ∃ ε > 0, ∀ x ∈ Ioo 0 ε, g x < 0 := by
  have hs := hasDerivAt_iff_tendsto_slope.mp hg
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), slope g 0 x < 0 :=
    (hs.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))).eventually
      (gt_mem_nhds hneg)
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨ε, hε, fun x hx => ?_⟩
  have h := hsub hx
  simp only [mem_setOf_eq, slope_def_field, hg0, sub_zero] at h
  exact (div_neg_iff.mp h).elim (fun h1 => absurd hx.1 (not_lt.mpr h1.2.le)) (fun h1 => h1.1)

theorem one_lt_norm_thetaLoopK_of_energy_neg {x y : ℝ} (hx : |x| < 1 / 4)
    (hg : thetaLoopEnergy x y < 0) : 1 < ‖thetaLoopK (x + y * I)‖ := by
  have hA := thetaLoopA_ne_zero (lam := x + y * I) (by simpa using hx)
  rw [thetaLoopEnergy, sub_neg] at hg
  rw [thetaLoopK, norm_div, one_lt_div (norm_pos_iff.mpr hA)]
  rw [← Complex.sq_norm, ← Complex.sq_norm] at hg
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hg

theorem norm_thetaLoopK_lt_one_of_energy_pos {x y : ℝ} (hx : |x| < 1 / 4)
    (hg : 0 < thetaLoopEnergy x y) : ‖thetaLoopK (x + y * I)‖ < 1 := by
  have hA := thetaLoopA_ne_zero (lam := x + y * I) (by simpa using hx)
  rw [thetaLoopEnergy, sub_pos] at hg
  rw [thetaLoopK, norm_div, div_lt_one (norm_pos_iff.mpr hA)]
  rw [← Complex.sq_norm, ← Complex.sq_norm] at hg
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hg

/-- **(12), both orientations.** Above every height there are simple critical zeros with
`X' > 0`, where the loop gain exceeds one just right of the axis. -/
theorem exists_loop_gain_gt_one (Y : ℝ) :
    ∃ y₀ > Y, Xi (2 * y₀) = 0 ∧ 0 < thetaLoopSlope y₀ ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, x ∈ Ioo 0 ε → 1 < ‖thetaLoopK (x + y₀ * I)‖ := by
  obtain ⟨γ, hγ, hXi, hd⟩ := exists_simpleCrossing_above 1 (Or.inl rfl) (2 * max Y 0)
  set y₀ := γ / 2
  have hy₀ : max Y 0 < y₀ := by simp only [y₀]; linarith
  have h2 : 2 * y₀ = γ := by simp only [y₀]; ring
  have hslope : 0 < thetaLoopSlope y₀ := by rw [thetaLoopSlope_eq_deriv, h2]; linarith
  have hXi' : Xi (2 * y₀) = 0 := by rw [h2]; exact hXi
  have hv := thetaLoopCharge_pos (lt_of_le_of_lt (le_max_right Y 0) hy₀)
  obtain ⟨ε, hε, hneg⟩ := exists_Ioo_neg_of_hasDerivAt_neg (hasDerivAt_thetaLoopEnergy hXi')
    (thetaLoopEnergy_zero y₀) (by nlinarith)
  refine ⟨y₀, lt_of_le_of_lt (le_max_left Y 0) hy₀, hXi', hslope, min ε (1 / 4),
    lt_min hε (by norm_num), fun x hx => ?_⟩
  have hx4 : |x| < 1 / 4 := by
    rw [abs_of_pos hx.1]; exact lt_of_lt_of_le hx.2 (min_le_right _ _)
  exact one_lt_norm_thetaLoopK_of_energy_neg hx4
    (hneg x ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩)

/-- **(12), both orientations.** Above every height there are simple critical zeros with
`X' < 0`, where the loop gain is below one just right of the axis. -/
theorem exists_loop_gain_lt_one (Y : ℝ) :
    ∃ y₀ > Y, Xi (2 * y₀) = 0 ∧ thetaLoopSlope y₀ < 0 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, x ∈ Ioo 0 ε → ‖thetaLoopK (x + y₀ * I)‖ < 1 := by
  obtain ⟨γ, hγ, hXi, hd⟩ := exists_simpleCrossing_above (-1) (Or.inr rfl) (2 * max Y 0)
  set y₀ := γ / 2
  have hy₀ : max Y 0 < y₀ := by simp only [y₀]; linarith
  have h2 : 2 * y₀ = γ := by simp only [y₀]; ring
  have hslope : thetaLoopSlope y₀ < 0 := by rw [thetaLoopSlope_eq_deriv, h2]; linarith
  have hXi' : Xi (2 * y₀) = 0 := by rw [h2]; exact hXi
  have hv := thetaLoopCharge_pos (lt_of_le_of_lt (le_max_right Y 0) hy₀)
  have hg := hasDerivAt_thetaLoopEnergy hXi'
  obtain ⟨ε, hε, hneg⟩ := exists_Ioo_neg_of_hasDerivAt_neg (g := fun x => -thetaLoopEnergy x y₀)
    hg.neg (by simp [thetaLoopEnergy_zero]) (by nlinarith)
  refine ⟨y₀, lt_of_le_of_lt (le_max_left Y 0) hy₀, hXi', hslope, min ε (1 / 4),
    lt_min hε (by norm_num), fun x hx => ?_⟩
  have hx4 : |x| < 1 / 4 := by
    rw [abs_of_pos hx.1]; exact lt_of_lt_of_le hx.2 (min_le_right _ _)
  have h := hneg x ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  exact norm_thetaLoopK_lt_one_of_energy_pos hx4 (by linarith)

/-! ## The Pick-defect kernel (13), (14) -/

/-- The Pick-defect kernel `P_K(λ, μ) = (1 - K(λ) conj K(μ))/(λ + conj μ)`. -/
def thetaLoopPick (lam mu : ℂ) : ℂ :=
  (1 - thetaLoopK lam * conj (thetaLoopK mu)) / (lam + conj mu)

theorem thetaLoopPick_swap (lam mu : ℂ) : thetaLoopPick mu lam = conj (thetaLoopPick lam mu) := by
  rw [thetaLoopPick, thetaLoopPick, map_div₀, map_sub, map_mul, map_add, map_one,
    Complex.conj_conj, Complex.conj_conj]
  ring_nf

/-- At a critical zero the loop closes: `K(iy) = -1`. -/
theorem thetaLoopK_I_mul_of_Xi_eq_zero {y : ℝ} (hy : Xi (2 * y) = 0) :
    thetaLoopK (y * I) = -1 := by
  have hA := thetaLoopA_ne_zero (lam := (y : ℂ) * I) (by simp)
  have h := XiC_two_I_mul_eq_thetaLoop ((y : ℂ) * I)
  rw [show 2 * I * ((y : ℂ) * I) = -((2 * y : ℝ) : ℂ) by
    push_cast; linear_combination (2 * (y : ℂ)) * I_sq, XiC_even, XiC_ofReal, hy,
    ofReal_zero] at h
  rw [thetaLoopK, show thetaLoopB (y * I) = -thetaLoopA (y * I) by linear_combination -h,
    neg_div, div_self hA]

/-- **(14), off-diagonal boundary values.** `P_K(iy_j, iy_k) = 0` for distinct critical zeros. -/
theorem thetaLoopPick_boundary_eq_zero {y₁ y₂ : ℝ} (h₁ : Xi (2 * y₁) = 0)
    (h₂ : Xi (2 * y₂) = 0) : thetaLoopPick (y₁ * I) (y₂ * I) = 0 := by
  rw [thetaLoopPick, thetaLoopK_I_mul_of_Xi_eq_zero h₁, thetaLoopK_I_mul_of_Xi_eq_zero h₂]
  simp

/-- The diagonal boundary value `d(y) = -X'(y)/v(y)`. -/
def thetaLoopBoundaryValue (y : ℝ) : ℝ := -thetaLoopSlope y / thetaLoopCharge y

theorem continuous_thetaLoopA_line (y : ℝ) : Continuous fun x : ℝ => thetaLoopA (x + y * I) :=
  differentiable_thetaLoopA.continuous.comp (by fun_prop)

theorem one_sub_sq_norm_thetaLoopK {lam : ℂ} (hlam : |lam.re| < 1 / 4) :
    1 - ‖thetaLoopK lam‖ ^ 2 =
      (Complex.normSq (thetaLoopA lam) - Complex.normSq (thetaLoopB lam)) /
        Complex.normSq (thetaLoopA lam) := by
  have hA := thetaLoopA_ne_zero hlam
  have hn : Complex.normSq (thetaLoopA lam) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  rw [thetaLoopK, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm]
  field_simp

/-- **(14).** The one-sided diagonal limit
`lim_{x↓0} (1 - |K(x + iy)|²)/(2x) = -X'(y)/v(y)` at a positive critical zero. -/
theorem tendsto_thetaLoopPick_diag {y : ℝ} (hy0 : 0 < y) (hy : Xi (2 * y) = 0) :
    Tendsto (fun x : ℝ => thetaLoopPick (x + y * I) (x + y * I)) (𝓝[>] 0)
      (𝓝 (thetaLoopBoundaryValue y : ℂ)) := by
  have hv := thetaLoopCharge_pos hy0
  have hg := hasDerivAt_thetaLoopEnergy hy
  have hslope := hasDerivAt_iff_tendsto_slope.mp hg
  have hs : Tendsto (fun x : ℝ => thetaLoopEnergy x y / x) (𝓝[>] 0)
      (𝓝 (-2 * thetaLoopCharge y * thetaLoopSlope y)) := by
    refine (hslope.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)).congr fun x => ?_
    rw [slope_def_field, thetaLoopEnergy_zero, sub_zero, sub_zero]
  have hA0 : Complex.normSq (thetaLoopA (y * I)) = thetaLoopCharge y ^ 2 := by
    rw [Complex.normSq_apply, thetaLoopCharge, re_thetaLoopA_I_mul, hy]; ring
  have hAc : Tendsto (fun x : ℝ => Complex.normSq (thetaLoopA (x + y * I))) (𝓝[>] 0)
      (𝓝 (thetaLoopCharge y ^ 2)) := by
    rw [← hA0]
    have := ((Complex.continuous_normSq.comp (continuous_thetaLoopA_line y)).tendsto 0)
    simpa [Function.comp_def] using this.mono_left nhdsWithin_le_nhds
  have hlim := (hs.div hAc (by positivity)).div_const 2
  have hval : -2 * thetaLoopCharge y * thetaLoopSlope y / thetaLoopCharge y ^ 2 / 2 =
      thetaLoopBoundaryValue y := by
    rw [thetaLoopBoundaryValue]; field_simp
  rw [hval] at hlim
  refine (continuous_ofReal.tendsto _).comp hlim |>.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with x hx
  have hx4 : |((x : ℂ) + y * I).re| < 1 / 4 := by
    rw [show ((x : ℂ) + y * I).re = x by simp, abs_of_pos hx.1]; exact hx.2
  simp only [Function.comp_def]
  rw [thetaLoopPick]
  have hK : thetaLoopK (x + y * I) * conj (thetaLoopK (x + y * I)) =
      ((‖thetaLoopK (x + y * I)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hden : (x : ℂ) + y * I + conj ((x : ℂ) + y * I) = ((2 * x : ℝ) : ℂ) := by
    apply Complex.ext <;> simp; ring
  rw [hK, hden, show (1 : ℂ) - ((‖thetaLoopK (x + y * I)‖ ^ 2 : ℝ) : ℂ) =
    ((1 - ‖thetaLoopK (x + y * I)‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
    one_sub_sq_norm_thetaLoopK hx4, ← ofReal_div]
  congr 1
  simp only [Pi.div_apply, thetaLoopEnergy]
  have hA := thetaLoopA_ne_zero hx4
  have hn : Complex.normSq (thetaLoopA (x + y * I)) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  have hx0 : x ≠ 0 := hx.1.ne'
  field_simp

theorem differentiable_thetaLoopB : Differentiable ℂ thetaLoopB := by
  unfold thetaLoopB
  exact ((differentiable_const _).sub differentiable_id).mul
    (differentiable_thetaRenewalDenominator.comp differentiable_id.neg)

theorem continuousAt_thetaLoopK_line {y : ℝ} :
    ContinuousAt (fun x : ℝ => thetaLoopK (x + y * I)) 0 := by
  have hA := thetaLoopA_ne_zero (lam := ((0 : ℝ) : ℂ) + y * I) (by simp)
  exact ((differentiable_thetaLoopB.continuous.comp (by fun_prop : Continuous
    fun x : ℝ => (x : ℂ) + y * I)).continuousAt).div
    ((continuous_thetaLoopA_line y).continuousAt) hA

/-- Off the diagonal the kernel tends to its vanishing boundary value. -/
theorem tendsto_thetaLoopPick_offDiag {y₁ y₂ : ℝ} (h₁ : Xi (2 * y₁) = 0) (h₂ : Xi (2 * y₂) = 0)
    (hne : y₁ ≠ y₂) :
    Tendsto (fun x : ℝ => thetaLoopPick (x + y₁ * I) (x + y₂ * I)) (𝓝 0) (𝓝 0) := by
  have hden : ((0 : ℝ) : ℂ) + y₁ * I + conj (((0 : ℝ) : ℂ) + y₂ * I) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hne (by linarith)
  have hc : ContinuousAt (fun x : ℝ => thetaLoopPick (x + y₁ * I) (x + y₂ * I)) 0 := by
    unfold thetaLoopPick
    exact ((continuousAt_const.sub (continuousAt_thetaLoopK_line.mul
      (continuous_conj.continuousAt.comp continuousAt_thetaLoopK_line))).div
      ((by fun_prop : Continuous fun x : ℝ =>
        (x : ℂ) + y₁ * I + conj ((x : ℂ) + y₂ * I)).continuousAt) hden)
  have h := hc.tendsto
  have hv : thetaLoopPick (((0 : ℝ) : ℂ) + y₁ * I) (((0 : ℝ) : ℂ) + y₂ * I) = 0 := by
    simpa using thetaLoopPick_boundary_eq_zero h₁ h₂
  rwa [hv] at h

/-- Critical zeros with a prescribed boundary sign are unbounded. -/
theorem infinite_zeros_boundaryValue_sign {s : ℝ} (hs : s = 1 ∨ s = -1) :
    {y : ℝ | 0 < y ∧ Xi (2 * y) = 0 ∧ 0 < s * thetaLoopBoundaryValue y}.Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨Y, hY⟩ => ?_
  obtain ⟨γ, hγ, hXi, hd⟩ := exists_simpleCrossing_above (-s)
    (by rcases hs with h | h <;> simp [h]) (2 * max Y 0)
  have hy0 : 0 < γ / 2 := by linarith [le_max_right Y 0]
  have hmem : γ / 2 ∈ {y : ℝ | 0 < y ∧ Xi (2 * y) = 0 ∧ 0 < s * thetaLoopBoundaryValue y} := by
    refine ⟨hy0, by rwa [show 2 * (γ / 2) = γ by ring], ?_⟩
    have hv := thetaLoopCharge_pos hy0
    rw [thetaLoopBoundaryValue, thetaLoopSlope_eq_deriv, show 2 * (γ / 2) = γ by ring]
    rw [mul_div_assoc', lt_div_iff₀ hv]
    nlinarith
  have := hY hmem
  linarith [le_max_left Y 0]

/-- **(13), infinite index.** For each sign `s = ±1` and every `n`, there are `n` points in the
right collar `0 < Re λ < a` whose Pick Gram matrix `s P_K(λ_i, λ_j)` is positive definite.  Hence
`P_K` has infinite positive and infinite negative index. -/
theorem exists_posDef_thetaLoopPick {s : ℝ} (hs : s = 1 ∨ s = -1) (n : ℕ) :
    ∃ pts : Fin n → ℂ, (∀ i, 0 < (pts i).re ∧ (pts i).re < 1 / 4) ∧
      ((s : ℂ) • Matrix.of fun i j => thetaLoopPick (pts i) (pts j)).PosDef := by
  set Z := {y : ℝ | 0 < y ∧ Xi (2 * y) = 0 ∧ 0 < s * thetaLoopBoundaryValue y}
  have hZ := infinite_zeros_boundaryValue_sign hs
  set f : Fin n → Z := fun i => hZ.natEmbedding _ i
  have hf : Function.Injective f := fun i j h => Fin.ext ((hZ.natEmbedding _).injective h)
  set y : Fin n → ℝ := fun i => (f i : ℝ)
  have hyZ : ∀ i, y i ∈ Z := fun i => (f i).2
  have hyinj : Function.Injective y := fun i j h => hf (Subtype.ext h)
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, 2 * δ ≤ s * thetaLoopBoundaryValue (y i) := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; exact ⟨1, one_pos, fun i => i.elim0⟩
    · haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
      obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ
        (fun i => s * thetaLoopBoundaryValue (y i)) Finset.univ_nonempty
      exact ⟨s * thetaLoopBoundaryValue (y i₀) / 2, by linarith [(hyZ i₀).2.2],
        fun i => by linarith [hi₀ i (Finset.mem_univ i)]⟩
  have hsn : ‖(s : ℂ)‖ = 1 := by rcases hs with h | h <;> simp [h]
  have hdiag : ∀ i, ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      δ ≤ ((s : ℂ) * thetaLoopPick ((x : ℂ) + y i * I) ((x : ℂ) + y i * I)).re := by
    intro i
    have h := (tendsto_thetaLoopPick_diag (hyZ i).1 (hyZ i).2.1).const_mul (s : ℂ)
    have hre := (Complex.continuous_re.tendsto _).comp h
    simp only [Function.comp_def] at hre
    refine hre.eventually (Ici_mem_nhds ?_)
    simp only [← ofReal_mul, ofReal_re]
    linarith [hδle i]
  have hoff : ∀ i j, i ≠ j → ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      ‖(s : ℂ) * thetaLoopPick ((x : ℂ) + y i * I) ((x : ℂ) + y j * I)‖ ≤ δ / (2 * n) := by
    intro i j hij
    have h := ((tendsto_thetaLoopPick_offDiag (hyZ i).2.1 (hyZ j).2.1
      (fun h => hij (hyinj h))).const_mul (s : ℂ)).norm
    rw [mul_zero, norm_zero] at h
    have hn : (0 : ℝ) < n := by
      have := Fin.pos i; exact_mod_cast this
    exact (h.mono_left nhdsWithin_le_nhds).eventually (Iic_mem_nhds (by positivity))
  have hall : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < 1 / 4 ∧ (∀ i, δ ≤
      ((s : ℂ) * thetaLoopPick ((x : ℂ) + y i * I) ((x : ℂ) + y i * I)).re) ∧
      ∀ i j, i ≠ j →
        ‖(s : ℂ) * thetaLoopPick ((x : ℂ) + y i * I) ((x : ℂ) + y j * I)‖ ≤ δ / (2 * n) := by
    refine (eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))).and
      ((Filter.eventually_all.mpr hdiag).and ?_)
    refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · filter_upwards [hoff i j hij] with x hx _ using hx
  obtain ⟨x, ⟨hx4, hxd, hxo⟩, hx0⟩ := (hall.and self_mem_nhdsWithin).exists
  refine ⟨fun i => (x : ℂ) + y i * I, fun i => by simp; exact ⟨hx0, by linarith⟩, ?_⟩
  refine GaloisForLFunctions.HTGeometry.posDef_of_diag_ge_of_offDiag_le ?_ hδ
    (fun i => by simpa using hxd i) (fun i j hij => by simpa using hxo i j hij)
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    star_mul', Complex.star_def, Complex.conj_ofReal]
  rw [← thetaLoopPick_swap]

end

end RHTower
