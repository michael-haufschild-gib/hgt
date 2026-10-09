import GaloisForLFunctions.RHTower.DeckPointPairSelbergTransform
import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainVolume

/-!
# The Selberg transform of a nonnegative profile on the real axis

Let `φ` be continuous, nonnegative, supported in `[0, R]` and not identically zero, and let
`h(s) = ∫_ℍ φ(u(i, w)) (Im w)^s dμ(w)` be its Selberg transform.

* **Symmetry** (`selbergTransform_one_sub`): `h(1 − s) = h(s)`. Both `(Im w)^s` and `(Im w)^{1−s}`
  are eigenfunctions of the Laplacian with eigenvalue `s(1 − s)`, so Selberg's theorem at the centre
  `i` gives `h(1 − s) = (Im i)^{1−s} h(s) = h(s)`.
* **Realness and positivity** (`selbergTransform_ofReal`, `selbergRealTransform_pos`): for real `σ`,
  `h(σ) = ∫ φ(u) y^σ dμ` is real and positive.
* **Cosh form and monotonicity** (`selbergRealTransform_eq_cosh`, `strictMonoOn_selbergRealTransform`): averaging the
  symmetry, `h(σ) = ∫ φ(u) √y cosh((σ − ½) log y) dμ`, which is strictly increasing on `[½, ∞)`
  because `φ(u(i, ·))` is positive at points with `y ≠ 1`.
* **Critical-line domination** (`norm_selbergTransform_half_add_le`):
  `|h(½ + ir)| ≤ h(½)` for real `r`, since `|y^{½+ir}| = y^{½}`.
* **Mass** (`selbergTransform_one_eq_mass`): `h(1) = h(0) = ∫ φ(u(i, w)) dμ(w)`, so
  `h(σ) > ∫ φ(u(i, w)) dμ` for every `σ > 1` (`integral_pairKernel_lt_selbergRealTransform`).
-/

open UpperHalfPlane MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry HyperbolicPointPairCentre HyperbolicRotationMean
  HyperbolicPowerEigen

noncomputable section

variable {φ : ℝ → ℝ} {R : ℝ}

/-- The real Selberg transform `σ ↦ ∫_ℍ φ(u(i, w)) (Im w)^σ dμ(w)`. -/
def selbergRealTransform (φ : ℝ → ℝ) (σ : ℝ) : ℝ := ∫ w, φ (pairU UpperHalfPlane.I w) * w.im ^ σ

theorem continuous_im_rpow (σ : ℝ) : Continuous fun w : ℍ => w.im ^ σ :=
  UpperHalfPlane.continuous_im.rpow_const fun w => Or.inl w.im_pos.ne'

theorem continuous_log_im : Continuous fun w : ℍ => Real.log w.im :=
  UpperHalfPlane.continuous_im.log fun w => w.im_pos.ne'

theorem integrable_pairKernel_I_mul (hφc : Continuous φ) (hφR : KernelSupport φ R) {G : ℍ → ℝ}
    (hG : Continuous G) : Integrable fun w => φ (pairU UpperHalfPlane.I w) * G w := by
  simpa [smul_eq_mul] using integrable_pairKernel_smul' hφc hφR hG UpperHalfPlane.I

theorem hasCompactSupport_pairKernel_mul (hφR : KernelSupport φ R) (G : ℍ → ℝ) :
    HasCompactSupport fun w => φ (pairU UpperHalfPlane.I w) * G w :=
  HasCompactSupport.intro (isCompact_closedBall UpperHalfPlane.I (1 + 2 * R)) fun w hw => by
    have : R < pairU UpperHalfPlane.I w := by
      by_contra h
      exact hw (Metric.mem_closedBall.2 (by rw [dist_comm]; exact dist_le_of_pairU_le (not_lt.1 h)))
    rw [hφR _ this, zero_mul]

/-- **Symmetry of the Selberg transform**: `h(1 − s) = h(s)`. -/
theorem selbergTransform_one_sub (hφc : Continuous φ) (hφR : KernelSupport φ R) (s : ℂ) :
    selbergTransform φ (1 - s) = selbergTransform φ s := by
  have h := integral_pairKernel_mul_eigen hφc hφR (powerEigen_smooth (1 - s)) (s := s)
    (fun z => by rw [powerEigen_laplacian]; ring) UpperHalfPlane.I
  rw [powerEigen_I, one_mul] at h
  exact h

theorem powerEigen_ofReal (σ : ℝ) (w : ℍ) : powerEigen (σ : ℂ) w = ((w.im ^ σ : ℝ) : ℂ) := by
  rw [powerEigen, Complex.ofReal_cpow w.im_pos.le]

/-- **Realness**: at real `σ` the Selberg transform is the real integral `∫ φ(u) y^σ dμ`. -/
theorem selbergTransform_ofReal (σ : ℝ) : selbergTransform φ σ = (selbergRealTransform φ σ : ℂ) := by
  rw [selbergTransform, selbergRealTransform, ← integral_complex_ofReal]
  congr 1
  funext w
  rw [powerEigen_ofReal]
  push_cast
  ring

theorem selbergRealTransform_one_sub (hφc : Continuous φ) (hφR : KernelSupport φ R) (σ : ℝ) :
    selbergRealTransform φ (1 - σ) = selbergRealTransform φ σ := by
  have h := selbergTransform_one_sub hφc hφR (σ : ℂ)
  rw [show (1 : ℂ) - σ = ((1 - σ : ℝ) : ℂ) by push_cast; ring, selbergTransform_ofReal,
    selbergTransform_ofReal] at h
  exact_mod_cast h

theorem rpow_add_rpow_one_sub {y : ℝ} (hy : 0 < y) (σ : ℝ) :
    y ^ σ + y ^ (1 - σ) = 2 * (Real.sqrt y * Real.cosh ((σ - 1 / 2) * Real.log y)) := by
  rw [Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hy, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy,
    Real.cosh_eq]
  have e1 : Real.log y * σ = Real.log y * (1 / 2) + (σ - 1 / 2) * Real.log y := by ring
  have e2 : Real.log y * (1 - σ) = Real.log y * (1 / 2) + -((σ - 1 / 2) * Real.log y) := by ring
  rw [e1, e2, Real.exp_add, Real.exp_add]
  ring

/-- **Cosh form**: `h(σ) = ∫ φ(u(i, w)) √y cosh((σ − ½) log y) dμ(w)`. -/
theorem selbergRealTransform_eq_cosh (hφc : Continuous φ) (hφR : KernelSupport φ R) (σ : ℝ) :
    selbergRealTransform φ σ = ∫ w, φ (pairU UpperHalfPlane.I w) *
      (Real.sqrt w.im * Real.cosh ((σ - 1 / 2) * Real.log w.im)) := by
  have h2 : 2 * selbergRealTransform φ σ = selbergRealTransform φ σ + selbergRealTransform φ (1 - σ) := by
    rw [selbergRealTransform_one_sub hφc hφR]; ring
  have hsum : selbergRealTransform φ σ + selbergRealTransform φ (1 - σ) = ∫ w, 2 * (φ (pairU UpperHalfPlane.I w) *
      (Real.sqrt w.im * Real.cosh ((σ - 1 / 2) * Real.log w.im))) := by
    rw [selbergRealTransform, selbergRealTransform, ← integral_add (integrable_pairKernel_I_mul hφc hφR
      (continuous_im_rpow σ)) (integrable_pairKernel_I_mul hφc hφR (continuous_im_rpow (1 - σ)))]
    congr 1
    funext w
    rw [← mul_add, rpow_add_rpow_one_sub w.im_pos]
    ring
  rw [hsum, integral_const_mul] at h2
  linarith

/-- A nonnegative continuous profile that is somewhere nonzero on `[0, ∞)` is positive at some
`u > 0`. -/
theorem exists_pos_of_ne_zero (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hne : ∃ u₀, 0 ≤ u₀ ∧ φ u₀ ≠ 0) : ∃ u₁, 0 < u₁ ∧ 0 < φ u₁ := by
  obtain ⟨u₀, hu₀, hφu₀⟩ := hne
  have hpos : 0 < φ u₀ := lt_of_le_of_ne (hφ0 _) (Ne.symm hφu₀)
  rcases hu₀.lt_or_eq with h | h
  · exact ⟨u₀, h, hpos⟩
  · have hev : ∀ᶠ u in 𝓝 u₀, 0 < φ u := hφc.continuousAt.eventually (lt_mem_nhds hpos)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨u₀ + ε / 2, by rw [← h]; linarith, hball ?_⟩
    rw [Real.dist_eq, show u₀ + ε / 2 - u₀ = ε / 2 by ring, abs_of_pos (by linarith)]
    linarith

/-- Every `u > 0` is the point-pair invariant `u(i, w)` of a point `w = iy` with `y > 1`. -/
theorem exists_pairU_eq_of_pos {u : ℝ} (hu : 0 < u) :
    ∃ w : ℍ, pairU UpperHalfPlane.I w = u ∧ 1 < w.im := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 + 2 * u + 2 * Real.sqrt (u * (u + 1)) := ⟨_, rfl⟩
  have hs := Real.sqrt_nonneg (u * (u + 1))
  have hss : Real.sqrt (u * (u + 1)) ^ 2 = u * (u + 1) := Real.sq_sqrt (by positivity)
  have hy1 : 1 < y := by rw [hy]; linarith
  have hyim : 0 < (Complex.I * (y : ℂ)).im := by simp; linarith
  refine ⟨⟨Complex.I * y, hyim⟩, ?_, by simpa using hy1⟩
  have hd : dist Complex.I (Complex.I * (y : ℂ)) = y - 1 := by
    rw [Complex.dist_eq, show Complex.I - Complex.I * y = Complex.I * ((1 - y : ℝ) : ℂ) by
      push_cast; ring, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith), neg_sub]
  have him : (⟨Complex.I * y, hyim⟩ : ℍ).im = y := by
    show (Complex.I * (y : ℂ)).im = y
    simp
  rw [pairU, him, UpperHalfPlane.I_im, UpperHalfPlane.coe_I]
  show dist Complex.I (Complex.I * (y : ℂ)) ^ 2 / (4 * 1 * y) = u
  rw [hd, div_eq_iff (by positivity)]
  rw [hy]
  nlinarith

/-- **Positivity**: `h(σ) > 0` for every real `σ`. -/
theorem selbergRealTransform_pos (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u) (hφR : KernelSupport φ R)
    (hne : ∃ u₀, 0 ≤ u₀ ∧ φ u₀ ≠ 0) (σ : ℝ) : 0 < selbergRealTransform φ σ := by
  obtain ⟨u₁, hu₁, hφu₁⟩ := exists_pos_of_ne_zero hφc hφ0 hne
  obtain ⟨w₁, hw₁, -⟩ := exists_pairU_eq_of_pos hu₁
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := w₁)
    ((hφc.comp (continuous_pairU_right _)).mul (continuous_im_rpow σ))
    (hasCompactSupport_pairKernel_mul hφR _)
    (fun w => mul_nonneg (hφ0 _) (Real.rpow_nonneg w.im_pos.le _)) ?_
  show φ (pairU UpperHalfPlane.I w₁) * w₁.im ^ σ ≠ 0
  rw [hw₁]
  exact mul_ne_zero hφu₁.ne' (Real.rpow_pos_of_pos w₁.im_pos _).ne'

/-- **Realness and positivity** of `h` on the real axis. -/
theorem selbergTransform_ofReal_re_pos (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hφR : KernelSupport φ R) (hne : ∃ u₀, 0 ≤ u₀ ∧ φ u₀ ≠ 0) (σ : ℝ) :
    (selbergTransform φ σ).im = 0 ∧ 0 < (selbergTransform φ σ).re := by
  rw [selbergTransform_ofReal, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, selbergRealTransform_pos hφc hφ0 hφR hne σ⟩

/-- **Strict monotonicity**: `h(σ₁) < h(σ₂)` for `½ ≤ σ₁ < σ₂`. -/
theorem selbergRealTransform_lt (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u) (hφR : KernelSupport φ R)
    (hne : ∃ u₀, 0 ≤ u₀ ∧ φ u₀ ≠ 0) {σ₁ σ₂ : ℝ} (h1 : 1 / 2 ≤ σ₁) (h12 : σ₁ < σ₂) :
    selbergRealTransform φ σ₁ < selbergRealTransform φ σ₂ := by
  have hG : Continuous fun w : ℍ => Real.sqrt w.im *
      (Real.cosh ((σ₂ - 1 / 2) * Real.log w.im) - Real.cosh ((σ₁ - 1 / 2) * Real.log w.im)) :=
    UpperHalfPlane.continuous_im.sqrt.mul
      ((Real.continuous_cosh.comp (continuous_const.mul continuous_log_im)).sub
        (Real.continuous_cosh.comp (continuous_const.mul continuous_log_im)))
  have hc : ∀ σ : ℝ, Continuous fun w : ℍ =>
      Real.sqrt w.im * Real.cosh ((σ - 1 / 2) * Real.log w.im) := fun σ =>
    UpperHalfPlane.continuous_im.sqrt.mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_log_im))
  have key : selbergRealTransform φ σ₂ - selbergRealTransform φ σ₁ = ∫ w, φ (pairU UpperHalfPlane.I w) *
      (Real.sqrt w.im * (Real.cosh ((σ₂ - 1 / 2) * Real.log w.im) -
        Real.cosh ((σ₁ - 1 / 2) * Real.log w.im))) := by
    rw [selbergRealTransform_eq_cosh hφc hφR, selbergRealTransform_eq_cosh hφc hφR,
      ← integral_sub (integrable_pairKernel_I_mul hφc hφR (hc σ₂))
        (integrable_pairKernel_I_mul hφc hφR (hc σ₁))]
    congr 1
    funext w
    ring
  have hcosh : ∀ L : ℝ, Real.cosh ((σ₁ - 1 / 2) * L) ≤ Real.cosh ((σ₂ - 1 / 2) * L) := fun L =>
    Real.cosh_le_cosh.2 (by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ₁ - 1 / 2),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ₂ - 1 / 2)]
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))
  rw [← sub_pos, key]
  obtain ⟨u₁, hu₁, hφu₁⟩ := exists_pos_of_ne_zero hφc hφ0 hne
  obtain ⟨w₁, hw₁, hy₁⟩ := exists_pairU_eq_of_pos hu₁
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := w₁)
    ((hφc.comp (continuous_pairU_right _)).mul hG) (hasCompactSupport_pairKernel_mul hφR _)
    (fun w => mul_nonneg (hφ0 _) (mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.2 (hcosh _)))) ?_
  show φ (pairU UpperHalfPlane.I w₁) * (Real.sqrt w₁.im * (Real.cosh ((σ₂ - 1 / 2) *
    Real.log w₁.im) - Real.cosh ((σ₁ - 1 / 2) * Real.log w₁.im))) ≠ 0
  rw [hw₁]
  have hL : 0 < Real.log w₁.im := Real.log_pos hy₁
  have hstrict : Real.cosh ((σ₁ - 1 / 2) * Real.log w₁.im) <
      Real.cosh ((σ₂ - 1 / 2) * Real.log w₁.im) :=
    Real.cosh_lt_cosh.2 (by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ₁ - 1 / 2),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ₂ - 1 / 2), abs_of_pos hL]
      exact mul_lt_mul_of_pos_right (by linarith) hL)
  exact mul_ne_zero hφu₁.ne' (mul_ne_zero (Real.sqrt_pos.2 w₁.im_pos).ne'
    (sub_pos.2 hstrict).ne')

/-- **`σ ↦ Re h(σ)` is strictly increasing on `[½, ∞)`.** -/
theorem strictMonoOn_selbergRealTransform (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hφR : KernelSupport φ R) (hne : ∃ u₀, 0 ≤ u₀ ∧ φ u₀ ≠ 0) :
    StrictMonoOn (fun σ : ℝ => (selbergTransform φ σ).re) (Ici (1 / 2)) := by
  intro σ₁ h1 σ₂ _ h12
  simp only [selbergTransform_ofReal, Complex.ofReal_re]
  exact selbergRealTransform_lt hφc hφ0 hφR hne h1 h12

/-- **Critical-line domination**: `|h(½ + ir)| ≤ h(½)` for real `r`. -/
theorem norm_selbergTransform_half_add_le (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hφR : KernelSupport φ R) (r : ℝ) :
    ‖selbergTransform φ (1 / 2 + r * Complex.I)‖ ≤ (selbergTransform φ (1 / 2)).re := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, selbergTransform_ofReal (1 / 2),
    Complex.ofReal_re, selbergRealTransform]
  refine norm_integral_le_of_norm_le (integrable_pairKernel_I_mul hφc hφR (continuous_im_rpow _))
    (Eventually.of_forall fun w => le_of_eq ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hφ0 _), powerEigen,
    Complex.norm_cpow_eq_rpow_re_of_pos w.im_pos]
  simp

/-- **The value at `s = 1` is the kernel mass**: `h(1) = ∫ φ(u(i, w)) dμ(w)`. -/
theorem selbergTransform_one_eq_mass (hφc : Continuous φ) (hφR : KernelSupport φ R) :
    selbergTransform φ 1 = ((∫ w, φ (pairU UpperHalfPlane.I w) : ℝ) : ℂ) := by
  have h := selbergTransform_one_sub hφc hφR 0
  rw [sub_zero] at h
  rw [h, selbergTransform, ← integral_complex_ofReal]
  congr 1
  funext w
  rw [powerEigen, Complex.cpow_zero, mul_one]

theorem selbergRealTransform_one_eq_mass (hφc : Continuous φ) (hφR : KernelSupport φ R) :
    selbergRealTransform φ 1 = ∫ w, φ (pairU UpperHalfPlane.I w) := by
  have h := selbergTransform_one_eq_mass hφc hφR
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num, selbergTransform_ofReal] at h
  exact_mod_cast h

/-- **Above `s = 1` the transform exceeds the kernel mass.** -/
theorem integral_pairKernel_lt_selbergRealTransform (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hφR : KernelSupport φ R) (hne : ∃ u₀, 0 ≤ u₀ ∧ φ u₀ ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    ∫ w, φ (pairU UpperHalfPlane.I w) < selbergRealTransform φ σ := by
  rw [← selbergRealTransform_one_eq_mass hφc hφR]
  exact selbergRealTransform_lt hφc hφ0 hφR hne (by norm_num) hσ

end

end GaloisForLFunctions.RHTower.DeckPointPair
