import GaloisForLFunctions.RHTower.RepPointPairEigen

/-!
# The cusp part of a point-pair operator is bounded by `h_φ(½)`

Let `ψ_Y` be the cusp cutoff (`0` below height `Y`, `1` above `2Y`).  High in the cusp only the
parabolic translates `±Tⁿ` bring points of the modular cell within a fixed hyperbolic distance of
each other (`c_eq_zero_of_pairU_le_high`), and these translates preserve the height.  The weight
`y^{1/2}` is the eigenfunction of every point-pair operator with Selberg transform
`h_φ(½) = ∫_ℍ φ(u(i, w)) (Im w)^{1/2} dμ(w)` (`integral_kernel_sqrt`), so the weighted Schur test
with weight `y^{1/2}` bounds the cusp operator `B_Y = ψ_Y L_φ ψ_Y` by `h_{|φ|}(½)`
(`norm_cuspOp_le`).  The test is run through the arithmetic–geometric inequality
`2fg ≤ r f² + g²/r` with the ratio `r = (Im z / Im z')^{1/2}` of the weights, which bounds the
sesquilinear form `⟪B_Y F, G⟫` by `h_{|φ|}(½)(‖F‖² + ‖G‖²)/2`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology
open scoped MatrixGroups ENNReal InnerProductSpace

namespace GaloisForLFunctions.RHTower.RepPointPair

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.HyperbolicPowerEigen
open GaloisForLFunctions.RHTower.DeckPointPair (selbergTransform integral_pairKernel_mul_eigen)

noncomputable section

variable {ι : Type} [Fintype ι] {ρ : SL(2, ℤ) →* (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)}

/-! ## The cusp cutoff -/

/-- The cusp cutoff `ψ_Y`: `0` below height `Y`, `1` above `2Y`, linear in between. -/
def cuspCutoff (Y : ℝ) (z : ℍ) : ℝ := min 1 (max 0 ((z.im - Y) / Y))

theorem cuspCutoff_nonneg (Y : ℝ) (z : ℍ) : 0 ≤ cuspCutoff Y z :=
  le_min zero_le_one (le_max_left _ _)

theorem cuspCutoff_le_one (Y : ℝ) (z : ℍ) : cuspCutoff Y z ≤ 1 := min_le_left _ _

theorem continuous_cuspCutoff (Y : ℝ) : Continuous (cuspCutoff Y) := by
  unfold cuspCutoff
  fun_prop

theorem lt_im_of_cuspCutoff_pos {Y : ℝ} (hY : 0 < Y) {z : ℍ} (h : 0 < cuspCutoff Y z) :
    Y < z.im := by
  by_contra hle
  push Not at hle
  have : (z.im - Y) / Y ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hY.le
  have h1 : max 0 ((z.im - Y) / Y) = 0 := max_eq_left this
  rw [cuspCutoff, h1, min_eq_right zero_le_one] at h
  exact lt_irrefl 0 h

theorem cuspCutoff_eq_one {Y : ℝ} (hY : 0 < Y) {z : ℍ} (h : 2 * Y ≤ z.im) : cuspCutoff Y z = 1 := by
  have : 1 ≤ (z.im - Y) / Y := by rw [le_div_iff₀ hY]; linarith
  rw [cuspCutoff, max_eq_right (by linarith), min_eq_left this]

theorem cuspCutoff_eq_zero {Y : ℝ} (hY : 0 < Y) {z : ℍ} (h : z.im ≤ Y) : cuspCutoff Y z = 0 := by
  have : (z.im - Y) / Y ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hY.le
  rw [cuspCutoff, max_eq_left this, min_eq_right zero_le_one]

/-! ## Heights of nearby translates -/

/-- **The modular cell maximises the height in its orbit**: `Im(Bz) ≤ Im z` for `z ∈ 𝒟`.  The
denominator `(cx + d)² + (cy)²` is at least `c² − |cd| + d² ≥ 1`, since `|z| ≥ 1`, `|x| ≤ ½` and
`(c, d) ≠ (0, 0)`. -/
theorem im_smul_le_of_mem_fd {z : ℍ} (hz : z ∈ fd) (B : SL(2, ℤ)) : (B • z).im ≤ z.im := by
  have hdet : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using B.det_coe
  have hne : B 1 0 ≠ 0 ∨ B 1 1 ≠ 0 := by
    by_contra h
    push Not at h
    rw [h.1, h.2] at hdet
    simp at hdet
  have hsq : 0 < B 1 0 ^ 2 + B 1 1 ^ 2 := by
    rcases hne with h | h
    · have : 0 < B 1 0 ^ 2 := by positivity
      nlinarith [sq_nonneg (B 1 1)]
    · have : 0 < B 1 1 ^ 2 := by positivity
      nlinarith [sq_nonneg (B 1 0)]
  have key : 0 < B 1 0 ^ 2 + B 1 1 ^ 2 - |B 1 0 * B 1 1| := by
    nlinarith [abs_mul (B 1 0) (B 1 1), sq_abs (B 1 0), sq_abs (B 1 1),
      sq_nonneg (|B 1 0| - |B 1 1|)]
  have keyR : (1 : ℝ) ≤ (B 1 0 : ℝ) ^ 2 + (B 1 1 : ℝ) ^ 2 - |(B 1 0 : ℝ) * B 1 1| := by
    have := Int.add_one_le_of_lt key
    rw [zero_add] at this
    exact_mod_cast this
  have hz1 : 1 ≤ z.re * z.re + z.im * z.im := by
    have := hz.1
    rwa [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at this
  have hx : |z.re| ≤ 1 / 2 := hz.2
  rw [im_smul_int]
  set c : ℝ := (B 1 0 : ℝ)
  set d : ℝ := (B 1 1 : ℝ)
  have h2x : |2 * c * d * z.re| ≤ |c * d| := by
    rw [show 2 * c * d * z.re = (c * d) * (2 * z.re) by ring, abs_mul]
    have : |2 * z.re| ≤ 1 := by rw [abs_mul, abs_two]; linarith
    exact mul_le_of_le_one_right (abs_nonneg _) this
  have hlow := neg_abs_le (2 * c * d * z.re)
  have hcc : c ^ 2 ≤ c ^ 2 * (z.re * z.re + z.im * z.im) :=
    le_mul_of_one_le_right (sq_nonneg c) hz1
  have hden : 1 ≤ (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by nlinarith
  exact div_le_self z.im_pos.le hden

/-- If `z'` lies in the modular cell and `u(z, Bz') ≤ R`, then `Im z ≤ (4R + 2) Im z'`. -/
theorem im_le_of_pairU_le {z z' : ℍ} (hz' : z' ∈ fd) {R : ℝ} {B : SL(2, ℤ)}
    (h : pairU z (B • z') ≤ R) : z.im ≤ (4 * R + 2) * z'.im := by
  have hR : 0 ≤ R := (pairU_nonneg _ _).trans h
  have h1 := (pairU_le_bounds h).1
  rw [div_le_iff₀ (by linarith)] at h1
  have h2 := im_smul_le_of_mem_fd hz' B
  nlinarith

/-- If `z` lies in the modular cell and `u(z, Bz') ≤ R`, then `Im z' ≤ (4R + 2) Im z`. -/
theorem im_le_of_pairU_le' {z z' : ℍ} (hz : z ∈ fd) {R : ℝ} {B : SL(2, ℤ)}
    (h : pairU z (B • z') ≤ R) : z'.im ≤ (4 * R + 2) * z.im := by
  rw [← pairU_smul_int B⁻¹, inv_smul_smul, pairU_comm] at h
  exact im_le_of_pairU_le hz h

/-- **High in the cusp only `±Tⁿ` bring points close.**  If `Y² > 4R + 2`, `Im z, Im z' > Y` and
`u(z, Bz') ≤ R`, then `B` has lower-left entry `0`. -/
theorem c_eq_zero_of_pairU_le_high {R Y : ℝ} (hY0 : 0 < Y) (hY : 4 * R + 2 < Y ^ 2) {z z' : ℍ}
    (hz : Y < z.im) (hz' : Y < z'.im) {B : SL(2, ℤ)} (h : pairU z (B • z') ≤ R) : B 1 0 = 0 := by
  by_contra hc
  have hlow := (pairU_le_bounds h).1
  have hR : 0 ≤ R := (pairU_nonneg _ _).trans h
  have hc1 : (1 : ℝ) ≤ (B 1 0 : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (B 1 0) ^ 2 := by
      have := sq_pos_of_ne_zero hc
      omega
    exact_mod_cast this
  have hy' := z'.im_pos
  have himB : (B • z').im ≤ 1 / z'.im := by
    rw [im_smul_int]
    have hden : (B 1 0 : ℝ) ^ 2 * z'.im ^ 2 ≤
        ((B 1 0 : ℝ) * z'.re + B 1 1) ^ 2 + ((B 1 0 : ℝ) * z'.im) ^ 2 := by
      nlinarith [sq_nonneg ((B 1 0 : ℝ) * z'.re + B 1 1)]
    rw [div_le_div_iff₀ (by positivity) hy']
    nlinarith [sq_nonneg z'.im]
  have h1 : z.im / (4 * R + 2) < 1 / Y := by
    calc z.im / (4 * R + 2) ≤ (B • z').im := hlow
      _ ≤ 1 / z'.im := himB
      _ < 1 / Y := one_div_lt_one_div_of_lt hY0 hz'
  rw [div_lt_div_iff₀ (by linarith) hY0, one_mul] at h1
  nlinarith

theorem im_smul_of_c_eq_zero (B : SL(2, ℤ)) (hc : B 1 0 = 0) (z : ℍ) : (B • z).im = z.im := by
  rw [im_smul_int, hc]
  have hdet := det_real B
  rw [hc] at hdet
  push_cast at hdet ⊢
  have hd : (B 1 1 : ℝ) ^ 2 = 1 := by
    have h1 : (B 0 0 : ℝ) * B 1 1 = 1 := by linarith
    have h2 : (B 0 0 : ℤ) * B 1 1 = 1 := by exact_mod_cast h1
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h2 with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  simp [hd]

/-! ## The weight `y^{1/2}` -/

/-- The weight `√(Im z)`. -/
def sqrtIm (z : ℍ) : ℝ := Real.sqrt z.im

theorem sqrtIm_pos (z : ℍ) : 0 < sqrtIm z := Real.sqrt_pos.2 z.im_pos

theorem continuous_sqrtIm : Continuous sqrtIm := Real.continuous_sqrt.comp continuous_im

/-- `h_φ(½) = ∫_ℍ φ(u(i, w)) (Im w)^{1/2} dμ(w)`. -/
def halfTransform (φ : ℝ → ℝ) : ℝ := ∫ w : ℍ, φ (pairU UpperHalfPlane.I w) * sqrtIm w

theorem powerEigen_half_eq (w : ℍ) : powerEigen (1 / 2 : ℂ) w = ((sqrtIm w : ℝ) : ℂ) := by
  rw [powerEigen, sqrtIm, Real.sqrt_eq_rpow, Complex.ofReal_cpow w.im_pos.le]
  norm_num

/-- **The weight identity**: `∫_ℍ φ(u(z, w)) (Im w)^{1/2} dμ(w) = h_φ(½) (Im z)^{1/2}`. -/
theorem integral_kernel_sqrt {φ : ℝ → ℝ} {R : ℝ} (hφc : Continuous φ) (hφR : KernelSupport φ R)
    (z : ℍ) : ∫ w : ℍ, φ (pairU z w) * sqrtIm w = halfTransform φ * sqrtIm z := by
  have h := integral_pairKernel_mul_eigen hφc (kernelSupport_deck hφR) (powerEigen_smooth (1 / 2))
    (fun z => powerEigen_laplacian (1 / 2) z) z
  simp only [powerEigen_half_eq] at h
  have h1 : ∫ w, ((φ (pairU z w) : ℝ) : ℂ) * ((sqrtIm w : ℝ) : ℂ) =
      ((∫ w : ℍ, φ (pairU z w) * sqrtIm w : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp only [Complex.ofReal_mul]
  have h2 : selbergTransform φ (1 / 2 : ℂ) = ((halfTransform φ : ℝ) : ℂ) := by
    unfold selbergTransform halfTransform
    rw [← integral_complex_ofReal]
    simp only [powerEigen_half_eq, Complex.ofReal_mul]
  rw [h1, h2, ← Complex.ofReal_mul] at h
  rw [mul_comm (halfTransform φ)]
  exact_mod_cast h

theorem isCompact_pairU_le (z : ℍ) (R : ℝ) : IsCompact {w : ℍ | pairU z w ≤ R} :=
  (isCompact_closedBall z (Real.arcosh (1 + 2 * R))).of_isClosed_subset
    (isClosed_le (continuous_pairU_right _) continuous_const) (by
      intro w hw
      simp only [Set.mem_setOf_eq] at hw
      rw [Metric.mem_closedBall, dist_comm]
      rw [pairU_eq_cosh] at hw
      have hc : Real.cosh (dist z w) ≤ 1 + 2 * R := by linarith
      have hd := dist_nonneg (x := z) (y := w)
      calc dist z w = Real.arcosh (Real.cosh (dist z w)) := (Real.arcosh_cosh hd).symm
        _ ≤ Real.arcosh (1 + 2 * R) :=
            (Real.arcosh_le_arcosh (Real.cosh_pos _)
              (by linarith [Real.one_le_cosh (dist z w)])).2 hc)

theorem halfTransform_abs_nonneg (φ : ℝ → ℝ) : 0 ≤ halfTransform (fun u => |φ u|) :=
  integral_nonneg fun w => mul_nonneg (abs_nonneg _) (sqrtIm_pos w).le

/-- The weight identity for `|φ|` in `lintegral` form. -/
theorem lintegral_kernel_sqrt {φ : ℝ → ℝ} {R : ℝ} (hφc : Continuous φ) (hφR : KernelSupport φ R)
    (z : ℍ) : ∫⁻ w, ENNReal.ofReal (|φ (pairU z w)| * sqrtIm w) =
      ENNReal.ofReal (halfTransform (fun u => |φ u|) * sqrtIm z) := by
  have hφc' : Continuous (fun u => |φ u|) := hφc.abs
  have hφR' : KernelSupport (fun u => |φ u|) R := fun u hu => by simp [hφR u hu]
  rw [← integral_kernel_sqrt hφc' hφR' z]
  refine (ofReal_integral_eq_lintegral_ofReal ?_
    (Eventually.of_forall fun w => mul_nonneg (abs_nonneg _) (sqrtIm_pos w).le)).symm
  refine ((hφc'.comp (continuous_pairU_right z)).mul continuous_sqrtIm).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_pairU_le z R) fun w hw => ?_
  simp only [Set.mem_setOf_eq, not_le] at hw
  simp [hφR _ hw]

/-- **Right tiling with the weight**: `Σ_B ∫_𝒟 |φ(u(z, Bz'))| √Im(Bz') dμ(z') = 2 h_{|φ|}(½) √Im z`. -/
theorem tsum_kernel_sqrt_fd {φ : ℝ → ℝ} {R : ℝ} (hφc : Continuous φ) (hφR : KernelSupport φ R)
    (z : ℍ) :
    ∑' B : SL(2, ℤ), ∫⁻ z' in fd, ENNReal.ofReal (|φ (pairU z (B • z'))| * sqrtIm (B • z')) =
      2 * ENNReal.ofReal (halfTransform (fun u => |φ u|) * sqrtIm z) := by
  rw [← lintegral_kernel_sqrt hφc hφR z]
  exact tsum_lintegral_fd_smul (fun w => ENNReal.ofReal (|φ (pairU z w)| * sqrtIm w))

/-- **Left tiling with the weight**: `Σ_B ∫_𝒟 |φ(u(z, Bz'))| √Im(B⁻¹z) dμ(z) = 2 h_{|φ|}(½) √Im z'`. -/
theorem tsum_kernel_sqrt_fd_left {φ : ℝ → ℝ} {R : ℝ} (hφc : Continuous φ) (hφR : KernelSupport φ R)
    (z' : ℍ) :
    ∑' B : SL(2, ℤ), ∫⁻ z in fd, ENNReal.ofReal (|φ (pairU z (B • z'))| * sqrtIm (B⁻¹ • z)) =
      2 * ENNReal.ofReal (halfTransform (fun u => |φ u|) * sqrtIm z') := by
  have e : ∀ (B : SL(2, ℤ)) (z : ℍ), pairU z (B • z') = pairU z' (B⁻¹ • z) := by
    intro B z
    rw [pairU_comm, ← pairU_smul_int B⁻¹, inv_smul_smul]
  simp_rw [e]
  rw [← tsum_kernel_sqrt_fd hφc hφR z']
  exact (Equiv.inv (SL(2, ℤ))).tsum_eq
    (fun B => ∫⁻ z in fd, ENNReal.ofReal (|φ (pairU z' (B • z))| * sqrtIm (B • z)))

/-! ## The weighted Schur test -/

/-- `‖(L_φ F)(z)‖ ≤ ½ Σ_B ∫_𝒟 |φ(u(z, Bz'))| ‖F(z')‖`. -/
theorem ofReal_norm_ppApply_le (φ : ℝ → ℝ) (F : ℍ → EuclideanSpace ℂ ι) (z : ℍ) :
    ENNReal.ofReal ‖ppApply ρ φ F z‖ ≤ ENNReal.ofReal (1 / 2) *
      ∑' B : SL(2, ℤ), ∫⁻ z' in fd, ENNReal.ofReal (|φ (pairU z (B • z'))| * ‖F z'‖) := by
  rw [ofReal_norm, ppApply, enorm_smul]
  have h2 : ‖(1 / 2 : ℂ)‖ₑ = ENNReal.ofReal (1 / 2) := by
    rw [← ofReal_norm]; norm_num
  rw [h2]
  gcongr
  refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun B => ?_)
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun z' => ?_))
  rw [← ofReal_norm]
  congr 1
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, LinearIsometryEquiv.norm_map]

/-- **The arithmetic–geometric step of the weighted Schur test.**  A nonzero term needs both points
above height `Y` and `u(z, Bz') ≤ R`, so `B` is parabolic and preserves heights; with the weight ratio
`r = √Im z / √Im z'`, `2fg ≤ r f² + g²/r`. -/
theorem cusp_amgm {φ : ℝ → ℝ} {R Y : ℝ} (hφR : KernelSupport φ R) (hY0 : 0 < Y)
    (hY : 4 * R + 2 < Y ^ 2) (z z' : ℍ) (B : SL(2, ℤ)) (f g : ℝ) :
    1 / 2 * (cuspCutoff Y z * cuspCutoff Y z' * |φ (pairU z (B • z'))| * f * g) ≤
      1 / 4 * (cuspCutoff Y z' * |φ (pairU z (B • z'))| * (sqrtIm (B⁻¹ • z) / sqrtIm z') * f ^ 2) +
      1 / 4 * (|φ (pairU z (B • z'))| * (sqrtIm (B • z') / sqrtIm z) * g ^ 2) := by
  have hψ0 := cuspCutoff_nonneg Y z
  have hψ'0 := cuspCutoff_nonneg Y z'
  have hψ1 := cuspCutoff_le_one Y z
  have hψ'1 := cuspCutoff_le_one Y z'
  have ha := abs_nonneg (φ (pairU z (B • z')))
  have hp := sqrtIm_pos z
  have hp' := sqrtIm_pos z'
  have hq1 : 0 ≤ sqrtIm (B⁻¹ • z) / sqrtIm z' := (div_pos (sqrtIm_pos _) hp').le
  have hq2 : 0 ≤ sqrtIm (B • z') / sqrtIm z := (div_pos (sqrtIm_pos _) hp).le
  by_cases h0 : cuspCutoff Y z * cuspCutoff Y z' * |φ (pairU z (B • z'))| = 0
  · rw [h0, zero_mul, zero_mul, mul_zero]
    positivity
  have hψ : 0 < cuspCutoff Y z := lt_of_le_of_ne hψ0 fun h => h0 (by rw [← h]; ring)
  have hψ' : 0 < cuspCutoff Y z' := lt_of_le_of_ne hψ'0 fun h => h0 (by rw [← h]; ring)
  have hapos : 0 < |φ (pairU z (B • z'))| := lt_of_le_of_ne ha fun h => h0 (by rw [← h]; ring)
  have hu : pairU z (B • z') ≤ R := by
    by_contra hu
    push Not at hu
    rw [hφR _ hu, abs_zero] at hapos
    exact lt_irrefl 0 hapos
  have hc := c_eq_zero_of_pairU_le_high hY0 hY (lt_im_of_cuspCutoff_pos hY0 hψ)
    (lt_im_of_cuspCutoff_pos hY0 hψ') hu
  have hcinv : (B⁻¹) 1 0 = 0 := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp [hc]
  have e1 : sqrtIm (B⁻¹ • z) = sqrtIm z := by rw [sqrtIm, im_smul_of_c_eq_zero _ hcinv]; rfl
  have e2 : sqrtIm (B • z') = sqrtIm z' := by rw [sqrtIm, im_smul_of_c_eq_zero _ hc]; rfl
  rw [e1, e2]
  set r := sqrtIm z / sqrtIm z' with hr_def
  have hr : 0 < r := div_pos hp hp'
  have hr' : sqrtIm z' / sqrtIm z = r⁻¹ := by rw [hr_def, inv_div]
  rw [hr']
  have amgm : 2 * (f * g) ≤ r * f ^ 2 + r⁻¹ * g ^ 2 := by
    have e : r * f ^ 2 + r⁻¹ * g ^ 2 - 2 * (f * g) = (r * f - g) ^ 2 / r := by
      field_simp
      ring
    have : 0 ≤ (r * f - g) ^ 2 / r := by positivity
    linarith
  set ψ := cuspCutoff Y z
  set ψ' := cuspCutoff Y z'
  set a := |φ (pairU z (B • z'))|
  have k1 : ψ * (ψ' * a * r * f ^ 2) ≤ ψ' * a * r * f ^ 2 :=
    mul_le_of_le_one_left (by positivity) hψ1
  have k2 : (ψ * ψ') * (a * r⁻¹ * g ^ 2) ≤ a * r⁻¹ * g ^ 2 :=
    mul_le_of_le_one_left (by positivity) (by nlinarith)
  have k3 := mul_le_mul_of_nonneg_left amgm (show 0 ≤ ψ * ψ' * a by positivity)
  nlinarith [k1, k2, k3]

/-- The first half of the arithmetic–geometric majorant (the `F`-side). -/
def cuspMajorantF (φ : ℝ → ℝ) (Y : ℝ) (F : ℍ → EuclideanSpace ℂ ι) (B : SL(2, ℤ)) (q : ℍ × ℍ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (1 / 4 * (cuspCutoff Y q.2 * |φ (pairU q.1 (B • q.2))| *
    (sqrtIm (B⁻¹ • q.1) / sqrtIm q.2) * ‖F q.2‖ ^ 2))

/-- The second half of the arithmetic–geometric majorant (the `G`-side). -/
def cuspMajorantG (φ : ℝ → ℝ) (G : ℍ → EuclideanSpace ℂ ι) (B : SL(2, ℤ)) (q : ℍ × ℍ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / 4 * (|φ (pairU q.1 (B • q.2))| * (sqrtIm (B • q.2) / sqrtIm q.1) *
    ‖G q.1‖ ^ 2))

theorem continuous_kernel_smul {φ : ℝ → ℝ} (hφc : Continuous φ) (B : SL(2, ℤ)) :
    Continuous (fun q : ℍ × ℍ => |φ (pairU q.1 (B • q.2))|) :=
  (hφc.comp (continuous_pairU.comp
    (continuous_fst.prodMk ((continuous_smul_int B).comp continuous_snd)))).abs

theorem measurable_cuspMajorantF {φ : ℝ → ℝ} (hφc : Continuous φ) (Y : ℝ)
    {F : ℍ → EuclideanSpace ℂ ι} (hF : StronglyMeasurable F) (B : SL(2, ℤ)) :
    Measurable (cuspMajorantF φ Y F B) := by
  have hc : Continuous (fun q : ℍ × ℍ => cuspCutoff Y q.2 * |φ (pairU q.1 (B • q.2))| *
      (sqrtIm (B⁻¹ • q.1) / sqrtIm q.2)) :=
    (((continuous_cuspCutoff Y).comp continuous_snd).mul (continuous_kernel_smul hφc B)).mul
      ((continuous_sqrtIm.comp ((continuous_smul_int B⁻¹).comp continuous_fst)).div
        (continuous_sqrtIm.comp continuous_snd) fun q => (sqrtIm_pos _).ne')
  exact ENNReal.measurable_ofReal.comp (measurable_const.mul (hc.measurable.mul
    ((hF.measurable.norm.pow_const 2).comp measurable_snd)))

theorem measurable_cuspMajorantG {φ : ℝ → ℝ} (hφc : Continuous φ)
    {G : ℍ → EuclideanSpace ℂ ι} (hG : StronglyMeasurable G) (B : SL(2, ℤ)) :
    Measurable (cuspMajorantG φ G B) := by
  have hc : Continuous (fun q : ℍ × ℍ => |φ (pairU q.1 (B • q.2))| *
      (sqrtIm (B • q.2) / sqrtIm q.1)) :=
    (continuous_kernel_smul hφc B).mul
      ((continuous_sqrtIm.comp ((continuous_smul_int B).comp continuous_snd)).div
        (continuous_sqrtIm.comp continuous_fst) fun q => (sqrtIm_pos _).ne')
  exact ENNReal.measurable_ofReal.comp (measurable_const.mul (hc.measurable.mul
    ((hG.measurable.norm.pow_const 2).comp measurable_fst)))

/-- Tonelli for the tiled double integral. -/
theorem lintegral_tsum_lintegral_swap {f : SL(2, ℤ) → ℍ × ℍ → ℝ≥0∞} (hf : ∀ B, Measurable (f B)) :
    ∫⁻ z in fd, ∑' B, ∫⁻ z' in fd, f B (z, z') = ∫⁻ z' in fd, ∑' B, ∫⁻ z in fd, f B (z, z') := by
  rw [lintegral_tsum fun B => ((hf B).lintegral_prod_right').aemeasurable,
    lintegral_tsum fun B => ((hf B).lintegral_prod_left').aemeasurable]
  exact tsum_congr fun B => lintegral_lintegral_swap ((hf B).aemeasurable)

/-- **The pointwise majorant.**  `ψ(z) ‖L_φ(ψF)(z)‖ ‖G(z)‖` is bounded by the two tiled halves of the
arithmetic–geometric majorant. -/
theorem ofReal_cusp_le_majorant {φ : ℝ → ℝ} {R Y : ℝ} (hφR : KernelSupport φ R) (hY0 : 0 < Y)
    (hY : 4 * R + 2 < Y ^ 2) {F G : ℍ → EuclideanSpace ℂ ι} (hF : StronglyMeasurable F) (hφc : Continuous φ)
    (z : ℍ) :
    ENNReal.ofReal (cuspCutoff Y z *
      ‖ppApply ρ φ (fun z' => ((cuspCutoff Y z' : ℝ) : ℂ) • F z') z‖ * ‖G z‖) ≤
      (∑' B, ∫⁻ z' in fd, cuspMajorantF φ Y F B (z, z')) +
        ∑' B, ∫⁻ z' in fd, cuspMajorantG φ G B (z, z') := by
  have h1 := ofReal_norm_ppApply_le (ρ := ρ) φ (fun z' => ((cuspCutoff Y z' : ℝ) : ℂ) • F z') z
  have hzG : 0 ≤ cuspCutoff Y z * ‖G z‖ := mul_nonneg (cuspCutoff_nonneg Y z) (norm_nonneg _)
  calc ENNReal.ofReal (cuspCutoff Y z *
        ‖ppApply ρ φ (fun z' => ((cuspCutoff Y z' : ℝ) : ℂ) • F z') z‖ * ‖G z‖)
      = ENNReal.ofReal (cuspCutoff Y z * ‖G z‖) *
          ENNReal.ofReal ‖ppApply ρ φ (fun z' => ((cuspCutoff Y z' : ℝ) : ℂ) • F z') z‖ := by
        rw [← ENNReal.ofReal_mul hzG]
        ring_nf
    _ ≤ ENNReal.ofReal (cuspCutoff Y z * ‖G z‖) * (ENNReal.ofReal (1 / 2) *
          ∑' B : SL(2, ℤ), ∫⁻ z' in fd, ENNReal.ofReal (|φ (pairU z (B • z'))| *
            ‖((cuspCutoff Y z' : ℝ) : ℂ) • F z'‖)) := by gcongr
    _ = ∑' B : SL(2, ℤ), ∫⁻ z' in fd, ENNReal.ofReal (1 / 2 * (cuspCutoff Y z * cuspCutoff Y z' *
          |φ (pairU z (B • z'))| * ‖F z'‖ * ‖G z‖)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hzG, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun B => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun z' => ?_
        rw [← ENNReal.ofReal_mul (mul_nonneg hzG (by norm_num)), norm_smul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (cuspCutoff_nonneg Y z')]
        ring_nf
    _ ≤ ∑' B : SL(2, ℤ), ∫⁻ z' in fd,
          (cuspMajorantF φ Y F B (z, z') + cuspMajorantG φ G B (z, z')) := by
        refine ENNReal.tsum_le_tsum fun B => lintegral_mono fun z' => ?_
        have hp1 : 0 ≤ 1 / 4 * (cuspCutoff Y z' * |φ (pairU z (B • z'))| *
            (sqrtIm (B⁻¹ • z) / sqrtIm z') * ‖F z'‖ ^ 2) :=
          mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (mul_nonneg (cuspCutoff_nonneg Y z')
            (abs_nonneg _)) (div_pos (sqrtIm_pos _) (sqrtIm_pos _)).le) (sq_nonneg _))
        have hp2 : 0 ≤ 1 / 4 * (|φ (pairU z (B • z'))| * (sqrtIm (B • z') / sqrtIm z) *
            ‖G z‖ ^ 2) :=
          mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (abs_nonneg _)
            (div_pos (sqrtIm_pos _) (sqrtIm_pos _)).le) (sq_nonneg _))
        simp only [cuspMajorantF, cuspMajorantG]
        rw [← ENNReal.ofReal_add hp1 hp2]
        exact ENNReal.ofReal_le_ofReal (cusp_amgm hφR hY0 hY z z' B _ _)
    _ = _ := by
        rw [← ENNReal.tsum_add]
        refine tsum_congr fun B => ?_
        exact lintegral_add_left ((measurable_cuspMajorantF hφc Y hF B).comp measurable_prodMk_left) _

/-- The `G`-side of the majorant integrates to `h_{|φ|}(½)/2 · ‖G(z)‖²`. -/
theorem tsum_cuspMajorantG {φ : ℝ → ℝ} {R : ℝ} (hφc : Continuous φ) (hφR : KernelSupport φ R)
    (G : ℍ → EuclideanSpace ℂ ι) (z : ℍ) :
    ∑' B, ∫⁻ z' in fd, cuspMajorantG φ G B (z, z') =
      ENNReal.ofReal (halfTransform (fun u => |φ u|) / 2) * ENNReal.ofReal (‖G z‖ ^ 2) := by
  have hh := halfTransform_abs_nonneg φ
  have hp := sqrtIm_pos z
  have hfac : ∀ (B : SL(2, ℤ)) (z' : ℍ), cuspMajorantG φ G B (z, z') =
      ENNReal.ofReal (|φ (pairU z (B • z'))| * sqrtIm (B • z')) *
        ENNReal.ofReal (‖G z‖ ^ 2 / (4 * sqrtIm z)) := by
    intro B z'
    rw [cuspMajorantG, ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (sqrtIm_pos _).le)]
    congr 1
    field_simp
  simp_rw [hfac]
  rw [show (∑' B : SL(2, ℤ), ∫⁻ z' in fd, ENNReal.ofReal (|φ (pairU z (B • z'))| * sqrtIm (B • z')) *
      ENNReal.ofReal (‖G z‖ ^ 2 / (4 * sqrtIm z))) = (∑' B : SL(2, ℤ), ∫⁻ z' in fd,
        ENNReal.ofReal (|φ (pairU z (B • z'))| * sqrtIm (B • z'))) *
          ENNReal.ofReal (‖G z‖ ^ 2 / (4 * sqrtIm z)) by
    rw [← ENNReal.tsum_mul_right]
    exact tsum_congr fun B => lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (halfTransform (fun u => |φ u|) * sqrtIm z) =
      ENNReal.ofReal (2 * (halfTransform (fun u => |φ u|) * sqrtIm z)) := by
    rw [ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_ofNat]
  rw [tsum_kernel_sqrt_fd hφc hφR z, h2, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/-- The `F`-side of the majorant, after the swap, integrates to at most `h_{|φ|}(½)/2 · ‖F(z')‖²`. -/
theorem tsum_cuspMajorantF_le {φ : ℝ → ℝ} {R : ℝ} (hφc : Continuous φ) (hφR : KernelSupport φ R)
    (Y : ℝ) (F : ℍ → EuclideanSpace ℂ ι) (z' : ℍ) :
    ∑' B, ∫⁻ z in fd, cuspMajorantF φ Y F B (z, z') ≤
      ENNReal.ofReal (halfTransform (fun u => |φ u|) / 2) * ENNReal.ofReal (‖F z'‖ ^ 2) := by
  have hh := halfTransform_abs_nonneg φ
  have hp := sqrtIm_pos z'
  have hψ0 := cuspCutoff_nonneg Y z'
  have hfac : ∀ (B : SL(2, ℤ)) (z : ℍ), cuspMajorantF φ Y F B (z, z') =
      ENNReal.ofReal (|φ (pairU z (B • z'))| * sqrtIm (B⁻¹ • z)) *
        ENNReal.ofReal (cuspCutoff Y z' * ‖F z'‖ ^ 2 / (4 * sqrtIm z')) := by
    intro B z
    rw [cuspMajorantF, ← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (sqrtIm_pos _).le)]
    congr 1
    field_simp
  simp_rw [hfac]
  rw [show (∑' B : SL(2, ℤ), ∫⁻ z in fd, ENNReal.ofReal (|φ (pairU z (B • z'))| * sqrtIm (B⁻¹ • z)) *
      ENNReal.ofReal (cuspCutoff Y z' * ‖F z'‖ ^ 2 / (4 * sqrtIm z'))) = (∑' B : SL(2, ℤ),
        ∫⁻ z in fd, ENNReal.ofReal (|φ (pairU z (B • z'))| * sqrtIm (B⁻¹ • z))) *
          ENNReal.ofReal (cuspCutoff Y z' * ‖F z'‖ ^ 2 / (4 * sqrtIm z')) by
    rw [← ENNReal.tsum_mul_right]
    exact tsum_congr fun B => lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (halfTransform (fun u => |φ u|) * sqrtIm z') =
      ENNReal.ofReal (2 * (halfTransform (fun u => |φ u|) * sqrtIm z')) := by
    rw [ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_ofNat]
  rw [tsum_kernel_sqrt_fd_left hφc hφR z', h2, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : 2 * (halfTransform (fun u => |φ u|) * sqrtIm z') *
      (cuspCutoff Y z' * ‖F z'‖ ^ 2 / (4 * sqrtIm z')) =
      halfTransform (fun u => |φ u|) / 2 * (cuspCutoff Y z' * ‖F z'‖ ^ 2) := by
    field_simp
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (sq_nonneg _) (cuspCutoff_le_one Y z'))
    (by positivity)

/-- **The weighted Schur test in integrated form.** -/
theorem lintegral_cusp_le {φ : ℝ → ℝ} {R Y : ℝ} (hφc : Continuous φ) (hφR : KernelSupport φ R)
    (hY0 : 0 < Y) (hY : 4 * R + 2 < Y ^ 2) {F G : ℍ → EuclideanSpace ℂ ι}
    (hF : StronglyMeasurable F) :
    ∫⁻ z in fd, ENNReal.ofReal (cuspCutoff Y z *
      ‖ppApply ρ φ (fun z' => ((cuspCutoff Y z' : ℝ) : ℂ) • F z') z‖ * ‖G z‖) ≤
      ENNReal.ofReal (halfTransform (fun u => |φ u|) / 2) * (∫⁻ z in fd, ENNReal.ofReal (‖F z‖ ^ 2)) +
      ENNReal.ofReal (halfTransform (fun u => |φ u|) / 2) * ∫⁻ z in fd, ENNReal.ofReal (‖G z‖ ^ 2) := by
  have hA : Measurable (fun z => ∑' B, ∫⁻ z' in fd, cuspMajorantF φ Y F B (z, z')) :=
    Measurable.tsum fun B => (measurable_cuspMajorantF hφc Y hF B).lintegral_prod_right'
  calc ∫⁻ z in fd, ENNReal.ofReal (cuspCutoff Y z *
        ‖ppApply ρ φ (fun z' => ((cuspCutoff Y z' : ℝ) : ℂ) • F z') z‖ * ‖G z‖)
      ≤ ∫⁻ z in fd, ((∑' B, ∫⁻ z' in fd, cuspMajorantF φ Y F B (z, z')) +
        ∑' B, ∫⁻ z' in fd, cuspMajorantG φ G B (z, z')) :=
        lintegral_mono fun z => ofReal_cusp_le_majorant (ρ := ρ) hφR hY0 hY hF hφc z
    _ = (∫⁻ z in fd, ∑' B, ∫⁻ z' in fd, cuspMajorantF φ Y F B (z, z')) +
        ∫⁻ z in fd, ∑' B, ∫⁻ z' in fd, cuspMajorantG φ G B (z, z') := lintegral_add_left hA _
    _ ≤ _ := by
        refine add_le_add ?_ (le_of_eq ?_)
        · rw [lintegral_tsum_lintegral_swap (measurable_cuspMajorantF hφc Y hF),
            ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact lintegral_mono fun z' => tsum_cuspMajorantF_le hφc hφR Y F z'
        · simp_rw [tsum_cuspMajorantG hφc hφR G]
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! ## Multiplication by a cutoff -/

theorem memLp_mulFun {g : ℍ → ℝ} (hg : Measurable g) (hg1 : ∀ z, |g z| ≤ 1) (F : RepL2 ι) :
    MemLp (fun z => ((g z : ℝ) : ℂ) • (F : ℍ → EuclideanSpace ℂ ι) z) 2 cellMeasure :=
  (Lp.memLp F).of_le ((Complex.measurable_ofReal.comp hg).aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable F)) (Eventually.of_forall fun z => by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hg1 z))

variable (ι) in
/-- Multiplication by a measurable `g` with `|g| ≤ 1`, as a linear map on `L²(𝒟; ℂ^ι)`. -/
def repMulLinear {g : ℍ → ℝ} (hg : Measurable g) (hg1 : ∀ z, |g z| ≤ 1) :
    RepL2 ι →ₗ[ℂ] RepL2 ι where
  toFun F := (memLp_mulFun hg hg1 F).toLp _
  map_add' F G := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_mulFun hg hg1 (F + G)),
      Lp.coeFn_add ((memLp_mulFun hg hg1 F).toLp _) ((memLp_mulFun hg hg1 G).toLp _),
      MemLp.coeFn_toLp (memLp_mulFun hg hg1 F), MemLp.coeFn_toLp (memLp_mulFun hg hg1 G),
      Lp.coeFn_add F G] with z h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, smul_add]
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_mulFun hg hg1 (c • F)),
      Lp.coeFn_smul c ((memLp_mulFun hg hg1 F).toLp _),
      MemLp.coeFn_toLp (memLp_mulFun hg hg1 F), Lp.coeFn_smul c F] with z h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, Pi.smul_apply, smul_comm]

variable (ι) in
/-- Multiplication by a measurable `g` with `|g| ≤ 1` on `L²(𝒟; ℂ^ι)`; its norm is at most `1`. -/
def repMul {g : ℍ → ℝ} (hg : Measurable g) (hg1 : ∀ z, |g z| ≤ 1) : RepL2 ι →L[ℂ] RepL2 ι :=
  LinearMap.mkContinuous (repMulLinear ι hg hg1) 1 fun F => by
    rw [one_mul]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_mulFun hg hg1 F)] with z hz
    change ‖((memLp_mulFun hg hg1 F).toLp _ : ℍ → EuclideanSpace ℂ ι) z‖ ≤ _
    rw [hz, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hg1 z)

theorem repMul_coeFn {g : ℍ → ℝ} (hg : Measurable g) (hg1 : ∀ z, |g z| ≤ 1) (F : RepL2 ι) :
    (repMul ι hg hg1 F : ℍ → EuclideanSpace ℂ ι) =ᵐ[cellMeasure] fun z => ((g z : ℝ) : ℂ) • F z :=
  MemLp.coeFn_toLp (memLp_mulFun hg hg1 F)

theorem abs_cuspCutoff_le (Y : ℝ) (z : ℍ) : |cuspCutoff Y z| ≤ 1 := by
  rw [abs_of_nonneg (cuspCutoff_nonneg Y z)]
  exact cuspCutoff_le_one Y z

variable (ι) in
/-- Multiplication by the cusp cutoff `ψ_Y`. -/
def cuspMul (Y : ℝ) : RepL2 ι →L[ℂ] RepL2 ι :=
  repMul ι (continuous_cuspCutoff Y).measurable (abs_cuspCutoff_le Y)

theorem lintegral_normSq_eq (F : RepL2 ι) :
    ∫⁻ z in fd, ENNReal.ofReal (‖(F : ℍ → EuclideanSpace ℂ ι) z‖ ^ 2) = ENNReal.ofReal (‖F‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F)]
  exact (eLpNorm_two_sq_ofReal _).symm

/-- An operator whose sesquilinear form is bounded by `c (‖x‖² + ‖y‖²)/2` has norm at most `c`. -/
theorem opNorm_le_of_inner_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {T : H →L[ℂ] H} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x y, ‖⟪T x, y⟫_ℂ‖ ≤ c / 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) : ‖T‖ ≤ c := by
  refine T.opNorm_le_bound hc fun x => ?_
  rcases eq_or_ne (T x) 0 with h0 | h0
  · rw [h0, norm_zero]
    positivity
  have hTx : 0 < ‖T x‖ := norm_pos_iff.2 h0
  have hx : 0 < ‖x‖ := by
    refine norm_pos_iff.2 fun hx => h0 ?_
    rw [hx, map_zero]
  have hy := h x (((‖x‖ / ‖T x‖ : ℝ) : ℂ) • T x)
  have ht : 0 ≤ ‖x‖ / ‖T x‖ := by positivity
  simp only [inner_smul_right, inner_self_eq_norm_sq_to_K, norm_mul, norm_pow, norm_smul,
    Complex.norm_real, RCLike.norm_ofReal, Real.norm_eq_abs, abs_norm, abs_of_nonneg ht] at hy
  rw [div_mul_cancel₀ _ hTx.ne'] at hy
  have hy' : ‖x‖ / ‖T x‖ * ‖T x‖ ^ 2 = ‖x‖ * ‖T x‖ := by
    field_simp
  rw [hy'] at hy
  nlinarith

/-! ## The cusp operator -/

section CuspOperator

variable {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M) (hR : 0 ≤ R)
  (hφR : KernelSupport φ R)

variable (ρ) in
/-- **The cusp operator** `B_Y = ψ_Y L_φ ψ_Y`. -/
def cuspOp (Y : ℝ) : RepL2 ι →L[ℂ] RepL2 ι :=
  cuspMul ι Y ∘L ppL2 ρ hφc hφM hR hφR ∘L cuspMul ι Y

theorem cuspOp_coeFn (Y : ℝ) (F : RepL2 ι) :
    (cuspOp ρ hφc hφM hR hφR Y F : ℍ → EuclideanSpace ℂ ι) =ᵐ[cellMeasure] fun z =>
      ((cuspCutoff Y z : ℝ) : ℂ) •
        ppApply ρ φ (fun z' => ((cuspCutoff Y z' : ℝ) : ℂ) • (F : ℍ → EuclideanSpace ℂ ι) z') z := by
  have h1 := repMul_coeFn (ι := ι) (continuous_cuspCutoff Y).measurable (abs_cuspCutoff_le Y)
    (ppL2 ρ hφc hφM hR hφR (cuspMul ι Y F))
  have h2 := ppL2_coeFn hφc hφM hR hφR (ρ := ρ) (cuspMul ι Y F)
  have h3 : ppApply ρ φ (cuspMul ι Y F : ℍ → EuclideanSpace ℂ ι) =
      ppApply ρ φ (fun z' => ((cuspCutoff Y z' : ℝ) : ℂ) • (F : ℍ → EuclideanSpace ℂ ι) z') :=
    ppApply_congr_ae φ (repMul_coeFn (continuous_cuspCutoff Y).measurable (abs_cuspCutoff_le Y) F)
  filter_upwards [h1, h2] with z hz1 hz2
  change (repMul ι (continuous_cuspCutoff Y).measurable (abs_cuspCutoff_le Y)
    (ppL2 ρ hφc hφM hR hφR (cuspMul ι Y F)) : ℍ → EuclideanSpace ℂ ι) z = _
  rw [hz1, hz2, h3]

/-- **The sesquilinear bound of the cusp operator**:
`|⟪B_Y F, G⟫| ≤ h_{|φ|}(½)(‖F‖² + ‖G‖²)/2` once `Y² > 4R + 2`. -/
theorem norm_inner_cuspOp_le {Y : ℝ} (hY0 : 0 < Y) (hY : 4 * R + 2 < Y ^ 2) (F G : RepL2 ι) :
    ‖⟪cuspOp ρ hφc hφM hR hφR Y F, G⟫_ℂ‖ ≤
      halfTransform (fun u => |φ u|) / 2 * (‖F‖ ^ 2 + ‖G‖ ^ 2) := by
  have hh : 0 ≤ halfTransform (fun u => |φ u|) / 2 := by
    have := halfTransform_abs_nonneg φ
    positivity
  have key : ENNReal.ofReal ‖⟪cuspOp ρ hφc hφM hR hφR Y F, G⟫_ℂ‖ ≤
      ENNReal.ofReal (halfTransform (fun u => |φ u|) / 2 * (‖F‖ ^ 2 + ‖G‖ ^ 2)) := by
    rw [MeasureTheory.L2.inner_def, ofReal_norm]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ z, ‖⟪(cuspOp ρ hφc hφM hR hφR Y F : ℍ → EuclideanSpace ℂ ι) z,
          (G : ℍ → EuclideanSpace ℂ ι) z⟫_ℂ‖ₑ ∂cellMeasure
        ≤ ∫⁻ z in fd, ENNReal.ofReal (cuspCutoff Y z * ‖ppApply ρ φ (fun z' =>
            ((cuspCutoff Y z' : ℝ) : ℂ) • (F : ℍ → EuclideanSpace ℂ ι) z') z‖ *
              ‖(G : ℍ → EuclideanSpace ℂ ι) z‖) := by
          refine lintegral_mono_ae ?_
          filter_upwards [cuspOp_coeFn hφc hφM hR hφR Y F] with z hz
          rw [hz, ← ofReal_norm]
          refine ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans (le_of_eq ?_))
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cuspCutoff_nonneg Y z)]
      _ ≤ _ := lintegral_cusp_le (F := (F : ℍ → EuclideanSpace ℂ ι))
          (G := (G : ℍ → EuclideanSpace ℂ ι)) hφc hφR hY0 hY (Lp.stronglyMeasurable F)
      _ = _ := by
          rw [lintegral_normSq_eq F, lintegral_normSq_eq G, ← ENNReal.ofReal_mul hh,
            ← ENNReal.ofReal_mul hh, ← ENNReal.ofReal_add (by positivity) (by positivity), mul_add]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key

/-- **The cusp bound**: `‖ψ_Y L_φ ψ_Y‖ ≤ h_{|φ|}(½)` once `Y² > 4R + 2`. -/
theorem norm_cuspOp_le {Y : ℝ} (hY0 : 0 < Y) (hY : 4 * R + 2 < Y ^ 2) :
    ‖cuspOp ρ hφc hφM hR hφR Y‖ ≤ halfTransform (fun u => |φ u|) :=
  opNorm_le_of_inner_le (halfTransform_abs_nonneg φ) (norm_inner_cuspOp_le hφc hφM hR hφR hY0 hY)

end CuspOperator

end

end GaloisForLFunctions.RHTower.RepPointPair
