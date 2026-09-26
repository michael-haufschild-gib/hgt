import GaloisForLFunctions.RHTower.WeightMaassLaplacian
import GaloisForLFunctions.RHTower.HalfWeightEisenstein
import GaloisForLFunctions.RHTower.EisensteinFundamentalDomainIntegrability

/-!
# The weight-`1/2` analogue of Selberg's conjecture fails: `y^{1/4} θ` has eigenvalue `3/16`

Let `θ(z) = Σ e(n²z)` and `F = y^{1/4} θ`.

* **Eigen-equation.** `θ` is holomorphic, so the general identity
  `Δ_k(y^{k/2} f) = (k/2)(1 - k/2) y^{k/2} f` at `k = 1/2` gives `Δ_{1/2} F = (3/16) F`
  (`theta_weightLaplacian`).
* **Automorphy.** On `Γ₀(4)`, `θ(γz) = J(γ,z) θ(z)` with `|J|² = |cz+d|`. Since
  `Im(γz) = y/|cz+d|²`, this gives `F(γz) = j(γ,z) F(z)` with the unitary multiplier
  `j = J/|J|` (`thetaMaass_smul`).
* **Square-integrability.** The Gaussian bound `|θ(τ)| ≤ 1 + 1/√(Im τ)` gives
  `y^{1/2}|θ|² ≤ 2√y + 1/√y`. For `z` in the modular fundamental domain and any
  `γ ∈ SL₂(ℤ)`, the height `v = Im(γz)` satisfies `v ≤ y + 2` and `1/√v = |cz+d|/√y`, so
  `y(γz)^{1/2}|θ(γz)|² = O(y^{1/2})`. This is integrable against `dμ` on the fundamental domain
  (`integrableOn_fd_thetaMaass_sq`).

Hence (`weight_half_exceptional`) the weight-`1/2` Laplacian on `Γ₀(4)` with the theta multiplier
has a square-integrable eigenfunction with eigenvalue `3/16 < 1/4`. Selberg's `3/16` is therefore
sharp for any argument whose inputs also hold in weight `1/2`: Kloosterman-sum bounds of Weil
strength hold equally for the theta multiplier (Salié sums).
-/

open Complex MeasureTheory Set UpperHalfPlane ModularGroup
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.HalfWeight

open WeightMaassLaplacian

noncomputable section

/-- `F(w) = y^{1/4} θ(w)` in the complex chart. -/
def thetaMaassC (w : ℂ) : ℂ := ((w.im ^ ((1 / 2 : ℝ) / 2) : ℝ) : ℂ) * theta w

theorem differentiableOn_theta : DifferentiableOn ℂ theta {w : ℂ | 0 < w.im} := by
  intro w hw
  have h2 : 0 < (2 * w).im := by simp only [mem_setOf_eq] at hw; simp; linarith
  exact ((differentiableAt_jacobiTheta h2).comp w
    ((differentiableAt_id).const_mul 2)).differentiableWithinAt

/-- **`y^{1/4} θ` is an eigenfunction of the weight-`1/2` Laplacian with eigenvalue `3/16`.** -/
theorem theta_weightLaplacian {z : ℂ} (hz : 0 < z.im) :
    weightLaplacian (1 / 2) thetaMaassC z = (3 / 16 : ℂ) * thetaMaassC z := by
  have h := weightLaplacian_rpowIm_mul (1 / 2) differentiableOn_theta hz
  unfold thetaMaassC
  rw [h]
  push_cast
  ring

/-- `y^{1/4} θ(z)` on the upper half-plane. -/
def thetaMaass (z : ℍ) : ℂ := thetaMaassC z

theorem norm_sq_thetaMaass (z : ℍ) : ‖thetaMaass z‖ ^ 2 = thetaInv z := by
  unfold thetaMaass thetaMaassC thetaInv
  simp only [UpperHalfPlane.coe_im]
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg z.im_pos.le _), ← Real.rpow_natCast, ← Real.rpow_mul z.im_pos.le,
    Real.sqrt_eq_rpow]
  norm_num

/-- **Unitary automorphy on `Γ₀(4)`:** `F(γz) = j(γ,z) F(z)`. -/
theorem thetaMaass_smul {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) (z : ℍ) :
    thetaMaass (γ • z) = jU γ z * thetaMaass z := by
  have hJ := norm_sq_J hγ z
  have hJ0 := norm_J_pos γ z
  have him := ModularGroup.im_smul_eq_div_normSq γ z
  rw [Complex.normSq_eq_norm_sq, ← hJ] at him
  unfold thetaMaass thetaMaassC jU
  rw [show ((γ • z : ℍ) : ℂ).im = (γ • z).im from rfl, him, theta_smul]
  have hq : ((z.im / (‖J γ z‖ ^ 2) ^ 2) ^ ((1 / 2 : ℝ) / 2) : ℝ) =
      z.im ^ ((1 / 2 : ℝ) / 2) / ‖J γ z‖ := by
    rw [Real.div_rpow z.im_pos.le (by positivity), ← pow_mul, ← Real.rpow_natCast,
      ← Real.rpow_mul hJ0.le]
    norm_num
  rw [hq]
  simp only [UpperHalfPlane.coe_im]
  push_cast
  field_simp

theorem thetaMaass_ne_zero (z : ℍ) : thetaMaass z ≠ 0 := by
  unfold thetaMaass thetaMaassC
  exact mul_ne_zero (by exact_mod_cast (Real.rpow_pos_of_pos z.im_pos _).ne') (theta_ne_zero' z)

theorem norm_theta_le (z : ℍ) : ‖theta z‖ ≤ 1 + 1 / √(2 * z.im) := by
  have h2 : 0 < (2 * (z : ℂ)).im := by simp [z.im_pos]
  have hb := norm_jacobiTheta_le h2
  have e : (2 * (z : ℂ)).im = 2 * z.im := by simp
  rw [e] at hb
  simpa [theta] using hb

/-- `y^{1/2}|θ|² ≤ 2√y + 1/√y`. -/
theorem thetaInv_le (z : ℍ) : thetaInv z ≤ 2 * √z.im + 1 / √z.im := by
  have hy := z.im_pos
  have hs : 0 < √z.im := Real.sqrt_pos.2 hy
  have h2s : 0 < √(2 * z.im) := Real.sqrt_pos.2 (by linarith)
  have hθ := norm_theta_le z
  have hθ0 := norm_nonneg (theta z)
  set t := 1 / √(2 * z.im) with htdef
  have ht2 : t ^ 2 = 1 / (2 * z.im) := by
    rw [htdef, div_pow, Real.sq_sqrt (by linarith), one_pow]
  have hsq : ‖theta z‖ ^ 2 ≤ 2 + 1 / z.im := by
    have h1 : ‖theta z‖ ^ 2 ≤ (1 + t) ^ 2 := pow_le_pow_left₀ hθ0 hθ 2
    have h3 : (1 + t) ^ 2 ≤ 2 + 2 * t ^ 2 := by nlinarith [sq_nonneg (1 - t)]
    rw [ht2] at h3
    have : 2 * (1 / (2 * z.im)) = 1 / z.im := by field_simp
    linarith
  unfold thetaInv
  have hyy : √z.im * (1 / z.im) = 1 / √z.im := by
    have h := Real.sq_sqrt hy.le
    field_simp
    nlinarith [Real.sqrt_nonneg z.im]
  calc √z.im * ‖theta z‖ ^ 2 ≤ √z.im * (2 + 1 / z.im) := mul_le_mul_of_nonneg_left hsq hs.le
    _ = 2 * √z.im + 1 / √z.im := by rw [mul_add, hyy]; ring

/-- On the modular fundamental domain, `y^{1/2}|θ|²` at `γz` is `O(y^{1/2})` for every
`γ ∈ SL₂(ℤ)`. -/
theorem thetaInv_smul_le (γ : SL(2, ℤ)) {z : ℍ} (hz : z ∈ ModularGroup.fd) :
    thetaInv (γ • z) ≤ (4 + 3 * (|(γ 1 0 : ℝ)| + |(γ 1 1 : ℝ)|)) * z.im ^ (1 / 2 : ℝ) := by
  have hy := z.im_pos
  have hy34 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have hre : |z.re| ≤ 1 / 2 := hz.2
  have hy1 : (1 / 2 : ℝ) ≤ z.im := by nlinarith
  set c : ℝ := ((γ 1 0 : ℤ) : ℝ) with hcdef
  set d : ℝ := ((γ 1 1 : ℤ) : ℝ) with hddef
  set D := ‖UpperHalfPlane.denom γ z‖ with hDdef
  have hden : UpperHalfPlane.denom γ z = (c : ℂ) * z + d := by
    simp [UpperHalfPlane.denom, c, d]
  have hv := ModularGroup.im_smul_eq_div_normSq γ z
  rw [Complex.normSq_eq_norm_sq] at hv
  change (γ • z).im = z.im / D ^ 2 at hv
  have hD0 : 0 < D := norm_pos_iff.2 (UpperHalfPlane.denom_ne_zero _ _)
  -- upper bound for D
  have hDup : D ≤ (|c| + |d|) * (1 + z.im) := by
    rw [hDdef, hden]
    have hz' : ‖(z : ℂ)‖ ≤ 1 + z.im := by
      have := Complex.norm_le_abs_re_add_abs_im (z : ℂ)
      simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at this
      rw [abs_of_pos hy] at this
      linarith
    calc ‖(c : ℂ) * z + d‖ ≤ ‖(c : ℂ) * z‖ + ‖(d : ℂ)‖ := norm_add_le _ _
      _ = |c| * ‖(z : ℂ)‖ + |d| := by rw [norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |c| * (1 + z.im) + |d| * (1 + z.im) := by
          gcongr; nlinarith [abs_nonneg d]
      _ = _ := by ring
  -- the image height is at most y + 2
  have hvle : (γ • z).im ≤ z.im + 2 := by
    rw [hv]
    by_cases hc : (γ 1 0 : ℤ) = 0
    · have hdet : (γ 0 0) * (γ 1 1) - (γ 0 1) * (γ 1 0) = 1 := by
        have := γ.2; rwa [Matrix.det_fin_two] at this
      rw [hc, mul_zero, sub_zero] at hdet
      have hd1 : |(γ 1 1 : ℤ)| = 1 := Int.isUnit_iff_abs_eq.mp (IsUnit.of_mul_eq_one (γ 0 0) (by rw [mul_comm]; exact hdet))
      have hD1 : D = 1 := by
        rw [hDdef, hden]
        have hc0 : c = 0 := by simp [c, hc]
        rw [hc0]
        simp only [Complex.ofReal_zero, zero_mul, zero_add, Complex.norm_real, Real.norm_eq_abs]
        have : |d| = 1 := by simp only [d]; exact_mod_cast hd1
        exact this
      rw [hD1]; simp
    · have hc1 : 1 ≤ |c| := by
        simp only [c]; exact_mod_cast Int.one_le_abs hc
      have hDlow : |c| * z.im ≤ D := by
        rw [hDdef, hden]
        have := Complex.abs_im_le_norm ((c : ℂ) * z + d)
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, zero_mul, add_zero] at this
        rw [abs_mul, abs_of_pos hy] at this
        linarith
      have hyD : z.im ≤ D := by nlinarith
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg D]
  have hy23 : (2 / 3 : ℝ) ≤ z.im := by nlinarith
  have h1 := thetaInv_le (γ • z)
  have hsy : 0 < √z.im := Real.sqrt_pos.2 hy
  have hsv : √((γ • z).im) ≤ 2 * √z.im := by
    have h4 : √(4 * z.im) = 2 * √z.im := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [← h4]
    exact Real.sqrt_le_sqrt (by linarith)
  have hinv : 1 / √((γ • z).im) = D / √z.im := by
    rw [hv, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hD0.le]
    field_simp
  have hDy : D / √z.im ≤ 3 * (|c| + |d|) * √z.im := by
    rw [div_le_iff₀ hsy]
    have hss : √z.im * √z.im = z.im := Real.mul_self_sqrt hy.le
    have h3 : (|c| + |d|) * (1 + z.im) ≤ 3 * (|c| + |d|) * z.im := by
      have := add_nonneg (abs_nonneg c) (abs_nonneg d)
      nlinarith
    nlinarith
  calc thetaInv (γ • z) ≤ 2 * √((γ • z).im) + 1 / √((γ • z).im) := h1
    _ ≤ 2 * (2 * √z.im) + 3 * (|c| + |d|) * √z.im := by rw [hinv]; linarith
    _ = (4 + 3 * (|c| + |d|)) * z.im ^ (1 / 2 : ℝ) := by rw [← Real.sqrt_eq_rpow]; ring

theorem continuous_thetaInv : Continuous thetaInv := by
  have hθ : Continuous fun z : ℍ => theta (z : ℂ) :=
    differentiableOn_theta.continuousOn.comp_continuous UpperHalfPlane.continuous_coe
      (fun z => z.im_pos)
  unfold thetaInv
  exact (Real.continuous_sqrt.comp UpperHalfPlane.continuous_im).mul (hθ.norm.pow 2)

/-- **Square-integrability over every translate of the modular fundamental domain**, hence over
`Γ₀(4)\ℍ` (a finite union of such translates). -/
theorem integrableOn_fd_thetaMaass_sq (γ : SL(2, ℤ)) :
    IntegrableOn (fun z : ℍ => ((‖thetaMaass (γ • z)‖ ^ 2 : ℝ) : ℂ)) ModularGroup.fd volume := by
  apply RHTower.integrableOn_fd_of_norm_le (β := 1 / 2)
    (C := 4 + 3 * (|((γ 1 0 : ℤ) : ℝ)| + |((γ 1 1 : ℤ) : ℝ)|))
  · apply Continuous.aestronglyMeasurable
    simp_rw [norm_sq_thetaMaass]
    have hγc : Continuous fun z : ℍ => γ • z := (Homeomorph.smul (γ : GL (Fin 2) ℝ)).continuous
    exact Complex.continuous_ofReal.comp (continuous_thetaInv.comp hγc)
  · norm_num
  · intro z hz
    rw [norm_sq_thetaMaass, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by unfold thetaInv; positivity)]
    exact thetaInv_smul_le γ hz

/-- **The weight-`1/2` analogue of Selberg's eigenvalue conjecture is false.** On `Γ₀(4)` with
the theta multiplier, `F = y^{1/4} θ` is nowhere zero, automorphic with the unitary multiplier
`j`, square-integrable on every translate of the fundamental domain, and an eigenfunction of the
weight-`1/2` Laplacian with eigenvalue `3/16 < 1/4`. -/
theorem weight_half_exceptional :
    (∀ z : ℍ, thetaMaass z ≠ 0) ∧
    (∀ γ ∈ CongruenceSubgroup.Gamma0 4, ∀ z : ℍ, thetaMaass (γ • z) = jU γ z * thetaMaass z) ∧
    (∀ z : ℂ, 0 < z.im → weightLaplacian (1 / 2) thetaMaassC z = (3 / 16 : ℂ) * thetaMaassC z) ∧
    (∀ γ : SL(2, ℤ),
      IntegrableOn (fun z : ℍ => ((‖thetaMaass (γ • z)‖ ^ 2 : ℝ) : ℂ)) ModularGroup.fd volume) ∧
    (3 / 16 : ℝ) < 1 / 4 :=
  ⟨thetaMaass_ne_zero, fun _ hγ z => thetaMaass_smul hγ z, fun _ hz => theta_weightLaplacian hz,
    integrableOn_fd_thetaMaass_sq, by norm_num⟩

end

end GaloisForLFunctions.RHTower.HalfWeight
