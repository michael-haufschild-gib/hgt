import GaloisForLFunctions.RHTower.SmoothAFEZetaResidueDecomposition
import GaloisForLFunctions.RHTower.DualCarrierWeightOscillation

/-!
# The smoothed diagonal of the block twisted moment: Mellin form and residues

On the diagonal `mh = nk` of the product approximate functional equation the direct side collapses,
along the reduced direction `m = jk'`, `n = jh'` (`h' = h/(h,k)`, `k' = k/(h,k)`), to the quadratic
smoothed sum

`D(σ₀, c, x) = Σ_{j ≥ 1} j^{-2σ₀} V(j² c / x)`,   `c = h'k'`,

with `V` the Gaussian cutoff `V(u) = (1/2πi)∫_{(1)} u^{-w} e^{w²}/w dw`.  Summing the Dirichlet
series under the integral gives the line integral of

`F(w) = ζ(2σ₀ + 2w) (x/c)^w e^{w²}/w`,

which has exactly two poles on the left of the line: the kernel pole at `0` with residue `ζ(2σ₀)`
and the zeta pole at `δ₀ = ½ − σ₀` with residue `(x/c)^{δ₀} e^{δ₀²}/(2δ₀)`.  Filling the zeta pole
with the corpus's entire regularisation `(s−1)ζ(s)` and taking two divided differences splits `F`
exactly into its two Cauchy kernels plus an entire remainder.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- The diagonal Mellin integrand `ζ(2σ₀+2w)(x/c)^w e^{w²}/w`. -/
def smoothDiagonalIntegrand (σ₀ c x : ℝ) (w : ℂ) : ℂ :=
  riemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * w) * ((x / c : ℝ) : ℂ) ^ w * smoothAFEGaussianKernel w

/-- The `j`-th term `(j+1)^{-(2σ₀+2w)} (x/c)^w e^{w²}/w`. -/
def smoothDiagonalTerm (σ₀ c x : ℝ) (j : ℕ) (w : ℂ) : ℂ :=
  (1 / (j + 1 : ℂ) ^ (((2 * σ₀ : ℝ) : ℂ) + 2 * w)) * ((x / c : ℝ) : ℂ) ^ w
    * smoothAFEGaussianKernel w

/-- The smoothed diagonal `Σ_j (j+1)^{-2σ₀} V((j+1)² c/x)`. -/
def smoothDiagonal (σ₀ c x : ℝ) : ℂ :=
  ∑' j : ℕ, (j + 1 : ℂ) ^ (-((2 * σ₀ : ℝ) : ℂ))
    * smoothAFECutoff (((j + 1 : ℝ) ^ 2 * c) / x)

/-! ## The term is a coefficient times the cutoff integrand -/

theorem smoothDiagonalTerm_eq {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (σ₀ : ℝ) (j : ℕ) (w : ℂ) :
    smoothDiagonalTerm σ₀ c x j w
      = (j + 1 : ℂ) ^ (-((2 * σ₀ : ℝ) : ℂ))
        * smoothAFEMellinIntegrand (((j + 1 : ℝ) ^ 2 * c) / x) w := by
  have hj : (0 : ℝ) < j + 1 := by positivity
  have hjc : (j + 1 : ℂ) ≠ 0 := by exact_mod_cast hj.ne'
  unfold smoothDiagonalTerm smoothAFEMellinIntegrand
  -- the cutoff argument
  have h1 : ((((j + 1 : ℝ) ^ 2 * c) / x : ℝ) : ℂ) ^ (-w)
      = (((j + 1 : ℝ) ^ 2 * c : ℝ) : ℂ) ^ (-w) * (x : ℂ) ^ w :=
    cpow_div_pos_neg (by positivity) hx w
  have h2 : (((j + 1 : ℝ) ^ 2 * c : ℝ) : ℂ) ^ (-w)
      = (((j + 1 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-w) * (c : ℂ) ^ (-w) := by
    rw [Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (by positivity) hc.le (-w)
  have h3 : (((j + 1 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-w) = (j + 1 : ℂ) ^ (-w) * (j + 1 : ℂ) ^ (-w) := by
    rw [show (((j + 1 : ℝ) ^ 2 : ℝ) : ℂ) = ((j + 1 : ℝ) : ℂ) * ((j + 1 : ℝ) : ℂ) by
      push_cast; ring]
    rw [Complex.mul_cpow_ofReal_nonneg hj.le hj.le (-w)]
    push_cast
    ring
  have h4 : ((x / c : ℝ) : ℂ) ^ w = (x : ℂ) ^ w * (c : ℂ) ^ (-w) := by
    have := cpow_div_pos_neg hx hc (-w)
    rw [neg_neg] at this
    exact this
  have h5 : (1 : ℂ) / (j + 1 : ℂ) ^ (((2 * σ₀ : ℝ) : ℂ) + 2 * w)
      = (j + 1 : ℂ) ^ (-((2 * σ₀ : ℝ) : ℂ)) * ((j + 1 : ℂ) ^ (-w) * (j + 1 : ℂ) ^ (-w)) := by
    rw [one_div, ← Complex.cpow_neg, show -(((2 * σ₀ : ℝ) : ℂ) + 2 * w)
      = -((2 * σ₀ : ℝ) : ℂ) + (-w + -w) by ring, Complex.cpow_add _ _ hjc,
      Complex.cpow_add _ _ hjc]
  rw [h1, h2, h3, h4, h5]
  ring

/-- Summing the Dirichlet series under the kernel. -/
theorem smoothDiagonalIntegrand_eq_tsum {σ₀ : ℝ} (c x : ℝ) {w : ℂ} (hw : 1 < 2 * σ₀ + 2 * w.re) :
    smoothDiagonalIntegrand σ₀ c x w = ∑' j : ℕ, smoothDiagonalTerm σ₀ c x j w := by
  unfold smoothDiagonalIntegrand smoothDiagonalTerm
  have hre : 1 < (((2 * σ₀ : ℝ) : ℂ) + 2 * w).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre, ← tsum_mul_right, ← tsum_mul_right]

/-! ## The line `Re w = 1`: integrability, summability, interchange -/

theorem smoothDiagonalTerm_one_line_eq {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (σ₀ : ℝ) (j : ℕ)
    (t : ℝ) :
    smoothDiagonalTerm σ₀ c x j (((1 : ℝ) : ℂ) + (t : ℂ) * I)
      = (j + 1 : ℂ) ^ (-((2 * σ₀ : ℝ) : ℂ)) * dualFrequencyKernel (((j + 1 : ℝ) ^ 2 * c) / x) t := by
  rw [smoothDiagonalTerm_eq hc hx]
  rfl

theorem norm_smoothDiagonalTerm_one_line_le {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (σ₀ : ℝ)
    (j : ℕ) (t : ℝ) :
    ‖smoothDiagonalTerm σ₀ c x j (((1 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ (1 / (j + 1 : ℝ) ^ (2 * σ₀ + 2)) * ((x / c) * Real.exp 1) * Real.exp (-(t ^ 2)) := by
  have hj : (0 : ℝ) < j + 1 := by positivity
  have hX : (0 : ℝ) < ((j + 1 : ℝ) ^ 2 * c) / x := by positivity
  rw [smoothDiagonalTerm_one_line_eq hc hx, norm_mul]
  have hcoef : ‖(j + 1 : ℂ) ^ (-((2 * σ₀ : ℝ) : ℂ))‖ = (j + 1 : ℝ) ^ (-(2 * σ₀)) := by
    rw [show (j + 1 : ℂ) = (((j : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hj]
    simp
  have hk := norm_dualFrequencyKernel_le hX t
  have hinv : (((j + 1 : ℝ) ^ 2 * c) / x)⁻¹ = (x / c) * (1 / (j + 1 : ℝ) ^ 2) := by
    field_simp
  calc ‖(j + 1 : ℂ) ^ (-((2 * σ₀ : ℝ) : ℂ))‖ * ‖dualFrequencyKernel (((j + 1 : ℝ) ^ 2 * c) / x) t‖
      ≤ (j + 1 : ℝ) ^ (-(2 * σ₀)) * (((((j + 1 : ℝ) ^ 2 * c) / x)⁻¹ * Real.exp 1)
          * Real.exp (-(t ^ 2))) := by
        rw [hcoef]
        exact mul_le_mul_of_nonneg_left hk (by positivity)
    _ = (1 / (j + 1 : ℝ) ^ (2 * σ₀ + 2)) * ((x / c) * Real.exp 1) * Real.exp (-(t ^ 2)) := by
        rw [hinv, Real.rpow_add hj, Real.rpow_neg hj.le, show ((j + 1 : ℝ)) ^ (2 : ℝ)
          = (j + 1 : ℝ) ^ 2 by norm_cast]
        field_simp

theorem integrable_smoothDiagonalTerm_one_line {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (σ₀ : ℝ)
    (j : ℕ) :
    Integrable (fun t : ℝ => smoothDiagonalTerm σ₀ c x j (((1 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  have hX : (0 : ℝ) < ((j + 1 : ℝ) ^ 2 * c) / x := by positivity
  have hcont : Continuous (fun t : ℝ => smoothDiagonalTerm σ₀ c x j (((1 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    have : (fun t : ℝ => smoothDiagonalTerm σ₀ c x j (((1 : ℝ) : ℂ) + (t : ℂ) * I))
        = fun t => (j + 1 : ℂ) ^ (-((2 * σ₀ : ℝ) : ℂ)) * dualFrequencyKernel (((j + 1 : ℝ) ^ 2 * c) / x) t :=
      funext fun t => smoothDiagonalTerm_one_line_eq hc hx σ₀ j t
    rw [this]
    exact continuous_const.mul (continuous_dualFrequencyKernel hX)
  refine Integrable.mono' (((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
    ((1 / (j + 1 : ℝ) ^ (2 * σ₀ + 2)) * ((x / c) * Real.exp 1)))) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have := norm_smoothDiagonalTerm_one_line_le hc hx σ₀ j t
  simpa [neg_mul, one_mul] using this

theorem summable_integral_norm_smoothDiagonalTerm_one_line {c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    {σ₀ : ℝ} (hσ : 0 ≤ σ₀) :
    Summable (fun j : ℕ => ∫ t : ℝ,
      ‖smoothDiagonalTerm σ₀ c x j (((1 : ℝ) : ℂ) + (t : ℂ) * I)‖) := by
  have hG : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have hmaj : Summable (fun j : ℕ => (1 / (j + 1 : ℝ) ^ (2 * σ₀ + 2))
      * (((x / c) * Real.exp 1) * ∫ t : ℝ, Real.exp (-(t ^ 2)))) :=
    (summable_smoothAFEZetaMajorant (by linarith)).mul_right _
  refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun t => norm_nonneg _)
    (fun j => ?_) hmaj
  calc ∫ t : ℝ, ‖smoothDiagonalTerm σ₀ c x j (((1 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ ∫ t : ℝ, (1 / (j + 1 : ℝ) ^ (2 * σ₀ + 2)) * ((x / c) * Real.exp 1) * Real.exp (-(t ^ 2)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
          (hG.const_mul _) (Filter.Eventually.of_forall fun t =>
            norm_smoothDiagonalTerm_one_line_le hc hx σ₀ j t)
    _ = (1 / (j + 1 : ℝ) ^ (2 * σ₀ + 2)) * (((x / c) * Real.exp 1) * ∫ t : ℝ, Real.exp (-(t ^ 2))) := by
        rw [← integral_const_mul, ← integral_const_mul]
        congr 1
        funext t
        ring

/-- **The smoothed diagonal is the line integral of its Mellin integrand.** -/
theorem smoothDiagonal_eq_integral {c x : ℝ} (hc : 0 < c) (hx : 0 < x) {σ₀ : ℝ} (hσ : 0 ≤ σ₀) :
    smoothDiagonal σ₀ c x
      = (1 / (2 * Real.pi)) • ∫ t : ℝ, smoothDiagonalIntegrand σ₀ c x (((1 : ℝ) : ℂ) + (t : ℂ) * I) := by
  have hint : ∀ t : ℝ, smoothDiagonalIntegrand σ₀ c x (((1 : ℝ) : ℂ) + (t : ℂ) * I)
      = ∑' j : ℕ, smoothDiagonalTerm σ₀ c x j (((1 : ℝ) : ℂ) + (t : ℂ) * I) := fun t =>
    smoothDiagonalIntegrand_eq_tsum c x (by simp; linarith)
  simp_rw [hint]
  rw [← integral_tsum_of_summable_integral_norm (fun j => integrable_smoothDiagonalTerm_one_line hc hx σ₀ j)
    (summable_integral_norm_smoothDiagonalTerm_one_line hc hx hσ)]
  unfold smoothDiagonal
  rw [← tsum_const_smul'' (1 / (2 * Real.pi))]
  refine tsum_congr fun j => ?_
  have hX : (0 : ℝ) < ((j + 1 : ℝ) ^ 2 * c) / x := by positivity
  rw [← smoothAFECutoffAt_eq_smoothAFECutoff hX one_pos, smoothAFECutoffAt_eq_integral]
  have hterm : (fun t : ℝ => smoothDiagonalTerm σ₀ c x j (((1 : ℝ) : ℂ) + (t : ℂ) * I))
      = fun t : ℝ => (j + 1 : ℂ) ^ (-((2 * σ₀ : ℝ) : ℂ))
        * smoothAFEMellinIntegrand (((j + 1 : ℝ) ^ 2 * c) / x) (((1 : ℝ) : ℂ) + (t : ℂ) * I) :=
    funext fun t => smoothDiagonalTerm_eq hc hx σ₀ j (((1 : ℝ) : ℂ) + (t : ℂ) * I)
  rw [hterm, integral_const_mul, Complex.real_smul, Complex.real_smul]
  ring

/-! ## The two-pole decomposition -/

/-- The half-width shift `δ₀ = ½ − σ₀`. -/
def diagonalShift (σ₀ : ℝ) : ℂ := ((1 / 2 - σ₀ : ℝ) : ℂ)

/-- The entire numerator `(x/c)^w e^{w²} ((2σ₀+2w−1)ζ(2σ₀+2w))/2`. -/
def smoothDiagonalNumerator (σ₀ c x : ℝ) (w : ℂ) : ℂ :=
  ((x / c : ℝ) : ℂ) ^ w * Complex.exp (w ^ 2) * regularizedRiemannZeta (((2 * σ₀ : ℝ) : ℂ) + 2 * w) / 2

/-- The entire remainder after removing both poles. -/
def smoothDiagonalRemainder (σ₀ c x : ℝ) : ℂ → ℂ :=
  dslope (dslope (smoothDiagonalNumerator σ₀ c x) 0) (diagonalShift σ₀)

/-- The residue at the zeta pole `δ₀`: `(x/c)^{δ₀} e^{δ₀²}/(2δ₀)`. -/
def smoothDiagonalShiftedResidue (σ₀ c x : ℝ) : ℂ :=
  ((x / c : ℝ) : ℂ) ^ diagonalShift σ₀ * Complex.exp (diagonalShift σ₀ ^ 2) / (2 * diagonalShift σ₀)

theorem differentiable_smoothDiagonalNumerator {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (σ₀ : ℝ) :
    Differentiable ℂ (smoothDiagonalNumerator σ₀ c x) := by
  haveI : NeZero ((x / c : ℝ) : ℂ) := ⟨Complex.ofReal_ne_zero.mpr (div_pos hx hc).ne'⟩
  unfold smoothDiagonalNumerator
  exact ((((differentiable_const_cpow_of_neZero ((x / c : ℝ) : ℂ)).comp differentiable_id).mul
    (differentiable_exp.comp (differentiable_pow 2))).mul
      (differentiable_regularizedRiemannZeta.comp (by fun_prop))).div_const 2

theorem differentiable_smoothDiagonalRemainder {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (σ₀ : ℝ) :
    Differentiable ℂ (smoothDiagonalRemainder σ₀ c x) := by
  have hN := differentiable_smoothDiagonalNumerator hc hx σ₀
  have hQ : Differentiable ℂ (dslope (smoothDiagonalNumerator σ₀ c x) 0) := by
    apply differentiableOn_univ.1
    rw [differentiableOn_dslope Filter.univ_mem]
    exact hN.differentiableOn
  apply differentiableOn_univ.1
  rw [smoothDiagonalRemainder, differentiableOn_dslope Filter.univ_mem]
  exact hQ.differentiableOn

theorem smoothDiagonalNumerator_zero {σ₀ : ℝ} (hσ : σ₀ ≠ 1 / 2) (c x : ℝ) :
    smoothDiagonalNumerator σ₀ c x 0 = -(diagonalShift σ₀) * riemannZeta ((2 * σ₀ : ℝ) : ℂ) := by
  have hne : (((2 * σ₀ : ℝ) : ℂ) + 2 * 0) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hσ (by linarith)
  unfold smoothDiagonalNumerator diagonalShift
  rw [regularizedRiemannZeta_of_ne_one hne]
  simp
  ring

theorem smoothDiagonalNumerator_shift (σ₀ c x : ℝ) :
    smoothDiagonalNumerator σ₀ c x (diagonalShift σ₀)
      = ((x / c : ℝ) : ℂ) ^ diagonalShift σ₀ * Complex.exp (diagonalShift σ₀ ^ 2) / 2 := by
  unfold smoothDiagonalNumerator
  have h1 : (((2 * σ₀ : ℝ) : ℂ) + 2 * diagonalShift σ₀) = 1 := by
    unfold diagonalShift
    push_cast
    ring
  rw [h1, regularizedRiemannZeta_one, mul_one]

private theorem two_pole_quotient_decomposition'
    {Nw N0 Nρ w ρ : ℂ} (hw : w ≠ 0) (hρ : ρ ≠ 0) (hwρ : w - ρ ≠ 0) :
    Nw / (w * (w - ρ)) =
      (-N0 / ρ) * w⁻¹ + (Nρ / ρ) * (w - ρ)⁻¹ +
        (((Nw - N0) / w) - ((Nρ - N0) / ρ)) / (w - ρ) := by
  rw [inv_eq_one_div, inv_eq_one_div]
  field_simp [hw, hρ, hwρ]
  ring

/-- **Two-pole decomposition of the diagonal integrand**: residue `ζ(2σ₀)` at `0`, residue
`(x/c)^{δ₀}e^{δ₀²}/(2δ₀)` at `δ₀`, entire remainder. -/
theorem smoothDiagonalIntegrand_eq_two_poles_add_remainder {σ₀ : ℝ} (hσ : σ₀ ≠ 1 / 2)
    (c x : ℝ) {w : ℂ} (hw0 : w ≠ 0) (hwδ : w ≠ diagonalShift σ₀) :
    smoothDiagonalIntegrand σ₀ c x w
      = riemannZeta ((2 * σ₀ : ℝ) : ℂ) * w⁻¹
        + smoothDiagonalShiftedResidue σ₀ c x * (w - diagonalShift σ₀)⁻¹
        + smoothDiagonalRemainder σ₀ c x w := by
  have hδ0 : diagonalShift σ₀ ≠ 0 := by
    unfold diagonalShift
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hσ (by linarith)
  have hwδ0 : w - diagonalShift σ₀ ≠ 0 := sub_ne_zero.mpr hwδ
  have hpole : (((2 * σ₀ : ℝ) : ℂ) + 2 * w) ≠ 1 := by
    intro h
    apply hwδ
    unfold diagonalShift
    push_cast at h ⊢
    linear_combination h / 2
  have hquot : smoothDiagonalIntegrand σ₀ c x w
      = smoothDiagonalNumerator σ₀ c x w / (w * (w - diagonalShift σ₀)) := by
    rw [smoothDiagonalIntegrand, smoothAFEGaussianKernel, smoothDiagonalNumerator,
      regularizedRiemannZeta_of_ne_one hpole]
    have hcoord : (((2 * σ₀ : ℝ) : ℂ) + 2 * w - 1) = 2 * (w - diagonalShift σ₀) := by
      unfold diagonalShift
      push_cast
      ring
    rw [hcoord]
    field_simp [hw0, hwδ0]
  have hres0 : -smoothDiagonalNumerator σ₀ c x 0 / diagonalShift σ₀
      = riemannZeta ((2 * σ₀ : ℝ) : ℂ) := by
    rw [smoothDiagonalNumerator_zero hσ]
    field_simp [hδ0]
  have hresδ : smoothDiagonalNumerator σ₀ c x (diagonalShift σ₀) / diagonalShift σ₀
      = smoothDiagonalShiftedResidue σ₀ c x := by
    rw [smoothDiagonalNumerator_shift, smoothDiagonalShiftedResidue]
    field_simp [hδ0]
  have hrem : smoothDiagonalRemainder σ₀ c x w
      = (((smoothDiagonalNumerator σ₀ c x w - smoothDiagonalNumerator σ₀ c x 0) / w)
          - ((smoothDiagonalNumerator σ₀ c x (diagonalShift σ₀)
              - smoothDiagonalNumerator σ₀ c x 0) / diagonalShift σ₀))
          / (w - diagonalShift σ₀) := by
    rw [smoothDiagonalRemainder, dslope_of_ne _ hwδ, slope_def_field, dslope_of_ne _ hw0,
      slope_def_field, dslope_of_ne _ hδ0, slope_def_field]
    simp only [sub_zero]
  rw [hquot, two_pole_quotient_decomposition' (N0 := smoothDiagonalNumerator σ₀ c x 0)
    (Nρ := smoothDiagonalNumerator σ₀ c x (diagonalShift σ₀)) hw0 hδ0 hwδ0, hres0, hresδ, ← hrem]

end RHTower

end
