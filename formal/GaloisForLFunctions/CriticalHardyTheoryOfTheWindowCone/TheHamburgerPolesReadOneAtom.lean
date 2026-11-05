import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheGaussianTestsReadHamburgerKernels
import Mathlib.Analysis.Complex.Hadamard

/-!
# Hamburger's poles read one atom

Let `δ` be a real sequence with `|δ(n)| ≤ V √n`, and read it against the kernels of the Gaussian tests:

  `S(t) = Σ_{n,k≥1} δ(n) (ratKer(kn, t) + expKer(kn, t))`,   `Re t > 1`.

The exponential kernel of an integer `x` is `i`-periodic up to a factor linear in `t`, so the second
difference `S(t + i) − 2S(t) + S(t − i)` sees only the rational kernels. Multiplied by `sinh³(πt)` it is an
entire function `T`, and `T(iL)` is exactly the discrete Laplacian of `N ↦ N D(N)` at `L`, where
`D(N) = Σ_{d ∣ N} δ(d)` (`poleT_I_mul`).

If `S` is small on the real ray, the three lines theorem carries the smallness first to `t ± i`, and then
across the imaginary axis to the poles (`norm_le_of_sector`). So smallness on a ray bounds every `δ(n)`
(`exists_abs_le_of_readS_small`): a quantitative form of Hamburger's uniqueness theorem. Its constants depend
on `V` and on the ray bound alone, and the exponent is explicit.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone

/-! ### The three lines theorem on a sector -/

/-- The point `a + r e^{iα}`. -/
def rayPt (a r α : ℝ) : ℂ := a + r * cexp ((α : ℂ) * I)

theorem rayPt_zero (a r : ℝ) : rayPt a r 0 = ((a + r : ℝ) : ℂ) := by
  simp [rayPt]

theorem rayPt_re (a r α : ℝ) : (rayPt a r α).re = a + r * Real.cos α := by
  simp [rayPt, Complex.exp_ofReal_mul_I_re]

theorem norm_rayPt_le {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (α : ℝ) : ‖rayPt a r α‖ ≤ a + r := by
  unfold rayPt
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg ha, Real.norm_of_nonneg hr]

theorem cos_half_pos {φ : ℝ} (hφ : 0 < φ) (hφ' : φ < π) : 0 < Real.cos (φ / 2) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

/-- `cos(α − φ/2) ≥ cos(φ/2)` for `α ∈ [0, φ]`. -/
theorem cos_half_le {φ α : ℝ} (hφ' : φ < π) (hα : α ∈ Icc 0 φ) :
    Real.cos (φ / 2) ≤ Real.cos (α - φ / 2) := by
  rw [← Real.cos_abs (α - φ / 2)]
  refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [hα.1, hα.2]) ?_
  rw [abs_le]
  constructor <;> linarith [hα.1, hα.2]

/-- **The three lines theorem on a sector.** If `F` grows at most like `e^{K r}` on the sector
`0 ≤ arg(t − a) ≤ φ`, `φ < π`, and is at most `M₀ e^{Kr}`, `M₁ e^{Kr}` on the two rays, then
`‖F(a + r e^{iα})‖ ≤ M₀^{1−α/φ} M₁^{α/φ} e^{K r / cos(φ/2)}`. -/
theorem norm_le_of_sector {F : ℂ → ℂ} {a φ K M₀ M₁ A : ℝ} (hφ : 0 < φ) (hφ' : φ < π) (hK : 0 ≤ K)
    (hF : ∀ r α, 0 < r → α ∈ Icc 0 φ → DifferentiableAt ℂ F (rayPt a r α))
    (hA : ∀ r α, 0 < r → α ∈ Icc 0 φ → ‖F (rayPt a r α)‖ ≤ A * Real.exp (K * r))
    (h₀ : ∀ r, 0 < r → ‖F (rayPt a r 0)‖ ≤ M₀ * Real.exp (K * r))
    (h₁ : ∀ r, 0 < r → ‖F (rayPt a r φ)‖ ≤ M₁ * Real.exp (K * r))
    {r α : ℝ} (hr : 0 < r) (hα : α ∈ Icc 0 φ) :
    ‖F (rayPt a r α)‖ ≤
      M₀ ^ (1 - α / φ) * M₁ ^ (α / φ) * Real.exp (K / Real.cos (φ / 2) * r) := by
  have hcos := cos_half_pos hφ hφ'
  obtain ⟨K₂, hK₂⟩ : ∃ K₂, K₂ = K / Real.cos (φ / 2) := ⟨_, rfl⟩
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  have hK₂c : K₂ * Real.cos (φ / 2) = K := by rw [hK₂]; field_simp
  rw [← hK₂]
  -- the conformal map from the strip to the sector
  set w : ℂ → ℂ := fun ζ => cexp ((φ : ℂ) * ζ * I) with hw
  set G : ℂ → ℂ := fun ζ =>
    F (a + w ζ) * cexp (-((K₂ : ℂ) * (w ζ * cexp (-(((φ / 2 : ℝ) : ℂ) * I))))) with hG
  have hwpt : ∀ ζ : ℂ, (a : ℂ) + w ζ = rayPt a (Real.exp (-(φ * ζ.im))) (φ * ζ.re) := by
    intro ζ
    simp only [hw, rayPt]
    congr 1
    have e : (φ : ℂ) * ζ * I = ((-(φ * ζ.im) : ℝ) : ℂ) + ((φ * ζ.re : ℝ) : ℂ) * I := by
      conv_lhs => rw [← Complex.re_add_im ζ]
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [e, Complex.exp_add, Complex.ofReal_exp]
  have hwpt' : ∀ ζ : ℂ, w ζ = ((Real.exp (-(φ * ζ.im)) : ℝ) : ℂ) * cexp (((φ * ζ.re : ℝ) : ℂ) * I) := by
    intro ζ
    have := hwpt ζ
    simp only [rayPt] at this
    exact add_left_cancel this
  -- the size of the exponential factor
  have hE : ∀ ζ : ℂ, ‖cexp (-((K₂ : ℂ) * (w ζ * cexp (-(((φ / 2 : ℝ) : ℂ) * I)))))‖ =
      Real.exp (-(K₂ * (Real.exp (-(φ * ζ.im)) * Real.cos (φ * ζ.re - φ / 2)))) := by
    intro ζ
    rw [Complex.norm_exp, hwpt']
    congr 1
    have e : ((Real.exp (-(φ * ζ.im)) : ℝ) : ℂ) * cexp (((φ * ζ.re : ℝ) : ℂ) * I) *
        cexp (-(((φ / 2 : ℝ) : ℂ) * I)) =
        ((Real.exp (-(φ * ζ.im)) : ℝ) : ℂ) * cexp (((φ * ζ.re - φ / 2 : ℝ) : ℂ) * I) := by
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [e, Complex.neg_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
  have hmem : ∀ ζ : ℂ, ζ.re ∈ Icc (0 : ℝ) 1 → φ * ζ.re ∈ Icc 0 φ := fun ζ h =>
    ⟨mul_nonneg hφ.le h.1, by nlinarith [h.2]⟩
  -- the factor beats the growth
  have hEle : ∀ ζ : ℂ, ζ.re ∈ Icc (0 : ℝ) 1 →
      Real.exp (K * Real.exp (-(φ * ζ.im))) *
        ‖cexp (-((K₂ : ℂ) * (w ζ * cexp (-(((φ / 2 : ℝ) : ℂ) * I)))))‖ ≤ 1 := by
    intro ζ h
    rw [hE, ← Real.exp_add]
    refine Real.exp_le_one_iff.mpr ?_
    have hr' := Real.exp_pos (-(φ * ζ.im))
    have hc := cos_half_le hφ' (hmem ζ h)
    have : K₂ * Real.cos (φ / 2) * Real.exp (-(φ * ζ.im)) ≤
        K₂ * (Real.exp (-(φ * ζ.im)) * Real.cos (φ * ζ.re - φ / 2)) := by
      have := mul_le_mul_of_nonneg_left hc (mul_nonneg hK₂0 hr'.le)
      nlinarith
    rw [hK₂c] at this
    linarith
  have hbound : ∀ ζ : ℂ, ∀ B : ℝ, ζ.re ∈ Icc (0 : ℝ) 1 →
      ‖F (a + w ζ)‖ ≤ B * Real.exp (K * Real.exp (-(φ * ζ.im))) → 0 ≤ B → ‖G ζ‖ ≤ B := by
    intro ζ B h h1 hB
    simp only [hG]
    rw [norm_mul]
    have hn := norm_nonneg (cexp (-((K₂ : ℂ) * (w ζ * cexp (-(((φ / 2 : ℝ) : ℂ) * I))))))
    calc ‖F (a + w ζ)‖ * ‖cexp (-((K₂ : ℂ) * (w ζ * cexp (-(((φ / 2 : ℝ) : ℂ) * I)))))‖
        ≤ (B * Real.exp (K * Real.exp (-(φ * ζ.im)))) *
            ‖cexp (-((K₂ : ℂ) * (w ζ * cexp (-(((φ / 2 : ℝ) : ℂ) * I)))))‖ :=
          mul_le_mul_of_nonneg_right h1 hn
      _ = B * (Real.exp (K * Real.exp (-(φ * ζ.im))) *
            ‖cexp (-((K₂ : ℂ) * (w ζ * cexp (-(((φ / 2 : ℝ) : ℂ) * I)))))‖) := by ring
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left (hEle ζ h) hB
      _ = B := mul_one B
  -- the bounds on the strip
  have hnonneg : ∀ {B : ℝ}, (∀ r, 0 < r → ‖F (rayPt a r 0)‖ ≤ B * Real.exp (K * r)) → 0 ≤ B := by
    intro B hB
    have := (norm_nonneg _).trans (hB 1 one_pos)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have hM₀ : 0 ≤ M₀ := hnonneg h₀
  have hA0 : 0 ≤ A := by
    have := (norm_nonneg _).trans (hA 1 0 one_pos ⟨le_rfl, hφ.le⟩)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have hM₁ : 0 ≤ M₁ := by
    have := (norm_nonneg _).trans (h₁ 1 one_pos)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have hGA : ∀ ζ : ℂ, ζ.re ∈ Icc (0 : ℝ) 1 → ‖G ζ‖ ≤ A := fun ζ h => hbound ζ A h
    (by rw [hwpt]; exact hA _ _ (Real.exp_pos _) (hmem ζ h)) hA0
  have hG0 : ∀ ζ ∈ re ⁻¹' {(0 : ℝ)}, ‖G ζ‖ ≤ M₀ := fun ζ hζ => by
    have h0 : ζ.re = 0 := hζ
    refine hbound ζ M₀ (by rw [h0]; exact ⟨le_rfl, zero_le_one⟩) ?_ hM₀
    rw [hwpt, h0, mul_zero]
    exact h₀ _ (Real.exp_pos _)
  have hG1 : ∀ ζ ∈ re ⁻¹' {(1 : ℝ)}, ‖G ζ‖ ≤ M₁ := fun ζ hζ => by
    have h0 : ζ.re = 1 := hζ
    refine hbound ζ M₁ (by rw [h0]; exact ⟨zero_le_one, le_rfl⟩) ?_ hM₁
    rw [hwpt, h0, mul_one]
    exact h₁ _ (Real.exp_pos _)
  -- differentiability
  have hdiff : ∀ ζ : ℂ, ζ.re ∈ Icc (0 : ℝ) 1 → DifferentiableAt ℂ G ζ := by
    intro ζ h
    have hw' : DifferentiableAt ℂ w ζ := by simp only [hw]; fun_prop
    have h1 : DifferentiableAt ℂ (fun ζ => F (a + w ζ)) ζ := by
      have hFa : DifferentiableAt ℂ F ((a : ℂ) + w ζ) := by
        rw [hwpt]
        exact hF _ _ (Real.exp_pos _) (hmem ζ h)
      exact hFa.comp ζ ((differentiableAt_const _).add hw')
    exact h1.mul (DifferentiableAt.cexp (by fun_prop))
  have hDC : DiffContOnCl ℂ G (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    have hcl : closure (Complex.HadamardThreeLines.verticalStrip 0 1) ⊆ re ⁻¹' Icc (0 : ℝ) 1 :=
      closure_minimal (preimage_mono Ioo_subset_Icc_self)
        (isClosed_Icc.preimage Complex.continuous_re)
    refine ⟨fun ζ hζ => (hdiff ζ (Ioo_subset_Icc_self hζ)).differentiableWithinAt,
      fun ζ hζ => (hdiff ζ (hcl hζ)).continuousAt.continuousWithinAt⟩
  have hbdd : BddAbove ((norm ∘ G) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨A, ?_⟩
    rintro _ ⟨ζ, hζ, rfl⟩
    exact hGA ζ hζ
  -- the point
  have hαφ : α / φ ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hα.1 hφ.le, (div_le_one hφ).mpr hα.2⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, ζ = ((α / φ : ℝ) : ℂ) + ((-(Real.log r / φ) : ℝ) : ℂ) * I := ⟨_, rfl⟩
  have hζre : ζ.re = α / φ := by rw [hζ]; simp
  have hζim : ζ.im = -(Real.log r / φ) := by rw [hζ]; simp
  have hH := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := G) (z := ζ) (a := M₀) (b := M₁) (l := 0) (u := 1) zero_lt_one
    (by simpa [Complex.HadamardThreeLines.verticalClosedStrip, hζre] using hαφ) hDC hbdd hG0 hG1
  simp only [sub_zero, div_one, hζre] at hH
  have hrpt : (a : ℂ) + w ζ = rayPt a r α := by
    rw [hwpt, hζre, hζim]
    have e1 : φ * (α / φ) = α := by field_simp
    have e2 : -(φ * -(Real.log r / φ)) = Real.log r := by field_simp
    rw [e1, e2, Real.exp_log hr]
  simp only [hG] at hH
  rw [hrpt, norm_mul, hE, hζim, hζre] at hH
  have e2 : Real.exp (-(φ * -(Real.log r / φ))) = r := by
    rw [show -(φ * -(Real.log r / φ)) = Real.log r by field_simp, Real.exp_log hr]
  have e1 : φ * (α / φ) = α := by field_simp
  rw [e2, e1] at hH
  have hc1 := Real.cos_le_one (α - φ / 2)
  have hexp : 1 ≤ Real.exp (-(K₂ * (r * Real.cos (α - φ / 2)))) * Real.exp (K₂ * r) := by
    rw [← Real.exp_add]
    refine Real.one_le_exp ?_
    have : K₂ * (r * Real.cos (α - φ / 2)) ≤ K₂ * (r * 1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc1 hr.le) hK₂0
    linarith
  have hEp := Real.exp_pos (K₂ * r)
  calc ‖F (rayPt a r α)‖ ≤ ‖F (rayPt a r α)‖ *
        (Real.exp (-(K₂ * (r * Real.cos (α - φ / 2)))) * Real.exp (K₂ * r)) :=
        le_mul_of_one_le_right (norm_nonneg _) hexp
    _ = ‖F (rayPt a r α)‖ * Real.exp (-(K₂ * (r * Real.cos (α - φ / 2)))) * Real.exp (K₂ * r) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hH hEp.le

/-! ### The entire quotient `sinh(πw)/w` -/

/-- The entire function `sinh(πw)/w`, with value `π` at `0`. -/
def sinhQuot : ℂ → ℂ := dslope (fun w => Complex.sinh ((π : ℂ) * w)) 0

theorem differentiable_sinhQuot : Differentiable ℂ sinhQuot := by
  have h : DifferentiableOn ℂ (dslope (fun w => Complex.sinh ((π : ℂ) * w)) 0) univ :=
    (Complex.differentiableOn_dslope univ_mem).mpr (by fun_prop)
  exact differentiableOn_univ.mp h

theorem mul_sinhQuot (w : ℂ) : w * sinhQuot w = Complex.sinh ((π : ℂ) * w) := by
  have := sub_smul_dslope (fun w => Complex.sinh ((π : ℂ) * w)) 0 w
  simpa [sinhQuot] using this

theorem sinhQuot_zero : sinhQuot 0 = π := by
  unfold sinhQuot
  rw [dslope_same]
  have h : HasDerivAt (fun w : ℂ => Complex.sinh ((π : ℂ) * w))
      (Complex.cosh ((π : ℂ) * 0) * ((π : ℂ) * 1)) 0 :=
    ((hasDerivAt_id (0 : ℂ)).const_mul (π : ℂ)).csinh
  rw [h.deriv]
  simp

theorem sinhQuot_I_mul_int {k : ℤ} (hk : k ≠ 0) : sinhQuot (I * k) = 0 := by
  have h := mul_sinhQuot (I * k)
  have hs : Complex.sinh ((π : ℂ) * (I * k)) = 0 := by
    rw [show (π : ℂ) * (I * k) = ((k : ℂ) * π) * I by ring, Complex.sinh_mul_I,
      Complex.sin_int_mul_pi, zero_mul]
  rw [hs] at h
  exact (mul_eq_zero.mp h).resolve_left (by simp [hk])

theorem norm_sinh_le (z : ℂ) : ‖Complex.sinh z‖ ≤ Real.exp |z.re| := by
  rw [Complex.sinh]
  rw [norm_div, Complex.norm_ofNat, div_le_iff₀ (by norm_num)]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re]
  have h1 : Real.exp z.re ≤ Real.exp |z.re| := Real.exp_le_exp.mpr (le_abs_self _)
  have h2 : Real.exp (-z.re) ≤ Real.exp |z.re| := Real.exp_le_exp.mpr (neg_le_abs _)
  linarith

/-- `‖sinh(πw)/w‖ (1 + ‖w‖) ≤ C₀ e^{π|Re w|}`. -/
theorem exists_norm_sinhQuot_le :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ w, ‖sinhQuot w‖ * (1 + ‖w‖) ≤ C₀ * Real.exp (π * |w.re|) := by
  obtain ⟨C₁, hC₁⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    differentiable_sinhQuot.continuous.continuousOn
  have hC₁0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0 (by simp))
  refine ⟨2 * C₁ + 2, by positivity, fun w => ?_⟩
  have hE : 1 ≤ Real.exp (π * |w.re|) := Real.one_le_exp (by positivity)
  rcases le_or_gt ‖w‖ 1 with hw | hw
  · have h := hC₁ w (by simpa using hw)
    have hn := norm_nonneg w
    have h1 : ‖sinhQuot w‖ * (1 + ‖w‖) ≤ C₁ * 2 :=
      mul_le_mul h (by linarith) (by linarith) hC₁0
    nlinarith
  · have hw0 : 0 < ‖w‖ := by linarith
    have h := mul_sinhQuot w
    have h1 : ‖w‖ * ‖sinhQuot w‖ ≤ Real.exp (π * |w.re|) := by
      rw [← norm_mul, h]
      refine (norm_sinh_le _).trans (le_of_eq ?_)
      congr 1
      rw [Complex.re_ofReal_mul, abs_mul, abs_of_pos Real.pi_pos]
    have hq := norm_nonneg (sinhQuot w)
    have hC2 : 0 ≤ 2 * C₁ * Real.exp (π * |w.re|) := by positivity
    nlinarith

/-- The translate `(−1)^M sinh(π(t − iM))/(t − iM)`, which is `sinh(πt)/(t − iM)`. -/
def sincAt (M : ℤ) (t : ℂ) : ℂ := (-1 : ℂ) ^ M * sinhQuot (t - I * M)

theorem differentiable_sincAt (M : ℤ) : Differentiable ℂ (sincAt M) := by
  unfold sincAt
  exact (differentiable_sinhQuot.comp (differentiable_id.sub_const _)).const_mul _

theorem neg_one_zpow_mul_self (M : ℤ) : (-1 : ℂ) ^ M * (-1 : ℂ) ^ M = 1 := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  exact Even.neg_one_zpow ⟨M, rfl⟩

theorem cos_int_mul_pi_eq (M : ℤ) : Complex.cos ((M : ℂ) * π) = (-1 : ℂ) ^ M := by
  have h := Real.cos_int_mul_pi M
  rw [show (M : ℂ) * (π : ℂ) = (((M : ℝ) * π : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cos, h]
  push_cast
  rfl

theorem sinh_eq_mul_sincAt (M : ℤ) (t : ℂ) :
    Complex.sinh ((π : ℂ) * t) = (t - I * M) * sincAt M t := by
  have h := mul_sinhQuot (t - I * M)
  have e : Complex.sinh ((π : ℂ) * (t - I * M)) = Complex.sinh ((π : ℂ) * t) * (-1 : ℂ) ^ M := by
    rw [show (π : ℂ) * (t - I * M) = (π : ℂ) * t - ((M : ℂ) * π) * I by ring, Complex.sinh_sub,
      Complex.cosh_mul_I, Complex.sinh_mul_I, cos_int_mul_pi_eq, Complex.sin_int_mul_pi]
    ring
  rw [e] at h
  unfold sincAt
  have h2 := neg_one_zpow_mul_self M
  calc Complex.sinh ((π : ℂ) * t)
      = Complex.sinh ((π : ℂ) * t) * ((-1 : ℂ) ^ M * (-1 : ℂ) ^ M) := by rw [h2, mul_one]
    _ = (Complex.sinh ((π : ℂ) * t) * (-1 : ℂ) ^ M) * (-1 : ℂ) ^ M := by ring
    _ = ((t - I * M) * sinhQuot (t - I * M)) * (-1 : ℂ) ^ M := by rw [h]
    _ = _ := by ring

theorem norm_sincAt_le {C₀ : ℝ}
    (hb : ∀ w, ‖sinhQuot w‖ * (1 + ‖w‖) ≤ C₀ * Real.exp (π * |w.re|)) (M : ℤ) (t : ℂ) :
    ‖sincAt M t‖ * (1 + |(M : ℝ)|) ≤ C₀ * Real.exp (π * |t.re|) * (1 + ‖t‖) := by
  have hn : ‖sincAt M t‖ = ‖sinhQuot (t - I * M)‖ := by
    unfold sincAt
    rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
  rw [hn]
  have hre : (t - I * M).re = t.re := by simp
  have h1 := hb (t - I * M)
  rw [hre] at h1
  have hM : |(M : ℝ)| ≤ ‖t‖ + ‖t - I * M‖ := by
    have e : ‖I * (M : ℂ)‖ = |(M : ℝ)| := by
      rw [norm_mul, Complex.norm_I, one_mul]
      simp
    rw [← e]
    have := norm_sub_le t (t - I * M)
    simpa using this
  have hw := norm_nonneg (t - I * M)
  have ht := norm_nonneg t
  have hq := norm_nonneg (sinhQuot (t - I * M))
  have h2 : 1 + |(M : ℝ)| ≤ (1 + ‖t - I * M‖) * (1 + ‖t‖) := by nlinarith
  calc ‖sinhQuot (t - I * M)‖ * (1 + |(M : ℝ)|)
      ≤ ‖sinhQuot (t - I * M)‖ * ((1 + ‖t - I * M‖) * (1 + ‖t‖)) :=
        mul_le_mul_of_nonneg_left h2 hq
    _ = (‖sinhQuot (t - I * M)‖ * (1 + ‖t - I * M‖)) * (1 + ‖t‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)

/-! ### The complex kernels -/

/-- The rational kernel at complex `t`. -/
def ratKerC (x : ℝ) (t : ℂ) : ℂ :=
  8 * (x : ℂ) ^ 4 / ((π : ℂ) * ((x : ℂ) ^ 2 + t ^ 2) ^ 3) -
    6 * (x : ℂ) ^ 2 / ((π : ℂ) * ((x : ℂ) ^ 2 + t ^ 2) ^ 2)

/-- The exponential kernel at complex `t`. -/
def expKerC (x : ℝ) (t : ℂ) : ℂ :=
  (x : ℂ) * (4 * (π : ℂ) ^ 2 * x * t - 4 * π) * cexp (-(2 * π * x * t))

/-- The kernel read by the Gaussian test `Y_t`. -/
def kerC (x : ℝ) (t : ℂ) : ℂ := ratKerC x t + expKerC x t

theorem kerC_ofReal (x t : ℝ) : kerC x t = ((ratKer x t + expKer x t : ℝ) : ℂ) := by
  unfold kerC ratKerC expKerC ratKer expKer
  push_cast
  ring_nf

theorem sub_I_mul_ne_zero {t : ℂ} (ht : 0 < t.re) (y : ℂ) (hy : y.im = 0) : t - I * y ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [hy] at this
  linarith

theorem add_I_mul_ne_zero {t : ℂ} (ht : 0 < t.re) (y : ℂ) (hy : y.im = 0) : t + I * y ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [hy] at this
  linarith

/-- The partial fractions of the rational kernel, whose poles sit at `t = ±ix`. -/
theorem ratKerC_eq {x : ℝ} {t : ℂ} (h1 : t - I * x ≠ 0) (h2 : t + I * x ≠ 0) :
    ratKerC x t = (I * x / π) * (1 / (t - I * x) ^ 3 - 1 / (t + I * x) ^ 3) := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = I * x := ⟨_, rfl⟩
  rw [← hz] at h1 h2 ⊢
  have hx2 : (x : ℂ) ^ 2 = -z ^ 2 := by rw [hz, mul_pow, I_sq]; ring
  have hx4 : (x : ℂ) ^ 4 = z ^ 4 := by
    rw [show (x : ℂ) ^ 4 = ((x : ℂ) ^ 2) ^ 2 by ring, hx2]
    ring
  have hS : (x : ℂ) ^ 2 + t ^ 2 = (t - z) * (t + z) := by rw [hx2]; ring
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold ratKerC
  rw [hS, hx4, hx2]
  field_simp
  ring

/-- `x² + t² ≠ 0` in the right half plane. -/
theorem sq_add_sq_ne_zero (x : ℝ) {t : ℂ} (ht : 0 < t.re) : (x : ℂ) ^ 2 + t ^ 2 ≠ 0 := by
  have hS : (x : ℂ) ^ 2 + t ^ 2 = (t - I * x) * (t + I * x) := by
    have : (I * (x : ℂ)) ^ 2 = -(x : ℂ) ^ 2 := by rw [mul_pow, I_sq]; ring
    linear_combination this
  rw [hS]
  exact mul_ne_zero (sub_I_mul_ne_zero ht _ (by simp)) (add_I_mul_ne_zero ht _ (by simp))

theorem differentiableAt_kerC (x : ℝ) {t : ℂ} (ht : 0 < t.re) : DifferentiableAt ℂ (kerC x) t := by
  have hS := sq_add_sq_ne_zero x ht
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold kerC ratKerC expKerC
  refine DifferentiableAt.add (DifferentiableAt.sub ?_ ?_) (by fun_prop)
  · exact (differentiableAt_const _).div (by fun_prop) (mul_ne_zero hpi (pow_ne_zero 3 hS))
  · exact (differentiableAt_const _).div (by fun_prop) (mul_ne_zero hpi (pow_ne_zero 2 hS))

/-- `1 + |y| ≤ 2 (1 + ‖t‖) ‖t − iy‖` when `Re t ≥ 1`. -/
theorem one_add_abs_le {t : ℂ} (ht : 1 ≤ t.re) (y : ℝ) :
    1 + |y| ≤ 2 * (1 + ‖t‖) * ‖t - I * y‖ := by
  have hd : 1 ≤ ‖t - I * y‖ := by
    have h := Complex.abs_re_le_norm (t - I * y)
    have e : (t - I * y).re = t.re := by simp
    rw [e] at h
    exact ht.trans ((le_abs_self _).trans h)
  have hy : |y| ≤ ‖t‖ + ‖t - I * y‖ := by
    have e : ‖I * (y : ℂ)‖ = |y| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [← e]
    have := norm_sub_le t (t - I * y)
    simpa using this
  have ht0 := norm_nonneg t
  nlinarith

theorem norm_one_div_cube_le {t : ℂ} (ht : 1 ≤ t.re) (y : ℝ) :
    ‖1 / (t - I * y) ^ 3‖ * (1 + |y|) ^ 3 ≤ 8 * (1 + ‖t‖) ^ 3 := by
  have hd : 0 < ‖t - I * y‖ := norm_pos_iff.mpr (sub_I_mul_ne_zero (by linarith) _ (by simp))
  have h := one_add_abs_le ht y
  have h3 := pow_le_pow_left₀ (by positivity) h 3
  rw [norm_div, norm_one, norm_pow, one_div, inv_mul_le_iff₀ (by positivity)]
  calc (1 + |y|) ^ 3 ≤ (2 * (1 + ‖t‖) * ‖t - I * y‖) ^ 3 := h3
    _ = _ := by ring

/-- On `Re t ≥ 1` the rational kernel is `O((1 + ‖t‖)³/x²)`. -/
theorem norm_ratKerC_le {x : ℝ} (hx : 1 ≤ x) {t : ℂ} (ht : 1 ≤ t.re) :
    ‖ratKerC x t‖ ≤ 6 * (1 + ‖t‖) ^ 3 / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 < t.re := by linarith
  have h1 := sub_I_mul_ne_zero ht0 (x : ℂ) (by simp)
  have h2 := add_I_mul_ne_zero ht0 (x : ℂ) (by simp)
  rw [ratKerC_eq h1 h2]
  have ha := norm_one_div_cube_le ht x
  have hb := norm_one_div_cube_le ht (-x)
  have e : t - I * ((-x : ℝ) : ℂ) = t + I * x := by push_cast; ring
  rw [e, abs_neg] at hb
  rw [abs_of_pos hx0] at ha hb
  have hpow : 0 < (1 + x) ^ 3 := by positivity
  have ha' : ‖1 / (t - I * x) ^ 3‖ ≤ 8 * (1 + ‖t‖) ^ 3 / (1 + x) ^ 3 := by
    rwa [le_div_iff₀ hpow]
  have hb' : ‖1 / (t + I * x) ^ 3‖ ≤ 8 * (1 + ‖t‖) ^ 3 / (1 + x) ^ 3 := by
    rwa [le_div_iff₀ hpow]
  have hI : ‖I * (x : ℂ) / (π : ℂ)‖ = x / π := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hx0.le, Real.norm_of_nonneg Real.pi_pos.le]
  rw [norm_mul, hI]
  have hsub := norm_sub_le (1 / (t - I * x) ^ 3) (1 / (t + I * x) ^ 3)
  have hsum : ‖1 / (t - I * x) ^ 3 - 1 / (t + I * x) ^ 3‖ ≤
      16 * (1 + ‖t‖) ^ 3 / (1 + x) ^ 3 := by
    have : 16 * (1 + ‖t‖) ^ 3 / (1 + x) ^ 3 =
        8 * (1 + ‖t‖) ^ 3 / (1 + x) ^ 3 + 8 * (1 + ‖t‖) ^ 3 / (1 + x) ^ 3 := by ring
    linarith
  have hpi := Real.pi_gt_three
  have hA : 0 ≤ (1 + ‖t‖) ^ 3 := by positivity
  calc x / π * ‖1 / (t - I * x) ^ 3 - 1 / (t + I * x) ^ 3‖
      ≤ x / π * (16 * (1 + ‖t‖) ^ 3 / (1 + x) ^ 3) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        have hx3 : x ^ 3 ≤ (1 + x) ^ 3 := pow_le_pow_left₀ hx0.le (by linarith) 3
        have h3 : x * (16 * (1 + ‖t‖) ^ 3) * x ^ 2 = 16 * (1 + ‖t‖) ^ 3 * x ^ 3 := by ring
        rw [h3]
        have h4 : 16 * (1 + ‖t‖) ^ 3 * x ^ 3 ≤ 16 * (1 + ‖t‖) ^ 3 * (1 + x) ^ 3 :=
          mul_le_mul_of_nonneg_left hx3 (by positivity)
        have h5 : 16 * (1 + ‖t‖) ^ 3 * (1 + x) ^ 3 ≤ 6 * (1 + ‖t‖) ^ 3 * (π * (1 + x) ^ 3) := by
          have := mul_nonneg hA hpow.le
          nlinarith
        linarith

/-- On `Re t ≥ 1` the exponential kernel is `O((1 + ‖t‖)/x²)`. -/
theorem norm_expKerC_le {x : ℝ} (hx : 1 ≤ x) {t : ℂ} (ht : 1 ≤ t.re) :
    ‖expKerC x t‖ ≤ (1 + ‖t‖) / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hpi := Real.pi_gt_three
  have hpi0 := Real.pi_pos
  have hy : 0 < 2 * π * x := by positivity
  have hexp : ‖cexp (-(2 * π * x * t))‖ ≤ 24 / (2 * π * x) ^ 4 := by
    rw [Complex.norm_exp]
    have e : (-(2 * (π : ℂ) * x * t)).re = -(2 * π * x * t.re) := by
      rw [show (2 * (π : ℂ) * x * t) = ((2 * π * x : ℝ) : ℂ) * t by push_cast; ring, Complex.neg_re,
        Complex.re_ofReal_mul]
    rw [e]
    have h1 : Real.exp (-(2 * π * x * t.re)) ≤ Real.exp (-(2 * π * x)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 := exp_neg_le_factorial_div hy 4
    have hf : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hf] at h2
    exact h1.trans h2
  have hlin : ‖4 * (π : ℂ) ^ 2 * x * t - 4 * π‖ ≤ 4 * π ^ 2 * x * ‖t‖ + 4 * π := by
    refine (norm_sub_le _ _).trans ?_
    have e1 : ‖4 * (π : ℂ) ^ 2 * x * t‖ = 4 * π ^ 2 * x * ‖t‖ := by
      rw [show 4 * (π : ℂ) ^ 2 * x * t = ((4 * π ^ 2 * x : ℝ) : ℂ) * t by push_cast; ring, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have e2 : ‖4 * (π : ℂ)‖ = 4 * π := by
      rw [show 4 * (π : ℂ) = ((4 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [e1, e2]
  unfold expKerC
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le]
  have ht0 := norm_nonneg t
  have hmain : x * (4 * π ^ 2 * x * ‖t‖ + 4 * π) ≤ (1 + ‖t‖) * (4 * π ^ 2 * x ^ 2) := by
    have h1 : 4 * π * x ≤ 4 * π ^ 2 * x ^ 2 := by
      have : π * x ≤ π ^ 2 * x ^ 2 := by
        have h : 1 ≤ π * x := by nlinarith
        nlinarith
      linarith
    nlinarith
  calc x * ‖4 * (π : ℂ) ^ 2 * x * t - 4 * π‖ * ‖cexp (-(2 * π * x * t))‖
      ≤ x * (4 * π ^ 2 * x * ‖t‖ + 4 * π) * (24 / (2 * π * x) ^ 4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlin hx0.le) hexp (norm_nonneg _) (by positivity)
    _ ≤ (1 + ‖t‖) * (4 * π ^ 2 * x ^ 2) * (24 / (2 * π * x) ^ 4) :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
    _ = (1 + ‖t‖) * (6 / π ^ 2) / x ^ 2 := by
        field_simp
        ring
    _ ≤ _ := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have : 6 / π ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith
        nlinarith

theorem norm_kerC_le {x : ℝ} (hx : 1 ≤ x) {t : ℂ} (ht : 1 ≤ t.re) :
    ‖kerC x t‖ ≤ 7 * (1 + ‖t‖) ^ 3 / x ^ 2 := by
  have h1 := norm_ratKerC_le hx ht
  have h2 := norm_expKerC_le hx ht
  have hn := norm_nonneg t
  have hx2 : 0 < x ^ 2 := by positivity
  have h3 : (1 + ‖t‖) / x ^ 2 ≤ (1 + ‖t‖) ^ 3 / x ^ 2 :=
    div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hn hn, mul_nonneg hn (mul_nonneg hn hn)])
      hx2.le
  have e : 7 * (1 + ‖t‖) ^ 3 / x ^ 2 = 6 * (1 + ‖t‖) ^ 3 / x ^ 2 + (1 + ‖t‖) ^ 3 / x ^ 2 := by ring
  unfold kerC
  rw [e]
  exact (norm_add_le _ _).trans (by linarith)

/-! ### The second difference kills the exponential kernel -/

/-- `sinh³(πt)` times the second difference of the rational kernel at the integer `N`, as an entire
function of `t`. -/
def ratTau (N : ℕ) (t : ℂ) : ℂ :=
  (I * (N : ℂ) / π) * (sincAt ((N : ℤ) - 1) t ^ 3 - sincAt (-(N : ℤ) - 1) t ^ 3 -
    2 * sincAt (N : ℤ) t ^ 3 + 2 * sincAt (-(N : ℤ)) t ^ 3 + sincAt ((N : ℤ) + 1) t ^ 3 -
    sincAt (1 - (N : ℤ)) t ^ 3)

theorem differentiable_ratTau (N : ℕ) : Differentiable ℂ (ratTau N) := by
  unfold ratTau
  have h : ∀ M : ℤ, Differentiable ℂ fun t => sincAt M t ^ 3 := fun M =>
    (differentiable_sincAt M).pow 3
  exact (((((h _).sub (h _)).sub ((h _).const_mul 2)).add ((h _).const_mul 2)).add (h _)).sub (h _)
    |>.const_mul _

theorem sinh_cube_mul_one_div {t : ℂ} (ht : 0 < t.re) (M : ℤ) :
    Complex.sinh ((π : ℂ) * t) ^ 3 * (1 / (t - I * M) ^ 3) = sincAt M t ^ 3 := by
  have h := sub_I_mul_ne_zero ht (M : ℂ) (by simp)
  rw [sinh_eq_mul_sincAt M t]
  field_simp

theorem expKerC_secondDiff (N : ℕ) (t : ℂ) :
    expKerC N (t + I) - 2 * expKerC N t + expKerC N (t - I) = 0 := by
  have hp : cexp (-(2 * π * ((N : ℝ) : ℂ) * (t + I))) = cexp (-(2 * π * ((N : ℝ) : ℂ) * t)) := by
    have e : -(2 * (π : ℂ) * ((N : ℝ) : ℂ) * (t + I)) =
        -(2 * π * ((N : ℝ) : ℂ) * t) + ((-(N : ℤ) : ℤ) : ℂ) * (2 * π * I) := by
      push_cast
      ring
    rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hm : cexp (-(2 * π * ((N : ℝ) : ℂ) * (t - I))) = cexp (-(2 * π * ((N : ℝ) : ℂ) * t)) := by
    have e : -(2 * (π : ℂ) * ((N : ℝ) : ℂ) * (t - I)) =
        -(2 * π * ((N : ℝ) : ℂ) * t) + (((N : ℤ) : ℤ) : ℂ) * (2 * π * I) := by
      push_cast
      ring
    rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  unfold expKerC
  rw [hp, hm]
  ring

theorem ne_zero_of_re_pos {z : ℂ} (h : 0 < z.re) : z ≠ 0 := by
  rintro rfl
  simp at h

/-- **The second difference at step `i` kills the exponential kernel.** -/
theorem sinh_cube_mul_secondDiff (N : ℕ) {t : ℂ} (ht : 0 < t.re) :
    Complex.sinh ((π : ℂ) * t) ^ 3 *
      (kerC N (t + I) - 2 * kerC N t + kerC N (t - I)) = ratTau N t := by
  have hre : ∀ y : ℂ, y.im = 0 → (t + I + I * y).re = t.re ∧ (t + I - I * y).re = t.re ∧
      (t - I + I * y).re = t.re ∧ (t - I - I * y).re = t.re := by
    intro y hy
    simp [hy]
  obtain ⟨h1, h2, h3, h4⟩ := hre ((N : ℝ) : ℂ) (by simp)
  have hx : ((N : ℝ) : ℂ) = (N : ℂ) := by push_cast; rfl
  have ep : ratKerC N (t + I) = (I * (N : ℂ) / π) *
      (1 / (t - I * (((N : ℤ) - 1 : ℤ) : ℂ)) ^ 3 - 1 / (t - I * ((-(N : ℤ) - 1 : ℤ) : ℂ)) ^ 3) := by
    rw [ratKerC_eq (ne_zero_of_re_pos (by rw [h2]; exact ht))
      (ne_zero_of_re_pos (by rw [h1]; exact ht)), hx,
      show t + I - I * (N : ℂ) = t - I * (((N : ℤ) - 1 : ℤ) : ℂ) by push_cast; ring,
      show t + I + I * (N : ℂ) = t - I * ((-(N : ℤ) - 1 : ℤ) : ℂ) by push_cast; ring]
  have e0 : ratKerC N t = (I * (N : ℂ) / π) *
      (1 / (t - I * ((N : ℤ) : ℂ)) ^ 3 - 1 / (t - I * ((-(N : ℤ) : ℤ) : ℂ)) ^ 3) := by
    rw [ratKerC_eq (sub_I_mul_ne_zero ht _ (by simp)) (add_I_mul_ne_zero ht _ (by simp)), hx,
      show t - I * (N : ℂ) = t - I * ((N : ℤ) : ℂ) by push_cast; ring,
      show t + I * (N : ℂ) = t - I * ((-(N : ℤ) : ℤ) : ℂ) by push_cast; ring]
  have em : ratKerC N (t - I) = (I * (N : ℂ) / π) *
      (1 / (t - I * (((N : ℤ) + 1 : ℤ) : ℂ)) ^ 3 - 1 / (t - I * ((1 - (N : ℤ) : ℤ) : ℂ)) ^ 3) := by
    rw [ratKerC_eq (ne_zero_of_re_pos (by rw [h4]; exact ht))
      (ne_zero_of_re_pos (by rw [h3]; exact ht)), hx,
      show t - I - I * (N : ℂ) = t - I * (((N : ℤ) + 1 : ℤ) : ℂ) by push_cast; ring,
      show t - I + I * (N : ℂ) = t - I * ((1 - (N : ℤ) : ℤ) : ℂ) by push_cast; ring]
  have hexp := expKerC_secondDiff N t
  have hk : kerC N (t + I) - 2 * kerC N t + kerC N (t - I) =
      ratKerC N (t + I) - 2 * ratKerC N t + ratKerC N (t - I) := by
    unfold kerC
    linear_combination hexp
  rw [hk, ep, e0, em]
  unfold ratTau
  rw [← sinh_cube_mul_one_div ht ((N : ℤ) - 1), ← sinh_cube_mul_one_div ht (-(N : ℤ) - 1),
    ← sinh_cube_mul_one_div ht (N : ℤ), ← sinh_cube_mul_one_div ht (-(N : ℤ)),
    ← sinh_cube_mul_one_div ht ((N : ℤ) + 1), ← sinh_cube_mul_one_div ht (1 - (N : ℤ))]
  ring

/-- `‖τ_N(t)‖ ≤ 3 B(t)³/N²`, `B(t) = C₀ e^{π|Re t|} (1 + ‖t‖)`. -/
theorem norm_ratTau_le {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hb : ∀ w, ‖sinhQuot w‖ * (1 + ‖w‖) ≤ C₀ * Real.exp (π * |w.re|)) {N : ℕ} (hN : 1 ≤ N) (t : ℂ) :
    ‖ratTau N t‖ ≤ 3 * (C₀ * Real.exp (π * |t.re|) * (1 + ‖t‖)) ^ 3 / (N : ℝ) ^ 2 := by
  obtain ⟨B, hB⟩ : ∃ B, B = C₀ * Real.exp (π * |t.re|) * (1 + ‖t‖) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  rw [← hB]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hs : ∀ M : ℤ, (N : ℝ) ≤ 1 + |(M : ℝ)| → ‖sincAt M t ^ 3‖ ≤ (B / N) ^ 3 := by
    intro M hM
    have h := norm_sincAt_le hb M t
    rw [← hB] at h
    have h2 : ‖sincAt M t‖ ≤ B / N := by
      rw [le_div_iff₀ hN0]
      exact (mul_le_mul_of_nonneg_left hM (norm_nonneg _)).trans h
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 3
  have hcast : ∀ M : ℤ, (N : ℤ) ≤ 1 + |M| → (N : ℝ) ≤ 1 + |(M : ℝ)| := by
    intro M hM
    have : ((N : ℤ) : ℝ) ≤ ((1 + |M| : ℤ) : ℝ) := by exact_mod_cast hM
    simpa using this
  have h1 := hs ((N : ℤ) - 1) (hcast _ (by rw [abs_of_nonneg (by omega)]; omega))
  have h2 := hs (-(N : ℤ) - 1) (hcast _ (by rw [abs_of_nonpos (by omega)]; omega))
  have h3 := hs (N : ℤ) (hcast _ (by rw [abs_of_nonneg (by omega)]; omega))
  have h4 := hs (-(N : ℤ)) (hcast _ (by rw [abs_of_nonpos (by omega)]; omega))
  have h5 := hs ((N : ℤ) + 1) (hcast _ (by rw [abs_of_nonneg (by omega)]; omega))
  have h6 := hs (1 - (N : ℤ)) (hcast _ (by rw [abs_of_nonpos (by omega)]; omega))
  have hsum : ∀ a b c d e f : ℂ, ‖a - b - 2 * c + 2 * d + e - f‖ ≤
      ‖a‖ + ‖b‖ + 2 * ‖c‖ + 2 * ‖d‖ + ‖e‖ + ‖f‖ := by
    intro a b c d e f
    have n1 := norm_sub_le (a - b - 2 * c + 2 * d + e) f
    have n2 := norm_add_le (a - b - 2 * c + 2 * d) e
    have n3 := norm_add_le (a - b - 2 * c) (2 * d)
    have n4 := norm_sub_le (a - b) (2 * c)
    have n5 := norm_sub_le a b
    have n6 : ‖(2 : ℂ) * c‖ = 2 * ‖c‖ := by simp
    have n7 : ‖(2 : ℂ) * d‖ = 2 * ‖d‖ := by simp
    linarith
  have hI : ‖I * (N : ℂ) / (π : ℂ)‖ = N / π := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  unfold ratTau
  rw [norm_mul, hI]
  have hpi := Real.pi_gt_three
  have hX : 0 ≤ (B / N) ^ 3 := by positivity
  calc (N : ℝ) / π * _ ≤ (N : ℝ) / π * (8 * (B / N) ^ 3) := by
        refine mul_le_mul_of_nonneg_left ((hsum _ _ _ _ _ _).trans ?_) (by positivity)
        linarith
    _ = (8 / π) * B ^ 3 / (N : ℝ) ^ 2 := by
        field_simp
    _ ≤ _ := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [div_le_iff₀ Real.pi_pos]
        linarith

/-! ### The two series -/

/-- The integer `(k + 1)(n + 1)` read at the index `(n, k)`. -/
def idxN (p : ℕ × ℕ) : ℕ := (p.2 + 1) * (p.1 + 1)

theorem one_le_idxN (p : ℕ × ℕ) : 1 ≤ idxN p := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)

/-- The summable weight of the double series. -/
def indexWeight (p : ℕ × ℕ) : ℝ := (1 / ((p.1 : ℝ) + 1) ^ (3 / 2 : ℝ)) * (1 / ((p.2 : ℝ) + 1) ^ 2)

theorem indexWeight_nonneg (p : ℕ × ℕ) : 0 ≤ indexWeight p := by
  unfold indexWeight
  positivity

theorem summable_indexWeight : Summable indexWeight := by
  have h1 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2))
    simpa using this
  have h2 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  exact h1.mul_of_nonneg h2 (fun n => by positivity) (fun n => by positivity)

/-- The size of one term of the double series. -/
theorem norm_term_le {δ : ℕ → ℝ} {V A : ℝ} (hV : 0 ≤ V)
    (hδ : ∀ n, 1 ≤ n → |δ n| ≤ V * Real.sqrt n) {g : ℕ → ℂ}
    (hg : ∀ N, 1 ≤ N → ‖g N‖ ≤ A / (N : ℝ) ^ 2) (p : ℕ × ℕ) :
    ‖(δ (p.1 + 1) : ℂ) * g (idxN p)‖ ≤ V * A * indexWeight p := by
  have hd := hδ (p.1 + 1) (Nat.succ_pos _)
  have hG := hg (idxN p) (one_le_idxN p)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (p.1 : ℝ) + 1 := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (p.2 : ℝ) + 1 := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by rw [hn]; have := (Nat.cast_nonneg p.1 : (0 : ℝ) ≤ p.1); linarith
  have hk1 : 1 ≤ k := by rw [hk]; have := (Nat.cast_nonneg p.2 : (0 : ℝ) ≤ p.2); linarith
  have hn0 : 0 < n := by linarith
  have hk0 : 0 < k := by linarith
  have hcast : (idxN p : ℝ) = k * n := by
    unfold idxN
    rw [hn, hk]
    push_cast
    ring
  have hcast2 : ((p.1 + 1 : ℕ) : ℝ) = n := by rw [hn]; push_cast; ring
  rw [hcast] at hG
  rw [hcast2] at hd
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hrp : n ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  unfold indexWeight
  rw [← hn, ← hk, hrp]
  calc |δ (p.1 + 1)| * ‖g (idxN p)‖
      ≤ (V * Real.sqrt n) * (A / (k * n) ^ 2) :=
        mul_le_mul hd hG (norm_nonneg _) (by positivity)
    _ = V * A * (1 / (n * Real.sqrt n) * (1 / k ^ 2)) := by
        have hsn : (Real.sqrt n) / n ^ 2 = 1 / (n * Real.sqrt n) := by
          rw [div_eq_div_iff (by positivity) (by positivity)]
          calc Real.sqrt n * (n * Real.sqrt n) = n * (Real.sqrt n * Real.sqrt n) := by ring
            _ = 1 * n ^ 2 := by rw [hss]; ring
        rw [← hsn]
        field_simp
    _ ≤ _ := le_rfl

/-- The reading `S(t) = Σ_{n,k≥1} δ(n) ker(kn, t)`. -/
def readS (δ : ℕ → ℝ) (t : ℂ) : ℂ := ∑' p : ℕ × ℕ, (δ (p.1 + 1) : ℂ) * kerC (idxN p) t

/-- The entire function `T(t) = Σ_{n,k≥1} δ(n) τ_{kn}(t)`. -/
def poleT (δ : ℕ → ℝ) (t : ℂ) : ℂ := ∑' p : ℕ × ℕ, (δ (p.1 + 1) : ℂ) * ratTau (idxN p) t

section Series

variable {δ : ℕ → ℝ} {V : ℝ}

theorem norm_kerC_nat_le {t : ℂ} (ht : 1 ≤ t.re) (N : ℕ) (hN : 1 ≤ N) :
    ‖kerC (N : ℝ) t‖ ≤ 7 * (1 + ‖t‖) ^ 3 / (N : ℝ) ^ 2 :=
  norm_kerC_le (by exact_mod_cast hN) ht

theorem summable_readS (hV : 0 ≤ V) (hδ : ∀ n, 1 ≤ n → |δ n| ≤ V * Real.sqrt n) {t : ℂ}
    (ht : 1 ≤ t.re) : Summable fun p : ℕ × ℕ => (δ (p.1 + 1) : ℂ) * kerC (idxN p) t :=
  Summable.of_norm_bounded (summable_indexWeight.mul_left (V * (7 * (1 + ‖t‖) ^ 3)))
    fun p => norm_term_le hV hδ (g := fun N => kerC (N : ℝ) t)
      (norm_kerC_nat_le ht) p

theorem norm_readS_le (hV : 0 ≤ V) (hδ : ∀ n, 1 ≤ n → |δ n| ≤ V * Real.sqrt n) {t : ℂ}
    (ht : 1 ≤ t.re) : ‖readS δ t‖ ≤ V * (7 * (1 + ‖t‖) ^ 3) * ∑' p, indexWeight p := by
  unfold readS
  refine (tsum_of_norm_bounded (summable_indexWeight.mul_left (V * (7 * (1 + ‖t‖) ^ 3))).hasSum
    fun p => norm_term_le hV hδ (g := fun N => kerC (N : ℝ) t)
      (norm_kerC_nat_le ht) p).trans (le_of_eq ?_)
  exact (summable_indexWeight.hasSum.mul_left _).tsum_eq.symm ▸ rfl

theorem differentiableAt_readS (hV : 0 ≤ V) (hδ : ∀ n, 1 ≤ n → |δ n| ≤ V * Real.sqrt n) {t : ℂ}
    (ht : 1 < t.re) : DifferentiableAt ℂ (readS δ) t := by
  obtain ⟨U, hU⟩ : ∃ U : Set ℂ, U = {w : ℂ | 1 < w.re} ∩ Metric.ball t 1 := ⟨_, rfl⟩
  have hUo : IsOpen U := by
    rw [hU]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hmem : t ∈ U := by
    rw [hU]
    exact ⟨ht, Metric.mem_ball_self one_pos⟩
  have hbd : ∀ w ∈ U, ‖w‖ ≤ ‖t‖ + 1 := by
    intro w hw
    rw [hU] at hw
    have h1 : ‖w - t‖ < 1 := by simpa [dist_eq_norm] using hw.2
    have := norm_le_norm_add_norm_sub' w t
    linarith
  have hd : DifferentiableOn ℂ (fun w => ∑' p : ℕ × ℕ, (δ (p.1 + 1) : ℂ) * kerC (idxN p) w) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun p => V * (7 * (1 + (‖t‖ + 1)) ^ 3) * indexWeight p)
      (summable_indexWeight.mul_left _) (fun p w hw => ?_) hUo (fun p w hw => ?_)
    · have hw' : 1 < w.re := by rw [hU] at hw; exact hw.1
      exact ((differentiableAt_kerC _ (by linarith)).const_mul _).differentiableWithinAt
    · have hw' : 1 < w.re := by rw [hU] at hw; exact hw.1
      have hb : ∀ N : ℕ, 1 ≤ N → ‖kerC (N : ℝ) w‖ ≤ 7 * (1 + (‖t‖ + 1)) ^ 3 / (N : ℝ) ^ 2 := by
        intro N hN
        refine (norm_kerC_nat_le hw'.le N hN).trans ?_
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have := hbd w hw
        have hn := norm_nonneg w
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 3) (by norm_num)
      exact norm_term_le hV hδ (g := fun N => kerC (N : ℝ) w) hb p
  exact hd.differentiableAt (hUo.mem_nhds hmem)

theorem differentiable_poleT {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hb : ∀ w, ‖sinhQuot w‖ * (1 + ‖w‖) ≤ C₀ * Real.exp (π * |w.re|)) (hV : 0 ≤ V)
    (hδ : ∀ n, 1 ≤ n → |δ n| ≤ V * Real.sqrt n) : Differentiable ℂ (poleT δ) := by
  intro t
  obtain ⟨U, hU⟩ : ∃ U : Set ℂ, U = Metric.ball t 1 := ⟨_, rfl⟩
  have hUo : IsOpen U := by rw [hU]; exact Metric.isOpen_ball
  have hmem : t ∈ U := by rw [hU]; exact Metric.mem_ball_self one_pos
  obtain ⟨R, hR⟩ : ∃ R, R = ‖t‖ + 1 := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  obtain ⟨A, hA⟩ : ∃ A, A = 3 * (C₀ * Real.exp (π * R) * (1 + R)) ^ 3 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hd : DifferentiableOn ℂ (fun w => ∑' p : ℕ × ℕ, (δ (p.1 + 1) : ℂ) * ratTau (idxN p) w) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun p => V * A * indexWeight p)
      (summable_indexWeight.mul_left _) (fun p w _ => ?_) hUo (fun p w hw => ?_)
    · exact (((differentiable_ratTau _) w).const_mul _).differentiableWithinAt
    · have hbd : ‖w‖ ≤ R := by
        rw [hU] at hw
        have h1 : ‖w - t‖ < 1 := by simpa [dist_eq_norm] using hw
        have := norm_le_norm_add_norm_sub' w t
        rw [hR]
        linarith
      have hg : ∀ N : ℕ, 1 ≤ N → ‖ratTau N w‖ ≤ A / (N : ℝ) ^ 2 := by
        intro N hN
        refine (norm_ratTau_le hC₀ hb hN w).trans ?_
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [hA]
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ 3) (by norm_num)
        have hre : |w.re| ≤ R := (Complex.abs_re_le_norm w).trans hbd
        have h1 : Real.exp (π * |w.re|) ≤ Real.exp (π * R) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hre Real.pi_pos.le)
        have hn := norm_nonneg w
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC₀) (by linarith) (by positivity)
          (by positivity)
      exact norm_term_le hV hδ (g := fun N => ratTau N w) hg p
  exact hd.differentiableAt (hUo.mem_nhds hmem)

/-- The size of `T`. -/
theorem norm_poleT_le {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hb : ∀ w, ‖sinhQuot w‖ * (1 + ‖w‖) ≤ C₀ * Real.exp (π * |w.re|)) (hV : 0 ≤ V)
    (hδ : ∀ n, 1 ≤ n → |δ n| ≤ V * Real.sqrt n) (t : ℂ) :
    ‖poleT δ t‖ ≤ V * (3 * (C₀ * Real.exp (π * |t.re|) * (1 + ‖t‖)) ^ 3) * ∑' p, indexWeight p := by
  unfold poleT
  have hA : 0 ≤ 3 * (C₀ * Real.exp (π * |t.re|) * (1 + ‖t‖)) ^ 3 := by positivity
  refine (tsum_of_norm_bounded (summable_indexWeight.mul_left _).hasSum
    fun p => norm_term_le hV hδ (g := fun N => ratTau N t)
      (fun N hN => norm_ratTau_le hC₀ hb hN t) p).trans (le_of_eq ?_)
  exact (summable_indexWeight.hasSum.mul_left _).tsum_eq.symm ▸ rfl

/-- `sinh³(πt) (S(t + i) − 2S(t) + S(t − i)) = T(t)` on `Re t > 1`. -/
theorem sinh_cube_mul_readS (hV : 0 ≤ V)
    (hδ : ∀ n, 1 ≤ n → |δ n| ≤ V * Real.sqrt n) {t : ℂ} (ht : 1 ≤ t.re) :
    Complex.sinh ((π : ℂ) * t) ^ 3 * (readS δ (t + I) - 2 * readS δ t + readS δ (t - I)) =
      poleT δ t := by
  have ht0 : 0 < t.re := by linarith
  have hp := summable_readS hV hδ (t := t + I) (by simpa using ht)
  have h0 := summable_readS hV hδ ht
  have hm := summable_readS hV hδ (t := t - I) (by simpa using ht)
  have hsum := ((hp.hasSum.sub (h0.hasSum.mul_left 2)).add hm.hasSum).mul_left
    (Complex.sinh ((π : ℂ) * t) ^ 3)
  have hfun : (fun p : ℕ × ℕ => (δ (p.1 + 1) : ℂ) * ratTau (idxN p) t) = fun i : ℕ × ℕ =>
      Complex.sinh ((π : ℂ) * t) ^ 3 * ((δ (i.1 + 1) : ℂ) * kerC (idxN i) (t + I) -
        2 * ((δ (i.1 + 1) : ℂ) * kerC (idxN i) t) + (δ (i.1 + 1) : ℂ) * kerC (idxN i) (t - I)) := by
    funext p
    rw [← sinh_cube_mul_secondDiff _ ht0]
    ring
  unfold readS poleT
  rw [hfun]
  exact hsum.tsum_eq.symm

theorem kerC_conj (x : ℝ) (t : ℂ) :
    kerC x ((starRingEnd ℂ) t) = (starRingEnd ℂ) (kerC x t) := by
  simp only [kerC, ratKerC, expKerC, map_add, map_sub, map_mul, map_div₀, map_pow, map_neg,
    Complex.conj_ofReal, map_ofNat, ← Complex.exp_conj]

/-- `S(t̄)` is the conjugate of `S(t)`. -/
theorem readS_conj (δ : ℕ → ℝ) (t : ℂ) :
    readS δ ((starRingEnd ℂ) t) = (starRingEnd ℂ) (readS δ t) := by
  unfold readS
  rw [Complex.conj_tsum]
  refine tsum_congr fun p => ?_
  rw [map_mul, Complex.conj_ofReal, kerC_conj]

end Series

/-! ### The poles read the divisor sums -/

theorem sincAt_cube_I (M : ℤ) (L : ℕ) :
    sincAt M (I * L) ^ 3 = if M = (L : ℤ) then (-1 : ℂ) ^ (L : ℤ) * (π : ℂ) ^ 3 else 0 := by
  split_ifs with h
  · subst h
    have e : I * ((L : ℕ) : ℂ) - I * (((L : ℤ) : ℤ) : ℂ) = 0 := by push_cast; ring
    unfold sincAt
    rw [e, sinhQuot_zero, mul_pow]
    have h2 := neg_one_zpow_mul_self (L : ℤ)
    congr 1
    calc ((-1 : ℂ) ^ (L : ℤ)) ^ 3 = (-1 : ℂ) ^ (L : ℤ) * ((-1 : ℂ) ^ (L : ℤ) * (-1 : ℂ) ^ (L : ℤ)) := by
          ring
      _ = _ := by rw [h2, mul_one]
  · have e : I * ((L : ℕ) : ℂ) - I * (M : ℂ) = I * (((L : ℤ) - M : ℤ) : ℂ) := by push_cast; ring
    unfold sincAt
    rw [e, sinhQuot_I_mul_int (by omega), mul_zero]
    simp

/-- The value of `τ_N` at the pole `iL`. -/
theorem ratTau_I {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L) :
    ratTau N (I * L) = I * π ^ 2 * (-1 : ℂ) ^ (L : ℤ) * ((N : ℂ) * ((if N = L + 1 then 1 else 0) -
      2 * (if N = L then 1 else 0) + (if N + 1 = L then 1 else 0))) := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have c1 : ((N : ℤ) - 1 = (L : ℤ)) ↔ N = L + 1 := by omega
  have c2 : ¬ (-(N : ℤ) - 1 = (L : ℤ)) := by omega
  have c3 : ((N : ℤ) = (L : ℤ)) ↔ N = L := by omega
  have c4 : ¬ (-(N : ℤ) = (L : ℤ)) := by omega
  have c5 : ((N : ℤ) + 1 = (L : ℤ)) ↔ N + 1 = L := by omega
  have c6 : ¬ (1 - (N : ℤ) = (L : ℤ)) := by omega
  unfold ratTau
  simp only [sincAt_cube_I, c1, c3, c5, if_neg c2, if_neg c4, if_neg c6]
  split_ifs <;> field_simp <;> ring

/-- `Σ_{(n,k): kn = N₀} δ(n)` is the divisor sum of `δ` at `N₀`. -/
theorem hasSum_indicator (δ : ℕ → ℝ) (N₀ : ℕ) :
    HasSum (fun p : ℕ × ℕ => if idxN p = N₀ then (δ (p.1 + 1) : ℂ) else 0)
      (∑ d ∈ N₀.divisors, (δ d : ℂ)) := by
  obtain ⟨s, hs⟩ : ∃ s : Finset (ℕ × ℕ), s = N₀.divisors.image fun d => (d - 1, N₀ / d - 1) :=
    ⟨_, rfl⟩
  have hzero : ∀ p ∉ s, (if idxN p = N₀ then (δ (p.1 + 1) : ℂ) else 0) = 0 := by
    intro p hp
    refine if_neg fun h => hp ?_
    rw [hs, Finset.mem_image]
    have hpos := one_le_idxN p
    have hN₀ : N₀ ≠ 0 := by omega
    refine ⟨p.1 + 1, ?_, ?_⟩
    · rw [Nat.mem_divisors]
      exact ⟨⟨p.2 + 1, by rw [← h]; unfold idxN; ring⟩, hN₀⟩
    · have hd : N₀ / (p.1 + 1) = p.2 + 1 := by
        rw [← h]
        unfold idxN
        exact Nat.mul_div_cancel _ (Nat.succ_pos _)
      rw [hd]
      simp
  have h : HasSum (fun p : ℕ × ℕ => if idxN p = N₀ then (δ (p.1 + 1) : ℂ) else 0)
      (∑ b ∈ s, if idxN b = N₀ then (δ (b.1 + 1) : ℂ) else 0) :=
    hasSum_sum_of_ne_finset_zero hzero
  have e : (∑ b ∈ s, if idxN b = N₀ then (δ (b.1 + 1) : ℂ) else 0) = ∑ d ∈ N₀.divisors, (δ d : ℂ) := by
    rw [hs, Finset.sum_image]
    · refine Finset.sum_congr rfl fun d hd => ?_
      have hdiv := Nat.dvd_of_mem_divisors hd
      have hN₀ : N₀ ≠ 0 := (Nat.mem_divisors.mp hd).2
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have hq : 0 < N₀ / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN₀) hdiv) hd0
      have e1 : d - 1 + 1 = d := by omega
      have e2 : N₀ / d - 1 + 1 = N₀ / d := by omega
      have e3 : idxN (d - 1, N₀ / d - 1) = N₀ := by
        unfold idxN
        simp only
        rw [e1, e2]
        exact Nat.div_mul_cancel hdiv
      simp only
      rw [if_pos e3, e1]
    · intro a ha b hb hab
      have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
      have hb0 : 0 < b := Nat.pos_of_mem_divisors hb
      have := congrArg Prod.fst hab
      simp only at this
      omega
  rw [e] at h
  exact h

/-- The divisor sum `D(N) = Σ_{d ∣ N} δ(d)`. -/
def divSum (δ : ℕ → ℝ) (N : ℕ) : ℝ := ∑ d ∈ N.divisors, δ d

theorem ite_arith {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L) (a : ℂ) :
    a * ((N : ℂ) * ((if N = L + 1 then 1 else 0) - 2 * (if N = L then 1 else 0) +
      (if N + 1 = L then 1 else 0))) =
      ((L + 1 : ℕ) : ℂ) * (if N = L + 1 then a else 0) - 2 * (L : ℂ) * (if N = L then a else 0) +
        ((L : ℂ) - 1) * (if N = L - 1 then a else 0) := by
  by_cases c1 : N = L + 1
  · have c2 : ¬ N = L := by omega
    have c3 : ¬ N + 1 = L := by omega
    have c5 : ¬ N = L - 1 := by omega
    rw [if_pos c1, if_neg c2, if_neg c3, if_pos c1, if_neg c2, if_neg c5, c1]
    ring
  · by_cases c2 : N = L
    · have c3 : ¬ N + 1 = L := by omega
      have c5 : ¬ N = L - 1 := by omega
      rw [if_neg c1, if_pos c2, if_neg c3, if_neg c1, if_pos c2, if_neg c5, c2]
      ring
    · by_cases c3 : N + 1 = L
      · have c5 : N = L - 1 := by omega
        have e5 : (N : ℂ) = (L : ℂ) - 1 := by
          rw [← c3]
          push_cast
          ring
        rw [if_neg c1, if_neg c2, if_pos c3, if_neg c1, if_neg c2, if_pos c5, e5]
        ring
      · have c5 : ¬ N = L - 1 := by omega
        rw [if_neg c1, if_neg c2, if_neg c3, if_neg c1, if_neg c2, if_neg c5]
        ring

/-- **The poles read the divisor sums.** `T(iL)` is, up to a unit times `π²`, the discrete Laplacian of
`N ↦ N D(N)` at `L`. -/
theorem poleT_I_mul (δ : ℕ → ℝ) {L : ℕ} (hL : 1 ≤ L) :
    poleT δ (I * L) = I * π ^ 2 * (-1 : ℂ) ^ (L : ℤ) *
      ((((L + 1 : ℕ) : ℝ) * divSum δ (L + 1) - 2 * ((L : ℝ) * divSum δ L) +
        (((L : ℝ) - 1) * divSum δ (L - 1)) : ℝ) : ℂ) := by
  have h1 := (hasSum_indicator δ (L + 1)).mul_left (((L + 1 : ℕ) : ℂ))
  have h2 := (hasSum_indicator δ L).mul_left (2 * (L : ℂ))
  have h3 := (hasSum_indicator δ (L - 1)).mul_left ((L : ℂ) - 1)
  have h := ((h1.sub h2).add h3).mul_left (I * π ^ 2 * (-1 : ℂ) ^ (L : ℤ))
  have e : ((((L + 1 : ℕ) : ℝ) * divSum δ (L + 1) - 2 * ((L : ℝ) * divSum δ L) +
      (((L : ℝ) - 1) * divSum δ (L - 1)) : ℝ) : ℂ) =
      ((L + 1 : ℕ) : ℂ) * (∑ d ∈ (L + 1).divisors, (δ d : ℂ)) -
        2 * (L : ℂ) * (∑ d ∈ L.divisors, (δ d : ℂ)) +
        ((L : ℂ) - 1) * (∑ d ∈ (L - 1).divisors, (δ d : ℂ)) := by
    unfold divSum
    push_cast
    ring
  have hfun : (fun p : ℕ × ℕ => (δ (p.1 + 1) : ℂ) * ratTau (idxN p) (I * L)) = fun i : ℕ × ℕ =>
      I * π ^ 2 * (-1 : ℂ) ^ (L : ℤ) *
        (((L + 1 : ℕ) : ℂ) * (if idxN i = L + 1 then (δ (i.1 + 1) : ℂ) else 0) -
          2 * (L : ℂ) * (if idxN i = L then (δ (i.1 + 1) : ℂ) else 0) +
          ((L : ℂ) - 1) * (if idxN i = L - 1 then (δ (i.1 + 1) : ℂ) else 0)) := by
    funext p
    rw [ratTau_I (one_le_idxN p) hL, ← ite_arith (one_le_idxN p) hL]
    ring
  unfold poleT
  rw [e, hfun]
  exact h.tsum_eq

/-! ### From the ray to the poles -/

theorem three_add_pow_le {r : ℝ} (hr : 0 ≤ r) : (3 + r) ^ 3 ≤ 27 * Real.exp r := by
  have h := Real.add_one_le_exp (r / 3)
  have h3 := pow_le_pow_left₀ (by positivity) h 3
  rw [← Real.exp_nat_mul] at h3
  have e : ((3 : ℕ) : ℝ) * (r / 3) = r := by push_cast; ring
  rw [e] at h3
  have e2 : (3 + r) ^ 3 = 27 * (r / 3 + 1) ^ 3 := by ring
  rw [e2]
  linarith

theorem one_add_pow_le {y : ℝ} (hy : 0 ≤ y) : (1 + y) ^ 3 ≤ 6 * Real.exp (1 + y) := by
  have h := Real.pow_div_factorial_le_exp (1 + y) (by linarith) 3
  have hf : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf, div_le_iff₀ (by norm_num)] at h
  linarith

/-- `a + y + i` lies on a ray of angle at most `π/4` from the apex `a`, when `y ≥ 1`. -/
theorem exists_ray_add_I (a : ℝ) {y : ℝ} (hy : 1 ≤ y) :
    ∃ r α : ℝ, 0 < r ∧ r ≤ y + 1 ∧ α ∈ Icc (0 : ℝ) (π / 4) ∧
      rayPt a r α = ((a + y : ℝ) : ℂ) + I := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = (y : ℂ) + I := ⟨_, rfl⟩
  have hre : z.re = y := by rw [hz]; simp
  have him : z.im = 1 := by rw [hz]; simp
  have hnorm : ‖z‖ ^ 2 = y ^ 2 + 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    ring
  have hr0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hrpos : 0 < ‖z‖ := by
    rcases hr0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hnorm
      nlinarith
  have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hrs : Real.sqrt 2 ≤ ‖z‖ := by
    refine abs_le_of_sq_le_sq' ?_ hr0 |>.2
    rw [hsq2, hnorm]
    nlinarith
  refine ⟨‖z‖, Complex.arg z, hrpos, ?_, ⟨?_, ?_⟩, ?_⟩
  · have h : ‖z‖ ^ 2 ≤ (y + 1) ^ 2 := by rw [hnorm]; nlinarith
    exact abs_le_of_sq_le_sq' h (by linarith) |>.2
  · exact Complex.arg_nonneg_iff.mpr (by rw [him]; norm_num)
  · rw [Complex.arg_of_re_nonneg (by rw [hre]; linarith), him]
    have hdiv : 1 / ‖z‖ ≤ Real.sqrt 2 / 2 := by
      rw [div_le_div_iff₀ hrpos (by norm_num)]
      nlinarith
    have hmem : 1 / ‖z‖ ∈ Icc (-1 : ℝ) 1 := by
      constructor
      · have : 0 ≤ 1 / ‖z‖ := by positivity
        linarith
      · rw [div_le_one hrpos]
        nlinarith
    refine (Real.arcsin_le_iff_le_sin hmem ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).mpr ?_
    rw [Real.sin_pi_div_four]
    exact hdiv
  · unfold rayPt
    rw [Complex.norm_mul_exp_arg_mul_I, hz]
    push_cast
    ring

theorem three_pi_div_eight_lt : (0 : ℝ) < 3 * π / 8 ∧ 3 * π / 8 < π := by
  have := Real.pi_pos
  constructor <;> linarith

section Reading

variable {δ : ℕ → ℝ} {V η : ℝ}

/-- **First step.** Smallness of `S` on the real ray reaches `S(τ ± i)`. -/
theorem norm_readS_add_I_le (hV : 1 ≤ V) (hη : 0 < η) (hη1 : η ≤ 1)
    (hδ : ∀ n, 1 ≤ n → |δ n| ≤ V * Real.sqrt n) (hS : ∀ t : ℝ, 2 ≤ t → ‖readS δ t‖ ≤ η)
    {τ : ℝ} (hτ : 3 ≤ τ) :
    ‖readS δ ((τ : ℂ) + I)‖ ≤
      η ^ (1 / 3 : ℝ) * (189 * V * ∑' p, indexWeight p) ^ (2 / 3 : ℝ) *
        Real.exp (1 / Real.cos (3 * π / 8 / 2) * (τ - 1)) := by
  obtain ⟨hφ, hφ'⟩ := three_pi_div_eight_lt
  have hpi := Real.pi_pos
  have hV0 : 0 ≤ V := by linarith
  obtain ⟨W, hW⟩ : ∃ W, W = ∑' p, indexWeight p := ⟨_, rfl⟩
  have hW1 : 1 ≤ W := by
    have h := summable_indexWeight.le_tsum (0, 0) (fun j _ => indexWeight_nonneg j)
    have e : indexWeight (0, 0) = 1 := by simp [indexWeight]
    rw [e, ← hW] at h
    exact h
  rw [← hW]
  obtain ⟨M, hM⟩ : ∃ M, M = 189 * V * W := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith
  rw [← hM]
  have hcos : ∀ r α : ℝ, α ∈ Icc (0 : ℝ) (3 * π / 8) → 0 ≤ r → 2 ≤ (rayPt 2 r α).re := by
    intro r α hα hr
    rw [rayPt_re]
    have : 0 ≤ Real.cos α := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hα.1])
      (by linarith [hα.2])
    nlinarith [mul_nonneg hr this]
  have hbound : ∀ r α : ℝ, 0 < r → α ∈ Icc (0 : ℝ) (3 * π / 8) →
      ‖readS δ (rayPt 2 r α)‖ ≤ M * Real.exp (1 * r) := by
    intro r α hr hα
    have hre := hcos r α hα hr.le
    refine (norm_readS_le hV0 hδ (by linarith)).trans ?_
    rw [← hW, one_mul]
    have hn := norm_rayPt_le (a := 2) (by norm_num) hr.le α
    have hp : (1 + ‖rayPt 2 r α‖) ^ 3 ≤ 27 * Real.exp r := by
      refine le_trans (pow_le_pow_left₀ (by positivity) ?_ 3) (three_add_pow_le hr.le)
      linarith
    calc V * (7 * (1 + ‖rayPt 2 r α‖) ^ 3) * W ≤ V * (7 * (27 * Real.exp r)) * W := by
          gcongr
      _ = _ := by rw [hM]; ring
  have hmain := fun {r α : ℝ} (hr : 0 < r) (hα : α ∈ Icc (0 : ℝ) (3 * π / 8)) =>
    norm_le_of_sector (F := readS δ) (a := 2) (K := 1) (M₀ := η) (M₁ := M) (A := M) hφ hφ' zero_le_one
      (fun r α hr hα => differentiableAt_readS hV0 hδ (by linarith [hcos r α hα hr.le]))
      hbound
      (fun r hr => by
        rw [rayPt_zero]
        refine (hS _ (by linarith)).trans ?_
        exact le_mul_of_one_le_right hη.le (Real.one_le_exp (by linarith)))
      (fun r hr => hbound r _ hr ⟨hφ.le, le_rfl⟩) hr hα
  obtain ⟨r, α, hr, hrle, hα, hpt⟩ := exists_ray_add_I 2 (y := τ - 2) (by linarith)
  have hτI : (τ : ℂ) + I = rayPt 2 r α := by
    rw [hpt]
    push_cast
    ring
  have hαφ : α ∈ Icc (0 : ℝ) (3 * π / 8) := ⟨hα.1, by linarith [hα.2]⟩
  rw [hτI]
  refine (hmain hr hαφ).trans ?_
  have hx : α / (3 * π / 8) ≤ 2 / 3 := by
    rw [div_le_iff₀ hφ]
    linarith [hα.2]
  have hx0 : 0 ≤ α / (3 * π / 8) := div_nonneg hα.1 hφ.le
  have h1 : η ^ (1 - α / (3 * π / 8)) ≤ η ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hη hη1 (by linarith)
  have h2 : M ^ (α / (3 * π / 8)) ≤ M ^ (2 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 hx
  have hcp := cos_half_pos hφ hφ'
  have h3 : Real.exp (1 / Real.cos (3 * π / 8 / 2) * r) ≤
      Real.exp (1 / Real.cos (3 * π / 8 / 2) * (τ - 1)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hp1 : 0 ≤ η ^ (1 / 3 : ℝ) := by positivity
  have hp2 : 0 ≤ M ^ (α / (3 * π / 8)) := by positivity
  have hp3 : 0 ≤ M ^ (2 / 3 : ℝ) := by positivity
  exact mul_le_mul (mul_le_mul h1 h2 hp2 hp1) h3 (Real.exp_pos _).le (mul_nonneg hp1 hp3)

/-- On the real ray, `T` is small: `‖T(τ)‖ ≤ 4 η^{1/3} M^{2/3} e^{(3π + K₂)τ}`. -/
theorem norm_poleT_ofReal_le (hV : 1 ≤ V) (hη : 0 < η) (hη1 : η ≤ 1)
    (hδ : ∀ n, 1 ≤ n → |δ n| ≤ V * Real.sqrt n) (hS : ∀ t : ℝ, 2 ≤ t → ‖readS δ t‖ ≤ η)
    {τ : ℝ} (hτ : 3 ≤ τ) :
    ‖poleT δ (τ : ℂ)‖ ≤
      4 * (η ^ (1 / 3 : ℝ) * (189 * V * ∑' p, indexWeight p) ^ (2 / 3 : ℝ)) *
        Real.exp ((3 * π + 1 / Real.cos (3 * π / 8 / 2)) * τ) := by
  obtain ⟨hφ, hφ'⟩ := three_pi_div_eight_lt
  have hV0 : 0 ≤ V := by linarith
  have hre : 1 ≤ ((τ : ℂ)).re := by simp; linarith
  rw [← sinh_cube_mul_readS hV0 hδ hre]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = η ^ (1 / 3 : ℝ) * (189 * V * ∑' p, indexWeight p) ^ (2 / 3 : ℝ) := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂, K₂ = 1 / Real.cos (3 * π / 8 / 2) := ⟨_, rfl⟩
  have hcp := cos_half_pos hφ hφ'
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  have hplus := norm_readS_add_I_le hV hη hη1 hδ hS hτ
  rw [← hQ, ← hK₂] at hplus
  have hminus : ‖readS δ ((τ : ℂ) - I)‖ ≤ Q * Real.exp (K₂ * (τ - 1)) := by
    have e : (τ : ℂ) - I = (starRingEnd ℂ) ((τ : ℂ) + I) := by
      rw [map_add, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [e, readS_conj, Complex.norm_conj]
    exact hplus
  have hzero : ‖readS δ (τ : ℂ)‖ ≤ η := hS τ (by linarith)
  have hW1 : 1 ≤ ∑' p, indexWeight p := by
    have h := summable_indexWeight.le_tsum (0, 0) (fun j _ => indexWeight_nonneg j)
    have e : indexWeight (0, 0) = 1 := by simp [indexWeight]
    rwa [e] at h
  have hM1 : 1 ≤ (189 * V * ∑' p, indexWeight p) := by nlinarith
  have hηQ : η ≤ Q := by
    rw [hQ]
    have h1 : η ≤ η ^ (1 / 3 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_ge hη hη1 (show (1 / 3 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have h2 : 1 ≤ (189 * V * ∑' p, indexWeight p) ^ (2 / 3 : ℝ) :=
      Real.one_le_rpow hM1 (by norm_num)
    have h3 : 0 ≤ η ^ (1 / 3 : ℝ) := by positivity
    nlinarith
  have hQ0 : 0 ≤ Q := hη.le.trans hηQ
  have hτ0 : 0 ≤ τ := by linarith
  have hexp1 : Real.exp (K₂ * (τ - 1)) ≤ Real.exp (K₂ * τ) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hK₂0)
  have hexp0 : 1 ≤ Real.exp (K₂ * τ) := Real.one_le_exp (by positivity)
  have hdiff : ‖readS δ ((τ : ℂ) + I) - 2 * readS δ (τ : ℂ) + readS δ ((τ : ℂ) - I)‖ ≤
      4 * Q * Real.exp (K₂ * τ) := by
    have n1 := norm_add_le (readS δ ((τ : ℂ) + I) - 2 * readS δ (τ : ℂ)) (readS δ ((τ : ℂ) - I))
    have n2 := norm_sub_le (readS δ ((τ : ℂ) + I)) (2 * readS δ (τ : ℂ))
    have n3 : ‖(2 : ℂ) * readS δ (τ : ℂ)‖ = 2 * ‖readS δ (τ : ℂ)‖ := by simp
    have q1 : Q * Real.exp (K₂ * (τ - 1)) ≤ Q * Real.exp (K₂ * τ) :=
      mul_le_mul_of_nonneg_left hexp1 hQ0
    have q2 : η ≤ Q * Real.exp (K₂ * τ) := by nlinarith
    linarith
  have hsinh : ‖Complex.sinh ((π : ℂ) * (τ : ℂ))‖ ≤ Real.exp (π * τ) := by
    refine (norm_sinh_le _).trans (le_of_eq ?_)
    congr 1
    rw [Complex.re_ofReal_mul, Complex.ofReal_re, abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hτ0]
  have hcube : ‖Complex.sinh ((π : ℂ) * (τ : ℂ)) ^ 3‖ ≤ Real.exp (3 * π * τ) := by
    rw [norm_pow]
    refine (pow_le_pow_left₀ (norm_nonneg _) hsinh 3).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [norm_mul, ← hK₂, ← hQ]
  calc _ ≤ Real.exp (3 * π * τ) * (4 * Q * Real.exp (K₂ * τ)) :=
        mul_le_mul hcube hdiff (norm_nonneg _) (Real.exp_pos _).le
    _ = 4 * Q * (Real.exp (3 * π * τ) * Real.exp (K₂ * τ)) := by ring
    _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring

end Reading

/-- `(−cos(π/12) + i sin(π/12))` at the apex `cot(π/12) L` reaches `iL`. -/
theorem rayPt_target (L : ℝ) {s c : ℝ} (hs : s = Real.sin (π / 12)) (hc : c = Real.cos (π / 12))
    (hs0 : 0 < s) : rayPt (c / s * L) (L / s) (11 * π / 12) = I * L := by
  have e : (11 * π / 12 : ℝ) = π - π / 12 := by ring
  unfold rayPt
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, e, Real.cos_pi_sub,
    Real.sin_pi_sub, ← hs, ← hc]
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  push_cast
  field_simp
  ring

theorem cot_pi_div_twelve_ge : 3 * Real.sin (π / 12) ≤ Real.cos (π / 12) := by
  have hpi := Real.pi_gt_three
  have hpi2 := Real.pi_lt_d2
  have h1 : Real.sin (π / 12) ≤ π / 12 := Real.sin_le (by positivity)
  have h2 := Real.one_sub_sq_div_two_le_cos (x := π / 12)
  nlinarith

/-- The growth of `T` on all of a sector, from its size on the plane. -/
theorem norm_poleT_rayPt_le {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hb : ∀ w, ‖sinhQuot w‖ * (1 + ‖w‖) ≤ C₀ * Real.exp (π * |w.re|)) {δ : ℕ → ℝ} {V : ℝ}
    (hV0 : 0 ≤ V) (hδ : ∀ n, 1 ≤ n → |δ n| ≤ V * Real.sqrt n) {a r : ℝ} (ha0 : 0 ≤ a) (hr : 0 ≤ r)
    (α : ℝ) :
    ‖poleT δ (rayPt a r α)‖ ≤ (18 * V * (∑' p, indexWeight p) * C₀ ^ 3 *
      Real.exp (1 + (3 * π + 1) * a)) * Real.exp ((3 * π + 1) * r) := by
  have hpi := Real.pi_pos
  have hn := norm_rayPt_le ha0 hr α
  obtain ⟨y, hy⟩ : ∃ y, y = a + r := ⟨_, rfl⟩
  rw [← hy] at hn
  have hy0 : 0 ≤ y := by rw [hy]; linarith
  have hW0 : 0 ≤ ∑' p, indexWeight p := tsum_nonneg indexWeight_nonneg
  have hre : |(rayPt a r α).re| ≤ y := (Complex.abs_re_le_norm _).trans hn
  have h1 : C₀ * Real.exp (π * |(rayPt a r α).re|) * (1 + ‖rayPt a r α‖) ≤
      C₀ * Real.exp (π * y) * (1 + y) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₀) (by linarith)
      (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left hre hpi.le
  have h2 := pow_le_pow_left₀ (by positivity) h1 3
  have h3 := one_add_pow_le hy0
  have e2 : Real.exp (π * y) ^ 3 = Real.exp (3 * π * y) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h4 : (C₀ * Real.exp (π * y) * (1 + y)) ^ 3 ≤
      C₀ ^ 3 * Real.exp (3 * π * y) * (6 * Real.exp (1 + y)) := by
    rw [mul_pow, mul_pow, e2]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  refine (norm_poleT_le hC₀ hb hV0 hδ (rayPt a r α)).trans ?_
  have h5 : V * (3 * (C₀ * Real.exp (π * |(rayPt a r α).re|) * (1 + ‖rayPt a r α‖)) ^ 3) *
      (∑' p, indexWeight p) ≤
      V * (3 * (C₀ ^ 3 * Real.exp (3 * π * y) * (6 * Real.exp (1 + y)))) * (∑' p, indexWeight p) := by
    have h6 := h2.trans h4
    gcongr
  refine h5.trans (le_of_eq ?_)
  have e3 : Real.exp (3 * π * y) * Real.exp (1 + y) =
      Real.exp (1 + (3 * π + 1) * a) * Real.exp ((3 * π + 1) * r) := by
    rw [← Real.exp_add, ← Real.exp_add, hy]
    congr 1
    ring
  calc V * (3 * (C₀ ^ 3 * Real.exp (3 * π * y) * (6 * Real.exp (1 + y)))) * (∑' p, indexWeight p)
      = 18 * V * (∑' p, indexWeight p) * C₀ ^ 3 * (Real.exp (3 * π * y) * Real.exp (1 + y)) := by ring
    _ = _ := by rw [e3]; ring

/-- The rate of the first step. -/
def rayRate : ℝ := 1 / Real.cos (3 * π / 8 / 2)

theorem rayRate_nonneg : 0 ≤ rayRate := by
  have := cos_half_pos three_pi_div_eight_lt.1 three_pi_div_eight_lt.2
  unfold rayRate
  positivity

theorem sector_two_angles : (0 : ℝ) < 23 * π / 24 ∧ 23 * π / 24 < π := by
  have := Real.pi_pos
  constructor <;> linarith

/-- The rate of the second step. -/
def poleRate : ℝ := (3 * π + 1 + rayRate) / Real.cos (23 * π / 24 / 2)

theorem poleRate_nonneg : 0 ≤ poleRate := by
  have := cos_half_pos sector_two_angles.1 sector_two_angles.2
  have := rayRate_nonneg
  have := Real.pi_pos
  unfold poleRate
  positivity

/-- **Second step.** The three lines theorem on the sector of angle `23π/24` from the apex `a ≥ 3`, at the
angle `11π/12`. -/
theorem norm_poleT_sector {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hb : ∀ w, ‖sinhQuot w‖ * (1 + ‖w‖) ≤ C₀ * Real.exp (π * |w.re|)) {δ : ℕ → ℝ} {V η : ℝ}
    (hV : 1 ≤ V) (hη : 0 < η) (hη1 : η ≤ 1) (hδ : ∀ n, 1 ≤ n → |δ n| ≤ V * Real.sqrt n)
    (hS : ∀ t : ℝ, 2 ≤ t → ‖readS δ t‖ ≤ η) {a r : ℝ} (ha : 3 ≤ a) (hr : 0 < r) :
    ‖poleT δ (rayPt a r (11 * π / 12))‖ ≤
      (4 * (η ^ (1 / 3 : ℝ) * (189 * V * ∑' p, indexWeight p) ^ (2 / 3 : ℝ)) *
        Real.exp ((3 * π + rayRate) * a)) ^ (1 / 23 : ℝ) *
      (18 * V * (∑' p, indexWeight p) * C₀ ^ 3 * Real.exp (1 + (3 * π + 1) * a)) ^ (22 / 23 : ℝ) *
      Real.exp (poleRate * r) := by
  have hpi := Real.pi_pos
  have hV0 : 0 ≤ V := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hR := rayRate_nonneg
  obtain ⟨hφ₂, hφ₂'⟩ := sector_two_angles
  obtain ⟨M₂, hM₂⟩ : ∃ M₂, M₂ = 18 * V * (∑' p, indexWeight p) * C₀ ^ 3 *
    Real.exp (1 + (3 * π + 1) * a) := ⟨_, rfl⟩
  have hbound : ∀ r α : ℝ, 0 < r → α ∈ Icc (0 : ℝ) (23 * π / 24) →
      ‖poleT δ (rayPt a r α)‖ ≤ M₂ * Real.exp ((3 * π + 1 + rayRate) * r) := by
    intro r α hr _
    have hW0 : 0 ≤ ∑' p, indexWeight p := tsum_nonneg indexWeight_nonneg
    have hM₂0 : 0 ≤ M₂ := by rw [hM₂]; positivity
    refine (norm_poleT_rayPt_le hC₀ hb hV0 hδ ha0 hr.le α).trans ?_
    rw [← hM₂]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM₂0
    exact mul_le_mul_of_nonneg_right (by linarith) hr.le
  have hray : ∀ r : ℝ, 0 < r → ‖poleT δ (rayPt a r 0)‖ ≤
      (4 * (η ^ (1 / 3 : ℝ) * (189 * V * ∑' p, indexWeight p) ^ (2 / 3 : ℝ)) *
        Real.exp ((3 * π + rayRate) * a)) * Real.exp ((3 * π + 1 + rayRate) * r) := by
    intro r hr
    rw [rayPt_zero]
    refine (norm_poleT_ofReal_le hV hη hη1 hδ hS (τ := a + r) (by linarith)).trans ?_
    have e : Real.exp ((3 * π + 1 / Real.cos (3 * π / 8 / 2)) * (a + r)) =
        Real.exp ((3 * π + rayRate) * a) * Real.exp ((3 * π + rayRate) * r) := by
      rw [← Real.exp_add]
      congr 1
      unfold rayRate
      ring
    rw [e, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
      (Real.exp_pos _).le) ?_
    · exact mul_le_mul_of_nonneg_right (by linarith) hr.le
    · have hW1 : 0 ≤ ∑' p, indexWeight p := tsum_nonneg indexWeight_nonneg
      positivity
  have hK : 0 ≤ 3 * π + 1 + rayRate := by positivity
  have hmain := norm_le_of_sector (F := poleT δ) (a := a) (K := 3 * π + 1 + rayRate)
    (M₀ := 4 * (η ^ (1 / 3 : ℝ) * (189 * V * ∑' p, indexWeight p) ^ (2 / 3 : ℝ)) *
        Real.exp ((3 * π + rayRate) * a)) (M₁ := M₂) (A := M₂) hφ₂ hφ₂' hK
    (fun r α _ _ => differentiable_poleT hC₀ hb hV0 hδ _)
    hbound hray (fun r hr => hbound r _ hr ⟨hφ₂.le, le_rfl⟩)
    hr (α := 11 * π / 12) ⟨by positivity, by linarith⟩
  have hx : (11 * π / 12) / (23 * π / 24) = 22 / 23 := by
    field_simp
    norm_num
  have hsplit : (1 : ℝ) - 22 / 23 = 1 / 23 := by norm_num
  rw [hx, hsplit, hM₂] at hmain
  exact hmain

/-- The arithmetic of the exponents. -/
theorem rpow_arith {Q₀ M₂ Z η E : ℝ} (hQ₀ : 0 ≤ Q₀) (hQZ : Q₀ ≤ Z) (hM₂ : 0 ≤ M₂) (hMZ : M₂ ≤ Z)
    (hη : 0 < η) (hE : 1 ≤ E) :
    (Q₀ * (η ^ (1 / 3 : ℝ) * E)) ^ (1 / 23 : ℝ) * M₂ ^ (22 / 23 : ℝ) ≤ Z * (η ^ (1 / 69 : ℝ) * E) := by
  have hE0 : 0 ≤ E := by linarith
  have hZ0 : 0 ≤ Z := hQ₀.trans hQZ
  have hηp : 0 < η ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hη _
  rw [Real.mul_rpow hQ₀ (by positivity), Real.mul_rpow hηp.le hE0, ← Real.rpow_mul hη.le]
  have e2 : (1 / 3 : ℝ) * (1 / 23) = 1 / 69 := by norm_num
  rw [e2]
  have h1 : Q₀ ^ (1 / 23 : ℝ) ≤ Z ^ (1 / 23 : ℝ) := Real.rpow_le_rpow hQ₀ hQZ (by norm_num)
  have h2 : M₂ ^ (22 / 23 : ℝ) ≤ Z ^ (22 / 23 : ℝ) := Real.rpow_le_rpow hM₂ hMZ (by norm_num)
  have h3 : E ^ (1 / 23 : ℝ) ≤ E := by
    have := Real.rpow_le_rpow_of_exponent_le hE (show (1 / 23 : ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have hZZ : Z ^ (1 / 23 : ℝ) * Z ^ (22 / 23 : ℝ) ≤ Z := by
    rcases hZ0.lt_or_eq with hpos | hzero
    · rw [← Real.rpow_add hpos]
      norm_num
    · rw [← hzero, Real.zero_rpow (by norm_num)]
      simp
  have hη69 : 0 ≤ η ^ (1 / 69 : ℝ) := by positivity
  have hprod : Q₀ ^ (1 / 23 : ℝ) * M₂ ^ (22 / 23 : ℝ) ≤ Z :=
    le_trans (mul_le_mul h1 h2 (by positivity) (by positivity)) hZZ
  have hE23 : 0 ≤ E ^ (1 / 23 : ℝ) := by positivity
  calc Q₀ ^ (1 / 23 : ℝ) * (η ^ (1 / 69 : ℝ) * E ^ (1 / 23 : ℝ)) * M₂ ^ (22 / 23 : ℝ)
      = (Q₀ ^ (1 / 23 : ℝ) * M₂ ^ (22 / 23 : ℝ)) * (η ^ (1 / 69 : ℝ) * E ^ (1 / 23 : ℝ)) := by ring
    _ ≤ Z * (η ^ (1 / 69 : ℝ) * E) :=
        mul_le_mul hprod (mul_le_mul_of_nonneg_left h3 hη69) (by positivity) hZ0

/-- **Smallness on the ray reaches the poles.** -/
theorem exists_poleT_I_le :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ (δ : ℕ → ℝ) (V η : ℝ), 1 ≤ V → 0 < η → η ≤ 1 →
      (∀ n, 1 ≤ n → |δ n| ≤ V * Real.sqrt n) → (∀ t : ℝ, 2 ≤ t → ‖readS δ t‖ ≤ η) →
      ∀ L : ℕ, 1 ≤ L → ‖poleT δ (I * L)‖ ≤ C * V * η ^ (1 / 69 : ℝ) * Real.exp (K * L) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_norm_sinhQuot_le
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  obtain ⟨W, hW⟩ : ∃ W, W = ∑' p, indexWeight p := ⟨_, rfl⟩
  have hW1 : 1 ≤ W := by
    have h := summable_indexWeight.le_tsum (0, 0) (fun j _ => indexWeight_nonneg j)
    have e : indexWeight (0, 0) = 1 := by simp [indexWeight]
    rwa [e, ← hW] at h
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sin (π / 12) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = Real.cos (π / 12) := ⟨_, rfl⟩
  have hs0 : 0 < s := by
    rw [hs]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hcs : 3 * s ≤ c := by rw [hs, hc]; exact cot_pi_div_twelve_ge
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = c / s := ⟨_, rfl⟩
  have hℓ3 : 3 ≤ ℓ := by rw [hℓ, le_div_iff₀ hs0]; exact hcs
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hR := rayRate_nonneg
  have hP := poleRate_nonneg
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀, Z₀ = 756 * W + 18 * W * C₀ ^ 3 * Real.exp 1 := ⟨_, rfl⟩
  have hZ₀0 : 0 ≤ Z₀ := by rw [hZ₀]; positivity
  refine ⟨Z₀, (3 * π + 1) * ℓ + (3 * π + rayRate) * ℓ + poleRate / s, hZ₀0, by positivity, ?_⟩
  intro δ V η hV hη hη1 hδ hS L hL
  have hV0 : 0 ≤ V := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨a, ha⟩ : ∃ a, a = ℓ * L := ⟨_, rfl⟩
  have ha3 : 3 ≤ a := by rw [ha]; nlinarith
  have ha0 : 0 ≤ a := by linarith
  have hmain := norm_poleT_sector hC₀ hb hV hη hη1 hδ hS ha3 (r := L / s) (by positivity)
  have htarget : rayPt a (L / s) (11 * π / 12) = I * L := by
    rw [ha, hℓ]
    exact rayPt_target L hs hc hs0
  rw [htarget, ← hW] at hmain
  refine hmain.trans ?_
  obtain ⟨M, hM⟩ : ∃ M, M = 189 * V * W := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith
  rw [← hM]
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀, Q₀ = 4 * M ^ (2 / 3 : ℝ) := ⟨_, rfl⟩
  have hQ₀0 : 0 ≤ Q₀ := by rw [hQ₀]; positivity
  obtain ⟨M₂, hM₂⟩ : ∃ M₂, M₂ = 18 * V * W * C₀ ^ 3 * Real.exp (1 + (3 * π + 1) * a) := ⟨_, rfl⟩
  have hM₂0 : 0 ≤ M₂ := by rw [hM₂]; positivity
  rw [← hM₂]
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = Z₀ * V * Real.exp ((3 * π + 1) * a) := ⟨_, rfl⟩
  have hexpa : 1 ≤ Real.exp ((3 * π + 1) * a) := Real.one_le_exp (by positivity)
  have hQ₀Z : Q₀ ≤ Z := by
    have h1 : M ^ (2 / 3 : ℝ) ≤ M := by
      have := Real.rpow_le_rpow_of_exponent_le hM1 (show (2 / 3 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have h2 : Q₀ ≤ 756 * W * V := by rw [hQ₀]; rw [hM] at h1 ⊢; linarith
    have h3 : 756 * W * V ≤ Z₀ * V := by
      refine mul_le_mul_of_nonneg_right ?_ hV0
      rw [hZ₀]
      have : 0 ≤ 18 * W * C₀ ^ 3 * Real.exp 1 := by positivity
      linarith
    have h4 : Z₀ * V ≤ Z := by
      rw [hZ]
      exact le_mul_of_one_le_right (by positivity) hexpa
    linarith
  have hM₂Z : M₂ ≤ Z := by
    have e : M₂ = 18 * W * C₀ ^ 3 * Real.exp 1 * V * Real.exp ((3 * π + 1) * a) := by
      rw [hM₂, Real.exp_add]
      ring
    rw [e, hZ]
    have hle : 18 * W * C₀ ^ 3 * Real.exp 1 ≤ Z₀ := by
      rw [hZ₀]
      have : 0 ≤ 756 * W := by positivity
      linarith
    gcongr
  have e1 : 4 * (η ^ (1 / 3 : ℝ) * M ^ (2 / 3 : ℝ)) * Real.exp ((3 * π + rayRate) * a) =
      Q₀ * (η ^ (1 / 3 : ℝ) * Real.exp ((3 * π + rayRate) * a)) := by
    rw [hQ₀]
    ring
  rw [e1]
  have hE1 : 1 ≤ Real.exp ((3 * π + rayRate) * a) := Real.one_le_exp (by positivity)
  have har := rpow_arith hQ₀0 hQ₀Z hM₂0 hM₂Z hη hE1
  refine (mul_le_mul_of_nonneg_right har (Real.exp_pos _).le).trans (le_of_eq ?_)
  rw [hZ]
  have hexp : Real.exp (((3 * π + 1) * ℓ + (3 * π + rayRate) * ℓ + poleRate / s) * L) =
      Real.exp ((3 * π + 1) * a) * Real.exp ((3 * π + rayRate) * a) *
        Real.exp (poleRate * (L / s)) := by
    rw [← Real.exp_add, ← Real.exp_add, ha]
    congr 1
    field_simp
  rw [hexp]
  ring

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
