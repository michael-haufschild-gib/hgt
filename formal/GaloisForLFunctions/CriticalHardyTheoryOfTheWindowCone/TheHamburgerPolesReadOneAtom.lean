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
    ((hasDerivAt_id (0 : ℂ)).const_mul (π : ℂ)).sinh
  rw [h.deriv]
  simp

theorem sinhQuot_I_mul_int {k : ℤ} (hk : k ≠ 0) : sinhQuot (I * k) = 0 := by
  have h := mul_sinhQuot (I * k)
  have hs : Complex.sinh ((π : ℂ) * (I * k)) = 0 := by
    rw [show (π : ℂ) * (I * k) = ((k : ℂ) * π) * I by ring, Complex.sinh_mul_I,
      Complex.sin_int_mul_pi, mul_zero]
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

theorem sinh_eq_mul_sincAt (M : ℤ) (t : ℂ) :
    Complex.sinh ((π : ℂ) * t) = (t - I * M) * sincAt M t := by
  have h := mul_sinhQuot (t - I * M)
  have e : Complex.sinh ((π : ℂ) * (t - I * M)) = Complex.sinh ((π : ℂ) * t) * (-1 : ℂ) ^ M := by
    rw [show (π : ℂ) * (t - I * M) = (π : ℂ) * t - ((M : ℂ) * π) * I by ring, Complex.sinh_sub,
      Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.cos_int_mul_pi, Complex.sin_int_mul_pi]
    ring
  rw [e] at h
  unfold sincAt
  have h2 := neg_one_zpow_mul_self M
  calc Complex.sinh ((π : ℂ) * t)
      = Complex.sinh ((π : ℂ) * t) * ((-1 : ℂ) ^ M * (-1 : ℂ) ^ M) := by rw [h2, mul_one]
    _ = (Complex.sinh ((π : ℂ) * t) * (-1 : ℂ) ^ M) * (-1 : ℂ) ^ M := by ring
    _ = ((t - I * M) * sinhQuot (t - I * M)) * (-1 : ℂ) ^ M := by rw [h]
    _ = _ := by ring

theorem norm_sincAt_le {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
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
    linear_combination -this
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

end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
