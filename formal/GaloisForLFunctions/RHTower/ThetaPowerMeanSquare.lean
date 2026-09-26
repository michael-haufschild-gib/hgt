import GaloisForLFunctions.RHTower.ThetaPowerShiftDifferenceBound
import GaloisForLFunctions.RHTower.ThetaPowerDirichletSplit
import GaloisForLFunctions.RHTower.StripHorizontalShift
import GaloisForLFunctions.HTGeometry.PlancherelInequalityReal
import GaloisForLFunctions.HTGeometry.GammaVerticalSharpBound

/-!
# Mean square of the Dirichlet error of the theta-power family

With `H(τ) = F_a(τ) - F_a(τ+iδ)`, `M(z) - M_δ(z) = ∫₀^∞ H(iy) y^{z-1} dy`.  In log coordinates this is
`2 ∫ e^{2zx} H(i e^{2x}) dx`; shifting the line to `Im = c < π/4` rotates the ray to angle `π/2 + 2c` and
gives `M - M_δ = 2 e^{2izc} Ĝ_c(2t)` with `G_c(x) = e^{2σx} H(i e^{2x+2ic})`.  The Plancherel inequality and
`|H(τ)| ≤ K δ^η (Im τ)^{-1/4-η} e^{-(πa/16) Im τ}` bound `∫ |M - M_δ|² e^{4ct} dt`; with `4c = π - 2/T` and the
sharp vertical bound for `1/Γ`, `∫_T^{2T} |E^δ(σ+it)|² dt ≤ C δ^{2η} T`.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {a : ℝ}

/-- `H(τ) = F_a(τ) - F_a(τ+iδ)`. -/
def thetaPowerShiftDiff (a δ : ℝ) (τ : ℂ) : ℂ := thetaPowerForm a τ - thetaPowerForm a (τ + δ * I)

/-- The rotated line function `G_c(x) = e^{2σx} H(i e^{2x+2ic})`. -/
def thetaPowerRotatedLine (a δ σ c : ℝ) (x : ℝ) : ℂ :=
  ((Real.exp (2 * σ * x) : ℝ) : ℂ) * thetaPowerShiftDiff a δ (I * Complex.exp (2 * x + 2 * c * I))

theorem im_I_mul_cexp (w : ℂ) : (I * Complex.exp w).im = Real.exp w.re * Real.cos w.im := by
  simp [Complex.exp_re]

theorem differentiableAt_thetaPowerShiftDiff (a δ : ℝ) (hδ : 0 ≤ δ) {τ : ℂ} (hτ : 0 < τ.im) :
    DifferentiableAt ℂ (thetaPowerShiftDiff a δ) τ := by
  have h1 : τ ∈ modUpperSet := hτ
  have h2 : τ + δ * I ∈ modUpperSet := by show 0 < (τ + δ * I).im; simp; linarith
  have hF := differentiableOn_thetaPowerForm a
  have hc : DifferentiableAt ℂ (fun σ : ℂ => thetaPowerForm a (σ + δ * I)) τ :=
    DifferentiableAt.comp (g := thetaPowerForm a) (f := fun σ : ℂ => σ + δ * I) τ
      (hF.differentiableAt (isOpen_modUpperSet.mem_nhds h2)) (differentiableAt_id.add_const _)
  exact (hF.differentiableAt (isOpen_modUpperSet.mem_nhds h1)).sub hc

/-- `Mellin` convergence of `F_a(iy)` for `Re z > 1/4`. -/
theorem mellinConvergent_thetaPowerForm (ha0 : 0 < a) (ha1 : a < 1 / 2) {z : ℂ} (hz : 1 / 4 < z.re) :
    MellinConvergent (fun y : ℝ => thetaPowerForm a (I * (y : ℂ))) z := by
  have hC1 := thetaPowerEnvelopeConstant_nonneg ha0 ha1
  have hdom : IntegrableOn (fun y : ℝ => thetaPowerEnvelopeConstant a *
      (y ^ (z.re - 5 / 4) * Real.exp (-(π * a / 8) * y ^ (1 : ℝ)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := z.re - 5 / 4) (b := π * a / 8)
      (by linarith) le_rfl (by positivity)).const_mul _
  have hcont : ContinuousOn (fun y : ℝ => (y : ℂ) ^ (z - 1) • thetaPowerForm a (I * (y : ℂ))) (Ioi 0) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hmem : I * (y : ℂ) ∈ modUpperSet := by show 0 < (I * (y : ℂ)).im; simpa using hy0
    refine ContinuousAt.continuousWithinAt ?_
    refine (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hy0.ne')).smul ?_
    exact ContinuousAt.comp (g := thetaPowerForm a) (f := fun y : ℝ => I * (y : ℂ))
      ((differentiableOn_thetaPowerForm a).differentiableAt (isOpen_modUpperSet.mem_nhds hmem)).continuousAt
      (by fun_prop)
  refine Integrable.mono' hdom (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have hτ : 0 < (I * (y : ℂ)).im := by simpa using hy0
  have henv := norm_thetaPowerForm_le_envelope ha0 ha1 hτ
  have him : (I * (y : ℂ)).im = y := by simp
  rw [him] at henv
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
  simp only [Complex.sub_re, Complex.one_re, Real.rpow_one]
  calc y ^ (z.re - 1) * ‖thetaPowerForm a (I * (y : ℂ))‖
      ≤ y ^ (z.re - 1) * (thetaPowerEnvelopeConstant a * y ^ (-(1 / 4 : ℝ)) *
          Real.exp (-(π * a / 8 * y))) := by gcongr
    _ = thetaPowerEnvelopeConstant a * (y ^ (z.re - 5 / 4) * Real.exp (-(π * a / 8) * y)) := by
        rw [show z.re - 5 / 4 = (z.re - 1) + (-(1 / 4)) by ring, Real.rpow_add hy0]
        rw [show -(π * a / 8 * y) = -(π * a / 8) * y by ring]; ring

/-- `Mellin` convergence of `F_a(i(y+δ))` for `Re z > 0`. -/
theorem mellinConvergent_thetaPowerForm_shift (ha0 : 0 < a) (ha1 : a < 1 / 2) {δ : ℝ} (hδ : 0 < δ)
    {z : ℂ} (hz : 0 < z.re) :
    MellinConvergent (fun y : ℝ => thetaPowerForm a (I * ((y + δ : ℝ) : ℂ))) z := by
  have hC1 := thetaPowerEnvelopeConstant_nonneg ha0 ha1
  set K : ℝ := thetaPowerEnvelopeConstant a * δ ^ (-(1 / 4 : ℝ))
  have hdom : IntegrableOn (fun y : ℝ => K * (y ^ (z.re - 1) * Real.exp (-(π * a / 8) * y ^ (1 : ℝ))))
      (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := z.re - 1) (b := π * a / 8)
      (by linarith) le_rfl (by positivity)).const_mul _
  have hcont : ContinuousOn (fun y : ℝ => (y : ℂ) ^ (z - 1) • thetaPowerForm a (I * ((y + δ : ℝ) : ℂ)))
      (Ioi 0) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hmem : I * ((y + δ : ℝ) : ℂ) ∈ modUpperSet := by
      show 0 < (I * ((y + δ : ℝ) : ℂ)).im; simp; linarith
    refine ContinuousAt.continuousWithinAt ?_
    refine (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hy0.ne')).smul ?_
    exact ContinuousAt.comp (g := thetaPowerForm a) (f := fun y : ℝ => I * ((y + δ : ℝ) : ℂ))
      ((differentiableOn_thetaPowerForm a).differentiableAt (isOpen_modUpperSet.mem_nhds hmem)).continuousAt
      (by fun_prop)
  refine Integrable.mono' hdom (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have hτ : 0 < (I * ((y + δ : ℝ) : ℂ)).im := by simp; linarith
  have henv := norm_thetaPowerForm_le_envelope ha0 ha1 hτ
  have him : (I * ((y + δ : ℝ) : ℂ)).im = y + δ := by simp
  rw [him] at henv
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
  simp only [Complex.sub_re, Complex.one_re, Real.rpow_one]
  have h1 : (y + δ) ^ (-(1 / 4 : ℝ)) ≤ δ ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hδ (by linarith) (by norm_num)
  have h2 : Real.exp (-(π * a / 8 * (y + δ))) ≤ Real.exp (-(π * a / 8) * y) :=
    Real.exp_le_exp.mpr (by nlinarith [show 0 ≤ π * a / 8 * δ by positivity])
  calc y ^ (z.re - 1) * ‖thetaPowerForm a (I * ((y + δ : ℝ) : ℂ))‖
      ≤ y ^ (z.re - 1) * (thetaPowerEnvelopeConstant a * (y + δ) ^ (-(1 / 4 : ℝ)) *
          Real.exp (-(π * a / 8 * (y + δ)))) := by gcongr
    _ ≤ y ^ (z.re - 1) * (thetaPowerEnvelopeConstant a * δ ^ (-(1 / 4 : ℝ)) *
          Real.exp (-(π * a / 8) * y)) := by gcongr
    _ = K * (y ^ (z.re - 1) * Real.exp (-(π * a / 8) * y)) := by ring

/-- `M - M_δ` is the Mellin transform of `H(iy)`, written in log coordinates. -/
theorem thetaPowerMellin_sub_shift_eq (ha0 : 0 < a) (ha1 : a < 1 / 2) {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : 1 / 4 < z.re) :
    thetaPowerMellin a z - thetaPowerShiftMellin a δ z =
      2 * ∫ x : ℝ, Complex.exp (2 * z * x) * thetaPowerShiftDiff a δ (I * Complex.exp (2 * x)) := by
  have h1 := mellinConvergent_thetaPowerForm ha0 ha1 hz
  have h2 := mellinConvergent_thetaPowerForm_shift ha0 ha1 hδ (z := z) (by linarith)
  have hmel : thetaPowerMellin a z - thetaPowerShiftMellin a δ z =
      mellin (fun y : ℝ => thetaPowerShiftDiff a δ (I * (y : ℂ))) z := by
    unfold thetaPowerMellin thetaPowerShiftMellin mellin
    rw [← integral_sub h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [thetaPowerShiftDiff, smul_eq_mul]
    rw [show I * ((y + δ : ℝ) : ℂ) = I * (y : ℂ) + δ * I by push_cast; ring]
    ring
  rw [hmel]
  have hcv := integral_cexp_mul_comp_exp_two (fun y : ℝ => thetaPowerShiftDiff a δ (I * (y : ℂ))) z
  have hcv' : ∫ x : ℝ, Complex.exp (2 * z * x) * thetaPowerShiftDiff a δ (I * Complex.exp (2 * x)) =
      (1 / 2) * mellin (fun y : ℝ => thetaPowerShiftDiff a δ (I * (y : ℂ))) z := by
    rw [← hcv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [Complex.ofReal_exp]; push_cast; ring_nf
  rw [hcv']; ring

/-- `e^{bu} e^{-λ e^{2u}} ≤ e^{(b+1)²/(8λ)} e^{-min(b,1)|u|}`. -/
theorem exp_mul_exp_neg_exp_le {b lam : ℝ} (hb : 0 < b) (hlam : 0 < lam) (u : ℝ) :
    Real.exp (b * u) * Real.exp (-(lam * Real.exp (2 * u))) ≤
      Real.exp ((b + 1) ^ 2 / (8 * lam)) * Real.exp (-(min b 1 * |u|)) := by
  have hE0 : 0 ≤ (b + 1) ^ 2 / (8 * lam) := by positivity
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmin1 : min b 1 ≤ b := min_le_left _ _
  have hmin2 : min b 1 ≤ 1 := min_le_right _ _
  have hmin0 : 0 < min b 1 := lt_min hb one_pos
  rcases le_total u 0 with hu | hu
  · rw [abs_of_nonpos hu]
    have : 0 ≤ lam * Real.exp (2 * u) := by positivity
    nlinarith
  · rw [abs_of_nonneg hu]
    have he := Real.sum_le_exp_of_nonneg (show 0 ≤ 2 * u by linarith) 3
    norm_num [Finset.sum_range_succ] at he
    have hq : (b + 1) * u - 2 * lam * u ^ 2 ≤ (b + 1) ^ 2 / (8 * lam) := by
      have : 0 ≤ 2 * lam * (u - (b + 1) / (4 * lam)) ^ 2 := by positivity
      have hid : 2 * lam * (u - (b + 1) / (4 * lam)) ^ 2 =
          2 * lam * u ^ 2 - (b + 1) * u + (b + 1) ^ 2 / (8 * lam) := by
        field_simp; ring
      linarith
    nlinarith

/-- **Strip decay** of the log-coordinate integrand `e^{2zw} H(i e^{2w})`. -/
theorem exists_norm_rotatedIntegrand_le (ha0 : 0 < a) (ha1 : a < 1 / 2) {δ η σ t c : ℝ} (hδ : 0 < δ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hσ : 1 / 4 + η < σ) (hc0 : 0 ≤ c) (hc : c < π / 4) :
    ∃ C r : ℝ, 0 < r ∧ ∀ w : ℂ, |w.im| ≤ c →
      ‖Complex.exp (2 * ((σ : ℂ) + t * I) * w) * thetaPowerShiftDiff a δ (I * Complex.exp (2 * w))‖ ≤
        C * Real.exp (-(r * |w.re|)) := by
  set κ : ℝ := Real.cos (2 * c) with hκ
  have hκ0 : 0 < κ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  set b : ℝ := 2 * σ - 1 / 2 - 2 * η with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  set lam : ℝ := π * a / 16 * κ with hlam
  have hlam0 : 0 < lam := by positivity
  set K : ℝ := 3 * thetaPowerEnvelopeConstant a * δ ^ η
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) (thetaPowerEnvelopeConstant_nonneg ha0 ha1))
    (Real.rpow_nonneg hδ.le _)
  refine ⟨K * κ ^ (-(1 / 4 : ℝ) - η) * Real.exp (2 * |t| * c) * Real.exp ((b + 1) ^ 2 / (8 * lam)),
    min b 1, lt_min hb0 one_pos, fun w hw => ?_⟩
  set u := w.re
  have hcos : κ ≤ Real.cos (2 * w.im) := by
    rw [← Real.cos_abs (2 * w.im)]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  have him : (I * Complex.exp (2 * w)).im = Real.exp (2 * u) * Real.cos (2 * w.im) := by
    rw [im_I_mul_cexp]; simp [u]
  have hImlow : Real.exp (2 * u) * κ ≤ (I * Complex.exp (2 * w)).im := by
    rw [him]; exact mul_le_mul_of_nonneg_left hcos (Real.exp_pos _).le
  have hImpos : 0 < (I * Complex.exp (2 * w)).im := lt_of_lt_of_le (by positivity) hImlow
  have hH := norm_thetaPowerForm_sub_shift_le ha0 ha1 hη0 hη1 hδ hImpos
  have hH' : ‖thetaPowerShiftDiff a δ (I * Complex.exp (2 * w))‖ ≤
      K * (Real.exp (2 * u) * κ) ^ (-(1 / 4 : ℝ) - η) * Real.exp (-(lam * Real.exp (2 * u))) := by
    refine hH.trans ?_
    have h1 : (I * Complex.exp (2 * w)).im ^ (-(1 / 4 : ℝ) - η) ≤ (Real.exp (2 * u) * κ) ^ (-(1 / 4 : ℝ) - η) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hImlow (by linarith)
    have h2 : Real.exp (-(π * a / 16 * (I * Complex.exp (2 * w)).im)) ≤ Real.exp (-(lam * Real.exp (2 * u))) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hImlow (show 0 ≤ π * a / 16 by positivity)
      rw [hlam]; nlinarith
    calc 3 * thetaPowerEnvelopeConstant a * δ ^ η * (I * Complex.exp (2 * w)).im ^ (-(1 / 4 : ℝ) - η) *
          Real.exp (-(π * a / 16 * (I * Complex.exp (2 * w)).im))
        = K * (I * Complex.exp (2 * w)).im ^ (-(1 / 4 : ℝ) - η) *
          Real.exp (-(π * a / 16 * (I * Complex.exp (2 * w)).im)) := rfl
      _ ≤ K * (Real.exp (2 * u) * κ) ^ (-(1 / 4 : ℝ) - η) * Real.exp (-(lam * Real.exp (2 * u))) := by
          gcongr
  have hexpz : ‖Complex.exp (2 * ((σ : ℂ) + t * I) * w)‖ ≤ Real.exp (2 * σ * u) * Real.exp (2 * |t| * c) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hre : (2 * ((σ : ℂ) + t * I) * w).re = 2 * σ * u - 2 * t * w.im := by
      simp [Complex.mul_re, u]
    rw [hre]
    have : -(t * w.im) ≤ |t| * c := by
      have h1 : |t * w.im| ≤ |t| * c := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hw (abs_nonneg t)
      linarith [neg_abs_le (t * w.im)]
    linarith
  have hsplit : (Real.exp (2 * u) * κ) ^ (-(1 / 4 : ℝ) - η) =
      κ ^ (-(1 / 4 : ℝ) - η) * Real.exp ((-(1 / 2 : ℝ) - 2 * η) * u) := by
    rw [Real.mul_rpow (Real.exp_pos _).le hκ0.le, ← Real.exp_mul]; rw [mul_comm]; congr 2; ring
  have hkey := exp_mul_exp_neg_exp_le hb0 hlam0 u
  rw [norm_mul]
  calc ‖Complex.exp (2 * ((σ : ℂ) + t * I) * w)‖ * ‖thetaPowerShiftDiff a δ (I * Complex.exp (2 * w))‖
      ≤ (Real.exp (2 * σ * u) * Real.exp (2 * |t| * c)) *
          (K * (Real.exp (2 * u) * κ) ^ (-(1 / 4 : ℝ) - η) * Real.exp (-(lam * Real.exp (2 * u)))) :=
        mul_le_mul hexpz hH' (norm_nonneg _) (by positivity)
    _ = K * κ ^ (-(1 / 4 : ℝ) - η) * Real.exp (2 * |t| * c) *
          (Real.exp (b * u) * Real.exp (-(lam * Real.exp (2 * u)))) := by
        rw [hsplit]
        have : Real.exp (2 * σ * u) * Real.exp ((-(1 / 2 : ℝ) - 2 * η) * u) = Real.exp (b * u) := by
          rw [← Real.exp_add]; congr 1; rw [hb]; ring
        calc Real.exp (2 * σ * u) * Real.exp (2 * |t| * c) *
              (K * (κ ^ (-(1 / 4 : ℝ) - η) * Real.exp ((-(1 / 2 : ℝ) - 2 * η) * u)) *
                Real.exp (-(lam * Real.exp (2 * u))))
            = K * κ ^ (-(1 / 4 : ℝ) - η) * Real.exp (2 * |t| * c) *
              ((Real.exp (2 * σ * u) * Real.exp ((-(1 / 2 : ℝ) - 2 * η) * u)) *
                Real.exp (-(lam * Real.exp (2 * u)))) := by ring
          _ = _ := by rw [this]
    _ ≤ K * κ ^ (-(1 / 4 : ℝ) - η) * Real.exp (2 * |t| * c) *
          (Real.exp ((b + 1) ^ 2 / (8 * lam)) * Real.exp (-(min b 1 * |u|))) := by
        gcongr
    _ = _ := by ring

/-- **Rotated representation** `M(z) - M_δ(z) = 2 e^{2izc} Ĝ_c(2t)`, `z = σ + it`. -/
theorem thetaPowerMellin_sub_shift_rotated (ha0 : 0 < a) (ha1 : a < 1 / 2) {δ η σ t c : ℝ} (hδ : 0 < δ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hσ : 1 / 4 + η < σ) (hc0 : 0 ≤ c) (hc : c < π / 4) :
    thetaPowerMellin a ((σ : ℂ) + t * I) - thetaPowerShiftMellin a δ ((σ : ℂ) + t * I) =
      2 * Complex.exp (2 * ((σ : ℂ) + t * I) * (c * I)) *
        angularFourier (thetaPowerRotatedLine a δ σ c) (2 * t) := by
  have hz : 1 / 4 < ((σ : ℂ) + t * I).re := by simp; linarith
  rw [thetaPowerMellin_sub_shift_eq ha0 ha1 hδ hz]
  obtain ⟨C, r, hr, hbound⟩ := exists_norm_rotatedIntegrand_le ha0 ha1 (t := t) hδ hη0 hη1 hσ hc0 hc
  set f : ℂ → ℂ := fun w => Complex.exp (2 * ((σ : ℂ) + t * I) * w) *
    thetaPowerShiftDiff a δ (I * Complex.exp (2 * w)) with hf
  have hdiff : ∀ w : ℂ, |w.im| ≤ c → DifferentiableAt ℂ f w := by
    intro w hw
    have hcos : 0 < Real.cos (2 * w.im) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> nlinarith [abs_le.mp hw, Real.pi_pos]
    have hpos : 0 < (I * Complex.exp (2 * w)).im := by rw [im_I_mul_cexp]; simp; positivity
    have hH := differentiableAt_thetaPowerShiftDiff a δ hδ.le hpos
    exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (2 * ((σ : ℂ) + t * I) * w)) w).mul
      (DifferentiableAt.comp (g := thetaPowerShiftDiff a δ) (f := fun w : ℂ => I * Complex.exp (2 * w))
        w hH (by fun_prop))
  have hshift := integral_horizontal_shift_of_decay (F := f) hc0 hr hdiff hbound
  have hline : ∫ x : ℝ, Complex.exp (2 * ((σ : ℂ) + t * I) * x) *
      thetaPowerShiftDiff a δ (I * Complex.exp (2 * x)) = ∫ x : ℝ, f (x : ℂ) := rfl
  rw [hline, ← hshift]
  unfold angularFourier thetaPowerRotatedLine
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hf]
  have h1 : Complex.exp (2 * ((σ : ℂ) + t * I) * ((x : ℂ) + (c : ℂ) * I)) =
      Complex.exp (2 * ((σ : ℂ) + t * I) * (c * I)) * (Complex.exp (I * ((2 * t : ℝ) : ℂ) * x) *
        ((Real.exp (2 * σ * x) : ℝ) : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  have h2 : Complex.exp (2 * ((x : ℂ) + (c : ℂ) * I)) = Complex.exp (2 * x + 2 * c * I) := by
    congr 1; ring
  rw [h1, h2]; ring

/-- Exponential decay of the rotated line function. -/
theorem exists_norm_rotatedLine_le (ha0 : 0 < a) (ha1 : a < 1 / 2) {δ η σ c : ℝ} (hδ : 0 < δ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hσ : 1 / 4 + η < σ) (hc0 : 0 ≤ c) (hc : c < π / 4) :
    ∃ C r : ℝ, 0 < r ∧ ∀ x : ℝ, ‖thetaPowerRotatedLine a δ σ c x‖ ≤ C * Real.exp (-(r * |x|)) := by
  obtain ⟨C, r, hr, hb⟩ := exists_norm_rotatedIntegrand_le ha0 ha1 (t := 0) hδ hη0 hη1 hσ hc0 hc
  refine ⟨C, r, hr, fun x => ?_⟩
  have h := hb ((x : ℂ) + c * I) (by simp [abs_of_nonneg hc0])
  have hre : ((x : ℂ) + c * I).re = x := by simp
  rw [hre] at h
  refine le_of_eq_of_le ?_ h
  unfold thetaPowerRotatedLine
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have h1 : (2 * ((σ : ℂ) + (0 : ℝ) * I) * ((x : ℂ) + c * I)).re = 2 * σ * x := by simp
  have h2 : Complex.exp (2 * ((x : ℂ) + c * I)) = Complex.exp (2 * x + 2 * c * I) := by congr 1; ring
  rw [h1, h2]

theorem continuous_thetaPowerRotatedLine {δ σ c : ℝ} (hδ : 0 ≤ δ) (hc : |c| < π / 4) :
    Continuous (thetaPowerRotatedLine a δ σ c) := by
  unfold thetaPowerRotatedLine
  refine (by fun_prop : Continuous fun x : ℝ => ((Real.exp (2 * σ * x) : ℝ) : ℂ)).mul ?_
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hpos : 0 < (I * Complex.exp (2 * (x : ℂ) + 2 * c * I)).im := by
    rw [im_I_mul_cexp]
    have hre : (2 * (x : ℂ) + 2 * c * I).re = 2 * x := by simp
    have him : (2 * (x : ℂ) + 2 * c * I).im = 2 * c := by simp
    rw [hre, him]
    have : 0 < Real.cos (2 * c) := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hc).1],
      by linarith [(abs_lt.mp hc).2]⟩
    positivity
  exact ContinuousAt.comp (g := thetaPowerShiftDiff a δ)
    (f := fun x : ℝ => I * Complex.exp (2 * (x : ℂ) + 2 * c * I))
    (differentiableAt_thetaPowerShiftDiff a δ hδ hpos).continuousAt (by fun_prop)

/-- **Plancherel for the rotated line**: `∫ |Ĝ_c(2t)|² dt ≤ π ∫ |G_c|²`. -/
theorem lintegral_rotatedFourier_le (ha0 : 0 < a) (ha1 : a < 1 / 2) {δ η σ c : ℝ} (hδ : 0 < δ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hσ : 1 / 4 + η < σ) (hc0 : 0 ≤ c) (hc : c < π / 4) :
    ∫⁻ t : ℝ, ENNReal.ofReal (‖angularFourier (thetaPowerRotatedLine a δ σ c) (2 * t)‖ ^ 2) ≤
      ENNReal.ofReal (π * ∫ x, ‖thetaPowerRotatedLine a δ σ c x‖ ^ 2) := by
  set G := thetaPowerRotatedLine a δ σ c with hG
  obtain ⟨C, r, hr, hdec⟩ := exists_norm_rotatedLine_le ha0 ha1 hδ hη0 hη1 hσ hc0 hc
  have hGc : Continuous G := continuous_thetaPowerRotatedLine hδ.le (by rw [abs_of_nonneg hc0]; exact hc)
  have hdom : Integrable fun x : ℝ => C * Real.exp (-(r * |x|)) :=
    (integrable_exp_neg_mul_abs' hr).const_mul C
  have hGint : Integrable G :=
    hdom.mono' hGc.aestronglyMeasurable (Filter.Eventually.of_forall hdec)
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hdec 0); simpa using this
  have hG2 : Integrable fun x => ‖G x‖ ^ 2 := by
    have hdom2 : Integrable fun x : ℝ => C ^ 2 * Real.exp (-((2 * r) * |x|)) :=
      (integrable_exp_neg_mul_abs' (by positivity)).const_mul _
    refine hdom2.mono' (hGc.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc ‖G x‖ ^ 2 ≤ (C * Real.exp (-(r * |x|))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hdec x) 2
      _ = C ^ 2 * Real.exp (-((2 * r) * |x|)) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  -- rescale `G̃(u) = G(u/2)/2`
  set Gt : ℝ → ℂ := fun u => (1 / 2 : ℂ) * G (u / 2) with hGt
  have hGtc : Continuous Gt := continuous_const.mul (hGc.comp (continuous_id.div_const 2))
  have hGtint : Integrable Gt := by
    have := (hGint.comp_mul_left' (R := 1 / 2) (by norm_num)).const_mul (1 / 2 : ℂ)
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [hGt]; congr 2; ring
  have hGt2 : Integrable fun u => ‖Gt u‖ ^ 2 := by
    have := (hG2.comp_mul_left' (R := 1 / 2) (by norm_num)).const_mul (1 / 4 : ℝ)
    refine this.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [hGt, norm_mul]
    rw [show u / 2 = 1 / 2 * u by ring]; norm_num; ring
  have hF : ∀ t : ℝ, angularFourier G (2 * t) = angularFourier Gt t := by
    intro t
    unfold angularFourier
    have h := MeasureTheory.Measure.integral_comp_mul_left
      (fun u : ℝ => Complex.exp (I * t * u) * G (u / 2)) 2
    calc ∫ s : ℝ, Complex.exp (I * ((2 * t : ℝ) : ℂ) * s) * G s
        = ∫ s : ℝ, (fun u : ℝ => Complex.exp (I * t * u) * G (u / 2)) (2 * s) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          simp only
          rw [show (2 * s) / 2 = s by ring]
          congr 2; push_cast; ring
      _ = |(2 : ℝ)⁻¹| • ∫ y : ℝ, (fun u : ℝ => Complex.exp (I * t * u) * G (u / 2)) y := h
      _ = ∫ u : ℝ, Complex.exp (I * t * u) * Gt u := by
          rw [abs_of_pos (by norm_num), real_smul, ← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          simp only [hGt]; push_cast; ring
  have hP := lintegral_norm_sq_angularFourier_le hGtc hGtint hGt2
  have hnorm : ∫ u, ‖Gt u‖ ^ 2 = (1 / 2) * ∫ x, ‖G x‖ ^ 2 := by
    have h := MeasureTheory.Measure.integral_comp_div (fun x : ℝ => ‖G x‖ ^ 2) 2
    simp only [hGt, norm_mul, mul_pow]
    rw [integral_const_mul, h]
    norm_num
    ring
  simp_rw [hF]
  refine hP.trans (le_of_eq ?_)
  rw [hnorm]; ring_nf

/-- `J_b = ∫ e^{by} e^{-(πa/8) e^{2y}} dy`. -/
def thetaPowerDecayIntegral (a b : ℝ) : ℝ :=
  ∫ y : ℝ, Real.exp (b * y) * Real.exp (-(π * a / 8 * Real.exp (2 * y)))

theorem integrable_exp_mul_exp_neg_exp (ha0 : 0 < a) {b : ℝ} (hb : 0 < b) :
    Integrable fun y : ℝ => Real.exp (b * y) * Real.exp (-(π * a / 8 * Real.exp (2 * y))) := by
  have hlam : 0 < π * a / 8 := by positivity
  refine ((integrable_exp_neg_mul_abs' (lt_min hb one_pos)).const_mul
    (Real.exp ((b + 1) ^ 2 / (8 * (π * a / 8))))).mono'
    (by fun_prop : Continuous fun y : ℝ => Real.exp (b * y) *
      Real.exp (-(π * a / 8 * Real.exp (2 * y)))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact exp_mul_exp_neg_exp_le hb hlam y

/-- **Uniform domination** of `J` on `[σ₁, 1]`. -/
theorem thetaPowerDecayIntegral_le (ha0 : 0 < a) {b b₁ : ℝ} (hb₁ : 0 < b₁) (hbb : b₁ ≤ b) (hb3 : b ≤ 3) :
    thetaPowerDecayIntegral a b ≤ thetaPowerDecayIntegral a b₁ + thetaPowerDecayIntegral a 3 := by
  unfold thetaPowerDecayIntegral
  rw [← integral_add (integrable_exp_mul_exp_neg_exp ha0 hb₁) (integrable_exp_mul_exp_neg_exp ha0 (by norm_num))]
  refine integral_mono (integrable_exp_mul_exp_neg_exp ha0 (by linarith))
    ((integrable_exp_mul_exp_neg_exp ha0 hb₁).add (integrable_exp_mul_exp_neg_exp ha0 (by norm_num)))
    (fun y => ?_)
  have he : 0 < Real.exp (-(π * a / 8 * Real.exp (2 * y))) := Real.exp_pos _
  rcases le_total y 0 with hy | hy
  · have : Real.exp (b * y) ≤ Real.exp (b₁ * y) := Real.exp_le_exp.mpr (by nlinarith)
    have h3 : 0 ≤ Real.exp (3 * y) * Real.exp (-(π * a / 8 * Real.exp (2 * y))) := by positivity
    show Real.exp (b * y) * Real.exp (-(π * a / 8 * Real.exp (2 * y))) ≤
      Real.exp (b₁ * y) * Real.exp (-(π * a / 8 * Real.exp (2 * y))) +
        Real.exp (3 * y) * Real.exp (-(π * a / 8 * Real.exp (2 * y)))
    nlinarith
  · have : Real.exp (b * y) ≤ Real.exp (3 * y) := Real.exp_le_exp.mpr (by nlinarith)
    have h1 : 0 ≤ Real.exp (b₁ * y) * Real.exp (-(π * a / 8 * Real.exp (2 * y))) := by positivity
    show Real.exp (b * y) * Real.exp (-(π * a / 8 * Real.exp (2 * y))) ≤
      Real.exp (b₁ * y) * Real.exp (-(π * a / 8 * Real.exp (2 * y))) +
        Real.exp (3 * y) * Real.exp (-(π * a / 8 * Real.exp (2 * y)))
    nlinarith

/-- **`L²` bound of the rotated line.** `∫ |G_c|² ≤ (3C₁)² δ^{2η} κ^{-2σ} J_{4σ-1-4η}`, `κ = cos 2c`. -/
theorem integral_norm_sq_rotatedLine_le (ha0 : 0 < a) (ha1 : a < 1 / 2) {δ η σ c : ℝ} (hδ : 0 < δ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hσ : 1 / 4 + η < σ) (hc0 : 0 ≤ c) (hc : c < π / 4) :
    ∫ x, ‖thetaPowerRotatedLine a δ σ c x‖ ^ 2 ≤
      (3 * thetaPowerEnvelopeConstant a) ^ 2 * δ ^ (2 * η) * Real.cos (2 * c) ^ (-(2 * σ)) *
        thetaPowerDecayIntegral a (4 * σ - 1 - 4 * η) := by
  set κ : ℝ := Real.cos (2 * c) with hκ
  have hκ0 : 0 < κ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  set L : ℝ := Real.log κ / 2 with hL
  set b : ℝ := 4 * σ - 1 - 4 * η with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  set K : ℝ := 3 * thetaPowerEnvelopeConstant a with hK
  have hK0 : 0 ≤ K := mul_nonneg (by norm_num) (thetaPowerEnvelopeConstant_nonneg ha0 ha1)
  set φ : ℝ → ℝ := fun y => Real.exp (b * y) * Real.exp (-(π * a / 8 * Real.exp (2 * y))) with hφ
  have hφint : Integrable φ := integrable_exp_mul_exp_neg_exp ha0 hb0
  -- pointwise bound
  have hpt : ∀ x : ℝ, ‖thetaPowerRotatedLine a δ σ c x‖ ^ 2 ≤
      K ^ 2 * δ ^ (2 * η) * κ ^ (-(2 * σ)) * φ (x + L) := by
    intro x
    set τ : ℂ := I * Complex.exp (2 * x + 2 * c * I) with hτ
    have him : τ.im = Real.exp (2 * x) * κ := by
      rw [hτ, im_I_mul_cexp]; simp [hκ]
    have hτ0 : 0 < τ.im := by rw [him]; positivity
    have hH := norm_thetaPowerForm_sub_shift_le ha0 ha1 hη0 hη1 hδ hτ0
    have hG : ‖thetaPowerRotatedLine a δ σ c x‖ = Real.exp (2 * σ * x) * ‖thetaPowerShiftDiff a δ τ‖ := by
      unfold thetaPowerRotatedLine
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hexpim : Real.exp (2 * x) * κ = Real.exp (2 * (x + L)) := by
      rw [show 2 * (x + L) = 2 * x + Real.log κ by rw [hL]; ring, Real.exp_add, Real.exp_log hκ0]
    have hbase : ‖thetaPowerShiftDiff a δ τ‖ ≤
        K * δ ^ η * Real.exp (2 * (x + L) * (-(1 / 4 : ℝ) - η)) *
          Real.exp (-(π * a / 16 * Real.exp (2 * (x + L)))) := by
      refine hH.trans (le_of_eq ?_)
      rw [him, hexpim, ← Real.exp_mul]
    rw [hG]
    have hsq : (Real.exp (2 * σ * x) * ‖thetaPowerShiftDiff a δ τ‖) ^ 2 ≤
        (Real.exp (2 * σ * x) * (K * δ ^ η * Real.exp (2 * (x + L) * (-(1 / 4 : ℝ) - η)) *
          Real.exp (-(π * a / 16 * Real.exp (2 * (x + L)))))) ^ 2 := by
      gcongr
    refine hsq.trans (le_of_eq ?_)
    have hκp : κ ^ (-(2 * σ)) = Real.exp (-(4 * σ * L)) := by
      rw [Real.rpow_def_of_pos hκ0, hL]; congr 1; ring
    have hδ2 : (δ ^ η) ^ 2 = δ ^ (2 * η) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; norm_num; ring_nf
    rw [hκp, hφ]
    simp only
    rw [mul_pow, mul_pow, mul_pow, mul_pow, hδ2]
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    have e1 : ((2 : ℕ) : ℝ) * (2 * σ * x) + ((2 : ℕ) : ℝ) * (2 * (x + L) * (-(1 / 4 : ℝ) - η)) =
        -(4 * σ * L) + b * (x + L) := by rw [hb]; push_cast; ring
    have e2 : ((2 : ℕ) : ℝ) * -(π * a / 16 * Real.exp (2 * (x + L))) =
        -(π * a / 8 * Real.exp (2 * (x + L))) := by push_cast; ring
    rw [e2]
    calc Real.exp (((2 : ℕ) : ℝ) * (2 * σ * x)) * (K ^ 2 * δ ^ (2 * η) *
          Real.exp (((2 : ℕ) : ℝ) * (2 * (x + L) * (-(1 / 4 : ℝ) - η))) *
            Real.exp (-(π * a / 8 * Real.exp (2 * (x + L)))))
        = K ^ 2 * δ ^ (2 * η) * (Real.exp (((2 : ℕ) : ℝ) * (2 * σ * x)) *
            Real.exp (((2 : ℕ) : ℝ) * (2 * (x + L) * (-(1 / 4 : ℝ) - η)))) *
            Real.exp (-(π * a / 8 * Real.exp (2 * (x + L)))) := by ring
      _ = K ^ 2 * δ ^ (2 * η) * (Real.exp (-(4 * σ * L)) * Real.exp (b * (x + L))) *
            Real.exp (-(π * a / 8 * Real.exp (2 * (x + L)))) := by
          rw [← Real.exp_add, ← Real.exp_add, e1]
      _ = _ := by ring
  have hG2int : Integrable fun x => ‖thetaPowerRotatedLine a δ σ c x‖ ^ 2 := by
    obtain ⟨C, r, hr, hdec⟩ := exists_norm_rotatedLine_le ha0 ha1 hδ hη0 hη1 hσ hc0 hc
    have hGc := continuous_thetaPowerRotatedLine (a := a) (σ := σ) hδ.le
      (by rw [abs_of_nonneg hc0]; exact hc)
    have hdom2 : Integrable fun x : ℝ => C ^ 2 * Real.exp (-((2 * r) * |x|)) :=
      (integrable_exp_neg_mul_abs' (by positivity)).const_mul _
    refine hdom2.mono' (hGc.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc ‖thetaPowerRotatedLine a δ σ c x‖ ^ 2 ≤ (C * Real.exp (-(r * |x|))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hdec x) 2
      _ = C ^ 2 * Real.exp (-((2 * r) * |x|)) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have hRint : Integrable fun x : ℝ => K ^ 2 * δ ^ (2 * η) * κ ^ (-(2 * σ)) * φ (x + L) :=
    (hφint.comp_add_right L).const_mul _
  refine (integral_mono hG2int hRint hpt).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add_right_eq_self φ L]
  rfl

/-- **Mean square of the Dirichlet error.** For `1/4 + η < σ₁ ≤ σ ≤ 1`, `0 < δ` and `T ≥ 1`,
`∫_T^{2T} |E^δ(σ+it)|² dt ≤ C δ^{2η} T`. -/
theorem exists_lintegral_thetaPowerDirichletError_le (ha0 : 0 < a) (ha1 : a < 1 / 2) {η σ₁ : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hσ₁ : 1 / 4 + η < σ₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ σ T : ℝ, 0 < δ → σ₁ ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∫⁻ t in Icc T (2 * T), ENNReal.ofReal (‖thetaPowerDirichletError a δ ((σ : ℂ) + t * I)‖ ^ 2) ≤
        ENNReal.ofReal (C * δ ^ (2 * η) * T) := by
  obtain ⟨CΓ, hCΓ, hΓ⟩ := exists_norm_inv_Gamma_le_sharp
  set b₁ : ℝ := 4 * σ₁ - 1 - 4 * η with hb₁
  have hb₁0 : 0 < b₁ := by rw [hb₁]; linarith
  set J₁ : ℝ := thetaPowerDecayIntegral a b₁ + thetaPowerDecayIntegral a 3 with hJ₁
  have hJnn : ∀ b, 0 ≤ thetaPowerDecayIntegral a b := fun b =>
    integral_nonneg fun y => by positivity
  have hJ₁0 : 0 ≤ J₁ := add_nonneg (hJnn _) (hJnn _)
  set K : ℝ := 3 * thetaPowerEnvelopeConstant a with hK
  have hK0 : 0 ≤ K := mul_nonneg (by norm_num) (thetaPowerEnvelopeConstant_nonneg ha0 ha1)
  set C : ℝ := 8 * Real.exp 4 * CΓ ^ 2 * π * K ^ 2 * J₁ * (π ^ 2 / 2) ^ 2 with hC
  refine ⟨C, by positivity, fun δ σ T hδ hσ₁σ hσ1 hT => ?_⟩
  have hσ : 1 / 4 + η < σ := by linarith
  have hσ0 : 0 ≤ σ := by linarith
  have hT0 : 0 < T := by linarith
  set c : ℝ := π / 4 - 1 / (2 * T) with hc
  have hhalf : 1 / (2 * T) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hc0 : 0 ≤ c := by rw [hc]; linarith [Real.pi_gt_three]
  have hcπ : c < π / 4 := by rw [hc]; linarith [show 0 < 1 / (2 * T) by positivity]
  set κ : ℝ := Real.cos (2 * c) with hκ
  have hκsin : κ = Real.sin (1 / T) := by
    rw [hκ, hc, show 2 * (π / 4 - 1 / (2 * T)) = π / 2 - 1 / T by field_simp; ring,
      Real.cos_pi_div_two_sub]
  have hκlow : 2 / π * (1 / T) ≤ κ := by
    rw [hκsin]; apply Real.mul_le_sin (by positivity)
    have : 1 / T ≤ 1 := by rw [div_le_one hT0]; exact hT
    linarith [Real.pi_gt_three]
  have hκ0 : 0 < κ := lt_of_lt_of_le (by positivity) hκlow
  set G := thetaPowerRotatedLine a δ σ c
  set A : ℝ := 8 * Real.exp 4 * π ^ (2 * σ) * CΓ ^ 2 * T ^ (1 - 2 * σ) with hA
  have hA0 : 0 ≤ A := by positivity
  -- pointwise bound on `[T, 2T]`
  have hpt : ∀ t ∈ Icc T (2 * T), ENNReal.ofReal (‖thetaPowerDirichletError a δ ((σ : ℂ) + t * I)‖ ^ 2) ≤
      ENNReal.ofReal (A * ‖angularFourier G (2 * t)‖ ^ 2) := by
    intro t ht
    apply ENNReal.ofReal_le_ofReal
    have ht1 : 1 ≤ |t| := by rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1]
    have htpos : 0 < t := by linarith [ht.1]
    have hrot := thetaPowerMellin_sub_shift_rotated ha0 ha1 (t := t) hδ hη0.le hη1 hσ hc0 hcπ
    unfold thetaPowerDirichletError
    rw [hrot]
    have hπn : ‖(π : ℂ) ^ ((σ : ℂ) + t * I)‖ = π ^ σ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]; simp
    have hexpn : ‖Complex.exp (2 * ((σ : ℂ) + t * I) * (c * I))‖ = Real.exp (-(2 * t * c)) := by
      rw [Complex.norm_exp]; congr 1; simp
    have hG := hΓ σ t hσ0 hσ1 ht1
    rw [abs_of_pos htpos] at hG
    rw [norm_div, norm_mul, norm_mul, norm_mul, hπn, hexpn, Complex.norm_ofNat, div_eq_mul_inv, ← norm_inv]
    set F := ‖angularFourier G (2 * t)‖
    have hmain : π ^ σ * (2 * Real.exp (-(2 * t * c)) * F) * ‖(Complex.Gamma ((σ : ℂ) + t * I))⁻¹‖ ≤
        π ^ σ * (2 * Real.exp (-(2 * t * c)) * F) * (CΓ * t ^ (1 / 2 - σ) * Real.exp (π * t / 2)) := by
      gcongr
    have hsq := pow_le_pow_left₀ (by positivity) hmain 2
    refine hsq.trans ?_
    have hexp : Real.exp (-(2 * t * c)) ^ 2 * Real.exp (π * t / 2) ^ 2 ≤ Real.exp 4 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : ((2 : ℕ) : ℝ) * -(2 * t * c) + ((2 : ℕ) : ℝ) * (π * t / 2) = 2 * t / T := by
        rw [hc]; push_cast; field_simp; ring
      rw [this, div_le_iff₀ hT0]; linarith [ht.2]
    have htp : (t ^ (1 / 2 - σ)) ^ 2 ≤ 2 * T ^ (1 - 2 * σ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul htpos.le]
      rw [show (1 / 2 - σ) * ((2 : ℕ) : ℝ) = 1 - 2 * σ by push_cast; ring]
      rcases le_total 0 (1 - 2 * σ) with hp | hp
      · calc t ^ (1 - 2 * σ) ≤ (2 * T) ^ (1 - 2 * σ) := Real.rpow_le_rpow htpos.le ht.2 hp
          _ = 2 ^ (1 - 2 * σ) * T ^ (1 - 2 * σ) := Real.mul_rpow (by norm_num) hT0.le
          _ ≤ 2 * T ^ (1 - 2 * σ) := by
              gcongr
              calc (2 : ℝ) ^ (1 - 2 * σ) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
                _ = 2 := Real.rpow_one 2
      · calc t ^ (1 - 2 * σ) ≤ T ^ (1 - 2 * σ) := Real.rpow_le_rpow_of_nonpos hT0 ht.1 hp
          _ ≤ 2 * T ^ (1 - 2 * σ) := by have := Real.rpow_nonneg hT0.le (1 - 2 * σ); linarith
    have hπ2 : (π ^ σ) ^ 2 = π ^ (2 * σ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]; push_cast; ring_nf
    calc (π ^ σ * (2 * Real.exp (-(2 * t * c)) * F) * (CΓ * t ^ (1 / 2 - σ) * Real.exp (π * t / 2))) ^ 2
        = 4 * (π ^ σ) ^ 2 * CΓ ^ 2 * (t ^ (1 / 2 - σ)) ^ 2 *
            (Real.exp (-(2 * t * c)) ^ 2 * Real.exp (π * t / 2) ^ 2) * F ^ 2 := by ring
      _ ≤ 4 * (π ^ σ) ^ 2 * CΓ ^ 2 * (2 * T ^ (1 - 2 * σ)) * Real.exp 4 * F ^ 2 := by
          gcongr
      _ = A * F ^ 2 := by rw [hA, hπ2]; ring
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (A * ‖angularFourier G (2 * t)‖ ^ 2) := by
    have hGc := continuous_thetaPowerRotatedLine (a := a) (δ := δ) (σ := σ) hδ.le
      (by rw [abs_of_nonneg hc0]; exact hcπ)
    have hGint : Integrable G := by
      obtain ⟨C', r, hr, hdec⟩ := exists_norm_rotatedLine_le ha0 ha1 hδ hη0.le hη1 hσ hc0 hcπ
      exact ((integrable_exp_neg_mul_abs' hr).const_mul C').mono' hGc.aestronglyMeasurable
        (Filter.Eventually.of_forall hdec)
    exact ((continuous_const.mul (((continuous_angularFourier hGc hGint).comp
      (continuous_const.mul continuous_id)).norm.pow 2))).measurable.ennreal_ofReal
  refine (setLIntegral_mono hmeas hpt).trans ?_
  refine (setLIntegral_le_lintegral _ _).trans ?_
  have hsplit : (fun t : ℝ => ENNReal.ofReal (A * ‖angularFourier G (2 * t)‖ ^ 2)) =
      fun t => ENNReal.ofReal A * ENNReal.ofReal (‖angularFourier G (2 * t)‖ ^ 2) := by
    funext t; rw [ENNReal.ofReal_mul hA0]
  rw [hsplit, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hP := lintegral_rotatedFourier_le ha0 ha1 hδ hη0.le hη1 hσ hc0 hcπ
  have hL2 := integral_norm_sq_rotatedLine_le ha0 ha1 hδ hη0.le hη1 hσ hc0 hcπ
  have hJ : thetaPowerDecayIntegral a (4 * σ - 1 - 4 * η) ≤ J₁ :=
    thetaPowerDecayIntegral_le ha0 hb₁0 (by rw [hb₁]; linarith) (by linarith)
  have hκp : κ ^ (-(2 * σ)) ≤ (π * T / 2) ^ (2 * σ) := by
    have h1 : κ ^ (-(2 * σ)) ≤ (2 / π * (1 / T)) ^ (-(2 * σ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hκlow (by linarith)
    refine h1.trans (le_of_eq ?_)
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
    congr 1; field_simp
  have hd : 0 ≤ δ ^ (2 * η) := Real.rpow_nonneg hδ.le _
  have hk : 0 ≤ κ ^ (-(2 * σ)) := Real.rpow_nonneg hκ0.le _
  have hG2 : ∫ x, ‖G x‖ ^ 2 ≤ K ^ 2 * δ ^ (2 * η) * (π * T / 2) ^ (2 * σ) * J₁ := by
    refine hL2.trans ?_
    have hstep : K ^ 2 * δ ^ (2 * η) * κ ^ (-(2 * σ)) * thetaPowerDecayIntegral a (4 * σ - 1 - 4 * η) ≤
        K ^ 2 * δ ^ (2 * η) * (π * T / 2) ^ (2 * σ) * J₁ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hκp (by positivity)) hJ (hJnn _)
        (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
    exact hstep
  have h1 : π ^ (2 * σ) * (π * T / 2) ^ (2 * σ) = (π ^ 2 / 2) ^ (2 * σ) * T ^ (2 * σ) := by
    rw [← Real.mul_rpow Real.pi_pos.le (by positivity), show π * (π * T / 2) = (π ^ 2 / 2) * T by ring,
      Real.mul_rpow (by positivity) hT0.le]
  have h2 : T ^ (1 - 2 * σ) * T ^ (2 * σ) = T := by
    rw [← Real.rpow_add hT0]; simp
  have h3 : (π ^ 2 / 2) ^ (2 * σ) ≤ (π ^ 2 / 2) ^ (2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · have := Real.pi_gt_three; nlinarith
    · linarith
  have hTT : π ^ (2 * σ) * T ^ (1 - 2 * σ) * (π * T / 2) ^ (2 * σ) ≤ (π ^ 2 / 2) ^ 2 * T := by
    have e : π ^ (2 * σ) * T ^ (1 - 2 * σ) * (π * T / 2) ^ (2 * σ) = (π ^ 2 / 2) ^ (2 * σ) * T := by
      rw [show π ^ (2 * σ) * T ^ (1 - 2 * σ) * (π * T / 2) ^ (2 * σ) =
        (π ^ (2 * σ) * (π * T / 2) ^ (2 * σ)) * T ^ (1 - 2 * σ) by ring, h1,
        show (π ^ 2 / 2) ^ (2 * σ) * T ^ (2 * σ) * T ^ (1 - 2 * σ) =
          (π ^ 2 / 2) ^ (2 * σ) * (T ^ (1 - 2 * σ) * T ^ (2 * σ)) by ring, h2]
    rw [e]
    calc (π ^ 2 / 2) ^ (2 * σ) * T ≤ (π ^ 2 / 2) ^ (2 : ℝ) * T := mul_le_mul_of_nonneg_right h3 hT0.le
      _ = (π ^ 2 / 2) ^ 2 * T := by rw [Real.rpow_two]
  have hfinal : A * (π * ∫ x, ‖G x‖ ^ 2) ≤ C * δ ^ (2 * η) * T := by
    have hstep1 : A * (π * ∫ x, ‖G x‖ ^ 2) ≤
        A * (π * (K ^ 2 * δ ^ (2 * η) * (π * T / 2) ^ (2 * σ) * J₁)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG2 Real.pi_pos.le) hA0
    have hstep2 : A * (π * (K ^ 2 * δ ^ (2 * η) * (π * T / 2) ^ (2 * σ) * J₁)) =
        8 * Real.exp 4 * CΓ ^ 2 * π * K ^ 2 * J₁ * δ ^ (2 * η) *
          (π ^ (2 * σ) * T ^ (1 - 2 * σ) * (π * T / 2) ^ (2 * σ)) := by rw [hA]; ring
    have hcoef : 0 ≤ 8 * Real.exp 4 * CΓ ^ 2 * π * K ^ 2 * J₁ * δ ^ (2 * η) := by positivity
    have hstep3 := mul_le_mul_of_nonneg_left hTT hcoef
    have hstep4 : 8 * Real.exp 4 * CΓ ^ 2 * π * K ^ 2 * J₁ * δ ^ (2 * η) * ((π ^ 2 / 2) ^ 2 * T) =
        C * δ ^ (2 * η) * T := by rw [hC]; ring
    linarith
  calc ENNReal.ofReal A * ∫⁻ t : ℝ, ENNReal.ofReal (‖angularFourier G (2 * t)‖ ^ 2)
      ≤ ENNReal.ofReal A * ENNReal.ofReal (π * ∫ x, ‖G x‖ ^ 2) := by gcongr
    _ = ENNReal.ofReal (A * (π * ∫ x, ‖G x‖ ^ 2)) := (ENNReal.ofReal_mul hA0).symm
    _ ≤ ENNReal.ofReal (C * δ ^ (2 * η) * T) := ENNReal.ofReal_le_ofReal hfinal

end

end RHTower
