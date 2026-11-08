import GaloisForLFunctions.BlackHoleRingdown.TheWeylUpperBound
import GaloisForLFunctions.RHTower.PeriodicFourierDecay
import GaloisForLFunctions.RHTower.WeilWorkDeficitProductKernelMellin
import GaloisForLFunctions.HTGeometry.BesselOrderPolyaRealZeros
import GaloisForLFunctions.RHTower.DeckCuspidalFourierExpansion

/-!
# The L-functions of the cusp modes

Every cusp form `g` of the modular horizon, of eigenvalue `λ = ¼ + t²`, carries an entire L-function with
a functional equation (`cusp_L_function`). Its modes are `a_n(y) = ρ(n) √y K_ν(2π|n|y)` with `ν = it`, and
`L(s) = Σ_{n ≠ 0} ρ(n) |n|^{-s}` converges absolutely for `Re s > 3/2`. The completed function

  `Λ(s) = ∫_0^∞ g(iy) y^{s - 1/2} dy/y = ¼ π^{-s} Γ((s+ν)/2) Γ((s-ν)/2) L(s)`

is entire and `Λ(1 - s) = Λ(s)`, and `L = 4π^s Λ / (Γ((s+ν)/2) Γ((s-ν)/2))` is entire.

**Modes.** On the imaginary axis `g(iy) = Σ_n a_n(y)`, by pointwise Fourier inversion for the `C²`
periodic slice (`hasSum_axis`). Each mode is a multiple of the Whittaker function, and boundedness of `g`
at the point `y = X/(2π|n|)` with `K_ν(X) ≠ 0` gives `|ρ(n)| ≤ C√|n|` (`exists_coeff_bound`).

**Decay and symmetry.** With `K_ν(x) ≤ e^{1-x} M` for `x ≥ 1`, `|g(iy)| ≤ D √y e^{-2πy}` for `y ≥ 1`
(`norm_axis_le`). The inversion `S: z ↦ -1/z` maps `iy` to `i/y`, so `g(i/y) = g(iy)`: the profile
`f(y) = y^{-1/2} g(iy)` satisfies `f(1/y) = y f(y)` and decays faster than every power at both ends. Hence
its Mellin transform is entire (`differentiable_completed`) and `Λ(1-s) = Λ(s)` (`completed_one_sub`).

**The Dirichlet series.** For `Re s > 3/2` the modes integrate termwise,
`∫_0^∞ y^{s-1} K_ν(2π|n|y) dy = (2π|n|)^{-s} 2^{s-2} Γ((s+ν)/2) Γ((s-ν)/2)`, absolutely summed by
`|ρ(n)| ≤ C√|n|` (`completed_eq`).
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.DeckPointPair
  GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open GaloisForLFunctions.HTGeometry (modifiedBesselKOrder norm_modifiedBesselKOrder_le_exp
  besselOrderUnitMass besselOrderUnitMass_nonneg eventually_re_modifiedBesselKOrder_pos)
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos)
open GaloisForLFunctions.RHTower.SelbergMaassCongruenceTrace (Deck)
open GaloisForLFunctions.RHTower.SelbergMaassMean (point directional)

namespace CuspL

open HeckeCusp

variable {lam : ℝ} {g : UpperHalfPlane → ℂ}

/-- The spectral parameter `ν = i√(λ - ¼)`. -/
def nu (lam : ℝ) : ℂ := (Real.sqrt (lam - 1 / 4) : ℂ) * I

theorem nu_sq (hlam : 1 / 4 ≤ lam) : nu lam ^ 2 = 1 / 4 - lam := by
  unfold nu
  rw [mul_pow, I_sq, ← ofReal_pow, Real.sq_sqrt (by linarith)]
  push_cast
  ring

theorem nu_re (lam : ℝ) : (nu lam).re = 0 := by simp [nu]

/-- A nonzero cusp form has eigenvalue at least `¼`. -/
theorem one_quarter_le (hg : g ∈ cuspSpace lam) (hg0 : g ≠ 0) : 1 / 4 ≤ lam :=
  one_quarter_le_of_cuspEigen (isCuspLaplaceEigen_vecOf hg) fun h =>
    hg0 (eq_zero_of_toDeckL2_eq_zero hg h)

/-! ### Fourier inversion on the imaginary axis -/

/-- The cusp form on the imaginary axis, `y ↦ g(iy)`. -/
def axis (g : UpperHalfPlane → ℂ) (y : ℝ) : ℂ := g (ofComplex (point 0 y))

/-- **Fourier inversion on the imaginary axis**: `g(iy) = Σ_n a_n(y)`. -/
theorem hasSum_axis (hg : g ∈ cuspSpace lam) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => fourierCoeff g n y) (axis g y) := by
  set F : ℂ → ℂ := g ∘ ofComplex
  have hF : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im} := hg.2.1.1
  have hF1 : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im} := hF.of_le (by norm_num)
  have hD : ContDiffOn ℝ 1 (directional 1 F) {z : ℂ | 0 < z.im} :=
    SelbergMaassMean.directional_contDiffOn hF (m := 1) le_rfl 1
  have hD2 : ContDiffOn ℝ 0 (directional 1 (directional 1 F)) {z : ℂ | 0 < z.im} :=
    SelbergMaassMean.directional_contDiffOn hD (m := 0) (by simp) 1
  have hp : ∀ x, F (point (x + 1) y) = F (point x y) := fun x => by
    rw [WeylUpper.point_add_one]; exact periodic_comp hg _ (point_im_pos hy)
  have hp' := SelbergMaassMean.directional_periodic hF1 hy 1 hp
  have hp'' := SelbergMaassMean.directional_periodic hD hy 1 hp'
  set f'' : ℝ → ℂ := fun x => directional 1 (directional 1 F) (point x y)
  have hc'' : Continuous f'' := SelbergMaassMean.slice_continuous hD2.continuousOn hy
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖f'' x‖ ≤ C := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hc''.continuousOn (s := Icc (0 : ℝ) 1))
    refine ⟨C, fun x => ?_⟩
    obtain ⟨x', hx', hxx⟩ := (show Function.Periodic f'' 1 from fun x => hp'' x).exists_mem_Ico₀
      one_pos x
    rw [hxx]
    exact hC x' (Ico_subset_Icc_self hx')
  have h := hasSum_fourier_of_periodic_two (a := 0) (b := 1) zero_lt_one
    (f := fun x => F (point x y)) (f' := fun x => directional 1 F (point x y)) (f'' := f'')
    (fun x _ => SelbergMaassMean.slice_horizontal hF1 hy x)
    (fun x _ => SelbergMaassMean.slice_horizontal hD hy x)
    ((SelbergMaassMean.slice_continuous hD.continuousOn hy).intervalIntegrable _ _)
    (hc''.intervalIntegrable _ _) hC (by simpa using hp 0) (by simpa using hp' 0)
    (x := 1) ⟨zero_lt_one, le_rfl⟩
  have hfour : ∀ n : ℤ, fourier n (((1 : ℝ) : ℝ) : AddCircle ((1 : ℝ) - 0)) = 1 := fun n => by
    rw [fourier_coe_apply]
    have e : 2 * (Real.pi : ℂ) * I * n * ((1 : ℝ) : ℂ) / (((1 : ℝ) - 0 : ℝ) : ℂ) =
        n * (2 * Real.pi * I) := by push_cast; ring
    rw [e, exp_int_mul_two_pi_mul_I]
  simp only [hfour, mul_one] at h
  have hval : F (point 1 y) = axis g y := by
    have := hp 0
    rw [zero_add] at this
    rw [this]
    rfl
  rw [hval] at h
  convert h using 1
  funext n
  unfold HeckeCusp.fourierCoeff
  exact SelbergMaassParseval.coefficient_eq_fourierCoeffOn 1 one_pos F y n

/-! ### The Whittaker coefficients -/

theorem abs_signedFrequency (n : ℤ) :
    |SelbergMaassFourier.signedFrequency ((0 + 1 : ℕ) : ℝ) n| = 2 * Real.pi * |(n : ℝ)| := by
  simp [SelbergMaassFourier.signedFrequency, abs_mul, abs_of_pos Real.pi_pos]

/-- **The modes are Whittaker functions**: `a_n(y) = ρ(n) √y K_ν(2π|n|y)`, with `ρ(0) = 0`. -/
theorem exists_whittaker (hg : g ∈ cuspSpace lam) :
    ∃ ρ : ℤ → ℂ, ρ 0 = 0 ∧ ∀ n : ℤ, ∀ y, 0 < y →
      fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
        modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lam) := by
  by_cases hg0 : g = 0
  · refine ⟨0, rfl, fun n y _ => ?_⟩
    subst hg0
    simp [HeckeCusp.fourierCoeff, SelbergMaassFourier.coefficient, _root_.RHTower.deningerFourierCoeff]
  have hlam := one_quarter_le hg hg0
  have hU := isCuspLaplaceEigen_vecOf hg
  have key : ∀ n : ℤ, ∃ r : ℂ, (n = 0 → r = 0) ∧ ∀ y, 0 < y →
      fourierCoeff g n y = r * (Real.sqrt y : ℂ) *
        modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lam) := by
    intro n
    by_cases hn : n = 0
    · refine ⟨0, fun _ => rfl, fun y hy => ?_⟩
      rw [hn, fourierCoeff_zero hg hy]
      ring
    · obtain ⟨r, hr⟩ := hU.deckMode_eq_whittaker (1 : Deck 0) hn (nu_sq hlam)
      refine ⟨r, fun h => absurd h hn, fun y hy => ?_⟩
      have h := hr y hy
      rw [deckMode_vecOf] at h
      rw [h, MaassWhittaker.whittakerW, abs_signedFrequency]
      simp only [MaassWhittaker.besK]
      ring
  choose ρ hρ0 hρ using key
  exact ⟨ρ, hρ0 0 rfl, hρ⟩

variable {ρ : ℤ → ℂ}

/-- **The coefficients grow at most like `√|n|`.** -/
theorem exists_coeff_bound (hg : g ∈ cuspSpace lam) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lam)) :
    ∃ C, 0 ≤ C ∧ ∀ n : ℤ, ‖ρ n‖ ≤ C * Real.sqrt |(n : ℝ)| := by
  obtain ⟨Cg, hCg⟩ := exists_bound hg
  obtain ⟨X, hX1, hXpos⟩ := eventually_re_modifiedBesselKOrder_pos (nu lam)
  set K₀ := modifiedBesselKOrder X (nu lam)
  have hK0 : 0 < ‖K₀‖ := lt_of_lt_of_le (hXpos X le_rfl) (Complex.re_le_norm _)
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg UpperHalfPlane.I)
  have hX0 : 0 < X := by linarith
  refine ⟨Cg / ‖K₀‖ * Real.sqrt (2 * Real.pi / X), by positivity, fun n => ?_⟩
  by_cases hn : n = 0
  · rw [hn, hρ0, norm_zero]
    positivity
  have hn0 : 0 < |(n : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hn)
  set y := X / (2 * Real.pi * |(n : ℝ)|)
  have hy : 0 < y := by positivity
  have harg : 2 * Real.pi * |(n : ℝ)| * y = X := by
    simp only [y]; field_simp
  have h1 := hρ n y hy
  rw [harg] at h1
  have h2 := WeylUpper.norm_fourierCoeff_le hCg n y
  rw [h1, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at h2
  have hsy : Real.sqrt y * (Real.sqrt (2 * Real.pi / X) * Real.sqrt |(n : ℝ)|) = 1 := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul hy.le]
    have : y * (2 * Real.pi / X * |(n : ℝ)|) = 1 := by simp only [y]; field_simp
    rw [this, Real.sqrt_one]
  have h2' : ‖ρ n‖ * Real.sqrt y ≤ Cg / ‖K₀‖ := by
    rw [le_div_iff₀ hK0]; linarith
  calc ‖ρ n‖ = (‖ρ n‖ * Real.sqrt y) * (Real.sqrt (2 * Real.pi / X) * Real.sqrt |(n : ℝ)|) := by
        rw [mul_assoc, hsy, mul_one]
    _ ≤ Cg / ‖K₀‖ * (Real.sqrt (2 * Real.pi / X) * Real.sqrt |(n : ℝ)|) :=
        mul_le_mul_of_nonneg_right h2' (by positivity)
    _ = Cg / ‖K₀‖ * Real.sqrt (2 * Real.pi / X) * Real.sqrt |(n : ℝ)| := by ring

/-! ### Decay on the imaginary axis -/

theorem summable_sqrt_exp : Summable fun n : ℤ => Real.sqrt |(n : ℝ)| * Real.exp (-(2 * Real.pi * |(n : ℝ)|)) := by
  have hr0 : 0 ≤ Real.exp (-(2 * Real.pi)) := (Real.exp_pos _).le
  have hr1 : ‖Real.exp (-(2 * Real.pi))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0, show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_lt_exp.2 (by linarith [Real.pi_pos])
  have hnat : Summable fun n : ℕ => (n : ℝ) ^ 1 * Real.exp (-(2 * Real.pi)) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr1
  have hb : ∀ n : ℕ, Real.sqrt |((n : ℤ) : ℝ)| * Real.exp (-(2 * Real.pi * |((n : ℤ) : ℝ)|)) ≤
      (n : ℝ) ^ 1 * Real.exp (-(2 * Real.pi)) ^ n := by
    intro n
    have habs : |((n : ℤ) : ℝ)| = n := by simp
    rw [habs, pow_one, ← Real.exp_nat_mul]
    have hsq : Real.sqrt n ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith
    refine mul_le_mul hsq (le_of_eq ?_) (Real.exp_pos _).le (by positivity)
    congr 1; ring
  have hb' : ∀ n : ℕ, Real.sqrt |((-(n : ℤ) : ℤ) : ℝ)| * Real.exp (-(2 * Real.pi * |((-(n : ℤ) : ℤ) : ℝ)|)) ≤
      (n : ℝ) ^ 1 * Real.exp (-(2 * Real.pi)) ^ n := by
    intro n
    have := hb n
    simpa [abs_neg] using this
  refine Summable.of_nat_of_neg ?_ ?_
  · exact Summable.of_nonneg_of_le (fun n => by positivity) hb hnat
  · exact Summable.of_nonneg_of_le (fun n => by positivity) hb' hnat

/-- **Every mode decays exponentially in the cusp**: `|a_n(y)| ≤ b_n √y e^{-2πy}` for `y ≥ 1`, with
`Σ_n b_n < ∞`. -/
theorem norm_mode_le (hg : g ∈ cuspSpace lam) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lam)) :
    ∃ b : ℤ → ℝ, Summable b ∧ (∀ n, 0 ≤ b n) ∧ ∀ n : ℤ, ∀ y, 1 ≤ y →
      ‖fourierCoeff g n y‖ ≤ b n * (Real.sqrt y * Real.exp (-(2 * Real.pi * y))) := by
  obtain ⟨C, hC0, hC⟩ := exists_coeff_bound hg hρ0 hρ
  set M := besselOrderUnitMass (nu lam)
  have hM := besselOrderUnitMass_nonneg (nu lam)
  set b : ℤ → ℝ := fun n => C * M * Real.exp (1 + 2 * Real.pi) *
    (Real.sqrt |(n : ℝ)| * Real.exp (-(2 * Real.pi * |(n : ℝ)|)))
  refine ⟨b, summable_sqrt_exp.mul_left _, fun n => by positivity, fun n y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  by_cases hn : n = 0
  · rw [hn, fourierCoeff_zero hg hy0, norm_zero]
    positivity
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hx : 1 ≤ 2 * Real.pi * |(n : ℝ)| * y := by
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| * y := by nlinarith
    rw [show 2 * Real.pi * |(n : ℝ)| * y = 2 * Real.pi * (|(n : ℝ)| * y) by ring]
    nlinarith [Real.pi_gt_three]
  have hK := norm_modifiedBesselKOrder_le_exp hx (nu lam)
  rw [hρ n y hy0, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hexp : Real.exp (1 - 2 * Real.pi * |(n : ℝ)| * y) ≤
      Real.exp (1 + 2 * Real.pi) * Real.exp (-(2 * Real.pi * |(n : ℝ)|)) *
        Real.exp (-(2 * Real.pi * y)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : |(n : ℝ)| + y - 1 ≤ |(n : ℝ)| * y := by nlinarith
    nlinarith [Real.pi_pos]
  calc ‖ρ n‖ * Real.sqrt y * ‖modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lam)‖
      ≤ (C * Real.sqrt |(n : ℝ)|) * Real.sqrt y *
          (Real.exp (1 - 2 * Real.pi * |(n : ℝ)| * y) * M) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hC n) (Real.sqrt_nonneg _)) hK (norm_nonneg _)
          (by positivity)
    _ ≤ (C * Real.sqrt |(n : ℝ)|) * Real.sqrt y *
          (Real.exp (1 + 2 * Real.pi) * Real.exp (-(2 * Real.pi * |(n : ℝ)|)) *
            Real.exp (-(2 * Real.pi * y)) * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hM) (by positivity)
    _ = b n * (Real.sqrt y * Real.exp (-(2 * Real.pi * y))) := by simp only [b]; ring

/-- **The cusp forms decay exponentially along the axis**: `|g(iy)| ≤ D √y e^{-2πy}` for `y ≥ 1`. -/
theorem norm_axis_le (hg : g ∈ cuspSpace lam) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lam)) :
    ∃ D, 0 ≤ D ∧ ∀ y, 1 ≤ y → ‖axis g y‖ ≤ D * Real.sqrt y * Real.exp (-(2 * Real.pi * y)) := by
  obtain ⟨b, hbs, hb0, hmode'⟩ := norm_mode_le hg hρ0 hρ
  refine ⟨∑' n, b n, tsum_nonneg hb0, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  have hmode := fun n => hmode' n y hy
  have hsum : Summable fun n : ℤ => ‖fourierCoeff g n y‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hmode (hbs.mul_right _)
  calc ‖axis g y‖ = ‖∑' n, fourierCoeff g n y‖ := by rw [(hasSum_axis hg hy0).tsum_eq]
    _ ≤ ∑' n, ‖fourierCoeff g n y‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n, b n * (Real.sqrt y * Real.exp (-(2 * Real.pi * y))) :=
        hsum.tsum_le_tsum hmode (hbs.mul_right _)
    _ = (∑' n, b n) * Real.sqrt y * Real.exp (-(2 * Real.pi * y)) := by
        rw [tsum_mul_right]; ring

/-! ### The completed L-function -/

/-- The profile `f(y) = y^{-1/2} g(iy)`, whose Mellin transform is the completed L-function. -/
def profile (g : UpperHalfPlane → ℂ) (y : ℝ) : ℂ := ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * axis g y

/-- The completed L-function `Λ(s) = ∫_0^∞ g(iy) y^{s-1/2} dy/y`. -/
def completed (g : UpperHalfPlane → ℂ) (s : ℂ) : ℂ := mellin (profile g) s

theorem point_inv {y : ℝ} (hy : 0 < y) :
    ModularGroup.S • ofComplex (point 0 y) = ofComplex (point 0 y⁻¹) := by
  have hp : 0 < (point 0 y).im := point_im_pos hy
  have hp' : 0 < (point 0 y⁻¹).im := point_im_pos (inv_pos.2 hy)
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul]
  show (-((ofComplex (point 0 y) : UpperHalfPlane) : ℂ))⁻¹ =
    ((ofComplex (point 0 y⁻¹) : UpperHalfPlane) : ℂ)
  rw [ofComplex_apply_of_im_pos hp, ofComplex_apply_of_im_pos hp']
  show (-(point 0 y))⁻¹ = point 0 y⁻¹
  simp only [point, ofReal_zero, zero_add, ofReal_inv]
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hyy : (y : ℂ)⁻¹ * y = 1 := inv_mul_cancel₀ hy'
  have hprod : (y : ℂ)⁻¹ * I * -((y : ℂ) * I) = 1 := by
    linear_combination (-((y : ℂ)⁻¹ * y)) * I_sq + hyy
  exact (eq_inv_of_mul_eq_one_left hprod).symm

/-- **The inversion symmetry**: `g(i/y) = g(iy)`. -/
theorem axis_inv (hg : g ∈ cuspSpace lam) {y : ℝ} (hy : 0 < y) : axis g y⁻¹ = axis g y := by
  unfold axis
  rw [← point_inv hy, hg.1]

theorem profile_inv (hg : g ∈ cuspSpace lam) {y : ℝ} (hy : 0 < y) :
    profile g y⁻¹ = (y : ℂ) * profile g y := by
  unfold profile
  rw [axis_inv hg hy, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le, neg_neg]
  have h : y ^ (1 / 2 : ℝ) = y * y ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_one_add' hy.le (by norm_num)]
    norm_num
  rw [h]
  push_cast
  ring

theorem continuousOn_axis (hg : g ∈ cuspSpace lam) : ContinuousOn (axis g) (Ioi 0) := by
  have hp : Continuous fun y : ℝ => point 0 y := by simp only [point]; fun_prop
  refine (hg.2.1.1.continuousOn.comp hp.continuousOn fun y hy => ?_)
  exact point_im_pos hy

theorem continuousOn_profile (hg : g ∈ cuspSpace lam) : ContinuousOn (profile g) (Ioi 0) := by
  refine ContinuousOn.mul ?_ (continuousOn_axis hg)
  exact continuous_ofReal.comp_continuousOn fun y hy =>
    (Real.continuousAt_rpow_const y _ (Or.inl (ne_of_gt hy))).continuousWithinAt

theorem profile_isBigO_atTop (hg : g ∈ cuspSpace lam) (a : ℝ) :
    profile g =O[atTop] fun y => y ^ (-a) := by
  obtain ⟨ρ, hρ0, hρ⟩ := exists_whittaker hg
  obtain ⟨D, hD0, hD⟩ := norm_axis_le hg hρ0 hρ
  have h1 : profile g =O[atTop] fun y => Real.exp (-(2 * Real.pi) * y) := by
    refine IsBigO.of_bound D ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hy0 : 0 < y := by linarith
    rw [profile, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    have hs : y ^ (-(1 / 2 : ℝ)) * Real.sqrt y = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hy0]; norm_num
    calc y ^ (-(1 / 2 : ℝ)) * ‖axis g y‖ ≤ y ^ (-(1 / 2 : ℝ)) * (D * Real.sqrt y *
          Real.exp (-(2 * Real.pi * y))) := mul_le_mul_of_nonneg_left (hD y hy) (by positivity)
      _ = D * Real.exp (-(2 * Real.pi) * y) := by
          rw [show -(2 * Real.pi) * y = -(2 * Real.pi * y) by ring]
          linear_combination (D * Real.exp (-(2 * Real.pi * y))) * hs
  exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop (by positivity) (-a)).isBigO

theorem profile_isBigO_zero (hg : g ∈ cuspSpace lam) (b : ℝ) :
    profile g =O[𝓝[>] 0] fun y => y ^ (-b) := by
  have h1 := (profile_isBigO_atTop hg (1 - b)).comp_tendsto tendsto_inv_nhdsGT_zero
  have h2 : (fun y : ℝ => (y⁻¹ : ℝ) • profile g y⁻¹) =O[𝓝[>] 0]
      fun y => y⁻¹ * (y⁻¹) ^ (-(1 - b)) := (isBigO_refl (fun y : ℝ => y⁻¹) _).smul h1
  refine h2.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : 0 < y := hy
    have h := profile_inv hg (inv_pos.2 hy0)
    rw [inv_inv] at h
    rw [real_smul, h]
  · filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : 0 < y := hy
    rw [Real.inv_rpow hy0.le, ← Real.rpow_neg hy0.le, neg_neg, ← Real.rpow_neg_one,
      ← Real.rpow_add hy0]
    congr 1
    ring

/-- **The completed L-function is entire.** -/
theorem differentiable_completed (hg : g ∈ cuspSpace lam) : Differentiable ℂ (completed g) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    ((continuousOn_profile hg).locallyIntegrableOn measurableSet_Ioi)
    (profile_isBigO_atTop hg _) (by linarith) (profile_isBigO_zero hg _) (by linarith)

/-- **The functional equation** `Λ(1 - s) = Λ(s)`. -/
theorem completed_one_sub (hg : g ∈ cuspSpace lam) (s : ℂ) : completed g (1 - s) = completed g s := by
  have h : mellin (fun t => profile g t⁻¹) (s - 1) = mellin (fun t => (t : ℂ) ^ (1 : ℂ) • profile g t) (s - 1) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only
    rw [profile_inv hg ht, cpow_one]
    simp only [smul_eq_mul]
  rw [mellin_comp_inv, mellin_cpow_smul] at h
  unfold completed
  rw [show (1 : ℂ) - s = -(s - 1) by ring, h, sub_add_cancel]

/-! ### The Dirichlet series -/

theorem integral_norm_scaled {s : ℂ} {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * modifiedBesselKOrder (c * t) (nu lam)‖ =
      c ^ (-s.re) * ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * modifiedBesselKOrder t (nu lam)‖ := by
  have h : ∫ t in Ioi (0 : ℝ), ‖(((c * t : ℝ)) : ℂ) ^ (s - 1) * modifiedBesselKOrder (c * t) (nu lam)‖ =
      c⁻¹ * ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * modifiedBesselKOrder t (nu lam)‖ := by
    have := integral_comp_mul_left_Ioi
      (fun x : ℝ => ‖(x : ℂ) ^ (s - 1) * modifiedBesselKOrder x (nu lam)‖) 0 hc
    simpa only [mul_zero, smul_eq_mul] using this
  have hcc : c ^ (1 - s.re) * c ^ ((s - 1).re) = 1 := by
    rw [← Real.rpow_add hc, show 1 - s.re + (s - 1).re = 0 by rw [sub_re, one_re]; ring, Real.rpow_zero]
  have e : EqOn (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) * modifiedBesselKOrder (c * t) (nu lam)‖)
      (fun t : ℝ => c ^ (1 - s.re) *
        ‖(((c * t : ℝ)) : ℂ) ^ (s - 1) * modifiedBesselKOrder (c * t) (nu lam)‖) (Ioi 0) := by
    intro t ht
    have ht0 : 0 < t := ht
    simp only
    rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos (mul_pos hc ht0),
      Real.mul_rpow hc.le ht0.le]
    linear_combination (-(t ^ ((s - 1).re) * ‖modifiedBesselKOrder (c * t) (nu lam)‖)) * hcc
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul, h, ← mul_assoc,
    ← Real.rpow_neg_one, ← Real.rpow_add hc, show 1 - s.re + -1 = -s.re by ring]

/-- **The Dirichlet series of the completed L-function.** For `Re s > 3/2`,
`Λ(s) = 2^{s-2} Γ((s+ν)/2) Γ((s-ν)/2) Σ_n ρ(n) (2π|n|)^{-s}`, absolutely convergent. -/
theorem completed_eq (hg : g ∈ cuspSpace lam) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lam)) {s : ℂ} (hs : 3 / 2 < s.re) :
    HasSum (fun n : ℤ => ρ n * ((2 * Real.pi * |(n : ℝ)| : ℝ) : ℂ) ^ (-s) *
      ((2 : ℂ) ^ (s - 2) * Gamma ((s + nu lam) / 2) * Gamma ((s - nu lam) / 2))) (completed g s) := by
  obtain ⟨C, hC0, hC⟩ := exists_coeff_bound hg hρ0 hρ
  have hs0 : 0 < s.re := by linarith
  have hν : |(nu lam).re| < s.re := by rw [nu_re, abs_zero]; exact hs0
  -- the termwise integrand
  set T : ℤ → ℝ → ℂ := fun n t => (t : ℂ) ^ (s - 1) * (((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * fourierCoeff g n t)
  have hT : ∀ n : ℤ, ∀ t ∈ Ioi (0 : ℝ), T n t =
      ρ n * ((t : ℂ) ^ (s - 1) * modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * t) (nu lam)) := by
    intro n t ht
    have ht0 : 0 < t := ht
    have hs1 : t ^ (-(1 / 2 : ℝ)) * Real.sqrt t = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0]; norm_num
    simp only [T]
    rw [hρ n t ht0]
    have : (((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Real.sqrt t : ℂ)) = 1 := by
      rw [← ofReal_mul, hs1, ofReal_one]
    linear_combination ((t : ℂ) ^ (s - 1) * ρ n *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * t) (nu lam)) * this
  have hint : ∀ n : ℤ, IntegrableOn (T n) (Ioi 0) := by
    intro n
    by_cases hn : n = 0
    · refine (integrableOn_zero).congr_fun (fun t ht => ?_) measurableSet_Ioi
      rw [hT n t ht, hn, hρ0, zero_mul]
    have hc : 0 < 2 * Real.pi * |(n : ℝ)| := by
      have := abs_pos.2 (Int.cast_ne_zero.2 hn : (n : ℝ) ≠ 0); positivity
    refine IntegrableOn.congr_fun
      ((RHTower.WeilWorkDeficitMellin.scaled_integrable hν hc).const_mul (ρ n)) (fun t ht => ?_)
      measurableSet_Ioi
    rw [hT n t ht]
  set J := ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * modifiedBesselKOrder t (nu lam)‖
  have hnorm : ∀ n : ℤ, ∫ t in Ioi (0 : ℝ), ‖T n t‖ =
      ‖ρ n‖ * ((2 * Real.pi * |(n : ℝ)|) ^ (-s.re) * J) := by
    intro n
    rw [setIntegral_congr_fun measurableSet_Ioi (show EqOn (fun t => ‖T n t‖) (fun t =>
      ‖ρ n * ((t : ℂ) ^ (s - 1) * modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * t) (nu lam))‖) (Ioi 0)
      from fun t ht => by simp only; rw [hT n t ht])]
    by_cases hn : n = 0
    · simp [hn, hρ0]
    have hc : 0 < 2 * Real.pi * |(n : ℝ)| := by
      have := abs_pos.2 (Int.cast_ne_zero.2 hn : (n : ℝ) ≠ 0); positivity
    simp_rw [norm_mul (ρ n)]
    rw [integral_const_mul, integral_norm_scaled hc]
  have hsumm : Summable fun n : ℤ => ∫ t in Ioi (0 : ℝ), ‖T n t‖ := by
    simp_rw [hnorm]
    have hb : 1 < s.re - 1 / 2 := by linarith
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((Real.summable_abs_int_rpow hb).mul_left (C * (2 * Real.pi) ^ (-s.re) * J))
    have hJ : 0 ≤ J := integral_nonneg fun _ => norm_nonneg _
    by_cases hn : n = 0
    · rw [hn, hρ0, norm_zero, zero_mul]
      positivity
    have hn0 : 0 < |(n : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hn)
    rw [Real.mul_rpow (by positivity) hn0.le]
    have hsq : Real.sqrt |(n : ℝ)| * |(n : ℝ)| ^ (-s.re) = |(n : ℝ)| ^ (-(s.re - 1 / 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]; congr 1; ring
    calc ‖ρ n‖ * ((2 * Real.pi) ^ (-s.re) * |(n : ℝ)| ^ (-s.re) * J)
        ≤ (C * Real.sqrt |(n : ℝ)|) * ((2 * Real.pi) ^ (-s.re) * |(n : ℝ)| ^ (-s.re) * J) := by
          gcongr; exact hC n
      _ = C * (2 * Real.pi) ^ (-s.re) * J * (Real.sqrt |(n : ℝ)| * |(n : ℝ)| ^ (-s.re)) := by ring
      _ = C * (2 * Real.pi) ^ (-s.re) * J * |(n : ℝ)| ^ (-(s.re - 1 / 2)) := by rw [hsq]
  have hmain := hasSum_integral_of_summable_integral_norm hint hsumm
  have hlim : ∫ t in Ioi (0 : ℝ), ∑' n, T n t = completed g s := by
    unfold completed mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    simp only [T]
    rw [tsum_mul_left, tsum_mul_left, (hasSum_axis hg ht0).tsum_eq, smul_eq_mul, profile]
  rw [hlim] at hmain
  refine hmain.congr_fun fun n => ?_
  by_cases hn : n = 0
  · rw [hn, hρ0, setIntegral_congr_fun measurableSet_Ioi
      (show EqOn (T 0) (fun _ => (0 : ℂ)) (Ioi 0) from fun t ht => by rw [hT 0 t ht, hρ0, zero_mul])]
    simp
  have hc : 0 < 2 * Real.pi * |(n : ℝ)| := by
    have := abs_pos.2 (Int.cast_ne_zero.2 hn : (n : ℝ) ≠ 0); positivity
  rw [setIntegral_congr_fun measurableSet_Ioi (show EqOn (T n) (fun t => ρ n * ((t : ℂ) ^ (s - 1) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * t) (nu lam))) (Ioi 0) from fun t ht => hT n t ht),
    integral_const_mul, RHTower.WeilWorkDeficitMellin.scaled_mellin hν hc]
  ring

/-- The L-series `L(s) = Σ_{n ≠ 0} ρ(n) |n|^{-s}`. -/
def lSeries (ρ : ℤ → ℂ) (s : ℂ) : ℂ := ∑' n : ℤ, ρ n * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)

/-- The L-function `L(s) = 4 π^s Λ(s) / (Γ((s+ν)/2) Γ((s-ν)/2))`. -/
def lFun (g : UpperHalfPlane → ℂ) (lam : ℝ) (s : ℂ) : ℂ :=
  4 * (Real.pi : ℂ) ^ s * (Gamma ((s + nu lam) / 2))⁻¹ * (Gamma ((s - nu lam) / 2))⁻¹ * completed g s

theorem differentiable_lFun (hg : g ∈ cuspSpace lam) : Differentiable ℂ (lFun g lam) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have h1 : Differentiable ℂ fun s : ℂ => (Real.pi : ℂ) ^ s := fun s =>
    (differentiableAt_id.const_cpow (Or.inl hpi))
  have h2 : Differentiable ℂ fun s : ℂ => (Gamma ((s + nu lam) / 2))⁻¹ :=
    differentiable_one_div_Gamma.comp ((differentiable_id.add_const _).div_const _)
  have h3 : Differentiable ℂ fun s : ℂ => (Gamma ((s - nu lam) / 2))⁻¹ :=
    differentiable_one_div_Gamma.comp ((differentiable_id.sub_const _).div_const _)
  exact ((((differentiable_const _).mul h1).mul h2).mul h3).mul (differentiable_completed hg)

/-- **The L-function of a cusp mode.** Every cusp form `g` of eigenvalue `λ` of the modular horizon has
Whittaker modes `a_n(y) = ρ(n) √y K_ν(2π|n|y)`, `ν = i√(λ - ¼)`; its L-series `Σ_{n≠0} ρ(n)|n|^{-s}`
converges absolutely for `Re s > 3/2` and equals the entire function `L`; and
`Λ(s) = ¼ π^{-s} Γ((s+ν)/2) Γ((s-ν)/2) L(s)` there, where `Λ` is entire with `Λ(1 - s) = Λ(s)`. -/
theorem cusp_L_function (hg : g ∈ cuspSpace lam) :
    ∃ ρ : ℤ → ℂ, (∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
        modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lam)) ∧
      Differentiable ℂ (lFun g lam) ∧ Differentiable ℂ (completed g) ∧
      (∀ s, completed g (1 - s) = completed g s) ∧
      ∀ s : ℂ, 3 / 2 < s.re →
        Summable (fun n : ℤ => ρ n * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)) ∧
        lFun g lam s = lSeries ρ s ∧
        completed g s = 1 / 4 * (Real.pi : ℂ) ^ (-s) * Gamma ((s + nu lam) / 2) *
          Gamma ((s - nu lam) / 2) * lSeries ρ s := by
  obtain ⟨ρ, hρ0, hρ⟩ := exists_whittaker hg
  refine ⟨ρ, hρ, differentiable_lFun hg, differentiable_completed hg, completed_one_sub hg,
    fun s hs => ?_⟩
  have hsum := completed_eq hg hρ0 hρ hs
  set G := (2 : ℂ) ^ (s - 2) * Gamma ((s + nu lam) / 2) * Gamma ((s - nu lam) / 2)
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hg1 : Gamma ((s + nu lam) / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [nu_re]; linarith)
  have hg2 : Gamma ((s - nu lam) / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [nu_re]; linarith)
  have hp : (Real.pi : ℂ) ^ (-s) ≠ 0 := by rw [cpow_def_of_ne_zero hpi]; exact exp_ne_zero _
  have hps : (Real.pi : ℂ) ^ s ≠ 0 := by rw [cpow_def_of_ne_zero hpi]; exact exp_ne_zero _
  set E := 1 / 4 * (Real.pi : ℂ) ^ (-s) * Gamma ((s + nu lam) / 2) * Gamma ((s - nu lam) / 2)
  have hne : E ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hp) hg1) hg2
  have h2pi : ∀ n : ℤ, ((2 * Real.pi * |(n : ℝ)| : ℝ) : ℂ) ^ (-s) =
      (2 : ℂ) ^ (-s) * (Real.pi : ℂ) ^ (-s) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s) := by
    intro n
    rw [ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) (abs_nonneg _), ofReal_mul,
      mul_cpow_ofReal_nonneg (by norm_num) Real.pi_pos.le]
    push_cast
    ring
  have h22 : (2 : ℂ) ^ (s - 2) * (2 : ℂ) ^ (-s) = 1 / 4 := by
    rw [← cpow_add _ _ (by norm_num), show s - 2 + -s = ((-2 : ℤ) : ℂ) by push_cast; ring, cpow_intCast]
    norm_num
  have hfac : G * ((2 : ℂ) ^ (-s) * (Real.pi : ℂ) ^ (-s)) = E := by
    simp only [G, E]
    linear_combination (Gamma ((s + nu lam) / 2) * Gamma ((s - nu lam) / 2) * (Real.pi : ℂ) ^ (-s)) * h22
  have hL : HasSum (fun n : ℤ => ρ n * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)) (completed g s / E) := by
    refine (hsum.div_const E).congr_fun fun n => ?_
    rw [h2pi n, eq_div_iff hne]
    linear_combination (-(ρ n * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s))) * hfac
  have hLs : lSeries ρ s = completed g s / E := hL.tsum_eq
  refine ⟨hL.summable, ?_, ?_⟩
  · rw [hLs]
    unfold lFun
    simp only [E]
    rw [cpow_neg]
    field_simp
  · rw [hLs]
    field_simp

end CuspL

end GaloisForLFunctions.BlackHoleRingdown
