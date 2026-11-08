import GaloisForLFunctions.BlackHoleRingdown.TheRankinSelbergIntegralOfTheCuspModes
import GaloisForLFunctions.BlackHoleRingdown.TheEisensteinFunctionIsAutomorphic
import GaloisForLFunctions.RHTower.OddWeilFunctionRigidity
import GaloisForLFunctions.CompletedArithmeticForms.BesselPositiveCutoff

/-!
# The continuation of the Rankin–Selberg function of a cusp mode

For a cusp form `g` of the modular horizon the completed Rankin–Selberg function

  `Λ_g(s) = ∫_𝒟 |g(z)|² E*(s - ½; z) dμ(z)`,   `E* = ξ(1+2u) E/((1+2u)(2u))`,

is holomorphic on `ℂ ∖ {0, ½, 1}` (`differentiableOn_completedRS`) and satisfies `Λ_g(1 - s) = Λ_g(s)`
(`completedRS_one_sub`). For `Re s > 1`, `Im s ≠ 0` it is
`½ Λ(2s) (2π)^{-s} G(s) Σ_{n≠0} |ρ(n)|² |n|^{-s}` with `Λ(s) = π^{-s/2}Γ(s/2)ζ(s)` the completed zeta function
(`completedRS_eq`). So the Rankin–Selberg series of every cusp mode continues meromorphically to the plane, its
poles lie among `s = 0, ½, 1` and the zeros of `Λ(2s) G(s)` — the zeros of `ζ(2s)` enter the quadratic response
of a cusp tone to the Eisenstein channel. On `Re s > ½` the only possible pole is `s = 1`
(`rankinSelberg_continuation`).

**Bounds.** Cusp forms decay exponentially in the cusp, uniformly in `x`: Fourier inversion at every point and
the modal bounds give `|g(x+iy)| ≤ D √y e^{-2πy}` (`norm_point_le`). The Whittaker tail of the Eisenstein function
is bounded uniformly for `Y ≥ ½` and `|Re u| ≤ R` (`norm_weightedTail_le`): each mode is at most
`(N+1)^k √Y e^{1-2π(N+1)Y} M_R`, summable uniformly. Hence on a closed ball in `ℂ∖{0, ±½}` the integrand
`|g|² E*(u)` is dominated on `𝒟` by `|g|²(a Y^A + b)`, a bounded function on a set of finite measure, and the
corpus Cauchy-domination lemma gives holomorphy. The functional equation and the identification on `Re s > 1`
come from the automorphic Eisenstein function and the Rankin–Selberg identity.
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.DeckPointPair
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos)
open GaloisForLFunctions.RHTower.SelbergMaassMean (point directional)

namespace CuspRSC

open HeckeCusp CuspL

variable {lamE : ℝ} {g : UpperHalfPlane → ℂ} {ρ : ℤ → ℂ}

/-! ### Uniform decay of a cusp form in the cusp -/

/-- **Fourier inversion at a point of `(0, 1]`.** -/
theorem hasSum_point (hg : g ∈ cuspSpace lamE) {x y : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (hy : 0 < y) :
    HasSum (fun n : ℤ => fourierCoeff g n y * fourier n ((x : ℝ) : AddCircle ((1 : ℝ) - 0)))
      (g (ofComplex (point x y))) := by
  set F : ℂ → ℂ := g ∘ ofComplex
  have hF : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im} := hg.2.1.1
  have hF1 : ContDiffOn ℝ 1 F {z : ℂ | 0 < z.im} := hF.of_le (by norm_num)
  have hD : ContDiffOn ℝ 1 (directional 1 F) {z : ℂ | 0 < z.im} :=
    GaloisForLFunctions.RHTower.SelbergMaassMean.directional_contDiffOn hF (m := 1) le_rfl 1
  have hD2 : ContDiffOn ℝ 0 (directional 1 (directional 1 F)) {z : ℂ | 0 < z.im} :=
    GaloisForLFunctions.RHTower.SelbergMaassMean.directional_contDiffOn hD (m := 0) (by simp) 1
  have hp : ∀ x, F (point (x + 1) y) = F (point x y) := fun x => by
    rw [WeylUpper.point_add_one]; exact periodic_comp hg _ (point_im_pos hy)
  have hp' := GaloisForLFunctions.RHTower.SelbergMaassMean.directional_periodic hF1 hy 1 hp
  have hp'' := GaloisForLFunctions.RHTower.SelbergMaassMean.directional_periodic hD hy 1 hp'
  set f'' : ℝ → ℂ := fun x => directional 1 (directional 1 F) (point x y)
  have hc'' : Continuous f'' := GaloisForLFunctions.RHTower.SelbergMaassMean.slice_continuous hD2.continuousOn hy
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖f'' x‖ ≤ C := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hc''.continuousOn (s := Icc (0 : ℝ) 1))
    refine ⟨C, fun x => ?_⟩
    obtain ⟨x', hx', hxx⟩ := (show Function.Periodic f'' 1 from fun x => hp'' x).exists_mem_Ico₀
      one_pos x
    rw [hxx]
    exact hC x' (Ico_subset_Icc_self hx')
  have h := GaloisForLFunctions.RHTower.hasSum_fourier_of_periodic_two (a := 0) (b := 1) zero_lt_one
    (f := fun x => F (point x y)) (f' := fun x => directional 1 F (point x y)) (f'' := f'')
    (fun x _ => GaloisForLFunctions.RHTower.SelbergMaassMean.slice_horizontal hF1 hy x)
    (fun x _ => GaloisForLFunctions.RHTower.SelbergMaassMean.slice_horizontal hD hy x)
    ((GaloisForLFunctions.RHTower.SelbergMaassMean.slice_continuous hD.continuousOn hy).intervalIntegrable _ _)
    (hc''.intervalIntegrable _ _) hC (by simpa using hp 0) (by simpa using hp' 0) hx
  convert h using 1
  funext n
  unfold HeckeCusp.fourierCoeff
  rw [GaloisForLFunctions.RHTower.SelbergMaassParseval.coefficient_eq_fourierCoeffOn 1 one_pos F y n]
  rfl

theorem norm_fourier_eq_one (n : ℤ) (x : ℝ) : ‖fourier n ((x : ℝ) : AddCircle ((1 : ℝ) - 0))‖ = 1 := by
  rw [fourier_coe_apply, Complex.norm_exp]
  simp

/-- **Cusp forms decay exponentially in the cusp, uniformly in `x`**: `|g(x+iy)| ≤ D √y e^{-2πy}`. -/
theorem norm_point_le (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    ∃ D, 0 ≤ D ∧ ∀ x y : ℝ, 1 ≤ y →
      ‖g (ofComplex (point x y))‖ ≤ D * (Real.sqrt y * Real.exp (-(2 * Real.pi * y))) := by
  obtain ⟨b, hbs, hb0, hmode⟩ := CuspL.norm_mode_le hg hρ0 hρ
  refine ⟨∑' n, b n, tsum_nonneg hb0, fun x y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  set x' := x - ⌈x⌉ + 1
  have hx' : x' ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · have := Int.ceil_lt_add_one x; simp only [x']; linarith
    · have := Int.le_ceil x; simp only [x']; linarith
  have hper : Function.Periodic (fun t : ℝ => g (ofComplex (point t y))) 1 := fun t => by
    have := periodic_comp hg (point t y) (point_im_pos hy0)
    simp only [Function.comp] at this
    simp only [WeylUpper.point_add_one, this]
  have hxx : g (ofComplex (point x y)) = g (ofComplex (point x' y)) := by
    have h := hper.sub_int_mul_eq (x := x) (n := ⌈x⌉ - 1)
    simp only [mul_one] at h
    rw [← h]
    congr 3
    simp only [x']; push_cast; ring
  rw [hxx]
  have hs := hasSum_point hg hx' hy0
  have hsum : Summable fun n : ℤ => ‖fourierCoeff g n y‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hmode n y hy) (hbs.mul_right _)
  calc ‖g (ofComplex (point x' y))‖
      = ‖∑' n, fourierCoeff g n y * fourier n ((x' : ℝ) : AddCircle ((1 : ℝ) - 0))‖ := by
        rw [hs.tsum_eq]
    _ ≤ ∑' n, ‖fourierCoeff g n y * fourier n ((x' : ℝ) : AddCircle ((1 : ℝ) - 0))‖ :=
        norm_tsum_le_tsum_norm (hsum.congr fun n => by rw [norm_mul, norm_fourier_eq_one, mul_one])
    _ = ∑' n, ‖fourierCoeff g n y‖ := by
        congr 1; funext n; rw [norm_mul, norm_fourier_eq_one, mul_one]
    _ ≤ ∑' n, b n * (Real.sqrt y * Real.exp (-(2 * Real.pi * y))) :=
        hsum.tsum_le_tsum (fun n => hmode n y hy) (hbs.mul_right _)
    _ = (∑' n, b n) * (Real.sqrt y * Real.exp (-(2 * Real.pi * y))) := tsum_mul_right

/-! ### A height-uniform bound for the Whittaker tail -/

/-- `M_R = ∫_0^∞ e^{-cosh t} cosh(Rt) dt`. -/
def kMass (R : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), Real.exp (-1 * Real.cosh t) * Real.cosh (R * t)

theorem norm_besselK_le {R : ℝ} (hR : 0 ≤ R) {ν : ℂ} (hν : |ν.re| ≤ R) {X : ℝ} (hX : 1 ≤ X) :
    ‖modifiedBesselKOrder X ν‖ ≤ Real.exp (1 - X) * kMass R := by
  refine (GaloisForLFunctions.CompletedArithmeticForms.norm_modifiedBesselKOrder_le_positive_base
    one_pos hX ν).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-1 * Real.cosh t) * Real.cosh (R * t)) (Ioi 0) := by
    have h : IntegrableOn (fun t => ‖besselOrderKernel 1 (R : ℂ) t‖) (Ioi 0) :=
      (integrableOn_besselOrderKernel one_pos (R : ℂ)).norm
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    show ‖besselOrderKernel 1 (R : ℂ) t‖ = _
    rw [besselOrderKernel_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le)]
  refine setIntegral_mono_on (integrableOn_besselOrderKernel one_pos ν).norm hint measurableSet_Ioi
    fun t ht => ?_
  refine (norm_besselOrderKernel_le_re 1 ν t).trans ?_
  have ht0 : 0 ≤ t := le_of_lt ht
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  · rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_right hν ht0

theorem summable_pow_exp (k : ℕ) :
    Summable fun N : ℕ => ((N : ℝ) + 1) ^ k * Real.exp (-(Real.pi * ((N : ℝ) + 1))) := by
  have hr1 : Real.exp (-Real.pi) < 1 := by
    have := Real.exp_lt_exp.2 (show -Real.pi < 0 by linarith [Real.pi_pos])
    rwa [Real.exp_zero] at this
  have hr : ‖Real.exp (-Real.pi)‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have h0 : Summable fun n : ℕ => (n : ℝ) ^ k * Real.exp (-Real.pi) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one k hr
  have h := h0.comp_injective (add_left_injective 1)
  refine h.congr fun N => ?_
  have e : Real.exp (-Real.pi) ^ (N + 1) = Real.exp (-(Real.pi * ((N : ℝ) + 1))) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, e]

/-- A summable majorant of the modes of the Whittaker tail, uniform for `Y ≥ ½` and `|Re u| ≤ R`. -/
theorem exists_term_bound {R : ℝ} (hR : 0 ≤ R) :
    ∃ b : ℕ → ℝ, Summable b ∧ ∀ (N : ℕ) (u : ℂ) (negative : Bool) (x Y : ℝ), |u.re| ≤ R → 1 / 2 ≤ Y →
      ‖modeCoefficient u N * d4BMSignedWhittakerMode negative N u x Y‖ ≤ b N := by
  set k := ⌈3 * R + 1⌉₊
  have hM : 0 ≤ kMass R := setIntegral_nonneg measurableSet_Ioi fun t _ =>
    mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
  set b : ℕ → ℝ := fun N => Real.exp (1 + Real.pi) * kMass R *
    (((N : ℝ) + 1) ^ k * Real.exp (-(Real.pi * ((N : ℝ) + 1))))
  have hbs : Summable b := (summable_pow_exp k).mul_left _
  refine ⟨b, hbs, fun N u negative x Y hu hY => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hterm : ‖modeCoefficient u N * d4BMSignedWhittakerMode negative N u x Y‖ ≤ b N := by
    have hX : 1 ≤ 2 * Real.pi * ((N : ℝ) + 1) * Y := by
      have h1 : (1 / 2 : ℝ) ≤ ((N : ℝ) + 1) * Y := by
        have := N.cast_nonneg (α := ℝ); nlinarith
      rw [show 2 * Real.pi * ((N : ℝ) + 1) * Y = 2 * Real.pi * (((N : ℝ) + 1) * Y) by ring]
      nlinarith [Real.pi_gt_three]
    have hK := norm_besselK_le hR hu hX
    rw [norm_mul, d4BMSignedWhittakerMode, norm_mul, d4BM_norm_completedEisensteinFourierPhase, one_mul,
      d4BMWhittakerP0, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hc := norm_modeCoefficient_le hu N
    have hsq : Real.sqrt Y * Real.exp (1 - 2 * Real.pi * ((N : ℝ) + 1) * Y) ≤
        Real.exp (1 + Real.pi) * Real.exp (-(Real.pi * ((N : ℝ) + 1))) := by
      have h1 : Real.sqrt Y ≤ Real.exp Y :=
        (Real.sqrt_le_left (by positivity)).2 (by nlinarith [Real.add_one_le_exp Y, Real.exp_pos Y])
      calc Real.sqrt Y * Real.exp (1 - 2 * Real.pi * ((N : ℝ) + 1) * Y)
          ≤ Real.exp Y * Real.exp (1 - 2 * Real.pi * ((N : ℝ) + 1) * Y) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = Real.exp (Y + (1 - 2 * Real.pi * ((N : ℝ) + 1) * Y)) := by rw [Real.exp_add]
        _ ≤ Real.exp (1 + Real.pi + -(Real.pi * ((N : ℝ) + 1))) := by
            refine Real.exp_le_exp.2 ?_
            have hN : (0 : ℝ) ≤ N := N.cast_nonneg
            nlinarith [mul_nonneg (sub_nonneg.2 hY)
              (show 0 ≤ 2 * Real.pi * ((N : ℝ) + 1) - 1 by nlinarith [Real.pi_gt_three]), Real.pi_gt_three]
        _ = Real.exp (1 + Real.pi) * Real.exp (-(Real.pi * ((N : ℝ) + 1))) := by rw [← Real.exp_add]
    have hscale : ((d4BMPositiveFourierScale N : ℝ)) = 2 * Real.pi * ((N : ℝ) + 1) := rfl
    rw [hscale]
    calc ‖modeCoefficient u N‖ * (Real.sqrt Y * ‖modifiedBesselKOrder (2 * Real.pi * ((N : ℝ) + 1) * Y) u‖)
        ≤ ((N : ℝ) + 1) ^ k * (Real.sqrt Y * (Real.exp (1 - 2 * Real.pi * ((N : ℝ) + 1) * Y) * kMass R)) :=
          mul_le_mul hc (mul_le_mul_of_nonneg_left hK (Real.sqrt_nonneg _)) (by positivity) (by positivity)
      _ = ((N : ℝ) + 1) ^ k * kMass R * (Real.sqrt Y * Real.exp (1 - 2 * Real.pi * ((N : ℝ) + 1) * Y)) := by
          ring
      _ ≤ ((N : ℝ) + 1) ^ k * kMass R * (Real.exp (1 + Real.pi) * Real.exp (-(Real.pi * ((N : ℝ) + 1)))) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = b N := by simp only [b]; ring
  exact hterm

/-- **The Whittaker tail is bounded uniformly for `Y ≥ ½` and `|Re u| ≤ R`.** -/
theorem norm_weightedTail_le {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℂ) (negative : Bool) (x Y : ℝ), |u.re| ≤ R → 1 / 2 ≤ Y →
      ‖weightedTail u negative x Y‖ ≤ C := by
  obtain ⟨b, hbs, hb⟩ := exists_term_bound hR
  have hb0 : ∀ N, 0 ≤ b N := fun N => (norm_nonneg _).trans (hb N 0 false 0 1 (by simpa using hR) (by norm_num))
  refine ⟨∑' N, b N, tsum_nonneg hb0, fun u negative x Y hu hY => ?_⟩
  have hsum : Summable fun N => ‖modeCoefficient u N * d4BMSignedWhittakerMode negative N u x Y‖ :=
    Summable.of_nonneg_of_le (fun N => norm_nonneg _) (fun N => hb N u negative x Y hu hY) hbs
  calc ‖weightedTail u negative x Y‖ ≤ ∑' N, ‖modeCoefficient u N * d4BMSignedWhittakerMode negative N u x Y‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' N, b N := hsum.tsum_le_tsum (fun N => hb N u negative x Y hu hY) hbs

/-! ### Continuity in the cusp region -/

theorem continuous_term_max (u : ℂ) (negative : Bool) (N : ℕ) :
    Continuous fun z : ℍ => modeCoefficient u N *
      d4BMSignedWhittakerMode negative N u z.re (max z.im (1 / 2)) := by
  refine continuous_const.mul ?_
  unfold d4BMSignedWhittakerMode d4BMCompletedEisensteinFourierPhase d4BMWhittakerP0
  have hY : Continuous fun z : ℍ => max z.im (1 / 2) :=
    UpperHalfPlane.continuous_im.max continuous_const
  have hpos : ∀ z : ℍ, 0 < max z.im (1 / 2) := fun z => lt_max_of_lt_right (by norm_num)
  refine Continuous.mul (by fun_prop) (Continuous.mul (Complex.continuous_ofReal.comp
    (Real.continuous_sqrt.comp hY)) ?_)
  have hK : ContinuousOn (fun t : ℝ => modifiedBesselKOrder t u) (Ioi 0) := fun t ht =>
    (GaloisForLFunctions.RHTower.MaassWhittaker.hasDerivAt_besK u ht).continuousAt.continuousWithinAt
  exact hK.comp_continuous (continuous_const.mul hY) fun z => mul_pos (d4BMPositiveFourierScale N).2 (hpos z)

theorem continuous_weightedTail_max (u : ℂ) (negative : Bool) :
    Continuous fun z : ℍ => weightedTail u negative z.re (max z.im (1 / 2)) := by
  obtain ⟨b, hbs, hb⟩ := exists_term_bound (abs_nonneg u.re)
  unfold weightedTail
  exact continuous_tsum (fun N => continuous_term_max u negative N) hbs
    fun N z => hb N u negative _ _ le_rfl (le_max_right _ _)

theorem continuous_completed_max (u : ℂ) :
    Continuous fun z : ℍ => EisAuto.completedEisenstein u z.re (max z.im (1 / 2)) := by
  have hY : Continuous fun z : ℍ => max z.im (1 / 2) := UpperHalfPlane.continuous_im.max continuous_const
  have hpos : ∀ z : ℍ, 0 < max z.im (1 / 2) := fun z => lt_max_of_lt_right (by norm_num)
  have hcp : ∀ w : ℂ, Continuous fun z : ℍ => ((max z.im (1 / 2) : ℝ) : ℂ) ^ w := fun w =>
    continuous_iff_continuousAt.2 fun z =>
      (continuousAt_cpow_const (ofReal_mem_slitPlane.2 (hpos z))).comp
        (f := fun z : ℍ => ((max z.im (1 / 2) : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hY).continuousAt
  unfold EisAuto.completedEisenstein eisensteinNumerator eisTail
  refine Continuous.div_const ?_ _
  exact (((hcp _).mul continuous_const).add ((continuous_const.mul continuous_const).mul (hcp _))).add
    (continuous_const.mul ((continuous_weightedTail_max u false).add (continuous_weightedTail_max u true)))

/-! ### Domination on compact sets of parameters -/

theorem norm_cpow_le {Y a : ℝ} (hY : 1 / 2 ≤ Y) (ha : 0 ≤ a) {w : ℂ} (hw : |w.re| ≤ a) :
    ‖(Y : ℂ) ^ w‖ ≤ Y ^ a + 2 ^ a := by
  have hY0 : 0 < Y := by linarith
  rw [norm_cpow_eq_rpow_re_of_pos hY0]
  rcases le_or_gt 1 Y with h1 | h1
  · have := Real.rpow_le_rpow_of_exponent_le h1 (le_of_abs_le hw)
    linarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) a]
  · have h2 : Y ^ w.re ≤ Y ^ (-a) :=
      Real.rpow_le_rpow_of_exponent_ge hY0 h1.le (by linarith [neg_abs_le w.re])
    have h3 : Y ^ (-a) ≤ 2 ^ a := by
      rw [Real.rpow_neg hY0.le, ← Real.inv_rpow hY0.le]
      exact Real.rpow_le_rpow (by positivity) (by rw [inv_le_comm₀ hY0 (by norm_num)]; linarith) ha
    linarith [Real.rpow_nonneg hY0.le a]

/-- **`E*` is dominated by `α Y^a + β` for `Y ≥ ½`, uniformly on a compact set of regular parameters.** -/
theorem exists_completed_bound {K : Set ℂ} (hK : IsCompact K)
    (hKU : ∀ u ∈ K, u ≠ 1 / 2 ∧ u ≠ 0 ∧ u ≠ -(1 / 2)) :
    ∃ α β a : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ a ∧ ∀ u ∈ K, ∀ (x Y : ℝ), 1 / 2 ≤ Y →
      ‖EisAuto.completedEisenstein u x Y‖ ≤ α * Y ^ a + β := by
  rcases K.eq_empty_or_nonempty with hE | hne
  · exact ⟨0, 0, 0, le_rfl, le_rfl, le_rfl, fun u hu => by simp [hE] at hu⟩
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (Complex.continuous_re.continuousOn (s := K))
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ hne.some_mem)
  set a := A + 1 / 2
  have hcont1 : ContinuousOn (fun u : ℂ => xi (1 + 2 * u)) K :=
    (differentiable_xi_shift).continuous.continuousOn
  have hcont2 : ContinuousOn (fun u : ℂ => (1 + 2 * u) / (2 * u - 1) * xi (2 * u)) K := by
    refine ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun u hu => ?_)
      ((xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)).continuous.continuousOn)
    intro h; exact (hKU u hu).1 (by linear_combination h / 2)
  have hcont3 : ContinuousOn (fun u : ℂ => (1 + 2 * u) * (2 * u)) K := by fun_prop
  obtain ⟨K₁, hK₁⟩ := hK.exists_bound_of_continuousOn hcont1
  obtain ⟨K₂, hK₂⟩ := hK.exists_bound_of_continuousOn hcont2
  obtain ⟨K₃, hK₃⟩ := hK.exists_bound_of_continuousOn hcont3
  obtain ⟨u₀, hu₀, hmin⟩ := hK.exists_isMinOn hne (hcont3.norm)
  set m := ‖(1 + 2 * u₀) * (2 * u₀)‖
  have hm : 0 < m := by
    refine norm_pos_iff.2 (mul_ne_zero (fun h => (hKU u₀ hu₀).2.2 (by linear_combination h / 2))
      (mul_ne_zero two_ne_zero (hKU u₀ hu₀).2.1))
  obtain ⟨Ct, hCt0, hCt⟩ := norm_weightedTail_le hA0
  have hK₁0 : 0 ≤ K₁ := (norm_nonneg _).trans (hK₁ _ hne.some_mem)
  have hK₂0 : 0 ≤ K₂ := (norm_nonneg _).trans (hK₂ _ hne.some_mem)
  have hK₃0 : 0 ≤ K₃ := (norm_nonneg _).trans (hK₃ _ hne.some_mem)
  refine ⟨(K₁ + K₂) / m, ((K₁ + K₂) * 2 ^ a + K₃ * (2 * Ct)) / m, a, by positivity, by positivity,
    by positivity, fun u hu x Y hY => ?_⟩
  have hre : |u.re| ≤ A := by simpa [Real.norm_eq_abs] using hA u hu
  have hre' := abs_le.1 hre
  have hw1 : |(1 / 2 + u).re| ≤ a := by
    have : (1 / 2 + u).re = 1 / 2 + u.re := by simp
    rw [this, abs_le]; simp only [a]; constructor <;> linarith
  have hw2 : |(1 / 2 - u).re| ≤ a := by
    have : (1 / 2 - u).re = 1 / 2 - u.re := by simp
    rw [this, abs_le]; simp only [a]; constructor <;> linarith
  have hP1 := norm_cpow_le hY (by positivity) hw1
  have hP2 := norm_cpow_le hY (by positivity) hw2
  have hT : ‖eisTail u x Y‖ ≤ 2 * Ct := by
    unfold eisTail
    refine (norm_add_le _ _).trans ?_
    linarith [hCt u false x Y hre hY, hCt u true x Y hre hY]
  have hnum : ‖eisensteinNumerator u x Y‖ ≤ (K₁ + K₂) * (Y ^ a + 2 ^ a) + K₃ * (2 * Ct) := by
    unfold eisensteinNumerator
    have e1 : ‖(Y : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u)‖ ≤ (Y ^ a + 2 ^ a) * K₁ := by
      rw [norm_mul]; exact mul_le_mul hP1 (hK₁ u hu) (norm_nonneg _) (by positivity)
    have e2 : ‖(1 + 2 * u) / (2 * u - 1) * xi (2 * u) * (Y : ℂ) ^ (1 / 2 - u)‖ ≤ K₂ * (Y ^ a + 2 ^ a) := by
      rw [norm_mul]; exact mul_le_mul (hK₂ u hu) hP2 (norm_nonneg _) hK₂0
    have e3 : ‖(1 + 2 * u) * (2 * u) * eisTail u x Y‖ ≤ K₃ * (2 * Ct) := by
      rw [norm_mul]; exact mul_le_mul (hK₃ u hu) hT (norm_nonneg _) hK₃0
    calc _ ≤ ‖(Y : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u)‖ +
          ‖(1 + 2 * u) / (2 * u - 1) * xi (2 * u) * (Y : ℂ) ^ (1 / 2 - u)‖ +
          ‖(1 + 2 * u) * (2 * u) * eisTail u x Y‖ := norm_add₃_le
      _ ≤ (Y ^ a + 2 ^ a) * K₁ + K₂ * (Y ^ a + 2 ^ a) + K₃ * (2 * Ct) := by linarith
      _ = (K₁ + K₂) * (Y ^ a + 2 ^ a) + K₃ * (2 * Ct) := by ring
  have hden : m ≤ ‖(1 + 2 * u) * (2 * u)‖ := hmin hu
  unfold EisAuto.completedEisenstein
  rw [norm_div]
  calc ‖eisensteinNumerator u x Y‖ / ‖(1 + 2 * u) * (2 * u)‖
      ≤ ((K₁ + K₂) * (Y ^ a + 2 ^ a) + K₃ * (2 * Ct)) / m :=
        div_le_div₀ (by positivity) hnum hm hden
    _ = (K₁ + K₂) / m * Y ^ a + ((K₁ + K₂) * 2 ^ a + K₃ * (2 * Ct)) / m := by ring

/-- **`|g|²(α Y^a + β)` is bounded on the modular domain.** -/
theorem exists_bound_on_fd (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {α β a : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (ha : 0 ≤ a) : ∃ B, ∀ z ∈ ModularGroup.fd, ‖g z‖ ^ 2 * (α * z.im ^ a + β) ≤ B := by
  obtain ⟨Cg, hCg⟩ := exists_bound hg
  obtain ⟨D, hD0, hD⟩ := norm_point_le hg hρ0 hρ
  set n := ⌈a + 1⌉₊
  refine ⟨Cg ^ 2 * (α + β) + D ^ 2 * (α + β) * n.factorial, fun z hz => ?_⟩
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg z)
  set y := z.im
  have hy0 : 0 < y := z.im_pos
  rcases le_or_gt y 1 with hy1 | hy1
  · have hya : y ^ a ≤ 1 := Real.rpow_le_one hy0.le hy1 ha
    have h1 : ‖g z‖ ^ 2 ≤ Cg ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hCg z) 2
    have h2 : α * y ^ a + β ≤ α + β := by nlinarith
    have : ‖g z‖ ^ 2 * (α * y ^ a + β) ≤ Cg ^ 2 * (α + β) :=
      mul_le_mul h1 h2 (by positivity) (sq_nonneg _)
    have : 0 ≤ D ^ 2 * (α + β) * n.factorial := by positivity
    linarith
  · have hz' : ofComplex (point z.re z.im) = z := by
      apply UpperHalfPlane.ext
      rw [ofComplex_apply_of_im_pos (point_im_pos z.im_pos)]
      simp [point]
      exact Complex.re_add_im (z : ℂ)
    have hgz := hD z.re y hy1.le
    rw [hz'] at hgz
    have hsq : ‖g z‖ ^ 2 ≤ D ^ 2 * (y * Real.exp (-(4 * Real.pi * y))) := by
      have := pow_le_pow_left₀ (norm_nonneg _) hgz 2
      have e : Real.exp (-(2 * Real.pi * y)) ^ 2 = Real.exp (-(4 * Real.pi * y)) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [mul_pow, mul_pow, Real.sq_sqrt hy0.le, e] at this
      exact this
    -- `y^{a+1} e^{-4πy} ≤ n!`
    have hpoly : y * (α * y ^ a + β) ≤ (α + β) * y ^ n := by
      have hn1 : (1 : ℝ) ≤ y := hy1.le
      have h1 : y ^ (a + 1) ≤ y ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (Nat.le_ceil _)
      have h2 : y ≤ y ^ (n : ℝ) := by
        calc y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
          _ ≤ y ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by
              have := Nat.le_ceil (a + 1); have : (1 : ℝ) ≤ a + 1 := by linarith
              exact_mod_cast (by linarith : (1 : ℝ) ≤ (n : ℝ)))
      rw [Real.rpow_natCast] at h1 h2
      have h3 : y * y ^ a = y ^ (a + 1) := by rw [Real.rpow_add hy0, Real.rpow_one]; ring
      nlinarith
    have hexp : y ^ n * Real.exp (-(4 * Real.pi * y)) ≤ n.factorial := by
      have h := Real.pow_div_factorial_le_exp y hy0.le n
      rw [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos n)] at h
      have h4 : Real.exp (-(4 * Real.pi * y)) * Real.exp y ≤ 1 := by
        rw [← Real.exp_add]; exact Real.exp_le_one_iff.2 (by nlinarith [Real.pi_gt_three])
      calc y ^ n * Real.exp (-(4 * Real.pi * y)) ≤ Real.exp y * n.factorial * Real.exp (-(4 * Real.pi * y)) :=
            mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
        _ = n.factorial * (Real.exp (-(4 * Real.pi * y)) * Real.exp y) := by ring
        _ ≤ n.factorial * 1 := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = n.factorial := mul_one _
    calc ‖g z‖ ^ 2 * (α * y ^ a + β) ≤ D ^ 2 * (y * Real.exp (-(4 * Real.pi * y))) * (α * y ^ a + β) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = D ^ 2 * Real.exp (-(4 * Real.pi * y)) * (y * (α * y ^ a + β)) := by ring
      _ ≤ D ^ 2 * Real.exp (-(4 * Real.pi * y)) * ((α + β) * y ^ n) :=
          mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = D ^ 2 * (α + β) * (y ^ n * Real.exp (-(4 * Real.pi * y))) := by ring
      _ ≤ D ^ 2 * (α + β) * n.factorial := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ Cg ^ 2 * (α + β) + D ^ 2 * (α + β) * n.factorial := by
          have : 0 ≤ Cg ^ 2 * (α + β) := by positivity
          linarith

/-! ### The completed Rankin–Selberg function -/

/-- `Λ_g(s) = ∫_𝒟 |g|² E*(s - ½)`. -/
def completedRS (g : UpperHalfPlane → ℂ) (s : ℂ) : ℂ :=
  ∫ z in ModularGroup.fd, ((‖g z‖ ^ 2 : ℝ) : ℂ) * EisAuto.completedEisenstein (s - 1 / 2) z.re z.im

theorem half_lt_im_of_mem_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) : 1 / 2 < z.im :=
  OddCusp.half_lt_im_of_mem_fd hz

/-- **The completed Rankin–Selberg function is holomorphic on `ℂ ∖ {0, ½, 1}`.** -/
theorem differentiableOn_completedRS (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    DifferentiableOn ℂ (completedRS g) ({0, 1 / 2, 1} : Set ℂ)ᶜ := by
  set U : Set ℂ := ({0, 1 / 2, 1} : Set ℂ)ᶜ
  have hU : IsOpen U := (Set.toFinite _).isClosed.isOpen_compl
  have hmemU : ∀ {s : ℂ}, s ∈ U ↔ s ≠ 0 ∧ s ≠ 1 / 2 ∧ s ≠ 1 := fun {s} => by
    simp [U, not_or]
  set F : ℍ → ℂ → ℂ := fun z s => ModularGroup.fd.indicator
    (fun w => ((‖g w‖ ^ 2 : ℝ) : ℂ) * EisAuto.completedEisenstein (s - 1 / 2) w.re w.im) z
  have hfd : MeasurableSet ModularGroup.fd := ModularGroup.isClosed_fd.measurableSet
  have hint : ∀ s, completedRS g s = ∫ z, F z s := fun s => by
    simp only [F]; rw [integral_indicator hfd]; rfl
  have hF : ∀ z, DifferentiableOn ℂ (F z) U := by
    intro z
    by_cases hz : z ∈ ModularGroup.fd
    · simp only [F, indicator_of_mem hz]
      intro s hs
      obtain ⟨h0, h1, h2⟩ := hmemU.1 hs
      have hd := EisAuto.differentiableAt_completed z.re z.im_pos (u := s - 1 / 2)
        (fun h => h2 (by linear_combination h)) (fun h => h1 (by linear_combination h))
        (fun h => h0 (by linear_combination h))
      exact ((differentiableAt_const _).mul (hd.comp s (differentiableAt_id.sub_const _))).differentiableWithinAt
    · simp only [F, indicator_of_notMem hz]
      exact differentiableOn_const _
  have hmeas : ∀ s ∈ U, AEStronglyMeasurable (fun z => F z s) volume := by
    intro s _
    have hc : Continuous fun w : ℍ => ((‖g w‖ ^ 2 : ℝ) : ℂ) *
        EisAuto.completedEisenstein (s - 1 / 2) w.re (max w.im (1 / 2)) :=
      (Complex.continuous_ofReal.comp ((continuous_of_maass hg.2.1).norm.pow 2)).mul
        (continuous_completed_max _)
    refine (hc.aestronglyMeasurable.indicator hfd).congr (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ ModularGroup.fd
    · simp only [F, indicator_of_mem hz, max_eq_left (half_lt_im_of_mem_fd hz).le]
    · simp only [F, indicator_of_notMem hz]
  refine (RHTower.differentiableOn_integral_of_locally_bounded hU hF hmeas fun s₀ hs₀ => ?_).congr
    fun s _ => hint s
  obtain ⟨h0, h1, h2⟩ := hmemU.1 hs₀
  set r := min ‖s₀‖ (min ‖s₀ - 1 / 2‖ ‖s₀ - 1‖) / 2
  have hr : 0 < r := by
    have := norm_pos_iff.2 h0; have := norm_pos_iff.2 (sub_ne_zero.2 h1)
    have := norm_pos_iff.2 (sub_ne_zero.2 h2)
    simp only [r]; positivity
  have hmin : r < ‖s₀‖ ∧ r < ‖s₀ - 1 / 2‖ ∧ r < ‖s₀ - 1‖ := by
    have a1 := norm_pos_iff.2 h0
    have a2 := norm_pos_iff.2 (sub_ne_zero.2 h1)
    have a3 := norm_pos_iff.2 (sub_ne_zero.2 h2)
    have m1 := min_le_left ‖s₀‖ (min ‖s₀ - 1 / 2‖ ‖s₀ - 1‖)
    have m2 := (min_le_right ‖s₀‖ (min ‖s₀ - 1 / 2‖ ‖s₀ - 1‖)).trans (min_le_left _ _)
    have m3 := (min_le_right ‖s₀‖ (min ‖s₀ - 1 / 2‖ ‖s₀ - 1‖)).trans (min_le_right _ _)
    have mpos : 0 < min ‖s₀‖ (min ‖s₀ - 1 / 2‖ ‖s₀ - 1‖) := lt_min a1 (lt_min a2 a3)
    simp only [r]
    exact ⟨by linarith, by linarith, by linarith⟩
  have hball : ∀ s ∈ Metric.closedBall s₀ r, s ≠ 0 ∧ s ≠ 1 / 2 ∧ s ≠ 1 := by
    intro s hs
    rw [Metric.mem_closedBall, dist_eq_norm] at hs
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [h, norm_sub_rev, sub_zero] at hs; linarith [hmin.1]
    · rw [h, norm_sub_rev] at hs; linarith [hmin.2.1]
    · rw [h, norm_sub_rev] at hs; linarith [hmin.2.2]
  refine ⟨r, hr, fun s hs => hmemU.2 (hball s hs), ?_⟩
  set K : Set ℂ := (fun s => s - 1 / 2) '' Metric.closedBall s₀ r
  have hK : IsCompact K := (isCompact_closedBall s₀ r).image (by fun_prop)
  have hKU : ∀ u ∈ K, u ≠ 1 / 2 ∧ u ≠ 0 ∧ u ≠ -(1 / 2) := by
    rintro u ⟨s, hs, rfl⟩
    obtain ⟨h0', h1', h2'⟩ := hball s hs
    exact ⟨fun h => h2' (by linear_combination h), fun h => h1' (by linear_combination h),
      fun h => h0' (by linear_combination h)⟩
  obtain ⟨α, β, a, hα, hβ, ha, hb⟩ := exists_completed_bound hK hKU
  obtain ⟨B, hB⟩ := exists_bound_on_fd hg hρ0 hρ hα hβ ha
  refine ⟨ModularGroup.fd.indicator (fun z => ‖g z‖ ^ 2 * (α * z.im ^ a + β)), ?_, fun z s hs => ?_⟩
  · have hvol : volume ModularGroup.fd ≠ ⊤ := by rw [volume_fd_eq]; exact ENNReal.ofReal_ne_top
    refine (integrable_indicator_iff hfd).2 (Measure.integrableOn_of_bounded (M := B) hvol ?_ ?_)
    · exact ((((continuous_of_maass hg.2.1).norm.pow 2).mul
        ((continuous_const.mul (UpperHalfPlane.continuous_im.rpow_const fun z =>
          Or.inl (ne_of_gt z.im_pos))).add continuous_const))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hfd] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := z.im_pos; positivity)]
      exact hB z hz
  · by_cases hz : z ∈ ModularGroup.fd
    · simp only [F, indicator_of_mem hz]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hb _ ⟨s, hs, rfl⟩ z.re z.im (half_lt_im_of_mem_fd hz).le)
        (sq_nonneg _)
    · simp only [F, indicator_of_notMem hz, norm_zero, le_refl]

/-- **The functional equation** `Λ_g(1 - s) = Λ_g(s)`. -/
theorem completedRS_one_sub {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) (h2 : s ≠ 1) :
    completedRS g (1 - s) = completedRS g s := by
  unfold completedRS
  refine setIntegral_congr_fun ModularGroup.isClosed_fd.measurableSet fun z _ => ?_
  rw [show 1 - s - 1 / 2 = -(s - 1 / 2) by ring,
    EisAuto.completedEisenstein_neg z.re z.im_pos (fun h => h2 (by linear_combination h))
      (fun h => h1 (by linear_combination h)) (fun h => h0 (by linear_combination h))]

/-- **On `Re s > 1` the completed function is the Rankin–Selberg series**:
`Λ_g(s) = ξ(2s)/(2s(2s-1)) · (2π)^{-s} G(s) Σ_{n≠0} |ρ(n)|² |n|^{-s}`. -/
theorem completedRS_eq (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 1 < s.re)
    (him : s.im ≠ 0) :
    completedRS g s = xi (2 * s) / (2 * s * (2 * s - 1)) * ((2 * Real.pi : ℂ) ^ (-s) *
      CuspRSI.gammaFactor (nu lamE) s * ∑' n : ℤ, ((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)) := by
  have hxi : xi (1 + 2 * (s - 1 / 2)) ≠ 0 := xi_ne_zero_of_one_le_re (by simp; linarith)
  have hpt : ∀ z : ℍ, EisAuto.completedEisenstein (s - 1 / 2) z.re z.im =
      normalizedEisenstein (s - 1 / 2) z.re z.im * (xi (2 * s) / (2 * s * (2 * s - 1))) := by
    intro z
    rw [normalizedEisenstein_eq_numerator_div hxi, EisAuto.completedEisenstein,
      show 1 + 2 * (s - 1 / 2) = 2 * s by ring, show 2 * (s - 1 / 2) = 2 * s - 1 by ring]
    have hx2 : xi (2 * s) ≠ 0 := by rwa [show 1 + 2 * (s - 1 / 2) = 2 * s by ring] at hxi
    rw [div_mul_div_comm, mul_comm (xi (2 * s)) (2 * s * (2 * s - 1)), mul_div_mul_right _ _ hx2]
  unfold completedRS
  simp_rw [hpt]
  have h := (CuspRSI.rankinSelberg_eisenstein hg hρ0 hρ hs him).tsum_eq
  rw [tsum_mul_left] at h
  have e : ∫ z in ModularGroup.fd, ((‖g z‖ ^ 2 : ℝ) : ℂ) *
      (normalizedEisenstein (s - 1 / 2) z.re z.im * (xi (2 * s) / (2 * s * (2 * s - 1)))) =
      (∫ z in ModularGroup.fd, ((‖g z‖ ^ 2 : ℝ) : ℂ) * normalizedEisenstein (s - 1 / 2) z.re z.im) *
        (xi (2 * s) / (2 * s * (2 * s - 1))) := by
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    ring
  rw [e, ← h]
  ring


/-- The factor `c(s) = ξ(2s)/(2s(2s-1)) (2π)^{-s} G(s)` relating `Λ_g` to the Rankin–Selberg series. -/
def rsFactor (lamE : ℝ) (s : ℂ) : ℂ :=
  xi (2 * s) / (2 * s * (2 * s - 1)) * ((2 * Real.pi : ℂ) ^ (-s) * CuspRSI.gammaFactor (nu lamE) s)

theorem gamma_args_re (lamE : ℝ) (s : ℂ) :
    ((s + nu lamE + nu lamE) / 2).re = s.re / 2 ∧ ((s + nu lamE - nu lamE) / 2).re = s.re / 2 ∧
      ((s - nu lamE + nu lamE) / 2).re = s.re / 2 ∧ ((s - nu lamE - nu lamE) / 2).re = s.re / 2 := by
  simp [nu_re]

theorem differentiableAt_Gamma_of_re_pos {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ Gamma w :=
  differentiableAt_Gamma w fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]

theorem differentiableAt_rsFactor {s : ℂ} (hs : 1 / 2 < s.re) : DifferentiableAt ℂ (rsFactor lamE) s := by
  have hs0 : 0 < s.re := by linarith
  have hden : 2 * s * (2 * s - 1) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero fun h => ?_) fun h => ?_
    · rw [h] at hs; simp at hs; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact ofReal_ne_zero.2 (by positivity)
  obtain ⟨g1, g2, g3, g4⟩ := gamma_args_re lamE s
  have hG : ∀ w : ℂ, w.re = s.re / 2 → ∀ f : ℂ → ℂ, DifferentiableAt ℂ f s → f s = w →
      DifferentiableAt ℂ (fun v => Gamma (f v)) s := fun w hw f hf hfw =>
    (differentiableAt_Gamma_of_re_pos (by rw [hfw, hw]; linarith)).comp s hf
  unfold rsFactor CuspRSI.gammaFactor
  have h1 : DifferentiableAt ℂ (fun v : ℂ => xi (2 * v) / (2 * v * (2 * v - 1))) s :=
    ((xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) s).div (by fun_prop) hden
  have h2 : DifferentiableAt ℂ (fun v : ℂ => (2 * Real.pi : ℂ) ^ (-v)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl hpi)
  have h3 : DifferentiableAt ℂ (fun v : ℂ => (2 : ℂ) ^ (v - 3) / Gamma v) s :=
    ((differentiableAt_id.sub_const 3).const_cpow (Or.inl two_ne_zero)).div
      (differentiableAt_Gamma_of_re_pos hs0) (Gamma_ne_zero_of_re_pos hs0)
  have h4 := hG _ g1 (fun v => (v + nu lamE + nu lamE) / 2) (by fun_prop) rfl
  have h5 := hG _ g2 (fun v => (v + nu lamE - nu lamE) / 2) (by fun_prop) rfl
  have h6 := hG _ g3 (fun v => (v - nu lamE + nu lamE) / 2) (by fun_prop) rfl
  have h7 := hG _ g4 (fun v => (v - nu lamE - nu lamE) / 2) (by fun_prop) rfl
  exact h1.mul (h2.mul (h3.mul (((h4.mul h5).mul h6).mul h7)))

theorem rsFactor_ne_zero {s : ℂ} (hs : 1 / 2 < s.re) : rsFactor lamE s ≠ 0 := by
  have hs0 : 0 < s.re := by linarith
  have hden : 2 * s * (2 * s - 1) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero fun h => ?_) fun h => ?_
    · rw [h] at hs; simp at hs; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  have hxi : xi (2 * s) ≠ 0 := xi_ne_zero_of_one_le_re (by simp; linarith)
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact ofReal_ne_zero.2 (by positivity)
  have hcp : ∀ (b w : ℂ), b ≠ 0 → b ^ w ≠ 0 := fun b w hb => by
    rw [cpow_def_of_ne_zero hb]; exact exp_ne_zero _
  obtain ⟨g1, g2, g3, g4⟩ := gamma_args_re lamE s
  unfold rsFactor CuspRSI.gammaFactor
  refine mul_ne_zero (div_ne_zero hxi hden) (mul_ne_zero (hcp _ _ hpi) (mul_ne_zero
    (div_ne_zero (hcp _ _ two_ne_zero) (Gamma_ne_zero_of_re_pos hs0)) ?_))
  have hp : 0 < s.re / 2 := by linarith
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Gamma_ne_zero_of_re_pos (g1 ▸ hp))
    (Gamma_ne_zero_of_re_pos (g2 ▸ hp))) (Gamma_ne_zero_of_re_pos (g3 ▸ hp)))
    (Gamma_ne_zero_of_re_pos (g4 ▸ hp))

/-- **The Rankin–Selberg series of a cusp mode continues holomorphically to `Re s > ½`, `s ≠ 1`.**
On `Re s > 1`, `Im s ≠ 0`, the continuation `Λ_g/c` equals `Σ_{n≠0} |ρ(n)|² |n|^{-s}`. -/
theorem rankinSelberg_continuation (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    DifferentiableOn ℂ (fun s => completedRS g s / rsFactor lamE s) {s | 1 / 2 < s.re ∧ s ≠ 1} ∧
      ∀ s : ℂ, 1 < s.re → s.im ≠ 0 →
        completedRS g s / rsFactor lamE s = ∑' n : ℤ, ((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s) := by
  refine ⟨fun s hs => ?_, fun s hs him => ?_⟩
  · obtain ⟨hs1, hs2⟩ := hs
    have hmem : s ∈ ({0, 1 / 2, 1} : Set ℂ)ᶜ := by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      refine ⟨fun h => ?_, fun h => ?_, hs2⟩
      · rw [h] at hs1; simp at hs1; linarith
      · rw [h] at hs1; norm_num at hs1
    have hopen : IsOpen ({0, 1 / 2, 1} : Set ℂ)ᶜ := (Set.toFinite _).isClosed.isOpen_compl
    have hd := (differentiableOn_completedRS hg hρ0 hρ).differentiableAt (hopen.mem_nhds hmem)
    exact (hd.div (differentiableAt_rsFactor hs1) (rsFactor_ne_zero hs1)).differentiableWithinAt
  · rw [completedRS_eq hg hρ0 hρ hs him, div_eq_iff (rsFactor_ne_zero (by linarith))]
    unfold rsFactor
    ring

end CuspRSC

end GaloisForLFunctions.BlackHoleRingdown
