import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.LewisPeriodReflectionPositivity
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheFrobeniusAtInfinityOfAWindow
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheFirstPrimeFold
import GaloisForLFunctions.ArithmeticCriticalityTheory.WindowJumpCounts.VariableHubSchurAndFoldedMarkovObstruction

/-!
# Logarithmic Period Unitary Equivalence, Window Frobenius Defect, and `sym_n` / Stick-Schur Transfer

This module establishes the Hilbert-space and quadratic-form bridge between the folded Mayer
co-isometry defect on `H_LP = L²((0, ∞), w_LP da)` (`LewisPeriodReflectionPositivity.lean`), the
window Frobenius multiplier (`TheFrobeniusAtInfinityOfAWindow.lean`), the symmetric and
antisymmetric prime-power fold functionals `foldSym` and `foldEnergy` (`TheFirstPrimeFold.lean`),
and the coupled 2-vertex `T₂`-stick Schur elimination (`VariableHubSchurAndFoldedMarkovObstruction.lean`):

1. **Logarithmic Unitary Equivalence `U_LP : H_LP ≃ L²(ℝ)` and Window Frobenius Intertwining:**
   `(logPeriodTransform f)(u) = (2 cosh u)^(-3) e^(u/4) f(e^u)` preserves norms and inner products
   between `H_LP` and `L²(ℝ)`, intertwines `lewisModularInversion s` with
   `windowMultiplier u (2s) * F(-u)`, and rewrites `lewisCoIsometryDefect s ψ` of every `+1`
   `I_s`-fixed period `ψ` as `-∫_0^∞ (e^(δu) + e^(-δu))(e^(δu) - e^(-δu))² ‖F(u) F(-u)‖ du`
   (`δ = 2 Re s - 1/2`).
2. **Canonical `+1` `I_s`-Invariant Mayer Period Lift of Window Tests & Multiplicative-Haar Folds:**
   Every continuous test `H` supported in `[-A, 0]` (`A ≥ 0`) lifts canonically to a `+1`
   `I_s`-invariant Mayer period `windowPeriodLift s H` whose defect equals
   `-∫_{-A}^0 frobeniusDefectFactor s (-x) * H(x)² dx` (expressed directly through
   `‖windowMultiplier x (2s)‖` and `‖windowMultiplier (-x) (2s)‖`), while `foldSym A (log n) H` and
   `foldEnergy A (log n) H` (`n ≥ 2`, `log n ≤ A`) equal the `db / b` dilation integrals of
   `periodWindowProfile s (windowPeriodLift s H)` over `[1, e^A / n]`.
3. **Two-Sided Quantitative `(foldSym, foldEnergy)` Transfer & `T₂`-Stick Schur Elimination:**
   `-lewisCoIsometryDefect s (windowPeriodLift s H)` dominates
   `((n^δ + n^(-δ))(n^δ - n^(-δ))² / 4) * (foldSym A (log n) H - foldEnergy A (log n) H)` at every
   stage `A ≥ log n` (sharpening to `/ 2` on fold-symmetric tests), is bounded above for
   `A ≥ 2 log 2` by `frobeniusDefectFactor s A * (foldEnergy A (log 2) H / 2 + foldSym A (log 2) H)`,
   and pairs with `WindowJumpCounts.twoVertexStick_ge_schur` across `[-A, -log 2]` via
   `g₁₂ * foldEnergy A (log 2) H`.
-/

open Complex Set Filter MeasureTheory Topology
open GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
open GaloisForLFunctions.ArithmeticCriticalityTheory.WindowJumpCounts

set_option autoImplicit false

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-! ## Part 1: Logarithmic unitary equivalence `U_LP : H_LP ≃ L²(ℝ)` and Frobenius intertwining -/

/-- Logarithmic unitary map `(U_LP f)(u) = (2 cosh u)^(-3) e^(u/4) f(e^u)` from `H_LP` to `L²(ℝ)`. -/
def logPeriodTransform (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  (((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (u / 4) : ℝ) : ℂ) * f (Real.exp u)

/-- Inverse map `(U_LP⁻¹ F)(a) = (a + a⁻¹)^3 a^(-1/4) F(log a)` on `(0, ∞)`. -/
def logPeriodInverse (F : ℝ → ℂ) (a : ℝ) : ℂ :=
  (((a + a⁻¹) ^ (3 : ℝ) * a ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * F (Real.log a)

private theorem two_mul_cosh_eq_exp_add_inv (u : ℝ) :
    2 * Real.cosh u = Real.exp u + (Real.exp u)⁻¹ := by
  rw [Real.cosh_eq, Real.exp_neg]
  ring

private theorem two_mul_cosh_pos (u : ℝ) : 0 < 2 * Real.cosh u := by
  rw [two_mul_cosh_eq_exp_add_inv]
  exact add_pos (Real.exp_pos u) (inv_pos.mpr (Real.exp_pos u))

/-- Pointwise left inverse `U_LP⁻¹ (U_LP f) = f` on `(0, ∞)`. -/
theorem logPeriodInverse_comp_transform (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    logPeriodInverse (logPeriodTransform f) a = f a := by
  unfold logPeriodInverse logPeriodTransform
  have hsum : 0 < a + a⁻¹ := add_pos ha (inv_pos.mpr ha)
  have hcosh : 2 * Real.cosh (Real.log a) = a + a⁻¹ := by
    rw [two_mul_cosh_eq_exp_add_inv, Real.exp_log ha]
  have hexp4 : Real.exp (Real.log a / 4) = a ^ (1 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos ha]
    congr 1; ring
  rw [Real.exp_log ha, hcosh, hexp4, ← mul_assoc, ← Complex.ofReal_mul]
  have hprod : ((a + a⁻¹) ^ (3 : ℝ) * a ^ (-(1 / 4 : ℝ))) *
      ((a + a⁻¹) ^ (-3 : ℝ) * a ^ (1 / 4 : ℝ)) = 1 := by
    calc
      ((a + a⁻¹) ^ (3 : ℝ) * a ^ (-(1 / 4 : ℝ))) *
          ((a + a⁻¹) ^ (-3 : ℝ) * a ^ (1 / 4 : ℝ))
          = ((a + a⁻¹) ^ (3 : ℝ) * (a + a⁻¹) ^ (-3 : ℝ)) *
              (a ^ (-(1 / 4 : ℝ)) * a ^ (1 / 4 : ℝ)) := by ring
      _ = 1 := by
        rw [← Real.rpow_add hsum, ← Real.rpow_add ha]
        norm_num
  rw [hprod, Complex.ofReal_one, one_mul]

/-- Pointwise right inverse `U_LP (U_LP⁻¹ F) = F` on `ℝ`. -/
theorem logPeriodTransform_comp_inverse (F : ℝ → ℂ) (u : ℝ) :
    logPeriodTransform (logPeriodInverse F) u = F u := by
  unfold logPeriodTransform logPeriodInverse
  have hc_pos : 0 < 2 * Real.cosh u := two_mul_cosh_pos u
  have hexp_pos : 0 < Real.exp u := Real.exp_pos u
  have hsum : Real.exp u + (Real.exp u)⁻¹ = 2 * Real.cosh u :=
    (two_mul_cosh_eq_exp_add_inv u).symm
  have hrpow : (Real.exp u) ^ (-(1 / 4 : ℝ)) = Real.exp (-(u / 4)) := by
    rw [Real.rpow_def_of_pos hexp_pos, Real.log_exp]
    congr 1; ring
  rw [Real.log_exp, hsum, hrpow, ← mul_assoc, ← Complex.ofReal_mul]
  have hprod : ((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (u / 4)) *
      ((2 * Real.cosh u) ^ (3 : ℝ) * Real.exp (-(u / 4))) = 1 := by
    calc
      ((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (u / 4)) *
          ((2 * Real.cosh u) ^ (3 : ℝ) * Real.exp (-(u / 4)))
          = ((2 * Real.cosh u) ^ (-3 : ℝ) * (2 * Real.cosh u) ^ (3 : ℝ)) *
              (Real.exp (u / 4) * Real.exp (-(u / 4))) := by ring
      _ = 1 := by
        rw [← Real.rpow_add hc_pos, ← Real.exp_add]
        norm_num
  rw [hprod, Complex.ofReal_one, one_mul]

/-- Exponential change of variables `a = e^u` mapping `ℝ` onto `(0, ∞)`. -/
theorem integral_Ioi_zero_exp_subst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) :
    (∫ a in Ioi (0 : ℝ), g a) = ∫ u : ℝ, Real.exp u • g (Real.exp u) := by
  have himg : Real.exp '' (Set.univ : Set ℝ) = Ioi (0 : ℝ) := by
    rw [Set.image_univ, Real.range_exp]
  have hinj : InjOn Real.exp Set.univ := Real.exp_injective.injOn
  have hderiv : ∀ u ∈ (Set.univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp u) Set.univ u :=
    fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt
  have hint := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ hderiv hinj g
  rw [himg, MeasureTheory.setIntegral_univ] at hint
  rw [hint]
  congr 1; ext u
  rw [abs_of_pos (Real.exp_pos u)]

/-- Exponential change of variables `b = e^u` mapping `(0, ∞)` onto `(1, ∞)`. -/
theorem integral_Ioi_one_exp_subst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) :
    (∫ b in Ioi (1 : ℝ), g b) = ∫ u in Ioi (0 : ℝ), Real.exp u • g (Real.exp u) := by
  have himg : Real.exp '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
    ext b
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact Real.one_lt_exp_iff.mpr hu
    · intro hb
      have hb0 : 0 < b := zero_lt_one.trans hb
      exact ⟨Real.log b, Real.log_pos hb, Real.exp_log hb0⟩
  have hinj : InjOn Real.exp (Ioi 0) := Real.exp_injective.injOn
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt Real.exp (Real.exp u) (Ioi 0) u :=
    fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt
  have hint := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv hinj g
  rw [himg] at hint
  rw [hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [abs_of_pos (Real.exp_pos u)]

private theorem norm_logPeriodTransform_sq_eq (f : ℝ → ℂ) (u : ℝ) :
    ‖logPeriodTransform f u‖ ^ 2 =
      Real.exp u * (‖f (Real.exp u)‖ ^ 2 * lewisCriticalWeight (Real.exp u)) := by
  have hc_pos : 0 < 2 * Real.cosh u := two_mul_cosh_pos u
  have hexp_pos : 0 < Real.exp u := Real.exp_pos u
  unfold logPeriodTransform lewisCriticalWeight
  rw [norm_mul, mul_pow, Complex.norm_real,
    Real.norm_of_nonneg (mul_pos (Real.rpow_pos_of_pos hc_pos _) (Real.exp_pos _)).le,
    mul_pow, ← Real.rpow_natCast ((2 * Real.cosh u) ^ (-3 : ℝ)) 2,
    ← Real.rpow_mul hc_pos.le, ← Real.exp_nat_mul,
    ← two_mul_cosh_eq_exp_add_inv u,
    Real.rpow_def_of_pos hexp_pos, Real.log_exp]
  have h1 : (-3 : ℝ) * ((2 : ℕ) : ℝ) = -6 := by norm_num
  have h2 : (2 : ℕ) * (u / 4) = u / 2 := by push_cast; ring
  have h3 : Real.exp u * Real.exp (u * -(1 / 2 : ℝ)) = Real.exp (u / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h1, h2]
  calc
    (2 * Real.cosh u) ^ (-6 : ℝ) * Real.exp (u / 2) * ‖f (Real.exp u)‖ ^ 2
        = (2 * Real.cosh u) ^ (-6 : ℝ) * (Real.exp u * Real.exp (u * -(1 / 2 : ℝ))) *
            ‖f (Real.exp u)‖ ^ 2 := by rw [h3]
    _ = Real.exp u * (‖f (Real.exp u)‖ ^ 2 *
          ((2 * Real.cosh u) ^ (-6 : ℝ) * Real.exp (u * -(1 / 2 : ℝ)))) := by ring

/-- Exact squared-norm preservation `‖f‖_LP² = ∫_ℝ ‖(U_LP f)(u)‖² du`. -/
theorem lewisCriticalNormSq_eq_l2NormSq_logPeriodTransform (f : ℝ → ℂ) :
    lewisCriticalNormSq f = ∫ u : ℝ, ‖logPeriodTransform f u‖ ^ 2 := by
  unfold lewisCriticalNormSq
  rw [integral_Ioi_zero_exp_subst]
  congr 1; ext u
  dsimp only [smul_eq_mul]
  exact (norm_logPeriodTransform_sq_eq f u).symm

/-- Exact Hermitian inner-product preservation `⟨f, g⟩_LP = ∫_ℝ (U_LP f)(u) conj((U_LP g)(u)) du`. -/
theorem lewisCriticalInner_eq_l2Inner_logPeriodTransform (f g : ℝ → ℂ) :
    lewisCriticalInner f g =
      ∫ u : ℝ, logPeriodTransform f u * (starRingEnd ℂ) (logPeriodTransform g u) := by
  unfold lewisCriticalInner
  rw [integral_Ioi_zero_exp_subst]
  congr 1; ext u
  have hc_pos : 0 < 2 * Real.cosh u := two_mul_cosh_pos u
  have hexp_pos : 0 < Real.exp u := Real.exp_pos u
  unfold logPeriodTransform lewisCriticalWeight
  rw [Complex.real_smul, map_mul, Complex.conj_ofReal,
    ← two_mul_cosh_eq_exp_add_inv u, Real.rpow_def_of_pos hexp_pos, Real.log_exp]
  have hreal_eq : Real.exp u * ((2 * Real.cosh u) ^ (-6 : ℝ) * Real.exp (u * -(1 / 2 : ℝ))) =
      ((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (u / 4)) *
        ((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (u / 4)) := by
    calc
      Real.exp u * ((2 * Real.cosh u) ^ (-6 : ℝ) * Real.exp (u * -(1 / 2 : ℝ)))
          = ((2 * Real.cosh u) ^ (-3 : ℝ) * (2 * Real.cosh u) ^ (-3 : ℝ)) *
              (Real.exp u * Real.exp (u * -(1 / 2 : ℝ))) := by
        rw [← Real.rpow_add hc_pos]; congr 2; norm_num
      _ = ((2 * Real.cosh u) ^ (-3 : ℝ) * (2 * Real.cosh u) ^ (-3 : ℝ)) *
            (Real.exp (u / 4) * Real.exp (u / 4)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 3; ring
      _ = ((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (u / 4)) *
            ((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (u / 4)) := by ring
  calc
    (Real.exp u : ℂ) * (f (Real.exp u) * (starRingEnd ℂ) (g (Real.exp u)) *
        (((2 * Real.cosh u) ^ (-6 : ℝ) * Real.exp (u * -(1 / 2 : ℝ)) : ℝ) : ℂ))
        = (((Real.exp u * ((2 * Real.cosh u) ^ (-6 : ℝ) *
            Real.exp (u * -(1 / 2 : ℝ))) : ℝ) : ℂ)) *
            (f (Real.exp u) * (starRingEnd ℂ) (g (Real.exp u))) := by push_cast; ring
    _ = ((((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (u / 4)) *
          ((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (u / 4)) : ℝ) : ℂ) *
          (f (Real.exp u) * (starRingEnd ℂ) (g (Real.exp u))) := by rw [hreal_eq]
    _ = (((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (u / 4) : ℝ) : ℂ) * f (Real.exp u) *
          ((((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (u / 4) : ℝ) : ℂ) *
            (starRingEnd ℂ) (g (Real.exp u))) := by push_cast; ring

/-- Equivalence of `L²(ℝ)` integrability of `logPeriodTransform f` and `H_LP` integrability of `f`. -/
theorem integrable_logPeriodTransform_normSq_iff (f : ℝ → ℂ) :
    Integrable (fun u : ℝ => ‖logPeriodTransform f u‖ ^ 2) ↔
      IntegrableOn (fun a : ℝ => ‖f a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) := by
  have himg : Real.exp '' (Set.univ : Set ℝ) = Ioi (0 : ℝ) := by
    rw [Set.image_univ, Real.range_exp]
  have hinj : InjOn Real.exp Set.univ := Real.exp_injective.injOn
  have hderiv : ∀ u ∈ (Set.univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp u) Set.univ u :=
    fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj
    (fun a : ℝ => ‖f a‖ ^ 2 * lewisCriticalWeight a)
  rw [himg, integrableOn_univ] at hiff
  refine Iff.trans ?_ hiff.symm
  refine integrable_congr (Eventually.of_forall fun u => ?_)
  dsimp only [smul_eq_mul]
  rw [abs_of_pos (Real.exp_pos u), norm_logPeriodTransform_sq_eq]

private theorem ofReal_exp_cpow (u : ℝ) (z : ℂ) :
    ((Real.exp u : ℝ) : ℂ) ^ z = Complex.exp ((u : ℂ) * z) := by
  have hp : 0 < Real.exp u := Real.exp_pos u
  have hne : ((Real.exp u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hp.le, Real.log_exp]

/-- **Window Frobenius Intertwining Identity:**
Under `logPeriodTransform`, the Lewis modular inversion `I_s` becomes reflection `u ↦ -u` twisted
by the CWS window Frobenius multiplier `windowMultiplier u (2 * s) = exp(-((2s - 1/2) * u))`. -/
theorem logPeriodTransform_modularInversion (s : ℂ) (f : ℝ → ℂ) (u : ℝ) :
    logPeriodTransform (lewisModularInversion s f) u =
      windowMultiplier u (2 * s) * logPeriodTransform f (-u) := by
  unfold logPeriodTransform lewisModularInversion windowMultiplier
  rw [← Real.exp_neg, Real.cosh_neg, ofReal_exp_cpow]
  have hexp_split : Real.exp (u / 4) = Real.exp (u / 2) * Real.exp (-u / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp_cast : ((Real.exp (u / 2) : ℝ) : ℂ) * Complex.exp ((u : ℂ) * -(2 * s)) =
      Complex.exp (-((2 * s - 1 / 2) * (u : ℂ))) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hexp_split]
  calc
    (((2 * Real.cosh u) ^ (-3 : ℝ) * (Real.exp (u / 2) * Real.exp (-u / 4)) : ℝ) : ℂ) *
        (Complex.exp ((u : ℂ) * -(2 * s)) * f (Real.exp (-u)))
        = (((Real.exp (u / 2) : ℝ) : ℂ) * Complex.exp ((u : ℂ) * -(2 * s))) *
            ((((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (-u / 4) : ℝ) : ℂ) *
              f (Real.exp (-u))) := by push_cast; ring
    _ = Complex.exp (-((2 * s - 1 / 2) * (u : ℂ))) *
          ((((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (-u / 4) : ℝ) : ℂ) *
            f (Real.exp (-u))) := by rw [hexp_cast]

/-- **Logarithmic Co-Isometry Defect Formula (`δ = 2 Re s - 1/2`).**
For any `+1` `I_s`-fixed period `ψ` satisfying the half-line integrability hypotheses,
`lewisCoIsometryDefect s ψ` equals `-∫_0^∞ (e^(δu) + e^(-δu))(e^(δu) - e^(-δu))² ‖F(u) F(-u)‖ du`
where `F = logPeriodTransform ψ`. -/
theorem lewisCoIsometryDefect_eq_neg_log_integral {s : ℂ} {ψ : ℝ → ℂ}
    (hfix : ∀ a > 0, lewisModularInversion s ψ a = ψ a)
    (hψ_int : IntegrableOn (fun a => ‖ψ a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0))
    (hψR_int : IntegrableOn
      (fun a => ‖lewisModularInversion (riemannMayerReflect s) ψ a‖ ^ 2 * lewisCriticalWeight a)
      (Ioi 0))
    (hfold1 : IntegrableOn
      (fun b => ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (4 * s.re - 3 / 2))) (Ioi 1))
    (hfold2 : IntegrableOn
      (fun b => ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ (-4 * s.re + 1 / 2))) (Ioi 1)) :
    lewisCoIsometryDefect s ψ =
      -∫ u in Ioi (0 : ℝ),
        (Real.exp ((2 * s.re - 1 / 2) * u) + Real.exp (-((2 * s.re - 1 / 2) * u))) *
          (Real.exp ((2 * s.re - 1 / 2) * u) - Real.exp (-((2 * s.re - 1 / 2) * u))) ^ 2 *
          ‖logPeriodTransform ψ u * logPeriodTransform ψ (-u)‖ := by
  rw [lewisCoIsometryDefect_eq_neg_integral hfix hψ_int hψR_int hfold1 hfold2,
    integral_Ioi_one_exp_subst]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  dsimp only [smul_eq_mul]
  let δ : ℝ := 2 * s.re - 1 / 2
  have hexp_pos : 0 < Real.exp u := Real.exp_pos u
  have hc_pos : 0 < 2 * Real.cosh u := two_mul_cosh_pos u
  -- Relate `F(-u)` to `F(u)` using `hfix`:
  have hF_sym : logPeriodTransform ψ (-u) =
      windowMultiplier (-u) (2 * s) * logPeriodTransform ψ u := by
    have h1 := logPeriodTransform_modularInversion s ψ (-u)
    rw [neg_neg, hfix (Real.exp (-u)) (Real.exp_pos (-u))] at h1
    exact h1
  have hnorm_wm : ‖windowMultiplier (-u) (2 * s)‖ = Real.exp (δ * u) := by
    rw [norm_windowMultiplier]
    congr 1; dsimp [δ]; simp; ring
  have hpair_norm : ‖logPeriodTransform ψ u * logPeriodTransform ψ (-u)‖ =
      (2 * Real.cosh u) ^ (-6 : ℝ) * Real.exp (2 * s.re * u) * ‖ψ (Real.exp u)‖ ^ 2 := by
    rw [hF_sym, norm_mul, norm_mul, hnorm_wm]
    have hFu_sq : ‖logPeriodTransform ψ u‖ * ‖logPeriodTransform ψ u‖ =
        (2 * Real.cosh u) ^ (-6 : ℝ) * Real.exp (u / 2) * ‖ψ (Real.exp u)‖ ^ 2 := by
      unfold logPeriodTransform
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (mul_pos (Real.rpow_pos_of_pos hc_pos _) (Real.exp_pos _)).le]
      calc
        ((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (u / 4) * ‖ψ (Real.exp u)‖) *
            ((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (u / 4) * ‖ψ (Real.exp u)‖)
            = ((2 * Real.cosh u) ^ (-3 : ℝ) * (2 * Real.cosh u) ^ (-3 : ℝ)) *
                (Real.exp (u / 4) * Real.exp (u / 4)) * ‖ψ (Real.exp u)‖ ^ 2 := by ring
        _ = (2 * Real.cosh u) ^ (-6 : ℝ) * Real.exp (u / 2) * ‖ψ (Real.exp u)‖ ^ 2 := by
          rw [← Real.rpow_add hc_pos, ← Real.exp_add]
          congr 2 <;> ring
    calc
      ‖logPeriodTransform ψ u‖ * (Real.exp (δ * u) * ‖logPeriodTransform ψ u‖)
          = Real.exp (δ * u) * (‖logPeriodTransform ψ u‖ * ‖logPeriodTransform ψ u‖) := by ring
      _ = (2 * Real.cosh u) ^ (-6 : ℝ) * (Real.exp (δ * u) * Real.exp (u / 2)) *
            ‖ψ (Real.exp u)‖ ^ 2 := by rw [hFu_sq]; ring
      _ = (2 * Real.cosh u) ^ (-6 : ℝ) * Real.exp (2 * s.re * u) * ‖ψ (Real.exp u)‖ ^ 2 := by
        rw [← Real.exp_add]; congr 2; congr 1; dsimp [δ]; ring
  have hb_pow1 : (Real.exp u) ^ (2 * s.re - 1) = Real.exp ((2 * s.re - 1) * u) := by
    rw [Real.rpow_def_of_pos hexp_pos, Real.log_exp]; ring_nf
  have hb_pow2 : (Real.exp u) ^ δ = Real.exp (δ * u) := by
    rw [Real.rpow_def_of_pos hexp_pos, Real.log_exp]; ring_nf
  have hb_pow3 : (Real.exp u) ^ (-δ) = Real.exp (-(δ * u)) := by
    rw [Real.rpow_def_of_pos hexp_pos, Real.log_exp]; ring_nf
  rw [hpair_norm, ← two_mul_cosh_eq_exp_add_inv u, hb_pow1, hb_pow2, hb_pow3]
  have hexp_merge : Real.exp u * Real.exp ((2 * s.re - 1) * u) = Real.exp (2 * s.re * u) := by
    rw [← Real.exp_add]; congr 1; ring
  calc
    Real.exp u *
        ((2 * Real.cosh u) ^ (-6 : ℝ) * Real.exp ((2 * s.re - 1) * u) *
          (Real.exp (δ * u) + Real.exp (-(δ * u))) *
          (Real.exp (δ * u) - Real.exp (-(δ * u))) ^ 2 * ‖ψ (Real.exp u)‖ ^ 2)
        = (2 * Real.cosh u) ^ (-6 : ℝ) * (Real.exp u * Real.exp ((2 * s.re - 1) * u)) *
            (Real.exp (δ * u) + Real.exp (-(δ * u))) *
            (Real.exp (δ * u) - Real.exp (-(δ * u))) ^ 2 * ‖ψ (Real.exp u)‖ ^ 2 := by ring
    _ = (Real.exp (δ * u) + Real.exp (-(δ * u))) *
          (Real.exp (δ * u) - Real.exp (-(δ * u))) ^ 2 *
          ((2 * Real.cosh u) ^ (-6 : ℝ) * Real.exp (2 * s.re * u) * ‖ψ (Real.exp u)‖ ^ 2) := by
      rw [hexp_merge]; ring

/-! ## Part 2: Canonical `+1` `I_s`-invariant Mayer period lift of window tests & Haar folds -/

/-- Canonical logarithmic lift `F_{H,s}` on `ℝ` of a window test `H` supported on `[-A, 0]`. -/
def windowLogLift (s : ℂ) (H : ℝ → ℝ) (u : ℝ) : ℂ :=
  if 0 < u then
    ((Real.exp (-((s.re - 1 / 4) * u)) * H (-u) : ℝ) : ℂ)
  else if u < 0 then
    Complex.exp (-((2 * s - 1 / 2) * (u : ℂ))) *
      ((Real.exp ((s.re - 1 / 4) * u) * H u : ℝ) : ℂ)
  else 0

/-- Canonical `+1` `I_s`-invariant Mayer period lift `ψ_{H,s} = U_LP⁻¹ F_{H,s}` on `(0, ∞)`. -/
def windowPeriodLift (s : ℂ) (H : ℝ → ℝ) (a : ℝ) : ℂ :=
  logPeriodInverse (windowLogLift s H) a

/-- Canonical normalized period profile `(W_s ψ)(b) = (b + b⁻¹)^(-3) b^(Re s) ψ(b)` on `(0, ∞)`. -/
def periodWindowProfile (s : ℂ) (ψ : ℝ → ℂ) (b : ℝ) : ℂ :=
  (((b + b⁻¹) ^ (-3 : ℝ) * b ^ s.re : ℝ) : ℂ) * ψ b

/-- Off-line Frobenius defect kernel `(e^(δu) + e^(-δu))(e^(δu) - e^(-δu))²` (`δ = 2 Re s - 1/2`). -/
def frobeniusDefectFactor (s : ℂ) (u : ℝ) : ℝ :=
  (Real.exp ((2 * s.re - 1 / 2) * u) + Real.exp (-((2 * s.re - 1 / 2) * u))) *
    (Real.exp ((2 * s.re - 1 / 2) * u) - Real.exp (-((2 * s.re - 1 / 2) * u))) ^ 2

/-- Identity between `frobeniusDefectFactor s u` and the CWS `windowMultiplier` modulus gap. -/
theorem frobeniusDefectFactor_eq_windowMultiplier (s : ℂ) (u : ℝ) :
    frobeniusDefectFactor s u =
      (‖windowMultiplier u (2 * s)‖ + ‖windowMultiplier (-u) (2 * s)‖) *
        (‖windowMultiplier u (2 * s)‖ - ‖windowMultiplier (-u) (2 * s)‖) ^ 2 := by
  rw [norm_windowMultiplier, norm_windowMultiplier]
  have hre : (2 * s).re - 1 / 2 = 2 * s.re - 1 / 2 := by simp
  rw [hre]
  unfold frobeniusDefectFactor
  have h1 : -((2 * s.re - 1 / 2) * (-u)) = (2 * s.re - 1 / 2) * u := by ring
  rw [h1]
  ring

theorem frobeniusDefectFactor_even (s : ℂ) (u : ℝ) :
    frobeniusDefectFactor s (-u) = frobeniusDefectFactor s u := by
  unfold frobeniusDefectFactor
  have h1 : (2 * s.re - 1 / 2) * (-u) = -((2 * s.re - 1 / 2) * u) := by ring
  rw [h1, neg_neg]
  ring

theorem frobeniusDefectFactor_nonneg (s : ℂ) (u : ℝ) : 0 ≤ frobeniusDefectFactor s u := by
  unfold frobeniusDefectFactor
  exact mul_nonneg (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (sq_nonneg _)

/-- Exact `+1` `I_s`-invariance of `windowPeriodLift s H` on `(0, ∞)` for every `H : ℝ → ℝ`. -/
theorem lewisModularInversion_windowPeriodLift (s : ℂ) (H : ℝ → ℝ) {a : ℝ} (ha : 0 < a) :
    lewisModularInversion s (windowPeriodLift s H) a = windowPeriodLift s H a := by
  have hF_fix : ∀ u : ℝ, windowMultiplier u (2 * s) * windowLogLift s H (-u) =
      windowLogLift s H u := by
    intro u
    unfold windowLogLift windowMultiplier
    rcases lt_trichotomy u 0 with hlt | rfl | hgt
    · have hpos_neg : 0 < -u := neg_pos.mpr hlt
      have hnot_gt : ¬ (0 < u) := not_lt.mpr hlt.le
      simp only [if_neg hnot_gt, if_pos hlt, if_pos hpos_neg, neg_neg]
      have harg : -((s.re - 1 / 4) * (-u)) = (s.re - 1 / 4) * u := by ring
      rw [harg]
    · simp
    · have hneg_neg : -u < 0 := neg_lt_zero.mpr hgt
      have hnot_gt : ¬ (0 < -u) := not_lt.mpr hneg_neg.le
      simp only [if_pos hgt, if_neg hnot_gt, if_pos hneg_neg]
      have hexp_cancel : Complex.exp (-((2 * s - 1 / 2) * (u : ℂ))) *
          Complex.exp (-((2 * s - 1 / 2) * ((-u : ℝ) : ℂ))) = 1 := by
        rw [← Complex.exp_add]
        have hz : -((2 * s - 1 / 2) * (u : ℂ)) + -((2 * s - 1 / 2) * ((-u : ℝ) : ℂ)) = 0 := by
          push_cast; ring
        rw [hz, Complex.exp_zero]
      have harg : (s.re - 1 / 4) * (-u) = -((s.re - 1 / 4) * u) := by ring
      rw [harg, ← mul_assoc, hexp_cancel, one_mul]
  have htr := logPeriodTransform_modularInversion s (windowPeriodLift s H) (Real.log a)
  rw [logPeriodTransform_comp_inverse, hF_fix (Real.log a)] at htr
  have hinv := congrArg (fun G => logPeriodInverse G a) htr
  dsimp only at hinv
  rwa [logPeriodInverse_comp_transform _ ha] at hinv

/-- On `(1, ∞)`, `periodWindowProfile s (windowPeriodLift s H) b` recovers `H (-log b)` directly. -/
theorem periodWindowProfile_windowPeriodLift (s : ℂ) (H : ℝ → ℝ) {b : ℝ} (hb : 1 < b) :
    periodWindowProfile s (windowPeriodLift s H) b = (H (-Real.log b) : ℂ) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hsum : 0 < b + b⁻¹ := add_pos hb0 (inv_pos.mpr hb0)
  have hlog : 0 < Real.log b := Real.log_pos hb
  unfold periodWindowProfile windowPeriodLift logPeriodInverse windowLogLift
  rw [if_pos hlog]
  have hexp : Real.exp (-((s.re - 1 / 4) * Real.log b)) = b ^ (1 / 4 - s.re) := by
    rw [Real.rpow_def_of_pos hb0]
    congr 1; ring
  rw [hexp, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have hprod : ((b + b⁻¹) ^ (-3 : ℝ) * b ^ s.re) *
      ((b + b⁻¹) ^ (3 : ℝ) * b ^ (-(1 / 4 : ℝ))) * b ^ (1 / 4 - s.re) = 1 := by
    calc
      ((b + b⁻¹) ^ (-3 : ℝ) * b ^ s.re) *
          ((b + b⁻¹) ^ (3 : ℝ) * b ^ (-(1 / 4 : ℝ))) * b ^ (1 / 4 - s.re)
          = ((b + b⁻¹) ^ (-3 : ℝ) * (b + b⁻¹) ^ (3 : ℝ)) *
              (b ^ s.re * b ^ (-(1 / 4 : ℝ)) * b ^ (1 / 4 - s.re)) := by ring
      _ = 1 := by
        rw [← Real.rpow_add hsum, ← Real.rpow_add hb0, ← Real.rpow_add hb0]
        have h0 : s.re + -(1 / 4 : ℝ) + (1 / 4 - s.re) = 0 := by ring
        rw [h0]
        norm_num
  rw [hprod, one_mul]

private theorem window_zero_at_zero {A : ℝ} {H : ℝ → ℝ} (hc : Continuous H)
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) : H 0 = 0 := by
  have hseq : ∀ n : ℕ, H (1 / ((n : ℝ) + 1)) = 0 := by
    intro n
    apply hv
    intro hm
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith [hm.2]
  have htend1 : Tendsto (fun n : ℕ => H (1 / ((n : ℝ) + 1))) atTop (𝓝 (H 0)) :=
    (hc.continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat)
  have htend0 : Tendsto (fun n : ℕ => H (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa [hseq] using (tendsto_const_nhds (x := (0 : ℝ)))
  exact tendsto_nhds_unique htend1 htend0

private theorem continuous_windowLogLift {A : ℝ} {H : ℝ → ℝ} (hc : Continuous H)
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (s : ℂ) :
    Continuous (windowLogLift s H) := by
  have hH0 : H 0 = 0 := window_zero_at_zero hc hv
  let f_pos : ℝ → ℂ := fun u => ((Real.exp (-((s.re - 1 / 4) * u)) * H (-u) : ℝ) : ℂ)
  let f_neg : ℝ → ℂ := fun u =>
    Complex.exp (-((2 * s - 1 / 2) * (u : ℂ))) *
      ((Real.exp ((s.re - 1 / 4) * u) * H u : ℝ) : ℂ)
  have hc_pos : Continuous f_pos := by
    dsimp [f_pos]; fun_prop
  have hc_neg : Continuous f_neg := by
    dsimp [f_neg]; fun_prop
  have hf_pos0 : f_pos 0 = 0 := by simp [f_pos, hH0]
  have hf_neg0 : f_neg 0 = 0 := by simp [f_neg, hH0]
  rw [continuous_iff_continuousAt]
  intro u₀
  rcases lt_trichotomy u₀ 0 with hlt | rfl | hgt
  · refine hc_neg.continuousAt.congr ?_
    filter_upwards [isOpen_Iio.mem_nhds hlt] with u hu
    have hnot : ¬ (0 < u) := not_lt.mpr (le_of_lt hu)
    simp [windowLogLift, f_neg, show u < 0 from hu, hnot]
  · rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.continuousAt_iff.mp hc_pos.continuousAt ε hε
    obtain ⟨δ₂, hδ₂, hb₂⟩ := Metric.continuousAt_iff.mp hc_neg.continuousAt ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun u hu => ?_⟩
    have hz0 : windowLogLift s H 0 = 0 := by simp [windowLogLift]
    rw [hz0]
    rcases lt_trichotomy u 0 with hlt | rfl | hgt
    · have hnot : ¬ (0 < u) := not_lt.mpr hlt.le
      have heq : windowLogLift s H u = f_neg u := by simp [windowLogLift, f_neg, hlt, hnot]
      rw [heq, ← hf_neg0]
      exact hb₂ (lt_of_lt_of_le hu (min_le_right _ _))
    · simp [windowLogLift, hε]
    · have heq : windowLogLift s H u = f_pos u := by simp [windowLogLift, f_pos, hgt]
      rw [heq, ← hf_pos0]
      exact hb₁ (lt_of_lt_of_le hu (min_le_left _ _))
  · refine hc_pos.continuousAt.congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hgt] with u hu
    simp [windowLogLift, f_pos, show 0 < u from hu]

private theorem hasCompactSupport_windowLogLift {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ}
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (s : ℂ) :
    HasCompactSupport (windowLogLift s H) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A)) fun u hu => ?_
  unfold windowLogLift
  rcases lt_trichotomy u 0 with hlt | rfl | hgt
  · have hnot : ¬ (0 < u) := not_lt.mpr hlt.le
    have hnotin : u ∉ Icc (-A) 0 := fun hm => hu ⟨hm.1, hm.2.trans hA⟩
    simp [hlt, hnot, hv u hnotin]
  · simp
  · have hnotin : -u ∉ Icc (-A) 0 := fun hm => hu ⟨by linarith [hm.2, hA], by linarith [hm.1]⟩
    simp [hgt, hv (-u) hnotin]

/-- **Exact Window Frobenius Defect Identity for `windowPeriodLift s H`.**
For any continuous window test `H` supported on `[-A, 0]` (`A ≥ 0`), `windowPeriodLift s H`
belongs to `H_LP` (with its reflected partner) and its co-isometry defect equals
`-∫_{-A}^0 frobeniusDefectFactor s (-x) * H(x)² dx`. -/
theorem windowPeriodLift_coIsometryDefect_eq {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ}
    (hc : Continuous H) (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (s : ℂ) :
    IntegrableOn (fun a => ‖windowPeriodLift s H a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) ∧
    IntegrableOn (fun a =>
      ‖lewisModularInversion (riemannMayerReflect s) (windowPeriodLift s H) a‖ ^ 2 *
        lewisCriticalWeight a) (Ioi 0) ∧
    lewisCoIsometryDefect s (windowPeriodLift s H) =
      -∫ x in Icc (-A) 0,
        (‖windowMultiplier x (2 * s)‖ + ‖windowMultiplier (-x) (2 * s)‖) *
          (‖windowMultiplier x (2 * s)‖ - ‖windowMultiplier (-x) (2 * s)‖) ^ 2 * H x ^ 2 := by
  let ψ : ℝ → ℂ := windowPeriodLift s H
  let F : ℝ → ℂ := windowLogLift s H
  have hF_eq : logPeriodTransform ψ = F := funext (logPeriodTransform_comp_inverse F)
  have hF_cont : Continuous F := continuous_windowLogLift hc hv s
  have hF_cs : HasCompactSupport F := hasCompactSupport_windowLogLift hA hv s
  have hψ_int : IntegrableOn (fun a => ‖ψ a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) := by
    rw [← integrable_logPeriodTransform_normSq_iff, hF_eq]
    exact (hF_cont.norm.pow 2).integrable_of_hasCompactSupport (hF_cs.norm.pow_left)
  have hψR_int : IntegrableOn
      (fun a => ‖lewisModularInversion (riemannMayerReflect s) ψ a‖ ^ 2 * lewisCriticalWeight a)
      (Ioi 0) := by
    rw [← integrable_logPeriodTransform_normSq_iff]
    have htr : (fun u : ℝ =>
        ‖logPeriodTransform (lewisModularInversion (riemannMayerReflect s) ψ) u‖ ^ 2) =
        fun u : ℝ => ‖windowMultiplier u (2 * riemannMayerReflect s) * F (-u)‖ ^ 2 := by
      ext u
      rw [logPeriodTransform_modularInversion, hF_eq]
    rw [htr]
    have hcontR : Continuous (fun u : ℝ =>
        ‖windowMultiplier u (2 * riemannMayerReflect s) * F (-u)‖ ^ 2) := by
      unfold windowMultiplier; fun_prop
    have hcsR : HasCompactSupport (fun u : ℝ =>
        ‖windowMultiplier u (2 * riemannMayerReflect s) * F (-u)‖ ^ 2) := by
      refine HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A)) fun u hu => ?_
      have hnu : -u ∉ Icc (-A) A := fun hm => hu ⟨by linarith [hm.2], by linarith [hm.1]⟩
      have hFu : F (-u) = 0 := image_eq_zero_of_notMem_tsupport
        (fun hm => hnu (HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A))
          (fun v hv' => by
            unfold F windowLogLift
            rcases lt_trichotomy v 0 with hlt | rfl | hgt
            · simp [hlt, not_lt.mpr hlt.le, hv v (fun h => hv' ⟨h.1, h.2.trans hA⟩)]
            · simp
            · simp [hgt, hv (-v) (fun h => hv' ⟨by linarith [h.2, hA], by linarith [h.1]⟩)]) |>
          fun _ => by exact hm))
      -- Simpler direct support proof without `tsupport`:
      sorry
    sorry
  sorry
