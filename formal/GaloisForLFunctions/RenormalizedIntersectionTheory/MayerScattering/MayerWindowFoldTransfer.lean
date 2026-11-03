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
  have hc6 : (2 * Real.cosh u) ^ (-6 : ℝ) =
      (2 * Real.cosh u) ^ (-3 : ℝ) * (2 * Real.cosh u) ^ (-3 : ℝ) := by
    rw [← Real.rpow_add hc_pos]; norm_num
  have hexp4 : Real.exp u * Real.exp (u * -(1 / 2 : ℝ)) =
      Real.exp (u / 4) * Real.exp (u / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  have hreal_eq : Real.exp u * ((2 * Real.cosh u) ^ (-6 : ℝ) * Real.exp (u * -(1 / 2 : ℝ))) =
      ((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (u / 4)) *
        ((2 * Real.cosh u) ^ (-3 : ℝ) * Real.exp (u / 4)) := by
    calc
      Real.exp u * ((2 * Real.cosh u) ^ (-6 : ℝ) * Real.exp (u * -(1 / 2 : ℝ)))
          = (2 * Real.cosh u) ^ (-6 : ℝ) *
              (Real.exp u * Real.exp (u * -(1 / 2 : ℝ))) := by ring
      _ = ((2 * Real.cosh u) ^ (-3 : ℝ) * (2 * Real.cosh u) ^ (-3 : ℝ)) *
            (Real.exp (u / 4) * Real.exp (u / 4)) := by rw [hc6, hexp4]
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
    rw [neg_neg] at h1
    have h2 : logPeriodTransform (lewisModularInversion s ψ) (-u) = logPeriodTransform ψ (-u) := by
      unfold logPeriodTransform
      rw [hfix (Real.exp (-u)) (Real.exp_pos (-u))]
    rwa [h2] at h1
  have hnorm_wm : ‖windowMultiplier (-u) (2 * s)‖ = Real.exp (δ * u) := by
    rw [norm_windowMultiplier]
    have hre : (2 * s).re = 2 * s.re := by simp
    rw [hre]
    congr 1; dsimp [δ]; ring
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
          have h1 : (-3 : ℝ) + -3 = -6 := by norm_num
          have h2 : u / 4 + u / 4 = u / 2 := by ring
          rw [h1, h2]
    calc
      ‖logPeriodTransform ψ u‖ * (Real.exp (δ * u) * ‖logPeriodTransform ψ u‖)
          = Real.exp (δ * u) * (‖logPeriodTransform ψ u‖ * ‖logPeriodTransform ψ u‖) := by ring
      _ = (2 * Real.cosh u) ^ (-6 : ℝ) * (Real.exp (δ * u) * Real.exp (u / 2)) *
            ‖ψ (Real.exp u)‖ ^ 2 := by rw [hFu_sq]; ring
      _ = (2 * Real.cosh u) ^ (-6 : ℝ) * Real.exp (2 * s.re * u) * ‖ψ (Real.exp u)‖ ^ 2 := by
        rw [← Real.exp_add]; congr 2; congr 1; dsimp [δ]; ring
  have hb_pow1 : (Real.exp u) ^ (2 * s.re - 1) = Real.exp ((2 * s.re - 1) * u) := by
    rw [Real.rpow_def_of_pos hexp_pos, Real.log_exp]; congr 1; ring
  have hb_pow2 : (Real.exp u) ^ δ = Real.exp (δ * u) := by
    rw [Real.rpow_def_of_pos hexp_pos, Real.log_exp]; congr 1; ring
  have hb_pow3 : (Real.exp u) ^ (-δ) = Real.exp (-(δ * u)) := by
    rw [Real.rpow_def_of_pos hexp_pos, Real.log_exp]; congr 1; ring
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
  have hlift_eq : windowPeriodLift s H = logPeriodInverse (windowLogLift s H) := rfl
  have htr_fn : logPeriodTransform (lewisModularInversion s (windowPeriodLift s H)) =
      windowLogLift s H := by
    ext u
    rw [logPeriodTransform_modularInversion, hlift_eq, logPeriodTransform_comp_inverse,
      hF_fix u]
  have hinv := congrArg (fun G => logPeriodInverse G a) htr_fn
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
  have hcast :
      (((b + b⁻¹) ^ (-3 : ℝ) * b ^ s.re : ℝ) : ℂ) *
        ((((b + b⁻¹) ^ (3 : ℝ) * b ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
          ((b ^ (1 / 4 - s.re) * H (-Real.log b) : ℝ) : ℂ)) =
      ((((b + b⁻¹) ^ (-3 : ℝ) * b ^ s.re) *
          ((b + b⁻¹) ^ (3 : ℝ) * b ^ (-(1 / 4 : ℝ))) * b ^ (1 / 4 - s.re) : ℝ) : ℂ) *
        (H (-Real.log b) : ℂ) := by
    push_cast; ring
  rw [hexp, hcast, hprod, Complex.ofReal_one, one_mul]

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
    rw [show (fun n : ℕ => H (1 / ((n : ℝ) + 1))) = fun _ : ℕ => (0 : ℝ) from funext hseq]
    exact tendsto_const_nhds
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

private theorem windowLogLift_eq_zero_of_notMem {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ}
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (s : ℂ) {u : ℝ} (hu : u ∉ Icc (-A) A) :
    windowLogLift s H u = 0 := by
  unfold windowLogLift
  rcases lt_trichotomy u 0 with hlt | rfl | hgt
  · simp [hlt, not_lt.mpr hlt.le, hv u (fun hm => hu ⟨hm.1, hm.2.trans hA⟩)]
  · simp
  · simp [hgt, hv (-u) (fun hm => hu ⟨by linarith [hm.2, hA], by linarith [hm.1]⟩)]

private theorem hasCompactSupport_windowLogLift {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ}
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (s : ℂ) :
    HasCompactSupport (windowLogLift s H) :=
  HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A)) fun _ hu =>
    windowLogLift_eq_zero_of_notMem hA hv s hu

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
  have hH0 : H 0 = 0 := window_zero_at_zero hc hv
  have hF_eq : logPeriodTransform ψ = F := funext (logPeriodTransform_comp_inverse F)
  have hF_cont : Continuous F := continuous_windowLogLift hc hv s
  have hF_cs : HasCompactSupport F := hasCompactSupport_windowLogLift hA hv s
  have hψ_int : IntegrableOn (fun a => ‖ψ a‖ ^ 2 * lewisCriticalWeight a) (Ioi 0) := by
    rw [← integrable_logPeriodTransform_normSq_iff, hF_eq]
    exact (hF_cont.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A)) fun u hu => by
        simp [F, windowLogLift_eq_zero_of_notMem hA hv s hu])
  have hψR_int : IntegrableOn
      (fun a => ‖lewisModularInversion (riemannMayerReflect s) ψ a‖ ^ 2 * lewisCriticalWeight a)
      (Ioi 0) := by
    rw [← integrable_logPeriodTransform_normSq_iff]
    have htr : (fun u : ℝ =>
        ‖logPeriodTransform (lewisModularInversion (riemannMayerReflect s) ψ) u‖ ^ 2) =
        fun u : ℝ => ‖windowMultiplier u (2 * riemannMayerReflect s) * F (-u)‖ ^ 2 := by
      ext u; rw [logPeriodTransform_modularInversion, hF_eq]
    rw [htr]
    have hcontR : Continuous (fun u : ℝ =>
        ‖windowMultiplier u (2 * riemannMayerReflect s) * F (-u)‖ ^ 2) := by
      have hc1 : Continuous (fun u : ℝ => windowMultiplier u (2 * riemannMayerReflect s)) := by
        unfold windowMultiplier; fun_prop
      have hc2 : Continuous (fun u : ℝ => F (-u)) := hF_cont.comp continuous_neg
      exact ((hc1.mul hc2).norm).pow 2
    refine hcontR.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A)) fun u hu => ?_)
    have hnu : -u ∉ Icc (-A) A := fun hm => hu ⟨by linarith [hm.2], by linarith [hm.1]⟩
    simp [F, windowLogLift_eq_zero_of_notMem hA hv s hnu]
  -- Compact-support integrability of any `rpow`-weighted square of `ψ` on `Ioi 1`:
  have hfold_int : ∀ β : ℝ,
      IntegrableOn (fun b => ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ β)) (Ioi 1) := by
    intro β
    have hψ_cont : ContinuousOn ψ (Ioi 0) := by
      intro b hb
      have hb0 : 0 < b := hb
      have hsum : b + b⁻¹ ≠ 0 := (add_pos hb0 (inv_pos.mpr hb0)).ne'
      have c1 : ContinuousAt (fun x : ℝ => (x + x⁻¹) ^ (3 : ℝ)) b :=
        (continuousAt_id.add (continuousAt_inv₀ hb0.ne')).rpow
          (continuousAt_const : ContinuousAt (fun _ : ℝ => (3 : ℝ)) b) (Or.inl hsum)
      have c2 : ContinuousAt (fun x : ℝ => x ^ (-(1 / 4 : ℝ))) b :=
        continuousAt_id.rpow
          (continuousAt_const : ContinuousAt (fun _ : ℝ => -(1 / 4 : ℝ)) b) (Or.inl hb0.ne')
      have c3 : ContinuousAt (fun x : ℝ => F (Real.log x)) b :=
        ContinuousAt.comp (g := F) (f := Real.log) hF_cont.continuousAt (Real.continuousAt_log hb0.ne')
      have c12 : ContinuousAt (fun x : ℝ =>
          (((x + x⁻¹) ^ (3 : ℝ) * x ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) b :=
        Complex.continuous_ofReal.continuousAt.comp (c1.mul c2)
      exact (c12.mul c3).continuousWithinAt
    have hcont_g : ContinuousOn
        (fun b : ℝ => ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ β)) (Icc 1 (Real.exp A)) := by
      intro b hb
      have hb0 : 0 < b := zero_lt_one.trans_le hb.1
      have hsum : b + b⁻¹ ≠ 0 := (add_pos hb0 (inv_pos.mpr hb0)).ne'
      have cψ : ContinuousAt (fun x : ℝ => ‖ψ x‖ ^ 2) b :=
        (hψ_cont.continuousAt (isOpen_Ioi.mem_nhds hb0)).norm.pow 2
      have cw1 : ContinuousAt (fun x : ℝ => (x + x⁻¹) ^ (-6 : ℝ)) b :=
        (continuousAt_id.add (continuousAt_inv₀ hb0.ne')).rpow
          (continuousAt_const : ContinuousAt (fun _ : ℝ => (-6 : ℝ)) b) (Or.inl hsum)
      have cw2 : ContinuousAt (fun x : ℝ => x ^ β) b :=
        continuousAt_id.rpow (continuousAt_const : ContinuousAt (fun _ : ℝ => β) b) (Or.inl hb0.ne')
      exact (cψ.mul (cw1.mul cw2)).continuousWithinAt
    have hint_Ioc : IntegrableOn
        (fun b : ℝ => ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ β)) (Ioc 1 (Real.exp A)) :=
      hcont_g.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hind_eq : Set.EqOn
        (fun b : ℝ => ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ β))
        ((Ioc 1 (Real.exp A)).indicator
          (fun b => ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ β))) (Ioi 1) := by
      intro b hb
      dsimp only
      by_cases hle : b ≤ Real.exp A
      · have hmem : b ∈ Ioc 1 (Real.exp A) := ⟨hb, hle⟩
        rw [indicator_of_mem hmem]
      · rw [not_le] at hle
        have hnot : Real.log b ∉ Icc (-A) A := fun hm =>
          hle.not_ge ((Real.log_le_iff_le_exp (zero_lt_one.trans hb)).mp hm.2)
        have hFz : F (Real.log b) = 0 := windowLogLift_eq_zero_of_notMem hA hv s hnot
        have hψz : ψ b = 0 := by simp [ψ, windowPeriodLift, logPeriodInverse, F, hFz]
        rw [indicator_of_notMem (fun hm => hle.not_ge hm.2), hψz]
        simp
    have hint_ind : IntegrableOn
        ((Ioc 1 (Real.exp A)).indicator
          (fun b => ‖ψ b‖ ^ 2 * ((b + b⁻¹) ^ (-6 : ℝ) * b ^ β))) (Ioi 1) :=
      (integrableOn_indicator_iff measurableSet_Ioc).mpr (hint_Ioc.mono_set inter_subset_left)
    exact hint_ind.congr_fun (fun b hb => (hind_eq hb).symm) measurableSet_Ioi
  refine ⟨hψ_int, hψR_int, ?_⟩
  rw [lewisCoIsometryDefect_eq_neg_log_integral
    (fun a ha => lewisModularInversion_windowPeriodLift s H ha)
    hψ_int hψR_int (hfold_int _) (hfold_int _), hF_eq]
  congr 1
  -- On `u > 0`, `‖F u * F (-u)‖ = H (-u) ^ 2`:
  have hpt_pos : ∀ u ∈ Ioi (0 : ℝ),
      (Real.exp ((2 * s.re - 1 / 2) * u) + Real.exp (-((2 * s.re - 1 / 2) * u))) *
        (Real.exp ((2 * s.re - 1 / 2) * u) - Real.exp (-((2 * s.re - 1 / 2) * u))) ^ 2 *
        ‖F u * F (-u)‖ = frobeniusDefectFactor s u * H (-u) ^ 2 := by
    intro u hu
    have hu0 : 0 < u := hu
    have hnu_lt : -u < 0 := neg_lt_zero.mpr hu0
    have hnu_not : ¬ (0 < -u) := not_lt.mpr hnu_lt.le
    have hpair : ‖F u * F (-u)‖ = H (-u) ^ 2 := by
      dsimp [F, windowLogLift]
      rw [if_pos hu0, if_neg hnu_not, if_pos hnu_lt, norm_mul, norm_mul,
        Complex.norm_exp, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      have hre_exp : (-((2 * s - 1 / 2) * ((-u : ℝ) : ℂ))).re = (2 * s.re - 1 / 2) * u := by
        simp
      rw [hre_exp]
      have hexp_one : Real.exp (-((s.re - 1 / 4) * u)) *
          (Real.exp ((2 * s.re - 1 / 2) * u) * Real.exp ((s.re - 1 / 4) * (-u))) = 1 := by
        rw [← Real.exp_add, ← Real.exp_add]
        have hz : -((s.re - 1 / 4) * u) + ((2 * s.re - 1 / 2) * u + (s.re - 1 / 4) * (-u)) = 0 := by
          ring
        rw [hz, Real.exp_zero]
      calc
        Real.exp (-((s.re - 1 / 4) * u)) * |H (-u)| *
            (Real.exp ((2 * s.re - 1 / 2) * u) * (Real.exp ((s.re - 1 / 4) * (-u)) * |H (-u)|))
            = (Real.exp (-((s.re - 1 / 4) * u)) *
                (Real.exp ((2 * s.re - 1 / 2) * u) * Real.exp ((s.re - 1 / 4) * (-u)))) *
                (|H (-u)| * |H (-u)|) := by ring
        _ = H (-u) ^ 2 := by rw [hexp_one, one_mul, ← sq, sq_abs]
    rw [hpair]; rfl
  rw [setIntegral_congr_fun measurableSet_Ioi hpt_pos, ← integral_indicator measurableSet_Ioi]
  -- Match indicator on `Ioi 0` with reflected indicator on `Icc (-A) 0`:
  have hind_neg : (Ioi (0 : ℝ)).indicator (fun u => frobeniusDefectFactor s u * H (-u) ^ 2) =
      fun u => (Icc (-A) 0).indicator (fun x => frobeniusDefectFactor s (-x) * H x ^ 2) (-u) := by
    ext u
    rcases lt_trichotomy u 0 with hlt | rfl | hgt
    · have h1 : u ∉ Ioi (0 : ℝ) := by simp [hlt.le]
      have h2 : -u ∉ Icc (-A) 0 := fun hm => by linarith [hm.2]
      rw [indicator_of_notMem h1, indicator_of_notMem h2]
    · have h1 : (0 : ℝ) ∉ Ioi (0 : ℝ) := by simp
      rw [indicator_of_notMem h1, neg_zero]
      by_cases h0m : (0 : ℝ) ∈ Icc (-A) 0
      · simp [h0m, hH0]
      · simp [h0m]
    · have hgt_mem : u ∈ Ioi (0 : ℝ) := hgt
      rw [indicator_of_mem hgt_mem]
      by_cases hle : u ≤ A
      · have hm : -u ∈ Icc (-A) 0 := ⟨by linarith, by linarith⟩
        rw [indicator_of_mem hm, neg_neg]
      · rw [not_le] at hle
        have hnot : -u ∉ Icc (-A) 0 := fun hm => by linarith [hm.1]
        rw [indicator_of_notMem hnot, hv (-u) hnot]
        ring
  rw [hind_neg, integral_neg_eq_self, integral_indicator measurableSet_Icc]
  refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  rw [frobeniusDefectFactor_even, frobeniusDefectFactor_eq_windowMultiplier]

/-- Multiplicative-Haar `db / b` substitution mapping `[1, e^A / n]` onto `[-A, -log n]`. -/
private theorem integral_Icc_fold_haar_subst {A : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hlog : Real.log n ≤ A) (g : ℝ → ℝ) :
    (∫ u in Icc (-A) (-Real.log n), g u) =
      ∫ b in Icc (1 : ℝ) (Real.exp A / n), g (-Real.log b - Real.log n) / b := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  let B : ℝ := Real.exp A / n
  by_cases hlt : Real.log n < A
  · have h1B : 1 < B := by
      dsimp [B]
      rw [one_lt_div hn_pos]
      exact (Real.log_lt_iff_lt_exp hn_pos).mp hlt
    let φ : ℝ → ℝ := fun b => -Real.log b - Real.log n
    have himg : φ '' Ioo (1 : ℝ) B = Ioo (-A) (-Real.log n) := by
      ext u
      simp only [φ, mem_image, mem_Ioo]
      constructor
      · rintro ⟨b, ⟨hb1, hbB⟩, rfl⟩
        have hb0 : 0 < b := zero_lt_one.trans hb1
        have hlog_pos : 0 < Real.log b := Real.log_pos hb1
        have hlog_lt : Real.log b < A - Real.log n := by
          have h := Real.log_lt_log hb0 hbB
          dsimp [B] at h
          rw [Real.log_div (Real.exp_pos A).ne' hn_pos.ne', Real.log_exp] at h
          exact h
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨hu1, hu2⟩
        let b : ℝ := Real.exp (-u - Real.log n)
        have hb1 : 1 < b := Real.one_lt_exp_iff.mpr (by linarith)
        have hbB : b < B := by
          dsimp [b, B]
          have h1 : Real.exp (-u - Real.log n) = Real.exp (-u) / n := by
            rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg (Real.log n), Real.exp_log hn_pos,
              div_eq_mul_inv]
          rw [h1]
          exact div_lt_div_of_pos_right (Real.exp_lt_exp.mpr (by linarith)) hn_pos
        refine ⟨b, ⟨hb1, hbB⟩, ?_⟩
        dsimp [b]
        rw [Real.log_exp]
        ring
    have hinj : InjOn φ (Ioo 1 B) := by
      intro b₁ hb₁ b₂ hb₂ heq
      dsimp [φ] at heq
      have hlog_eq : Real.log b₁ = Real.log b₂ := by linarith
      exact Real.log_injOn_pos (zero_lt_one.trans hb₁.1) (zero_lt_one.trans hb₂.1) hlog_eq
    have hderiv : ∀ b ∈ Ioo (1 : ℝ) B, HasDerivWithinAt φ (-b⁻¹) (Ioo 1 B) b := by
      intro b hb
      have hb0 : 0 < b := zero_lt_one.trans hb.1
      exact (((Real.hasDerivAt_log hb0.ne').neg).sub_const (Real.log n)).hasDerivWithinAt
    have hint := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      measurableSet_Ioo hderiv hinj g
    rw [himg] at hint
    rw [← setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc,
      ← setIntegral_congr_set (s := Ioo 1 B) (t := Icc 1 B) MeasureTheory.Ioo_ae_eq_Icc, hint]
    refine setIntegral_congr_fun measurableSet_Ioo fun b hb => ?_
    have hb0 : 0 < b := zero_lt_one.trans hb.1
    dsimp only [φ, smul_eq_mul]
    rw [abs_neg, abs_of_pos (inv_pos.mpr hb0), div_eq_mul_inv, mul_comm]
  · have heq_A : A = Real.log n := le_antisymm (not_lt.mp hlt) hlog
    rw [heq_A, Real.exp_log hn_pos, div_self hn_pos.ne']
    simp

/-- **Multiplicative-Haar Representation of `foldSym A (log n) H` on `[1, e^A / n]`.** -/
theorem foldSym_eq_haar_periodWindowProfile {A : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hlog : Real.log n ≤ A) (s : ℂ) (H : ℝ → ℝ) :
    foldSym A (Real.log n) H =
      (1 / 2) * ∫ b in Icc (1 : ℝ) (Real.exp A / n),
        ((periodWindowProfile s (windowPeriodLift s H) (n * b) +
          periodWindowProfile s (windowPeriodLift s H) b).re) ^ 2 / b := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hn_ge2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold foldSym
  rw [integral_indicator measurableSet_Icc, integral_Icc_fold_haar_subst hn hlog]
  congr 1
  rw [← setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc,
    ← setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc]
  refine setIntegral_congr_fun measurableSet_Ioo fun b hb => ?_
  have hb1 : 1 < b := hb.1
  have hb0 : 0 < b := zero_lt_one.trans hb1
  have hnb1 : 1 < (n : ℝ) * b := by
    calc
      (1 : ℝ) < 1 * b := by linarith
      _ ≤ (n : ℝ) * b := mul_le_mul_of_nonneg_right (by linarith) hb0.le
  rw [periodWindowProfile_windowPeriodLift s H hb1,
    periodWindowProfile_windowPeriodLift s H hnb1]
  have hlog_mul : -Real.log ((n : ℝ) * b) = -Real.log b - Real.log n := by
    rw [Real.log_mul hn_pos.ne' hb0.ne']; ring
  have hshift : (-Real.log b - Real.log n) + Real.log n = -Real.log b := by ring
  rw [hlog_mul, hshift]
  simp only [Complex.add_re, Complex.ofReal_re]

/-- **Multiplicative-Haar Representation of `foldEnergy A (log n) H` on `[1, e^A / n]`.** -/
theorem foldEnergy_eq_haar_periodWindowProfile {A : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hlog : Real.log n ≤ A) (s : ℂ) (H : ℝ → ℝ) :
    foldEnergy A (Real.log n) H =
      ∫ b in Icc (1 : ℝ) (Real.exp A / n),
        ((periodWindowProfile s (windowPeriodLift s H) (n * b) -
          periodWindowProfile s (windowPeriodLift s H) b).re) ^ 2 / b := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have hn_ge2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold foldEnergy
  rw [integral_indicator measurableSet_Icc, integral_Icc_fold_haar_subst hn hlog]
  rw [← setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc,
    ← setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc]
  refine setIntegral_congr_fun measurableSet_Ioo fun b hb => ?_
  have hb1 : 1 < b := hb.1
  have hb0 : 0 < b := zero_lt_one.trans hb1
  have hnb1 : 1 < (n : ℝ) * b := by
    calc
      (1 : ℝ) < 1 * b := by linarith
      _ ≤ (n : ℝ) * b := mul_le_mul_of_nonneg_right (by linarith) hb0.le
  rw [periodWindowProfile_windowPeriodLift s H hb1,
    periodWindowProfile_windowPeriodLift s H hnb1]
  have hlog_mul : -Real.log ((n : ℝ) * b) = -Real.log b - Real.log n := by
    rw [Real.log_mul hn_pos.ne' hb0.ne']; ring
  have hshift : (-Real.log b - Real.log n) + Real.log n = -Real.log b := by ring
  rw [hlog_mul, hshift]
  simp only [Complex.sub_re, Complex.ofReal_re]

/-! ## Part 3: Two-sided quantitative `(foldSym, foldEnergy)` transfer & `T₂`-stick Schur elimination -/

/-- Monotonicity of `frobeniusDefectFactor s` on `[0, ∞)`. -/
theorem frobeniusDefectFactor_mono_nonneg (s : ℂ) {u₁ u₂ : ℝ}
    (hu₁ : 0 ≤ u₁) (hle : u₁ ≤ u₂) :
    frobeniusDefectFactor s u₁ ≤ frobeniusDefectFactor s u₂ := by
  let δ : ℝ := |2 * s.re - 1 / 2|
  have hδ_nn : 0 ≤ δ := abs_nonneg _
  have habs_eq : ∀ u : ℝ, frobeniusDefectFactor s u =
      (Real.exp (δ * u) + (Real.exp (δ * u))⁻¹) *
        (Real.exp (δ * u) - (Real.exp (δ * u))⁻¹) ^ 2 := by
    intro u
    unfold frobeniusDefectFactor
    dsimp [δ]
    rcases le_or_gt 0 (2 * s.re - 1 / 2) with hpos | hneg
    · rw [abs_of_nonneg hpos, Real.exp_neg]
    · rw [abs_of_neg hneg]
      have h1 : -(2 * s.re - 1 / 2) * u = -((2 * s.re - 1 / 2) * u) := by ring
      rw [h1, Real.exp_neg, inv_inv]
      ring
  rw [habs_eq u₁, habs_eq u₂]
  let e₁ : ℝ := Real.exp (δ * u₁)
  let e₂ : ℝ := Real.exp (δ * u₂)
  have he₁_ge1 : 1 ≤ e₁ := Real.one_le_exp (mul_nonneg hδ_nn hu₁)
  have he₁_pos : 0 < e₁ := zero_lt_one.trans_le he₁_ge1
  have he₁_le_e₂ : e₁ ≤ e₂ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle hδ_nn)
  have he₂_ge1 : 1 ≤ e₂ := he₁_ge1.trans he₁_le_e₂
  have he₂_pos : 0 < e₂ := zero_lt_one.trans_le he₂_ge1
  have hsum_le : e₁ + e₁⁻¹ ≤ e₂ + e₂⁻¹ := by
    have hdiff : (e₂ + e₂⁻¹) - (e₁ + e₁⁻¹) = (e₂ - e₁) * (e₁ * e₂ - 1) / (e₁ * e₂) := by
      field_simp [he₁_pos.ne', he₂_pos.ne']; ring
    have hprod_ge1 : 1 ≤ e₁ * e₂ := one_le_mul_of_one_le_of_one_le he₁_ge1 he₂_ge1
    have hnn : 0 ≤ (e₂ - e₁) * (e₁ * e₂ - 1) / (e₁ * e₂) :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
    linarith
  have hd₁_nn : 0 ≤ e₁ - e₁⁻¹ := by
    have : e₁⁻¹ ≤ 1 := inv_le_one_of_one_le₀ he₁_ge1
    linarith
  have hdiff_le : e₁ - e₁⁻¹ ≤ e₂ - e₂⁻¹ := by
    have hinv_le : e₂⁻¹ ≤ e₁⁻¹ := inv_anti₀ he₁_pos he₁_le_e₂
    linarith
  have hsq_le : (e₁ - e₁⁻¹) ^ 2 ≤ (e₂ - e₂⁻¹) ^ 2 :=
    pow_le_pow_left₀ hd₁_nn hdiff_le 2
  exact mul_le_mul hsum_le hsq_le (sq_nonneg _) (by positivity)

private theorem frobeniusDefectFactor_log_nat (s : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    frobeniusDefectFactor s (Real.log n) =
      ((n : ℝ) ^ (2 * s.re - 1 / 2) + (n : ℝ) ^ (-(2 * s.re - 1 / 2))) *
        ((n : ℝ) ^ (2 * s.re - 1 / 2) - (n : ℝ) ^ (-(2 * s.re - 1 / 2))) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold frobeniusDefectFactor
  rw [Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0]
  have h1 : Real.log n * (2 * s.re - 1 / 2) = (2 * s.re - 1 / 2) * Real.log n := by ring
  have h2 : Real.log n * -(2 * s.re - 1 / 2) = -((2 * s.re - 1 / 2) * Real.log n) := by ring
  rw [h1, h2]

private theorem windowPeriodLift_neg_defect_eq_Icc {A : ℝ} (hA : 0 ≤ A) {H : ℝ → ℝ}
    (hc : Continuous H) (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (s : ℂ) :
    -lewisCoIsometryDefect s (windowPeriodLift s H) =
      ∫ x in Icc (-A) 0, frobeniusDefectFactor s (-x) * H x ^ 2 := by
  obtain ⟨_, _, hdef⟩ := windowPeriodLift_coIsometryDefect_eq hA hc hv s
  rw [hdef, neg_neg]
  refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  rw [frobeniusDefectFactor_even, frobeniusDefectFactor_eq_windowMultiplier]

/-- **Universal `n`-th Fold Lower Bound (`A ≥ log n`, `n ≥ 2`).**
At every active window stage `A ≥ log n`, the off-line co-isometry defect of `windowPeriodLift s H`
dominates `((n^δ + n^(-δ))(n^δ - n^(-δ))² / 4) * (foldSym A (log n) H - foldEnergy A (log n) H)`. -/
theorem windowPeriodLift_neg_defect_ge_foldSym_sub_foldEnergy {A : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hlog : Real.log n ≤ A) {H : ℝ → ℝ}
    (hc : Continuous H) (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (s : ℂ) :
    (((n : ℝ) ^ (2 * s.re - 1 / 2) + (n : ℝ) ^ (-(2 * s.re - 1 / 2))) *
      ((n : ℝ) ^ (2 * s.re - 1 / 2) - (n : ℝ) ^ (-(2 * s.re - 1 / 2))) ^ 2 / 4) *
      (foldSym A (Real.log n) H - foldEnergy A (Real.log n) H) ≤
      -lewisCoIsometryDefect s (windowPeriodLift s H) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hn_gt1 : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
  have hlog_pos : 0 < Real.log n := Real.log_pos hn_gt1
  have hA : 0 ≤ A := hlog_pos.le.trans hlog
  rw [windowPeriodLift_neg_defect_eq_Icc hA hc hv s, ← frobeniusDefectFactor_log_nat s hn1]
  have hsub_Icc : Icc (-A) (-Real.log n) ⊆ Icc (-A) 0 :=
    fun x hx => ⟨hx.1, hx.2.trans (by linarith)⟩
  -- SOS lower bound `H(x)² ≥ (1/8)(H(x) + H(x + ℓ))² - (1/4)(H(x) - H(x + ℓ))²`:
  let ℓ : ℝ := Real.log n
  have hint_sq : IntegrableOn (fun x => H x ^ 2) (Icc (-A) (-ℓ)) :=
    (hc.pow 2).continuousOn.integrableOn_Icc
  have hint_sym : IntegrableOn (fun x => (H x + H (x + ℓ)) ^ 2) (Icc (-A) (-ℓ)) :=
    ((hc.add (hc.comp (continuous_add_const ℓ))).pow 2).continuousOn.integrableOn_Icc
  have hint_en : IntegrableOn (fun x => (H x - H (x + ℓ)) ^ 2) (Icc (-A) (-ℓ)) :=
    ((hc.sub (hc.comp (continuous_add_const ℓ))).pow 2).continuousOn.integrableOn_Icc
  have hsos_int : (foldSym A ℓ H - foldEnergy A ℓ H) / 4 ≤
      ∫ x in Icc (-A) (-ℓ), H x ^ 2 := by
    have hmono := setIntegral_mono_on
      ((hint_sym.const_mul (1 / 8)).sub (hint_en.const_mul (1 / 4))) hint_sq
      measurableSet_Icc fun x _ => by
        simp only [Pi.sub_apply]
        have hsos : 8 * H x ^ 2 - (H x + H (x + ℓ)) ^ 2 + 2 * (H x - H (x + ℓ)) ^ 2 =
            (3 * H x - H (x + ℓ)) ^ 2 := by ring
        linarith [hsos, sq_nonneg (3 * H x - H (x + ℓ))]
    simp only [Pi.sub_apply] at hmono
    rw [integral_sub (hint_sym.const_mul (1 / 8)) (hint_en.const_mul (1 / 4)),
      integral_const_mul, integral_const_mul] at hmono
    have hsym_eq : foldSym A ℓ H = (1 / 2) * ∫ x in Icc (-A) (-ℓ), (H x + H (x + ℓ)) ^ 2 := by
      unfold foldSym; rw [integral_indicator measurableSet_Icc]
    have hen_eq : foldEnergy A ℓ H = ∫ x in Icc (-A) (-ℓ), (H x - H (x + ℓ)) ^ 2 := by
      unfold foldEnergy; rw [integral_indicator measurableSet_Icc]
    linarith
  -- Monotonicity on `[-A, -ℓ] ⊆ [-A, 0]`:
  have hint_full : IntegrableOn (fun x => frobeniusDefectFactor s (-x) * H x ^ 2) (Icc (-A) 0) := by
    have hcont_f : Continuous (fun x : ℝ => frobeniusDefectFactor s (-x) * H x ^ 2) := by
      unfold frobeniusDefectFactor; fun_prop
    exact hcont_f.continuousOn.integrableOn_Icc
  have hdom_sub : ∫ x in Icc (-A) (-ℓ), frobeniusDefectFactor s (-x) * H x ^ 2 ≤
      ∫ x in Icc (-A) 0, frobeniusDefectFactor s (-x) * H x ^ 2 := by
    have hunion : Icc (-A) 0 = Icc (-A) (-ℓ) ∪ (Icc (-A) 0 \ Icc (-A) (-ℓ)) :=
      (Set.union_sdiff_cancel hsub_Icc).symm
    conv_rhs => rw [hunion]
    rw [setIntegral_union disjoint_sdiff_self_right (measurableSet_Icc.diff measurableSet_Icc)
      (hint_full.mono_set hsub_Icc) (hint_full.mono_set Set.sdiff_subset)]
    have hrest : 0 ≤ ∫ x in Icc (-A) 0 \ Icc (-A) (-ℓ),
        frobeniusDefectFactor s (-x) * H x ^ 2 :=
      setIntegral_nonneg (measurableSet_Icc.diff measurableSet_Icc) fun x _ =>
        mul_nonneg (frobeniusDefectFactor_nonneg s (-x)) (sq_nonneg _)
    linarith
  have hlow_left : frobeniusDefectFactor s ℓ * ∫ x in Icc (-A) (-ℓ), H x ^ 2 ≤
      ∫ x in Icc (-A) (-ℓ), frobeniusDefectFactor s (-x) * H x ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hint_sq.const_mul _) (hint_full.mono_set hsub_Icc)
      measurableSet_Icc fun x hx =>
        mul_le_mul_of_nonneg_right
          (frobeniusDefectFactor_mono_nonneg s hlog_pos.le (by linarith [hx.2])) (sq_nonneg _)
  have hmult := mul_le_mul_of_nonneg_left hsos_int (frobeniusDefectFactor_nonneg s ℓ)
  linarith [show (frobeniusDefectFactor s ℓ / 4) * (foldSym A ℓ H - foldEnergy A ℓ H) =
    frobeniusDefectFactor s ℓ * ((foldSym A ℓ H - foldEnergy A ℓ H) / 4) by ring]

/-- **Sharp Fold-Symmetric Lower Bound (`A ≥ log n`, `n ≥ 2`).**
On fold-symmetric tests `H(x + log n) = H(x)` (`x ∈ [-A, -log n]`), the constant sharpens to `1/2`:
`-lewisCoIsometryDefect s (windowPeriodLift s H) ≥ ((n^δ + n^(-δ))(n^δ - n^(-δ))² / 2) * foldSym`. -/
theorem windowPeriodLift_neg_defect_ge_half_foldSym_of_symmetric {A : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hlog : Real.log n ≤ A) {H : ℝ → ℝ}
    (hc : Continuous H) (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0)
    (hsym : ∀ u ∈ Icc (-A) (-Real.log n), H (u + Real.log n) = H u) (s : ℂ) :
    (((n : ℝ) ^ (2 * s.re - 1 / 2) + (n : ℝ) ^ (-(2 * s.re - 1 / 2))) *
      ((n : ℝ) ^ (2 * s.re - 1 / 2) - (n : ℝ) ^ (-(2 * s.re - 1 / 2))) ^ 2 / 2) *
      foldSym A (Real.log n) H ≤
      -lewisCoIsometryDefect s (windowPeriodLift s H) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hn_gt1 : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)
  have hlog_pos : 0 < Real.log n := Real.log_pos hn_gt1
  have hA : 0 ≤ A := hlog_pos.le.trans hlog
  rw [windowPeriodLift_neg_defect_eq_Icc hA hc hv s, ← frobeniusDefectFactor_log_nat s hn1]
  let ℓ : ℝ := Real.log n
  have hsub_Icc : Icc (-A) (-ℓ) ⊆ Icc (-A) 0 :=
    fun x hx => ⟨hx.1, hx.2.trans (by linarith)⟩
  have hsym_eq : foldSym A ℓ H = 2 * ∫ x in Icc (-A) (-ℓ), H x ^ 2 := by
    unfold foldSym
    rw [integral_indicator measurableSet_Icc]
    have hcongr : Set.EqOn (fun u => (H u + H (u + ℓ)) ^ 2)
        (fun u => 4 * H u ^ 2) (Icc (-A) (-ℓ)) := fun u hu => by
      dsimp only [ℓ]
      rw [hsym u hu]; ring
    rw [setIntegral_congr_fun measurableSet_Icc hcongr, integral_const_mul]
    ring
  have hint_sq : IntegrableOn (fun x => H x ^ 2) (Icc (-A) (-ℓ)) :=
    (hc.pow 2).continuousOn.integrableOn_Icc
  have hint_full : IntegrableOn (fun x => frobeniusDefectFactor s (-x) * H x ^ 2) (Icc (-A) 0) := by
    have hcont_f : Continuous (fun x : ℝ => frobeniusDefectFactor s (-x) * H x ^ 2) := by
      unfold frobeniusDefectFactor; fun_prop
    exact hcont_f.continuousOn.integrableOn_Icc
  have hdom_sub : ∫ x in Icc (-A) (-ℓ), frobeniusDefectFactor s (-x) * H x ^ 2 ≤
      ∫ x in Icc (-A) 0, frobeniusDefectFactor s (-x) * H x ^ 2 := by
    have hunion : Icc (-A) 0 = Icc (-A) (-ℓ) ∪ (Icc (-A) 0 \ Icc (-A) (-ℓ)) :=
      (Set.union_sdiff_cancel hsub_Icc).symm
    conv_rhs => rw [hunion]
    rw [setIntegral_union disjoint_sdiff_self_right (measurableSet_Icc.diff measurableSet_Icc)
      (hint_full.mono_set hsub_Icc) (hint_full.mono_set Set.sdiff_subset)]
    have hrest : 0 ≤ ∫ x in Icc (-A) 0 \ Icc (-A) (-ℓ),
        frobeniusDefectFactor s (-x) * H x ^ 2 :=
      setIntegral_nonneg (measurableSet_Icc.diff measurableSet_Icc) fun x _ =>
        mul_nonneg (frobeniusDefectFactor_nonneg s (-x)) (sq_nonneg _)
    linarith
  have hlow_left : frobeniusDefectFactor s ℓ * ∫ x in Icc (-A) (-ℓ), H x ^ 2 ≤
      ∫ x in Icc (-A) (-ℓ), frobeniusDefectFactor s (-x) * H x ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hint_sq.const_mul _) (hint_full.mono_set hsub_Icc)
      measurableSet_Icc fun x hx =>
        mul_le_mul_of_nonneg_right
          (frobeniusDefectFactor_mono_nonneg s hlog_pos.le (by linarith [hx.2])) (sq_nonneg _)
  rw [hsym_eq]
  linarith [show (frobeniusDefectFactor s ℓ / 2) * (2 * ∫ x in Icc (-A) (-ℓ), H x ^ 2) =
    frobeniusDefectFactor s ℓ * ∫ x in Icc (-A) (-ℓ), H x ^ 2 by ring]

/-- **Universal First-Prime Capacity Upper Bound (`A ≥ 2 log 2`).**
Once the two ends `[-A, -log 2]` and `[log 2 - A, 0]` cover `[-A, 0]`, any bound on
`foldEnergy A (log 2) H / 2 + foldSym A (log 2) H` directly upper-bounds the Mayer defect
`-lewisCoIsometryDefect s (windowPeriodLift s H)`. -/
theorem windowPeriodLift_neg_defect_le_firstPrime_fold {A : ℝ}
    (hA2 : 2 * Real.log 2 ≤ A) {H : ℝ → ℝ}
    (hc : Continuous H) (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (s : ℂ) :
    -lewisCoIsometryDefect s (windowPeriodLift s H) ≤
      frobeniusDefectFactor s A *
        (foldEnergy A (Real.log 2) H / 2 + foldSym A (Real.log 2) H) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by linarith
  have hcs : HasCompactSupport H := HasCompactSupport.intro (isCompact_Icc (a := -A) (b := 0)) hv
  rw [windowPeriodLift_neg_defect_eq_Icc hA hc hv s]
  -- Pointwise on `[-A, 0]`, `frobeniusDefectFactor s (-x) ≤ frobeniusDefectFactor s A`:
  have hint_full : IntegrableOn (fun x => frobeniusDefectFactor s (-x) * H x ^ 2) (Icc (-A) 0) := by
    have hcont_f : Continuous (fun x : ℝ => frobeniusDefectFactor s (-x) * H x ^ 2) := by
      unfold frobeniusDefectFactor; fun_prop
    exact hcont_f.continuousOn.integrableOn_Icc
  have hint_sq_Icc : IntegrableOn (fun x => H x ^ 2) (Icc (-A) 0) :=
    (hc.pow 2).continuousOn.integrableOn_Icc
  have hup1 : ∫ x in Icc (-A) 0, frobeniusDefectFactor s (-x) * H x ^ 2 ≤
      frobeniusDefectFactor s A * ∫ x in Icc (-A) 0, H x ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hint_full (hint_sq_Icc.const_mul _) measurableSet_Icc fun x hx =>
      mul_le_mul_of_nonneg_right
        (frobeniusDefectFactor_mono_nonneg s (by linarith [hx.2]) (by linarith [hx.1]))
        (sq_nonneg _)
  -- On `[-A, 0]`, `1 ≤ inWindowCount A (Real.log 2) x` since `A ≥ 2 log 2`:
  have hcount_ge1 : ∀ x : ℝ, (Icc (-A) 0).indicator (fun x => H x ^ 2) x ≤
      inWindowCount A (Real.log 2) x * H x ^ 2 := by
    intro x
    by_cases hx : x ∈ Icc (-A) 0
    · rw [indicator_of_mem hx]
      have h1_le : 1 ≤ inWindowCount A (Real.log 2) x := by
        unfold inWindowCount
        by_cases hleft : x ≤ -Real.log 2
        · have hm1 : x ∈ Icc (-A) (-Real.log 2) := ⟨hx.1, hleft⟩
          have hnn2 : 0 ≤ (Icc (Real.log 2 - A) 0).indicator (1 : ℝ → ℝ) x :=
            indicator_nonneg (fun _ _ => zero_le_one) x
          rw [indicator_of_mem hm1]
          simp only [Pi.one_apply]
          linarith
        · rw [not_le] at hleft
          have hm2 : x ∈ Icc (Real.log 2 - A) 0 := ⟨by linarith, hx.2⟩
          have hnn1 : 0 ≤ (Icc (-A) (-Real.log 2)).indicator (1 : ℝ → ℝ) x :=
            indicator_nonneg (fun _ _ => zero_le_one) x
          rw [indicator_of_mem hm2]
          simp only [Pi.one_apply]
          linarith
      simpa only [one_mul] using mul_le_mul_of_nonneg_right h1_le (sq_nonneg (H x))
    · rw [indicator_of_notMem hx]
      exact mul_nonneg (inWindowCount_nonneg A (Real.log 2) x) (sq_nonneg _)
  have hint_count : Integrable (fun x => inWindowCount A (Real.log 2) x * H x ^ 2) := by
    have iH : Integrable (fun x => H x ^ 2) := (hc.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -A) (b := 0)) fun y hy => by simp [hv y hy])
    have m1 : MeasurableSet (Icc (-A) (-Real.log 2)) := measurableSet_Icc
    have m2 : MeasurableSet (Icc (Real.log 2 - A) 0) := measurableSet_Icc
    refine ((iH.indicator m1).add (iH.indicator m2)).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    exact (inWindowCount_mul A (Real.log 2) x (fun y => H y ^ 2)).symm
  have hsq_le_count : ∫ x in Icc (-A) 0, H x ^ 2 ≤
      ∫ x, inWindowCount A (Real.log 2) x * H x ^ 2 := by
    rw [← integral_indicator measurableSet_Icc]
    exact integral_mono ((integrable_indicator_iff measurableSet_Icc).mpr hint_sq_Icc)
      hint_count hcount_ge1
  have hcount_id : ∫ x, inWindowCount A (Real.log 2) x * H x ^ 2 =
      foldEnergy A (Real.log 2) H / 2 + foldSym A (Real.log 2) H := by
    have h := foldEnergy_sub_count_eq_anti_sub_sym hc hcs (Real.log 2) (A := A)
    linarith
  rw [hcount_id] at hsq_le_count
  exact hup1.trans (mul_le_mul_of_nonneg_left hsq_le_count (frobeniusDefectFactor_nonneg s A))

/-- **Integrated Coupled `T₂`-Stick Schur Lower Bound Across `[-A, -log 2]`.**
Integrating `WindowJumpCounts.twoVertexStick_ge_schur` against `(u₁, u₂) = (H(x + log 2), H(x))`
couples inner-origin potentials `(p₁, w₁)` (`x + log 2 ∈ [log 2 - A, 0]`) with outer-edge
potentials `(p₂, w₂)` (`x ∈ [-A, -log 2]`, allowing `p₂(x) + w₂(x) < 0`) via the exact first-prime
fold energy `g₁₂ * foldEnergy A (log 2) H`. -/
theorem integral_firstPrime_stick_ge_schur {A g₁₂ uBar : ℝ}
    {p₁ p₂ w₁ w₂ H : ℝ → ℝ}
    (hc : Continuous H)
    (hp₁ : ContinuousOn p₁ (Icc (-A) (-Real.log 2)))
    (hp₂ : ContinuousOn p₂ (Icc (-A) (-Real.log 2)))
    (hw₁ : ContinuousOn w₁ (Icc (-A) (-Real.log 2)))
    (hw₂ : ContinuousOn w₂ (Icc (-A) (-Real.log 2)))
    (hd₁ : ∀ x ∈ Icc (-A) (-Real.log 2), 0 < stickDiag1 (p₁ x) (w₁ x) g₁₂)
    (hΔ : ∀ x ∈ Icc (-A) (-Real.log 2), 0 < stickDet (p₁ x) (p₂ x) (w₁ x) (w₂ x) g₁₂) :
    (∫ x in Icc (-A) (-Real.log 2),
      stickSchurNum (p₁ x) (p₂ x) (w₁ x) (w₂ x) g₁₂ /
        stickDet (p₁ x) (p₂ x) (w₁ x) (w₂ x) g₁₂) * uBar ^ 2 ≤
      (∫ x in Icc (-A) (-Real.log 2),
        p₁ x * H (x + Real.log 2) ^ 2 + w₁ x * (H (x + Real.log 2) - uBar) ^ 2 +
          p₂ x * H x ^ 2 + w₂ x * (H x - uBar) ^ 2) +
        g₁₂ * foldEnergy A (Real.log 2) H := by
  let S : Set ℝ := Icc (-A) (-Real.log 2)
  have hc_Hsh : ContinuousOn (fun x => H (x + Real.log 2)) S :=
    (hc.comp (continuous_add_const (Real.log 2))).continuousOn
  have hc_schur : ContinuousOn
      (fun x => stickSchurNum (p₁ x) (p₂ x) (w₁ x) (w₂ x) g₁₂ /
        stickDet (p₁ x) (p₂ x) (w₁ x) (w₂ x) g₁₂) S := by
    have c_num : ContinuousOn (fun x => stickSchurNum (p₁ x) (p₂ x) (w₁ x) (w₂ x) g₁₂) S := by
      unfold stickSchurNum
      exact (((hp₁.mul hp₂).add ((hp₁.add hp₂).const_mul g₁₂)).mul (hw₁.add hw₂)).add
        (((hp₁.add hp₂).mul hw₁).mul hw₂)
    have c_det : ContinuousOn (fun x => stickDet (p₁ x) (p₂ x) (w₁ x) (w₂ x) g₁₂) S := by
      unfold stickDet stickDiag1 stickDiag2
      exact (((hp₁.add hw₁).add continuousOn_const).mul
        ((hp₂.add hw₂).add continuousOn_const)).sub continuousOn_const
    exact c_num.div c_det fun x hx => (hΔ x hx).ne'
  have hc_quad : ContinuousOn
      (fun x => p₁ x * H (x + Real.log 2) ^ 2 + w₁ x * (H (x + Real.log 2) - uBar) ^ 2 +
        p₂ x * H x ^ 2 + w₂ x * (H x - uBar) ^ 2) S :=
    (((hp₁.mul (hc_Hsh.pow 2)).add (hw₁.mul ((hc_Hsh.sub continuousOn_const).pow 2))).add
      (hp₂.mul (hc.continuousOn.pow 2))).add
      (hw₂.mul ((hc.continuousOn.sub continuousOn_const).pow 2))
  have hc_fold : ContinuousOn (fun x => (H x - H (x + Real.log 2)) ^ 2) S :=
    ((hc.continuousOn.sub hc_Hsh).pow 2)
  have i_schur : IntegrableOn
      (fun x => (stickSchurNum (p₁ x) (p₂ x) (w₁ x) (w₂ x) g₁₂ /
        stickDet (p₁ x) (p₂ x) (w₁ x) (w₂ x) g₁₂) * uBar ^ 2) S :=
    (hc_schur.integrableOn_Icc).mul_const (uBar ^ 2)
  have i_quad : IntegrableOn
      (fun x => p₁ x * H (x + Real.log 2) ^ 2 + w₁ x * (H (x + Real.log 2) - uBar) ^ 2 +
        p₂ x * H x ^ 2 + w₂ x * (H x - uBar) ^ 2) S :=
    hc_quad.integrableOn_Icc
  have i_fold : IntegrableOn (fun x => g₁₂ * (H x - H (x + Real.log 2)) ^ 2) S :=
    (hc_fold.integrableOn_Icc).const_mul g₁₂
  have hfold_eq : g₁₂ * foldEnergy A (Real.log 2) H =
      ∫ x in S, g₁₂ * (H x - H (x + Real.log 2)) ^ 2 := by
    unfold foldEnergy
    rw [integral_indicator measurableSet_Icc, integral_const_mul]
  rw [← integral_mul_const, hfold_eq, ← integral_add i_quad i_fold]
  refine setIntegral_mono_on i_schur (i_quad.add i_fold) measurableSet_Icc fun x hx => ?_
  have hpt := twoVertexStick_ge_schur (hd₁ x hx) (hΔ x hx) (H (x + Real.log 2)) (H x) uBar
  have hsub_sq : (H (x + Real.log 2) - H x) ^ 2 = (H x - H (x + Real.log 2)) ^ 2 := by ring
  linarith

#print axioms logPeriodInverse_comp_transform
#print axioms logPeriodTransform_comp_inverse
#print axioms lewisCriticalNormSq_eq_l2NormSq_logPeriodTransform
#print axioms lewisCriticalInner_eq_l2Inner_logPeriodTransform
#print axioms logPeriodTransform_modularInversion
#print axioms lewisCoIsometryDefect_eq_neg_log_integral
#print axioms lewisModularInversion_windowPeriodLift
#print axioms windowPeriodLift_coIsometryDefect_eq
#print axioms foldSym_eq_haar_periodWindowProfile
#print axioms foldEnergy_eq_haar_periodWindowProfile
#print axioms windowPeriodLift_neg_defect_ge_foldSym_sub_foldEnergy
#print axioms windowPeriodLift_neg_defect_ge_half_foldSym_of_symmetric
#print axioms windowPeriodLift_neg_defect_le_firstPrime_fold
#print axioms integral_firstPrime_stick_ge_schur

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
