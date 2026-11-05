import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Sqrt
import GaloisForLFunctions.HTGeometry.BesselOrderPolyaRealZeros
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinTwoKBesselMellinProduct

/-!
# Half-order Bessel squares and radial imaginary-order integrals

The half-real-order Schläfli value never vanishes. Its argument-weighted
squared modulus has logarithmic slope between minus two and two. A
Schläfli product identity identifies this positive square with a radial
line integral of the imaginary-order carrier.
-/

open Complex Filter Set MeasureTheory
open scoped ComplexConjugate Topology
namespace GaloisForLFunctions.CompletedArithmeticForms
open HTGeometry RHTower
noncomputable section

/-- The half-real-order Schläfli value. -/
def besselHalfOrderValue (τ x : ℝ) : ℂ :=
  modifiedBesselKOrder x (1 / 2 + (τ : ℂ) * I)

/-- The argument-weighted square of the half-real-order Schläfli value. -/
def besselHalfOrderSquare (τ x : ℝ) : ℝ :=
  x * Complex.normSq (besselHalfOrderValue τ x)

theorem besselHalfOrderValue_ne_zero {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    besselHalfOrderValue τ x ≠ 0 := by
  intro h
  have hz := re_eq_zero_of_modifiedBesselKOrder_eq_zero hx h
  norm_num at hz

theorem besselHalfOrderSquare_pos {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    0 < besselHalfOrderSquare τ x := by
  exact mul_pos hx (Complex.normSq_pos.mpr (besselHalfOrderValue_ne_zero hx τ))

/-- Order reflection turns the adjacent-order derivative into a conjugate-linear system. -/
theorem hasDerivAt_besselHalfOrderValue {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    HasDerivAt (besselHalfOrderValue τ)
      (-(1 / 2 + (τ : ℂ) * I) / x * besselHalfOrderValue τ x -
        conj (besselHalfOrderValue τ x)) x := by
  let ν : ℂ := 1 / 2 + (τ : ℂ) * I
  have hm : ν - 1 = -(conj ν) := by
    apply Complex.ext <;>
      norm_num [ν, Complex.div_re, Complex.div_im, Complex.normSq_apply]
  have href : modifiedBesselKOrder x (ν - 1) =
      conj (modifiedBesselKOrder x ν) := by
    rw [hm, modifiedBesselKOrder_neg, modifiedBesselKOrder_conj]
  have h := hasDerivAt_modifiedBesselKOrder_arg hx ν
  rw [modifiedBesselKOrder_add_one hx, href] at h
  change HasDerivAt (besselHalfOrderValue τ) _ x at h
  apply h.congr_deriv
  dsimp [besselHalfOrderValue, ν]
  ring

/-- The exact square flux has no frequency restriction. -/
theorem hasDerivAt_besselHalfOrderSquare {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    HasDerivAt (besselHalfOrderSquare τ)
      (-2 * x * ((besselHalfOrderValue τ x).re ^ 2 -
        (besselHalfOrderValue τ x).im ^ 2)) x := by
  have h := hasDerivAt_besselHalfOrderValue hx τ
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h
  have hd := (hasDerivAt_id x).mul ((hr.pow 2).add (hi.pow 2))
  unfold besselHalfOrderSquare
  simp only [Complex.normSq_apply, ← sq]
  apply hd.congr_deriv
  dsimp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Function.comp_apply, id_eq,
    Complex.reCLM_apply, Complex.imCLM_apply]
  norm_num [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.neg_re, Complex.neg_im,
    Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im,
    Complex.normSq_apply]
  field_simp [hx.ne']
  ring

/-- Multiplication by `exp(2x)` exposes a nonnegative square derivative. -/
theorem hasDerivAt_exp_mul_besselHalfOrderSquare {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    HasDerivAt (fun y => Real.exp (2 * y) * besselHalfOrderSquare τ y)
      (4 * x * Real.exp (2 * x) * (besselHalfOrderValue τ x).im ^ 2) x := by
  have he := ((hasDerivAt_id x).const_mul 2).exp
  have h := he.mul (hasDerivAt_besselHalfOrderSquare hx τ)
  apply h.congr_deriv
  simp only [besselHalfOrderSquare, Complex.normSq_apply, id_eq]
  ring

/-- The square's logarithmic slope lies between minus two and two. -/
theorem abs_deriv_besselHalfOrderSquare_le {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    |deriv (besselHalfOrderSquare τ) x| ≤ 2 * besselHalfOrderSquare τ x := by
  rw [(hasDerivAt_besselHalfOrderSquare hx τ).deriv, abs_le]
  dsimp only [besselHalfOrderSquare, Complex.normSq_apply]
  constructor <;> nlinarith only
    [mul_nonneg hx.le (sq_nonneg (besselHalfOrderValue τ x).re),
     mul_nonneg hx.le (sq_nonneg (besselHalfOrderValue τ x).im)]

/-- The exponentially rescaled square increases on the positive argument ray. -/
theorem monotoneOn_exp_mul_besselHalfOrderSquare (τ : ℝ) :
    MonotoneOn (fun x => Real.exp (2 * x) * besselHalfOrderSquare τ x) (Ioi 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
  · intro x hx
    exact (hasDerivAt_exp_mul_besselHalfOrderSquare hx τ).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_exp_mul_besselHalfOrderSquare
      (show 0 < x from interior_subset hx) τ).hasDerivWithinAt
  · intro x hx
    have hx0 : 0 ≤ x := le_of_lt (show 0 < x from interior_subset hx)
    positivity

/-- Every positive argument retains its exact exponential square reserve farther out. -/
theorem besselHalfOrderSquare_exp_lower {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (τ : ℝ) :
    Real.exp (-2 * (y - x)) * besselHalfOrderSquare τ x ≤ besselHalfOrderSquare τ y := by
  have h := monotoneOn_exp_mul_besselHalfOrderSquare τ hx (hx.trans_le hxy) hxy
  calc
    _ = Real.exp (-2 * y) * (Real.exp (2 * x) * besselHalfOrderSquare τ x) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-2 * y) * (Real.exp (2 * y) * besselHalfOrderSquare τ y) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      have he : -2 * y + 2 * y = 0 := by ring
      rw [he, Real.exp_zero, one_mul]

/-- The product of two whole-line Schläfli kernels. -/
def besselProductPlaneKernel (x : ℝ) (α β : ℂ) (z : ℝ × ℝ) : ℂ :=
  besselOrderExpKernel x α z.1 * besselOrderExpKernel x β z.2

theorem integrable_besselProductPlaneKernel {x : ℝ} (hx : 0 < x) (α β : ℂ) :
    Integrable (besselProductPlaneKernel x α β) :=
  (integrable_besselOrderExpKernel hx α).mul_prod (integrable_besselOrderExpKernel hx β)

private theorem productPlane_pairMap (x : ℝ) (α β : ℂ) (t u : ℝ) :
    besselProductPlaneKernel x α β (twoKPairMap (t,u)) =
      Complex.exp ((α + β) * (t : ℂ)) *
        besselOrderExpKernel (2 * x * Real.cosh t) (α - β) u := by
  simp only [besselProductPlaneKernel, twoKPairMap, besselOrderExpKernel,
    LinearMap.coe_mk, AddHom.coe_mk, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cosh,
    Complex.cosh_add, Complex.cosh_sub, ← Complex.exp_add]
  congr 1
  ring

private theorem integral_productPlane_pairMap_right {x : ℝ} (hx : 0 < x)
  (α β : ℂ) (t : ℝ) :
    (∫ u : ℝ, besselProductPlaneKernel x α β (twoKPairMap (t,u))) =
      2 * (Complex.exp ((α + β) * (t : ℂ)) *
        modifiedBesselKOrder (2 * x * Real.cosh t) (α - β)) := by
  simp_rw [productPlane_pairMap]
  rw [integral_const_mul, integral_besselOrderExpKernel_eq_two_mul
    (mul_pos (mul_pos (by norm_num) hx) (Real.cosh_pos t))]
  ring

theorem integrable_besselProductPlaneKernel_pairMap {x : ℝ} (hx : 0 < x) (α β : ℂ) :
    Integrable (fun z => besselProductPlaneKernel x α β (twoKPairMap z)) := by
  have hmap : Measure.map (twoKPairMap : (ℝ × ℝ) → (ℝ × ℝ)) volume =
      ENNReal.ofReal (1 / 2 : ℝ) • (volume : Measure (ℝ × ℝ)) := by
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (ℝ × ℝ)) (by rw [twoKPairMap_det]; norm_num)
    rw [twoKPairMap_det] at h
    norm_num at h ⊢
    exact h
  have hH := integrable_besselProductPlaneKernel hx α β
  have hHm : Integrable (besselProductPlaneKernel x α β)
      (Measure.map (twoKPairMap : (ℝ × ℝ) → (ℝ × ℝ)) volume) := by
    rw [hmap]
    exact hH.smul_measure (by norm_num)
  exact (integrable_map_measure hHm.aestronglyMeasurable
    twoKPairMap.continuous_of_finiteDimensional.measurable.aemeasurable).mp hHm

/-- Absolute integrability of the one-dimensional Schläfli product representation. -/
theorem integrable_exp_mul_modifiedBesselKOrder_cosh {x : ℝ} (hx : 0 < x) (α β : ℂ) :
    Integrable (fun t : ℝ => Complex.exp ((α + β) * (t : ℂ)) *
      modifiedBesselKOrder (2 * x * Real.cosh t) (α - β)) := by
  have h := (integrable_besselProductPlaneKernel_pairMap hx α β).integral_prod_left
  refine (h.const_mul (1 / 2 : ℂ)).congr (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [integral_productPlane_pairMap_right hx α β]
  ring

/-- The determinant-two Schläfli product formula on the whole real line. -/
theorem modifiedBesselKOrder_mul_eq_integral {x : ℝ} (hx : 0 < x) (α β : ℂ) :
    modifiedBesselKOrder x α * modifiedBesselKOrder x β =
      ∫ t : ℝ, Complex.exp ((α + β) * (t : ℂ)) *
        modifiedBesselKOrder (2 * x * Real.cosh t) (α - β) := by
  have hH := integrable_besselProductPlaneKernel hx α β
  have hT := integrable_besselProductPlaneKernel_pairMap hx α β
  have hprod : (∫ z : ℝ × ℝ, besselProductPlaneKernel x α β z) =
      4 * (modifiedBesselKOrder x α * modifiedBesselKOrder x β) := by
    change (∫ z : ℝ × ℝ, besselOrderExpKernel x α z.1 *
      besselOrderExpKernel x β z.2 ∂((volume : Measure ℝ).prod volume)) = _
    rw [integral_prod_mul,
      integral_besselOrderExpKernel_eq_two_mul hx,
      integral_besselOrderExpKernel_eq_two_mul hx]
    ring
  have hchange := integral_comp_linearMap_addHaar
    (volume : Measure (ℝ × ℝ)) (f := twoKPairMap)
    (by rw [twoKPairMap_det]; norm_num) hH.aestronglyMeasurable
  rw [twoKPairMap_det, hprod] at hchange
  norm_num at hchange
  change (∫ z : ℝ × ℝ, besselProductPlaneKernel x α β (twoKPairMap z)
    ∂((volume : Measure ℝ).prod volume)) = _ at hchange
  rw [integral_prod _ hT] at hchange
  simp_rw [integral_productPlane_pairMap_right hx α β] at hchange
  rw [integral_const_mul] at hchange
  linear_combination (-1 / 2 : ℂ) * hchange

/-- Hyperbolic coordinates identify a cosh-weighted line integral with a radial slice. -/
theorem integral_cosh_mul_radial_slice {x : ℝ} (hx : 0 < x) (f : ℝ → ℂ) :
    (∫ t : ℝ, (x * Real.cosh t : ℝ) • f (2 * x * Real.cosh t)) =
      ∫ w : ℝ, f (2 * Real.sqrt (x ^ 2 + w ^ 2)) := by
  let T : ℝ → ℝ := fun t => x * Real.sinh t
  have hT : Function.Bijective T := by
    constructor
    · intro t u h
      exact Real.sinh_injective (mul_left_cancel₀ hx.ne' h)
    · intro w
      obtain ⟨t, ht⟩ := Real.sinh_surjective (w / x)
      refine ⟨t, ?_⟩
      dsimp [T]
      rw [ht, mul_div_cancel₀ _ hx.ne']
  have himage : T '' (Set.univ : Set ℝ) = Set.univ :=
    Set.image_univ.trans (Set.range_eq_univ.mpr hT.2)
  have h := integral_image_eq_integral_abs_deriv_smul (s := Set.univ)
    (f := T) (f' := fun t => x * Real.cosh t) MeasurableSet.univ
    (fun t _ => ((Real.hasDerivAt_sinh t).const_mul x).hasDerivWithinAt)
    hT.1.injOn (fun w => f (2 * Real.sqrt (x ^ 2 + w ^ 2)))
  rw [himage, setIntegral_univ, setIntegral_univ] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards with t
  have he : x ^ 2 + (x * Real.sinh t) ^ 2 = (x * Real.cosh t) ^ 2 := by
    rw [mul_pow, mul_pow, Real.cosh_sq]
    ring
  rw [abs_of_pos (mul_pos hx (Real.cosh_pos t))]
  dsimp only [T]
  rw [he, Real.sqrt_sq (mul_pos hx (Real.cosh_pos t)).le]
  congr 2
  ring


/-- Symmetrizing the Schläfli product replaces the exponential weight by a cosh. -/
theorem modifiedBesselKOrder_mul_eq_coshIntegral {x : ℝ} (hx : 0 < x) (α β : ℂ) :
    modifiedBesselKOrder x α * modifiedBesselKOrder x β =
      ∫ t : ℝ, Complex.cosh ((α + β) * (t : ℂ)) *
        modifiedBesselKOrder (2 * x * Real.cosh t) (α - β) := by
  let P : ℝ → ℂ := fun t => Complex.exp ((α + β) * (t : ℂ)) *
    modifiedBesselKOrder (2 * x * Real.cosh t) (α - β)
  let Q : ℝ → ℂ := fun t => Complex.exp (-((α + β) * (t : ℂ))) *
    modifiedBesselKOrder (2 * x * Real.cosh t) (α - β)
  have hP : Integrable P := integrable_exp_mul_modifiedBesselKOrder_cosh hx α β
  have hQ : Integrable Q := by
    have h := integrable_exp_mul_modifiedBesselKOrder_cosh hx (-α) (-β)
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    dsimp only [Q]
    rw [show -α - -β = -(α - β) by ring, modifiedBesselKOrder_neg]
    congr 2
    ring
  have hplus : (∫ t, P t) = modifiedBesselKOrder x α * modifiedBesselKOrder x β :=
    (modifiedBesselKOrder_mul_eq_integral hx α β).symm
  have hminus : (∫ t, Q t) = modifiedBesselKOrder x α * modifiedBesselKOrder x β := by
    have h := modifiedBesselKOrder_mul_eq_integral hx (-α) (-β)
    rw [modifiedBesselKOrder_neg, modifiedBesselKOrder_neg] at h
    rw [h]
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [Q]
    rw [show -α - -β = -(α - β) by ring, modifiedBesselKOrder_neg]
    congr 2
    ring
  have he : (fun t : ℝ => Complex.cosh ((α + β) * (t : ℂ)) *
      modifiedBesselKOrder (2 * x * Real.cosh t) (α - β)) =
        fun t => (1 / 2 : ℂ) * (P t + Q t) := by
    funext t
    dsimp only [P, Q]
    rw [Complex.cosh]
    ring
  rw [he, integral_const_mul, integral_add hP hQ, hplus, hminus]
  ring

/-- The half-order square is a radial line integral of the imaginary-order carrier. -/
theorem besselHalfOrderSquare_eq_radial_integral {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    (besselHalfOrderSquare τ x : ℂ) =
      ∫ w : ℝ, modifiedBesselKOrder (2 * Real.sqrt (x ^ 2 + w ^ 2))
        ((2 * τ : ℝ) * I) := by
  let ν : ℂ := 1 / 2 + (τ : ℂ) * I
  have hsum : ν + conj ν = 1 := by
    apply Complex.ext <;> norm_num [ν, Complex.div_re, Complex.div_im, Complex.normSq_apply]
  have hdiff : ν - conj ν = ((2 * τ : ℝ) : ℂ) * I := by
    apply Complex.ext <;> norm_num [ν, Complex.div_re, Complex.div_im, Complex.normSq_apply]; ring
  have hp := modifiedBesselKOrder_mul_eq_coshIntegral hx ν (conj ν)
  rw [modifiedBesselKOrder_conj, Complex.mul_conj, hsum, hdiff] at hp
  simp only [one_mul, ← Complex.ofReal_cosh] at hp
  rw [besselHalfOrderSquare, Complex.ofReal_mul]
  change (x : ℂ) * (Complex.normSq (modifiedBesselKOrder x ν) : ℂ) = _
  rw [hp, ← integral_const_mul]
  calc
    _ = ∫ t : ℝ, (x * Real.cosh t : ℝ) •
        modifiedBesselKOrder (2 * x * Real.cosh t) (((2 * τ : ℝ) : ℂ) * I) := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [Complex.real_smul, Complex.ofReal_mul]
      ring
    _ = _ := integral_cosh_mul_radial_slice hx
      (fun u => modifiedBesselKOrder u (((2 * τ : ℝ) : ℂ) * I))


end
end GaloisForLFunctions.CompletedArithmeticForms
