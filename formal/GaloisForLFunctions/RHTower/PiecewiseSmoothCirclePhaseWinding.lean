import GaloisForLFunctions.RHTower.CircleHankelSeamEnergy
import GaloisForLFunctions.RHTower.CirclePhaseFourierMomentIntegral
import GaloisForLFunctions.RHTower.RestrictedProjectionCubicCocycle

/-!
# Winding number of a piecewise smooth circle phase as a cubic relative index

A *piecewise smooth circle phase* is a continuous `1`-periodic unimodular `f : ℝ → ℂ` which is
differentiable off a countable set, with a bounded measurable periodic derivative `f'`.  Every
continuous piecewise `C¹` phase (finitely many corners) is of this kind.  For such `f`:

* `\hat{f'}(n) = 2πi n \hat f(n)` (fundamental theorem of calculus off a countable set; the
  boundary term cancels by periodicity);
* Parseval for `f'` gives `∑ n² |\hat f(n)|² < ∞`, so `f` has finite half-Sobolev energy and
  `[P, M_f]` is Hilbert–Schmidt — although `∑ |n| |\hat f(n)|` may diverge at corners;
* Parseval gives `(2πi)⁻¹ ∫₀¹ f'/f = ∑_n n |\hat f(n)|²`.

Hence the winding number `wind(f) = (2πi)⁻¹ ∫₀¹ f'/f` is the cubic trace
`Tr (M_f† P M_f - P)³`, i.e. the relative index of the pair, and is an integer.  For two such
phases, `Tr (R_f - R_g)³ = wind(f) - wind(g) = wind(f ḡ)` with `R_f = M_f† P M_f`.
-/

noncomputable section

open Complex MeasureTheory intervalIntegral ContinuousLinearMap Filter Set
open scoped Real

namespace RHTower

/-! ## Circle lifts of measurable periodic functions -/

theorem measurable_circleLift {f : ℝ → ℂ} (hf : Measurable f) : Measurable (circleLift f) :=
  hf.comp (measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable)

theorem norm_circleLift_le {f : ℝ → ℂ} {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C)
    (z : AddCircle (1 : ℝ)) : ‖circleLift f z‖ ≤ C :=
  h _

theorem memLp_circleLift {f : ℝ → ℂ} (hf : Measurable f) {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C) :
    MemLp (circleLift f) 2 AddCircle.haarAddCircle :=
  MemLp.of_bound (measurable_circleLift hf).aestronglyMeasurable C
    (Eventually.of_forall (norm_circleLift_le h))

private theorem haarAddCircle_one_eq_volume' :
    (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

/-- **Parseval** for a continuous periodic `f` and a periodic `g` with square-integrable lift:
`∫₀¹ \bar f g = ∑_n \overline{\hat f(n)} \hat g(n)`. -/
theorem tsum_conj_fourierCoeff_mul_fourierCoeff_of_memLp {f g : ℝ → ℂ}
    (hf : Function.Periodic f 1) (hfc : Continuous f)
    (hg : Function.Periodic g 1) (hgL : MemLp (circleLift g) 2 AddCircle.haarAddCircle) :
    ∑' n : ℤ, starRingEnd ℂ (fourierCoeff (circleLift f) n) * fourierCoeff (circleLift g) n =
      ∫ x in (0 : ℝ)..1, starRingEnd ℂ (f x) * g x := by
  let G : CCMCircleL2 := hgL.toLp
  have hGc : ((G : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      circleLift g := MemLp.coeFn_toLp hgL
  have hP := (fourierBasis (T := (1 : ℝ))).tsum_inner_mul_inner (circleLiftLp hf hfc) G
  have hrepr : ∀ (v : CCMCircleL2) (n : ℤ),
      inner ℂ ((fourierBasis (T := (1 : ℝ))) n) v =
        fourierCoeff ((v : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) n := by
    intro v n
    rw [← (fourierBasis (T := (1 : ℝ))).repr_apply_apply, fourierBasis_repr]
  have hterm : ∀ n : ℤ,
      inner ℂ (circleLiftLp hf hfc) ((fourierBasis (T := (1 : ℝ))) n) *
          inner ℂ ((fourierBasis (T := (1 : ℝ))) n) G =
        starRingEnd ℂ (fourierCoeff (circleLift f) n) * fourierCoeff (circleLift g) n := by
    intro n
    rw [← inner_conj_symm, hrepr, hrepr, fourierCoeff_circleLiftLp, fourierCoeff_congr_ae hGc]
  simp_rw [hterm] at hP
  rw [hP, MeasureTheory.L2.inner_def]
  have hae : (fun z => inner ℂ (((circleLiftLp hf hfc : CCMCircleL2) :
        AddCircle (1 : ℝ) → ℂ) z) ((G : AddCircle (1 : ℝ) → ℂ) z)) =ᵐ[AddCircle.haarAddCircle]
      fun z => starRingEnd ℂ (circleLift f z) * circleLift g z := by
    filter_upwards [circleLiftLp_coeFn hf hfc, hGc] with z h1 h2
    rw [h1, h2, RCLike.inner_apply', mul_comm]
  rw [integral_congr_ae hae, haarAddCircle_one_eq_volume']
  have hpre := AddCircle.intervalIntegral_preimage (1 : ℝ) 0
    (fun z => starRingEnd ℂ (circleLift f z) * circleLift g z)
  rw [zero_add] at hpre
  rw [← hpre]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [circleLift_coe hf, circleLift_coe hg]

/-! ## Piecewise smooth circle functions -/

/-- A continuous `1`-periodic function, differentiable off a countable set of corners, with a
bounded measurable periodic derivative. -/
structure PiecewiseSmoothCircleFunction where
  f : ℝ → ℂ
  f' : ℝ → ℂ
  periodic : Function.Periodic f 1
  continuous : Continuous f
  corners : Set ℝ
  countable_corners : corners.Countable
  hasDerivAt : ∀ x ∉ corners, HasDerivAt f (f' x) x
  periodic' : Function.Periodic f' 1
  measurable' : Measurable f'
  bound : ℝ
  norm_deriv_le : ∀ x, ‖f' x‖ ≤ bound

namespace PiecewiseSmoothCircleFunction

variable (u : PiecewiseSmoothCircleFunction)

theorem intervalIntegrable_mul_deriv {g : ℝ → ℂ} (hg : Continuous g) (a b : ℝ) :
    IntervalIntegrable (fun x => g x * u.f' x) volume a b := by
  rcases le_total a b with hab | hab
  · obtain ⟨M, hM⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      hg.continuousOn
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 ?_
    refine Measure.integrableOn_of_bounded (M := M * u.bound) (by simp)
      (hg.measurable.mul u.measurable').aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [norm_mul]
    exact mul_le_mul (hM x hx) (u.norm_deriv_le x) (norm_nonneg _)
      ((norm_nonneg _).trans (hM x hx))
  · obtain ⟨M, hM⟩ := (isCompact_Icc (a := b) (b := a)).exists_bound_of_continuousOn
      hg.continuousOn
    refine ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 ?_).symm
    refine Measure.integrableOn_of_bounded (M := M * u.bound) (by simp)
      (hg.measurable.mul u.measurable').aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [norm_mul]
    exact mul_le_mul (hM x hx) (u.norm_deriv_le x) (norm_nonneg _)
      ((norm_nonneg _).trans (hM x hx))

/-- **Fourier coefficients of the derivative**: `\hat{f'}(n) = 2πi n \hat f(n)`. -/
theorem fourierCoeff_deriv (n : ℤ) :
    fourierCoeff (circleLift u.f') n = 2 * π * I * n * fourierCoeff (circleLift u.f) n := by
  rw [fourierCoeff_circleLift, fourierCoeff_circleLift]
  let e : ℝ → ℂ := fun y => fourier (-n) (y : AddCircle (1 : ℝ))
  have he : Continuous e := (fourier (-n)).continuous.comp (AddCircle.continuous_mk' 1)
  let c : ℂ := 2 * π * I * ((-n : ℤ) : ℂ) / ((1 : ℝ) : ℂ)
  have hderiv : ∀ x ∉ u.corners, HasDerivAt (fun y => e y * u.f y)
      (c * e x * u.f x + e x * u.f' x) x :=
    fun x hx => (hasDerivAt_fourier 1 (-n) x).mul (u.hasDerivAt x hx)
  have hint1 : IntervalIntegrable (fun x => c * e x * u.f x) volume 0 1 :=
    ((continuous_const.mul he).mul u.continuous).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun x => e x * u.f' x) volume 0 1 :=
    u.intervalIntegrable_mul_deriv he 0 1
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le (fun y => e y * u.f y)
    (fun x => c * e x * u.f x + e x * u.f' x) zero_le_one u.countable_corners
    (he.mul u.continuous).continuousOn (fun x hx => hderiv x hx.2) (hint1.add hint2)
  have hbd : e 1 * u.f 1 - e 0 * u.f 0 = 0 := by
    have h1 : ((1 : ℝ) : AddCircle (1 : ℝ)) = ((0 : ℝ) : AddCircle (1 : ℝ)) := by
      rw [AddCircle.coe_period, AddCircle.coe_zero]
    have hf1 : u.f 1 = u.f 0 := by simpa using u.periodic 0
    simp only [e, h1, hf1, sub_self]
  rw [hbd, intervalIntegral.integral_add hint1 hint2] at hFTC
  have hsplit : ∫ x in (0 : ℝ)..1, c * e x * u.f x = c * ∫ x in (0 : ℝ)..1, e x * u.f x := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [hsplit] at hFTC
  change ∫ x in (0 : ℝ)..1, e x * u.f' x = 2 * π * I * n * ∫ x in (0 : ℝ)..1, e x * u.f x
  have hc : c = -(2 * π * I * n) := by
    simp only [c, Int.cast_neg, ofReal_one, div_one]
    ring
  rw [hc] at hFTC
  linear_combination hFTC

theorem memLp_circleLift_deriv :
    MemLp (circleLift u.f') 2 AddCircle.haarAddCircle :=
  memLp_circleLift u.measurable' u.norm_deriv_le

/-- The second moment `∑ n² |\hat f(n)|²` is finite. -/
theorem summable_sq_mul_norm_sq :
    Summable fun n : ℤ => ((n : ℝ) ^ 2) * ‖fourierCoeff (circleLift u.f) n‖ ^ 2 := by
  have hP := hasSum_norm_inner_fourierLp_sq (u.memLp_circleLift_deriv.toLp)
  have hcoeff : ∀ n : ℤ, inner ℂ (fourierLp (T := (1 : ℝ)) 2 n : CCMCircleL2)
      (u.memLp_circleLift_deriv.toLp : CCMCircleL2) = fourierCoeff (circleLift u.f') n := by
    intro n
    rw [GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff,
      fourierCoeff_congr_ae (MemLp.coeFn_toLp u.memLp_circleLift_deriv)]
  have hs : Summable fun n : ℤ => ‖fourierCoeff (circleLift u.f') n‖ ^ 2 :=
    hP.summable.congr fun n => by rw [hcoeff]
  have hpi : 0 < (2 * π) ^ 2 := by positivity
  refine (hs.div_const ((2 * π) ^ 2)).congr fun n => ?_
  rw [u.fourierCoeff_deriv, norm_mul, norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_I, Complex.norm_intCast, mul_one]
  field_simp
  rw [sq_abs]
  ring

end PiecewiseSmoothCircleFunction

/-- Half-Sobolev energies along an injective reindexing are dominated by the second moment. -/
theorem summable_energy_along {c : ℤ → ℂ}
    (h : Summable fun n : ℤ => ((n : ℝ) ^ 2) * ‖c n‖ ^ 2) {g : ℕ → ℤ}
    (hg : Function.Injective g) (habs : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) = |(g n : ℝ)|) :
    Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖c (g n)‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h.comp_injective hg)
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  change ((n + 1 : ℕ) : ℝ) * ‖c (g n)‖ ^ 2 ≤ ((g n : ℤ) : ℝ) ^ 2 * ‖c (g n)‖ ^ 2
  rw [← sq_abs ((g n : ℤ) : ℝ), ← habs n]
  exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)

/-! ## Piecewise smooth phases -/

/-- A piecewise smooth circle function of modulus one. -/
structure PiecewiseSmoothCirclePhase extends PiecewiseSmoothCircleFunction where
  norm_eq_one : ∀ x, ‖f x‖ = 1

namespace PiecewiseSmoothCirclePhase

variable (u : PiecewiseSmoothCirclePhase)

theorem norm_circleLift (z : AddCircle (1 : ℝ)) : ‖circleLift u.f z‖ = 1 :=
  u.norm_eq_one _

/-- The phase as a finite-energy circle phase. -/
def toHankelPhase : HankelCirclePhase where
  toFun := circleLift u.f
  measurable := (continuous_circleLift u.periodic u.continuous).measurable
  norm_eq_one := u.norm_circleLift
  positiveEnergy := summable_energy_along u.summable_sq_mul_norm_sq
    (g := fun n : ℕ => ((n + 1 : ℕ) : ℤ)) (fun a b h => by simpa using h)
    (fun n => by push_cast; rw [abs_of_pos (by positivity)])
  negativeEnergy := summable_energy_along u.summable_sq_mul_norm_sq
    (g := fun n : ℕ => -((n + 1 : ℕ) : ℤ)) (fun a b h => by simpa using h)
    (fun n => by push_cast; rw [abs_neg, abs_of_pos (by positivity)])

/-- The winding number `(2πi)⁻¹ ∫₀¹ f'/f`. -/
def windingNumber : ℂ :=
  (2 * π * I)⁻¹ * ∫ x in (0 : ℝ)..1, u.f' x / u.f x

theorem div_eq_conj_mul (x : ℝ) : u.f' x / u.f x = starRingEnd ℂ (u.f x) * u.f' x := by
  have hne : u.f x ≠ 0 := by
    intro h; have := u.norm_eq_one x; rw [h, norm_zero] at this; exact zero_ne_one this
  have hconj : starRingEnd ℂ (u.f x) * u.f x = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, u.norm_eq_one]; norm_num
  rw [div_eq_iff hne]
  linear_combination (-(u.f' x)) * hconj

/-- **Winding integral in Fourier form**: `∫₀¹ f'/f = 2πi ∑_n n |\hat f(n)|²`. -/
theorem integral_div_eq_tsum :
    ∫ x in (0 : ℝ)..1, u.f' x / u.f x =
      2 * π * I * ((∑' n : ℤ, (n : ℝ) * ‖fourierCoeff (circleLift u.f) n‖ ^ 2 : ℝ) : ℂ) := by
  simp_rw [u.div_eq_conj_mul]
  rw [← tsum_conj_fourierCoeff_mul_fourierCoeff_of_memLp u.periodic u.continuous u.periodic'
    u.memLp_circleLift_deriv, ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [u.fourierCoeff_deriv n]
  have h : ((‖fourierCoeff (circleLift u.f) n‖ : ℂ)) ^ 2 =
      starRingEnd ℂ (fourierCoeff (circleLift u.f) n) * fourierCoeff (circleLift u.f) n := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  push_cast
  rw [h]
  ring

/-- The two-sided first moment splits into the positive and negative half-Sobolev energies. -/
theorem tsum_moment_eq_windingMoment :
    (∑' n : ℤ, (n : ℝ) * ‖fourierCoeff (circleLift u.f) n‖ ^ 2) =
      u.toHankelPhase.windingMoment := by
  set c : ℤ → ℂ := fourierCoeff (circleLift u.f) with hc
  let h : ℤ → ℝ := fun n => (n : ℝ) * ‖c n‖ ^ 2
  let A : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) * ‖c ((n + 1 : ℕ) : ℤ)‖ ^ 2
  let B : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) * ‖c (-((n + 1 : ℕ) : ℤ))‖ ^ 2
  have hA : Summable A := summable_energy_along u.summable_sq_mul_norm_sq
    (g := fun n : ℕ => ((n + 1 : ℕ) : ℤ)) (fun a b h => by simpa using h)
    (fun n => by push_cast; rw [abs_of_pos (by positivity)])
  have hB : Summable B := summable_energy_along u.summable_sq_mul_norm_sq
    (g := fun n : ℕ => -((n + 1 : ℕ) : ℤ)) (fun a b h => by simpa using h)
    (fun n => by push_cast; rw [abs_neg, abs_of_pos (by positivity)])
  have hAh : ∀ n : ℕ, h ((n + 1 : ℕ) : ℤ) = A n := fun n => by
    simp only [h, A, Int.cast_natCast]
  have hBh : ∀ n : ℕ, h (-((n : ℤ) + 1)) = -B n := fun n => by
    simp only [h, B]
    rw [show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by push_cast; ring]
    rw [Int.cast_neg, Int.cast_natCast]
    ring
  have hnat : Summable fun n : ℕ => h n :=
    (summable_nat_add_iff 1).1 (hA.congr fun n => (hAh n).symm)
  have hneg : Summable fun n : ℕ => h (-((n : ℤ) + 1)) :=
    hB.neg.congr fun n => (hBh n).symm
  change ∑' n : ℤ, h n = (∑' n : ℕ, A n) - ∑' n : ℕ, B n
  rw [tsum_of_nat_of_neg_add_one hnat hneg, hnat.tsum_eq_zero_add]
  have h0 : h ((0 : ℕ) : ℤ) = 0 := by simp [h]
  rw [h0, zero_add, tsum_congr hAh, tsum_congr hBh, tsum_neg]
  ring

/-- The winding number is the signed first moment of the phase. -/
theorem windingNumber_eq_windingMoment :
    u.windingNumber = (u.toHankelPhase.windingMoment : ℂ) := by
  rw [windingNumber, u.integral_div_eq_tsum, u.tsum_moment_eq_windingMoment]
  have hne : (2 * π * I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    simp [this, I_ne_zero]
  field_simp

/-- **Winding number = cubic trace.**  `Tr (M_f† P M_f - P)³ = (2πi)⁻¹ ∫₀¹ f'/f`. -/
theorem opTrace_cubicDefect :
    opTrace (restrictedProjectionCubicDefect u.toHankelPhase.datum.conjugateProjection
      u.toHankelPhase.datum.projection) = u.windingNumber := by
  rw [u.toHankelPhase.opTrace_cubicDefect, u.windingNumber_eq_windingMoment]

/-- The relative index of `(M_f† P M_f, P)` is the winding number. -/
theorem relativeIndex_eq_windingNumber :
    ((restrictedProjectionRelativeIndex u.toHankelPhase.datum.conjugateProjection
      u.toHankelPhase.datum.projection : ℤ) : ℂ) = u.windingNumber := by
  rw [← u.opTrace_cubicDefect, u.toHankelPhase.datum.opTrace_cubicDefect_eq_relativeIndex]

/-- The winding number of a piecewise smooth phase is an integer. -/
theorem windingNumber_eq_intCast : ∃ m : ℤ, u.windingNumber = m :=
  ⟨_, u.relativeIndex_eq_windingNumber.symm⟩

/-! ## Relative pairs of phases -/

/-- The polarization `R_f = M_f† P M_f`. -/
abbrev polarization : CCMCircleL2 →L[ℂ] CCMCircleL2 := u.toHankelPhase.datum.conjugateProjection

/-- **Relative cubic trace of two phases**: `Tr (R_f - R_g)³ = wind(f) - wind(g)`. -/
theorem opTrace_relativeCubicDefect (v : PiecewiseSmoothCirclePhase) :
    opTrace (restrictedProjectionCubicDefect u.polarization v.polarization) =
      u.windingNumber - v.windingNumber := by
  have hcoc := opTrace_restrictedProjectionCubicDefect_cocycle u.polarization
    ccmCircleHardyProjection v.polarization u.toHankelPhase.datum.conjugateProjection_idempotent
    ccmCircleHardyProjection_idempotent v.toHankelPhase.datum.conjugateProjection_idempotent
    u.toHankelPhase.datum.displacement_isHilbertSchmidt
    (by
      have h := v.toHankelPhase.datum.displacement_isHilbertSchmidt.neg
      have heq : restrictedProjectionDisplacement ccmCircleHardyProjection v.polarization =
          -restrictedProjectionDisplacement v.toHankelPhase.datum.conjugateProjection
            v.toHankelPhase.datum.projection := by
        simp only [restrictedProjectionDisplacement]
        change ccmCircleHardyProjection - v.polarization = -(v.polarization - ccmCircleHardyProjection)
        abel
      rw [heq]; exact h)
  rw [hcoc, restrictedProjectionCubicDefect_swap v.polarization ccmCircleHardyProjection,
    opTrace_neg]
  have hu := u.opTrace_cubicDefect
  have hv := v.opTrace_cubicDefect
  change opTrace (restrictedProjectionCubicDefect u.polarization ccmCircleHardyProjection) = _
    at hu
  change opTrace (restrictedProjectionCubicDefect v.polarization ccmCircleHardyProjection) = _
    at hv
  rw [hu, hv]
  ring

theorem conj_mul_self (x : ℝ) : starRingEnd ℂ (u.f x) * u.f x = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, u.norm_eq_one]; norm_num

theorem ne_zero (x : ℝ) : u.f x ≠ 0 := by
  intro h; have := u.norm_eq_one x; rw [h, norm_zero] at this; exact zero_ne_one this

/-- Off the corners the derivative is tangent: `f' ar f + f \overline{f'} = 0`. -/
theorem deriv_mul_conj_add (x : ℝ) (hx : x ∉ u.corners) :
    u.f' x * starRingEnd ℂ (u.f x) + u.f x * starRingEnd ℂ (u.f' x) = 0 := by
  have hd : HasDerivAt (fun y => u.f y * starRingEnd ℂ (u.f y))
      (u.f' x * starRingEnd ℂ (u.f x) + u.f x * starRingEnd ℂ (u.f' x)) x :=
    (u.hasDerivAt x hx).mul (u.hasDerivAt x hx).star
  have hconst : (fun y => u.f y * starRingEnd ℂ (u.f y)) = fun _ => (1 : ℂ) := by
    funext y; rw [mul_comm]; exact u.conj_mul_self y
  rw [hconst] at hd
  exact hd.unique (hasDerivAt_const x 1)

/-- The relative phase `f ar g` of two piecewise smooth phases. -/
def mulConj (v : PiecewiseSmoothCirclePhase) : PiecewiseSmoothCirclePhase where
  f x := u.f x * starRingEnd ℂ (v.f x)
  f' x := u.f' x * starRingEnd ℂ (v.f x) + u.f x * starRingEnd ℂ (v.f' x)
  periodic x := by simp only [u.periodic x, v.periodic x]
  continuous := u.continuous.mul (Complex.continuous_conj.comp v.continuous)
  norm_eq_one x := by rw [norm_mul, Complex.norm_conj, u.norm_eq_one, v.norm_eq_one, one_mul]
  corners := u.corners ∪ v.corners
  countable_corners := u.countable_corners.union v.countable_corners
  hasDerivAt x hx :=
    (u.hasDerivAt x (fun h => hx (Or.inl h))).mul (v.hasDerivAt x (fun h => hx (Or.inr h))).star
  periodic' x := by simp only [u.periodic x, v.periodic x, u.periodic' x, v.periodic' x]
  measurable' := (u.measurable'.mul (Complex.continuous_conj.measurable.comp
      v.continuous.measurable)).add
    (u.continuous.measurable.mul (Complex.continuous_conj.measurable.comp v.measurable'))
  bound := u.bound + v.bound
  norm_deriv_le x := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, u.norm_eq_one, v.norm_eq_one,
      mul_one, one_mul]
    exact add_le_add (u.norm_deriv_le x) (v.norm_deriv_le x)

theorem intervalIntegrable_div : IntervalIntegrable (fun x => u.f' x / u.f x) volume 0 1 := by
  have h := u.intervalIntegrable_mul_deriv (Complex.continuous_conj.comp u.continuous) 0 1
  exact h.congr fun x _ => (u.div_eq_conj_mul x).symm

/-- **Additivity of winding**: `wind(f ar g) = wind(f) - wind(g)`. -/
theorem windingNumber_mulConj (v : PiecewiseSmoothCirclePhase) :
    (u.mulConj v).windingNumber = u.windingNumber - v.windingNumber := by
  have hae : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      (u.mulConj v).f' x / (u.mulConj v).f x = u.f' x / u.f x - v.f' x / v.f x := by
    have hnull : volume (u.corners ∪ v.corners) = 0 :=
      (u.countable_corners.union v.countable_corners).measure_zero volume
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx _
    have hu : x ∉ u.corners := fun h => hx (Or.inl h)
    have hv : x ∉ v.corners := fun h => hx (Or.inr h)
    have htan := v.deriv_mul_conj_add x hv
    have hcv := v.conj_mul_self x
    have hun := u.ne_zero x
    have hvn := v.ne_zero x
    have hvinv : starRingEnd ℂ (v.f x) = (v.f x)⁻¹ := eq_inv_of_mul_eq_one_left hcv
    rw [hvinv] at htan
    have h1 : v.f x * starRingEnd ℂ (v.f' x) = -(v.f' x * (v.f x)⁻¹) := by
      linear_combination htan
    have key : starRingEnd ℂ (v.f' x) = -(v.f' x * (v.f x)⁻¹) * (v.f x)⁻¹ := by
      rw [← h1, mul_comm (v.f x), mul_assoc, mul_inv_cancel₀ hvn, mul_one]
    change (u.f' x * starRingEnd ℂ (v.f x) + u.f x * starRingEnd ℂ (v.f' x)) /
      (u.f x * starRingEnd ℂ (v.f x)) = _
    rw [hvinv, key]
    field_simp
    ring
  rw [windingNumber, windingNumber, windingNumber, intervalIntegral.integral_congr_ae hae,
    intervalIntegral.integral_sub u.intervalIntegrable_div v.intervalIntegrable_div]
  ring

/-- **Relative cubic trace of two phases is the winding of the relative phase.** -/
theorem opTrace_relativeCubicDefect_eq_mulConj (v : PiecewiseSmoothCirclePhase) :
    opTrace (restrictedProjectionCubicDefect u.polarization v.polarization) =
      (u.mulConj v).windingNumber := by
  rw [u.opTrace_relativeCubicDefect v, u.windingNumber_mulConj v]

end PiecewiseSmoothCirclePhase

end RHTower
