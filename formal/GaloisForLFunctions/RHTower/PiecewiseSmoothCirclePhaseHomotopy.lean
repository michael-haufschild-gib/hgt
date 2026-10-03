import GaloisForLFunctions.RHTower.PiecewiseSmoothCirclePhaseWinding
import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicTraceConstancy

/-!
# `C¹` homotopies of piecewise smooth phases are trace-class homotopies

For a piecewise smooth circle function `w` the Hardy commutator obeys the Sobolev bound

`‖[P, M_w]‖²_HS = ∑_{n ≠ 0} |n| |ŵ(n)|² ≤ ∑ n² |ŵ(n)|² = ‖w'‖²_{L²} / (2π)² ≤ (sup |w'| / 2π)²`.

Consequently a family of piecewise smooth phases `u_s` converging uniformly together with its
derivatives gives unitaries `M_{u_s}` converging in operator norm with Hardy commutators
converging in Hilbert–Schmidt norm.  The cubic defects then move continuously in trace norm, both
in the one-endpoint form `(R_{u_s} - P)³` and in the relative form `(R_v - R_{u_s})³`, and on a
preconnected parameter space their traces are constant.
-/

noncomputable section

open Complex MeasureTheory ContinuousLinearMap Filter Topology Set
open scoped Real

namespace RHTower

/-! ## Multipliers depend only on the symbol function -/

theorem ccmCircleMultiplier_apply_coeFn (a : CCMCircleBoundedSymbol) (f : CCMCircleL2) :
    ((ccmCircleMultiplier a f : CCMCircleL2) : AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun z => a.toFun z * (f : AddCircle (1 : ℝ) → ℂ) z :=
  lpBoundedMulCLM_coeFn _ _ _ f

/-- `M_a = M_b - M_c` whenever `a = b - c` pointwise. -/
theorem ccmCircleMultiplier_eq_sub {a b c : CCMCircleBoundedSymbol}
    (h : ∀ z, a.toFun z = b.toFun z - c.toFun z) :
    ccmCircleMultiplier a = ccmCircleMultiplier b - ccmCircleMultiplier c := by
  ext1 f
  apply Lp.ext
  filter_upwards [ccmCircleMultiplier_apply_coeFn a f, ccmCircleMultiplier_apply_coeFn b f,
    ccmCircleMultiplier_apply_coeFn c f,
    Lp.coeFn_sub (ccmCircleMultiplier b f) (ccmCircleMultiplier c f)] with z ha hb hc hs
  rw [sub_apply, hs, Pi.sub_apply, ha, hb, hc, h, sub_mul]

/-- `‖M_a‖ ≤ B` whenever `|a| ≤ B` pointwise. -/
theorem norm_ccmCircleMultiplier_le {a : CCMCircleBoundedSymbol} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ z, ‖a.toFun z‖ ≤ B) : ‖ccmCircleMultiplier a‖ ≤ B := by
  let a' : CCMCircleBoundedSymbol :=
    { toFun := a.toFun, bound := B, bound_nonneg := hB0, measurable := a.measurable,
      norm_le := hB }
  have heq : ccmCircleMultiplier a = ccmCircleMultiplier a' := by
    ext1 f
    apply Lp.ext
    filter_upwards [ccmCircleMultiplier_apply_coeFn a f, ccmCircleMultiplier_apply_coeFn a' f]
      with z h1 h2
    rw [h1, h2]
  rw [heq]
  exact norm_lpBoundedMulCLM_le _ _ _

/-! ## The Sobolev bound for the Hardy commutator -/

namespace PiecewiseSmoothCircleFunction

variable (u : PiecewiseSmoothCircleFunction)

theorem exists_bound : ∃ C, 0 ≤ C ∧ ∀ x, ‖u.f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    u.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have h := hC (Int.fract x) ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have hp : u.f (Int.fract x) = u.f x := by
    have := u.periodic.sub_int_mul_eq (x := x) ⌊x⌋
    rw [mul_one] at this
    rw [Int.fract, this]
  rw [hp] at h
  exact h.trans (le_max_left _ _)

/-- The circle lift as a finite-energy bounded symbol. -/
def toHankelSymbol : CCMCircleHankelSymbol where
  toFun := circleLift u.f
  bound := u.exists_bound.choose
  bound_nonneg := u.exists_bound.choose_spec.1
  measurable := (continuous_circleLift u.periodic u.continuous).measurable
  norm_le z := norm_circleLift_le u.exists_bound.choose_spec.2 z
  positiveEnergy := summable_energy_along u.summable_sq_mul_norm_sq
    (g := fun n : ℕ => ((n + 1 : ℕ) : ℤ)) (fun a b h => by simpa using h)
    (fun n => by push_cast; rw [abs_of_pos (by positivity)])
  negativeEnergy := summable_energy_along u.summable_sq_mul_norm_sq
    (g := fun n : ℕ => -((n + 1 : ℕ) : ℤ)) (fun a b h => by simpa using h)
    (fun n => by push_cast; rw [abs_neg, abs_of_pos (by positivity)])

/-- Parseval for the derivative: `∑ |\hat{w'}(n)|² ≤ (sup |w'|)²`. -/
theorem tsum_norm_fourierCoeff_deriv_sq_le {B : ℝ} (hB : ∀ x, ‖u.f' x‖ ≤ B) :
    ∑' n : ℤ, ‖fourierCoeff (circleLift u.f') n‖ ^ 2 ≤ B ^ 2 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hmem : MemLp (circleLift u.f') 2 AddCircle.haarAddCircle :=
    memLp_circleLift u.measurable' hB
  have hP := hasSum_norm_inner_fourierLp_sq (hmem.toLp)
  have hcoeff : ∀ n : ℤ, inner ℂ (fourierLp (T := (1 : ℝ)) 2 n : CCMCircleL2)
      (hmem.toLp : CCMCircleL2) = fourierCoeff (circleLift u.f') n := by
    intro n
    rw [GaloisForLFunctions.inner_fourierLp_eq_fourierCoeff,
      fourierCoeff_congr_ae (MemLp.coeFn_toLp hmem)]
  rw [show (fun n : ℤ => ‖fourierCoeff (circleLift u.f') n‖ ^ 2) =
      fun n : ℤ => ‖inner ℂ (fourierLp (T := (1 : ℝ)) 2 n : CCMCircleL2)
        (hmem.toLp : CCMCircleL2)‖ ^ 2 from funext fun n => by rw [hcoeff], hP.tsum_eq]
  have hnorm : ‖(hmem.toLp : CCMCircleL2)‖ ≤ B := by
    have h := Lp.norm_le_of_ae_bound (f := (hmem.toLp : CCMCircleL2)) hB0
      (by filter_upwards [MemLp.coeFn_toLp hmem] with z hz
          rw [hz]; exact norm_circleLift_le hB z)
    have h1 : (measureUnivNNReal (AddCircle.haarAddCircle (T := (1 : ℝ))) : ℝ) = 1 := by
      simp [measureUnivNNReal]
    rwa [h1, Real.one_rpow, one_mul] at h
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- The second moment is bounded by the derivative: `∑ n² |ŵ(n)|² ≤ (sup |w'| / 2π)²`. -/
theorem tsum_sq_mul_norm_sq_le {B : ℝ} (hB : ∀ x, ‖u.f' x‖ ≤ B) :
    ∑' n : ℤ, ((n : ℝ) ^ 2) * ‖fourierCoeff (circleLift u.f) n‖ ^ 2 ≤ (B / (2 * π)) ^ 2 := by
  have hpi : 0 < (2 * π) ^ 2 := by positivity
  have hterm : ∀ n : ℤ, ((n : ℝ) ^ 2) * ‖fourierCoeff (circleLift u.f) n‖ ^ 2 =
      ‖fourierCoeff (circleLift u.f') n‖ ^ 2 / (2 * π) ^ 2 := by
    intro n
    rw [u.fourierCoeff_deriv, norm_mul, norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_I, Complex.norm_intCast, mul_one]
    field_simp
    rw [sq_abs]
    ring
  rw [tsum_congr hterm, tsum_div_const, div_pow]
  exact div_le_div_of_nonneg_right (u.tsum_norm_fourierCoeff_deriv_sq_le hB) hpi.le

/-- **Sobolev bound for the Hardy commutator**: `‖[P, M_w]‖²_HS ≤ (sup |w'| / 2π)²`. -/
theorem hsNormSq_commutator_le {B : ℝ} (hB : ∀ x, ‖u.f' x‖ ≤ B) :
    hsNormSq (ccmCircleHardyProjection *
        ccmCircleMultiplier u.toHankelSymbol.toCCMCircleBoundedSymbol -
      ccmCircleMultiplier u.toHankelSymbol.toCCMCircleBoundedSymbol *
        ccmCircleHardyProjection) ≤ (B / (2 * π)) ^ 2 := by
  rw [u.toHankelSymbol.hsNormSq_commutator]
  refine le_trans ?_ (u.tsum_sq_mul_norm_sq_le hB)
  set c : ℤ → ℂ := fourierCoeff (circleLift u.f)
  let h : ℤ → ℝ := fun n => ((n : ℝ) ^ 2) * ‖c n‖ ^ 2
  have hs : Summable h := u.summable_sq_mul_norm_sq
  have hnat : Summable fun n : ℕ => h n := hs.comp_injective Nat.cast_injective
  have hneg : Summable fun n : ℕ => h (-((n : ℤ) + 1)) :=
    hs.comp_injective (fun a b hab => by simpa using hab)
  have hA := u.toHankelSymbol.positiveEnergy
  have hBs := u.toHankelSymbol.negativeEnergy
  change Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖c ((n + 1 : ℕ) : ℤ)‖ ^ 2 at hA
  change Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖c (-((n + 1 : ℕ) : ℤ))‖ ^ 2 at hBs
  change (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖c ((n + 1 : ℕ) : ℤ)‖ ^ 2) +
      ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖c (-((n + 1 : ℕ) : ℤ))‖ ^ 2 ≤ ∑' n : ℤ, h n
  rw [tsum_of_nat_of_neg_add_one hnat hneg, hnat.tsum_eq_zero_add]
  have h0 : h ((0 : ℕ) : ℤ) = 0 := by simp [h]
  rw [h0, zero_add]
  have hle : ∀ n : ℕ, (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := fun n => by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  refine add_le_add ?_ ?_
  · refine hA.tsum_le_tsum (fun n => ?_) ((summable_nat_add_iff 1).2 hnat)
    change _ ≤ (((n + 1 : ℕ) : ℤ) : ℝ) ^ 2 * ‖c ((n + 1 : ℕ) : ℤ)‖ ^ 2
    rw [Int.cast_natCast]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hle n]) (sq_nonneg _)
  · refine hBs.tsum_le_tsum (fun n => ?_) hneg
    change _ ≤ ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2 * ‖c (-((n : ℤ) + 1))‖ ^ 2
    rw [show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, Int.cast_neg,
      Int.cast_natCast, neg_sq]
    exact mul_le_mul_of_nonneg_right (by nlinarith [hle n]) (sq_nonneg _)

/-- Difference of two piecewise smooth circle functions. -/
def sub (v : PiecewiseSmoothCircleFunction) : PiecewiseSmoothCircleFunction where
  f x := u.f x - v.f x
  f' x := u.f' x - v.f' x
  periodic x := by simp only [u.periodic x, v.periodic x]
  continuous := u.continuous.sub v.continuous
  corners := u.corners ∪ v.corners
  countable_corners := u.countable_corners.union v.countable_corners
  hasDerivAt x hx :=
    (u.hasDerivAt x (fun h => hx (Or.inl h))).sub (v.hasDerivAt x (fun h => hx (Or.inr h)))
  periodic' x := by simp only [u.periodic' x, v.periodic' x]
  measurable' := u.measurable'.sub v.measurable'
  bound := u.bound + v.bound
  norm_deriv_le x := (norm_sub_le _ _).trans (add_le_add (u.norm_deriv_le x) (v.norm_deriv_le x))

end PiecewiseSmoothCircleFunction

/-! ## Continuity of phase data -/

namespace PiecewiseSmoothCirclePhase

variable (u : PiecewiseSmoothCirclePhase)

theorem toHankelPhase_multiplier :
    u.toHankelPhase.multiplier =
      ccmCircleMultiplier u.toPiecewiseSmoothCircleFunction.toHankelSymbol.toCCMCircleBoundedSymbol := by
  ext1 f
  apply Lp.ext
  filter_upwards [u.toHankelPhase.multiplier_coeFn f, ccmCircleMultiplier_apply_coeFn
    u.toPiecewiseSmoothCircleFunction.toHankelSymbol.toCCMCircleBoundedSymbol f] with z h1 h2
  rw [h1, h2]
  rfl

theorem multiplier_sub (v : PiecewiseSmoothCirclePhase) :
    u.toHankelPhase.multiplier - v.toHankelPhase.multiplier =
      ccmCircleMultiplier (u.toPiecewiseSmoothCircleFunction.sub
        v.toPiecewiseSmoothCircleFunction).toHankelSymbol.toCCMCircleBoundedSymbol := by
  rw [toHankelPhase_multiplier, toHankelPhase_multiplier]
  symm
  refine ccmCircleMultiplier_eq_sub fun z => ?_
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  change circleLift (fun y => u.f y - v.f y) x = circleLift u.f x - circleLift v.f x
  rw [circleLift_coe (f := fun y => u.f y - v.f y)
      (fun y => by simp only [u.periodic y, v.periodic y]), circleLift_coe u.periodic,
    circleLift_coe v.periodic]

/-- Operator-norm control of the unitary by the sup-distance of the phases. -/
theorem norm_multiplier_sub_le (v : PiecewiseSmoothCirclePhase) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x, ‖u.f x - v.f x‖ ≤ ε) :
    ‖u.toHankelPhase.multiplier - v.toHankelPhase.multiplier‖ ≤ ε := by
  rw [u.multiplier_sub v]
  refine norm_ccmCircleMultiplier_le hε fun z => ?_
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  change ‖circleLift (fun y => u.f y - v.f y) x‖ ≤ ε
  rw [circleLift_coe (f := fun y => u.f y - v.f y)
      (fun y => by simp only [u.periodic y, v.periodic y])]
  exact h x

/-- Hilbert–Schmidt control of the Hardy commutator by the sup-distance of the derivatives. -/
theorem hsNorm_commutator_sub_le (v : PiecewiseSmoothCirclePhase) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x, ‖u.f' x - v.f' x‖ ≤ ε) :
    (restrictedUnitaryCommutator ccmCircleHardyProjection u.toHankelPhase.multiplier -
        restrictedUnitaryCommutator ccmCircleHardyProjection v.toHankelPhase.multiplier).hsNorm ≤
      ε / (2 * π) := by
  have heq : restrictedUnitaryCommutator ccmCircleHardyProjection u.toHankelPhase.multiplier -
      restrictedUnitaryCommutator ccmCircleHardyProjection v.toHankelPhase.multiplier =
      ccmCircleHardyProjection * (u.toHankelPhase.multiplier - v.toHankelPhase.multiplier) -
        (u.toHankelPhase.multiplier - v.toHankelPhase.multiplier) * ccmCircleHardyProjection := by
    simp only [restrictedUnitaryCommutator]
    noncomm_ring
  rw [heq, u.multiplier_sub v, ContinuousLinearMap.hsNorm]
  have hle := (u.toPiecewiseSmoothCircleFunction.sub v.toPiecewiseSmoothCircleFunction)
    |>.hsNormSq_commutator_le (B := ε) h
  have hnn : 0 ≤ ε / (2 * π) := by positivity
  calc Real.sqrt _ ≤ Real.sqrt ((ε / (2 * π)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = ε / (2 * π) := Real.sqrt_sq hnn

/-- A family of phases converging uniformly with derivatives gives operator-norm convergence of
the unitaries and Hilbert–Schmidt convergence of the Hardy commutators. -/
theorem tendsto_datum {ι : Type*} {l : Filter ι} (w : ι → PiecewiseSmoothCirclePhase)
    (hval : ∀ ε > 0, ∀ᶠ j in l, ∀ x, ‖(w j).f x - u.f x‖ ≤ ε)
    (hder : ∀ ε > 0, ∀ᶠ j in l, ∀ x, ‖(w j).f' x - u.f' x‖ ≤ ε) :
    Tendsto (fun j => ‖(w j).toHankelPhase.multiplier - u.toHankelPhase.multiplier‖) l (𝓝 0) ∧
    Tendsto (fun j =>
      (restrictedUnitaryCommutator ccmCircleHardyProjection (w j).toHankelPhase.multiplier -
        restrictedUnitaryCommutator ccmCircleHardyProjection u.toHankelPhase.multiplier).hsNorm)
      l (𝓝 0) := by
  constructor
  · refine Metric.tendsto_nhds.2 fun ε hε => ?_
    filter_upwards [hval (ε / 2) (by positivity)] with j hj
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    exact ((w j).norm_multiplier_sub_le u (by positivity) hj).trans_lt (by linarith)
  · refine Metric.tendsto_nhds.2 fun ε hε => ?_
    filter_upwards [hder (ε * π) (by positivity)] with j hj
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (ContinuousLinearMap.hsNorm_nonneg _)]
    refine ((w j).hsNorm_commutator_sub_le u (by positivity) hj).trans_lt ?_
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]

/-- **Trace-class homotopy.**  Uniform `C¹` convergence of phases gives trace-norm convergence of
the cubic defects `(R_{w_j} - P)³`. -/
theorem tendsto_traceNorm_cubicDefect {ι : Type*} {l : Filter ι}
    (w : ι → PiecewiseSmoothCirclePhase)
    (hval : ∀ ε > 0, ∀ᶠ j in l, ∀ x, ‖(w j).f x - u.f x‖ ≤ ε)
    (hder : ∀ ε > 0, ∀ᶠ j in l, ∀ x, ‖(w j).f' x - u.f' x‖ ≤ ε) :
    Tendsto (fun j => traceNorm CCMCircleL2
      (restrictedProjectionCubicDefect (w j).polarization ccmCircleHardyProjection -
        restrictedProjectionCubicDefect u.polarization ccmCircleHardyProjection)) l (𝓝 0) := by
  obtain ⟨hU, hC⟩ := u.tendsto_datum w hval hder
  exact traceNorm_restrictedUnitaryCubicDefect_tendsto ccmCircleHardyProjection_idempotent
    ccmCircleHardyProjection_adjoint (fun j => (w j).toHankelPhase.adjoint_multiplier_mul_multiplier)
    (fun j => (w j).toHankelPhase.multiplier_mul_adjoint_multiplier)
    u.toHankelPhase.adjoint_multiplier_mul_multiplier u.toHankelPhase.multiplier_mul_adjoint_multiplier
    (fun j => (w j).toHankelPhase.toHankelSymbol.commutator_isHilbertSchmidt)
    u.toHankelPhase.toHankelSymbol.commutator_isHilbertSchmidt hU hC

theorem hsNorm_neg' (T : CCMCircleL2 →L[ℂ] CCMCircleL2) : (-T).hsNorm = T.hsNorm := by
  rw [ContinuousLinearMap.hsNorm, ContinuousLinearMap.hsNorm,
    ContinuousLinearMap.hsNormSq_neg_eq_self]

/-- The polarization `R_u` is an orthogonal projection whose displacement from `R_v` is
Hilbert–Schmidt. -/
theorem polarization_displacement_isHilbertSchmidt (v : PiecewiseSmoothCirclePhase) :
    (restrictedProjectionDisplacement v.polarization u.polarization).IsHilbertSchmidt := by
  have h1 := v.toHankelPhase.datum.displacement_isHilbertSchmidt
  have h2 := u.toHankelPhase.datum.displacement_isHilbertSchmidt
  have heq : restrictedProjectionDisplacement v.polarization u.polarization =
      restrictedProjectionDisplacement v.toHankelPhase.datum.conjugateProjection
          v.toHankelPhase.datum.projection -
        restrictedProjectionDisplacement u.toHankelPhase.datum.conjugateProjection
          u.toHankelPhase.datum.projection := by
    simp only [restrictedProjectionDisplacement]
    change v.polarization - u.polarization =
      (v.polarization - ccmCircleHardyProjection) - (u.polarization - ccmCircleHardyProjection)
    abel
  rw [heq]
  exact h1.sub h2

/-- **Relative trace-class homotopy.**  For a fixed phase `v`, uniform `C¹` convergence
`w_j → u` gives trace-norm convergence `(R_v - R_{w_j})³ → (R_v - R_u)³`. -/
theorem tendsto_traceNorm_relativeCubicDefect (v : PiecewiseSmoothCirclePhase) {ι : Type*}
    {l : Filter ι} (w : ι → PiecewiseSmoothCirclePhase)
    (hval : ∀ ε > 0, ∀ᶠ j in l, ∀ x, ‖(w j).f x - u.f x‖ ≤ ε)
    (hder : ∀ ε > 0, ∀ᶠ j in l, ∀ x, ‖(w j).f' x - u.f' x‖ ≤ ε) :
    Tendsto (fun j => traceNorm CCMCircleL2
      (restrictedProjectionCubicDefect v.polarization (w j).polarization -
        restrictedProjectionCubicDefect v.polarization u.polarization)) l (𝓝 0) := by
  obtain ⟨hU, hC⟩ := u.tendsto_datum w hval hder
  refine traceNorm_restrictedProjectionCubicDefect_tendsto
    (fun _ => v.toHankelPhase.datum.conjugateProjection_idempotent)
    (fun j => (w j).toHankelPhase.datum.conjugateProjection_idempotent)
    v.toHankelPhase.datum.conjugateProjection_idempotent
    u.toHankelPhase.datum.conjugateProjection_idempotent
    (fun _ => v.toHankelPhase.datum.conjugateProjection_adjoint)
    (fun j => (w j).toHankelPhase.datum.conjugateProjection_adjoint)
    v.toHankelPhase.datum.conjugateProjection_adjoint
    u.toHankelPhase.datum.conjugateProjection_adjoint
    (fun j => (w j).polarization_displacement_isHilbertSchmidt v)
    (u.polarization_displacement_isHilbertSchmidt v) ?_
  have hbound : ∀ j, (restrictedProjectionDisplacement v.polarization (w j).polarization -
      restrictedProjectionDisplacement v.polarization u.polarization).hsNorm ≤
      ‖(w j).toHankelPhase.multiplier - u.toHankelPhase.multiplier‖ *
          (restrictedUnitaryCommutator ccmCircleHardyProjection u.toHankelPhase.multiplier).hsNorm +
        (restrictedUnitaryCommutator ccmCircleHardyProjection (w j).toHankelPhase.multiplier -
          restrictedUnitaryCommutator ccmCircleHardyProjection u.toHankelPhase.multiplier).hsNorm := by
    intro j
    have heq : restrictedProjectionDisplacement v.polarization (w j).polarization -
        restrictedProjectionDisplacement v.polarization u.polarization =
        -(restrictedProjectionDisplacement
            (restrictedUnitaryConjugateProjection ccmCircleHardyProjection
              (w j).toHankelPhase.multiplier) ccmCircleHardyProjection -
          restrictedProjectionDisplacement
            (restrictedUnitaryConjugateProjection ccmCircleHardyProjection
              u.toHankelPhase.multiplier) ccmCircleHardyProjection) := by
      simp only [restrictedProjectionDisplacement]
      change v.polarization - (w j).polarization - (v.polarization - u.polarization) =
        -(((w j).polarization - ccmCircleHardyProjection) -
          (u.polarization - ccmCircleHardyProjection))
      abel
    rw [heq, hsNorm_neg']
    exact hsNorm_restrictedUnitaryDisplacement_sub_le ccmCircleHardyProjection
      (w j).toHankelPhase.multiplier u.toHankelPhase.multiplier
      (w j).toHankelPhase.adjoint_multiplier_mul_multiplier
      u.toHankelPhase.adjoint_multiplier_mul_multiplier
      (w j).toHankelPhase.toHankelSymbol.commutator_isHilbertSchmidt
      u.toHankelPhase.toHankelSymbol.commutator_isHilbertSchmidt
  have hupper : Tendsto (fun j =>
      ‖(w j).toHankelPhase.multiplier - u.toHankelPhase.multiplier‖ *
          (restrictedUnitaryCommutator ccmCircleHardyProjection u.toHankelPhase.multiplier).hsNorm +
        (restrictedUnitaryCommutator ccmCircleHardyProjection (w j).toHankelPhase.multiplier -
          restrictedUnitaryCommutator ccmCircleHardyProjection u.toHankelPhase.multiplier).hsNorm)
      l (𝓝 0) := by
    simpa using (hU.mul_const _).add hC
  exact squeeze_zero (fun j => ContinuousLinearMap.hsNorm_nonneg _) hbound hupper

end PiecewiseSmoothCirclePhase

end RHTower
