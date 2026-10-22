import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanPointCapacity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiRayleighInfimum
import GaloisForLFunctions.RHTower.GaussianEvenCarrier
import GaloisForLFunctions.RHTower.Suzuki.SuzukiRWCHMDQuotientCoordinates

/-!
# Suzuki's screw completion is a proper dense subspace of the Weil form domain

On a smooth source `g` supported strictly inside `(−a, a)` Suzuki's screw quadratic
`⟨g', G_a g'⟩` and the restricted Weil form `W(g, g)` coincide. The two completions differ:
Suzuki's coordinate is the derivative `g' ∈ L²₀(−a, a)` with the norm `‖g'‖₂`, the restricted Weil
form domain `𝒟_W` carries the archimedean Gamma norm, of logarithmic order in frequency. The
primitive map `P : L²₀(−a, a) → 𝒟_W` is continuous, injective, with dense range, and
`W(Pφ, Pψ) = ⟨φ, G_a ψ⟩` on all of `L²₀` (`ccmRestrictedWeilForm_primitive_eq_screw`).

Dilating a source by `r ≥ 1` multiplies the derivative norm by `√r`
(`norm_sq_toDerivativeZeroMean_shrink`) and the Weil form norm by `O(√((1 + log r)/r))`
(`norm_ccmSmoothShrink_le`). Hence no bound `‖g'‖₂ ≤ C ‖g‖_W` holds on the common core
(`not_exists_derivative_norm_le_weilFormNorm`), and `P` is not onto
(`not_surjective_suzukiZeroMeanPrimitiveCCMFormCLM`): the screw completion is a proper dense
subspace of the Weil form domain and the identity of the core does not extend to an isomorphism.

The sign is nevertheless one receiver: the screw form is nonnegative on all of `L²₀(−a, a)` iff the
restricted Weil form is nonnegative on its whole form domain
(`screw_nonneg_iff_restrictedWeil_nonneg`), and then the CHMD quotient energy is nonnegative on the
closure of the common core in the signed-radical quotient
(`quotientWeilForm_nonneg_of_restrictedWeil_nonneg`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance (a : SuzukiPositiveAperture) : CompleteSpace (SuzukiApertureZeroMean a) :=
  (suzukiApertureZeroMean_isClosed a).completeSpace_coe

/-! ## The derivative norm of a source and of its dilations -/

/-- Suzuki's coordinate norm is the `L²` norm of the derivative on the line. -/
theorem norm_sq_toDerivativeZeroMean {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) :
    ‖g.toDerivativeZeroMean‖ ^ 2 = ∫ x, ‖deriv g x‖ ^ 2 := by
  have h1 : ‖g.toDerivativeZeroMean‖ =
      ‖suzukiApertureZeroExtendL2 (g.toDerivativeZeroMean : SuzukiApertureIntervalL2 a.1)‖ :=
    (norm_suzukiApertureZeroExtendL2 _).symm
  rw [h1, norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [suzukiApertureZeroExtendL2_coeFn
      (g.toDerivativeZeroMean : SuzukiApertureIntervalL2 a.1),
    suzukiApertureZeroExtend_smoothDerivativeCoordinate a g g.smooth g.hasCompactSupport
      g.tsupport_subset] with x h1 h2
  rw [h1]
  exact congrArg (‖·‖ ^ 2) h2

/-- Dilation by `r` multiplies the squared derivative norm by `r`. -/
theorem norm_sq_toDerivativeZeroMean_shrink {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) (r : ℝ) (hr : 1 ≤ r) :
    ‖(g.shrink r hr).toDerivativeZeroMean‖ ^ 2 = r * ‖g.toDerivativeZeroMean‖ ^ 2 := by
  have hr0 : 0 < r := by linarith
  rw [norm_sq_toDerivativeZeroMean, norm_sq_toDerivativeZeroMean]
  have hd : ∀ x, ‖deriv (g.shrink r hr) x‖ ^ 2 = r ^ 2 * ‖deriv g (r * x)‖ ^ 2 := fun x => by
    change ‖deriv (fun y => g (r * y)) x‖ ^ 2 = _
    rw [deriv_comp_mul_left r (g : ℝ → ℂ) x, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp_rw [hd]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun y => ‖deriv g y‖ ^ 2) r,
    abs_of_pos (inv_pos.mpr hr0), smul_eq_mul]
  field_simp

/-- A source that is nonzero somewhere has a nonzero derivative coordinate. -/
theorem norm_toDerivativeZeroMean_pos {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) {x₀ : ℝ} (hx₀ : g x₀ ≠ 0) :
    0 < ‖g.toDerivativeZeroMean‖ := by
  refine (norm_nonneg _).lt_of_ne fun h0 => hx₀ ?_
  have hcont : Continuous (deriv (g : ℝ → ℂ)) :=
    (contDiff_infty_iff_deriv.mp g.smooth).2.continuous
  have hsq : Continuous fun x => ‖deriv g x‖ ^ 2 := hcont.norm.pow 2
  have hint : ∫ x, ‖deriv g x‖ ^ 2 = 0 := by
    rw [← norm_sq_toDerivativeZeroMean, ← h0]; simp
  have hcs : HasCompactSupport fun x => ‖deriv g x‖ ^ 2 :=
    g.hasCompactSupport.deriv.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity)
    (hsq.integrable_of_hasCompactSupport hcs)).mp hint
  have hfun := (Continuous.ae_eq_iff_eq volume hsq continuous_const).mp hae
  have hd : ∀ x, deriv g x = 0 := fun x => by
    have hx : ‖deriv g x‖ ^ 2 = 0 := congrFun hfun x
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hx)
  have hconst := is_const_of_deriv_eq_zero (g.smooth.differentiable (by simp)) hd x₀ a.1
  rw [hconst]
  exact image_eq_zero_of_notMem_tsupport fun h => lt_irrefl _ (g.tsupport_subset h).2

/-! ## No comparison of the derivative norm with the Weil form norm -/

/-- **The derivative norm is not controlled by the Weil form norm.** No constant `C` gives
`‖g'‖₂ ≤ C ‖g‖_W` for all smooth strict-interior sources: the dilations of one bump violate it. -/
theorem not_exists_derivative_norm_le_weilFormNorm (a : SuzukiPositiveAperture) :
    ¬ ∃ C : ℝ, ∀ g : CCMComplexSmoothInteriorSource a,
      ‖g.toDerivativeZeroMean‖ ≤ C * ‖g.toCCMFormVector‖ := by
  rintro ⟨C, hC⟩
  set g := polarCenterBump a
  have hA := norm_toDerivativeZeroMean_pos g (x₀ := 0) (by rw [polarCenterBump_zero]; exact one_ne_zero)
  set A := ‖g.toDerivativeZeroMean‖ ^ 2 with hAdef
  have hA0 : 0 < A := by positivity
  set K := ‖ccmLogToArchimedean‖ * ‖ccmArchimedeanToLog‖ * ‖g.toCCMFormVector‖
  -- every dilation `r ≥ 1` obeys `r A ≤ (C K)²`
  have hbound : ∀ r : ℝ, (hr : 1 ≤ r) → r * A ≤ (C * K) ^ 2 := by
    intro r hr
    have hr0 : 0 < r := by linarith
    have hB : suzukiHlogScaleBound r ≤ r := by
      rw [suzukiHlogScaleBound, Real.posLog_eq_log (by rw [abs_of_pos hr0]; exact hr)]
      linarith [Real.log_le_sub_one_of_pos hr0]
    have hle := (hC (g.shrink r hr)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
    have hle' := hle.trans (mul_le_mul_of_nonneg_left (norm_ccmSmoothShrink_le g r hr)
      (abs_nonneg C))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hle' 2
    rw [norm_sq_toDerivativeZeroMean_shrink, mul_pow, mul_pow,
      Real.sq_sqrt (div_nonneg (suzukiHlogScaleBound_pos hr0).le hr0.le), sq_abs] at hsq
    have hq : suzukiHlogScaleBound r / r ≤ 1 := (div_le_one hr0).mpr hB
    have hK : 0 ≤ C ^ 2 * K ^ 2 := by positivity
    calc r * A ≤ C ^ 2 * (K ^ 2 * (suzukiHlogScaleBound r / r)) := hsq
      _ ≤ C ^ 2 * (K ^ 2 * 1) := by gcongr
      _ = (C * K) ^ 2 := by ring
  have h := hbound ((C * K) ^ 2 / A + 1) (le_add_of_nonneg_left (by positivity))
  rw [add_mul, div_mul_cancel₀ _ hA0.ne', one_mul] at h
  linarith

/-- The primitive map sends Suzuki's coordinate of a source to its Weil form vector. -/
theorem suzukiZeroMeanPrimitiveCCMFormCLM_toDerivativeZeroMean {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) :
    suzukiZeroMeanPrimitiveCCMFormCLM a g.toDerivativeZeroMean = g.toCCMFormVector := by
  rw [suzukiZeroMeanPrimitiveCCMFormCLM_apply, g.toCCMFormVector_eq_primitive]

/-- The primitive map from Suzuki's coordinate to the Weil form domain is injective. -/
theorem suzukiZeroMeanPrimitiveCCMFormCLM_injective (a : SuzukiPositiveAperture) :
    Function.Injective (suzukiZeroMeanPrimitiveCCMFormCLM a) := by
  refine (injective_iff_map_eq_zero (suzukiZeroMeanPrimitiveCCMFormCLM a)).mpr fun φ hφ => ?_
  have h1 : ccmArchimedeanFormToAperture a (suzukiZeroMeanPrimitiveCCMFormCLM a φ) = 0 := by
    rw [hφ, map_zero]
  rw [suzukiZeroMeanPrimitiveCCMFormCLM_apply,
    ccmArchimedeanFormToAperture_primitiveCCMFormVector] at h1
  have h2 : suzukiAperturePrimitiveCLM a (φ : SuzukiApertureIntervalL2 a.1) =
      suzukiAperturePrimitiveCLM a 0 := by
    rw [map_zero]; exact (suzukiApertureL2Equiv a).map_eq_zero_iff.mp h1
  exact Subtype.ext (suzukiAperturePrimitiveCLM_injective a h2)

/-- **No lower bound for the primitive map**: `‖φ‖ ≤ C ‖Pφ‖_W` fails on `L²₀(−a, a)`. -/
theorem not_exists_norm_le_primitive_norm (a : SuzukiPositiveAperture) :
    ¬ ∃ C : ℝ, ∀ φ : SuzukiApertureZeroMean a,
      ‖φ‖ ≤ C * ‖suzukiZeroMeanPrimitiveCCMFormCLM a φ‖ := by
  rintro ⟨C, hC⟩
  exact not_exists_derivative_norm_le_weilFormNorm a ⟨C, fun g => by
    simpa only [suzukiZeroMeanPrimitiveCCMFormCLM_toDerivativeZeroMean] using
      hC g.toDerivativeZeroMean⟩

/-- **The screw completion is a proper subspace of the Weil form domain**: the primitive map is
injective with dense range (`denseRange_suzukiZeroMeanPrimitiveCCMFormCLM`) but not onto. -/
theorem not_surjective_suzukiZeroMeanPrimitiveCCMFormCLM (a : SuzukiPositiveAperture) :
    ¬ Function.Surjective (suzukiZeroMeanPrimitiveCCMFormCLM a) := by
  intro hsurj
  obtain ⟨C, -, hC⟩ := (suzukiZeroMeanPrimitiveCCMFormCLM a).exists_preimage_norm_le hsurj
  refine not_exists_norm_le_primitive_norm a ⟨C, fun φ => ?_⟩
  obtain ⟨x, hx, hxn⟩ := hC (suzukiZeroMeanPrimitiveCCMFormCLM a φ)
  rwa [suzukiZeroMeanPrimitiveCCMFormCLM_injective a hx] at hxn

/-! ## One sign on the three completions -/

theorem continuous_re_ccmRestrictedWeilForm_self (a : SuzukiPositiveAperture) :
    Continuous fun q : CCMArchimedeanFormDomain a => (ccmRestrictedWeilForm a q q).re := by
  unfold ccmRestrictedWeilForm
  have hι := (ccmArchimedeanFormToAperture a).continuous
  have hB := (ccmRestrictedWeilBoundedRemainder a).continuous
  exact Complex.continuous_re.comp ((continuous_id.inner continuous_id).add
    ((hB.comp hι).inner hι))

/-- **The screw and restricted Weil receivers have the same sign**: `⟨φ, G_a φ⟩ ≥ 0` on all of
`L²₀(−a, a)` iff `W ≥ 0` on the whole Weil form domain. -/
theorem screw_nonneg_iff_restrictedWeil_nonneg (a : SuzukiPositiveAperture) :
    (∀ φ : SuzukiApertureZeroMean a, 0 ≤ (inner ℂ φ (suzukiScrewZeroMeanOperator a φ)).re) ↔
      ∀ q : CCMArchimedeanFormDomain a, 0 ≤ (ccmRestrictedWeilForm a q q).re := by
  constructor
  · intro h q
    have hclosed : IsClosed {q : CCMArchimedeanFormDomain a | 0 ≤ (ccmRestrictedWeilForm a q q).re} :=
      isClosed_le continuous_const (continuous_re_ccmRestrictedWeilForm_self a)
    have hsub : Set.range (suzukiZeroMeanPrimitiveCCMFormCLM a) ⊆
        {q | 0 ≤ (ccmRestrictedWeilForm a q q).re} := by
      rintro _ ⟨φ, rfl⟩
      change 0 ≤ (ccmRestrictedWeilForm a _ _).re
      rw [suzukiZeroMeanPrimitiveCCMFormCLM_apply, ccmRestrictedWeilForm_primitive_eq_screw]
      exact h φ
    exact hclosed.closure_subset_iff.mpr hsub (denseRange_suzukiZeroMeanPrimitiveCCMFormCLM a q)
  · intro h φ
    have := h (suzukiZeroMeanPrimitiveCCMFormCLM a φ)
    rwa [suzukiZeroMeanPrimitiveCCMFormCLM_apply, ccmRestrictedWeilForm_primitive_eq_screw] at this

/-- Restricted Weil nonnegativity makes the CHMD quotient energy nonnegative on the closure of the
common core in the signed-radical quotient. -/
theorem quotientWeilForm_nonneg_of_restrictedWeil_nonneg (a : SuzukiPositiveAperture)
    (h : ∀ q : CCMArchimedeanFormDomain a, 0 ≤ (ccmRestrictedWeilForm a q q).re) :
    ∀ x ∈ closure (Set.range (suzukiCoreSignedQuotient a)),
      0 ≤ CHMDDoobGraph.quotientWeilForm x := by
  have hclosed : IsClosed {x | 0 ≤ CHMDDoobGraph.quotientWeilForm x} :=
    isClosed_le continuous_const CHMDDoobGraph.continuous_quotientWeilForm
  refine hclosed.closure_subset_iff.mpr ?_
  rintro _ ⟨u, rfl⟩
  change 0 ≤ CHMDDoobGraph.quotientWeilForm _
  rw [suzukiCoreSignedQuotient_weil]
  exact h _

end RHTower
