import GaloisForLFunctions.RHTower.BurnolSoninEvenCosineAperture

/-!
# The constant-head class is closed

The class of `L²(ℝ)` vectors that are almost everywhere constant on the aperture head `(0,a)` is
the kernel of one bounded operator: the head cutoff minus the rank-one projection onto the head
indicator.  Hence it is closed, and Burnol's extended Sonine space `L_a` — the intersection of the
constant-head class with its cosine preimage — is a closed subspace of the even carrier, so it is
itself a Hilbert space.

Completeness is what makes the continuous Gamma-completed evaluation vector `k_{w,a}` available:
the aperture estimate says the completed Mellin evaluation is a bounded functional on `L_a`, and on
a complete inner product space a bounded functional has a Riesz representative.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The `L²` indicator of the aperture head. -/
def soninHeadIndicator (a : ℝ) : SoninL2 :=
  indicatorConstLp 2 (measurableSet_Ioo (a := (0 : ℝ)) (b := a))
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (1 : ℂ)

theorem coeFn_soninHeadIndicator (a : ℝ) :
    (soninHeadIndicator a : ℝ → ℂ) =ᵐ[volume]
      (Ioo (0 : ℝ) a).indicator fun _ => (1 : ℂ) :=
  indicatorConstLp_coeFn

/-- The head pairing computes the head integral. -/
theorem inner_soninHeadIndicator (a : ℝ) (f : SoninL2) :
    inner ℂ (soninHeadIndicator a) f = ∫ x in Ioo (0 : ℝ) a, f x := by
  rw [MeasureTheory.L2.inner_def, ← integral_indicator measurableSet_Ioo]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_soninHeadIndicator a] with x hx
  rw [hx, RCLike.inner_apply]
  by_cases hmem : x ∈ Ioo (0 : ℝ) a
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    simp
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
    simp

/-- The bounded operator whose kernel is the constant-head class: the head cutoff minus the
rank-one projection onto the head indicator. -/
def soninHeadDefect (a : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (Ioo (0 : ℝ) a) measurableSet_Ioo -
    (innerSL ℂ (soninHeadIndicator a)).smulRight
      (((a : ℂ)⁻¹) • soninHeadIndicator a)

theorem coeFn_soninHeadDefect (a : ℝ) (f : SoninL2) :
    (soninHeadDefect a f : ℝ → ℂ) =ᵐ[volume]
      fun x => (Ioo (0 : ℝ) a).indicator (fun y => f y) x -
        (inner ℂ (soninHeadIndicator a) f * (a : ℂ)⁻¹) *
          (Ioo (0 : ℝ) a).indicator (fun _ => (1 : ℂ)) x := by
  have hsub := Lp.coeFn_sub (indicatorCutoff (Ioo (0 : ℝ) a) measurableSet_Ioo f)
    ((inner ℂ (soninHeadIndicator a) f) • (((a : ℂ)⁻¹) • soninHeadIndicator a))
  have hcut := indicatorCutoff_ae (Ioo (0 : ℝ) a) measurableSet_Ioo f
  have hsm1 := Lp.coeFn_smul (inner ℂ (soninHeadIndicator a) f)
    ((((a : ℂ)⁻¹) • soninHeadIndicator a))
  have hsm2 := Lp.coeFn_smul ((a : ℂ)⁻¹) (soninHeadIndicator a)
  filter_upwards [hsub, hcut, hsm1, hsm2, coeFn_soninHeadIndicator a]
    with x h1 h2 h3 h4 h5
  have hdef : (soninHeadDefect a f : ℝ → ℂ) x =
      (indicatorCutoff (Ioo (0 : ℝ) a) measurableSet_Ioo f -
        (inner ℂ (soninHeadIndicator a) f) •
          (((a : ℂ)⁻¹) • soninHeadIndicator a) : SoninL2) x := rfl
  rw [hdef, h1, Pi.sub_apply, h2, h3, Pi.smul_apply, h4, Pi.smul_apply, h5,
    smul_eq_mul, smul_eq_mul]
  ring

/-- **The constant-head class is a kernel.** -/
theorem soninHeadDefect_eq_zero_iff {a : ℝ} (ha : 0 < a) (f : SoninL2) :
    soninHeadDefect a f = 0 ↔ SoninHeadConstant a (f : ℝ → ℂ) := by
  constructor
  · intro hzero
    refine ⟨inner ℂ (soninHeadIndicator a) f * (a : ℂ)⁻¹, ?_⟩
    have hae : (soninHeadDefect a f : ℝ → ℂ) =ᵐ[volume] 0 := by
      rw [hzero]
      exact Lp.coeFn_zero ℂ 2 volume
    have hcomb := (coeFn_soninHeadDefect a f).symm.trans hae
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hcomb] with x hx
    intro hmem
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem] at hx
    simpa using sub_eq_zero.mp (by simpa using hx)
  · rintro ⟨c, hc⟩
    have hpair : inner ℂ (soninHeadIndicator a) f = c * (a : ℂ) := by
      rw [inner_soninHeadIndicator]
      rw [setIntegral_congr_ae measurableSet_Ioo
        (by filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hc] with x hx
            intro hmem
            exact hx hmem),
        setIntegral_const]
      have hvol : (volume : Measure ℝ).real (Ioo (0 : ℝ) a) = a := by
        simp [ha.le]
      rw [hvol, Complex.real_smul]
      ring
    refine Lp.ext ?_
    filter_upwards [coeFn_soninHeadDefect a f, Lp.coeFn_zero ℂ 2 volume,
      (ae_restrict_iff' measurableSet_Ioo).mp hc] with x h1 h2 h3
    rw [h1, h2, Pi.zero_apply, hpair]
    by_cases hmem : x ∈ Ioo (0 : ℝ) a
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, h3 hmem]
      have hane : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
      rw [mul_one, mul_assoc, mul_inv_cancel₀ hane, mul_one, sub_self]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
      ring

theorem isClosed_soninHeadConstant {a : ℝ} (ha : 0 < a) :
    IsClosed {f : SoninL2 | SoninHeadConstant a (f : ℝ → ℂ)} := by
  have hset : {f : SoninL2 | SoninHeadConstant a (f : ℝ → ℂ)} =
      (LinearMap.ker (soninHeadDefect a).toLinearMap : Set SoninL2) := by
    ext f
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe]
    exact (soninHeadDefect_eq_zero_iff ha f).symm
  rw [hset]
  exact (soninHeadDefect a).isClosed_ker

theorem isClosed_soninHeadConstantSubmodule {a : ℝ} (ha : 0 < a) :
    IsClosed (soninHeadConstantSubmodule a : Set evenSubspace) :=
  (isClosed_soninHeadConstant ha).preimage continuous_subtype_val

/-- **Burnol's extended Sonine space is closed.** -/
theorem isClosed_soninExtendedSpace {a : ℝ} (ha : 0 < a) :
    IsClosed (soninExtendedSpace a : Set evenSubspace) := by
  have h1 := isClosed_soninHeadConstantSubmodule ha
  have h2 : IsClosed
      ((soninHeadConstantSubmodule a).comap
        soninCosineUnitary.toLinearEquiv.toLinearMap : Set evenSubspace) :=
    h1.preimage soninCosineUnitary.continuous
  exact h1.inter h2

instance instCompleteSpaceSoninExtendedSpace {a : ℝ} [Fact (0 < a)] :
    CompleteSpace (soninExtendedSpace a) :=
  (isClosed_soninExtendedSpace (Fact.out : 0 < a)).completeSpace_coe

end RHTower
