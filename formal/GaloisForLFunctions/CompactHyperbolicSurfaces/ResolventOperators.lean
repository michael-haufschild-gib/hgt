import GaloisForLFunctions.CompactHyperbolicSurfaces.AutomorphicKernels
import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventIdentity
import GaloisForLFunctions.HTGeometry.SchurKernelComposition

/-!
# The resolvent operators of a compact hyperbolic surface

A `CompactQuotient` is a cocompact free group `Γ ≤ SL(2, ℝ)` with a measurable fundamental domain
`F` inside a compact set.  On `L²(F)` a profile `k ≥ 0` of finite mass defines the Schur kernel
`K(z, w) = Σ_γ k(u(z, γw))` (`profileKernel`): unfolding bounds its rows and columns by the mass
`∫_ℍ k(u(i, w)) dμ(w)`.  For `k_s` the mass is `1/(s(s − 1))` (`lintegral_resKernel_mass`).

The resolvent operators `T_s` are self-adjoint with `‖T_s‖ ≤ 1/(s(s − 1))`, and the kernel
identity `k_s ⋆ k_a = D_{a,s}/(s(s−1) − a(a−1))` unfolds to

  `T_s T_a = (T_a − T_s)/(s(s − 1) − a(a − 1))`   (`resOp_comp`).
-/

open MeasureTheory Set Filter UpperHalfPlane Real
open scoped ENNReal MatrixGroups Pointwise

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.SchurKernel

noncomputable section

/-- A compact hyperbolic surface `Γ\ℍ` presented by a fundamental domain. -/
structure CompactQuotient where
  Γ : Subgroup SL(2, ℝ)
  cocompactFree : IsCocompactFree Γ
  F : Set ℍ
  K : Set ℍ
  isCompact_K : IsCompact K
  F_subset : F ⊆ K
  measurableSet_F : MeasurableSet F
  isFundamentalDomain : IsFundamentalDomain Γ F volume

namespace CompactQuotient

variable (X : CompactQuotient)

instance : Countable X.Γ := X.cocompactFree.countable

/-- The measure `μ|_F`. -/
abbrev μ : Measure ℍ := volume.restrict X.F

theorem volume_F_lt_top : volume X.F < ∞ :=
  (measure_mono X.F_subset).trans_lt X.isCompact_K.measure_lt_top

instance : IsFiniteMeasure X.μ := ⟨by
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]; exact X.volume_F_lt_top⟩

/-- Points of `ℍ` are null. -/
theorem volume_singleton (p : ℍ) : volume ({p} : Set ℍ) = 0 := by
  have h := volume_pairU_preimage_eq_zero p (measurableSet_singleton (0 : ℝ)) Real.volume_singleton
  have : {w : ℍ | pairU p w ∈ ({0} : Set ℝ)} = {p} := by
    ext w
    simp only [mem_setOf_eq, mem_singleton_iff]
    rw [pairU_eq_cosh]
    constructor
    · intro h0
      have h1 : Real.cosh (dist p w) = 1 := by linarith
      by_contra hne
      have h2 : dist p w ≠ 0 := fun h => hne (dist_eq_zero.mp h).symm
      have := Real.one_lt_cosh.mpr h2
      linarith
    · rintro rfl; simp
  rwa [this] at h

/-- Orbits are null. -/
theorem volume_orbit (p : ℍ) : volume (Set.range fun γ : X.Γ => (γ : SL(2, ℝ)) • p) = 0 := by
  rw [← iUnion_singleton_eq_range]
  exact measure_iUnion_null fun γ => volume_singleton _

/-! ### Kernels of profiles -/

/-- The Schur kernel `K(z, w) = Σ_γ k(u(z, γw))` of a profile of finite mass. -/
def profileKernel {k : ℝ → ℝ≥0∞} (hk : Measurable k) (hm : ∫⁻ w, k (pairU I w) < ∞) :
    SchurKernel X.μ where
  toFun z w := ((autK X.Γ k z w).toReal : ℂ)
  measurable := Complex.measurable_ofReal.comp (measurable_autK hk).ennreal_toReal
  bound := (∫⁻ w, k (pairU I w)).toNNReal
  row z := by
    rw [ENNReal.coe_toNNReal hm.ne]
    calc ∫⁻ w in X.F, ‖((autK X.Γ k z w).toReal : ℂ)‖ₑ
        ≤ ∫⁻ w in X.F, autK X.Γ k z w := lintegral_mono fun w => by
          rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
          exact ENNReal.ofReal_toReal_le
      _ = ∫⁻ w, k (pairU I w) := by
          rw [setLIntegral_autK X.isFundamentalDomain hk, lintegral_pairU_eq_I]
  col w := by
    rw [ENNReal.coe_toNNReal hm.ne]
    calc ∫⁻ z in X.F, ‖((autK X.Γ k z w).toReal : ℂ)‖ₑ
        ≤ ∫⁻ z in X.F, autK X.Γ k w z := lintegral_mono fun z => by
          rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
            autK_comm]
          exact ENNReal.ofReal_toReal_le
      _ = ∫⁻ w, k (pairU I w) := by
          rw [setLIntegral_autK X.isFundamentalDomain hk, lintegral_pairU_eq_I]

theorem profileKernel_toFun {k : ℝ → ℝ≥0∞} (hk : Measurable k) (hm : ∫⁻ w, k (pairU I w) < ∞)
    (z w : ℍ) : (X.profileKernel hk hm).toFun z w = ((autK X.Γ k z w).toReal : ℂ) := rfl

theorem isSelfAdjoint_profileKernel {k : ℝ → ℝ≥0∞} (hk : Measurable k)
    (hm : ∫⁻ w, k (pairU I w) < ∞) : IsSelfAdjoint (X.profileKernel hk hm).op := by
  refine isSelfAdjoint_op _ fun z w => ?_
  rw [profileKernel_toFun, profileKernel_toFun, Complex.conj_ofReal, autK_comm]

theorem norm_profileKernel_le {k : ℝ → ℝ≥0∞} (hk : Measurable k) (hm : ∫⁻ w, k (pairU I w) < ∞) :
    ‖(X.profileKernel hk hm).op‖ ≤ (∫⁻ w, k (pairU I w)).toReal :=
  (norm_op_le _).trans (le_of_eq (ENNReal.coe_toNNReal_eq_toReal _))

end CompactQuotient

/-! ### Masses -/

/-- `∫_ℍ k_s(u(i, w)) dμ(w) = 1/(s(s − 1))`. -/
theorem lintegral_resKernel_mass {s : ℝ} (hs : 1 < s) :
    ∫⁻ w, resKernel s (pairU I w) = ENNReal.ofReal (1 / (s * (s - 1))) := by
  rw [lintegral_pairU_I (measurable_resKernel s)]
  simp_rw [abelL_resKernel (by linarith : (1 / 2 : ℝ) < s)]
  have hsplit := lintegral_add_compl (μ := volume) (fun τ : ℝ => ENNReal.ofReal (Real.exp (-(τ / 2))) *
    ENNReal.ofReal (Real.exp (-((s - 1 / 2) * |τ|)) / (2 * s - 1))) (measurableSet_Ioi (a := (0 : ℝ)))
  rw [compl_Ioi] at hsplit
  rw [← hsplit]
  have h1 : ∀ τ ∈ Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(τ / 2))) *
      ENNReal.ofReal (Real.exp (-((s - 1 / 2) * |τ|)) / (2 * s - 1)) =
      ENNReal.ofReal (1 / (2 * s - 1)) * ENNReal.ofReal (Real.exp ((-s) * τ)) := by
    intro τ hτ
    have hτ' : (0 : ℝ) < τ := hτ
    rw [abs_of_pos hτ', ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (one_div_pos.mpr (by linarith : (0:ℝ) < 2 * s - 1)).le]
    congr 1
    rw [mul_div_assoc', ← Real.exp_add, div_eq_mul_one_div, mul_comm]
    congr 2; ring
  have h2 : ∀ τ ∈ Iic (0 : ℝ), ENNReal.ofReal (Real.exp (-(τ / 2))) *
      ENNReal.ofReal (Real.exp (-((s - 1 / 2) * |τ|)) / (2 * s - 1)) =
      ENNReal.ofReal (1 / (2 * s - 1)) * ENNReal.ofReal (Real.exp ((s - 1) * τ)) := by
    intro τ hτ
    have hτ' : τ ≤ 0 := hτ
    rw [abs_of_nonpos hτ', ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (one_div_pos.mpr (by linarith : (0:ℝ) < 2 * s - 1)).le]
    congr 1
    rw [mul_div_assoc', ← Real.exp_add, div_eq_mul_one_div, mul_comm]
    congr 2; ring
  have hA : 0 ≤ -Real.exp ((-s) * 0) / -s := by
    rw [neg_div_neg_eq]; exact div_nonneg (Real.exp_pos _).le (by linarith)
  have hB : 0 ≤ Real.exp ((s - 1) * 0) / (s - 1) := div_nonneg (Real.exp_pos _).le (by linarith)
  have hC : 0 ≤ 1 / (2 * s - 1) := (one_div_pos.mpr (by linarith : (0:ℝ) < 2 * s - 1)).le
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, setLIntegral_congr_fun measurableSet_Iic h2,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    setLIntegral_exp_mul_Ioi (by linarith), setLIntegral_exp_mul_Iic (by linarith),
    ← mul_add, ← ENNReal.ofReal_add hA hB, ← ENNReal.ofReal_mul hC]
  congr 1
  simp only [mul_zero, Real.exp_zero]
  have h1' : s - 1 ≠ 0 := by linarith
  have h2' : 2 * s - 1 ≠ 0 := by linarith
  have h3' : s ≠ 0 := by linarith
  field_simp
  ring

theorem lintegral_resKernel_mass_lt_top {s : ℝ} (hs : 1 < s) :
    ∫⁻ w, resKernel s (pairU I w) < ∞ := by
  rw [lintegral_resKernel_mass hs]; exact ENNReal.ofReal_lt_top

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
