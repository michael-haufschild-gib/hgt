import GaloisForLFunctions.RHTower.FokasLenellsRHBoundary
import GaloisForLFunctions.RHTower.CauchyTransformHardy

/-!
# Half-plane orientation of the Fokas–Lenells Cauchy inverse

The Fourier transform uses the negative exponential. Consequently its positive
frequency datum ray gives lower-half-plane Hardy boundary values. This identifies
the signed Cauchy operator with the actual Hardy decomposition, beyond its
algebraic square identity, and checks the normalized RH solution against it.
-/

open MeasureTheory Complex Set
namespace RHTower.FokasLenells
noncomputable section

/-- Positive-ray cutoff fixes exactly the positive-support subspace. -/
theorem positiveCutoff_fixed_iff (u : SoninL2) :
    indicatorCutoff (Ioi 0) measurableSet_Ioi u = u ↔ u ∈ halfLineL2 := by
  rw [mem_halfLineL2_iff]
  constructor
  · intro h
    have he := indicatorCutoff_ae (Ioi 0) measurableSet_Ioi u
    rw [h] at he
    filter_upwards [he] with s hs hneg
    simpa only [Set.indicator_of_notMem (show s ∉ Ioi (0:ℝ) from not_lt.mpr hneg.le)] using hs
  · intro h
    have hne : ∀ᵐ s : ℝ, s ≠ 0 := by rw [ae_iff]; simp
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (Ioi 0) measurableSet_Ioi u,h,hne] with s hs hz hne
    rw [hs]
    rcases lt_or_gt_of_ne hne with hn | hp
    · simp [Set.indicator_of_notMem (show s ∉ Ioi (0:ℝ) from not_lt.mpr hn.le),hz hn]
    · exact Set.indicator_of_mem hp _

/-- Positive-ray cutoff kills exactly the negative-support subspace. -/
theorem positiveCutoff_zero_iff (u : SoninL2) :
    indicatorCutoff (Ioi 0) measurableSet_Ioi u = 0 ↔ u ∈ lowerHalfLineL2 := by
  rw [mem_lowerHalfLineL2_iff]
  constructor
  · intro h
    have he := indicatorCutoff_ae (Ioi 0) measurableSet_Ioi u
    rw [h] at he
    filter_upwards [he,Lp.coeFn_zero ℂ 2 volume] with s hs hz hp
    rw [hz,Set.indicator_of_mem (show s ∈ Ioi (0:ℝ) from hp)] at hs
    exact hs.symm
  · intro h
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (Ioi 0) measurableSet_Ioi u,h,Lp.coeFn_zero ℂ 2 volume]
      with s hs hz h0
    rw [hs,h0]
    by_cases hp : 0 < s
    · simpa only [Set.indicator_of_mem (show s ∈ Ioi (0:ℝ) from hp),Pi.zero_apply] using hz hp
    · exact Set.indicator_of_notMem hp _

private theorem mem_fourier_image_iff (H : Submodule ℂ SoninL2) (u : SoninL2) :
    u ∈ H.map fourierUnitary.toLinearEquiv.toLinearMap ↔ fourierUnitary.symm u ∈ H := by
  constructor
  · rintro ⟨v,hv,he⟩
    change fourierUnitary v = u at he
    rw [← he,fourierUnitary.symm_apply_apply]
    exact hv
  · intro h
    exact ⟨fourierUnitary.symm u,h,fourierUnitary.apply_symm_apply u⟩

/-- The negative eigenspace is precisely the lower-half-plane Hardy space. -/
theorem negativeCauchy_eq_neg_iff (u : SoninL2) :
    negativeCauchy u = -u ↔ u ∈ hardyL2ᗮ := by
  rw [hardyL2_orthogonal]
  change -fourierUnitary (indicatorCutoff (Ioi 0) measurableSet_Ioi (fourierUnitary.symm u)) = -u ↔
    u ∈ halfLineL2.map fourierUnitary.toLinearEquiv.toLinearMap
  rw [neg_inj,← fourierUnitary.symm.injective.eq_iff,fourierUnitary.symm_apply_apply,
    positiveCutoff_fixed_iff,mem_fourier_image_iff]

/-- The kernel is precisely the upper-half-plane Hardy space. -/
theorem negativeCauchy_eq_zero_iff (u : SoninL2) :
    negativeCauchy u = 0 ↔ u ∈ hardyL2 := by
  change -fourierUnitary (indicatorCutoff (Ioi 0) measurableSet_Ioi (fourierUnitary.symm u)) = 0 ↔
    u ∈ lowerHalfLineL2.map fourierUnitary.toLinearEquiv.toLinearMap
  rw [neg_eq_zero,← fourierUnitary.symm.injective.eq_iff,fourierUnitary.symm_apply_apply,map_zero,
    positiveCutoff_zero_iff,mem_fourier_image_iff]

theorem boundaryCauchy_eq_neg_iff (u : Boundary) :
    boundaryCauchy u = -u ↔ u.1 ∈ hardyL2ᗮ ∧ u.2 ∈ hardyL2ᗮ := by
  change (negativeCauchy u.1,negativeCauchy u.2) = (-u.1,-u.2) ↔ _
  rw [Prod.ext_iff,negativeCauchy_eq_neg_iff,negativeCauchy_eq_neg_iff]

theorem boundaryCauchy_eq_zero_iff (u : Boundary) :
    boundaryCauchy u = 0 ↔ u.1 ∈ hardyL2 ∧ u.2 ∈ hardyL2 := by
  change (negativeCauchy u.1,negativeCauchy u.2) = (0,0) ↔ _
  rw [Prod.ext_iff,negativeCauchy_eq_zero_iff,negativeCauchy_eq_zero_iff]

/-- Both lower correction entries belong to the actual lower-half-plane Hardy space. -/
theorem directLowerCorrection_mem_hardy_orthogonal (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    (directLowerCorrection q t x i).1 ∈ hardyL2ᗮ ∧
    (directLowerCorrection q t x i).2 ∈ hardyL2ᗮ :=
  (boundaryCauchy_eq_neg_iff _).mp (directLowerCorrection_hardy q t x i)

/-- Both upper correction entries belong to the actual upper-half-plane Hardy space. -/
theorem directUpperCorrection_mem_hardy (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    (directUpperCorrection q t x i).1 ∈ hardyL2 ∧
    (directUpperCorrection q t x i).2 ∈ hardyL2 :=
  (boundaryCauchy_eq_zero_iff _).mp (directUpperCorrection_hardy q t x i)

/-- The RH boundary existence and uniqueness statement with intrinsic Hardy-space conditions. -/
theorem directIntrinsicHardyRHBoundary_existsUnique (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i : Fin 2) :
    ∃! uv : Boundary × Boundary,
      (uv.1.1 ∈ hardyL2ᗮ ∧ uv.1.2 ∈ hardyL2ᗮ) ∧
      (uv.2.1 ∈ hardyL2 ∧ uv.2.2 ∈ hardyL2) ∧
      normalizedBoundaryRow i uv.2 =ᵐ[volume]
        (fun z => GaloisForLFunctions.HTGeometry.FokasLenells.matrixVector
          (GaloisForLFunctions.HTGeometry.FokasLenells.regularJump
            (GaloisForLFunctions.HTGeometry.FokasLenells.globalSmallScatteringPotential q) t x z).transpose
          (normalizedBoundaryRow i uv.1 z)) := by
  simpa only [boundaryCauchy_eq_neg_iff,boundaryCauchy_eq_zero_iff] using
    directHardyRHBoundary_existsUnique q t x i

/-- A rational boundary probe with its pole strictly above the real axis. -/
def upperPoleProbe (r a : ℝ) : SoninL2 :=
  (memLp_cauchyKernel (w := (r:ℂ)+(Real.exp a:ℂ)*I)
    (by simpa only [Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_mul,add_zero,zero_add,zero_sub,neg_ne_zero,neg_lt_zero] using Real.exp_ne_zero a)).toLp
    (fun s => ((s:ℂ)-((r:ℂ)+(Real.exp a:ℂ)*I))⁻¹)

/-- A rational boundary probe with its pole strictly below the real axis. -/
def lowerPoleProbe (r a : ℝ) : SoninL2 :=
  (memLp_cauchyKernel (w := (r:ℂ)-(Real.exp a:ℂ)*I)
    (by simpa only [Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_mul,add_zero,zero_add,zero_sub,neg_ne_zero,neg_lt_zero] using Real.exp_ne_zero a)).toLp
    (fun s => ((s:ℂ)-((r:ℂ)-(Real.exp a:ℂ)*I))⁻¹)

/-- An upper-pole rational function is a lower Hardy boundary and has C⁻ value minus itself. -/
theorem negativeCauchy_upperPoleProbe (r a : ℝ) :
    negativeCauchy (upperPoleProbe r a) = -upperPoleProbe r a := by
  apply (negativeCauchy_eq_neg_iff _).mpr
  exact cauchyKernel_mem_hardyL2_orthogonal (by simpa only [Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_mul,add_zero,zero_add,zero_sub,neg_ne_zero,neg_lt_zero] using Real.exp_pos a)

/-- A lower-pole rational function is an upper Hardy boundary and is killed by C⁻. -/
theorem negativeCauchy_lowerPoleProbe (r a : ℝ) :
    negativeCauchy (lowerPoleProbe r a) = 0 := by
  apply (negativeCauchy_eq_zero_iff _).mpr
  exact cauchyKernel_mem_hardyL2 (by simpa only [Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_mul,add_zero,zero_add,zero_sub,neg_ne_zero,neg_lt_zero] using Real.exp_pos a)

end
end RHTower.FokasLenells
