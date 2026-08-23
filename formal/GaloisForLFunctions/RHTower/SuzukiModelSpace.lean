import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.RHTower.SuzukiWeilPropOneTwo
import Mathlib.Analysis.Fourier.LpSpace

/-!
# The model space `K(Theta_xi)` of Suzuki's Hilbert-space theorems

Masatoshi Suzuki, arXiv:2301.00421v3, Sections 2.4 and 5.  This file builds, from scratch, the two
objects the RH-conditional half of the paper rests on and which neither mathlib nor the corpus had:

* `hardyL2` — `H^2 = F(L^2(0,infty))`, the Hardy space of the upper half-plane realized as a closed
  subspace of `L^2(R)` through boundary values, exactly as Suzuki sets it up;
* `suzukiModelSpace` — `K(Theta_xi) = H^2 minus Theta_xi H^2` (eq. 2.7), also closed.

Three design choices make this work in Lean.

`L^2(0,infty)` is the *kernel* of multiplication by the indicator of the negative ray
(`negRayProj`), so it is a submodule and closed for free.  `H^2` is its image under mathlib's
unitary `Lp.fourierTransformₗᵢ`, closed because that map is a homeomorphism.

`Theta_xi = E^sharp/E` is only unimodular where `E` does not vanish, and `lpBoundedMulCLM_inner_unimodular`
wants unimodularity *everywhere*; so `suzukiThetaSymbol` is normalized to `1` at the zeros of `E`,
which changes nothing almost everywhere.  On the real line `E^sharp(x) = conj(E(x))`
(`xiHedenmalmDeBrangesESharp_ofReal_eq_conj`), which is what makes the symbol unimodular at all.

`Theta H^2` is closed not by an isometry-image argument but because it is the *preimage* of `H^2`
under multiplication by `conj Theta`, the explicit two-sided inverse of `thetaMul`.
-/

open Complex Filter Topology MeasureTheory Set
open MeasureTheory

namespace RHTower
noncomputable section

/-- The indicator symbol of the negative half-line. -/
def negRaySymbol : ℝ → ℂ := Set.indicator (Set.Iio 0) 1

theorem measurable_negRaySymbol : Measurable negRaySymbol := by
  unfold negRaySymbol
  exact (measurable_const.indicator measurableSet_Iio)

theorem norm_negRaySymbol_le (x : ℝ) : ‖negRaySymbol x‖ ≤ 1 := by
  unfold negRaySymbol
  by_cases hx : x ∈ Set.Iio 0
  · rw [Set.indicator_of_mem hx]
    simp
  · rw [Set.indicator_of_notMem hx]
    simp

/-- Multiplication by the negative-ray indicator, as a continuous linear map on `L²(ℝ)`. -/
def negRayProj : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) measurable_negRaySymbol
    (by norm_num : (0:ℝ) ≤ 1) norm_negRaySymbol_le

theorem negRayProj_coeFn (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (negRayProj f : ℝ → ℂ) =ᵐ[volume] fun x => negRaySymbol x * (f : ℝ → ℂ) x :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) measurable_negRaySymbol
    (by norm_num) norm_negRaySymbol_le f

/-- `L²(0,∞)` inside `L²(ℝ)`: the kernel of multiplication by the negative-ray indicator. -/
def halfLineL2 : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  LinearMap.ker (negRayProj : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ))

theorem isClosed_halfLineL2 : IsClosed (halfLineL2 : Set (Lp ℂ 2 (volume : Measure ℝ))) :=
  negRayProj.isClosed_ker

theorem mem_halfLineL2_iff (f : Lp ℂ 2 (volume : Measure ℝ)) :
    f ∈ halfLineL2 ↔ ∀ᵐ x : ℝ, x < 0 → (f : ℝ → ℂ) x = 0 := by
  constructor
  · intro hf
    have h0 : negRayProj f = 0 := LinearMap.mem_ker.mp hf
    have hcoe := negRayProj_coeFn f
    have hz : (negRayProj f : ℝ → ℂ) =ᵐ[volume] 0 := by
      rw [h0]
      exact Lp.coeFn_zero ℂ 2 volume
    filter_upwards [hcoe, hz] with x h1 h2 hx
    rw [h1] at h2
    have hind : negRaySymbol x = 1 := by
      unfold negRaySymbol
      rw [Set.indicator_of_mem (Set.mem_Iio.mpr hx)]
      rfl
    rw [hind, one_mul] at h2
    exact h2
  · intro hf
    have hcoe := negRayProj_coeFn f
    show negRayProj f = 0
    refine Lp.ext ?_
    filter_upwards [hcoe, hf, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x h1 h2 h3
    rw [h1, h3]
    by_cases hx : x < 0
    · rw [h2 hx, mul_zero]
      rfl
    · have hind : negRaySymbol x = 0 := by
        unfold negRaySymbol
        rw [Set.indicator_of_notMem (by simpa using hx)]
      rw [hind, zero_mul]
      rfl

def posRaySymbol : ℝ → ℂ := Set.indicator (Set.Ioi 0) 1

theorem measurable_posRaySymbol : Measurable posRaySymbol :=
  measurable_const.indicator measurableSet_Ioi

theorem norm_posRaySymbol_le (x : ℝ) : ‖posRaySymbol x‖ ≤ 1 := by
  unfold posRaySymbol
  by_cases hx : x ∈ Set.Ioi (0:ℝ)
  · rw [Set.indicator_of_mem hx]; simp
  · rw [Set.indicator_of_notMem hx]; simp

def posRayProj : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) measurable_posRaySymbol
    (by norm_num : (0:ℝ) ≤ 1) norm_posRaySymbol_le

theorem posRayProj_coeFn (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (posRayProj f : ℝ → ℂ) =ᵐ[volume] fun x => posRaySymbol x * (f : ℝ → ℂ) x :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) measurable_posRaySymbol
    (by norm_num) norm_posRaySymbol_le f

/-- `L²(-∞,0)` inside `L²(ℝ)`. -/
def lowerHalfLineL2 : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  LinearMap.ker (posRayProj : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ))

theorem mem_lowerHalfLineL2_iff (f : Lp ℂ 2 (volume : Measure ℝ)) :
    f ∈ lowerHalfLineL2 ↔ ∀ᵐ x : ℝ, 0 < x → (f : ℝ → ℂ) x = 0 := by
  constructor
  · intro hf
    have h0 : posRayProj f = 0 := LinearMap.mem_ker.mp hf
    have hz : (posRayProj f : ℝ → ℂ) =ᵐ[volume] 0 := by
      rw [h0]; exact Lp.coeFn_zero ℂ 2 volume
    filter_upwards [posRayProj_coeFn f, hz] with x h1 h2 hx
    rw [h1] at h2
    have hind : posRaySymbol x = 1 := by
      unfold posRaySymbol
      rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hx)]; rfl
    rw [hind, one_mul] at h2
    exact h2
  · intro hf
    show posRayProj f = 0
    refine Lp.ext ?_
    filter_upwards [posRayProj_coeFn f, hf, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)]
      with x h1 h2 h3
    rw [h1, h3]
    by_cases hx : 0 < x
    · rw [h2 hx, mul_zero]; rfl
    · have hind : posRaySymbol x = 0 := by
        unfold posRaySymbol
        rw [Set.indicator_of_notMem (by simpa using hx)]
      rw [hind, zero_mul]; rfl

theorem isClosed_lowerHalfLineL2 :
    IsClosed (lowerHalfLineL2 : Set (Lp ℂ 2 (volume : Measure ℝ))) :=
  posRayProj.isClosed_ker

/-- **Suzuki's `H² = 𝖥(L²(0,∞))`**, the Hardy space of the *upper* half-plane realized as a closed
subspace of `L²(ℝ)` through boundary values.

The datum ray is `(-∞,0)`, not `(0,∞)`: mathlib's Fourier transform uses the kernel
`e^{-2πi x ξ}`, whose modulus on a datum supported in `x < 0` is `e^{2π x Im ξ}`, decaying exactly
when `Im ξ > 0`.  Suzuki's kernel is `e^{izx}` on `x > 0`, which decays for `Im z > 0` as well, so
the two conventions agree on *which half-plane* `H²` belongs to while disagreeing on which ray
carries the datum. -/
def hardyL2 : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  Submodule.map
    ((MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.toLinearMap) lowerHalfLineL2

theorem isClosed_hardyL2 : IsClosed (hardyL2 : Set (Lp ℂ 2 (volume : Measure ℝ))) := by
  have himg : (hardyL2 : Set (Lp ℂ 2 (volume : Measure ℝ)))
      = (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) ''
        (lowerHalfLineL2 : Set (Lp ℂ 2 (volume : Measure ℝ))) := rfl
  rw [himg]
  exact (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).toHomeomorph.isClosedMap _
    isClosed_lowerHalfLineL2

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## The meromorphic inner function as an `L²` multiplier -/

theorem xiHedenmalmDeBrangesESharp_ofReal_eq_conj (x : ℝ) :
    xiHedenmalmDeBrangesESharp ((x : ℝ) : ℂ)
      = (starRingEnd ℂ) (xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)) := by
  rw [xiHedenmalmDeBrangesESharp, xiHedenmalmDeBrangesE, map_add, map_mul, Complex.conj_I,
    Complex.conj_eq_iff_im.mpr (XiC_ofReal_im x),
    Complex.conj_eq_iff_im.mpr (deriv_XiC_ofReal_im x)]
  ring

/-- Suzuki's `Θ_ξ = E^♯/E` on the real line, normalized to `1` at the (countably many) zeros of
`E` so that it is unimodular everywhere. -/
def suzukiThetaSymbol (x : ℝ) : ℂ :=
  if xiHedenmalmDeBrangesE ((x : ℝ) : ℂ) = 0 then 1
  else xiHedenmalmDeBrangesESharp ((x : ℝ) : ℂ) / xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)

theorem measurable_suzukiThetaSymbol : Measurable suzukiThetaSymbol := by
  have hE : Measurable (fun x : ℝ => xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)) := by
    have hX : Measurable (fun x : ℝ => XiC ((x : ℝ) : ℂ)) :=
      continuous_XiC.measurable.comp Complex.measurable_ofReal
    have hD : Measurable (fun x : ℝ => deriv XiC ((x : ℝ) : ℂ)) :=
      (measurable_deriv XiC).comp Complex.measurable_ofReal
    simp only [xiHedenmalmDeBrangesE]
    exact hX.add (measurable_const.mul hD)
  have hEs : Measurable (fun x : ℝ => xiHedenmalmDeBrangesESharp ((x : ℝ) : ℂ)) := by
    simp only [fun x : ℝ => xiHedenmalmDeBrangesESharp_ofReal_eq_conj x]
    exact Complex.continuous_conj.measurable.comp hE
  unfold suzukiThetaSymbol
  exact Measurable.ite (hE (measurableSet_singleton 0)) measurable_const (hEs.div hE)

theorem suzukiThetaSymbol_unimodular (x : ℝ) :
    (starRingEnd ℂ) (suzukiThetaSymbol x) * suzukiThetaSymbol x = 1 := by
  unfold suzukiThetaSymbol
  by_cases hE : xiHedenmalmDeBrangesE ((x : ℝ) : ℂ) = 0
  · rw [if_pos hE]
    simp
  · rw [if_neg hE, xiHedenmalmDeBrangesESharp_ofReal_eq_conj, map_div₀, Complex.conj_conj]
    have hne : (starRingEnd ℂ) (xiHedenmalmDeBrangesE ((x : ℝ) : ℂ)) ≠ 0 := by
      simpa using hE
    field_simp

theorem norm_suzukiThetaSymbol (x : ℝ) : ‖suzukiThetaSymbol x‖ = 1 := by
  have h := suzukiThetaSymbol_unimodular x
  have h2 : ‖suzukiThetaSymbol x‖ * ‖suzukiThetaSymbol x‖ = 1 := by
    have hc := congrArg (fun z : ℂ => ‖z‖) h
    simpa [norm_mul, Complex.norm_conj] using hc
  nlinarith [norm_nonneg (suzukiThetaSymbol x), h2]

theorem norm_suzukiThetaSymbol_le (x : ℝ) : ‖suzukiThetaSymbol x‖ ≤ 1 :=
  le_of_eq (norm_suzukiThetaSymbol x)

/-- Multiplication by `Θ_ξ` on `L²(ℝ)`. -/
def thetaMul : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) measurable_suzukiThetaSymbol
    (by norm_num : (0:ℝ) ≤ 1) norm_suzukiThetaSymbol_le

/-- Multiplication by `conj Θ_ξ`, the inverse of `thetaMul`. -/
def thetaMulInv : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (Complex.continuous_conj.measurable.comp measurable_suzukiThetaSymbol)
    (by norm_num : (0:ℝ) ≤ 1)
    (fun x => by rw [Function.comp_apply, Complex.norm_conj]; exact norm_suzukiThetaSymbol_le x)

theorem thetaMul_coeFn (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (thetaMul f : ℝ → ℂ) =ᵐ[volume] fun x => suzukiThetaSymbol x * (f : ℝ → ℂ) x :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) measurable_suzukiThetaSymbol
    (by norm_num) norm_suzukiThetaSymbol_le f

theorem thetaMulInv_coeFn (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (thetaMulInv f : ℝ → ℂ) =ᵐ[volume]
      fun x => (starRingEnd ℂ) (suzukiThetaSymbol x) * (f : ℝ → ℂ) x :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) _ _ _ f

theorem thetaMul_thetaMulInv (f : Lp ℂ 2 (volume : Measure ℝ)) :
    thetaMul (thetaMulInv f) = f := by
  refine Lp.ext ?_
  filter_upwards [thetaMul_coeFn (thetaMulInv f), thetaMulInv_coeFn f] with x h1 h2
  rw [h1, h2, ← mul_assoc, mul_comm (suzukiThetaSymbol x),
    suzukiThetaSymbol_unimodular x, one_mul]

theorem thetaMulInv_thetaMul (f : Lp ℂ 2 (volume : Measure ℝ)) :
    thetaMulInv (thetaMul f) = f := by
  refine Lp.ext ?_
  filter_upwards [thetaMulInv_coeFn (thetaMul f), thetaMul_coeFn f] with x h1 h2
  rw [h1, h2, ← mul_assoc, suzukiThetaSymbol_unimodular x, one_mul]

end
end RHTower

namespace RHTower
noncomputable section
open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

/-! ## The model space `K(Θ)` -/

/-- `Θ_ξ H²`. -/
def thetaHardyL2 : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  Submodule.map (thetaMul : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    hardyL2

theorem thetaHardyL2_eq_preimage :
    (thetaHardyL2 : Set (Lp ℂ 2 (volume : Measure ℝ)))
      = thetaMulInv ⁻¹' (hardyL2 : Set (Lp ℂ 2 (volume : Measure ℝ))) := by
  ext y
  constructor
  · rintro ⟨f, hf, rfl⟩
    show thetaMulInv (thetaMul f) ∈ hardyL2
    rw [thetaMulInv_thetaMul]
    exact hf
  · intro hy
    exact ⟨thetaMulInv y, hy, thetaMul_thetaMulInv y⟩

theorem isClosed_thetaHardyL2 :
    IsClosed (thetaHardyL2 : Set (Lp ℂ 2 (volume : Measure ℝ))) := by
  rw [thetaHardyL2_eq_preimage]
  exact isClosed_hardyL2.preimage thetaMulInv.continuous

/-- **Suzuki's model space** `K(Θ_ξ) = H² ⊖ Θ_ξ H²` (eq. 2.7), realized as a closed subspace of
`L²(ℝ)`. -/
def suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  hardyL2 ⊓ thetaHardyL2ᗮ

theorem isClosed_suzukiModelSpace :
    IsClosed (suzukiModelSpace : Set (Lp ℂ 2 (volume : Measure ℝ))) :=
  isClosed_hardyL2.inter (Submodule.isClosed_orthogonal _)

theorem mem_suzukiModelSpace_iff (f : Lp ℂ 2 (volume : Measure ℝ)) :
    f ∈ suzukiModelSpace ↔ f ∈ hardyL2 ∧ ∀ g ∈ thetaHardyL2, (inner ℂ g f : ℂ) = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun g hg => Submodule.mem_orthogonal _ _ |>.mp h2 g hg⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Submodule.mem_orthogonal _ _ |>.mpr fun g hg => h2 g hg⟩

end
end RHTower

