import GaloisForLFunctions.HTGeometry.CompactAbelianCharacter
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Hermitian kernels detect `L²`

A vector orthogonal to every continuous function is zero, because continuous functions are dense in
`L²` of a finite regular measure.  The Hermitian kernels — those with `conj (k (-z)) = k z` — span
the continuous functions over `ℂ`, since `f = f₁ + i f₂` with `f₁ = (f + f⋆)/2` and
`f₂ = (f - f⋆)/(2i)`, where `f⋆ z = conj (f (-z))`.  Hence a vector annihilated by every Hermitian
convolution operator is zero.

This is the density input of the Peter–Weyl argument: it is what forbids a nonzero vector orthogonal
to every character.
-/

open MeasureTheory TopologicalSpace

namespace GaloisForLFunctions

namespace CompactAbelian

noncomputable section

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
/-- A vector orthogonal to every continuous function vanishes. -/
theorem eq_zero_of_inner_toLp_eq_zero {v : Lp ℂ 2 (haarProb G)}
    (h : ∀ f : C(G, ℂ), inner ℂ v (ContinuousMap.toLp 2 (haarProb G) ℂ f) = 0) : v = 0 := by
  have hdense : DenseRange
      (ContinuousMap.toLp 2 (haarProb G) ℂ : C(G, ℂ) →L[ℂ] Lp ℂ 2 (haarProb G)) :=
    ContinuousMap.toLp_denseRange (𝕜 := ℂ) (E := ℂ) (μ := haarProb G) (p := 2) (by norm_num)
  have hcont : Continuous fun u : Lp ℂ 2 (haarProb G) => inner ℂ v u := (innerSL ℂ v).continuous
  have hzero : (fun u : Lp ℂ 2 (haarProb G) => inner ℂ v u) = fun _ => (0 : ℂ) := by
    refine Continuous.ext_on hdense hcont continuous_const ?_
    rintro u ⟨f, rfl⟩
    exact h f
  have : inner ℂ v v = (0 : ℂ) := congrFun hzero v
  exact inner_self_eq_zero.mp this

/-- The Hermitian part of a continuous function. -/
def hermPart (f : C(G, ℂ)) : C(G, ℂ) :=
  (2 : ℂ)⁻¹ • (f + ⟨fun z => (starRingEnd ℂ) (f (-z)),
    Complex.continuous_conj.comp (f.continuous.comp continuous_neg)⟩)

/-- The anti-Hermitian part of a continuous function, divided by `i`. -/
def hermPart' (f : C(G, ℂ)) : C(G, ℂ) :=
  ((2 : ℂ) * Complex.I)⁻¹ • (f - ⟨fun z => (starRingEnd ℂ) (f (-z)),
    Complex.continuous_conj.comp (f.continuous.comp continuous_neg)⟩)

omit [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
theorem hermPart_apply (f : C(G, ℂ)) (z : G) :
    hermPart f z = (2 : ℂ)⁻¹ * (f z + (starRingEnd ℂ) (f (-z))) := rfl

omit [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
theorem hermPart'_apply (f : C(G, ℂ)) (z : G) :
    hermPart' f z = ((2 : ℂ) * Complex.I)⁻¹ * (f z - (starRingEnd ℂ) (f (-z))) := rfl

omit [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
theorem hermPart_hermitian (f : C(G, ℂ)) (z : G) :
    (starRingEnd ℂ) (hermPart f (-z)) = hermPart f z := by
  rw [hermPart_apply, hermPart_apply, neg_neg, map_mul, map_add, Complex.conj_conj]
  have h2 : (starRingEnd ℂ) ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [map_inv₀, map_ofNat]
  rw [h2]
  ring

omit [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
theorem hermPart'_hermitian (f : C(G, ℂ)) (z : G) :
    (starRingEnd ℂ) (hermPart' f (-z)) = hermPart' f z := by
  rw [hermPart'_apply, hermPart'_apply, neg_neg, map_mul, map_sub, Complex.conj_conj, map_inv₀]
  have hI : (starRingEnd ℂ) ((2 : ℂ) * Complex.I) = -((2 : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_I, map_ofNat]
    ring
  rw [hI, inv_neg]
  ring

omit [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
theorem eq_hermPart_add (f : C(G, ℂ)) : f = hermPart f + Complex.I • hermPart' f := by
  ext z
  rw [ContinuousMap.add_apply, ContinuousMap.smul_apply, hermPart_apply, hermPart'_apply,
    smul_eq_mul]
  have hI : Complex.I * ((2 : ℂ) * Complex.I)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [mul_inv, mul_comm ((2 : ℂ)⁻¹) (Complex.I⁻¹), ← mul_assoc,
      mul_inv_cancel₀ Complex.I_ne_zero, one_mul]
  rw [← mul_assoc, hI]
  ring

omit [T2Space G] in
/-- **A vector orthogonal to every Hermitian continuous function vanishes.** -/
theorem eq_zero_of_inner_hermitian {v : Lp ℂ 2 (haarProb G)}
    (h : ∀ f : C(G, ℂ), (∀ z, (starRingEnd ℂ) (f (-z)) = f z) →
      inner ℂ v (ContinuousMap.toLp 2 (haarProb G) ℂ f) = 0) : v = 0 := by
  refine eq_zero_of_inner_toLp_eq_zero fun f => ?_
  have hsplit : ContinuousMap.toLp 2 (haarProb G) ℂ f
      = ContinuousMap.toLp 2 (haarProb G) ℂ (hermPart f)
        + Complex.I • ContinuousMap.toLp 2 (haarProb G) ℂ (hermPart' f) := by
    rw [← map_smul, ← map_add, ← eq_hermPart_add]
  rw [hsplit, inner_add_right, inner_smul_right,
    h (hermPart f) (hermPart_hermitian f), h (hermPart' f) (hermPart'_hermitian f)]
  ring

variable (k : G → ℂ) (hk : Continuous k) {C : ℝ} (hC : ∀ z, ‖k z‖ ≤ C)

omit [T2Space G] in
include hk hC in
/-- If a Hermitian convolution kills a vector, the vector is orthogonal to the kernel. -/
theorem inner_toLp_eq_zero_of_convOp_eq_zero
    (herm : ∀ z : G, (starRingEnd ℂ) (k (-z)) = k z)
    {v : Lp ℂ 2 (haarProb G)} (hv : convOp k hk hC v = 0) :
    inner ℂ v (ContinuousMap.toLp 2 (haarProb G) ℂ ⟨k, hk⟩) = 0 := by
  -- the continuous representative of `k * v` vanishes identically
  have hzeroae : (fun x : G => convC k hk hC v x) =ᵐ[haarProb G] fun _ : G => (0 : ℂ) := by
    have h1 := convOp_coeFn k hk hC v
    have h2 : (fun x => ((convOp k hk hC v : Lp ℂ 2 (haarProb G)) : G → ℂ) x)
        =ᵐ[haarProb G] fun _ => (0 : ℂ) := by
      rw [hv]
      filter_upwards [Lp.coeFn_zero ℂ 2 (haarProb G)] with x hx
      rw [hx]
      rfl
    filter_upwards [h1, h2] with x hx1 hx2
    rw [← hx1, hx2]
  have hcont : Continuous fun x : G => convC k hk hC v x := (convC k hk hC v).continuous
  have hzero : (fun x : G => convC k hk hC v x) = fun _ : G => (0 : ℂ) :=
    (hcont.ae_eq_iff_eq (haarProb G) continuous_const).mp hzeroae
  have hzero0 : ∫ y, (v y) * k (0 - y) ∂(haarProb G) = 0 := congrFun hzero 0
  -- conjugating turns it into the inner product
  have hinner : inner ℂ v (ContinuousMap.toLp 2 (haarProb G) ℂ ⟨k, hk⟩)
      = ∫ y, (starRingEnd ℂ) (v y) * k y ∂(haarProb G) := by
    rw [inner_lp_eq]
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (haarProb G)
      (⟨k, hk⟩ : C(G, ℂ))] with y hy
    rw [hy]
    rfl
  rw [hinner]
  have hconj : (starRingEnd ℂ) (∫ y, (v y) * k (0 - y) ∂(haarProb G))
      = ∫ y, (starRingEnd ℂ) (v y) * k y ∂(haarProb G) := by
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (starRingEnd ℂ) ((v : G → ℂ) y * k (0 - y))
        = (starRingEnd ℂ) ((v : G → ℂ) y) * k y
    rw [map_mul]
    congr 1
    have hy0 : (0 : G) - y = -y := by abel
    rw [hy0, herm y]
  rw [← hconj, hzero0, map_zero]

end

end CompactAbelian

end GaloisForLFunctions
