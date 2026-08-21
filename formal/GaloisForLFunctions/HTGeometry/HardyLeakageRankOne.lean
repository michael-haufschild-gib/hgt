import GaloisForLFunctions.HTGeometry.HardyDiskModelSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The rank-one Hardy leakage channel

Let `A` and `B` be single Blaschke factors of `H²(D)` with zeros `α` and `β`, and let
`φ = A · conj B` be the unimodular boundary symbol of the shifted quotient.  Its causal Toeplitz
compression is `T_φ = T_B^* T_A` (a product of two Blaschke multiplication operators, both
internal to `H²`), and the anti-causal *leakage* channel `L = P_- M_φ|_{H²}` satisfies
`L^*L = I - T_φ^* T_φ` because `|φ| = 1` on the circle.

This module computes that Schur defect exactly:

```text
‖f‖² - ‖T_B^*(T_A f)‖² = |A(β)|² ‖P_{K_B} f‖²,
```

where `K_B = H² ⊖ B H² = ℂ ∙ k_β` is the one-dimensional model space of `B`.  Hence the leakage
channel has **rank one** and **norm `|A(β)| = |b_α(β)|`**, the pseudo-hyperbolic distance between
the two Blaschke zeros.  In particular the norm tends to `0` as the two zeros merge, while the rank
stays one: norm continuity of the leakage family at the static endpoint is compatible with a
persistent off-line channel.

The half-line/upper-half-plane form of the same statement (`‖L‖ = ω/a` for the Blaschke pair
`b_{a±ω}`) is the Cayley image of this one; `norm_blaschkeFactor_cayley` evaluates the
pseudo-hyperbolic distance of the Cayley images and gives exactly `ω/a`.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {α β : ℂ}

/-- The Blaschke multiplication operator of a single factor. -/
def blaschkeMul (ha : ‖α‖ < 1) : HardyDisk →L[ℂ] HardyDisk :=
  hardyMul (singleBlaschke ha).toMultiplier

theorem norm_blaschkeMul (ha : ‖α‖ < 1) (x : HardyDisk) : ‖blaschkeMul ha x‖ = ‖x‖ :=
  norm_hardyMul_blaschke _ x

/-- The Blaschke multiplication operator, packaged as a linear isometry. -/
def blaschkeIsometry (ha : ‖α‖ < 1) : HardyDisk →ₗᵢ[ℂ] HardyDisk where
  toLinearMap := (blaschkeMul ha).toLinearMap
  norm_map' := norm_blaschkeMul ha

theorem inner_blaschkeMul (ha : ‖α‖ < 1) (x y : HardyDisk) :
    (inner ℂ (blaschkeMul ha x) (blaschkeMul ha y) : ℂ) = inner ℂ x y :=
  (blaschkeIsometry ha).inner_map_map x y

theorem adjoint_blaschkeMul_comp (ha : ‖α‖ < 1) (x : HardyDisk) :
    (ContinuousLinearMap.adjoint (blaschkeMul ha)) (blaschkeMul ha x) = x := by
  refine ext_inner_right ℂ fun y => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, inner_blaschkeMul]

/-- The model space of a single Blaschke factor. -/
def modelSpace (hb : ‖β‖ < 1) : Submodule ℂ HardyDisk := ℂ ∙ hardyKernel hb

instance instFiniteDimensionalModelSpace (hb : ‖β‖ < 1) :
    FiniteDimensional ℂ (modelSpace hb) :=
  FiniteDimensional.span_singleton ℂ _

theorem orthogonal_modelSpace (hb : ‖β‖ < 1) :
    (modelSpace hb)ᗮ = LinearMap.range ((blaschkeMul hb : HardyDisk →L[ℂ] HardyDisk) :
      HardyDisk →ₗ[ℂ] HardyDisk) :=
  (range_hardyMul_singleBlaschke hb).symm

/-- **The Blaschke multiplier acts on the model-space projection by its value at the zero.** -/
theorem starProjection_modelSpace_blaschkeMul (ha : ‖α‖ < 1) (hb : ‖β‖ < 1) (f : HardyDisk) :
    (modelSpace hb).starProjection (blaschkeMul ha f)
      = blaschkeFactor α β • (modelSpace hb).starProjection f := by
  show (ℂ ∙ hardyKernel hb).starProjection (blaschkeMul ha f)
      = blaschkeFactor α β • (ℂ ∙ hardyKernel hb).starProjection f
  rw [Submodule.starProjection_singleton ℂ, Submodule.starProjection_singleton ℂ]
  have hval : (inner ℂ (hardyKernel hb) (blaschkeMul ha f) : ℂ)
      = blaschkeFactor α β * (inner ℂ (hardyKernel hb) f : ℂ) := by
    rw [inner_hardyKernel hb, inner_hardyKernel hb, blaschkeMul, hardyFun_hardyMul _ _ hb]
    show (singleBlaschke ha).fn β * hardyFun f β = blaschkeFactor α β * hardyFun f β
    rw [singleBlaschke_fn]
  rw [hval, smul_smul]
  congr 1
  field_simp

/-- **The adjoint of a Blaschke multiplier loses exactly the model-space component.** -/
theorem norm_sq_adjoint_blaschkeMul (hb : ‖β‖ < 1) (g : HardyDisk) :
    ‖(ContinuousLinearMap.adjoint (blaschkeMul hb)) g‖ ^ 2
      = ‖g‖ ^ 2 - ‖(modelSpace hb).starProjection g‖ ^ 2 := by
  classical
  set K : Submodule ℂ HardyDisk := modelSpace hb with hK
  set u : HardyDisk := K.starProjection g with hu
  set v : HardyDisk := g - u with hv
  have hvmem : v ∈ Kᗮ := by
    rw [hv, hu]
    exact K.sub_starProjection_mem_orthogonal g
  obtain ⟨h, hh⟩ : ∃ h : HardyDisk, blaschkeMul hb h = v := by
    have := (orthogonal_modelSpace hb) ▸ hvmem
    simpa using this
  have humem : u ∈ K := by
    rw [hu]
    exact K.starProjection_apply_mem g
  have hadjU : (ContinuousLinearMap.adjoint (blaschkeMul hb)) u = 0 := by
    refine ext_inner_right ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
    have hy : blaschkeMul hb y ∈ Kᗮ := by
      rw [orthogonal_modelSpace hb]
      exact ⟨y, rfl⟩
    exact (K.mem_orthogonal _).1 hy u humem
  have hsplit : g = u + v := by rw [hv]; abel
  have hadj : (ContinuousLinearMap.adjoint (blaschkeMul hb)) g = h := by
    rw [hsplit, map_add, hadjU, zero_add, ← hh, adjoint_blaschkeMul_comp]
  have hperp : (inner ℂ u v : ℂ) = 0 := (K.mem_orthogonal _).1 hvmem u humem
  have hpyth : ‖g‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    rw [hsplit]
    simpa [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u v hperp
  have hnh : ‖h‖ = ‖v‖ := by rw [← hh, norm_blaschkeMul]
  rw [hadj, hnh, hpyth]
  ring

/-- **The exact Schur defect of the shifted-quotient Toeplitz compression.**  The leakage energy of
`f` is `|b_α(β)|²` times the squared model-space component of `f`. -/
theorem hardyLeakage_sq (ha : ‖α‖ < 1) (hb : ‖β‖ < 1) (f : HardyDisk) :
    ‖f‖ ^ 2
      - ‖(ContinuousLinearMap.adjoint (blaschkeMul hb)) (blaschkeMul ha f)‖ ^ 2
      = ‖blaschkeFactor α β‖ ^ 2 * ‖(modelSpace hb).starProjection f‖ ^ 2 := by
  rw [norm_sq_adjoint_blaschkeMul hb, norm_blaschkeMul ha,
    starProjection_modelSpace_blaschkeMul ha hb, norm_smul]
  ring

/-- **Rank one.**  The leakage energy vanishes exactly on the orthogonal complement of the
one-dimensional model space, whenever the two Blaschke zeros are distinct. -/
theorem hardyLeakage_eq_zero_iff (ha : ‖α‖ < 1) (hb : ‖β‖ < 1)
    (hne : blaschkeFactor α β ≠ 0) (f : HardyDisk) :
    ‖f‖ ^ 2
      - ‖(ContinuousLinearMap.adjoint (blaschkeMul hb)) (blaschkeMul ha f)‖ ^ 2 = 0
      ↔ (modelSpace hb).starProjection f = 0 := by
  rw [hardyLeakage_sq ha hb]
  constructor
  · intro h
    have hc : ‖blaschkeFactor α β‖ ^ 2 ≠ 0 := by positivity
    have := mul_eq_zero.1 h
    rcases this with h1 | h2
    · exact absurd h1 hc
    · exact norm_eq_zero.1 (sq_eq_zero_iff.1 h2)
  · intro h
    rw [h]
    simp

/-- **The leakage norm bound.** -/
theorem hardyLeakage_le (ha : ‖α‖ < 1) (hb : ‖β‖ < 1) (f : HardyDisk) :
    ‖f‖ ^ 2
      - ‖(ContinuousLinearMap.adjoint (blaschkeMul hb)) (blaschkeMul ha f)‖ ^ 2
      ≤ ‖blaschkeFactor α β‖ ^ 2 * ‖f‖ ^ 2 := by
  rw [hardyLeakage_sq ha hb]
  have hle : ‖(modelSpace hb).starProjection f‖ ≤ ‖f‖ :=
    (modelSpace hb).norm_starProjection_apply_le f
  have hnn : (0 : ℝ) ≤ ‖(modelSpace hb).starProjection f‖ := norm_nonneg _
  have h1 : ‖(modelSpace hb).starProjection f‖ ^ 2 ≤ ‖f‖ ^ 2 := by nlinarith
  have h0 : (0 : ℝ) ≤ ‖blaschkeFactor α β‖ ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left h1 h0

/-- **The bound is attained at the reproducing kernel**, so the leakage norm is exactly
`|b_α(β)|`. -/
theorem hardyLeakage_kernel (ha : ‖α‖ < 1) (hb : ‖β‖ < 1) :
    ‖hardyKernel hb‖ ^ 2
      - ‖(ContinuousLinearMap.adjoint (blaschkeMul hb)) (blaschkeMul ha (hardyKernel hb))‖ ^ 2
      = ‖blaschkeFactor α β‖ ^ 2 * ‖hardyKernel hb‖ ^ 2 := by
  rw [hardyLeakage_sq ha hb]
  congr 1
  have hmem : hardyKernel hb ∈ modelSpace hb := Submodule.mem_span_singleton_self _
  rw [Submodule.starProjection_eq_self_iff.2 hmem]

/-! ## The Cayley evaluation -/

/-- The Cayley image of the upper-half-plane point `i y`. -/
def cayleyPoint (y : ℝ) : ℂ := ((y - 1 : ℝ) : ℂ) / ((y + 1 : ℝ) : ℂ)

theorem norm_cayleyPoint_lt_one {y : ℝ} (hy : 0 < y) : ‖cayleyPoint y‖ < 1 := by
  rw [cayleyPoint, norm_div]
  have hpos : (0 : ℝ) < y + 1 := by linarith
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hpos, div_lt_one hpos]
  rcases le_total y 1 with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

/-- **The pseudo-hyperbolic distance of the Cayley images.**  For `0 < ω < a`, the Blaschke value
between the Cayley images of `i(a+ω)` and `i(a-ω)` has modulus `ω/a`: the upper-half-plane leakage
norm of the card. -/
theorem norm_blaschkeFactor_cayley {a omega : ℝ} (h0 : 0 < omega) (h1 : omega < a) :
    ‖blaschkeFactor (cayleyPoint (a + omega)) (cayleyPoint (a - omega))‖ = omega / a := by
  have ha : 0 < a := lt_trans h0 h1
  have hp : (0 : ℝ) < a + omega + 1 := by linarith
  have hm : (0 : ℝ) < a - omega + 1 := by linarith
  have hval : blaschkeFactor (cayleyPoint (a + omega)) (cayleyPoint (a - omega))
      = ((-(omega / a) : ℝ) : ℂ) := by
    rw [blaschkeFactor, cayleyPoint, cayleyPoint]
    rw [map_div₀, Complex.conj_ofReal, Complex.conj_ofReal]
    have hpc : ((a + omega + 1 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hp)
    have hmc : ((a - omega + 1 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hm)
    have hac : ((a : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
    field_simp
    push_cast
    ring
  rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]


/-- **The static endpoint.**  The leakage norm tends to zero as the transverse shift decreases to
zero, although the channel and its rank persist for every positive shift. -/
theorem tendsto_cayleyLeakageNorm_zero (a : ℝ) :
    Filter.Tendsto (fun omega : ℝ => omega / a) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hcont : Filter.Tendsto (fun omega : ℝ => omega / a) (nhds 0) (nhds (0 / a)) :=
    (continuous_id.div_const a).tendsto 0
  rw [zero_div] at hcont
  exact hcont.mono_left nhdsWithin_le_nhds

/-- **The crossing endpoint.**  The unit singularity sits at the moving zero-crossing `ω = a`, not
at the static boundary `ω = 0`. -/
theorem tendsto_cayleyLeakageNorm_one {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun omega : ℝ => omega / a) (nhdsWithin a (Set.Iio a)) (nhds 1) := by
  have hcont : Filter.Tendsto (fun omega : ℝ => omega / a) (nhds a) (nhds (a / a)) :=
    (continuous_id.div_const a).tendsto a
  rw [div_self (ne_of_gt ha)] at hcont
  exact hcont.mono_left nhdsWithin_le_nhds

end GaloisForLFunctions.HTGeometry

end
