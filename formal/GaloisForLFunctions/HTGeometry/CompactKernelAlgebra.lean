import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# The algebra of compactly supported continuous kernels on `ℝ × ℝ`

Continuous compactly supported kernels `k(x, y)` form a non-unital `*`-algebra under composition
`(k₁ k₂)(x, z) = ∫ k₁(x, y) k₂(y, z) dy` and the adjoint `k*(x, y) = conj k(y, x)`:

* composition stays continuous (parametric integral over the compact `y`-shadow of `supp k₁`) and
  compactly supported (inside `π₁(supp k₁) × π₂(supp k₂)`);
* associativity is Fubini for the compactly supported continuous integrand
  `(y, w) ↦ k₁(x, w) k₂(w, y) k₃(y, z)`;
* `(k₁ k₂)* = k₂* k₁*` is conjugation under the integral.

Under `F(s, x) = k(x, x - s)` this is the twisted convolution algebra of the translation action of
`ℝ` on `C₀(ℝ)`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped CompactlySupported

noncomputable section

namespace GaloisForLFunctions.HTGeometry

namespace KernelCore

/-- The first-coordinate shadow of the support of a compactly supported kernel. -/
def fstSupp (k : C_c(ℝ × ℝ, ℂ)) : Set ℝ := Prod.fst '' tsupport k

/-- The second-coordinate shadow of the support. -/
def sndSupp (k : C_c(ℝ × ℝ, ℂ)) : Set ℝ := Prod.snd '' tsupport k

theorem isCompact_fstSupp (k : C_c(ℝ × ℝ, ℂ)) : IsCompact (fstSupp k) :=
  k.hasCompactSupport.isCompact.image continuous_fst

theorem isCompact_sndSupp (k : C_c(ℝ × ℝ, ℂ)) : IsCompact (sndSupp k) :=
  k.hasCompactSupport.isCompact.image continuous_snd

theorem eq_zero_of_snd_notMem (k : C_c(ℝ × ℝ, ℂ)) {x y : ℝ} (hy : y ∉ sndSupp k) :
    k (x, y) = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hy ⟨(x, y), h, rfl⟩

theorem eq_zero_of_fst_notMem (k : C_c(ℝ × ℝ, ℂ)) {x y : ℝ} (hx : x ∉ fstSupp k) :
    k (x, y) = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx ⟨(x, y), h, rfl⟩

/-- The integrand `y ↦ k₁(x, y) k₂(y, z)` of a kernel composition. -/
theorem integrable_comp_integrand (k₁ k₂ : C_c(ℝ × ℝ, ℂ)) (x z : ℝ) :
    Integrable (fun y => k₁ (x, y) * k₂ (y, z)) := by
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  refine HasCompactSupport.intro (isCompact_sndSupp k₁) fun y hy => ?_
  rw [eq_zero_of_snd_notMem k₁ hy, zero_mul]

/-- **Kernel composition** `(k₁ k₂)(x, z) = ∫ k₁(x, y) k₂(y, z) dy`. -/
def comp (k₁ k₂ : C_c(ℝ × ℝ, ℂ)) : C_c(ℝ × ℝ, ℂ) where
  toFun p := ∫ y, k₁ (p.1, y) * k₂ (y, p.2)
  continuous_toFun := by
    have h : (fun p : ℝ × ℝ => ∫ y, k₁ (p.1, y) * k₂ (y, p.2)) =
        fun p => ∫ y in sndSupp k₁, k₁ (p.1, y) * k₂ (y, p.2) := by
      funext p
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
        rw [eq_zero_of_snd_notMem k₁ hy, zero_mul]).symm
    rw [h]
    exact continuous_parametric_integral_of_continuous (by fun_prop) (isCompact_sndSupp k₁)
  hasCompactSupport' := by
    refine HasCompactSupport.intro ((isCompact_fstSupp k₁).prod (isCompact_sndSupp k₂)) ?_
    rintro ⟨x, z⟩ hxz
    simp only [mem_prod, not_and_or] at hxz
    rcases hxz with hx | hz
    · simp [eq_zero_of_fst_notMem k₁ hx]
    · simp [eq_zero_of_snd_notMem k₂ hz]

theorem comp_apply (k₁ k₂ : C_c(ℝ × ℝ, ℂ)) (x z : ℝ) :
    comp k₁ k₂ (x, z) = ∫ y, k₁ (x, y) * k₂ (y, z) := rfl

/-- The adjoint kernel `k*(x, y) = conj k(y, x)`. -/
def adj (k : C_c(ℝ × ℝ, ℂ)) : C_c(ℝ × ℝ, ℂ) where
  toFun p := star (k (p.2, p.1))
  continuous_toFun := by fun_prop
  hasCompactSupport' := by
    refine HasCompactSupport.intro (k.hasCompactSupport.isCompact.image continuous_swap) ?_
    rintro ⟨x, y⟩ hxy
    have : (y, x) ∉ tsupport k := fun h => hxy ⟨(y, x), h, rfl⟩
    simp [image_eq_zero_of_notMem_tsupport this]

theorem adj_apply (k : C_c(ℝ × ℝ, ℂ)) (x y : ℝ) : adj k (x, y) = star (k (y, x)) := rfl

theorem comp_add_left (k₁ k₂ k₃ : C_c(ℝ × ℝ, ℂ)) :
    comp (k₁ + k₂) k₃ = comp k₁ k₃ + comp k₂ k₃ := by
  ext ⟨x, z⟩
  simp only [comp_apply, CompactlySupportedContinuousMap.coe_add, Pi.add_apply, add_mul]
  exact integral_add (integrable_comp_integrand k₁ k₃ x z) (integrable_comp_integrand k₂ k₃ x z)

theorem comp_add_right (k₁ k₂ k₃ : C_c(ℝ × ℝ, ℂ)) :
    comp k₁ (k₂ + k₃) = comp k₁ k₂ + comp k₁ k₃ := by
  ext ⟨x, z⟩
  simp only [comp_apply, CompactlySupportedContinuousMap.coe_add, Pi.add_apply, mul_add]
  exact integral_add (integrable_comp_integrand k₁ k₂ x z) (integrable_comp_integrand k₁ k₃ x z)

theorem comp_smul_left (c : ℂ) (k₁ k₂ : C_c(ℝ × ℝ, ℂ)) :
    comp (c • k₁) k₂ = c • comp k₁ k₂ := by
  ext ⟨x, z⟩
  simp only [comp_apply, CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul,
    mul_assoc]
  exact integral_const_mul c _

theorem comp_smul_right (c : ℂ) (k₁ k₂ : C_c(ℝ × ℝ, ℂ)) :
    comp k₁ (c • k₂) = c • comp k₁ k₂ := by
  ext ⟨x, z⟩
  simp only [comp_apply, CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul,
    mul_left_comm _ c]
  exact integral_const_mul c _

theorem comp_assoc (k₁ k₂ k₃ : C_c(ℝ × ℝ, ℂ)) :
    comp (comp k₁ k₂) k₃ = comp k₁ (comp k₂ k₃) := by
  ext ⟨x, z⟩
  simp only [comp_apply]
  have hL : (fun y => (∫ w, k₁ (x, w) * k₂ (w, y)) * k₃ (y, z)) =
      fun y => ∫ w, k₁ (x, w) * k₂ (w, y) * k₃ (y, z) := by
    funext y
    exact (integral_mul_const _ _).symm
  have hR : (fun w => k₁ (x, w) * ∫ y, k₂ (w, y) * k₃ (y, z)) =
      fun w => ∫ y, k₁ (x, w) * k₂ (w, y) * k₃ (y, z) := by
    funext w
    rw [← integral_const_mul]
    simp only [mul_assoc]
  rw [hL, hR]
  refine integral_integral_swap ?_
  rw [← Measure.volume_eq_prod]
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  refine HasCompactSupport.intro ((isCompact_fstSupp k₃).prod (isCompact_sndSupp k₁)) ?_
  rintro ⟨y, w⟩ hyw
  simp only [mem_prod, not_and_or] at hyw
  rcases hyw with hy | hw
  · simp [Function.uncurry, eq_zero_of_fst_notMem k₃ hy]
  · simp [Function.uncurry, eq_zero_of_snd_notMem k₁ hw]

theorem adj_adj (k : C_c(ℝ × ℝ, ℂ)) : adj (adj k) = k := by
  ext ⟨x, y⟩
  simp [adj_apply]

theorem adj_add (k₁ k₂ : C_c(ℝ × ℝ, ℂ)) : adj (k₁ + k₂) = adj k₁ + adj k₂ := by
  ext ⟨x, y⟩
  simp [adj_apply]

theorem adj_smul (c : ℂ) (k : C_c(ℝ × ℝ, ℂ)) : adj (c • k) = star c • adj k := by
  ext ⟨x, y⟩
  simp [adj_apply]

theorem adj_comp (k₁ k₂ : C_c(ℝ × ℝ, ℂ)) : adj (comp k₁ k₂) = comp (adj k₂) (adj k₁) := by
  ext ⟨x, z⟩
  simp only [adj_apply, comp_apply]
  change (starRingEnd ℂ) (∫ y, k₁ (z, y) * k₂ (y, x)) =
    ∫ y, (starRingEnd ℂ) (k₂ (y, x)) * (starRingEnd ℂ) (k₁ (z, y))
  rw [← integral_conj]
  congr 1
  funext y
  rw [map_mul, mul_comm]

end KernelCore

/-- The **kernel algebra**: continuous compactly supported kernels on `ℝ × ℝ` with composition
`(k₁ k₂)(x, z) = ∫ k₁(x, y) k₂(y, z) dy` and adjoint `k*(x, y) = conj k(y, x)`. -/
def KernelAlg : Type := C_c(ℝ × ℝ, ℂ)

instance : AddCommGroup KernelAlg := inferInstanceAs (AddCommGroup C_c(ℝ × ℝ, ℂ))
instance : Module ℂ KernelAlg := inferInstanceAs (Module ℂ C_c(ℝ × ℝ, ℂ))
instance : Mul KernelAlg := ⟨KernelCore.comp⟩
instance : Star KernelAlg := ⟨KernelCore.adj⟩

namespace KernelAlg

/-- The kernel function of an element. -/
def toFun (k : KernelAlg) : ℝ × ℝ → ℂ := ⇑(show C_c(ℝ × ℝ, ℂ) from k)

/-- An element from a compactly supported continuous kernel. -/
def ofCc (k : C_c(ℝ × ℝ, ℂ)) : KernelAlg := k

theorem mul_apply (k₁ k₂ : KernelAlg) (x z : ℝ) :
    (k₁ * k₂).toFun (x, z) = ∫ y, k₁.toFun (x, y) * k₂.toFun (y, z) := rfl

theorem star_apply (k : KernelAlg) (x y : ℝ) : (star k).toFun (x, y) = star (k.toFun (y, x)) :=
  rfl

theorem add_apply (k₁ k₂ : KernelAlg) (p : ℝ × ℝ) :
    (k₁ + k₂).toFun p = k₁.toFun p + k₂.toFun p := rfl

theorem smul_apply (c : ℂ) (k : KernelAlg) (p : ℝ × ℝ) : (c • k).toFun p = c * k.toFun p := rfl

theorem zero_apply (p : ℝ × ℝ) : (0 : KernelAlg).toFun p = 0 := rfl

theorem sub_apply (k₁ k₂ : KernelAlg) (p : ℝ × ℝ) :
    (k₁ - k₂).toFun p = k₁.toFun p - k₂.toFun p := rfl

theorem ext {k₁ k₂ : KernelAlg} (h : ∀ p, k₁.toFun p = k₂.toFun p) : k₁ = k₂ :=
  CompactlySupportedContinuousMap.ext h

theorem continuous_toFun (k : KernelAlg) : Continuous k.toFun :=
  (k : C_c(ℝ × ℝ, ℂ)).continuous

theorem hasCompactSupport_toFun (k : KernelAlg) : HasCompactSupport k.toFun :=
  (k : C_c(ℝ × ℝ, ℂ)).hasCompactSupport

end KernelAlg

instance : NonUnitalRing KernelAlg where
  left_distrib := KernelCore.comp_add_right
  right_distrib := KernelCore.comp_add_left
  zero_mul k := by
    have := KernelCore.comp_smul_left 0 (0 : C_c(ℝ × ℝ, ℂ)) k
    simp only [zero_smul] at this
    exact this
  mul_zero k := by
    have := KernelCore.comp_smul_right 0 k (0 : C_c(ℝ × ℝ, ℂ))
    simp only [zero_smul] at this
    exact this
  mul_assoc := KernelCore.comp_assoc

instance : StarRing KernelAlg where
  star_involutive := KernelCore.adj_adj
  star_mul := KernelCore.adj_comp
  star_add := KernelCore.adj_add

instance : IsScalarTower ℂ KernelAlg KernelAlg := ⟨fun c x y => KernelCore.comp_smul_left c x y⟩

instance : SMulCommClass ℂ KernelAlg KernelAlg :=
  ⟨fun c x y => (KernelCore.comp_smul_right c x y).symm⟩

instance : StarModule ℂ KernelAlg := ⟨fun c k => KernelCore.adj_smul c k⟩


end GaloisForLFunctions.HTGeometry
