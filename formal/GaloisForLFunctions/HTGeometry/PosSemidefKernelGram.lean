/-
# Gram realization of a scalar positive semidefinite kernel

Every positive semidefinite kernel `K : X → X → ℂ` is the Gram kernel of a family of vectors in a
complex Hilbert space.  The space is the completion of the finitely supported coefficient space
carrying the semi-inner product `⟪c, d⟫ = ∑ conj (c y) * d x * K x y`, and the vectors are the
images of the point masses.

This is the scalar case of Moore's theorem; it is separated out here because the whole downstream
use only needs the vectors and their inner products, not the function-space picture.
-/
import Mathlib

noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*}

/-- A scalar positive semidefinite kernel on an arbitrary index type. -/
structure IsPSDKernel (K : X → X → ℂ) : Prop where
  /-- The kernel is Hermitian. -/
  conj_symm : ∀ x y, conj (K x y) = K y x
  /-- Every finitely supported coefficient vector has nonnegative energy. -/
  nonneg : ∀ c : X →₀ ℂ,
    0 ≤ (c.sum fun y a => c.sum fun x b => conj a * b * K x y).re

/-! ## The kernel semi-inner product on coefficient vectors -/

variable {K : X → X → ℂ}

/-- The kernel semi-inner product on finitely supported coefficient vectors. -/
def kernelForm (K : X → X → ℂ) (f g : X →₀ ℂ) : ℂ :=
  f.sum fun y a => g.sum fun x b => conj a * b * K x y

theorem kernelForm_single (K : X → X → ℂ) (x y : X) :
    kernelForm K (Finsupp.single y 1) (Finsupp.single x 1) = K x y := by
  simp [kernelForm, Finsupp.sum_single_index]

theorem kernelForm_conj_symm (hK : IsPSDKernel K) (f g : X →₀ ℂ) :
    conj (kernelForm K g f) = kernelForm K f g := by
  rw [kernelForm, kernelForm, map_finsuppSum]
  simp only [map_finsuppSum, map_mul, Complex.conj_conj]
  rw [Finsupp.sum_comm]
  refine Finsupp.sum_congr (fun y _ => Finsupp.sum_congr (fun x _ => ?_))
  rw [hK.conj_symm]
  ring

theorem kernelForm_add_left (K : X → X → ℂ) (f g h : X →₀ ℂ) :
    kernelForm K (f + g) h = kernelForm K f h + kernelForm K g h := by
  rw [kernelForm, kernelForm, kernelForm, Finsupp.sum_add_index']
  · intro x
    simp
  · intro x b₁ b₂
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr (fun z _ => ?_)
    simp only [map_add]
    ring

theorem kernelForm_smul_left (K : X → X → ℂ) (f g : X →₀ ℂ) (r : ℂ) :
    kernelForm K (r • f) g = conj r * kernelForm K f g := by
  rw [kernelForm, kernelForm, Finsupp.sum_smul_index']
  · rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr (fun y _ => ?_)
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr (fun x _ => ?_)
    simp only [map_mul, smul_eq_mul]
    ring
  · intro x
    simp

set_option linter.unusedVariables false in
/-- The finitely supported coefficient space carrying the kernel semi-inner product. -/
@[nolint unusedArguments]
def KernelPre (K : X → X → ℂ) : Type _ := X →₀ ℂ

namespace KernelPre

instance : AddCommGroup (KernelPre K) := inferInstanceAs (AddCommGroup (X →₀ ℂ))
instance : Module ℂ (KernelPre K) := inferInstanceAs (Module ℂ (X →₀ ℂ))

/-- The point mass at `x`, as an element of the coefficient space. -/
def single (K : X → X → ℂ) (x : X) : KernelPre K := (Finsupp.single x (1 : ℂ) : X →₀ ℂ)

variable [hfact : Fact (IsPSDKernel K)]

instance instCore : PreInnerProductSpace.Core ℂ (KernelPre K) where
  inner f g := kernelForm K f g
  conj_inner_symm f g := kernelForm_conj_symm hfact.out f g
  re_inner_nonneg f := hfact.out.nonneg f
  add_left f g h := kernelForm_add_left K f g h
  smul_left f g r := kernelForm_smul_left K f g r

instance instSeminormed : SeminormedAddCommGroup (KernelPre K) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

instance instInner : InnerProductSpace ℂ (KernelPre K) := .ofCore _

theorem inner_def (f g : KernelPre K) : ⟪f, g⟫_ℂ = kernelForm K f g := rfl

end KernelPre

/-- The Hilbert space realizing a positive semidefinite kernel as a Gram kernel. -/
abbrev KernelHilbert (K : X → X → ℂ) [Fact (IsPSDKernel K)] : Type _ :=
  UniformSpace.Completion (KernelPre K)

namespace KernelHilbert

variable [Fact (IsPSDKernel K)]

/-- The Gram vector attached to a point of the index type. -/
def vector (K : X → X → ℂ) [Fact (IsPSDKernel K)] (x : X) : KernelHilbert K :=
  ((KernelPre.single K x : KernelPre K) : UniformSpace.Completion (KernelPre K))

/-- **The Gram realization.**  The inner products of the Gram vectors are the kernel values. -/
theorem inner_vector (x y : X) :
    ⟪vector K y, vector K x⟫_ℂ = K x y := by
  rw [vector, vector, UniformSpace.Completion.inner_coe, KernelPre.inner_def]
  exact kernelForm_single K x y

end KernelHilbert

end GaloisForLFunctions.HTGeometry
