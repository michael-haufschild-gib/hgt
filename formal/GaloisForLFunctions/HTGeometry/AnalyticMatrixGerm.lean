import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.ThreeParticleLegsRing

/-!
# Matrices of analytic functions as matrices over the analytic germ domain

A matrix-valued analytic function on `U` is a matrix over the analytic germ subring of `U`, and
the passage respects sums, products, the tensor legs and germ differentiation.  Composing with the
fraction-field map gives a matrix over the meromorphic function field, where the Sutherland
argument lives.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher Matrix

noncomputable section

variable {U : Set ℂ} {m n p : Type*}

/-- A matrix-valued analytic function as a matrix over the analytic germ domain. -/
def analyticMatrixElement (A : ℂ → Matrix m n ℂ)
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun t => A t i j) U) : Matrix m n (analyticSubring U) :=
  fun i j => analyticFunctionElement (fun t => A t i j) (hA i j)

private theorem analyticFunctionElement_coe (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    ((analyticFunctionElement f hf : analyticSubring U) : Germ (𝓟 U) ℂ) =
      Germ.coeRingHom (𝓟 U) f := rfl

/-- Two analytic functions agreeing on `U` have the same germ element. -/
theorem analyticFunctionElement_congr {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) (h : ∀ z ∈ U, f z = g z) :
    analyticFunctionElement f hf = analyticFunctionElement g hg := by
  apply Subtype.ext
  change (↑f : Germ (𝓟 U) ℂ) = (↑g : Germ (𝓟 U) ℂ)
  rw [Germ.coe_eq]
  exact eventually_principal.mpr h

theorem analyticFunctionElement_mul_congr {f g h : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) (hh : AnalyticOnNhd ℂ h U)
    (hmul : ∀ z ∈ U, f z * g z = h z) :
    analyticFunctionElement f hf * analyticFunctionElement g hg = analyticFunctionElement h hh := by
  apply Subtype.ext
  show (↑f : Germ (𝓟 U) ℂ) * (↑g : Germ (𝓟 U) ℂ) = (↑h : Germ (𝓟 U) ℂ)
  rw [← Germ.coe_mul, Germ.coe_eq]
  exact eventually_principal.mpr fun z hz => hmul z hz

theorem analyticMatrixElement_congr {A B : ℂ → Matrix m n ℂ}
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun t => A t i j) U)
    (hB : ∀ i j, AnalyticOnNhd ℂ (fun t => B t i j) U)
    (h : ∀ z ∈ U, A z = B z) :
    analyticMatrixElement A hA = analyticMatrixElement B hB := by
  ext i j
  exact congrArg _ (analyticFunctionElement_congr (hA i j) (hB i j)
    fun z hz => by rw [h z hz])

theorem analyticMatrixElement_add {A B : ℂ → Matrix m n ℂ}
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun t => A t i j) U)
    (hB : ∀ i j, AnalyticOnNhd ℂ (fun t => B t i j) U)
    (hAB : ∀ i j, AnalyticOnNhd ℂ (fun t => (A t + B t) i j) U) :
    analyticMatrixElement (fun t => A t + B t) hAB =
      analyticMatrixElement A hA + analyticMatrixElement B hB := by
  ext i j
  change Germ.coeRingHom (𝓟 U) (fun t => A t i j + B t i j) = _
  have hfun : (fun t => A t i j + B t i j)
      = (fun t => A t i j) + (fun t => B t i j) := rfl
  rw [hfun, map_add]
  rfl

theorem analyticMatrixElement_sub {A B : ℂ → Matrix m n ℂ}
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun t => A t i j) U)
    (hB : ∀ i j, AnalyticOnNhd ℂ (fun t => B t i j) U)
    (hAB : ∀ i j, AnalyticOnNhd ℂ (fun t => (A t - B t) i j) U) :
    analyticMatrixElement (fun t => A t - B t) hAB =
      analyticMatrixElement A hA - analyticMatrixElement B hB := by
  ext i j
  change Germ.coeRingHom (𝓟 U) (fun t => A t i j - B t i j) = _
  have hfun : (fun t => A t i j - B t i j)
      = (fun t => A t i j) - (fun t => B t i j) := rfl
  rw [hfun, map_sub]
  rfl

theorem analyticMatrixElement_mul [Fintype n] [DecidableEq n] {A : ℂ → Matrix m n ℂ}
    {B : ℂ → Matrix n p ℂ}
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun t => A t i j) U)
    (hB : ∀ i j, AnalyticOnNhd ℂ (fun t => B t i j) U)
    (hAB : ∀ i j, AnalyticOnNhd ℂ (fun t => (A t * B t) i j) U) :
    analyticMatrixElement (fun t => A t * B t) hAB =
      analyticMatrixElement A hA * analyticMatrixElement B hB := by
  ext i j
  change Germ.coeRingHom (𝓟 U) (fun t => ∑ k : n, A t i k * B t k j) = _
  have hfun : (fun t => ∑ k : n, A t i k * B t k j)
      = ∑ k : n, fun t => A t i k * B t k j := by
    funext t
    simp
  rw [hfun, map_sum]
  rw [Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfun2 : (fun t => A t i k * B t k j)
      = (fun t => A t i k) * (fun t => B t k j) := rfl
  rw [hfun2, map_mul]
  rfl

/-- Entrywise analyticity of a matrix-valued function. -/
def MatAnalyticOn (U : Set ℂ) (A : ℂ → Matrix m n ℂ) : Prop :=
  ∀ i j, AnalyticOnNhd ℂ (fun t => A t i j) U

theorem MatAnalyticOn.add {A B : ℂ → Matrix m n ℂ} (hA : MatAnalyticOn U A)
    (hB : MatAnalyticOn U B) : MatAnalyticOn U (fun t => A t + B t) :=
  fun i j => (hA i j).add (hB i j)

theorem MatAnalyticOn.sub {A B : ℂ → Matrix m n ℂ} (hA : MatAnalyticOn U A)
    (hB : MatAnalyticOn U B) : MatAnalyticOn U (fun t => A t - B t) :=
  fun i j => (hA i j).sub (hB i j)

theorem MatAnalyticOn.mul [Fintype n] [DecidableEq n] {A : ℂ → Matrix m n ℂ}
    {B : ℂ → Matrix n p ℂ} (hA : MatAnalyticOn U A) (hB : MatAnalyticOn U B) :
    MatAnalyticOn U (fun t => A t * B t) := by
  intro i j
  have : (fun t => (A t * B t) i j) = fun t => ∑ k : n, A t i k * B t k j := by
    funext t
    rw [Matrix.mul_apply]
  rw [this]
  intro z hz
  have hfun : (fun t => ∑ k : n, A t i k * B t k j)
      = ∑ k : n, (fun t => A t i k) * (fun t => B t k j) := by
    funext t
    simp
  rw [hfun]
  exact Finset.analyticAt_sum _ fun k _ => ((hA i k) z hz).mul ((hB k j) z hz)

theorem MatAnalyticOn.const (C : Matrix m n ℂ) : MatAnalyticOn U (fun _ => C) :=
  fun _ _ => analyticOnNhd_const

theorem MatAnalyticOn.legLeft {κ : Type*} [DecidableEq κ]
    {A : ℂ → Matrix (κ × κ) (κ × κ) ℂ} (hA : MatAnalyticOn U A) :
    MatAnalyticOn U (fun t => HTGeometry.legLeft (A t)) := by
  intro i j
  exact (hA (i.1, i.2.1) (j.1, j.2.1)).mul analyticOnNhd_const

theorem MatAnalyticOn.legRight {κ : Type*} [DecidableEq κ]
    {A : ℂ → Matrix (κ × κ) (κ × κ) ℂ} (hA : MatAnalyticOn U A) :
    MatAnalyticOn U (fun t => HTGeometry.legRight (A t)) := by
  intro i j
  exact analyticOnNhd_const.mul (hA i.2 j.2)

/-- Evaluation of a germ over the principal filter of `U` at a point of `U`. -/
def germEvalAt (U : Set ℂ) (z : ℂ) (hz : z ∈ U) : Germ (𝓟 U) ℂ →+* ℂ where
  toFun := Quotient.lift (fun f : ℂ → ℂ => f z) (by
    intro f g h
    exact eventually_principal.mp h z hz)
  map_one' := rfl
  map_mul' := by
    intro f g
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    rfl
  map_zero' := rfl
  map_add' := by
    intro f g
    induction f using Quotient.inductionOn
    induction g using Quotient.inductionOn
    rfl

/-- Evaluation of an analytic germ at a point of its domain. -/
def analyticEvalAt (U : Set ℂ) (z : ℂ) (hz : z ∈ U) : analyticSubring U →+* ℂ :=
  (germEvalAt U z hz).comp (analyticSubring U).subtype

@[simp]
theorem analyticEvalAt_analyticFunctionElement (z : ℂ) (hz : z ∈ U) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) :
    analyticEvalAt U z hz (analyticFunctionElement f hf) = f z := rfl

theorem analyticMatrixElement_map_eval (z : ℂ) (hz : z ∈ U) (A : ℂ → Matrix m n ℂ)
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun t => A t i j) U) :
    (analyticMatrixElement A hA).map (analyticEvalAt U z hz) = A z := rfl

theorem analyticMatrixElement_legLeft {κ : Type*} [DecidableEq κ]
    {A : ℂ → Matrix (κ × κ) (κ × κ) ℂ}
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun t => A t i j) U)
    (hLA : ∀ i j, AnalyticOnNhd ℂ (fun t => legLeft (A t) i j) U) :
    analyticMatrixElement (fun t => legLeft (A t)) hLA =
      legLeft (analyticMatrixElement A hA) := by
  refine Matrix.ext fun i j => ?_
  show analyticFunctionElement (fun t => legLeft (A t) i j) (hLA i j) = _
  rw [legLeft_apply]
  by_cases h : i.2.2 = j.2.2
  · have h1 : ((1 : Matrix κ κ (analyticSubring U)) i.2.2 j.2.2) = 1 := by
      simp [Matrix.one_apply, h]
    rw [h1, mul_one]
    exact analyticFunctionElement_congr _ _ fun t _ => by
      simp [legLeft, Matrix.one_apply, h]
  · have h1 : ((1 : Matrix κ κ (analyticSubring U)) i.2.2 j.2.2) = 0 := by
      simp [h]
    rw [h1, mul_zero]
    apply Subtype.ext
    change (↑(fun t => legLeft (A t) i j) : Germ (𝓟 U) ℂ) = 0
    have hfun : (fun t => legLeft (A t) i j) = fun _ : ℂ => (0 : ℂ) := by
      funext t
      simp [legLeft, Matrix.one_apply, h]
    rw [hfun]
    rfl

theorem analyticMatrixElement_legRight {κ : Type*} [DecidableEq κ]
    {A : ℂ → Matrix (κ × κ) (κ × κ) ℂ}
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun t => A t i j) U)
    (hLA : ∀ i j, AnalyticOnNhd ℂ (fun t => legRight (A t) i j) U) :
    analyticMatrixElement (fun t => legRight (A t)) hLA =
      legRight (analyticMatrixElement A hA) := by
  refine Matrix.ext fun i j => ?_
  show analyticFunctionElement (fun t => legRight (A t) i j) (hLA i j) = _
  rw [legRight_apply]
  by_cases h : i.1 = j.1
  · have h1 : ((1 : Matrix κ κ (analyticSubring U)) i.1 j.1) = 1 := by
      simp [Matrix.one_apply, h]
    rw [h1, one_mul]
    exact analyticFunctionElement_congr _ _ fun t _ => by
      simp [legRight, Matrix.one_apply, h]
  · have h1 : ((1 : Matrix κ κ (analyticSubring U)) i.1 j.1) = 0 := by
      simp [h]
    rw [h1, zero_mul]
    apply Subtype.ext
    change (↑(fun t => legRight (A t) i j) : Germ (𝓟 U) ℂ) = 0
    have hfun : (fun t => legRight (A t) i j) = fun _ : ℂ => (0 : ℂ) := by
      funext t
      simp [legRight, Matrix.one_apply, h]
    rw [hfun]
    rfl

theorem analyticSubringDeriv_analyticFunctionElement (hUo : IsOpen U) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) :
    analyticSubringDeriv hUo (analyticFunctionElement f hf) =
      analyticFunctionElement (deriv f)
        (by simpa using analyticOnNhd_iteratedDeriv hf 1) := by
  have h := analyticSubringDeriv_analyticJetElement hUo f hf 0
  rw [analyticJetElement_zero] at h
  rw [h]
  show analyticJetElement f hf 1 = _
  apply Subtype.ext
  change ((iteratedDeriv 1 f : ℂ → ℂ) : Germ (𝓟 U) ℂ) = ((deriv f : ℂ → ℂ) : Germ (𝓟 U) ℂ)
  rw [iteratedDeriv_one]

/-- Germ differentiation of a matrix of analytic germs is the entrywise derivative. -/
theorem analyticMatrixElement_deriv (hUo : IsOpen U) {A B : ℂ → Matrix m n ℂ}
    (hA : ∀ i j, AnalyticOnNhd ℂ (fun t => A t i j) U)
    (hB : ∀ i j, AnalyticOnNhd ℂ (fun t => B t i j) U)
    (hderiv : ∀ t i j, B t i j = deriv (fun s => A s i j) t) :
    analyticMatrixElement B hB =
      fun i j => analyticSubringDeriv hUo (analyticMatrixElement A hA i j) := by
  refine Matrix.ext fun i j => ?_
  show analyticFunctionElement (fun t => B t i j) (hB i j) =
    analyticSubringDeriv hUo (analyticFunctionElement (fun t => A t i j) (hA i j))
  rw [analyticSubringDeriv_analyticFunctionElement hUo]
  exact analyticFunctionElement_congr _ _ fun t _ => hderiv t i j

end

end GaloisForLFunctions.HTGeometry
