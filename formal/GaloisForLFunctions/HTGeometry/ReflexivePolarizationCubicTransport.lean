import GaloisForLFunctions.HTGeometry.ReflexivePolarizationVectorSynchronization
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Cubic transport of synchronization tension

Along the fused source correction flow the channel residuals fall at the Hessian rate and the
Hessians themselves move at the third-response rate.  Differentiating the constitutive equations
therefore transports the synchronization tension by the third response alone: second response
creates the tension, third response moves it, and positive Hessian data determine no sign for
that motion.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ## Higher response forms -/

/-- Hessian form of a scalar potential. -/
def hessianForm (A : V → ℝ) (x : V) : V →L[ℝ] V →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ A) x

/-- Third response form of a scalar potential. -/
def thirdForm (A : V → ℝ) (x : V) : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (fderiv ℝ A)) x

theorem hasFDerivAt_fderiv {A : V → ℝ} (hA : ContDiff ℝ 3 A) (x : V) :
    HasFDerivAt (fderiv ℝ A) (hessianForm A x) x :=
  ((hA.fderiv_right (m := 2) (by norm_num)).differentiable
    (by norm_num)).differentiableAt.hasFDerivAt

theorem hasFDerivAt_hessianForm {A : V → ℝ} (hA : ContDiff ℝ 3 A) (x : V) :
    HasFDerivAt (hessianForm A) (thirdForm A x) x := by
  have h2 : ContDiff ℝ 2 (fderiv ℝ A) := hA.fderiv_right (m := 2) (by norm_num)
  have h1 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ A)) := h2.fderiv_right (m := 1) (by norm_num)
  exact (h1.differentiable (by norm_num)).differentiableAt.hasFDerivAt

/-- **The residual falls at the Hessian rate.** -/
theorem hasDerivAt_fderiv_curve {A : V → ℝ} (hA : ContDiff ℝ 3 A) {θ : ℝ → V} {v : V} {t : ℝ}
    (hθ : HasDerivAt θ v t) :
    HasDerivAt (fun s => fderiv ℝ A (θ s)) (hessianForm A (θ t) v) t :=
  (hasFDerivAt_fderiv hA (θ t)).comp_hasDerivAt t hθ

/-- **The Hessian moves at the third-response rate.** -/
theorem hasDerivAt_hessianForm_curve {A : V → ℝ} (hA : ContDiff ℝ 3 A) {θ : ℝ → V} {v : V} {t : ℝ}
    (hθ : HasDerivAt θ v t) :
    HasDerivAt (fun s => hessianForm A (θ s)) (thirdForm A (θ t) v) t := by
  have h : HasDerivAt (hessianForm A ∘ θ) (thirdForm A (θ t) v) t :=
    HasFDerivAt.comp_hasDerivAt (l := hessianForm A) (l' := thirdForm A (θ t)) t
      (hasFDerivAt_hessianForm hA (θ t)) hθ
  simpa [Function.comp_def] using h

/-! ## Positive definite forms and the dual equivalence -/

/-- The third response is symmetric in its last two slots: the pointwise Hessian symmetry is an
identity between two differentiable scalar fields, so their derivatives agree. -/
theorem thirdForm_symm_right {A : V → ℝ} (hA : ContDiff ℝ 3 A) (x u w z : V) :
    thirdForm A x u w z = thirdForm A x u z w := by
  have h1 : HasFDerivAt (hessianForm A) (thirdForm A x) x := hasFDerivAt_hessianForm hA x
  have step : ∀ a b : V, HasFDerivAt (fun y => hessianForm A y a b)
      (((thirdForm A x).flip a).flip b) x := by
    intro a b
    have k1 := h1.clm_apply (hasFDerivAt_const a x)
    have k2 := k1.clm_apply (hasFDerivAt_const b x)
    simpa using k2
  have hfun : (fun y => hessianForm A y w z) = fun y => hessianForm A y z w := by
    funext y
    exact ((hA.contDiffAt (x := y)).isSymmSndFDerivAt (n := 3) (by norm_num)) w z
  have e1 := step w z
  rw [hfun] at e1
  have huniq := e1.unique (step z w)
  have h3 := congrArg (fun ξ : V →L[ℝ] ℝ => ξ u) huniq
  simpa using h3


variable [FiniteDimensional ℝ V]

theorem finrank_dual_eq : Module.finrank ℝ (V →L[ℝ] ℝ) = Module.finrank ℝ V := by
  have h1 : Module.finrank ℝ (V →ₗ[ℝ] ℝ) = Module.finrank ℝ (V →L[ℝ] ℝ) :=
    LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := ℝ))
  rw [← h1]
  exact Subspace.dual_finrank_eq

theorem bijective_of_posDef (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ u : V, u ≠ 0 → 0 < B u u) :
    Function.Bijective (fun u => B u) := by
  have hinj : Function.Injective (fun u : V => B u) := by
    intro x y hxy
    by_contra hne
    have hd : x - y ≠ 0 := sub_ne_zero.2 hne
    have h0 : B (x - y) = 0 := by
      have hxy' : B x = B y := hxy
      rw [map_sub, hxy', sub_self]
    have hpos := hB (x - y) hd
    rw [h0] at hpos
    simp at hpos
  refine ⟨hinj, ?_⟩
  have hlin : Function.Injective (B.toLinearMap) := hinj
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank finrank_dual_eq.symm).1 hlin

/-- A positive definite continuous bilinear form identifies the space with its continuous dual. -/
def posDefDualEquiv (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ u : V, u ≠ 0 → 0 < B u u) :
    V ≃L[ℝ] (V →L[ℝ] ℝ) :=
  (LinearEquiv.ofBijective B.toLinearMap (bijective_of_posDef B hB)).toContinuousLinearEquiv

@[simp] theorem posDefDualEquiv_apply (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ u : V, u ≠ 0 → 0 < B u u) (u : V) : posDefDualEquiv B hB u = B u := rfl

/-! ## The reflexive formation flow -/

variable {ι : Type*} [Fintype ι]

/-- The reflexive formation flow of `ULF-LGPD-2`: `C³` channel potentials with positive definite
Hessians, fixed source-marked targets, and a curve whose velocity solves the fused constitutive
equation. -/
structure ReflexiveFlow (ι : Type*) [Fintype ι] (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] where
  /-- Channel potentials. -/
  potential : ι → V → ℝ
  /-- Each potential is three times continuously differentiable. -/
  smooth : ∀ i, ContDiff ℝ 3 (potential i)
  /-- Each Hessian is positive definite. -/
  posDef : ∀ i x, ∀ u : V, u ≠ 0 → 0 < hessianForm (potential i) x u u
  /-- Source-marked targets. -/
  target : ι → V →L[ℝ] ℝ
  /-- The source history. -/
  curve : ℝ → V
  /-- Its velocity. -/
  velocity : ℝ → V
  /-- The history is differentiable with the stated velocity. -/
  hasDeriv : ∀ t, HasDerivAt curve (velocity t) t
  /-- The fused constitutive equation. -/
  fused : ∀ t, fusedForm (fun i => hessianForm (potential i) (curve t)) (velocity t)
    = ∑ i, (target i - fderiv ℝ (potential i) (curve t))

namespace ReflexiveFlow

variable (F : ReflexiveFlow ι V) (i : ι) (t : ℝ)

/-- Channel residual covector. -/
def residual : V →L[ℝ] ℝ := F.target i - fderiv ℝ (F.potential i) (F.curve t)

/-- Channel Hessian form along the history. -/
def hess : V →L[ℝ] V →L[ℝ] ℝ := hessianForm (F.potential i) (F.curve t)

/-- Channel third response along the history. -/
def third : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ := thirdForm (F.potential i) (F.curve t)

/-- The dual identification supplied by the positive definite Hessian. -/
def hessEquiv : V ≃L[ℝ] (V →L[ℝ] ℝ) :=
  posDefDualEquiv (F.hess i t) (F.posDef i (F.curve t))

/-- Local correction velocity. -/
def localVel : V := (F.hessEquiv i t).symm (F.residual i t)

theorem hess_localVel : F.hess i t (F.localVel i t) = F.residual i t := by
  rw [localVel, hess]
  exact (F.hessEquiv i t).apply_symm_apply (F.residual i t)

/-- **The residual falls at the Hessian rate.** -/
theorem hasDerivAt_residual :
    HasDerivAt (fun s => F.residual i s) (-(F.hess i t (F.velocity t))) t := by
  have h := hasDerivAt_fderiv_curve (F.smooth i) (F.hasDeriv t)
  exact HasDerivAt.const_sub (F.target i) h

/-- **The Hessian moves at the third-response rate.** -/
theorem hasDerivAt_hess :
    HasDerivAt (fun s => F.hess i s) (F.third i t (F.velocity t)) t :=
  hasDerivAt_hessianForm_curve (F.smooth i) (F.hasDeriv t)

theorem coe_hessEquiv : ((F.hessEquiv i t : V ≃L[ℝ] (V →L[ℝ] ℝ)) : V →L[ℝ] (V →L[ℝ] ℝ))
    = F.hess i t := by
  ext u
  rfl

theorem localVel_eq_inverse :
    F.localVel i t = ContinuousLinearMap.inverse (F.hess i t) (F.residual i t) := by
  rw [localVel, ← F.coe_hessEquiv i t, ContinuousLinearMap.inverse_equiv]
  rfl

theorem differentiableAt_inverse_hess :
    DifferentiableAt ℝ (fun s => ContinuousLinearMap.inverse (F.hess i s)) t := by
  have hdiff : DifferentiableAt ℝ (fun s => F.hess i s) t :=
    ⟨_, (F.hasDerivAt_hess i t).hasFDerivAt⟩
  have hinv : ContDiffAt ℝ 1 ContinuousLinearMap.inverse (F.hess i t) := by
    have h := contDiffAt_map_inverse (𝕜 := ℝ) (n := 1) (F.hessEquiv i t)
    rwa [F.coe_hessEquiv i t] at h
  exact (hinv.differentiableAt (by norm_num)).comp t hdiff

theorem differentiableAt_localVel : DifferentiableAt ℝ (fun s => F.localVel i s) t := by
  have heq : (fun s => F.localVel i s)
      = fun s => ContinuousLinearMap.inverse (F.hess i s) (F.residual i s) := by
    funext s
    exact F.localVel_eq_inverse i s
  rw [heq]
  exact (F.differentiableAt_inverse_hess i t).clm_apply
    ⟨_, (F.hasDerivAt_residual i t).hasFDerivAt⟩

/-- The instantaneous rate of the local correction velocity. -/
def localAccel : V := deriv (fun s => F.localVel i s) t

theorem hasDerivAt_localVel : HasDerivAt (fun s => F.localVel i s) (F.localAccel i t) t :=
  (F.differentiableAt_localVel i t).hasDerivAt

/-- **Implicit differentiation of the channel constitutive equation.** -/
theorem third_add_hess_localAccel :
    F.third i t (F.velocity t) (F.localVel i t) + F.hess i t (F.localAccel i t)
      = -(F.hess i t (F.velocity t)) := by
  have hlhs : HasDerivAt (fun s => F.hess i s (F.localVel i s))
      (F.third i t (F.velocity t) (F.localVel i t) + F.hess i t (F.localAccel i t)) t :=
    (F.hasDerivAt_hess i t).clm_apply (F.hasDerivAt_localVel i t)
  have hrhs : HasDerivAt (fun s => F.hess i s (F.localVel i s))
      (-(F.hess i t (F.velocity t))) t := by
    have hres := F.hasDerivAt_residual i t
    refine hres.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => F.hess_localVel i s
  exact hlhs.unique hrhs

/-- **Cubic transport of one channel's correction power.** -/
theorem hasDerivAt_channelPower :
    HasDerivAt (fun s => F.hess i s (F.localVel i s) (F.localVel i s))
      (-(2 * F.hess i t (F.velocity t) (F.localVel i t))
        - F.third i t (F.velocity t) (F.localVel i t) (F.localVel i t)) t := by
  have h1 : HasDerivAt (fun s => F.hess i s (F.localVel i s))
      (F.third i t (F.velocity t) (F.localVel i t) + F.hess i t (F.localAccel i t)) t :=
    (F.hasDerivAt_hess i t).clm_apply (F.hasDerivAt_localVel i t)
  have h2 := h1.clm_apply (F.hasDerivAt_localVel i t)
  refine h2.congr_deriv ?_
  have hkey := F.third_add_hess_localAccel i t
  have hsplit : F.hess i t (F.localAccel i t) (F.localVel i t)
      = -(F.hess i t (F.velocity t) (F.localVel i t))
        - F.third i t (F.velocity t) (F.localVel i t) (F.localVel i t) := by
    have := congrArg (fun ξ : V →L[ℝ] ℝ => ξ (F.localVel i t)) hkey
    simp only [add_apply, neg_apply] at this
    linarith
  have hsymm : F.hess i t (F.localVel i t) (F.localAccel i t)
      = F.hess i t (F.localAccel i t) (F.localVel i t) := by
    have hs := ((F.smooth i).contDiffAt (x := F.curve t)).isSymmSndFDerivAt (n := 3) (by norm_num)
    exact hs (F.localVel i t) (F.localAccel i t)
  simp only [add_apply]
  rw [hsplit, hsymm, hsplit]
  ring

/-! ## The aggregate powers -/

variable (F : ReflexiveFlow ι V)

/-- Independent local correction power along the history. -/
def locPower (t : ℝ) : ℝ := ∑ i, F.hess i t (F.localVel i t) (F.localVel i t)

/-- Executable fused correction power along the history. -/
def fusPower (t : ℝ) : ℝ := fusedForm (fun i => F.hess i t) (F.velocity t) (F.velocity t)

/-- Synchronization tension along the history. -/
def tension (t : ℝ) : ℝ :=
  ∑ i, F.hess i t (F.localVel i t - F.velocity t) (F.localVel i t - F.velocity t)

theorem sum_hess_velocity_localVel (t : ℝ) :
    ∑ i, F.hess i t (F.velocity t) (F.localVel i t) = F.fusPower t := by
  have hsymm : ∀ i, F.hess i t (F.velocity t) (F.localVel i t)
      = F.hess i t (F.localVel i t) (F.velocity t) := by
    intro i
    have hs := ((F.smooth i).contDiffAt (x := F.curve t)).isSymmSndFDerivAt (n := 3) (by norm_num)
    exact hs (F.velocity t) (F.localVel i t)
  have hres : ∀ i, F.hess i t (F.localVel i t) (F.velocity t) = F.residual i t (F.velocity t) := by
    intro i
    rw [F.hess_localVel i t]
  rw [Finset.sum_congr rfl fun i _ => (hsymm i).trans (hres i)]
  have hfin : ∑ i, F.residual i t (F.velocity t) = (∑ i, F.residual i t) (F.velocity t) := by
    simp
  rw [hfin]
  simp only [residual]
  rw [← F.fused t, fusPower]
  rfl

/-- **Cubic transport of independent local power** (`RPS.13`). -/
theorem hasDerivAt_locPower (t : ℝ) :
    HasDerivAt (fun s => F.locPower s)
      (-2 * F.fusPower t - ∑ i, F.third i t (F.velocity t) (F.localVel i t) (F.localVel i t)) t := by
  have hraw := HasDerivAt.sum
    (A := fun (i : ι) (s : ℝ) => F.hess i s (F.localVel i s) (F.localVel i s))
    (u := (Finset.univ : Finset ι))
    (fun i (_ : i ∈ Finset.univ) => F.hasDerivAt_channelPower i t)
  have hsum : HasDerivAt (fun s => ∑ i, F.hess i s (F.localVel i s) (F.localVel i s))
      (∑ i, (-(2 * F.hess i t (F.velocity t) (F.localVel i t))
        - F.third i t (F.velocity t) (F.localVel i t) (F.localVel i t))) t := by
    refine hraw.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => by simp
  refine hsum.congr_deriv ?_
  have h1 : ∑ i, -(2 * F.hess i t (F.velocity t) (F.localVel i t))
      = -2 * ∑ i, F.hess i t (F.velocity t) (F.localVel i t) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_sub_distrib, h1, F.sum_hess_velocity_localVel t]

/-! ## The fused channel -/

variable [Nonempty ι]

/-- The fused polarization form along the history. -/
def fusedHess (t : ℝ) : V →L[ℝ] V →L[ℝ] ℝ := fusedForm (fun i => F.hess i t)

omit [Nonempty ι] in
theorem fusedHess_apply (t : ℝ) (u w : V) : F.fusedHess t u w = ∑ i, F.hess i t u w := by
  rw [fusedHess, fusedForm_apply]

omit [Nonempty ι] in
theorem fusedHess_symm (t : ℝ) (u w : V) : F.fusedHess t u w = F.fusedHess t w u := by
  rw [F.fusedHess_apply t, F.fusedHess_apply t]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs := ((F.smooth i).contDiffAt (x := F.curve t)).isSymmSndFDerivAt (n := 3) (by norm_num)
  exact hs u w

theorem fusedHess_posDef (t : ℝ) : ∀ u : V, u ≠ 0 → 0 < F.fusedHess t u u := by
  intro u hu
  rw [F.fusedHess_apply t]
  exact Finset.sum_pos (fun i _ => F.posDef i (F.curve t) u hu) Finset.univ_nonempty

/-- The dual identification supplied by the fused Hessian. -/
def fusedEquiv (t : ℝ) : V ≃L[ℝ] (V →L[ℝ] ℝ) :=
  posDefDualEquiv (F.fusedHess t) (F.fusedHess_posDef t)

theorem coe_fusedEquiv (t : ℝ) :
    ((F.fusedEquiv t : V ≃L[ℝ] (V →L[ℝ] ℝ)) : V →L[ℝ] (V →L[ℝ] ℝ)) = F.fusedHess t := by
  ext u
  rfl

omit [Nonempty ι] in
theorem fusedHess_velocity (t : ℝ) : F.fusedHess t (F.velocity t) = ∑ i, F.residual i t := by
  rw [fusedHess]
  simp only [residual]
  exact F.fused t

/-- The fused velocity written through the dual identification. -/
def fusedVel (t : ℝ) : V := (F.fusedEquiv t).symm (∑ i, F.residual i t)

theorem velocity_eq_fusedVel (t : ℝ) : F.velocity t = F.fusedVel t := by
  rw [fusedVel, ← F.fusedHess_velocity t]
  have hco : (F.fusedEquiv t) (F.velocity t) = F.fusedHess t (F.velocity t) := rfl
  rw [← hco, (F.fusedEquiv t).symm_apply_apply]

theorem fusedVel_eq_inverse (t : ℝ) :
    F.fusedVel t = ContinuousLinearMap.inverse (F.fusedHess t) (∑ i, F.residual i t) := by
  rw [fusedVel, ← F.coe_fusedEquiv t, ContinuousLinearMap.inverse_equiv]
  rfl

omit [Nonempty ι] in
theorem hasDerivAt_fusedHess (t : ℝ) :
    HasDerivAt (fun s => F.fusedHess s) (∑ i, F.third i t (F.velocity t)) t := by
  have hraw := HasDerivAt.sum
    (A := fun (i : ι) (s : ℝ) => F.hess i s)
    (u := (Finset.univ : Finset ι))
    (fun i (_ : i ∈ Finset.univ) => F.hasDerivAt_hess i t)
  refine hraw.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall fun s => ?_
  refine ContinuousLinearMap.ext fun u => ?_
  simp [fusedHess, fusedForm]

omit [Nonempty ι] in
theorem hasDerivAt_sum_residual (t : ℝ) :
    HasDerivAt (fun s => ∑ i, F.residual i s) (-(F.fusedHess t (F.velocity t))) t := by
  have hraw := HasDerivAt.sum
    (A := fun (i : ι) (s : ℝ) => F.residual i s)
    (u := (Finset.univ : Finset ι))
    (fun i (_ : i ∈ Finset.univ) => F.hasDerivAt_residual i t)
  have hsum : HasDerivAt (fun s => ∑ i, F.residual i s)
      (∑ i, -(F.hess i t (F.velocity t))) t := by
    refine hraw.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => by simp
  refine hsum.congr_deriv ?_
  refine ContinuousLinearMap.ext fun u => ?_
  simp [F.fusedHess_apply t]

theorem differentiableAt_velocity (t : ℝ) : DifferentiableAt ℝ F.velocity t := by
  have heq : F.velocity
      = fun s => ContinuousLinearMap.inverse (F.fusedHess s) (∑ i, F.residual i s) := by
    funext s
    rw [F.velocity_eq_fusedVel s, F.fusedVel_eq_inverse s]
  rw [heq]
  have hinv : ContDiffAt ℝ 1 ContinuousLinearMap.inverse (F.fusedHess t) := by
    have h := contDiffAt_map_inverse (𝕜 := ℝ) (n := 1) (F.fusedEquiv t)
    rwa [F.coe_fusedEquiv t] at h
  have hdiff : DifferentiableAt ℝ (fun s => F.fusedHess s) t :=
    ⟨_, (F.hasDerivAt_fusedHess t).hasFDerivAt⟩
  exact ((hinv.differentiableAt (by norm_num)).comp t hdiff).clm_apply
    ⟨_, (F.hasDerivAt_sum_residual t).hasFDerivAt⟩

/-- The instantaneous rate of the fused correction velocity. -/
def accel (t : ℝ) : V := deriv F.velocity t

theorem hasDerivAt_velocity (t : ℝ) : HasDerivAt F.velocity (F.accel t) t :=
  (F.differentiableAt_velocity t).hasDerivAt

/-- **Implicit differentiation of the fused constitutive equation.** -/
theorem sumThird_add_fusedHess_accel (t : ℝ) :
    (∑ i, F.third i t (F.velocity t)) (F.velocity t) + F.fusedHess t (F.accel t)
      = -(F.fusedHess t (F.velocity t)) := by
  have hlhs : HasDerivAt (fun s => F.fusedHess s (F.velocity s))
      ((∑ i, F.third i t (F.velocity t)) (F.velocity t) + F.fusedHess t (F.accel t)) t :=
    (F.hasDerivAt_fusedHess t).clm_apply (F.hasDerivAt_velocity t)
  have hrhs : HasDerivAt (fun s => F.fusedHess s (F.velocity s))
      (-(F.fusedHess t (F.velocity t))) t := by
    refine (F.hasDerivAt_sum_residual t).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => F.fusedHess_velocity s
  exact hlhs.unique hrhs

/-- **Cubic transport of the executable fused power** (`RPS.14`). -/
theorem hasDerivAt_fusPower (t : ℝ) :
    HasDerivAt (fun s => F.fusPower s)
      (-2 * F.fusPower t
        - (∑ i, F.third i t (F.velocity t)) (F.velocity t) (F.velocity t)) t := by
  have h1 : HasDerivAt (fun s => F.fusedHess s (F.velocity s))
      ((∑ i, F.third i t (F.velocity t)) (F.velocity t) + F.fusedHess t (F.accel t)) t :=
    (F.hasDerivAt_fusedHess t).clm_apply (F.hasDerivAt_velocity t)
  have h2 := h1.clm_apply (F.hasDerivAt_velocity t)
  have hfp : (fun s => F.fusedHess s (F.velocity s) (F.velocity s)) = fun s => F.fusPower s := by
    funext s
    rw [fusPower, fusedHess]
  rw [hfp] at h2
  refine h2.congr_deriv ?_
  have hkey := F.sumThird_add_fusedHess_accel t
  have hsplit : F.fusedHess t (F.accel t) (F.velocity t)
      = -(F.fusedHess t (F.velocity t) (F.velocity t))
        - (∑ i, F.third i t (F.velocity t)) (F.velocity t) (F.velocity t) := by
    have h := congrArg (fun ξ : V →L[ℝ] ℝ => ξ (F.velocity t)) hkey
    simp only [add_apply, neg_apply] at h
    linarith
  have hsymm : F.fusedHess t (F.velocity t) (F.accel t)
      = F.fusedHess t (F.accel t) (F.velocity t) := F.fusedHess_symm t _ _
  have hfp2 : F.fusPower t = F.fusedHess t (F.velocity t) (F.velocity t) := by
    rw [fusPower, fusedHess]
  simp only [add_apply]
  rw [hsplit, hsymm, hsplit, hfp2]
  ring

/-! ## Tension transport -/

omit [Nonempty ι] in
theorem hess_symm (i : ι) (t : ℝ) (u w : V) : F.hess i t u w = F.hess i t w u := by
  have hs := ((F.smooth i).contDiffAt (x := F.curve t)).isSymmSndFDerivAt (n := 3) (by norm_num)
  exact hs u w

omit [Nonempty ι] in
theorem third_symm (i : ι) (t : ℝ) (u w z : V) :
    F.third i t u w z = F.third i t u z w :=
  thirdForm_symm_right (F.smooth i) (F.curve t) u w z

/-- The constitutive packet of the flow at one instant. -/
def toPacket (t : ℝ) : PolarizationPacket ι V where
  form := fun i => F.hess i t
  residual := fun i => F.residual i t
  localVelocity := fun i => F.localVel i t
  fusedVelocity := F.velocity t
  symm := fun i u w => F.hess_symm i t u w
  local_eq := fun i => F.hess_localVel i t
  fused_eq := F.fusedHess_velocity t

omit [Nonempty ι] in
/-- **Exact synchronization conservation along the history** (`RPS.7`). -/
theorem locPower_eq_fusPower_add_tension (t : ℝ) :
    F.locPower t = F.fusPower t + F.tension t :=
  (F.toPacket t).localPower_eq_fusedPower_add_syncTension

/-- **Transport of synchronization tension** (`RPS.15`). -/
theorem hasDerivAt_tension (t : ℝ) :
    HasDerivAt (fun s => F.tension s)
      ((∑ i, F.third i t (F.velocity t)) (F.velocity t) (F.velocity t)
        - ∑ i, F.third i t (F.velocity t) (F.localVel i t) (F.localVel i t)) t := by
  have heq : (fun s => F.tension s) = fun s => F.locPower s - F.fusPower s := by
    funext s
    rw [F.locPower_eq_fusPower_add_tension s]
    ring
  rw [heq]
  have hd := (F.hasDerivAt_locPower t).sub (F.hasDerivAt_fusPower t)
  have hd' : HasDerivAt (fun s => F.locPower s - F.fusPower s)
      ((-2 * F.fusPower t - ∑ i, F.third i t (F.velocity t) (F.localVel i t) (F.localVel i t))
        - (-2 * F.fusPower t
          - (∑ i, F.third i t (F.velocity t)) (F.velocity t) (F.velocity t))) t := by
    refine hd.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => rfl
  refine hd'.congr_deriv ?_
  ring

/-- Relative velocity of a channel. -/
def delta (i : ι) (t : ℝ) : V := F.localVel i t - F.velocity t

omit [Nonempty ι] in
theorem localVel_eq_velocity_add_delta (i : ι) (t : ℝ) :
    F.localVel i t = F.velocity t + F.delta i t := by
  rw [delta]
  abel

omit [Nonempty ι] in
theorem third_localVel_expand (i : ι) (t : ℝ) :
    F.third i t (F.velocity t) (F.localVel i t) (F.localVel i t)
      = F.third i t (F.velocity t) (F.velocity t) (F.velocity t)
        + 2 * F.third i t (F.velocity t) (F.velocity t) (F.delta i t)
        + F.third i t (F.velocity t) (F.delta i t) (F.delta i t) := by
  have hd := F.localVel_eq_velocity_add_delta i t
  rw [hd]
  have hsym := F.third_symm i t (F.velocity t) (F.delta i t) (F.velocity t)
  simp only [map_add, add_apply]
  rw [hsym]
  ring

/-- **Third response transports the tension** (`RPS.16`). -/
theorem hasDerivAt_tension_delta (t : ℝ) :
    HasDerivAt (fun s => F.tension s)
      (-∑ i, (2 * F.third i t (F.velocity t) (F.velocity t) (F.delta i t)
        + F.third i t (F.velocity t) (F.delta i t) (F.delta i t))) t := by
  refine (F.hasDerivAt_tension t).congr_deriv ?_
  have hsum : (∑ i, F.third i t (F.velocity t)) (F.velocity t) (F.velocity t)
      = ∑ i, F.third i t (F.velocity t) (F.velocity t) (F.velocity t) := by
    simp
  rw [hsum, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => F.third_localVel_expand i t,
    ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Quadratic formations preserve unresolved local failure** (`RPS.19`). -/
theorem hasDerivAt_tension_zero (t : ℝ) (h3 : ∀ i, F.third i t = 0) :
    HasDerivAt (fun s => F.tension s) 0 t := by
  refine (F.hasDerivAt_tension_delta t).congr_deriv ?_
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (by
    rw [h3 i]
    simp : (2 * F.third i t (F.velocity t) (F.velocity t) (F.delta i t)
      + F.third i t (F.velocity t) (F.delta i t) (F.delta i t)) = 0)]
  simp

/-! ## Quadratic formations -/

omit [Nonempty ι] in
theorem localAccel_eq_neg_velocity (i : ι) (t : ℝ) (h3 : F.third i t = 0) :
    F.localAccel i t = -F.velocity t := by
  have hk := F.third_add_hess_localAccel i t
  rw [h3] at hk
  simp only [zero_apply, zero_add] at hk
  refine (bijective_of_posDef (F.hess i t) (F.posDef i (F.curve t))).1 ?_
  show F.hess i t (F.localAccel i t) = F.hess i t (-F.velocity t)
  rw [map_neg]
  exact hk

theorem accel_eq_neg_velocity (t : ℝ) (h3 : ∀ i, F.third i t = 0) :
    F.accel t = -F.velocity t := by
  have hk := F.sumThird_add_fusedHess_accel t
  have hz : (∑ i, F.third i t (F.velocity t)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h3 i]
    simp
  rw [hz] at hk
  simp only [zero_apply, zero_add] at hk
  refine (bijective_of_posDef (F.fusedHess t) (F.fusedHess_posDef t)).1 ?_
  show F.fusedHess t (F.accel t) = F.fusedHess t (-F.velocity t)
  rw [map_neg]
  exact hk

theorem hasDerivAt_velocity_neg (h3 : ∀ i t, F.third i t = 0) (t : ℝ) :
    HasDerivAt F.velocity (-F.velocity t) t := by
  have h := F.hasDerivAt_velocity t
  rwa [F.accel_eq_neg_velocity t (fun i => h3 i t)] at h

/-- **The relative velocity packet is frozen** (`RPS.20`, differential form). -/
theorem hasDerivAt_delta_zero (h3 : ∀ i t, F.third i t = 0) (i : ι) (t : ℝ) :
    HasDerivAt (fun s => F.delta i s) 0 t := by
  have hl := F.hasDerivAt_localVel i t
  rw [F.localAccel_eq_neg_velocity i t (h3 i t)] at hl
  have hv := F.hasDerivAt_velocity_neg h3 t
  have hd := hl.sub hv
  have hd' : HasDerivAt (fun s => F.localVel i s - F.velocity s)
      (-F.velocity t - -F.velocity t) t := by
    refine hd.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => rfl
  refine hd'.congr_deriv ?_
  abel

/-- **Exponential relaxation of the fused velocity** (`RPS.20`). -/
theorem velocity_eq_exp_smul (h3 : ∀ i t, F.third i t = 0) (t : ℝ) :
    F.velocity t = Real.exp (-t) • F.velocity 0 := by
  have hgd : ∀ s : ℝ, HasDerivAt (fun r : ℝ => Real.exp r • F.velocity r) 0 s := by
    intro s
    have h1 : HasDerivAt (fun r : ℝ => Real.exp r) (Real.exp s) s := Real.hasDerivAt_exp s
    have h2 := h1.smul (F.hasDerivAt_velocity_neg h3 s)
    refine h2.congr_deriv ?_
    rw [smul_neg]
    abel
  have hdiff : Differentiable ℝ (fun r : ℝ => Real.exp r • F.velocity r) := fun s =>
    (hgd s).differentiableAt
  have hfd : ∀ s : ℝ, fderiv ℝ (fun r : ℝ => Real.exp r • F.velocity r) s = 0 := by
    intro s
    have := (hgd s).hasFDerivAt
    rw [this.fderiv]
    ext
    simp
  have hconst := is_const_of_fderiv_eq_zero hdiff hfd t 0
  simp only [Real.exp_zero, one_smul] at hconst
  have hpos : Real.exp t ≠ 0 := Real.exp_ne_zero t
  have := congrArg (fun w : V => (Real.exp t)⁻¹ • w) hconst
  simp only [smul_smul, inv_mul_cancel₀ hpos, one_smul] at this
  rw [this, Real.exp_neg]

end ReflexiveFlow

end

end GaloisForLFunctions.HTGeometry
