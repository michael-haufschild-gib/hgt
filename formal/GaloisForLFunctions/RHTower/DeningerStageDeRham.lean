import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The holomorphic de Rham complex of a finite character stage

A finite character stage is the complex torus `(ℂ^×)^r`, an open subset of `ℂ^r`.  Its holomorphic
differential forms and their exterior derivative are the finite level of the cylinder de Rham
complex: a cylinder form is, locally, the pullback of one of these along finitely many evaluation
coordinates.  The exterior derivative preserves holomorphy and squares to zero, so each finite stage
carries an honest complex, and the logarithmic differentials of the coordinates — the classes that
generate the cohomology of a torus — are closed.

* `deningerStageTorus` : the stage `(ℂ^×)^r`, an open subset of `ℂ^r`.
* `DeningerIsHolomorphicForm` : holomorphy of a differential form on the stage.
* `deningerStage_extDeriv_holomorphic` : the exterior derivative preserves holomorphy.
* `deningerStage_extDeriv_extDeriv` : the exterior derivative squares to zero.
* `deningerDlogForm`, `deningerDlogForm_closed` : the logarithmic differentials are closed.
-/

namespace RHTower

open ContinuousAlternatingMap

open scoped Topology

section StageTorus

/-- **The finite character stage** `Z_{W,L} = Hom(L, ℂ^×) ≅ (ℂ^×)^r`, presented as the open subset
of `ℂ^r` where every coordinate is invertible. -/
def deningerStageTorus (r : ℕ) : Set (Fin r → ℂ) := {z | ∀ i, z i ≠ 0}

theorem mem_deningerStageTorus {r : ℕ} {z : Fin r → ℂ} :
    z ∈ deningerStageTorus r ↔ ∀ i, z i ≠ 0 := Iff.rfl

/-- **The stage is open**, so holomorphy on it is a local condition. -/
theorem deningerStageTorus_isOpen (r : ℕ) : IsOpen (deningerStageTorus r) := by
  have h : deningerStageTorus r = ⋂ i, (fun z : Fin r → ℂ => z i) ⁻¹' ({0}ᶜ) := by
    ext z
    simp [deningerStageTorus, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_compl_singleton).preimage (continuous_apply i)

theorem deningerStageTorus_mem_nhds {r : ℕ} {z : Fin r → ℂ} (hz : z ∈ deningerStageTorus r) :
    deningerStageTorus r ∈ 𝓝 z :=
  (deningerStageTorus_isOpen r).mem_nhds hz

end StageTorus

section StageForms

variable {r n : ℕ}

/-- A differential `n`-form on a finite character stage. -/
abbrev DeningerStageForm (r n : ℕ) := (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ

/-- **Holomorphy of a differential form on the stage**: analyticity at every point of `(ℂ^×)^r`.
This is the local condition defining `Ω^n_{Z_{W,L}}`. -/
def DeningerIsHolomorphicForm (ω : DeningerStageForm r n) : Prop :=
  AnalyticOnNhd ℂ ω (deningerStageTorus r)

theorem deningerIsHolomorphicForm_zero : DeningerIsHolomorphicForm (0 : DeningerStageForm r n) :=
  fun _ _ => analyticAt_const

theorem deningerIsHolomorphicForm_add {ω₁ ω₂ : DeningerStageForm r n}
    (h₁ : DeningerIsHolomorphicForm ω₁) (h₂ : DeningerIsHolomorphicForm ω₂) :
    DeningerIsHolomorphicForm (ω₁ + ω₂) :=
  fun z hz => (h₁ z hz).add (h₂ z hz)

theorem deningerIsHolomorphicForm_smul {ω : DeningerStageForm r n} (c : ℂ)
    (h : DeningerIsHolomorphicForm ω) : DeningerIsHolomorphicForm (c • ω) :=
  fun z hz => analyticAt_const.smul (h z hz)

/-- **The exterior derivative of a holomorphic form is holomorphic**: it is the alternatization of
the derivative, and alternatization is a continuous linear operation. -/
theorem deningerStage_extDeriv_holomorphic {ω : DeningerStageForm r n}
    (hω : DeningerIsHolomorphicForm ω) : DeningerIsHolomorphicForm (extDeriv ω) := by
  have h : extDeriv ω =
      (alternatizeUncurryFinCLM ℂ (Fin r → ℂ) ℂ (n := n)) ∘ (fderiv ℂ ω) := rfl
  rw [h]
  exact ContinuousLinearMap.comp_analyticOnNhd _
    (hω.fderiv_of_isOpen (deningerStageTorus_isOpen r))

/-- **The exterior derivative squares to zero on a holomorphic form**, so a finite character stage
carries an honest holomorphic de Rham complex. -/
theorem deningerStage_extDeriv_extDeriv {ω : DeningerStageForm r n}
    (hω : DeningerIsHolomorphicForm ω) {z : Fin r → ℂ} (hz : z ∈ deningerStageTorus r) :
    extDeriv (extDeriv ω) z = 0 :=
  extDeriv_extDeriv_apply (r := ⊤) (hω z hz).contDiffAt le_top

end StageForms

section Dlog

variable {r : ℕ}

/-- **The logarithmic differential of a coordinate**, `d log z_i = z_i⁻¹ dz_i`.  These are the
classes `d log P(a)` that generate the cohomology of a character stage. -/
noncomputable def deningerDlogForm (r : ℕ) (i : Fin r) : DeningerStageForm r 1 := fun z =>
  (z i)⁻¹ • (ContinuousAlternatingMap.ofSubsingleton ℂ (Fin r → ℂ) ℂ (0 : Fin 1)
    (ContinuousLinearMap.proj i))

@[simp]
theorem deningerDlogForm_apply (i : Fin r) (z : Fin r → ℂ) (v : Fin 1 → (Fin r → ℂ)) :
    deningerDlogForm r i z v = (z i)⁻¹ * v 0 i := rfl

/-- The evaluation of the logarithmic differential in a fixed direction, as a function of the
point. -/
theorem deningerDlogForm_eval (i : Fin r) (v : Fin 1 → (Fin r → ℂ)) :
    (fun z => deningerDlogForm r i z v) = fun z : Fin r → ℂ => (z i)⁻¹ * v 0 i := rfl

/-- **The logarithmic differentials are holomorphic on the stage.** -/
theorem deningerDlogForm_holomorphic (i : Fin r) :
    DeningerIsHolomorphicForm (deningerDlogForm r i) := by
  intro z hz
  have hproj : AnalyticAt ℂ (fun w : Fin r → ℂ => w i) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) i).analyticAt z
  exact (hproj.inv (hz i)).smul analyticAt_const

/-- The derivative of the coefficient of a logarithmic differential, in a fixed direction. -/
theorem deningerDlog_fderiv_apply (i : Fin r) {z : Fin r → ℂ} (hz : z i ≠ 0) (c : ℂ)
    (u : Fin r → ℂ) :
    fderiv ℂ (fun w : Fin r → ℂ => (w i)⁻¹ * c) z u = -((z i) ^ 2)⁻¹ * u i * c := by
  have hproj : HasFDerivAt (fun w : Fin r → ℂ => w i)
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) i) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) i).hasFDerivAt
  have hinv : HasFDerivAt (fun w : Fin r → ℂ => (w i)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℂ (-((z i) ^ 2)⁻¹)).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) i)) z :=
    (hasFDerivAt_inv hz).comp z hproj
  rw [(hinv.mul_const c).fderiv]
  simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

/-- **The logarithmic differentials are closed**: `d(z_i⁻¹ dz_i) = -z_i⁻² dz_i ∧ dz_i = 0`.  This is
the closedness of the generators `d log P(a)` of the cohomology of a character stage. -/
theorem deningerDlogForm_closed (i : Fin r) {z : Fin r → ℂ} (hz : z ∈ deningerStageTorus r) :
    extDeriv (deningerDlogForm r i) z = 0 := by
  have hdiff : DifferentiableAt ℂ (deningerDlogForm r i) z :=
    (deningerDlogForm_holomorphic i z hz).differentiableAt
  ext v
  rw [extDeriv_apply hdiff v]
  have hcoord : ∀ (w : Fin 1 → (Fin r → ℂ)) (u : Fin r → ℂ),
      fderiv ℂ (fun y => deningerDlogForm r i y w) z u = -((z i) ^ 2)⁻¹ * u i * w 0 i := by
    intro w u
    rw [deningerDlogForm_eval]
    exact deningerDlog_fderiv_apply i (hz i) (w 0 i) u
  have h0 : ((0 : Fin 2).removeNth v) 0 = v 1 := rfl
  have h1 : ((1 : Fin 2).removeNth v) 0 = v 0 := rfl
  rw [Fin.sum_univ_two]
  simp only [hcoord, h0, h1]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  rw [show (0 : (Fin r → ℂ) [⋀^Fin 2]→L[ℂ] ℂ) v = 0 from rfl]
  ring

end Dlog

end RHTower
