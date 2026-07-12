import GaloisForLFunctions.RHTower.XiThetaL2Cyclicity

/-!
# Ordinary `L²` metric collapse for the Hedenmalm theta source

Any jointly continuous sesquilinear form on ordinary `L²(R)` which is
invariant under simultaneous translation and annihilates the normalized
theta source is identically zero.  Hence a nonzero Hedenmalm metric is forced
to be singular relative to the ordinary `L²` topology (or to abandon a
translation-stable source domain).
-/

open Complex MeasureTheory Set

namespace RHTower

open MellinL2

noncomputable section

/-- A jointly continuous complex sesquilinear form on a normed space, linear
in the first argument and conjugate-linear in the second. -/
structure ContinuousSesquilinearForm (H : Type*) [NormedAddCommGroup H]
    [NormedSpace ℂ H] where
  toFun : H → H → ℂ
  map_add_left : ∀ u v w, toFun (u + v) w = toFun u w + toFun v w
  map_smul_left : ∀ (c : ℂ) u v, toFun (c • u) v = c * toFun u v
  map_add_right : ∀ u v w, toFun u (v + w) = toFun u v + toFun u w
  map_smul_right : ∀ (c : ℂ) u v,
    toFun u (c • v) = (starRingEnd ℂ) c * toFun u v
  continuous : Continuous (fun p : H × H ↦ toFun p.1 p.2)

instance {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] :
    CoeFun (ContinuousSesquilinearForm H) (fun _ ↦ H → H → ℂ) :=
  ⟨ContinuousSesquilinearForm.toFun⟩

namespace ContinuousSesquilinearForm

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

@[simp] theorem apply_zero_left (Q : ContinuousSesquilinearForm H) (v : H) :
    Q 0 v = 0 := by
  have h := Q.map_smul_left 0 0 v
  simpa using h

@[simp] theorem apply_add_left (Q : ContinuousSesquilinearForm H) (u v w : H) :
    Q (u + v) w = Q u w + Q v w :=
  Q.map_add_left u v w

@[simp] theorem apply_smul_left (Q : ContinuousSesquilinearForm H)
    (c : ℂ) (u v : H) :
    Q (c • u) v = c * Q u v :=
  Q.map_smul_left c u v

/-- The left radical of a continuous sesquilinear form. -/
def leftRadical (Q : ContinuousSesquilinearForm H) : Submodule ℂ H where
  carrier := {u | ∀ v, Q u v = 0}
  zero_mem' := Q.apply_zero_left
  add_mem' hu hv w := by simp [hu w, hv w]
  smul_mem' c u hu w := by simp [hu w]

theorem mem_leftRadical_iff (Q : ContinuousSesquilinearForm H) (u : H) :
    u ∈ Q.leftRadical ↔ ∀ v, Q u v = 0 :=
  Iff.rfl

/-- Joint continuity makes the left radical closed in the ambient norm
topology. -/
theorem isClosed_leftRadical (Q : ContinuousSesquilinearForm H) :
    IsClosed (Q.leftRadical : Set H) := by
  have heq : (Q.leftRadical : Set H) = ⋂ v : H, {u | Q u v = 0} := by
    ext u
    simp [leftRadical]
  rw [heq]
  apply isClosed_iInter
  intro v
  exact isClosed_eq
    (Q.continuous.comp (continuous_id.prodMk continuous_const))
    continuous_const

end ContinuousSesquilinearForm

abbrev XiThetaL2 := Lp (α := ℝ) ℂ 2 volume

/-- Simultaneous invariance under the ordinary real translation
representation. -/
def XiThetaL2TranslationInvariant
    (Q : ContinuousSesquilinearForm XiThetaL2) : Prop :=
  ∀ (a : ℝ) (u v : XiThetaL2),
    Q (additiveTranslationUnitary a u) (additiveTranslationUnitary a v) = Q u v

/-- **Ordinary `L²` metric collapse.**  Translation invariance and nullity of
the actual theta source force every jointly continuous pullback form to
vanish identically. -/
theorem xiThetaL2_continuousForm_eq_zero
    (Q : ContinuousSesquilinearForm XiThetaL2)
    (hinvariant : XiThetaL2TranslationInvariant Q)
    (hnull : ∀ v : XiThetaL2, Q xiThetaSourceL2 v = 0) :
    ∀ u v : XiThetaL2, Q u v = 0 := by
  let N : Submodule ℂ XiThetaL2 := Q.leftRadical
  have hNclosed : IsClosed (N : Set XiThetaL2) := Q.isClosed_leftRadical
  have horbit : ∀ a : ℝ, xiThetaTranslationOrbit a ∈ N := by
    intro a
    rw [ContinuousSesquilinearForm.mem_leftRadical_iff]
    intro v
    let w : XiThetaL2 := (additiveTranslationUnitary a).symm v
    have hv : additiveTranslationUnitary a w = v :=
      (additiveTranslationUnitary a).apply_symm_apply v
    rw [← hv, xiThetaTranslationOrbit, hinvariant]
    exact hnull w
  have hNtop : N = ⊤ :=
    closedSubmodule_eq_top_of_isCyclicFamily
      isCyclicFamily_xiThetaTranslationOrbit N hNclosed horbit
  intro u v
  have hu : u ∈ N := by rw [hNtop]; exact Submodule.mem_top
  exact hu v

/-- Positive topology law: there is no nonzero ordinary-`L²` continuous,
translation-invariant form whose left radical contains the theta source. -/
theorem not_exists_nonzero_xiThetaL2_continuousForm :
    ¬ ∃ Q : ContinuousSesquilinearForm XiThetaL2,
      XiThetaL2TranslationInvariant Q ∧
      (∀ v : XiThetaL2, Q xiThetaSourceL2 v = 0) ∧
      ∃ u v : XiThetaL2, Q u v ≠ 0 := by
  rintro ⟨Q, hinvariant, hnull, u, v, huv⟩
  exact huv (xiThetaL2_continuousForm_eq_zero Q hinvariant hnull u v)

end

end RHTower
