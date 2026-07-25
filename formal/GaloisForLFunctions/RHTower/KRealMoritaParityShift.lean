import GaloisForLFunctions.RHTower.KRealKernelCokernel

/-!
# Quaternionic Real Morita parity shift

Let `E` be an odd `KRealStructure`, let `M` be an even one, and let endomorphisms of `E`
act on `M`. If the action is compatible with the induced Real structure on `End E`, the
complex-linear Morita intertwiners `E → M` inherit an odd `KRealStructure`.

The descended reflection is

`(τ F)(e) = σ_M (F (-σ_E e))`.

Its square is `-1`; no product or direct-sum doubling is introduced. This is the algebraic
degree-four Real-Brauer parity mechanism needed by the rational CCM construction.

No topology, trace, cyclic homology, positivity, zero spectrum, or Riemann-hypothesis premise
occurs.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

variable {E M : Type*}
  [AddCommGroup E] [Module ℂ E]
  [AddCommGroup M] [Module ℂ M]

/--
Real structure induced on complex endomorphisms by an odd `KRealStructure`.

Because the inverse of the odd reflection is its negative, this is `T ↦ -σ_E T σ_E`.
-/
def kRealOddEndomorphismRealStructure
    (KE : KRealStructure true E) (T : Module.End ℂ E) :
    Module.End ℂ E where
  toFun e := -KE.sigma (T (KE.sigma e))
  map_add' e f := by simp; abel
  map_smul' z e := by simp

theorem kRealOddEndomorphismRealStructure_apply
    (KE : KRealStructure true E) (T : Module.End ℂ E) (e : E) :
    kRealOddEndomorphismRealStructure KE T e =
      -KE.sigma (T (KE.sigma e)) :=
  rfl

/-- Quaternionic conjugation induces an involution on complex endomorphisms. -/
theorem kRealOddEndomorphismRealStructure_sq
    (KE : KRealStructure true E) (T : Module.End ℂ E) :
    kRealOddEndomorphismRealStructure KE
      (kRealOddEndomorphismRealStructure KE T) = T := by
  apply LinearMap.ext
  intro e
  simp [kRealOddEndomorphismRealStructure_apply, KE.sq, kRealParityAction]

/-- The inverse odd reflection intertwines `T` with its induced Real conjugate. -/
theorem kRealOddInverseSigma_endomorphism
    (KE : KRealStructure true E) (T : Module.End ℂ E) (e : E) :
    -KE.sigma (T e) =
      kRealOddEndomorphismRealStructure KE T (-KE.sigma e) := by
  simp [kRealOddEndomorphismRealStructure_apply, KE.sq, kRealParityAction]

/-- Complex-linear intertwiners from the Morita fiber to a represented module. -/
def kRealMoritaIntertwiners
    (r : Module.End ℂ E → Module.End ℂ M) :
    Submodule ℂ (E →ₗ[ℂ] M) where
  carrier := {F | ∀ T e, F (T e) = r T (F e)}
  zero_mem' := by simp
  add_mem' := by
    intro F G hF hG T e
    simp [hF T e, hG T e]
  smul_mem' := by
    intro z F hF T e
    simp [hF T e]

/--
Morita reflection on the ambient complex-linear Hom space.

It is complex-linear in `e` because both the source inverse reflection and target reflection
are conjugate-linear.
-/
def kRealMoritaReflection
    (KE : KRealStructure true E) (KM : KRealStructure false M)
    (F : E →ₗ[ℂ] M) : E →ₗ[ℂ] M where
  toFun e := KM.sigma (F (-KE.sigma e))
  map_add' e f := by simp; abel
  map_smul' z e := by simp

theorem kRealMoritaReflection_apply
    (KE : KRealStructure true E) (KM : KRealStructure false M)
    (F : E →ₗ[ℂ] M) (e : E) :
    kRealMoritaReflection KE KM F e =
      KM.sigma (F (-KE.sigma e)) :=
  rfl

/--
Real compatibility of the endomorphism action makes the Morita intertwiner space stable under
the descended reflection.
-/
theorem kRealMoritaReflection_mem
    (KE : KRealStructure true E) (KM : KRealStructure false M)
    (r : Module.End ℂ E → Module.End ℂ M)
    (hcompat : ∀ T m,
      KM.sigma (r (kRealOddEndomorphismRealStructure KE T) m) =
        r T (KM.sigma m))
    (F : kRealMoritaIntertwiners r) :
    kRealMoritaReflection KE KM F ∈ kRealMoritaIntertwiners r := by
  intro T e
  rw [kRealMoritaReflection_apply]
  rw [kRealOddInverseSigma_endomorphism]
  rw [F.property (kRealOddEndomorphismRealStructure KE T) (-KE.sigma e)]
  exact hcompat T (F.1 (-KE.sigma e))

/-- Descended quaternionic reflection on the Morita intertwiner space. -/
def kRealMoritaDescentSigma
    (KE : KRealStructure true E) (KM : KRealStructure false M)
    (r : Module.End ℂ E → Module.End ℂ M)
    (hcompat : ∀ T m,
      KM.sigma (r (kRealOddEndomorphismRealStructure KE T) m) =
        r T (KM.sigma m)) :
    kRealMoritaIntertwiners r →ₗ⋆[ℂ] kRealMoritaIntertwiners r where
  toFun F :=
    ⟨kRealMoritaReflection KE KM F,
      kRealMoritaReflection_mem KE KM r hcompat F⟩
  map_add' F G := by
    apply Subtype.ext
    apply LinearMap.ext
    intro e
    simp [kRealMoritaReflection_apply]
  map_smul' z F := by
    apply Subtype.ext
    apply LinearMap.ext
    intro e
    simp [kRealMoritaReflection_apply]

/-- The Morita-descended reflection has odd square, without doubling the carrier. -/
theorem kRealMoritaDescentSigma_sq
    (KE : KRealStructure true E) (KM : KRealStructure false M)
    (r : Module.End ℂ E → Module.End ℂ M)
    (hcompat : ∀ T m,
      KM.sigma (r (kRealOddEndomorphismRealStructure KE T) m) =
        r T (KM.sigma m))
    (F : kRealMoritaIntertwiners r) :
    kRealMoritaDescentSigma KE KM r hcompat
      (kRealMoritaDescentSigma KE KM r hcompat F) = -F := by
  apply Subtype.ext
  apply LinearMap.ext
  intro e
  change KM.sigma (KM.sigma (F.1 (-KE.sigma (-KE.sigma e)))) = -F.1 e
  rw [KM.sq]
  simp [kRealParityAction, KE.sq]

/--
Quaternionic Real Morita parity shift: an even represented module descends through an odd
Morita fiber to an odd `KRealStructure`.
-/
def kRealMoritaParityShift
    (KE : KRealStructure true E) (KM : KRealStructure false M)
    (r : Module.End ℂ E → Module.End ℂ M)
    (hcompat : ∀ T m,
      KM.sigma (r (kRealOddEndomorphismRealStructure KE T) m) =
        r T (KM.sigma m)) :
    KRealStructure true (kRealMoritaIntertwiners r) where
  sigma := kRealMoritaDescentSigma KE KM r hcompat
  sq := by
    intro F
    exact kRealMoritaDescentSigma_sq KE KM r hcompat F

section RepresentedAlgebra

variable {A : Type*} [AddCommGroup A] [Module ℂ A]

/--
Morita intertwiners for an arbitrary represented complex algebra or operator space.

No algebra laws are required for the parity argument itself: only the two actions and their
Real compatibility enter.
-/
def kRealMoritaActionIntertwiners
    (s : A → Module.End ℂ E) (r : A → Module.End ℂ M) :
    Submodule ℂ (E →ₗ[ℂ] M) where
  carrier := {F | ∀ a e, F (s a e) = r a (F e)}
  zero_mem' := by simp
  add_mem' := by
    intro F G hF hG a e
    simp [hF a e, hG a e]
  smul_mem' := by
    intro z F hF a e
    simp [hF a e]

/--
The Morita reflection preserves intertwiners for any represented even Real operator object.
-/
theorem kRealMoritaActionReflection_mem
    (KA : KRealStructure false A)
    (KE : KRealStructure true E) (KM : KRealStructure false M)
    (s : A → Module.End ℂ E) (r : A → Module.End ℂ M)
    (hsource : ∀ a e,
      -KE.sigma (s a e) = s (KA.sigma a) (-KE.sigma e))
    (htarget : ∀ a m,
      KM.sigma (r (KA.sigma a) m) = r a (KM.sigma m))
    (F : kRealMoritaActionIntertwiners s r) :
    kRealMoritaReflection KE KM F ∈
      kRealMoritaActionIntertwiners s r := by
  intro a e
  rw [kRealMoritaReflection_apply]
  rw [hsource]
  rw [F.property (KA.sigma a) (-KE.sigma e)]
  exact htarget a (F.1 (-KE.sigma e))

/-- Descended reflection for a represented Real operator object. -/
def kRealMoritaActionDescentSigma
    (KA : KRealStructure false A)
    (KE : KRealStructure true E) (KM : KRealStructure false M)
    (s : A → Module.End ℂ E) (r : A → Module.End ℂ M)
    (hsource : ∀ a e,
      -KE.sigma (s a e) = s (KA.sigma a) (-KE.sigma e))
    (htarget : ∀ a m,
      KM.sigma (r (KA.sigma a) m) = r a (KM.sigma m)) :
    kRealMoritaActionIntertwiners s r →ₗ⋆[ℂ]
      kRealMoritaActionIntertwiners s r where
  toFun F :=
    ⟨kRealMoritaReflection KE KM F,
      kRealMoritaActionReflection_mem KA KE KM s r hsource htarget F⟩
  map_add' F G := by
    apply Subtype.ext
    apply LinearMap.ext
    intro e
    simp [kRealMoritaReflection_apply]
  map_smul' z F := by
    apply Subtype.ext
    apply LinearMap.ext
    intro e
    simp [kRealMoritaReflection_apply]

/-- The represented-algebra Morita descent has square `-1` on the unchanged intertwiner carrier. -/
theorem kRealMoritaActionDescentSigma_sq
    (KA : KRealStructure false A)
    (KE : KRealStructure true E) (KM : KRealStructure false M)
    (s : A → Module.End ℂ E) (r : A → Module.End ℂ M)
    (hsource : ∀ a e,
      -KE.sigma (s a e) = s (KA.sigma a) (-KE.sigma e))
    (htarget : ∀ a m,
      KM.sigma (r (KA.sigma a) m) = r a (KM.sigma m))
    (F : kRealMoritaActionIntertwiners s r) :
    kRealMoritaActionDescentSigma KA KE KM s r hsource htarget
      (kRealMoritaActionDescentSigma KA KE KM s r hsource htarget F) =
        -F := by
  apply Subtype.ext
  apply LinearMap.ext
  intro e
  change KM.sigma (KM.sigma (F.1 (-KE.sigma (-KE.sigma e)))) = -F.1 e
  rw [KM.sq]
  simp [kRealParityAction, KE.sq]

/--
General Real-Brauer parity shift for a represented algebra or bounded-operator algebra.

This is the application form relevant to an analytic CCM trace-class module, where not every
algebraic endomorphism of the Hilbert fiber acts continuously.
-/
def kRealMoritaActionParityShift
    (KA : KRealStructure false A)
    (KE : KRealStructure true E) (KM : KRealStructure false M)
    (s : A → Module.End ℂ E) (r : A → Module.End ℂ M)
    (hsource : ∀ a e,
      -KE.sigma (s a e) = s (KA.sigma a) (-KE.sigma e))
    (htarget : ∀ a m,
      KM.sigma (r (KA.sigma a) m) = r a (KM.sigma m)) :
    KRealStructure true (kRealMoritaActionIntertwiners s r) where
  sigma :=
    kRealMoritaActionDescentSigma KA KE KM s r hsource htarget
  sq := by
    intro F
    exact kRealMoritaActionDescentSigma_sq
      KA KE KM s r hsource htarget F

end RepresentedAlgebra

end RHTower
end GaloisForLFunctions
