import GaloisForLFunctions.RHTower.EulerCutoffConstraintAlgebra
import GaloisForLFunctions.RHTower.RouteRPrimeHarmonicSummableCorona

/-!
# Reduced cofinal Euler completion

The compatible inverse limit of the radical finite Euler cutoff quotients is an ordinary reduced
completion.  This separates ordinary source completion from the nonreduced summable-tail corona:
there is no injective multiplicative map from that corona into this completion.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Coordinate ring at Euler cutoff `N`. -/
abbrev EulerCutoffStage (N : ℕ) :=
  AddMonoidAlgebra ℂ ℂ ⧸ eulerJ N

instance eulerCutoffStage_isReduced (N : ℕ) :
    IsReduced (EulerCutoffStage N) :=
  eulerCutoffQuotient_isReduced N

/-- Adjacent quotient bond in the decreasing Euler-constraint filtration. -/
def eulerCutoffBond (N : ℕ) :
    EulerCutoffStage (N + 1) →+* EulerCutoffStage N :=
  (eulerCutoffTransition (Nat.le_succ N)).toRingHom

@[simp] theorem eulerCutoffBond_mk (N : ℕ)
    (a : AddMonoidAlgebra ℂ ℂ) :
    eulerCutoffBond N (Ideal.Quotient.mk (eulerJ (N + 1)) a) =
      Ideal.Quotient.mk (eulerJ N) a := rfl

/-- Compatible families in all finite reduced Euler cutoff quotients. -/
def eulerCofinalReducedCompletionSubring :
    Subring (∀ N : ℕ, EulerCutoffStage N) where
  carrier := {x | ∀ N, eulerCutoffBond N (x (N + 1)) = x N}
  zero_mem' := fun N => by simp
  one_mem' := fun N => by simp
  add_mem' {x y} hx hy := fun N => by
    simp only [Pi.add_apply, map_add, hx N, hy N]
  neg_mem' {x} hx := fun N => by
    simp only [Pi.neg_apply, map_neg, hx N]
  mul_mem' {x y} hx hy := fun N => by
    simp only [Pi.mul_apply, map_mul, hx N, hy N]

/-- Algebraic inverse-limit completion of the finite Euler cutoff coordinate rings. -/
abbrev EulerCofinalReducedCompletion :=
  eulerCofinalReducedCompletionSubring

/-- Coordinate projection from the inverse-limit completion. -/
def eulerCofinalReducedCompletionEval (N : ℕ) :
    EulerCofinalReducedCompletion →+* EulerCutoffStage N where
  toFun x := x.1 N
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Canonical source map into its compatible finite-cutoff completion. -/
def eulerCofinalReducedCompletionMap :
    AddMonoidAlgebra ℂ ℂ →+* EulerCofinalReducedCompletion where
  toFun a := ⟨fun N => Ideal.Quotient.mk (eulerJ N) a, fun N => rfl⟩
  map_one' := by ext N; simp
  map_mul' a b := by ext N; simp
  map_zero' := by ext N; simp
  map_add' a b := by ext N; simp

@[simp] theorem eulerCofinalReducedCompletionMap_apply
    (a : AddMonoidAlgebra ℂ ℂ) (N : ℕ) :
    (eulerCofinalReducedCompletionMap a).1 N =
      Ideal.Quotient.mk (eulerJ N) a := rfl

/-- Cofinal Euler separation makes the source-to-completion map injective. -/
theorem eulerCofinalReducedCompletionMap_injective :
    Function.Injective eulerCofinalReducedCompletionMap := by
  intro a b hab
  apply eulerCofinalQuotientMap_injective
  funext N
  exact congrArg (fun x : EulerCofinalReducedCompletion => x.1 N) hab

/-- The actual compatible Euler inverse limit is reduced because every coordinate ring is
reduced. -/
theorem eulerCofinalReducedCompletion_isReduced :
    IsReduced EulerCofinalReducedCompletion := by
  refine ⟨fun x hx => ?_⟩
  apply Subtype.ext
  funext N
  exact (hx.map (eulerCofinalReducedCompletionEval N)).eq_zero

/-- No nonzero first-order nilpotent exists in the ordinary Euler completion. -/
theorem eq_zero_of_sq_zero_eulerCofinalReducedCompletion
    {x : EulerCofinalReducedCompletion} (hx : x ^ (2 : ℕ) = 0) : x = 0 := by
  letI : IsReduced EulerCofinalReducedCompletion :=
    eulerCofinalReducedCompletion_isReduced
  exact (show IsNilpotent x from ⟨2, hx⟩).eq_zero

/-- The nonreduced summable-tail corona cannot embed multiplicatively in the ordinary reduced
Euler completion.  Thus any source/corona comparison must either retain summable tails or cease to
be a faithful ring map. -/
theorem no_injective_routeRSummableHadamardCorona_to_eulerCofinalReducedCompletion
    (phi : _root_.RHTower.RouteRSummableHadamardCorona →+*
      EulerCofinalReducedCompletion) :
    ¬ Function.Injective phi := by
  letI : IsReduced EulerCofinalReducedCompletion :=
    eulerCofinalReducedCompletion_isReduced
  intro hinj
  apply _root_.RHTower.routeRPrimeHarmonicSummableHadamardClass_ne_zero
  apply hinj
  simpa using
    _root_.RHTower.routeRPrimeHarmonicSummableHadamardClass_map_eq_zero phi

end

end GaloisForLFunctions.RHTower
