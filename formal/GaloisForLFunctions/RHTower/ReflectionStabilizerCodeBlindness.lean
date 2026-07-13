import GaloisForLFunctions.RHTower.ReflectionFermionBoundary

/-!
# Reflection-stabilizer code blindness

Keeping only the `+1` swap-stabilized sector of a free two-cycle produces one copy of the
coefficient type, exactly as a fixed singleton does.  The anti-invariant syndrome is the datum
that the stabilized code forgets.
-/

namespace RHTower

/-- The `+1` stabilizer condition for the swap on a two-mode packet. -/
def SwapStabilized {A : Type*} (x : A × A) : Prop := x.swap = x

/-- The stabilized sector of a free swap pair is canonically just one copy of `A`.  Therefore its
abstract code-space type is the same as that of one fixed mode. -/
def swapStabilizedEquiv (A : Type*) : A ≃ {x : A × A // SwapStabilized x} where
  toFun a := ⟨(a, a), rfl⟩
  invFun x := x.1.1
  left_inv a := rfl
  right_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨a, b⟩, h⟩
    change (a, a) = (a, b)
    change (b, a) = (a, b) at h
    have hba : b = a := congrArg Prod.fst h
    rw [hba]

@[simp]
theorem swapStabilizedEquiv_apply (A : Type*) (a : A) :
    (swapStabilizedEquiv A a : A × A) = (a, a) := rfl

/-- The anti-invariant syndrome discarded by passage to the stabilized sector. -/
def swapAntiSyndrome {A : Type*} [AddGroup A] (x : A × A) : A := x.1 - x.2

/-- Vanishing anti-invariant syndrome is exactly the swap-stabilizer condition. -/
theorem swapAntiSyndrome_eq_zero_iff {A : Type*} [AddGroup A] (x : A × A) :
    swapAntiSyndrome x = 0 ↔ SwapStabilized x := by
  rcases x with ⟨a, b⟩
  simp only [swapAntiSyndrome, SwapStabilized, Prod.swap_prod_mk]
  rw [sub_eq_zero]
  constructor
  · rintro rfl
    rfl
  · intro h
    exact congrArg Prod.fst h |>.symm

end RHTower
