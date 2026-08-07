import GaloisForLFunctions.HTGeometry.CDGAFreeCellExtend
import GaloisForLFunctions.HTGeometry.CDGACellTowerColimit

/-!
# Maps out of a twisted extension

A morphism out of a cell attachment `P ⊕_τ Q` is a morphism out of the base together with a
degree-preserving equivariant map out of the cell whose failure to commute with the differential is
exactly the image of the twist.  That extra datum is the null-homotopy which the attachment was made
to record.

* `HTGeometry.CDGATwistedLift` : the datum on the cell.
* `HTGeometry.twistedExtend` : the induced morphism.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
  {K : ℕ → Type w} [∀ n, AddCommGroup (K n)] [∀ n, Module R (K n)]
  {P : CDGAModuleStructure A M} {Q : CDGAModuleStructure A N} {S : CDGAModuleStructure A K}

/-- **The datum extending a morphism across a cell attachment**: an equivariant degreewise linear
map out of the cell whose differential differs from the composite with the differential of the cell
by the image of the twist. -/
structure CDGATwistedLift (t : CDGATwist P Q) (S : CDGAModuleStructure A K)
    (ε : CDGAModuleHom P S) where
  /-- The map out of the cell. -/
  η : ∀ n : ℕ, N n → K n
  /-- It is additive. -/
  η_add : ∀ (n : ℕ) (c c' : N n), η n (c + c') = η n c + η n c'
  /-- It is linear. -/
  η_smul : ∀ (n : ℕ) (r : R) (c : N n), η n (r • c) = r • η n c
  /-- It is equivariant. -/
  η_act : ∀ {a b n : ℕ} (h : a + b = n) (x : X a) (c : N b),
    η n (Q.act h x c) = S.act h x (η b c)
  /-- Its differential is corrected by the twist. -/
  η_d : ∀ (n : ℕ) (c : N n),
    S.d n (η n c) = ε.toFun (n + 1) (t.τ n c) + η (n + 1) (Q.d n c)

/-- **A morphism out of a cell attachment.** -/
def twistedExtend {t : CDGATwist P Q} (ε : CDGAModuleHom P S)
    (l : CDGATwistedLift t S ε) :
    CDGAModuleHom (CDGAModuleStructure.twisted P Q t) S where
  toFun n z := ε.toFun n z.1 + l.η n z.2
  map_add n z z' := by
    show ε.toFun n (z.1 + z'.1) + l.η n (z.2 + z'.2) = _
    rw [ε.map_add, l.η_add]
    abel
  map_smul n c z := by
    show ε.toFun n (c • z.1) + l.η n (c • z.2) = _
    rw [ε.map_smul, l.η_smul, smul_add]
  map_act h x z := by
    show ε.toFun _ (P.act h x z.1) + l.η _ (Q.act h x z.2) = _
    rw [ε.map_act h x z.1, l.η_act h x z.2, S.act_add_right]
  map_d n z := by
    show ε.toFun (n + 1) (P.d n z.1 + t.τ n z.2) + l.η (n + 1) (Q.d n z.2)
      = S.d n (ε.toFun n z.1 + l.η n z.2)
    rw [ε.map_add, ε.map_d n z.1, S.d_add, l.η_d n z.2]
    abel

@[simp] theorem twistedExtend_toFun {t : CDGATwist P Q}
    (ε : CDGAModuleHom P S) (l : CDGATwistedLift t S ε) (n : ℕ) (z : M n × N n) :
    (twistedExtend ε l).toFun n z = ε.toFun n z.1 + l.η n z.2 := rfl

/-- The extension restricts to the given morphism on the base. -/
theorem twistedExtend_comp_inl {t : CDGATwist P Q} (ε : CDGAModuleHom P S)
    (l : CDGATwistedLift t S ε) :
    (twistedExtend ε l).comp (twistedInl P Q t) = ε := by
  refine CDGAModuleHom.hom_ext fun n m => ?_
  show ε.toFun n m + l.η n 0 = ε.toFun n m
  rw [show l.η n (0 : N n) = 0 by
    have h := l.η_add n 0 0
    rw [add_zero] at h
    exact (add_right_cancel (b := l.η n 0) (by rw [zero_add, ← h])), add_zero]

end GaloisForLFunctions.HTGeometry
