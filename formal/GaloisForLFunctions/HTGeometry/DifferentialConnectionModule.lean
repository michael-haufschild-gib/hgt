import GaloisForLFunctions.HTGeometry.DifferentialOperatorOre

/-!
# Ore modules from differential connections

An additive connection `conn : M → M` satisfying

`\nabla (a • m) = a • \nabla m + a′ • m`

integrates to a left action of the Ore ring `K[∂; δ]` on `M`.  This is the reusable
connection-to-module construction; it applies in particular to relative Kähler differentials over
a nonconstant differential base.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K M : Type*} [CommRing K] [Differential K]
  [AddCommGroup M] [Module K M]

/-- The coefficient action `a ↦ a · connⁿ m`. -/
def connectionDiffOpAux (conn : M →+ M) (m : M) (n : ℕ) : K →+ M where
  toFun a := a • ((conn : M → M)^[n] m)
  map_zero' := zero_smul _ _
  map_add' a b := add_smul a b _

/-- A differential operator acts through a connection. -/
def connectionDiffOpSMul (conn : M →+ M) (p : DiffOp K) (m : M) : M :=
  Finsupp.liftAddHom (connectionDiffOpAux conn m) (DiffOp.toFinsupp p)

theorem connectionDiffOpSMul_mono (conn : M →+ M) (n : ℕ) (a : K) (m : M) :
    connectionDiffOpSMul conn (DiffOp.mono n a) m = a • ((conn : M → M)^[n] m) := by
  rw [connectionDiffOpSMul, DiffOp.toFinsupp_mono]
  exact Finsupp.liftAddHom_apply_single (connectionDiffOpAux conn m) n a

@[simp] theorem connectionDiffOpSMul_zero_op (conn : M →+ M) (m : M) :
    connectionDiffOpSMul conn (0 : DiffOp K) m = 0 := by
  rw [connectionDiffOpSMul, DiffOp.toFinsupp_zero, map_zero]

theorem connectionDiffOpSMul_add_op (conn : M →+ M) (p q : DiffOp K) (m : M) :
    connectionDiffOpSMul conn (p + q) m =
      connectionDiffOpSMul conn p m + connectionDiffOpSMul conn q m := by
  rw [connectionDiffOpSMul, connectionDiffOpSMul, connectionDiffOpSMul,
    DiffOp.toFinsupp_add, map_add]

theorem connectionDiffOpSMul_smul (conn : M →+ M) (a : K) (p : DiffOp K) (m : M) :
    connectionDiffOpSMul conn (a • p) m = a • connectionDiffOpSMul conn p m := by
  refine DiffOp.induction_linear
    (motive := fun p => connectionDiffOpSMul conn (a • p) m =
      a • connectionDiffOpSMul conn p m) p ?_ ?_ ?_
  · simp
  · intro p q hp hq
    rw [smul_add, connectionDiffOpSMul_add_op, connectionDiffOpSMul_add_op,
      hp, hq, smul_add]
  · intro n c
    rw [DiffOp.smul_mono, connectionDiffOpSMul_mono,
      connectionDiffOpSMul_mono, mul_smul]

theorem connectionDiffOpSMul_dpartial (conn : M →+ M)
    (hleibniz : ∀ (a : K) (m : M), conn (a • m) = a • conn m + (Differential.deriv a) • m)
    (p : DiffOp K) (m : M) :
    connectionDiffOpSMul conn (DiffOp.dpartial p) m = conn (connectionDiffOpSMul conn p m) := by
  refine DiffOp.induction_linear
    (motive := fun p => connectionDiffOpSMul conn (DiffOp.dpartial p) m =
      conn (connectionDiffOpSMul conn p m)) p ?_ ?_ ?_
  · simp
  · intro p q hp hq
    rw [DiffOp.dpartial_add, connectionDiffOpSMul_add_op, hp, hq,
      connectionDiffOpSMul_add_op, map_add]
  · intro n a
    rw [DiffOp.dpartial_mono, connectionDiffOpSMul_add_op,
      connectionDiffOpSMul_mono, connectionDiffOpSMul_mono,
      connectionDiffOpSMul_mono, hleibniz, Function.iterate_succ_apply']

theorem connectionDiffOpSMul_dpartial_iterate (conn : M →+ M)
    (hleibniz : ∀ (a : K) (m : M), conn (a • m) = a • conn m + (Differential.deriv a) • m)
    (n : ℕ) (p : DiffOp K) (m : M) :
    connectionDiffOpSMul conn (DiffOp.dpartial^[n] p) m =
      (conn : M → M)^[n] (connectionDiffOpSMul conn p m) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        connectionDiffOpSMul_dpartial conn hleibniz, ih]

theorem connectionDiffOpSMul_mul (conn : M →+ M)
    (hleibniz : ∀ (a : K) (m : M), conn (a • m) = a • conn m + (Differential.deriv a) • m)
    (p q : DiffOp K) (m : M) :
    connectionDiffOpSMul conn (p * q) m =
      connectionDiffOpSMul conn p (connectionDiffOpSMul conn q m) := by
  refine DiffOp.induction_linear
    (motive := fun p => connectionDiffOpSMul conn (p * q) m =
      connectionDiffOpSMul conn p (connectionDiffOpSMul conn q m)) p ?_ ?_ ?_
  · rw [DiffOp.zero_mul', connectionDiffOpSMul_zero_op, connectionDiffOpSMul_zero_op]
  · intro p₁ p₂ h₁ h₂
    rw [DiffOp.add_mul', connectionDiffOpSMul_add_op, h₁, h₂,
      connectionDiffOpSMul_add_op]
  · intro n a
    rw [DiffOp.mono_mul, connectionDiffOpSMul_smul,
      connectionDiffOpSMul_dpartial_iterate conn hleibniz, connectionDiffOpSMul_mono]

theorem connectionDiffOpSMul_zero (conn : M →+ M) (p : DiffOp K) :
    connectionDiffOpSMul conn p 0 = 0 := by
  refine DiffOp.induction_linear
    (motive := fun p => connectionDiffOpSMul conn p 0 = 0) p ?_ ?_ ?_
  · rw [connectionDiffOpSMul_zero_op]
  · intro p q hp hq
    rw [connectionDiffOpSMul_add_op, hp, hq, add_zero]
  · intro n a
    rw [connectionDiffOpSMul_mono, Function.iterate_fixed (map_zero conn), smul_zero]

theorem connectionDiffOpSMul_add (conn : M →+ M) (p : DiffOp K) (m n : M) :
    connectionDiffOpSMul conn p (m + n) =
      connectionDiffOpSMul conn p m + connectionDiffOpSMul conn p n := by
  have hiter : ∀ r : ℕ, (conn : M → M)^[r] (m + n) =
      (conn : M → M)^[r] m + (conn : M → M)^[r] n := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', ih, map_add]
  refine DiffOp.induction_linear
    (motive := fun p => connectionDiffOpSMul conn p (m + n) =
      connectionDiffOpSMul conn p m + connectionDiffOpSMul conn p n) p ?_ ?_ ?_
  · rw [connectionDiffOpSMul_zero_op, connectionDiffOpSMul_zero_op,
      connectionDiffOpSMul_zero_op, add_zero]
  · intro p q hp hq
    rw [connectionDiffOpSMul_add_op, connectionDiffOpSMul_add_op,
      connectionDiffOpSMul_add_op, hp, hq]
    abel
  · intro r a
    rw [connectionDiffOpSMul_mono, connectionDiffOpSMul_mono,
      connectionDiffOpSMul_mono, hiter, smul_add]

theorem connectionDiffOpSMul_one (conn : M →+ M) (m : M) :
    connectionDiffOpSMul conn (1 : DiffOp K) m = m := by
  rw [DiffOp.one_def, connectionDiffOpSMul_mono]
  simp

/-- The left Ore-module structure integrated from a differential connection. -/
@[reducible] def connectionDiffOpModule (conn : M →+ M)
    (hleibniz : ∀ (a : K) (m : M), conn (a • m) = a • conn m + (Differential.deriv a) • m) :
    Module (DiffOp K) M where
  smul := connectionDiffOpSMul conn
  one_smul := connectionDiffOpSMul_one conn
  mul_smul := connectionDiffOpSMul_mul conn hleibniz
  smul_zero := connectionDiffOpSMul_zero conn
  smul_add := connectionDiffOpSMul_add conn
  add_smul p q m := connectionDiffOpSMul_add_op conn p q m
  zero_smul := connectionDiffOpSMul_zero_op conn

end

end GaloisForLFunctions.HTGeometry
