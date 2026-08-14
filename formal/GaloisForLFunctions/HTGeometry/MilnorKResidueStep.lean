import GaloisForLFunctions.HTGeometry.MilnorKResidueData
import GaloisForLFunctions.HTGeometry.MilnorKGradedRingAssoc

/-!
# The residue step of Milnor `K`-theory

Milnor's residue is the `ξ`-component of a homomorphism into the graded ring
`K_*^M(k) ⊕ K_{*-1}^M(k)·ξ`, where `ξ` anticommutes with the odd part and satisfies
`ξ² = {-1}·ξ`.  A unit `a` of the valued field goes to `[ū_a] + v(a)·ξ`, so multiplying by it is the
map

`(x, y) ↦ ([ū_a]·x, [ū_a]·y + (-1)^n v(a)·x + (-1)^{n-1} v(a)·{-1}·y)`

on the degree-`n` part.  That map is what this file builds, together with the fold of it over a
symbol.  Because a unit goes to a sum of two terms each additive in the unit, the step is additive
in `a` — which is the multilinearity of Milnor `K`-theory, one of the two relations the residue has
to respect.

* `resSymbol`, `mulSymbol` : the degree-one class of a residue unit and multiplication by it.
* `resStepHom` : **multiplication by `[ū_a] + v(a)·ξ`.**
* `resStepHom_mul` : **it is additive in `a`.**
* `resPair` : **the fold over a symbol**, giving the specialization and the residue.
-/

namespace GaloisForLFunctions.HTGeometry

section ResidueStep

variable {k : Type*} [Field k]

/-- The degree-one Milnor class of a unit. -/
def resSymbol (u : kˣ) : MilnorKDeg k 1 := milnorClassDeg k 1 ⟨[u], rfl⟩

theorem resSymbol_mul (u v : kˣ) : resSymbol (u * v) = resSymbol u + resSymbol v :=
  milnorClassDeg_mul_of_eq k u v [] [] rfl rfl rfl _ _ _

theorem resSymbol_one : resSymbol (1 : kˣ) = 0 := by
  have h := resSymbol_mul (1 : kˣ) (1 : kˣ)
  rw [one_mul] at h
  have h0 : resSymbol (1 : kˣ) + (0 : MilnorKDeg k 1)
      = resSymbol (1 : kˣ) + resSymbol (1 : kˣ) := by
    rw [add_zero]
    exact h
  exact (add_right_injective (resSymbol (1 : kˣ)) h0).symm

/-- **`{-1} + {-1} = 0`**, because `(-1)(-1) = 1`. -/
theorem resSymbol_neg_one_add_self :
    resSymbol (-1 : kˣ) + resSymbol (-1 : kˣ) = 0 := by
  have h := resSymbol_mul (-1 : kˣ) (-1 : kˣ)
  rw [show (-1 : kˣ) * (-1 : kˣ) = 1 by simp, resSymbol_one] at h
  exact h.symm

theorem resSymbol_neg (u : kˣ) : resSymbol (-u) = resSymbol (-1 : kˣ) + resSymbol u := by
  have h := resSymbol_mul (-1 : kˣ) u
  rwa [show (-1 : kˣ) * u = -u by simp] at h

/-- Multiplication by a degree-one class. -/
noncomputable def mulSymbol (u : kˣ) (n : ℕ) : MilnorKDeg k n →+ MilnorKDeg k (n + 1) :=
  (milnorDegCongr (Nat.add_comm 1 n)).comp (milnorMul k 1 n (resSymbol u))

theorem mulSymbol_mul (u v : kˣ) (n : ℕ) :
    mulSymbol (u * v) n = mulSymbol u n + mulSymbol v n := by
  show (milnorDegCongr (Nat.add_comm 1 n)).comp (milnorMul k 1 n (resSymbol (u * v))) = _
  rw [resSymbol_mul, map_add]
  refine AddMonoidHom.ext fun x => ?_
  show milnorDegCongr (Nat.add_comm 1 n)
      ((milnorMul k 1 n (resSymbol u) + milnorMul k 1 n (resSymbol v)) x) = _
  rw [AddMonoidHom.add_apply, map_add]
  rfl

variable {K : Type*} [Field K] (D : ResidueData K k)

/-- **Multiplication by `[ū_a] + v(a)·ξ`** on the degree-`n` part of the target of the residue. -/
noncomputable def resStepHom (a : Kˣ) : ∀ n : ℕ,
    (MilnorKDeg k n × MilnorKDeg k (n - 1)) →+ (MilnorKDeg k (n + 1) × MilnorKDeg k n)
  | 0 =>
      ((mulSymbol (D.residueUnit a) 0).comp (AddMonoidHom.fst _ _)).prod
        (D.val' a • (AddMonoidHom.fst (MilnorKDeg k 0) (MilnorKDeg k 0)))
  | (m + 1) =>
      ((mulSymbol (D.residueUnit a) (m + 1)).comp (AddMonoidHom.fst _ _)).prod
        (((mulSymbol (D.residueUnit a) m).comp (AddMonoidHom.snd _ _)
            + ((-1 : ℤ) ^ (m + 1) * D.val' a) •
              (AddMonoidHom.fst (MilnorKDeg k (m + 1)) (MilnorKDeg k m)))
          + ((-1 : ℤ) ^ m * D.val' a) •
              ((mulSymbol (-1 : kˣ) m).comp (AddMonoidHom.snd _ _)))

@[simp]
theorem resStepHom_zero_apply (a : Kˣ) (p : MilnorKDeg k 0 × MilnorKDeg k 0) :
    resStepHom D a 0 p = (mulSymbol (D.residueUnit a) 0 p.1, D.val' a • p.1) := rfl

@[simp]
theorem resStepHom_succ_apply (a : Kˣ) (m : ℕ)
    (p : MilnorKDeg k (m + 1) × MilnorKDeg k m) :
    resStepHom D a (m + 1) p
      = (mulSymbol (D.residueUnit a) (m + 1) p.1,
          mulSymbol (D.residueUnit a) m p.2
            + ((-1 : ℤ) ^ (m + 1) * D.val' a) • p.1
            + ((-1 : ℤ) ^ m * D.val' a) • mulSymbol (-1 : kˣ) m p.2) := rfl

/-- **The residue step is additive in the unit.**  This is the multilinearity of Milnor
`K`-theory: `[ū_{ab}] = [ū_a] + [ū_b]` and `v(ab) = v(a) + v(b)`. -/
theorem resStepHom_mul (a b : Kˣ) (n : ℕ) :
    resStepHom D (a * b) n = resStepHom D a n + resStepHom D b n := by
  cases n with
  | zero =>
      refine AddMonoidHom.ext fun p => ?_
      rw [resStepHom_zero_apply, AddMonoidHom.add_apply, resStepHom_zero_apply,
        resStepHom_zero_apply]
      refine Prod.ext ?_ ?_
      · show mulSymbol (D.residueUnit (a * b)) 0 p.1 = _
        rw [D.residueUnit_mul, mulSymbol_mul]
        rfl
      · show D.val' (a * b) • p.1 = _
        rw [D.val'_mul, add_zsmul]
        rfl
  | succ m =>
      refine AddMonoidHom.ext fun p => ?_
      rw [resStepHom_succ_apply, AddMonoidHom.add_apply, resStepHom_succ_apply,
        resStepHom_succ_apply]
      refine Prod.ext ?_ ?_
      · show mulSymbol (D.residueUnit (a * b)) (m + 1) p.1 = _
        rw [D.residueUnit_mul, mulSymbol_mul]
        rfl
      · show mulSymbol (D.residueUnit (a * b)) m p.2
            + ((-1 : ℤ) ^ (m + 1) * D.val' (a * b)) • p.1
            + ((-1 : ℤ) ^ m * D.val' (a * b)) • mulSymbol (-1 : kˣ) m p.2 = _
        rw [D.residueUnit_mul, mulSymbol_mul, D.val'_mul, mul_add, mul_add, add_zsmul, add_zsmul]
        simp only [Prod.snd_add, AddMonoidHom.add_apply]
        abel

/-- **The fold of the residue step over a symbol**: the specialization and the residue. -/
noncomputable def resPair : (l : List Kˣ) → MilnorKDeg k l.length × MilnorKDeg k (l.length - 1)
  | [] => (milnorOne, 0)
  | a :: l => resStepHom D a l.length (resPair l)

/-- **The composite of the residue steps along a list**, acting on the degree-`n` part.  Indexing
the target by `n + l.length` makes the recursion typecheck without any transport. -/
noncomputable def resFold : (l : List Kˣ) → (n : ℕ) →
    (MilnorKDeg k n × MilnorKDeg k (n - 1)) →+
      (MilnorKDeg k (n + l.length) × MilnorKDeg k (n + l.length - 1))
  | [], _ => AddMonoidHom.id _
  | a :: l, n => (resStepHom D a (n + l.length)).comp (resFold l n)

@[simp]
theorem resFold_nil (n : ℕ) : resFold D ([] : List Kˣ) n = AddMonoidHom.id _ := rfl

@[simp]
theorem resFold_cons (a : Kˣ) (l : List Kˣ) (n : ℕ) :
    resFold D (a :: l) n = (resStepHom D a (n + l.length)).comp (resFold D l n) := rfl

@[simp]
theorem resPair_nil : resPair D ([] : List Kˣ) = (milnorOne, 0) := rfl

@[simp]
theorem resPair_cons (a : Kˣ) (l : List Kˣ) :
    resPair D (a :: l) = resStepHom D a l.length (resPair D l) := rfl

end ResidueStep

end GaloisForLFunctions.HTGeometry
