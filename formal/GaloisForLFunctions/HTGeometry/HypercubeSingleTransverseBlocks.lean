import GaloisForLFunctions.HTGeometry.BlockDiagonalCharpolyQuadratic
import GaloisForLFunctions.HTGeometry.BooleanHypercubeTranspositionLaw

/-!
# A single transverse coupling makes the hypercube Hamiltonian block-diagonal

With arbitrary diagonal energies and a *single* transverse flip at coordinate `0`, the Hamiltonian
on the Boolean hypercube decouples into `2^m` symmetric `2 × 2` blocks, one for each environment
`z : Fin m → Bool`, the block at `z` coupling the two vertices `Fin.cons false z` and
`Fin.cons true z`.  Its characteristic polynomial is therefore an explicit product of quadratics
with discriminants

  `(d(cons false z) − d(cons true z))² + 4u²`.

This is the block decomposition that the generic two-local Galois computation runs on: the
discriminants are the elements whose square roots generate the multiquadratic extension.

## Main results

* `singleTransverseHam` — the Hamiltonian.
* `reindex_singleTransverseHam` — it is block-diagonal after the `Fin 2 × environment` reindexing.
* `charpoly_singleTransverseHam` — its characteristic polynomial as a product of quadratics.
-/

open Polynomial Matrix

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {m : ℕ}

/-- Arbitrary diagonal energies plus a single transverse flip at coordinate `0`. -/
def singleTransverseHam (d : (Fin (m + 1) → Bool) → R) (u : R) :
    Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) R :=
  fun x y => if x = y then d x else if y = boolToggle x 0 then u else 0

/-- The reindexing splitting off coordinate `0` as a `Fin 2` index. -/
def cubeSplit (m : ℕ) : (Fin (m + 1) → Bool) ≃ (Fin 2 × (Fin m → Bool)) :=
  (Fin.consEquiv fun _ : Fin (m + 1) => Bool).symm.trans
    (finTwoEquiv.symm.prodCongr (Equiv.refl _))

@[simp] theorem cubeSplit_symm_apply (m : ℕ) (p : Fin 2 × (Fin m → Bool)) :
    (cubeSplit m).symm p = Fin.cons (finTwoEquiv p.1) p.2 := rfl

/-- The `2 × 2` block attached to one environment. -/
def transverseBlock (d : (Fin (m + 1) → Bool) → R) (u : R) (z : Fin m → Bool) :
    Matrix (Fin 2) (Fin 2) R :=
  symmTwo (d (Fin.cons false z)) (d (Fin.cons true z)) u

theorem boolToggle_zero_cons (a : Bool) (z : Fin m → Bool) :
    boolToggle (Fin.cons a z) 0 = Fin.cons (!a) z := by
  funext j
  refine Fin.cases ?_ (fun j' => ?_) j
  · simp [boolToggle]
  · simp [boolToggle, Fin.succ_ne_zero]

theorem cons_injective {a b : Bool} {z w : Fin m → Bool}
    (h : (Fin.cons a z : Fin (m + 1) → Bool) = Fin.cons b w) : a = b ∧ z = w := by
  constructor
  · simpa using congrFun h 0
  · funext j
    simpa using congrFun h j.succ

/-- **Block-diagonal form.** -/
theorem reindex_singleTransverseHam (d : (Fin (m + 1) → Bool) → R) (u : R) :
    Matrix.reindex (cubeSplit m) (cubeSplit m) (singleTransverseHam d u)
      = Matrix.blockDiagonal (transverseBlock d u) := by
  classical
  ext ⟨a, z⟩ ⟨b, w⟩
  have hA : (cubeSplit m).symm (a, z) = Fin.cons (finTwoEquiv a) z := rfl
  have hB : (cubeSplit m).symm (b, w) = Fin.cons (finTwoEquiv b) w := rfl
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, hA, hB,
    Matrix.blockDiagonal_apply, singleTransverseHam, transverseBlock, symmTwo]
  by_cases hzw : z = w
  · subst hzw
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl]
      fin_cases a <;> simp [finTwoEquiv]
    · have hab' : finTwoEquiv a ≠ finTwoEquiv b := fun h => hab (finTwoEquiv.injective h)
      have hne : (Fin.cons (finTwoEquiv a) z : Fin (m + 1) → Bool)
          ≠ Fin.cons (finTwoEquiv b) z := by
        intro h
        exact hab' (cons_injective h).1
      have hflip : (Fin.cons (finTwoEquiv b) z : Fin (m + 1) → Bool)
          = boolToggle (Fin.cons (finTwoEquiv a) z) 0 := by
        rw [boolToggle_zero_cons]
        congr 1
        cases hA2 : finTwoEquiv a <;> cases hB2 : finTwoEquiv b <;> simp_all
      rw [if_neg hne, hflip, if_pos rfl, if_pos rfl]
      fin_cases a <;> fin_cases b <;> simp_all
  · have hne : (Fin.cons (finTwoEquiv a) z : Fin (m + 1) → Bool)
        ≠ Fin.cons (finTwoEquiv b) w := by
      intro h
      exact hzw (cons_injective h).2
    have hflipne : (Fin.cons (finTwoEquiv b) w : Fin (m + 1) → Bool)
        ≠ boolToggle (Fin.cons (finTwoEquiv a) z) 0 := by
      rw [boolToggle_zero_cons]
      intro h
      exact hzw ((cons_injective h).2).symm
    rw [if_neg hne, if_neg hflipne, if_neg hzw]

/-- **The characteristic polynomial is the product of the block quadratics.** -/
theorem charpoly_singleTransverseHam [Nontrivial R] [DecidableEq R]
    (d : (Fin (m + 1) → Bool) → R) (u : R) :
    (singleTransverseHam d u).charpoly
      = ∏ z : Fin m → Bool,
          (X ^ (2 : ℕ) - C (d (Fin.cons false z) + d (Fin.cons true z)) * X
            + C (d (Fin.cons false z) * d (Fin.cons true z) - u * u)) := by
  classical
  have hre := Matrix.charpoly_reindex (cubeSplit m) (singleTransverseHam d u)
  rw [reindex_singleTransverseHam] at hre
  rw [← hre, charpoly_blockDiagonal]
  exact Finset.prod_congr rfl fun z _ => by
    rw [transverseBlock, charpoly_symmTwo]

end GaloisForLFunctions.HTGeometry
