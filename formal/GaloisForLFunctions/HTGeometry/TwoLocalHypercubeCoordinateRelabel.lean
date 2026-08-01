import GaloisForLFunctions.HTGeometry.TwoLocalUniversalHypercubeFamily

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Relabel Boolean-cube coordinates by a permutation of qubits. -/
def cubeCoordinateRelabel {n : ℕ} (e : Fin n ≃ Fin n) :
    (Fin n → Bool) ≃ (Fin n → Bool) :=
  Equiv.piCongrLeft (fun _ : Fin n => Bool) e

theorem cubeCoordinateRelabel_symm_apply {n : ℕ}
    (e : Fin n ≃ Fin n) (x : Fin n → Bool) (i : Fin n) :
    (cubeCoordinateRelabel e).symm x i = x (e i) := by
  exact Equiv.piCongrLeft_symm_apply
    (fun _ : Fin n => Bool) e x i

theorem cubeCoordinateRelabel_symm_boolToggle {n : ℕ}
    (e : Fin n ≃ Fin n) (x : Fin n → Bool) (i : Fin n) :
    (cubeCoordinateRelabel e).symm (boolToggle x (e i)) =
      boolToggle ((cubeCoordinateRelabel e).symm x) i := by
  funext j
  simp [cubeCoordinateRelabel_symm_apply, boolToggle,
    Function.update, e.injective.eq_iff]

theorem cubeCoordinateRelabel_symm_eq_boolToggle_iff {n : ℕ}
    (e : Fin n ≃ Fin n) (x y : Fin n → Bool) (i : Fin n) :
    (cubeCoordinateRelabel e).symm y =
        boolToggle ((cubeCoordinateRelabel e).symm x) i ↔
      y = boolToggle x (e i) := by
  rw [← cubeCoordinateRelabel_symm_boolToggle]
  exact (cubeCoordinateRelabel e).symm.injective.eq_iff

/-- The universal two-local Hamiltonian family is closed under arbitrary
qubit-coordinate relabeling. -/
theorem reindex_hypercubeTwoLocalHamiltonian {n : ℕ}
    (e : Fin n ≃ Fin n)
    (constant : ℂ) (onsite : Fin n → ℂ)
    (interaction : Fin n → Fin n → ℂ)
    (transverse : Fin n → ℂ) :
    Matrix.reindex (cubeCoordinateRelabel e)
        (cubeCoordinateRelabel e)
        (hypercubeTwoLocalHamiltonian constant onsite
          interaction transverse) =
      hypercubeTwoLocalHamiltonian constant
        (fun i => onsite (e.symm i))
        (fun i j => interaction (e.symm i) (e.symm j))
        (fun i => transverse (e.symm i)) := by
  ext x y
  change
    hypercubeTwoLocalHamiltonian constant onsite interaction transverse
        ((cubeCoordinateRelabel e).symm x)
        ((cubeCoordinateRelabel e).symm y) =
      hypercubeTwoLocalHamiltonian constant
        (fun i => onsite (e.symm i))
        (fun i j => interaction (e.symm i) (e.symm j))
        (fun i => transverse (e.symm i)) x y
  simp only [hypercubeTwoLocalHamiltonian]
  by_cases hxy : x = y
  · subst y
    have honsite :
        (∑ i, onsite i *
          (boolOccupation ((cubeCoordinateRelabel e).symm x i) : ℂ)) =
        ∑ i, onsite (e.symm i) *
          (boolOccupation (x i) : ℂ) := by
      have h := Equiv.sum_comp e
        (fun i => onsite (e.symm i) *
          (boolOccupation (x i) : ℂ))
      simpa [cubeCoordinateRelabel_symm_apply] using h
    have hinteraction :
        (∑ i, ∑ j, interaction i j *
          (boolOccupation ((cubeCoordinateRelabel e).symm x i) : ℂ) *
          (boolOccupation ((cubeCoordinateRelabel e).symm x j) : ℂ)) =
        ∑ i, ∑ j, interaction (e.symm i) (e.symm j) *
          (boolOccupation (x i) : ℂ) *
          (boolOccupation (x j) : ℂ) := by
      have h :=
        Equiv.sum_comp (Equiv.prodCongr e e)
          (fun q =>
            interaction (e.symm q.1) (e.symm q.2) *
              (boolOccupation (x q.1) : ℂ) *
              (boolOccupation (x q.2) : ℂ))
      simpa [Fintype.sum_prod_type,
        cubeCoordinateRelabel_symm_apply] using h
    rw [honsite, hinteraction]
    simp
  · have hsymm :
        (cubeCoordinateRelabel e).symm x ≠
          (cubeCoordinateRelabel e).symm y :=
      (cubeCoordinateRelabel e).symm.injective.ne hxy
    rw [if_neg hsymm, if_neg hxy]
    calc
      (∑ i, if (cubeCoordinateRelabel e).symm y =
          boolToggle ((cubeCoordinateRelabel e).symm x) i
          then transverse i else 0) =
          ∑ i, if y = boolToggle x (e i)
            then transverse i else 0 := by
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases h :
            (cubeCoordinateRelabel e).symm y =
              boolToggle ((cubeCoordinateRelabel e).symm x) i
        · rw [if_pos h, if_pos
            ((cubeCoordinateRelabel_symm_eq_boolToggle_iff
              e x y i).mp h)]
        · rw [if_neg h, if_neg
            (fun hright =>
              h ((cubeCoordinateRelabel_symm_eq_boolToggle_iff
                e x y i).mpr hright))]
      _ = ∑ i, if y = boolToggle x i
          then transverse (e.symm i) else 0 := by
        have h := Equiv.sum_comp e
          (fun i => if y = boolToggle x i
            then transverse (e.symm i) else 0)
        simpa using h

/-- Coefficient relabeling induced by a qubit-coordinate permutation. -/
def relabelHypercubeTwoLocalParameters {n : ℕ}
    (e : Fin n ≃ Fin n)
    (p : HypercubeTwoLocalParameter n → ℂ) :
    HypercubeTwoLocalParameter n → ℂ
  | .constant => p .constant
  | .onsite i => p (.onsite (e.symm i))
  | .interaction i j =>
      p (.interaction (e.symm i) (e.symm j))
  | .transverse i => p (.transverse (e.symm i))

/-- Evaluation commutes exactly with qubit-coordinate relabeling. -/
theorem eval_relabelHypercubeTwoLocalParameters {n : ℕ}
    (e : Fin n ≃ Fin n)
    (p : HypercubeTwoLocalParameter n → ℂ) :
    (universalHypercubeTwoLocalPolynomialMatrix n).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (relabelHypercubeTwoLocalParameters e p)) =
      Matrix.reindex (cubeCoordinateRelabel e)
        (cubeCoordinateRelabel e)
        ((universalHypercubeTwoLocalPolynomialMatrix n).map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ) p)) := by
  rw [eval_universalHypercubeTwoLocalPolynomialMatrix,
    eval_universalHypercubeTwoLocalPolynomialMatrix]
  exact
    (reindex_hypercubeTwoLocalHamiltonian e
      (p .constant) (fun i => p (.onsite i))
      (fun i j => p (.interaction i j))
      (fun i => p (.transverse i))).symm

theorem cubeCoordinateRelabel_boolToggle {n : ℕ}
    (e : Fin n ≃ Fin n) (x : Fin n → Bool) (i : Fin n) :
    cubeCoordinateRelabel e (boolToggle x i) =
      boolToggle (cubeCoordinateRelabel e x) (e i) := by
  apply (cubeCoordinateRelabel e).symm.injective
  rw [cubeCoordinateRelabel_symm_boolToggle]
  simp

/-- The selected-edge monodromy can be based at either endpoint. -/
theorem twoLocalCubeSelectedEdgeSwap_tail {m : ℕ}
    (u : Fin (m + 1) → Bool) :
    twoLocalCubeSelectedEdgeSwap (Fin.tail u) =
      Equiv.swap u (boolToggle u 0) := by
  rw [twoLocalCubeSelectedEdgeSwap_eq_swap]
  have hu : Fin.cons (u 0) (Fin.tail u) = u :=
    Fin.cons_self_tail u
  cases hzero : u 0
  · have hfalse :
        Fin.cons false (Fin.tail u) = u := by
      simpa [hzero] using hu
    rw [← hfalse, boolToggle_finCons_zero]
    rfl
  · have htrue :
        Fin.cons true (Fin.tail u) = u := by
      simpa [hzero] using hu
    calc
      Equiv.swap (Fin.cons false (Fin.tail u))
          (Fin.cons true (Fin.tail u)) =
        Equiv.swap (Fin.cons true (Fin.tail u))
          (Fin.cons false (Fin.tail u)) :=
            Equiv.swap_comm _ _
      _ = Equiv.swap u (boolToggle u 0) := by
        congr 1
        rw [← htrue, boolToggle_finCons_zero]
        rfl

/-- Conjugate the selected-edge transposition by a qubit-coordinate
permutation. -/
def relabeledTwoLocalCubeSelectedEdgeSwap {m : ℕ}
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (z₀ : Fin m → Bool) :
    Equiv.Perm (Fin (m + 1) → Bool) :=
  (cubeCoordinateRelabel e).symm.trans
    ((twoLocalCubeSelectedEdgeSwap z₀).trans
      (cubeCoordinateRelabel e))

theorem relabeledTwoLocalCubeSelectedEdgeSwap_at {m : ℕ}
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) :
    relabeledTwoLocalCubeSelectedEdgeSwap e
        (Fin.tail ((cubeCoordinateRelabel e).symm x)) =
      Equiv.swap x (boolToggle x (e 0)) := by
  let u := (cubeCoordinateRelabel e).symm x
  rw [relabeledTwoLocalCubeSelectedEdgeSwap,
    twoLocalCubeSelectedEdgeSwap_tail u]
  rw [← Equiv.trans_assoc, Equiv.symm_trans_swap_trans]
  change
    Equiv.swap (cubeCoordinateRelabel e u)
        (cubeCoordinateRelabel e (boolToggle u 0)) =
      Equiv.swap x (boolToggle x (e 0))
  rw [cubeCoordinateRelabel_boolToggle]
  simp [u]

/-- Every edge transposition of every finite Boolean hypercube is the
coordinate relabeling of an explicitly realized full-matrix two-local
monodromy loop. -/
theorem everyHypercubeEdge_is_relabeledTwoLocalSelectedEdge
    {m : ℕ} (x : Fin (m + 1) → Bool) (i : Fin (m + 1)) :
    ∃ z₀ : Fin m → Bool,
      relabeledTwoLocalCubeSelectedEdgeSwap (Equiv.swap 0 i) z₀ =
        Equiv.swap x (boolToggle x i) := by
  refine ⟨Fin.tail
    ((cubeCoordinateRelabel (Equiv.swap 0 i)).symm x), ?_⟩
  rw [relabeledTwoLocalCubeSelectedEdgeSwap_at]
  rw [Equiv.swap_apply_left]

end GaloisForLFunctions.HTGeometry
