import GaloisForLFunctions.HTGeometry.TwoLocalHypercubeCoordinateRelabel

/-!
# Every hypercube edge as exact two-local spectral monodromy

This file upgrades the explicit selected-edge construction to a universal
generator theorem.  It supplies explicit continuous coordinates in one
all-qubit polynomial two-local family, proves nonvanishing characteristic
resultant along the loop, transports the complete root packet under arbitrary
qubit-coordinate relabeling, and realizes every Boolean-hypercube edge as the
exact endpoint permutation of a closed simple-spectrum loop.
-/

open Topology unitInterval

namespace GaloisForLFunctions.HTGeometry

structure SelectedEdgeBaseCoefficients {m : ℕ}
    (z₀ : Fin m → Bool) where
  constant : ℂ
  longitudinal : ℂ
  transverse : ℂ
  onsite : Fin m → ℂ
  interaction : Fin m → ℂ
  realization :
    twoLocalStarHamiltonianMatrix z₀ 0 =
      distinguishedStarTwoLocalHamiltonian constant longitudinal
        transverse onsite interaction

theorem selectedEdgeBaseCoefficients_nonempty {m : ℕ}
    (z₀ : Fin m → Bool) :
    Nonempty (SelectedEdgeBaseCoefficients z₀) := by
  rcases twoLocalStarHamiltonian_is_complex_twoLocal z₀ 0 with
    ⟨constant, longitudinal, transverse, onsite, interaction, h⟩
  exact ⟨⟨constant, longitudinal, transverse, onsite, interaction, h⟩⟩

noncomputable def selectedEdgeBaseCoefficients {m : ℕ}
    (z₀ : Fin m → Bool) :
    SelectedEdgeBaseCoefficients z₀ :=
  Classical.choice (selectedEdgeBaseCoefficients_nonempty z₀)

noncomputable def selectedEdgeStarParameters {m : ℕ}
    (z₀ : Fin m → Bool) (w : ℂ) :
    DistinguishedStarTwoLocalParameter m → ℂ
  | .constant =>
      (selectedEdgeBaseCoefficients z₀).constant + w
  | .longitudinal =>
      (selectedEdgeBaseCoefficients z₀).longitudinal - 2 * w
  | .transverse =>
      (selectedEdgeBaseCoefficients z₀).transverse
  | .onsite i =>
      (selectedEdgeBaseCoefficients z₀).onsite i
  | .interaction i =>
      (selectedEdgeBaseCoefficients z₀).interaction i

theorem twoLocalStarHamiltonian_eq_selectedEdgeStarParameters
    {m : ℕ} (z₀ : Fin m → Bool) (w : ℂ) :
    twoLocalStarHamiltonianMatrix z₀ w =
      distinguishedStarTwoLocalHamiltonian
        (selectedEdgeStarParameters z₀ w .constant)
        (selectedEdgeStarParameters z₀ w .longitudinal)
        (selectedEdgeStarParameters z₀ w .transverse)
        (fun i => selectedEdgeStarParameters z₀ w (.onsite i))
        (fun i =>
          selectedEdgeStarParameters z₀ w (.interaction i)) := by
  let c := selectedEdgeBaseCoefficients z₀
  have hbase := c.realization
  ext x y
  have hbasexy := congrFun (congrFun hbase x) y
  by_cases hxy : x = y
  · subst y
    rw [twoLocalStarHamiltonian_diagonal]
    simp only [distinguishedStarTwoLocalHamiltonian, if_pos,
      selectedEdgeStarParameters]
    rw [twoLocalStarHamiltonian_diagonal] at hbasexy
    simp only [distinguishedStarTwoLocalHamiltonian, if_pos] at hbasexy
    have henergy :
        (twoLocalSymmetricIsolatedEdgeEnergy z₀ x : ℂ) =
          c.constant +
            c.longitudinal * (boolOccupation x.1 : ℂ) +
            ∑ i, c.onsite i *
              (boolOccupation (x.2 i) : ℂ) +
            ∑ i, c.interaction i *
              (boolOccupation x.1 : ℂ) *
              (boolOccupation (x.2 i) : ℂ) := by
      simpa using hbasexy
    change
      (twoLocalSymmetricIsolatedEdgeEnergy z₀ x : ℂ) + w -
          2 * w * (boolOccupation x.1 : ℂ) =
        (c.constant + w) +
            (c.longitudinal - 2 * w) *
              (boolOccupation x.1 : ℂ) +
            ∑ i, c.onsite i *
              (boolOccupation (x.2 i) : ℂ) +
            ∑ i, c.interaction i *
              (boolOccupation x.1 : ℂ) *
              (boolOccupation (x.2 i) : ℂ)
    rw [henergy]
    ring
  · change
      twoLocalStarHamiltonianMatrix z₀ w x y =
        distinguishedStarTwoLocalHamiltonian
          (c.constant + w) (c.longitudinal - 2 * w)
          c.transverse c.onsite c.interaction x y
    have hw0 :
        twoLocalStarHamiltonianMatrix z₀ w x y =
          twoLocalStarHamiltonianMatrix z₀ 0 x y := by
      by_cases henv : x.2 = y.2
      · have hbit : x.1 ≠ y.1 := by
          intro hb
          exact hxy (Prod.ext hb henv)
        simp [twoLocalStarHamiltonianMatrix, henv, hbit]
      · simp [twoLocalStarHamiltonianMatrix, henv]
    rw [hw0, hbasexy]
    simp [distinguishedStarTwoLocalHamiltonian, hxy, c]

noncomputable def selectedEdgeHypercubeParameters {m : ℕ}
    (z₀ : Fin m → Bool) (w : ℂ) :
    HypercubeTwoLocalParameter (m + 1) → ℂ
  | .constant =>
      selectedEdgeStarParameters z₀ w .constant
  | .onsite i =>
      embeddedStarOnsite
        (selectedEdgeStarParameters z₀ w .longitudinal)
        (fun j =>
          selectedEdgeStarParameters z₀ w (.onsite j)) i
  | .interaction i j =>
      embeddedStarInteraction
        (fun k =>
          selectedEdgeStarParameters z₀ w (.interaction k)) i j
  | .transverse i =>
      embeddedStarTransverse
        (selectedEdgeStarParameters z₀ w .transverse) i

theorem eval_selectedEdgeHypercubeParameters {m : ℕ}
    (z₀ : Fin m → Bool) (w : ℂ) :
    (universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (selectedEdgeHypercubeParameters z₀ w)) =
      Matrix.reindex (boolEnvironmentEquiv m)
        (boolEnvironmentEquiv m)
        (twoLocalStarHamiltonianMatrix z₀ w) := by
  rw [eval_universalHypercubeTwoLocalPolynomialMatrix]
  change
    hypercubeTwoLocalHamiltonian
        (selectedEdgeStarParameters z₀ w .constant)
        (embeddedStarOnsite
          (selectedEdgeStarParameters z₀ w .longitudinal)
          (fun j =>
            selectedEdgeStarParameters z₀ w (.onsite j)))
        (embeddedStarInteraction
          (fun k =>
            selectedEdgeStarParameters z₀ w (.interaction k)))
        (embeddedStarTransverse
          (selectedEdgeStarParameters z₀ w .transverse)) =
      Matrix.reindex (boolEnvironmentEquiv m)
        (boolEnvironmentEquiv m)
        (twoLocalStarHamiltonianMatrix z₀ w)
  apply
    (Equiv.eq_symm_apply
      (Matrix.reindex (boolEnvironmentEquiv m).symm
        (boolEnvironmentEquiv m).symm)).2
  rw [reindex_hypercubeTwoLocalHamiltonian_eq_distinguishedStar]
  exact
    (twoLocalStarHamiltonian_eq_selectedEdgeStarParameters
      z₀ w).symm

theorem continuous_selectedEdgeHypercubeParameters {m : ℕ}
    (z₀ : Fin m → Bool) :
    Continuous fun s : I =>
      selectedEdgeHypercubeParameters z₀
        (twoLocalSelectedEdgeParameter s) := by
  apply continuous_pi
  intro q
  cases q with
  | constant =>
      simp only [selectedEdgeHypercubeParameters,
        selectedEdgeStarParameters]
      change Continuous
        ((fun _ : I =>
          (selectedEdgeBaseCoefficients z₀).constant) +
            twoLocalSelectedEdgeParameter)
      exact
        continuous_const.add
          continuous_twoLocalSelectedEdgeParameter
  | onsite i =>
      refine Fin.cases ?_ (fun _ => ?_) i
      · simp only [selectedEdgeHypercubeParameters,
          selectedEdgeStarParameters,
          embeddedStarOnsite, Fin.cases_zero]
        change Continuous
          ((fun _ : I =>
              (selectedEdgeBaseCoefficients z₀).longitudinal) -
            (fun _ : I => (2 : ℂ)) *
              twoLocalSelectedEdgeParameter)
        exact
          continuous_const.sub
            (continuous_const.mul
              continuous_twoLocalSelectedEdgeParameter)
      · simp only [selectedEdgeHypercubeParameters,
          selectedEdgeStarParameters,
          embeddedStarOnsite, Fin.cases_succ]
        exact continuous_const
  | interaction i j =>
      refine Fin.cases ?_ (fun _ => ?_) i
      · refine Fin.cases ?_ (fun _ => ?_) j
        · simp only [selectedEdgeHypercubeParameters,
            selectedEdgeStarParameters,
            embeddedStarInteraction, Fin.cases_zero]
          exact continuous_const
        · simp only [selectedEdgeHypercubeParameters,
            selectedEdgeStarParameters,
            embeddedStarInteraction, Fin.cases_zero, Fin.cases_succ]
          exact continuous_const
      · simp only [selectedEdgeHypercubeParameters,
          selectedEdgeStarParameters,
          embeddedStarInteraction, Fin.cases_succ]
        exact continuous_const
  | transverse i =>
      refine Fin.cases ?_ (fun _ => ?_) i
      · simp only [selectedEdgeHypercubeParameters,
          selectedEdgeStarParameters,
          embeddedStarTransverse, Fin.cases_zero]
        exact continuous_const
      · simp only [selectedEdgeHypercubeParameters,
          selectedEdgeStarParameters,
          embeddedStarTransverse, Fin.cases_succ]
        exact continuous_const

theorem selectedEdgeHypercubeParameters_closed {m : ℕ}
    (z₀ : Fin m → Bool) :
    selectedEdgeHypercubeParameters z₀
        (twoLocalSelectedEdgeParameter 1) =
      selectedEdgeHypercubeParameters z₀
        (twoLocalSelectedEdgeParameter 0) := by
  rw [twoLocalSelectedEdgeParameter_closed]

noncomputable def selectedEdgeHypercubeParameterLoop {m : ℕ}
    (z₀ : Fin m → Bool) :
    Path
      (selectedEdgeHypercubeParameters z₀
        (twoLocalSelectedEdgeParameter 0))
      (selectedEdgeHypercubeParameters z₀
        (twoLocalSelectedEdgeParameter 0)) where
  toFun := fun s =>
    selectedEdgeHypercubeParameters z₀
      (twoLocalSelectedEdgeParameter s)
  continuous_toFun :=
    continuous_selectedEdgeHypercubeParameters z₀
  source' := rfl
  target' := selectedEdgeHypercubeParameters_closed z₀

theorem selectedEdgeHypercubeParameterLoop_resultant_ne_zero
    {m : ℕ} (z₀ : Fin m → Bool) (s : I) :
    MvPolynomial.eval
        (selectedEdgeHypercubeParameterLoop z₀ s)
        (matrixCharacteristicResultantPolynomial
          (universalHypercubeTwoLocalPolynomialMatrix (m + 1))) ≠ 0 := by
  change
    (MvPolynomial.eval₂Hom (RingHom.id ℂ)
      (selectedEdgeHypercubeParameters z₀
        (twoLocalSelectedEdgeParameter s)))
      (matrixCharacteristicResultantPolynomial
        (universalHypercubeTwoLocalPolynomialMatrix (m + 1))) ≠ 0
  rw [eval_matrixCharacteristicResultantPolynomial]
  apply
    matrixCharacteristicResultant_ne_zero_of_complete_injective_roots
      ((universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (selectedEdgeHypercubeParameters z₀
            (twoLocalSelectedEdgeParameter s))))
      (fun x => twoLocalCubeEigenvalueLift z₀ x s)
      (twoLocalCubeEigenvalueLift_injective z₀ s)
  intro x
  rw [eval_selectedEdgeHypercubeParameters]
  exact twoLocalCubeEigenvalueLift_root z₀ x s

theorem continuous_relabelHypercubeTwoLocalParameters
    {n : ℕ} (e : Fin n ≃ Fin n) :
    Continuous (relabelHypercubeTwoLocalParameters e :
      (HypercubeTwoLocalParameter n → ℂ) →
        HypercubeTwoLocalParameter n → ℂ) := by
  apply continuous_pi
  intro q
  cases q with
  | constant =>
      exact continuous_apply _
  | onsite i =>
      exact continuous_apply _
  | interaction i j =>
      exact continuous_apply _
  | transverse i =>
      exact continuous_apply _

noncomputable def relabeledSelectedEdgeHypercubeParameterLoop
    {m : ℕ} (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) :
    Path
      (relabelHypercubeTwoLocalParameters e
        (selectedEdgeHypercubeParameters z₀
          (twoLocalSelectedEdgeParameter 0)))
      (relabelHypercubeTwoLocalParameters e
        (selectedEdgeHypercubeParameters z₀
          (twoLocalSelectedEdgeParameter 0))) :=
  (selectedEdgeHypercubeParameterLoop z₀).map
    (continuous_relabelHypercubeTwoLocalParameters e)

noncomputable def relabeledCubeEigenvalueLift {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) (s : I) : ℂ :=
  twoLocalCubeEigenvalueLift z₀
    ((cubeCoordinateRelabel e).symm x) s

theorem relabeledCubeEigenvalueLift_root {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) (s : I) :
    (Matrix.charpoly
      ((universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (relabeledSelectedEdgeHypercubeParameterLoop z₀ e s)))).eval
        (relabeledCubeEigenvalueLift z₀ e x s) = 0 := by
  change
    (Matrix.charpoly
      ((universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
      (MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (relabelHypercubeTwoLocalParameters e
          (selectedEdgeHypercubeParameters z₀
            (twoLocalSelectedEdgeParameter s)))))).eval
        (twoLocalCubeEigenvalueLift z₀
          ((cubeCoordinateRelabel e).symm x) s) = 0
  rw [eval_relabelHypercubeTwoLocalParameters,
    Matrix.charpoly_reindex]
  rw [eval_selectedEdgeHypercubeParameters]
  exact twoLocalCubeEigenvalueLift_root z₀
    ((cubeCoordinateRelabel e).symm x) s

theorem relabeledCubeEigenvalueLift_injective {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (s : I) :
    Function.Injective fun x =>
      relabeledCubeEigenvalueLift z₀ e x s := by
  intro x y h
  apply (cubeCoordinateRelabel e).symm.injective
  exact twoLocalCubeEigenvalueLift_injective z₀ s h

theorem relabeledCubeEigenvalueLift_endpoint {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) :
    relabeledCubeEigenvalueLift z₀ e x 1 =
      relabeledCubeEigenvalueLift z₀ e
        (relabeledTwoLocalCubeSelectedEdgeSwap e z₀ x) 0 := by
  change
    twoLocalCubeEigenvalueLift z₀
        ((cubeCoordinateRelabel e).symm x) 1 =
      twoLocalCubeEigenvalueLift z₀
        ((cubeCoordinateRelabel e).symm
          (relabeledTwoLocalCubeSelectedEdgeSwap e z₀ x)) 0
  rw [twoLocalCubeEigenvalueLift_endpoint]
  congr 1
  simp [relabeledTwoLocalCubeSelectedEdgeSwap,
    Equiv.trans_apply]

theorem relabeledSelectedEdgeHypercubeParameterLoop_resultant_ne_zero
    {m : ℕ} (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (s : I) :
    MvPolynomial.eval
        (relabeledSelectedEdgeHypercubeParameterLoop z₀ e s)
        (matrixCharacteristicResultantPolynomial
          (universalHypercubeTwoLocalPolynomialMatrix (m + 1))) ≠ 0 := by
  change
    (MvPolynomial.eval₂Hom (RingHom.id ℂ)
      (relabeledSelectedEdgeHypercubeParameterLoop z₀ e s))
      (matrixCharacteristicResultantPolynomial
        (universalHypercubeTwoLocalPolynomialMatrix (m + 1))) ≠ 0
  rw [eval_matrixCharacteristicResultantPolynomial]
  exact
    matrixCharacteristicResultant_ne_zero_of_complete_injective_roots
      _
      (fun x => relabeledCubeEigenvalueLift z₀ e x s)
      (relabeledCubeEigenvalueLift_injective z₀ e s)
      (relabeledCubeEigenvalueLift_root z₀ e · s)

theorem everyHypercubeEdge_has_exact_twoLocalParameterLoop
    {m : ℕ} (x : Fin (m + 1) → Bool) (i : Fin (m + 1)) :
    ∃ (p₀ : HypercubeTwoLocalParameter (m + 1) → ℂ)
        (loop : Path p₀ p₀)
        (root :
          (Fin (m + 1) → Bool) → I → ℂ),
      (∀ s,
        MvPolynomial.eval (loop s)
          (matrixCharacteristicResultantPolynomial
            (universalHypercubeTwoLocalPolynomialMatrix (m + 1))) ≠ 0) ∧
      (∀ y s,
        (Matrix.charpoly
          ((universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
            (MvPolynomial.eval₂Hom
              (RingHom.id ℂ) (loop s)))).eval (root y s) = 0) ∧
      (∀ s, Function.Injective fun y => root y s) ∧
      ∀ y,
        root y 1 =
          root ((Equiv.swap x (boolToggle x i)) y) 0 := by
  let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap 0 i
  let z₀ : Fin m → Bool :=
    Fin.tail ((cubeCoordinateRelabel e).symm x)
  have hperm :
      relabeledTwoLocalCubeSelectedEdgeSwap e z₀ =
        Equiv.swap x (boolToggle x i) := by
    simpa [e, z₀] using
      relabeledTwoLocalCubeSelectedEdgeSwap_at e x
  refine
    ⟨relabelHypercubeTwoLocalParameters e
        (selectedEdgeHypercubeParameters z₀
          (twoLocalSelectedEdgeParameter 0)),
      relabeledSelectedEdgeHypercubeParameterLoop z₀ e,
      relabeledCubeEigenvalueLift z₀ e,
      ?_, ?_, ?_, ?_⟩
  · exact
      relabeledSelectedEdgeHypercubeParameterLoop_resultant_ne_zero
        z₀ e
  · exact relabeledCubeEigenvalueLift_root z₀ e
  · exact relabeledCubeEigenvalueLift_injective z₀ e
  · intro y
    rw [← hperm]
    exact relabeledCubeEigenvalueLift_endpoint z₀ e y

end GaloisForLFunctions.HTGeometry
