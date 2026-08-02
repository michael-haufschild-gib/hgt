import GaloisForLFunctions.HTGeometry.DiagonalParabolicSpectralBridge
import GaloisForLFunctions.HTGeometry.TwoLocalDiagonalAnchoredMonodromy
import GaloisForLFunctions.HTGeometry.TwoLocalUniversalEdgeMonodromy

/-!
# Every two-local edge monodromy anchored at one named diagonal spectrum

This file embeds the diagonal-anchored local loop and its controlled
connector into the universal all-qubit two-local polynomial family.  It then
uses the parabolic spectral bridge to join every relabelled edge construction
to one fixed simple diagonal Hamiltonian.

Unlike arbitrary simple-spectrum transport, every stage carries an explicit
root packet indexed by the same computational labels.  Hence conjugating a
local loop to the common base preserves the identity of the swapped edge.
-/

open scoped BigOperators

open Topology unitInterval

namespace GaloisForLFunctions.HTGeometry

/-! ## Exact universal coordinates for variable transverse coupling -/

noncomputable def variableSelectedEdgeStarParameters {m : ℕ}
    (z₀ : Fin m → Bool) (w u : ℂ) :
    DistinguishedStarTwoLocalParameter m → ℂ
  | .constant =>
      (selectedEdgeBaseCoefficients z₀).constant + w
  | .longitudinal =>
      (selectedEdgeBaseCoefficients z₀).longitudinal - 2 * w
  | .transverse => u
  | .onsite i =>
      (selectedEdgeBaseCoefficients z₀).onsite i
  | .interaction i =>
      (selectedEdgeBaseCoefficients z₀).interaction i

theorem twoLocalVariableStar_eq_variableSelectedEdgeStarParameters
    {m : ℕ} (z₀ : Fin m → Bool) (w u : ℂ) :
    twoLocalVariableStarHamiltonianMatrix z₀ w u =
      distinguishedStarTwoLocalHamiltonian
        (variableSelectedEdgeStarParameters z₀ w u .constant)
        (variableSelectedEdgeStarParameters z₀ w u .longitudinal)
        (variableSelectedEdgeStarParameters z₀ w u .transverse)
        (fun i =>
          variableSelectedEdgeStarParameters z₀ w u (.onsite i))
        (fun i =>
          variableSelectedEdgeStarParameters z₀ w u
            (.interaction i)) := by
  let c := selectedEdgeBaseCoefficients z₀
  have hold :=
    twoLocalStarHamiltonian_eq_selectedEdgeStarParameters z₀ w
  ext x y
  have hxy := congrFun (congrFun hold x) y
  by_cases henv : x.2 = y.2
  · by_cases hbit : x.1 = y.1
    · have hfull : x = y := Prod.ext hbit henv
      subst y
      calc
        twoLocalVariableStarHamiltonianMatrix z₀ w u x x =
            twoLocalStarHamiltonianMatrix z₀ w x x := by
          rcases x with ⟨b, z⟩
          cases b <;>
            simp [twoLocalVariableStarHamiltonianMatrix,
              twoLocalStarHamiltonianMatrix]
        _ = distinguishedStarTwoLocalHamiltonian
            (variableSelectedEdgeStarParameters z₀ w u .constant)
            (variableSelectedEdgeStarParameters z₀ w u .longitudinal)
            (variableSelectedEdgeStarParameters z₀ w u .transverse)
            (fun i =>
              variableSelectedEdgeStarParameters z₀ w u (.onsite i))
            (fun i =>
              variableSelectedEdgeStarParameters z₀ w u
                (.interaction i)) x x := by
          simpa [variableSelectedEdgeStarParameters,
            selectedEdgeStarParameters,
            distinguishedStarTwoLocalHamiltonian] using hxy
    · have hne : x ≠ y := fun h => hbit (congrArg Prod.fst h)
      simp [twoLocalVariableStarHamiltonianMatrix,
        variableSelectedEdgeStarParameters,
        distinguishedStarTwoLocalHamiltonian,
        henv, hbit, hne]
  · have hne : x ≠ y := fun h => henv (congrArg Prod.snd h)
    simp [twoLocalVariableStarHamiltonianMatrix,
      variableSelectedEdgeStarParameters,
      distinguishedStarTwoLocalHamiltonian, henv, hne]

noncomputable def variableSelectedEdgeHypercubeParameters {m : ℕ}
    (z₀ : Fin m → Bool) (w u : ℂ) :
    HypercubeTwoLocalParameter (m + 1) → ℂ
  | .constant =>
      variableSelectedEdgeStarParameters z₀ w u .constant
  | .onsite i =>
      embeddedStarOnsite
        (variableSelectedEdgeStarParameters z₀ w u .longitudinal)
        (fun j =>
          variableSelectedEdgeStarParameters z₀ w u (.onsite j)) i
  | .interaction i j =>
      embeddedStarInteraction
        (fun k =>
          variableSelectedEdgeStarParameters z₀ w u
            (.interaction k)) i j
  | .transverse i =>
      embeddedStarTransverse
        (variableSelectedEdgeStarParameters z₀ w u .transverse) i

theorem eval_variableSelectedEdgeHypercubeParameters {m : ℕ}
    (z₀ : Fin m → Bool) (w u : ℂ) :
    (universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (variableSelectedEdgeHypercubeParameters z₀ w u)) =
      Matrix.reindex (boolEnvironmentEquiv m)
        (boolEnvironmentEquiv m)
        (twoLocalVariableStarHamiltonianMatrix z₀ w u) := by
  rw [eval_universalHypercubeTwoLocalPolynomialMatrix]
  change
    hypercubeTwoLocalHamiltonian
        (variableSelectedEdgeStarParameters z₀ w u .constant)
        (embeddedStarOnsite
          (variableSelectedEdgeStarParameters z₀ w u .longitudinal)
          (fun j =>
            variableSelectedEdgeStarParameters z₀ w u (.onsite j)))
        (embeddedStarInteraction
          (fun k =>
            variableSelectedEdgeStarParameters z₀ w u
              (.interaction k)))
        (embeddedStarTransverse
          (variableSelectedEdgeStarParameters z₀ w u .transverse)) =
      Matrix.reindex (boolEnvironmentEquiv m)
        (boolEnvironmentEquiv m)
        (twoLocalVariableStarHamiltonianMatrix z₀ w u)
  apply
    (Equiv.eq_symm_apply
      (Matrix.reindex (boolEnvironmentEquiv m).symm
        (boolEnvironmentEquiv m).symm)).2
  rw [reindex_hypercubeTwoLocalHamiltonian_eq_distinguishedStar]
  exact
    (twoLocalVariableStar_eq_variableSelectedEdgeStarParameters
      z₀ w u).symm

theorem continuous_variableSelectedEdgeHypercubeParameters
    {m : ℕ} (z₀ : Fin m → Bool)
    {w u : I → ℂ} (hw : Continuous w) (hu : Continuous u) :
    Continuous fun s =>
      variableSelectedEdgeHypercubeParameters z₀ (w s) (u s) := by
  apply continuous_pi
  intro q
  cases q with
  | constant =>
      change Continuous
        ((fun _ : I =>
          (selectedEdgeBaseCoefficients z₀).constant) + w)
      exact continuous_const.add hw
  | onsite i =>
      refine Fin.cases ?_ (fun _ => ?_) i
      · change Continuous
          ((fun _ : I =>
              (selectedEdgeBaseCoefficients z₀).longitudinal) -
            (fun _ : I => (2 : ℂ)) * w)
        exact continuous_const.sub (continuous_const.mul hw)
      · exact continuous_const
  | interaction i j =>
      refine Fin.cases ?_ (fun _ => ?_) i
      · refine Fin.cases ?_ (fun _ => ?_) j
        · exact continuous_const
        · exact continuous_const
      · exact continuous_const
  | transverse i =>
      refine Fin.cases ?_ (fun _ => ?_) i
      · exact hu
      · exact continuous_const

/-! ## Loop, controlled connector, and named cube roots -/

noncomputable def anchoredEdgeHypercubeParameterLoop {m : ℕ}
    (z₀ : Fin m → Bool) :
    Path
      (variableSelectedEdgeHypercubeParameters z₀ 0 (1 / 2))
      (variableSelectedEdgeHypercubeParameters z₀ 0 (1 / 2)) where
  toFun := fun s =>
    variableSelectedEdgeHypercubeParameters z₀
      (twoLocalAnchoredLongitudinal s)
      (twoLocalAnchoredTransverse s)
  continuous_toFun :=
    continuous_variableSelectedEdgeHypercubeParameters z₀
      continuous_twoLocalAnchoredLongitudinal
      continuous_twoLocalAnchoredTransverse
  source' := by simp
  target' := by simp

noncomputable def anchoredEdgeHypercubeConnector {m : ℕ}
    (z₀ : Fin m → Bool) :
    Path
      (variableSelectedEdgeHypercubeParameters z₀ 0 (1 / 2))
      (variableSelectedEdgeHypercubeParameters z₀ (1 / 2) 0) where
  toFun := fun s =>
    variableSelectedEdgeHypercubeParameters z₀
      (twoLocalDiagonalConnectorLongitudinal s)
      (twoLocalDiagonalConnectorTransverse s)
  continuous_toFun :=
    continuous_variableSelectedEdgeHypercubeParameters z₀
      continuous_twoLocalDiagonalConnectorLongitudinal
      continuous_twoLocalDiagonalConnectorTransverse
  source' := by simp
  target' := by simp

noncomputable def anchoredCubeRoot {m : ℕ}
    (z₀ : Fin m → Bool) (x : Fin (m + 1) → Bool)
    (s : I) : ℂ :=
  twoLocalAnchoredGlobalRoot z₀
    ((boolEnvironmentEquiv m).symm x) s

noncomputable def anchoredConnectorCubeRoot {m : ℕ}
    (z₀ : Fin m → Bool) (x : Fin (m + 1) → Bool)
    (s : I) : ℂ :=
  twoLocalDiagonalConnectorGlobalRoot z₀
    ((boolEnvironmentEquiv m).symm x) s

theorem anchoredCubeRoot_root {m : ℕ}
    (z₀ : Fin m → Bool) (x : Fin (m + 1) → Bool)
    (s : I) :
    (Matrix.charpoly
      ((universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (anchoredEdgeHypercubeParameterLoop z₀ s)))).eval
        (anchoredCubeRoot z₀ x s) = 0 := by
  change
    (Matrix.charpoly
      ((universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (variableSelectedEdgeHypercubeParameters z₀
            (twoLocalAnchoredLongitudinal s)
            (twoLocalAnchoredTransverse s))))).eval
      (twoLocalAnchoredGlobalRoot z₀
        ((boolEnvironmentEquiv m).symm x) s) = 0
  rw [eval_variableSelectedEdgeHypercubeParameters,
    Matrix.charpoly_reindex]
  exact
    twoLocalAnchoredGlobalRoot_fullMatrix_root z₀
      ((boolEnvironmentEquiv m).symm x) s

theorem anchoredConnectorCubeRoot_root {m : ℕ}
    (z₀ : Fin m → Bool) (x : Fin (m + 1) → Bool)
    (s : I) :
    (Matrix.charpoly
      ((universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (anchoredEdgeHypercubeConnector z₀ s)))).eval
        (anchoredConnectorCubeRoot z₀ x s) = 0 := by
  change
    (Matrix.charpoly
      ((universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (variableSelectedEdgeHypercubeParameters z₀
            (twoLocalDiagonalConnectorLongitudinal s)
            (twoLocalDiagonalConnectorTransverse s))))).eval
      (twoLocalDiagonalConnectorGlobalRoot z₀
        ((boolEnvironmentEquiv m).symm x) s) = 0
  rw [eval_variableSelectedEdgeHypercubeParameters,
    Matrix.charpoly_reindex]
  exact
    twoLocalDiagonalConnectorGlobalRoot_fullMatrix_root z₀
      ((boolEnvironmentEquiv m).symm x) s

theorem anchoredCubeRoot_injective {m : ℕ}
    (z₀ : Fin m → Bool) (s : I) :
    Function.Injective fun x => anchoredCubeRoot z₀ x s := by
  intro x y h
  apply (boolEnvironmentEquiv m).symm.injective
  exact twoLocalAnchoredGlobalRoot_injective z₀ s h

theorem anchoredConnectorCubeRoot_injective {m : ℕ}
    (z₀ : Fin m → Bool) (s : I) :
    Function.Injective fun x =>
      anchoredConnectorCubeRoot z₀ x s := by
  intro x y h
  apply (boolEnvironmentEquiv m).symm.injective
  exact twoLocalDiagonalConnectorGlobalRoot_injective z₀ s h

theorem anchoredCubeRoot_endpoint {m : ℕ}
    (z₀ : Fin m → Bool) (x : Fin (m + 1) → Bool) :
    anchoredCubeRoot z₀ x 1 =
      anchoredCubeRoot z₀
        (twoLocalCubeSelectedEdgeSwap z₀ x) 0 := by
  rw [anchoredCubeRoot,
    twoLocalAnchoredGlobalRoot_endpoint]
  rfl

theorem anchoredCubeRoot_eq_connector_at_base {m : ℕ}
    (z₀ : Fin m → Bool) (x : Fin (m + 1) → Bool) :
    anchoredCubeRoot z₀ x 0 =
      anchoredConnectorCubeRoot z₀ x 0 := by
  exact
    twoLocalAnchoredRoot_eq_connectorRoot_at_zero z₀
      ((boolEnvironmentEquiv m).symm x)

/-! ## Real diagonal endpoint and one fixed common base -/

noncomputable def anchoredDiagonalEnergyReal {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) : ℝ :=
  if x.1 then
    -((starIsingBinaryCode z₀ x.2 : ℝ) + 1 / 2)
  else
    (starIsingBinaryCode z₀ x.2 : ℝ) + 1 / 2

theorem coe_anchoredDiagonalEnergyReal {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) :
    (anchoredDiagonalEnergyReal z₀ x : ℂ) =
      twoLocalAnchoredDiagonalEnergy z₀ x := by
  rcases x with ⟨b, z⟩
  cases b <;>
    norm_num [anchoredDiagonalEnergyReal,
      twoLocalAnchoredDiagonalEnergy]

theorem anchoredDiagonalEnergyReal_injective {m : ℕ}
    (z₀ : Fin m → Bool) :
    Function.Injective (anchoredDiagonalEnergyReal z₀) := by
  intro x y h
  apply twoLocalDiagonalConnectorGlobalRoot_injective z₀ 1
  change
    twoLocalDiagonalConnectorGlobalRoot z₀ x 1 =
      twoLocalDiagonalConnectorGlobalRoot z₀ y 1
  rw [twoLocalDiagonalConnectorRoot_at_one,
    twoLocalDiagonalConnectorRoot_at_one,
    ← coe_anchoredDiagonalEnergyReal,
    ← coe_anchoredDiagonalEnergyReal]
  exact_mod_cast h

noncomputable def anchoredDiagonalCubeEnergyReal {m : ℕ}
    (z₀ : Fin m → Bool) (x : Fin (m + 1) → Bool) : ℝ :=
  anchoredDiagonalEnergyReal z₀
    ((boolEnvironmentEquiv m).symm x)

theorem anchoredDiagonalCubeEnergyReal_injective {m : ℕ}
    (z₀ : Fin m → Bool) :
    Function.Injective (anchoredDiagonalCubeEnergyReal z₀) := by
  intro x y h
  apply (boolEnvironmentEquiv m).symm.injective
  exact anchoredDiagonalEnergyReal_injective z₀ h

theorem anchoredConnectorCubeRoot_at_diagonal {m : ℕ}
    (z₀ : Fin m → Bool) (x : Fin (m + 1) → Bool) :
    anchoredConnectorCubeRoot z₀ x 1 =
      (anchoredDiagonalCubeEnergyReal z₀ x : ℂ) := by
  rw [anchoredConnectorCubeRoot,
    twoLocalDiagonalConnectorRoot_at_one]
  exact
    (coe_anchoredDiagonalEnergyReal z₀
      ((boolEnvironmentEquiv m).symm x)).symm

noncomputable def anchoredDiagonalHypercubeParameters {m : ℕ}
    (z₀ : Fin m → Bool) :
    HypercubeTwoLocalParameter (m + 1) → ℂ :=
  variableSelectedEdgeHypercubeParameters z₀ (1 / 2) 0

theorem eval_anchoredDiagonalHypercubeParameters {m : ℕ}
    (z₀ : Fin m → Bool) :
    (universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (anchoredDiagonalHypercubeParameters z₀)) =
      Matrix.diagonal
        (fun x => (anchoredDiagonalCubeEnergyReal z₀ x : ℂ)) := by
  rw [anchoredDiagonalHypercubeParameters,
    eval_variableSelectedEdgeHypercubeParameters,
    twoLocalVariableStar_diagonalAnchor]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [Matrix.reindex_apply,
      anchoredDiagonalCubeEnergyReal,
      coe_anchoredDiagonalEnergyReal]
  · have hsymm :
      (boolEnvironmentEquiv m).symm x ≠
        (boolEnvironmentEquiv m).symm y :=
      (boolEnvironmentEquiv m).symm.injective.ne hxy
    simp [Matrix.reindex_apply, Matrix.diagonal_apply,
      hxy, hsymm]

noncomputable def commonTwoLocalDiagonalParameters (m : ℕ) :
    HypercubeTwoLocalParameter (m + 1) → ℂ :=
  anchoredDiagonalHypercubeParameters (fun _ => false)

noncomputable def commonTwoLocalDiagonalEnergyReal (m : ℕ)
    (x : Fin (m + 1) → Bool) : ℝ :=
  anchoredDiagonalCubeEnergyReal (fun _ => false) x

theorem commonTwoLocalDiagonalEnergyReal_injective (m : ℕ) :
    Function.Injective (commonTwoLocalDiagonalEnergyReal m) :=
  anchoredDiagonalCubeEnergyReal_injective (fun _ => false)

theorem eval_commonTwoLocalDiagonalParameters (m : ℕ) :
    (universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (commonTwoLocalDiagonalParameters m)) =
      Matrix.diagonal
        (fun x => (commonTwoLocalDiagonalEnergyReal m x : ℂ)) :=
  eval_anchoredDiagonalHypercubeParameters (fun _ => false)

/-! ## Relabelled diagonal endpoints and explicit bridge to common base -/

noncomputable def relabeledAnchoredDiagonalParameters {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) :
    HypercubeTwoLocalParameter (m + 1) → ℂ :=
  relabelHypercubeTwoLocalParameters e
    (anchoredDiagonalHypercubeParameters z₀)

noncomputable def relabeledAnchoredDiagonalEnergyReal {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) : ℝ :=
  anchoredDiagonalCubeEnergyReal z₀
    ((cubeCoordinateRelabel e).symm x)

theorem relabeledAnchoredDiagonalEnergyReal_injective {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) :
    Function.Injective
      (relabeledAnchoredDiagonalEnergyReal z₀ e) := by
  intro x y h
  apply (cubeCoordinateRelabel e).symm.injective
  exact anchoredDiagonalCubeEnergyReal_injective z₀ h

theorem eval_relabeledAnchoredDiagonalParameters {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) :
    (universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (relabeledAnchoredDiagonalParameters z₀ e)) =
      Matrix.diagonal
        (fun x =>
          (relabeledAnchoredDiagonalEnergyReal z₀ e x : ℂ)) := by
  rw [relabeledAnchoredDiagonalParameters,
    eval_relabelHypercubeTwoLocalParameters,
    eval_anchoredDiagonalHypercubeParameters]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [Matrix.reindex_apply,
      relabeledAnchoredDiagonalEnergyReal]
  · have hsymm :
      (cubeCoordinateRelabel e).symm x ≠
        (cubeCoordinateRelabel e).symm y :=
      (cubeCoordinateRelabel e).symm.injective.ne hxy
    simp [Matrix.reindex_apply, Matrix.diagonal_apply,
      hxy, hsymm]

/-- Evaluation of the universal linear two-local family commutes with the
parabolic coefficient bridge. -/
theorem eval_parabolicHypercubeCoefficientBridge
    {n : ℕ}
    (p q : HypercubeTwoLocalParameter n → ℂ) (s : I) :
    (universalHypercubeTwoLocalPolynomialMatrix n).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (parabolicCoefficientBridge p q s)) =
      fun x y =>
        (1 - (s : ℝ)) *
            ((universalHypercubeTwoLocalPolynomialMatrix n).map
              (MvPolynomial.eval₂Hom (RingHom.id ℂ) p)) x y +
          ((s : ℝ) +
            Complex.I * ((s : ℝ) * (1 - (s : ℝ)))) *
            ((universalHypercubeTwoLocalPolynomialMatrix n).map
              (MvPolynomial.eval₂Hom (RingHom.id ℂ) q)) x y := by
  rw [eval_universalHypercubeTwoLocalPolynomialMatrix,
    eval_universalHypercubeTwoLocalPolynomialMatrix,
    eval_universalHypercubeTwoLocalPolynomialMatrix]
  ext x y
  let α : ℂ := 1 - (s : ℝ)
  let β : ℂ :=
    (s : ℝ) + Complex.I * ((s : ℝ) * (1 - (s : ℝ)))
  have hcoeff (k : HypercubeTwoLocalParameter n) :
      parabolicCoefficientBridge p q s k =
        α * p k + β * q k := by
    simp [parabolicCoefficientBridge, α, β]
    ring
  have honsite (x : Fin n → Bool) :
      (∑ i,
        parabolicCoefficientBridge p q s (.onsite i) *
          (boolOccupation (x i) : ℂ)) =
        α * (∑ i, p (.onsite i) *
          (boolOccupation (x i) : ℂ)) +
        β * (∑ i, q (.onsite i) *
          (boolOccupation (x i) : ℂ)) := by
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hcoeff]
    ring
  have hinteraction (x : Fin n → Bool) :
      (∑ i, ∑ j,
        parabolicCoefficientBridge p q s (.interaction i j) *
          (boolOccupation (x i) : ℂ) *
          (boolOccupation (x j) : ℂ)) =
        α * (∑ i, ∑ j, p (.interaction i j) *
          (boolOccupation (x i) : ℂ) *
          (boolOccupation (x j) : ℂ)) +
        β * (∑ i, ∑ j, q (.interaction i j) *
          (boolOccupation (x i) : ℂ) *
          (boolOccupation (x j) : ℂ)) := by
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [hcoeff]
    ring
  by_cases hxy : x = y
  · subst y
    simp only [hypercubeTwoLocalHamiltonian, if_pos]
    rw [hcoeff, honsite, hinteraction]
    change
      α * p .constant + β * q .constant +
          (α * (∑ i, p (.onsite i) *
            (boolOccupation (x i) : ℂ)) +
           β * (∑ i, q (.onsite i) *
            (boolOccupation (x i) : ℂ))) +
          (α * (∑ i, ∑ j, p (.interaction i j) *
            (boolOccupation (x i) : ℂ) *
            (boolOccupation (x j) : ℂ)) +
           β * (∑ i, ∑ j, q (.interaction i j) *
            (boolOccupation (x i) : ℂ) *
            (boolOccupation (x j) : ℂ))) =
        α * (p .constant +
          ∑ i, p (.onsite i) * (boolOccupation (x i) : ℂ) +
          ∑ i, ∑ j, p (.interaction i j) *
            (boolOccupation (x i) : ℂ) *
            (boolOccupation (x j) : ℂ)) +
        β * (q .constant +
          ∑ i, q (.onsite i) * (boolOccupation (x i) : ℂ) +
          ∑ i, ∑ j, q (.interaction i j) *
            (boolOccupation (x i) : ℂ) *
            (boolOccupation (x j) : ℂ))
    ring
  · simp only [hypercubeTwoLocalHamiltonian, if_neg hxy]
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : y = boolToggle x i
    · simp [hi, hcoeff, α, β]
    · simp [hi]

noncomputable def edgeToCommonDiagonalParameterPath {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) :
    Path
      (relabeledAnchoredDiagonalParameters z₀ e)
      (commonTwoLocalDiagonalParameters m) where
  toFun := fun s =>
    parabolicCoefficientBridge
      (relabeledAnchoredDiagonalParameters z₀ e)
      (commonTwoLocalDiagonalParameters m) s
  continuous_toFun :=
    continuous_parabolicCoefficientBridge
      (relabeledAnchoredDiagonalParameters z₀ e)
      (commonTwoLocalDiagonalParameters m)
  source' := parabolicCoefficientBridge_zero _ _
  target' := parabolicCoefficientBridge_one _ _

noncomputable def edgeToCommonDiagonalRoot {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) (s : I) : ℂ :=
  diagonalParabolicSpectralBridge
    (relabeledAnchoredDiagonalEnergyReal z₀ e)
    (commonTwoLocalDiagonalEnergyReal m) s x

theorem eval_edgeToCommonDiagonalParameterPath {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (s : I) :
    (universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (edgeToCommonDiagonalParameterPath z₀ e s)) =
      Matrix.diagonal
        (edgeToCommonDiagonalRoot z₀ e · s) := by
  change
    (universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (parabolicCoefficientBridge
            (relabeledAnchoredDiagonalParameters z₀ e)
            (commonTwoLocalDiagonalParameters m) s)) =
      Matrix.diagonal
        (edgeToCommonDiagonalRoot z₀ e · s)
  rw [
    eval_parabolicHypercubeCoefficientBridge,
    eval_relabeledAnchoredDiagonalParameters,
    eval_commonTwoLocalDiagonalParameters]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [Matrix.diagonal_apply,
      edgeToCommonDiagonalRoot,
      diagonalParabolicSpectralBridge]
    ring
  · simp [Matrix.diagonal_apply, hxy]

theorem edgeToCommonDiagonalRoot_root {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) (s : I) :
    (Matrix.charpoly
      ((universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (edgeToCommonDiagonalParameterPath z₀ e s)))).eval
        (edgeToCommonDiagonalRoot z₀ e x s) = 0 := by
  rw [eval_edgeToCommonDiagonalParameterPath]
  exact
    diagonalParabolicSpectralBridge_charpoly_root
      (relabeledAnchoredDiagonalEnergyReal z₀ e)
      (commonTwoLocalDiagonalEnergyReal m) s x

theorem edgeToCommonDiagonalRoot_injective {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (s : I) :
    Function.Injective fun x =>
      edgeToCommonDiagonalRoot z₀ e x s := by
  exact
    diagonalParabolicSpectralBridge_injective
      (relabeledAnchoredDiagonalEnergyReal z₀ e)
      (commonTwoLocalDiagonalEnergyReal m)
      (relabeledAnchoredDiagonalEnergyReal_injective z₀ e)
      (commonTwoLocalDiagonalEnergyReal_injective m) s

@[simp] theorem edgeToCommonDiagonalRoot_zero {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) :
    edgeToCommonDiagonalRoot z₀ e x 0 =
      (relabeledAnchoredDiagonalEnergyReal z₀ e x : ℂ) := by
  simp [edgeToCommonDiagonalRoot]

@[simp] theorem edgeToCommonDiagonalRoot_one {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) :
    edgeToCommonDiagonalRoot z₀ e x 1 =
      (commonTwoLocalDiagonalEnergyReal m x : ℂ) := by
  simp [edgeToCommonDiagonalRoot]

end GaloisForLFunctions.HTGeometry
