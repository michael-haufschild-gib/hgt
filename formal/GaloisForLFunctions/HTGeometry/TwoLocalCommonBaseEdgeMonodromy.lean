import GaloisForLFunctions.HTGeometry.LabeledPolynomialMatrixPath
import GaloisForLFunctions.HTGeometry.TwoLocalUniversalDiagonalAnchoring

/-!
# Every hypercube edge transposition at one fixed two-local base

For every edge of every finite Boolean cube, this file constructs a closed
simple-spectrum loop in the universal two-local polynomial Hamiltonian family
based at the *same* fixed diagonal Hamiltonian.  A complete root packet starts
with the common computational labelling and ends with exactly the chosen edge
transposition.

The proof composes three label-controlled pieces:

1. the reverse parabolic bridge from the common diagonal base to the
   edge-specific diagonal anchor;
2. the reverse transverse-decoupling connector followed by the exact local
   sheet-swap loop;
3. the forward connector and parabolic bridge, relabelled by the swapped
   edge.

The labelled-path groupoid makes the endpoint permutation literal and rules
out the unknown-conjugacy gap left by arbitrary common-base transport.
-/

open Topology unitInterval

namespace GaloisForLFunctions.HTGeometry

/-! ## Relabelled local loop and connector -/

noncomputable def relabeledAnchoredEdgeParameterLoop {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) :
    Path
      (relabelHypercubeTwoLocalParameters e
        (variableSelectedEdgeHypercubeParameters z₀ 0 (1 / 2)))
      (relabelHypercubeTwoLocalParameters e
        (variableSelectedEdgeHypercubeParameters z₀ 0 (1 / 2))) :=
  (anchoredEdgeHypercubeParameterLoop z₀).map
    (continuous_relabelHypercubeTwoLocalParameters e)

noncomputable def relabeledAnchoredEdgeConnector {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) :
    Path
      (relabelHypercubeTwoLocalParameters e
        (variableSelectedEdgeHypercubeParameters z₀ 0 (1 / 2)))
      (relabeledAnchoredDiagonalParameters z₀ e) :=
  (anchoredEdgeHypercubeConnector z₀).map
    (continuous_relabelHypercubeTwoLocalParameters e)

noncomputable def relabeledAnchoredCubeRoot {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) (s : I) : ℂ :=
  anchoredCubeRoot z₀ ((cubeCoordinateRelabel e).symm x) s

noncomputable def relabeledAnchoredConnectorCubeRoot {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) (s : I) : ℂ :=
  anchoredConnectorCubeRoot z₀
    ((cubeCoordinateRelabel e).symm x) s

theorem continuous_relabeledAnchoredCubeRoot {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) :
    Continuous (relabeledAnchoredCubeRoot z₀ e x) := by
  change Continuous fun s =>
    twoLocalAnchoredGlobalRoot z₀
      ((boolEnvironmentEquiv m).symm
        ((cubeCoordinateRelabel e).symm x)) s
  exact
    continuous_twoLocalAnchoredGlobalRoot z₀
      ((boolEnvironmentEquiv m).symm
        ((cubeCoordinateRelabel e).symm x))

theorem continuous_relabeledAnchoredConnectorCubeRoot {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) :
    Continuous (relabeledAnchoredConnectorCubeRoot z₀ e x) := by
  change Continuous fun s =>
    twoLocalDiagonalConnectorGlobalRoot z₀
      ((boolEnvironmentEquiv m).symm
        ((cubeCoordinateRelabel e).symm x)) s
  exact
    continuous_twoLocalDiagonalConnectorGlobalRoot z₀
      ((boolEnvironmentEquiv m).symm
        ((cubeCoordinateRelabel e).symm x))

theorem relabeledAnchoredCubeRoot_root {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) (s : I) :
    (Matrix.charpoly
      ((universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (relabeledAnchoredEdgeParameterLoop z₀ e s)))).eval
        (relabeledAnchoredCubeRoot z₀ e x s) = 0 := by
  change
    (Matrix.charpoly
      ((universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (relabelHypercubeTwoLocalParameters e
            (variableSelectedEdgeHypercubeParameters z₀
              (twoLocalAnchoredLongitudinal s)
              (twoLocalAnchoredTransverse s)))))).eval
      (anchoredCubeRoot z₀
        ((cubeCoordinateRelabel e).symm x) s) = 0
  rw [eval_relabelHypercubeTwoLocalParameters,
    Matrix.charpoly_reindex]
  exact
    anchoredCubeRoot_root z₀
      ((cubeCoordinateRelabel e).symm x) s

theorem relabeledAnchoredConnectorCubeRoot_root {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) (s : I) :
    (Matrix.charpoly
      ((universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (relabeledAnchoredEdgeConnector z₀ e s)))).eval
        (relabeledAnchoredConnectorCubeRoot z₀ e x s) = 0 := by
  change
    (Matrix.charpoly
      ((universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (relabelHypercubeTwoLocalParameters e
            (variableSelectedEdgeHypercubeParameters z₀
              (twoLocalDiagonalConnectorLongitudinal s)
              (twoLocalDiagonalConnectorTransverse s)))))).eval
      (anchoredConnectorCubeRoot z₀
        ((cubeCoordinateRelabel e).symm x) s) = 0
  rw [eval_relabelHypercubeTwoLocalParameters,
    Matrix.charpoly_reindex]
  exact
    anchoredConnectorCubeRoot_root z₀
      ((cubeCoordinateRelabel e).symm x) s

theorem relabeledAnchoredCubeRoot_injective {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (s : I) :
    Function.Injective fun x =>
      relabeledAnchoredCubeRoot z₀ e x s :=
  (anchoredCubeRoot_injective z₀ s).comp
    (cubeCoordinateRelabel e).symm.injective

theorem relabeledAnchoredConnectorCubeRoot_injective {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) (s : I) :
    Function.Injective fun x =>
      relabeledAnchoredConnectorCubeRoot z₀ e x s :=
  (anchoredConnectorCubeRoot_injective z₀ s).comp
    (cubeCoordinateRelabel e).symm.injective

theorem relabeledAnchoredCubeRoot_endpoint {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) :
    relabeledAnchoredCubeRoot z₀ e x 1 =
      relabeledAnchoredCubeRoot z₀ e
        (relabeledTwoLocalCubeSelectedEdgeSwap e z₀ x) 0 := by
  change
    anchoredCubeRoot z₀ ((cubeCoordinateRelabel e).symm x) 1 =
      anchoredCubeRoot z₀
        ((cubeCoordinateRelabel e).symm
          (relabeledTwoLocalCubeSelectedEdgeSwap e z₀ x)) 0
  rw [anchoredCubeRoot_endpoint]
  congr 1
  simp [relabeledTwoLocalCubeSelectedEdgeSwap,
    Equiv.trans_apply]

theorem relabeledAnchoredRoot_eq_connector_at_base {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) :
    relabeledAnchoredCubeRoot z₀ e x 0 =
      relabeledAnchoredConnectorCubeRoot z₀ e x 0 :=
  anchoredCubeRoot_eq_connector_at_base z₀
    ((cubeCoordinateRelabel e).symm x)

theorem relabeledAnchoredConnectorRoot_at_diagonal {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) :
    relabeledAnchoredConnectorCubeRoot z₀ e x 1 =
      (relabeledAnchoredDiagonalEnergyReal z₀ e x : ℂ) :=
  anchoredConnectorCubeRoot_at_diagonal z₀
    ((cubeCoordinateRelabel e).symm x)

/-! ## Labelled-path certificates -/

noncomputable def relabeledLocalBaseRoot {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) : ℂ :=
  relabeledAnchoredCubeRoot z₀ e x 0

noncomputable def relabeledEdgeDiagonalRoot {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1))
    (x : Fin (m + 1) → Bool) : ℂ :=
  (relabeledAnchoredDiagonalEnergyReal z₀ e x : ℂ)

noncomputable def commonTwoLocalDiagonalRoot (m : ℕ)
    (x : Fin (m + 1) → Bool) : ℂ :=
  (commonTwoLocalDiagonalEnergyReal m x : ℂ)

noncomputable def relabeledAnchoredLoopCertificate {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) :
    LabeledPolynomialMatrixPath
      (universalHypercubeTwoLocalPolynomialMatrix (m + 1))
      (relabelHypercubeTwoLocalParameters e
        (variableSelectedEdgeHypercubeParameters z₀ 0 (1 / 2)))
      (relabelHypercubeTwoLocalParameters e
        (variableSelectedEdgeHypercubeParameters z₀ 0 (1 / 2)))
      (relabeledLocalBaseRoot z₀ e)
      (relabeledLocalBaseRoot z₀ e ∘
        relabeledTwoLocalCubeSelectedEdgeSwap e z₀) where
  parameterPath := relabeledAnchoredEdgeParameterLoop z₀ e
  rootPath x :=
    { toFun := relabeledAnchoredCubeRoot z₀ e x
      continuous_toFun :=
        continuous_relabeledAnchoredCubeRoot z₀ e x
      source' := rfl
      target' := relabeledAnchoredCubeRoot_endpoint z₀ e x }
  root_is := relabeledAnchoredCubeRoot_root z₀ e
  root_injective := relabeledAnchoredCubeRoot_injective z₀ e

noncomputable def relabeledAnchoredConnectorCertificate {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) :
    LabeledPolynomialMatrixPath
      (universalHypercubeTwoLocalPolynomialMatrix (m + 1))
      (relabelHypercubeTwoLocalParameters e
        (variableSelectedEdgeHypercubeParameters z₀ 0 (1 / 2)))
      (relabeledAnchoredDiagonalParameters z₀ e)
      (relabeledLocalBaseRoot z₀ e)
      (relabeledEdgeDiagonalRoot z₀ e) where
  parameterPath := relabeledAnchoredEdgeConnector z₀ e
  rootPath x :=
    { toFun := relabeledAnchoredConnectorCubeRoot z₀ e x
      continuous_toFun :=
        continuous_relabeledAnchoredConnectorCubeRoot z₀ e x
      source' :=
        (relabeledAnchoredRoot_eq_connector_at_base z₀ e x).symm
      target' :=
        relabeledAnchoredConnectorRoot_at_diagonal z₀ e x }
  root_is := relabeledAnchoredConnectorCubeRoot_root z₀ e
  root_injective :=
    relabeledAnchoredConnectorCubeRoot_injective z₀ e

noncomputable def edgeToCommonDiagonalCertificate {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) :
    LabeledPolynomialMatrixPath
      (universalHypercubeTwoLocalPolynomialMatrix (m + 1))
      (relabeledAnchoredDiagonalParameters z₀ e)
      (commonTwoLocalDiagonalParameters m)
      (relabeledEdgeDiagonalRoot z₀ e)
      (commonTwoLocalDiagonalRoot m) where
  parameterPath := edgeToCommonDiagonalParameterPath z₀ e
  rootPath x :=
    { toFun := edgeToCommonDiagonalRoot z₀ e x
      continuous_toFun :=
        continuous_diagonalParabolicSpectralBridge
          (relabeledAnchoredDiagonalEnergyReal z₀ e)
          (commonTwoLocalDiagonalEnergyReal m) x
      source' := edgeToCommonDiagonalRoot_zero z₀ e x
      target' := edgeToCommonDiagonalRoot_one z₀ e x }
  root_is := edgeToCommonDiagonalRoot_root z₀ e
  root_injective := edgeToCommonDiagonalRoot_injective z₀ e

noncomputable def edgeToCommonTransportCertificate {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) :
    LabeledPolynomialMatrixPath
      (universalHypercubeTwoLocalPolynomialMatrix (m + 1))
      (relabelHypercubeTwoLocalParameters e
        (variableSelectedEdgeHypercubeParameters z₀ 0 (1 / 2)))
      (commonTwoLocalDiagonalParameters m)
      (relabeledLocalBaseRoot z₀ e)
      (commonTwoLocalDiagonalRoot m) :=
  (relabeledAnchoredConnectorCertificate z₀ e).trans
    (edgeToCommonDiagonalCertificate z₀ e)

/-- Closed common-base loop carrying the exact named local edge
transposition. -/
noncomputable def commonBaseEdgeLoopCertificate {m : ℕ}
    (z₀ : Fin m → Bool)
    (e : Fin (m + 1) ≃ Fin (m + 1)) :
    LabeledPolynomialMatrixPath
      (universalHypercubeTwoLocalPolynomialMatrix (m + 1))
      (commonTwoLocalDiagonalParameters m)
      (commonTwoLocalDiagonalParameters m)
      (commonTwoLocalDiagonalRoot m)
      (commonTwoLocalDiagonalRoot m ∘
        relabeledTwoLocalCubeSelectedEdgeSwap e z₀) :=
  ((edgeToCommonTransportCertificate z₀ e).symm.trans
      (relabeledAnchoredLoopCertificate z₀ e)).trans
    ((edgeToCommonTransportCertificate z₀ e).relabel
      (relabeledTwoLocalCubeSelectedEdgeSwap e z₀))

/-! ## Every hypercube edge at the same base -/

theorem everyHypercubeEdge_has_exact_commonBase_twoLocalLoop
    {m : ℕ} (x : Fin (m + 1) → Bool) (i : Fin (m + 1)) :
    ∃ (loop :
          Path (commonTwoLocalDiagonalParameters m)
            (commonTwoLocalDiagonalParameters m))
        (root : (Fin (m + 1) → Bool) → I → ℂ),
      (∀ s,
        MvPolynomial.eval (loop s)
          (matrixCharacteristicResultantPolynomial
            (universalHypercubeTwoLocalPolynomialMatrix
              (m + 1))) ≠ 0) ∧
      (∀ y s,
        (Matrix.charpoly
          ((universalHypercubeTwoLocalPolynomialMatrix
            (m + 1)).map
            (MvPolynomial.eval₂Hom
              (RingHom.id ℂ) (loop s)))).eval
          (root y s) = 0) ∧
      (∀ s, Function.Injective fun y => root y s) ∧
      (∀ y, root y 0 =
        commonTwoLocalDiagonalRoot m y) ∧
      ∀ y, root y 1 =
        commonTwoLocalDiagonalRoot m
          ((Equiv.swap x (boolToggle x i)) y) := by
  let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap 0 i
  let z₀ : Fin m → Bool :=
    Fin.tail ((cubeCoordinateRelabel e).symm x)
  have hperm :
      relabeledTwoLocalCubeSelectedEdgeSwap e z₀ =
        Equiv.swap x (boolToggle x i) := by
    simpa [e, z₀] using
      relabeledTwoLocalCubeSelectedEdgeSwap_at e x
  let P := commonBaseEdgeLoopCertificate z₀ e
  refine ⟨P.parameterPath, fun y s => P.rootPath y s,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact P.resultant_ne_zero
  · exact P.root_is
  · exact P.root_injective
  · intro y
    exact (P.rootPath y).source
  · intro y
    rw [← hperm]
    exact (P.rootPath y).target

/-! ## Full symmetric common-base monodromy -/

theorem commonTwoLocalDiagonalRoot_injective (m : ℕ) :
    Function.Injective (commonTwoLocalDiagonalRoot m) := by
  intro x y h
  apply commonTwoLocalDiagonalEnergyReal_injective m
  change
    (commonTwoLocalDiagonalEnergyReal m x : ℂ) =
      (commonTwoLocalDiagonalEnergyReal m y : ℂ) at h
  exact_mod_cast h

/-- A permutation is realized when one closed simple-spectrum path at the
fixed common base transports every common root label by that permutation. -/
def commonBaseTwoLocalRealizedPermutation (m : ℕ)
    (perm : Equiv.Perm (Fin (m + 1) → Bool)) : Prop :=
  Nonempty
    (LabeledPolynomialMatrixPath
      (universalHypercubeTwoLocalPolynomialMatrix (m + 1))
      (commonTwoLocalDiagonalParameters m)
      (commonTwoLocalDiagonalParameters m)
      (commonTwoLocalDiagonalRoot m)
      (commonTwoLocalDiagonalRoot m ∘ perm))

noncomputable def commonBaseIdentityCertificate (m : ℕ) :
    LabeledPolynomialMatrixPath
      (universalHypercubeTwoLocalPolynomialMatrix (m + 1))
      (commonTwoLocalDiagonalParameters m)
      (commonTwoLocalDiagonalParameters m)
      (commonTwoLocalDiagonalRoot m)
      (commonTwoLocalDiagonalRoot m) where
  parameterPath := Path.refl _
  rootPath x := Path.refl _
  root_is x s := by
    change
      ((universalHypercubeTwoLocalPolynomialMatrix (m + 1)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (commonTwoLocalDiagonalParameters m))).charpoly.eval
        (commonTwoLocalDiagonalRoot m x) = 0
    rw [eval_commonTwoLocalDiagonalParameters]
    rw [Matrix.charpoly_diagonal, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ x)
    simp [commonTwoLocalDiagonalRoot]
  root_injective _ := commonTwoLocalDiagonalRoot_injective m

theorem commonBaseTwoLocalRealizedPermutation_one (m : ℕ) :
    commonBaseTwoLocalRealizedPermutation m 1 := by
  refine ⟨?_⟩
  simpa [commonBaseTwoLocalRealizedPermutation,
    Function.comp_def] using
      commonBaseIdentityCertificate m

theorem commonBaseTwoLocalRealizedPermutation_mul
    {m : ℕ}
    {permA permB : Equiv.Perm (Fin (m + 1) → Bool)}
    (hA : commonBaseTwoLocalRealizedPermutation m permA)
    (hB : commonBaseTwoLocalRealizedPermutation m permB) :
    commonBaseTwoLocalRealizedPermutation m (permA * permB) := by
  rcases hA with ⟨PA⟩
  rcases hB with ⟨PB⟩
  refine ⟨?_⟩
  simpa [commonBaseTwoLocalRealizedPermutation,
    Function.comp_def, Equiv.Perm.mul_apply] using
    PB.trans (PA.relabel permB)

theorem commonBaseTwoLocalRealizedPermutation_inv
    {m : ℕ} {perm : Equiv.Perm (Fin (m + 1) → Bool)}
    (hperm : commonBaseTwoLocalRealizedPermutation m perm) :
    commonBaseTwoLocalRealizedPermutation m perm⁻¹ := by
  rcases hperm with ⟨P⟩
  refine ⟨?_⟩
  simpa [commonBaseTwoLocalRealizedPermutation,
    Function.comp_def] using
    P.symm.relabel perm.symm

/-- Realized endpoint permutations at the fixed diagonal Hamiltonian form a
subgroup of the full permutation group. -/
def commonBaseTwoLocalMonodromySubgroup (m : ℕ) :
    Subgroup (Equiv.Perm (Fin (m + 1) → Bool)) where
  carrier := commonBaseTwoLocalRealizedPermutation m
  one_mem' := commonBaseTwoLocalRealizedPermutation_one m
  mul_mem' hA hB :=
    commonBaseTwoLocalRealizedPermutation_mul hA hB
  inv_mem' hperm :=
    commonBaseTwoLocalRealizedPermutation_inv hperm

theorem hypercubeEdgeSwaps_subset_commonBaseTwoLocalMonodromy
    (m : ℕ) :
    hypercubeEdgeSwaps (m + 1) ⊆
      commonBaseTwoLocalMonodromySubgroup m := by
  intro perm hperm
  rcases hperm with ⟨x, i, rfl⟩
  let e : Fin (m + 1) ≃ Fin (m + 1) := Equiv.swap 0 i
  let z₀ : Fin m → Bool :=
    Fin.tail ((cubeCoordinateRelabel e).symm x)
  have hperm :
      relabeledTwoLocalCubeSelectedEdgeSwap e z₀ =
        Equiv.swap x (boolToggle x i) := by
    simpa [e, z₀] using
      relabeledTwoLocalCubeSelectedEdgeSwap_at e x
  change
    commonBaseTwoLocalRealizedPermutation m
      (Equiv.swap x (boolToggle x i))
  refine ⟨?_⟩
  simpa [hperm] using
    commonBaseEdgeLoopCertificate z₀ e

/-- **Full common-base symmetric monodromy.**  The spectral monodromy group
of the universal complexified two-local family at the explicit fixed
diagonal Hamiltonian is the full symmetric group. -/
theorem commonBaseTwoLocalMonodromySubgroup_eq_top (m : ℕ) :
    commonBaseTwoLocalMonodromySubgroup m = ⊤ := by
  apply top_unique
  rw [← closure_hypercubeEdgeSwaps (m + 1)]
  exact (Subgroup.closure_le _).mpr
    (hypercubeEdgeSwaps_subset_commonBaseTwoLocalMonodromy m)

/-- Every permutation of every finite Boolean spectrum is realized by a
closed simple-spectrum loop of one universal two-local Hamiltonian family,
all at the same explicit diagonal base. -/
theorem everyPermutation_has_exact_commonBase_twoLocalLoop
    (m : ℕ) (perm : Equiv.Perm (Fin (m + 1) → Bool)) :
    commonBaseTwoLocalRealizedPermutation m perm := by
  change perm ∈ commonBaseTwoLocalMonodromySubgroup m
  rw [commonBaseTwoLocalMonodromySubgroup_eq_top]
  exact Subgroup.mem_top perm

end GaloisForLFunctions.HTGeometry
