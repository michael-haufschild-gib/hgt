import GaloisForLFunctions.HTGeometry.CDGATensorAlgebraMap
import GaloisForLFunctions.HTGeometry.CDGAConstCellTensor

/-!
# The tensor product of algebras through the module layer

Forgetting the action of an algebra on itself turns a morphism of commutative differential graded
algebras into a morphism of differential graded modules with zero action, and the induced map on a
tensor product of algebras is then the module-level comparison in the left variable.  So every
invariance theorem proved for `− ⊗ −` on modules applies verbatim to a tensor product of algebras.

* `HTGeometry.zeroActHom` : a morphism of algebras as a morphism of zero-action modules.
* `HTGeometry.tensorCDGAMap_eq_tensorMapLeft` : the bridge.
* `HTGeometry.tensorCDGAMap_isQuasiIsoFull_of_constCellTower` : invariance for a cell tower.
-/

universe u w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R]
  {X₀ : ℕ → Type w} [∀ n, AddCommGroup (X₀ n)] [∀ n, Module R (X₀ n)] {A₀ : CDGAStructure R X₀}
  {X : ℕ → Type w} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
  {X' : ℕ → Type w} [∀ n, AddCommGroup (X' n)] [∀ n, Module R (X' n)]
  {Y : ℕ → Type w} [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]
  {A : CDGAStructure R X} {A' : CDGAStructure R X'} {B : CDGAStructure R Y}

/-- **A morphism of algebras as a morphism of zero-action modules.** -/
def zeroActHom (φ : CDGAHom A A') :
    CDGAModuleHom (zeroActModule (A := A₀) A) (zeroActModule (A := A₀) A') where
  toFun := φ.toFun
  map_add := φ.map_add
  map_smul := φ.map_smul
  map_act _ _ _ := (φ.mapₗ _).map_zero
  map_d := φ.map_d

/-- **Invariance for a tensor product of algebras.**  Forgetting the actions turns the induced
comparison of tensor products into the module-level comparison in the left variable, so the cell
tower theorem applies verbatim: if the right factor is a tower of cells for the ground ring and the
comparison of left factors is a full quasi-isomorphism, so is the comparison of tensor products. -/
theorem tensorMapLeft_zeroActHom_constCellTower (φ : CDGAHom A A')
    (hφ : (zeroActHom (A₀ := A₀) φ).IsQuasiIsoFull)
    {Yb : ℕ → Type w} [∀ n, AddCommGroup (Yb n)] [∀ n, Module R (Yb n)]
    (Q₀ : CDGAModuleStructure A₀ Yb)
    {W : ℕ → Type w} [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
    {kk : ℕ → ℕ} {ι : ℕ → Type w} [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (bb : ∀ i, Module.Basis (ι i) R (W i))
    (τ : ∀ (i : ℕ) (S : CDGAModuleStructure A₀
        (towerCarrier Yb (fun j => ConstCellCarrier (W j) (kk j)) i)),
      CDGATwist S (constCellModule A₀ (W i) (kk i)))
    (h₀ : (tensorMapLeft (zeroActHom (A₀ := A₀) φ) Q₀).IsQuasiIsoFull) (i : ℕ) :
    (tensorMapLeft (zeroActHom (A₀ := A₀) φ)
      (towerMod Q₀ (fun j => constCellModule A₀ (W j) (kk j)) τ i)).IsQuasiIsoFull :=
  tensorMapLeft_constCellTower_isQuasiIsoFull (zeroActHom (A₀ := A₀) φ) hφ Q₀ bb τ h₀ i

end GaloisForLFunctions.HTGeometry
