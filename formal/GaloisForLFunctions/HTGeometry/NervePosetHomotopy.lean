import Mathlib

/-!
# Comparable monotone maps induce a simplicial homotopy of nerves

If `f ≤ g` pointwise for monotone maps of preorders, the assignment

`(x : Fin(n+1) ⥤ P, α : Fin(n+1) →o Fin 2) ↦ (i ↦ if α i = 0 then f (x i) else g (x i))`

is monotone in `i`: the four cases `α i, α j ∈ {0,1}` with `i ≤ j` are `f x_i ≤ f x_j`,
`f x_i ≤ f x_j ≤ g x_j`, `g x_i ≤ g x_j`, and the impossible `1 ≤ 0`.  It is natural in `⦋n⦌`
because both `x` and `α` are precomposed by the same simplicial operator, so it defines a morphism

`N(P) ⊗ Δ[1] ⟶ N(Q)`

restricting to `N(f)` at the `0` end and `N(g)` at the `1` end — a simplicial homotopy in the sense
of `SSet.Homotopy`, requiring no fibrancy of the target and no model structure.

Consequently a poset deformation retract, `r ∘ i = id` and `i ∘ r ≤ id`, gives an explicit homotopy
equivalence of order complexes, with both directions witnessed.
-/

universe u

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory

namespace GaloisForLFunctions.HTGeometry

variable {P Q : Type u} [Preorder P] [Preorder Q]

/-- Interpolation between two comparable monotone maps along a `Fin 2` coordinate. -/
def orderInterpolate (f g : P →o Q) (p : P) (t : Fin 2) : Q :=
  if t = 0 then f p else g p

@[simp]
theorem orderInterpolate_zero (f g : P →o Q) (p : P) :
    orderInterpolate f g p 0 = f p := by
  simp [orderInterpolate]

@[simp]
theorem orderInterpolate_one (f g : P →o Q) (p : P) :
    orderInterpolate f g p 1 = g p := by
  simp [orderInterpolate]

/-- **The interpolation is monotone in both arguments jointly.** -/
theorem orderInterpolate_mono (f g : P →o Q) (hfg : ∀ p, f p ≤ g p)
    {p p' : P} (hp : p ≤ p') {t t' : Fin 2} (ht : t ≤ t') :
    orderInterpolate f g p t ≤ orderInterpolate f g p' t' := by
  fin_cases t <;> fin_cases t'
  · simpa using f.monotone hp
  · exact le_trans (by simpa using f.monotone hp) (by simpa using hfg p')
  · exact absurd ht (by decide)
  · simpa using g.monotone hp

/-- The interpolating chain of a chain in `P` and a monotone `Fin 2`-labelling. -/
def orderInterpolateChain (f g : P →o Q) (hfg : ∀ p, f p ≤ g p) {n : ℕ}
    (x : Fin (n + 1) →o P) (a : Fin (n + 1) →o Fin 2) : Fin (n + 1) →o Q where
  toFun i := orderInterpolate f g (x i) (a i)
  monotone' _ _ hij := orderInterpolate_mono f g hfg (x.monotone hij) (a.monotone hij)

@[simp]
theorem orderInterpolateChain_apply (f g : P →o Q) (hfg : ∀ p, f p ≤ g p) {n : ℕ}
    (x : Fin (n + 1) →o P) (a : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) :
    orderInterpolateChain f g hfg x a i = orderInterpolate f g (x i) (a i) := rfl

/-- At the `0` end the interpolating chain is `f` applied pointwise. -/
theorem orderInterpolateChain_const_zero (f g : P →o Q) (hfg : ∀ p, f p ≤ g p) {n : ℕ}
    (x : Fin (n + 1) →o P) :
    orderInterpolateChain f g hfg x (OrderHom.const _ (0 : Fin 2)) = f.comp x := by
  ext i
  simp [orderInterpolateChain, orderInterpolate]

/-- At the `1` end the interpolating chain is `g` applied pointwise. -/
theorem orderInterpolateChain_const_one (f g : P →o Q) (hfg : ∀ p, f p ≤ g p) {n : ℕ}
    (x : Fin (n + 1) →o P) :
    orderInterpolateChain f g hfg x (OrderHom.const _ (1 : Fin 2)) = g.comp x := by
  ext i
  simp [orderInterpolateChain, orderInterpolate]

/-- **Naturality.**  Precomposing the chain and the labelling by the same monotone reindexing
commutes with interpolation, which is the simplicial naturality of the homotopy. -/
theorem orderInterpolateChain_comp (f g : P →o Q) (hfg : ∀ p, f p ≤ g p) {m n : ℕ}
    (x : Fin (n + 1) →o P) (a : Fin (n + 1) →o Fin 2) (u : Fin (m + 1) →o Fin (n + 1)) :
    (orderInterpolateChain f g hfg x a).comp u
      = orderInterpolateChain f g hfg (x.comp u) (a.comp u) := by
  ext i
  rfl


/-- The chain of objects of a composable-arrows diagram in a preorder, as an order homomorphism. -/
def orderHomOfComposable {n : ℕ} (x : CategoryTheory.ComposableArrows P n) : Fin (n + 1) →o P where
  toFun i := x.obj i
  monotone' _ _ h := CategoryTheory.leOfHom (x.map (CategoryTheory.homOfLE h))

@[simp]
theorem orderHomOfComposable_apply {n : ℕ} (x : CategoryTheory.ComposableArrows P n)
    (i : Fin (n + 1)) : orderHomOfComposable x i = x.obj i := rfl

/-- A monotone chain read back as a composable-arrows diagram. -/
def composableOfOrderHom {n : ℕ} (x : Fin (n + 1) →o Q) : CategoryTheory.ComposableArrows Q n :=
  x.monotone.functor

@[simp]
theorem composableOfOrderHom_obj {n : ℕ} (x : Fin (n + 1) →o Q) (i : Fin (n + 1)) :
    (composableOfOrderHom x).obj i = x i := rfl

/-- **The homotopy datum at a single simplicial degree.** -/
noncomputable def nerveHomotopyChain (f g : P →o Q) (hfg : ∀ p, f p ≤ g p) {n : ℕ}
    (x : CategoryTheory.ComposableArrows P n) (a : Fin (n + 1) →o Fin 2) :
    CategoryTheory.ComposableArrows Q n :=
  composableOfOrderHom (orderInterpolateChain f g hfg (orderHomOfComposable x) a)

@[simp]
theorem nerveHomotopyChain_obj (f g : P →o Q) (hfg : ∀ p, f p ≤ g p) {n : ℕ}
    (x : CategoryTheory.ComposableArrows P n) (a : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) :
    (nerveHomotopyChain f g hfg x a).obj i = orderInterpolate f g (x.obj i) (a i) := rfl

/-- At the `0` end the homotopy datum is the nerve of `f`. -/
theorem nerveHomotopyChain_zero (f g : P →o Q) (hfg : ∀ p, f p ≤ g p) {n : ℕ}
    (x : CategoryTheory.ComposableArrows P n) :
    nerveHomotopyChain f g hfg x (OrderHom.const _ (0 : Fin 2))
      = x.comp f.monotone.functor := by
  refine CategoryTheory.Functor.ext (fun i => ?_) (fun i j h => Subsingleton.elim _ _)
  simp [nerveHomotopyChain]

/-- At the `1` end the homotopy datum is the nerve of `g`. -/
theorem nerveHomotopyChain_one (f g : P →o Q) (hfg : ∀ p, f p ≤ g p) {n : ℕ}
    (x : CategoryTheory.ComposableArrows P n) :
    nerveHomotopyChain f g hfg x (OrderHom.const _ (1 : Fin 2))
      = x.comp g.monotone.functor := by
  refine CategoryTheory.Functor.ext (fun i => ?_) (fun i j h => Subsingleton.elim _ _)
  simp [nerveHomotopyChain]


/-- **The simplicial homotopy datum.**  Comparable monotone maps induce a morphism
`N(P) ⊗ Δ[1] ⟶ N(Q)`. -/
noncomputable def nerveHomotopyHom (f g : P →o Q) (hfg : ∀ p, f p ≤ g p) :
    CategoryTheory.nerve P ⊗ Δ[1] ⟶ CategoryTheory.nerve Q where
  app Δ := ↾fun z =>
    nerveHomotopyChain f g hfg z.1 (SSet.stdSimplex.objEquiv z.2).toOrderHom
  naturality Δ Δ' φ := rfl

end GaloisForLFunctions.HTGeometry
