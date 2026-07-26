import GaloisForLFunctions.HTGeometry.CheckerboardBlockTransfer

/-!
# Support of a decomposable eigenvector in a product frame

An eigenvector's coordinates in an eigenbasis vanish at every index carrying a different eigenvalue,
so a decomposable eigenvector of a product frame has coordinate array — the outer product of the two
coordinate vectors — supported on the block of grid points sharing its eigenvalue.

This is what turns the multiplicity pattern of the frame into a support condition on an outer
product, which the block lemmas then resolve into proportionality of the factors.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {K : Type*} [Field K] {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The coordinate array of a decomposable vector in a product frame is the outer product of the
two coordinate vectors. -/
theorem productBasis_repr_segreTensor {a : I → (I → K)} {b : J → (J → K)}
    (e : Basis (I × J) K (Matrix I J K))
    (he : ∀ p, e p = criticalHorizonSegreTensor (a p.1) (b p.2))
    (x : I → K) (y : J → K) (q : I × J) :
    e.repr (criticalHorizonSegreTensor (∑ i, x i • a i) (∑ j, y j • b j)) q =
      x q.1 * y q.2 := by
  rw [criticalHorizonSegreTensor_sum_smul]
  have hsum : ∑ i, ∑ j, (x i * y j) • criticalHorizonSegreTensor (a i) (b j) =
      ∑ p : I × J, (x p.1 * y p.2) • e p := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [he (i, j)]
  rw [hsum]
  simp [map_sum, Basis.repr_self, Finsupp.single_apply, Finset.sum_ite_eq']

/-- **Block support.**  A decomposable eigenvector of a product eigenframe has outer-product
coordinates vanishing at every grid point whose eigenvalue differs from its own. -/
theorem productFrame_outerProduct_eq_zero_of_eigenvalue_ne {a : I → (I → K)} {b : J → (J → K)}
    (e : Basis (I × J) K (Matrix I J K))
    (he : ∀ p, e p = criticalHorizonSegreTensor (a p.1) (b p.2))
    {T : Module.End K (Matrix I J K)} {ν : I × J → K} (hT : ∀ p, T (e p) = ν p • e p)
    {x : I → K} {y : J → K} {lam : K}
    (hv : T (criticalHorizonSegreTensor (∑ i, x i • a i) (∑ j, y j • b j)) =
      lam • criticalHorizonSegreTensor (∑ i, x i • a i) (∑ j, y j • b j))
    {q : I × J} (hq : ν q ≠ lam) :
    x q.1 * y q.2 = 0 := by
  rw [← productBasis_repr_segreTensor e he x y q]
  exact repr_eq_zero_of_eigenvalue_ne e hT hv hq

/-! ### The axis dichotomy

At a grid point whose eigenvalue differs from that of a decomposable eigenvector, one of the two
coordinate vectors vanishes.  Over a two-element index this puts the corresponding factor on one of
the frame's axes, so a decomposable eigenvector always has at least one factor on an axis of the
frame — unless the whole grid carries its eigenvalue, which is the scalar case. -/

/-- One of the two coordinates vanishes at any grid point outside the eigenvalue's block. -/
theorem productFrame_coeff_eq_zero_or {a : I → (I → K)} {b : J → (J → K)}
    (e : Basis (I × J) K (Matrix I J K))
    (he : ∀ p, e p = criticalHorizonSegreTensor (a p.1) (b p.2))
    {T : Module.End K (Matrix I J K)} {ν : I × J → K} (hT : ∀ p, T (e p) = ν p • e p)
    {x : I → K} {y : J → K} {lam : K}
    (hv : T (criticalHorizonSegreTensor (∑ i, x i • a i) (∑ j, y j • b j)) =
      lam • criticalHorizonSegreTensor (∑ i, x i • a i) (∑ j, y j • b j))
    {q : I × J} (hq : ν q ≠ lam) :
    x q.1 = 0 ∨ y q.2 = 0 :=
  mul_eq_zero.mp (productFrame_outerProduct_eq_zero_of_eigenvalue_ne e he hT hv hq)

/-- Over a two-element index, a vanishing coordinate puts the vector on the other axis. -/
theorem eq_smul_of_coeff_eq_zero {a : Fin 2 → (Fin 2 → K)} {x : Fin 2 → K} {v : Fin 2 → K}
    (hv : v = ∑ i, x i • a i) (h0 : v ≠ 0) {i₁ : Fin 2} (hx : x i₁ = 0) :
    ∃ (i : Fin 2) (c : K), c ≠ 0 ∧ i ≠ i₁ ∧ v = c • a i := by
  rw [Fin.sum_univ_two] at hv
  rcases (by omega : i₁ = 0 ∨ i₁ = 1) with rfl | rfl
  · refine ⟨1, x 1, ?_, by decide, ?_⟩
    · intro hc
      refine h0 ?_
      rw [hv, hx, hc]
      simp
    · rw [hv, hx]
      simp
  · refine ⟨0, x 0, ?_, by decide, ?_⟩
    · intro hc
      refine h0 ?_
      rw [hv, hx, hc]
      simp
    · rw [hv, hx]
      simp

/-- **Axis dichotomy.**  If some grid point carries an eigenvalue different from that of a
decomposable eigenvector, then one of its two factors lies on an axis of the frame. -/
theorem productFrame_factor_on_axis {a b : Fin 2 → (Fin 2 → K)}
    (e : Basis (Fin 2 × Fin 2) K (Matrix (Fin 2) (Fin 2) K))
    (he : ∀ p, e p = criticalHorizonSegreTensor (a p.1) (b p.2))
    {T : Module.End K (Matrix (Fin 2) (Fin 2) K)} {ν : Fin 2 × Fin 2 → K}
    (hT : ∀ p, T (e p) = ν p • e p)
    {x y : Fin 2 → K} {u w : Fin 2 → K} (hu : u = ∑ i, x i • a i) (hw : w = ∑ j, y j • b j)
    (hu0 : u ≠ 0) (hw0 : w ≠ 0) {lam : K}
    (hv : T (criticalHorizonSegreTensor u w) = lam • criticalHorizonSegreTensor u w)
    {q : Fin 2 × Fin 2} (hq : ν q ≠ lam) :
    (∃ (i : Fin 2) (c : K), c ≠ 0 ∧ i ≠ q.1 ∧ u = c • a i) ∨
      (∃ (j : Fin 2) (d : K), d ≠ 0 ∧ j ≠ q.2 ∧ w = d • b j) := by
  have hv' : T (criticalHorizonSegreTensor (∑ i, x i • a i) (∑ j, y j • b j)) =
      lam • criticalHorizonSegreTensor (∑ i, x i • a i) (∑ j, y j • b j) := by
    rw [← hu, ← hw]
    exact hv
  rcases productFrame_coeff_eq_zero_or e he hT hv' hq with hx | hy
  · exact Or.inl (eq_smul_of_coeff_eq_zero hu hu0 hx)
  · exact Or.inr (eq_smul_of_coeff_eq_zero hw hw0 hy)

end GaloisForLFunctions.HTGeometry
