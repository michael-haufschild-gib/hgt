/-
# The local-extension chart as a polynomial matrix family

The chart Hamiltonian `diag(E ⊕ shift) + M ⊗ edge` is *affine* in the local shifts and in the
entries of the new edge channel, so it is the evaluation of one matrix of polynomials in those
coordinates.  Presenting it that way is what lets the chart escape feed the characteristic-
coefficient pullback: the labeling-orbit obstruction becomes a genuine polynomial in the physical
parameters, nonzero because it is nonzero at one chart point, hence nonzero somewhere inside every
nonempty open set of *real* parameters.

Main results:
* `genericLocalExtensionMatrix`, `chartCoord`, `map_genericLocalExtensionMatrix` — the family.
* `exists_eval_localExtensionPullback_ne_zero` — the complex witness.
* `exists_mem_real_localExtension_quadraticRate_ne_zero` — **fixed-shell nonflatness on the
  extension architecture**: inside every nonempty open set of real chart parameters there is a
  point at which no relabeling of the quadratic-rate relation holds.
-/
import GaloisForLFunctions.HTGeometry.ChartFieldOrbitBridge
import GaloisForLFunctions.HTGeometry.VariableRateMatrixObstruction

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Family

variable {α ρ : Type*} [Fintype α] [Fintype ρ] [DecidableEq α] [DecidableEq ρ]

/-- The coordinate labelling of the chart parameter space: one variable per local shift and one per
edge entry. -/
def chartVar (ρ : Type*) [Fintype ρ] [DecidableEq ρ] :
    (ρ ⊕ ρ × ρ) ≃ Fin (Fintype.card (ρ ⊕ ρ × ρ)) := Fintype.equivFin _

/-- The coordinates of a chart point. -/
def chartCoord (p : (ρ → ℂ) × Matrix ρ ρ ℂ) : Fin (Fintype.card (ρ ⊕ ρ × ρ)) → ℂ :=
  fun t => match (chartVar ρ).symm t with
    | Sum.inl r => p.1 r
    | Sum.inr q => p.2 q.1 q.2

@[simp] theorem chartCoord_shift (p : (ρ → ℂ) × Matrix ρ ρ ℂ) (r : ρ) :
    chartCoord p (chartVar ρ (Sum.inl r)) = p.1 r := by
  rw [chartCoord, Equiv.symm_apply_apply]

@[simp] theorem chartCoord_edge (p : (ρ → ℂ) × Matrix ρ ρ ℂ) (u v : ρ) :
    chartCoord p (chartVar ρ (Sum.inr (u, v))) = p.2 u v := by
  rw [chartCoord, Equiv.symm_apply_apply]

/-- The chart Hamiltonian as a matrix of polynomials in the chart coordinates. -/
def genericLocalExtensionMatrix (E : α → ℂ) (M : Matrix α α ℂ) :
    Matrix (α × ρ) (α × ρ) (MvPolynomial (Fin (Fintype.card (ρ ⊕ ρ × ρ))) ℂ) :=
  fun x y =>
    (if x = y then MvPolynomial.C (E x.1) + MvPolynomial.X (chartVar ρ (Sum.inl x.2)) else 0)
      + MvPolynomial.C (M x.1 y.1) * MvPolynomial.X (chartVar ρ (Sum.inr (x.2, y.2)))

omit [Fintype α] in
/-- **The family evaluates to the chart Hamiltonian.** -/
theorem map_genericLocalExtensionMatrix (E : α → ℂ) (M : Matrix α α ℂ)
    (p : (ρ → ℂ) × Matrix ρ ρ ℂ) :
    (genericLocalExtensionMatrix (ρ := ρ) E M).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (chartCoord p))
      = localExtensionMatrix E p.1 M p.2 := by
  refine Matrix.ext fun x y => ?_
  rw [Matrix.map_apply, localExtensionMatrix, Matrix.add_apply, genericLocalExtensionMatrix]
  show MvPolynomial.eval₂ (RingHom.id ℂ) (chartCoord p) _ = _
  rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_X, chartCoord_edge]
  have hdiag : MvPolynomial.eval₂ (RingHom.id ℂ) (chartCoord p)
      (if x = y then MvPolynomial.C (E x.1) + MvPolynomial.X (chartVar ρ (Sum.inl x.2)) else 0)
      = Matrix.diagonal (layeredEnergy E p.1) x y := by
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, MvPolynomial.eval₂_add, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
        chartCoord_shift, Matrix.diagonal_apply_eq]
      rfl
    · rw [if_neg hxy, MvPolynomial.eval₂_zero, Matrix.diagonal_apply_ne _ hxy]
  rw [hdiag]
  rfl

end Family

/-! ## The obstruction as a polynomial in the physical parameters -/

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- **The complex witness.**  The labeling-orbit obstruction, pulled back through the
characteristic coefficients of the chart family, is a nonzero polynomial. -/
theorem exists_eval_localExtensionPullback_ne_zero [Nonempty A] (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ →
      ((E β : ℂ) - (E α : ℂ)) = ((E δ : ℂ) - (E γ : ℂ)) → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hMherm : M.IsHermitian) (hM : ∀ α β : A, α ≠ β → M β α ≠ 0)
    {z₀ : ℂ}
    (hbase : Function.Injective (layeredEnergy (fun a => (E a : ℂ)) (boolShift z₀)))
    (C : LocalExtensionEigenbranchChart (fun a => (E a : ℂ)) (boolShift z₀) M)
    (c : A × Bool → ℂ) (κ : ℂ) (hzero : ∑ i, c i = 0) (hcne : c ≠ 0) :
    ∃ z : Fin (Fintype.card (Bool ⊕ Bool × Bool)) → ℂ,
      MvPolynomial.eval₂ (RingHom.id ℂ) z
        (quadraticRateObstructionPullback
          (genericLocalExtensionMatrix (ρ := Bool) (fun a => (E a : ℂ)) M) c κ) ≠ 0 := by
  obtain ⟨p, hp, hne⟩ := exists_chart_fieldQuadraticRateOrbitValue_ne_zero hcard hE hgap hMherm hM
    hbase C c κ hzero hcne
  refine ⟨chartCoord p, ?_⟩
  have hroot : ∀ i, matrixCharpolyRelation
      ((genericLocalExtensionMatrix (ρ := Bool) (fun a => (E a : ℂ)) M).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (chartCoord p)), C.branch i p) = 0 := by
    intro i
    rw [map_genericLocalExtensionMatrix]
    exact C.root p hp i
  rw [eval_quadraticRateObstructionPullback _ c κ (chartCoord p) (fun i => C.branch i p)
    (C.simple p hp) hroot]
  exact hne

/-- **Fixed-shell nonflatness on the extension architecture.**  Inside every nonempty open set of
real chart parameters there is a point at which no relabeling of the quadratic-rate relation holds
for any simple root packet of the chart Hamiltonian there. -/
theorem exists_mem_real_localExtension_quadraticRate_ne_zero [Nonempty A]
    (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ →
      ((E β : ℂ) - (E α : ℂ)) = ((E δ : ℂ) - (E γ : ℂ)) → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hMherm : M.IsHermitian) (hM : ∀ α β : A, α ≠ β → M β α ≠ 0)
    {z₀ : ℂ}
    (hbase : Function.Injective (layeredEnergy (fun a => (E a : ℂ)) (boolShift z₀)))
    (C : LocalExtensionEigenbranchChart (fun a => (E a : ℂ)) (boolShift z₀) M)
    (c : A × Bool → ℂ) (κ : ℂ) (hzero : ∑ i, c i = 0) (hcne : c ≠ 0)
    {V : Set (Fin (Fintype.card (Bool ⊕ Bool × Bool)) → ℝ)} (hVopen : IsOpen V)
    (hVne : V.Nonempty) :
    ∃ q ∈ V, ∀ energy : A × Bool → ℂ, Function.Injective energy →
      (∀ i, matrixCharpolyRelation
        ((genericLocalExtensionMatrix (ρ := Bool) (fun a => (E a : ℂ)) M).map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (q t : ℂ))), energy i) = 0) →
      ∀ σ : Equiv.Perm (A × Bool),
        (∑ j, c (σ.symm j) * energy j) ^ 2 - κ * ∑ j, energy j ^ 2 ≠ 0 := by
  obtain ⟨q, hq, hqne⟩ := exists_mem_eval₂_ne_zero_of_exists _
    (exists_eval_localExtensionPullback_ne_zero hcard hE hgap hMherm hM hbase C c κ hzero hcne)
    hVopen hVne
  refine ⟨q, hq, fun energy hinj hroot σ hσ => hqne ?_⟩
  rw [eval_quadraticRateObstructionPullback _ c κ (fun t => (q t : ℂ)) energy hinj hroot]
  exact (fieldQuadraticRateOrbitValue_eq_zero_iff c κ energy).mpr ⟨σ, hσ⟩

end

end GaloisForLFunctions.HTGeometry
