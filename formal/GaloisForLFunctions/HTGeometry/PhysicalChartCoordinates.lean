/-
# The one-qubit extension chart in physical coordinates

The chart parameter space of a one-qubit extension is a local field on the new site and an edge
channel on it.  Physically the field is real and the edge is Hermitian, so the physical slice is a
*real* six-parameter family: two field values, two real diagonal edge entries, and the real and
imaginary parts of the single off-diagonal edge entry.

Over the complex numbers that parametrisation is a bijection onto the whole chart, with an explicit
inverse, so a chart statement transports to it verbatim; over the reals it lands exactly in the
Hermitian data of the leaf-extended architecture.

Main results:
* `physShift`, `physEdge`, `physChartCoord` — the parametrisation and its inverse.
* `physShift_star`, `physEdge_isHermitian` — real parameters give physical data.
* `physShift_physChartCoord`, `physEdge_physChartCoord` — the parametrisation is onto.
-/
import GaloisForLFunctions.HTGeometry.LocalExtensionPolynomialFamily

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The local field of the attached qubit in physical coordinates. -/
def physShift (t : Fin 6 → ℂ) : Bool → ℂ
  | false => t 0
  | true => t 1

/-- The edge channel of the attached qubit in physical coordinates: two diagonal entries and the
real and imaginary parts of the single off-diagonal entry. -/
def physEdge (t : Fin 6 → ℂ) : Matrix Bool Bool ℂ
  | false, false => t 2
  | false, true => t 3 + Complex.I * t 4
  | true, false => t 3 - Complex.I * t 4
  | true, true => t 5

/-- Real parameters give a real field. -/
theorem physShift_star {t : Fin 6 → ℂ} (ht : ∀ i, star (t i) = t i) (s : Bool) :
    star (physShift t s) = physShift t s := by
  cases s <;> simp [physShift, ht]

/-- **Real parameters give a Hermitian edge.** -/
theorem physEdge_isHermitian {t : Fin 6 → ℂ} (ht : ∀ i, star (t i) = t i) :
    (physEdge t).IsHermitian := by
  refine Matrix.ext fun u v => ?_
  show star (physEdge t v u) = physEdge t u v
  cases u <;> cases v
  · exact ht 2
  · show star (physEdge t true false) = physEdge t false true
    show star (t 3 - Complex.I * t 4) = t 3 + Complex.I * t 4
    rw [star_sub, star_mul, ht 3, ht 4, Complex.star_def, Complex.conj_I]
    ring
  · show star (physEdge t false true) = physEdge t true false
    show star (t 3 + Complex.I * t 4) = t 3 - Complex.I * t 4
    rw [star_add, star_mul, ht 3, ht 4, Complex.star_def, Complex.conj_I]
    ring
  · exact ht 5

/-- The physical coordinates of a chart point. -/
def physChartCoord (p : (Bool → ℂ) × Matrix Bool Bool ℂ) : Fin 6 → ℂ
  | 0 => p.1 false
  | 1 => p.1 true
  | 2 => p.2 false false
  | 3 => (p.2 false true + p.2 true false) / 2
  | 4 => (p.2 false true - p.2 true false) / (2 * Complex.I)
  | 5 => p.2 true true

theorem physShift_physChartCoord (p : (Bool → ℂ) × Matrix Bool Bool ℂ) :
    physShift (physChartCoord p) = p.1 := by
  funext s
  cases s <;> rfl

theorem physEdge_physChartCoord (p : (Bool → ℂ) × Matrix Bool Bool ℂ) :
    physEdge (physChartCoord p) = p.2 := by
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  refine Matrix.ext fun u v => ?_
  cases u <;> cases v
  · rfl
  · show (p.2 false true + p.2 true false) / 2
        + Complex.I * ((p.2 false true - p.2 true false) / (2 * Complex.I)) = p.2 false true
    field_simp
    ring
  · show (p.2 false true + p.2 true false) / 2
        - Complex.I * ((p.2 false true - p.2 true false) / (2 * Complex.I)) = p.2 true false
    field_simp
    ring
  · rfl

/-! ## The polynomial family in physical coordinates -/

/-- The local field as a polynomial in the physical coordinates. -/
def physShiftPoly : Bool → MvPolynomial (Fin 6) ℂ
  | false => MvPolynomial.X 0
  | true => MvPolynomial.X 1

/-- The edge channel as a matrix of polynomials in the physical coordinates. -/
def physEdgePoly : Bool → Bool → MvPolynomial (Fin 6) ℂ
  | false, false => MvPolynomial.X 2
  | false, true => MvPolynomial.X 3 + MvPolynomial.C Complex.I * MvPolynomial.X 4
  | true, false => MvPolynomial.X 3 - MvPolynomial.C Complex.I * MvPolynomial.X 4
  | true, true => MvPolynomial.X 5

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The chart Hamiltonian as a matrix of polynomials in the physical coordinates. -/
def genericPhysicalLeafMatrix (E : A → ℂ) (M : Matrix A A ℂ) :
    Matrix (A × Bool) (A × Bool) (MvPolynomial (Fin 6) ℂ) :=
  fun x y =>
    (if x = y then MvPolynomial.C (E x.1) + physShiftPoly x.2 else 0)
      + MvPolynomial.C (M x.1 y.1) * physEdgePoly x.2 y.2

omit [Fintype A] in
/-- **The physical family evaluates to the chart Hamiltonian.** -/
theorem map_genericPhysicalLeafMatrix (E : A → ℂ) (M : Matrix A A ℂ) (t : Fin 6 → ℂ) :
    (genericPhysicalLeafMatrix E M).map (MvPolynomial.eval₂Hom (RingHom.id ℂ) t)
      = localExtensionMatrix E (physShift t) M (physEdge t) := by
  refine Matrix.ext fun x y => ?_
  rw [Matrix.map_apply, localExtensionMatrix, Matrix.add_apply, genericPhysicalLeafMatrix]
  show MvPolynomial.eval₂ (RingHom.id ℂ) t _ = _
  have hedge : MvPolynomial.eval₂ (RingHom.id ℂ) t (physEdgePoly x.2 y.2)
      = physEdge t x.2 y.2 := by
    cases hx : x.2 <;> cases hy : y.2 <;>
      simp [physEdgePoly, physEdge, MvPolynomial.eval₂_add, MvPolynomial.eval₂_sub,
        MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  have hshift : MvPolynomial.eval₂ (RingHom.id ℂ) t
      (if x = y then MvPolynomial.C (E x.1) + physShiftPoly x.2 else 0)
      = Matrix.diagonal (layeredEnergy E (physShift t)) x y := by
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, MvPolynomial.eval₂_add, MvPolynomial.eval₂_C, Matrix.diagonal_apply_eq]
      have : MvPolynomial.eval₂ (RingHom.id ℂ) t (physShiftPoly x.2) = physShift t x.2 := by
        cases hx : x.2 <;> simp [physShiftPoly, physShift, MvPolynomial.eval₂_X]
      rw [this]
      rfl
    · rw [if_neg hxy, MvPolynomial.eval₂_zero, Matrix.diagonal_apply_ne _ hxy]
  rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hshift, hedge]
  rfl

/-- **The complex witness in physical coordinates.**  The labeling-orbit obstruction pulled back
through the physical family is a nonzero polynomial. -/
theorem exists_eval_physicalLeafPullback_ne_zero [Nonempty A] (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ →
      ((E β : ℂ) - (E α : ℂ)) = ((E δ : ℂ) - (E γ : ℂ)) → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hMherm : M.IsHermitian) (hM : ∀ α β : A, α ≠ β → M β α ≠ 0)
    {z₀ : ℂ}
    (hbase : Function.Injective (layeredEnergy (fun a => (E a : ℂ)) (boolShift z₀)))
    (C : LocalExtensionEigenbranchChart (fun a => (E a : ℂ)) (boolShift z₀) M)
    (c : A × Bool → ℂ) (κ : ℂ) (hzero : ∑ i, c i = 0) (hcne : c ≠ 0) :
    ∃ t : Fin 6 → ℂ, MvPolynomial.eval₂ (RingHom.id ℂ) t
      (quadraticRateObstructionPullback
        (genericPhysicalLeafMatrix (fun a => (E a : ℂ)) M) c κ) ≠ 0 := by
  obtain ⟨p, hp, hne⟩ := exists_chart_fieldQuadraticRateOrbitValue_ne_zero hcard hE hgap hMherm hM
    hbase C c κ hzero hcne
  refine ⟨physChartCoord p, ?_⟩
  have hroot : ∀ i, matrixCharpolyRelation
      ((genericPhysicalLeafMatrix (fun a => (E a : ℂ)) M).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (physChartCoord p)), C.branch i p) = 0 := by
    intro i
    rw [map_genericPhysicalLeafMatrix, physShift_physChartCoord, physEdge_physChartCoord]
    exact C.root p hp i
  rw [eval_quadraticRateObstructionPullback _ c κ (physChartCoord p) (fun i => C.branch i p)
    (C.simple p hp) hroot]
  exact hne

/-- **Fixed-shell nonflatness in physical coordinates.**  Inside every nonempty open set of real
physical parameters there is a point whose field is real and whose edge is Hermitian -- so the
chart Hamiltonian there is a Hermitian one-qubit extension -- at which no relabeling of the
quadratic-rate relation holds for any simple root packet. -/
theorem exists_mem_real_physicalLeaf_quadraticRate_ne_zero [Nonempty A]
    (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ →
      ((E β : ℂ) - (E α : ℂ)) = ((E δ : ℂ) - (E γ : ℂ)) → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hMherm : M.IsHermitian) (hM : ∀ α β : A, α ≠ β → M β α ≠ 0)
    {z₀ : ℂ}
    (hbase : Function.Injective (layeredEnergy (fun a => (E a : ℂ)) (boolShift z₀)))
    (C : LocalExtensionEigenbranchChart (fun a => (E a : ℂ)) (boolShift z₀) M)
    (c : A × Bool → ℂ) (κ : ℂ) (hzero : ∑ i, c i = 0) (hcne : c ≠ 0)
    {V : Set (Fin 6 → ℝ)} (hVopen : IsOpen V) (hVne : V.Nonempty) :
    ∃ q ∈ V,
      (physEdge (fun i => (q i : ℂ))).IsHermitian ∧
      (∀ s, star (physShift (fun i => (q i : ℂ)) s) = physShift (fun i => (q i : ℂ)) s) ∧
      ∀ energy : A × Bool → ℂ, Function.Injective energy →
        (∀ i, matrixCharpolyRelation
          (localExtensionMatrix (fun a => (E a : ℂ)) (physShift (fun i => (q i : ℂ))) M
            (physEdge (fun i => (q i : ℂ))), energy i) = 0) →
        ∀ σ : Equiv.Perm (A × Bool),
          (∑ j, c (σ.symm j) * energy j) ^ 2 - κ * ∑ j, energy j ^ 2 ≠ 0 := by
  obtain ⟨q, hq, hqne⟩ := exists_mem_eval₂_ne_zero_of_exists _
    (exists_eval_physicalLeafPullback_ne_zero hcard hE hgap hMherm hM hbase C c κ hzero hcne)
    hVopen hVne
  have hreal : ∀ i, star ((q i : ℂ)) = (q i : ℂ) := fun i => Complex.conj_ofReal (q i)
  refine ⟨q, hq, physEdge_isHermitian hreal, physShift_star hreal, ?_⟩
  intro energy hinj hroot σ hσ
  refine hqne ?_
  have hroot' : ∀ i, matrixCharpolyRelation
      ((genericPhysicalLeafMatrix (fun a => (E a : ℂ)) M).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun i => (q i : ℂ))), energy i) = 0 := by
    intro i
    rw [map_genericPhysicalLeafMatrix]
    exact hroot i
  rw [eval_quadraticRateObstructionPullback _ c κ (fun i => (q i : ℂ)) energy hinj hroot']
  exact (fieldQuadraticRateOrbitValue_eq_zero_iff c κ energy).mpr ⟨σ, hσ⟩

end

end GaloisForLFunctions.HTGeometry
