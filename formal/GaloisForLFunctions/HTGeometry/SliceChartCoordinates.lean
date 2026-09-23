/-
# The traceless slice of a one-qubit extension chart in real coordinates

Physically the local field of the attached qubit is real and the edge channel is Hermitian.  On the
*split* slice the field is `±z/2` and the edge is a real multiple of the exchange matrix, so the
slice is a real *two*-parameter family whose field is traceless by construction -- which is what
keeps a leaf extension inside the nearest-neighbour Pauli span.

Main results:
* `sliceShift`, `sliceEdge`, `realSliceParameter` — the parametrisation.
* `genericSliceLeafMatrix`, `map_genericSliceLeafMatrix` — the polynomial family.
* `exists_mem_real_sliceLeaf_quadraticRate_ne_zero` — **fixed-shell nonflatness on the traceless
  slice**.
-/
import GaloisForLFunctions.HTGeometry.SliceQuadraticOrbitEscape
import GaloisForLFunctions.HTGeometry.ChartFieldOrbitBridge
import GaloisForLFunctions.HTGeometry.VariableRateMatrixObstruction

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The traceless local field of the attached qubit on the split slice. -/
def sliceShift (t : Fin 2 → ℂ) : Bool → ℂ := boolShift (t 0)

/-- The edge channel of the attached qubit on the split slice. -/
def sliceEdge (t : Fin 2 → ℂ) : Matrix Bool Bool ℂ :=
  t 1 • selectedLayerExchangeMatrix false true

theorem sliceShift_star {t : Fin 2 → ℂ} (ht : ∀ i, star (t i) = t i) (s : Bool) :
    star (sliceShift t s) = sliceShift t s := by
  cases s <;> simp [sliceShift, boolShift, ht 0]

theorem sliceEdge_isHermitian {t : Fin 2 → ℂ} (ht : ∀ i, star (t i) = t i) :
    (sliceEdge t).IsHermitian := by
  refine Matrix.ext fun u v => ?_
  show star (sliceEdge t v u) = sliceEdge t u v
  cases u <;> cases v <;>
    simp [sliceEdge, selectedLayerExchangeMatrix, ht 1]

/-- The slice parametrisation on real coordinates. -/
def realSliceParameter (q : Fin 2 → ℝ) : (Bool → ℂ) × Matrix Bool Bool ℂ :=
  (sliceShift (fun i => (q i : ℂ)), sliceEdge (fun i => (q i : ℂ)))

theorem continuous_realSliceParameter : Continuous realSliceParameter := by
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun b => ?_
    cases b
    · show Continuous fun q : Fin 2 → ℝ => ((q 0 : ℝ) : ℂ) / 2
      fun_prop
    · show Continuous fun q : Fin 2 → ℝ => -(((q 0 : ℝ) : ℂ) / 2)
      fun_prop
  · refine continuous_pi fun u => continuous_pi fun v => ?_
    show Continuous fun q : Fin 2 → ℝ =>
      ((q 1 : ℝ) : ℂ) * selectedLayerExchangeMatrix false true u v
    fun_prop

/-! ## The polynomial family on the slice -/

/-- The traceless local field as a polynomial in the slice coordinates. -/
def sliceShiftPoly : Bool → MvPolynomial (Fin 2) ℂ
  | false => MvPolynomial.C (1 / 2) * MvPolynomial.X 0
  | true => -(MvPolynomial.C (1 / 2) * MvPolynomial.X 0)

/-- The edge channel as a matrix of polynomials in the slice coordinates. -/
def sliceEdgePoly : Bool → Bool → MvPolynomial (Fin 2) ℂ
  | false, false => 0
  | false, true => MvPolynomial.X 1
  | true, false => MvPolynomial.X 1
  | true, true => 0

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The slice Hamiltonian as a matrix of polynomials in the slice coordinates. -/
def genericSliceLeafMatrix (E : A → ℂ) (M : Matrix A A ℂ) :
    Matrix (A × Bool) (A × Bool) (MvPolynomial (Fin 2) ℂ) :=
  fun x y =>
    (if x = y then MvPolynomial.C (E x.1) + sliceShiftPoly x.2 else 0)
      + MvPolynomial.C (M x.1 y.1) * sliceEdgePoly x.2 y.2

omit [Fintype A] in
/-- **The slice family evaluates to the slice Hamiltonian.** -/
theorem map_genericSliceLeafMatrix (E : A → ℂ) (M : Matrix A A ℂ) (t : Fin 2 → ℂ) :
    (genericSliceLeafMatrix E M).map (MvPolynomial.eval₂Hom (RingHom.id ℂ) t)
      = localExtensionMatrix E (sliceShift t) M (sliceEdge t) := by
  refine Matrix.ext fun x y => ?_
  rw [Matrix.map_apply, localExtensionMatrix, Matrix.add_apply, genericSliceLeafMatrix]
  show MvPolynomial.eval₂ (RingHom.id ℂ) t _ = _
  have hedge : MvPolynomial.eval₂ (RingHom.id ℂ) t (sliceEdgePoly x.2 y.2)
      = sliceEdge t x.2 y.2 := by
    cases hx : x.2 <;> cases hy : y.2 <;>
      simp [sliceEdgePoly, sliceEdge, selectedLayerExchangeMatrix, MvPolynomial.eval₂_X]
  have hshift : MvPolynomial.eval₂ (RingHom.id ℂ) t
      (if x = y then MvPolynomial.C (E x.1) + sliceShiftPoly x.2 else 0)
      = Matrix.diagonal (layeredEnergy E (sliceShift t)) x y := by
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, MvPolynomial.eval₂_add, MvPolynomial.eval₂_C, Matrix.diagonal_apply_eq]
      have hs : MvPolynomial.eval₂ (RingHom.id ℂ) t (sliceShiftPoly x.2) = sliceShift t x.2 := by
        cases hx : x.2 <;>
          simp [sliceShiftPoly, sliceShift, boolShift, MvPolynomial.eval₂_X,
            MvPolynomial.eval₂_neg, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C] <;> ring
      rw [hs]
      rfl
    · rw [if_neg hxy, MvPolynomial.eval₂_zero, Matrix.diagonal_apply_ne _ hxy]
  rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hshift, hedge]
  rfl

/-- **The complex witness on the slice.**  The labeling-orbit obstruction pulled back through the
slice family is a nonzero polynomial. -/
theorem exists_eval_sliceLeafPullback_ne_zero [Nonempty A] (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ →
      ((E β : ℂ) - (E α : ℂ)) = ((E δ : ℂ) - (E γ : ℂ)) → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hMherm : M.IsHermitian) (hM : ∀ α β : A, α ≠ β → M β α ≠ 0)
    {z₀ : ℂ}
    (hbase : Function.Injective (layeredEnergy (fun a => (E a : ℂ)) (boolShift z₀)))
    (C : LocalExtensionEigenbranchChart (fun a => (E a : ℂ)) (boolShift z₀) M)
    (c : A × Bool → ℂ) (κ : ℂ) (hzero : ∑ i, c i = 0) (hcne : c ≠ 0) :
    ∃ t : Fin 2 → ℂ, MvPolynomial.eval₂ (RingHom.id ℂ) t
      (quadraticRateObstructionPullback
        (genericSliceLeafMatrix (fun a => (E a : ℂ)) M) c κ) ≠ 0 := by
  have hM' : ∀ α β : A, α ≠ β → M α β * M β α ≠ 0 := fun α β hab =>
    mul_ne_zero (hM β α (Ne.symm hab)) (hM α β hab)
  obtain ⟨z, g, hp, hne⟩ :=
    exists_sliceQuadraticOrbit_ne_zero hcard hE hgap hMherm hM' hbase C c κ hzero hcne
  refine ⟨![z, g], ?_⟩
  have h1 : (selectedPairChartPoint (boolShift z₀) false true z g).1 = sliceShift ![z, g] := by
    show selectedPairShiftLine (boolShift z₀) false true z = sliceShift ![z, g]
    rw [selectedPairShiftLine_boolShift]
    rfl
  have h2 : (selectedPairChartPoint (boolShift z₀) false true z g).2 = sliceEdge ![z, g] := rfl
  have hroot : ∀ i, matrixCharpolyRelation
      ((genericSliceLeafMatrix (fun a => (E a : ℂ)) M).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) ![z, g]),
          C.branch i (selectedPairChartPoint (boolShift z₀) false true z g)) = 0 := by
    intro i
    rw [map_genericSliceLeafMatrix, ← h1, ← h2]
    exact C.root _ hp i
  rw [eval_quadraticRateObstructionPullback _ c κ ![z, g]
    (fun i => C.branch i (selectedPairChartPoint (boolShift z₀) false true z g))
    (C.simple _ hp) hroot]
  rw [fieldQuadraticRateOrbitValue_chart C hp c κ]
  exact hne

/-- **Fixed-shell nonflatness on the traceless slice.**  Inside every nonempty open set of real
slice parameters there is a point whose field is `boolShift` of a real number -- hence traceless --
and whose edge is Hermitian, at which no relabeling of the quadratic-rate relation holds for any
simple root packet. -/
theorem exists_mem_real_sliceLeaf_quadraticRate_ne_zero [Nonempty A] (hcard : 3 ≤ Fintype.card A)
    {E : A → ℝ} (hE : Function.Injective fun a => (E a : ℂ))
    (hgap : ∀ α β γ δ : A, α ≠ β → γ ≠ δ →
      ((E β : ℂ) - (E α : ℂ)) = ((E δ : ℂ) - (E γ : ℂ)) → (α, β) = (γ, δ))
    {M : Matrix A A ℂ} (hMherm : M.IsHermitian) (hM : ∀ α β : A, α ≠ β → M β α ≠ 0)
    {z₀ : ℂ}
    (hbase : Function.Injective (layeredEnergy (fun a => (E a : ℂ)) (boolShift z₀)))
    (C : LocalExtensionEigenbranchChart (fun a => (E a : ℂ)) (boolShift z₀) M)
    (c : A × Bool → ℂ) (κ : ℂ) (hzero : ∑ i, c i = 0) (hcne : c ≠ 0)
    {U : Set (Fin 2 → ℝ)} (hUopen : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U,
      (sliceEdge (fun i => (q i : ℂ))).IsHermitian ∧
      sliceShift (fun i => (q i : ℂ)) = boolShift ((q 0 : ℝ) : ℂ) ∧
      ∀ energy : A × Bool → ℂ, Function.Injective energy →
        (∀ i, matrixCharpolyRelation
          (localExtensionMatrix (fun a => (E a : ℂ)) (sliceShift (fun i => (q i : ℂ))) M
            (sliceEdge (fun i => (q i : ℂ))), energy i) = 0) →
        ∀ σ : Equiv.Perm (A × Bool),
          (∑ j, c (σ.symm j) * energy j) ^ (2 : ℕ) - κ * ∑ j, energy j ^ (2 : ℕ) ≠ 0 := by
  obtain ⟨q, hq, hqne⟩ := exists_mem_eval₂_ne_zero_of_exists _
    (exists_eval_sliceLeafPullback_ne_zero hcard hE hgap hMherm hM hbase C c κ hzero hcne)
    hUopen hUne
  have hreal : ∀ i, star ((q i : ℂ)) = (q i : ℂ) := fun i => Complex.conj_ofReal (q i)
  refine ⟨q, hq, sliceEdge_isHermitian hreal, rfl, ?_⟩
  intro energy hinj hroot σ hσ
  refine hqne ?_
  have hroot' : ∀ i, matrixCharpolyRelation
      ((genericSliceLeafMatrix (fun a => (E a : ℂ)) M).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun i => (q i : ℂ))), energy i) = 0 := by
    intro i
    rw [map_genericSliceLeafMatrix]
    exact hroot i
  rw [eval_quadraticRateObstructionPullback _ c κ (fun i => (q i : ℂ)) energy hinj hroot']
  exact (fieldQuadraticRateOrbitValue_eq_zero_iff c κ energy).mpr ⟨σ, hσ⟩

end

end GaloisForLFunctions.HTGeometry
