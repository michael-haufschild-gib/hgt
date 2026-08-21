/-
# The path shell as the patch space of its diagonal splitting

The commuting diagonal subfamily of the nearest-neighbour Pauli shell -- one `Z` per site and one
`ZZ` per edge -- splits the coefficient labels into a block of size `2n+3` and a transverse block of
size `10n+12`.  Relabelling and regrouping the coordinates is a linear isometry of the coefficient
space onto the patch space of that splitting, so the codimension tube estimates of the incubation
layer and the genericity of the shell live on the same object.

Main results:
* `IsDiagLabel`, `diagLabelEquiv`, `card_diagLabel`, `offDiagLabelEquiv`, `card_offDiagLabel`.
* `pathPatchIsometry` — **the path shell is the patch space of the diagonal splitting**.
* `pathHamiltonianLM`, `norm_pathHamiltonianLM_sub_le` — the shell map and its Lipschitz constant.
* `toSphere_preimage_pathBadSphere_eq_zero` — the degenerate directions stay null.
-/
import GaloisForLFunctions.HTGeometry.PathShellDelayFloor
import GaloisForLFunctions.HTGeometry.SphericalPatchTube
import GaloisForLFunctions.HTGeometry.CrossSphereIsometryTransport
import GaloisForLFunctions.HTGeometry.PathShellProjectiveGenericity
import GaloisForLFunctions.HTGeometry.PathChainLabelIdentification

open MeasureTheory Metric Set
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-- The labels of the commuting diagonal path subfamily: onsite `Z` and edge `ZZ`. -/
def IsDiagLabel : PathLabel n → Prop
  | Sum.inl sq => sq.2 = 2
  | Sum.inr eab => eab.2 = (2, 2)

instance decidableIsDiagLabel : DecidablePred (IsDiagLabel (n := n)) := fun l =>
  match l with
  | Sum.inl sq => inferInstanceAs (Decidable (sq.2 = 2))
  | Sum.inr eab => inferInstanceAs (Decidable (eab.2 = (2, 2)))

/-- The diagonal labels are one per site plus one per edge. -/
def diagLabelEquiv (n : ℕ) :
    {l : PathLabel n // IsDiagLabel l} ≃ Fin (n + 2) ⊕ Fin (n + 1) where
  toFun l :=
    match l with
    | ⟨Sum.inl sq, _⟩ => Sum.inl sq.1
    | ⟨Sum.inr eab, _⟩ => Sum.inr eab.1
  invFun x :=
    match x with
    | Sum.inl s => ⟨Sum.inl (s, 2), rfl⟩
    | Sum.inr e => ⟨Sum.inr (e, (2, 2)), rfl⟩
  left_inv := by
    rintro ⟨l, hl⟩
    cases l with
    | inl sq =>
        obtain ⟨s, q⟩ := sq
        have hq : q = 2 := hl
        subst hq
        rfl
    | inr eab =>
        obtain ⟨e, ab⟩ := eab
        have hq : ab = (2, 2) := hl
        subst hq
        rfl
  right_inv := by
    rintro (s | e) <;> rfl

theorem card_diagLabel (n : ℕ) :
    Fintype.card {l : PathLabel n // IsDiagLabel l} = 2 * n + 3 := by
  rw [Fintype.card_congr (diagLabelEquiv n), Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]
  omega

/-- The off-diagonal labels: two transverse axes per site and eight per edge. -/
def offDiagLabelEquiv (n : ℕ) :
    {l : PathLabel n // ¬ IsDiagLabel l} ≃
      (Fin (n + 2) × {q : Fin 3 // q ≠ 2}) ⊕ (Fin (n + 1) × {ab : Fin 3 × Fin 3 // ab ≠ (2, 2)})
    where
  toFun l :=
    match l with
    | ⟨Sum.inl sq, h⟩ => Sum.inl (sq.1, ⟨sq.2, h⟩)
    | ⟨Sum.inr eab, h⟩ => Sum.inr (eab.1, ⟨eab.2, h⟩)
  invFun x :=
    match x with
    | Sum.inl sq => ⟨Sum.inl (sq.1, sq.2.1), sq.2.2⟩
    | Sum.inr eab => ⟨Sum.inr (eab.1, eab.2.1), eab.2.2⟩
  left_inv := by
    rintro ⟨l, hl⟩
    cases l with
    | inl sq => rfl
    | inr eab => rfl
  right_inv := by
    rintro (⟨s, q⟩ | ⟨e, ab⟩) <;> rfl

theorem card_offDiagLabel (n : ℕ) :
    Fintype.card {l : PathLabel n // ¬ IsDiagLabel l} = 10 * n + 12 := by
  classical
  have hq : Fintype.card {q : Fin 3 // q ≠ 2} = 2 := by
    rw [Fintype.card_subtype_compl]
    simp
  have hab : Fintype.card {ab : Fin 3 × Fin 3 // ab ≠ (2, 2)} = 8 := by
    rw [Fintype.card_subtype_compl]
    simp
  rw [Fintype.card_congr (offDiagLabelEquiv n), Fintype.card_sum, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hq, hab]
  omega


/-- The path labels, split into the diagonal block and its complement. -/
def pathPatchEquiv (n : ℕ) : Fin (2 * n + 3) ⊕ Fin (10 * n + 12) ≃ PathLabel n :=
  (Equiv.sumCongr (Fintype.equivFinOfCardEq (card_diagLabel n)).symm
    (Fintype.equivFinOfCardEq (card_offDiagLabel n)).symm).trans
    (Equiv.sumCompl (IsDiagLabel (n := n)))

/-- **The path shell is the patch space of the diagonal splitting.** -/
def pathPatchIsometry (n : ℕ) :
    PatchSpace (2 * n + 3) (10 * n + 12) ≃ₗᵢ[ℝ] PathShell n :=
  (PiLp.sumPiLpEquivProdLpPiLp 2
      (fun _ : Fin (2 * n + 3) ⊕ Fin (10 * n + 12) => ℝ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (pathPatchEquiv n))


/-- **The path-local Hamiltonian is bounded by the coefficient norm.** -/
theorem norm_pathHamiltonian_le (u : PathShell n) :
    ‖pathHamiltonian u‖ ≤ Real.sqrt (Fintype.card (PathLabel n)) * ‖u‖ := by
  classical
  have hnorm : ‖u‖ = Real.sqrt (∑ l, (WithLp.ofLp u l) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    refine congrArg Real.sqrt (Finset.sum_congr rfl fun l _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
  rw [pathHamiltonian_eq_sum, hnorm]
  exact l2_opNorm_pauliCombination_le (pathWord (n := n)) (fun l => WithLp.ofLp u l)

/-- The path-local Hamiltonian as a real-linear map of the coefficients. -/
def pathHamiltonianLM (n : ℕ) : PathShell n →ₗ[ℝ]
    Matrix (FiniteQubitConfiguration (Fin (n + 2))) (FiniteQubitConfiguration (Fin (n + 2))) ℂ
    where
  toFun := pathHamiltonian
  map_add' u v := by
    rw [pathHamiltonian_eq_sum, pathHamiltonian_eq_sum, pathHamiltonian_eq_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    show ((WithLp.ofLp u l + WithLp.ofLp v l : ℝ) : ℂ) • finitePauliMatrix (pathWord l)
      = ((WithLp.ofLp u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l)
        + ((WithLp.ofLp v l : ℝ) : ℂ) • finitePauliMatrix (pathWord l)
    rw [Complex.ofReal_add, add_smul]
  map_smul' c u := by
    rw [RingHom.id_apply, pathHamiltonian_eq_sum, pathHamiltonian_eq_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    show ((c * WithLp.ofLp u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l)
      = c • (((WithLp.ofLp u l : ℝ) : ℂ) • finitePauliMatrix (pathWord l))
    rw [Complex.ofReal_mul, mul_smul]
    ext x y
    simp [Complex.real_smul]

theorem norm_pathHamiltonianLM_sub_le (u v : PathShell n) :
    ‖pathHamiltonianLM n u - pathHamiltonianLM n v‖
      ≤ Real.sqrt (Fintype.card (PathLabel n)) * ‖u - v‖ := by
  rw [← map_sub]
  exact norm_pathHamiltonian_le (u - v)

theorem isSelfAdjoint_pathHamiltonianLM (u : PathShell n) :
    IsSelfAdjoint (pathHamiltonianLM n u) := isSelfAdjoint_pathHamiltonian u

/-- **The degenerate directions are null in the patch parametrization.** -/
theorem toSphere_preimage_pathBadSphere_eq_zero (k : ℕ) :
    (volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere
        (crossSphereMap (pathPatchIsometry (k + 1)) ⁻¹' pathBadSphere k) = 0 := by
  rw [toSphere_preimage_crossSphereMap (pathPatchIsometry (k + 1))
    (measurableSet_pathBadSphere k)]
  exact toSphere_pathBadSphere_eq_zero k

end GaloisForLFunctions.HTGeometry

end
