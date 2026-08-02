import GaloisForLFunctions.HTGeometry.ObserverMetricSpace
import GaloisForLFunctions.HTGeometry.HermitianApartment

/-!
# Maximal flats of the space of observer metrics

The directions diagonal in one orthonormal frame form a real vector space, linearly parametrized by
their weights, and the traceless ones — the directions whose rays stay in the determinant-one space
of observer metrics — form a subspace of dimension one less than the dimension of the space.  That
is the real rank of the observer-metric geometry: a maximal flat is a Euclidean space of dimension
`N - 1`, so its boundary sphere has dimension `N - 2`, the dimension of an apartment of the
building.

All directions of one flat commute, so by the apartment theorem their degeneration flags lie in a
single apartment.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## The directions diagonal in a frame -/

/-- The Hermitian direction diagonal in a frame with prescribed real weights. -/
noncomputable def diagOp (b : OrthonormalBasis (Fin n) ℂ E) (w : Fin n → ℝ) : E →ₗ[ℂ] E :=
  pieceOperator (fun i => (ℂ ∙ b i)) w

theorem diagOp_apply_basis (b : OrthonormalBasis (Fin n) ℂ E) (w : Fin n → ℝ) (i : Fin n) :
    diagOp b w (b i) = ((w i : ℝ) : ℂ) • b i :=
  pieceOperator_apply_of_mem _
    (fun _ _ hij _ hx _ hy => inner_eq_zero_of_mem_span_singleton b.orthonormal hij hx hy)
    (Submodule.mem_span_singleton_self _)

theorem isSymmetric_diagOp (b : OrthonormalBasis (Fin n) ℂ E) (w : Fin n → ℝ) :
    (diagOp b w).IsSymmetric :=
  isSymmetric_pieceOperator _ _

theorem diagOp_add (b : OrthonormalBasis (Fin n) ℂ E) (w w' : Fin n → ℝ) :
    diagOp b (w + w') = diagOp b w + diagOp b w' := by
  refine Basis.ext b.toBasis fun i => ?_
  rw [OrthonormalBasis.coe_toBasis, LinearMap.add_apply, diagOp_apply_basis, diagOp_apply_basis,
    diagOp_apply_basis]
  simp only [Pi.add_apply, Complex.ofReal_add, add_smul]

theorem diagOp_smul (b : OrthonormalBasis (Fin n) ℂ E) (r : ℝ) (w : Fin n → ℝ) :
    diagOp b (r • w) = (r : ℂ) • diagOp b w := by
  refine Basis.ext b.toBasis fun i => ?_
  rw [OrthonormalBasis.coe_toBasis, LinearMap.smul_apply, diagOp_apply_basis, diagOp_apply_basis]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, smul_smul]

/-- The weights-to-directions map of a frame, as a real-linear map. -/
noncomputable def diagOpₗ (b : OrthonormalBasis (Fin n) ℂ E) :
    (Fin n → ℝ) →ₗ[ℝ] (E →ₗ[ℂ] E) where
  toFun w := diagOp b w
  map_add' := diagOp_add b
  map_smul' r w := by
    rw [diagOp_smul b r w]
    rfl

@[simp] theorem diagOpₗ_apply (b : OrthonormalBasis (Fin n) ℂ E) (w : Fin n → ℝ) :
    diagOpₗ b w = diagOp b w := rfl

/-- **A frame parametrizes its diagonal directions faithfully.** -/
theorem diagOpₗ_injective (b : OrthonormalBasis (Fin n) ℂ E) :
    Function.Injective (diagOpₗ b) := by
  intro w w' h
  funext i
  have hi : diagOp b w (b i) = diagOp b w' (b i) := by rw [show diagOp b w = diagOp b w' from h]
  rw [diagOp_apply_basis, diagOp_apply_basis] at hi
  have := smul_left_injective ℂ (b.orthonormal.ne_zero i) hi
  exact_mod_cast this

/-- **The trace of a diagonal direction is the sum of its weights.** -/
theorem trace_diagOp (b : OrthonormalBasis (Fin n) ℂ E) (w : Fin n → ℝ) :
    LinearMap.trace ℂ E (diagOp b w) = ((∑ i, w i : ℝ) : ℂ) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis,
    toMatrix_diagonal_of_orthonormalBasis b (diagOp_apply_basis b w), Matrix.trace_diagonal,
    Complex.ofReal_sum]

/-! ## The flat of a frame -/

/-- The sum of the weights, as a real-linear functional. -/
noncomputable def weightSum (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i

@[simp] theorem weightSum_apply (w : Fin n → ℝ) : weightSum n w = ∑ i, w i := by
  simp [weightSum]

/-- **A maximal flat**: the traceless directions diagonal in a frame. -/
noncomputable def flat (b : OrthonormalBasis (Fin n) ℂ E) : Submodule ℝ (E →ₗ[ℂ] E) :=
  Submodule.map (diagOpₗ b) (LinearMap.ker (weightSum n))

theorem mem_flat_iff (b : OrthonormalBasis (Fin n) ℂ E) {T : E →ₗ[ℂ] E} :
    T ∈ flat b ↔ ∃ w : Fin n → ℝ, (∑ i, w i) = 0 ∧ diagOp b w = T := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, by simpa using hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, by simpa using hw, rfl⟩

/-- **Every direction of a flat is Hermitian and traceless**, so its ray of observer metrics stays
in the determinant-one space. -/
theorem isSymmetric_and_trace_zero_of_mem_flat (b : OrthonormalBasis (Fin n) ℂ E)
    {T : E →ₗ[ℂ] E} (hT : T ∈ flat b) :
    T.IsSymmetric ∧ LinearMap.trace ℂ E T = 0 := by
  obtain ⟨w, hw, rfl⟩ := (mem_flat_iff b).1 hT
  refine ⟨isSymmetric_diagOp b w, ?_⟩
  rw [trace_diagOp b w, hw]
  simp

/-- **Any two directions of a flat commute.** -/
theorem commute_of_mem_flat (b : OrthonormalBasis (Fin n) ℂ E) {S T : E →ₗ[ℂ] E}
    (hS : S ∈ flat b) (hT : T ∈ flat b) (v : E) : S (T v) = T (S v) := by
  obtain ⟨w, -, rfl⟩ := (mem_flat_iff b).1 hS
  obtain ⟨w', -, rfl⟩ := (mem_flat_iff b).1 hT
  have hbasis : ∀ i, diagOp b w (diagOp b w' (b i)) = diagOp b w' (diagOp b w (b i)) := by
    intro i
    rw [diagOp_apply_basis, diagOp_apply_basis, map_smul, map_smul, diagOp_apply_basis,
      diagOp_apply_basis, smul_smul, smul_smul, mul_comm]
  have hext : (diagOp b w) ∘ₗ (diagOp b w') = (diagOp b w') ∘ₗ (diagOp b w) := by
    refine Basis.ext b.toBasis fun i => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, OrthonormalBasis.coe_toBasis]
    exact hbasis i
  exact congrArg (fun f : E →ₗ[ℂ] E => f v) hext

/-- **The directions of one flat have all their flags in one apartment.**  A maximal flat of the
observer-metric space determines a single apartment of the building at infinity. -/
theorem exists_frame_flat (b : OrthonormalBasis (Fin n) ℂ E) {S T : E →ₗ[ℂ] E}
    (hS : S ∈ flat b) (hT : T ∈ flat b) :
    ∃ (ι : Type) (F : LatticeFrame (Submodule ℂ E) ι ⊤),
      (∀ c : ℝ, ∃ s : Set ι, eigenSum S c = F.span s) ∧
        ∀ c : ℝ, ∃ s : Set ι, eigenSum T c = F.span s :=
  exists_frame_eigenSum_span_commuting (isSymmetric_and_trace_zero_of_mem_flat b hS).1
    (isSymmetric_and_trace_zero_of_mem_flat b hT).1 (commute_of_mem_flat b hS hT)

/-! ## The rank -/

theorem finrank_ker_weightSum (hn : 0 < n) :
    finrank ℝ (LinearMap.ker (weightSum n)) = n - 1 := by
  have hsurj : Function.Surjective (weightSum n) := by
    intro r
    refine ⟨fun i => if i = ⟨0, hn⟩ then r else 0, ?_⟩
    rw [weightSum_apply]
    simp
  have hrange : finrank ℝ (LinearMap.range (weightSum n)) = 1 := by
    rw [LinearMap.range_eq_top.2 hsurj]
    simp
  have hsum := LinearMap.finrank_range_add_finrank_ker (weightSum n)
  rw [hrange] at hsum
  have hdim : finrank ℝ (Fin n → ℝ) = n := by simp
  omega

/-- **A maximal flat has dimension one less than the space.**  That is the real rank of the
observer-metric geometry, so the boundary sphere of a flat has dimension `N - 2` — the dimension of
an apartment of the building. -/
theorem finrank_flat (b : OrthonormalBasis (Fin n) ℂ E) (hn : 0 < n) :
    finrank ℝ (flat b) = n - 1 := by
  rw [flat, ← (Submodule.equivMapOfInjective (diagOpₗ b) (diagOpₗ_injective b)
    (LinearMap.ker (weightSum n))).finrank_eq, finrank_ker_weightSum hn]

end GaloisForLFunctions.HTGeometry
