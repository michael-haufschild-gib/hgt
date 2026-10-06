import GaloisForLFunctions.HTGeometry.SourceResponseFormationEnergy
import GaloisForLFunctions.HTGeometry.ValuatedRectangularCompound
import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator

/-!
# Spectral margin and Plücker reconstruction of the formation Laplacian

For a finite-dimensional source space `V` the formation Laplacian `L = A*A` of a response packet is
a positive symmetric operator.  In an orthonormal eigenbasis `L b_k = μ_k b_k`,
`𝓔(x) = Σ_k μ_k ⟨b_k, x⟩²`, the kernel `K` is spanned by the null eigenvectors, and
`dist(x, K)² = Σ_{μ_k ≠ 0} ⟨b_k, x⟩²`.

* **Part III, (FLP.8).**  If `K ≠ V`, the least positive eigenvalue `λ_F` satisfies
  `𝓔(x) ≥ λ_F dist(x, K)²`, is the largest such constant, and the finite-energy sublevels of the
  descended form on `V/K` are compact.
* **Part V, (FLP.10).**  With `B` the matrix of `A|_{Kᗮ}` in orthonormal bases,
  `pdet(L) = det(BᵀB) = Σ_{|S| = r} det(B_S)²`, which is positive; for `K = 0` a nonzero maximal
  minor is exactly a finite certificate of separation.

The Cauchy–Binet step is the rectangular compound identity `C_r(BᵀB) = C_r(Bᵀ) C_r(B)` read at
the single `r`-subset of the columns.
-/

open Filter Topology Matrix
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry.SourceResponse

/-! ### Cauchy–Binet for a Gram determinant -/

section CauchyBinet

/-- The `r × r` submatrix of `B` on the rows of `S`, enumerated increasingly. -/
def rowMinor {m r : ℕ} (B : Matrix (Fin m) (Fin r) ℝ) (S : Set.powersetCard (Fin m) r) :
    Matrix (Fin r) (Fin r) ℝ :=
  B.submatrix (subsetEnum S) id

/-- The full `r`-subset of `Fin r`. -/
def fullSubset (r : ℕ) : Set.powersetCard (Fin r) r :=
  ⟨Finset.univ, by simp⟩

/-- The increasing enumeration of the full subset is a permutation. -/
def fullSubsetPerm (r : ℕ) : Equiv.Perm (Fin r) :=
  Equiv.ofBijective (subsetEnum (fullSubset r))
    (Finite.injective_iff_bijective.1 (subsetEnum_injective _))

theorem fullSubsetPerm_apply (r : ℕ) (i : Fin r) :
    fullSubsetPerm r i = subsetEnum (fullSubset r) i := rfl

/-- **Cauchy–Binet, `(FLP.21)`**: `det(BᵀB) = Σ_{|S| = r} det(B_S)²`. -/
theorem det_transpose_mul_self_eq_sum_sq {m r : ℕ} (B : Matrix (Fin m) (Fin r) ℝ) :
    (Bᵀ * B).det = ∑ S : Set.powersetCard (Fin m) r, (rowMinor B S).det ^ 2 := by
  set u := fullSubset r
  set σ := fullSubsetPerm r
  have h := congrArg (fun M => M u u) (rectangularCompound_mul r Bᵀ B)
  simp only [Matrix.mul_apply] at h
  -- the left side is `det(BᵀB)`
  have hL : rectangularCompound r (Bᵀ * B) u u = (Bᵀ * B).det := by
    rw [rectangularCompound_apply]
    have : (Matrix.of fun i j => (Bᵀ * B) (subsetEnum u j) (subsetEnum u i)) =
        ((Bᵀ * B).submatrix σ σ)ᵀ := by
      ext i j
      rfl
    rw [this, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
  -- each summand is a squared row minor
  have hR : ∀ S : Set.powersetCard (Fin m) r,
      rectangularCompound r Bᵀ u S * rectangularCompound r B S u = (rowMinor B S).det ^ 2 := by
    intro S
    have h1 : rectangularCompound r Bᵀ u S = ((rowMinor B S).submatrix id σ).det := by
      rw [rectangularCompound_apply]
      congr 1
    have h2 : rectangularCompound r B S u = (((rowMinor B S).submatrix id σ)ᵀ).det := by
      rw [rectangularCompound_apply]
      congr 1
    rw [h1, h2, Matrix.det_transpose, Matrix.det_permute']
    have hs : ((Equiv.Perm.sign σ : ℤ) : ℝ) ^ 2 = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    calc ((Equiv.Perm.sign σ : ℤ) : ℝ) * (rowMinor B S).det *
          (((Equiv.Perm.sign σ : ℤ) : ℝ) * (rowMinor B S).det)
        = ((Equiv.Perm.sign σ : ℤ) : ℝ) ^ 2 * (rowMinor B S).det ^ 2 := by ring
      _ = (rowMinor B S).det ^ 2 := by rw [hs, one_mul]
  rw [← hL, h]
  exact Finset.sum_congr rfl fun S _ => hR S

end CauchyBinet

/-! ### The spectral decomposition of the formation Laplacian -/

section Spectral

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {I : Type*} [Fintype I] [Nonempty I] (P : ResponsePacket I V W) (i₀ : I)

namespace ResponsePacket

omit [Nonempty I] in
theorem laplacian_isSymmetric : (P.laplacian : V →ₗ[ℝ] V).IsSymmetric := fun x y => by
  change ⟪P.laplacian x, y⟫_ℝ = ⟪x, P.laplacian y⟫_ℝ
  simp only [ResponsePacket.laplacian, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

/-- An orthonormal eigenbasis `b_k` of the formation Laplacian. -/
def eigBasis : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V :=
  P.laplacian_isSymmetric.eigenvectorBasis rfl

/-- The eigenvalues `μ_k` of the formation Laplacian. -/
def eig : Fin (Module.finrank ℝ V) → ℝ :=
  P.laplacian_isSymmetric.eigenvalues rfl

omit [Nonempty I] in
theorem laplacian_eigBasis (k : Fin (Module.finrank ℝ V)) :
    P.laplacian (P.eigBasis k) = P.eig k • P.eigBasis k := by
  have h := P.laplacian_isSymmetric.apply_eigenvectorBasis rfl k
  exact h

omit [Nonempty I] in
theorem inner_eigBasis_laplacian (k : Fin (Module.finrank ℝ V)) (x : V) :
    ⟪P.eigBasis k, P.laplacian x⟫_ℝ = P.eig k * ⟪P.eigBasis k, x⟫_ℝ := by
  have hs : ⟪P.laplacian (P.eigBasis k), x⟫_ℝ = ⟪P.eigBasis k, P.laplacian x⟫_ℝ :=
    P.laplacian_isSymmetric _ _
  rw [← hs, laplacian_eigBasis, real_inner_smul_left]

omit [Nonempty I] in
/-- `𝓔(x) = Σ_k μ_k ⟨b_k, x⟩²`. -/
theorem energy_eq_sum_eig (x : V) :
    P.energy x = ∑ k, P.eig k * ⟪P.eigBasis k, x⟫_ℝ ^ 2 := by
  rw [← P.inner_laplacian_self x, ← (P.eigBasis).sum_inner_mul_inner (P.laplacian x) x]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_comm, inner_eigBasis_laplacian]
  ring

omit [Nonempty I] in
theorem eig_nonneg (k : Fin (Module.finrank ℝ V)) : 0 ≤ P.eig k := by
  have h := P.inner_eigBasis_laplacian k (P.eigBasis k)
  rw [real_inner_self_eq_norm_sq, (P.eigBasis).orthonormal.1 k, one_pow, mul_one,
    real_inner_comm, P.inner_laplacian_self] at h
  rw [← h]
  exact P.energy_nonneg _

theorem mem_syncKernel_iff_eig (x : V) :
    x ∈ P.syncKernel i₀ ↔ ∀ k, P.eig k ≠ 0 → ⟪P.eigBasis k, x⟫_ℝ = 0 := by
  rw [← P.energy_eq_zero_iff i₀, energy_eq_sum_eig,
    Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (P.eig_nonneg k) (sq_nonneg _)]
  refine forall_congr' fun k => ⟨fun h hk => ?_, fun h _ => ?_⟩
  · rcases mul_eq_zero.1 (h (Finset.mem_univ k)) with h1 | h1
    · exact absurd h1 hk
    · exact (pow_eq_zero_iff two_ne_zero).1 h1
  · by_cases hk : P.eig k = 0
    · rw [hk, zero_mul]
    · rw [h hk]
      ring

theorem eigBasis_mem_syncKernel {k : Fin (Module.finrank ℝ V)} (hk : P.eig k = 0) :
    P.eigBasis k ∈ P.syncKernel i₀ := by
  rw [mem_syncKernel_iff_eig]
  intro j hj
  have hjk : j ≠ k := fun h => hj (h ▸ hk)
  exact (P.eigBasis).orthonormal.2 hjk

theorem eigBasis_mem_orthogonal {k : Fin (Module.finrank ℝ V)} (hk : P.eig k ≠ 0) :
    P.eigBasis k ∈ (P.syncKernel i₀)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  rw [real_inner_comm]
  exact (P.mem_syncKernel_iff_eig i₀ v).1 hv k hk

omit [FiniteDimensional ℝ W] [Fintype I] [Nonempty I] in
theorem infDist_eq_norm (x : V) :
    Metric.infDist x (P.syncKernel i₀) = ‖x - (P.syncKernel i₀).starProjection x‖ := by
  rw [Submodule.starProjection_minimal, Metric.infDist_eq_iInf]
  simp only [dist_eq_norm]
  rfl

/-- `dist(x, K)² = Σ_{μ_k ≠ 0} ⟨b_k, x⟩²`. -/
theorem infDist_sq_eq (x : V) :
    Metric.infDist x (P.syncKernel i₀) ^ 2 =
      ∑ k ∈ Finset.univ.filter (fun k => P.eig k ≠ 0), ⟪P.eigBasis k, x⟫_ℝ ^ 2 := by
  classical
  set y : V := ∑ k ∈ Finset.univ.filter (fun k => P.eig k = 0), ⟪P.eigBasis k, x⟫_ℝ • P.eigBasis k
  have hy : y ∈ P.syncKernel i₀ := Submodule.sum_mem _ fun k hk =>
    Submodule.smul_mem _ _ (P.eigBasis_mem_syncKernel i₀ (Finset.mem_filter.1 hk).2)
  have hxy : x - y = ∑ k ∈ Finset.univ.filter (fun k => P.eig k ≠ 0),
      ⟪P.eigBasis k, x⟫_ℝ • P.eigBasis k := by
    have h := (P.eigBasis).sum_repr' x
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => P.eig k = 0)] at h
    nth_rewrite 1 [← h]
    simp only [y, add_sub_cancel_left, ne_eq]
  have hproj : (P.syncKernel i₀).starProjection x = y := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hy fun w hw => ?_
    rw [hxy, sum_inner]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [real_inner_smul_left, (P.mem_syncKernel_iff_eig i₀ w).1 hw k (Finset.mem_filter.1 hk).2,
      mul_zero]
  rw [infDist_eq_norm, hproj, hxy,
    norm_sq_sum_smul_orthonormal (P.eigBasis).orthonormal]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

omit [FiniteDimensional ℝ W] [Fintype I] [Nonempty I] in
theorem infDist_eq_norm_of_mem_orthogonal {x : V} (hx : x ∈ (P.syncKernel i₀)ᗮ) :
    Metric.infDist x (P.syncKernel i₀) = ‖x‖ := by
  have h0 : (P.syncKernel i₀).starProjection x = 0 := by
    rw [Submodule.starProjection_apply, Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hx,
      Submodule.coe_zero]
  rw [infDist_eq_norm, h0, sub_zero]

/-! ### Part III: finite-dimensional quotient properness -/

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- **Part III**, trivial case: if `K = V` the energy vanishes identically. -/
theorem energy_eq_zero_of_syncKernel_eq_top (hK : P.syncKernel i₀ = ⊤) (x : V) :
    P.energy x = 0 :=
  (P.energy_eq_zero_iff i₀ x).2 (hK ▸ Submodule.mem_top)

theorem exists_eig_ne_zero (hK : P.syncKernel i₀ ≠ ⊤) : ∃ k, P.eig k ≠ 0 := by
  by_contra! h
  apply hK
  rw [eq_top_iff]
  intro x _
  rw [mem_syncKernel_iff_eig]
  intro k hk
  exact absurd (h k) hk

theorem positiveEig_nonempty (hK : P.syncKernel i₀ ≠ ⊤) :
    ((Finset.univ.filter fun k => P.eig k ≠ 0).image P.eig).Nonempty := by
  obtain ⟨k, hk⟩ := P.exists_eig_ne_zero i₀ hK
  exact ⟨P.eig k, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩)⟩

/-- The least positive eigenvalue `λ_F` of the formation Laplacian (when `K ≠ V`). -/
def leastPositiveEig (hK : P.syncKernel i₀ ≠ ⊤) : ℝ :=
  ((Finset.univ.filter fun k => P.eig k ≠ 0).image P.eig).min' (P.positiveEig_nonempty i₀ hK)

theorem leastPositiveEig_spec (hK : P.syncKernel i₀ ≠ ⊤) :
    (∃ k, P.eig k ≠ 0 ∧ P.eig k = P.leastPositiveEig i₀ hK) ∧
      ∀ k, P.eig k ≠ 0 → P.leastPositiveEig i₀ hK ≤ P.eig k := by
  constructor
  · have h := Finset.min'_mem ((Finset.univ.filter fun k => P.eig k ≠ 0).image P.eig)
      (P.positiveEig_nonempty i₀ hK)
    obtain ⟨k, hk, hk'⟩ := Finset.mem_image.1 h
    exact ⟨k, (Finset.mem_filter.1 hk).2, hk'⟩
  · intro k hk
    exact Finset.min'_le _ (P.eig k)
      (Finset.mem_image_of_mem P.eig (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩))

/-- **Part III, (FLP.8)**: if `K ≠ V`, the least positive eigenvalue `λ_F` of `L` is positive, is an
eigenvalue, bounds every positive eigenvalue from below, satisfies
`𝓔(x) ≥ λ_F dist(x, K)²`, and is the largest such constant; the finite-energy sublevels on the
orthogonal complement `Kᗮ ≅ V/K` are compact. -/
theorem quotient_properness (hK : P.syncKernel i₀ ≠ ⊤) :
    0 < P.leastPositiveEig i₀ hK ∧
      Module.End.HasEigenvalue (P.laplacian : V →ₗ[ℝ] V) (P.leastPositiveEig i₀ hK) ∧
      (∀ μ, Module.End.HasEigenvalue (P.laplacian : V →ₗ[ℝ] V) μ → 0 < μ →
        P.leastPositiveEig i₀ hK ≤ μ) ∧
      (∀ x, P.leastPositiveEig i₀ hK * Metric.infDist x (P.syncKernel i₀) ^ 2 ≤ P.energy x) ∧
      (∀ c : ℝ, (∀ x, c * Metric.infDist x (P.syncKernel i₀) ^ 2 ≤ P.energy x) →
        c ≤ P.leastPositiveEig i₀ hK) ∧
      ∀ c : ℝ, IsCompact {x | x ∈ (P.syncKernel i₀)ᗮ ∧ P.energy x ≤ c} := by
  obtain ⟨⟨k₀, hk₀, hk₀eq⟩, hmin⟩ := P.leastPositiveEig_spec i₀ hK
  set lamF := P.leastPositiveEig i₀ hK
  have hpos : 0 < lamF := hk₀eq ▸ lt_of_le_of_ne (P.eig_nonneg k₀) (Ne.symm hk₀)
  have hbound : ∀ x, lamF * Metric.infDist x (P.syncKernel i₀) ^ 2 ≤ P.energy x := fun x => by
    rw [P.infDist_sq_eq i₀, energy_eq_sum_eig, Finset.mul_sum,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => P.eig k ≠ 0)]
    have h2 : 0 ≤ ∑ k ∈ Finset.univ.filter (fun k => ¬ P.eig k ≠ 0),
        P.eig k * ⟪P.eigBasis k, x⟫_ℝ ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (P.eig_nonneg k) (sq_nonneg _)
    have h1 : ∑ k ∈ Finset.univ.filter (fun k => P.eig k ≠ 0), lamF * ⟪P.eigBasis k, x⟫_ℝ ^ 2 ≤
        ∑ k ∈ Finset.univ.filter (fun k => P.eig k ≠ 0), P.eig k * ⟪P.eigBasis k, x⟫_ℝ ^ 2 :=
      Finset.sum_le_sum fun k hk =>
        mul_le_mul_of_nonneg_right (hmin k (Finset.mem_filter.1 hk).2) (sq_nonneg _)
    linarith
  refine ⟨hpos, ?_, ?_, hbound, ?_, ?_⟩
  · rw [← hk₀eq]
    have := P.laplacian_isSymmetric.hasEigenvalue_eigenvalues rfl k₀
    simpa [eig] using this
  · intro μ hμ hμpos
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hLv : P.laplacian v = μ • v := Module.End.mem_eigenspace_iff.1 hv.1
    have hv0 : v ≠ 0 := hv.2
    obtain ⟨k, hk⟩ : ∃ k, ⟪P.eigBasis k, v⟫_ℝ ≠ 0 := by
      by_contra! h
      apply hv0
      rw [← (P.eigBasis).sum_repr' v]
      exact Finset.sum_eq_zero fun k _ => by rw [h k, zero_smul]
    have hk' := P.inner_eigBasis_laplacian k v
    rw [hLv, real_inner_smul_right] at hk'
    have heq : P.eig k = μ := mul_right_cancel₀ hk hk'.symm
    exact heq ▸ hmin k (heq ▸ hμpos.ne')
  · intro c hc
    have h := hc (P.eigBasis k₀)
    rw [P.infDist_eq_norm_of_mem_orthogonal i₀ (P.eigBasis_mem_orthogonal i₀ hk₀),
      (P.eigBasis).orthonormal.1 k₀, one_pow, mul_one, ← P.inner_laplacian_self,
      laplacian_eigBasis, real_inner_smul_left, real_inner_self_eq_norm_sq,
      (P.eigBasis).orthonormal.1 k₀, one_pow, mul_one, hk₀eq] at h
    exact h
  · intro c
    have hcont : Continuous P.energy := by
      unfold ResponsePacket.energy
      fun_prop
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (Submodule.isClosed_orthogonal _).inter (isClosed_le hcont continuous_const)
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨Real.sqrt (c / lamF), fun x hx => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have h := hbound x
      rw [P.infDist_eq_norm_of_mem_orthogonal i₀ hx.1] at h
      have hsq : ‖x‖ ^ 2 ≤ c / lamF := by
        rw [le_div_iff₀ hpos]
        linarith [hx.2]
      calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg x)).symm
        _ ≤ Real.sqrt (c / lamF) := Real.sqrt_le_sqrt hsq

/-- The formation energy descended to `V/K`. -/
def descendedEnergy : V ⧸ P.syncKernel i₀ → ℝ :=
  Quotient.lift P.energy fun a b hab => by
    have h : a - b ∈ P.syncKernel i₀ := (Submodule.quotientRel_def _).1 hab
    rw [← P.energy_add_mem i₀ b (a - b) h, add_sub_cancel]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem descendedEnergy_mk (x : V) :
    P.descendedEnergy i₀ (Submodule.Quotient.mk x) = P.energy x := rfl

/-- **Part III**: the descended quadratic form on `V/K` is proper: every finite-energy sublevel is
compact. -/
theorem isCompact_descendedEnergy_sublevel (c : ℝ) :
    IsCompact {q : V ⧸ P.syncKernel i₀ | P.descendedEnergy i₀ q ≤ c} := by
  by_cases hK : P.syncKernel i₀ = ⊤
  · have hsub : Subsingleton (V ⧸ P.syncKernel i₀) := by
      rw [hK]
      infer_instance
    exact Set.Subsingleton.isCompact (Set.subsingleton_of_subsingleton)
  · have himage : {q : V ⧸ P.syncKernel i₀ | P.descendedEnergy i₀ q ≤ c} =
        (P.syncKernel i₀).mkQ '' {x | x ∈ (P.syncKernel i₀)ᗮ ∧ P.energy x ≤ c} := by
      ext q
      constructor
      · intro hq
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        refine ⟨x - (P.syncKernel i₀).starProjection x,
          ⟨Submodule.sub_starProjection_mem_orthogonal x, ?_⟩, ?_⟩
        · have h := P.energy_add_mem i₀ (x - (P.syncKernel i₀).starProjection x)
            ((P.syncKernel i₀).starProjection x) (Submodule.starProjection_apply_mem _ x)
          rw [sub_add_cancel] at h
          rw [← h]
          exact hq
        · rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
          simp only [sub_sub_cancel_left, neg_mem_iff]
          exact Submodule.starProjection_apply_mem _ x
      · rintro ⟨x, ⟨_, hx⟩, rfl⟩
        exact hx
    rw [himage]
    exact ((P.quotient_properness i₀ hK).2.2.2.2.2 c).image
      (Submodule.continuous_mkQ _)

/-! ### Part V: Plücker reconstruction -/

/-- The pseudo-determinant of `L`: the product of its nonzero eigenvalues (empty product `1`). -/
def pdet : ℝ := ∏ k ∈ Finset.univ.filter (fun k => P.eig k ≠ 0), P.eig k

omit [Nonempty I] in
theorem pdet_pos : 0 < P.pdet :=
  Finset.prod_pos fun k hk => lt_of_le_of_ne (P.eig_nonneg k) (Ne.symm (Finset.mem_filter.1 hk).2)

theorem laplacian_mem_orthogonal (x : V) : P.laplacian x ∈ (P.syncKernel i₀)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro k hk
  have hLk : P.laplacian k = 0 := by
    have := (P.ker_laplacian i₀).symm ▸ hk
    exact this
  have hs : ⟪P.laplacian k, x⟫_ℝ = ⟪k, P.laplacian x⟫_ℝ := P.laplacian_isSymmetric _ _
  rw [← hs, hLk, inner_zero_left]

/-- The compression of `L` to `Kᗮ`. -/
def laplacianRestrict : (P.syncKernel i₀)ᗮ →ₗ[ℝ] (P.syncKernel i₀)ᗮ :=
  (P.laplacian : V →ₗ[ℝ] V).restrict fun x _ => P.laplacian_mem_orthogonal i₀ x

/-- The eigenvectors with nonzero eigenvalue, as vectors of `Kᗮ`. -/
def orthEigVec (k : {k // P.eig k ≠ 0}) : (P.syncKernel i₀)ᗮ :=
  ⟨P.eigBasis k, P.eigBasis_mem_orthogonal i₀ k.2⟩

theorem orthEigVec_linearIndependent : LinearIndependent ℝ (P.orthEigVec i₀) := by
  apply LinearIndependent.of_comp (P.syncKernel i₀)ᗮ.subtype
  exact (P.eigBasis).orthonormal.linearIndependent.comp _ Subtype.val_injective

theorem orthEigVec_span : ⊤ ≤ Submodule.span ℝ (Set.range (P.orthEigVec i₀)) := by
  classical
  intro u _
  have hu : u = ∑ k : {k // P.eig k ≠ 0}, ⟪P.eigBasis k, (u : V)⟫_ℝ • P.orthEigVec i₀ k := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, orthEigVec]
    rw [← Finset.sum_subtype (Finset.univ.filter fun k => P.eig k ≠ 0) (fun k => by simp)
      (fun k => ⟪P.eigBasis k, (u : V)⟫_ℝ • P.eigBasis k)]
    have h := (P.eigBasis).sum_repr' (u : V)
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => P.eig k ≠ 0)] at h
    have hzero : ∑ k ∈ Finset.univ.filter (fun k => ¬ P.eig k ≠ 0),
        ⟪P.eigBasis k, (u : V)⟫_ℝ • P.eigBasis k = 0 := Finset.sum_eq_zero fun k hk => by
      have hk0 : P.eig k = 0 := not_not.1 (Finset.mem_filter.1 hk).2
      rw [(Submodule.mem_orthogonal _ _).1 u.2 _ (P.eigBasis_mem_syncKernel i₀ hk0), zero_smul]
    rw [hzero, add_zero] at h
    exact h.symm
  rw [hu]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- The eigenbasis of `Kᗮ` made of the eigenvectors with nonzero eigenvalue. -/
def orthEigBasis : Module.Basis {k // P.eig k ≠ 0} ℝ (P.syncKernel i₀)ᗮ :=
  Module.Basis.mk (P.orthEigVec_linearIndependent i₀) (P.orthEigVec_span i₀)

/-- `det(L|_{Kᗮ}) = pdet(L)`. -/
theorem det_laplacianRestrict : LinearMap.det (P.laplacianRestrict i₀) = P.pdet := by
  classical
  rw [← LinearMap.det_toMatrix (P.orthEigBasis i₀)]
  have hdiag : LinearMap.toMatrix (P.orthEigBasis i₀) (P.orthEigBasis i₀) (P.laplacianRestrict i₀) =
      Matrix.diagonal fun k : {k // P.eig k ≠ 0} => P.eig k := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have hT : P.laplacianRestrict i₀ (P.orthEigBasis i₀ j) = P.eig j • P.orthEigBasis i₀ j := by
      apply Subtype.ext
      simp only [orthEigBasis, Module.Basis.mk_apply, orthEigVec, laplacianRestrict,
        LinearMap.restrict_apply, Submodule.coe_smul]
      exact P.laplacian_eigBasis j
    rw [hT, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Matrix.diagonal_apply,
      Finsupp.single_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  rw [hdiag, Matrix.det_diagonal, pdet]
  exact (Finset.prod_subtype (Finset.univ.filter fun k => P.eig k ≠ 0) (fun k => by simp)
    P.eig).symm

/-- **Part V, (FLP.10), (FLP.20)–(FLP.21)**: with `B` the matrix of `A|_{Kᗮ}` in orthonormal bases,
`pdet(L) = det(BᵀB) = Σ_{|S| = r} det(B_S)²`, and this volume is positive (`1` when `r = 0`). -/
theorem pluecker_reconstruction {r m : ℕ} (bK : OrthonormalBasis (Fin r) ℝ (P.syncKernel i₀)ᗮ)
    (bP : OrthonormalBasis (Fin m) ℝ (PiLp 2 (fun _ : I => W))) :
    P.pdet = (((LinearMap.toMatrix bK.toBasis bP.toBasis)
        ((P.analysis : V →ₗ[ℝ] PiLp 2 (fun _ : I => W)) ∘ₗ (P.syncKernel i₀)ᗮ.subtype))ᵀ *
        (LinearMap.toMatrix bK.toBasis bP.toBasis)
        ((P.analysis : V →ₗ[ℝ] PiLp 2 (fun _ : I => W)) ∘ₗ (P.syncKernel i₀)ᗮ.subtype)).det ∧
      (((LinearMap.toMatrix bK.toBasis bP.toBasis)
        ((P.analysis : V →ₗ[ℝ] PiLp 2 (fun _ : I => W)) ∘ₗ (P.syncKernel i₀)ᗮ.subtype))ᵀ *
        (LinearMap.toMatrix bK.toBasis bP.toBasis)
        ((P.analysis : V →ₗ[ℝ] PiLp 2 (fun _ : I => W)) ∘ₗ (P.syncKernel i₀)ᗮ.subtype)).det =
        ∑ S : Set.powersetCard (Fin m) r, (rowMinor ((LinearMap.toMatrix bK.toBasis bP.toBasis)
          ((P.analysis : V →ₗ[ℝ] PiLp 2 (fun _ : I => W)) ∘ₗ
    (P.syncKernel i₀)ᗮ.subtype)) S).det ^ 2 ∧
      0 < P.pdet := by
  set f : (P.syncKernel i₀)ᗮ →ₗ[ℝ] PiLp 2 (fun _ : I => W) :=
    (P.analysis : V →ₗ[ℝ] PiLp 2 (fun _ : I => W)) ∘ₗ (P.syncKernel i₀)ᗮ.subtype with hf
  set B := LinearMap.toMatrix bK.toBasis bP.toBasis f with hB
  have hgram : LinearMap.adjoint f ∘ₗ f = P.laplacianRestrict i₀ := by
    refine LinearMap.ext fun u => ext_inner_right ℝ fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    change ⟪P.analysis u, P.analysis v⟫_ℝ = ⟪P.laplacian u, (v : V)⟫_ℝ
    rw [ResponsePacket.laplacian, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left]
  have hmat : Bᵀ * B = LinearMap.toMatrix bK.toBasis bK.toBasis (LinearMap.adjoint f ∘ₗ f) := by
    rw [LinearMap.toMatrix_comp bK.toBasis bP.toBasis bK.toBasis, LinearMap.toMatrix_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  refine ⟨?_, det_transpose_mul_self_eq_sum_sq B, P.pdet_pos⟩
  rw [hmat, LinearMap.det_toMatrix, hgram, det_laplacianRestrict]

/-- **Part V, separation certificate**: the packet separates all source displacements (`K = 0`)
exactly when some maximal minor of the matrix of `A` is nonzero. -/
theorem separation_certificate {n m : ℕ} (bV : OrthonormalBasis (Fin n) ℝ V)
    (bP : OrthonormalBasis (Fin m) ℝ (PiLp 2 (fun _ : I => W))) :
    P.syncKernel i₀ = ⊥ ↔ ∃ S : Set.powersetCard (Fin m) n,
      (rowMinor (LinearMap.toMatrix bV.toBasis bP.toBasis
        (P.analysis : V →ₗ[ℝ] PiLp 2 (fun _ : I => W))) S).det ≠ 0 := by
  set f : V →ₗ[ℝ] PiLp 2 (fun _ : I => W) := (P.analysis : V →ₗ[ℝ] PiLp 2 (fun _ : I => W))
    with hf
  set M := LinearMap.toMatrix bV.toBasis bP.toBasis f with hM
  have hgram : LinearMap.adjoint f ∘ₗ f = (P.laplacian : V →ₗ[ℝ] V) := by
    refine LinearMap.ext fun u => ext_inner_right ℝ fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    change ⟪P.analysis u, P.analysis v⟫_ℝ = ⟪P.laplacian u, v⟫_ℝ
    rw [ResponsePacket.laplacian, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left]
  have hdet : (Mᵀ * M).det = LinearMap.det (P.laplacian : V →ₗ[ℝ] V) := by
    rw [← hgram, ← LinearMap.det_toMatrix bV.toBasis, LinearMap.toMatrix_comp bV.toBasis
      bP.toBasis bV.toBasis, LinearMap.toMatrix_adjoint,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  have hsum := det_transpose_mul_self_eq_sum_sq M
  rw [← P.ker_laplacian i₀]
  constructor
  · intro hker
    by_contra! hall
    have h0 : (Mᵀ * M).det = 0 := by
      rw [hsum]
      exact Finset.sum_eq_zero fun S _ => by rw [hall S]; ring
    rw [hdet, LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
    exact h0 hker
  · rintro ⟨S, hS⟩
    by_contra hker
    have h0 := (LinearMap.det_eq_zero_iff_ker_ne_bot).2 hker
    rw [← hdet, hsum, Finset.sum_eq_zero_iff_of_nonneg fun S _ => sq_nonneg _] at h0
    exact hS (pow_eq_zero_iff two_ne_zero |>.1 (h0 S (Finset.mem_univ _)))

end ResponsePacket

/-- **Part V, sign loss**: the Gram matrix `BᵀB`, hence the positive Laplacian, is unchanged by
`B ↦ -B`, while every maximal minor changes by `(-1)^r`: the Laplacian retains the squared oriented
volumes, not their signs. -/
theorem gram_neg_and_minor_neg {m r : ℕ} (B : Matrix (Fin m) (Fin r) ℝ)
    (S : Set.powersetCard (Fin m) r) :
    (-B)ᵀ * (-B) = Bᵀ * B ∧ (rowMinor (-B) S).det = (-1) ^ r * (rowMinor B S).det := by
  refine ⟨by rw [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg], ?_⟩
  have h : rowMinor (-B) S = -rowMinor B S := rfl
  rw [h, Matrix.det_neg, Fintype.card_fin]

end Spectral

end GaloisForLFunctions.HTGeometry.SourceResponse
