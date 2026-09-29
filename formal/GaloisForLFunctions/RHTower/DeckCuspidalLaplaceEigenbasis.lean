import GaloisForLFunctions.RHTower.DeckPointPairEigenRepresentative

/-!
# The spectral theorem for the cuspidal finite-deck Laplacian

A cuspidal Laplace eigenfunction is a `C²` deck-equivariant square-integrable `U` with cuspidal
class and `-y²ΔU = λU`.  For such `U` and every `C²` profile `φ` the Green identity gives
`L_{Dφ} U = -λ L_φ U`; symmetry of `L_φ` and `L_{Dφ}` then forces `⟨L_φ U, W⟩ = 0` for eigenfunctions
with distinct eigenvalues, and the approximate identity gives `⟨U, W⟩ = 0`.

For completeness, let `f` be cuspidal and orthogonal to all eigenfunctions.  Each nonzero eigenspace
of the compact symmetric operator `L_φ` on cuspidal `L²` is finite-dimensional and invariant under
the symmetric operator `L_{Dφ}`, whose eigenvectors there are Laplace eigenfunctions; hence `f` is
orthogonal to all nonzero eigenspaces of `L_φ` and `L_φ f = 0`.  Letting `φ` run through an
approximate identity gives `f = 0`.

By Selberg's theorem each eigenvalue space lies in an eigenspace `L_φ = h_φ(s)` with `h_φ(s) ≠ 0`,
so it is finite-dimensional.  Orthonormal bases of the eigenvalue spaces form a Hilbert basis of
cuspidal `L²` consisting of Laplace eigenfunctions.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Module End
open scoped MatrixGroups ENNReal InnerProductSpace

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry SelbergMaassTraceEnergy

noncomputable section

variable {N : ℕ}

/-- **A compact symmetric operator kills every vector orthogonal to its nonzero eigenspaces.** -/
theorem apply_eq_zero_of_orthogonal_nonzero_eigenspaces {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {T : E →L[ℂ] E} (hT : IsCompactOperator T)
    (hsym : (T : E →ₗ[ℂ] E).IsSymmetric) {f : E}
    (hf : ∀ μ : ℂ, μ ≠ 0 → ∀ x ∈ eigenspace (T : E →ₗ[ℂ] E) μ, ⟪x, f⟫_ℂ = 0) : T f = 0 := by
  have hbot := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hsym
  have hle : (⨆ μ, eigenspace (T : E →ₗ[ℂ] E) μ) ≤ (ℂ ∙ T f)ᗮ := iSup_le fun μ x hx => by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have h1 : ⟪T f, x⟫_ℂ = ⟪f, T x⟫_ℂ := (hsym f x)
    have h2 : T x = μ • x := mem_eigenspace_iff.1 hx
    rw [h1, h2, inner_smul_right]
    by_cases hμ : μ = 0
    · simp [hμ]
    · rw [← inner_conj_symm, hf μ hμ x hx, map_zero, mul_zero]
  have hmem : T f ∈ (⨆ μ, eigenspace (T : E →ₗ[ℂ] E) μ)ᗮ :=
    (Submodule.mem_orthogonal' _ _).2 fun u hu =>
      (Submodule.mem_orthogonal_singleton_iff_inner_right).1 (hle hu)
  rw [hbot] at hmem
  exact (Submodule.mem_bot ℂ).1 hmem

/-! ## Central-fixed classes -/

theorem toDeckL2_mem_deckCentralFixedL2 {U : ℍ → DeckSpace N} (hUe : deckEquivariant N U)
    (hU : MemLp U 2 cellMeasure) : toDeckL2 U hU ∈ deckCentralFixedL2 N := by
  change deckCentralL2 N (toDeckL2 U hU) - toDeckL2 U hU = 0
  rw [sub_eq_zero]
  apply Lp.ext
  filter_upwards [(deckCentralCoeff N).coeFn_compLpL (toDeckL2 U hU), MemLp.coeFn_toLp hU]
    with z hcentral hF
  change (((deckCentralCoeff N).compLpL 2 cellMeasure) (toDeckL2 U hU)) z = (toDeckL2 U hU) z
  rw [hcentral]
  change (deckCentralCoeff N) ((MemLp.toLp U hU) z) = (MemLp.toLp U hU) z
  rw [hF]
  change finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N) (U z) = U z
  rw [← hUe (-1) z, SL_neg_smul, one_smul]

theorem cuspidalL2Closure_le_deckCentralFixedL2 :
    cuspidalL2Closure N ≤ deckCentralFixedL2 N := by
  refine Submodule.topologicalClosure_minimal _ ?_
    (deckCentralL2 N - ContinuousLinearMap.id ℂ (DeckL2 N)).isClosed_ker
  rintro _ ⟨v, rfl⟩
  change deckCentralL2 N (formInclusion N ⟨v.1, cuspidalFormDomainClosure_le_formDomainClosure N
    v.2⟩) - formInclusion N ⟨v.1, cuspidalFormDomainClosure_le_formDomainClosure N v.2⟩ = 0
  rw [formInclusion_deckCentral_fixed, sub_self]

/-! ## Orthogonality of distinct Laplace eigenvalues -/

theorem ppL2_toDeckL2_eq {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M)
    (hR : 0 ≤ R) (hφR : KernelSupport φ R) {U : ℍ → DeckSpace N} (hU : MemLp U 2 cellMeasure) :
    ppL2 hφc hφM hR hφR (toDeckL2 U hU) =
      toDeckL2 (ppApply φ U) (memLp_ppApply hφc hφM hR hφR hU) := by
  rw [ppL2_apply]
  exact toDeckL2_congr _ _ (Eventually.of_forall fun z => by
    rw [ppApply_congr_ae φ (show ⇑(toDeckL2 U hU) =ᵐ[cellMeasure] U from MemLp.coeFn_toLp hU)])

namespace SmoothProfile

variable (P : SmoothProfile)

/-- `L_{Dφ} U = -λ L_φ U` for a Laplace eigenfunction, by the Green identity. -/
theorem lap_op_eigen {lam : ℝ} {V : ℍ → DeckSpace N} (hV : IsCuspLaplaceEigen N lam V) :
    P.lap.op N (toDeckL2 V hV.memLp) = ((-lam : ℝ) : ℂ) • P.pp.op N (toDeckL2 V hV.memLp) := by
  unfold PairProfile.op
  rw [ppL2_toDeckL2_eq, ppL2_toDeckL2_eq, ← toDeckL2_smul]
  refine toDeckL2_congr _ _ (Eventually.of_forall fun z => ?_)
  change ppApply (radialLap P.toFun) V z = (((-lam : ℝ) : ℂ) • ppApply P.toFun V) z
  rw [← ppApply_hypLap P.contDiff_two P.radius_nonneg P.kernelSupport hV.contDiffOn
    hV.equivariant z]
  have h : hypLap V = ((-lam : ℝ) : ℂ) • V := funext hV.eigen
  rw [h, ppApply_smul]

theorem inner_op_eq_zero_of_ne {lam lam' : ℝ} {U W : ℍ → DeckSpace N}
    (hU : IsCuspLaplaceEigen N lam U) (hW : IsCuspLaplaceEigen N lam' W) (hne : lam ≠ lam') :
    ⟪P.pp.op N (toDeckL2 U hU.memLp), toDeckL2 W hW.memLp⟫_ℂ = 0 := by
  have hs1 := P.lap.op_isSymmetric N (toDeckL2 U hU.memLp) (toDeckL2 W hW.memLp)
  have hs2 := P.pp.op_isSymmetric N (toDeckL2 U hU.memLp) (toDeckL2 W hW.memLp)
  change ⟪P.lap.op N _, _⟫_ℂ = ⟪_, P.lap.op N _⟫_ℂ at hs1
  change ⟪P.pp.op N _, _⟫_ℂ = ⟪_, P.pp.op N _⟫_ℂ at hs2
  rw [P.lap_op_eigen hU, P.lap_op_eigen hW, inner_smul_left, inner_smul_right, ← hs2,
    Complex.conj_ofReal] at hs1
  have hd : ((-lam : ℝ) : ℂ) - ((-lam' : ℝ) : ℂ) ≠ 0 := by
    rw [sub_ne_zero, Ne, Complex.ofReal_inj, neg_inj]
    exact hne
  exact (mul_eq_zero.1 (by linear_combination hs1)).resolve_left hd

end SmoothProfile

/-- A smooth unit profile of radius `R/2` as a `SmoothProfile`. -/
theorem exists_smoothUnitProfile {R : ℝ} (hR : 0 < R) :
    ∃ P : SmoothProfile, P.radius ≤ R ∧ (∀ u, 0 ≤ P.toFun u) ∧ ppKernelMass P.toFun = 1 := by
  obtain ⟨φ, hφs, hφ0, hφR, hmass⟩ := exists_unitProfile (half_pos hR)
  exact ⟨⟨φ, R / 2, (half_pos hR).le, hφs.of_le (by norm_cast), hφR⟩, by simp; linarith,
    hφ0, hmass⟩

/-- **Distinct Laplace eigenvalues give orthogonal eigenfunctions.** -/
theorem inner_toDeckL2_eq_zero_of_ne {lam lam' : ℝ} {U W : ℍ → DeckSpace N}
    (hU : IsCuspLaplaceEigen N lam U) (hW : IsCuspLaplaceEigen N lam' W) (hne : lam ≠ lam') :
    ⟪toDeckL2 U hU.memLp, toDeckL2 W hW.memLp⟫_ℂ = 0 := by
  have hu := toDeckL2_mem_deckCentralFixedL2 hU.equivariant hU.memLp
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun δ hδ => ?_)
  obtain ⟨R₀, hR₀, happ⟩ := exists_radius_approxIdentity (⟨_, hu⟩ : deckCentralFixedL2 N)
    (ε := δ / (‖toDeckL2 W hW.memLp‖ + 1)) (by positivity)
  obtain ⟨P, hPR, hP0, hPm⟩ := exists_smoothUnitProfile hR₀
  have h0 := P.inner_op_eq_zero_of_ne hU hW hne
  have h1 := happ P.pp.differentiable.continuous P.pp.abs_le P.pp.radius_nonneg P.pp.support hP0
    hPm hPR
  change ‖P.pp.op N (toDeckL2 U hU.memLp) - toDeckL2 U hU.memLp‖ ≤ _ at h1
  have hw0 := norm_nonneg (toDeckL2 W hW.memLp)
  calc ‖⟪toDeckL2 U hU.memLp, toDeckL2 W hW.memLp⟫_ℂ‖
      = ‖⟪toDeckL2 U hU.memLp - P.pp.op N (toDeckL2 U hU.memLp), toDeckL2 W hW.memLp⟫_ℂ‖ := by
        rw [inner_sub_left, h0, sub_zero]
    _ ≤ ‖toDeckL2 U hU.memLp - P.pp.op N (toDeckL2 U hU.memLp)‖ * ‖toDeckL2 W hW.memLp‖ :=
        norm_inner_le_norm _ _
    _ ≤ δ / (‖toDeckL2 W hW.memLp‖ + 1) * ‖toDeckL2 W hW.memLp‖ := by
        rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_right h1 hw0
    _ ≤ 0 + δ := by
        rw [zero_add, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

/-! ## Completeness -/

/-- In a finite-dimensional invariant subspace of a symmetric operator, a vector orthogonal to all
eigenvectors lying in the subspace is orthogonal to the whole subspace. -/
theorem inner_eq_zero_of_symm_invariant {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {S : E →ₗ[ℂ] E} (hS : S.IsSymmetric) {V : Submodule ℂ E} [FiniteDimensional ℂ V]
    (hV : ∀ v ∈ V, S v ∈ V) {f : E}
    (hf : ∀ v ∈ V, v ≠ 0 → ∀ κ : ℝ, S v = (κ : ℂ) • v → ⟪v, f⟫_ℂ = 0) :
    ∀ x ∈ V, ⟪x, f⟫_ℂ = 0 := by
  intro x hx
  have hsym := hS.restrict_invariant hV
  let b := hsym.eigenvectorBasis rfl
  have hbi : ∀ i, ⟪((b i : V) : E), f⟫_ℂ = 0 := by
    intro i
    refine hf _ (b i).2 (fun h => b.orthonormal.ne_zero i (Subtype.ext h))
      (hsym.eigenvalues rfl i) ?_
    have := hsym.apply_eigenvectorBasis rfl i
    exact congrArg Subtype.val this
  have hxsum := (b.sum_repr ⟨x, hx⟩).symm
  have hx' : x = ((∑ i, (b.repr ⟨x, hx⟩).ofLp i • b i : V) : E) := by rw [← hxsum]
  rw [hx', Submodule.coe_sum, sum_inner]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Submodule.coe_smul, inner_smul_left, hbi i, mul_zero]

/-- A vector orthogonal to every cuspidal Laplace eigenfunction is orthogonal to every nonzero
eigenspace of `L_φ`: such an eigenspace is finite-dimensional and `L_{Dφ}`-invariant, and an
eigenvector of `L_{Dφ}` inside it is a Laplace eigenfunction. -/
theorem SmoothProfile.inner_eigenspace_eq_zero (P : SmoothProfile) {μ : ℂ} (hμ : μ ≠ 0)
    {f : CuspidalL2 N}
    (hf : ∀ (lam : ℝ) (U : ℍ → DeckSpace N) (hU : IsCuspLaplaceEigen N lam U),
      ⟪toDeckL2 U hU.memLp, (f : DeckL2 N)⟫_ℂ = 0)
    {x : CuspidalL2 N}
    (hx : x ∈ eigenspace (P.pp.cuspOp N : CuspidalL2 N →ₗ[ℂ] CuspidalL2 N) μ) :
    ⟪x, f⟫_ℂ = 0 := by
  haveI : FiniteDimensional ℂ (eigenspace (P.pp.cuspOp N : CuspidalL2 N →ₗ[ℂ] CuspidalL2 N) μ) :=
    ContinuousLinearMap.finite_dimensional_eigenspace P.pp.isCompactOperator_cuspOp μ hμ
  refine inner_eq_zero_of_symm_invariant (P.lap.cuspOp_isSymmetric (N := N))
    (fun v hv => mem_eigenspace_iff.2 (SmoothProfile.lap_cuspOp_mem hμ (mem_eigenspace_iff.1 hv)))
    (fun v hv hne κ hκ => ?_) x hx
  have hT : P.pp.cuspOp N v = μ • v := mem_eigenspace_iff.1 hv
  have hU := SmoothProfile.isCuspLaplaceEigen_eigenRep hμ hT hne hκ
  have h := hf _ _ hU
  rw [SmoothProfile.toDeckL2_eigenRep hμ hT] at h
  exact h

/-- **Completeness of the cuspidal Laplace eigenfunctions**: a cuspidal vector orthogonal to all of
them vanishes. -/
theorem eq_zero_of_forall_inner_cuspLaplaceEigen (f : CuspidalL2 N)
    (hf : ∀ (lam : ℝ) (U : ℍ → DeckSpace N) (hU : IsCuspLaplaceEigen N lam U),
      ⟪toDeckL2 U hU.memLp, (f : DeckL2 N)⟫_ℂ = 0) : f = 0 := by
  have hfc : (f : DeckL2 N) ∈ deckCentralFixedL2 N := cuspidalL2Closure_le_deckCentralFixedL2 f.2
  suffices h : ‖(f : DeckL2 N)‖ = 0 from Subtype.ext (norm_eq_zero.1 h)
  refine le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) (norm_nonneg _)
  obtain ⟨R₀, hR₀, happ⟩ := exists_radius_approxIdentity (⟨_, hfc⟩ : deckCentralFixedL2 N) hδ
  obtain ⟨P, hPR, hP0, hPm⟩ := exists_smoothUnitProfile hR₀
  have hT : P.pp.cuspOp N f = 0 :=
    apply_eq_zero_of_orthogonal_nonzero_eigenspaces P.pp.isCompactOperator_cuspOp
      P.pp.cuspOp_isSymmetric fun μ hμ x hx => P.inner_eigenspace_eq_zero hμ hf hx
  have h1 := happ P.pp.differentiable.continuous P.pp.abs_le P.pp.radius_nonneg P.pp.support hP0
    hPm hPR
  change ‖P.pp.op N (f : DeckL2 N) - (f : DeckL2 N)‖ ≤ δ at h1
  have h2 : P.pp.op N (f : DeckL2 N) = 0 := by
    rw [← PairProfile.coe_cuspOp, hT]
    rfl
  rw [h2, zero_sub, norm_neg] at h1
  linarith

/-! ## The eigenvalue spaces -/

theorem dir_dir_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : ℂ → E}
    (hf : ContDiffOn ℝ 2 f {ζ : ℂ | 0 < ζ.im}) (hg : ContDiffOn ℝ 2 g {ζ : ℂ | 0 < ζ.im})
    {ζ : ℂ} (hζ : 0 < ζ.im) (v : ℂ) :
    dir v (dir v (f + g)) ζ = dir v (dir v f) ζ + dir v (dir v g) ζ := by
  have hopen : IsOpen {ζ : ℂ | 0 < ζ.im} := isOpen_lt continuous_const Complex.continuous_im
  have h1 : dir v (f + g) =ᶠ[𝓝 ζ] dir v f + dir v g := by
    filter_upwards [hopen.mem_nhds hζ] with ζ' hζ'
    unfold dir
    rw [Pi.add_apply, fderiv_add ((hf.differentiableOn (by norm_num)).differentiableAt
      (hopen.mem_nhds hζ')) ((hg.differentiableOn (by norm_num)).differentiableAt
      (hopen.mem_nhds hζ'))]
    rfl
  have hdf := ((dir_contDiffOn hf (m := 1) (by norm_num) v).differentiableOn (by norm_num))
    |>.differentiableAt (hopen.mem_nhds hζ)
  have hdg := ((dir_contDiffOn hg (m := 1) (by norm_num) v).differentiableOn (by norm_num))
    |>.differentiableAt (hopen.mem_nhds hζ)
  change fderiv ℝ (dir v (f + g)) ζ v = _
  rw [h1.fderiv_eq, fderiv_add hdf hdg]
  rfl

theorem hypLap_add {U W : ℍ → DeckSpace N}
    (hU : ContDiffOn ℝ 2 (fun ζ => U (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im})
    (hW : ContDiffOn ℝ 2 (fun ζ => W (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im}) (w : ℍ) :
    hypLap (U + W) w = hypLap U w + hypLap W w := by
  unfold hypLap chartLap
  have e : (fun ζ => (U + W) (ofComplex ζ)) =
      (fun ζ => U (ofComplex ζ)) + fun ζ => W (ofComplex ζ) := rfl
  rw [e, dir_dir_add hU hW w.im_pos, dir_dir_add hU hW w.im_pos]
  simp only [smul_add]
  abel

theorem hypLap_smul {U : ℍ → DeckSpace N}
    (hU : ContDiffOn ℝ 2 (fun ζ => U (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im}) (c : ℂ) (w : ℍ) :
    hypLap (c • U) w = c • hypLap U w := by
  let L : DeckSpace N →L[ℝ] DeckSpace N := (c • ContinuousLinearMap.id ℂ (DeckSpace N)).restrictScalars ℝ
  unfold hypLap chartLap
  have e : (fun ζ => (c • U) (ofComplex ζ)) = fun ζ => L (U (ofComplex ζ)) := rfl
  rw [e, dir_dir_comp_clm hU L w.im_pos, dir_dir_comp_clm hU L w.im_pos, ← map_add, smul_comm]
  rfl

namespace IsCuspLaplaceEigen

variable {lam : ℝ}

theorem zero : IsCuspLaplaceEigen N lam 0 where
  contDiffOn := contDiffOn_const
  equivariant := fun A z => by simp
  memLp := MemLp.zero
  cuspidal := by
    have : toDeckL2 (0 : ℍ → DeckSpace N) MemLp.zero = 0 := by
      rw [toDeckL2]; exact MemLp.toLp_zero _
    rw [this]; exact Submodule.zero_mem _
  eigen := fun z => by
    have h : hypLap (0 : ℍ → DeckSpace N) z = 0 := by
      have := hypLap_smul (U := (0 : ℍ → DeckSpace N)) contDiffOn_const 0 z
      simpa using this
    rw [h]; simp

theorem add {U W : ℍ → DeckSpace N} (hU : IsCuspLaplaceEigen N lam U)
    (hW : IsCuspLaplaceEigen N lam W) : IsCuspLaplaceEigen N lam (U + W) where
  contDiffOn := hU.contDiffOn.add hW.contDiffOn
  equivariant := fun A z => by
    show U (A • z) + W (A • z) = _
    rw [hU.equivariant A z, hW.equivariant A z, Pi.add_apply, map_add]
  memLp := hU.memLp.add hW.memLp
  cuspidal := by
    rw [toDeckL2_add hU.memLp hW.memLp]
    exact add_mem hU.cuspidal hW.cuspidal
  eigen := fun z => by
    rw [hypLap_add hU.contDiffOn hW.contDiffOn z, hU.eigen z, hW.eigen z, Pi.add_apply, smul_add]

theorem smul {U : ℍ → DeckSpace N} (hU : IsCuspLaplaceEigen N lam U) (c : ℂ) :
    IsCuspLaplaceEigen N lam (c • U) where
  contDiffOn := hU.contDiffOn.const_smul c
  equivariant := deckEquivariant_smul c hU.equivariant
  memLp := hU.memLp.const_smul c
  cuspidal := by
    rw [toDeckL2_smul c hU.memLp]
    exact Submodule.smul_mem _ c hU.cuspidal
  eigen := fun z => by
    rw [hypLap_smul hU.contDiffOn c z, hU.eigen z, Pi.smul_apply, smul_comm]

end IsCuspLaplaceEigen

/-- The cuspidal classes of Laplace eigenfunctions with eigenvalue `λ`. -/
def eigenClassSpace (N : ℕ) (lam : ℝ) : Submodule ℂ (CuspidalL2 N) where
  carrier := {f | ∃ (U : ℍ → DeckSpace N) (hU : IsCuspLaplaceEigen N lam U),
    (f : DeckL2 N) = toDeckL2 U hU.memLp}
  add_mem' := by
    rintro f g ⟨U, hU, hf⟩ ⟨W, hW, hg⟩
    exact ⟨U + W, hU.add hW, by rw [Submodule.coe_add, hf, hg, toDeckL2_add]⟩
  zero_mem' := ⟨0, IsCuspLaplaceEigen.zero, by
    rw [ZeroMemClass.coe_zero, toDeckL2]; exact (MemLp.toLp_zero _).symm⟩
  smul_mem' := by
    rintro c f ⟨U, hU, hf⟩
    exact ⟨c • U, hU.smul c, by rw [Submodule.coe_smul, hf, toDeckL2_smul]⟩

/-- Every eigenvalue space lies in an eigenspace of a point-pair operator, by Selberg's theorem. -/
theorem eigenClassSpace_le_eigenspace (P : SmoothProfile) {lam : ℝ} {s : ℂ}
    (hs : s * (1 - s) = lam) :
    eigenClassSpace N lam ≤ eigenspace (P.pp.cuspOp N : CuspidalL2 N →ₗ[ℂ] CuspidalL2 N)
      (selbergTransform P.toFun s) := by
  rintro f ⟨U, hU, hf⟩
  rw [mem_eigenspace_iff]
  apply Subtype.ext
  change P.pp.op N (f : DeckL2 N) = selbergTransform P.toFun s • (f : DeckL2 N)
  rw [hf]
  unfold PairProfile.op
  rw [ppL2_toDeckL2_eq, ← toDeckL2_smul]
  refine toDeckL2_congr _ _ (Eventually.of_forall fun z => ?_)
  change ppApply P.toFun U z = selbergTransform P.toFun s • U z
  refine ppApply_eigen P.pp.differentiable.continuous P.kernelSupport hU.contDiffOn hU.equivariant
    (fun z => ?_) z
  rw [hU.eigen z, hs]
  push_cast
  ring_nf

theorem finiteDimensional_eigenClassSpace (lam : ℝ) :
    FiniteDimensional ℂ (eigenClassSpace N lam) := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq ((1 / 4 : ℂ) - lam) (n := 2) (by norm_num)
  have hs : (1 / 2 + t) * (1 - (1 / 2 + t)) = (lam : ℂ) := by
    linear_combination -ht
  obtain ⟨R₀, hR₀, hne⟩ := exists_radius_selbergTransform_ne_zero (1 / 2 + t)
  obtain ⟨P, hPR, hP0, hPm⟩ := exists_smoothUnitProfile hR₀
  have hh := hne P.pp.differentiable.continuous hP0 hPm P.kernelSupport hPR
  haveI := ContinuousLinearMap.finite_dimensional_eigenspace
    (P.pp.isCompactOperator_cuspOp (N := N)) (selbergTransform P.toFun (1 / 2 + t)) hh
  exact Submodule.finiteDimensional_of_le (eigenClassSpace_le_eigenspace (N := N) P hs)

instance (lam : ℝ) : FiniteDimensional ℂ (eigenClassSpace N lam) :=
  finiteDimensional_eigenClassSpace lam

theorem orthogonalFamily_eigenClassSpace :
    OrthogonalFamily ℂ (fun lam : ℝ => eigenClassSpace N lam)
      (fun lam => (eigenClassSpace N lam).subtypeₗᵢ) := by
  intro lam lam' hne v w
  obtain ⟨U, hU, hv⟩ := v.2
  obtain ⟨W, hW, hw⟩ := w.2
  change ⟪((v : CuspidalL2 N) : DeckL2 N), ((w : CuspidalL2 N) : DeckL2 N)⟫_ℂ = 0
  rw [hv, hw]
  exact inner_toDeckL2_eq_zero_of_ne hU hW hne

/-! ## The cuspidal Hilbert eigenbasis -/

section SigmaBasis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {ι : Type*}
  (V : ι → Submodule ℂ E) [∀ i, FiniteDimensional ℂ (V i)]

/-- Orthonormal bases of the members of a family of finite-dimensional subspaces, collected. -/
def sigmaVec (a : Σ i, Fin (Module.finrank ℂ (V i))) : E :=
  (stdOrthonormalBasis ℂ (V a.1) a.2 : E)

omit [CompleteSpace E] in
theorem sigmaVec_mem (a : Σ i, Fin (Module.finrank ℂ (V i))) : sigmaVec V a ∈ V a.1 :=
  (stdOrthonormalBasis ℂ (V a.1) a.2).2

variable {V}

omit [CompleteSpace E] in
theorem orthonormal_sigmaVec (hV : OrthogonalFamily ℂ (fun i => V i) (fun i => (V i).subtypeₗᵢ)) :
    Orthonormal ℂ (sigmaVec V) :=
  hV.orthonormal_sigma_orthonormal fun i => (stdOrthonormalBasis ℂ (V i)).orthonormal

omit [CompleteSpace E] in
theorem mem_span_sigmaVec {i : ι} {g : E} (hg : g ∈ V i) :
    g ∈ Submodule.span ℂ (Set.range (sigmaVec V)) := by
  have hsum := (stdOrthonormalBasis ℂ (V i)).sum_repr ⟨g, hg⟩
  have hg' : g = ∑ k, ((stdOrthonormalBasis ℂ (V i)).repr ⟨g, hg⟩).ofLp k •
      ((stdOrthonormalBasis ℂ (V i) k : V i) : E) := by
    have := congrArg (fun y : V i => (y : E)) hsum
    simpa using this.symm
  rw [hg']
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, k⟩, rfl⟩)

/-- A complete orthogonal family of finite-dimensional subspaces gives a Hilbert basis. -/
def sigmaHilbertBasis (hV : OrthogonalFamily ℂ (fun i => V i) (fun i => (V i).subtypeₗᵢ))
    (htop : ∀ f : E, (∀ i, ∀ v ∈ V i, ⟪v, f⟫_ℂ = 0) → f = 0) :
    HilbertBasis (Σ i, Fin (Module.finrank ℂ (V i))) ℂ E :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_sigmaVec hV) (by
    refine eq_bot_iff.2 fun f hf => ?_
    rw [htop f fun i v hv => by
      rw [← inner_conj_symm, (Submodule.mem_orthogonal' _ _).1 hf _ (mem_span_sigmaVec hv),
        map_zero]]
    exact Submodule.zero_mem _)

theorem sigmaHilbertBasis_mem (hV : OrthogonalFamily ℂ (fun i => V i) (fun i => (V i).subtypeₗᵢ))
    (htop : ∀ f : E, (∀ i, ∀ v ∈ V i, ⟪v, f⟫_ℂ = 0) → f = 0)
    (a : Σ i, Fin (Module.finrank ℂ (V i))) : (sigmaHilbertBasis hV htop a : E) ∈ V a.1 := by
  rw [sigmaHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact sigmaVec_mem V a

end SigmaBasis

/-- Index of the cuspidal eigenbasis: an eigenvalue and an index into an orthonormal basis of its
finite-dimensional eigenvalue space. -/
abbrev CuspEigenIndex (N : ℕ) : Type := Σ lam : ℝ, Fin (Module.finrank ℂ (eigenClassSpace N lam))

/-- **Spectral theorem for the cuspidal finite-deck Laplacian**: the cuspidal `L²` space has a
Hilbert basis consisting of classes of `C²` deck-equivariant Laplace eigenfunctions. -/
def cuspEigenBasis (N : ℕ) : HilbertBasis (CuspEigenIndex N) ℂ (CuspidalL2 N) :=
  sigmaHilbertBasis orthogonalFamily_eigenClassSpace fun f hf =>
    eq_zero_of_forall_inner_cuspLaplaceEigen f fun lam U hU => by
      have h := hf lam ⟨toDeckL2 U hU.memLp, hU.cuspidal⟩ ⟨U, hU, rfl⟩
      exact h

/-- Every vector of the cuspidal eigenbasis is the class of a cuspidal Laplace eigenfunction. -/
theorem cuspEigenBasis_spec (i : CuspEigenIndex N) :
    ∃ (U : ℍ → DeckSpace N) (hU : IsCuspLaplaceEigen N i.1 U),
      ((cuspEigenBasis N i : CuspidalL2 N) : DeckL2 N) = toDeckL2 U hU.memLp :=
  sigmaHilbertBasis_mem _ _ i

end

end GaloisForLFunctions.RHTower.DeckPointPair
