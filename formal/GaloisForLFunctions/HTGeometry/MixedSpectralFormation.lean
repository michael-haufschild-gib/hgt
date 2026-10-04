import GaloisForLFunctions.HTGeometry.UnitaryAtomicDecomposition

/-!
# Mixed spectral formation: the fixed Hilbert–Schmidt geometry

For a unitary `U` with eigenprojections `P_λ` and continuous projection `P_c`, conjugation
`α(T) = U* T U` on Hilbert–Schmidt operators has fixed space

`ker δ = {T : T P_c = 0, P_c T = 0, T P_λ = P_λ T for all λ}`,

the block-diagonal operators over the eigenspaces (Theorem 3.2, `(MSF.2)`).  The **atomic
pinching** `Π_at(T) = ∑_λ P_λ T P_λ` (`(MSF.1)`, convergent in Hilbert–Schmidt norm) is the
Hilbert–Schmidt orthogonal projection onto this fixed space, and the Cesàro formation converges to
it: `M_N(T) → Π_at(T)` in `S₂` (Corollary 3.3, `(MSF.4)`).

All computations run on the adapted Hilbert basis of eigenvectors and `H_c`.
-/

open Filter Topology Set
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {U : H ≃ₗᵢ[ℂ] H}

/-- The eigenprojection `P_λ`. -/
abbrev eigenproj (U : H ≃ₗᵢ[ℂ] H) (c : ℂ) : H →L[ℂ] H := (unitaryEigenspace U c).starProjection

/-- The continuous projection `P_c`. -/
abbrev contproj (U : H ≃ₗᵢ[ℂ] H) : H →L[ℂ] H := (continuousSubspace U).starProjection

/-! ### The fixed space -/

omit [CompleteSpace H] in
theorem comm_of_hsConj_eq {T : H →L[ℂ] H} (h : hsConj U T = T) : ∀ x, T (U x) = U (T x) := by
  intro x
  have := congrArg (fun S : H →L[ℂ] H => U (S x)) h
  simpa using this

omit [CompleteSpace H] in
theorem hsConj_eq_of_comm {T : H →L[ℂ] H} (h : ∀ x, T (U x) = U (T x)) : hsConj U T = T := by
  ext x
  simp [h]

theorem eigenproj_adaptedVec_inl (c d : ℂ) (k : eigenBasisIndex U d) :
    eigenproj U c (adaptedVec U (Sum.inl ⟨d, k⟩)) =
      if d = c then adaptedVec U (Sum.inl ⟨d, k⟩) else 0 :=
  eigenprojection_adaptedVec c (Sum.inl ⟨d, k⟩)

theorem eigenproj_adaptedVec_inr (c : ℂ) (k : continuousBasisIndex U) :
    eigenproj U c (adaptedVec U (Sum.inr k)) = 0 :=
  eigenprojection_adaptedVec c (Sum.inr k)

theorem contproj_adaptedVec_inl (d : ℂ) (k : eigenBasisIndex U d) :
    contproj U (adaptedVec U (Sum.inl ⟨d, k⟩)) = 0 :=
  continuousProjection_adaptedVec (Sum.inl ⟨d, k⟩)

theorem contproj_adaptedVec_inr (k : continuousBasisIndex U) :
    contproj U (adaptedVec U (Sum.inr k)) = adaptedVec U (Sum.inr k) :=
  continuousProjection_adaptedVec (Sum.inr k)

theorem ext_adapted {A B : H →L[ℂ] H} (h : ∀ i, A (adaptedVec U i) = B (adaptedVec U i)) :
    A = B :=
  ext_hilbertBasis (adaptedBasis U) fun i => by rw [adaptedBasis_apply]; exact h i

/-- **Theorem 3.2, `(MSF.2)`.**  A Hilbert–Schmidt operator is fixed by conjugation exactly when
it vanishes on and into `H_c` and commutes with every eigenprojection: it is block diagonal over
the eigenspaces. -/
theorem hsConj_eq_iff {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    hsConj U T = T ↔ (T ∘L contproj U = 0 ∧ contproj U ∘L T = 0 ∧
      ∀ c, T ∘L eigenproj U c = eigenproj U c ∘L T) := by
  constructor
  · intro h
    have hc := comm_of_hsConj_eq h
    obtain ⟨h1, h2⟩ := compact_comm_continuousProjection hc hT.isCompactOperator
    exact ⟨h1, h2, commute_eigenprojection hc⟩
  · rintro ⟨h1, h2, h3⟩
    refine hsConj_eq_of_comm fun x => ?_
    have hext : T ∘L unitaryCLM U = unitaryCLM U ∘L T := by
      refine ext_adapted (U := U) fun i => ?_
      simp only [ContinuousLinearMap.comp_apply, unitaryCLM_apply]
      rcases i with ⟨d, k⟩ | k
      · have hv := adaptedVec_inl_mem d k
        have hUv : U (adaptedVec U (Sum.inl ⟨d, k⟩)) = d • adaptedVec U (Sum.inl ⟨d, k⟩) :=
          mem_unitaryEigenspace.mp hv
        have hTv : T (adaptedVec U (Sum.inl ⟨d, k⟩)) ∈ unitaryEigenspace U d := by
          have := congrArg (fun L : H →L[ℂ] H => L (adaptedVec U (Sum.inl ⟨d, k⟩))) (h3 d)
          simp only [ContinuousLinearMap.comp_apply, eigenproj_adaptedVec_inl, if_true] at this
          rw [this]
          exact Submodule.starProjection_apply_mem _ _
        rw [hUv, map_smul, mem_unitaryEigenspace.mp hTv]
      · have hv := adaptedVec_inr_mem k
        have hTv : T (adaptedVec U (Sum.inr k)) = 0 := by
          have := congrArg (fun L : H →L[ℂ] H => L (adaptedVec U (Sum.inr k))) h1
          simpa [contproj_adaptedVec_inr] using this
        have hTUv : T (U (adaptedVec U (Sum.inr k))) = 0 := by
          have := congrArg (fun L : H →L[ℂ] H => L (U (adaptedVec U (Sum.inr k)))) h1
          simp only [ContinuousLinearMap.comp_apply, zero_apply] at this
          rwa [Submodule.starProjection_eq_self_iff.mpr (unitary_mapsTo_continuous _ hv)] at this
        rw [hTv, hTUv, map_zero]
    exact congrArg (fun L : H →L[ℂ] H => L x) hext

/-! ### The atomic pinching -/

section Pinching

variable (U)

/-- The columns of the atomic pinching on the adapted basis: `P_λ T e` on an eigenvector `e` of
eigenvalue `λ`, and `0` on `H_c`. -/
def atomicPinchCol (T : H →L[ℂ] H) : AdaptedIndex U → H
  | Sum.inl j => eigenproj U j.1 (T (adaptedVec U (Sum.inl j)))
  | Sum.inr _ => 0

variable {U}

theorem norm_atomicPinchCol_le (T : H →L[ℂ] H) (i : AdaptedIndex U) :
    ‖atomicPinchCol U T i‖ ≤ ‖T (adaptedVec U i)‖ := by
  rcases i with j | k
  · exact Submodule.norm_starProjection_apply_le _ _
  · simp [atomicPinchCol]

theorem summable_atomicPinchCol {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    Summable fun i => ‖atomicPinchCol U T i‖ ^ 2 := by
  have h := hT.summable (adaptedBasis U)
  simp only [adaptedBasis_apply] at h
  exact h.of_nonneg_of_le (fun i => by positivity) fun i =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_atomicPinchCol_le T i) 2

/-- The atomic pinching columns as an element of `ℓ²`. -/
def atomicPinchColumns (U : H ≃ₗᵢ[ℂ] H) {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    lp (fun _ : AdaptedIndex U => H) 2 :=
  ⟨atomicPinchCol U T, memℓp_gen <| by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using summable_atomicPinchCol hT⟩

/-- **`(MSF.1)`.**  The atomic pinching `Π_at(T) = ∑_λ P_λ T P_λ`, built from its columns on the
adapted basis. -/
def atomicPinch (U : H ≃ₗᵢ[ℂ] H) {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) : H →L[ℂ] H :=
  columnOperator (adaptedBasis U) (atomicPinchColumns U hT)

theorem atomicPinch_apply {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (i : AdaptedIndex U) :
    atomicPinch U hT (adaptedVec U i) = atomicPinchCol U T i := by
  classical
  rw [← adaptedBasis_apply, atomicPinch, columnOperator_basis]
  rfl

theorem isHilbertSchmidt_atomicPinch {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (atomicPinch U hT) :=
  isHilbertSchmidt_columnOperator (adaptedBasis U) (atomicPinchColumns U hT)

theorem eigenproj_eigenproj_of_ne {c d : ℂ} (hcd : d ≠ c) (y : H) :
    eigenproj U c (eigenproj U d y) = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff _).mpr
    ((Submodule.isOrtho_iff_le.mp (unitaryEigenspace_isOrtho hcd))
      (Submodule.starProjection_apply_mem _ y))

theorem eigenproj_idem (c : ℂ) (y : H) : eigenproj U c (eigenproj U c y) = eigenproj U c y :=
  Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ y)

theorem contproj_eigenproj (c : ℂ) (y : H) : contproj U (eigenproj U c y) = 0 := by
  refine (Submodule.starProjection_apply_eq_zero_iff _).mpr ?_
  show _ ∈ (atomicSubspace U)ᗮᗮ
  rw [Submodule.orthogonal_orthogonal]
  exact unitaryEigenspace_le_atomic c (Submodule.starProjection_apply_mem _ y)

/-- **Theorem 3.2.**  The atomic pinching is fixed by conjugation. -/
theorem hsConj_atomicPinch {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    hsConj U (atomicPinch U hT) = atomicPinch U hT := by
  refine (hsConj_eq_iff (isHilbertSchmidt_atomicPinch (U := U) hT)).mpr ⟨?_, ?_, fun c => ?_⟩
  · refine ext_adapted (U := U) fun i => ?_
    rcases i with ⟨d, k⟩ | k
    · simp [contproj_adaptedVec_inl]
    · simp only [ContinuousLinearMap.comp_apply, contproj_adaptedVec_inr, zero_apply]
      rw [atomicPinch_apply]
      rfl
  · refine ext_adapted (U := U) fun i => ?_
    rcases i with ⟨d, k⟩ | k
    · simp [atomicPinch_apply, atomicPinchCol, contproj_eigenproj]
    · simp [atomicPinch_apply, atomicPinchCol]
  · refine ext_adapted (U := U) fun i => ?_
    rcases i with ⟨d, k⟩ | k
    · simp only [ContinuousLinearMap.comp_apply, eigenproj_adaptedVec_inl, atomicPinch_apply,
        atomicPinchCol]
      split_ifs with hdc
      · subst hdc
        rw [atomicPinch_apply, eigenproj_idem]
        rfl
      · rw [map_zero, eigenproj_eigenproj_of_ne hdc]
    · simp [eigenproj_adaptedVec_inr, atomicPinch_apply, atomicPinchCol]

/-- **Theorem 3.2.**  `T - Π_at(T)` is Hilbert–Schmidt orthogonal to every fixed Hilbert–Schmidt
operator, columnwise on the adapted basis. -/
theorem inner_sub_atomicPinch_fixed {T S : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    (hS : IsHilbertSchmidt S) (hfix : hsConj U S = S) (i : AdaptedIndex U) :
    ⟪(T - atomicPinch U hT) (adaptedVec U i), S (adaptedVec U i)⟫_ℂ = 0 := by
  obtain ⟨h1, -, h3⟩ := (hsConj_eq_iff hS).mp hfix
  rcases i with ⟨d, k⟩ | k
  · have hSv : S (adaptedVec U (Sum.inl ⟨d, k⟩)) ∈ unitaryEigenspace U d := by
      have := congrArg (fun L : H →L[ℂ] H => L (adaptedVec U (Sum.inl ⟨d, k⟩))) (h3 d)
      simp only [ContinuousLinearMap.comp_apply, eigenproj_adaptedVec_inl, if_true] at this
      rw [this]
      exact Submodule.starProjection_apply_mem _ _
    rw [sub_apply, atomicPinch_apply]
    exact Submodule.inner_left_of_mem_orthogonal hSv
      (Submodule.sub_starProjection_mem_orthogonal _)
  · have hSv : S (adaptedVec U (Sum.inr k)) = 0 := by
      have := congrArg (fun L : H →L[ℂ] H => L (adaptedVec U (Sum.inr k))) h1
      simpa [contproj_adaptedVec_inr] using this
    rw [hSv, inner_zero_right]

/-- The fixed columns of conjugation are the columns of fixed operators. -/
theorem hsConj_columnOperator_of_columnConj {x : lp (fun _ : AdaptedIndex U => H) 2}
    (hx : columnConj (adaptedBasis U) U x = x) :
    hsConj U (columnOperator (adaptedBasis U) x) = columnOperator (adaptedBasis U) x := by
  have h := congrArg (columnOperator (adaptedBasis U)) hx
  rwa [show columnConj (adaptedBasis U) U x = hsColumns (adaptedBasis U)
      (isHilbertSchmidt_hsConj (U := U) (isHilbertSchmidt_columnOperator (adaptedBasis U) x))
    from rfl, columnOperator_hsColumns] at h

/-- The fixed subspace of column conjugation. -/
abbrev fixedColumns (U : H ≃ₗᵢ[ℂ] H) : Submodule ℂ (lp (fun _ : AdaptedIndex U => H) 2) :=
  (columnConj (adaptedBasis U) U : lp (fun _ : AdaptedIndex U => H) 2 →ₗ[ℂ]
      lp (fun _ : AdaptedIndex U => H) 2).eqLocus
    ((1 : lp (fun _ : AdaptedIndex U => H) 2 →L[ℂ] lp (fun _ : AdaptedIndex U => H) 2) :
      lp (fun _ : AdaptedIndex U => H) 2 →ₗ[ℂ] lp (fun _ : AdaptedIndex U => H) 2)

/-- **Theorem 3.2.**  The atomic pinching is the Hilbert–Schmidt orthogonal projection onto the
fixed space: in the column Hilbert space `cols Π_at(T) = proj_{ker δ} (cols T)`. -/
theorem atomicPinch_eq_starProjection {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    (fixedColumns U).starProjection (hsColumns (adaptedBasis U) hT) =
      hsColumns (adaptedBasis U) (isHilbertSchmidt_atomicPinch (U := U) hT) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
  · rw [LinearMap.mem_eqLocus]
    show columnConj (adaptedBasis U) U _ = _
    rw [columnConj_hsColumns]
    congr 1
    exact hsConj_atomicPinch hT
  · have hwfix : columnConj (adaptedBasis U) U w = w := LinearMap.mem_eqLocus.mp hw
    have hS := hsConj_columnOperator_of_columnConj hwfix
    rw [lp.inner_eq_tsum]
    refine (tsum_congr fun i => ?_).trans tsum_zero
    have hwcol : (w : AdaptedIndex U → H) i =
        columnOperator (adaptedBasis U) w (adaptedVec U i) := by
      classical
      rw [← adaptedBasis_apply, columnOperator_basis]
    rw [lp.coeFn_sub, Pi.sub_apply, hsColumns_apply, hsColumns_apply, adaptedBasis_apply, hwcol,
      ← sub_apply]
    exact inner_sub_atomicPinch_fixed hT (isHilbertSchmidt_columnOperator _ w) hS i

/-- **Corollary 3.3, `(MSF.4)`.**  The Cesàro formation converges to the atomic pinching in
Hilbert–Schmidt norm. -/
theorem tendsto_hsNorm_hsCesaro_sub_atomicPinch {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    Tendsto (fun N => (hsCesaro U N T - atomicPinch U hT).hsNorm) atTop (𝓝 0) := by
  have h := (columnConj (adaptedBasis U) U).tendsto_birkhoffAverage_orthogonalProjection
    (norm_columnConj_le (adaptedBasis U) U) (hsColumns (adaptedBasis U) hT)
  rw [← Submodule.starProjection_apply, atomicPinch_eq_starProjection hT] at h
  have h2 := (tendsto_iff_norm_sub_tendsto_zero.mp h)
  refine h2.congr fun N => ?_
  have hHS : IsHilbertSchmidt (hsCesaro U N T - atomicPinch U hT) :=
    (isHilbertSchmidt_hsCesaro U hT N).sub (isHilbertSchmidt_atomicPinch (U := U) hT)
  rw [← norm_hsColumns (adaptedBasis U) hHS, ← hsColumns_hsCesaro (adaptedBasis U) U hT N]
  congr 1

/-- A fixed Hilbert–Schmidt operator equals its atomic pinching: it is the orthogonal sum of its
eigenspace blocks. -/
theorem atomicPinch_eq_self_of_fixed {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T)
    (hfix : hsConj U T = T) : atomicPinch U hT = T := by
  obtain ⟨h1, -, h3⟩ := (hsConj_eq_iff hT).mp hfix
  refine ext_adapted (U := U) fun i => ?_
  rw [atomicPinch_apply]
  rcases i with ⟨d, k⟩ | k
  · have := congrArg (fun L : H →L[ℂ] H => L (adaptedVec U (Sum.inl ⟨d, k⟩))) (h3 d)
    simp only [ContinuousLinearMap.comp_apply, eigenproj_adaptedVec_inl, if_true] at this
    exact this.symm
  · have := congrArg (fun L : H →L[ℂ] H => L (adaptedVec U (Sum.inr k))) h1
    simp only [ContinuousLinearMap.comp_apply, contproj_adaptedVec_inr, zero_apply] at this
    exact this.symm

/-- The eigenvalue label of an adapted index (`0` on `H_c`, where the pinching columns vanish). -/
def adaptedLabel : AdaptedIndex U → ℂ
  | Sum.inl j => j.1
  | Sum.inr _ => 0

theorem atomicPinch_sub_sum_apply {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (s : Finset ℂ)
    (i : AdaptedIndex U) :
    (atomicPinch U hT - ∑ c ∈ s, eigenproj U c ∘L T ∘L eigenproj U c) (adaptedVec U i) =
      if adaptedLabel i ∈ s then 0 else atomicPinchCol U T i := by
  rw [sub_apply, sum_apply, atomicPinch_apply]
  rcases i with ⟨d, k⟩ | k
  · simp only [ContinuousLinearMap.comp_apply, eigenproj_adaptedVec_inl]
    have : ∑ c ∈ s, eigenproj U c (T (if d = c then adaptedVec U (Sum.inl ⟨d, k⟩) else 0)) =
        if d ∈ s then atomicPinchCol U T (Sum.inl ⟨d, k⟩) else 0 := by
      rw [Finset.sum_congr rfl fun c _ => by rw [apply_ite T, map_zero, apply_ite (eigenproj U c),
        map_zero], Finset.sum_ite_eq]
      rfl
    rw [this]
    simp only [adaptedLabel]
    split_ifs <;> simp
  · simp [eigenproj_adaptedVec_inr, atomicPinchCol]

/-- **`(MSF.1)`.**  `Π_at(T) = ∑_λ P_λ T P_λ`: the finite block sums converge to the atomic
pinching in Hilbert–Schmidt norm. -/
theorem tendsto_hsNorm_atomicPinch_sub_sum {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    Tendsto (fun s : Finset ℂ =>
      (atomicPinch U hT - ∑ c ∈ s, eigenproj U c ∘L T ∘L eigenproj U c).hsNorm) atTop (𝓝 0) := by
  classical
  set g : AdaptedIndex U → ℝ := fun i => ‖atomicPinchCol U T i‖ ^ 2
  have hg : Summable g := summable_atomicPinchCol hT
  have hHS : ∀ s : Finset ℂ,
      IsHilbertSchmidt (atomicPinch U hT - ∑ c ∈ s, eigenproj U c ∘L T ∘L eigenproj U c) := by
    intro s
    refine (isHilbertSchmidt_atomicPinch hT).sub ?_
    induction s using Finset.induction_on with
    | empty => simpa using isHilbertSchmidt_zero
    | insert c s hcs ih =>
        rw [Finset.sum_insert hcs]
        exact ((hT.comp_right _).comp_left _).add ih
  have hsq : ∀ s : Finset ℂ,
      hsNormSq (atomicPinch U hT - ∑ c ∈ s, eigenproj U c ∘L T ∘L eigenproj U c) =
        ∑' i, Set.indicator {i | adaptedLabel i ∉ s} g i := by
    intro s
    rw [hsNormSq_eq (hHS s) (adaptedBasis U)]
    refine tsum_congr fun i => ?_
    rw [adaptedBasis_apply, atomicPinch_sub_sum_apply]
    by_cases h : adaptedLabel i ∈ s
    · simp [h]
    · simp [h, g]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp (tendsto_tsum_compl_atTop_zero g)) (ε ^ 2)
    (by positivity)
  refine ⟨J.image adaptedLabel, fun s hs => ?_⟩
  have htail := hJ J le_rfl
  rw [Real.dist_eq, sub_zero] at htail
  have hle : hsNormSq (atomicPinch U hT - ∑ c ∈ s, eigenproj U c ∘L T ∘L eigenproj U c) ≤
      ∑' i : {x // x ∉ J}, g i := by
    have hsub : (∑' i : {x // x ∉ J}, g i) = ∑' i, Set.indicator {x | x ∉ J} g i :=
      tsum_subtype ({x | x ∉ J} : Set (AdaptedIndex U)) g
    rw [hsq, hsub]
    refine Summable.tsum_le_tsum (fun i => ?_) (hg.indicator _) (hg.indicator _)
    by_cases hi : i ∈ J
    · have : adaptedLabel i ∈ s := hs (Finset.mem_image_of_mem _ hi)
      simp [Set.indicator, this, hi]
    · simp only [Set.indicator, Set.mem_setOf_eq, hi, not_false_eq_true, if_true]
      split_ifs
      · exact sq_nonneg ‖atomicPinchCol U T i‖
      · exact le_refl (g i)
  have hnn : 0 ≤ ∑' i : {x // x ∉ J}, g i := tsum_nonneg fun _ => sq_nonneg _
  rw [abs_of_nonneg hnn] at htail
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNorm_nonneg _), ContinuousLinearMap.hsNorm]
  calc Real.sqrt (hsNormSq _) ≤ Real.sqrt (∑' i : {x // x ∉ J}, g i) := Real.sqrt_le_sqrt hle
    _ < Real.sqrt (ε ^ 2) := Real.sqrt_lt_sqrt hnn htail
    _ = ε := Real.sqrt_sq hε.le

end Pinching

end GaloisForLFunctions.HTGeometry
