import GaloisForLFunctions.HTGeometry.ManifoldTopFormIntegral

/-!
# The product orientation and its chart signs

For finite-dimensional spaces `V, W` of positive dimensions `m, n`, the product of orientations
`o₁ × o₂` is the orientation of the concatenation of positively oriented bases
(`prodOrientation`); it is independent of the bases, transported factorwise by `A × B`
(`prodOrientation_map`), and changes sign with either factor.  Consequently, relative to the
product reference orientation, signs multiply:
`sign_{e₁×e₂}(o₁ × o₂) = sign_{e₁}(o₁) · sign_{e₂}(o₂)`.

On a product of oriented manifolds the tangent trivialization of a product chart is the product
of the factor trivializations (`tangentChartEquiv_prod`), so the pointwise product orientation is
locally constant and defines `prodManifoldOrientation`; its chart sign in a product chart is the
product of the factor chart signs (`chartSign_prodManifoldOrientation`).
-/

open Module

namespace GaloisForLFunctions.HTGeometry

section VectorSpace

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W] {m n : ℕ}

private theorem card_fin_eq {m : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (h : finrank ℝ V = m) : Fintype.card (Fin m) = finrank ℝ V := by simp [h]

/-- The product of orientations of two finite-dimensional spaces: the orientation of the
concatenation of positively oriented bases. -/
noncomputable def prodOrientation [NeZero m] [NeZero n] (hm : finrank ℝ V = m)
    (hn : finrank ℝ W = n) (o₁ : Orientation ℝ V (Fin m)) (o₂ : Orientation ℝ W (Fin n)) :
    Orientation ℝ (V × W) (Fin (m + n)) :=
  Orientation.reindex ℝ (V × W) finSumFinEquiv
    ((o₁.someBasis (card_fin_eq hm)).prod (o₂.someBasis (card_fin_eq hn))).orientation

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
private theorem prod_map_prodCongr (b : Basis (Fin m) ℝ V) (c : Basis (Fin n) ℝ W)
    (A : V ≃ₗ[ℝ] V) (B : W ≃ₗ[ℝ] W) :
    (b.prod c).map (A.prodCongr B) = (b.map A).prod (c.map B) := by
  ext i <;> rcases i with i | i <;> simp [Basis.map_apply, LinearEquiv.prodCongr_apply]

private theorem prodBasis_orientation_eq (b b₀ : Basis (Fin m) ℝ V) (c c₀ : Basis (Fin n) ℝ W)
    (hb : b.orientation = b₀.orientation) (hc : c.orientation = c₀.orientation) :
    (b.prod c).orientation = (b₀.prod c₀).orientation := by
  let A : V ≃ₗ[ℝ] V := b₀.equiv b (Equiv.refl _)
  let B : W ≃ₗ[ℝ] W := c₀.equiv c (Equiv.refl _)
  have hA' : b₀.map A = b := by ext i; simp [A]
  have hB' : c₀.map B = c := by ext i; simp [B]
  have hA : 0 < LinearMap.det (A : V →ₗ[ℝ] V) := by
    rw [← Basis.orientation_comp_linearEquiv_eq_iff_det_pos b₀ A, hA']
    exact hb
  have hB : 0 < LinearMap.det (B : W →ₗ[ℝ] W) := by
    rw [← Basis.orientation_comp_linearEquiv_eq_iff_det_pos c₀ B, hB']
    exact hc
  have hdet : 0 < LinearMap.det
      ((A.prodCongr B : (V × W) ≃ₗ[ℝ] (V × W)) : (V × W) →ₗ[ℝ] (V × W)) := by
    rw [LinearEquiv.coe_prodCongr, LinearMap.det_prodMap]
    exact mul_pos hA hB
  have h := (Basis.orientation_comp_linearEquiv_eq_iff_det_pos (b₀.prod c₀)
    (A.prodCongr B)).mpr hdet
  rwa [prod_map_prodCongr, hA', hB'] at h

/-- The product orientation computed from any positively oriented bases. -/
theorem prodOrientation_eq_of_basis [NeZero m] [NeZero n] (hm : finrank ℝ V = m)
    (hn : finrank ℝ W = n) {o₁ : Orientation ℝ V (Fin m)} {o₂ : Orientation ℝ W (Fin n)}
    (b : Basis (Fin m) ℝ V) (c : Basis (Fin n) ℝ W) (hb : b.orientation = o₁)
    (hc : c.orientation = o₂) :
    prodOrientation hm hn o₁ o₂ = Orientation.reindex ℝ (V × W) finSumFinEquiv
      (b.prod c).orientation := by
  unfold prodOrientation
  congr 1
  exact prodBasis_orientation_eq _ _ _ _ (by rw [Orientation.someBasis_orientation, hb])
    (by rw [Orientation.someBasis_orientation, hc])

private theorem compLinearMap_domDomCongr' {V' W' : Type*} [AddCommGroup V'] [Module ℝ V']
    [AddCommGroup W'] [Module ℝ W'] {ι ι' : Type*} (e : V' ≃ₗ[ℝ] W') (eι : ι ≃ ι')
    (v : V' [⋀^ι]→ₗ[ℝ] ℝ) :
    (v.domDomCongr eι).compLinearMap (e.symm : W' →ₗ[ℝ] V') =
      (v.compLinearMap (e.symm : W' →ₗ[ℝ] V')).domDomCongr eι := by
  ext g
  simp [AlternatingMap.compLinearMap_apply, Function.comp_def]

theorem orientation_map_reindex' {V' W' : Type*} [AddCommGroup V'] [Module ℝ V']
    [AddCommGroup W'] [Module ℝ W'] {ι ι' : Type*} (e : V' ≃ₗ[ℝ] W') (eι : ι ≃ ι')
    (x : Orientation ℝ V' ι) :
    Orientation.map ι' e (Orientation.reindex ℝ V' eι x) =
      Orientation.reindex ℝ W' eι (Orientation.map ι e x) := by
  induction x using Module.Ray.ind with
  | h v hv =>
    simp only [Orientation.map_apply, Orientation.reindex_apply]
    refine (ray_eq_iff _ _).mpr ?_
    rw [compLinearMap_domDomCongr']
    exact SameRay.rfl

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
private theorem prod_map_prodCongr' {V' W' : Type*} [AddCommGroup V'] [Module ℝ V']
    [AddCommGroup W'] [Module ℝ W'] (b : Basis (Fin m) ℝ V) (c : Basis (Fin n) ℝ W)
    (A : V ≃ₗ[ℝ] V') (B : W ≃ₗ[ℝ] W') :
    (b.prod c).map (A.prodCongr B) = (b.map A).prod (c.map B) := by
  ext i <;> rcases i with i | i <;> simp [Basis.map_apply, LinearEquiv.prodCongr_apply]

/-- Transporting both factors transports the product orientation. -/
theorem prodOrientation_map {V' W' : Type*} [AddCommGroup V'] [Module ℝ V']
    [FiniteDimensional ℝ V'] [AddCommGroup W'] [Module ℝ W'] [FiniteDimensional ℝ W']
    [NeZero m] [NeZero n]
    (hm : finrank ℝ V = m) (hn : finrank ℝ W = n) (hm' : finrank ℝ V' = m)
    (hn' : finrank ℝ W' = n) (o₁ : Orientation ℝ V (Fin m)) (o₂ : Orientation ℝ W (Fin n))
    (A : V ≃ₗ[ℝ] V') (B : W ≃ₗ[ℝ] W') :
    Orientation.map (Fin (m + n)) (A.prodCongr B) (prodOrientation hm hn o₁ o₂) =
      prodOrientation hm' hn' (Orientation.map (Fin m) A o₁) (Orientation.map (Fin n) B o₂) := by
  set b := o₁.someBasis (card_fin_eq hm)
  set c := o₂.someBasis (card_fin_eq hn)
  rw [prodOrientation_eq_of_basis hm hn b c (Orientation.someBasis_orientation _ _)
      (Orientation.someBasis_orientation _ _),
    prodOrientation_eq_of_basis hm' hn' (b.map A) (c.map B)
      (by rw [Basis.orientation_map, Orientation.someBasis_orientation])
      (by rw [Basis.orientation_map, Orientation.someBasis_orientation]),
    orientation_map_reindex', ← Basis.orientation_map, prod_map_prodCongr']

theorem prodOrientation_neg_left [NeZero m] [NeZero n] (hm : finrank ℝ V = m)
    (hn : finrank ℝ W = n) (o₁ : Orientation ℝ V (Fin m)) (o₂ : Orientation ℝ W (Fin n)) :
    prodOrientation hm hn (-o₁) o₂ = -prodOrientation hm hn o₁ o₂ := by
  set b := o₁.someBasis (card_fin_eq hm)
  set b' := (-o₁).someBasis (card_fin_eq hm)
  let A : V ≃ₗ[ℝ] V := b.equiv b' (Equiv.refl _)
  have hA' : b.map A = b' := by ext i; simp [A]
  have hmapA : Orientation.map (Fin m) A o₁ = -o₁ := by
    have hbo : b.orientation = o₁ := Orientation.someBasis_orientation _ _
    calc Orientation.map (Fin m) A o₁ = Orientation.map (Fin m) A b.orientation := by rw [hbo]
      _ = (b.map A).orientation := (Basis.orientation_map b A).symm
      _ = -o₁ := by rw [hA']; exact Orientation.someBasis_orientation _ _
  have hdetA : LinearMap.det (A : V →ₗ[ℝ] V) < 0 :=
    (Orientation.map_eq_neg_iff_det_neg o₁ A (card_fin_eq hm)).mp hmapA
  have hmap := prodOrientation_map hm hn hm hn o₁ o₂ A (LinearEquiv.refl ℝ W)
  rw [hmapA, Orientation.map_refl, Equiv.refl_apply] at hmap
  rw [← hmap]
  refine (Orientation.map_eq_neg_iff_det_neg _ _ (by simp [hm, hn, finrank_prod])).mpr ?_
  rw [LinearEquiv.coe_prodCongr, LinearMap.det_prodMap, LinearEquiv.refl_toLinearMap,
    LinearMap.det_id, mul_one]
  exact hdetA

theorem prodOrientation_neg_right [NeZero m] [NeZero n] (hm : finrank ℝ V = m)
    (hn : finrank ℝ W = n) (o₁ : Orientation ℝ V (Fin m)) (o₂ : Orientation ℝ W (Fin n)) :
    prodOrientation hm hn o₁ (-o₂) = -prodOrientation hm hn o₁ o₂ := by
  set c := o₂.someBasis (card_fin_eq hn)
  set c' := (-o₂).someBasis (card_fin_eq hn)
  let B : W ≃ₗ[ℝ] W := c.equiv c' (Equiv.refl _)
  have hB' : c.map B = c' := by ext i; simp [B]
  have hmapB : Orientation.map (Fin n) B o₂ = -o₂ := by
    have hco : c.orientation = o₂ := Orientation.someBasis_orientation _ _
    calc Orientation.map (Fin n) B o₂ = Orientation.map (Fin n) B c.orientation := by rw [hco]
      _ = (c.map B).orientation := (Basis.orientation_map c B).symm
      _ = -o₂ := by rw [hB']; exact Orientation.someBasis_orientation _ _
  have hdetB : LinearMap.det (B : W →ₗ[ℝ] W) < 0 :=
    (Orientation.map_eq_neg_iff_det_neg o₂ B (card_fin_eq hn)).mp hmapB
  have hmap := prodOrientation_map hm hn hm hn o₁ o₂ (LinearEquiv.refl ℝ V) B
  rw [hmapB, Orientation.map_refl, Equiv.refl_apply] at hmap
  rw [← hmap]
  refine (Orientation.map_eq_neg_iff_det_neg _ _ (by simp [hm, hn, finrank_prod])).mpr ?_
  rw [LinearEquiv.coe_prodCongr, LinearMap.det_prodMap, LinearEquiv.refl_toLinearMap,
    LinearMap.det_id, one_mul]
  exact hdetB

end VectorSpace

section Sign

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] {m n : ℕ}

/-- **Sign multiplicativity**: relative to a product reference orientation, the sign of a
product orientation is the product of the signs. -/
theorem orientationSign_prodOrientation [NeZero m] [NeZero n] (hm : finrank ℝ E₁ = m)
    (hn : finrank ℝ E₂ = n) (e₁ o₁ : Orientation ℝ E₁ (Fin m))
    (e₂ o₂ : Orientation ℝ E₂ (Fin n)) :
    orientationSign (prodOrientation hm hn e₁ e₂) (prodOrientation hm hn o₁ o₂) =
      orientationSign e₁ o₁ * orientationSign e₂ o₂ := by
  have hc1 : Fintype.card (Fin m) = finrank ℝ E₁ := by simp [hm]
  have hc2 : Fintype.card (Fin n) = finrank ℝ E₂ := by simp [hn]
  rcases Orientation.eq_or_eq_neg o₁ e₁ hc1 with h1 | h1 <;>
    rcases Orientation.eq_or_eq_neg o₂ e₂ hc2 with h2 | h2 <;> subst h1 <;> subst h2
  · simp [orientationSign_self]
  · rw [prodOrientation_neg_right, orientationSign_self, orientationSign, orientationSign,
      if_neg (Module.Ray.ne_neg_self _).symm, if_neg (Module.Ray.ne_neg_self _).symm]
    ring
  · rw [prodOrientation_neg_left, orientationSign_self, orientationSign, orientationSign,
      if_neg (Module.Ray.ne_neg_self _).symm, if_neg (Module.Ray.ne_neg_self _).symm]
    ring
  · have hnn : - -prodOrientation hm hn e₁ e₂ = prodOrientation hm hn e₁ e₂ := by
      exact @neg_neg (Orientation ℝ (E₁ × E₂) (Fin (m + n))) _ _
    rw [prodOrientation_neg_left, prodOrientation_neg_right, hnn, orientationSign_self,
      orientationSign, orientationSign, if_neg (Module.Ray.ne_neg_self _).symm,
      if_neg (Module.Ray.ne_neg_self _).symm]
    ring

end Sign

section Manifold

open Manifold Bundle Set
open scoped Manifold ContDiff

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {H₁ H₂ : Type*} [TopologicalSpace H₁] [TopologicalSpace H₂]
  {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
  {M₁ M₂ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]

/-- In a product chart the tangent coordinate change is the product of the factor changes. -/
theorem tangentCoordChange_prod (p z : M₁ × M₂)
    (hz : z ∈ (chartAt (ModelProd H₁ H₂) p).source) :
    tangentCoordChange (I₁.prod I₂) z p z =
      (tangentCoordChange I₁ z.1 p.1 z.1).prodMap (tangentCoordChange I₂ z.2 p.2 z.2) := by
  have hz' : z.1 ∈ (chartAt H₁ p.1).source ∧ z.2 ∈ (chartAt H₂ p.2).source := by
    simpa only [prodChartedSpace_chartAt, OpenPartialHomeomorph.prod_source, Set.mem_prod]
      using hz
  have hz₁ : z.1 ∈ (extChartAt I₁ z.1).source ∩ (extChartAt I₁ p.1).source :=
    ⟨mem_extChartAt_source .., by simpa only [extChartAt_source] using hz'.1⟩
  have hz₂ : z.2 ∈ (extChartAt I₂ z.2).source ∩ (extChartAt I₂ p.2).source :=
    ⟨mem_extChartAt_source .., by simpa only [extChartAt_source] using hz'.2⟩
  have hzp : z ∈ (extChartAt (I₁.prod I₂) z).source ∩ (extChartAt (I₁.prod I₂) p).source :=
    ⟨mem_extChartAt_source .., by simpa only [extChartAt_source] using hz⟩
  refine ((I₁.prod I₂).uniqueDiffWithinAt_image (x := (chartAt (ModelProd H₁ H₂) z) z)).eq
    (hasFDerivWithinAt_tangentCoordChange (I := I₁.prod I₂) hzp) ?_
  have h₁ := hasFDerivWithinAt_tangentCoordChange (I := I₁) hz₁
  have h₂ := hasFDerivWithinAt_tangentCoordChange (I := I₂) hz₂
  have hs₁ : Prod.fst '' (Set.range (I₁.prod I₂)) = Set.range I₁ := by
    rw [ModelWithCorners.range_prod]
    exact Set.fst_image_prod (Set.range I₁) ⟨I₂ ((chartAt H₂ p.2) p.2), Set.mem_range_self _⟩
  have hs₂ : Prod.snd '' (Set.range (I₁.prod I₂)) = Set.range I₂ := by
    rw [ModelWithCorners.range_prod]
    exact Set.snd_image_prod ⟨I₁ ((chartAt H₁ p.1) p.1), Set.mem_range_self _⟩ (Set.range I₂)
  rw [← hs₁] at h₁
  rw [← hs₂] at h₂
  have h := HasFDerivWithinAt.prodMap
    (p := (extChartAt I₁ z.1 z.1, extChartAt I₂ z.2 z.2)) h₁ h₂
  have hfun : ((extChartAt (I₁.prod I₂) p) ∘ (extChartAt (I₁.prod I₂) z).symm) =
      Prod.map ((extChartAt I₁ p.1) ∘ (extChartAt I₁ z.1).symm)
        ((extChartAt I₂ p.2) ∘ (extChartAt I₂ z.2).symm) := by
    funext q
    simp only [Function.comp_apply, extChartAt_prod, PartialEquiv.prod_symm,
      PartialEquiv.prod_coe]
    rfl
  have hpt : extChartAt (I₁.prod I₂) z z = (extChartAt I₁ z.1 z.1, extChartAt I₂ z.2 z.2) := by
    simp only [extChartAt_prod, PartialEquiv.prod_coe]
  rw [← hfun, ← hpt] at h
  exact h

/-- The tangent chart equivalence of a product chart is the product of the factor ones. -/
theorem tangentChartEquiv_prod (p z : M₁ × M₂)
    (hz : z ∈ (trivializationAt (E₁ × E₂) (TangentSpace (I₁.prod I₂)) p).baseSet)
    (h₁ : z.1 ∈ (trivializationAt E₁ (TangentSpace I₁) p.1).baseSet)
    (h₂ : z.2 ∈ (trivializationAt E₂ (TangentSpace I₂) p.2).baseSet) :
    DifferentialGeometry.tangentChartEquiv (I₁.prod I₂) (M₁ × M₂) p z hz =
      (DifferentialGeometry.tangentChartEquiv I₁ M₁ p.1 z.1 h₁).prodCongr
        (DifferentialGeometry.tangentChartEquiv I₂ M₂ p.2 z.2 h₂) := by
  have hzc : z ∈ (chartAt (ModelProd H₁ H₂) p).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hz
  have h₁c : z.1 ∈ (chartAt H₁ p.1).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using h₁
  have h₂c : z.2 ∈ (chartAt H₂ p.2).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using h₂
  refine LinearEquiv.ext fun v => ?_
  change (Bundle.Trivialization.linearEquivAt ℝ
      (trivializationAt (E₁ × E₂) (TangentSpace (I₁.prod I₂)) p) z hz) v =
    (Bundle.Trivialization.linearEquivAt ℝ (trivializationAt E₁ (TangentSpace I₁) p.1) z.1 h₁ v.1,
      Bundle.Trivialization.linearEquivAt ℝ (trivializationAt E₂ (TangentSpace I₂) p.2) z.2 h₂
        v.2)
  simp only [Bundle.Trivialization.linearEquivAt_apply]
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hz,
    ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ h₁,
    ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ h₂]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hzc,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core h₁c,
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core h₂c]
  exact congrArg (fun L => L v) (tangentCoordChange_prod (I₁ := I₁) (I₂ := I₂) p z hzc)


theorem mem_baseSet_prod_iff (p z : M₁ × M₂) :
    z ∈ (trivializationAt (E₁ × E₂) (TangentSpace (I₁.prod I₂)) p).baseSet ↔
      z.1 ∈ (trivializationAt E₁ (TangentSpace I₁) p.1).baseSet ∧
        z.2 ∈ (trivializationAt E₂ (TangentSpace I₂) p.2).baseSet := by
  simp only [TangentBundle.trivializationAt_baseSet, prodChartedSpace_chartAt,
    OpenPartialHomeomorph.prod_source, Set.mem_prod]

variable [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] {m n : ℕ} [NeZero m] [NeZero n]

/-- **The product orientation** of two oriented manifolds. -/
noncomputable def prodManifoldOrientation
    (o₁ : DifferentialGeometry.ManifoldOrientation I₁ M₁ m)
    (o₂ : DifferentialGeometry.ManifoldOrientation I₂ M₂ n) :
    DifferentialGeometry.ManifoldOrientation (I₁.prod I₂) (M₁ × M₂) (m + n) where
  dimension_eq := by simp [Module.finrank_prod, o₁.dimension_eq, o₂.dimension_eq]
  orientation z := prodOrientation o₁.dimension_eq o₂.dimension_eq (o₁.orientation z.1)
    (o₂.orientation z.2)
  locally_constant := by
    intro p x hx
    obtain ⟨hx₁, hx₂⟩ := (mem_baseSet_prod_iff p x).mp hx
    obtain ⟨U₁, hU₁o, hxU₁, hU₁, hlc₁⟩ := o₁.locally_constant p.1 x.1 hx₁
    obtain ⟨U₂, hU₂o, hxU₂, hU₂, hlc₂⟩ := o₂.locally_constant p.2 x.2 hx₂
    have hU : U₁ ×ˢ U₂ ⊆ (trivializationAt (E₁ × E₂) (TangentSpace (I₁.prod I₂)) p).baseSet :=
      fun y hy => (mem_baseSet_prod_iff p y).mpr ⟨hU₁ hy.1, hU₂ hy.2⟩
    refine ⟨U₁ ×ˢ U₂, hU₁o.prod hU₂o, ⟨hxU₁, hxU₂⟩, hU, fun y hy => ?_⟩
    rw [tangentChartEquiv_prod p y (hU hy) (hU₁ hy.1) (hU₂ hy.2),
      tangentChartEquiv_prod p x hx hx₁ hx₂]
    calc Orientation.map (Fin (m + n))
          ((DifferentialGeometry.tangentChartEquiv I₁ M₁ p.1 y.1 (hU₁ hy.1)).prodCongr
            (DifferentialGeometry.tangentChartEquiv I₂ M₂ p.2 y.2 (hU₂ hy.2)))
          (prodOrientation o₁.dimension_eq o₂.dimension_eq (o₁.orientation y.1)
            (o₂.orientation y.2))
        = prodOrientation o₁.dimension_eq o₂.dimension_eq
            (Orientation.map (Fin m) (DifferentialGeometry.tangentChartEquiv I₁ M₁ p.1 y.1
              (hU₁ hy.1)) (o₁.orientation y.1))
            (Orientation.map (Fin n) (DifferentialGeometry.tangentChartEquiv I₂ M₂ p.2 y.2
              (hU₂ hy.2)) (o₂.orientation y.2)) :=
          prodOrientation_map _ _ o₁.dimension_eq o₂.dimension_eq _ _ _ _
      _ = prodOrientation o₁.dimension_eq o₂.dimension_eq
            (Orientation.map (Fin m) (DifferentialGeometry.tangentChartEquiv I₁ M₁ p.1 x.1 hx₁)
              (o₁.orientation x.1))
            (Orientation.map (Fin n) (DifferentialGeometry.tangentChartEquiv I₂ M₂ p.2 x.2 hx₂)
              (o₂.orientation x.2)) := by
          rw [hlc₁ y.1 hy.1, hlc₂ y.2 hy.2]
      _ = Orientation.map (Fin (m + n))
          ((DifferentialGeometry.tangentChartEquiv I₁ M₁ p.1 x.1 hx₁).prodCongr
            (DifferentialGeometry.tangentChartEquiv I₂ M₂ p.2 x.2 hx₂))
          (prodOrientation o₁.dimension_eq o₂.dimension_eq (o₁.orientation x.1)
            (o₂.orientation x.2)) :=
          (prodOrientation_map _ _ o₁.dimension_eq o₂.dimension_eq _ _ _ _).symm

/-- The product orientation read in a product chart. -/
theorem prodManifoldOrientation_inChart
    (o₁ : DifferentialGeometry.ManifoldOrientation I₁ M₁ m)
    (o₂ : DifferentialGeometry.ManifoldOrientation I₂ M₂ n) (p z : M₁ × M₂)
    (hz : z ∈ (trivializationAt (E₁ × E₂) (TangentSpace (I₁.prod I₂)) p).baseSet)
    (h₁ : z.1 ∈ (trivializationAt E₁ (TangentSpace I₁) p.1).baseSet)
    (h₂ : z.2 ∈ (trivializationAt E₂ (TangentSpace I₂) p.2).baseSet) :
    (prodManifoldOrientation o₁ o₂).inChart p z hz =
      prodOrientation o₁.dimension_eq o₂.dimension_eq (o₁.inChart p.1 z.1 h₁)
        (o₂.inChart p.2 z.2 h₂) := by
  unfold DifferentialGeometry.ManifoldOrientation.inChart
  rw [tangentChartEquiv_prod p z hz h₁ h₂]
  exact prodOrientation_map o₁.dimension_eq o₂.dimension_eq o₁.dimension_eq o₂.dimension_eq
    _ _ _ _

/-- **Chart-sign multiplicativity** for the product orientation. -/
theorem chartSign_prodManifoldOrientation
    (o₁ : DifferentialGeometry.ManifoldOrientation I₁ M₁ m)
    (o₂ : DifferentialGeometry.ManifoldOrientation I₂ M₂ n)
    (e₁ : Orientation ℝ E₁ (Fin m)) (e₂ : Orientation ℝ E₂ (Fin n)) (p z : M₁ × M₂) :
    chartSign (prodManifoldOrientation o₁ o₂)
        (prodOrientation o₁.dimension_eq o₂.dimension_eq e₁ e₂) p z =
      chartSign o₁ e₁ p.1 z.1 * chartSign o₂ e₂ p.2 z.2 := by
  unfold chartSign
  by_cases hz : z ∈ (trivializationAt (E₁ × E₂) (TangentSpace (I₁.prod I₂)) p).baseSet
  · obtain ⟨h₁, h₂⟩ := (mem_baseSet_prod_iff p z).mp hz
    rw [dif_pos hz, dif_pos h₁, dif_pos h₂, prodManifoldOrientation_inChart o₁ o₂ p z hz h₁ h₂,
      orientationSign_prodOrientation]
  · rw [dif_neg hz]
    rw [mem_baseSet_prod_iff, not_and_or] at hz
    rcases hz with h | h
    · rw [dif_neg h, zero_mul]
    · rw [dif_neg h, mul_zero]

end Manifold

end GaloisForLFunctions.HTGeometry
