import GaloisForLFunctions.HTGeometry.HilbertSchmidtTraceIdeal
import GaloisForLFunctions.HTGeometry.ComplexJacobiFormula

/-!
# The determinant of finite-rank perturbations of the identity

For a bounded operator `g` on a complex inner-product space whose defect `g − 1` has finite rank,
`finiteRankDet g` is the determinant of `g` on the invariant subspace `range (g − 1)`.

* `det_restrict_eq_finiteRankDet`: the same value on every finite-dimensional `V ⊇ range (g − 1)`
  (the induced map on `V / range (g − 1)` is the identity).
* `finiteRankDet_mul`, `finiteRankDet_one`, `finiteRankDet_ne_zero`: multiplicativity and
  non-vanishing on invertible operators.
* `opTrace_eq_trace_restrict`: the operator trace of an operator with range in a finite-dimensional
  `V` is the trace of its restriction to `V`.
* `hasDerivAt_finiteRankDet` (**Jacobi's formula**): along a differentiable path with defects in a
  fixed `V`, `d/dt det g = det g · Tr(g⁻¹ ġ)`.
* `finiteRankDet_eq_mul_exp_integral`: `det g(b) = det g(a) · exp ∫ₐᵇ Tr(g⁻¹ ġ)`.
-/

set_option autoImplicit false

open ContinuousLinearMap
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `g` maps the range of `g − 1` into itself. -/
theorem mapsTo_range_sub_one (g : H →L[ℂ] H) :
    ∀ x ∈ LinearMap.range ((g : H →ₗ[ℂ] H) - 1),
      (g : H →ₗ[ℂ] H) x ∈ LinearMap.range ((g : H →ₗ[ℂ] H) - 1) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨g y, ?_⟩
  simp

/-- The determinant of an operator `g` whose defect `g − 1` has finite rank: the determinant of
`g` on the invariant subspace `range (g − 1)`. -/
def finiteRankDet (g : H →L[ℂ] H) : ℂ :=
  LinearMap.det ((g : H →ₗ[ℂ] H).restrict (mapsTo_range_sub_one g))

theorem mapsTo_of_range_le {g : H →L[ℂ] H} {V : Submodule ℂ H}
    (hV : LinearMap.range ((g : H →ₗ[ℂ] H) - 1) ≤ V) : ∀ x ∈ V, (g : H →ₗ[ℂ] H) x ∈ V := by
  intro x hx
  have h : (g : H →ₗ[ℂ] H) x - x ∈ V := hV ⟨x, by simp⟩
  simpa using V.add_mem h hx

/-- **Independence of the invariant subspace**: on any finite-dimensional `V ⊇ range (g − 1)` the
determinant of `g` is `finiteRankDet g`, since `g` acts trivially on `V / range (g − 1)`. -/
theorem det_restrict_eq_finiteRankDet {g : H →L[ℂ] H} {V : Submodule ℂ H} [FiniteDimensional ℂ V]
    (hV : LinearMap.range ((g : H →ₗ[ℂ] H) - 1) ≤ V) :
    LinearMap.det ((g : H →ₗ[ℂ] H).restrict (mapsTo_of_range_le hV)) = finiteRankDet g := by
  set R := LinearMap.range ((g : H →ₗ[ℂ] H) - 1)
  set e := (g : H →ₗ[ℂ] H).restrict (mapsTo_of_range_le hV)
  set W : Submodule ℂ V := R.comap V.subtype
  have he : W ≤ W.comap e := by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply, W] at hx ⊢
    exact mapsTo_range_sub_one g _ hx
  rw [LinearMap.det_eq_det_mul_det W e he]
  have hq : W.mapQ W e he = LinearMap.id := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, LinearMap.id_comp]
    rw [Submodule.Quotient.eq]
    show ((e x : V) : H) - x ∈ R
    exact ⟨x, by simp [e]⟩
  rw [hq, LinearMap.det_id, mul_one]
  -- `W ≃ R` intertwines the two restrictions
  have hWR : ∀ x : R, (x : H) ∈ V := fun x => hV x.2
  let φ : W ≃ₗ[ℂ] R :=
    { toFun := fun x => ⟨((x : V) : H), x.2⟩
      invFun := fun x => ⟨⟨x, hWR x⟩, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← LinearMap.det_conj (e.restrict he) φ]
  unfold finiteRankDet
  congr 1

theorem finiteRankDet_one : finiteRankDet (1 : H →L[ℂ] H) = 1 := by
  have h : LinearMap.range (((1 : H →L[ℂ] H) : H →ₗ[ℂ] H) - 1) = ⊥ := by simp
  rw [← det_restrict_eq_finiteRankDet (V := ⊥) h.le]
  exact LinearMap.det_eq_one_of_subsingleton _

/-- **Multiplicativity** of the finite-rank determinant. -/
theorem finiteRankDet_mul {g h : H →L[ℂ] H}
    (hg : FiniteDimensional ℂ (LinearMap.range ((g : H →ₗ[ℂ] H) - 1)))
    (hh : FiniteDimensional ℂ (LinearMap.range ((h : H →ₗ[ℂ] H) - 1))) :
    finiteRankDet (g * h) = finiteRankDet g * finiteRankDet h := by
  set V := LinearMap.range ((g : H →ₗ[ℂ] H) - 1) ⊔ LinearMap.range ((h : H →ₗ[ℂ] H) - 1)
  haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_sup _ _
  have hgV : LinearMap.range ((g : H →ₗ[ℂ] H) - 1) ≤ V := le_sup_left
  have hhV : LinearMap.range ((h : H →ₗ[ℂ] H) - 1) ≤ V := le_sup_right
  have hghV : LinearMap.range (((g * h : H →L[ℂ] H) : H →ₗ[ℂ] H) - 1) ≤ V := by
    rintro _ ⟨x, rfl⟩
    have h1 : ((g : H →ₗ[ℂ] H) - 1) (h x) ∈ V := hgV ⟨h x, rfl⟩
    have h2 : ((h : H →ₗ[ℂ] H) - 1) x ∈ V := hhV ⟨x, rfl⟩
    have := V.add_mem h1 h2
    simpa [sub_add_sub_cancel] using this
  rw [← det_restrict_eq_finiteRankDet hghV, ← det_restrict_eq_finiteRankDet hgV,
    ← det_restrict_eq_finiteRankDet hhV, ← LinearMap.det_comp]
  congr 1

/-- An invertible operator with finite-rank defect has nonzero determinant. -/
theorem finiteRankDet_ne_zero {g : H →L[ℂ] H} (hu : IsUnit g)
    (hg : FiniteDimensional ℂ (LinearMap.range ((g : H →ₗ[ℂ] H) - 1))) :
    finiteRankDet g ≠ 0 := by
  set e := (g : H →ₗ[ℂ] H).restrict (mapsTo_range_sub_one g)
  have hginj : Function.Injective g := by
    obtain ⟨u, rfl⟩ := hu
    intro a b hab
    have h2 := congrArg (↑u⁻¹ : H →L[ℂ] H) hab
    rwa [← mul_apply_eq_comp, ← mul_apply_eq_comp, Units.inv_mul,
      one_apply_eq_self, one_apply_eq_self] at h2
  have hinj : Function.Injective e := by
    intro x y hxy
    exact Subtype.ext (hginj (congrArg Subtype.val hxy))
  have hunit : IsUnit e := (Module.End.isUnit_iff e).mpr
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  exact (LinearMap.isUnit_iff_isUnit_det e |>.mp hunit).ne_zero

/-! ## Comparison with the operator trace -/

section Trace

variable [CompleteSpace H]

open InnerProductSpace in
theorem opTrace_rankOne_eq (x y : H) : opTrace (rankOne ℂ x y) = ⟪y, x⟫_ℂ := by
  rw [opTrace]
  simpa only [rankOne_apply, inner_smul_right] using (hsBasis ℂ H).tsum_inner_mul_inner y x

open InnerProductSpace in
theorem summable_diag_rankOne (x y : H) :
    Summable fun i => ⟪hsBasis ℂ H i, rankOne ℂ x y (hsBasis ℂ H i)⟫_ℂ := by
  simpa only [rankOne_apply, inner_smul_right] using (hsBasis ℂ H).summable_inner_mul_inner y x

open InnerProductSpace in
/-- The operator trace of an operator with range in a finite-dimensional subspace `V` is the trace
of its restriction to `V`. -/
theorem opTrace_eq_trace_restrict {T : H →L[ℂ] H} {V : Submodule ℂ H} [FiniteDimensional ℂ V]
    (hT : ∀ x, T x ∈ V) :
    opTrace T = LinearMap.trace ℂ V ((T : H →ₗ[ℂ] H).restrict (fun x _ => hT x)) := by
  set b := stdOrthonormalBasis ℂ V
  have hexp : T = ∑ j, rankOne ℂ (b j : H) (adjoint T (b j : H)) := by
    ext x
    have hrep := b.sum_repr (⟨T x, hT x⟩ : V)
    have hc := congrArg Subtype.val hrep
    rw [Submodule.coe_sum] at hc
    rw [_root_.sum_apply]
    conv_lhs => rw [show T x = ((⟨T x, hT x⟩ : V) : H) from rfl, ← hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rankOne_apply, Submodule.coe_smul, OrthonormalBasis.repr_apply_apply,
      adjoint_inner_left]
    rfl
  have hsum : opTrace (∑ j, rankOne ℂ (b j : H) (adjoint T (b j : H))) =
      ∑ j, opTrace (rankOne ℂ (b j : H) (adjoint T (b j : H))) := by
    simp only [opTrace, sum_apply, inner_sum]
    exact Summable.tsum_finsetSum fun j _ => summable_diag_rankOne _ _
  conv_lhs => rw [hexp]
  rw [hsum, LinearMap.trace_eq_matrix_trace ℂ b.toBasis, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [opTrace_rankOne_eq, adjoint_inner_left, Matrix.diag_apply, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.coe_toBasis]
  rfl

end Trace

/-! ## Jacobi's formula along paths -/

section Jacobi

variable [CompleteSpace H] {V : Submodule ℂ H} [FiniteDimensional ℂ V]

omit [CompleteSpace H] in
/-- The derivative of an operator path whose defect stays in `V` has range in `V`. -/
theorem deriv_mem_of_defect_mem {g : ℝ → H →L[ℂ] H} {g' : H →L[ℂ] H} {t : ℝ}
    (hV : ∀ᶠ s in nhds t, ∀ x, g s x - x ∈ V) (hg : HasDerivAt g g' t) (x : H) : g' x ∈ V := by
  have hx : HasDerivAt (fun s => g s x - x) (g' x) t := by
    have := ((ContinuousLinearMap.apply ℂ H x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hg
    simpa using this.sub_const x
  have hcl : IsClosed (V : Set H) := V.closed_of_finiteDimensional
  refine hcl.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.mp hx) ?_
  filter_upwards [nhdsWithin_le_nhds hV] with s hs
  simp only [slope_def_module, SetLike.mem_coe]
  exact V.smul_mem _ (V.sub_mem (hs x) (hV.self_of_nhds x))

/-- The matrix entry `⟪b i, T (b j)⟫` as a continuous functional of the operator `T`. -/
def operatorMatrixEntry (u v : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ H v)

omit [CompleteSpace H] in
theorem operatorMatrixEntry_apply (u v : H) (T : H →L[ℂ] H) :
    operatorMatrixEntry u v T = ⟪u, T v⟫_ℂ := rfl

omit [CompleteSpace H] [FiniteDimensional ℂ V] in
/-- The matrix of the restriction of a `V`-preserving operator in an orthonormal basis of `V`. -/
theorem toMatrix_restrict_apply {T : H →L[ℂ] H} (hT : ∀ v ∈ V, T v ∈ V)
    (b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V) (i j : Fin (Module.finrank ℂ V)) :
    LinearMap.toMatrix b.toBasis b.toBasis ((T : H →ₗ[ℂ] H).restrict hT) i j =
      ⟪(b i : H), T (b j : H)⟫_ℂ := by
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]
  rfl

/-- **Jacobi's formula** for the finite-rank determinant along a path with defects in `V`:
`d/dt det g = det g · Tr(g⁻¹ ġ)`. -/
theorem hasDerivAt_finiteRankDet {g : ℝ → H →L[ℂ] H} {g' : H →L[ℂ] H} {t : ℝ}
    (hV : ∀ᶠ s in nhds t, ∀ x, g s x - x ∈ V) (hg : HasDerivAt g g' t) (hu : IsUnit (g t)) :
    HasDerivAt (fun s => finiteRankDet (g s))
      (finiteRankDet (g t) * opTrace (Ring.inverse (g t) * g')) t := by
  classical
  have hR' : ∀ s, (∀ x, g s x - x ∈ V) → LinearMap.range ((g s : H →ₗ[ℂ] H) - 1) ≤ V := by
    rintro s hs _ ⟨x, rfl⟩
    simpa using hs x
  have hgV' : ∀ s, (∀ x, g s x - x ∈ V) → ∀ v ∈ V, g s v ∈ V := fun s hs v hv => by
    simpa using V.add_mem (hs v) hv
  have hVt := hV.self_of_nhds
  have hR := hR' t hVt
  have hgV := hgV' t hVt
  set b := stdOrthonormalBasis ℂ V
  set n := Module.finrank ℂ V
  set M : ℝ → Fin n → Fin n → ℂ := fun s i j => ⟪(b i : H), g s (b j : H)⟫_ℂ
  have hM : HasDerivAt M (fun i j => ⟪(b i : H), g' (b j : H)⟫_ℂ) t := by
    refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
    exact ((operatorMatrixEntry (b i : H) (b j : H)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      t hg
  have hMs : ∀ s (hs : ∀ x, g s x - x ∈ V), Matrix.of (M s) =
      LinearMap.toMatrix b.toBasis b.toBasis ((g s : H →ₗ[ℂ] H).restrict (hgV' s hs)) :=
    fun s hs => by
      ext i j
      rw [toMatrix_restrict_apply]
      rfl
  have hdet : ∀ s (hs : ∀ x, g s x - x ∈ V), Matrix.det (Matrix.of (M s)) = finiteRankDet (g s) :=
    fun s hs => by rw [hMs s hs, LinearMap.det_toMatrix, det_restrict_eq_finiteRankDet (hR' s hs)]
  have J := hasDerivAt_det_complex hM
  have hev : (fun s => Matrix.det (Matrix.of (M s))) =ᶠ[nhds t] fun s => finiteRankDet (g s) := by
    filter_upwards [hV] with s hs
    exact hdet s hs
  refine (J.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  -- identify `tr(adj M · M')` with `det g · Tr(g⁻¹ ġ)`
  obtain ⟨u, hu'⟩ := hu
  set ginv : H →L[ℂ] H := ↑u⁻¹
  have hginv_g : ∀ x, ginv (g t x) = x := fun x => by
    rw [← hu', ← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]
  have hsurj : ∀ v ∈ V, ∃ w ∈ V, g t w = v := by
    let e : V →ₗ[ℂ] V := (g t : H →ₗ[ℂ] H).restrict hgV
    have hinj : Function.Injective e := fun x y hxy => Subtype.ext (by
      have h1 := congrArg (fun z : V => ginv (z : H)) hxy
      simpa [e, hginv_g] using h1)
    intro v hv
    obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨v, hv⟩
    exact ⟨w, w.2, congrArg Subtype.val hw⟩
  have hginvV : ∀ v ∈ V, ginv v ∈ V := fun v hv => by
    obtain ⟨w, hw, rfl⟩ := hsurj v hv
    rwa [hginv_g]
  have hg'V := deriv_mem_of_defect_mem hV hg
  have hRi : Ring.inverse (g t) = ginv := by rw [← hu', Ring.inverse_unit]
  have hdet0 : Matrix.det (Matrix.of (M t)) ≠ 0 := by
    rw [hdet t hVt]
    exact finiteRankDet_ne_zero ⟨u, hu'⟩ (Submodule.finiteDimensional_of_le hR)
  rw [trace_adjugate_mul_eq _ _ hdet0, hdet t hVt, hRi]
  congr 1
  have hginvV' : ∀ v ∈ V, ginv v ∈ V := hginvV
  have hg'V' : ∀ v ∈ V, g' v ∈ V := fun v _ => hg'V v
  have hT : ∀ x, (ginv * g') x ∈ V := fun x => hginvV _ (hg'V x)
  have hinv : (Matrix.of (M t))⁻¹ =
      LinearMap.toMatrix b.toBasis b.toBasis ((ginv : H →ₗ[ℂ] H).restrict hginvV') := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hMs t hVt, ← LinearMap.toMatrix_mul]
    have : ((ginv : H →ₗ[ℂ] H).restrict hginvV') * ((g t : H →ₗ[ℂ] H).restrict hgV) = 1 := by
      ext v
      simp [hginv_g]
    rw [this, LinearMap.toMatrix_one]
  have hB : Matrix.of (fun i j => ⟪(b i : H), g' (b j : H)⟫_ℂ) =
      LinearMap.toMatrix b.toBasis b.toBasis ((g' : H →ₗ[ℂ] H).restrict hg'V') := by
    ext i j
    rw [toMatrix_restrict_apply]
    rfl
  rw [hinv, hB, ← LinearMap.toMatrix_mul, ← LinearMap.trace_eq_matrix_trace,
    opTrace_eq_trace_restrict hT]
  congr 1

/-- **Integrated Jacobi formula**: along a path with defects in `V`,
`det g(b) = det g(a) · exp ∫ₐᵇ Tr(g⁻¹ ġ)`. -/
theorem finiteRankDet_eq_mul_exp_integral {g g' : ℝ → H →L[ℂ] H} {a b : ℝ} (hab : a ≤ b)
    {U : Set ℝ} (hU : IsOpen U) (hIcc : Set.Icc a b ⊆ U)
    (hV : ∀ s ∈ U, ∀ x, g s x - x ∈ V) (hg : ∀ s ∈ U, HasDerivAt g (g' s) s)
    (hu : ∀ s ∈ U, IsUnit (g s))
    (hτ : ContinuousOn (fun s => opTrace (Ring.inverse (g s) * g' s)) (Set.Icc a b)) :
    finiteRankDet (g b) =
      finiteRankDet (g a) * Complex.exp (∫ s in a..b, opTrace (Ring.inverse (g s) * g' s)) := by
  set τ : ℝ → ℂ := fun s => opTrace (Ring.inverse (g s) * g' s) with hτdef
  set F : ℝ → ℂ := fun s => ∫ r in a..s, τ r
  set ψ : ℝ → ℂ := fun s => finiteRankDet (g s) * Complex.exp (-F s)
  have hD : ∀ x ∈ U, HasDerivAt (fun s => finiteRankDet (g s)) (finiteRankDet (g x) * τ x) x :=
    fun x hx => hasDerivAt_finiteRankDet (Filter.eventually_of_mem (hU.mem_nhds hx) hV)
      (hg x hx) (hu x hx)
  have hFcont : ContinuousOn F (Set.Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume)
      (hτ.mono (Set.uIcc_of_le hab).subset |>.integrableOn_compact isCompact_uIcc)
    rwa [Set.uIcc_of_le hab] at this
  have hcont : ContinuousOn ψ (Set.Icc a b) := by
    refine ContinuousOn.mul (fun x hx => (hD x (hIcc hx)).continuousAt.continuousWithinAt) ?_
    exact Complex.continuous_exp.comp_continuousOn hFcont.neg
  have hderiv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt ψ 0 (Set.Ici x) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := Set.Ico_subset_Icc_self hx
    have hIoo : Set.Icc a b ∈ nhdsWithin x (Set.Ioi x) :=
      Filter.mem_of_superset (Ioo_mem_nhdsGT hx.2) (Set.Ioo_subset_Icc_self.trans
        (Set.Icc_subset_Icc hx.1 le_rfl))
    have hFd : HasDerivWithinAt F (τ x) (Set.Ici x) x := by
      refine intervalIntegral.integral_hasDerivWithinAt_right
        (hτ.mono (by rw [Set.uIcc_of_le hx.1]; exact Set.Icc_subset_Icc le_rfl hx.2.le)
          |>.intervalIntegrable) ?_ ((hτ x hxIcc).mono_of_mem_nhdsWithin hIoo)
      have hsub : Set.Ioo x b ⊆ Set.Icc a b :=
        Set.Ioo_subset_Icc_self.trans (Set.Icc_subset_Icc hx.1 le_rfl)
      have hm := (hτ.mono hsub).stronglyMeasurableAtFilter_nhdsWithin
        (μ := MeasureTheory.volume) measurableSet_Ioo x
      rwa [nhdsWithin_Ioo_eq_nhdsGT hx.2] at hm
    have hE : HasDerivWithinAt (fun s => Complex.exp (-F s)) (Complex.exp (-F x) * -τ x)
        (Set.Ici x) x :=
      (Complex.hasDerivAt_exp (-F x)).comp_hasDerivWithinAt x hFd.neg
    have hP := (hD x (hIcc hxIcc)).hasDerivWithinAt.mul hE
    refine hP.congr_deriv ?_
    ring
  have hψ := constant_of_has_deriv_right_zero hcont hderiv b ⟨hab, le_rfl⟩
  simp only [ψ, F, intervalIntegral.integral_same, neg_zero, Complex.exp_zero, mul_one] at hψ
  rw [← hψ, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

end Jacobi

end

end GaloisForLFunctions.HTGeometry
