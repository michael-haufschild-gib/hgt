import GaloisForLFunctions.HTGeometry.ObserverCriticalCarrierConfinementLaw

/-!
# Analytic finite-rank loci

For a globally analytic map from a finite Euclidean space, a derivative whose
range has dimension at least `k` at one point forces the derivative-rank-`< k`
locus to have Lebesgue measure zero.  The proof constructs a finite-dimensional
linear observer from an independent subfamily of the derivative range and
applies the analytic observer-minor nullity law.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Postcomposition cannot increase the dimension of a finite derivative range. -/
theorem finrank_range_comp_left_le
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (A : X →L[ℝ] Y) (C : Y →L[ℝ] Z) :
    Module.finrank ℝ (C.comp A).range ≤ Module.finrank ℝ A.range := by
  let g : A.range →ₗ[ℝ] Z := C.toLinearMap.domRestrict A.range
  have hrange : (C.comp A).toLinearMap.range = g.range := by
    ext z
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨⟨A x, ⟨x, rfl⟩⟩, hx⟩
    · rintro ⟨x, hx⟩
      rcases x with ⟨x, ⟨w, hw⟩⟩
      change C x = z at hx
      rw [← hw] at hx
      exact ⟨w, hx⟩
  rw [show (C.comp A).range = (C.comp A).toLinearMap.range by rfl, hrange]
  exact LinearMap.finrank_range_le g

/-- Precomposition by a surjective finite coordinate map preserves every
postcomposed range dimension. -/
theorem finrank_range_comp_right_ge_of_surjective
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (A : X →L[ℝ] Y) (C : Y →L[ℝ] Z)
    (hA : Function.Surjective A) :
    Module.finrank ℝ C.range ≤ Module.finrank ℝ (C.comp A).range := by
  have hrange : C.range ≤ (C.comp A).range := by
    rintro y ⟨x, hx⟩
    obtain ⟨w, hw⟩ := hA x
    refine ⟨w, ?_⟩
    change C (A w) = y
    rw [hw]
    exact hx
  exact LinearMap.finrank_le_finrank_of_injective
    (f := Submodule.inclusion hrange) (Submodule.inclusion_injective hrange)

/-- A globally analytic finite-dimensional map with a rank-`k` derivative at
the origin has a volume-null rank-deficient locus. -/
theorem analytic_lowRank_fderiv_volume_zero
    {m k : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : EuclideanSpace ℝ (Fin m) → V)
    (hF : AnalyticOnNhd ℝ F Set.univ)
    (hrank : k ≤ Module.finrank ℝ (fderiv ℝ F 0).range) :
    volume {x | Module.finrank ℝ (fderiv ℝ F x).range < k} = 0 := by
  let D := fderiv ℝ F 0
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank
    (show k ≤ Module.finrank ℝ D.range by exact hrank)
  choose u hu using fun i => (v i).property
  let M : (Fin k → ℝ) →L[ℝ] V :=
    (Fintype.linearCombination ℝ fun i => (v i : V)).toContinuousLinearMap
  have hv' : LinearIndependent ℝ (fun i => (v i : V)) := by
    simpa [Function.comp_def] using hv.map' D.range.subtype
      (LinearMap.ker_eq_bot_of_injective (Submodule.subtype_injective _))
  have hMinj : Function.Injective M := by
    exact hv'.fintypeLinearCombination_injective
  let L : V →L[ℝ] (Fin k → ℝ) := M.toLinearMap.leftInverse.toContinuousLinearMap
  let e : (Fin k → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    (EuclideanSpace.equiv (Fin k) ℝ).symm.toContinuousLinearMap
  let O : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k) :=
    fun x => e (L (F x))
  have hO : AnalyticOnNhd ℝ O Set.univ := by
    intro x _
    have hLF : AnalyticAt ℝ (fun x => L (F x)) x :=
      (L.analyticAt (F x)).comp (hF x (Set.mem_univ x))
    simpa [O, Function.comp_def] using
      AnalyticAt.comp (f := fun y => L (F y)) (g := fun q => e q)
        (e.analyticAt (L (F x))) hLF
  have hD : HasFDerivAt F D 0 := by
    change HasFDerivAt F (fderiv ℝ F 0) 0
    exact (hF 0 (Set.mem_univ 0)).differentiableAt.hasFDerivAt
  have hOderiv : HasFDerivAt O (e.comp (L.comp D)) 0 := by
    have hLF : HasFDerivAt (fun x => L (F x)) (L.comp D) 0 :=
      HasFDerivAt.comp (f := F) (g := fun y => L y) 0 L.hasFDerivAt hD
    exact HasFDerivAt.comp (f := fun x => L (F x)) (g := fun y => e y) 0
      e.hasFDerivAt hLF
  have hLsingle (i : Fin k) : L (D (u i)) = Pi.single i 1 := by
    have hMsingle : M (Pi.single i 1) = (v i : V) := by
      simp [M, Fintype.linearCombination_apply]
    calc
      L (D (u i)) = L (v i : V) := congrArg L (hu i)
      _ = L (M (Pi.single i 1)) := congrArg L hMsingle.symm
      _ = Pi.single i 1 := by
        simpa [L] using LinearMap.leftInverse_apply_of_inj
          (LinearMap.ker_eq_bot_of_injective hMinj) (Pi.single i 1)
  have hminor : (observerMinor (fun x => fderiv ℝ O x) u 0).det ≠ 0 := by
    have hmatrix : observerMinor (fun x => fderiv ℝ O x) u 0 = 1 := by
      ext i j
      change (fderiv ℝ O 0) (u j) i = (1 : Matrix (Fin k) (Fin k) ℝ) i j
      rw [hOderiv.fderiv]
      change e (L (D (u j))) i = (1 : Matrix (Fin k) (Fin k) ℝ) i j
      rw [hLsingle j]
      by_cases hij : i = j
      · subst i
        simp [e]
      · simp [e, hij]
    rw [hmatrix, Matrix.det_one]
    exact one_ne_zero
  have hcritical : volume {x | ¬ Function.Surjective (fderiv ℝ O x)} = 0 :=
    analytic_observer_criticalSet_volume_zero hO u hminor
  apply measure_mono_null (t := {x | ¬ Function.Surjective (fderiv ℝ O x)})
  · intro x hx hsurj
    have htop : (fderiv ℝ O x).range = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    have hOD : fderiv ℝ O x =
        e.comp (L.comp (fderiv ℝ F x)) := by
      have hFD : HasFDerivAt F (fderiv ℝ F x) x :=
        (hF x (Set.mem_univ x)).differentiableAt.hasFDerivAt
      have hLF : HasFDerivAt (fun y => L (F y))
          (L.comp (fderiv ℝ F x)) x :=
        HasFDerivAt.comp (f := F) (g := fun y => L y) x L.hasFDerivAt hFD
      exact (HasFDerivAt.comp (f := fun y => L (F y)) (g := fun y => e y) x
        e.hasFDerivAt hLF).fderiv
    have hle : Module.finrank ℝ (fderiv ℝ O x).range ≤
        Module.finrank ℝ (fderiv ℝ F x).range := by
      rw [hOD]
      exact finrank_range_comp_left_le (fderiv ℝ F x) (e.comp L)
    have hdim : k ≤ Module.finrank ℝ (fderiv ℝ F x).range := by
      calc
        k = Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) := by simp
        _ = Module.finrank ℝ (fderiv ℝ O x).range := by rw [htop, finrank_top]
        _ ≤ Module.finrank ℝ (fderiv ℝ F x).range := hle
    exact (not_lt_of_ge hdim) hx
  · exact hcritical

/-- A globally analytic finite-dimensional map whose derivative has rank at
least `k` at some point has a volume-null rank-deficient locus. -/
theorem analytic_lowRank_fderiv_volume_zero_of_exists
    {m k : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : EuclideanSpace ℝ (Fin m) → V)
    (hF : AnalyticOnNhd ℝ F Set.univ)
    (hrank : ∃ x, k ≤ Module.finrank ℝ (fderiv ℝ F x).range) :
    volume {x | Module.finrank ℝ (fderiv ℝ F x).range < k} = 0 := by
  obtain ⟨x0, hx0⟩ := hrank
  let H : EuclideanSpace ℝ (Fin m) → V := fun y => F (y + x0)
  have hH : AnalyticOnNhd ℝ H Set.univ := by
    intro y _
    change AnalyticAt ℝ (fun z => F (z + x0)) y
    exact AnalyticAt.comp (f := fun z => z + x0) (g := F)
      (hF (y + x0) (Set.mem_univ _))
      ((analyticAt_id (𝕜 := ℝ) (z := y)).add (analyticAt_const (v := x0)))
  have hTderiv (y : EuclideanSpace ℝ (Fin m)) :
      HasFDerivAt (fun z : EuclideanSpace ℝ (Fin m) => z + x0)
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))) y :=
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))).hasFDerivAt.add_const x0
  have hHderiv (y : EuclideanSpace ℝ (Fin m)) :
      fderiv ℝ H y = fderiv ℝ F (y + x0) := by
    have hFderiv : HasFDerivAt F (fderiv ℝ F (y + x0)) (y + x0) :=
      (hF (y + x0) (Set.mem_univ _)).differentiableAt.hasFDerivAt
    have hcomp := HasFDerivAt.comp
      (f := fun z : EuclideanSpace ℝ (Fin m) => z + x0) (g := F) y hFderiv (hTderiv y)
    change fderiv ℝ (F ∘ fun z => z + x0) y = _
    exact hcomp.fderiv
  have hHrank : k ≤ Module.finrank ℝ (fderiv ℝ H 0).range := by
    rw [hHderiv]
    have hxzero : (0 : EuclideanSpace ℝ (Fin m)) + x0 = x0 := zero_add _
    rw [hxzero]
    exact hx0
  have hHzero : volume {y | Module.finrank ℝ (fderiv ℝ H y).range < k} = 0 :=
    analytic_lowRank_fderiv_volume_zero H hH hHrank
  have hbad : {x | Module.finrank ℝ (fderiv ℝ F x).range < k} =
      (fun y : EuclideanSpace ℝ (Fin m) => y - x0) ⁻¹'
        {y | Module.finrank ℝ (fderiv ℝ H y).range < k} := by
    ext y
    change Module.finrank ℝ (fderiv ℝ F y).range < k ↔
      Module.finrank ℝ (fderiv ℝ H (y - x0)).range < k
    rw [hHderiv (y - x0)]
    have hy : y - x0 + x0 = y := sub_add_cancel y x0
    rw [hy]
  rw [hbad]
  exact (measurePreserving_add_right volume (-x0)).preimage_null hHzero

end

end GaloisForLFunctions.HTGeometry
