import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

/-!
# Analytic eigenvalue branches at any simple base point

The corpus's universal branch theorem produces analytic characteristic-root branches for an analytic
matrix family whose base value is *diagonal* with distinct entries.  Conjugation invariance of the
characteristic relation removes that normal form: a base value which is merely diagonalizable with
distinct eigenvalues carries the same branches, because conjugating the whole family by the fixed
diagonalizing matrix changes neither analyticity nor characteristic roots.

Together with a finite intersection of neighbourhoods this gives, at every simple base point, one
neighbourhood carrying an analytic branch through each eigenvalue simultaneously.
-/

open Filter Topology Complex ContinuousLinearMap Set
open scoped BigOperators Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The characteristic relation is invariant under conjugation. -/
theorem matrixCharpolyRelation_conj {S : Matrix ι ι ℂ} (hS : IsUnit S.det) (H : Matrix ι ι ℂ)
    (w : ℂ) :
    matrixCharpolyRelation (S⁻¹ * H * S, w) = matrixCharpolyRelation (H, w) := by
  have hSinv : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hS
  have hconj : Matrix.scalar ι w - S⁻¹ * H * S
      = S⁻¹ * (Matrix.scalar ι w - H) * S := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    have hscal : (Matrix.scalar ι) w = w • (1 : Matrix ι ι ℂ) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    rw [hscal, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hSinv]
  rw [matrixCharpolyRelation, matrixCharpolyRelation, hconj, Matrix.det_mul, Matrix.det_mul]
  have hdet : S⁻¹.det * (Matrix.scalar ι w - H).det * S.det
      = (S⁻¹.det * S.det) * (Matrix.scalar ι w - H).det := by ring
  rw [hdet, ← Matrix.det_mul, hSinv, Matrix.det_one, one_mul]

/-- Conjugating an analytic matrix family by a fixed matrix keeps it analytic. -/
theorem analyticAt_conj_matrixFamily {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {H : P → Matrix ι ι ℂ} {p₀ : P} (hH : AnalyticAt ℂ H p₀) (S : Matrix ι ι ℂ) :
    AnalyticAt ℂ (fun p => S⁻¹ * H p * S) p₀ := by
  let conjMap : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
    { toFun := fun M => S⁻¹ * M * S
      map_add' := by
        intro M N
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c M
        simp }
  have hleft : AnalyticAt ℂ (fun M : Matrix ι ι ℂ => S⁻¹ * M * S) (H p₀) := by
    have hana : AnalyticAt ℂ
        (fun M : Matrix ι ι ℂ => conjMap.toContinuousLinearMap M) (H p₀) :=
      (conjMap.toContinuousLinearMap).analyticAt _
    simpa [conjMap] using hana
  exact hleft.comp hH

/-- **Analytic eigenvalue branch at a simple base point.**  If the base value of an analytic matrix
family is diagonalizable with distinct eigenvalues, every eigenvalue continues analytically. -/
theorem analyticMatrixFamily_eigenvalueBranch_of_conj {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℂ P] {H : P → Matrix ι ι ℂ} {p₀ : P} (hH : AnalyticAt ℂ H p₀)
    (energy : ι → ℂ) (hinj : Function.Injective energy) {S : Matrix ι ι ℂ} (hS : IsUnit S.det)
    (hbase : S⁻¹ * H p₀ * S = Matrix.diagonal energy) (x : ι) :
    ∃ branch : P → ℂ,
      AnalyticAt ℂ branch p₀ ∧ branch p₀ = energy x ∧
      (∀ᶠ p in 𝓝 p₀, matrixCharpolyRelation (H p, branch p) = 0) := by
  obtain ⟨branch, hbranchA, hbranch0, hbranchRoot⟩ :=
    analyticMatrixFamily_eigenvalueBranch (analyticAt_conj_matrixFamily hH S) energy hinj hbase x
  refine ⟨branch, hbranchA, hbranch0, ?_⟩
  filter_upwards [hbranchRoot] with p hp
  rwa [matrixCharpolyRelation_conj hS] at hp

/-- **Simultaneous analytic branches.**  At a simple base point one neighbourhood carries an
analytic branch through every eigenvalue at once. -/
theorem exists_simultaneous_eigenvalueBranches {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℂ P] {H : P → Matrix ι ι ℂ} {p₀ : P} (hH : AnalyticAt ℂ H p₀)
    (energy : ι → ℂ) (hinj : Function.Injective energy) {S : Matrix ι ι ℂ} (hS : IsUnit S.det)
    (hbase : S⁻¹ * H p₀ * S = Matrix.diagonal energy) :
    ∃ (U : Set P) (branch : ι → P → ℂ),
      IsOpen U ∧ p₀ ∈ U ∧ (∀ x, AnalyticOnNhd ℂ (branch x) U) ∧
      (∀ x, branch x p₀ = energy x) ∧
      (∀ x, ∀ᶠ p in 𝓝 p₀, matrixCharpolyRelation (H p, branch x p) = 0) := by
  classical
  choose branch hbranchA hbranch0 hbranchRoot using fun x =>
    analyticMatrixFamily_eigenvalueBranch_of_conj hH energy hinj hS hbase x
  -- each branch is analytic on some open neighbourhood; intersect the finitely many of them
  have hopen : ∀ x : ι, ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧ AnalyticOnNhd ℂ (branch x) V := by
    intro x
    obtain ⟨V, hVmem, hVanalytic⟩ := (hbranchA x).exists_mem_nhds_analyticOnNhd
    obtain ⟨W, hWV, hWopen, hWmem⟩ := mem_nhds_iff.mp hVmem
    exact ⟨W, hWopen, hWmem, hVanalytic.mono hWV⟩
  choose V hVopen hVmem hVanalytic using hopen
  refine ⟨⋂ x : ι, V x, branch, isOpen_iInter_of_finite hVopen, Set.mem_iInter.mpr hVmem,
    fun x => (hVanalytic x).mono (Set.iInter_subset _ x), hbranch0, hbranchRoot⟩


/-- Conjugating a continuous matrix family by a fixed matrix keeps it continuous. -/
theorem continuousAt_conj_matrixFamily {P : Type*} [TopologicalSpace P]
    {H : P → Matrix ι ι ℂ} {p₀ : P} (hH : ContinuousAt H p₀) (S : Matrix ι ι ℂ) :
    ContinuousAt (fun p => S⁻¹ * H p * S) p₀ := by
  let conjMap : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
    { toFun := fun M => S⁻¹ * M * S
      map_add' := by
        intro M N
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c M
        simp }
  have hcont : Continuous fun M : Matrix ι ι ℂ => S⁻¹ * M * S := by
    have h := (conjMap.toContinuousLinearMap).continuous
    simpa [conjMap] using h
  exact hcont.continuousAt.comp hH

/-- **Root germs are unique at a simple base value.**  Two continuous characteristic roots through
the same simple eigenvalue of a diagonalizable base agree near the base. -/
theorem simpleMatrix_root_germs_unique_of_conj {P : Type*} [TopologicalSpace P]
    (energy : ι → ℂ) (hinj : Function.Injective energy) (x : ι)
    {p₀ : P} {H : P → Matrix ι ι ℂ} {s t : P → ℂ} {S : Matrix ι ι ℂ} (hS : IsUnit S.det)
    (hbase : S⁻¹ * H p₀ * S = Matrix.diagonal energy) (hH : ContinuousAt H p₀)
    (hs : Filter.Tendsto s (𝓝 p₀) (𝓝 (energy x)))
    (ht : Filter.Tendsto t (𝓝 p₀) (𝓝 (energy x)))
    (hsroot : ∀ᶠ p in 𝓝 p₀, matrixCharpolyRelation (H p, s p) = 0)
    (htroot : ∀ᶠ p in 𝓝 p₀, matrixCharpolyRelation (H p, t p) = 0) :
    s =ᶠ[𝓝 p₀] t := by
  have hK : Filter.Tendsto (fun p => S⁻¹ * H p * S) (𝓝 p₀) (𝓝 (Matrix.diagonal energy)) := by
    have hcont := continuousAt_conj_matrixFamily hH S
    change Filter.Tendsto (fun p => S⁻¹ * H p * S) (𝓝 p₀) (𝓝 (S⁻¹ * H p₀ * S)) at hcont
    rwa [hbase] at hcont
  refine simpleDiagonalMatrix_root_germs_unique energy hinj x hK hs ht ?_ ?_
  · filter_upwards [hsroot] with p hp
    rwa [matrixCharpolyRelation_conj hS]
  · filter_upwards [htroot] with p hp
    rwa [matrixCharpolyRelation_conj hS]

/-- **Branch identification.**  An explicitly given continuous root path through a simple base value
agrees near the base with the analytic branch through that value, so explicit spectra may be
substituted for the abstract branches. -/
theorem eventuallyEq_branch_of_root_path {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {H : P → Matrix ι ι ℂ} {p₀ : P} (hH : AnalyticAt ℂ H p₀)
    (energy : ι → ℂ) (hinj : Function.Injective energy) {S : Matrix ι ι ℂ} (hS : IsUnit S.det)
    (hbase : S⁻¹ * H p₀ * S = Matrix.diagonal energy) (x : ι)
    {branch : P → ℂ} (hbranchA : AnalyticAt ℂ branch p₀) (hbranch0 : branch p₀ = energy x)
    (hbranchRoot : ∀ᶠ p in 𝓝 p₀, matrixCharpolyRelation (H p, branch p) = 0)
    {r : P → ℂ} (hr : ContinuousAt r p₀) (hr0 : r p₀ = energy x)
    (hrroot : ∀ᶠ p in 𝓝 p₀, matrixCharpolyRelation (H p, r p) = 0) :
    r =ᶠ[𝓝 p₀] branch := by
  refine simpleMatrix_root_germs_unique_of_conj energy hinj x hS hbase hH.continuousAt ?_ ?_
    hrroot hbranchRoot
  · have := hr
    rwa [ContinuousAt, hr0] at this
  · have := hbranchA.continuousAt
    rwa [ContinuousAt, hbranch0] at this

end

end GaloisForLFunctions.HTGeometry
