import GaloisForLFunctions.HTGeometry.ConformalMetricLowRegularity

/-!
# The d'Alembertian of a product with a flat factor

A chart on `Fin n → ℝ` is crossed with a flat factor of `k` further coordinates: the inverse metric
of the product is block diagonal, its first block the inverse metric of the factor read at the
projected point and its second block the identity, and the density is the density of the factor.

A field which is constant in the transverse directions is the pullback of a field on the factor
along the projection. For such a field the two constructions commute: the d'Alembertian of the
product chart is the d'Alembertian of the factor, read at the projected point. The transverse block
contributes nothing, because the metric has no mixed entries and the pullback has no transverse
derivative.

Only the regularity that the chart calculus consumes — differentiable partial derivatives on a
region — is used, and it transports to the pullback along the projection.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

/-! ## The projection onto the first block -/

section Front

variable (n k : ℕ)

/-- The projection of a point of the product onto the first block of coordinates. -/
def frontMap (y : Fin (n + k) → ℝ) : Fin n → ℝ := fun i => y (Fin.castAdd k i)

/-- The projection as a continuous linear map. -/
noncomputable def frontCLM : (Fin (n + k) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castAdd k i)

theorem frontCLM_coe : ⇑(frontCLM n k) = frontMap n k := rfl

theorem continuous_frontMap : Continuous (frontMap n k) := by
  rw [← frontCLM_coe]
  exact (frontCLM n k).continuous

theorem contDiff_frontMap : ContDiff ℝ ∞ (frontMap n k) := by
  rw [← frontCLM_coe]
  exact (frontCLM n k).contDiff

theorem hasFDerivAt_frontMap (y : Fin (n + k) → ℝ) :
    HasFDerivAt (frontMap n k) (frontCLM n k) y := by
  rw [← frontCLM_coe]
  exact (frontCLM n k).hasFDerivAt

theorem frontMap_apply (y : Fin (n + k) → ℝ) (i : Fin n) :
    frontMap n k y i = y (Fin.castAdd k i) := rfl

variable {n k}

/-- The projection sends the coordinate vector of a front direction to the corresponding coordinate
vector of the factor. -/
theorem frontCLM_single_castAdd (i : Fin n) :
    frontCLM n k (Pi.single (Fin.castAdd k i) (1 : ℝ)) = Pi.single i (1 : ℝ) := by
  funext j
  show (Pi.single (Fin.castAdd k i) (1 : ℝ) : Fin (n + k) → ℝ) (Fin.castAdd k j)
      = (Pi.single i (1 : ℝ) : Fin n → ℝ) j
  by_cases h : j = i
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · have hne : (Fin.castAdd k j : Fin (n + k)) ≠ Fin.castAdd k i := by
      intro hc
      exact h (Fin.ext (by simpa using congrArg Fin.val hc))
    rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne h]

/-- The projection kills the coordinate vectors of the transverse directions. -/
theorem frontCLM_single_natAdd (i : Fin k) :
    frontCLM n k (Pi.single (Fin.natAdd n i) (1 : ℝ)) = 0 := by
  funext j
  show (Pi.single (Fin.natAdd n i) (1 : ℝ) : Fin (n + k) → ℝ) (Fin.castAdd k j) = (0 : ℝ)
  have hne : (Fin.castAdd k j : Fin (n + k)) ≠ Fin.natAdd n i := by
    intro hc
    have hval := congrArg Fin.val hc
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
    have := j.isLt
    omega
  rw [Pi.single_eq_of_ne hne]

/-- **A front derivative of a pullback is the corresponding derivative of the factor.** -/
theorem coordPartial_comp_frontMap_castAdd {u : (Fin n → ℝ) → ℝ} {y : Fin (n + k) → ℝ}
    (hu : DifferentiableAt ℝ u (frontMap n k y)) (i : Fin n) :
    coordPartial (Fin.castAdd k i) (fun z => u (frontMap n k z)) y
      = coordPartial i u (frontMap n k y) := by
  have hcomp : HasFDerivAt (fun z => u (frontMap n k z))
      ((fderiv ℝ u (frontMap n k y)).comp (frontCLM n k)) y :=
    hu.hasFDerivAt.comp y (hasFDerivAt_frontMap n k y)
  rw [coordPartial, hcomp.fderiv]
  show fderiv ℝ u (frontMap n k y) (frontCLM n k (Pi.single (Fin.castAdd k i) (1 : ℝ)))
    = coordPartial i u (frontMap n k y)
  rw [frontCLM_single_castAdd]
  rfl

/-- **A pullback has no transverse derivative.** -/
theorem coordPartial_comp_frontMap_natAdd {u : (Fin n → ℝ) → ℝ} {y : Fin (n + k) → ℝ}
    (hu : DifferentiableAt ℝ u (frontMap n k y)) (i : Fin k) :
    coordPartial (Fin.natAdd n i) (fun z => u (frontMap n k z)) y = 0 := by
  have hcomp : HasFDerivAt (fun z => u (frontMap n k z))
      ((fderiv ℝ u (frontMap n k y)).comp (frontCLM n k)) y :=
    hu.hasFDerivAt.comp y (hasFDerivAt_frontMap n k y)
  rw [coordPartial, hcomp.fderiv]
  show fderiv ℝ u (frontMap n k y) (frontCLM n k (Pi.single (Fin.natAdd n i) (1 : ℝ))) = 0
  rw [frontCLM_single_natAdd, map_zero]

theorem differentiableAt_comp_frontMap {u : (Fin n → ℝ) → ℝ} {y : Fin (n + k) → ℝ}
    (hu : DifferentiableAt ℝ u (frontMap n k y)) :
    DifferentiableAt ℝ (fun z => u (frontMap n k z)) y :=
  (hu.hasFDerivAt.comp y (hasFDerivAt_frontMap n k y)).differentiableAt

end Front

namespace SmoothMetricChart

/-! ## The product chart -/

section Prod

variable {n : ℕ} (M : SmoothMetricChart n) (k : ℕ)

/-- The block diagonal inverse metric of the product of a chart with a flat factor. -/
noncomputable def prodFlatInverse (y : Fin (n + k) → ℝ) :
    Matrix (Fin (n + k)) (Fin (n + k)) ℝ :=
  Matrix.of fun a b =>
    Fin.addCases (motive := fun _ => ℝ)
      (fun i => Fin.addCases (motive := fun _ => ℝ)
        (fun j => M.inverseMetric (frontMap n k y) i j) (fun _ => (0 : ℝ)) b)
      (fun i => Fin.addCases (motive := fun _ => ℝ)
        (fun _ => (0 : ℝ)) (fun j => if i = j then (1 : ℝ) else 0) b) a

@[simp] theorem prodFlatInverse_castAdd_castAdd (y : Fin (n + k) → ℝ) (i j : Fin n) :
    M.prodFlatInverse k y (Fin.castAdd k i) (Fin.castAdd k j)
      = M.inverseMetric (frontMap n k y) i j := by
  simp [prodFlatInverse]

@[simp] theorem prodFlatInverse_castAdd_natAdd (y : Fin (n + k) → ℝ) (i : Fin n) (j : Fin k) :
    M.prodFlatInverse k y (Fin.castAdd k i) (Fin.natAdd n j) = 0 := by
  simp [prodFlatInverse]

@[simp] theorem prodFlatInverse_natAdd_castAdd (y : Fin (n + k) → ℝ) (i : Fin k) (j : Fin n) :
    M.prodFlatInverse k y (Fin.natAdd n i) (Fin.castAdd k j) = 0 := by
  simp [prodFlatInverse]

@[simp] theorem prodFlatInverse_natAdd_natAdd (y : Fin (n + k) → ℝ) (i j : Fin k) :
    M.prodFlatInverse k y (Fin.natAdd n i) (Fin.natAdd n j) = if i = j then (1 : ℝ) else 0 := by
  simp [prodFlatInverse]

/-- **The product of a chart with a flat factor.** -/
noncomputable def prodFlat : SmoothMetricChart (n + k) where
  inverseMetric := M.prodFlatInverse k
  density := fun y => M.density (frontMap n k y)
  contDiff_inverseMetric := by
    intro a b
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left j =>
        have h : (fun y => M.prodFlatInverse k y (Fin.castAdd k i) (Fin.castAdd k j))
            = fun y => M.inverseMetric (frontMap n k y) i j := by
          funext y
          exact M.prodFlatInverse_castAdd_castAdd k y i j
        rw [h]
        exact (M.contDiff_inverseMetric i j).comp (contDiff_frontMap n k)
      | right j =>
        have h : (fun y => M.prodFlatInverse k y (Fin.castAdd k i) (Fin.natAdd n j))
            = fun _ => (0 : ℝ) := by
          funext y
          exact M.prodFlatInverse_castAdd_natAdd k y i j
        rw [h]
        exact contDiff_const
    | right i =>
      induction b using Fin.addCases with
      | left j =>
        have h : (fun y => M.prodFlatInverse k y (Fin.natAdd n i) (Fin.castAdd k j))
            = fun _ => (0 : ℝ) := by
          funext y
          exact M.prodFlatInverse_natAdd_castAdd k y i j
        rw [h]
        exact contDiff_const
      | right j =>
        have h : (fun y => M.prodFlatInverse k y (Fin.natAdd n i) (Fin.natAdd n j))
            = fun _ => if i = j then (1 : ℝ) else 0 := by
          funext y
          exact M.prodFlatInverse_natAdd_natAdd k y i j
        rw [h]
        exact contDiff_const
  contDiff_density := M.contDiff_density.comp (contDiff_frontMap n k)
  density_pos := fun y => M.density_pos _
  inverseMetric_symm := by
    intro y a b
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left j =>
        rw [M.prodFlatInverse_castAdd_castAdd, M.prodFlatInverse_castAdd_castAdd,
          M.inverseMetric_symm]
      | right j =>
        rw [M.prodFlatInverse_castAdd_natAdd, M.prodFlatInverse_natAdd_castAdd]
    | right i =>
      induction b using Fin.addCases with
      | left j =>
        rw [M.prodFlatInverse_natAdd_castAdd, M.prodFlatInverse_castAdd_natAdd]
      | right j =>
        rw [M.prodFlatInverse_natAdd_natAdd, M.prodFlatInverse_natAdd_natAdd]
        by_cases h : i = j
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (Ne.symm h)]

@[simp] theorem prodFlat_inverseMetric (y : Fin (n + k) → ℝ) :
    (M.prodFlat k).inverseMetric y = M.prodFlatInverse k y := rfl

@[simp] theorem prodFlat_density (y : Fin (n + k) → ℝ) :
    (M.prodFlat k).density y = M.density (frontMap n k y) := rfl

/-! ## Regularity of a pullback -/

/-- **The pullback of a regular field along the projection is regular on the tube.** -/
theorem differentiablePartialsOn_comp_frontMap {u : (Fin n → ℝ) → ℝ} {W : Set (Fin n → ℝ)}
    (hW : IsOpen W) (hu : DifferentiablePartialsOn u W) :
    DifferentiablePartialsOn (fun z => u (frontMap n k z)) (frontMap n k ⁻¹' W) where
  base := fun x hx => differentiableAt_comp_frontMap (hu.base _ hx)
  coord := by
    have hpre : IsOpen (frontMap n k ⁻¹' W) := hW.preimage (continuous_frontMap n k)
    intro a x hx
    induction a using Fin.addCases with
    | left i =>
      have hev : coordPartial (Fin.castAdd k i) (fun z => u (frontMap n k z)) =ᶠ[nhds x]
          fun z => coordPartial i u (frontMap n k z) :=
        Filter.eventuallyEq_of_mem (hpre.mem_nhds hx) fun z hz =>
          coordPartial_comp_frontMap_castAdd (hu.base _ hz) i
      rw [hev.differentiableAt_iff]
      exact differentiableAt_comp_frontMap (hu.coord i _ hx)
    | right i =>
      have hev : coordPartial (Fin.natAdd n i) (fun z => u (frontMap n k z)) =ᶠ[nhds x]
          fun _ => (0 : ℝ) :=
        Filter.eventuallyEq_of_mem (hpre.mem_nhds hx) fun z hz =>
          coordPartial_comp_frontMap_natAdd (hu.base _ hz) i
      rw [hev.differentiableAt_iff]
      exact differentiableAt_const 0

/-! ## The flux and the d'Alembertian of a pullback -/

/-- **The flux of the product chart in a front direction is the flux of the factor.** -/
theorem prodFlat_flux_castAdd {u : (Fin n → ℝ) → ℝ} {y : Fin (n + k) → ℝ}
    (hu : DifferentiableAt ℝ u (frontMap n k y)) (i : Fin n) :
    (M.prodFlat k).flux (fun z => u (frontMap n k z)) (Fin.castAdd k i) y
      = M.flux u i (frontMap n k y) := by
  rw [flux, flux, prodFlat_density, Fin.sum_univ_add]
  have h1 : ∀ j : Fin n,
      (M.prodFlat k).inverseMetric y (Fin.castAdd k i) (Fin.castAdd k j)
          * coordPartial (Fin.castAdd k j) (fun z => u (frontMap n k z)) y
        = M.inverseMetric (frontMap n k y) i j * coordPartial j u (frontMap n k y) := by
    intro j
    rw [prodFlat_inverseMetric, M.prodFlatInverse_castAdd_castAdd,
      coordPartial_comp_frontMap_castAdd hu j]
  have h2 : ∀ j : Fin k,
      (M.prodFlat k).inverseMetric y (Fin.castAdd k i) (Fin.natAdd n j)
          * coordPartial (Fin.natAdd n j) (fun z => u (frontMap n k z)) y = 0 := by
    intro j
    rw [prodFlat_inverseMetric, M.prodFlatInverse_castAdd_natAdd, zero_mul]
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_congr rfl fun j _ => h2 j,
    Finset.sum_const_zero, add_zero]

/-- **The flux of the product chart in a transverse direction vanishes on a pullback.** -/
theorem prodFlat_flux_natAdd {u : (Fin n → ℝ) → ℝ} {y : Fin (n + k) → ℝ}
    (hu : DifferentiableAt ℝ u (frontMap n k y)) (i : Fin k) :
    (M.prodFlat k).flux (fun z => u (frontMap n k z)) (Fin.natAdd n i) y = 0 := by
  rw [flux, Fin.sum_univ_add]
  have h1 : ∀ j : Fin n,
      (M.prodFlat k).inverseMetric y (Fin.natAdd n i) (Fin.castAdd k j)
          * coordPartial (Fin.castAdd k j) (fun z => u (frontMap n k z)) y = 0 := by
    intro j
    rw [prodFlat_inverseMetric, M.prodFlatInverse_natAdd_castAdd, zero_mul]
  have h2 : ∀ j : Fin k,
      (M.prodFlat k).inverseMetric y (Fin.natAdd n i) (Fin.natAdd n j)
          * coordPartial (Fin.natAdd n j) (fun z => u (frontMap n k z)) y = 0 := by
    intro j
    rw [coordPartial_comp_frontMap_natAdd hu j, mul_zero]
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_congr rfl fun j _ => h2 j,
    Finset.sum_const_zero, Finset.sum_const_zero, add_zero, mul_zero]

/-- **The d'Alembertian of the product chart on a pullback is the d'Alembertian of the factor.**

The transverse block of the metric is diagonal and the pullback is constant in those directions, so
the transverse fluxes vanish identically near the point; the front fluxes are the fluxes of the
factor, pulled back. -/
theorem prodFlat_dalembert_comp_front {u : (Fin n → ℝ) → ℝ} {W : Set (Fin n → ℝ)}
    (hW : IsOpen W) (hu : DifferentiablePartialsOn u W) {y : Fin (n + k) → ℝ}
    (hy : frontMap n k y ∈ W) :
    (M.prodFlat k).dalembert (fun z => u (frontMap n k z)) y = M.dalembert u (frontMap n k y) := by
  have hpre : IsOpen (frontMap n k ⁻¹' W) := hW.preimage (continuous_frontMap n k)
  have hmem : y ∈ frontMap n k ⁻¹' W := hy
  have hfront : ∀ i : Fin n,
      coordPartial (Fin.castAdd k i)
          ((M.prodFlat k).flux (fun z => u (frontMap n k z)) (Fin.castAdd k i)) y
        = coordPartial i (M.flux u i) (frontMap n k y) := by
    intro i
    have hev : (M.prodFlat k).flux (fun z => u (frontMap n k z)) (Fin.castAdd k i) =ᶠ[nhds y]
        fun z => M.flux u i (frontMap n k z) :=
      Filter.eventuallyEq_of_mem (hpre.mem_nhds hmem) fun z hz =>
        M.prodFlat_flux_castAdd k (hu.base _ hz) i
    rw [coordPartial_congr hev (Fin.castAdd k i),
      coordPartial_comp_frontMap_castAdd (M.differentiableAt_flux_on hu i hy) i]
  have htrans : ∀ i : Fin k,
      coordPartial (Fin.natAdd n i)
          ((M.prodFlat k).flux (fun z => u (frontMap n k z)) (Fin.natAdd n i)) y = 0 := by
    intro i
    have hev : (M.prodFlat k).flux (fun z => u (frontMap n k z)) (Fin.natAdd n i) =ᶠ[nhds y]
        fun _ => (0 : ℝ) :=
      Filter.eventuallyEq_of_mem (hpre.mem_nhds hmem) fun z hz =>
        M.prodFlat_flux_natAdd k (hu.base _ hz) i
    rw [coordPartial_congr hev (Fin.natAdd n i), coordPartial_const]
  rw [dalembert, dalembert, prodFlat_density, Fin.sum_univ_add,
    Finset.sum_congr rfl fun i _ => hfront i, Finset.sum_congr rfl fun i _ => htrans i,
    Finset.sum_const_zero, add_zero]

end Prod

end SmoothMetricChart

end GaloisForLFunctions.HTGeometry
