import GaloisForLFunctions.HTGeometry.ConstraintRelativity.ConormalPersistence
import GaloisForLFunctions.HTGeometry.ConstraintLaplacian
import GaloisForLFunctions.HTGeometry.ConstitutivePrimitiveFormationProperness
import GaloisForLFunctions.HTGeometry.ConstitutiveCyclicProcessFourShadow
import GaloisForLFunctions.HTGeometry.GramDeterminantDistance
import GaloisForLFunctions.HTGeometry.SeparatedNodeProducts

open Metric

namespace GaloisForLFunctions.HTGeometry

open HTGeometry.ConstraintRelativity

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Squared least formation work relative to a closed Hilbert subspace. -/
def conjugateFormationWork (L : Submodule ℂ H) (x : H) : ℝ :=
  quotientDistance L x ^ 2

/-- A normalized reporter annihilates the formation subspace and reads the target as one. -/
def IsNormalizedFormationReporter (L : Submodule ℂ H) (x : H)
    (φ : StrongDual ℂ H) : Prop :=
  φ ∈ conormal L ∧ φ x = 1

/-- Squared norms attained by normalized reporters. -/
def normalizedReporterNormSqSet (L : Submodule ℂ H) (x : H) : Set ℝ :=
  {r | ∃ φ : StrongDual ℂ H,
    IsNormalizedFormationReporter L x φ ∧ ‖φ‖ ^ 2 = r}

/-- Least normalized reporter capacity. -/
def conjugateReporterCapacity (L : Submodule ℂ H) (x : H) : ℝ :=
  sInf (normalizedReporterNormSqSet L x)

/-- Orthogonal innovation outside the formation subspace. -/
def formationResidual (L : Submodule ℂ H) [L.HasOrthogonalProjection] (x : H) : H :=
  x - L.starProjection x

omit [CompleteSpace H] in
theorem formationResidual_ne_zero {L : Submodule ℂ H} [L.HasOrthogonalProjection]
    {x : H} (hx : x ∉ L) :
    formationResidual L x ≠ 0 := by
  intro hzero
  apply hx
  apply Submodule.starProjection_eq_self_iff.mp
  exact (sub_eq_zero.mp hzero).symm

/-- Riesz reporter of the orthogonal formation innovation. -/
def canonicalFormationReporter (L : Submodule ℂ H) [L.HasOrthogonalProjection]
    (x : H) : StrongDual ℂ H :=
  ((‖formationResidual L x‖ ^ 2 : ℝ) : ℂ)⁻¹ •
    (InnerProductSpace.toDual ℂ H) (formationResidual L x)

omit [CompleteSpace H] in
theorem inner_formationResidual_target (L : Submodule ℂ H) [L.HasOrthogonalProjection]
    (x : H) :
    inner ℂ (formationResidual L x) x =
      ((‖formationResidual L x‖ ^ 2 : ℝ) : ℂ) := by
  let q := formationResidual L x
  have hq : q ∈ Lᗮ := L.sub_starProjection_mem_orthogonal x
  have horth : inner ℂ q (L.starProjection x) = 0 :=
    (L.mem_orthogonal' q).mp hq _ (L.starProjection_apply_mem x)
  calc
    inner ℂ q x = inner ℂ q (L.starProjection x + q) := by
      congr 1
      simp [q, formationResidual]
    _ = ((‖q‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_add_right, horth, zero_add, inner_self_eq_norm_sq_to_K]
      norm_cast

theorem canonicalFormationReporter_apply_target {L : Submodule ℂ H}
    [L.HasOrthogonalProjection] {x : H}
    (hx : x ∉ L) :
    canonicalFormationReporter L x x = 1 := by
  rw [canonicalFormationReporter, smul_apply,
    InnerProductSpace.toDual_apply_apply, inner_formationResidual_target]
  have hq := formationResidual_ne_zero hx
  have hnorm : ‖formationResidual L x‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hq)
  exact inv_mul_cancel₀ (by exact_mod_cast hnorm)

theorem canonicalFormationReporter_mem_conormal (L : Submodule ℂ H)
    [L.HasOrthogonalProjection] (x : H) :
    canonicalFormationReporter L x ∈ conormal L := by
  intro y hy
  rw [canonicalFormationReporter, smul_apply,
    InnerProductSpace.toDual_apply_apply]
  have hq : formationResidual L x ∈ Lᗮ :=
    L.sub_starProjection_mem_orthogonal x
  rw [(L.mem_orthogonal' _).mp hq y hy]
  simp

theorem canonicalFormationReporter_isNormalized {L : Submodule ℂ H}
    [L.HasOrthogonalProjection] {x : H}
    (hx : x ∉ L) :
    IsNormalizedFormationReporter L x (canonicalFormationReporter L x) :=
  ⟨canonicalFormationReporter_mem_conormal L x,
    canonicalFormationReporter_apply_target hx⟩

theorem norm_sq_canonicalFormationReporter {L : Submodule ℂ H}
    [L.HasOrthogonalProjection] {x : H}
    (hx : x ∉ L) :
    ‖canonicalFormationReporter L x‖ ^ 2 =
      (‖formationResidual L x‖ ^ 2)⁻¹ := by
  have hq := formationResidual_ne_zero hx
  have hnorm : 0 < ‖formationResidual L x‖ := norm_pos_iff.mpr hq
  rw [canonicalFormationReporter, norm_smul,
    LinearIsometryEquiv.norm_map]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_pow, abs_norm]
  field_simp

omit [CompleteSpace H] in
theorem normalizedReporter_norm_inv_le {L : Submodule ℂ H}
    [L.HasOrthogonalProjection] {x : H}
    (hx : x ∉ L) {φ : StrongDual ℂ H}
    (hφ : IsNormalizedFormationReporter L x φ) :
    ‖formationResidual L x‖⁻¹ ≤ ‖φ‖ := by
  have hq := formationResidual_ne_zero hx
  have hqpos : 0 < ‖formationResidual L x‖ := norm_pos_iff.mpr hq
  have hφq : φ (formationResidual L x) = 1 := by
    rw [formationResidual, map_sub, hφ.1 (L.starProjection x)
      (L.starProjection_apply_mem x), hφ.2, sub_zero]
  have hbound : 1 ≤ ‖φ‖ * ‖formationResidual L x‖ := calc
    1 = ‖φ (formationResidual L x)‖ := by rw [hφq]; norm_num
    _ ≤ ‖φ‖ * ‖formationResidual L x‖ := φ.le_opNorm _
  rw [inv_eq_one_div]
  exact (div_le_iff₀ hqpos).2 (by simpa [mul_comm] using hbound)

omit [CompleteSpace H] in
theorem normalizedReporter_inv_sq_le {L : Submodule ℂ H}
    [L.HasOrthogonalProjection] {x : H}
    (hx : x ∉ L) {φ : StrongDual ℂ H}
    (hφ : IsNormalizedFormationReporter L x φ) :
    (‖formationResidual L x‖ ^ 2)⁻¹ ≤ ‖φ‖ ^ 2 := by
  rw [← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _))
    (normalizedReporter_norm_inv_le hx hφ) 2

theorem conjugateReporterCapacity_eq {L : Submodule ℂ H}
    [L.HasOrthogonalProjection] {x : H}
    (hx : x ∉ L) :
    conjugateReporterCapacity L x = (‖formationResidual L x‖ ^ 2)⁻¹ := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro r ⟨φ, hφ, rfl⟩
      exact sq_nonneg ‖φ‖
    · exact ⟨canonicalFormationReporter L x,
        canonicalFormationReporter_isNormalized hx,
        norm_sq_canonicalFormationReporter hx⟩
  · apply le_csInf
    · exact ⟨_, canonicalFormationReporter L x,
        canonicalFormationReporter_isNormalized hx,
        norm_sq_canonicalFormationReporter hx⟩
    · rintro r ⟨φ, hφ, rfl⟩
      exact normalizedReporter_inv_sq_le hx hφ

/-- The canonical reporter is the unique normalized reporter attaining least capacity. -/
theorem canonicalFormationReporter_unique {L : Submodule ℂ H}
    [L.HasOrthogonalProjection] {x : H} (hx : x ∉ L)
    {φ : StrongDual ℂ H} (hφ : IsNormalizedFormationReporter L x φ)
    (hmin : ‖φ‖ ^ 2 = conjugateReporterCapacity L x) :
    φ = canonicalFormationReporter L x := by
  let q := formationResidual L x
  let g : H := (InnerProductSpace.toDual ℂ H).symm φ
  have hg_apply (y : H) : inner ℂ g y = φ y := by
    rw [← InnerProductSpace.toDual_apply_apply]
    change ((InnerProductSpace.toDual ℂ H)
      ((InnerProductSpace.toDual ℂ H).symm φ)) y = φ y
    rw [LinearIsometryEquiv.apply_symm_apply]
  have hφq : φ q = 1 := by
    change φ (x - L.starProjection x) = 1
    rw [map_sub,
      hφ.1 (L.starProjection x) (L.starProjection_apply_mem x),
      hφ.2, sub_zero]
  have hgq : inner ℂ g q = 1 := (hg_apply q).trans hφq
  have hgnorm : ‖g‖ = ‖φ‖ :=
    (InnerProductSpace.toDual ℂ H).symm.norm_map φ
  have hgnormsq : ‖g‖ ^ 2 = (‖q‖ ^ 2)⁻¹ := by
    rw [hgnorm, hmin, conjugateReporterCapacity_eq hx]
  let c : ℂ := ((‖q‖ ^ 2 : ℝ) : ℂ)⁻¹
  have hqne : q ≠ 0 := formationResidual_ne_zero hx
  have hqnormne : ‖q‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hqne)
  have hqnormpos : 0 < ‖q‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hqne)
  have hc : c = (((‖q‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    exact (Complex.ofReal_inv (‖q‖ ^ 2)).symm
  have hinvCastRe : RCLike.re ((((‖q‖ ^ 2 : ℝ) : ℂ))⁻¹) =
      (‖q‖ ^ 2)⁻¹ := by
    rw [← Complex.ofReal_inv]
    exact RCLike.ofReal_re _
  have hinvCastNorm : ‖((((‖q‖ ^ 2 : ℝ) : ℂ))⁻¹)‖ =
      (‖q‖ ^ 2)⁻¹ := by
    rw [← Complex.ofReal_inv]
    calc
      ‖(((‖q‖ ^ 2)⁻¹ : ℝ) : ℂ)‖ = ‖((‖q‖ ^ 2)⁻¹ : ℝ)‖ :=
        Complex.norm_real _
      _ = |(‖q‖ ^ 2)⁻¹| := Real.norm_eq_abs _
      _ = (‖q‖ ^ 2)⁻¹ := abs_of_pos (inv_pos.mpr hqnormpos)
  have hcastInvRe : RCLike.re (((‖q‖ ^ 2)⁻¹ : ℝ) : ℂ) =
      (‖q‖ ^ 2)⁻¹ := RCLike.ofReal_re _
  have hcastInvNorm : ‖(((‖q‖ ^ 2)⁻¹ : ℝ) : ℂ)‖ =
      (‖q‖ ^ 2)⁻¹ := by
    calc
      ‖(((‖q‖ ^ 2)⁻¹ : ℝ) : ℂ)‖ = ‖((‖q‖ ^ 2)⁻¹ : ℝ)‖ :=
        Complex.norm_real _
      _ = |(‖q‖ ^ 2)⁻¹| := Real.norm_eq_abs _
      _ = (‖q‖ ^ 2)⁻¹ := abs_of_pos (inv_pos.mpr hqnormpos)
  have hdist : ‖g - c • q‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, hgq, mul_one, norm_smul,
      hgnormsq, hc, hcastInvRe, hcastInvNorm]
    field_simp
    ring
  have hgc : g = c • q := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hdist))
  apply ContinuousLinearMap.ext
  intro y
  rw [← hg_apply y, hgc]
  simp [canonicalFormationReporter, c, q, RCLike.star_def, mul_comm]

omit [CompleteSpace H] in
theorem quotientDistance_eq_norm_formationResidual (L : Submodule ℂ H)
    [L.HasOrthogonalProjection] (x : H) :
    quotientDistance L x = ‖formationResidual L x‖ := by
  rw [quotientDistance, Metric.infDist_eq_iInf]
  change (⨅ y : L, dist x y) = ‖x - L.starProjection x‖
  rw [L.starProjection_minimal]
  exact iInf_congr fun u => by rw [dist_eq_norm]

/-- Exact formation-work/reporter-capacity reciprocity. -/
theorem conjugateFormationWork_mul_reporterCapacity {L : Submodule ℂ H}
    [L.HasOrthogonalProjection] {x : H}
    (hx : x ∉ L) :
    conjugateFormationWork L x * conjugateReporterCapacity L x = 1 := by
  rw [conjugateFormationWork, conjugateReporterCapacity_eq hx,
    quotientDistance_eq_norm_formationResidual]
  exact mul_inv_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr
    (formationResidual_ne_zero hx)))

/-- Distance to a continuous Hilbert hyperplane is value divided by reporter norm. -/
theorem quotientDistance_ker_continuousLinearMap
    (δ : StrongDual ℂ H) (hδ : δ ≠ 0) (x : H) :
    quotientDistance (LinearMap.ker (δ : H →ₗ[ℂ] ℂ)) x = ‖δ x‖ / ‖δ‖ := by
  have hδnorm : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  apply le_antisymm
  · rw [quotientDistance, Metric.infDist_eq_iInf]
    let g : H := (InnerProductSpace.toDual ℂ H).symm δ
    let a : ℂ := δ x / ((‖δ‖ ^ 2 : ℝ) : ℂ)
    let y : H := x - a • g
    have hg_apply (z : H) : inner ℂ g z = δ z := by
      rw [← InnerProductSpace.toDual_apply_apply]
      change ((InnerProductSpace.toDual ℂ H)
        ((InnerProductSpace.toDual ℂ H).symm δ)) z = δ z
      rw [LinearIsometryEquiv.apply_symm_apply]
    have hgnorm : ‖g‖ = ‖δ‖ :=
      (InnerProductSpace.toDual ℂ H).symm.norm_map δ
    have hδg : δ g = ((‖δ‖ ^ 2 : ℝ) : ℂ) := by
      rw [← hg_apply, inner_self_eq_norm_sq_to_K, hgnorm]
      norm_cast
    have hδnormsq : ((‖δ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (pow_ne_zero 2 hδnorm.ne')
    have hy : y ∈ LinearMap.ker (δ : H →ₗ[ℂ] ℂ) := by
      change δ (x - (δ x / ((‖δ‖ ^ 2 : ℝ) : ℂ)) • g) = 0
      rw [map_sub, map_smul, hδg]
      simp only [smul_eq_mul]
      field_simp
      ring
    have hbdd : BddBelow (Set.range
        (fun z : LinearMap.ker (δ : H →ₗ[ℂ] ℂ) => dist x (z : H))) := by
      refine ⟨(0 : ℝ), ?_⟩
      rintro _ ⟨z, rfl⟩
      exact dist_nonneg
    calc
      (⨅ z : LinearMap.ker (δ : H →ₗ[ℂ] ℂ), dist x z) ≤
          dist x (⟨y, hy⟩ : LinearMap.ker (δ : H →ₗ[ℂ] ℂ)) :=
        ciInf_le hbdd ⟨y, hy⟩
      _ = ‖a • g‖ := by simp [y]
      _ = ‖δ x‖ / ‖δ‖ := by
        change ‖(δ x / ((‖δ‖ ^ 2 : ℝ) : ℂ)) • g‖ = _
        rw [norm_smul, hgnorm, norm_div]
        have hcast : ‖(((‖δ‖ ^ 2 : ℝ) : ℂ))‖ = ‖δ‖ ^ 2 := by
          calc
            ‖(((‖δ‖ ^ 2 : ℝ) : ℂ))‖ = ‖(‖δ‖ ^ 2 : ℝ)‖ := Complex.norm_real _
            _ = |‖δ‖ ^ 2| := Real.norm_eq_abs _
            _ = ‖δ‖ ^ 2 := abs_of_pos (sq_pos_of_pos hδnorm)
        rw [hcast]
        field_simp
  · apply (le_infDist ⟨0, (LinearMap.ker (δ : H →ₗ[ℂ] ℂ)).zero_mem⟩).2
    intro y hy
    rw [dist_eq_norm]
    have hxy : δ x = δ (x - y) := by
      rw [map_sub, show δ y = 0 from hy, sub_zero]
    apply (div_le_iff₀ hδnorm).2
    rw [hxy]
    simpa [mul_comm] using δ.le_opNorm (x - y)

/-- Charged reporter form of exact work--capacity reciprocity. -/
theorem conjugateFormationWork_ker_mul_norm_sq
    (δ : StrongDual ℂ H) (hδ : δ ≠ 0) (x : H) :
    conjugateFormationWork (LinearMap.ker (δ : H →ₗ[ℂ] ℂ)) x * ‖δ‖ ^ 2 =
      ‖δ x‖ ^ 2 := by
  rw [conjugateFormationWork, quotientDistance_ker_continuousLinearMap δ hδ]
  have hδnorm : ‖δ‖ ≠ 0 := norm_ne_zero_iff.mpr hδ
  field_simp

theorem conjugateReporterCapacity_ker_eq_norm_ratio
    (δ : StrongDual ℂ H) (hδ : δ ≠ 0) {x : H} (hδx : δ x ≠ 0) :
    conjugateReporterCapacity (LinearMap.ker (δ : H →ₗ[ℂ] ℂ)) x =
      ‖δ‖ ^ 2 / ‖δ x‖ ^ 2 := by
  have hx : x ∉ LinearMap.ker (δ : H →ₗ[ℂ] ℂ) := hδx
  rw [conjugateReporterCapacity_eq hx,
    ← quotientDistance_eq_norm_formationResidual,
    quotientDistance_ker_continuousLinearMap δ hδ]
  have hδnorm : ‖δ‖ ≠ 0 := norm_ne_zero_iff.mpr hδ
  have hδxnorm : ‖δ x‖ ≠ 0 := norm_ne_zero_iff.mpr hδx
  field_simp

section IsometricTransport

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Formation subspace transported by a linear isometry. -/
def isometricFormationSubspace (T : H →ₗᵢ[ℂ] K) (L : Submodule ℂ H) :
    Submodule ℂ K := Submodule.map (T : H →ₗ[ℂ] K) L

omit [CompleteSpace H] [CompleteSpace K] in
theorem mem_isometricFormationSubspace_iff (T : H →ₗᵢ[ℂ] K)
    (L : Submodule ℂ H) (y : K) :
    y ∈ isometricFormationSubspace T L ↔ ∃ x ∈ L, T x = y := by
  rfl

omit [CompleteSpace H] [CompleteSpace K] in
theorem linearIsometry_target_not_mem {T : H →ₗᵢ[ℂ] K}
    {L : Submodule ℂ H} {x : H} (hx : x ∉ L) :
    T x ∉ isometricFormationSubspace T L := by
  rintro ⟨y, hy, hTy⟩
  have hyx : y = x := T.injective hTy
  exact hx (hyx ▸ hy)

omit [CompleteSpace H] [CompleteSpace K] in
theorem quotientDistance_isometricFormationSubspace
    (T : H →ₗᵢ[ℂ] K) (L : Submodule ℂ H) (x : H) :
    quotientDistance (isometricFormationSubspace T L) (T x) =
      quotientDistance L x := by
  have himg : (T : H → K) '' (L : Set H) =
      (isometricFormationSubspace T L : Set K) := by
    ext y
    simp [isometricFormationSubspace]
  rw [quotientDistance, quotientDistance, ← himg,
    Metric.infDist_image T.isometry]

omit [CompleteSpace H] [CompleteSpace K] in
theorem conjugateFormationWork_linearIsometry
    (T : H →ₗᵢ[ℂ] K) (L : Submodule ℂ H) (x : H) :
    conjugateFormationWork (isometricFormationSubspace T L) (T x) =
      conjugateFormationWork L x := by
  simp [conjugateFormationWork,
    quotientDistance_isometricFormationSubspace]

/-- Linear isometries preserve both work and normalized reporter capacity. -/
theorem conjugateReporterCapacity_linearIsometry
    (T : H →ₗᵢ[ℂ] K) (L : Submodule ℂ H)
    [L.HasOrthogonalProjection]
    [(isometricFormationSubspace T L).HasOrthogonalProjection]
    {x : H} (hx : x ∉ L) :
    conjugateReporterCapacity (isometricFormationSubspace T L) (T x) =
      conjugateReporterCapacity L x := by
  have hTx := linearIsometry_target_not_mem (T := T) hx
  have hleft := conjugateFormationWork_mul_reporterCapacity hTx
  have hright := conjugateFormationWork_mul_reporterCapacity hx
  rw [conjugateFormationWork_linearIsometry] at hleft
  have hworkpos : 0 < conjugateFormationWork L x := by
    rw [conjugateFormationWork, quotientDistance_eq_norm_formationResidual]
    exact sq_pos_of_pos (norm_pos_iff.mpr (formationResidual_ne_zero hx))
  exact (mul_left_cancel₀ hworkpos.ne' (hleft.trans hright.symm))

end IsometricTransport

section MarkovRecoveryTransport

open MeasureTheory ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Joint recovered law `μ(dx) K(x,dy)`, formed from identity and recovery kernels. -/
def markovRecoveryJointMeasure (mu : Measure X) (K : Kernel X Y) : Measure (X × Y) :=
  mu.bind (Kernel.prod Kernel.id K)

/-- Markov normalization makes first-coordinate projection preserve the observer law. -/
theorem markovRecoveryJointMeasure_fst_measurePreserving
    (mu : Measure X) (K : Kernel X Y) [IsMarkovKernel K] :
    MeasurePreserving Prod.fst (markovRecoveryJointMeasure mu K) mu := by
  refine ⟨measurable_fst, ?_⟩
  ext s hs
  rw [Measure.map_apply measurable_fst hs, markovRecoveryJointMeasure,
    Measure.bind_apply (measurable_fst hs) (Kernel.prod Kernel.id K).aemeasurable]
  have hpreimage : Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set Y) := by
    ext p
    simp
  simp_rw [hpreimage, Kernel.prod_apply_prod, Kernel.id_apply]
  have hdirac : ∀ x : X, Measure.dirac x s = s.indicator 1 x := by
    intro x
    rw [Measure.dirac_apply' _ hs]
  simp_rw [hdirac]
  simp only [measure_univ, mul_one]
  exact lintegral_indicator_one hs

/-- CFR.20: `J_K f(x,y)=f(x)` as the canonical `L²` pullback isometry. -/
def markovRecoveryIsometry (mu : Measure X) (K : Kernel X Y) [IsMarkovKernel K] :
    Lp ℂ 2 mu →ₗᵢ[ℂ] Lp ℂ 2 (markovRecoveryJointMeasure mu K) :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.fst
    (markovRecoveryJointMeasure_fst_measurePreserving mu K)

/-- CFR.21, work half: common Markov recovery preserves conjugate formation work exactly. -/
theorem conjugateFormationWork_markovRecovery
    (mu : Measure X) (K : Kernel X Y) [IsMarkovKernel K]
    (L : Submodule ℂ (Lp ℂ 2 mu)) (x : Lp ℂ 2 mu) :
    conjugateFormationWork
        (isometricFormationSubspace (markovRecoveryIsometry mu K) L)
        (markovRecoveryIsometry mu K x) =
      conjugateFormationWork L x :=
  conjugateFormationWork_linearIsometry (markovRecoveryIsometry mu K) L x

/-- CFR.21, capacity half: common Markov recovery preserves normalized reporter capacity. -/
theorem conjugateReporterCapacity_markovRecovery
    (mu : Measure X) (K : Kernel X Y) [IsMarkovKernel K]
    (L : Submodule ℂ (Lp ℂ 2 mu))
    [L.HasOrthogonalProjection]
    [(isometricFormationSubspace (markovRecoveryIsometry mu K) L).HasOrthogonalProjection]
    {x : Lp ℂ 2 mu} (hx : x ∉ L) :
    conjugateReporterCapacity
        (isometricFormationSubspace (markovRecoveryIsometry mu K) L)
        (markovRecoveryIsometry mu K x) =
      conjugateReporterCapacity L x :=
  conjugateReporterCapacity_linearIsometry (markovRecoveryIsometry mu K) L hx

/-- Pullback along a measure-preserving measurable observer equivalence is an onto `L²` isometry. -/
def observerFunctionalEquationUnitary (mu : Measure X) (R : X ≃ᵐ X)
    (hR : MeasurePreserving R mu mu) : Lp ℂ 2 mu ≃ₗᵢ[ℂ] Lp ℂ 2 mu where
  __ := Lp.compMeasurePreservingₗᵢ ℂ R hR
  invFun := Lp.compMeasurePreserving R.symm hR.symm
  left_inv f := by
    change Lp.compMeasurePreserving R.symm hR.symm
      (Lp.compMeasurePreserving R hR f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f hR hR.symm]
    simp
  right_inv f := by
    change Lp.compMeasurePreserving R hR
      (Lp.compMeasurePreserving R.symm hR.symm f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f hR.symm hR]
    simp

/-- Functional-equation transform followed by common recovery remains an isometry. -/
def functionalEquationMarkovRecoveryIsometry (mu : Measure X) (R : X ≃ᵐ X)
    (hR : MeasurePreserving R mu mu) (K : Kernel X Y) [IsMarkovKernel K] :
    Lp ℂ 2 mu →ₗᵢ[ℂ] Lp ℂ 2 (markovRecoveryJointMeasure mu K) :=
  (markovRecoveryIsometry mu K).comp
    (observerFunctionalEquationUnitary mu R hR).toLinearIsometry

/-- Functional-equation transform--recover lift preserves both work and capacity. -/
theorem functionalEquationMarkovRecovery_preserves_conjugate_pair
    (mu : Measure X) (R : X ≃ᵐ X) (hR : MeasurePreserving R mu mu)
    (K : Kernel X Y) [IsMarkovKernel K]
    (L : Submodule ℂ (Lp ℂ 2 mu))
    [L.HasOrthogonalProjection]
    [(isometricFormationSubspace
      (functionalEquationMarkovRecoveryIsometry mu R hR K) L).HasOrthogonalProjection]
    {x : Lp ℂ 2 mu} (hx : x ∉ L) :
    conjugateFormationWork
        (isometricFormationSubspace
          (functionalEquationMarkovRecoveryIsometry mu R hR K) L)
        (functionalEquationMarkovRecoveryIsometry mu R hR K x) =
        conjugateFormationWork L x ∧
      conjugateReporterCapacity
        (isometricFormationSubspace
          (functionalEquationMarkovRecoveryIsometry mu R hR K) L)
        (functionalEquationMarkovRecoveryIsometry mu R hR K x) =
        conjugateReporterCapacity L x := by
  constructor
  · exact conjugateFormationWork_linearIsometry
      (functionalEquationMarkovRecoveryIsometry mu R hR K) L x
  · exact conjugateReporterCapacity_linearIsometry
      (functionalEquationMarkovRecoveryIsometry mu R hR K) L hx

end MarkovRecoveryTransport

section WeightedDividedDifference

open Polynomial

/-- Half-density source scale for a positive weighted packet. -/
def weightedPacketScale {N : ℕ} (w : Fin N → ℝ) (v : Fin N → ℂ)
    (i : Fin N) : ℂ := (Real.sqrt (w i) : ℂ) * v i

/-- Coefficient of the normalized weighted divided-difference reporter. -/
def weightedPacketReporterCoeff (n : ℕ) (nodes : Fin (n + 1) ↪ ℂ)
    (w : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℂ) (i : Fin (n + 1)) : ℂ :=
  Lagrange.nodalWeight Finset.univ nodes i / weightedPacketScale w v i

/-- Riesz vector of the weighted divided-difference reporter. -/
def weightedPacketReporterVector (n : ℕ) (nodes : Fin (n + 1) ↪ ℂ)
    (w : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℂ) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => star (weightedPacketReporterCoeff n nodes w v i))

/-- Weighted divided-difference reporter on the half-density packet Hilbert space. -/
def weightedPacketReporter (n : ℕ) (nodes : Fin (n + 1) ↪ ℂ)
    (w : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℂ) :
    StrongDual ℂ (EuclideanSpace ℂ (Fin (n + 1))) :=
  (InnerProductSpace.toDual ℂ (EuclideanSpace ℂ (Fin (n + 1))))
    (weightedPacketReporterVector n nodes w v)

@[simp] theorem weightedPacketReporter_apply (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (y : EuclideanSpace ℂ (Fin (n + 1))) :
    weightedPacketReporter n nodes w v y =
      ∑ i, weightedPacketReporterCoeff n nodes w v i * y i := by
  rw [weightedPacketReporter, InnerProductSpace.toDual_apply_apply]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [weightedPacketReporterVector, dotProduct, Pi.star_apply, mul_comm]

/-- Weighted half-density realization of a polynomial formation packet. -/
def weightedPolynomialPacket (n : ℕ) (nodes : Fin (n + 1) ↪ ℂ)
    (w : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℂ) (P : ℂ[X]) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => weightedPacketScale w v i * P.eval (nodes i))

/-- Weighted half-density realization of the source resolvent packet. -/
def weightedResolventPacket (n : ℕ) (nodes : Fin (n + 1) ↪ ℂ)
    (w : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℂ)
    (c : {z : ℂ // z ∉ Set.range nodes}) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => weightedPacketScale w v i * (c.1 - nodes i)⁻¹)

theorem weightedPacketScale_ne_zero {N : ℕ} {w : Fin N → ℝ}
    {v : Fin N → ℂ} (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0)
    (i : Fin N) : weightedPacketScale w v i ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (Real.sqrt_pos.2 (hw i)).ne'
  · exact hv i

theorem weightedPacketReporter_polynomial (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0)
    (P : ℂ[X]) :
    weightedPacketReporter n nodes w v (weightedPolynomialPacket n nodes w v P) =
      packetDividedDifference n nodes (fun i => P.eval (nodes i)) := by
  rw [weightedPacketReporter_apply]
  simp only [weightedPacketReporterCoeff, weightedPolynomialPacket,
    weightedPacketScale]
  apply Finset.sum_congr rfl
  intro i _
  have hs : (Real.sqrt (w i) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (hw i)).ne'
  dsimp
  field_simp [hs, hv i]

theorem weightedPacketReporter_polynomial_zero_of_natDegree_lt (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0)
    (P : ℂ[X]) (hP : P.natDegree < n) :
    weightedPacketReporter n nodes w v (weightedPolynomialPacket n nodes w v P) = 0 := by
  rw [weightedPacketReporter_polynomial n nodes w v hw hv P]
  exact packetDividedDifference_polynomial_eq_zero_of_natDegree_lt n nodes P hP

theorem weightedPacketReporter_resolvent (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0)
    (c : {z : ℂ // z ∉ Set.range nodes}) :
    weightedPacketReporter n nodes w v (weightedResolventPacket n nodes w v c) =
      ∏ i, (c.1 - nodes i)⁻¹ := by
  rw [weightedPacketReporter_apply]
  simp only [weightedPacketReporterCoeff, weightedResolventPacket,
    weightedPacketScale]
  rw [← resolventDividedDifference_eq n nodes c]
  apply Finset.sum_congr rfl
  intro i _
  have hs : (Real.sqrt (w i) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (hw i)).ne'
  have hc : c.1 - nodes i ≠ 0 := sub_ne_zero.mpr fun h => c.2 ⟨i, h.symm⟩
  field_simp [hs, hv i, hc]

theorem weightedPacketReporter_resolvent_ne_zero (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0)
    (c : {z : ℂ // z ∉ Set.range nodes}) :
    weightedPacketReporter n nodes w v (weightedResolventPacket n nodes w v c) ≠ 0 := by
  rw [weightedPacketReporter_resolvent n nodes w v hw hv c]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact inv_ne_zero (sub_ne_zero.mpr fun h => c.2 ⟨i, h.symm⟩)

theorem norm_sq_weightedPacketReporter (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) :
    ‖weightedPacketReporter n nodes w v‖ ^ 2 =
      ∑ i, ‖weightedPacketReporterCoeff n nodes w v i‖ ^ 2 := by
  rw [weightedPacketReporter, LinearIsometryEquiv.norm_map]
  change ‖weightedPacketReporterVector n nodes w v‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp [weightedPacketReporterVector]

theorem norm_sq_weightedPacketReporter_exact (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) :
    ‖weightedPacketReporter n nodes w v‖ ^ 2 =
      ∑ i, ‖Lagrange.nodalWeight Finset.univ nodes i‖ ^ 2 /
        (w i * ‖v i‖ ^ 2) := by
  rw [norm_sq_weightedPacketReporter]
  apply Finset.sum_congr rfl
  intro i _
  have hsqrtNorm : ‖((Real.sqrt (w i) : ℝ) : ℂ)‖ = Real.sqrt (w i) := by
    calc
      ‖((Real.sqrt (w i) : ℝ) : ℂ)‖ = ‖Real.sqrt (w i)‖ := Complex.norm_real _
      _ = |Real.sqrt (w i)| := Real.norm_eq_abs _
      _ = Real.sqrt (w i) := abs_of_nonneg (Real.sqrt_nonneg _)
  rw [weightedPacketReporterCoeff, weightedPacketScale, norm_div, norm_mul,
    hsqrtNorm, div_pow, mul_pow,
    Real.sq_sqrt (hw i).le]

theorem norm_sq_nodalWeight_eq_inv_product (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (i : Fin (n + 1)) :
    ‖Lagrange.nodalWeight Finset.univ nodes i‖ ^ 2 =
      1 / ‖∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (nodes i - nodes j)‖ ^ 2 := by
  rw [Lagrange.nodalWeight, Finset.prod_inv_distrib, norm_inv]
  rw [inv_pow]
  rw [inv_eq_one_div]

theorem norm_sq_weightedPacketReporter_product_exact (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) :
    ‖weightedPacketReporter n nodes w v‖ ^ 2 =
      ∑ i, 1 /
        (w i * ‖v i‖ ^ 2 *
          ‖∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
            (nodes i - nodes j)‖ ^ 2) := by
  rw [norm_sq_weightedPacketReporter_exact n nodes w v hw]
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_sq_nodalWeight_eq_inv_product]
  ring

/-- Depth-`n-1` weighted formation hyperplane, presented by its exact divided-difference charge. -/
def weightedLowDepthFormationSubspace (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (n + 1))) :=
  LinearMap.ker ((weightedPacketReporter n nodes w v :
    StrongDual ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :
      EuclideanSpace ℂ (Fin (n + 1)) →ₗ[ℂ] ℂ)

theorem weightedPolynomialPacket_mem_lowDepthFormationSubspace (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0)
    (P : ℂ[X]) (hP : P.natDegree < n) :
    weightedPolynomialPacket n nodes w v P ∈
      weightedLowDepthFormationSubspace n nodes w v := by
  change weightedPacketReporter n nodes w v
    (weightedPolynomialPacket n nodes w v P) = 0
  exact weightedPacketReporter_polynomial_zero_of_natDegree_lt
    n nodes w v hw hv P hP

/-- Exact classification: reporter kernel equals weighted polynomial formations of degree `< n`. -/
theorem mem_weightedLowDepthFormationSubspace_iff_exists_polynomial
    (n : ℕ) (hn : 0 < n) (nodes : Fin (n + 1) ↪ ℂ)
    (w : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℂ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0)
    (y : EuclideanSpace ℂ (Fin (n + 1))) :
    y ∈ weightedLowDepthFormationSubspace n nodes w v ↔
      ∃ P : ℂ[X], P.natDegree < n ∧
        weightedPolynomialPacket n nodes w v P = y := by
  constructor
  · intro hy
    let values : Fin (n + 1) → ℂ := fun i => y i / weightedPacketScale w v i
    let P : ℂ[X] := Lagrange.interpolate Finset.univ nodes values
    have hdegree := Lagrange.degree_interpolate_le
      (s := (Finset.univ : Finset (Fin (n + 1)))) values nodes.injective.injOn
    have hdegreeN : P.degree ≤ n := by simpa [P] using hdegree
    have hdegreeLt : P.degree < n + 1 := hdegreeN.trans_lt (by
      exact_mod_cast Nat.lt_succ_self n)
    have hpacket : weightedPolynomialPacket n nodes w v P = y := by
      ext i
      change weightedPacketScale w v i * P.eval (nodes i) = y i
      rw [show P.eval (nodes i) = values i by
        exact Lagrange.eval_interpolate_at_node _ nodes.injective.injOn
          (Finset.mem_univ i)]
      dsimp [values]
      field_simp [weightedPacketScale_ne_zero hw hv i]
    have hddzero : packetDividedDifference n nodes
        (fun i => P.eval (nodes i)) = 0 := by
      rw [← weightedPacketReporter_polynomial n nodes w v hw hv P,
        hpacket]
      exact hy
    have htop : P.coeff n = 0 := by
      rw [← packetDividedDifference_polynomial_eq_coeff n nodes P hdegreeLt]
      exact hddzero
    have hnat : P.natDegree ≤ n := Polynomial.natDegree_le_of_degree_le hdegreeN
    have hnatLt : P.natDegree < n := by
      by_cases hP : P = 0
      · simpa [hP] using hn
      · have hcoeffne : P.coeff P.natDegree ≠ 0 := by
          rw [Polynomial.coeff_natDegree]
          exact Polynomial.leadingCoeff_ne_zero.mpr hP
        exact lt_of_le_of_ne hnat fun heq =>
          hcoeffne (by simpa [heq] using htop)
    exact ⟨P, hnatLt, hpacket⟩
  · rintro ⟨P, hP, rfl⟩
    exact weightedPolynomialPacket_mem_lowDepthFormationSubspace
      n nodes w v hw hv P hP

theorem weightedPacketReporter_ne_zero (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0)
    (c : {z : ℂ // z ∉ Set.range nodes}) :
    weightedPacketReporter n nodes w v ≠ 0 := by
  intro hzero
  have happ := congrArg
    (fun δ : StrongDual ℂ (EuclideanSpace ℂ (Fin (n + 1))) =>
      δ (weightedResolventPacket n nodes w v c)) hzero
  rw [weightedPacketReporter_resolvent n nodes w v hw hv c] at happ
  simp only [zero_apply] at happ
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ =>
    inv_ne_zero (sub_ne_zero.mpr fun h => c.2 ⟨i, h.symm⟩))) happ

theorem weightedResolventPacket_not_mem_lowDepthFormationSubspace (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0)
    (c : {z : ℂ // z ∉ Set.range nodes}) :
    weightedResolventPacket n nodes w v c ∉
      weightedLowDepthFormationSubspace n nodes w v := by
  intro hmem
  exact weightedPacketReporter_resolvent_ne_zero n nodes w v hw hv c hmem

/-- Explicit least weighted work for leaving the depth-`n-1` formation hyperplane. -/
theorem weightedResolvent_conjugateFormationWork_eq (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0)
    (c : {z : ℂ // z ∉ Set.range nodes}) :
    conjugateFormationWork (weightedLowDepthFormationSubspace n nodes w v)
        (weightedResolventPacket n nodes w v c) =
      ‖∏ i, (c.1 - nodes i)⁻¹‖ ^ 2 /
        (∑ i, ‖Lagrange.nodalWeight Finset.univ nodes i‖ ^ 2 /
          (w i * ‖v i‖ ^ 2)) := by
  let δ := weightedPacketReporter n nodes w v
  have hδ : δ ≠ 0 := weightedPacketReporter_ne_zero n nodes w v hw hv c
  have hcharge := conjugateFormationWork_ker_mul_norm_sq δ hδ
    (weightedResolventPacket n nodes w v c)
  have hnormsq := norm_sq_weightedPacketReporter_exact n nodes w v hw
  have happly := weightedPacketReporter_resolvent n nodes w v hw hv c
  change conjugateFormationWork (weightedLowDepthFormationSubspace n nodes w v)
      (weightedResolventPacket n nodes w v c) * ‖δ‖ ^ 2 =
        ‖δ (weightedResolventPacket n nodes w v c)‖ ^ 2 at hcharge
  rw [hnormsq, happly] at hcharge
  have hsumne : (∑ i, ‖Lagrange.nodalWeight Finset.univ nodes i‖ ^ 2 /
      (w i * ‖v i‖ ^ 2)) ≠ 0 := by
    rw [← hnormsq]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hδ)
  exact (eq_div_iff hsumne).2 hcharge

/-- Exact normalized reporter capacity for the weighted resolvent packet. -/
theorem weightedResolvent_conjugateReporterCapacity_eq (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0)
    (c : {z : ℂ // z ∉ Set.range nodes}) :
    conjugateReporterCapacity (weightedLowDepthFormationSubspace n nodes w v)
        (weightedResolventPacket n nodes w v c) =
      (∑ i, ‖Lagrange.nodalWeight Finset.univ nodes i‖ ^ 2 /
          (w i * ‖v i‖ ^ 2)) /
        ‖∏ i, (c.1 - nodes i)⁻¹‖ ^ 2 := by
  let δ := weightedPacketReporter n nodes w v
  have hδ : δ ≠ 0 := weightedPacketReporter_ne_zero n nodes w v hw hv c
  have hδx : δ (weightedResolventPacket n nodes w v c) ≠ 0 :=
    weightedPacketReporter_resolvent_ne_zero n nodes w v hw hv c
  have hcap := conjugateReporterCapacity_ker_eq_norm_ratio δ hδ hδx
  change conjugateReporterCapacity (weightedLowDepthFormationSubspace n nodes w v)
      (weightedResolventPacket n nodes w v c) = _ at hcap
  rw [norm_sq_weightedPacketReporter_exact n nodes w v hw,
    weightedPacketReporter_resolvent n nodes w v hw hv c] at hcap
  exact hcap

/-- Scale-free weighted work--capacity conservation. -/
theorem weightedResolvent_work_mul_capacity_eq_one (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0)
    (c : {z : ℂ // z ∉ Set.range nodes}) :
    conjugateFormationWork (weightedLowDepthFormationSubspace n nodes w v)
        (weightedResolventPacket n nodes w v c) *
      conjugateReporterCapacity (weightedLowDepthFormationSubspace n nodes w v)
        (weightedResolventPacket n nodes w v c) = 1 := by
  exact conjugateFormationWork_mul_reporterCapacity
    (weightedResolventPacket_not_mem_lowDepthFormationSubspace
      n nodes w v hw hv c)

end WeightedDividedDifference

section GramSchurReciprocity

open InnerProductSpace

/-- An infinite sequence whose first `n` values are `u` and whose next value is `x`. -/
def borderedFormationSequence {n : ℕ} (u : Fin n → H) (x : H) (k : ℕ) : H :=
  if hk : k < n then u ⟨k, hk⟩ else x

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
@[simp]
theorem borderedFormationSequence_apply_lt {n : ℕ} (u : Fin n → H) (x : H)
    (k : ℕ) (hk : k < n) :
    borderedFormationSequence u x k = u ⟨k, hk⟩ := by
  simp [borderedFormationSequence, hk]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
@[simp]
theorem borderedFormationSequence_apply_eq {n : ℕ} (u : Fin n → H) (x : H) :
    borderedFormationSequence u x n = x := by
  simp [borderedFormationSequence]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem borderedFormationSequence_fin_eq {n : ℕ} (u : Fin n → H) (x : H) :
    (fun i : Fin n ↦ borderedFormationSequence u x i) = u := by
  funext i
  simp [borderedFormationSequence, i.2]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem borderedFormationSequence_fin_succ_eq {n : ℕ} (u : Fin n → H) (x : H) :
    (fun i : Fin (n + 1) ↦ borderedFormationSequence u x i) = Fin.snoc u x := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp
  · simp [borderedFormationSequence, j.2]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem borderedFormationSequence_image_Iio {n : ℕ} (u : Fin n → H) (x : H) :
    borderedFormationSequence u x '' Set.Iio n = Set.range u := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, (borderedFormationSequence_apply_lt u x k hk).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, borderedFormationSequence_apply_lt u x i i.2⟩

omit [CompleteSpace H] in
/-- The last Gram--Schmidt norm is exactly distance from `x` to the preceding span. -/
theorem norm_gramSchmidt_borderedFormationSequence_eq_quotientDistance {n : ℕ}
    (u : Fin n → H) (x : H) :
    ‖gramSchmidt ℂ (borderedFormationSequence u x) n‖ =
      quotientDistance (Submodule.span ℂ (Set.range u)) x := by
  let w := borderedFormationSequence u x
  let L := Submodule.span ℂ (Set.range u)
  have hspan : Submodule.span ℂ (gramSchmidt ℂ w '' Set.Iio n) = L := by
    rw [span_gramSchmidt_Iio, borderedFormationSequence_image_Iio]
  apply le_antisymm
  · rw [quotientDistance]
    refine (Metric.le_infDist ?_).2 ?_
    · exact ⟨0, Submodule.zero_mem _⟩
    intro y hy
    rw [dist_eq_norm]
    have hymem : y ∈ Submodule.span ℂ (gramSchmidt ℂ w '' Set.Iio n) := by
      rw [hspan]
      simpa [L] using hy
    simpa [w] using norm_gramSchmidt_le_of_mem_span w n hymem
  · have hcorrection := sub_gramSchmidt_mem_span w n
    rw [hspan] at hcorrection
    have hdist := Metric.infDist_le_dist_of_mem (x := x)
      (SetLike.mem_coe.2 hcorrection)
    rw [quotientDistance]
    simpa [L, w, dist_eq_norm] using hdist

omit [CompleteSpace H] in
/-- Exact bordered Gram/Schur determinant ratio: preceding span work is determinant growth. -/
theorem det_gram_fin_snoc_div_det_gram_eq_conjugateFormationWork {n : ℕ}
    (u : Fin n → H) (x : H) (hu : LinearIndependent ℂ u) :
    (Matrix.gram ℂ (Fin.snoc u x)).det / (Matrix.gram ℂ u).det =
      (conjugateFormationWork (Submodule.span ℂ (Set.range u)) x : ℂ) := by
  let w := borderedFormationSequence u x
  have hprevU : (Matrix.gram ℂ u).det ≠ 0 := by
    apply Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
    exact hu
  have hprev : (Matrix.gram ℂ (fun i : Fin n ↦ w i)).det ≠ 0 := by
    simpa [w] using hprevU
  have hdet := det_gram_fin_succ_of_det_ne_zero w n hprev
  rw [borderedFormationSequence_fin_eq,
    borderedFormationSequence_fin_succ_eq] at hdet
  rw [hdet, mul_div_cancel_left₀ _ hprevU]
  rw [inner_self_eq_norm_sq_to_K]
  rw [norm_gramSchmidt_borderedFormationSequence_eq_quotientDistance]
  simp [conjugateFormationWork, Complex.ofReal_pow]

end GramSchurReciprocity

section WeightedGramSchurSpecialization

open Polynomial

/-- Algebraic feature matrix, with features in columns and observation nodes in rows. -/
def weightedFeatureDesign {N J : ℕ} (a : Fin J → Fin N → ℂ) :
    Matrix (Fin N) (Fin J) ℂ :=
  Matrix.of fun i j ↦ a j i

/-- Diagonal positive observation-weight matrix. -/
def weightedObservationMatrix {N : ℕ} (w : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i ↦ (w i : ℂ)

/-- Half-density Hilbert packet attached to a feature column. -/
def weightedFeaturePacket {N J : ℕ} (w : Fin N → ℝ)
    (a : Fin J → Fin N → ℂ) (j : Fin J) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 fun i ↦ (Real.sqrt (w i) : ℂ) * a j i

/-- Exact identity `Gram = A⁺ Ω A` for positive weighted feature packets. -/
theorem gram_weightedFeaturePacket_eq_design_mul_weight_mul_design {N J : ℕ}
    (w : Fin N → ℝ) (a : Fin J → Fin N → ℂ) (hw : ∀ i, 0 < w i) :
    Matrix.gram ℂ (weightedFeaturePacket w a) =
      (weightedFeatureDesign a).conjTranspose * weightedObservationMatrix w *
        weightedFeatureDesign a := by
  ext j k
  rw [Matrix.gram_apply, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  change ((Real.sqrt (w i) : ℂ) * a k i) *
      star ((Real.sqrt (w i) : ℂ) * a j i) =
    ((weightedFeatureDesign a).conjTranspose *
        Matrix.diagonal (fun i ↦ (w i : ℂ))) j i *
      weightedFeatureDesign a i k
  rw [Matrix.mul_diagonal]
  simp only [weightedFeatureDesign, Matrix.conjTranspose_apply,
    Matrix.of_apply]
  rw [star_mul, Complex.star_def, Complex.conj_ofReal]
  have hsqrt : ((Real.sqrt (w i) : ℝ) : ℂ) * (Real.sqrt (w i) : ℂ) = (w i : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw i).le]
  calc
    (Real.sqrt (w i) : ℂ) * a k i *
        (star (a j i) * (Real.sqrt (w i) : ℂ)) =
      ((Real.sqrt (w i) : ℂ) * (Real.sqrt (w i) : ℂ)) *
        star (a j i) * a k i := by ring
    _ = _ := by rw [hsqrt, Complex.star_def]; ring

/-- Weighted packets of the monomial basis of degrees below `n`. -/
def weightedMonomialPacket (n : ℕ) (nodes : Fin (n + 1) ↪ ℂ)
    (w : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℂ) (k : Fin n) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  weightedPolynomialPacket n nodes w v (X ^ (k : ℕ))

/-- Unweighted polynomial feature columns underlying `A`. -/
def weightedPolynomialFeature (n : ℕ) (nodes : Fin (n + 1) ↪ ℂ)
    (v : Fin (n + 1) → ℂ) (k : Fin n) (i : Fin (n + 1)) : ℂ :=
  v i * nodes i ^ (k : ℕ)

/-- Unweighted bordered feature block `[A\mid r]`. -/
def weightedBorderedFeature (n : ℕ) (nodes : Fin (n + 1) ↪ ℂ)
    (v : Fin (n + 1) → ℂ) (c : {z : ℂ // z ∉ Set.range nodes})
    (k : Fin (n + 1)) (i : Fin (n + 1)) : ℂ :=
  Fin.lastCases (v i * (c.1 - nodes i)⁻¹)
    (fun j ↦ weightedPolynomialFeature n nodes v j i) k

/-- Weighted polynomial Gram block `G = A⁺ Ω A`. -/
def weightedFormationGram (n : ℕ) (nodes : Fin (n + 1) ↪ ℂ)
    (w : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (weightedFeatureDesign (weightedPolynomialFeature n nodes v)).conjTranspose *
    weightedObservationMatrix w *
      weightedFeatureDesign (weightedPolynomialFeature n nodes v)

/-- Weighted bordered Gram block `G̃ = [A\mid r]⁺ Ω [A\mid r]`. -/
def weightedBorderedFormationGram (n : ℕ) (nodes : Fin (n + 1) ↪ ℂ)
    (w : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℂ)
    (c : {z : ℂ // z ∉ Set.range nodes}) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (weightedFeatureDesign (weightedBorderedFeature n nodes v c)).conjTranspose *
    weightedObservationMatrix w *
      weightedFeatureDesign (weightedBorderedFeature n nodes v c)

theorem weightedFeaturePacket_polynomial_eq (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) :
    weightedFeaturePacket w (weightedPolynomialFeature n nodes v) =
      weightedMonomialPacket n nodes w v := by
  funext k
  ext i
  simp [weightedFeaturePacket, weightedPolynomialFeature, weightedMonomialPacket,
    weightedPolynomialPacket, weightedPacketScale]
  ring

theorem weightedFeaturePacket_bordered_eq (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (c : {z : ℂ // z ∉ Set.range nodes}) :
    weightedFeaturePacket w (weightedBorderedFeature n nodes v c) =
      Fin.snoc (weightedMonomialPacket n nodes w v)
        (weightedResolventPacket n nodes w v c) := by
  funext k
  refine Fin.lastCases ?_ (fun j ↦ ?_) k
  · ext i
    simp [weightedFeaturePacket, weightedBorderedFeature, weightedResolventPacket,
      weightedPacketScale]
    ring
  · ext i
    simp [weightedFeaturePacket, weightedBorderedFeature, weightedPolynomialFeature,
      weightedMonomialPacket, weightedPolynomialPacket, weightedPacketScale]
    ring

theorem weightedFormationGram_eq_packetGram (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) :
    weightedFormationGram n nodes w v =
      Matrix.gram ℂ (weightedMonomialPacket n nodes w v) := by
  rw [← weightedFeaturePacket_polynomial_eq]
  exact (gram_weightedFeaturePacket_eq_design_mul_weight_mul_design
    w (weightedPolynomialFeature n nodes v) hw).symm

theorem weightedBorderedFormationGram_eq_packetGram (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i)
    (c : {z : ℂ // z ∉ Set.range nodes}) :
    weightedBorderedFormationGram n nodes w v c =
      Matrix.gram ℂ (Fin.snoc (weightedMonomialPacket n nodes w v)
        (weightedResolventPacket n nodes w v c)) := by
  rw [← weightedFeaturePacket_bordered_eq]
  exact (gram_weightedFeaturePacket_eq_design_mul_weight_mul_design
    w (weightedBorderedFeature n nodes v c) hw).symm

/-- Restriction of a packet to the first `n` nodes. -/
def restrictWeightedPacket (n : ℕ) :
    EuclideanSpace ℂ (Fin (n + 1)) →ₗ[ℂ] (Fin n → ℂ) :=
  (LinearMap.funLeft ℂ ℂ Fin.castSucc).comp
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (n + 1) ↦ ℂ)).toLinearMap

@[simp]
theorem restrictWeightedPacket_apply (n : ℕ)
    (y : EuclideanSpace ℂ (Fin (n + 1))) (i : Fin n) :
    restrictWeightedPacket n y i = y i.castSucc := rfl

/-- Positive half-density scaling preserves Vandermonde independence of low-degree monomials. -/
theorem weightedMonomialPacket_linearIndependent (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0) :
    LinearIndependent ℂ (weightedMonomialPacket n nodes w v) := by
  let z : Fin n → ℂ := fun i ↦ nodes i.castSucc
  let s : Fin n → ℂ := fun i ↦ weightedPacketScale w v i.castSucc
  let B : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k ↦ s i * z i ^ (k : ℕ)
  have hz : Function.Injective z := by
    intro i j hij
    exact Fin.castSucc_injective n (nodes.injective hij)
  have hs : ∀ i, s i ≠ 0 := fun i ↦ weightedPacketScale_ne_zero hw hv i.castSucc
  have hdetB : B.det ≠ 0 := by
    have hBdef : B =
        (Matrix.of (fun i k : Fin n ↦ s i * z i ^ (k : ℕ)) :
          Matrix (Fin n) (Fin n) ℂ) := rfl
    rw [hBdef, det_weightedVandermonde]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hs i)
      (Matrix.det_vandermonde_ne_zero_iff.mpr hz)
  apply LinearIndependent.of_comp (restrictWeightedPacket n)
  have hrows : LinearIndependent ℂ (B.transpose.row) :=
    Matrix.linearIndependent_rows_of_det_ne_zero (A := B.transpose) (by
      rw [Matrix.det_transpose]
      exact hdetB)
  have hcomp :
      ((restrictWeightedPacket n :
          EuclideanSpace ℂ (Fin (n + 1)) →ₗ[ℂ] (Fin n → ℂ)) ∘
        weightedMonomialPacket n nodes w v) = B.transpose.row := by
    funext k i
    simp [Function.comp_def, restrictWeightedPacket, weightedMonomialPacket,
      weightedPolynomialPacket, B, z, s, Matrix.row]
  rw [hcomp]
  exact hrows

/-- Polynomial packet is its coefficient sum of weighted monomial packets. -/
theorem weightedPolynomialPacket_eq_sum_support (n : ℕ)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (P : ℂ[X]) :
    weightedPolynomialPacket n nodes w v P =
      ∑ k ∈ P.support, P.coeff k •
        weightedPolynomialPacket n nodes w v (X ^ k) := by
  ext i
  change weightedPacketScale w v i * P.eval (nodes i) = _
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  simp [weightedPolynomialPacket]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Low-depth weighted formation hyperplane is exactly span of weighted monomial columns. -/
theorem span_weightedMonomialPacket_eq_lowDepthFormationSubspace (n : ℕ) (hn : 0 < n)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0) :
    Submodule.span ℂ (Set.range (weightedMonomialPacket n nodes w v)) =
      weightedLowDepthFormationSubspace n nodes w v := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact weightedPolynomialPacket_mem_lowDepthFormationSubspace
      n nodes w v hw hv (X ^ (k : ℕ)) (by
        simpa only [natDegree_pow, natDegree_X, mul_one] using k.2)
  · intro y hy
    obtain ⟨P, hP, rfl⟩ :=
      (mem_weightedLowDepthFormationSubspace_iff_exists_polynomial
        n hn nodes w v hw hv y).1 hy
    rw [weightedPolynomialPacket_eq_sum_support]
    apply Submodule.sum_mem
    intro k hk
    apply Submodule.smul_mem
    apply Submodule.subset_span
    have hkn : k < n :=
      lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp k hk) hP
    exact ⟨⟨k, hkn⟩, rfl⟩

/-- CFR.19: weighted monomial/resolvent bordered Gram ratio equals exact formation work. -/
theorem weightedResolvent_gram_det_ratio_eq_work (n : ℕ) (hn : 0 < n)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0)
    (c : {z : ℂ // z ∉ Set.range nodes}) :
    (Matrix.gram ℂ (Fin.snoc (weightedMonomialPacket n nodes w v)
        (weightedResolventPacket n nodes w v c))).det /
      (Matrix.gram ℂ (weightedMonomialPacket n nodes w v)).det =
        (conjugateFormationWork (weightedLowDepthFormationSubspace n nodes w v)
          (weightedResolventPacket n nodes w v c) : ℂ) := by
  rw [← span_weightedMonomialPacket_eq_lowDepthFormationSubspace
    n hn nodes w v hw hv]
  exact det_gram_fin_snoc_div_det_gram_eq_conjugateFormationWork
    (weightedMonomialPacket n nodes w v)
    (weightedResolventPacket n nodes w v c)
    (weightedMonomialPacket_linearIndependent n nodes w v hw hv)

/-- Literal CFR.19 Schur-complement determinant law for `G=A⁺ΩA` and its resolvent border. -/
theorem weightedBorderedFormationGram_det_ratio_eq_work (n : ℕ) (hn : 0 < n)
    (nodes : Fin (n + 1) ↪ ℂ) (w : Fin (n + 1) → ℝ)
    (v : Fin (n + 1) → ℂ) (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ≠ 0)
    (c : {z : ℂ // z ∉ Set.range nodes}) :
    (weightedBorderedFormationGram n nodes w v c).det /
      (weightedFormationGram n nodes w v).det =
        (conjugateFormationWork (weightedLowDepthFormationSubspace n nodes w v)
          (weightedResolventPacket n nodes w v c) : ℂ) := by
  rw [weightedBorderedFormationGram_eq_packetGram n nodes w v hw c,
    weightedFormationGram_eq_packetGram n nodes w v hw]
  exact weightedResolvent_gram_det_ratio_eq_work
    n hn nodes w v hw hv c

end WeightedGramSchurSpecialization

section DepthInvisibilityCounterexample

open Polynomial

/-- Literal consecutive nodes `1,…,n+1` of CFR.22. -/
def consecutivePrimitiveNodes (n : ℕ) : Fin (n + 1) ↪ ℂ where
  toFun i := (((i : ℕ) + 1 : ℝ) : ℂ)
  inj' := by
    intro i j hij
    have hreal : (((i : ℕ) + 1 : ℝ)) = (((j : ℕ) + 1 : ℝ)) := by
      simpa using congrArg Complex.re hij
    have hnat : (i : ℕ) + 1 = (j : ℕ) + 1 := by
      exact_mod_cast hreal
    apply Fin.ext
    omega

/-- Zero lies off every positive consecutive node. -/
def zeroOffConsecutivePrimitiveNodes (n : ℕ) :
    {z : ℂ // z ∉ Set.range (consecutivePrimitiveNodes n)} :=
  ⟨0, by
    rintro ⟨i, hi⟩
    have hpos : (0 : ℝ) < (i : ℕ) + 1 := by positivity
    have hne : ((((i : ℕ) + 1 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast hpos.ne'
    exact hne hi⟩

/-- Chu--Vandermonde square identity in the exact indexing used by CFR.23. -/
theorem sum_choose_sq_eq_choose_two_mul (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), n.choose k * n.choose k = (2 * n).choose n := by
  rw [show 2 * n = n + n by omega, Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.choose_symm (Finset.mem_range_succ_iff.mp hk)]

/-- Consecutive-node erased denominator has exact factorial-pair norm. -/
theorem norm_consecutivePrimitiveNodes_prod_erase (n : ℕ) (i : Fin (n + 1)) :
    ‖∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
        (consecutivePrimitiveNodes n i - consecutivePrimitiveNodes n j)‖ =
      (((i : ℕ).factorial : ℝ) * ((n - (i : ℕ)).factorial : ℝ)) := by
  rw [norm_prod]
  convert _root_.HTGeometry.prod_erase_index_dist n i using 1
  apply Finset.prod_congr rfl
  intro j _
  calc
    ‖consecutivePrimitiveNodes n i - consecutivePrimitiveNodes n j‖ =
        ‖((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) : ℝ) : ℂ)‖ := by
      congr 1
      simp [consecutivePrimitiveNodes]
    _ = ‖((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)‖ := Complex.norm_real _
    _ = |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := Real.norm_eq_abs _

/-- Consecutive resolvent divided-difference charge has squared magnitude `1/((n+1)!)²`. -/
theorem norm_sq_consecutivePrimitive_resolvent_charge (n : ℕ) :
    ‖∏ i, ((zeroOffConsecutivePrimitiveNodes n).1 -
        consecutivePrimitiveNodes n i)⁻¹‖ ^ 2 =
      1 / ((((n + 1).factorial : ℕ) : ℝ) ^ 2) := by
  have hnorm :
      ‖∏ i, ((zeroOffConsecutivePrimitiveNodes n).1 -
          consecutivePrimitiveNodes n i)⁻¹‖ =
        ((((n + 1).factorial : ℕ) : ℝ))⁻¹ := by
    rw [norm_prod]
    have hterm : ∀ i : Fin (n + 1),
        ‖((zeroOffConsecutivePrimitiveNodes n).1 -
          consecutivePrimitiveNodes n i)⁻¹‖ =
          ((((i : ℕ) + 1 : ℕ) : ℝ))⁻¹ := by
      intro i
      rw [norm_inv]
      congr 1
      calc
        ‖(zeroOffConsecutivePrimitiveNodes n).1 -
            consecutivePrimitiveNodes n i‖ =
            ‖-((((i : ℕ) + 1 : ℝ) : ℂ))‖ := by
              congr 1
              simp [zeroOffConsecutivePrimitiveNodes, consecutivePrimitiveNodes]
        _ = ‖((((i : ℕ) + 1 : ℝ) : ℂ))‖ := norm_neg _
        _ = ‖((i : ℕ) + 1 : ℝ)‖ := Complex.norm_real _
        _ = ((i : ℕ) : ℝ) + 1 := by
          rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        _ = (((i : ℕ) + 1 : ℕ) : ℝ) := by norm_num
    simp_rw [hterm]
    rw [Fin.prod_univ_eq_prod_range
      (fun i : ℕ ↦ (((i + 1 : ℕ) : ℝ))⁻¹) (n + 1)]
    rw [Finset.prod_inv_distrib, ← Nat.cast_prod,
      ← Nat.factorial_eq_prod_range_add_one]
  rw [hnorm, inv_pow, inv_eq_one_div]

theorem inv_sq_factorial_pair_eq_choose_sq_div_factorial_sq
    (n : ℕ) (i : Fin (n + 1)) :
    1 / (((((i : ℕ).factorial : ℕ) : ℝ) *
        (((n - (i : ℕ)).factorial : ℕ) : ℝ)) ^ 2) =
      ((((n.choose (i : ℕ) : ℕ) : ℝ) ^ 2) /
        ((((n.factorial : ℕ) : ℝ)) ^ 2)) := by
  have hi : (i : ℕ) ≤ n := by omega
  have hfactNat := Nat.choose_mul_factorial_mul_factorial hi
  have hfact :
      ((n.choose (i : ℕ) : ℝ) * ((i : ℕ).factorial : ℝ) *
          ((n - (i : ℕ)).factorial : ℝ)) =
        (n.factorial : ℝ) := by
    exact_mod_cast hfactNat
  rw [← hfact]
  have hchoose : (n.choose (i : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hi).ne'
  have hfi : (((i : ℕ).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hfn : (((n - (i : ℕ)).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Exact squared reporter norm for consecutive nodes. -/
theorem sum_inv_sq_factorial_pair_eq_choose_div_factorial_sq (n : ℕ) :
    ∑ i : Fin (n + 1),
        1 / (((((i : ℕ).factorial : ℕ) : ℝ) *
          (((n - (i : ℕ)).factorial : ℕ) : ℝ)) ^ 2) =
      (((2 * n).choose n : ℕ) : ℝ) / ((((n.factorial : ℕ) : ℝ)) ^ 2) := by
  simp_rw [inv_sq_factorial_pair_eq_choose_sq_div_factorial_sq]
  rw [← Finset.sum_div]
  congr 1
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ ↦ (((n.choose k : ℕ) : ℝ) ^ 2)) (n + 1)]
  exact_mod_cast (by simpa [pow_two] using sum_choose_sq_eq_choose_two_mul n)

/-- Consecutive-node normalized reporter norm is the central-binomial/factorial quotient. -/
theorem norm_sq_consecutivePrimitive_reporter (n : ℕ) :
    ‖weightedPacketReporter n (consecutivePrimitiveNodes n) (fun _ ↦ 1) (fun _ ↦ 1)‖ ^ 2 =
      (((2 * n).choose n : ℕ) : ℝ) / ((((n.factorial : ℕ) : ℝ)) ^ 2) := by
  rw [norm_sq_weightedPacketReporter_product_exact n
    (consecutivePrimitiveNodes n) (fun _ ↦ 1) (fun _ ↦ 1) (by simp)]
  simp only [one_mul, norm_one, one_pow]
  simp_rw [norm_consecutivePrimitiveNodes_prod_erase]
  exact sum_inv_sq_factorial_pair_eq_choose_div_factorial_sq n

/-- CFR.22 exact depth: not formable below depth `n`, formable at depth at most `n`. -/
theorem consecutivePrimitive_resolvent_exact_depth (n : ℕ) :
    resolventPacket n (consecutivePrimitiveNodes n) (zeroOffConsecutivePrimitiveNodes n) ∉
        Set.range (lowDepthPacketMap n (consecutivePrimitiveNodes n)) ∧
      resolventPacket n (consecutivePrimitiveNodes n) (zeroOffConsecutivePrimitiveNodes n) ∈
        Set.range (atMostDepthPacketMap n (consecutivePrimitiveNodes n)) :=
  ⟨resolventPacket_not_mem_range_lowDepthPacketMap _ _ _,
    resolventPacket_mem_range_atMostDepthPacketMap _ _ _⟩

/-- Least work for consecutive unit nodes/amplitudes/weights and pole `c=0`. -/
def consecutivePrimitiveWork (n : ℕ) : ℝ :=
  conjugateFormationWork
    (weightedLowDepthFormationSubspace n (consecutivePrimitiveNodes n)
      (fun _ ↦ 1) (fun _ ↦ 1))
    (weightedResolventPacket n (consecutivePrimitiveNodes n)
      (fun _ ↦ 1) (fun _ ↦ 1) (zeroOffConsecutivePrimitiveNodes n))

/-- Normalized reporter capacity for the consecutive primitive packet. -/
def consecutivePrimitiveCapacity (n : ℕ) : ℝ :=
  conjugateReporterCapacity
    (weightedLowDepthFormationSubspace n (consecutivePrimitiveNodes n)
      (fun _ ↦ 1) (fun _ ↦ 1))
    (weightedResolventPacket n (consecutivePrimitiveNodes n)
      (fun _ ↦ 1) (fun _ ↦ 1) (zeroOffConsecutivePrimitiveNodes n))

/-- CFR.23 exact work value, with packet size `N=n+1`. -/
theorem consecutivePrimitiveWork_eq (n : ℕ) :
    consecutivePrimitiveWork n =
      1 / (((n + 1 : ℕ) : ℝ) ^ 2 * (((2 * n).choose n : ℕ) : ℝ)) := by
  have hw : ∀ i : Fin (n + 1), (0 : ℝ) < (1 : ℝ) := by simp
  have hv : ∀ i : Fin (n + 1), (1 : ℂ) ≠ 0 := by simp
  have hwork := weightedResolvent_conjugateFormationWork_eq n
    (consecutivePrimitiveNodes n) (fun _ ↦ 1) (fun _ ↦ 1) hw hv
    (zeroOffConsecutivePrimitiveNodes n)
  rw [← norm_sq_weightedPacketReporter_exact n (consecutivePrimitiveNodes n)
      (fun _ ↦ 1) (fun _ ↦ 1) hw,
    norm_sq_consecutivePrimitive_resolvent_charge,
    norm_sq_consecutivePrimitive_reporter] at hwork
  change consecutivePrimitiveWork n = _ at hwork
  rw [hwork]
  have hfact : ((((n + 1).factorial : ℕ) : ℝ)) =
      ((n + 1 : ℕ) : ℝ) * (((n.factorial : ℕ) : ℝ)) := by
    rw [Nat.factorial_succ]
    norm_num
  rw [hfact]
  have hchoose : ((((2 * n).choose n : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 2 * n)).ne'
  have hfactorial : ((((n.factorial : ℕ) : ℝ)) ≠ 0) := by positivity
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

/-- CFR.24 exact reciprocal capacity value, with packet size `N=n+1`. -/
theorem consecutivePrimitiveCapacity_eq (n : ℕ) :
    consecutivePrimitiveCapacity n =
      (((n + 1 : ℕ) : ℝ) ^ 2 * (((2 * n).choose n : ℕ) : ℝ)) := by
  have hw : ∀ i : Fin (n + 1), (0 : ℝ) < (1 : ℝ) := by simp
  have hv : ∀ i : Fin (n + 1), (1 : ℂ) ≠ 0 := by simp
  have hcap := weightedResolvent_conjugateReporterCapacity_eq n
    (consecutivePrimitiveNodes n) (fun _ ↦ 1) (fun _ ↦ 1) hw hv
    (zeroOffConsecutivePrimitiveNodes n)
  rw [← norm_sq_weightedPacketReporter_exact n (consecutivePrimitiveNodes n)
      (fun _ ↦ 1) (fun _ ↦ 1) hw,
    norm_sq_consecutivePrimitive_reporter,
    norm_sq_consecutivePrimitive_resolvent_charge] at hcap
  change consecutivePrimitiveCapacity n = _ at hcap
  rw [hcap]
  have hfact : ((((n + 1).factorial : ℕ) : ℝ)) =
      ((n + 1 : ℕ) : ℝ) * (((n.factorial : ℕ) : ℝ)) := by
    rw [Nat.factorial_succ]
    norm_num
  rw [hfact]
  have hchoose : ((((2 * n).choose n : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : n ≤ 2 * n)).ne'
  have hfactorial : ((((n.factorial : ℕ) : ℝ)) ≠ 0) := by positivity
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

theorem consecutivePrimitive_denominator_ge_size (n : ℕ) :
    (((n + 1 : ℕ) : ℝ)) ≤
      (((n + 1 : ℕ) : ℝ) ^ 2 * (((2 * n).choose n : ℕ) : ℝ)) := by
  have hsize : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
  have hchooseNat : 1 ≤ (2 * n).choose n := by
    have := Nat.choose_pos (by omega : n ≤ 2 * n)
    omega
  have hchoose : (1 : ℝ) ≤ (((2 * n).choose n : ℕ) : ℝ) := by
    exact_mod_cast hchooseNat
  calc
    (((n + 1 : ℕ) : ℝ)) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    _ = ((n + 1 : ℕ) : ℝ) ^ 2 * 1 := by ring
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * (((2 * n).choose n : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hchoose (sq_nonneg _)

/-- CFR.23 asymptotic: exact formation depth escapes while least work tends to zero. -/
theorem tendsto_consecutivePrimitiveWork_atTop_zero :
    Filter.Tendsto consecutivePrimitiveWork Filter.atTop (nhds 0) := by
  apply squeeze_zero (g := fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ)))
  · intro n
    rw [consecutivePrimitiveWork_eq]
    positivity
  · intro n
    rw [consecutivePrimitiveWork_eq]
    exact one_div_le_one_div_of_le (by positivity)
      (consecutivePrimitive_denominator_ge_size n)
  · have hsize : Filter.Tendsto
        (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ))) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n ↦ by norm_num)
        (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
    simpa [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hsize

/-- CFR.24 asymptotic: normalized reporter capacity diverges to infinity. -/
theorem tendsto_consecutivePrimitiveCapacity_atTop :
    Filter.Tendsto consecutivePrimitiveCapacity Filter.atTop Filter.atTop := by
  have hsize : Filter.Tendsto
      (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ))) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n ↦ by norm_num)
      (tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
  apply Filter.tendsto_atTop_mono (fun n ↦ ?_) hsize
  rw [consecutivePrimitiveCapacity_eq]
  exact consecutivePrimitive_denominator_ge_size n

end DepthInvisibilityCounterexample

end

end GaloisForLFunctions.HTGeometry
