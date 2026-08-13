import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
import GaloisForLFunctions.HTGeometry.GreedyCourantFischer

/-!
# The finite Dirac compression theorem of Connes--Consani

This file formalizes Lemma `diracpm2` and Proposition `diracpm3` of
Connes--Consani, *Spectral triples and zeta-cycles* (2021).  The source uses the
Courant--Fischer theorem for the positive eigenvalues of a Hermitian matrix and
then constrains the maximizing subspace to be orthogonal to a prescribed part
of the kernel.  Mathlib supplies sorted eigenvalues and the spectral theorem,
but not this higher min--max statement, so the complete finite-dimensional
argument is proved here from the sorted orthonormal eigenbasis.

The extrema below are encoded by their universal property plus an attaining
witness.  Thus `CCMIsRayleighMinimum T F r` literally says that `r` is the
minimum on the unit sphere of `F`, while `CCMIsConstrainedMinMax ... μ` says
that `μ` is the attained maximum of those minima.  This avoids defining the
source eigenvalue by its variational formula: `μ` remains mathlib's independently
defined decreasing eigenvalue.
-/

open Module Set
open scoped InnerProductSpace

noncomputable section

namespace RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Literal Hermitian quadratic value used in the CCM min--max formulas. -/
def ccmHermitianQuadraticValue (T : E →ₗ[ℂ] E) (x : E) : ℝ :=
  Complex.re (inner ℂ x (T x))

/-- `r` is the attained minimum of the Hermitian quadratic value on the unit
sphere of `F`. -/
def CCMIsRayleighMinimum (T : E →ₗ[ℂ] E) (F : Submodule ℂ E) (r : ℝ) : Prop :=
  (∀ x : E, x ∈ F → ‖x‖ = 1 → r ≤ ccmHermitianQuadraticValue T x) ∧
    ∃ x : E, x ∈ F ∧ ‖x‖ = 1 ∧ ccmHermitianQuadraticValue T x = r

/-- Literal universal-property form of the constrained `max_F min_x` in
`diracpm2`.  Every admissible subspace has an attained minimum no larger than
`μ`, and one admissible subspace attains `μ`. -/
def CCMIsConstrainedMinMax (T : E →ₗ[ℂ] E) (k : ℕ)
    (K : Submodule ℂ E) (μ : ℝ) : Prop :=
  (∀ F : Submodule ℂ E, Module.finrank ℂ F = k → F ≤ Kᗮ →
      ∃ r : ℝ, CCMIsRayleighMinimum T F r ∧ r ≤ μ) ∧
    ∃ F : Submodule ℂ E, Module.finrank ℂ F = k ∧ F ≤ Kᗮ ∧
      CCMIsRayleighMinimum T F μ

/-- Span of the first `i+1` vectors in the decreasing Hermitian eigenbasis. -/
def ccmLeadingEigenSubspace {n : ℕ} {T : E →ₗ[ℂ] E}
    (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n) (i : Fin n) :
    Submodule ℂ E :=
  Submodule.span ℂ ((hT.eigenvectorBasis hn : Fin n → E) '' Set.Iic i)

/-- Quadratic value in the sorted eigenbasis. -/
theorem ccmHermitianQuadraticValue_eq_sum {n : ℕ} {T : E →ₗ[ℂ] E}
    (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n) (x : E) :
    ccmHermitianQuadraticValue T x =
      ∑ j : Fin n, hT.eigenvalues hn j * ‖(hT.eigenvectorBasis hn).repr x j‖ ^ 2 := by
  rw [ccmHermitianQuadraticValue]
  have hinner :
      inner ℂ x (T x) =
        ∑ j : Fin n,
          (hT.eigenvalues hn j : ℂ) *
            ((starRingEnd ℂ) ((hT.eigenvectorBasis hn).repr x j) *
              (hT.eigenvectorBasis hn).repr x j) := by
    rw [← (hT.eigenvectorBasis hn).repr.inner_map_map x (T x)]
    simp_rw [PiLp.inner_apply, RCLike.inner_apply',
      hT.eigenvectorBasis_apply_self_apply hn]
    apply Finset.sum_congr rfl
    intro j _
    ac_rfl
  rw [hinner, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.mul_re, Complex.normSq_apply]

/-- The leading eigenspace has exactly the source rank `i+1`. -/
theorem ccmLeadingEigenSubspace_finrank {n : ℕ} {T : E →ₗ[ℂ] E}
    (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n) (i : Fin n) :
    Module.finrank ℂ (ccmLeadingEigenSubspace hT hn i) = i.val + 1 := by
  let b := hT.eigenvectorBasis hn
  let v : Set.Iic i → E := fun j => b j.1
  have hv : LinearIndependent ℂ v :=
    b.toBasis.linearIndependent.comp (fun j : Set.Iic i => j.1) Subtype.val_injective
  have hrange : Set.range v = (b : Fin n → E) '' Set.Iic i := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.1, j.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  rw [ccmLeadingEigenSubspace, ← hrange, finrank_span_eq_card hv]
  simp

/-- Membership in the leading eigenspace kills every later eigen-coordinate. -/
theorem ccmLeadingEigenSubspace_repr_eq_zero_of_not_le {n : ℕ}
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (i j : Fin n) {x : E} (hx : x ∈ ccmLeadingEigenSubspace hT hn i)
    (hji : ¬j ≤ i) :
    (hT.eigenvectorBasis hn).repr x j = 0 := by
  have hsupp :
      ↑((hT.eigenvectorBasis hn).toBasis.repr x).support ⊆ Set.Iic i :=
    (hT.eigenvectorBasis hn).toBasis.repr_support_subset_of_mem_span (Set.Iic i) hx
  have hjnot : j ∉ ((hT.eigenvectorBasis hn).toBasis.repr x).support := by
    intro hj
    exact hji (hsupp hj)
  simpa only [(hT.eigenvectorBasis hn).coe_toBasis_repr_apply] using
    (Finsupp.notMem_support_iff.mp hjnot)

/-- Every unit vector in the leading eigenspace has quadratic value at least the
`i`-th decreasing eigenvalue. -/
theorem ccmLeadingEigenSubspace_eigenvalue_le_quadratic {n : ℕ}
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (i : Fin n) {x : E} (hx : x ∈ ccmLeadingEigenSubspace hT hn i)
    (hxnorm : ‖x‖ = 1) :
    hT.eigenvalues hn i ≤ ccmHermitianQuadraticValue T x := by
  rw [ccmHermitianQuadraticValue_eq_sum hT hn x]
  have hnormsum :
      ∑ j : Fin n, ‖(hT.eigenvectorBasis hn).repr x j‖ ^ 2 = ‖x‖ ^ 2 := by
    simpa only [(hT.eigenvectorBasis hn).repr_apply_apply] using
      (hT.eigenvectorBasis hn).sum_sq_norm_inner_right x
  calc
    hT.eigenvalues hn i =
        hT.eigenvalues hn i *
          (∑ j : Fin n, ‖(hT.eigenvectorBasis hn).repr x j‖ ^ 2) := by
            rw [hnormsum, hxnorm]
            ring
    _ = ∑ j : Fin n,
          hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x j‖ ^ 2 := by
            rw [Finset.mul_sum]
    _ ≤ ∑ j : Fin n,
          hT.eigenvalues hn j * ‖(hT.eigenvectorBasis hn).repr x j‖ ^ 2 := by
            apply Finset.sum_le_sum
            intro j _
            by_cases hji : j ≤ i
            · exact mul_le_mul_of_nonneg_right
                (hT.eigenvalues_antitone hn hji)
                (sq_nonneg _)
            · rw [ccmLeadingEigenSubspace_repr_eq_zero_of_not_le hT hn i j hx hji,
                norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, mul_zero]

/-- The `i`-th eigenvector belongs to the leading eigenspace. -/
theorem eigenvectorBasis_mem_ccmLeadingEigenSubspace {n : ℕ}
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (i : Fin n) :
    hT.eigenvectorBasis hn i ∈ ccmLeadingEigenSubspace hT hn i := by
  apply Submodule.subset_span
  exact ⟨i, Set.mem_Iic.mpr le_rfl, rfl⟩

/-- The `i`-th eigenvector attains its eigenvalue in the quadratic form. -/
theorem ccmHermitianQuadraticValue_eigenvectorBasis {n : ℕ}
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (i : Fin n) :
    ccmHermitianQuadraticValue T (hT.eigenvectorBasis hn i) =
      hT.eigenvalues hn i := by
  rw [ccmHermitianQuadraticValue, hT.apply_eigenvectorBasis]
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K,
    (hT.eigenvectorBasis hn).norm_eq_one]
  simp

/-- The independently defined `i`-th eigenvalue is the attained minimum on the
leading eigenspace. -/
theorem ccmLeadingEigenSubspace_isRayleighMinimum {n : ℕ}
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (i : Fin n) :
    CCMIsRayleighMinimum T (ccmLeadingEigenSubspace hT hn i)
      (hT.eigenvalues hn i) := by
  constructor
  · intro x hx hxnorm
    exact ccmLeadingEigenSubspace_eigenvalue_le_quadratic hT hn i hx hxnorm
  · exact ⟨hT.eigenvectorBasis hn i,
      eigenvectorBasis_mem_ccmLeadingEigenSubspace hT hn i,
      (hT.eigenvectorBasis hn).norm_eq_one i,
      ccmHermitianQuadraticValue_eigenvectorBasis hT hn i⟩

/-- The Hermitian quadratic value is continuous in finite dimension. -/
theorem continuous_ccmHermitianQuadraticValue (T : E →ₗ[ℂ] E) :
    Continuous (ccmHermitianQuadraticValue T) := by
  exact Complex.continuous_re.comp
    ((continuous_inner (𝕜 := ℂ)).comp
      (continuous_id.prodMk T.continuous_of_finiteDimensional))

/-- Every nonzero finite-dimensional subspace has an attained Rayleigh minimum. -/
theorem exists_ccmIsRayleighMinimum (T : E →ₗ[ℂ] E)
    (F : Submodule ℂ E) (hF : 0 < Module.finrank ℂ F) :
    ∃ r : ℝ, CCMIsRayleighMinimum T F r := by
  letI : Nontrivial F := nontrivial_of_finrank_pos hF
  let S : Set E := (F : Set E) ∩ Metric.sphere (0 : E) 1
  have hScompact : IsCompact S :=
    (isCompact_sphere (0 : E) 1).inter_left F.closed_of_finiteDimensional
  obtain ⟨z : F, hz⟩ : ∃ z : F, z ≠ 0 := exists_ne 0
  let x : E := ((‖(z : E)‖ : ℂ)⁻¹) • (z : E)
  have hxF : x ∈ F := F.smul_mem _ z.2
  have hxnorm : ‖x‖ = 1 := by
    exact norm_smul_inv_norm (Subtype.coe_ne_coe.mpr hz)
  have hSne : S.Nonempty := ⟨x, hxF, by simpa using hxnorm⟩
  obtain ⟨y, hyS, hymin⟩ := hScompact.exists_isMinOn hSne
    (continuous_ccmHermitianQuadraticValue T).continuousOn
  refine ⟨ccmHermitianQuadraticValue T y, ?_⟩
  constructor
  · intro u huF hunorm
    exact hymin ⟨huF, by simpa using hunorm⟩
  · exact ⟨y, hyS.1, by simpa using hyS.2, rfl⟩

/-- Every `(i+1)`-dimensional trial subspace contains a unit vector whose
quadratic value is at most the `i`-th decreasing eigenvalue.  This is the hard
dimension-count half of Courant--Fischer. -/
theorem exists_unit_mem_quadratic_le_eigenvalue {n : ℕ}
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (i : Fin n) (F : Submodule ℂ E)
    (hF : Module.finrank ℂ F = i.val + 1) :
    ∃ x : E, x ∈ F ∧ ‖x‖ = 1 ∧
      ccmHermitianQuadraticValue T x ≤ hT.eigenvalues hn i := by
  let b := hT.eigenvectorBasis hn
  let w : ℕ → E := fun m => if hm : m < n then b ⟨m, hm⟩ else 0
  have hdim : i.val < Module.finrank ℂ F := by omega
  obtain ⟨x, hxF, hxzero, hxorth⟩ :=
    ContinuousLinearMap.exists_mem_ne_zero_orthogonal_of_finrank_lt F w i.val hdim
  let y : E := ((‖x‖ : ℂ)⁻¹) • x
  have hynorm : ‖y‖ = 1 := norm_smul_inv_norm hxzero
  have hyF : y ∈ F := F.smul_mem _ hxF
  have hxrepr (j : Fin n) (hji : j < i) : b.repr x j = 0 := by
    rw [b.repr_apply_apply]
    have h := hxorth j.val hji
    change inner ℂ (w j.val) x = 0 at h
    simpa only [w, dif_pos j.isLt] using h
  have hyrepr (j : Fin n) (hji : j < i) : b.repr y j = 0 := by
    simp only [y, map_smul, PiLp.smul_apply, hxrepr j hji, smul_eq_mul, mul_zero]
  refine ⟨y, hyF, hynorm, ?_⟩
  rw [ccmHermitianQuadraticValue_eq_sum hT hn y]
  have hnormsum : ∑ j : Fin n, ‖b.repr y j‖ ^ 2 = ‖y‖ ^ 2 := by
    simpa only [b.repr_apply_apply] using b.sum_sq_norm_inner_right y
  calc
    ∑ j : Fin n, hT.eigenvalues hn j * ‖b.repr y j‖ ^ 2 ≤
        ∑ j : Fin n, hT.eigenvalues hn i * ‖b.repr y j‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hij : i ≤ j
          · exact mul_le_mul_of_nonneg_right
              (hT.eigenvalues_antitone hn hij) (sq_nonneg _)
          · have hji : j < i := lt_of_not_ge hij
            rw [hyrepr j hji, norm_zero,
              zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, mul_zero]
    _ = hT.eigenvalues hn i * (∑ j : Fin n, ‖b.repr y j‖ ^ 2) := by
          rw [Finset.mul_sum]
    _ = hT.eigenvalues hn i := by rw [hnormsum, hynorm]; ring

/-- Positive leading eigenvectors are orthogonal to every prescribed subspace
of the kernel. -/
theorem ccmLeadingEigenSubspace_le_orthogonal_of_le_ker {n : ℕ}
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (K : Submodule ℂ E) (hK : K ≤ LinearMap.ker T) (i : Fin n)
    (hi : 0 < hT.eigenvalues hn i) :
    ccmLeadingEigenSubspace hT hn i ≤ Kᗮ := by
  rw [ccmLeadingEigenSubspace]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, hji, rfl⟩
  apply (K.mem_orthogonal _).2
  intro y hyK
  have hTy : T y = 0 := LinearMap.mem_ker.mp (hK hyK)
  have hjpos : 0 < hT.eigenvalues hn j :=
    hi.trans_le (hT.eigenvalues_antitone hn hji)
  have hsym := hT y (hT.eigenvectorBasis hn j)
  rw [hTy, hT.apply_eigenvectorBasis, inner_zero_left, inner_smul_right] at hsym
  exact (mul_eq_zero.mp hsym.symm).resolve_left
    (Complex.ofReal_ne_zero.mpr hjpos.ne')

/-- **Connes--Consani Lemma `diracpm2` (exact source theorem).**

For a positive eigenvalue of a finite-dimensional self-adjoint operator, the
decreasing eigenvalue is the attained maximum of Rayleigh minima over
`(i+1)`-dimensional subspaces orthogonal to any prescribed subspace `K` of the
kernel. -/
theorem connesConsani_diracpm2 {n : ℕ} {T : E →ₗ[ℂ] E}
    (hT : T.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (K : Submodule ℂ E) (hK : K ≤ LinearMap.ker T) (i : Fin n)
    (hi : 0 < hT.eigenvalues hn i) :
    CCMIsConstrainedMinMax T (i.val + 1) K (hT.eigenvalues hn i) := by
  constructor
  · intro F hF _hFK
    obtain ⟨r, hr⟩ := exists_ccmIsRayleighMinimum T F (by omega)
    refine ⟨r, hr, ?_⟩
    obtain ⟨x, hxF, hxnorm, hxle⟩ :=
      exists_unit_mem_quadratic_le_eigenvalue hT hn i F hF
    exact (hr.1 x hxF hxnorm).trans hxle
  · exact ⟨ccmLeadingEigenSubspace hT hn i,
      ccmLeadingEigenSubspace_finrank hT hn i,
      ccmLeadingEigenSubspace_le_orthogonal_of_le_ker hT hn K hK i hi,
      ccmLeadingEigenSubspace_isRayleighMinimum hT hn i⟩

/-! ## Exact orthogonal compression -/

/-- Source compression `D_P = (1-P)D(1-P)`. -/
def ccmOrthogonalCompression (D P : E →ₗ[ℂ] E) : E →ₗ[ℂ] E :=
  (1 - P) * D * (1 - P)

omit [FiniteDimensional ℂ E] in
/-- The complementary projection is symmetric. -/
theorem isSymmetric_one_sub_of_isSymmetricProjection {P : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) : (1 - P).IsSymmetric :=
  LinearMap.IsSymmetric.one.sub hP.isSymmetric

omit [FiniteDimensional ℂ E] in
/-- Orthogonal compression of a symmetric operator is symmetric. -/
theorem isSymmetric_ccmOrthogonalCompression {D P : E →ₗ[ℂ] E}
    (hD : D.IsSymmetric) (hP : P.IsSymmetricProjection) :
    (ccmOrthogonalCompression D P).IsSymmetric := by
  let Q : E →ₗ[ℂ] E := 1 - P
  have hQ : Q.IsSymmetric := isSymmetric_one_sub_of_isSymmetricProjection hP
  intro x y
  change inner ℂ (Q (D (Q x))) y = inner ℂ x (Q (D (Q y)))
  rw [hQ, hD, hQ]

omit [FiniteDimensional ℂ E] in
/-- The range of the removed projection lies in the kernel of `D_P`. -/
theorem range_le_ker_ccmOrthogonalCompression {D P : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) :
    LinearMap.range P ≤ LinearMap.ker (ccmOrthogonalCompression D P) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  have hPP : P (P x) = P x := by
    simpa only [Module.End.mul_apply] using congr($hP.isIdempotentElem.eq x)
  simp [ccmOrthogonalCompression, Module.End.mul_apply, hPP]

omit [FiniteDimensional ℂ E] in
/-- A symmetric projection vanishes exactly on the orthogonal complement of
its range. -/
theorem isSymmetricProjection_apply_eq_zero_of_mem_range_orthogonal
    {P : E →ₗ[ℂ] E} (hP : P.IsSymmetricProjection) {x : E}
    (hx : x ∈ (LinearMap.range P)ᗮ) : P x = 0 := by
  obtain ⟨hproj, hPeq⟩ :=
    LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hP
  letI : (LinearMap.range P).HasOrthogonalProjection := hproj
  rw [hPeq]
  exact (Submodule.starProjection_apply_eq_zero_iff
    (K := LinearMap.range P)).mpr hx

omit [FiniteDimensional ℂ E] in
/-- On vectors orthogonal to the removed range, the compressed and original
quadratic values coincide exactly. -/
theorem ccmOrthogonalCompression_quadratic_eq {D P : E →ₗ[ℂ] E}
    (hP : P.IsSymmetricProjection) {x : E}
    (hx : x ∈ (LinearMap.range P)ᗮ) :
    ccmHermitianQuadraticValue (ccmOrthogonalCompression D P) x =
      ccmHermitianQuadraticValue D x := by
  let Q : E →ₗ[ℂ] E := 1 - P
  have hQ : Q.IsSymmetric := isSymmetric_one_sub_of_isSymmetricProjection hP
  have hPx : P x = 0 :=
    isSymmetricProjection_apply_eq_zero_of_mem_range_orthogonal hP hx
  have hQx : Q x = x := by simp [Q, hPx]
  rw [ccmHermitianQuadraticValue, ccmHermitianQuadraticValue]
  change Complex.re (inner ℂ x (Q (D (Q x)))) = Complex.re (inner ℂ x (D x))
  rw [← hQ x (D (Q x)), hQx]

omit [FiniteDimensional ℂ E] in
/-- Source grading law `diracpm`: compression by a projection commuting with
the grading preserves anticommutation with the Dirac operator. -/
theorem ccmOrthogonalCompression_anticommutes_grading
    (D P Γ : E →ₗ[ℂ] E)
    (hΓD : Γ * D = -(D * Γ)) (hΓP : Γ * P = P * Γ) :
    Γ * ccmOrthogonalCompression D P =
      -(ccmOrthogonalCompression D P * Γ) := by
  let Q : E →ₗ[ℂ] E := 1 - P
  have hΓQ : Γ * Q = Q * Γ := by
    dsimp [Q]
    rw [mul_sub, sub_mul, mul_one, one_mul, hΓP]
  calc
    Γ * ccmOrthogonalCompression D P = Γ * (Q * D * Q) := by rfl
    _ = (Γ * Q) * D * Q := by simp only [mul_assoc]
    _ = (Q * Γ) * D * Q := by rw [hΓQ]
    _ = Q * (Γ * D) * Q := by simp only [mul_assoc]
    _ = Q * (-(D * Γ)) * Q := by rw [hΓD]
    _ = -(Q * D * (Γ * Q)) := by simp only [mul_neg, neg_mul, mul_assoc]
    _ = -(Q * D * (Q * Γ)) := by rw [hΓQ]
    _ = -((Q * D * Q) * Γ) := by simp only [mul_assoc]
    _ = -(ccmOrthogonalCompression D P * Γ) := by rfl

omit [FiniteDimensional ℂ E] in
/-- Rayleigh minima are extensional in the quadratic value on their subspace. -/
theorem ccmIsRayleighMinimum_congr {S T : E →ₗ[ℂ] E}
    {F : Submodule ℂ E} {r : ℝ}
    (hST : ∀ x : E, x ∈ F →
      ccmHermitianQuadraticValue S x = ccmHermitianQuadraticValue T x) :
    CCMIsRayleighMinimum S F r ↔ CCMIsRayleighMinimum T F r := by
  constructor
  · rintro ⟨hlow, ⟨x, hxF, hxnorm, hxeq⟩⟩
    constructor
    · intro y hyF hynorm
      rw [← hST y hyF]
      exact hlow y hyF hynorm
    · exact ⟨x, hxF, hxnorm, (hST x hxF).symm.trans hxeq⟩
  · rintro ⟨hlow, ⟨x, hxF, hxnorm, hxeq⟩⟩
    constructor
    · intro y hyF hynorm
      rw [hST y hyF]
      exact hlow y hyF hynorm
    · exact ⟨x, hxF, hxnorm, (hST x hxF).trans hxeq⟩

omit [FiniteDimensional ℂ E] in
/-- Constrained max--min values are extensional on the constraining
orthogonal complement. -/
theorem ccmIsConstrainedMinMax_congr {S T : E →ₗ[ℂ] E}
    {k : ℕ} {K : Submodule ℂ E} {μ : ℝ}
    (hST : ∀ x : E, x ∈ Kᗮ →
      ccmHermitianQuadraticValue S x = ccmHermitianQuadraticValue T x) :
    CCMIsConstrainedMinMax S k K μ ↔ CCMIsConstrainedMinMax T k K μ := by
  constructor
  · rintro ⟨hall, ⟨F, hFdim, hFK, hFmin⟩⟩
    constructor
    · intro G hGdim hGK
      obtain ⟨r, hr, hrle⟩ := hall G hGdim hGK
      exact ⟨r, (ccmIsRayleighMinimum_congr
        (fun x hx => hST x (hGK hx))).mp hr, hrle⟩
    · exact ⟨F, hFdim, hFK, (ccmIsRayleighMinimum_congr
        (fun x hx => hST x (hFK hx))).mp hFmin⟩
  · rintro ⟨hall, ⟨F, hFdim, hFK, hFmin⟩⟩
    constructor
    · intro G hGdim hGK
      obtain ⟨r, hr, hrle⟩ := hall G hGdim hGK
      exact ⟨r, (ccmIsRayleighMinimum_congr
        (fun x hx => hST x (hGK hx))).mpr hr, hrle⟩
    · exact ⟨F, hFdim, hFK, (ccmIsRayleighMinimum_congr
        (fun x hx => hST x (hFK hx))).mpr hFmin⟩

/-- **Connes--Consani Proposition `diracpm3(i)` (exact source theorem).**

The positive eigenvalues of `D_P=QDQ` are the constrained max--min values of
the *uncompressed* quadratic form of `D` on subspaces orthogonal to the range
of `P`. -/
theorem connesConsani_diracpm3_i {n : ℕ} {D P : E →ₗ[ℂ] E}
    (hD : D.IsSymmetric) (hP : P.IsSymmetricProjection)
    (hn : Module.finrank ℂ E = n) (i : Fin n)
    (hi : 0 < (isSymmetric_ccmOrthogonalCompression hD hP).eigenvalues hn i) :
    CCMIsConstrainedMinMax D (i.val + 1) (LinearMap.range P)
      ((isSymmetric_ccmOrthogonalCompression hD hP).eigenvalues hn i) := by
  apply (ccmIsConstrainedMinMax_congr
    (fun x hx => ccmOrthogonalCompression_quadratic_eq hP hx)).mp
  exact connesConsani_diracpm2
    (isSymmetric_ccmOrthogonalCompression hD hP) hn (LinearMap.range P)
    (range_le_ker_ccmOrthogonalCompression hP) i hi

omit [FiniteDimensional ℂ E] in
/-- An attained Rayleigh minimum has a unique value. -/
theorem ccmIsRayleighMinimum_unique {T : E →ₗ[ℂ] E}
    {F : Submodule ℂ E} {r s : ℝ}
    (hr : CCMIsRayleighMinimum T F r)
    (hs : CCMIsRayleighMinimum T F s) : r = s := by
  obtain ⟨x, hxF, hxnorm, hxeq⟩ := hr.2
  obtain ⟨y, hyF, hynorm, hyeq⟩ := hs.2
  apply le_antisymm
  · simpa [hyeq] using hr.1 y hyF hynorm
  · simpa [hxeq] using hs.1 x hxF hxnorm

/-- **Connes--Consani Proposition `diracpm3(ii)` (exact source theorem).**

Increasing the removed projection can only decrease every positive compressed
eigenvalue (at a common decreasing index). -/
theorem connesConsani_diracpm3_ii {n : ℕ} {D P₁ P₂ : E →ₗ[ℂ] E}
    (hD : D.IsSymmetric) (hP₁ : P₁.IsSymmetricProjection)
    (hP₂ : P₂.IsSymmetricProjection)
    (hP₁P₂ : LinearMap.range P₁ ≤ LinearMap.range P₂)
    (hn : Module.finrank ℂ E = n) (i : Fin n)
    (hi₁ : 0 < (isSymmetric_ccmOrthogonalCompression hD hP₁).eigenvalues hn i)
    (hi₂ : 0 < (isSymmetric_ccmOrthogonalCompression hD hP₂).eigenvalues hn i) :
    (isSymmetric_ccmOrthogonalCompression hD hP₂).eigenvalues hn i ≤
      (isSymmetric_ccmOrthogonalCompression hD hP₁).eigenvalues hn i := by
  let μ₁ := (isSymmetric_ccmOrthogonalCompression hD hP₁).eigenvalues hn i
  let μ₂ := (isSymmetric_ccmOrthogonalCompression hD hP₂).eigenvalues hn i
  have hminmax₁ := connesConsani_diracpm3_i hD hP₁ hn i hi₁
  have hminmax₂ := connesConsani_diracpm3_i hD hP₂ hn i hi₂
  obtain ⟨F₂, hF₂dim, hF₂P₂, hF₂min⟩ := hminmax₂.2
  have hF₂P₁ : F₂ ≤ (LinearMap.range P₁)ᗮ :=
    fun x hx => Submodule.orthogonal_le hP₁P₂ (hF₂P₂ hx)
  obtain ⟨r, hrmin, hrle⟩ := hminmax₁.1 F₂ hF₂dim hF₂P₁
  have hrequal : r = μ₂ := ccmIsRayleighMinimum_unique hrmin hF₂min
  simpa [μ₁, μ₂, hrequal] using hrle

/-! ## Literal Hermitian-matrix endpoints -/

/-- Matrix-level source compression `D_P=(1-P)D(1-P)`. -/
def ccmMatrixOrthogonalCompression {N : ℕ}
    (D P : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (1 - P) * D * (1 - P)

/-- The literal matrix compression is Hermitian. -/
theorem isHermitian_ccmMatrixOrthogonalCompression {N : ℕ}
    {D P : Matrix (Fin N) (Fin N) ℂ}
    (hD : D.IsHermitian) (hP : P.IsHermitian) :
    (ccmMatrixOrthogonalCompression D P).IsHermitian := by
  let Q : Matrix (Fin N) (Fin N) ℂ := 1 - P
  have hQ : Q.IsHermitian := Matrix.isHermitian_one.sub hP
  change (Q * D * Q).IsHermitian
  simpa only [hQ.eq] using Matrix.isHermitian_conjTranspose_mul_mul Q hD

/-- A Hermitian idempotent matrix becomes a symmetric projection on literal
Euclidean space. -/
theorem isSymmetricProjection_toEuclideanLin {N : ℕ}
    {P : Matrix (Fin N) (Fin N) ℂ}
    (hP : P.IsHermitian) (hPid : P * P = P) :
    (Matrix.toEuclideanLin P).IsSymmetricProjection := by
  constructor
  · rw [IsIdempotentElem]
    change Matrix.toEuclideanLin P ∘ₗ Matrix.toEuclideanLin P =
      Matrix.toEuclideanLin P
    rw [← Matrix.toLpLin_mul_same, hPid]
  · exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hP

/-- Matrix compression and operator compression agree, not merely up to
spectrum. -/
theorem toEuclideanLin_ccmMatrixOrthogonalCompression {N : ℕ}
    (D P : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.toEuclideanLin (ccmMatrixOrthogonalCompression D P) =
      ccmOrthogonalCompression (Matrix.toEuclideanLin D)
        (Matrix.toEuclideanLin P) := by
  simp [ccmMatrixOrthogonalCompression, ccmOrthogonalCompression,
    Matrix.toLpLin_mul_same, Module.End.mul_eq_comp, Module.End.one_eq_id]

/-- Matrix projection order (`P₂P₁=P₁`) gives inclusion of literal ranges. -/
theorem range_toEuclideanLin_mono_of_mul_eq {N : ℕ}
    {P₁ P₂ : Matrix (Fin N) (Fin N) ℂ} (hP₁P₂ : P₂ * P₁ = P₁) :
    LinearMap.range (Matrix.toEuclideanLin P₁) ≤
      LinearMap.range (Matrix.toEuclideanLin P₂) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨Matrix.toEuclideanLin P₁ x, ?_⟩
  simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply] using
    congrArg (fun A : Matrix (Fin N) (Fin N) ℂ => Matrix.toEuclideanLin A x) hP₁P₂

/-- **Connes--Consani `diracpm2`, literal matrix form.**

For a Hermitian matrix and a subspace of its literal kernel, each positive
decreasing matrix eigenvalue is the attained constrained Courant--Fischer
max--min value. -/
theorem connesConsani_diracpm2_matrix {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (K : Submodule ℂ (EuclideanSpace ℂ (Fin N)))
    (hK : K ≤ LinearMap.ker (Matrix.toEuclideanLin A))
    (i : Fin (Fintype.card (Fin N))) (hi : 0 < hA.eigenvalues₀ i) :
    CCMIsConstrainedMinMax (Matrix.toEuclideanLin A) (i.val + 1) K
      (hA.eigenvalues₀ i) := by
  exact connesConsani_diracpm2
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    finrank_euclideanSpace K hK i hi

/-- **Connes--Consani `diracpm3(i)`, literal matrix form.**

Here the eigenvalue is exactly `Matrix.IsHermitian.eigenvalues₀` of the source
matrix `(1-P)D(1-P)`, while the Rayleigh minima use the uncompressed matrix
`D`. -/
theorem connesConsani_diracpm3_i_matrix {N : ℕ}
    {D P : Matrix (Fin N) (Fin N) ℂ}
    (hD : D.IsHermitian) (hP : P.IsHermitian) (hPid : P * P = P)
    (i : Fin (Fintype.card (Fin N)))
    (hi : 0 < (isHermitian_ccmMatrixOrthogonalCompression hD hP).eigenvalues₀ i) :
    CCMIsConstrainedMinMax (Matrix.toEuclideanLin D) (i.val + 1)
      (LinearMap.range (Matrix.toEuclideanLin P))
      ((isHermitian_ccmMatrixOrthogonalCompression hD hP).eigenvalues₀ i) := by
  let hPlin := isSymmetricProjection_toEuclideanLin hP hPid
  let C := ccmMatrixOrthogonalCompression D P
  let hC : C.IsHermitian := isHermitian_ccmMatrixOrthogonalCompression hD hP
  let hClin : (Matrix.toEuclideanLin C).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hC
  have hmap : Matrix.toEuclideanLin C =
      ccmOrthogonalCompression (Matrix.toEuclideanLin D)
        (Matrix.toEuclideanLin P) :=
    toEuclideanLin_ccmMatrixOrthogonalCompression D P
  have hker : LinearMap.range (Matrix.toEuclideanLin P) ≤
      LinearMap.ker (Matrix.toEuclideanLin C) := by
    rw [hmap]
    exact range_le_ker_ccmOrthogonalCompression hPlin
  have hraw : CCMIsConstrainedMinMax (Matrix.toEuclideanLin C) (i.val + 1)
      (LinearMap.range (Matrix.toEuclideanLin P))
      (hClin.eigenvalues finrank_euclideanSpace i) :=
    connesConsani_diracpm2 hClin finrank_euclideanSpace _ hker i hi
  apply (ccmIsConstrainedMinMax_congr (S := Matrix.toEuclideanLin C)
    (T := Matrix.toEuclideanLin D) (fun x hx => ?_)).mp hraw
  rw [hmap]
  exact ccmOrthogonalCompression_quadratic_eq hPlin hx

/-- **Connes--Consani `diracpm3(ii)`, literal matrix form.**

For Hermitian idempotents ordered by `P₂P₁=P₁`, the positive decreasing
eigenvalues of the literal compressed matrices are monotone. -/
theorem connesConsani_diracpm3_ii_matrix {N : ℕ}
    {D P₁ P₂ : Matrix (Fin N) (Fin N) ℂ}
    (hD : D.IsHermitian)
    (hP₁ : P₁.IsHermitian) (hP₁id : P₁ * P₁ = P₁)
    (hP₂ : P₂.IsHermitian) (hP₂id : P₂ * P₂ = P₂)
    (hP₁P₂ : P₂ * P₁ = P₁) (i : Fin (Fintype.card (Fin N)))
    (hi₁ : 0 < (isHermitian_ccmMatrixOrthogonalCompression hD hP₁).eigenvalues₀ i)
    (hi₂ : 0 < (isHermitian_ccmMatrixOrthogonalCompression hD hP₂).eigenvalues₀ i) :
    (isHermitian_ccmMatrixOrthogonalCompression hD hP₂).eigenvalues₀ i ≤
      (isHermitian_ccmMatrixOrthogonalCompression hD hP₁).eigenvalues₀ i := by
  have hminmax₁ := connesConsani_diracpm3_i_matrix hD hP₁ hP₁id i hi₁
  have hminmax₂ := connesConsani_diracpm3_i_matrix hD hP₂ hP₂id i hi₂
  obtain ⟨F₂, hF₂dim, hF₂P₂, hF₂min⟩ := hminmax₂.2
  have hrange : LinearMap.range (Matrix.toEuclideanLin P₁) ≤
      LinearMap.range (Matrix.toEuclideanLin P₂) :=
    range_toEuclideanLin_mono_of_mul_eq hP₁P₂
  have hF₂P₁ : F₂ ≤ (LinearMap.range (Matrix.toEuclideanLin P₁))ᗮ :=
    fun x hx => Submodule.orthogonal_le hrange (hF₂P₂ hx)
  obtain ⟨r, hrmin, hrle⟩ := hminmax₁.1 F₂ hF₂dim hF₂P₁
  have hrequal : r =
      (isHermitian_ccmMatrixOrthogonalCompression hD hP₂).eigenvalues₀ i :=
    ccmIsRayleighMinimum_unique hrmin hF₂min
  simpa [hrequal] using hrle

end RHTower
