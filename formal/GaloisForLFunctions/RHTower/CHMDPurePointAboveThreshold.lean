import GaloisForLFunctions.RHTower.CHMDNoWeylAboveThreshold
import GaloisForLFunctions.RHTower.CHMDWeakCoreAdmission

/-!
# The spectrum of the arithmetic resolvent above the threshold is pure point

Every point `μ > 1/2` of the spectrum of the arithmetic resolvent `R` is an eigenvalue; every
eigenspace above `1/2` is finite-dimensional; and for every `ε > 0` only finitely many eigenvalues
lie in `[1/2 + ε, 1]`.

Mechanism. A symmetric bounded operator on a real Hilbert space has approximate eigenvectors at every
spectral point (Weyl's criterion: a symmetric operator bounded below is a unit). Bounded sequences
have weakly convergent subsequences (the mass space is second countable); the weak limit of a unit
approximate eigenvector sequence at `μ > 1/2` is nonzero (otherwise the subsequence is a weakly null
Weyl sequence above the threshold, which does not exist) and is an eigenvector. Infinitely many
eigenvalues in `[1/2+ε, 1]` would give an orthonormal eigenfamily with a convergent subsequence of
eigenvalues, hence a weakly null Weyl sequence at a level `≥ 1/2 + ε`.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump

/-! ## Weyl's criterion for symmetric bounded operators on a real Hilbert space -/

/-- A symmetric bounded operator on a real Hilbert space that is bounded below is a unit. -/
theorem isUnit_of_symmetric_of_bounded_below {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {S : H →L[ℝ] H}
    (hS : ∀ x y, ⟪S x, y⟫_ℝ = ⟪x, S y⟫_ℝ) {m : ℝ} (hm0 : 0 < m) (hm : ∀ x, m * ‖x‖ ≤ ‖S x‖) :
    IsUnit S := by
  have hanti : AntilipschitzWith ⟨m⁻¹, by positivity⟩ S := by
    refine S.antilipschitz_of_bound fun x => ?_
    show ‖x‖ ≤ m⁻¹ * ‖S x‖
    rw [← div_eq_inv_mul, le_div_iff₀ hm0]
    linarith [hm x]
  have hinj : Function.Injective S := hanti.injective
  have hclosed : IsClosed (Set.range S) := hanti.isClosed_range S.uniformContinuous
  have hdense : (LinearMap.range (S : H →ₗ[ℝ] H)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    have h1 : ⟪S (S y), y⟫_ℝ = 0 := hy _ (LinearMap.mem_range_self (S : H →ₗ[ℝ] H) (S y))
    rw [hS] at h1
    have hSy : S y = 0 := inner_self_eq_zero.mp h1
    exact hinj (by rw [hSy, map_zero])
  have hrange : LinearMap.range (S : H →ₗ[ℝ] H) = ⊤ := by
    rw [← hdense]
    symm
    apply IsClosed.submodule_topologicalClosure_eq
    rw [LinearMap.coe_range]
    exact hclosed
  have hsurj : Function.Surjective S := LinearMap.range_eq_top.mp hrange
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩

/-- **Weyl's criterion.** Every spectral point of a symmetric bounded operator on a real Hilbert
space admits a sequence of unit approximate eigenvectors. -/
theorem exists_approx_eigen_of_mem_spectrum {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {T : H →L[ℝ] H}
    (hT : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ) {μ : ℝ} (hμ : μ ∈ spectrum ℝ T) :
    ∃ w : ℕ → H, (∀ n, ‖w n‖ = 1) ∧ Tendsto (fun n => ‖T (w n) - μ • w n‖) atTop (𝓝 0) := by
  by_contra hcon
  have hbdd : ∃ m : ℝ, 0 < m ∧ ∀ x, m * ‖x‖ ≤ ‖T x - μ • x‖ := by
    by_contra hno
    have hseq : ∀ n : ℕ, ∃ u : H, ‖u‖ = 1 ∧ ‖T u - μ • u‖ < 1 / ((n : ℝ) + 1) := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hx : ∃ x : H, ‖T x - μ • x‖ < 1 / ((n : ℝ) + 1) * ‖x‖ := by
        by_contra hall
        apply hno
        refine ⟨1 / ((n : ℝ) + 1), hpos, fun x => ?_⟩
        by_contra hlt
        rw [not_le] at hlt
        exact hall ⟨x, hlt⟩
      obtain ⟨x, hx⟩ := hx
      have hx0 : x ≠ 0 := by
        intro h
        rw [h, norm_zero, mul_zero, smul_zero, map_zero, sub_zero, norm_zero] at hx
        exact lt_irrefl _ hx
      have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      refine ⟨‖x‖⁻¹ • x, norm_smul_inv_norm hx0, ?_⟩
      have hsplit : T (‖x‖⁻¹ • x) - μ • (‖x‖⁻¹ • x) = ‖x‖⁻¹ • (T x - μ • x) := by
        rw [map_smul, smul_sub, smul_comm]
      rw [hsplit, norm_smul, norm_inv, norm_norm, inv_mul_lt_iff₀ hxn, mul_comm]
      exact hx
    choose u hu1 hu2 using hseq
    exact hcon ⟨u, hu1, squeeze_zero (fun n => norm_nonneg _) (fun n => (hu2 n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat⟩
  obtain ⟨m, hm0, hm⟩ := hbdd
  set S : H →L[ℝ] H := algebraMap ℝ (H →L[ℝ] H) μ - T with hS_def
  have hSx : ∀ x, S x = μ • x - T x := by
    intro x
    simp only [hS_def, sub_apply, Algebra.algebraMap_eq_smul_one,
      smul_apply, one_apply_eq_self]
  have hSsym : ∀ x y, ⟪S x, y⟫_ℝ = ⟪x, S y⟫_ℝ := by
    intro x y
    rw [hSx, hSx, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hT]
  have hSlow : ∀ x, m * ‖x‖ ≤ ‖S x‖ := by
    intro x
    rw [hSx, norm_sub_rev]
    exact hm x
  exact (spectrum.mem_iff.mp hμ) (isUnit_of_symmetric_of_bounded_below hSsym hm0 hSlow)

/-- An eigenvalue of a bounded operator is a spectral point. -/
theorem mem_spectrum_of_eigenvector {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {T : H →L[ℝ] H} {μ : ℝ} {x : H} (hx0 : x ≠ 0) (hx : T x = μ • x) :
    μ ∈ spectrum ℝ T := by
  rw [spectrum.mem_iff]
  intro hu
  have hinj : Function.Injective (algebraMap ℝ (H →L[ℝ] H) μ - T) :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
  apply hx0
  apply hinj
  simp only [sub_apply, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply_eq_self, hx, sub_self, map_zero]

/-! ## Eigenvectors above the threshold -/

/-- Eigenvalues of the arithmetic resolvent are at most `1`. -/
theorem eigenvalue_le_one {μ : ℝ} {x : MassSpace} (hx0 : x ≠ 0) (hx : resolvent x = μ • x) :
    μ ≤ 1 := by
  have h1 : ‖resolvent x‖ ≤ ‖x‖ :=
    (resolvent.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) norm_resolvent_le)
  rw [hx, norm_smul, Real.norm_eq_abs] at h1
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have h2 : |μ| ≤ 1 := le_of_mul_le_mul_right (by linarith) hpos
  exact (le_abs_self μ).trans h2

/-- **Unit approximate eigenvectors above the threshold converge weakly, along a subsequence, to a
genuine eigenvector.** -/
theorem exists_eigenvector_of_approx_eigen_above_half {μ : ℝ} (hμ : 1 / 2 < μ) (w : ℕ → MassSpace)
    (hw1 : ∀ n, ‖w n‖ = 1) (hw : Tendsto (fun n => ‖resolvent (w n) - μ • w n‖) atTop (𝓝 0)) :
    ∃ x : MassSpace, x ≠ 0 ∧ resolvent x = μ • x := by
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology MassSpace := Lp.SecondCountableTopology
  obtain ⟨x, φ, hφ, hweak⟩ := exists_real_weak_subseq w 1 fun n => (hw1 n).le
  have hw' : Tendsto (fun n => ‖resolvent (w (φ n)) - μ • w (φ n)‖) atTop (𝓝 0) :=
    hw.comp hφ.tendsto_atTop
  refine ⟨x, ?_, ?_⟩
  · intro hx0
    rw [hx0] at hweak
    refine no_weakly_null_weyl_above_half hμ (fun n => w (φ n)) (fun n => hw1 _) ?_ hw'
    intro k
    simpa using hweak k
  · apply ext_inner_right ℝ
    intro k
    have h1 : Tendsto (fun n => ⟪resolvent (w (φ n)) - μ • w (φ n), k⟫_ℝ) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => norm_inner_le_norm _ _) ?_
      simpa using hw'.mul_const ‖k‖
    have ha : Tendsto (fun n => ⟪resolvent (w (φ n)), k⟫_ℝ) atTop (𝓝 ⟪resolvent x, k⟫_ℝ) := by
      have h := hweak (resolvent k)
      rw [← resolvent_symm] at h
      refine Filter.Tendsto.congr (fun n => ?_) h
      exact (resolvent_symm _ _).symm
    have hb : Tendsto (fun n => μ * ⟪w (φ n), k⟫_ℝ) atTop (𝓝 (μ * ⟪x, k⟫_ℝ)) :=
      (hweak k).const_mul μ
    have h2 : Tendsto (fun n => ⟪resolvent (w (φ n)) - μ • w (φ n), k⟫_ℝ) atTop
        (𝓝 (⟪resolvent x, k⟫_ℝ - μ * ⟪x, k⟫_ℝ)) := by
      refine Filter.Tendsto.congr (fun n => ?_) (ha.sub hb)
      rw [inner_sub_left, real_inner_smul_left]
    have h3 := tendsto_nhds_unique h2 h1
    rw [real_inner_smul_left]
    linarith

/-- **Pure point spectrum above the threshold.** Every spectral point `μ > 1/2` of the arithmetic
resolvent is an eigenvalue. -/
theorem exists_eigenvector_of_mem_spectrum_above_half {μ : ℝ} (hμ : 1 / 2 < μ)
    (hμs : μ ∈ spectrum ℝ resolvent) : ∃ x : MassSpace, x ≠ 0 ∧ resolvent x = μ • x := by
  obtain ⟨w, hw1, hw⟩ := exists_approx_eigen_of_mem_spectrum resolvent_symm hμs
  exact exists_eigenvector_of_approx_eigen_above_half hμ w hw1 hw

/-- Above the threshold, spectrum and eigenvalues coincide. -/
theorem mem_spectrum_iff_hasEigenvalue_above_half {μ : ℝ} (hμ : 1 / 2 < μ) :
    μ ∈ spectrum ℝ resolvent ↔
      Module.End.HasEigenvalue (resolvent : MassSpace →ₗ[ℝ] MassSpace) μ := by
  constructor
  · intro h
    obtain ⟨x, hx0, hx⟩ := exists_eigenvector_of_mem_spectrum_above_half hμ h
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hx, hx0⟩)
  · intro h
    obtain ⟨x, hx⟩ := Module.End.HasEigenvalue.exists_hasEigenvector h
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
    exact mem_spectrum_of_eigenvector hx.2 hx.1

/-! ## Local finiteness of the eigenvalues above the threshold -/

theorem resolvent_isSymmetric : (resolvent : MassSpace →ₗ[ℝ] MassSpace).IsSymmetric :=
  fun a b => resolvent_symm a b

/-- **Only finitely many eigenvalues in `[1/2 + ε, 1]`.** -/
theorem finite_eigenvalues_above {ε : ℝ} (hε : 0 < ε) :
    {μ : ℝ | 1 / 2 + ε ≤ μ ∧ Module.End.HasEigenvalue (resolvent : MassSpace →ₗ[ℝ] MassSpace) μ}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  set S := {μ : ℝ | 1 / 2 + ε ≤ μ ∧ Module.End.HasEigenvalue (resolvent : MassSpace →ₗ[ℝ] MassSpace) μ}
    with hS
  let f : ℕ ↪ S := hinf.natEmbedding
  have hfS : ∀ n, ((f n : S) : ℝ) ∈ S := fun n => (f n).2
  have hvec : ∀ n, ∃ x : MassSpace, ‖x‖ = 1 ∧ resolvent x = ((f n : S) : ℝ) • x := by
    intro n
    obtain ⟨x, hx⟩ := Module.End.HasEigenvalue.exists_hasEigenvector (hfS n).2
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
    refine ⟨‖x‖⁻¹ • x, norm_smul_inv_norm hx.2, ?_⟩
    have h1 : resolvent x = ((f n : S) : ℝ) • x := by
      have h := hx.1
      rwa [ContinuousLinearMap.coe_coe] at h
    rw [map_smul, h1, smul_comm]
  choose x hx1 hx2 using hvec
  have horth : Orthonormal ℝ x := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [hx1]
    · simp only [hij, if_false]
      have hne : ((f i : S) : ℝ) ≠ ((f j : S) : ℝ) := fun h => hij (f.injective (Subtype.ext h))
      exact resolvent_isSymmetric.orthogonalFamily_eigenspaces hne
        ⟨x i, Module.End.mem_eigenspace_iff.mpr (hx2 i)⟩
        ⟨x j, Module.End.mem_eigenspace_iff.mpr (hx2 j)⟩
  have hmem : ∀ n, ((f n : S) : ℝ) ∈ Icc (1 / 2 + ε) 1 := fun n =>
    ⟨(hfS n).1, eigenvalue_le_one (by rw [← norm_ne_zero_iff, hx1]; exact one_ne_zero) (hx2 n)⟩
  obtain ⟨μ, hμI, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
  have hμ : 1 / 2 < μ := by linarith [hμI.1]
  refine no_weakly_null_weyl_above_half hμ (x ∘ φ) (fun n => hx1 _)
    (weaklyNull_of_orthonormal (horth.comp φ hφ.injective)) ?_
  have hdef : ∀ n, ‖resolvent ((x ∘ φ) n) - μ • (x ∘ φ) n‖ = |((f (φ n) : S) : ℝ) - μ| := by
    intro n
    simp only [Function.comp_apply]
    rw [hx2, ← sub_smul, norm_smul, hx1, mul_one, Real.norm_eq_abs]
  simp only [hdef]
  have h := (hlim.sub_const μ).abs
  simpa using h

/-! ## Finite multiplicity -/

theorem isClosed_eigenspace (μ : ℝ) :
    IsClosed ((Module.End.eigenspace (resolvent : MassSpace →ₗ[ℝ] MassSpace) μ : Submodule ℝ MassSpace)
      : Set MassSpace) := by
  have h : ((Module.End.eigenspace (resolvent : MassSpace →ₗ[ℝ] MassSpace) μ :
      Submodule ℝ MassSpace) : Set MassSpace) = {x | resolvent x = μ • x} := by
    ext x
    exact Module.End.mem_eigenspace_iff
  rw [h]
  exact isClosed_eq resolvent.continuous (continuous_id.const_smul μ)

/-- **Finite multiplicity.** Every eigenspace of the arithmetic resolvent above `1/2` is
finite-dimensional. -/
theorem finiteDimensional_eigenspace_above_half {μ : ℝ} (hμ : 1 / 2 < μ) :
    FiniteDimensional ℝ (Module.End.eigenspace (resolvent : MassSpace →ₗ[ℝ] MassSpace) μ) := by
  set K : Submodule ℝ MassSpace :=
    Module.End.eigenspace (resolvent : MassSpace →ₗ[ℝ] MassSpace) μ with hK
  haveI : CompleteSpace K := (isClosed_eigenspace μ).completeSpace_coe
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis ℝ K
  by_cases hw : w.Finite
  · have hrange : Set.range b = w := by
      rw [hb]
      exact Subtype.range_coe
    have hfin : (Set.range b).Finite := by
      rw [hrange]
      exact hw
    haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range b)) :=
      FiniteDimensional.span_of_finite ℝ hfin
    have hspan : Submodule.span ℝ (Set.range b) = ⊤ := by
      have h1 := b.dense_span
      rwa [(Submodule.closed_of_finiteDimensional _).submodule_topologicalClosure_eq] at h1
    exact (LinearEquiv.ofTop _ hspan).finiteDimensional
  · exfalso
    have hinf : w.Infinite := hw
    let f : ℕ ↪ w := hinf.natEmbedding
    have h1 : Orthonormal ℝ (b ∘ f) := b.orthonormal.comp f f.injective
    have horth : Orthonormal ℝ (fun n => ((b (f n) : K) : MassSpace)) :=
      (K.subtypeₗᵢ.orthonormal_comp_iff (v := b ∘ f)).mpr h1
    exact no_orthonormal_eigenfamily_above_half hμ _ horth fun n =>
      Module.End.mem_eigenspace_iff.mp (b (f n)).2

end RHTower.CHMDPolar
