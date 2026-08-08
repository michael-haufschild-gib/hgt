/-
# The zeros of the entire regularized determinant are reciprocal eigenvalues

Assembling the finite-section chain: the entire determinant is the uniform-on-discs limit of the
block determinants, whose zeros are the reciprocal block eigenvalues (Hurwitz); the block
eigenvectors lift to `ℓ²` eigenvectors of the truncated operators, which converge to the kernel
operator in operator norm; and a limit of eigenvalues of operators converging to a compact one is
an eigenvalue of the limit.

The only new bookkeeping is producing a *single* convergent family of block eigenvalues out of the
family-of-radii statement Hurwitz gives.  That is done by taking, for each block, the point of its
spectrum nearest to `1/z₀`: the spectrum is closed, `ℂ` is proper, so the nearest point exists, and
Hurwitz says its distance tends to zero.

Main result: `exists_eigenvector_of_entireDet2_eq_zero`.
-/
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantEigenvalues
import GaloisForLFunctions.HTGeometry.HilbertSchmidtBlockEigenvector
import GaloisForLFunctions.HTGeometry.CompactOperatorSpectrumLimit
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt Metric Filter Matrix

variable {ι : Type*} [DecidableEq ι]

/-! ## The spectrum of a block -/

/-- The spectrum of the finite block, as the zero set of its characteristic polynomial. -/
def blockSpectrum (K : ι × ι → ℂ) (s : Finset ι) : Set ℂ :=
  {μ | Polynomial.eval μ (blockMatrix K s).charpoly = 0}

theorem isClosed_blockSpectrum (K : ι × ι → ℂ) (s : Finset ι) : IsClosed (blockSpectrum K s) :=
  isClosed_eq (Polynomial.continuous _) continuous_const

theorem scalar_mulVec {s : Finset ι} (μ : ℂ) (v : ↥s → ℂ) :
    (Matrix.scalar ↥s μ) *ᵥ v = μ • v := by
  ext i
  simp [Matrix.scalar, Matrix.mulVec, Matrix.diagonal, dotProduct]

theorem mem_blockSpectrum_iff (K : ι × ι → ℂ) (s : Finset ι) (μ : ℂ) :
    μ ∈ blockSpectrum K s ↔ ∃ v : ↥s → ℂ, v ≠ 0 ∧ (blockMatrix K s) *ᵥ v = μ • v := by
  rw [blockSpectrum, Set.mem_setOf_eq, Matrix.eval_charpoly]
  constructor
  · intro h
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, scalar_mulVec] at hv
    exact (sub_eq_zero.mp hv).symm
  · rintro ⟨v, hv0, hv⟩
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, scalar_mulVec, hv, sub_self]

/-! ## Isolation of the zeros -/

theorem eventually_entireDet2_ne_zero {K : ι × ι → ℂ} (hK : IsHS K) (z₀ : ℂ) :
    ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, entireDet2 K z ≠ 0 := by
  have hA : AnalyticOnNhd ℂ (entireDet2 K) Set.univ :=
    (differentiable_entireDet2 hK).differentiableOn.analyticOnNhd isOpen_univ
  rcases (hA z₀ (Set.mem_univ z₀)).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hzero := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z₀) h
    have h0 : entireDet2 K 0 = 0 := hzero (Set.mem_univ 0)
    have h1 : entireDet2 K 0 = 1 := (isRegularizedDet_entireDet2 hK).eq_one_at_zero
    rw [h0] at h1
    exact zero_ne_one h1
  · exact h

/-- A radius below which every circle around `z₀` avoids the zeros of the determinant, and which
also stays inside the punctured plane. -/
theorem exists_radius_isolating {K : ι × ι → ℂ} (hK : IsHS K) {z₀ : ℂ} (hz₀0 : z₀ ≠ 0) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < ‖z₀‖ ∧
      ∀ r, 0 < r → r ≤ r₀ → ∀ z ∈ sphere z₀ r, entireDet2 K z ≠ 0 := by
  have hne := eventually_entireDet2_ne_zero hK z₀
  rw [eventually_nhdsWithin_iff] at hne
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp hne
  have hz : 0 < ‖z₀‖ := norm_pos_iff.mpr hz₀0
  refine ⟨min (ε / 2) (‖z₀‖ / 2), by positivity, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · intro r hr hrle z hz'
    have hd : dist z z₀ = r := Metric.mem_sphere.mp hz'
    have hlt : dist z z₀ < ε := by
      rw [hd]
      calc r ≤ min (ε / 2) (‖z₀‖ / 2) := hrle
        _ ≤ ε / 2 := min_le_left _ _
        _ < ε := by linarith
    refine hb hlt ?_
    intro hzz
    rw [Set.mem_singleton_iff] at hzz
    rw [hzz] at hd
    simp only [dist_self] at hd
    exact hr.ne hd

/-! ## The nearest block eigenvalue -/

/-- **The distance from `1/z₀` to the block spectrum tends to zero** at a zero of the
determinant. -/
theorem tendsto_infDist_blockSpectrum {K : ι × ι → ℂ} (hK : IsHS K) {z₀ : ℂ} (hz₀0 : z₀ ≠ 0)
    (hz₀ : entireDet2 K z₀ = 0) :
    Tendsto (fun s : Finset ι => infDist z₀⁻¹ (blockSpectrum K s)) atTop (nhds 0) := by
  obtain ⟨r₀, hr₀, hr₀z, hiso⟩ := exists_radius_isolating hK hz₀0
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hinv : ∀ᶠ z in nhds z₀, dist z⁻¹ z₀⁻¹ < ε :=
    (continuousAt_inv₀ hz₀0).tendsto (Metric.ball_mem_nhds _ hε)
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.eventually_nhds_iff.mp hinv
  set r : ℝ := min r₀ (r₁ / 2) with hrdef
  have hr : 0 < r := lt_min hr₀ (by positivity)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrz : r < ‖z₀‖ := lt_of_le_of_lt hrr₀ hr₀z
  filter_upwards [eventually_exists_blockEigenvalue_near hK hr hrz hz₀
    (hiso r hr hrr₀)] with s hs
  obtain ⟨z, hzmem, v, hv0, hv⟩ := hs
  have hzd : dist z z₀ < r₁ := by
    have h1 := mem_ball.mp hzmem
    have h2 : r ≤ r₁ / 2 := min_le_right _ _
    linarith
  have hclose : dist z⁻¹ z₀⁻¹ < ε := hb₁ hzd
  have hmem : z⁻¹ ∈ blockSpectrum K s := (mem_blockSpectrum_iff K s z⁻¹).mpr ⟨v, hv0, hv⟩
  have hle : infDist z₀⁻¹ (blockSpectrum K s) ≤ dist z₀⁻¹ z⁻¹ := infDist_le_dist_of_mem hmem
  have hnonneg : 0 ≤ infDist z₀⁻¹ (blockSpectrum K s) := infDist_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  calc infDist z₀⁻¹ (blockSpectrum K s) ≤ dist z₀⁻¹ z⁻¹ := hle
    _ = dist z⁻¹ z₀⁻¹ := dist_comm _ _
    _ < ε := hclose

theorem eventually_blockSpectrum_nonempty {K : ι × ι → ℂ} (hK : IsHS K) {z₀ : ℂ} (hz₀0 : z₀ ≠ 0)
    (hz₀ : entireDet2 K z₀ = 0) :
    ∀ᶠ s : Finset ι in atTop, (blockSpectrum K s).Nonempty := by
  obtain ⟨r₀, hr₀, hr₀z, hiso⟩ := exists_radius_isolating hK hz₀0
  filter_upwards [eventually_exists_blockEigenvalue_near hK hr₀ hr₀z hz₀
    (hiso r₀ hr₀ le_rfl)] with s hs
  obtain ⟨z, _, v, hv0, hv⟩ := hs
  exact ⟨z⁻¹, (mem_blockSpectrum_iff K s z⁻¹).mpr ⟨v, hv0, hv⟩⟩

/-! ## The eigenvalue of the kernel operator -/

/-- **A zero of the entire regularized determinant is a reciprocal eigenvalue of the kernel
operator.** -/
theorem exists_eigenvector_of_entireDet2_eq_zero {K : ι × ι → ℂ} (hK : IsHS K) {z₀ : ℂ}
    (hz₀0 : z₀ ≠ 0) (hz₀ : entireDet2 K z₀ = 0) :
    ∃ w : lp (fun _ : ι => ℂ) 2, w ≠ 0 ∧ toOperator hK w = z₀⁻¹ • w := by
  classical
  have hdist := tendsto_infDist_blockSpectrum hK hz₀0 hz₀
  have hnonempty := eventually_blockSpectrum_nonempty hK hz₀0 hz₀
  -- the nearest point of the block spectrum
  set μ : Finset ι → ℂ := fun s =>
    if h : (blockSpectrum K s).Nonempty then
      Classical.choose ((isClosed_blockSpectrum K s).exists_infDist_eq_dist h z₀⁻¹) else 0
    with hμdef
  have hμspec : ∀ᶠ s : Finset ι in atTop,
      μ s ∈ blockSpectrum K s ∧ infDist z₀⁻¹ (blockSpectrum K s) = dist z₀⁻¹ (μ s) := by
    filter_upwards [hnonempty] with s hs
    have hc := Classical.choose_spec ((isClosed_blockSpectrum K s).exists_infDist_eq_dist hs z₀⁻¹)
    rw [hμdef]
    simp only [hs, dif_pos]
    exact hc
  have hμlim : Tendsto μ atTop (nhds z₀⁻¹) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun s => dist_nonneg) ?_ hdist
    filter_upwards [hμspec] with s hs
    rw [dist_comm]
    exact le_of_eq hs.2.symm
  -- the corresponding unit eigenvectors in `ℓ²`
  set V : Finset ι → lp (fun _ : ι => ℂ) 2 := fun s =>
    if h : ∃ v : ↥s → ℂ, v ≠ 0 ∧ (blockMatrix K s) *ᵥ v = μ s • v then
      ((‖liftBlockLp (Classical.choose h)‖⁻¹ : ℝ) : ℂ) • liftBlockLp (Classical.choose h) else 0
    with hVdef
  have hVprop : ∀ᶠ s : Finset ι in atTop,
      ‖V s‖ = 1 ∧ toOperator (isHS_truncKernel hK s) (V s) = μ s • V s := by
    filter_upwards [hμspec] with s hs
    have hex : ∃ v : ↥s → ℂ, v ≠ 0 ∧ (blockMatrix K s) *ᵥ v = μ s • v :=
      (mem_blockSpectrum_iff K s (μ s)).mp hs.1
    obtain ⟨hv0, hv⟩ := Classical.choose_spec hex
    have hlift0 : liftBlockLp (Classical.choose hex) ≠ 0 := liftBlockLp_ne_zero hv0
    have hVs : V s
        = ((‖liftBlockLp (Classical.choose hex)‖⁻¹ : ℝ) : ℂ) • liftBlockLp (Classical.choose hex) := by
      rw [hVdef]
      simp only [hex, dif_pos]
    have hpos : 0 < ‖liftBlockLp (Classical.choose hex)‖ := norm_pos_iff.mpr hlift0
    constructor
    · rw [hVs, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hpos.ne']
    · rw [hVs, map_smul, toOperator_truncKernel_liftBlockLp hK s hv, smul_comm]
  -- the compact limit operator
  have hTcompact : IsCompactOperator (toOperator hK) :=
    (isHilbertSchmidt_toOperator hK).isCompactOperator
  exact exists_eigenvector_of_tendsto_of_isCompactOperator hTcompact
    (tendsto_norm_toOperator_truncKernel_sub hK)
    (hVprop.mono fun s hs => hs.1) (hVprop.mono fun s hs => hs.2) hμlim (inv_ne_zero hz₀0)

end GaloisForLFunctions.HTGeometry
