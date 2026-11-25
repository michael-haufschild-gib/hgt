import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.CriticalClearance
import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw
import GaloisForLFunctions.HTGeometry.GaussianIntervalPositivity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualDynamics

/-! # Min-max saddle subdifferential transversality at 1/10 and degree-free anti-concentration

This module analyzes the first-order directional and subdifferential geometry of
`V ↦ torusCriticalHeight e V j` at attained `(θ_⋆, W_⋆)` saddles along self-adjoint
transverse generators `K` and Pauli commutators `i [P, H]`, and resolves when directional
non-stationarity yields fixed-`e = 1/10` Gaussian anti-concentration without polynomial
degree loss:

1. **Attained min-max saddles and operator-norm Gateaux calculus:**
   - `exists_torusCriticalHeight_saddle`: every `(e, V, j)` attains its min-max height
     `torusCriticalHeight e V j = ‖projectiveSpectralMatrix e V θ_⋆ - W_⋆‖` on
     `𝕋^d × phaseCircuitMatrixImageAtMost N j`.
   - `tendsto_opNorm_directionalDeriv`: for `0 < ‖M₀‖`, the right directional derivative of
     `u ↦ ‖M₀ + u Δ‖` at `0⁺` equals `max_{ψ ∈ S(M₀)} Re ⟨M₀ ψ, Δ ψ⟩ / ‖M₀‖` over the
     compact unit sphere `maxRightSingularSphere M₀`.
   - `dini_torusPointDistance_sandwich` and `liminf_torusCriticalHeight_transverseFlow_ge`:
     exact two-sided right Dini sandwich for `g_{e, j}(e^{-i u K} V, θ)` and lower Dini
     envelope bound for `torusCriticalHeight e (e^{-i u K} V) j`.
2. **Unitary-ratio eigenmode formula and Pauli-commutator `[P, H]` classification:**
   - `exists_unitaryRatio_singularEigenmode`: for unitaries `U_⋆, W_⋆` with
     `r = ‖U_⋆ - W_⋆‖ > 0`, there exist `ψ ∈ maxRightSingularSphere (U_⋆ - W_⋆)` and `β ∈ ℝ`
     with `β² = r² * (1 - r² / 4)` and `W_⋆ ψ = (1 - r² / 2 + i β) • U_⋆ ψ`, reducing the
     directional variation along `e^{-i u K}` on `ψ` to
     `(β / r) * (Re ⟨U_⋆ ψ, K U_⋆ ψ⟩ - Re ⟨ψ, K ψ⟩)`.
   - `sup_selfAdjoint_expectation_diff_eq` and `tenth_saddle_unitBall_sensitivity_eq`:
     the supremum of `|Re ⟨ξ, K ξ⟩ - Re ⟨ψ, K ψ⟩|` over unit-norm self-adjoint `K` is
     attained and equals `2 * √(1 - ‖⟨ψ, ξ⟩‖²)`; at `r = 1/10` the maximum mode slope is
     `(√399 / 10) * √(1 - ‖⟨ψ, U_⋆ ψ⟩‖²)`, whereas at `r = 2` or on common eigenmodes it
     vanishes for every self-adjoint `K`.
   - `pauliCommutator_stationary_iff_eigenmode` and `finrank_chainPauliTransverseSpan_le`:
     under simple spectrum of `H`, all `4^N` Pauli commutators `i [σ_p, H]` have zero
     expectation shift on `ψ` if and only if `‖⟨ψ, U_⋆ ψ⟩‖ = 1` (`U_⋆ ψ = c • ψ`), while the
     `12N - 9` open-chain two-local Pauli commutators span real dimension at most `12N - 9`.
3. **Failure of pure Lipschitz non-stationarity vs. degree-free Dini anti-concentration:**
   - `oscillatorySliceCounterexample_violation`: explicit real-analytic `1`-Lipschitz family
     `f_δ(x) = e₀ + δ / 2 + 2 δ sin(x_{i₀} / (2 δ))` with derivative `≥ √3 / 2` across the
     `[e₀ - δ / 2, e₀ + 3 δ / 2]` collar yet product-Gaussian mass
     `≥ exp(-1/2) / (10 π √(2 π))` in `(e₀, e₀ + δ]` for all `δ ∈ (0, 1 / (8 π)]`.
   - `dini_mul_sub_le_sub`, `gaussian_degreeFree_dini_anticoncentration`, and
     `fixed_tenth_locking_of_dini_anticoncentration`: non-smooth right Dini monotonicity on
     `M` convex fiber pieces yields degree-free Gaussian anti-concentration
     `≤ M * δ / (√(2 π) * c)` for every fixed `e₀` and transfers directly to fixed-`e = 1/10`
     zero-drop locking `m_{1/10 + δ} = m_{1/10}`. -/

open Set Filter MeasureTheory ProbabilityTheory Real Topology Matrix
open scoped Matrix.Norms.L2Operator ENNReal ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev UGroup (N : ℕ) := Matrix.unitaryGroup (Config N) ℂ
private abbrev StateSpace (N : ℕ) := EuclideanSpace ℂ (Config N)

private abbrev euclCLM {N : ℕ} (A : Register N) : StateSpace N →L[ℂ] StateSpace N :=
  Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ) A

/-- Compact sphere of unit vectors in `EuclideanSpace ℂ (Config N)` attaining the `L²`
operator norm of `M`. -/
def maxRightSingularSphere {N : ℕ} (M : Register N) : Set (StateSpace N) :=
  {ψ : StateSpace N | ‖ψ‖ = 1 ∧ ‖euclCLM M ψ‖ = ‖M‖}

/-- Skew-adjoint commutator tangent `-i [K, U]` of `u ↦ e^{-i u K} U e^{i u K}` at `u = 0`. -/
def skewAdjointCommutator {N : ℕ} (K : selfAdjoint (Register N)) (U : Register N) : Register N :=
  (-Complex.I) • (K.val * U - U * K.val)

/-- Transverse eigenframe rotation `V(u) = e^{-i u K} V` in `U(2^N)`. -/
def transverseEigenspaceFlow {N : ℕ} (K : selfAdjoint (Register N)) (V : UGroup N) (u : ℝ) :
    UGroup N :=
  ⟨unitaryEvolution K.val u * V.val, mul_mem (unitaryEvolution_mem_unitary K.2 u) V.2⟩

/-- Self-adjoint generator `i [P, H]` associated with a Hermitian probe `P` and Hamiltonian `H`. -/
def pauliTransverseGenerator {N : ℕ} (H P : selfAdjoint (Register N)) :
    selfAdjoint (Register N) :=
  ⟨Complex.I • (P.val * H.val - H.val * P.val), by
    rw [selfAdjoint.mem_iff, star_smul, star_sub, star_mul, star_mul,
      P.2.star_eq, H.2.star_eq, Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]⟩

/-- Real-analytic `1`-Lipschitz test family oscillating at period `4 π δ` around `e₀ + δ / 2`. -/
def oscillatorySliceCounterexample {ι : Type*} (i₀ : ι) (e₀ δ : ℝ) (x : ι → ℝ) : ℝ :=
  e₀ + δ / 2 + 2 * δ * Real.sin (x i₀ / (2 * δ))

/-! ## Section 1: Attained min-max saddles and operator-norm Gateaux calculus -/

theorem isCompact_maxRightSingularSphere {N : ℕ} (M : Register N) :
    IsCompact (maxRightSingularSphere M) := by
  have heq : maxRightSingularSphere M =
      Metric.sphere (0 : StateSpace N) 1 ∩ {ψ | ‖euclCLM M ψ‖ = ‖M‖} := by
    ext ψ
    simp [maxRightSingularSphere, mem_sphere_zero_iff_norm]
  rw [heq]
  exact (isCompact_sphere (0 : StateSpace N) 1).inter_right
    (isClosed_eq ((euclCLM M).continuous.norm) continuous_const)

theorem nonempty_maxRightSingularSphere {N : ℕ} (M : Register N) :
    (maxRightSingularSphere M).Nonempty := by
  let x₀ : Config N := fun _ => false
  have hS_ne : (Metric.sphere (0 : StateSpace N) 1).Nonempty :=
    ⟨EuclideanSpace.single x₀ 1, by simp [mem_sphere_zero_iff_norm]⟩
  obtain ⟨ψ, hψ_mem, hψ_max⟩ :=
    (isCompact_sphere (0 : StateSpace N) 1).exists_isMaxOn hS_ne (euclCLM M).continuous.norm.continuousOn
  have hψ_norm : ‖ψ‖ = 1 := mem_sphere_zero_iff_norm.mp hψ_mem
  refine ⟨ψ, hψ_norm, le_antisymm ?_ ?_⟩
  · simpa only [Matrix.l2_opNorm_toEuclideanCLM, hψ_norm, mul_one] using (euclCLM M).le_opNorm ψ
  · rw [← Matrix.l2_opNorm_toEuclideanCLM]
    refine (euclCLM M).opNorm_le_bound (norm_nonneg _) fun x => ?_
    by_cases hx : x = 0
    · simp [hx]
    · have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      let u : StateSpace N := ((‖x‖⁻¹ : ℝ) : ℂ) • x
      have hu_norm : ‖u‖ = 1 := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hx_pos.ne']
      have hu_le : ‖euclCLM M u‖ ≤ ‖euclCLM M ψ‖ :=
        hψ_max (mem_sphere_zero_iff_norm.mpr hu_norm)
      have hscale : euclCLM M u = ((‖x‖⁻¹ : ℝ) : ℂ) • euclCLM M x := map_smul (euclCLM M) _ _
      rw [hscale, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm] at hu_le
      exact (inv_mul_le_iff₀ hx_pos).mp hu_le

/-- Every eigenbasis critical height `torusCriticalHeight e V j` is attained at a saddle pair
`(θ_⋆, W_⋆) ∈ 𝕋^d × phaseCircuitMatrixImageAtMost N j`. -/
theorem exists_torusCriticalHeight_saddle {N d : ℕ} (e : Config N ≃ Fin (d + 1))
    (V : UGroup N) (j : ℕ) :
    ∃ (θ_star : Fin d → UnitAddCircle) (W_star : Register N),
      W_star ∈ phaseCircuitMatrixImageAtMost N j ∧
      torusCriticalHeight e V j =
        Metric.infDist (projectiveSpectralMatrix e V θ_star) (phaseCircuitMatrixImageAtMost N j) ∧
      torusCriticalHeight e V j = ‖projectiveSpectralMatrix e V θ_star - W_star‖ := by
  let f : (Fin d → UnitAddCircle) → ℝ := fun θ =>
    Metric.infDist (projectiveSpectralMatrix e V θ) (phaseCircuitMatrixImageAtMost N j)
  have hf_cont : Continuous f :=
    (Metric.continuous_infDist_pt _).comp (continuous_projectiveSpectralMatrix e V)
  obtain ⟨θ_star, _, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hf_cont.continuousOn
  have hsup : torusCriticalHeight e V j = f θ_star := by
    unfold torusCriticalHeight
    refine le_antisymm (csSup_le (range_nonempty f) ?_)
      (le_csSup (by
        refine ⟨2, ?_⟩
        rintro _ ⟨θ, rfl⟩
        have h1 : (1 : ℂ) • ((TwoQubitCircuit.one N).eval : Register N) ∈
            phaseCircuitMatrixImageAtMost N j :=
          mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨1, norm_one, TwoQubitCircuit.one N, Nat.zero_le _, rfl⟩
        refine (Metric.infDist_le_dist_of_mem h1).trans ?_
        rw [dist_eq_norm, one_smul, TwoQubitCircuit.one_eval]
        have hunit : projectiveSpectralMatrix e V θ ∈ unitary (Register N) := by
          unfold projectiveSpectralMatrix
          refine mul_mem (mul_mem V.2 ?_) (Unitary.star_mem V.2)
          rw [Unitary.mem_iff, star_eq_conjTranspose, diagonal_conjTranspose,
            diagonal_mul_diagonal, diagonal_mul_diagonal]
          constructor <;> ext a b <;> by_cases hab : a = b
          · subst hab; simp only [diagonal_apply_eq, one_apply_eq]
            exact Complex.normSq_eq_conj_mul_self.symm.trans (by simp)
          · simp [hab]
          · subst hab; simp only [diagonal_apply_eq, one_apply_eq]; rw [mul_comm]
            exact Complex.normSq_eq_conj_mul_self.symm.trans (by simp)
          · simp [hab]
        linarith only [norm_sub_le (projectiveSpectralMatrix e V θ) 1,
          CStarRing.norm_of_mem_unitary hunit, norm_one (α := Register N)])
      (mem_range_self θ_star))
    rintro _ ⟨θ, rfl⟩
    exact hmax (mem_univ θ)
  have hC_ne : (phaseCircuitMatrixImageAtMost N j).Nonempty :=
    ⟨(1 : ℂ) • ((TwoQubitCircuit.one N).eval : Register N),
      mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨1, norm_one, TwoQubitCircuit.one N, Nat.zero_le _, rfl⟩⟩
  obtain ⟨W_star, hW_mem, hW_dist⟩ := exists_compactTarget_minDist
    (isCompact_phaseCircuitMatrixImageAtMost N j) hC_ne (projectiveSpectralMatrix e V θ_star)
  refine ⟨θ_star, W_star, hW_mem, hsup, ?_⟩
  rw [hsup, show f θ_star = _ from hW_dist.symm, dist_eq_norm]

/-- Exact global subgradient inequality for the `L²` operator norm at any maximal right
singular vector `ψ ∈ maxRightSingularSphere M₀`. -/
theorem opNorm_add_smul_ge_of_mem_maxRightSingularSphere {N : ℕ} {M₀ : Register N}
    (hM₀ : 0 < ‖M₀‖) {ψ : StateSpace N} (hψ : ψ ∈ maxRightSingularSphere M₀)
    (Δ : Register N) (u : ℝ) :
    ‖M₀‖ + u * ((inner ℂ (euclCLM M₀ ψ) (euclCLM Δ ψ)).re / ‖M₀‖) ≤
      ‖M₀ + (u : ℂ) • Δ‖ := by
  obtain ⟨hψ1, hMψ⟩ := hψ
  let φ : StateSpace N := ((‖M₀‖⁻¹ : ℝ) : ℂ) • euclCLM M₀ ψ
  have hφ_norm : ‖φ‖ = 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, hMψ,
      inv_mul_cancel₀ hM₀.ne']
  have hcs : (inner ℂ φ (euclCLM (M₀ + (u : ℂ) • Δ) ψ)).re ≤
      ‖euclCLM (M₀ + (u : ℂ) • Δ) ψ‖ := by
    have h1 := Complex.re_le_norm (inner ℂ φ (euclCLM (M₀ + (u : ℂ) • Δ) ψ))
    have h2 := norm_inner_le_norm φ (euclCLM (M₀ + (u : ℂ) • Δ) ψ)
    rw [hφ_norm, one_mul] at h2
    exact h1.trans h2
  have hle_op : ‖euclCLM (M₀ + (u : ℂ) • Δ) ψ‖ ≤ ‖M₀ + (u : ℂ) • Δ‖ := by
    simpa only [Matrix.l2_opNorm_toEuclideanCLM, hψ1, mul_one] using
      (euclCLM (M₀ + (u : ℂ) • Δ)).le_opNorm ψ
  have hre : (inner ℂ φ (euclCLM (M₀ + (u : ℂ) • Δ) ψ)).re =
      ‖M₀‖ + u * ((inner ℂ (euclCLM M₀ ψ) (euclCLM Δ ψ)).re / ‖M₀‖) := by
    have hexp : euclCLM (M₀ + (u : ℂ) • Δ) ψ = euclCLM M₀ ψ + (u : ℂ) • euclCLM Δ ψ := by
      rw [map_add, map_smul]; rfl
    rw [hexp, inner_add_right, inner_smul_right, Complex.add_re]
    have hself : (inner ℂ φ (euclCLM M₀ ψ)).re = ‖M₀‖ := by
      dsimp only [φ]
      rw [inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K, hMψ]
      simp only [Complex.ofReal_cpow (norm_nonneg M₀), ← Complex.ofReal_pow, ← Complex.ofReal_mul,
        Complex.ofReal_re]
      field_simp [hM₀.ne']
    have hcross : ((u : ℂ) * inner ℂ φ (euclCLM Δ ψ)).re =
        u * ((inner ℂ (euclCLM M₀ ψ) (euclCLM Δ ψ)).re / ‖M₀‖) := by
      dsimp only [φ]
      rw [inner_smul_left, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
        Complex.re_ofReal_mul]
      ring
    rw [hself, hcross]
  linarith only [hcs, hle_op, hre]

/-- Exact right Gateaux derivative of the finite-matrix `L²` operator norm over the compact
maximal singular sphere `maxRightSingularSphere M₀`. -/
theorem tendsto_opNorm_directionalDeriv {N : ℕ} {M₀ : Register N} (hM₀ : 0 < ‖M₀‖)
    (Δ : Register N) :
    let g : StateSpace N → ℝ := fun ψ => (inner ℂ (euclCLM M₀ ψ) (euclCLM Δ ψ)).re / ‖M₀‖
    (∃ ψ_max ∈ maxRightSingularSphere M₀, ∀ ψ ∈ maxRightSingularSphere M₀, g ψ ≤ g ψ_max) ∧
    Tendsto (fun u : ℝ => (‖M₀ + (u : ℂ) • Δ‖ - ‖M₀‖) / u) (𝓝[>] 0)
      (𝓝 (sSup (g '' maxRightSingularSphere M₀))) := by
  intro g
  have hg_cont : Continuous g := by
    refine Continuous.div_const ?_ ‖M₀‖
    exact Complex.continuous_re.comp
      (Continuous.inner ((euclCLM M₀).continuous) ((euclCLM Δ).continuous))
  obtain ⟨ψ_max, hψ_mem, hψ_max⟩ := (isCompact_maxRightSingularSphere M₀).exists_isMaxOn
    (nonempty_maxRightSingularSphere M₀) hg_cont.continuousOn
  have hsup_eq : sSup (g '' maxRightSingularSphere M₀) = g ψ_max := by
    refine le_antisymm (csSup_le ((nonempty_maxRightSingularSphere M₀).image g) ?_)
      (le_csSup ((isCompact_maxRightSingularSphere M₀).image hg_cont).bddAbove
        ⟨ψ_max, hψ_mem, rfl⟩)
    rintro _ ⟨ψ, hψ, rfl⟩
    exact hψ_max hψ
  refine ⟨⟨ψ_max, hψ_mem, fun ψ hψ => hψ_max hψ⟩, ?_⟩
  rw [hsup_eq, Metric.tendsto_nhds]
  intro ε hε
  -- Upper bound by compactness: outside an open neighborhood U of maxRightSingularSphere M₀
  -- inside the unit sphere, ‖euclCLM M₀ ψ‖ ≤ ‖M₀‖ - η for some η > 0.
  let S₁ := Metric.sphere (0 : StateSpace N) 1
  let U : Set (StateSpace N) := {ψ | g ψ < g ψ_max + ε / 2}
  have hU_open : IsOpen U := isOpen_lt hg_cont continuous_const
  let K_bad : Set (StateSpace N) := S₁ \ U
  have hK_compact : IsCompact K_bad := (isCompact_sphere (0 : StateSpace N) 1).diff hU_open
  have hgap_bad : ∃ δ₁ > (0 : ℝ), ∀ u ∈ Ioo (0 : ℝ) δ₁,
      ∀ ψ ∈ maxRightSingularSphere (M₀ + (u : ℂ) • Δ), g ψ < g ψ_max + ε / 2 := by
    by_cases hK_emp : K_bad = ∅
    · refine ⟨1, zero_lt_one, fun u _ ψ hψ => ?_⟩
      have hψ_S₁ : ψ ∈ S₁ := mem_sphere_zero_iff_norm.mpr hψ.1
      by_contra hnotU
      have hmem : ψ ∈ K_bad := ⟨hψ_S₁, hnotU⟩
      rw [hK_emp] at hmem
      exact hmem
    · obtain ⟨ψ_b, hψ_b, hmax_b⟩ := hK_compact.exists_isMaxOn
        (nonempty_iff_ne_empty.mpr hK_emp) (euclCLM M₀).continuous.norm.continuousOn
      have hlt_M₀ : ‖euclCLM M₀ ψ_b‖ < ‖M₀‖ := by
        have hle : ‖euclCLM M₀ ψ_b‖ ≤ ‖M₀‖ := by
          simpa only [Matrix.l2_opNorm_toEuclideanCLM, mem_sphere_zero_iff_norm.mp hψ_b.1, mul_one]
            using (euclCLM M₀).le_opNorm ψ_b
        refine lt_of_le_of_ne hle fun heq => hψ_b.2 ?_
        have hmem_max : ψ_b ∈ maxRightSingularSphere M₀ :=
          ⟨mem_sphere_zero_iff_norm.mp hψ_b.1, heq⟩
        exact (hψ_max hmem_max).trans_lt (by linarith only [hε])
      let η := ‖M₀‖ - ‖euclCLM M₀ ψ_b‖
      have hη_pos : 0 < η := sub_pos.mpr hlt_M₀
      refine ⟨η / (2 * (‖Δ‖ + 1)), div_pos hη_pos (by positivity), fun u hu ψ hψ => ?_⟩
      by_contra hnotU
      have hmem : ψ ∈ K_bad := ⟨mem_sphere_zero_iff_norm.mpr hψ.1, hnotU⟩
      have h1 : ‖euclCLM M₀ ψ‖ ≤ ‖M₀‖ - η := by
        dsimp only [η]; linarith only [hmax_b hmem]
      have h2 : ‖M₀ + (u : ℂ) • Δ‖ ≤ ‖euclCLM M₀ ψ‖ + u * ‖Δ‖ := by
        rw [← hψ.2, map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hu.1.le]
        refine mul_le_mul_of_nonneg_left ?_ hu.1.le
        simpa only [Matrix.l2_opNorm_toEuclideanCLM, hψ.1, mul_one] using (euclCLM Δ).le_opNorm ψ
      have h3 : ‖M₀‖ - u * ‖Δ‖ ≤ ‖M₀ + (u : ℂ) • Δ‖ := by
        have htri := norm_sub_le (M₀ + (u : ℂ) • Δ) ((u : ℂ) • Δ)
        rw [add_sub_cancel_right, norm_smul, Complex.norm_real, Real.norm_of_nonneg hu.1.le] at htri
        linarith only [htri]
      have hu_small : 2 * u * ‖Δ‖ < η := by
        have hlt1 : u * (2 * (‖Δ‖ + 1)) < η := (lt_div_iff₀ (by positivity)).mp hu.2
        nlinarith only [hu.1, norm_nonneg Δ, hlt1]
      linarith only [h1, h2, h3, hu_small]
  obtain ⟨δ₁, hδ₁, hbad⟩ := hgap_bad
  let δ₂ := min (‖M₀‖ / (2 * (‖Δ‖ + 1))) (ε * ‖M₀‖ / (2 * (‖Δ‖ ^ 2 + 1)))
  have hδ₂ : 0 < δ₂ := lt_min (div_pos hM₀ (by positivity))
    (div_pos (mul_pos hε hM₀) (by positivity))
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ₁ hδ₂)] with u hu
  have hu_pos : 0 < u := hu.1
  have hu_δ₁ : u ∈ Ioo 0 δ₁ := ⟨hu_pos, hu.2.trans_le (min_le_left _ _)⟩
  have hu_δ₂ : u < δ₂ := hu.2.trans_le (min_le_right _ _)
  -- Lower bound from ψ_max
  have hlo : g ψ_max ≤ (‖M₀ + (u : ℂ) • Δ‖ - ‖M₀‖) / u := by
    have hsub := opNorm_add_smul_ge_of_mem_maxRightSingularSphere hM₀ hψ_mem Δ u
    exact (le_div_iff₀ hu_pos).mpr (by rw [mul_comm]; linarith only [hsub])
  -- Upper bound from a maximizer ψ_u of M₀ + u Δ
  obtain ⟨ψ_u, hψ_u⟩ := nonempty_maxRightSingularSphere (M₀ + (u : ℂ) • Δ)
  have hg_u : g ψ_u < g ψ_max + ε / 2 := hbad u hu_δ₁ ψ_u hψ_u
  have hM_pos : 0 < ‖M₀ + (u : ℂ) • Δ‖ + ‖M₀‖ := by linarith only [hM₀, norm_nonneg (M₀ + (u : ℂ) • Δ)]
  have hsq : ‖M₀ + (u : ℂ) • Δ‖ ^ 2 ≤
      ‖M₀‖ ^ 2 + 2 * u * ‖M₀‖ * g ψ_u + u ^ 2 * ‖Δ‖ ^ 2 := by
    rw [← hψ_u.2, map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      @norm_add_sq ℂ]
    have hMψ_le : ‖euclCLM M₀ ψ_u‖ ≤ ‖M₀‖ := by
      simpa only [Matrix.l2_opNorm_toEuclideanCLM, hψ_u.1, mul_one] using (euclCLM M₀).le_opNorm ψ_u
    have hΔψ_le : ‖(u : ℂ) • euclCLM Δ ψ_u‖ ≤ u * ‖Δ‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
      refine mul_le_mul_of_nonneg_left ?_ hu_pos.le
      simpa only [Matrix.l2_opNorm_toEuclideanCLM, hψ_u.1, mul_one] using (euclCLM Δ).le_opNorm ψ_u
    have hinner_eq : 2 * (inner ℂ (euclCLM M₀ ψ_u) ((u : ℂ) • euclCLM Δ ψ_u)).re =
        2 * u * ‖M₀‖ * g ψ_u := by
      rw [inner_smul_right, Complex.re_ofReal_mul]
      dsimp only [g]
      field_simp [hM₀.ne']
    rw [hinner_eq]
    have hsq1 : ‖euclCLM M₀ ψ_u‖ ^ 2 ≤ ‖M₀‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hMψ_le 2
    have hsq2 : ‖(u : ℂ) • euclCLM Δ ψ_u‖ ^ 2 ≤ (u * ‖Δ‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hΔψ_le 2
    linarith only [hsq1, hsq2, show (u * ‖Δ‖) ^ 2 = u ^ 2 * ‖Δ‖ ^ 2 by ring]
  -- Simpler linear upper bound: if ‖M₀ + u Δ‖ ≤ ‖M₀‖, quotient ≤ 0; wait: g ψ_max can be negative!
  -- Instead divide ‖M₀ + u Δ‖^2 - ‖M₀‖^2 by ‖M₀ + u Δ‖ + ‖M₀‖ and compare with 2 ‖M₀‖!
  have hnorm_diff : |‖M₀ + (u : ℂ) • Δ‖ - ‖M₀‖| ≤ u * ‖Δ‖ := by
    simpa only [add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_of_nonneg hu_pos.le]
      using abs_norm_sub_norm_le (M₀ + (u : ℂ) • Δ) M₀
  -- Better: directly bound ‖(M₀ + u Δ) ψ_u‖ - ‖M₀‖ using ‖x‖ ≤ (‖x‖^2 + ‖M₀‖^2)/(2 ‖M₀‖)!
  have hamgm : ‖M₀ + (u : ℂ) • Δ‖ ≤ (‖M₀ + (u : ℂ) • Δ‖ ^ 2 + ‖M₀‖ ^ 2) / (2 * ‖M₀‖) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [sq_nonneg (‖M₀ + (u : ℂ) • Δ‖ - ‖M₀‖)]
  have hhi_raw : (‖M₀ + (u : ℂ) • Δ‖ - ‖M₀‖) / u ≤ g ψ_u + u * ‖Δ‖ ^ 2 / (2 * ‖M₀‖) := by
    rw [div_le_iff₀ hu_pos]
    have h1 : ‖M₀ + (u : ℂ) • Δ‖ - ‖M₀‖ ≤
        (2 * u * ‖M₀‖ * g ψ_u + u ^ 2 * ‖Δ‖ ^ 2) / (2 * ‖M₀‖) := by
      have h2 : (‖M₀ + (u : ℂ) • Δ‖ ^ 2 + ‖M₀‖ ^ 2) / (2 * ‖M₀‖) - ‖M₀‖ ≤
          (2 * u * ‖M₀‖ * g ψ_u + u ^ 2 * ‖Δ‖ ^ 2) / (2 * ‖M₀‖) := by
        rw [div_sub' (by positivity)]
        exact div_le_div_of_nonneg_right (by linarith only [hsq]) (by positivity)
      linarith only [hamgm, h2]
    have hsplit : (2 * u * ‖M₀‖ * g ψ_u + u ^ 2 * ‖Δ‖ ^ 2) / (2 * ‖M₀‖) =
        (g ψ_u + u * ‖Δ‖ ^ 2 / (2 * ‖M₀‖)) * u := by
      field_simp [hM₀.ne']
    exact h1.trans_eq hsplit
  have htail : u * ‖Δ‖ ^ 2 / (2 * ‖M₀‖) < ε / 2 := by
    have hu2 : u < ε * ‖M₀‖ / (2 * (‖Δ‖ ^ 2 + 1)) := hu_δ₂.trans_le (min_le_right _ _)
    rw [div_lt_iff₀ (by positivity)]
    have hlt2 : u * (2 * (‖Δ‖ ^ 2 + 1)) < ε * ‖M₀‖ := (lt_div_iff₀ (by positivity)).mp hu2
    nlinarith only [hu_pos, sq_nonneg ‖Δ‖, hlt2]
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith only [hlo, hε], by linarith only [hhi_raw, hg_u, htail]⟩

/-! ## Section 2: Transverse commutator identity and two-sided Dini saddle sandwich -/

/-- Exact cancellation of the `U ψ` diagonal term in `Re ⟨(U - W) ψ, (-i [K, U]) ψ⟩` for every
unitary `U ∈ U(2^N)` and self-adjoint `K`. -/
theorem re_inner_unitary_sub_skewAdjointCommutator {N : ℕ} {U : Register N}
    (hU : U ∈ unitary (Register N)) (W : Register N) (K : selfAdjoint (Register N))
    (ψ : StateSpace N) :
    (inner ℂ (euclCLM (U - W) ψ) (euclCLM (skewAdjointCommutator K U) ψ)).re =
      -(inner ℂ (euclCLM W ψ) (euclCLM (K.val * U - U * K.val) ψ)).im := by
  have hadj (M : Register N) (x y : StateSpace N) :
      inner ℂ (euclCLM (star M) x) y = inner ℂ x (euclCLM M y) := by
    have hstar : euclCLM (star M) = ContinuousLinearMap.adjoint (euclCLM M) :=
      map_star Matrix.toEuclideanCLM M
    rw [hstar, ContinuousLinearMap.adjoint_inner_left]
  have hself_im (x : StateSpace N) : (inner ℂ x (euclCLM K.val x)).im = 0 := by
    have hsym : inner ℂ x (euclCLM K.val x) = starRingEnd ℂ (inner ℂ x (euclCLM K.val x)) := by
      rw [inner_conj_symm, ← hadj K.val x x, K.2.star_eq]
    exact Complex.conj_eq_iff_im.mp hsym.symm
  have hU_zero : (inner ℂ (euclCLM U ψ) (euclCLM (skewAdjointCommutator K U) ψ)).re = 0 := by
    unfold skewAdjointCommutator
    rw [map_smul, map_sub, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      inner_smul_right, inner_sub_right]
    have h1 : euclCLM (K.val * U) ψ = euclCLM K.val (euclCLM U ψ) := by rw [map_mul]; rfl
    have h2 : inner ℂ (euclCLM U ψ) (euclCLM (U * K.val) ψ) =
        inner ℂ ψ (euclCLM K.val ψ) := by
      rw [map_mul, ContinuousLinearMap.mul_apply, ← hadj U, ← ContinuousLinearMap.mul_apply,
        ← map_mul, (Unitary.mem_iff.mp hU).1, map_one, ContinuousLinearMap.one_apply]
    rw [h1, h2]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      neg_zero, zero_mul, zero_sub, neg_neg, one_mul, Complex.sub_im,
      hself_im (euclCLM U ψ), hself_im ψ, sub_zero]
  rw [map_sub, ContinuousLinearMap.sub_apply, inner_sub_left, Complex.sub_re, hU_zero, zero_sub]
  unfold skewAdjointCommutator
  rw [map_smul, ContinuousLinearMap.smul_apply, inner_smul_right]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, zero_mul, zero_sub, neg_neg, one_mul]
  ring

private theorem norm_conj_unitaryEvolution_sub_linear_le {N : ℕ}
    (K : selfAdjoint (Register N)) {U : Register N} (hU : ‖U‖ ≤ 1) {u : ℝ} (hu : 0 ≤ u) :
    ‖unitaryEvolution K.val u * U * star (unitaryEvolution K.val u) -
        (U + (u : ℂ) • skewAdjointCommutator K U)‖ ≤
      u ^ 2 * ‖K.val‖ ^ 2 * (2 + u * ‖K.val‖ / 2) := by
  let L : Register N := ((u : ℂ) * -Complex.I) • K.val
  let E : Register N := unitaryEvolution K.val u - (1 + L)
  have hE : ‖E‖ ≤ (u * ‖K.val‖) ^ 2 / 2 := by
    have h := norm_selfAdjoint_exp_sub_hamiltonianTaylor_le K.val K.2 1 u
    have hT : selfAdjointHamiltonianTaylor K.val 1 u = 1 + L := by
      simp only [selfAdjointHamiltonianTaylor, cstarExponentialTaylor, Finset.sum_range_succ,
        Finset.sum_range_zero, pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one,
        Nat.cast_one, div_one, one_smul, zero_add, L]
      rw [← Complex.real_smul, smul_assoc]
    rw [hT] at h
    change ‖E‖ ≤ _ at h
    simpa [abs_of_nonneg hu, mul_pow, mul_comm] using h
  have hstarL : star L = ((u : ℂ) * Complex.I) • K.val := by
    dsimp only [L]
    rw [star_smul, K.2.star_eq, star_mul, Complex.star_def, Complex.conj_ofReal,
      star_neg, Complex.star_def, Complex.conj_I, neg_neg, mul_comm]
  have hL_norm : ‖L‖ = u * ‖K.val‖ := by
    dsimp only [L]
    rw [norm_smul, norm_mul, norm_neg, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg hu]
  have hdecomp : unitaryEvolution K.val u * U * star (unitaryEvolution K.val u) -
      (U + (u : ℂ) • skewAdjointCommutator K U) =
      E * U * star (unitaryEvolution K.val u) + (1 + L) * U * star E + L * U * star L := by
    have hev : unitaryEvolution K.val u = (1 + L) + E := by dsimp only [E]; abel
    have hst : star (unitaryEvolution K.val u) = (1 + star L) + star E := by
      rw [hev, star_add, star_add, star_one]
    have hmid : L * U + U * star L = (u : ℂ) • skewAdjointCommutator K U := by
      rw [hstarL]
      dsimp only [L, skewAdjointCommutator]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub]
      simp only [mul_neg, neg_smul, sub_eq_add_neg, neg_neg]
    rw [hev, hst]
    -- Expand manually with noncomm_ring after substituting hmid
    have hlin : (1 + L) * U * (1 + star L) = U + (L * U + U * star L) + L * U * star L := by
      noncomm_ring
    calc ((1 + L + E) * U * (1 + star L + star E)) - (U + (u : ℂ) • skewAdjointCommutator K U)
        = E * U * (1 + star L + star E) + (1 + L) * U * star E +
            ((1 + L) * U * (1 + star L) - (U + (u : ℂ) • skewAdjointCommutator K U)) := by
            noncomm_ring
      _ = E * U * star (unitaryEvolution K.val u) + (1 + L) * U * star E + L * U * star L := by
            rw [← hst, hlin, hmid]; abel
  have hunit_norm : ‖star (unitaryEvolution K.val u)‖ = 1 := by
    rw [norm_star]
    exact CStarRing.norm_of_mem_unitary (unitaryEvolution_mem_unitary K.2 u)
  have h1 : ‖E * U * star (unitaryEvolution K.val u)‖ ≤ (u * ‖K.val‖) ^ 2 / 2 := calc
    ‖E * U * star (unitaryEvolution K.val u)‖ ≤ ‖E * U‖ * ‖star (unitaryEvolution K.val u)‖ :=
      norm_mul_le _ _
    _ ≤ (‖E‖ * 1) * 1 := mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hU (norm_nonneg _)))
        hunit_norm.le (norm_nonneg _) zero_le_one
    _ ≤ (u * ‖K.val‖) ^ 2 / 2 := by linarith only [hE]
  have h2 : ‖(1 + L) * U * star E‖ ≤ (1 + u * ‖K.val‖) * ((u * ‖K.val‖) ^ 2 / 2) := calc
    ‖(1 + L) * U * star E‖ ≤ ‖(1 + L) * U‖ * ‖star E‖ := norm_mul_le _ _
    _ ≤ (‖(1 : Register N) + L‖ * 1) * ‖E‖ := mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hU (norm_nonneg _)))
        (norm_star E).le (norm_nonneg _) (by positivity)
    _ ≤ (1 + u * ‖K.val‖) * ((u * ‖K.val‖) ^ 2 / 2) := by
        have h1L : ‖(1 : Register N) + L‖ ≤ 1 + u * ‖K.val‖ :=
          (norm_add_le 1 L).trans (by rw [hL_norm]; linarith only [norm_one_le (α := Register N)])
        rw [mul_one]
        exact mul_le_mul h1L hE (norm_nonneg _) (by positivity)
  have h3 : ‖L * U * star L‖ ≤ (u * ‖K.val‖) ^ 2 := calc
    ‖L * U * star L‖ ≤ ‖L * U‖ * ‖star L‖ := norm_mul_le _ _
    _ ≤ (‖L‖ * 1) * ‖L‖ := mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hU (norm_nonneg _)))
        (norm_star L).le (norm_nonneg _) (by positivity)
    _ = (u * ‖K.val‖) ^ 2 := by rw [hL_norm]; ring
  rw [hdecomp]
  have htri := (norm_add_le (E * U * star (unitaryEvolution K.val u) + (1 + L) * U * star E)
    (L * U * star L)).trans (add_le_add (norm_add_le _ _) le_rfl)
  nlinarith only [htri, h1, h2, h3, sq_nonneg (u * ‖K.val‖)]

/-- Exact two-sided right Dini sandwich for the pointwise torus circuit distance
`g(u) = infDist (projectiveSpectralMatrix e (transverseEigenspaceFlow K V u) θ) C_j`
at any phase point `θ` with `g(0) > 0`. -/
theorem dini_torusPointDistance_sandwich {N d : ℕ} (e : Config N ≃ Fin (d + 1))
    (V : UGroup N) (K : selfAdjoint (Register N)) (j : ℕ) (θ : Fin d → UnitAddCircle)
    (hr : 0 < Metric.infDist (projectiveSpectralMatrix e V θ) (phaseCircuitMatrixImageAtMost N j)) :
    let U₀ := projectiveSpectralMatrix e V θ
    let r := Metric.infDist U₀ (phaseCircuitMatrixImageAtMost N j)
    let W_opt := {W ∈ phaseCircuitMatrixImageAtMost N j | ‖U₀ - W‖ = r}
    let dirVal : Register N → StateSpace N → ℝ := fun W ψ =>
      -(inner ℂ (euclCLM W ψ) (euclCLM (K.val * U₀ - U₀ * K.val) ψ)).im / r
    let q : ℝ → ℝ := fun u =>
      (Metric.infDist (projectiveSpectralMatrix e (transverseEigenspaceFlow K V u) θ)
        (phaseCircuitMatrixImageAtMost N j) - r) / u
    W_opt.Nonempty ∧
    (∀ W_star ∈ W_opt, ∀ ε > 0, ∀ᶠ u in 𝓝[>] 0,
      q u < sSup (dirVal W_star '' maxRightSingularSphere (U₀ - W_star)) + ε) ∧
    (∀ ε > 0, ∀ᶠ u in 𝓝[>] 0,
      ∃ W_star ∈ W_opt, ∃ ψ_star ∈ maxRightSingularSphere (U₀ - W_star),
        dirVal W_star ψ_star - ε < q u) := by
  intro U₀ r W_opt dirVal q
  have hU₀_unit : U₀ ∈ unitary (Register N) := by
    dsimp only [U₀]
    unfold projectiveSpectralMatrix
    refine mul_mem (mul_mem V.2 ?_) (Unitary.star_mem V.2)
    rw [Unitary.mem_iff, star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    constructor <;> ext a b <;> by_cases hab : a = b
    · subst hab; simp only [diagonal_apply_eq, one_apply_eq]
      exact Complex.normSq_eq_conj_mul_self.symm.trans (by simp)
    · simp [hab]
    · subst hab; simp only [diagonal_apply_eq, one_apply_eq]; rw [mul_comm]
      exact Complex.normSq_eq_conj_mul_self.symm.trans (by simp)
    · simp [hab]
  have hU₀_norm : ‖U₀‖ ≤ 1 := (CStarRing.norm_of_mem_unitary hU₀_unit).le
  have hflow_eq (u : ℝ) :
      projectiveSpectralMatrix e (transverseEigenspaceFlow K V u) θ =
        unitaryEvolution K.val u * U₀ * star (unitaryEvolution K.val u) := by
    dsimp only [U₀, transverseEigenspaceFlow]
    unfold projectiveSpectralMatrix
    have hinv : ((⟨unitaryEvolution K.val u * V.val,
        mul_mem (unitaryEvolution_mem_unitary K.2 u) V.2⟩ : UGroup N)⁻¹ : UGroup N).val =
        star V.val * star (unitaryEvolution K.val u) := by
      change star (unitaryEvolution K.val u * V.val) = _
      exact star_mul _ _
    have hVinv : (V⁻¹ : UGroup N).val = star V.val := rfl
    rw [hinv, hVinv]
    simp only [mul_assoc]
  have hC_compact : IsCompact (phaseCircuitMatrixImageAtMost N j) :=
    isCompact_phaseCircuitMatrixImageAtMost N j
  have hC_ne : (phaseCircuitMatrixImageAtMost N j).Nonempty :=
    ⟨(1 : ℂ) • ((TwoQubitCircuit.one N).eval : Register N),
      mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨1, norm_one, TwoQubitCircuit.one N, Nat.zero_le _, rfl⟩⟩
  obtain ⟨W₀, hW₀_mem, hW₀_dist⟩ := exists_compactTarget_minDist hC_compact hC_ne U₀
  have hW_opt_ne : W_opt.Nonempty := ⟨W₀, hW₀_mem, by rw [← dist_eq_norm, hW₀_dist]⟩
  refine ⟨hW_opt_ne, ?_, ?_⟩
  · -- Upper bound for each W_star ∈ W_opt
    intro W_star ⟨hW_mem, hW_eq⟩ ε hε
    have hM₀_pos : 0 < ‖U₀ - W_star‖ := hW_eq.symm ▸ hr
    have hdir_eq : (fun ψ => (inner ℂ (euclCLM (U₀ - W_star) ψ)
        (euclCLM (skewAdjointCommutator K U₀) ψ)).re / ‖U₀ - W_star‖) = dirVal W_star := by
      funext ψ
      rw [re_inner_unitary_sub_skewAdjointCommutator hU₀_unit W_star K ψ, hW_eq]
    have htend := (tendsto_opNorm_directionalDeriv hM₀_pos (skewAdjointCommutator K U₀)).2
    rw [hdir_eq] at htend
    have hev1 := (Metric.tendsto_nhds.mp htend (ε / 2) (half_pos hε)).mono fun u hu =>
      (abs_lt.mp (Real.dist_eq _ _ ▸ hu)).2
    have hquad_lim : Tendsto (fun u : ℝ => u * ‖K.val‖ ^ 2 * (2 + u * ‖K.val‖ / 2))
        (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun u : ℝ => u * ‖K.val‖ ^ 2 * (2 + u * ‖K.val‖ / 2)) := by continuity
      simpa using hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [Ioi_mem_nhdsGT (0 : ℝ), hev1,
      hquad_lim.eventually_lt_const (half_pos hε)] with u hu_pos hu1 hu_quad
    have hu_pos' : 0 < u := hu_pos
    have hinf_le : Metric.infDist (projectiveSpectralMatrix e (transverseEigenspaceFlow K V u) θ)
        (phaseCircuitMatrixImageAtMost N j) ≤
        ‖unitaryEvolution K.val u * U₀ * star (unitaryEvolution K.val u) - W_star‖ := by
      rw [← hflow_eq u, ← dist_eq_norm]
      exact Metric.infDist_le_dist_of_mem hW_mem
    have hrem := norm_conj_unitaryEvolution_sub_linear_le K hU₀_norm hu_pos'.le
    have htri : ‖unitaryEvolution K.val u * U₀ * star (unitaryEvolution K.val u) - W_star‖ ≤
        ‖(U₀ - W_star) + (u : ℂ) • skewAdjointCommutator K U₀‖ +
          u ^ 2 * ‖K.val‖ ^ 2 * (2 + u * ‖K.val‖ / 2) := by
      have heq : unitaryEvolution K.val u * U₀ * star (unitaryEvolution K.val u) - W_star =
          ((U₀ - W_star) + (u : ℂ) • skewAdjointCommutator K U₀) +
            (unitaryEvolution K.val u * U₀ * star (unitaryEvolution K.val u) -
              (U₀ + (u : ℂ) • skewAdjointCommutator K U₀)) := by abel
      rw [heq]
      exact (norm_add_le _ _).trans (add_le_add_left hrem _)
    have hq_le : q u ≤ (‖(U₀ - W_star) + (u : ℂ) • skewAdjointCommutator K U₀‖ - ‖U₀ - W_star‖) / u +
        u * ‖K.val‖ ^ 2 * (2 + u * ‖K.val‖ / 2) := by
      dsimp only [q]
      rw [← hW_eq, ← add_div_eq_mul_add_div _ _ hu_pos'.ne']
      refine div_le_div_of_nonneg_right ?_ hu_pos'.le
      have hsq_eq : u * (u * ‖K.val‖ ^ 2 * (2 + u * ‖K.val‖ / 2)) =
          u ^ 2 * ‖K.val‖ ^ 2 * (2 + u * ‖K.val‖ / 2) := by ring
      linarith only [hinf_le, htri, hW_eq, hsq_eq]
    linarith only [hq_le, hu1, hu_quad]
  · -- Lower bound by compactness of W_opt × S₁
    intro ε hε
    by_contra hnot_ev
    rw [Filter.not_eventually] at hnot_ev
    -- Extract a sequence u_n → 0⁺ violating the lower bound
    have hex_seq (n : ℕ) : ∃ u ∈ Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)),
        ¬ (∃ W_star ∈ W_opt, ∃ ψ_star ∈ maxRightSingularSphere (U₀ - W_star),
          dirVal W_star ψ_star - ε < q u) := by
      have hmem : Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)) ∈ 𝓝[>] (0 : ℝ) :=
        Ioo_mem_nhdsGT (by positivity)
      exact (hnot_ev.and_eventually hmem).exists.imp fun u ⟨h1, h2⟩ => ⟨h2, h1⟩
    choose u hu_mem hviol using hex_seq
    have hu_tend : Tendsto u atTop (𝓝 0) :=
      squeeze_zero (fun n => (hu_mem n).1.le) (fun n => (hu_mem n).2.le)
        (tendsto_one_div_add_atTop_nhds_zero_nat)
    -- At each n, pick W_n ∈ C_j realizing infDist at u n, and ψ_n ∈ maxRightSingularSphere (U₀ - W_n)
    choose Wn hWn_mem hWn_dist using fun n =>
      exists_compactTarget_minDist hC_compact hC_ne
        (projectiveSpectralMatrix e (transverseEigenspaceFlow K V (u n)) θ)
    choose ψn hψn_mem using fun n => nonempty_maxRightSingularSphere (U₀ - Wn n)
    let P_comp := phaseCircuitMatrixImageAtMost N j ×ˢ Metric.sphere (0 : StateSpace N) 1
    have hP_compact : IsCompact P_comp := hC_compact.prod (isCompact_sphere (0 : StateSpace N) 1)
    have hseq_in (n : ℕ) : (Wn n, ψn n) ∈ P_comp :=
      ⟨hWn_mem n, mem_sphere_zero_iff_norm.mpr (hψn_mem n).1⟩
    obtain ⟨⟨W_lim, ψ_lim⟩, ⟨hW_lim_mem, hψ_lim_sph⟩, φ, hφ_mono, hφ_tend⟩ :=
      hP_compact.tendsto_subseq hseq_in
    have hW_tend : Tendsto (Wn ∘ φ) atTop (𝓝 W_lim) := (continuous_fst.tendsto _).comp hφ_tend
    have hψ_tend : Tendsto (ψn ∘ φ) atTop (𝓝 ψ_lim) := (continuous_snd.tendsto _).comp hφ_tend
    -- Show ‖U₀ - Wn (φ k)‖ → r, so W_lim ∈ W_opt and ψ_lim ∈ maxRightSingularSphere (U₀ - W_lim)
    have hflow_tend : Tendsto (fun k =>
        projectiveSpectralMatrix e (transverseEigenspaceFlow K V (u (φ k))) θ) atTop (𝓝 U₀) := by
      simp_rw [hflow_eq]
      have hev_cont : Continuous (unitaryEvolution K.val) := by
        have hL : LipschitzWith ⟨‖K.val‖, norm_nonneg _⟩ (unitaryEvolution K.val) :=
          LipschitzWith.of_dist_le_mul fun x y => by
            rw [dist_eq_norm, Real.dist_eq]; exact norm_unitaryEvolution_time_sub_le K.2 x y
        exact hL.continuous
      have h0 : unitaryEvolution K.val 0 * U₀ * star (unitaryEvolution K.val 0) = U₀ := by
        simp [unitaryEvolution]
      rw [← h0]
      exact (((hev_cont.tendsto 0).comp (hu_tend.comp hφ_mono.tendsto_atTop)).mul tendsto_const_nhds).mul
        (continuous_star.tendsto _ |>.comp ((hev_cont.tendsto 0).comp (hu_tend.comp hφ_mono.tendsto_atTop)))
    have hnorm_Wn_tend : Tendsto (fun k => ‖U₀ - Wn (φ k)‖) atTop (𝓝 ‖U₀ - W_lim‖) :=
      (continuous_const.sub continuous_id).norm.tendsto W_lim |>.comp hW_tend
    have hr_tend : Tendsto (fun k =>
        ‖projectiveSpectralMatrix e (transverseEigenspaceFlow K V (u (φ k))) θ - Wn (φ k)‖)
        atTop (𝓝 r) := by
      have heq_dist (k : ℕ) :
          ‖projectiveSpectralMatrix e (transverseEigenspaceFlow K V (u (φ k))) θ - Wn (φ k)‖ =
            Metric.infDist (projectiveSpectralMatrix e (transverseEigenspaceFlow K V (u (φ k))) θ)
              (phaseCircuitMatrixImageAtMost N j) := by
        rw [← dist_eq_norm, (hWn_dist (φ k)).symm]
      simp_rw [heq_dist]
      exact (Metric.continuous_infDist_pt _).tendsto U₀ |>.comp hflow_tend
    have hW_lim_eq : ‖U₀ - W_lim‖ = r :=
      tendsto_nhds_unique ((hflow_tend.sub hW_tend).norm.congr fun _ => rfl) hr_tend |>.symm.trans
        (tendsto_nhds_unique (by
          exact (continuous_const.sub continuous_id).norm.tendsto W_lim |>.comp hW_tend) hnorm_Wn_tend).symm
      |> fun h => by
        have h1 : Tendsto (fun k =>
            ‖projectiveSpectralMatrix e (transverseEigenspaceFlow K V (u (φ k))) θ - Wn (φ k)‖)
            atTop (𝓝 ‖U₀ - W_lim‖) := (hflow_tend.sub hW_tend).norm
        exact tendsto_nhds_unique h1 hr_tend
    have hW_lim_opt : W_lim ∈ W_opt := ⟨hW_lim_mem, hW_lim_eq⟩
    have hψ_lim_max : ψ_lim ∈ maxRightSingularSphere (U₀ - W_lim) := by
      refine ⟨mem_sphere_zero_iff_norm.mp hψ_lim_sph, ?_⟩
      have h1 : Tendsto (fun k => ‖euclCLM (U₀ - Wn (φ k)) (ψn (φ k))‖) atTop
          (𝓝 ‖euclCLM (U₀ - W_lim) ψ_lim‖) := by
        have hbilin : Continuous (fun p : Register N × StateSpace N => ‖euclCLM p.1 p.2‖) := by
          have hc : Continuous (fun p : (StateSpace N →L[ℂ] StateSpace N) × StateSpace N => p.1 p.2) :=
            isBoundedBilinearMap_apply.continuous
          exact (hc.comp (((Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ)).toContinuousLinearEquiv.continuous.comp
            continuous_fst).prodMk continuous_snd)).norm
        exact hbilin.tendsto (U₀ - W_lim, ψ_lim) |>.comp ((tendsto_const_nhds.sub hW_tend).prodMk_nhds hψ_tend)
      have h2 : Tendsto (fun k => ‖euclCLM (U₀ - Wn (φ k)) (ψn (φ k))‖) atTop (𝓝 ‖U₀ - W_lim‖) := by
        simp_rw [(hψn_mem _).2]
        exact hnorm_Wn_tend
      exact tendsto_nhds_unique h1 h2
    -- Subgradient lower bound at step φ k
    have hlim_quot : Tendsto (fun k =>
        (inner ℂ (euclCLM (U₀ - Wn (φ k)) (ψn (φ k)))
          (euclCLM (skewAdjointCommutator K U₀) (ψn (φ k)))).re / ‖U₀ - Wn (φ k)‖ -
          u (φ k) * ‖K.val‖ ^ 2 * (2 + u (φ k) * ‖K.val‖ / 2))
        atTop (𝓝 (dirVal W_lim ψ_lim)) := by
      have hnum : Tendsto (fun k =>
          (inner ℂ (euclCLM (U₀ - Wn (φ k)) (ψn (φ k)))
            (euclCLM (skewAdjointCommutator K U₀) (ψn (φ k)))).re) atTop
          (𝓝 (inner ℂ (euclCLM (U₀ - W_lim) ψ_lim)
            (euclCLM (skewAdjointCommutator K U₀) ψ_lim)).re) := by
        have happ : Continuous (fun p : Register N × StateSpace N => euclCLM p.1 p.2) :=
          isBoundedBilinearMap_apply.continuous.comp
            (((Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ)).toContinuousLinearEquiv.continuous.comp
              continuous_fst).prodMk continuous_snd)
        exact Complex.continuous_re.tendsto _ |>.comp <|
          (Continuous.inner (happ.comp ((continuous_const.sub continuous_fst).prodMk continuous_snd))
            ((euclCLM (skewAdjointCommutator K U₀)).continuous.comp continuous_snd)).tendsto
            (W_lim, ψ_lim) |>.comp (hW_tend.prodMk_nhds hψ_tend)
      have hdiv := hnum.div hnorm_Wn_tend (hW_lim_eq.symm ▸ hr.ne')
      have hrem0 : Tendsto (fun k => u (φ k) * ‖K.val‖ ^ 2 * (2 + u (φ k) * ‖K.val‖ / 2))
          atTop (𝓝 0) := by
        have hc : Continuous (fun x : ℝ => x * ‖K.val‖ ^ 2 * (2 + x * ‖K.val‖ / 2)) := by continuity
        simpa using (hc.tendsto 0).comp (hu_tend.comp hφ_mono.tendsto_atTop)
      have hsub0 := hdiv.sub hrem0
      rw [sub_zero, re_inner_unitary_sub_skewAdjointCommutator hU₀_unit W_lim K ψ_lim, hW_lim_eq] at hsub0
      exact hsub0
    obtain ⟨k, hk_gt, hk_pos⟩ := ((hlim_quot.eventually (Ioi_mem_nhds (sub_lt_self (dirVal W_lim ψ_lim) hε))).and
      (hnorm_Wn_tend.eventually (Ioi_mem_nhds (hW_lim_eq.symm ▸ hr)))).exists
    have hu_pos : 0 < u (φ k) := (hu_mem (φ k)).1
    have hstep_ge : (inner ℂ (euclCLM (U₀ - Wn (φ k)) (ψn (φ k)))
        (euclCLM (skewAdjointCommutator K U₀) (ψn (φ k)))).re / ‖U₀ - Wn (φ k)‖ -
          u (φ k) * ‖K.val‖ ^ 2 * (2 + u (φ k) * ‖K.val‖ / 2) ≤ q (u (φ k)) := by
      have hr_le_Wk : r ≤ ‖U₀ - Wn (φ k)‖ := by
        rw [← dist_eq_norm]
        exact Metric.infDist_le_dist_of_mem (hWn_mem (φ k))
      have hsubg := opNorm_add_smul_ge_of_mem_maxRightSingularSphere hk_pos (hψn_mem (φ k))
        (skewAdjointCommutator K U₀) (u (φ k))
      have hrem := norm_conj_unitaryEvolution_sub_linear_le K hU₀_norm hu_pos.le
      have htri : ‖(U₀ - Wn (φ k)) + (u (φ k) : ℂ) • skewAdjointCommutator K U₀‖ -
          u (φ k) ^ 2 * ‖K.val‖ ^ 2 * (2 + u (φ k) * ‖K.val‖ / 2) ≤
          ‖unitaryEvolution K.val (u (φ k)) * U₀ * star (unitaryEvolution K.val (u (φ k))) - Wn (φ k)‖ := by
        have heq : (U₀ - Wn (φ k)) + (u (φ k) : ℂ) • skewAdjointCommutator K U₀ =
            (unitaryEvolution K.val (u (φ k)) * U₀ * star (unitaryEvolution K.val (u (φ k))) - Wn (φ k)) -
              (unitaryEvolution K.val (u (φ k)) * U₀ * star (unitaryEvolution K.val (u (φ k))) -
                (U₀ + (u (φ k) : ℂ) • skewAdjointCommutator K U₀)) := by abel
        have hle := norm_sub_le
          (unitaryEvolution K.val (u (φ k)) * U₀ * star (unitaryEvolution K.val (u (φ k))) - Wn (φ k))
          (unitaryEvolution K.val (u (φ k)) * U₀ * star (unitaryEvolution K.val (u (φ k))) -
            (U₀ + (u (φ k) : ℂ) • skewAdjointCommutator K U₀))
        rw [← heq] at hle
        linarith only [hle, hrem]
      have hdist_eq : Metric.infDist
          (projectiveSpectralMatrix e (transverseEigenspaceFlow K V (u (φ k))) θ)
          (phaseCircuitMatrixImageAtMost N j) =
          ‖unitaryEvolution K.val (u (φ k)) * U₀ * star (unitaryEvolution K.val (u (φ k))) - Wn (φ k)‖ := by
        rw [← hflow_eq (u (φ k)), ← dist_eq_norm, (hWn_dist (φ k)).symm]
      dsimp only [q]
      rw [hdist_eq, le_div_iff₀ hu_pos]
      have hsq_eq : u (φ k) * (u (φ k) * ‖K.val‖ ^ 2 * (2 + u (φ k) * ‖K.val‖ / 2)) =
          u (φ k) ^ 2 * ‖K.val‖ ^ 2 * (2 + u (φ k) * ‖K.val‖ / 2) := by ring
      nlinarith only [hr_le_Wk, hsubg, htri, hsq_eq, hu_pos]
    exact hviol (φ k) ⟨W_lim, hW_lim_opt, ψ_lim, hψ_lim_max, lt_of_lt_of_le hk_gt hstep_ge⟩

/-- Lower Dini envelope bound for `u ↦ torusCriticalHeight e (transverseEigenspaceFlow K V u) j`
at any maximizing phase point `θ_⋆`. -/
theorem liminf_torusCriticalHeight_transverseFlow_ge {N d : ℕ} (e : Config N ≃ Fin (d + 1))
    (V : UGroup N) (K : selfAdjoint (Register N)) (j : ℕ) (θ_star : Fin d → UnitAddCircle)
    (hmax : torusCriticalHeight e V j =
      Metric.infDist (projectiveSpectralMatrix e V θ_star) (phaseCircuitMatrixImageAtMost N j))
    (hr : 0 < torusCriticalHeight e V j) :
    let U₀ := projectiveSpectralMatrix e V θ_star
    let r := torusCriticalHeight e V j
    let W_opt := {W ∈ phaseCircuitMatrixImageAtMost N j | ‖U₀ - W‖ = r}
    ∀ ε > 0, ∀ᶠ u in 𝓝[>] 0,
      ∃ W_star ∈ W_opt, ∃ ψ_star ∈ maxRightSingularSphere (U₀ - W_star),
        -(inner ℂ (euclCLM W_star ψ_star) (euclCLM (K.val * U₀ - U₀ * K.val) ψ_star)).im / r - ε <
          (torusCriticalHeight e (transverseEigenspaceFlow K V u) j - r) / u := by
  intro U₀ r W_opt ε hε
  have hr' : 0 < Metric.infDist U₀ (phaseCircuitMatrixImageAtMost N j) := hmax ▸ hr
  have hsand := (dini_torusPointDistance_sandwich e V K j θ_star hr').2.2 ε hε
  filter_upwards [Ioi_mem_nhdsGT (0 : ℝ), hsand] with u hu_pos ⟨W_star, hW, ψ_star, hψ, hlt⟩
  have hu_pos' : 0 < u := hu_pos
  have hpt_le : Metric.infDist (projectiveSpectralMatrix e (transverseEigenspaceFlow K V u) θ_star)
      (phaseCircuitMatrixImageAtMost N j) ≤
      torusCriticalHeight e (transverseEigenspaceFlow K V u) j := by
    unfold torusCriticalHeight
    refine le_csSup ?_ (mem_range_self θ_star)
    obtain ⟨θ_m, _, hθ_m, _⟩ := exists_torusCriticalHeight_saddle e (transverseEigenspaceFlow K V u) j
    exact ⟨2, by
      rintro _ ⟨θ, rfl⟩
      have h1 : (1 : ℂ) • ((TwoQubitCircuit.one N).eval : Register N) ∈
          phaseCircuitMatrixImageAtMost N j :=
        mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨1, norm_one, TwoQubitCircuit.one N, Nat.zero_le _, rfl⟩
      refine (Metric.infDist_le_dist_of_mem h1).trans ?_
      rw [dist_eq_norm, one_smul, TwoQubitCircuit.one_eval]
      have hunit : projectiveSpectralMatrix e (transverseEigenspaceFlow K V u) θ ∈ unitary (Register N) := by
        unfold projectiveSpectralMatrix
        refine mul_mem (mul_mem (transverseEigenspaceFlow K V u).2 ?_)
          (Unitary.star_mem (transverseEigenspaceFlow K V u).2)
        rw [Unitary.mem_iff, star_eq_conjTranspose, diagonal_conjTranspose,
          diagonal_mul_diagonal, diagonal_mul_diagonal]
        constructor <;> ext a b <;> by_cases hab : a = b
        · subst hab; simp only [diagonal_apply_eq, one_apply_eq]
          exact Complex.normSq_eq_conj_mul_self.symm.trans (by simp)
        · simp [hab]
        · subst hab; simp only [diagonal_apply_eq, one_apply_eq]; rw [mul_comm]
          exact Complex.normSq_eq_conj_mul_self.symm.trans (by simp)
        · simp [hab]
      linarith only [norm_sub_le (projectiveSpectralMatrix e (transverseEigenspaceFlow K V u) θ) 1,
        CStarRing.norm_of_mem_unitary hunit, norm_one (α := Register N)]⟩
  have hW' : W_star ∈ W_opt := by simpa only [W_opt, r, hmax] using hW
  refine ⟨W_star, hW', ψ_star, hψ, ?_⟩
  have hlt' : -(inner ℂ (euclCLM W_star ψ_star) (euclCLM (K.val * U₀ - U₀ * K.val) ψ_star)).im / r - ε <
      (Metric.infDist (projectiveSpectralMatrix e (transverseEigenspaceFlow K V u) θ_star)
        (phaseCircuitMatrixImageAtMost N j) - r) / u := by
    simpa only [r, hmax] using hlt
  exact hlt'.trans_le (div_le_div_of_nonneg_right (sub_le_sub_right hpt_le r) hu_pos'.le)

/-! ## Section 3: Unitary-ratio eigenmode formula and Pauli-commutator `[P, H]` classification -/

/-- For any two unitaries `U_⋆, W_⋆ ∈ U(2^N)` at distance `r = ‖U_⋆ - W_⋆‖ > 0`, there exist a
maximal right singular vector `ψ ∈ maxRightSingularSphere (U_⋆ - W_⋆)` and `β ∈ ℝ` with
`β² = r² * (1 - r² / 4)` and `W_⋆ ψ = (1 - r² / 2 + i β) • U_⋆ ψ`, reducing the transverse
commutator variation on `ψ` to `(β / r) * (Re ⟨U_⋆ ψ, K U_⋆ ψ⟩ - Re ⟨ψ, K ψ⟩)`. -/
theorem exists_unitaryRatio_singularEigenmode {N : ℕ} (U_star W_star : UGroup N)
    (hr : 0 < ‖U_star.val - W_star.val‖) :
    let r := ‖U_star.val - W_star.val‖
    ∃ ψ ∈ maxRightSingularSphere (U_star.val - W_star.val), ∃ β : ℝ,
      β ^ 2 = r ^ 2 * (1 - r ^ 2 / 4) ∧
      euclCLM W_star.val ψ = (((1 - r ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)) • euclCLM U_star.val ψ ∧
      ‖inner ℂ ψ (euclCLM W_star.val ψ)‖ = ‖inner ℂ ψ (euclCLM U_star.val ψ)‖ ∧
      ∀ K : selfAdjoint (Register N),
        (inner ℂ (euclCLM (U_star.val - W_star.val) ψ)
          (euclCLM (skewAdjointCommutator K U_star.val) ψ)).re / r =
          (β / r) * ((inner ℂ (euclCLM U_star.val ψ) (euclCLM K.val (euclCLM U_star.val ψ))).re -
            (inner ℂ ψ (euclCLM K.val ψ)).re) := by
  intro r
  let Z : Register N := star U_star.val * W_star.val
  have hZ_unit : Z ∈ unitary (Register N) := mul_mem (Unitary.star_mem U_star.2) W_star.2
  have hadj (M : Register N) (x y : StateSpace N) :
      inner ℂ (euclCLM (star M) x) y = inner ℂ x (euclCLM M y) := by
    have hstar : euclCLM (star M) = ContinuousLinearMap.adjoint (euclCLM M) :=
      map_star Matrix.toEuclideanCLM M
    rw [hstar, ContinuousLinearMap.adjoint_inner_left]
  -- Gap operator H_gap = (U_⋆ - W_⋆)* (U_⋆ - W_⋆) = 2 - (Z + Z*)
  let H_gap : Register N := star (U_star.val - W_star.val) * (U_star.val - W_star.val)
  have hH_gap_eq : H_gap = (2 : ℂ) • (1 : Register N) - (Z + star Z) := by
    dsimp only [H_gap, Z]
    rw [star_sub, sub_mul, mul_sub, mul_sub, (Unitary.mem_iff.mp U_star.2).1,
      (Unitary.mem_iff.mp W_star.2).1, star_mul, star_star]
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    ring
  have hH_gap_norm : ‖H_gap‖ = r ^ 2 := by
    dsimp only [H_gap, r]
    rw [star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose_mul_self, sq]
  -- Every ξ ∈ maxRightSingularSphere (U_⋆ - W_⋆) lies in ker (H_gap - r^2 • 1)
  let L_gap : StateSpace N →ₗ[ℂ] StateSpace N :=
    (euclCLM (H_gap - ((r ^ 2 : ℝ) : ℂ) • (1 : Register N))).toLinearMap
  let E : Submodule ℂ (StateSpace N) := LinearMap.ker L_gap
  obtain ⟨ξ₀, hξ₀_mem⟩ := nonempty_maxRightSingularSphere (U_star.val - W_star.val)
  have hξ₀_in_E : ξ₀ ∈ E := by
    rw [LinearMap.mem_ker]
    -- Compute ‖H_gap ξ₀ - r^2 ξ₀‖^2 = ‖H_gap ξ₀‖^2 - 2 r^2 ⟨ξ₀, H_gap ξ₀⟩ + r^4 ‖ξ₀‖^2 ≤ 0
    have hquad : inner ℂ ξ₀ (euclCLM H_gap ξ₀) = ((r ^ 2 : ℝ) : ℂ) := by
      dsimp only [H_gap]
      rw [map_mul, ContinuousLinearMap.mul_apply, hadj, inner_self_eq_norm_sq_to_K, hξ₀_mem.2]
      simp [r, Complex.ofReal_cpow (norm_nonneg _), ← Complex.ofReal_pow]
    have hnorm_Hξ : ‖euclCLM H_gap ξ₀‖ ≤ r ^ 2 := by
      have h1 := (euclCLM H_gap).le_opNorm ξ₀
      rwa [Matrix.l2_opNorm_toEuclideanCLM, hH_gap_norm, hξ₀_mem.1, mul_one] at h1
    have hdiff_sq : ‖L_gap ξ₀‖ ^ 2 ≤ 0 := by
      change ‖euclCLM H_gap ξ₀ - ((r ^ 2 : ℝ) : ℂ) • ξ₀‖ ^ 2 ≤ 0
      rw [@norm_sub_sq ℂ, inner_smul_right, hquad, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (sq_nonneg r), hξ₀_mem.1, mul_one]
      have hre : (starRingEnd ℂ ((r ^ 2 : ℝ) : ℂ) * ((r ^ 2 : ℝ) : ℂ)).re = (r ^ 2) ^ 2 := by
        rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
      -- Wait: @norm_sub_sq ℂ has - 2 * (inner ℂ (euclCLM H_gap ξ₀) (((r^2 : ℝ) : ℂ) • ξ₀)).re
      have hinner_rev : (inner ℂ (euclCLM H_gap ξ₀) (((r ^ 2 : ℝ) : ℂ) • ξ₀)).re = (r ^ 2) ^ 2 := by
        rw [inner_smul_right, ← inner_conj_symm, hquad, Complex.conj_ofReal,
          ← Complex.ofReal_mul, Complex.ofReal_re]
        ring
      linarith only [pow_le_pow_left₀ (norm_nonneg _) hnorm_Hξ 2, hinner_rev]
    exact norm_le_zero_iff.mp (sq_eq_zero_iff.mp (le_antisymm hdiff_sq (sq_nonneg _))).le
  have hE_pos : 0 < Module.finrank ℂ E := by
    refine Module.finrank_pos_iff.mpr ⟨⟨ξ₀, hξ₀_in_E⟩, ?_⟩
    intro h0
    have hnorm0 : ‖ξ₀‖ = 0 := by rw [show ξ₀ = 0 from congrArg Subtype.val h0, norm_zero]
    linarith only [hξ₀_mem.1, hnorm0]
  -- Skew-part B = (-I / 2) • (Z - star Z) commutes with H_gap, hence preserves E and is symmetric
  let Bmat : Register N := (-Complex.I / 2) • (Z - star Z)
  have hB_herm : IsSelfAdjoint Bmat := by
    dsimp only [Bmat]
    rw [IsSelfAdjoint, star_smul, star_sub, star_star, star_div₀, star_neg,
      Complex.star_def, Complex.conj_I, Complex.conj_ofNat, neg_neg, ← smul_neg, neg_sub]
  have hcomm : (H_gap - ((r ^ 2 : ℝ) : ℂ) • (1 : Register N)) * Bmat =
      Bmat * (H_gap - ((r ^ 2 : ℝ) : ℂ) • (1 : Register N)) := by
    rw [hH_gap_eq]
    dsimp only [Bmat]
    have hZZ1 : Z * star Z = 1 := (Unitary.mem_iff.mp hZ_unit).2
    have hZZ2 : star Z * Z = 1 := (Unitary.mem_iff.mp hZ_unit).1
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc ((2 : ℂ) • (1 : Register N) - (Z + star Z) - ((r ^ 2 : ℝ) : ℂ) • 1) * (Z - star Z)
        = ((2 : ℂ) - ((r ^ 2 : ℝ) : ℂ)) • (Z - star Z) - (Z * Z - Z * star Z + star Z * Z - star Z * star Z) := by
          ext a b
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_add,
            Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Matrix.sub_apply,
            Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
          ring
      _ = (Z - star Z) * ((2 : ℂ) • (1 : Register N) - (Z + star Z) - ((r ^ 2 : ℝ) : ℂ) • 1) := by
          rw [hZZ1, hZZ2]
          ext a b
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_add,
            Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Matrix.sub_apply,
            Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
          ring
  let B_E : E →ₗ[ℂ] E :=
    { toFun := fun x => ⟨euclCLM Bmat x.1, by
        rw [LinearMap.mem_ker]
        change euclCLM ((H_gap - ((r ^ 2 : ℝ) : ℂ) • 1) * Bmat) x.1 = 0
        rw [hcomm, map_mul, ContinuousLinearMap.mul_apply]
        have hx0 : euclCLM (H_gap - ((r ^ 2 : ℝ) : ℂ) • 1) x.1 = 0 := x.2
        rw [hx0, map_zero]⟩
      map_add' := fun x y => Subtype.ext (map_add (euclCLM Bmat) x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_smul (euclCLM Bmat) c x.1) }
  have hB_sym : B_E.IsSymmetric := by
    intro x y
    change inner ℂ (euclCLM Bmat x.1) y.1 = inner ℂ x.1 (euclCLM Bmat y.1)
    rw [← hadj Bmat x.1 y.1, hB_herm.star_eq]
  let i₀ : Fin (Module.finrank ℂ E) := ⟨0, hE_pos⟩
  let u_eig : E := hB_sym.eigenvectorBasis rfl i₀
  let β : ℝ := hB_sym.eigenvalues rfl i₀
  let ψ : StateSpace N := u_eig.1
  have hψ_norm : ‖ψ‖ = 1 := by
    change ‖u_eig‖ = 1
    exact (hB_sym.eigenvectorBasis rfl).orthonormal.1 i₀
  have hBψ : euclCLM Bmat ψ = (β : ℂ) • ψ :=
    congrArg Subtype.val (hB_sym.apply_eigenvectorBasis rfl i₀)
  have hHψ : euclCLM H_gap ψ = ((r ^ 2 : ℝ) : ℂ) • ψ := by
    have hz : euclCLM (H_gap - ((r ^ 2 : ℝ) : ℂ) • 1) ψ = 0 := u_eig.2
    rw [map_sub, map_smul, map_one, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, sub_eq_zero] at hz
    exact hz
  have hψ_mem : ψ ∈ maxRightSingularSphere (U_star.val - W_star.val) := by
    refine ⟨hψ_norm, ?_⟩
    have hsq : ‖euclCLM (U_star.val - W_star.val) ψ‖ ^ 2 = r ^ 2 := by
      have h1 : inner ℂ ψ (euclCLM H_gap ψ) = ((‖euclCLM (U_star.val - W_star.val) ψ‖ ^ 2 : ℝ) : ℂ) := by
        dsimp only [H_gap]
        rw [map_mul, ContinuousLinearMap.mul_apply, hadj, inner_self_eq_norm_sq_to_K]
        simp [Complex.ofReal_cpow (norm_nonneg _), ← Complex.ofReal_pow]
      rw [hHψ, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ_norm] at h1
      simpa using congrArg Complex.re h1.symm
    exact (sq_eq_sq₀ (norm_nonneg _) hr.le).mp hsq
  have hZψ : euclCLM Z ψ = (((1 - r ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)) • ψ := by
    have hsum : euclCLM (Z + star Z) ψ = ((2 - r ^ 2 : ℝ) : ℂ) • ψ := by
      have h1 : Z + star Z = (2 : ℂ) • (1 : Register N) - H_gap := by
        rw [hH_gap_eq]; abel
      rw [h1, map_sub, map_smul, map_one, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, hHψ, ← sub_smul]
      congr 1; push_cast; ring
    have hdiff : euclCLM (Z - star Z) ψ = ((2 : ℂ) * Complex.I * (β : ℂ)) • ψ := by
      have h1 : Z - star Z = ((2 : ℂ) * Complex.I) • Bmat := by
        dsimp only [Bmat]
        rw [smul_smul]
        have hc : (2 : ℂ) * Complex.I * (-Complex.I / 2) = 1 := by
          calc (2 : ℂ) * Complex.I * (-Complex.I / 2)
              = -(Complex.I * Complex.I) := by ring
            _ = 1 := by rw [Complex.I_mul_I, neg_neg]
        rw [hc, one_smul]
      rw [h1, map_smul, ContinuousLinearMap.smul_apply, hBψ, smul_smul, mul_assoc]
    have hZ_half : Z = ((1 / 2 : ℂ) • (Z + star Z)) + ((1 / 2 : ℂ) • (Z - star Z)) := by
      ext a b; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    conv_lhs => rw [hZ_half]
    rw [map_add, map_smul, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
      hsum, hdiff, smul_smul, smul_smul, ← add_smul]
    congr 1; push_cast; ring
  have hWψ : euclCLM W_star.val ψ =
      (((1 - r ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)) • euclCLM U_star.val ψ := by
    have hUZ : U_star.val * Z = W_star.val := by
      dsimp only [Z]
      rw [← mul_assoc, (Unitary.mem_iff.mp U_star.2).2, one_mul]
    rw [← hUZ, map_mul, ContinuousLinearMap.mul_apply, hZψ, map_smul]
  have hλ_norm_sq : (1 - r ^ 2 / 2) ^ 2 + β ^ 2 = 1 := by
    have hZ_isom : ‖euclCLM Z ψ‖ = 1 := by
      have h1 : inner ℂ (euclCLM Z ψ) (euclCLM Z ψ) = 1 := by
        rw [← hadj Z, ← ContinuousLinearMap.mul_apply, ← map_mul,
          (Unitary.mem_iff.mp hZ_unit).1, map_one, ContinuousLinearMap.one_apply,
          inner_self_eq_norm_sq_to_K, hψ_norm]
        norm_num
      rw [inner_self_eq_norm_sq_to_K] at h1
      have hsq : ‖euclCLM Z ψ‖ ^ 2 = 1 := by simpa using congrArg Complex.re h1
      nlinarith only [hsq, norm_nonneg (euclCLM Z ψ)]
    rw [hZψ, norm_smul, hψ_norm, mul_one] at hZ_isom
    have hc_eq : (((1 - r ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)) =
        ⟨1 - r ^ 2 / 2, β⟩ := by
      apply Complex.ext <;> simp
    rw [hc_eq] at hZ_isom
    have hsq := congrArg (· ^ 2) hZ_isom
    rw [one_pow, Complex.sq_norm, Complex.normSq_mk] at hsq
    linarith only [hsq]
  have hβ_sq : β ^ 2 = r ^ 2 * (1 - r ^ 2 / 4) := by linarith only [hλ_norm_sq]
  have hλ_norm : ‖(((1 - r ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ))‖ = 1 := by
    have hc_eq : (((1 - r ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)) = ⟨1 - r ^ 2 / 2, β⟩ := by
      apply Complex.ext <;> simp
    rw [hc_eq, Complex.norm_def, Complex.normSq_mk]
    rw [show (1 - r ^ 2 / 2) * (1 - r ^ 2 / 2) + β * β = 1 by linarith only [hλ_norm_sq], Real.sqrt_one]
  refine ⟨ψ, hψ_mem, β, hβ_sq, hWψ, ?_, ?_⟩
  · rw [hWψ, inner_smul_right, norm_mul, hλ_norm, one_mul]
  · intro K
    have hadj_K (x : StateSpace N) : (inner ℂ x (euclCLM K.val x)).im = 0 := by
      have hsym : inner ℂ x (euclCLM K.val x) = starRingEnd ℂ (inner ℂ x (euclCLM K.val x)) := by
        rw [inner_conj_symm, ← hadj K.val x x, K.2.star_eq]
      exact Complex.conj_eq_iff_im.mp hsym.symm
    rw [re_inner_unitary_sub_skewAdjointCommutator U_star.2 W_star.val K ψ, hWψ, inner_smul_left]
    have hcomm_inner : inner ℂ (euclCLM U_star.val ψ) (euclCLM (K.val * U_star.val - U_star.val * K.val) ψ) =
        inner ℂ (euclCLM U_star.val ψ) (euclCLM K.val (euclCLM U_star.val ψ)) -
          inner ℂ ψ (euclCLM K.val ψ) := by
      rw [map_sub, ContinuousLinearMap.sub_apply, inner_sub_right, map_mul,
        ContinuousLinearMap.mul_apply, map_mul, ContinuousLinearMap.mul_apply, ← hadj U_star.val,
        ← ContinuousLinearMap.mul_apply, ← map_mul, (Unitary.mem_iff.mp U_star.2).1,
        map_one, ContinuousLinearMap.one_apply]
    rw [hcomm_inner]
    set d : ℝ := (inner ℂ (euclCLM U_star.val ψ) (euclCLM K.val (euclCLM U_star.val ψ))).re -
      (inner ℂ ψ (euclCLM K.val ψ)).re
    have hd_eq : inner ℂ (euclCLM U_star.val ψ) (euclCLM K.val (euclCLM U_star.val ψ)) -
        inner ℂ ψ (euclCLM K.val ψ) = (d : ℂ) := by
      apply Complex.ext
      · simp [d]
      · simp [hadj_K (euclCLM U_star.val ψ), hadj_K ψ]
    rw [hd_eq]
    have him : -((starRingEnd ℂ (((1 - r ^ 2 / 2 : ℝ) : ℂ) + Complex.I * (β : ℂ)) * (d : ℂ)).im) =
        β * d := by
      simp [Complex.mul_im]
    rw [him, mul_div_right_comm]

/-- Exact supremum of `|Re ⟨ξ, K ξ⟩ - Re ⟨ψ, K ψ⟩|` over unit-norm self-adjoint operators `K`:
bounded above by `2 * √(1 - ‖⟨ψ, ξ⟩‖²) * ‖K‖` and attained at norm `≤ 1`. -/
theorem sup_selfAdjoint_expectation_diff_eq {N : ℕ} {ξ ψ : StateSpace N}
    (hξ : ‖ξ‖ = 1) (hψ : ‖ψ‖ = 1) :
    (∀ K : selfAdjoint (Register N),
      |(inner ℂ ξ (euclCLM K.val ξ)).re - (inner ℂ ψ (euclCLM K.val ψ)).re| ≤
        2 * Real.sqrt (1 - ‖inner ℂ ψ ξ‖ ^ 2) * ‖K.val‖) ∧
    ∃ K_star : selfAdjoint (Register N), ‖K_star.val‖ ≤ 1 ∧
      (inner ℂ ξ (euclCLM K_star.val ξ)).re - (inner ℂ ψ (euclCLM K_star.val ψ)).re =
        2 * Real.sqrt (1 - ‖inner ℂ ψ ξ‖ ^ 2) := by
  let c : ℂ := inner ℂ ψ ξ
  have hc_le : ‖c‖ ≤ 1 := by
    simpa only [hψ, hξ, mul_one] using norm_inner_le_norm ψ ξ
  have h1_sub : 0 ≤ 1 - ‖c‖ ^ 2 := by nlinarith only [hc_le, norm_nonneg c]
  -- Phase-align ξ' = w • ξ so ⟨ψ, ξ'⟩ = ‖c‖ ∈ ℝ
  let w : ℂ := if c = 0 then 1 else star c / ‖c‖
  have hw_norm : ‖w‖ = 1 := by
    dsimp only [w]
    split_ifs with hc0
    · exact norm_one
    · rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg c),
        div_self (norm_ne_zero_iff.mpr hc0)]
  have hwc : w * c = (‖c‖ : ℂ) := by
    dsimp only [w]
    split_ifs with hc0
    · simp [hc0]
    · have hconj : star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast; rfl
      rw [div_mul_eq_mul_div, hconj]
      have hne : (‖c‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc0)
      push_cast; field_simp [hne]
  let ξ' : StateSpace N := w • ξ
  have hξ'_norm : ‖ξ'‖ = 1 := by rw [norm_smul, hw_norm, hξ, mul_one]
  have hinner_ξ' : inner ℂ ψ ξ' = (‖c‖ : ℂ) := by
    rw [inner_smul_right]; exact hwc
  let p : StateSpace N := ξ' + ψ
  let q : StateSpace N := ξ' - ψ
  have hpq_orth : inner ℂ p q = 0 := by
    dsimp only [p, q]
    rw [inner_sub_right, inner_add_left, inner_add_left,
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hξ'_norm, hψ,
      ← inner_conj_symm ξ' ψ, hinner_ξ', Complex.conj_ofReal]
    ring
  have hp_sq : ‖p‖ ^ 2 = 2 * (1 + ‖c‖) := by
    dsimp only [p]
    rw [@norm_add_sq ℂ, hξ'_norm, hψ, ← inner_conj_symm ξ' ψ, hinner_ξ',
      Complex.conj_ofReal, Complex.ofReal_re]
    ring
  have hq_sq : ‖q‖ ^ 2 = 2 * (1 - ‖c‖) := by
    dsimp only [q]
    rw [@norm_sub_sq ℂ, hξ'_norm, hψ, ← inner_conj_symm ξ' ψ, hinner_ξ',
      Complex.conj_ofReal, Complex.ofReal_re]
    ring
  have hpq_prod : ‖p‖ * ‖q‖ = 2 * Real.sqrt (1 - ‖c‖ ^ 2) := by
    have hsq : (‖p‖ * ‖q‖) ^ 2 = (2 * Real.sqrt (1 - ‖c‖ ^ 2)) ^ 2 := by
      rw [mul_pow, hp_sq, hq_sq, mul_pow, Real.sq_sqrt h1_sub]
      ring
    exact (sq_eq_sq₀ (by positivity) (by positivity)).mp hsq
  have hadj (M : Register N) (x y : StateSpace N) :
      inner ℂ (euclCLM (star M) x) y = inner ℂ x (euclCLM M y) := by
    have hstar : euclCLM (star M) = ContinuousLinearMap.adjoint (euclCLM M) :=
      map_star Matrix.toEuclideanCLM M
    rw [hstar, ContinuousLinearMap.adjoint_inner_left]
  -- Polarization: Re ⟨ξ, K ξ⟩ - Re ⟨ψ, K ψ⟩ = Re ⟨p, K q⟩
  have hpol (K : selfAdjoint (Register N)) :
      (inner ℂ ξ (euclCLM K.val ξ)).re - (inner ℂ ψ (euclCLM K.val ψ)).re =
        (inner ℂ p (euclCLM K.val q)).re := by
    have hξ_eq : inner ℂ ξ' (euclCLM K.val ξ') = inner ℂ ξ (euclCLM K.val ξ) := by
      dsimp only [ξ']
      rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc]
      have hww : starRingEnd ℂ w * w = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hw_norm, one_pow,
          Complex.ofReal_one]
      rw [hww, one_mul]
    dsimp only [p, q]
    rw [map_sub, inner_sub_right, inner_add_left, inner_add_left, Complex.sub_re,
      Complex.add_re, Complex.add_re, hξ_eq]
    have hsym : (inner ℂ ψ (euclCLM K.val ξ')).re = (inner ℂ ξ' (euclCLM K.val ψ)).re := by
      have h1 : inner ℂ ψ (euclCLM K.val ξ') = starRingEnd ℂ (inner ℂ ξ' (euclCLM K.val ψ)) := by
        rw [inner_conj_symm, ← hadj K.val ξ' ψ, K.2.star_eq]
      rw [h1, Complex.conj_re]
    linarith only [hsym]
  refine ⟨fun K => ?_, ?_⟩
  · rw [hpol K]
    calc |(inner ℂ p (euclCLM K.val q)).re|
        ≤ ‖inner ℂ p (euclCLM K.val q)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖p‖ * ‖euclCLM K.val q‖ := norm_inner_le_norm p _
      _ ≤ ‖p‖ * (‖K.val‖ * ‖q‖) := mul_le_mul_of_nonneg_left
          (by simpa only [Matrix.l2_opNorm_toEuclideanCLM] using (euclCLM K.val).le_opNorm q)
          (norm_nonneg p)
      _ = 2 * Real.sqrt (1 - ‖c‖ ^ 2) * ‖K.val‖ := by rw [← mul_assoc, mul_right_comm, hpq_prod]
  · by_cases hΔ : 1 - ‖c‖ ^ 2 = 0
    · refine ⟨0, by simp, ?_⟩
      rw [hΔ, Real.sqrt_zero, mul_zero]
      simp
    · have hΔ_pos : 0 < 1 - ‖c‖ ^ 2 := lt_of_le_of_ne h1_sub (Ne.symm hΔ)
      have hpq_pos : 0 < ‖p‖ * ‖q‖ := by rw [hpq_prod]; exact mul_pos zero_lt_two (Real.sqrt_pos.mpr hΔ_pos)
      have hp_pos : 0 < ‖p‖ := (mul_pos_iff_of_pos_right (lt_of_le_of_ne (norm_nonneg q)
        (fun h0 => by simp [← h0] at hpq_pos))).mp hpq_pos
      have hq_pos : 0 < ‖q‖ := (mul_pos_iff_of_pos_left hp_pos).mp hpq_pos
      let p_hat : StateSpace N := ((‖p‖⁻¹ : ℝ) : ℂ) • p
      let q_hat : StateSpace N := ((‖q‖⁻¹ : ℝ) : ℂ) • q
      have hp_hat_norm : ‖p_hat‖ = 1 := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hp_pos.ne']
      have hq_hat_norm : ‖q_hat‖ = 1 := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hq_pos.ne']
      have hpq_hat_orth : inner ℂ p_hat q_hat = 0 := by
        dsimp only [p_hat, q_hat]
        rw [inner_smul_left, inner_smul_right, hpq_orth, mul_zero, mul_zero]
      -- Construct the continuous linear swap T_star x = ⟨q_hat, x⟩ • p_hat + ⟨p_hat, x⟩ • q_hat
      let T_lin : StateSpace N →ₗ[ℂ] StateSpace N :=
        { toFun := fun x => inner ℂ q_hat x • p_hat + inner ℂ p_hat x • q_hat
          map_add' := fun x y => by simp only [inner_add_right, add_smul]; abel
          map_smul' := fun a x => by
            simp only [inner_smul_right, RingHom.id_apply, smul_add, mul_smul] }
      let T_clm : StateSpace N →L[ℂ] StateSpace N := T_lin.toContinuousLinearMap
      let K_mat : Register N := (Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ)).symm T_clm
      have heucl_K : euclCLM K_mat = T_clm :=
        (Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ)).apply_symm_apply T_clm
      have hK_sa : IsSelfAdjoint K_mat := by
        rw [IsSelfAdjoint]
        apply (Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ)).injective
        rw [map_star, heucl_K]
        ext x
        apply ext_inner_left ℂ
        intro y
        rw [ContinuousLinearMap.adjoint_inner_right]
        change inner ℂ y (inner ℂ q_hat x • p_hat + inner ℂ p_hat x • q_hat) =
          inner ℂ (inner ℂ q_hat y • p_hat + inner ℂ p_hat y • q_hat) x
        rw [inner_add_right, inner_smul_right, inner_smul_right,
          inner_add_left, inner_smul_left, inner_smul_left,
          ← inner_conj_symm p_hat y, ← inner_conj_symm q_hat y,
          ← inner_conj_symm x q_hat, ← inner_conj_symm x p_hat]
        ring
      have hK_norm : ‖K_mat‖ ≤ 1 := by
        rw [← Matrix.l2_opNorm_toEuclideanCLM, heucl_K]
        refine T_clm.opNorm_le_bound zero_le_one fun x => ?_
        rw [one_mul]
        refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
        change ‖inner ℂ q_hat x • p_hat + inner ℂ p_hat x • q_hat‖ ^ 2 ≤ ‖x‖ ^ 2
        rw [@norm_add_sq ℂ, inner_smul_left, inner_smul_right, hpq_hat_orth,
          mul_zero, mul_zero, Complex.zero_re, mul_zero, add_zero,
          norm_smul, norm_smul, hp_hat_norm, hq_hat_norm, mul_one, mul_one]
        -- Bessel inequality for orthonormal pair {p_hat, q_hat}
        let r_res : StateSpace N := x - (inner ℂ p_hat x • p_hat + inner ℂ q_hat x • q_hat)
        have hexp_x : x = (inner ℂ p_hat x • p_hat + inner ℂ q_hat x • q_hat) + r_res := by
          dsimp only [r_res]; abel
        have horth_r : inner ℂ (inner ℂ p_hat x • p_hat + inner ℂ q_hat x • q_hat) r_res = 0 := by
          dsimp only [r_res]
          rw [inner_sub_right, inner_add_left, inner_add_left, inner_add_right, inner_add_right,
            inner_smul_left, inner_smul_left, inner_smul_left,
            inner_smul_right, inner_smul_right, inner_smul_right, inner_smul_right,
            inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
            hp_hat_norm, hq_hat_norm, hpq_hat_orth, ← inner_conj_symm p_hat q_hat, hpq_hat_orth]
          simp; ring
        have hx_sq : ‖x‖ ^ 2 = ‖inner ℂ p_hat x • p_hat + inner ℂ q_hat x • q_hat‖ ^ 2 + ‖r_res‖ ^ 2 := by
          conv_lhs => rw [hexp_x]
          rw [@norm_add_sq ℂ, horth_r, Complex.zero_re, mul_zero, add_zero]
        have hproj_sq : ‖inner ℂ p_hat x • p_hat + inner ℂ q_hat x • q_hat‖ ^ 2 =
            ‖inner ℂ p_hat x‖ ^ 2 + ‖inner ℂ q_hat x‖ ^ 2 := by
          rw [@norm_add_sq ℂ, inner_smul_left, inner_smul_right, hpq_hat_orth,
            mul_zero, mul_zero, Complex.zero_re, mul_zero, add_zero,
            norm_smul, norm_smul, hp_hat_norm, hq_hat_norm, mul_one, mul_one]
        linarith only [hx_sq, hproj_sq, sq_nonneg ‖r_res‖]
      refine ⟨⟨K_mat, hK_sa⟩, hK_norm, ?_⟩
      rw [hpol ⟨K_mat, hK_sa⟩, heucl_K]
      change (inner ℂ p (inner ℂ q_hat q • p_hat + inner ℂ p_hat q • q_hat)).re = _
      have hqq : inner ℂ q_hat q = (‖q‖ : ℂ) := by
        dsimp only [q_hat]
        rw [inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K]
        simp only [Complex.ofReal_cpow (norm_nonneg q), ← Complex.ofReal_pow, ← Complex.ofReal_mul]
        congr 1; field_simp [hq_pos.ne']
      have hpq0 : inner ℂ p_hat q = 0 := by
        dsimp only [p_hat]; rw [inner_smul_left, hpq_orth, mul_zero]
      have hpp : inner ℂ p p_hat = (‖p‖ : ℂ) := by
        dsimp only [p_hat]
        rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
        simp only [Complex.ofReal_cpow (norm_nonneg p), ← Complex.ofReal_pow, ← Complex.ofReal_mul]
        congr 1; field_simp [hp_pos.ne']
      rw [hqq, hpq0, zero_smul, add_zero, inner_smul_right, hpp, ← Complex.ofReal_mul,
        Complex.ofReal_re, mul_comm ‖q‖ ‖p‖, hpq_prod]

/-- At the plateau tolerance `r = 1 / 10`, the unitary-ratio saddle mode achieves exact
unit-ball sensitivity `(√399 / 10) * √(1 - ‖⟨ψ, U_⋆ ψ⟩‖²)`. -/
theorem tenth_saddle_unitBall_sensitivity_eq {N : ℕ} (U_star W_star : UGroup N)
    (hr : ‖U_star.val - W_star.val‖ = 1 / 10) :
    ∃ ψ ∈ maxRightSingularSphere (U_star.val - W_star.val),
      (∀ K : selfAdjoint (Register N), ‖K.val‖ ≤ 1 →
        |(inner ℂ (euclCLM (U_star.val - W_star.val) ψ)
          (euclCLM (skewAdjointCommutator K U_star.val) ψ)).re / (1 / 10)| ≤
          (Real.sqrt 399 / 10) * Real.sqrt (1 - ‖inner ℂ ψ (euclCLM U_star.val ψ)‖ ^ 2)) ∧
      ∃ K_star : selfAdjoint (Register N), ‖K_star.val‖ ≤ 1 ∧
        |(inner ℂ (euclCLM (U_star.val - W_star.val) ψ)
          (euclCLM (skewAdjointCommutator K_star U_star.val) ψ)).re / (1 / 10)| =
          (Real.sqrt 399 / 10) * Real.sqrt (1 - ‖inner ℂ ψ (euclCLM U_star.val ψ)‖ ^ 2) := by
  have hr_pos : 0 < ‖U_star.val - W_star.val‖ := by rw [hr]; norm_num
  obtain ⟨ψ, hψ_mem, β, hβ_sq, _, _, hdir⟩ := exists_unitaryRatio_singularEigenmode U_star W_star hr_pos
  have hUψ_norm : ‖euclCLM U_star.val ψ‖ = 1 := by
    have hadj : inner ℂ (euclCLM U_star.val ψ) (euclCLM U_star.val ψ) = 1 := by
      have hst : euclCLM (star U_star.val) = ContinuousLinearMap.adjoint (euclCLM U_star.val) :=
        map_star Matrix.toEuclideanCLM U_star.val
      rw [← ContinuousLinearMap.adjoint_inner_left, ← hst, ← ContinuousLinearMap.mul_apply,
        ← map_mul, (Unitary.mem_iff.mp U_star.2).1, map_one, ContinuousLinearMap.one_apply,
        inner_self_eq_norm_sq_to_K, hψ_mem.1]
      norm_num
    rw [inner_self_eq_norm_sq_to_K] at hadj
    have hsq : ‖euclCLM U_star.val ψ‖ ^ 2 = 1 := by simpa using congrArg Complex.re hadj
    nlinarith only [hsq, norm_nonneg (euclCLM U_star.val ψ)]
  obtain ⟨hsup_le, K_star, hK_norm, hK_eq⟩ := sup_selfAdjoint_expectation_diff_eq hUψ_norm hψ_mem.1
  have hβ_abs : |β / (1 / 10)| * 2 = Real.sqrt 399 / 10 := by
    rw [hr] at hβ_sq
    have hsq : (|β / (1 / 10)| * 2) ^ 2 = (Real.sqrt 399 / 10) ^ 2 := by
      rw [mul_pow, sq_abs, div_pow, hβ_sq, div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    exact (sq_eq_sq₀ (by positivity) (by positivity)).mp hsq
  refine ⟨ψ, hψ_mem, fun K hK => ?_, K_star, hK_norm, ?_⟩
  · have hd := hdir K
    rw [hr] at hd
    rw [hd, abs_mul]
    have hb := (hsup_le K).trans (mul_le_mul_of_nonneg_left hK (by positivity))
    rw [mul_one] at hb
    calc |β / (1 / 10)| * |_ - _|
        ≤ |β / (1 / 10)| * (2 * Real.sqrt (1 - ‖inner ℂ ψ (euclCLM U_star.val ψ)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = (|β / (1 / 10)| * 2) * Real.sqrt (1 - ‖inner ℂ ψ (euclCLM U_star.val ψ)‖ ^ 2) := by ring
      _ = (Real.sqrt 399 / 10) * Real.sqrt (1 - ‖inner ℂ ψ (euclCLM U_star.val ψ)‖ ^ 2) := by
          rw [hβ_abs]
  · have hd := hdir K_star
    rw [hr] at hd
    rw [hd, abs_mul, hK_eq, abs_of_nonneg (by positivity), ← mul_assoc, hβ_abs]

/-- Antipodal diameter stationarity (`r = 2`) and common-eigenmode stationarity: first-order
transverse directional variations vanish for all self-adjoint generators `K`. -/
theorem common_eigenmode_sensitivity_zero {N : ℕ} {U W : Register N}
    (hU : U ∈ unitary (Register N)) {ψ : StateSpace N} {μ : ℂ}
    (hUψ : euclCLM U ψ = μ • ψ) {ν : ℂ} (hWψ : euclCLM W ψ = ν • ψ)
    (K : selfAdjoint (Register N)) :
    (inner ℂ (euclCLM (U - W) ψ) (euclCLM (skewAdjointCommutator K U) ψ)).re = 0 := by
  rw [re_inner_unitary_sub_skewAdjointCommutator hU W K ψ, hWψ,
    map_sub, ContinuousLinearMap.sub_apply, map_mul, ContinuousLinearMap.mul_apply,
    map_mul, ContinuousLinearMap.mul_apply, hUψ, map_smul, sub_self, inner_zero_right,
    Complex.zero_im, neg_zero]

/-- Under simple spectrum of `H`, all `4^N` Pauli commutators `i [σ_p, H]` have zero expectation
shift between `ψ` and `U_⋆ ψ` (`U_⋆ = projectiveSpectralMatrix e V θ`) if and only if
`‖⟨ψ, U_⋆ ψ⟩‖ = 1` (equivalently `U_⋆ ψ = c • ψ` for some unit phase `c`). -/
theorem pauliCommutator_stationary_iff_eigenmode {N d : ℕ}
    (H : selfAdjoint (Register N)) (hinj : Function.Injective H.2.isHermitian.eigenvalues)
    (e : Config N ≃ Fin (d + 1)) (θ : Fin d → UnitAddCircle)
    {ψ : StateSpace N} (hψ : ‖ψ‖ = 1) :
    let V : UGroup N := hermitianEigenbasisUnitary H.2.isHermitian
    let U_star := projectiveSpectralMatrix e V θ
    (∀ p : Fin N → Option (Fin 3),
      (inner ℂ (euclCLM U_star ψ)
        (euclCLM (pauliTransverseGenerator H (finitePauliSelfAdjoint p)).val (euclCLM U_star ψ))).re =
      (inner ℂ ψ (euclCLM (pauliTransverseGenerator H (finitePauliSelfAdjoint p)).val ψ)).re) ↔
      ‖inner ℂ ψ (euclCLM U_star ψ)‖ = 1 := by
  intro V U_star
  have hadj (M : Register N) (x y : StateSpace N) :
      inner ℂ (euclCLM (star M) x) y = inner ℂ x (euclCLM M y) := by
    have hstar : euclCLM (star M) = ContinuousLinearMap.adjoint (euclCLM M) :=
      map_star Matrix.toEuclideanCLM M
    rw [hstar, ContinuousLinearMap.adjoint_inner_left]
  have hU_unit : U_star ∈ unitary (Register N) := by
    dsimp only [U_star]
    unfold projectiveSpectralMatrix
    refine mul_mem (mul_mem V.2 ?_) (Unitary.star_mem V.2)
    rw [Unitary.mem_iff, star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    constructor <;> ext a b <;> by_cases hab : a = b
    · subst hab; simp only [diagonal_apply_eq, one_apply_eq]
      exact Complex.normSq_eq_conj_mul_self.symm.trans (by simp)
    · simp [hab]
    · subst hab; simp only [diagonal_apply_eq, one_apply_eq]; rw [mul_comm]
      exact Complex.normSq_eq_conj_mul_self.symm.trans (by simp)
    · simp [hab]
  have hUψ_norm : ‖euclCLM U_star ψ‖ = 1 := by
    have h1 : inner ℂ (euclCLM U_star ψ) (euclCLM U_star ψ) = 1 := by
      rw [← hadj U_star, ← ContinuousLinearMap.mul_apply, ← map_mul,
        (Unitary.mem_iff.mp hU_unit).1, map_one, ContinuousLinearMap.one_apply,
        inner_self_eq_norm_sq_to_K, hψ]
      norm_num
    rw [inner_self_eq_norm_sq_to_K] at h1
    have hsq : ‖euclCLM U_star ψ‖ ^ 2 = 1 := by simpa using congrArg Complex.re h1
    nlinarith only [hsq, norm_nonneg (euclCLM U_star ψ)]
  constructor
  · intro hpauli
    -- Step 1: extend from Pauli basis to all P ∈ selfAdjoint (Register N)
    let Λ : selfAdjoint (Register N) →ₗ[ℝ] ℝ :=
      { toFun := fun P =>
          (inner ℂ (euclCLM U_star ψ)
            (euclCLM (pauliTransverseGenerator H P).val (euclCLM U_star ψ))).re -
          (inner ℂ ψ (euclCLM (pauliTransverseGenerator H P).val ψ)).re
        map_add' := fun P Q => by
          have hadd : (pauliTransverseGenerator H (P + Q)).val =
              (pauliTransverseGenerator H P).val + (pauliTransverseGenerator H Q).val := by
            dsimp only [pauliTransverseGenerator]
            simp only [AddSubgroup.coe_add, add_mul, mul_add, smul_sub, smul_add]
            abel
          rw [hadd, map_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
            inner_add_right, inner_add_right, Complex.add_re, Complex.add_re]
          ring
        map_smul' := fun c P => by
          have hsmul : (pauliTransverseGenerator H (c • P)).val =
              (c : ℂ) • (pauliTransverseGenerator H P).val := by
            dsimp only [pauliTransverseGenerator]
            have hc : (c • P).val = (c : ℂ) • P.val := Complex.real_smul.symm
            rw [hc, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, smul_comm]
          rw [hsmul, map_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
            inner_smul_right, inner_smul_right, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
            RingHom.id_apply, smul_eq_mul]
          ring }
    have hΛ_all (P : selfAdjoint (Register N)) : Λ P = 0 := by
      have hker : Submodule.span ℝ (Set.range (finitePauliSelfAdjoint :
          (Fin N → Option (Fin 3)) → selfAdjoint (Register N))) ≤ LinearMap.ker Λ := by
        rw [Submodule.span_le]
        rintro _ ⟨p, rfl⟩
        exact sub_eq_zero.mpr (hpauli p)
      have htop : Submodule.span ℝ (Set.range (finitePauliSelfAdjoint :
          (Fin N → Option (Fin 3)) → selfAdjoint (Register N))) = ⊤ := by
        have hb := (finitePauliSelfAdjointBasis (Fin N)).span_eq
        simpa [funext finitePauliSelfAdjointBasis_apply] using hb
      rw [htop] at hker
      exact hker Submodule.mem_top
    -- Step 2: every K ∈ selfAdjoint (Register N) decomposes in the V-basis as K_diag + i [P, H]
    -- where K_diag commutes with U_star!
    have hK_all (K : selfAdjoint (Register N)) :
        (inner ℂ (euclCLM U_star ψ) (euclCLM K.val (euclCLM U_star ψ))).re -
          (inner ℂ ψ (euclCLM K.val ψ)).re = 0 := by
      let E_eig := H.2.isHermitian.eigenvalues
      have hspec : H.val = V.val * diagonal (Complex.ofReal ∘ E_eig) * star V.val :=
        H.2.isHermitian.spectral_theorem
      have hVV1 : star V.val * V.val = 1 := (Unitary.mem_iff.mp V.2).1
      have hVV2 : V.val * star V.val = 1 := (Unitary.mem_iff.mp V.2).2
      let M_eig : Register N := star V.val * K.val * V.val
      have hM_sa : IsSelfAdjoint M_eig := by
        rw [IsSelfAdjoint, star_mul, star_mul, star_star, K.2.star_eq, mul_assoc]
      let K_diag : Register N := V.val * diagonal (fun a => M_eig a a) * star V.val
      let P_tilde : Register N := fun a b =>
        if a = b then 0 else (-Complex.I * M_eig a b) / ((E_eig b : ℂ) - (E_eig a : ℂ))
      have hP_tilde_sa : IsSelfAdjoint P_tilde := by
        rw [IsSelfAdjoint]
        ext a b
        by_cases hab : a = b
        · subst hab; simp [P_tilde]
        · have hba : b ≠ a := Ne.symm hab
          have hM_conj : star (M_eig b a) = M_eig a b := by
            have h := congrFun (congrFun hM_sa a) b
            simpa [Matrix.star_apply] using h
          simp only [P_tilde, Matrix.star_apply, if_neg hab, if_neg hba]
          rw [star_div₀, star_mul, star_neg, Complex.star_def, Complex.conj_I, neg_neg,
            hM_conj, star_sub, Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal]
          have hden_ne : (E_eig b : ℂ) - (E_eig a : ℂ) ≠ 0 :=
            sub_ne_zero.mpr (Complex.ofReal_ne_ofReal.mpr (hinj.ne hba))
          have hden_neg : (E_eig a : ℂ) - (E_eig b : ℂ) = -((E_eig b : ℂ) - (E_eig a : ℂ)) := by ring
          rw [hden_neg, div_neg, ← neg_div, neg_mul]
      let P : selfAdjoint (Register N) :=
        ⟨V.val * P_tilde * star V.val, by
          rw [selfAdjoint.mem_iff, star_mul, star_mul, star_star, hP_tilde_sa.star_eq, mul_assoc]⟩
      have hcomm_PH : (pauliTransverseGenerator H P).val = K.val - K_diag := by
        dsimp only [pauliTransverseGenerator, P, K_diag]
        have hVH : star V.val * H.val * V.val = diagonal (Complex.ofReal ∘ E_eig) := by
          calc star V.val * (V.val * diagonal (Complex.ofReal ∘ E_eig) * star V.val) * V.val
              = (star V.val * V.val) * diagonal (Complex.ofReal ∘ E_eig) * (star V.val * V.val) := by
                simp only [mul_assoc]
            _ = diagonal (Complex.ofReal ∘ E_eig) := by rw [hVV1, one_mul, mul_one]
        -- Check equality after conjugating by V* ... V
        have hmid : Complex.I • (P_tilde * diagonal (Complex.ofReal ∘ E_eig) -
            diagonal (Complex.ofReal ∘ E_eig) * P_tilde) =
            M_eig - diagonal (fun a => M_eig a a) := by
          ext a b
          simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_diagonal,
            Matrix.diagonal_mul, Function.comp_apply, smul_eq_mul]
          by_cases hab : a = b
          · subst hab; simp [P_tilde]
          · simp only [P_tilde, if_neg hab, diagonal_apply_ne _ hab, sub_zero]
            have hden : (E_eig b : ℂ) - (E_eig a : ℂ) ≠ 0 :=
              sub_ne_zero.mpr (Complex.ofReal_ne_ofReal.mpr (hinj.ne (Ne.symm hab)))
            calc Complex.I * (-Complex.I * M_eig a b / (↑(E_eig b) - ↑(E_eig a)) * ↑(E_eig b) -
                    ↑(E_eig a) * (-Complex.I * M_eig a b / (↑(E_eig b) - ↑(E_eig a))))
                = (Complex.I * -Complex.I) * M_eig a b *
                    ((↑(E_eig b) - ↑(E_eig a)) / (↑(E_eig b) - ↑(E_eig a))) := by ring
              _ = M_eig a b := by rw [div_self hden]; simp [Complex.I_mul_I]
        calc Complex.I • ((V.val * P_tilde * star V.val) * H.val -
                H.val * (V.val * P_tilde * star V.val))
            = Complex.I • (V.val * (P_tilde * (star V.val * H.val * V.val) -
                (star V.val * H.val * V.val) * P_tilde) * star V.val) := by
                congr 1
                calc V.val * P_tilde * star V.val * H.val - H.val * (V.val * P_tilde * star V.val)
                    = V.val * P_tilde * star V.val * H.val * (V.val * star V.val) -
                        (V.val * star V.val) * H.val * (V.val * P_tilde * star V.val) := by
                        rw [hVV2, mul_one, one_mul]
                  _ = V.val * (P_tilde * (star V.val * H.val * V.val) -
                        (star V.val * H.val * V.val) * P_tilde) * star V.val := by
                        noncomm_ring
          _ = V.val * (Complex.I • (P_tilde * diagonal (Complex.ofReal ∘ E_eig) -
                diagonal (Complex.ofReal ∘ E_eig) * P_tilde)) * star V.val := by
                rw [hVH, Matrix.mul_smul, Matrix.smul_mul]
          _ = V.val * (M_eig - diagonal (fun a => M_eig a a)) * star V.val := by rw [hmid]
          _ = K.val - V.val * diagonal (fun a => M_eig a a) * star V.val := by
                dsimp only [M_eig]
                rw [Matrix.mul_sub, Matrix.sub_mul]
                congr 1
                calc V.val * (star V.val * K.val * V.val) * star V.val
                    = (V.val * star V.val) * K.val * (V.val * star V.val) := by simp only [mul_assoc]
                  _ = K.val := by rw [hVV2, one_mul, mul_one]
      -- Show star U_star * K_diag * U_star = K_diag because both are diagonal in V-basis
      have hU_Kdiag : star U_star * K_diag * U_star = K_diag := by
        dsimp only [U_star, K_diag]
        unfold projectiveSpectralMatrix
        have hVinv : (V⁻¹ : UGroup N).val = star V.val := rfl
        rw [hVinv]
        set d_phase := fun i => (fourier 1 (RHTower.zeroAnchoredPhase d θ (e i)) : ℂ)
        have hstar_U : star (V.val * diagonal d_phase * star V.val) =
            V.val * star (diagonal d_phase) * star V.val := by
          rw [star_mul, star_mul, star_star, mul_assoc]
        have hdiag_comm : star (diagonal d_phase) * diagonal (fun a => M_eig a a) * diagonal d_phase =
            diagonal (fun a => M_eig a a) := by
          rw [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
          ext a b
          by_cases hab : a = b
          · subst hab; simp only [diagonal_apply_eq]
            rw [mul_right_comm, mul_comm (star (d_phase a)), ← Complex.normSq_eq_conj_mul_self]
            have h1 : ‖d_phase a‖ = 1 := by simp [d_phase, fourier_apply]
            rw [Complex.normSq_eq_norm_sq, h1, one_pow, Complex.ofReal_one, mul_one]
          · simp [hab]
        rw [hstar_U]
        calc V.val * star (diagonal d_phase) * star V.val *
              (V.val * diagonal (fun a => M_eig a a) * star V.val) *
              (V.val * diagonal d_phase * star V.val)
            = V.val * ((star (diagonal d_phase) * (star V.val * V.val) *
                diagonal (fun a => M_eig a a) * (star V.val * V.val) * diagonal d_phase)) * star V.val := by
                simp only [mul_assoc]
          _ = V.val * diagonal (fun a => M_eig a a) * star V.val := by
                rw [hVV1, mul_one, mul_one, hdiag_comm]
      have hK_split : K.val = K_diag + (pauliTransverseGenerator H P).val := by
        rw [hcomm_PH]; abel
      have hdiag_zero : (inner ℂ (euclCLM U_star ψ) (euclCLM K_diag (euclCLM U_star ψ))).re -
          (inner ℂ ψ (euclCLM K_diag ψ)).re = 0 := by
        have h1 : inner ℂ (euclCLM U_star ψ) (euclCLM K_diag (euclCLM U_star ψ)) =
            inner ℂ ψ (euclCLM K_diag ψ) := by
          rw [← hadj U_star, ← ContinuousLinearMap.mul_apply, ← map_mul,
            ← ContinuousLinearMap.mul_apply, ← map_mul, hU_Kdiag]
        rw [h1, sub_self]
      have hP0 : Λ P = 0 := hΛ_all P
      dsimp only [Λ] at hP0
      rw [hK_split, map_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        inner_add_right, inner_add_right, Complex.add_re, Complex.add_re]
      linarith only [hdiag_zero, hP0]
    -- Step 3: conclude ‖⟨ψ, U_star ψ⟩‖ = 1 via sup_selfAdjoint_expectation_diff_eq
    obtain ⟨_, K_star, _, hK_star_eq⟩ := sup_selfAdjoint_expectation_diff_eq hUψ_norm hψ
    have h0 := hK_all K_star
    rw [h0] at hK_star_eq
    have hsqrt0 : Real.sqrt (1 - ‖inner ℂ ψ (euclCLM U_star ψ)‖ ^ 2) = 0 := by
      linarith only [hK_star_eq]
    have hc_le : ‖inner ℂ ψ (euclCLM U_star ψ)‖ ≤ 1 := by
      simpa only [hψ, hUψ_norm, mul_one] using norm_inner_le_norm ψ (euclCLM U_star ψ)
    have h1_nn : 0 ≤ 1 - ‖inner ℂ ψ (euclCLM U_star ψ)‖ ^ 2 := by
      nlinarith only [hc_le, norm_nonneg (inner ℂ ψ (euclCLM U_star ψ))]
    have hsub0 : 1 - ‖inner ℂ ψ (euclCLM U_star ψ)‖ ^ 2 = 0 :=
      (Real.sqrt_eq_zero h1_nn).mp hsqrt0
    have hsq1 : ‖inner ℂ ψ (euclCLM U_star ψ)‖ ^ 2 = 1 ^ 2 := by linarith only [hsub0]
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hsq1
  · intro h1 p
    obtain ⟨hsup_le, _⟩ := sup_selfAdjoint_expectation_diff_eq hUψ_norm hψ
    have hb := hsup_le (pauliTransverseGenerator H (finitePauliSelfAdjoint p))
    rw [h1, one_pow, sub_self, Real.sqrt_zero, mul_zero, zero_mul, abs_le_zero_iff, sub_eq_zero] at hb
    exact hb

/-- The real subspace of transverse Pauli commutators `i [P_l, H]` generated by all open-chain
two-local Pauli terms on `N = n + 2` qubits has dimension at most `12 * (n + 2) - 9`. -/
theorem finrank_chainPauliTransverseSpan_le (n : ℕ) (H : selfAdjoint (Register (n + 2))) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range fun l : PathLabel n =>
      pauliTransverseGenerator H (finitePauliSelfAdjoint (pathWord l)))) ≤
      12 * (n + 2) - 9 := by
  classical
  let φ : (PathLabel n → ℝ) →ₗ[ℝ] selfAdjoint (Register (n + 2)) :=
    { toFun := fun c => ∑ l : PathLabel n,
        c l • pauliTransverseGenerator H (finitePauliSelfAdjoint (pathWord l))
      map_add' := fun a b => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by simp only [Pi.smul_apply, smul_eq_mul, mul_smul,
        RingHom.id_apply, Finset.smul_sum] }
  have hle_range : Submodule.span ℝ (Set.range fun l : PathLabel n =>
      pauliTransverseGenerator H (finitePauliSelfAdjoint (pathWord l))) ≤ LinearMap.range φ := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    refine ⟨Pi.single l 1, ?_⟩
    simp [φ, Pi.single_apply]
  have hcard : Fintype.card (PathLabel n) = 12 * (n + 2) - 9 := by
    simp only [PathLabel, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    omega
  calc Module.finrank ℝ (Submodule.span ℝ _)
      ≤ Module.finrank ℝ (LinearMap.range φ) := Submodule.finrank_mono hle_range
    _ ≤ Module.finrank ℝ (PathLabel n → ℝ) := LinearMap.finrank_range_le φ
    _ = 12 * (n + 2) - 9 := by rw [Module.finrank_pi, hcard]

/-! ## Section 4: Collar-transverse counterexample vs. degree-free Dini anti-concentration -/

private theorem abs_sin_sub_sin_le_abs (a b : ℝ) : |Real.sin a - Real.sin b| ≤ |a - b| := by
  have hle (x y : ℝ) (hxy : x ≤ y) : |Real.sin y - Real.sin x| ≤ y - x := by
    have hhi : Real.sin y - Real.sin x ≤ 1 * (y - x) :=
      convex_univ.image_sub_le_mul_sub_of_deriv_le Real.continuous_sin.continuousOn
        Real.differentiable_sin.differentiableOn
        (fun t _ => by rw [Real.deriv_sin]; exact Real.cos_le_one t) x trivial y trivial hxy
    have hlo : (-1 : ℝ) * (y - x) ≤ Real.sin y - Real.sin x :=
      convex_univ.mul_sub_le_image_sub_of_le_deriv Real.continuous_sin.continuousOn
        Real.differentiable_sin.differentiableOn
        (fun t _ => by rw [Real.deriv_sin]; exact Real.neg_one_le_cos t) x trivial y trivial hxy
    exact abs_le.mpr ⟨by linarith only [hlo], by linarith only [hhi]⟩
  rcases le_total a b with hab | hba
  · rw [abs_sub_comm, abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr hab)]
    exact hle a b hab
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    exact hle b a hba

/-- Pure Lipschitz Clarke/Gateaux non-stationarity on a collar of `[e₀, e₀ + δ]` fails to give
`O(δ)` Gaussian anti-concentration: `oscillatorySliceCounterexample` is `1`-Lipschitz and smooth
everywhere with directional derivative `≥ √3 / 2` across `[e₀ - δ/2, e₀ + 3δ/2]`, yet carries
product-Gaussian mass `≥ exp(-1/2) / (10 π √(2 π))` in `(e₀, e₀ + δ]` for all
`δ ∈ (0, 1 / (8 π)]`. -/
theorem oscillatorySliceCounterexample_violation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (e₀ : ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ_hi : δ ≤ 1 / (8 * Real.pi)) :
    LipschitzWith 1 (oscillatorySliceCounterexample i₀ e₀ δ) ∧
    (∀ x : ι → ℝ, HasDerivAt
      (fun t => oscillatorySliceCounterexample i₀ e₀ δ (Function.update x i₀ t))
      (Real.cos (x i₀ / (2 * δ))) (x i₀)) ∧
    (∀ x : ι → ℝ,
      oscillatorySliceCounterexample i₀ e₀ δ x ∈ Icc (e₀ - δ / 2) (e₀ + 3 * δ / 2) →
      Real.sqrt 3 / 2 ≤ |Real.cos (x i₀ / (2 * δ))|) ∧
    Real.exp (-1 / 2) / (10 * Real.pi * Real.sqrt (2 * Real.pi)) ≤
      (Measure.pi fun _ : ι => gaussianReal 0 1).real
        {x : ι → ℝ | oscillatorySliceCounterexample i₀ e₀ δ x ∈ Ioc e₀ (e₀ + δ)} := by
  have h2δ_pos : 0 < 2 * δ := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1-Lipschitz globally on ι → ℝ
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [NNReal.coe_one, one_mul, Real.dist_eq]
    unfold oscillatorySliceCounterexample
    have hdiff : e₀ + δ / 2 + 2 * δ * Real.sin (x i₀ / (2 * δ)) -
        (e₀ + δ / 2 + 2 * δ * Real.sin (y i₀ / (2 * δ))) =
        2 * δ * (Real.sin (x i₀ / (2 * δ)) - Real.sin (y i₀ / (2 * δ))) := by ring
    rw [hdiff, abs_mul, abs_of_pos h2δ_pos]
    have hsin := abs_sin_sub_sin_le_abs (x i₀ / (2 * δ)) (y i₀ / (2 * δ))
    rw [← sub_div, abs_div, abs_of_pos h2δ_pos] at hsin
    have hcoord : |x i₀ - y i₀| ≤ dist x y := by
      simpa only [dist_eq_norm, Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) i₀
    calc 2 * δ * |Real.sin (x i₀ / (2 * δ)) - Real.sin (y i₀ / (2 * δ))|
        ≤ 2 * δ * (|x i₀ - y i₀| / (2 * δ)) := mul_le_mul_of_nonneg_left hsin h2δ_pos.le
      _ = |x i₀ - y i₀| := mul_div_cancel₀ _ h2δ_pos.ne'
      _ ≤ dist x y := hcoord
  · -- Exact directional derivative cos(x_{i₀} / (2 δ))
    intro x
    have hlin : HasDerivAt (fun t : ℝ => t / (2 * δ)) (1 / (2 * δ)) (x i₀) := by
      simpa using (hasDerivAt_id (x i₀)).div_const (2 * δ)
    have hsin : HasDerivAt (fun t : ℝ => Real.sin (t / (2 * δ)))
        (Real.cos (x i₀ / (2 * δ)) * (1 / (2 * δ))) (x i₀) :=
      (Real.hasDerivAt_sin (x i₀ / (2 * δ))).comp (x i₀) hlin
    have hmul := (hsin.const_mul (2 * δ)).const_add (e₀ + δ / 2)
    have hderiv_eq : 2 * δ * (Real.cos (x i₀ / (2 * δ)) * (1 / (2 * δ))) =
        Real.cos (x i₀ / (2 * δ)) := by field_simp [h2δ_pos.ne']
    rw [hderiv_eq] at hmul
    refine hmul.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp [oscillatorySliceCounterexample]
  · -- Gradient ≥ √3 / 2 across the [e₀ - δ/2, e₀ + 3δ/2] collar
    intro x ⟨hlo, hhi⟩
    unfold oscillatorySliceCounterexample at hlo hhi
    have hsin_le : |Real.sin (x i₀ / (2 * δ))| ≤ 1 / 2 := by
      rw [abs_le]
      constructor
      · have h1 : -δ ≤ 2 * δ * Real.sin (x i₀ / (2 * δ)) := by linarith only [hlo]
        exact (le_div_iff₀ h2δ_pos).mp (by field_simp [hδ0.ne']; linarith only [h1])
      · have h1 : 2 * δ * Real.sin (x i₀ / (2 * δ)) ≤ δ := by linarith only [hhi]
        exact (div_le_iff₀ h2δ_pos).mp (by field_simp [hδ0.ne']; linarith only [h1])
    have hsin_sq : Real.sin (x i₀ / (2 * δ)) ^ 2 ≤ 1 / 4 := by
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hsin_le 2
      rw [sq_abs] at hsq
      linarith only [hsq]
    have hcos_sq : 3 / 4 ≤ |Real.cos (x i₀ / (2 * δ))| ^ 2 := by
      rw [sq_abs]
      linarith only [Real.sin_sq_add_cos_sq (x i₀ / (2 * δ)), hsin_sq]
    have h34 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    rw [← h34] at hcos_sq
    exact (sq_le_sq₀ (by positivity) (abs_nonneg _)).mp hcos_sq
  · -- Product-Gaussian measure lower bound ≥ exp(-1/2) / (10 π √(2 π))
    let S₁ : Set ℝ := {t : ℝ | e₀ + δ / 2 + 2 * δ * Real.sin (t / (2 * δ)) ∈ Ioc e₀ (e₀ + δ)}
    have hpi_eq : {x : ι → ℝ | oscillatorySliceCounterexample i₀ e₀ δ x ∈ Ioc e₀ (e₀ + δ)} =
        Set.univ.pi (fun i => if i = i₀ then S₁ else Set.univ) := by
      ext x
      simp only [mem_setOf_eq, mem_univ_pi]
      constructor
      · intro hx i
        split_ifs with hi
        · subst hi; exact hx
        · trivial
      · intro hx
        simpa using hx i₀
    have hprob_eq : (Measure.pi fun _ : ι => gaussianReal 0 1).real
        {x : ι → ℝ | oscillatorySliceCounterexample i₀ e₀ δ x ∈ Ioc e₀ (e₀ + δ)} =
        (gaussianReal 0 1).real S₁ := by
      rw [hpi_eq, Measure.real, Measure.pi_pi]
      have hprod : (∏ i : ι, (gaussianReal 0 1) (if i = i₀ then S₁ else Set.univ)) =
          (gaussianReal 0 1) S₁ := by
        rw [Finset.prod_eq_single i₀]
        · simp
        · intro i _ hi; simp [hi]
        · intro h; exact (h (Finset.mem_univ i₀)).elim
      rw [hprod, ← Measure.real]
    rw [hprob_eq]
    -- Pack K = ⌊1 / (4 π δ)⌋ disjoint periods inside [-1, 1]
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have h4piδ_pos : 0 < 4 * Real.pi * δ := by positivity
    have h4piδ_le : 4 * Real.pi * δ ≤ 1 / 2 := by
      have h1 : 8 * Real.pi * δ ≤ 1 := (le_div_iff₀ (by positivity)).mp hδ_hi
      linarith only [h1]
    have hquot_ge2 : 2 ≤ 1 / (4 * Real.pi * δ) := by
      rw [le_div_iff₀ h4piδ_pos]; linarith only [h4piδ_le]
    let K : ℕ := ⌊1 / (4 * Real.pi * δ)⌋₊
    have hK_ge2 : 2 ≤ K := Nat.le_floor hquot_ge2
    have hK_le : (K : ℝ) * (4 * Real.pi * δ) ≤ 1 :=
      (le_div_iff₀ h4piδ_pos).mp (Nat.floor_le (by positivity))
    have hK_ge_half : 1 / 2 ≤ (K : ℝ) * (4 * Real.pi * δ) := by
      have hlt : 1 / (4 * Real.pi * δ) < (K : ℝ) + 1 := Nat.lt_floor_add_one _
      have h1 : 1 < ((K : ℝ) + 1) * (4 * Real.pi * δ) := (div_lt_iff₀ h4piδ_pos).mp hlt
      have hK1 : (K : ℝ) + 1 ≤ 2 * (K : ℝ) := by
        have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 1 ≤ K)
        linarith only [this]
      have h2 := mul_le_mul_of_nonneg_right hK1 h4piδ_pos.le
      linarith only [h1, h2]
    let J (k : ℕ) : Set ℝ :=
      Icc (4 * Real.pi * (k : ℝ) * δ - 2 / 5 * δ) (4 * Real.pi * (k : ℝ) * δ + 2 / 5 * δ)
    let U : Set ℝ := ⋃ k ∈ Finset.range K, J k
    have hU_meas : MeasurableSet U :=
      Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Icc
    have hU_sub_Icc : U ⊆ Icc (-1 : ℝ) 1 := by
      rintro t ht
      obtain ⟨k, hk_mem, ht_lo, ht_hi⟩ := mem_iUnion₂.mp ht
      have hk_lt : k < K := Finset.mem_range.mp hk_mem
      have hk1_le : ((k : ℝ) + 1) ≤ (K : ℝ) := by exact_mod_cast hk_lt
      have hpi3 : 3 < Real.pi := Real.pi_gt_three
      constructor
      · have hk_nn : 0 ≤ 4 * Real.pi * (k : ℝ) * δ := by positivity
        nlinarith only [ht_lo, hk_nn, h4piδ_le, hpi3, hδ0]
      · have hhi_step : 4 * Real.pi * (k : ℝ) * δ + 2 / 5 * δ ≤ (K : ℝ) * (4 * Real.pi * δ) := by
          nlinarith only [hk1_le, hpi3, hδ0]
        linarith only [ht_hi, hhi_step, hK_le]
    have hU_sub_S₁ : U ⊆ S₁ := by
      rintro t ht
      obtain ⟨k, _, ht_lo, ht_hi⟩ := mem_iUnion₂.mp ht
      let u := t / (2 * δ) - (k : ℝ) * (2 * Real.pi)
      have hsin_eq : Real.sin (t / (2 * δ)) = Real.sin u := by
        have h1 : t / (2 * δ) = u + (k : ℕ) * (2 * Real.pi) := by dsimp only [u]; ring
        rw [h1]
        exact (Real.sin_periodic.nat_mul k) u
      have hu_abs : |u| ≤ 1 / 5 := by
        have hdiff : u = (t - 4 * Real.pi * (k : ℝ) * δ) / (2 * δ) := by
          dsimp only [u]; field_simp [h2δ_pos.ne']; ring
        rw [hdiff, abs_div, abs_of_pos h2δ_pos, div_le_iff₀ h2δ_pos]
        rw [abs_le]
        exact ⟨by linarith only [ht_lo], by linarith only [ht_hi]⟩
      have hsin_abs : |Real.sin (t / (2 * δ))| ≤ 1 / 5 := by
        rw [hsin_eq]
        have h1 := abs_sin_sub_sin_le_abs u 0
        rw [Real.sin_zero, sub_zero, sub_zero] at h1
        exact h1.trans hu_abs
      obtain ⟨hs_lo, hs_hi⟩ := abs_le.mp hsin_abs
      dsimp only [S₁]
      rw [mem_setOf_eq, mem_Ioc]
      constructor <;> nlinarith only [hs_lo, hs_hi, hδ0]
    have hdisj : Pairwise fun k₁ k₂ : ℕ => Disjoint (J k₁) (J k₂) := by
      intro k₁ k₂ hne
      have hpi3 : 3 < Real.pi := Real.pi_gt_three
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine disjoint_left.mpr fun t ht₁ ht₂ => ?_
        have hk_step : ((k₁ : ℝ) + 1) ≤ (k₂ : ℝ) := by exact_mod_cast hlt
        nlinarith only [ht₁.2, ht₂.1, hk_step, hpi3, hδ0]
      · refine disjoint_left.mpr fun t ht₁ ht₂ => ?_
        have hk_step : ((k₂ : ℝ) + 1) ≤ (k₁ : ℝ) := by exact_mod_cast hgt
        nlinarith only [ht₂.2, ht₁.1, hk_step, hpi3, hδ0]
    have hU_vol : volume U = ENNReal.ofReal ((K : ℝ) * (4 / 5 * δ)) := by
      rw [measure_biUnion_finset (fun k₁ _ k₂ _ hne => hdisj hne) (fun _ _ => measurableSet_Icc)]
      have hlen (k : ℕ) : volume (J k) = ENNReal.ofReal (4 / 5 * δ) := by
        dsimp only [J]
        rw [Real.volume_Icc]
        congr 1; ring
      simp only [hlen, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg K), ENNReal.ofReal_natCast]
    -- Gaussian density on [-1, 1] is ≥ (√(2π))⁻¹ * exp(-1/2)
    let c_pdf : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1 / 2)
    have hc_pdf_pos : 0 < c_pdf := by positivity
    have hgauss_U : ENNReal.ofReal (c_pdf * ((K : ℝ) * (4 / 5 * δ))) ≤ (gaussianReal 0 1) U := by
      rw [gaussianReal_apply 0 (by norm_num) U]
      have hlow : ∀ t ∈ U, ENNReal.ofReal c_pdf ≤ gaussianPDF 0 1 t := by
        intro t ht
        have ht_Icc := hU_sub_Icc ht
        rw [gaussianPDF]
        apply ENNReal.ofReal_le_ofReal
        rw [gaussianPDFReal_def]
        simp only [NNReal.coe_one, mul_one, sub_zero]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        have hsq : t ^ 2 ≤ 1 := by nlinarith only [ht_Icc.1, ht_Icc.2]
        linarith only [hsq]
      have hmono : ∫⁻ _t in U, ENNReal.ofReal c_pdf ≤ ∫⁻ t in U, gaussianPDF 0 1 t := by
        refine setLIntegral_mono_ae (by fun_prop) ?_
        filter_upwards [ae_restrict_mem hU_meas] with t ht using hlow t ht
      rw [setLIntegral_const, hU_vol, ← ENNReal.ofReal_mul hc_pdf_pos.le] at hmono
      exact hmono
    have hU_le_S₁ : (gaussianReal 0 1).real U ≤ (gaussianReal 0 1).real S₁ :=
      measureReal_mono hU_sub_S₁ (measure_ne_top _ _)
    have hU_real : c_pdf * ((K : ℝ) * (4 / 5 * δ)) ≤ (gaussianReal 0 1).real U := by
      rw [Measure.real]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hgauss_U
    have hK_len : 1 / (10 * Real.pi) ≤ (K : ℝ) * (4 / 5 * δ) := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : (K : ℝ) * (4 / 5 * δ) * (10 * Real.pi) = 2 * ((K : ℝ) * (4 * Real.pi * δ)) := by ring
      linarith only [h1, hK_ge_half]
    calc Real.exp (-1 / 2) / (10 * Real.pi * Real.sqrt (2 * Real.pi))
        = c_pdf * (1 / (10 * Real.pi)) := by dsimp only [c_pdf]; ring
      _ ≤ c_pdf * ((K : ℝ) * (4 / 5 * δ)) := mul_le_mul_of_nonneg_left hK_len hc_pdf_pos.le
      _ ≤ (gaussianReal 0 1).real S₁ := hU_real.trans hU_le_S₁

/-- Non-smooth right Dini growth lemma: if `g` is continuous on `[a, b]` and at every `t ∈ [a, b)`
and `ε > 0` admits a right step `h ∈ (0, b - t]` with `(c - ε) * h ≤ g(t + h) - g(t)`, then
`c * (b - a) ≤ g(b) - g(a)` without any differentiability assumption. -/
theorem dini_mul_sub_le_sub {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b))
    (hdini : ∀ t ∈ Ico a b, ∀ ε > 0, ∃ h ∈ Ioc (0 : ℝ) (b - t), (c - ε) * h ≤ g (t + h) - g t) :
    c * (b - a) ≤ g b - g a := by
  suffices h_eps : ∀ ε > 0, (c - ε) * (b - a) ≤ g b - g a by
    by_contra! hlt
    let ε := (c * (b - a) - (g b - g a)) / (2 * (b - a + 1))
    have hden : 0 < 2 * (b - a + 1) := by linarith only [hab]
    have hε : 0 < ε := div_pos (sub_pos.mpr hlt) hden
    have h1 := h_eps ε hε
    have h2 : ε * (b - a) ≤ (c * (b - a) - (g b - g a)) / 2 := by
      dsimp only [ε]
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hden zero_lt_two]
      nlinarith only [hab, hlt]
    linarith only [h1, h2, hlt]
  intro ε hε
  let g_clip : ℝ → ℝ := fun t => g (max a (min t b))
  have hg_clip_cont : Continuous g_clip := by
    refine hg.comp_continuous (continuous_const.max (continuous_id.min continuous_const)) fun t => ?_
    exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hg_clip_eq {t : ℝ} (ht : t ∈ Icc a b) : g_clip t = g t := by
    dsimp only [g_clip]
    rw [min_eq_left ht.2, max_eq_right ht.1]
  let S : Set ℝ := Icc a b ∩ {t : ℝ | (c - ε) * (t - a) ≤ g_clip t - g a}
  have hS_closed : IsClosed S := isClosed_Icc.inter
    (isClosed_le (continuous_const.mul (continuous_id.sub continuous_const))
      (hg_clip_cont.sub continuous_const))
  have ha_mem : a ∈ S := ⟨⟨le_rfl, hab⟩, by rw [hg_clip_eq ⟨le_rfl, hab⟩, sub_self, sub_self, mul_zero]⟩
  have hS_bdd : BddAbove S := ⟨b, fun t ht => ht.1.2⟩
  let s := sSup S
  have hs_mem : s ∈ S := hS_closed.csSup_mem ⟨a, ha_mem⟩ hS_bdd
  have hs_eq_b : s = b := by
    by_contra hne
    have hs_lt : s < b := lt_of_le_of_ne hs_mem.1.2 hne
    obtain ⟨h, ⟨hh_pos, hh_le⟩, hh_step⟩ := hdini s ⟨hs_mem.1.1, hs_lt⟩ ε hε
    have hsh_Icc : s + h ∈ Icc a b := ⟨by linarith only [hs_mem.1.1, hh_pos], by linarith only [hh_le]⟩
    have hsh_mem : s + h ∈ S := by
      refine ⟨hsh_Icc, ?_⟩
      rw [hg_clip_eq hsh_Icc]
      have hs_ineq := hs_mem.2
      rw [hg_clip_eq hs_mem.1] at hs_ineq
      nlinarith only [hs_ineq, hh_step]
    have hle_sup : s + h ≤ s := le_csSup hS_bdd hsh_mem
    linarith only [hh_pos, hle_sup]
  have hb_mem : b ∈ S := hs_eq_b ▸ hs_mem
  have hb_ineq := hb_mem.2
  rwa [hg_clip_eq ⟨hab, le_rfl⟩] at hb_ineq

private theorem gaussianReal_le_density_mul_volume (S : Set ℝ) (hS : MeasurableSet S) :
    (gaussianReal 0 1) S ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) * volume S := by
  rw [gaussianReal_apply 0 (by norm_num) S, ← setLIntegral_const]
  refine setLIntegral_mono_ae (by fun_prop) ?_
  filter_upwards [ae_restrict_mem hS] with t _
  rw [gaussianPDF]
  apply ENNReal.ofReal_le_ofReal
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg t]))

/-- Degree-free product-Gaussian anti-concentration under `M`-piece non-smooth right Dini
monotonicity along coordinate `i₀`: for every `e₀ ∈ ℝ` and `δ ≥ 0`, the slice probability on
`Ω` is at most `M * δ / (√(2 π) * c)` with zero polynomial degree dependence. -/
theorem gaussian_degreeFree_dini_anticoncentration {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) {F : (ι → ℝ) → ℝ} (hF : Measurable F)
    {Ω : Set (ι → ℝ)} (hΩ : MeasurableSet Ω)
    (M : ℕ) {c : ℝ} (hc : 0 < c)
    (hfib : ∀ y : ι → ℝ, ∃ (I_piece : Fin M → Set ℝ) (sgn : Fin M → Bool),
      {t : ℝ | Function.update y i₀ t ∈ Ω} ⊆ ⋃ m : Fin M, I_piece m ∧
      ∀ m : Fin M, Convex ℝ (I_piece m) ∧
        ContinuousOn (fun t => F (Function.update y i₀ t)) (I_piece m) ∧
        ∀ t₁ ∈ I_piece m, ∀ t₂ ∈ I_piece m, t₁ < t₂ → ∀ ε > 0,
          ∃ h ∈ Ioc (0 : ℝ) (t₂ - t₁),
            (c - ε) * h ≤
              (if sgn m then 1 else -1) *
                (F (Function.update y i₀ (t₁ + h)) - F (Function.update y i₀ t₁)))
    (e₀ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)} ≤
      (M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c) := by
  let γ_pi := Measure.pi fun _ : ι => gaussianReal 0 1
  let E : Set (ι → ℝ) := {x | x ∈ Ω ∧ F x ∈ Ioc e₀ (e₀ + δ)}
  have hE_meas : MeasurableSet E := hΩ.inter (hF measurableSet_Ioc)
  -- One-dimensional fiber bound for every y : ι → ℝ
  have h1d (y : ι → ℝ) :
      (gaussianReal 0 1) {t : ℝ | Function.update y i₀ t ∈ E} ≤
        ENNReal.ofReal ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
    obtain ⟨I_piece, sgn, hcov, hpiece⟩ := hfib y
    let g : ℝ → ℝ := fun t => F (Function.update y i₀ t)
    -- Bound each convex piece m ∈ Fin M inside a closed interval of length δ / c
    have hpiece_box (m : Fin M) : ∃ a_m : ℝ,
        I_piece m ∩ {t | g t ∈ Ioc e₀ (e₀ + δ)} ⊆ Icc a_m (a_m + δ / c) := by
      let A_m := I_piece m ∩ {t | g t ∈ Ioc e₀ (e₀ + δ)}
      by_cases hA_emp : A_m = ∅
      · exact ⟨0, by rw [hA_emp]; exact empty_subset _⟩
      · obtain ⟨t₀, ht₀⟩ := nonempty_iff_ne_empty.mpr hA_emp
        -- Show every two points t₁ ≤ t₂ in A_m satisfy t₂ - t₁ ≤ δ / c
        obtain ⟨hconv, hcont, hdini_m⟩ := hpiece m
        have hdiam : ∀ t₁ ∈ A_m, ∀ t₂ ∈ A_m, t₁ ≤ t₂ → t₂ - t₁ ≤ δ / c := by
          intro t₁ ht₁ t₂ ht₂ h12
          rcases eq_or_lt_of_le h12 with rfl | hlt
          · simp [div_nonneg hδ hc.le]
          · have hIcc_sub : Icc t₁ t₂ ⊆ I_piece m := hconv.ordConnected.out ht₁.1 ht₂.1
            let σ : ℝ := if sgn m then 1 else -1
            let g_σ : ℝ → ℝ := fun t => σ * g t
            have hg_σ_cont : ContinuousOn g_σ (Icc t₁ t₂) :=
              continuousOn_const.mul (hcont.mono hIcc_sub)
            have hg_σ_dini : ∀ t ∈ Ico t₁ t₂, ∀ ε > 0, ∃ h ∈ Ioc (0 : ℝ) (t₂ - t),
                (c - ε) * h ≤ g_σ (t + h) - g_σ t := by
              intro t ht ε hε
              obtain ⟨h, hh_mem, hh_step⟩ := hdini_m t (hIcc_sub ⟨ht.1, ht.2.le⟩) t₂ ht₂.1 ht.2 ε hε
              exact ⟨h, hh_mem, by dsimp only [g_σ, σ]; linarith only [hh_step]⟩
            have hgrowth := dini_mul_sub_le_sub h12 hg_σ_cont hg_σ_dini
            have hspan : g_σ t₂ - g_σ t₁ ≤ δ := by
              dsimp only [g_σ, σ]
              split_ifs
              · linarith only [ht₁.2.1, ht₂.2.2]
              · linarith only [ht₁.2.2, ht₂.2.1]
            exact (le_div_iff₀ hc).mpr (by rw [mul_comm]; linarith only [hgrowth, hspan])
        have hA_bddBelow : BddBelow A_m := ⟨t₀ - δ / c, fun t ht => by
          rcases le_total t t₀ with hle | hge
          · linarith only [hdiam t ht t₀ ht₀ hle]
          · linarith only [hge, div_nonneg hδ hc.le]⟩
        let a_m := sInf A_m
        refine ⟨a_m, fun t ht => ⟨csInf_le hA_bddBelow ht, ?_⟩⟩
        -- For every ε > 0, some u ∈ A_m has u < a_m + ε; actually t - δ / c is a lower bound on A_m!
        have hlb : t - δ / c ≤ a_m := le_csInf ⟨t₀, ht₀⟩ fun u hu => by
          rcases le_total u t with hut | htu
          · linarith only [hdiam u hu t ht hut]
          · linarith only [htu, div_nonneg hδ hc.le]
        linarith only [hlb]
    choose a_m ha_m using hpiece_box
    have hsub_union : {t : ℝ | Function.update y i₀ t ∈ E} ⊆
        ⋃ m : Fin M, Icc (a_m m) (a_m m + δ / c) := by
      intro t ⟨htΩ, htF⟩
      obtain ⟨m, hm⟩ := mem_iUnion.mp (hcov htΩ)
      exact mem_iUnion.mpr ⟨m, ha_m m ⟨hm, htF⟩⟩
    calc (gaussianReal 0 1) {t : ℝ | Function.update y i₀ t ∈ E}
        ≤ (gaussianReal 0 1) (⋃ m : Fin M, Icc (a_m m) (a_m m + δ / c)) := measure_mono hsub_union
      _ ≤ ∑ m : Fin M, (gaussianReal 0 1) (Icc (a_m m) (a_m m + δ / c)) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _m : Fin M, ENNReal.ofReal (δ / (Real.sqrt (2 * Real.pi) * c)) := by
          refine Finset.sum_le_sum fun m _ => ?_
          refine (gaussianReal_le_density_mul_volume _ measurableSet_Icc).trans ?_
          rw [Real.volume_Icc, add_sub_cancel_left, ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          exact le_of_eq (by ring)
      _ = ENNReal.ofReal ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg M), mul_div_assoc]
  -- Disintegrate Measure.pi along i₀ vs {i // i ≠ i₀}
  let e_split := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· = i₀)).trans
    ((MeasurableEquiv.funUnique {i : ι // i = i₀} ℝ).prodCongr (MeasurableEquiv.refl _))
  let μ_rest := Measure.pi fun _ : {i : ι // i ≠ i₀} => gaussianReal 0 1
  have hmp : MeasurePreserving e_split γ_pi ((gaussianReal 0 1).prod μ_rest) :=
    (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => gaussianReal 0 1) (· = i₀)).trans
      ((measurePreserving_funUnique (gaussianReal 0 1) {i : ι // i = i₀}).prod
        (MeasurePreserving.id μ_rest))
  have hE_eq : γ_pi E = ((gaussianReal 0 1).prod μ_rest) (e_split.symm ⁻¹' E) := by
    rw [← hmp.measure_preimage (e_split.symm.measurable hE_meas).nullMeasurableSet]
    congr 1; ext x; simp
  have hprod_eval : ((gaussianReal 0 1).prod μ_rest) (e_split.symm ⁻¹' E) =
      ∫⁻ z, (gaussianReal 0 1) {t : ℝ | e_split.symm (t, z) ∈ E} ∂μ_rest :=
    Measure.prod_apply_symm (e_split.symm.measurable hE_meas)
  have hsec_le : ∀ z : {i : ι // i ≠ i₀} → ℝ,
      (gaussianReal 0 1) {t : ℝ | e_split.symm (t, z) ∈ E} ≤
        ENNReal.ofReal ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
    intro z
    let y : ι → ℝ := e_split.symm (0, z)
    have hupd_eq (t : ℝ) : e_split.symm (t, z) = Function.update y i₀ t := by
      funext i
      by_cases hi : i = i₀
      · subst hi
        simp [e_split, y, MeasurableEquiv.piEquivPiSubtypeProd]
      · simp [e_split, y, hi, MeasurableEquiv.piEquivPiSubtypeProd]
    simp_rw [hupd_eq]
    exact h1d y
  have htot : γ_pi E ≤ ENNReal.ofReal ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
    rw [hE_eq, hprod_eval]
    refine (lintegral_mono hsec_le).trans ?_
    rw [lintegral_const, measure_univ, mul_one]
  rw [Measure.real]
  exact (ENNReal.toReal_le_of_le_ofReal (by positivity) htot)

/-- Direct transfer of `M`-piece right Dini transversality across active budgets
`j < (4 N + 1) * (2 N + 2) * (2 ^ N) ^ 2` to fixed-`e = 1 / 10` zero-drop locking
`m_{1/10 + δ} = m_{1/10}` without polynomial degree loss. -/
theorem fixed_tenth_locking_of_dini_anticoncentration {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N : ℕ} (hN : 2 ≤ N) (i₀ : ι)
    (H : (ι → ℝ) → selfAdjoint (Register N))
    (hH_meas : ∀ j : ℕ, Measurable fun x => criticalHeight (H x) j)
    {Ω : ℕ → Set (ι → ℝ)} (hΩ_meas : ∀ j, MeasurableSet (Ω j))
    (M : ℕ) {c : ℝ} (hc : 0 < c)
    (hfib : ∀ j < (4 * N + 1) * (2 * N + 2) * (2 ^ N) ^ 2, ∀ y : ι → ℝ,
      ∃ (I_piece : Fin M → Set ℝ) (sgn : Fin M → Bool),
        {t : ℝ | Function.update y i₀ t ∈ Ω j} ⊆ ⋃ m : Fin M, I_piece m ∧
        ∀ m : Fin M, Convex ℝ (I_piece m) ∧
          ContinuousOn (fun t => criticalHeight (H (Function.update y i₀ t)) j) (I_piece m) ∧
          ∀ t₁ ∈ I_piece m, ∀ t₂ ∈ I_piece m, t₁ < t₂ → ∀ ε > 0,
            ∃ h ∈ Ioc (0 : ℝ) (t₂ - t₁),
              (c - ε) * h ≤
                (if sgn m then 1 else -1) *
                  (criticalHeight (H (Function.update y i₀ (t₁ + h))) j -
                    criticalHeight (H (Function.update y i₀ t₁)) j))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    let Q := (4 * N + 1) * (2 * N + 2) * (2 ^ N) ^ 2
    let Ω_all := ⋂ j ∈ Finset.range Q, Ω j
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      {x ∈ Ω_all | ∃ m₁ m₂ : ℕ,
        IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10) m₁ ∧
        IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10 + δ) m₂ ∧ m₁ ≠ m₂} ≤
      (Q : ℝ) * ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
  intro Q Ω_all
  let γ_pi := Measure.pi fun _ : ι => gaussianReal 0 1
  let Bad := {x : ι → ℝ | x ∈ Ω_all ∧ ∃ m₁ m₂ : ℕ,
    IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10) m₁ ∧
    IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10 + δ) m₂ ∧ m₁ ≠ m₂}
  have hsub : Bad ⊆ ⋃ j ∈ Finset.range Q,
      {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)} := by
    rintro x ⟨hxΩ, m₁, m₂, hm₁, hm₂, hne⟩
    have hnot_clear : ¬ (1 / 10 : ℝ) ∉ jumpTolerances (H x) δ := by
      intro hclear
      exact hne ((maximum_eq_iff_criticalHeight_clearance hN (H x) (by norm_num) hδ hm₁ hm₂).2.mpr hclear)
    rw [not_not] at hnot_clear
    obtain ⟨j, _, hj_mem⟩ := hnot_clear
    have hj_lt_Q : j < Q := by
      by_contra hge
      have h0 := criticalHeight_eq_zero_of_exact_cap hN (H x) (Nat.le_of_not_lt hge)
      rw [h0] at hj_mem
      linarith only [hj_mem.1]
    exact mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj_lt_Q,
      (mem_iInter₂.mp hxΩ) j (Finset.mem_range.mpr hj_lt_Q), hj_mem⟩
  have hmeas_union : γ_pi Bad ≤ ∑ j ∈ Finset.range Q,
      γ_pi {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)} :=
    (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
  have hbound_enn : γ_pi Bad ≤ ENNReal.ofReal ((Q : ℝ) * ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c))) := by
    refine hmeas_union.trans ?_
    calc ∑ j ∈ Finset.range Q, γ_pi {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)}
        ≤ ∑ _j ∈ Finset.range Q, ENNReal.ofReal ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj_lt : j < Q := Finset.mem_range.mp hj
          have hreal := gaussian_degreeFree_dini_anticoncentration i₀ (hH_meas j) (hΩ_meas j)
            M hc (hfib j hj_lt) (1 / 10) hδ
          rw [← ENNReal.ofReal_toReal (measure_ne_top γ_pi _)]
          exact ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal ((Q : ℝ) * ((M : ℝ) * δ / (Real.sqrt (2 * Real.pi) * c))) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg Q)]
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbound_enn

#print axioms exists_torusCriticalHeight_saddle
#print axioms opNorm_add_smul_ge_of_mem_maxRightSingularSphere
#print axioms tendsto_opNorm_directionalDeriv
#print axioms re_inner_unitary_sub_skewAdjointCommutator
#print axioms dini_torusPointDistance_sandwich
#print axioms liminf_torusCriticalHeight_transverseFlow_ge
#print axioms exists_unitaryRatio_singularEigenmode
#print axioms sup_selfAdjoint_expectation_diff_eq
#print axioms tenth_saddle_unitBall_sensitivity_eq
#print axioms common_eigenmode_sensitivity_zero
#print axioms pauliCommutator_stationary_iff_eigenmode
#print axioms finrank_chainPauliTransverseSpan_le
#print axioms oscillatorySliceCounterexample_violation
#print axioms dini_mul_sub_le_sub
#print axioms gaussian_degreeFree_dini_anticoncentration
#print axioms fixed_tenth_locking_of_dini_anticoncentration

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau

