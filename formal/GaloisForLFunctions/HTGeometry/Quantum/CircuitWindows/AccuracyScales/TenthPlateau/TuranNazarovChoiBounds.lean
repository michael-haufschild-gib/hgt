import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.DeterminantalCircuitBarriers
import GaloisForLFunctions.HTGeometry.MontgomeryVaughanIntervalMeanSquare
import GaloisForLFunctions.HTGeometry.PowerSumTuranWeightedLowerBound
import GaloisForLFunctions.HTGeometry.PolynomialExtrapolationRemez

/-! # Quantitative Montgomery–Vaughan and Turán bounds on homogeneous Choi circuit annihilators

This module resolves the quantitative lower- and upper-bound geometry of homogeneous degree-`r`
Choi circuit annihilators `evalHomogeneousChoiPoly W (unitaryEvolution H.val t)` past the
`choose(2N, 2)` matchgate threshold:

1. **Exact Hilbert-sphere chordal ceiling vs. non-linear `1 / 10` threshold:**
   - `norm_evalHomogeneousChoiPoly_le_one` and `no_unitChoiPoly_gt_r_div_ten`: for every unit-norm
     Choi functional `W` (`‖W‖ = 1`) and every unitary `U ∈ U(2^N)`, `‖P_W(U)‖ ≤ 1`; consequently,
     for every `r ≥ 10` (including `r = 192 * N * Nat.log 2 N`), `‖P_W(exp(-i t H))‖ ≤ r / 10`
     holds identically for all `t ∈ ℝ`.
   - `norm_evalHomogeneousChoiPoly_le_sqrt_one_sub_chordal` and
     `tenthPlateauOnset_le_of_choiPoly_gt_chordal`: two-vector Bessel orthogonality on the unit
     Choi sphere lowers the impossible `r / 10` threshold to the exact non-linear chordal barrier
     `√(1 - (199 / 200)^(2 r)) < 1`: whenever `‖P_W(exp(-i t H))‖ > √(1 - (199 / 200)^(2 r))` for
     `t ∈ [0, T]`, `1 / 10 < orbitCircuitDistance H s t` and `tenthPlateauOnset H s ≤ T`.
   - `exists_unitary_dist_tenth_choiPoly_eq_chordal`, `norm_choiPoly_smallScale_le`, and
     `gaussian_rk3_choiPoly_strang_ceiling`: the threshold `√(1 - (199 / 200)^(2 r))` is attained
     with equality at operator-norm distance `1 / 10` from `1`, small-gap generators `ε • H` obey
     `‖P_W(exp(-i t (ε H)))‖ ≤ r * |ε * t|`, and brickwork Strang compilation keeps
     `‖P_W(exp(-i t H(x)))‖ ≤ √(1 - (199 / 200)^(2 r))` across `s ≥ choose(2N, 2)` and
     `(130 * R)^3 * t^3 ≤ N` on `Ω_rk3(n, η) ∩ {‖x‖_∞ ≤ R}`.
2. **Abstract Montgomery–Vaughan positive-density and Turán short-horizon extrapolation:**
   - `angular_expSum_meanSquare_ge`, `exists_angular_expSum_ge_at_gapHorizon`, and
     `volume_angular_expSum_gt_ge`: for angular frequencies separated by `Γ > 0`, the interval mean
     square over `[a, a + T]` is at least `(T - 52 / Γ) * E`, yielding
     `sup_{t ∈ [0, 104 / Γ]} ‖f(t)‖ ≥ √(E / 2)` and positive Lebesgue occupation `(E / 2) * T`
     where `‖f(t)‖ > √E / 2` for `T ≥ 208 / Γ`.
   - `exists_angular_expSum_shortHorizon_ge_of_turan`: backward unit-circle stepping via
     `exists_norm_weightedPowerSum_ge` transfers any long-time witness `‖f(t_★)‖ ≥ β` down to an
     explicit quantitative lower bound on `[0, T]` for every `T > 0`.
3. **Symmetric replica eigenmode annihilators with explicit `2^(-N r)` Parseval floor:**
   - `exists_quantitative_choiAnnihilator_of_carrier_lt_multiset` and
     `quantitative_turanNazarov_choiAnnihilator_past_matchgate`: rank-nullity on the orthonormal
     symmetric replica subspace `O_r(V)` produces a unit-norm `s`-gate Choi annihilator whose
     eigenfrequency expansion has explicit Hamiltonian-independent Parseval energy `≥ 2^(-N r)`,
     delivering unconditional Montgomery–Vaughan and Turán lower bounds at `s = choose(2N, 2) + 1`
     and `r = 192 * N * Nat.log 2 N` for all `N ≥ 64`. -/

open Set Filter MeasureTheory ProbabilityTheory Real Topology Matrix NormedSpace
open scoped Matrix.Norms.L2Operator ENNReal NNReal ComplexConjugate BigOperators
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
open WeakBonds PrescribedTimes SpanningDensity.FixedHorizon
open OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw GaloisForLFunctions.RHTower
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev UGroup (N : ℕ) := Matrix.unitaryGroup (Config N) ℂ

/-! ## Section 1: Abstract Hilbert-sphere chordal-Bessel geometry and exact `1 / 10` threshold -/

section AbstractChordalBessel

/-- Two-vector Bessel inequality in any complex inner product space: if `‖W‖ = 1`, `‖w‖ = 1`,
`‖x‖ = 1`, and `⟨W, w⟩ = 0`, then `‖⟨W, x⟩‖^2 + ‖⟨w, x⟩‖^2 ≤ 1`. -/
theorem two_orth_bessel_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {W w x : E} (hW : ‖W‖ = 1) (hw : ‖w‖ = 1) (hx : ‖x‖ = 1) (horth : inner ℂ W w = 0) :
    ‖inner ℂ W x‖ ^ 2 + ‖inner ℂ w x‖ ^ 2 ≤ 1 := by
  let v : Fin 2 → E := ![W, w]
  have hv_orth : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [v, inner_self_eq_norm_sq_to_K, hW, hw, horth, inner_eq_zero_symm.mp horth]
  have hb := hv_orth.sum_inner_products_le (s := Finset.univ) x
  rw [Fin.sum_univ_two, hx, one_pow] at hb
  simpa [v] using hb

/-- Chordal inner-product lower bound for unit vectors in any complex inner product space:
if `‖u‖ = 1`, `‖v‖ = 1`, and `‖u - v‖ ≤ e`, then `1 - e^2 / 2 ≤ (inner ℂ u v).re`, and if
additionally `e^2 ≤ 2`, then `1 - e^2 / 2 ≤ ‖inner ℂ u v‖`. -/
theorem re_and_norm_inner_ge_of_unit_sub_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {e : ℝ} (_he0 : 0 ≤ e)
    (hsub : ‖u - v‖ ≤ e) :
    1 - e ^ 2 / 2 ≤ (inner ℂ u v).re ∧
    (e ^ 2 ≤ 2 → 1 - e ^ 2 / 2 ≤ ‖inner ℂ u v‖) := by
  have hsq_le : ‖u - v‖ ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsub 2
  have hsub_sq : ‖u - v‖ ^ 2 = 2 - 2 * (inner ℂ u v).re := by
    have h1 : ((‖u - v‖ ^ 2 : ℝ) : ℂ) = inner ℂ (u - v) (u - v) := by
      rw [Complex.ofReal_pow, inner_self_eq_norm_sq_to_K]; rfl
    have h2 := congrArg Complex.re h1
    rw [Complex.ofReal_re, inner_sub_left, inner_sub_right, inner_sub_right] at h2
    have huu : (inner ℂ u u).re = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
    have hvv : (inner ℂ v v).re = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; norm_num
    have hvu : (inner ℂ v u).re = (inner ℂ u v).re := by
      rw [← inner_conj_symm u v, Complex.conj_re]
    simp only [Complex.sub_re, huu, hvv, hvu] at h2
    linarith only [h2]
  have hre : 1 - e ^ 2 / 2 ≤ (inner ℂ u v).re := by linarith only [hsq_le, hsub_sq]
  refine ⟨hre, fun _ => hre.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))⟩

/-- Inner product of `r`-fold pure tensor powers factors as the `r`-th power of the single-copy
inner product. -/
theorem inner_finitePureTensorPowerEuclidean_eq_pow {ι : Type*} [Fintype ι]
    (r : ℕ) (u v : ι → ℂ) :
    inner ℂ (finitePureTensorPowerEuclidean r u) (finitePureTensorPowerEuclidean r v) =
      (inner ℂ (WithLp.toLp 2 u : EuclideanSpace ℂ ι)
        (WithLp.toLp 2 v : EuclideanSpace ℂ ι)) ^ r := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct finitePureTensorPowerEuclidean finitePureTensorPower
  simp only [Pi.star_apply, star_prod, ← Finset.prod_mul_distrib]
  rw [(Fintype.prod_sum fun (_ : Fin r) (i : ι) => v i * star (u i)).symm,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end AbstractChordalBessel

private theorem norm_matrixNormalizedChoi_of_mem_unitary {N : ℕ} {A : Register N}
    (hA : A ∈ unitary (Register N)) :
    ‖(WithLp.toLp 2 (matrixNormalizedChoi A) : EuclideanSpace ℂ (Config N × Config N))‖ = 1 := by
  have hsq : ‖(WithLp.toLp 2 (matrixNormalizedChoi A) : EuclideanSpace ℂ _)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    unfold matrixNormalizedChoi
    have hcard_pos : (0 : ℝ) < Fintype.card (Config N) := Nat.cast_pos.mpr Fintype.card_pos
    have hterm (x y : Config N) :
        ‖A x y / Real.sqrt (Fintype.card (Config N))‖ ^ 2 =
          ‖A x y‖ ^ 2 / Fintype.card (Config N) := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        div_pow, Real.sq_sqrt hcard_pos.le]
    simp_rw [hterm, ← Finset.sum_div]
    have hsum_col (x : Config N) : (∑ y : Config N, ‖A x y‖ ^ 2) = 1 := by
      have h1 := congrFun (congrFun (Unitary.mem_iff.mp hA).2 x) x
      rw [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.one_apply_eq] at h1
      have h2 : ((∑ y : Config N, ‖A x y‖ ^ 2 : ℝ) : ℂ) = 1 := by
        rw [← h1, Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      exact_mod_cast h2
    simp_rw [hsum_col, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      div_self hcard_pos.ne']
  nlinarith only [hsq, norm_nonneg (WithLp.toLp 2 (matrixNormalizedChoi A) : EuclideanSpace ℂ _),
    sq_nonneg (‖(WithLp.toLp 2 (matrixNormalizedChoi A) : EuclideanSpace ℂ _)‖ - 1)]

private theorem norm_pureTensorPower_of_mem_unitary {N : ℕ} (r : ℕ) {A : Register N}
    (hA : A ∈ unitary (Register N)) :
    ‖finitePureTensorPowerEuclidean r (matrixNormalizedChoi A)‖ = 1 := by
  have hsq := norm_sq_finitePureTensorPowerEuclidean_eq_pow r (matrixNormalizedChoi A)
  rw [norm_matrixNormalizedChoi_of_mem_unitary hA, one_pow, one_pow] at hsq
  nlinarith only [hsq, norm_nonneg (finitePureTensorPowerEuclidean r (matrixNormalizedChoi A)),
    sq_nonneg (‖finitePureTensorPowerEuclidean r (matrixNormalizedChoi A)‖ - 1)]

private theorem norm_choi_sub_le_opNorm {N : ℕ} (A B : Register N) :
    ‖(WithLp.toLp 2 (matrixNormalizedChoi A) : EuclideanSpace ℂ (Config N × Config N)) -
      WithLp.toLp 2 (matrixNormalizedChoi B)‖ ≤ ‖A - B‖ := by
  have hsq :
      ‖(WithLp.toLp 2 (matrixNormalizedChoi A) : EuclideanSpace ℂ (Config N × Config N)) -
        WithLp.toLp 2 (matrixNormalizedChoi B)‖ ^ 2 ≤ ‖A - B‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    let X := A - B
    have hcard_eq : (Fintype.card (Config N) : ℝ) = (2 : ℝ) ^ N := by simp [Config]
    have hterm (x y : Config N) :
        ‖((WithLp.toLp 2 (matrixNormalizedChoi A) : EuclideanSpace ℂ (Config N × Config N)) -
          WithLp.toLp 2 (matrixNormalizedChoi B)).ofLp (x, y)‖ ^ 2 =
          ((2 : ℝ) ^ N)⁻¹ * ‖X x y‖ ^ 2 := by
      dsimp [matrixNormalizedChoi, X]
      rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        div_pow, Real.sq_sqrt (by positivity), hcard_eq, div_eq_inv_mul]
    simp_rw [hterm, ← Finset.mul_sum]
    have hcol (y : Config N) : (∑ x : Config N, ‖X x y‖ ^ 2) ≤ ‖X‖ ^ 2 := by
      let e_y : EuclideanSpace ℂ (Config N) := PiLp.single 2 y 1
      have he_norm : ‖e_y‖ = 1 := by simp [e_y]
      have hact : ‖(WithLp.toLp 2 (X *ᵥ e_y.ofLp) : EuclideanSpace ℂ (Config N))‖ ≤ ‖X‖ := by
        have hle := Matrix.l2_opNorm_mulVec X e_y
        rwa [he_norm, mul_one] at hle
      have hsq_col : ‖(WithLp.toLp 2 (X *ᵥ e_y.ofLp) : EuclideanSpace ℂ (Config N))‖ ^ 2 ≤ ‖X‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hact 2
      rw [EuclideanSpace.norm_sq_eq] at hsq_col
      refine le_trans ?_ hsq_col
      refine Finset.sum_le_sum fun x _ => ?_
      have hxy : (X *ᵥ e_y.ofLp) x = X x y := by
        simp [Matrix.mulVec, dotProduct, e_y, PiLp.single_apply]
      rw [WithLp.ofLp_toLp, hxy]
    have hfrob : (∑ x : Config N, ∑ y : Config N, ‖X x y‖ ^ 2) ≤ ((2 : ℝ) ^ N) * ‖X‖ ^ 2 := by
      rw [Finset.sum_comm]
      calc (∑ y : Config N, ∑ x : Config N, ‖X x y‖ ^ 2)
          ≤ ∑ _y : Config N, ‖X‖ ^ 2 := Finset.sum_le_sum fun y _ => hcol y
        _ = ((2 : ℝ) ^ N) * ‖X‖ ^ 2 := by simp [Fintype.card_fin, Fintype.card_bool]
    calc ((2 : ℝ) ^ N)⁻¹ * ∑ x : Config N, ∑ y : Config N, ‖X x y‖ ^ 2
        ≤ ((2 : ℝ) ^ N)⁻¹ * (((2 : ℝ) ^ N) * ‖X‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hfrob (inv_nonneg.mpr (by positivity))
      _ = ‖X‖ ^ 2 := by rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Universal Cauchy–Schwarz unit ceiling: for every unit-norm degree-`r` Choi functional `W` and
every unitary `U ∈ unitary (Register N)`, `‖evalHomogeneousChoiPoly W U‖ ≤ 1`. -/
theorem norm_evalHomogeneousChoiPoly_le_one {N r : ℕ}
    {W : EuclideanSpace ℂ (Fin r → Config N × Config N)} (hW : ‖W‖ = 1)
    {U : Register N} (hU : U ∈ unitary (Register N)) :
    ‖evalHomogeneousChoiPoly W U‖ ≤ 1 := by
  unfold evalHomogeneousChoiPoly
  calc ‖inner ℂ W (finitePureTensorPowerEuclidean r (matrixNormalizedChoi U))‖
      ≤ ‖W‖ * ‖finitePureTensorPowerEuclidean r (matrixNormalizedChoi U)‖ :=
        norm_inner_le_norm _ _
    _ = 1 := by rw [hW, norm_pureTensorPower_of_mem_unitary r hU, mul_one]

/-- No-go for the linearized threshold `r / 10`: for every `r ≥ 10`, every unit-norm Choi functional
`W`, every `H : selfAdjoint (Register N)`, and every `t ∈ ℝ`,
`‖evalHomogeneousChoiPoly W (unitaryEvolution H.val t)‖ ≤ r / 10` (so `> r / 10` is impossible). -/
theorem no_unitChoiPoly_gt_r_div_ten {N r : ℕ} (hr : 10 ≤ r)
    {W : EuclideanSpace ℂ (Fin r → Config N × Config N)} (hW : ‖W‖ = 1)
    (H : selfAdjoint (Register N)) :
    (∀ t : ℝ, ‖evalHomogeneousChoiPoly W (unitaryEvolution H.val t)‖ ≤ (r : ℝ) / 10) ∧
    ¬ ∃ t : ℝ, (r : ℝ) / 10 < ‖evalHomogeneousChoiPoly W (unitaryEvolution H.val t)‖ := by
  have hr_ge : (1 : ℝ) ≤ (r : ℝ) / 10 := by
    have hr10 : (10 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith only [hr10]
  have hall : ∀ t : ℝ, ‖evalHomogeneousChoiPoly W (unitaryEvolution H.val t)‖ ≤ (r : ℝ) / 10 :=
    fun t => (norm_evalHomogeneousChoiPoly_le_one hW (unitaryEvolution_mem_unitary H.2 t)).trans hr_ge
  exact ⟨hall, fun ⟨t, ht⟩ => (not_lt_of_ge (hall t)) ht⟩

/-- Exact non-linear chordal upper bound on `S_circ(r, s)ᗮ`: if `‖W‖ = 1` vanishes on all
projective `s`-gate circuits and `Metric.infDist U (phaseCircuitMatrixImageAtMost N s) ≤ e` with
`0 ≤ e` and `e^2 ≤ 2`, then `‖evalHomogeneousChoiPoly W U‖ ≤ √(1 - (1 - e^2 / 2)^(2 r))`. -/
theorem norm_evalHomogeneousChoiPoly_le_sqrt_one_sub_chordal {N s r : ℕ}
    {W : EuclideanSpace ℂ (Fin r → Config N × Config N)} (hW : ‖W‖ = 1)
    (hvan : ∀ (C : TwoQubitCircuit N), C.gateCount ≤ s → ∀ z : ℂ,
      evalHomogeneousChoiPoly W (z • (C.eval : Register N)) = 0)
    {U : Register N} (hU : U ∈ unitary (Register N))
    {e : ℝ} (he0 : 0 ≤ e) (he2 : e ^ 2 ≤ 2)
    (hdist : Metric.infDist U (phaseCircuitMatrixImageAtMost N s) ≤ e) :
    ‖evalHomogeneousChoiPoly W U‖ ≤ Real.sqrt (1 - (1 - e ^ 2 / 2) ^ (2 * r)) := by
  have hsq_le_all : ∀ δ > 0, e + δ ≤ Real.sqrt 2 →
      ‖evalHomogeneousChoiPoly W U‖ ^ 2 ≤ 1 - (1 - (e + δ) ^ 2 / 2) ^ (2 * r) := by
    intro δ hδ hcap
    have hC_ne : (phaseCircuitMatrixImageAtMost N s).Nonempty :=
      ⟨(1 : ℂ) • ((TwoQubitCircuit.one N).eval : Register N),
        mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨1, norm_one, TwoQubitCircuit.one N, Nat.zero_le _, rfl⟩⟩
    obtain ⟨M_c, hM_mem, hM_lt⟩ := (Metric.infDist_lt_iff hC_ne).mp
      (lt_of_le_of_lt hdist (lt_add_of_pos_right e hδ))
    obtain ⟨z, hz, C, hC, rfl⟩ := mem_phaseCircuitMatrixImageAtMost_iff.mp hM_mem
    rw [dist_eq_norm] at hM_lt
    have hM_unit : z • (C.eval : Register N) ∈ unitary (Register N) := by
      rw [Unitary.mem_iff]
      have hC_u := Unitary.mem_iff.mp C.eval.2
      have hzz : (starRingEnd ℂ) z * z = 1 := by
        rw [Complex.conj_mul', hz, Complex.ofReal_one, one_pow]
      exact ⟨by rw [star_smul, smul_mul_smul_comm, Complex.star_def, hzz, hC_u.1, one_smul],
        by rw [star_smul, smul_mul_smul_comm, Complex.star_def, mul_comm, hzz, hC_u.2, one_smul]⟩
    let u_c : EuclideanSpace ℂ (Config N × Config N) := WithLp.toLp 2 (matrixNormalizedChoi U)
    let v_c : EuclideanSpace ℂ (Config N × Config N) :=
      WithLp.toLp 2 (matrixNormalizedChoi (z • (C.eval : Register N)))
    have hu_n : ‖u_c‖ = 1 := norm_matrixNormalizedChoi_of_mem_unitary hU
    have hv_n : ‖v_c‖ = 1 := norm_matrixNormalizedChoi_of_mem_unitary hM_unit
    have heδ0 : 0 ≤ e + δ := add_nonneg he0 hδ.le
    have heδ2 : (e + δ) ^ 2 ≤ 2 := by
      have h1 := pow_le_pow_left₀ heδ0 hcap 2
      rwa [Real.sq_sqrt two_pos.le] at h1
    have hchoi_le : ‖v_c - u_c‖ ≤ e + δ := by
      rw [norm_sub_rev]
      exact (norm_choi_sub_le_opNorm U _).trans hM_lt.le
    have hinner_ge : 1 - (e + δ) ^ 2 / 2 ≤ ‖inner ℂ v_c u_c‖ :=
      (re_and_norm_inner_ge_of_unit_sub_le hv_n hu_n heδ0 hchoi_le).2 heδ2
    let x := finitePureTensorPowerEuclidean r (matrixNormalizedChoi U)
    let w := finitePureTensorPowerEuclidean r (matrixNormalizedChoi (z • (C.eval : Register N)))
    have hx_n : ‖x‖ = 1 := norm_pureTensorPower_of_mem_unitary r hU
    have hw_n : ‖w‖ = 1 := norm_pureTensorPower_of_mem_unitary r hM_unit
    have horth : inner ℂ W w = 0 := hvan C hC z
    have hbessel := two_orth_bessel_sq hW hw_n hx_n horth
    have hwx_ge : (1 - (e + δ) ^ 2 / 2) ^ (2 * r) ≤ ‖inner ℂ w x‖ ^ 2 := by
      have hwx_eq : ‖inner ℂ w x‖ = ‖inner ℂ v_c u_c‖ ^ r := by
        dsimp only [w, x, v_c, u_c]
        rw [inner_finitePureTensorPowerEuclidean_eq_pow, norm_pow]
      rw [hwx_eq, ← pow_mul, mul_comm r 2]
      exact pow_le_pow_left₀ (by linarith only [heδ2]) hinner_ge (2 * r)
    unfold evalHomogeneousChoiPoly
    linarith only [hbessel, hwx_ge]
  have hsq_final : ‖evalHomogeneousChoiPoly W U‖ ^ 2 ≤ 1 - (1 - e ^ 2 / 2) ^ (2 * r) := by
    by_cases hstrict : e < Real.sqrt 2
    · have htend : Tendsto (fun δ : ℝ => 1 - (1 - (e + δ) ^ 2 / 2) ^ (2 * r))
          (𝓝[>] 0) (𝓝 (1 - (1 - e ^ 2 / 2) ^ (2 * r))) := by
        have hc2 : Continuous (fun δ : ℝ => 1 - (1 - (e + δ) ^ 2 / 2) ^ (2 * r)) := by fun_prop
        simpa only [add_zero] using (hc2.tendsto 0).mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
          ‖evalHomogeneousChoiPoly W U‖ ^ 2 ≤ 1 - (1 - (e + δ) ^ 2 / 2) ^ (2 * r) := by
        have hlt_mem : Iio (Real.sqrt 2 - e) ∈ 𝓝[>] (0 : ℝ) :=
          nhdsWithin_le_nhds (Iio_mem_nhds (sub_pos.mpr hstrict))
        filter_upwards [self_mem_nhdsWithin, hlt_mem] with δ hδ_pos hδ_lt
        exact hsq_le_all δ hδ_pos (by linarith only [mem_Iio.mp hδ_lt])
      exact le_of_tendsto_of_tendsto tendsto_const_nhds htend hev
    · have he_eq : e = Real.sqrt 2 := by
        have hle : e ≤ Real.sqrt 2 := by
          rw [← Real.sqrt_sq he0]
          exact Real.sqrt_le_sqrt he2
        exact le_antisymm hle (not_lt.mp hstrict)
      rw [he_eq, Real.sq_sqrt two_pos.le, div_self two_ne_zero, sub_self]
      rcases eq_or_ne r 0 with rfl | hr_ne
      · have hu1 : finitePureTensorPowerEuclidean 0 (matrixNormalizedChoi U) =
            finitePureTensorPowerEuclidean 0
              (matrixNormalizedChoi ((1 : ℂ) • ((TwoQubitCircuit.one N).eval : Register N))) := by
          ext p; simp [finitePureTensorPowerEuclidean, finitePureTensorPower]
        have h0 : evalHomogeneousChoiPoly W U = 0 := by
          unfold evalHomogeneousChoiPoly
          rw [hu1]
          exact hvan (TwoQubitCircuit.one N) (Nat.zero_le _) 1
        rw [h0, norm_zero]; norm_num
      · rw [zero_pow (Nat.mul_ne_zero two_ne_zero hr_ne), sub_zero]
        have h1 := norm_evalHomogeneousChoiPoly_le_one hW hU
        nlinarith only [h1, norm_nonneg (evalHomogeneousChoiPoly W U)]
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt hsq_final

/-- Exact non-linear `1 / 10` onset witness: if `W` (`‖W‖ = 1`) vanishes on all projective `s`-gate
circuits and `√(1 - (199 / 200)^(2 r)) < ‖evalHomogeneousChoiPoly W (exp(-i t H))‖` at some
`t ∈ [0, T]` (`0 ≤ T`), then `1 / 10 < orbitCircuitDistance H s t`, and `tenthPlateauOnset H s ≤ T`. -/
theorem tenthPlateauOnset_le_of_choiPoly_gt_chordal {N s r : ℕ}
    {W : EuclideanSpace ℂ (Fin r → Config N × Config N)} (hW : ‖W‖ = 1)
    (hvan : ∀ (C : TwoQubitCircuit N), C.gateCount ≤ s → ∀ z : ℂ,
      evalHomogeneousChoiPoly W (z • (C.eval : Register N)) = 0)
    (H : selfAdjoint (Register N)) {T t : ℝ} (_hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    (hgt : Real.sqrt (1 - (199 / 200 : ℝ) ^ (2 * r)) <
      ‖evalHomogeneousChoiPoly W (unitaryEvolution H.val t)‖) :
    1 / 10 < orbitCircuitDistance H s t ∧ tenthPlateauOnset H s ≤ T := by
  have hdist_gt : 1 / 10 < orbitCircuitDistance H s t := by
    by_contra hle
    have hle' : orbitCircuitDistance H s t ≤ 1 / 10 := not_lt.mp hle
    have hbound := norm_evalHomogeneousChoiPoly_le_sqrt_one_sub_chordal hW hvan
      (unitaryEvolution_mem_unitary H.2 t) (by norm_num : (0 : ℝ) ≤ 1 / 10)
      (by norm_num : (1 / 10 : ℝ) ^ 2 ≤ 2) hle'
    have h199 : 1 - (1 / 10 : ℝ) ^ 2 / 2 = (199 / 200 : ℝ) := by norm_num
    rw [h199] at hbound
    exact (not_lt_of_ge hbound) hgt
  refine ⟨hdist_gt, ?_⟩
  have h0_zero : orbitCircuitDistance H s 0 = 0 := by
    apply le_antisymm _ Metric.infDist_nonneg
    have hmem : (1 : ℂ) • ((TwoQubitCircuit.one N).eval : Register N) ∈
        phaseCircuitMatrixImageAtMost N s :=
      mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨1, norm_one, TwoQubitCircuit.one N, Nat.zero_le _, rfl⟩
    have hu0 : unitaryEvolution H.val 0 = 1 := by simp [unitaryEvolution]
    refine (Metric.infDist_le_dist_of_mem hmem).trans_eq ?_
    rw [dist_eq_norm, hu0, one_smul, TwoQubitCircuit.one_eval,
      Submonoid.coe_one, sub_self, norm_zero]
  have hcont : Continuous (orbitCircuitDistance H s) := (orbitCircuitDistance_lipschitz H s).continuous
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.continuousAt_iff.mp hcont.continuousAt
    (1 / 10 : ℝ) (by norm_num)
  let r₀ := δ / 2
  have hr₀_pos : 0 < r₀ := half_pos hδ_pos
  have hr₀_all : ∀ τ ∈ Icc 0 r₀, orbitCircuitDistance H s τ < 1 / 10 := by
    intro τ hτ
    have hdist_τ : dist τ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hτ.1]
      linarith only [hτ.2, hδ_pos, show r₀ = δ / 2 from rfl]
    have h1 := hδ_ball hdist_τ
    rw [Real.dist_eq, h0_zero, sub_zero] at h1
    exact lt_of_le_of_lt (le_abs_self _) h1
  exact (tenthPlateauOnset_spec H hr₀_pos ht.1 hr₀_all hdist_gt).2.1.le.trans ht.2

private theorem sum_config_qubitZero_avg {N : ℕ} (hN : 1 ≤ N) (a b : ℂ) :
    (∑ x : Config N, if x ⟨0, hN⟩ then a else b) =
      (Fintype.card (Config N) : ℂ) * ((a + b) / 2) := by
  let i₀ : Fin N := ⟨0, hN⟩
  have hinv_fn (x : Config N) :
      Function.update (Function.update x i₀ (!x i₀)) i₀ (!Function.update x i₀ (!x i₀) i₀) = x := by
    funext j
    by_cases hj : j = i₀
    · subst hj; simp
    · simp [hj]
  let flip : Config N ≃ Config N :=
    { toFun := fun x => Function.update x i₀ (!x i₀)
      invFun := fun x => Function.update x i₀ (!x i₀)
      left_inv := hinv_fn
      right_inv := hinv_fn }
  let g : Config N → ℂ := fun x => if x i₀ then a else b
  have hflip : (∑ x : Config N, g x) = ∑ x : Config N, g (flip x) := (Equiv.sum_comp flip g).symm
  have hpair (x : Config N) : g x + g (flip x) = a + b := by
    change (if x i₀ then a else b) + (if Function.update x i₀ (!x i₀) i₀ then a else b) = a + b
    rw [Function.update_self]
    cases x i₀ <;> simp [add_comm]
  have h2 : 2 * ∑ x : Config N, g x = (Fintype.card (Config N) : ℂ) * (a + b) := by
    calc 2 * ∑ x : Config N, g x
        = (∑ x : Config N, g x) + ∑ x : Config N, g (flip x) := by rw [← hflip]; ring
      _ = ∑ x : Config N, (g x + g (flip x)) := Finset.sum_add_distrib.symm
      _ = ∑ _x : Config N, (a + b) := Finset.sum_congr rfl fun x _ => hpair x
      _ = (Fintype.card (Config N) : ℂ) * (a + b) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  dsimp only [g] at h2
  linear_combination (1 / 2 : ℂ) * h2

/-- Exact sharpness of the chordal threshold `√(1 - (199 / 200)^(2 r))` at distance `1 / 10`:
for every `N ≥ 1` and `r ≥ 1`, there exist `U_α ∈ unitary (Register N)` with `‖U_α - 1‖ = 1 / 10`
(hence `Metric.infDist U_α (phaseCircuitMatrixImageAtMost N 0) ≤ 1 / 10`) and a unit-norm `0`-gate
Choi annihilator `W` achieving `‖evalHomogeneousChoiPoly W U_α‖ = √(1 - (199 / 200)^(2 r))`. -/
theorem exists_unitary_dist_tenth_choiPoly_eq_chordal {N r : ℕ} (hN : 1 ≤ N) (hr : 1 ≤ r) :
    ∃ (U_α : Register N) (W : EuclideanSpace ℂ (Fin r → Config N × Config N)),
      U_α ∈ unitary (Register N) ∧
      ‖U_α - (1 : Register N)‖ = 1 / 10 ∧
      ‖W‖ = 1 ∧
      (∀ (C : TwoQubitCircuit N), C.gateCount ≤ 0 → ∀ z : ℂ,
        evalHomogeneousChoiPoly W (z • (C.eval : Register N)) = 0) ∧
      ‖evalHomogeneousChoiPoly W U_α‖ = Real.sqrt (1 - (199 / 200 : ℝ) ^ (2 * r)) := by
  let i₀ : Fin N := ⟨0, hN⟩
  let y₀ : ℝ := Real.sqrt (399 / 40000)
  have hy₀_sq : y₀ ^ 2 = 399 / 40000 := Real.sq_sqrt (by norm_num)
  let z_plus : ℂ := ⟨199 / 200, y₀⟩
  let z_minus : ℂ := ⟨199 / 200, -y₀⟩
  have hz_plus_norm_sq : Complex.normSq z_plus = 1 := by
    have hre : z_plus.re = 199 / 200 := rfl
    have him : z_plus.im = y₀ := rfl
    rw [Complex.normSq_apply, hre, him]; nlinarith only [hy₀_sq]
  have hz_minus_norm_sq : Complex.normSq z_minus = 1 := by
    have hre : z_minus.re = 199 / 200 := rfl
    have him : z_minus.im = -y₀ := rfl
    rw [Complex.normSq_apply, hre, him]; nlinarith only [hy₀_sq]
  have hz_plus_sub_sq : ‖z_plus - 1‖ ^ 2 = (1 / 10 : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hre : (z_plus - 1).re = -1 / 200 := by simp [z_plus]; ring
    have him : (z_plus - 1).im = y₀ := by simp [z_plus]
    rw [hre, him]; nlinarith only [hy₀_sq]
  have hz_minus_sub_sq : ‖z_minus - 1‖ ^ 2 = (1 / 10 : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hre : (z_minus - 1).re = -1 / 200 := by simp [z_minus]; ring
    have him : (z_minus - 1).im = -y₀ := by simp [z_minus]
    rw [hre, him]; nlinarith only [hy₀_sq]
  have hz_plus_sub : ‖z_plus - 1‖ = 1 / 10 := by
    nlinarith only [hz_plus_sub_sq, norm_nonneg (z_plus - 1), sq_nonneg (‖z_plus - 1‖ - 1 / 10)]
  have hz_minus_sub : ‖z_minus - 1‖ = 1 / 10 := by
    nlinarith only [hz_minus_sub_sq, norm_nonneg (z_minus - 1), sq_nonneg (‖z_minus - 1‖ - 1 / 10)]
  let d_fn : Config N → ℂ := fun x => if x i₀ then z_minus else z_plus
  let U_α : Register N := Matrix.diagonal d_fn
  have hU_unit : U_α ∈ unitary (Register N) := by
    rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose]
    dsimp only [U_α]
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    have hconj_mul (x : Config N) :
        (starRingEnd ℂ) (d_fn x) * d_fn x = 1 ∧ d_fn x * (starRingEnd ℂ) (d_fn x) = 1 := by
      have hns : Complex.normSq (d_fn x) = 1 := by
        dsimp only [d_fn]; split_ifs <;> [exact hz_minus_norm_sq; exact hz_plus_norm_sq]
      have h1 : (starRingEnd ℂ) (d_fn x) * d_fn x = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self, hns, Complex.ofReal_one]
      exact ⟨h1, by rw [mul_comm, h1]⟩
    constructor <;> ext x y <;> by_cases hxy : x = y
    · subst hxy; simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply, Complex.star_def]
      exact (hconj_mul x).1
    · simp [hxy]
    · subst hxy; simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply, Complex.star_def]
      exact (hconj_mul x).2
    · simp [hxy]
  have h1_norm : ‖(1 : Register N)‖ = 1 :=
    CStarRing.norm_of_mem_unitary (Submonoid.one_mem (unitary (Register N)))
  have hU_dist : ‖U_α - (1 : Register N)‖ = 1 / 10 := by
    have hdiff_diag : U_α - (1 : Register N) = Matrix.diagonal (fun x => d_fn x - 1) := by
      ext x y; by_cases hxy : x = y <;> simp [U_α, hxy]
    have hdfn_sub (x : Config N) : ‖d_fn x - 1‖ = 1 / 10 := by
      dsimp only [d_fn]; split_ifs <;> [exact hz_minus_sub; exact hz_plus_sub]
    apply le_antisymm
    · have hstar_mul : star (U_α - 1) * (U_α - 1) = ((1 / 100 : ℝ) : ℂ) • (1 : Register N) := by
        rw [hdiff_diag, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
          Matrix.diagonal_mul_diagonal]
        ext x y
        by_cases hxy : x = y
        · subst hxy
          simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
            Pi.star_apply, Complex.star_def, Complex.conj_mul', hdfn_sub x, smul_eq_mul, mul_one]
          push_cast; norm_num
        · simp [hxy]
      have hcs := CStarRing.norm_star_mul_self (x := U_α - (1 : Register N))
      rw [hstar_mul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by norm_num),
        h1_norm, mul_one] at hcs
      have hsq : ‖U_α - (1 : Register N)‖ ^ 2 = (1 / 10 : ℝ) ^ 2 := by linarith only [hcs]
      nlinarith only [hsq, norm_nonneg (U_α - (1 : Register N)),
        sq_nonneg (‖U_α - (1 : Register N)‖ - 1 / 10)]
    · let x₀ : Config N := fun _ => false
      let e_0 : EuclideanSpace ℂ (Config N) := PiLp.single 2 x₀ 1
      have he0_n : ‖e_0‖ = 1 := by simp [e_0]
      have hact := Matrix.l2_opNorm_mulVec (U_α - (1 : Register N)) e_0
      rw [he0_n, mul_one] at hact
      have hvec_raw : (U_α - (1 : Register N)) *ᵥ e_0.ofLp = (d_fn x₀ - 1) • e_0.ofLp := by
        funext x
        rw [hdiff_diag, Matrix.mulVec_diagonal]
        simp only [e_0, PiLp.single_apply, Pi.smul_apply, smul_eq_mul]
        by_cases hx : x = x₀
        · subst hx; ring
        · simp [hx]
      rw [hvec_raw, map_smul, norm_smul] at hact
      have he0_eq : (EuclideanSpace.equiv (Config N) ℂ).symm e_0.ofLp = e_0 := rfl
      rw [he0_eq, he0_n, mul_one, hdfn_sub x₀] at hact
      exact hact
  let u_one : EuclideanSpace ℂ (Config N × Config N) :=
    WithLp.toLp 2 (matrixNormalizedChoi (1 : Register N))
  let u_α : EuclideanSpace ℂ (Config N × Config N) :=
    WithLp.toLp 2 (matrixNormalizedChoi U_α)
  have hinner_single : inner ℂ u_one u_α = (199 / 200 : ℂ) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    unfold dotProduct u_one u_α matrixNormalizedChoi
    simp only [Pi.star_apply]
    rw [Fintype.sum_prod_type]
    have hpos : (0 : ℝ) < Fintype.card (Config N) := Nat.cast_pos.mpr Fintype.card_pos
    have hsq_c : (↑(Real.sqrt ↑(Fintype.card (Config N))) : ℂ) *
        ↑(Real.sqrt ↑(Fintype.card (Config N))) = (Fintype.card (Config N) : ℂ) := by
      rw [← Complex.ofReal_mul, ← sq, Real.sq_sqrt hpos.le, Complex.ofReal_natCast]
    have hdiag_sum (x : Config N) :
        (∑ y : Config N, U_α (x, y).1 (x, y).2 / ↑(Real.sqrt ↑(Fintype.card (Config N))) *
          star ((1 : Register N) (x, y).1 (x, y).2 / ↑(Real.sqrt ↑(Fintype.card (Config N))))) =
          d_fn x / (Fintype.card (Config N) : ℂ) := by
      rw [Finset.sum_eq_single x]
      · simp only [U_α, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        rw [Complex.star_def, map_div₀, map_one, Complex.conj_ofReal, div_mul_div_comm,
          mul_one, hsq_c]
      · intro y _ hyx; simp [Matrix.one_apply_ne (Ne.symm hyx)]
      · intro h; exact (h (Finset.mem_univ x)).elim
    simp_rw [hdiag_sum, ← Finset.sum_div]
    have hsum_d : (∑ x : Config N, d_fn x) =
        (Fintype.card (Config N) : ℂ) * ((z_minus + z_plus) / 2) :=
      sum_config_qubitZero_avg hN z_minus z_plus
    have hz_avg : (z_minus + z_plus) / 2 = (199 / 200 : ℂ) := by
      apply Complex.ext <;> simp [z_minus, z_plus]
    have hcard_ne : (Fintype.card (Config N) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [hsum_d, hz_avg, mul_div_cancel_left₀ _ hcard_ne]
  let w₀ := finitePureTensorPowerEuclidean r (matrixNormalizedChoi (1 : Register N))
  let x_α := finitePureTensorPowerEuclidean r (matrixNormalizedChoi U_α)
  have hw₀_n : ‖w₀‖ = 1 :=
    norm_pureTensorPower_of_mem_unitary r (Submonoid.one_mem (unitary (Register N)))
  have hxα_n : ‖x_α‖ = 1 := norm_pureTensorPower_of_mem_unitary r hU_unit
  have hinner_r : inner ℂ w₀ x_α = ((199 / 200 : ℝ) ^ r : ℂ) := by
    dsimp only [w₀, x_α]
    rw [inner_finitePureTensorPowerEuclidean_eq_pow, hinner_single]
    push_cast; rfl
  let γ_r : ℝ := (199 / 200 : ℝ) ^ r
  let s_r : ℝ := Real.sqrt (1 - (199 / 200 : ℝ) ^ (2 * r))
  have hγ_lt1 : γ_r ^ 2 < 1 := by
    dsimp only [γ_r]
    rw [← pow_mul, mul_comm r 2]
    exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.mul_ne_zero two_ne_zero (by omega))
  have hs_pos : 0 < s_r := Real.sqrt_pos.mpr (sub_pos.mpr (by
    dsimp only [γ_r] at hγ_lt1; rwa [← pow_mul, mul_comm r 2] at hγ_lt1))
  let w_raw := x_α - (γ_r : ℂ) • w₀
  have hw_raw_orth : inner ℂ w_raw w₀ = 0 := by
    dsimp only [w_raw]
    rw [inner_sub_left, inner_smul_left, ← inner_conj_symm x_α w₀, hinner_r,
      inner_self_eq_norm_sq_to_K, hw₀_n]
    dsimp only [γ_r]; push_cast; simp
  have hw_raw_sq : ‖w_raw‖ ^ 2 = s_r ^ 2 := by
    have h1 : ((‖w_raw‖ ^ 2 : ℝ) : ℂ) = inner ℂ w_raw w_raw := by
      rw [Complex.ofReal_pow, inner_self_eq_norm_sq_to_K]; rfl
    have h2 : inner ℂ w_raw w_raw = inner ℂ w_raw x_α := by
      conv_lhs => arg 2; dsimp only [w_raw]
      rw [inner_sub_right, inner_smul_right, hw_raw_orth, mul_zero, sub_zero]
    have h3 : inner ℂ w_raw x_α = 1 - ((γ_r ^ 2 : ℝ) : ℂ) := by
      dsimp only [w_raw]
      rw [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, hxα_n, hinner_r,
        Complex.conj_ofReal]
      dsimp only [γ_r]; push_cast; ring
    have hre := congrArg Complex.re (h1.trans (h2.trans h3))
    simp only [Complex.ofReal_re, Complex.sub_re, Complex.one_re] at hre
    have hs_sq : s_r ^ 2 = 1 - γ_r ^ 2 := by
      dsimp only [s_r, γ_r]
      rw [Real.sq_sqrt (sub_pos.mpr (by
        dsimp only [γ_r] at hγ_lt1; rwa [← pow_mul, mul_comm r 2] at hγ_lt1)).le,
        ← pow_mul, mul_comm r 2]
    linarith only [hre, hs_sq]
  have hw_raw_norm : ‖w_raw‖ = s_r := by
    nlinarith only [hw_raw_sq, norm_nonneg w_raw, hs_pos, sq_nonneg (‖w_raw‖ - s_r)]
  let W : EuclideanSpace ℂ (Fin r → Config N × Config N) := ((s_r⁻¹ : ℝ) : ℂ) • w_raw
  have hW_norm : ‖W‖ = 1 := by
    dsimp only [W]
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hs_pos.le),
      hw_raw_norm, inv_mul_cancel₀ hs_pos.ne']
  have hW_van : ∀ (C : TwoQubitCircuit N), C.gateCount ≤ 0 → ∀ z : ℂ,
      evalHomogeneousChoiPoly W (z • (C.eval : Register N)) = 0 := by
    intro C hC z
    have hC0 : C.gateCount = 0 := Nat.eq_zero_of_le_zero hC
    have hC_eval : (C.eval : Register N) = 1 := by
      unfold TwoQubitCircuit.eval TwoQubitArchitecture.contraction
      have hnil : (List.ofFn fun k : Fin C.gateCount => C.architecture.gateLift k (C.gates k)) = [] :=
        List.eq_nil_iff_length_eq_zero.mpr (by simp [hC0])
      rw [hnil]; rfl
    rw [hC_eval]
    unfold evalHomogeneousChoiPoly
    have hsmul : finitePureTensorPowerEuclidean r (matrixNormalizedChoi (z • (1 : Register N))) =
        (z ^ r) • w₀ := by
      ext p
      simp only [w₀, finitePureTensorPowerEuclidean, finitePureTensorPower, matrixNormalizedChoi,
        Matrix.smul_apply, smul_eq_mul, mul_div_assoc, PiLp.smul_apply, WithLp.ofLp_toLp,
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hsmul, inner_smul_right]
    dsimp only [W]
    rw [inner_smul_left, hw_raw_orth, mul_zero, mul_zero]
  have hW_eval : ‖evalHomogeneousChoiPoly W U_α‖ = s_r := by
    unfold evalHomogeneousChoiPoly
    change ‖inner ℂ W x_α‖ = s_r
    have hin : inner ℂ W x_α = (s_r : ℂ) := by
      dsimp only [W]
      rw [inner_smul_left, Complex.conj_ofReal]
      have hwx : inner ℂ w_raw x_α = ((s_r ^ 2 : ℝ) : ℂ) := by
        have h1 : inner ℂ w_raw x_α = inner ℂ w_raw w_raw := by
          conv_rhs => arg 2; dsimp only [w_raw]
          rw [inner_sub_right, inner_smul_right, hw_raw_orth, mul_zero, sub_zero]
        rw [h1, inner_self_eq_norm_sq_to_K, hw_raw_norm]
        norm_cast
      rw [hwx]
      push_cast
      field_simp [hs_pos.ne']
    rw [hin, Complex.norm_real, Real.norm_of_nonneg hs_pos.le]
  exact ⟨U_α, W, hU_unit, hU_dist, hW_norm, hW_van, hW_eval⟩

/-- Separation-free small-scale barrier: without a lower bound on the Hamiltonian eigenfrequency
scale, rescaling `H` (`‖H.val‖ ≤ 1`) to `ε • H` keeps
`‖evalHomogeneousChoiPoly W (exp(-i t (ε H)))‖ ≤ r * |ε * t|` for every unit-norm `s`-gate Choi
annihilator `W` and every `t ∈ ℝ`. -/
theorem norm_choiPoly_smallScale_le {N s r : ℕ}
    {W : EuclideanSpace ℂ (Fin r → Config N × Config N)} (hW : ‖W‖ = 1)
    (hvan : ∀ (C : TwoQubitCircuit N), C.gateCount ≤ s → ∀ z : ℂ,
      evalHomogeneousChoiPoly W (z • (C.eval : Register N)) = 0)
    (H : selfAdjoint (Register N)) (hH_norm : ‖H.val‖ ≤ 1) (ε t : ℝ) :
    ‖evalHomogeneousChoiPoly W (unitaryEvolution ((ε : ℂ) • H.val) t)‖ ≤
      (r : ℝ) * |ε * t| := by
  have hvan_1 : evalHomogeneousChoiPoly W ((1 : ℂ) • ((TwoQubitCircuit.one N).eval : Register N)) = 0 :=
    hvan (TwoQubitCircuit.one N) (Nat.zero_le _) 1
  rw [one_smul, TwoQubitCircuit.one_eval, Submonoid.coe_one] at hvan_1
  have hscale_eq : unitaryEvolution ((ε : ℂ) • H.val) t = unitaryEvolution H.val (ε * t) := by
    unfold unitaryEvolution
    congr 1; ext x y
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast; ring
  have hop_le : ‖unitaryEvolution H.val (ε * t) - (1 : Register N)‖ ≤ |ε * t| := by
    have h0 : unitaryEvolution H.val 0 = 1 := by simp [unitaryEvolution]
    have h1 := norm_unitaryEvolution_time_sub_le H.2 (ε * t) 0
    rw [h0, sub_zero] at h1
    exact h1.trans ((mul_le_mul_of_nonneg_right hH_norm (abs_nonneg _)).trans_eq (one_mul _))
  rw [hscale_eq]
  let u_c : EuclideanSpace ℂ (Config N × Config N) :=
    WithLp.toLp 2 (matrixNormalizedChoi (unitaryEvolution H.val (ε * t)))
  let v_c : EuclideanSpace ℂ (Config N × Config N) :=
    WithLp.toLp 2 (matrixNormalizedChoi (1 : Register N))
  have hu_n : ‖u_c‖ = 1 := norm_matrixNormalizedChoi_of_mem_unitary
    (unitaryEvolution_mem_unitary H.2 (ε * t))
  have hsub_eval : evalHomogeneousChoiPoly W (unitaryEvolution H.val (ε * t)) =
      inner ℂ W (finitePureTensorPowerEuclidean r u_c.ofLp -
        finitePureTensorPowerEuclidean r v_c.ofLp) := by
    rw [inner_sub_right, ← evalHomogeneousChoiPoly, ← evalHomogeneousChoiPoly, hvan_1, sub_zero]
  have htensor_lip : ∀ (k : ℕ),
      ‖finitePureTensorPowerEuclidean k u_c.ofLp - finitePureTensorPowerEuclidean k v_c.ofLp‖ ≤
        (k : ℝ) * ‖u_c - v_c‖ := by
    intro k
    induction k with
    | zero =>
        have h0 : finitePureTensorPowerEuclidean 0 u_c.ofLp =
            finitePureTensorPowerEuclidean 0 v_c.ofLp := by
          ext p; simp [finitePureTensorPowerEuclidean, finitePureTensorPower]
        rw [h0, sub_self, norm_zero, Nat.cast_zero, zero_mul]
    | succ k ih =>
        let mid : EuclideanSpace ℂ (Fin (k + 1) → Config N × Config N) :=
          WithLp.toLp 2 (fun f => u_c.ofLp (f 0) *
            (finitePureTensorPowerEuclidean k v_c.ofLp).ofLp (fun j => f j.succ))
        have hv_k_n : ‖finitePureTensorPowerEuclidean k v_c.ofLp‖ = 1 :=
          norm_pureTensorPower_of_mem_unitary k (Submonoid.one_mem (unitary (Register N)))
        have hcons_sum {g : (Fin (k + 1) → Config N × Config N) → ℝ} :
            (∑ f : Fin (k + 1) → Config N × Config N, g f) =
              ∑ i : Config N × Config N, ∑ tail : Fin k → Config N × Config N, g (Fin.cons i tail) := by
          rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (k + 1) => Config N × Config N) g,
            Fintype.sum_prod_type]
          rfl
        have h1_sq : ‖finitePureTensorPowerEuclidean (k + 1) u_c.ofLp - mid‖ ^ 2 =
            ‖finitePureTensorPowerEuclidean k u_c.ofLp -
              finitePureTensorPowerEuclidean k v_c.ofLp‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq, hcons_sum]
          have hterm (i : Config N × Config N) (tail : Fin k → Config N × Config N) :
              ‖(finitePureTensorPowerEuclidean (k + 1) u_c.ofLp - mid).ofLp (Fin.cons i tail)‖ ^ 2 =
                ‖u_c.ofLp i‖ ^ 2 * ‖(finitePureTensorPowerEuclidean k u_c.ofLp -
                  finitePureTensorPowerEuclidean k v_c.ofLp).ofLp tail‖ ^ 2 := by
            simp only [WithLp.ofLp_sub, Pi.sub_apply, finitePureTensorPowerEuclidean,
              finitePureTensorPower, mid, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
            rw [← mul_sub, norm_mul, mul_pow]
          simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul, ← EuclideanSpace.norm_sq_eq,
            hu_n, one_pow, one_mul]
        have h2_sq : ‖mid - finitePureTensorPowerEuclidean (k + 1) v_c.ofLp‖ ^ 2 =
            ‖u_c - v_c‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq, hcons_sum]
          have hterm (i : Config N × Config N) (tail : Fin k → Config N × Config N) :
              ‖(mid - finitePureTensorPowerEuclidean (k + 1) v_c.ofLp).ofLp (Fin.cons i tail)‖ ^ 2 =
                ‖(u_c - v_c).ofLp i‖ ^ 2 *
                  ‖(finitePureTensorPowerEuclidean k v_c.ofLp).ofLp tail‖ ^ 2 := by
            simp only [WithLp.ofLp_sub, Pi.sub_apply, finitePureTensorPowerEuclidean,
              finitePureTensorPower, mid, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
            rw [← sub_mul, norm_mul, mul_pow]
          simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul, ← EuclideanSpace.norm_sq_eq,
            hv_k_n, one_pow, mul_one]
        have h1 : ‖finitePureTensorPowerEuclidean (k + 1) u_c.ofLp - mid‖ =
            ‖finitePureTensorPowerEuclidean k u_c.ofLp -
              finitePureTensorPowerEuclidean k v_c.ofLp‖ := by
          nlinarith only [h1_sq, norm_nonneg (finitePureTensorPowerEuclidean (k + 1) u_c.ofLp - mid),
            norm_nonneg (finitePureTensorPowerEuclidean k u_c.ofLp -
              finitePureTensorPowerEuclidean k v_c.ofLp),
            sq_nonneg (‖finitePureTensorPowerEuclidean (k + 1) u_c.ofLp - mid‖ -
              ‖finitePureTensorPowerEuclidean k u_c.ofLp -
                finitePureTensorPowerEuclidean k v_c.ofLp‖)]
        have h2 : ‖mid - finitePureTensorPowerEuclidean (k + 1) v_c.ofLp‖ = ‖u_c - v_c‖ := by
          nlinarith only [h2_sq, norm_nonneg (mid - finitePureTensorPowerEuclidean (k + 1) v_c.ofLp),
            norm_nonneg (u_c - v_c),
            sq_nonneg (‖mid - finitePureTensorPowerEuclidean (k + 1) v_c.ofLp‖ - ‖u_c - v_c‖)]
        have htri := norm_sub_le_norm_sub_add_norm_sub
          (finitePureTensorPowerEuclidean (k + 1) u_c.ofLp) mid
          (finitePureTensorPowerEuclidean (k + 1) v_c.ofLp)
        push_cast; linarith only [htri, h1, h2, ih]
  rw [hsub_eval]
  calc ‖inner ℂ W (finitePureTensorPowerEuclidean r u_c.ofLp -
        finitePureTensorPowerEuclidean r v_c.ofLp)‖
      ≤ ‖W‖ * ‖finitePureTensorPowerEuclidean r u_c.ofLp -
          finitePureTensorPowerEuclidean r v_c.ofLp‖ := norm_inner_le_norm _ _
    _ ≤ 1 * ((r : ℝ) * ‖u_c - v_c‖) := by
        rw [hW]; exact mul_le_mul_of_nonneg_left (htensor_lip r) zero_le_one
    _ ≤ (r : ℝ) * ‖unitaryEvolution H.val (ε * t) - (1 : Register N)‖ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left (norm_choi_sub_le_opNorm _ _) (Nat.cast_nonneg r)
    _ ≤ (r : ℝ) * |ε * t| := mul_le_mul_of_nonneg_left hop_le (Nat.cast_nonneg r)

/-- Brickwork Strang `T ≲ N^(1/3) / R` ceiling on Choi annihilators over `Ω_rk3(n, η)`:
throughout `Ω_rk3(n, η) ∩ {‖x‖_∞ ≤ R}`, for every `s ≥ (n + 2) * (2 * (n + 2) - 1)`, every `r`,
every unit-norm `s`-gate Choi annihilator `W`, and every `t ∈ [0, T]` with `(130 * R)^3 * T^3 ≤ n + 2`,
`‖evalHomogeneousChoiPoly W (exp(-i t H(x)))‖ ≤ √(1 - (199 / 200)^(2 r))`. -/
theorem gaussian_rk3_choiPoly_strang_ceiling (n r : ℕ) {η R : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hR1 : 1 ≤ R) :
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let E_surv : Set (PrefixIndex n → ℝ) :=
      bondRankThreeFieldEvent n η ∩ {x | ∀ i : PrefixIndex n, |x i| ≤ R}
    1 - ((38 * n + 39 : ℕ) : ℝ) * η ^ 2 -
        2 * ((12 * n + 15 : ℕ) : ℝ) * Real.exp (-(R ^ 2 / 2)) ≤ μ.real E_surv ∧
      ∀ x ∈ E_surv,
        let u : PathShell n := WithLp.toLp 2 (x ∘ (pathCoeffEquiv n).symm)
        let H : selfAdjoint (Register (n + 2)) :=
          ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
        ∀ s ≥ (n + 2) * (2 * (n + 2) - 1),
        ∀ W : EuclideanSpace ℂ (Fin r → Config (n + 2) × Config (n + 2)), ‖W‖ = 1 →
        (∀ (C : TwoQubitCircuit (n + 2)), C.gateCount ≤ s → ∀ z : ℂ,
          evalHomogeneousChoiPoly W (z • (C.eval : Register (n + 2))) = 0) →
        ∀ T ≥ 0, (130 * R) ^ 3 * T ^ 3 ≤ ((n + 2 : ℕ) : ℝ) →
        ∀ t ∈ Icc (0 : ℝ) T,
          ‖evalHomogeneousChoiPoly W (unitaryEvolution H.val t)‖ ≤
            Real.sqrt (1 - (199 / 200 : ℝ) ^ (2 * r)) := by
  intro μ E_surv
  obtain ⟨hprob, hsurv⟩ := gaussian_rk3_strang_onset_survival n hη0 hη1 hR1
  refine ⟨hprob, fun x hx => ?_⟩
  intro u H s hs W hW hvan T hT0 hT_cube t ht
  have hlt := (hsurv x hx s hs T hT0 hT_cube).1 t ht
  have hbound := norm_evalHomogeneousChoiPoly_le_sqrt_one_sub_chordal hW hvan
    (unitaryEvolution_mem_unitary H.2 t) (by norm_num : (0 : ℝ) ≤ 1 / 10)
    (by norm_num : (1 / 10 : ℝ) ^ 2 ≤ 2) hlt.le
  have h199 : 1 - (1 / 10 : ℝ) ^ 2 / 2 = (199 / 200 : ℝ) := by norm_num
  rwa [h199] at hbound

/-! ## Section 2: Abstract Montgomery–Vaughan positive-density and Turán short-horizon extrapolation -/

section AbstractExpSumExtrapolation

/-- Angular-frequency Montgomery–Vaughan interval mean-square lower bound: if `ω : ι → ℝ` has
pairwise separation `|ω i - ω j| ≥ Γ > 0` (`i ≠ j`), then on every interval `[a, a + T]`,
`(T - 52 / Γ) * ∑ i, ‖c i‖^2 ≤ ∫ t in a..a + T, ‖∑ i, c i * exp(-i t ω_i)‖^2`. -/
theorem angular_expSum_meanSquare_ge {ι : Type} [Fintype ι] [DecidableEq ι]
    (ω : ι → ℝ) (c : ι → ℂ) {Γ a T : ℝ} (hΓ : 0 < Γ)
    (hsep : ∀ i j : ι, i ≠ j → Γ ≤ |ω i - ω j|) :
    (T - 52 / Γ) * ∑ i : ι, ‖c i‖ ^ 2 ≤
      ∫ t in a..a + T,
        ‖∑ i : ι, c i * Complex.exp (-(Complex.I * ((t * ω i : ℝ) : ℂ)))‖ ^ 2 := by
  let u : ι → ℝ := fun i => -ω i / (2 * Real.pi)
  let D : ℝ := Γ / (2 * Real.pi)
  have h2pi_pos : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  have hD_pos : 0 < D := div_pos hΓ h2pi_pos
  have hu_sep : ∀ i j : ι, i ≠ j → D ≤ |u i - u j| := by
    intro i j hij
    dsimp only [u, D]
    have hdiff : -ω i / (2 * Real.pi) - -ω j / (2 * Real.pi) =
        -(ω i - ω j) / (2 * Real.pi) := by ring
    rw [hdiff, abs_div, abs_neg, abs_of_pos h2pi_pos]
    exact div_le_div_of_nonneg_right (hsep i j hij) h2pi_pos.le
  have hmv := GaloisForLFunctions.HTGeometry.interval_integral_normSq_expSum_ge u c
    (a := a) (ℓ := T) hD_pos hu_sep
  have h26 : 26 / (Real.pi * D) = 52 / Γ := by
    dsimp only [D]
    field_simp [Real.pi_ne_zero, hΓ.ne']
    ring
  have hterm (t : ℝ) (i : ι) :
      GaloisForLFunctions.HTGeometry.mvExp (u i) t =
        Complex.exp (-(Complex.I * ((t * ω i : ℝ) : ℂ))) := by
    unfold GaloisForLFunctions.HTGeometry.mvExp
    dsimp only [u]
    congr 1
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp [hpi_ne]
  rw [h26] at hmv
  refine hmv.trans_eq ?_
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp_rw [hterm t]

/-- Gap-calibrated point lower bound at `T = 104 / Γ`: for `Γ > 0`-separated frequencies `ω`,
there exists `t_★ ∈ [0, 104 / Γ]` with `√((∑ i, ‖c i‖^2) / 2) ≤ ‖∑ i, c i * exp(-i t_★ ω_i)‖`. -/
theorem exists_angular_expSum_ge_at_gapHorizon {ι : Type} [Fintype ι] [DecidableEq ι]
    (ω : ι → ℝ) (c : ι → ℂ) {Γ : ℝ} (hΓ : 0 < Γ)
    (hsep : ∀ i j : ι, i ≠ j → Γ ≤ |ω i - ω j|) :
    ∃ t_star ∈ Icc (0 : ℝ) (104 / Γ),
      Real.sqrt ((∑ i : ι, ‖c i‖ ^ 2) / 2) ≤
        ‖∑ i : ι, c i * Complex.exp (-(Complex.I * ((t_star * ω i : ℝ) : ℂ)))‖ := by
  let T : ℝ := 104 / Γ
  have hT_pos : 0 < T := div_pos (by norm_num) hΓ
  let f : ℝ → ℂ := fun t => ∑ i : ι, c i * Complex.exp (-(Complex.I * ((t * ω i : ℝ) : ℂ)))
  have hf_cont : Continuous fun t : ℝ => ‖f t‖ ^ 2 := by
    dsimp only [f]; fun_prop
  obtain ⟨t_star, ht_mem, ht_max⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hT_pos.le) hf_cont.continuousOn
  have hmv := angular_expSum_meanSquare_ge ω c (a := 0) (T := T) hΓ hsep
  rw [zero_add] at hmv
  have h52 : T - 52 / Γ = T / 2 := by dsimp only [T]; ring
  rw [h52] at hmv
  have hint_le : (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) ≤ T * ‖f t_star‖ ^ 2 := by
    calc (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2)
        ≤ ∫ _t in (0 : ℝ)..T, ‖f t_star‖ ^ 2 := by
          refine intervalIntegral.integral_mono_on hT_pos.le (hf_cont.intervalIntegrable 0 T)
            intervalIntegrable_const fun t ht => ht_max ht
      _ = T * ‖f t_star‖ ^ 2 := by rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hsq_ge : (∑ i : ι, ‖c i‖ ^ 2) / 2 ≤ ‖f t_star‖ ^ 2 := by
    have hmul : (T / 2) * ∑ i : ι, ‖c i‖ ^ 2 ≤ T * ‖f t_star‖ ^ 2 := hmv.trans hint_le
    have hmul2 : T * ((∑ i : ι, ‖c i‖ ^ 2) / 2) ≤ T * ‖f t_star‖ ^ 2 := by linarith only [hmul]
    exact le_of_mul_le_mul_left hmul2 hT_pos
  refine ⟨t_star, ht_mem, ?_⟩
  rw [← Real.sqrt_sq (norm_nonneg (f t_star))]
  exact Real.sqrt_le_sqrt hsq_ge

/-- Positive Lebesgue occupation lower bound on every window `[a, a + T]` of length `T ≥ 208 / Γ`
for unit-bounded `Γ`-separated exponential sums (`∀ t, ‖f t‖ ≤ 1`):
`((∑ i, ‖c i‖^2) / 2) * T ≤ (volume {t ∈ Icc a (a + T) | √(∑ i, ‖c i‖^2) / 2 < ‖f t‖}).toReal`. -/
theorem volume_angular_expSum_gt_ge {ι : Type} [Fintype ι] [DecidableEq ι]
    (ω : ι → ℝ) (c : ι → ℂ) {Γ a T : ℝ} (hΓ : 0 < Γ)
    (hsep : ∀ i j : ι, i ≠ j → Γ ≤ |ω i - ω j|)
    (hT : 208 / Γ ≤ T)
    (hub : ∀ t : ℝ, ‖∑ i : ι, c i * Complex.exp (-(Complex.I * ((t * ω i : ℝ) : ℂ)))‖ ≤ 1) :
    let E := ∑ i : ι, ‖c i‖ ^ 2
    (E / 2) * T ≤
      (volume {t ∈ Icc a (a + T) | Real.sqrt E / 2 <
        ‖∑ i : ι, c i * Complex.exp (-(Complex.I * ((t * ω i : ℝ) : ℂ)))‖}).toReal := by
  intro E
  have hE_nn : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT_pos : 0 < T := lt_of_lt_of_le (div_pos (by norm_num) hΓ) hT
  let f : ℝ → ℂ := fun t => ∑ i : ι, c i * Complex.exp (-(Complex.I * ((t * ω i : ℝ) : ℂ)))
  have hf_cont : Continuous fun t : ℝ => ‖f t‖ := by dsimp only [f]; fun_prop
  let S_hi : Set ℝ := {t ∈ Icc a (a + T) | Real.sqrt E / 2 < ‖f t‖}
  have hS_meas : MeasurableSet S_hi :=
    measurableSet_Icc.inter (measurableSet_lt measurable_const hf_cont.measurable)
  have hS_fin : volume S_hi < ⊤ := by
    refine lt_of_le_of_lt (measure_mono (fun t ht => ht.1)) ?_
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hmv := angular_expSum_meanSquare_ge ω c (a := a) (T := T) hΓ hsep
  have h34 : (3 / 4 : ℝ) * T * E ≤ (T - 52 / Γ) * E := by
    have h208 : 52 / Γ = (1 / 4 : ℝ) * (208 / Γ) := by ring
    have hsub : (3 / 4 : ℝ) * T ≤ T - 52 / Γ := by linarith only [hT, h208]
    exact mul_le_mul_of_nonneg_right hsub hE_nn
  let g_dom : ℝ → ℝ := fun t => E / 4 + S_hi.indicator (fun _ => (1 : ℝ)) t
  have hpt_le (t : ℝ) (ht : t ∈ Ioc a (a + T)) : ‖f t‖ ^ 2 ≤ g_dom t := by
    dsimp only [g_dom]
    by_cases hmem : t ∈ S_hi
    · rw [Set.indicator_of_mem hmem]
      have h1 : ‖f t‖ ^ 2 ≤ 1 := by
        have hu := hub t
        nlinarith only [hu, norm_nonneg (f t)]
      linarith only [h1, hE_nn]
    · rw [Set.indicator_of_notMem hmem, add_zero]
      have hle_half : ‖f t‖ ≤ Real.sqrt E / 2 := by
        by_contra hgt
        exact hmem ⟨Ioc_subset_Icc_self ht, not_le.mp hgt⟩
      calc ‖f t‖ ^ 2 ≤ (Real.sqrt E / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle_half 2
        _ = E / 4 := by rw [div_pow, Real.sq_sqrt hE_nn]; norm_num
  have hint_eq : (∫ t in a..a + T, ‖f t‖ ^ 2) = ∫ t in Ioc a (a + T), ‖f t‖ ^ 2 :=
    intervalIntegral.integral_of_le (by linarith only [hT_pos])
  have hIoc_fin : volume (Ioc a (a + T)) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hconst_int : IntegrableOn (fun _ : ℝ => E / 4) (Ioc a (a + T)) :=
    integrableOn_const (hs := hIoc_fin)
  have hf_int : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioc a (a + T)) :=
    (hf_cont.pow 2).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hind_int : IntegrableOn (S_hi.indicator fun _ => (1 : ℝ)) (Ioc a (a + T)) :=
    ((integrable_indicator_iff hS_meas).mpr (integrableOn_const (hs := hS_fin.ne))).integrableOn
  have hg_int : IntegrableOn g_dom (Ioc a (a + T)) := hconst_int.add hind_int
  have hint_le : (∫ t in Ioc a (a + T), ‖f t‖ ^ 2) ≤ (E / 4) * T + (volume S_hi).toReal := by
    calc (∫ t in Ioc a (a + T), ‖f t‖ ^ 2)
        ≤ ∫ t in Ioc a (a + T), g_dom t := setIntegral_mono_on hf_int hg_int measurableSet_Ioc hpt_le
      _ = (∫ _t in Ioc a (a + T), E / 4) +
            ∫ t in Ioc a (a + T), S_hi.indicator (fun _ => (1 : ℝ)) t :=
          integral_add hconst_int hind_int
      _ ≤ (E / 4) * T + (volume S_hi).toReal := by
          have hconst : (∫ _t in Ioc a (a + T), E / 4) = (E / 4) * T := by
            rw [setIntegral_const, Measure.real, Real.volume_Ioc, add_sub_cancel_left,
              ENNReal.toReal_ofReal hT_pos.le, smul_eq_mul, mul_comm]
          have hind_le : (∫ t in Ioc a (a + T), S_hi.indicator (fun _ => (1 : ℝ)) t) ≤
              (volume S_hi).toReal := by
            rw [setIntegral_indicator hS_meas, setIntegral_const, smul_eq_mul, mul_one, Measure.real]
            exact ENNReal.toReal_mono hS_fin.ne (measure_mono inter_subset_right)
          linarith only [hconst, hind_le]
  rw [hint_eq] at hmv
  linarith only [h34, hmv, hint_le]

/-- Turán backward unit-circle extrapolation to arbitrary short horizons `T > 0`:
if `s : Finset ι` (`s.Nonempty`) and `‖∑ i ∈ s, c i * exp(-i t_★ ω_i)‖ ≥ β > 0` at `t_★ ≥ 0`, then
with `K = s.card` and `M = ⌊K * t_★ / T⌋ + 1`, there exists `t ∈ [0, T]` satisfying
`β / (2 * (e * K * (6 * (K + 1) * (M + 2 * K + 2))^K)) ≤ ‖∑ i ∈ s, c i * exp(-i t ω_i)‖`. -/
theorem exists_angular_expSum_shortHorizon_ge_of_turan {ι : Type*} (s : Finset ι)
    (hs_ne : s.Nonempty) (ω : ι → ℝ) (c : ι → ℂ)
    {t_star β T : ℝ} (ht_star0 : 0 ≤ t_star) (hβ0 : 0 < β) (hT0 : 0 < T)
    (h_at_star : β ≤ ‖∑ i ∈ s, c i * Complex.exp (-(Complex.I * ((t_star * ω i : ℝ) : ℂ)))‖) :
    let K := s.card
    let M := Nat.floor ((K : ℝ) * t_star / T) + 1
    ∃ t ∈ Icc (0 : ℝ) T,
      β / (2 * (Real.exp 1 * (K : ℝ) * (6 * ((K : ℝ) + 1) * ((M : ℝ) + 2 * (K : ℝ) + 2)) ^ K)) ≤
        ‖∑ i ∈ s, c i * Complex.exp (-(Complex.I * ((t * ω i : ℝ) : ℂ)))‖ := by
  classical
  intro K M
  have hK1 : 1 ≤ K := Finset.card_pos.mpr hs_ne
  have hK1_r : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  let denom : ℝ :=
    2 * (Real.exp 1 * (K : ℝ) * (6 * ((K : ℝ) + 1) * ((M : ℝ) + 2 * (K : ℝ) + 2)) ^ K)
  have hdenom_ge1 : 1 ≤ denom := by
    have hexp1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    have hbase1 : (1 : ℝ) ≤ 6 * ((K : ℝ) + 1) * ((M : ℝ) + 2 * (K : ℝ) + 2) := by
      have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      nlinarith only [hK1_r, hM0]
    have hpow1 : (1 : ℝ) ≤ (6 * ((K : ℝ) + 1) * ((M : ℝ) + 2 * (K : ℝ) + 2)) ^ K :=
      one_le_pow₀ hbase1
    have hprod1 : (1 : ℝ) ≤ Real.exp 1 * (K : ℝ) *
        (6 * ((K : ℝ) + 1) * ((M : ℝ) + 2 * (K : ℝ) + 2)) ^ K := by
      calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
        _ ≤ Real.exp 1 * (K : ℝ) * (6 * ((K : ℝ) + 1) * ((M : ℝ) + 2 * (K : ℝ) + 2)) ^ K :=
            mul_le_mul (mul_le_mul hexp1 hK1_r zero_le_one (Real.exp_pos 1).le)
              hpow1 zero_le_one (by positivity)
    dsimp only [denom]
    linarith only [hprod1]
  by_cases hshort : t_star ≤ T
  · refine ⟨t_star, ⟨ht_star0, hshort⟩, ?_⟩
    exact (div_le_self hβ0.le hdenom_ge1).trans h_at_star
  · have ht_gt : T < t_star := not_le.mp hshort
    have ht_pos : 0 < t_star := hT0.trans ht_gt
    have hMK_pos : 0 < (M : ℝ) + (K : ℝ) := by positivity
    let δ : ℝ := t_star / ((M : ℝ) + (K : ℝ))
    let b_tilde : ι → ℂ := fun i =>
      c i * Complex.exp (-(Complex.I * ((t_star * ω i : ℝ) : ℂ)))
    let z : ι → ℂ := fun i => Complex.exp (Complex.I * ((δ * ω i : ℝ) : ℂ))
    have hz_norm (i : ι) : ‖z i‖ = 1 := by
      dsimp only [z]
      rw [Complex.norm_exp]
      have hre : (Complex.I * ((δ * ω i : ℝ) : ℂ)).re = 0 := by simp
      rw [hre, Real.exp_zero]
    obtain ⟨i₀, hi₀⟩ := hs_ne
    have htop : ∃ i ∈ s, 1 ≤ ‖z i‖ := ⟨i₀, hi₀, by rw [hz_norm]⟩
    have hβ_filter : ∀ τ : ℝ, 1 - 1 / ((M : ℝ) + 2 * (s.card : ℝ) + 2) ≤ τ → τ ≤ 1 →
        β ≤ ‖∑ i ∈ s.filter (fun i => τ ≤ ‖z i‖), b_tilde i‖ := by
      intro τ _ hτ1
      have hfilt : s.filter (fun i => τ ≤ ‖z i‖) = s :=
        Finset.filter_true_of_mem fun i _ => by rw [hz_norm]; exact hτ1
      rw [hfilt]
      exact h_at_star
    obtain ⟨ν, hν_lo, hν_hi, hν_ge⟩ :=
      GaloisForLFunctions.HTGeometry.exists_norm_weightedPowerSum_ge s z b_tilde htop M hβ0 hβ_filter
    let t : ℝ := t_star - (ν : ℝ) * δ
    have ht_lo : 0 ≤ t := by
      dsimp only [t, δ]
      have hν_le : (ν : ℝ) ≤ (M : ℝ) + (K : ℝ) := by exact_mod_cast hν_hi
      have hmul : (ν : ℝ) * (t_star / ((M : ℝ) + (K : ℝ))) ≤ t_star := by
        rw [← mul_div_assoc, div_le_iff₀ hMK_pos]
        nlinarith only [hν_le, ht_pos]
      linarith only [hmul]
    have ht_hi : t ≤ T := by
      dsimp only [t, δ]
      have hν_ge_r : (M : ℝ) + 1 ≤ (ν : ℝ) := by exact_mod_cast hν_lo
      have hM_gt : (K : ℝ) * t_star / T < (M : ℝ) := by
        dsimp only [M]
        exact_mod_cast Nat.lt_floor_add_one ((K : ℝ) * t_star / T)
      have hKT : (K : ℝ) * t_star < (M : ℝ) * T := (div_lt_iff₀ hT0).mp hM_gt
      have hdiff_le : t_star - (ν : ℝ) * (t_star / ((M : ℝ) + (K : ℝ))) ≤
          ((K : ℝ) - 1) * t_star / ((M : ℝ) + (K : ℝ)) := by
        have heq : t_star - (ν : ℝ) * (t_star / ((M : ℝ) + (K : ℝ))) =
            ((M : ℝ) + (K : ℝ) - (ν : ℝ)) * t_star / ((M : ℝ) + (K : ℝ)) := by
          field_simp [hMK_pos.ne']
        rw [heq]
        refine div_le_div_of_nonneg_right ?_ hMK_pos.le
        nlinarith only [hν_ge_r, ht_pos]
      refine hdiff_le.trans ?_
      rw [div_le_iff₀ hMK_pos]
      nlinarith only [hKT, ht_pos, hT0, hK1_r]
    have hsum_eq : (∑ i ∈ s, b_tilde i * z i ^ ν) =
        ∑ i ∈ s, c i * Complex.exp (-(Complex.I * ((t * ω i : ℝ) : ℂ))) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only [b_tilde, z, t]
      rw [mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 2
      push_cast; ring
    exact ⟨t, ⟨ht_lo, ht_hi⟩, hsum_eq ▸ hν_ge⟩

end AbstractExpSumExtrapolation

/-! ## Section 3: Symmetric replica eigenmode annihilators and quantitative Choi bounds past `choose(2N, 2)` -/

/-- Collective eigenfrequency of a degree-`r` configuration multiset `m : Sym (Config N) r`. -/
def symCollectiveEnergy {N r : ℕ} (E : Config N → ℝ) (m : Sym (Config N) r) : ℝ :=
  ∑ x : Config N, (m.val.count x : ℝ) * E x

/-- Pairwise separation predicate `∀ m₁ ≠ m₂, Γ ≤ |ω(m₁) - ω(m₂)|` for degree-`r` collective
eigenfrequencies. -/
def HasCollectiveEnergyGap {N : ℕ} (E : Config N → ℝ) (r : ℕ) (Γ : ℝ) : Prop :=
  ∀ m₁ m₂ : Sym (Config N) r, m₁ ≠ m₂ →
    Γ ≤ |symCollectiveEnergy E m₁ - symCollectiveEnergy E m₂|

private theorem symCollectiveEnergy_injective {N r : ℕ} {E : Config N → ℝ}
    (hmax : MaximallyProjectiveEnergy E) :
    Function.Injective (symCollectiveEnergy E : Sym (Config N) r → ℝ) := by
  classical
  let hist (m : Sym (Config N) r) : Config N → ℕ := fun x => m.val.count x
  have hhist_mem (m : Sym (Config N) r) : hist m ∈ (Finset.univ : Finset (Config N)).piAntidiag r := by
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, fun _ _ => Finset.mem_univ _⟩
    dsimp [hist]
    have hsum_cnt : ∀ l : Multiset (Config N), (∑ x : Config N, l.count x) = l.card := fun l => by
      induction l using Multiset.induction_on with
      | empty => simp
      | cons a s ih => simp [Multiset.count_cons, Finset.sum_add_distrib, ih, Multiset.card_cons]
    exact (hsum_cnt ↑m).trans m.2
  have hex_rep (m : Sym (Config N) r) :
      ∃ α : Fin r → Config N, orderedReplicaMultiplicity α = hist m := by
    have hcard_eq := GaloisForLFunctions.HTGeometry.card_fiber_orderedReplicaMultiplicity (hhist_mem m)
    have hpos : 0 < (Finset.univ.filter fun α : Fin r → Config N =>
        orderedReplicaMultiplicity α = hist m).card := by
      rw [hcard_eq]
      exact Nat.multinomial_pos _ _
    obtain ⟨α, hα⟩ := Finset.card_pos.mp hpos
    exact ⟨α, (Finset.mem_filter.mp hα).2⟩
  intro m₁ m₂ heq
  obtain ⟨α₁, hα₁⟩ := hex_rep m₁
  obtain ⟨α₂, hα₂⟩ := hex_rep m₂
  have hcre (m : Sym (Config N) r) (α : Fin r → Config N)
      (hα : orderedReplicaMultiplicity α = hist m) :
      GaloisForLFunctions.HTGeometry.collectiveReplicaEnergy E α = symCollectiveEnergy E m := by
    rw [GaloisForLFunctions.HTGeometry.collectiveReplicaEnergy_eq_sum_multiplicity, hα]
    rfl
  have hcre_eq : GaloisForLFunctions.HTGeometry.collectiveReplicaEnergy E α₁ =
      GaloisForLFunctions.HTGeometry.collectiveReplicaEnergy E α₂ := by
    rw [hcre m₁ α₁ hα₁, hcre m₂ α₂ hα₂, heq]
  have hmult_eq :=
    (GaloisForLFunctions.HTGeometry.collectiveReplicaEnergy_eq_iff_multiplicity_eq hmax α₁ α₂).mp hcre_eq
  rw [hα₁, hα₂] at hmult_eq
  exact Subtype.ext (Multiset.ext.mpr fun x => congrFun hmult_eq x)

/-- Every Hamiltonian with `MaximallyProjectiveEnergy` (`1 ≤ N`, `1 ≤ r`) has a strictly positive
degree-`r` collective frequency gap `Γ > 0`. -/
theorem exists_pos_collectiveEnergyGap_of_maximallyProjective {N r : ℕ}
    (_hN : 1 ≤ N) (_hr : 1 ≤ r) {E : Config N → ℝ} (hmax : MaximallyProjectiveEnergy E) :
    ∃ Γ > 0, HasCollectiveEnergyGap E r Γ := by
  classical
  have hinj := symCollectiveEnergy_injective (r := r) hmax
  let pairs : Finset (Sym (Config N) r × Sym (Config N) r) :=
    Finset.univ.filter fun p => p.1 ≠ p.2
  by_cases hp_ne : pairs.Nonempty
  · let Γ := pairs.inf' hp_ne (fun p => |symCollectiveEnergy E p.1 - symCollectiveEnergy E p.2|)
    have hΓ_pos : 0 < Γ := by
      rw [Finset.lt_inf'_iff]
      intro p hp
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      exact abs_pos.mpr (sub_ne_zero.mpr (hinj.ne hne))
    refine ⟨Γ, hΓ_pos, fun m₁ m₂ hm => ?_⟩
    exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ (m₁, m₂), hm⟩)
  · refine ⟨1, zero_lt_one, fun m₁ m₂ hm => ?_⟩
    exact (hp_ne ⟨(m₁, m₂), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩⟩).elim

private theorem tupleEigenmode_orthonormal {N r : ℕ} (V : UGroup N) :
    Orthonormal ℂ (fun α : Fin r → Config N =>
      (WithLp.toLp 2 (fun p : Fin r → Config N × Config N =>
        ∏ k : Fin r, V.val (p k).1 (α k) * star (V.val (p k).2 (α k))) :
        EuclideanSpace ℂ (Fin r → Config N × Config N))) := by
  rw [orthonormal_iff_ite]
  intro α β
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  simp only [Pi.star_apply, star_prod, ← Finset.prod_mul_distrib]
  rw [(Fintype.prod_sum fun (k : Fin r) (uv : Config N × Config N) =>
    (V.val uv.1 (β k) * star (V.val uv.2 (β k))) *
      star (V.val uv.1 (α k) * star (V.val uv.2 (α k)))).symm]
  have hsingle (x y : Config N) :
      (∑ uv : Config N × Config N,
        (V.val uv.1 y * star (V.val uv.2 y)) * star (V.val uv.1 x * star (V.val uv.2 x))) =
        if x = y then 1 else 0 := by
    rw [Fintype.sum_prod_type]
    have hprod : (∑ u : Config N, ∑ v : Config N,
        (V.val u y * star (V.val v y)) * star (V.val u x * star (V.val v x))) =
        (∑ u : Config N, star (V.val u x) * V.val u y) *
          (∑ v : Config N, V.val v x * star (V.val v y)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by rw [star_mul, star_star]; ring
    rw [hprod]
    have hv1 := congrFun (congrFun V.2.1 x) y
    rw [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.one_apply] at hv1
    simp only [Matrix.conjTranspose_apply] at hv1
    have hv2 := congrFun (congrFun V.2.1 y) x
    rw [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.one_apply] at hv2
    simp only [Matrix.conjTranspose_apply] at hv2
    have hv2' : (∑ v : Config N, V.val v x * star (V.val v y)) = if y = x then 1 else 0 := by
      rw [← hv2]; exact Finset.sum_congr rfl fun v _ => mul_comm _ _
    rw [hv1, hv2']
    by_cases hxy : x = y
    · subst hxy; simp
    · have hyx : y ≠ x := Ne.symm hxy
      simp [hxy, hyx]
  simp_rw [hsingle]
  by_cases hαβ : α = β
  · subst hαβ; simp
  · rw [if_neg hαβ]
    have hex : ∃ k : Fin r, α k ≠ β k := by
      by_contra hall; push Not at hall; exact hαβ (funext hall)
    obtain ⟨k₀, hk₀⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ k₀) (by simp [hk₀])

private def symOfOrderedTuple {N r : ℕ} (α : Fin r → Config N) : Sym (Config N) r :=
  ⟨(Finset.univ : Finset (Fin r)).val.map α, by simp⟩

private theorem count_symOfOrderedTuple_eq {N r : ℕ} (α : Fin r → Config N) (x : Config N) :
    (symOfOrderedTuple α).val.count x = orderedReplicaMultiplicity α x := by
  dsimp only [symOfOrderedTuple, orderedReplicaMultiplicity]
  rw [Multiset.count_map]
  simp [Finset.card_def, Finset.filter_val, eq_comm]

private theorem symFiber_nonempty {N r : ℕ} (m : Sym (Config N) r) :
    (Finset.univ.filter fun α : Fin r → Config N => symOfOrderedTuple α = m).Nonempty := by
  classical
  let hist : Config N → ℕ := fun x => m.val.count x
  have hhist_mem : hist ∈ (Finset.univ : Finset (Config N)).piAntidiag r := by
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, fun _ _ => Finset.mem_univ _⟩
    dsimp [hist]
    have hsum_cnt : ∀ l : Multiset (Config N), (∑ x : Config N, l.count x) = l.card := fun l => by
      induction l using Multiset.induction_on with
      | empty => simp
      | cons a s ih => simp [Multiset.count_cons, Finset.sum_add_distrib, ih, Multiset.card_cons]
    exact (hsum_cnt ↑m).trans m.2
  have hcard_eq := GaloisForLFunctions.HTGeometry.card_fiber_orderedReplicaMultiplicity hhist_mem
  have hpos : 0 < (Finset.univ.filter fun α : Fin r → Config N =>
      orderedReplicaMultiplicity α = hist).card := by
    rw [hcard_eq]; exact Nat.multinomial_pos _ _
  obtain ⟨α, hα⟩ := Finset.card_pos.mp hpos
  have hmult := (Finset.mem_filter.mp hα).2
  refine ⟨α, Finset.mem_filter.mpr ⟨Finset.mem_univ α, ?_⟩⟩
  exact Subtype.ext (Multiset.ext.mpr fun x => (count_symOfOrderedTuple_eq α x).trans (congrFun hmult x))

private theorem finrank_circuitReplicaTargetSpan_le {N s : ℕ} (hN : 1 ≤ N) (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r
      (fun C : {C : TwoQubitCircuit N // C.gateCount ≤ s} =>
        matrixNormalizedChoi (C.val.eval : Register N))) ≤
      (N * N) ^ s * (r * s + s * 16).choose (s * 16) := by
  let q₀ : Fin N := ⟨0, hN⟩
  let pos : {C : TwoQubitCircuit N // C.gateCount ≤ s} →
      TwoQubitCircuit.twoQubitCircuitArchitectureIndex N s :=
    fun C k => if hk : k.val < C.val.gateCount then C.val.reversePosition ⟨k.val, hk⟩ else (q₀, q₀)
  let G : {C : TwoQubitCircuit N // C.gateCount ≤ s} → Fin s → Register N :=
    fun C k => if hk : k.val < C.val.gateCount then C.val.reverseGate ⟨k.val, hk⟩ else 1
  have hG : ∀ C k, TwoQubitCircuit.IsTwoQubitGate (pos C k).1 (pos C k).2 (G C k) := by
    intro C k
    by_cases hk : k.val < C.val.gateCount
    · dsimp only [pos, G]; rw [dif_pos hk, dif_pos hk]
      exact C.val.reverseGate_isTwoQubitGate ⟨k.val, hk⟩
    · dsimp only [pos, G]; rw [dif_neg hk, dif_neg hk]
      exact TwoQubitCircuit.isTwoQubitGate_one q₀ q₀
  have hpad {m : ℕ} (f : Fin m → Register N) :
      ∀ {s' : ℕ}, m ≤ s' →
        (List.ofFn (fun k : Fin s' => if hk : k.val < m then f ⟨k.val, hk⟩ else 1)).prod =
          (List.ofFn f).prod := by
    intro s' hms
    induction s', hms using Nat.le_induction with
    | base =>
        have hfn : (fun k : Fin m => if hk : k.val < m then f ⟨k.val, hk⟩ else 1) = f :=
          funext fun k => dif_pos k.isLt
        rw [hfn]
    | succ d _ ih =>
        have hlast : ¬ (Fin.last d).val < m := by rw [Fin.val_last]; omega
        rw [List.ofFn_succ', List.prod_concat, dif_neg hlast, mul_one]
        exact ih
  have htarget : (fun (C : {C : TwoQubitCircuit N // C.gateCount ≤ s})
      (p : Config N × Config N) =>
        (List.ofFn (G C)).prod p.1 p.2 / Real.sqrt (Fintype.card (Config N))) =
      fun C => matrixNormalizedChoi (C.val.eval : Register N) := by
    funext C p
    have hprod : (List.ofFn (G C)).prod = (C.val.eval : Register N) :=
      (hpad C.val.reverseGate C.property).trans C.val.reverseGate_prod_eq_eval
    rw [hprod]; rfl
  rw [← htarget]
  exact TwoQubitCircuit.finrank_replicaTargetSpan_twoQubitCircuitChoi_complete_totalDegree_le
    pos G hG r

/-- Explicit symmetric-eigenmode Choi annihilator with `2^(-N r)` Parseval energy floor:
whenever `(N * N)^s * (r * s + s * 16).choose (s * 16) < (2^N + r - 1).choose r`, every self-adjoint
`H` admits a unit-norm `s`-gate Choi annihilator `W` (`‖W‖ = 1`) and exact spectral amplitudes
`b : Sym (Config N) r → ℂ` such that:
1. `evalHomogeneousChoiPoly W (z • C.eval) = 0` for all `C.gateCount ≤ s` and `z ∈ ℂ`;
2. `evalHomogeneousChoiPoly W (exp(-i t H)) = ∑ m, b m * exp(-i t * symCollectiveEnergy E m)` for all `t ∈ ℝ`;
3. `2^(-N * r) ≤ ∑ m, ‖b m‖^2`. -/
theorem exists_quantitative_choiAnnihilator_of_carrier_lt_multiset {N s r : ℕ}
    (hN : 1 ≤ N) (_hr : 1 ≤ r)
    (H : selfAdjoint (Register N))
    (hdim : (N * N) ^ s * (r * s + s * 16).choose (s * 16) < (2 ^ N + r - 1).choose r) :
    let E := H.2.isHermitian.eigenvalues
    ∃ (W : EuclideanSpace ℂ (Fin r → Config N × Config N)) (b : Sym (Config N) r → ℂ),
      ‖W‖ = 1 ∧
      (∀ (C : TwoQubitCircuit N), C.gateCount ≤ s → ∀ z : ℂ,
        evalHomogeneousChoiPoly W (z • (C.eval : Register N)) = 0) ∧
      (∀ t : ℝ, evalHomogeneousChoiPoly W (unitaryEvolution H.val t) =
        ∑ m : Sym (Config N) r,
          b m * Complex.exp (-(Complex.I * ((t * symCollectiveEnergy E m : ℝ) : ℂ)))) ∧
      ((2 : ℝ) ^ (N * r))⁻¹ ≤ ∑ m : Sym (Config N) r, ‖b m‖ ^ 2 := by
  classical
  intro E
  let V : UGroup N := hermitianEigenbasisUnitary H.2.isHermitian
  let Dom := Fin r → Config N × Config N
  let Ψ : (Fin r → Config N) → EuclideanSpace ℂ Dom := fun α =>
    WithLp.toLp 2 (fun p : Dom => ∏ k : Fin r, V.val (p k).1 (α k) * star (V.val (p k).2 (α k)))
  have hΨ_orth : Orthonormal ℂ Ψ := tupleEigenmode_orthonormal V
  let F_fib (m : Sym (Config N) r) : Finset (Fin r → Config N) :=
    Finset.univ.filter fun α => symOfOrderedTuple α = m
  have hF_pos (m : Sym (Config N) r) : (0 : ℝ) < (F_fib m).card :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (symFiber_nonempty m))
  let Ξ : Sym (Config N) r → EuclideanSpace ℂ Dom := fun m =>
    (((Real.sqrt (F_fib m).card : ℝ)⁻¹ : ℝ) : ℂ) • ∑ α ∈ F_fib m, Ψ α
  have hΞ_orth : Orthonormal ℂ Ξ := by
    rw [orthonormal_iff_ite]
    intro m₁ m₂
    dsimp only [Ξ]
    rw [inner_smul_left, inner_smul_right, sum_inner, Complex.conj_ofReal]
    have hsum_inner (α : Fin r → Config N) (hα : α ∈ F_fib m₁) :
        inner ℂ (Ψ α) (∑ β ∈ F_fib m₂, Ψ β) = if m₁ = m₂ then 1 else 0 := by
      rw [inner_sum]
      by_cases hm : m₁ = m₂
      · subst hm
        rw [if_pos rfl, Finset.sum_eq_single α]
        · exact (orthonormal_iff_ite.mp hΨ_orth α α).trans (by simp)
        · intro β _ hβα; exact (orthonormal_iff_ite.mp hΨ_orth α β).trans (if_neg hβα.symm)
        · intro hnot; exact (hnot hα).elim
      · rw [if_neg hm]
        refine Finset.sum_eq_zero fun β hβ => ?_
        have hne : α ≠ β := fun heq => hm ((Finset.mem_filter.mp hα).2.symm.trans
          (heq ▸ (Finset.mem_filter.mp hβ).2))
        exact (orthonormal_iff_ite.mp hΨ_orth α β).trans (if_neg hne)
    rw [Finset.sum_congr rfl hsum_inner, Finset.sum_const, nsmul_eq_mul]
    by_cases hm : m₁ = m₂
    · subst hm
      rw [if_pos rfl, mul_one]
      have hpos := hF_pos m₁
      have hr_ne : Real.sqrt (F_fib m₁).card ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
      have h1 : (Real.sqrt (F_fib m₁).card)⁻¹ *
          ((Real.sqrt (F_fib m₁).card)⁻¹ * ((F_fib m₁).card : ℝ)) = 1 := by
        field_simp [hr_ne]
        exact (Real.sq_sqrt hpos.le).symm
      exact_mod_cast h1
    · rw [if_neg hm, mul_zero, mul_zero, mul_zero]
  let E_V : EuclideanSpace ℂ (Sym (Config N) r) →ₗ[ℂ] EuclideanSpace ℂ Dom :=
    { toFun := fun w => ∑ m : Sym (Config N) r, w m • Ξ m
      map_add' := fun u v => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c u => by
        simp only [RingHom.id_apply, PiLp.smul_apply, smul_eq_mul, Finset.smul_sum]
        exact Finset.sum_congr rfl fun m _ => mul_smul c (u m) (Ξ m) }
  have hEV_norm_sq (w : EuclideanSpace ℂ (Sym (Config N) r)) : ‖E_V w‖ ^ 2 = ‖w‖ ^ 2 := by
    have h1 : ((‖E_V w‖ ^ 2 : ℝ) : ℂ) = inner ℂ (E_V w) (E_V w) := by
      rw [Complex.ofReal_pow, inner_self_eq_norm_sq_to_K]; rfl
    have h2 : inner ℂ (E_V w) (E_V w) = ∑ m : Sym (Config N) r, star (w m) * w m := by
      change inner ℂ (∑ m, w m • Ξ m) (∑ m', w m' • Ξ m') = _
      rw [sum_inner]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [inner_sum, Finset.sum_eq_single m]
      · rw [inner_smul_left, inner_smul_right, (orthonormal_iff_ite.mp hΞ_orth m m),
          if_pos rfl, mul_one]
        rfl
      · intro m' _ hm'
        rw [inner_smul_left, inner_smul_right, (orthonormal_iff_ite.mp hΞ_orth m m'),
          if_neg hm'.symm, mul_zero, mul_zero]
      · intro h; exact (h (Finset.mem_univ m)).elim
    have hre := congrArg Complex.re (h1.trans h2)
    rw [Complex.ofReal_re, Complex.re_sum] at hre
    rw [hre, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  let S_circ := replicaTargetSpan r
    (fun C : {C : TwoQubitCircuit N // C.gateCount ≤ s} =>
      matrixNormalizedChoi (C.val.eval : Register N))
  let projMap : EuclideanSpace ℂ (Sym (Config N) r) →ₗ[ℂ] S_circ :=
    (S_circ.orthogonalProjectionOnto.toLinearMap).comp E_V
  have hker_ne : LinearMap.ker projMap ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective projMap := LinearMap.ker_eq_bot.mp hbot
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [finrank_euclideanSpace, Sym.card_sym_eq_choose] at hle
    have hcard_cfg : Fintype.card (Config N) = 2 ^ N := by simp [Config]
    rw [hcard_cfg] at hle
    have hfin_circ := finrank_circuitReplicaTargetSpan_le (s := s) hN r
    dsimp only [S_circ] at hle
    omega
  obtain ⟨w_raw, hw_mem, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  have hw_pos : 0 < ‖w_raw‖ := norm_pos_iff.mpr hw_ne
  let w : EuclideanSpace ℂ (Sym (Config N) r) := ((‖w_raw‖⁻¹ : ℝ) : ℂ) • w_raw
  have hw_norm : ‖w‖ = 1 := by
    dsimp only [w]
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hw_pos.le),
      inv_mul_cancel₀ hw_pos.ne']
  have hw_ker : projMap w = 0 := by
    dsimp only [w]; rw [map_smul, LinearMap.mem_ker.mp hw_mem, smul_zero]
  let W : EuclideanSpace ℂ Dom := E_V w
  have hW_norm : ‖W‖ = 1 := by
    have hsq : ‖W‖ ^ 2 = 1 := by dsimp only [W]; rw [hEV_norm_sq, hw_norm, one_pow]
    nlinarith only [hsq, norm_nonneg W, sq_nonneg (‖W‖ - 1)]
  have hW_orth : ∀ u ∈ S_circ, inner ℂ W u = 0 := by
    intro u hu
    have hmem_orth : W ∈ S_circᗮ := by
      have hsub := Submodule.sub_starProjection_mem_orthogonal (K := S_circ) W
      have hproj0 : S_circ.starProjection W = 0 := by
        change (S_circ.orthogonalProjectionOnto W : EuclideanSpace ℂ Dom) = 0
        have hk : S_circ.orthogonalProjectionOnto W = 0 := hw_ker
        rw [hk]; rfl
      simpa only [hproj0, sub_zero] using hsub
    exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal S_circ W).mp hmem_orth u hu)
  have hvan (C : TwoQubitCircuit N) (hC : C.gateCount ≤ s) (z : ℂ) :
      evalHomogeneousChoiPoly W (z • (C.eval : Register N)) = 0 := by
    unfold evalHomogeneousChoiPoly
    have hsmul : finitePureTensorPowerEuclidean r (matrixNormalizedChoi (z • (C.eval : Register N))) =
        (z ^ r) • finitePureTensorPowerEuclidean r (matrixNormalizedChoi (C.eval : Register N)) := by
      ext p
      simp only [finitePureTensorPowerEuclidean, finitePureTensorPower, matrixNormalizedChoi,
        Matrix.smul_apply, smul_eq_mul, mul_div_assoc, PiLp.smul_apply, WithLp.ofLp_toLp,
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hsmul]
    exact hW_orth _ (S_circ.smul_mem (z ^ r)
      (Submodule.subset_span (Set.mem_range_self (⟨C, hC⟩ : {C : TwoQubitCircuit N // C.gateCount ≤ s}))))
  let c_dim : ℝ := ((Real.sqrt ((2 : ℝ) ^ N))⁻¹) ^ r
  have hc_dim_sq : c_dim ^ 2 = ((2 : ℝ) ^ (N * r))⁻¹ := by
    dsimp only [c_dim]
    rw [← pow_mul, mul_comm r 2, pow_mul, inv_pow, Real.sq_sqrt (by positivity),
      inv_pow, ← pow_mul]
  let b : Sym (Config N) r → ℂ := fun m =>
    ((c_dim * Real.sqrt (F_fib m).card : ℝ) : ℂ) * star (w m)
  have hexpand_orbit (t : ℝ) :
      finitePureTensorPowerEuclidean r (matrixNormalizedChoi (unitaryEvolution H.val t)) =
        ∑ m : Sym (Config N) r,
          (((c_dim * Real.sqrt (F_fib m).card : ℝ) : ℂ) *
            Complex.exp (-(Complex.I * ((t * symCollectiveEnergy E m : ℝ) : ℂ)))) • Ξ m := by
    have hsingle_entry (u v : Config N) :
        matrixNormalizedChoi (unitaryEvolution H.val t) (u, v) =
          ((Real.sqrt ((2 : ℝ) ^ N))⁻¹ : ℂ) *
            ∑ x : Config N, V.val u x * star (V.val v x) *
              Complex.exp (-(Complex.I * ((t * E x : ℝ) : ℂ))) := by
      unfold matrixNormalizedChoi
      have hcard_eq : (Fintype.card (Config N) : ℝ) = (2 : ℝ) ^ N := by simp [Config]
      rw [hcard_eq, div_eq_inv_mul]
      congr 1
      rw [unitaryEvolution_spectral H.2.isHermitian t]
      change ((V.val * Matrix.diagonal (fun a => Complex.exp (-(Complex.I * (t * E a)))) *
        star V.val) u v) = _
      rw [Matrix.mul_apply]
      have hrow (x : Config N) :
          (V.val * Matrix.diagonal (fun a => Complex.exp (-(Complex.I * (t * E a))))) u x *
            (star V.val) x v =
          V.val u x * star (V.val v x) * Complex.exp (-(Complex.I * ((t * E x : ℝ) : ℂ))) := by
        rw [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
        push_cast; ring
      exact Finset.sum_congr rfl fun x _ => hrow x
    have htuple_sum :
        finitePureTensorPowerEuclidean r (matrixNormalizedChoi (unitaryEvolution H.val t)) =
          ∑ α : Fin r → Config N,
            ((c_dim : ℂ) * Complex.exp (-(Complex.I *
              ((t * GaloisForLFunctions.HTGeometry.collectiveReplicaEnergy E α : ℝ) : ℂ)))) • Ψ α := by
      ext p
      simp only [finitePureTensorPowerEuclidean, finitePureTensorPower, WithLp.ofLp_toLp,
        WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Ψ]
      simp_rw [hsingle_entry (p _).1 (p _).2]
      rw [Finset.prod_mul_distrib (f := fun _ : Fin r => ((Real.sqrt ((2 : ℝ) ^ N))⁻¹ : ℂ)),
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [Fintype.prod_sum]
      have hc_cast : (((Real.sqrt ((2 : ℝ) ^ N))⁻¹ : ℂ) ^ r) = (c_dim : ℂ) := by
        dsimp only [c_dim]; push_cast; rfl
      rw [hc_cast, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      have hprod_split :
          (∏ k : Fin r, (V.val (p k).1 (α k) * star (V.val (p k).2 (α k))) *
            Complex.exp (-(Complex.I * ((t * E (α k) : ℝ) : ℂ)))) =
          Complex.exp (-(Complex.I *
            ((t * GaloisForLFunctions.HTGeometry.collectiveReplicaEnergy E α : ℝ) : ℂ))) *
            ∏ k : Fin r, V.val (p k).1 (α k) * star (V.val (p k).2 (α k)) := by
        rw [Finset.prod_mul_distrib (f := fun k => V.val (p k).1 (α k) * star (V.val (p k).2 (α k))),
          mul_comm, ← Complex.exp_sum]
        congr 2
        unfold GaloisForLFunctions.HTGeometry.collectiveReplicaEnergy
        push_cast
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_neg_distrib]
      rw [hprod_split, ← mul_assoc]
    rw [htuple_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (g := symOfOrderedTuple)
      (fun α _ => Finset.mem_univ (symOfOrderedTuple α))]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hcre_m (α : Fin r → Config N) (hα : α ∈ F_fib m) :
        GaloisForLFunctions.HTGeometry.collectiveReplicaEnergy E α = symCollectiveEnergy E m := by
      have hm_eq := (Finset.mem_filter.mp hα).2
      rw [GaloisForLFunctions.HTGeometry.collectiveReplicaEnergy_eq_sum_multiplicity]
      unfold GaloisForLFunctions.HTGeometry.replicaMultiplicityEnergy symCollectiveEnergy
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← count_symOfOrderedTuple_eq α x, hm_eq]
    have hfib_eq : (Finset.univ.filter fun α : Fin r → Config N => symOfOrderedTuple α = m) =
        F_fib m := rfl
    rw [hfib_eq]
    have hconst_coeff : (∑ α ∈ F_fib m,
        ((c_dim : ℂ) * Complex.exp (-(Complex.I *
          ((t * GaloisForLFunctions.HTGeometry.collectiveReplicaEnergy E α : ℝ) : ℂ)))) • Ψ α) =
        ((c_dim : ℂ) * Complex.exp (-(Complex.I * ((t * symCollectiveEnergy E m : ℝ) : ℂ)))) •
          ∑ α ∈ F_fib m, Ψ α := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [hcre_m α hα]
    rw [hconst_coeff]
    dsimp only [Ξ]
    rw [smul_smul]
    congr 1
    have hpos := hF_pos m
    have hsqrt_ne : ((Real.sqrt (F_fib m).card : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
    push_cast
    field_simp [hsqrt_ne]
  have heval_eq (t : ℝ) :
      evalHomogeneousChoiPoly W (unitaryEvolution H.val t) =
        ∑ m : Sym (Config N) r,
          b m * Complex.exp (-(Complex.I * ((t * symCollectiveEnergy E m : ℝ) : ℂ))) := by
    unfold evalHomogeneousChoiPoly
    rw [hexpand_orbit t, inner_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [inner_smul_right]
    have hW_Ξ : inner ℂ W (Ξ m) = star (w m) := by
      dsimp only [W, E_V, LinearMap.coe_mk, AddHom.coe_mk]
      rw [sum_inner, Finset.sum_eq_single m]
      · rw [inner_smul_left, (orthonormal_iff_ite.mp hΞ_orth m m), if_pos rfl, mul_one]
        rfl
      · intro m' _ hm'
        rw [inner_smul_left, (orthonormal_iff_ite.mp hΞ_orth m' m), if_neg hm', mul_zero]
      · intro h; exact (h (Finset.mem_univ m)).elim
    rw [hW_Ξ]
    dsimp only [b]; ring
  have hb_energy : ((2 : ℝ) ^ (N * r))⁻¹ ≤ ∑ m : Sym (Config N) r, ‖b m‖ ^ 2 := by
    have hterm_ge (m : Sym (Config N) r) :
        ((2 : ℝ) ^ (N * r))⁻¹ * ‖w m‖ ^ 2 ≤ ‖b m‖ ^ 2 := by
      dsimp only [b]
      rw [norm_mul, norm_star, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (by dsimp [c_dim]; positivity) (Real.sqrt_nonneg _)),
        mul_pow, mul_pow, Real.sq_sqrt (hF_pos m).le, hc_dim_sq]
      have hcard_ge1 : (1 : ℝ) ≤ (F_fib m).card :=
        Nat.one_le_cast.mpr (Finset.card_pos.mpr (symFiber_nonempty m))
      calc ((2 : ℝ) ^ (N * r))⁻¹ * ‖w m‖ ^ 2
          = (((2 : ℝ) ^ (N * r))⁻¹ * 1) * ‖w m‖ ^ 2 := by ring
        _ ≤ (((2 : ℝ) ^ (N * r))⁻¹ * (F_fib m).card) * ‖w m‖ ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcard_ge1 (by positivity)) (sq_nonneg _)
    calc ((2 : ℝ) ^ (N * r))⁻¹
        = ((2 : ℝ) ^ (N * r))⁻¹ * ‖w‖ ^ 2 := by rw [hw_norm, one_pow, mul_one]
      _ = ∑ m : Sym (Config N) r, ((2 : ℝ) ^ (N * r))⁻¹ * ‖w m‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
      _ ≤ ∑ m : Sym (Config N) r, ‖b m‖ ^ 2 := Finset.sum_le_sum fun m _ => hterm_ge m
  exact ⟨W, b, hW_norm, hvan, heval_eq, hb_energy⟩

private theorem nat_lt_two_pow_sub_three_aux : ∀ L : ℕ, 6 ≤ L → L < 2 ^ (L - 3)
  | L, hL => by
      obtain ⟨d, rfl⟩ : ∃ d, L = d + 6 := ⟨L - 6, by omega⟩
      clear hL
      induction d with
      | zero => decide
      | succ d ih =>
          have heq : d + 1 + 6 - 3 = (d + 6 - 3) + 1 := by omega
          rw [heq, pow_succ]; omega

private theorem three_mul_two_log_add_six_le_aux (N : ℕ) (hN : 64 ≤ N) :
    3 * (2 * Nat.log 2 N + 6) ≤ N := by
  let L := Nat.log 2 N
  have hL6 : 6 ≤ L := Nat.le_log_of_pow_le (by decide) (by norm_num; exact hN)
  have hpow_le : 2 ^ L ≤ N := Nat.pow_log_le_self 2 (by omega)
  suffices hp : 3 * (2 * L + 6) ≤ 2 ^ L from hp.trans hpow_le
  obtain ⟨d, hd⟩ : ∃ d, L = d + 6 := ⟨L - 6, by omega⟩
  rw [hd]; clear hL6 hpow_le hd L hN N
  induction d with
  | zero => decide
  | succ d ih =>
      have heq : d + 1 + 6 = (d + 6) + 1 := by omega
      rw [heq, pow_succ]; omega

private theorem past_matchgate_dim_lt {N : ℕ} (hN : 64 ≤ N) :
    let s := N * (2 * N - 1) + 1
    let r := 192 * N * Nat.log 2 N
    (N * N) ^ s * (r * s + s * 16).choose (s * 16) < (2 ^ N + r - 1).choose r := by
  intro s r
  let L := Nat.log 2 N
  have hL6 : 6 ≤ L := Nat.le_log_of_pow_le (by decide) (by norm_num; exact hN)
  have hr_pos : 1 ≤ r := by dsimp [r, L]; nlinarith only [hN, hL6]
  have hs_le : s ≤ 2 * N ^ 2 := by
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    dsimp [s]
    have h2 : (k + 1) * (2 * (k + 1) - 1) + (k + 1) = 2 * (k + 1) ^ 2 := by
      change (k + 1) * (2 * k + 1) + (k + 1) = 2 * (k + 1) ^ 2; ring
    omega
  have hN_lt : N < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by decide) N
  have hL_pow : L < 2 ^ (L - 3) := nat_lt_two_pow_sub_three_aux L hL6
  have h3_log : 3 * (2 * L + 6) ≤ N := three_mul_two_log_add_six_le_aux N hN
  have hr_plus_lt : r + 16 ≤ 2 ^ (2 * L + 6) := by
    have hr_lt : 192 * N * L < 2 ^ (2 * L + 6) := by
      have heq_exp : 2 * L + 6 = 8 + (L + 1) + (L - 3) := by omega
      rw [heq_exp, pow_add, pow_add, show 2 ^ 8 = 256 by norm_num]
      calc 192 * N * L = 192 * (N * L) := Nat.mul_assoc 192 N L
        _ ≤ 256 * (N * L) := Nat.mul_le_mul_right (N * L) (by norm_num)
        _ < 256 * (2 ^ (L + 1) * 2 ^ (L - 3)) :=
            Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul'' hN_lt hL_pow) (by norm_num)
        _ = 256 * 2 ^ (L + 1) * 2 ^ (L - 3) := (Nat.mul_assoc _ _ _).symm
    have hdvd1 : 64 ∣ r := ⟨3 * N * L, by dsimp [r]; ring⟩
    have hdvd2 : 64 ∣ 2 ^ (2 * L + 6) := by
      rw [pow_add, show 2 ^ 6 = 64 by decide, mul_comm]; exact dvd_mul_right 64 _
    obtain ⟨a, ha⟩ := hdvd1
    obtain ⟨b, hb⟩ := hdvd2
    have hmod_le : r < 2 ^ (2 * L + 6) := hr_lt
    rw [ha, hb] at hmod_le ⊢
    have hab : a + 1 ≤ b := Nat.succ_le_of_lt (Nat.lt_of_mul_lt_mul_left hmod_le)
    nlinarith only [hab]
  have hchoose_ub : (r * s + s * 16).choose (s * 16) ≤ (r + 16) ^ (s * 16) := by
    let m := r * s
    let k := s * 16
    have hs_pos : 1 ≤ s := by dsimp [s]; omega
    have hm_pos : (0 : ℝ) < m := by dsimp [m]; exact_mod_cast Nat.mul_pos hr_pos hs_pos
    have hk_pos : (0 : ℝ) < k := by dsimp [k]; exact_mod_cast Nat.mul_pos hs_pos (by decide)
    let x : ℝ := (k : ℝ) / (m : ℝ)
    have hx_pos : 0 < x := div_pos hk_pos hm_pos
    have hbinom : ((m + k).choose k : ℝ) * x ^ k ≤ (1 + x) ^ (m + k) := by
      rw [add_comm (1 : ℝ) x, add_pow]
      have hmem : k ∈ Finset.range (m + k + 1) := Finset.mem_range.mpr (by omega)
      refine le_trans ?_ (Finset.single_le_sum (fun j _ => by positivity) hmem)
      simp [mul_comm]
    have h1x_pow : (1 + x) ^ (m + k) / x ^ k =
        (1 + (k : ℝ) / (m : ℝ)) ^ m * (1 + (m : ℝ) / (k : ℝ)) ^ k := by
      rw [pow_add, mul_div_assoc]; congr 1; rw [← div_pow]; congr 1
      dsimp [x]; field_simp [hm_pos.ne', hk_pos.ne']; ring
    have hexp_bound : (1 + (k : ℝ) / (m : ℝ)) ^ m ≤ (3 : ℝ) ^ k := by
      calc (1 + (k : ℝ) / (m : ℝ)) ^ m
          ≤ (Real.exp ((k : ℝ) / (m : ℝ))) ^ m :=
            pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ((k : ℝ) / (m : ℝ))]) m
        _ = (Real.exp 1) ^ k := by
            rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_one]; congr 1; field_simp [hm_pos.ne']
        _ ≤ (3 : ℝ) ^ k :=
            pow_le_pow_left₀ (Real.exp_nonneg 1) (Real.exp_one_lt_d9.le.trans (by norm_num)) k
    have hmk_eq : (m : ℝ) / (k : ℝ) = (r : ℝ) / 16 := by
      have hs_ne : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      dsimp [m, k]; push_cast; field_simp [hs_ne]
    have hreal_le : ((m + k).choose k : ℝ) ≤ ((r + 16 : ℕ) : ℝ) ^ k := by
      have hle1 : ((m + k).choose k : ℝ) ≤ (1 + x) ^ (m + k) / x ^ k :=
        (le_div_iff₀ (pow_pos hx_pos k)).mpr hbinom
      rw [h1x_pow, hmk_eq] at hle1
      refine hle1.trans ?_
      calc (1 + (k : ℝ) / (m : ℝ)) ^ m * (1 + (r : ℝ) / 16) ^ k
          ≤ (3 : ℝ) ^ k * (1 + (r : ℝ) / 16) ^ k :=
            mul_le_mul_of_nonneg_right hexp_bound (by positivity)
        _ = (3 * (1 + (r : ℝ) / 16)) ^ k := (mul_pow _ _ k).symm
        _ ≤ ((r + 16 : ℕ) : ℝ) ^ k := pow_le_pow_left₀ (by positivity) (by push_cast; linarith) k
    exact_mod_cast hreal_le
  have hdiv_multiset : (2 ^ N / r) ^ r ≤ (2 ^ N + r - 1).choose r := by
    let D := 2 ^ N
    have hprod_eq : ∀ k : ℕ, (∏ i ∈ Finset.range k, (D + i)) = k.factorial * (D + k - 1).choose k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rcases k with _ | m
          · simp
          · rw [Finset.prod_range_succ, ih]
            have hD1 : 1 ≤ D := Nat.one_le_pow N 2 (by decide)
            have h1 : D + (m + 1) - 1 = D + m := by omega
            have h2 : D + (m + 2) - 1 = D + m + 1 := by omega
            rw [h1, h2, mul_assoc]
            have hch := Nat.add_one_mul_choose_eq (D + m) (m + 1)
            have hmul : (D + m).choose (m + 1) * (D + (m + 1)) =
                (m + 2) * (D + m + 1).choose (m + 2) := by linarith [hch]
            rw [hmul, ← mul_assoc, Nat.factorial_succ (m + 1)]; ring
    have hprod_le : (D / r) ^ r * r.factorial ≤ ∏ i ∈ Finset.range r, (D + i) := by
      have hfac_gen : ∀ q : ℕ, (D / r) ^ q * q.factorial = ∏ i ∈ Finset.range q, ((D / r) * (i + 1)) := by
        intro q
        induction q with
        | zero => simp
        | succ k ih =>
            rw [Finset.prod_range_succ, ← ih, pow_succ, Nat.factorial_succ]
            ring
      rw [hfac_gen r]
      refine Finset.prod_le_prod' fun i hi => ?_
      calc (D / r) * (i + 1)
          ≤ (D / r) * r := Nat.mul_le_mul_left _ (Finset.mem_range.mp hi)
        _ ≤ D := Nat.div_mul_le_self D r
        _ ≤ D + i := Nat.le_add_right D i
    rw [hprod_eq r, mul_comm r.factorial] at hprod_le
    exact Nat.le_of_mul_le_mul_right hprod_le (Nat.factorial_pos r)
  have hdiv_ge : 2 ^ (N - (2 * L + 6)) ≤ 2 ^ N / r := by
    have hr_le : r ≤ 2 ^ (2 * L + 6) := (Nat.le_add_right r 16).trans hr_plus_lt
    refine (Nat.le_div_iff_mul_le hr_pos).mpr ?_
    calc 2 ^ (N - (2 * L + 6)) * r
        ≤ 2 ^ (N - (2 * L + 6)) * 2 ^ (2 * L + 6) := Nat.mul_le_mul_left _ hr_le
      _ = 2 ^ N := by rw [← pow_add]; congr 1; omega
  have hlhs_le : (N * N) ^ s * (r * s + s * 16).choose (s * 16) ≤ 2 ^ ((68 * L + 196) * N ^ 2) := by
    calc (N * N) ^ s * (r * s + s * 16).choose (s * 16)
        ≤ (N * N) ^ s * (r + 16) ^ (s * 16) := Nat.mul_le_mul_left _ hchoose_ub
      _ ≤ (2 ^ (L + 1) * 2 ^ (L + 1)) ^ s * (2 ^ (2 * L + 6)) ^ (s * 16) :=
          Nat.mul_le_mul
            (Nat.pow_le_pow_left (Nat.mul_le_mul hN_lt.le hN_lt.le) s)
            (Nat.pow_le_pow_left hr_plus_lt (s * 16))
      _ = 2 ^ ((34 * L + 98) * s) := by
          rw [← pow_add, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
      _ ≤ 2 ^ ((34 * L + 98) * (2 * N ^ 2)) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hs_le)
      _ = 2 ^ ((68 * L + 196) * N ^ 2) := by congr 1; ring
  have hrhs_ge : 2 ^ (128 * L * N ^ 2) ≤ (2 ^ N + r - 1).choose r := by
    have h23 : 2 * N ≤ 3 * (N - (2 * L + 6)) := by omega
    have hexp_le : 128 * L * N ^ 2 ≤ (N - (2 * L + 6)) * r := by
      dsimp [r]
      calc 128 * L * N ^ 2 = 64 * L * N * (2 * N) := by ring
        _ ≤ 64 * L * N * (3 * (N - (2 * L + 6))) := Nat.mul_le_mul_left _ h23
        _ = (N - (2 * L + 6)) * (192 * N * L) := by ring
    calc 2 ^ (128 * L * N ^ 2)
        ≤ 2 ^ ((N - (2 * L + 6)) * r) := Nat.pow_le_pow_right (by decide) hexp_le
      _ = (2 ^ (N - (2 * L + 6))) ^ r := pow_mul 2 _ r
      _ ≤ (2 ^ N / r) ^ r := Nat.pow_le_pow_left hdiv_ge r
      _ ≤ (2 ^ N + r - 1).choose r := hdiv_multiset
  have hexp_strict : (68 * L + 196) * N ^ 2 < 128 * L * N ^ 2 :=
    Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
  exact lt_of_le_of_lt hlhs_le (lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) hexp_strict) hrhs_ge)

/-- Flagship quantitative Montgomery–Vaughan and Turán–Nazarov lower bound on homogeneous Choi
annihilators past the `choose(2N, 2) = N * (2 * N - 1)` matchgate barrier (`N ≥ 64`):
at `s = N * (2 * N - 1) + 1` and `r = 192 * N * Nat.log 2 N`, every self-adjoint `H` admits a
unit-norm `s`-gate Choi annihilator `W` such that for any collective frequency gap `Γ > 0`
(`HasCollectiveEnergyGap H.2.isHermitian.eigenvalues r Γ`):
1. **Gap-horizon maximum (`T = 104 / Γ`):** `∃ t_★ ∈ [0, 104 / Γ]`,
   `√((2^(N r) * 2)⁻¹) ≤ ‖evalHomogeneousChoiPoly W (exp(-i t_★ H))‖`.
2. **Positive-density occupation (`T ≥ 208 / Γ`):** on every window `[a, a + T]`,
   `(2^(N r) * 2)⁻¹ * T ≤ (volume {t ∈ Icc a (a + T) | √(2^(-N r)) / 2 < ‖P_W(exp(-i t H))‖}).toReal`.
3. **Arbitrary short-horizon Turán extrapolation (`T > 0`):** with `B_r = (2^N + r - 1).choose r`
   and `M = ⌊B_r * (104 / Γ) / T⌋ + 1`, there exists `t ∈ [0, T]` satisfying
   `√((2^(N r) * 2)⁻¹) / (2 * e * B_r * (6 * (B_r + 1) * (M + 2 * B_r + 2))^B_r) ≤ ‖P_W(exp(-i t H))‖`. -/
theorem quantitative_turanNazarov_choiAnnihilator_past_matchgate {N : ℕ} (hN : 64 ≤ N)
    (H : selfAdjoint (Register N)) :
    let s := N * (2 * N - 1) + 1
    let r := 192 * N * Nat.log 2 N
    let B_r := (2 ^ N + r - 1).choose r
    ∃ W : EuclideanSpace ℂ (Fin r → Config N × Config N),
      ‖W‖ = 1 ∧
      (∀ (C : TwoQubitCircuit N), C.gateCount ≤ s → ∀ z : ℂ,
        evalHomogeneousChoiPoly W (z • (C.eval : Register N)) = 0) ∧
      ∀ (Γ : ℝ), 0 < Γ → HasCollectiveEnergyGap H.2.isHermitian.eigenvalues r Γ →
        (∃ t_star ∈ Icc (0 : ℝ) (104 / Γ),
          Real.sqrt (((2 : ℝ) ^ (N * r) * 2)⁻¹) ≤
            ‖evalHomogeneousChoiPoly W (unitaryEvolution H.val t_star)‖) ∧
        (∀ a T : ℝ, 208 / Γ ≤ T →
          (((2 : ℝ) ^ (N * r) * 2)⁻¹) * T ≤
            (volume {t ∈ Icc a (a + T) |
              Real.sqrt (((2 : ℝ) ^ (N * r))⁻¹) / 2 <
                ‖evalHomogeneousChoiPoly W (unitaryEvolution H.val t)‖}).toReal) ∧
        (∀ T : ℝ, 0 < T →
          let M_cap := Nat.floor ((B_r : ℝ) * (104 / Γ) / T) + 1
          ∃ t ∈ Icc (0 : ℝ) T,
            Real.sqrt (((2 : ℝ) ^ (N * r) * 2)⁻¹) /
              (2 * (Real.exp 1 * (B_r : ℝ) *
                (6 * ((B_r : ℝ) + 1) * ((M_cap : ℝ) + 2 * (B_r : ℝ) + 2)) ^ B_r)) ≤
              ‖evalHomogeneousChoiPoly W (unitaryEvolution H.val t)‖) := by
  intro s r B_r
  have hL6 : 6 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by decide) (by norm_num; exact hN)
  have hr_pos : 1 ≤ r := by dsimp [r]; nlinarith only [hN, hL6]
  have hdim : (N * N) ^ s * (r * s + s * 16).choose (s * 16) < B_r := past_matchgate_dim_lt hN
  obtain ⟨W, b, hW_norm, hvan, heval_eq, hb_ge⟩ :=
    exists_quantitative_choiAnnihilator_of_carrier_lt_multiset (by omega) hr_pos H hdim
  refine ⟨W, hW_norm, hvan, ?_⟩
  intro Γ hΓ hgap
  let ω : Sym (Config N) r → ℝ := symCollectiveEnergy H.2.isHermitian.eigenvalues
  have hE_half_ge : (((2 : ℝ) ^ (N * r) * 2)⁻¹) ≤ (∑ m : Sym (Config N) r, ‖b m‖ ^ 2) / 2 := by
    rw [mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hb_ge (by norm_num)
  have hβ_pos : 0 < Real.sqrt (((2 : ℝ) ^ (N * r) * 2)⁻¹) :=
    Real.sqrt_pos.mpr (by positivity)
  obtain ⟨t_star, ht_star_mem, ht_star_ge⟩ :=
    exists_angular_expSum_ge_at_gapHorizon ω b hΓ hgap
  have ht_star_choi : Real.sqrt (((2 : ℝ) ^ (N * r) * 2)⁻¹) ≤
      ‖evalHomogeneousChoiPoly W (unitaryEvolution H.val t_star)‖ := by
    rw [heval_eq t_star]
    exact (Real.sqrt_le_sqrt hE_half_ge).trans ht_star_ge
  refine ⟨⟨t_star, ht_star_mem, ht_star_choi⟩, ?_, ?_⟩
  · intro a T hT208
    have hub_exp (t : ℝ) :
        ‖∑ m : Sym (Config N) r,
          b m * Complex.exp (-(Complex.I * ((t * ω m : ℝ) : ℂ)))‖ ≤ 1 := by
      rw [← heval_eq t]
      exact norm_evalHomogeneousChoiPoly_le_one hW_norm (unitaryEvolution_mem_unitary H.2 t)
    have hvol := volume_angular_expSum_gt_ge ω b (a := a) (T := T) hΓ hgap hT208 hub_exp
    have hT_nn : 0 ≤ T := le_trans (by positivity) hT208
    have hsub_set :
        {t ∈ Icc a (a + T) |
          Real.sqrt (∑ m : Sym (Config N) r, ‖b m‖ ^ 2) / 2 <
            ‖∑ m : Sym (Config N) r, b m * Complex.exp (-(Complex.I * ((t * ω m : ℝ) : ℂ)))‖} ⊆
        {t ∈ Icc a (a + T) |
          Real.sqrt (((2 : ℝ) ^ (N * r))⁻¹) / 2 <
            ‖evalHomogeneousChoiPoly W (unitaryEvolution H.val t)‖} := by
      rintro t ⟨htI, ht_gt⟩
      refine ⟨htI, ?_⟩
      rw [heval_eq t]
      have hsq_mono : Real.sqrt (((2 : ℝ) ^ (N * r))⁻¹) / 2 ≤
          Real.sqrt (∑ m : Sym (Config N) r, ‖b m‖ ^ 2) / 2 :=
        div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hb_ge) two_pos.le
      exact lt_of_le_of_lt hsq_mono ht_gt
    have hfin : volume {t ∈ Icc a (a + T) |
        Real.sqrt (((2 : ℝ) ^ (N * r))⁻¹) / 2 <
          ‖evalHomogeneousChoiPoly W (unitaryEvolution H.val t)‖} < ⊤ := by
      refine lt_of_le_of_lt (measure_mono fun t ht => ht.1) ?_
      rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    calc (((2 : ℝ) ^ (N * r) * 2)⁻¹) * T
        ≤ ((∑ m : Sym (Config N) r, ‖b m‖ ^ 2) / 2) * T :=
          mul_le_mul_of_nonneg_right hE_half_ge hT_nn
      _ ≤ _ := hvol.trans (ENNReal.toReal_mono hfin.ne (measure_mono hsub_set))
  · intro T hT0 M_cap
    have hcard_sym : (Finset.univ : Finset (Sym (Config N) r)).card = B_r := by
      rw [Finset.card_univ, Sym.card_sym_eq_choose]
      have hc : Fintype.card (Config N) = 2 ^ N := by simp [Config]
      rw [hc]
    have hs_ne : (Finset.univ : Finset (Sym (Config N) r)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have hc0 := congrArg Finset.card hemp
      rw [hcard_sym, Finset.card_empty] at hc0
      have hB_pos : 0 < B_r := Nat.lt_of_le_of_lt (Nat.zero_le _) hdim
      omega
    have ht_star_sum : Real.sqrt (((2 : ℝ) ^ (N * r) * 2)⁻¹) ≤
        ‖∑ m ∈ (Finset.univ : Finset (Sym (Config N) r)),
          b m * Complex.exp (-(Complex.I * ((t_star * ω m : ℝ) : ℂ)))‖ := by
      rwa [← heval_eq t_star]
    obtain ⟨t, ht_mem, ht_ge⟩ := exists_angular_expSum_shortHorizon_ge_of_turan
      (Finset.univ : Finset (Sym (Config N) r)) hs_ne ω b
      ht_star_mem.1 hβ_pos hT0 ht_star_sum
    refine ⟨t, ht_mem, ?_⟩
    rw [heval_eq t]
    let M_star := Nat.floor ((B_r : ℝ) * t_star / T) + 1
    have hM_le : M_star ≤ M_cap := by
      dsimp only [M_star, M_cap]
      refine Nat.add_le_add_right (Nat.floor_mono ?_) 1
      refine div_le_div_of_nonneg_right ?_ hT0.le
      exact mul_le_mul_of_nonneg_left ht_star_mem.2 (Nat.cast_nonneg B_r)
    have hM_le_r : (M_star : ℝ) ≤ (M_cap : ℝ) := by exact_mod_cast hM_le
    rw [hcard_sym] at ht_ge
    change Real.sqrt (((2 : ℝ) ^ (N * r) * 2)⁻¹) /
      (2 * (Real.exp 1 * (B_r : ℝ) * (6 * ((B_r : ℝ) + 1) * ((M_star : ℝ) + 2 * (B_r : ℝ) + 2)) ^ B_r)) ≤ _ at ht_ge
    refine le_trans ?_ ht_ge
    refine div_le_div_of_nonneg_left hβ_pos.le ?_ ?_
    · have hb0 : 0 < B_r := Nat.lt_of_le_of_lt (Nat.zero_le _) hdim
      have hB_pos : 0 < (B_r : ℝ) := by exact_mod_cast hb0
      positivity
    · refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) two_pos.le
      refine pow_le_pow_left₀ (by positivity) ?_ B_r
      exact mul_le_mul_of_nonneg_left (by linarith only [hM_le_r]) (by positivity)

#print axioms two_orth_bessel_sq
#print axioms norm_evalHomogeneousChoiPoly_le_one
#print axioms no_unitChoiPoly_gt_r_div_ten
#print axioms norm_evalHomogeneousChoiPoly_le_sqrt_one_sub_chordal
#print axioms tenthPlateauOnset_le_of_choiPoly_gt_chordal
#print axioms exists_unitary_dist_tenth_choiPoly_eq_chordal
#print axioms norm_choiPoly_smallScale_le
#print axioms gaussian_rk3_choiPoly_strang_ceiling
#print axioms angular_expSum_meanSquare_ge
#print axioms exists_angular_expSum_shortHorizon_ge_of_turan
#print axioms exists_quantitative_choiAnnihilator_of_carrier_lt_multiset
#print axioms quantitative_turanNazarov_choiAnnihilator_past_matchgate

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
