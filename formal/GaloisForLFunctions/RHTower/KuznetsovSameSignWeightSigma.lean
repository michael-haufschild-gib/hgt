import GaloisForLFunctions.RHTower.KuznetsovSameSignWeightKernel
import GaloisForLFunctions.RHTower.KuznetsovSameSignParseval

/-!
# The bilinear same-sign Kuznetsov identity against a general weight, `σ > 1`

For two finite families of frequencies, cusp vectors and coefficients put
`F_t = Σ_k b_k (2πμ_k)^{−it} U(·| σ−it, μ_k, v_k)` and `G_t = Σ_l b'_l (2πμ'_l)^{−it} U(·| σ−it, μ'_l, v'_l)`.
The geometric side of `⟨F_t, G_t⟩` is `Σ_{k,l} b̄_k b'_l (2 diag_{kl} + 2 R_{kl}(t))` (`inner_famL2_famL2`) and
Parseval gives

`⟨F_t, G_t⟩ = 4 Σ_j |W(σ+it, ν_j)|² A_j Ā'_j + π⁻¹ ∫ Σ_i |W(σ+it, ir)|² B_i(r) B̄'_i(r) dr`

(`inner_famL2_eq_spectral`).  Both sides are bounded uniformly in `t` (`‖F_t‖ ≤ Σ_k |b_k| ‖v_k‖ ‖A_σ‖₂`), so
for every same-sign weight `(h, G)` the identity may be integrated against `h(t) dt` term by term:

`Σ_{k,l} b̄_k b'_l [2 diag_{kl} ∫h + 2 Σ_{(c,d)} w⁺ c^{−2σ} Ψ_σ^G(4π√(μ_kμ'_l)/|c|)]
   = 4 Σ_j A_j Ā'_j ∫ h |W(σ+it, ν_j)|² dt + π⁻¹ ∫ Σ_i B_i B̄'_i ∫ h |W(σ+it, ir)|² dt dr`

(`kuznetsov_same_sign_weight_sigma`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex Filter Topology
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry KuznetsovGauss

noncomputable section

variable {N : ℕ} {ι : Type*} (W : SameSignWeight)

/-! ## The row sum against the weight -/

theorem integrable_weight_mul_rowTerm {σ : ℝ} (hσ : 1 < σ) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (v w : DeckSpace N) (r : ReducedRow) :
    Integrable (fun t : ℝ => W.h t * (rowWeightPlus μ ν v w r.1 *
      ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))))
    ∧ ∫ t : ℝ, ‖W.h t * (rowWeightPlus μ ν v w r.1 *
      ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)))‖ ≤
      (∫ t : ℝ, ‖W.h t‖) * (‖v‖ * ‖w‖ *
        ((σ - 1) / 2) ^ ((σ - 1) / 2) * (2 * Real.pi * ν)⁻¹ ^ ((σ - 1) / 2) *
        ((∫ y in Ioi (0 : ℝ), y ^ ((σ - 1) / 2 - 1) * Real.exp (-(2 * Real.pi * μ * y))) *
          ∫ ξ : ℝ, (1 + ξ ^ 2) ^ ((σ - 1) / 2 - σ))) * rowSq r ^ (-(σ - (σ - 1) / 2)) := by
  set δ := (σ - 1) / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hδσ : δ < σ - 1 / 2 := by simp only [δ]; linarith
  have hq := rowSq_pos r
  set B := δ ^ δ * (2 * Real.pi * ν)⁻¹ ^ δ *
    ((∫ y in Ioi (0 : ℝ), y ^ (δ - 1) * Real.exp (-(2 * Real.pi * μ * y))) *
      ∫ ξ : ℝ, (1 + ξ ^ 2) ^ (δ - σ))
  have hB : 0 ≤ B := by
    have h1 : 0 ≤ ∫ y in Ioi (0 : ℝ), y ^ (δ - 1) * Real.exp (-(2 * Real.pi * μ * y)) :=
      setIntegral_nonneg measurableSet_Ioi fun y (hy : 0 < y) => by positivity
    have h2 : 0 ≤ ∫ ξ : ℝ, (1 + ξ ^ 2) ^ (δ - σ) := integral_nonneg fun ξ => by positivity
    positivity
  have hpt : ∀ t : ℝ, ‖W.h t * (rowWeightPlus μ ν v w r.1 *
      ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)))‖ ≤
      ‖W.h t‖ * (‖v‖ * ‖w‖ * B * rowSq r ^ (-(σ - δ))) := fun t => by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h1 := norm_rowWeightPlus_le μ ν v w r.1
    have h2 := norm_sameSignKernel_le hμ hν hq hσ hδ hδσ t
    have h3 : rowSq r ^ (-σ) * rowSq r ^ δ = rowSq r ^ (-(σ - δ)) := by
      rw [← Real.rpow_add hq]; congr 1; ring
    calc ‖rowWeightPlus μ ν v w r.1‖ * rowSq r ^ (-σ) *
          ‖sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))‖
        ≤ ‖v‖ * ‖w‖ * rowSq r ^ (-σ) * (B * rowSq r ^ δ) := by gcongr
      _ = _ := by rw [← h3]; ring
  have hint : Integrable (fun t : ℝ => W.h t * (rowWeightPlus μ ν v w r.1 *
      ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)))) :=
    (W.integrable_h.norm.mul_const _).mono'
      (W.continuous_h.aestronglyMeasurable.mul
        (aestronglyMeasurable_const.mul (aestronglyMeasurable_sameSignKernel σ _)))
      (Eventually.of_forall hpt)
  refine ⟨hint, ?_⟩
  calc ∫ t : ℝ, ‖W.h t * (rowWeightPlus μ ν v w r.1 *
        ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)))‖
      ≤ ∫ t : ℝ, ‖W.h t‖ * (‖v‖ * ‖w‖ * B * rowSq r ^ (-(σ - δ))) :=
        integral_mono hint.norm (W.integrable_h.norm.mul_const _) hpt
    _ = _ := by rw [integral_mul_const]; ring

/-- **The row sum integrated against the weight.** -/
theorem integral_weight_mul_rowSum {σ : ℝ} (hσ : 1 < σ) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (v w : DeckSpace N) :
    Integrable (fun t : ℝ => W.h t *
      ∑' r : ReducedRow, rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ) *
        sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))) ∧
    ∫ t : ℝ, W.h t *
        ∑' r : ReducedRow, rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ) *
          sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)) =
      ∑' r : ReducedRow, rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ) *
        weightKernel W σ (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)) := by
  have hrow := fun r => integrable_weight_mul_rowTerm W hσ hμ hν v w r
  have hsum : Summable fun r : ReducedRow => ∫ t : ℝ, ‖W.h t *
      (rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ) *
        sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)))‖ :=
    ((summable_reducedRow_rpow (τ := σ - (σ - 1) / 2) (by linarith)).mul_left _).of_nonneg_of_le
      (fun r => integral_nonneg fun t => norm_nonneg _) fun r => (hrow r).2
  have heq : ∀ t : ℝ, W.h t *
      ∑' r : ReducedRow, rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ) *
        sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r)) =
      ∑' r : ReducedRow, W.h t * (rowWeightPlus μ ν v w r.1 *
        ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))) :=
    fun t => (tsum_mul_left).symm
  simp_rw [heq]
  refine ⟨integrable_tsum_of_summable_integral_norm (fun r => (hrow r).1) hsum, ?_⟩
  rw [← integral_tsum_of_summable_integral_norm (fun r => (hrow r).1) hsum]
  refine tsum_congr fun r => ?_
  have hX : 0 < 4 * Real.pi * Real.sqrt (μ * ν / rowSq r) := by
    have := Real.sqrt_pos.2 (show 0 < μ * ν / rowSq r by have := rowSq_pos r; positivity)
    positivity
  have hpt : ∀ t : ℝ, W.h t * (rowWeightPlus μ ν v w r.1 *
      ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))) =
      (rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ)) * (W.h t *
        sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))) := fun t => by ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_weight_mul_sameSignKernel W hσ hX]

/-- The integrated pairing `2 diag ∫h + 2 Σ_{(c,d)} ⟨v, ρ(M)⁻¹w⟩ e((μd+νa)/c) c^{−2σ} Ψ_σ^G(X_c)`. -/
def weightRow (σ μ ν : ℝ) (v w : DeckSpace N) : ℂ :=
  2 * diagPlus (σ : ℂ) σ μ ν v w * (∫ t : ℝ, W.h t) + 2 * ∑' r : ReducedRow,
    rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ) *
      weightKernel W σ (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))

theorem integrable_and_integral_weight_mul_linePair {σ : ℝ} (hσ : 1 < σ) {μ ν : ℝ} (hμ : 0 < μ)
    (hν : 0 < ν) (v w : DeckSpace N) :
    Integrable (fun t : ℝ => W.h t * linePair σ t μ ν v w) ∧
      ∫ t : ℝ, W.h t * linePair σ t μ ν v w = weightRow W σ μ ν v w := by
  obtain ⟨hint, heq⟩ := integral_weight_mul_rowSum W hσ hμ hν v w
  have hpt : (fun t : ℝ => W.h t * linePair σ t μ ν v w) = fun t =>
      2 * diagPlus (σ : ℂ) σ μ ν v w * W.h t + 2 * (W.h t *
        ∑' r : ReducedRow, rowWeightPlus μ ν v w r.1 * ((rowSq r ^ (-σ) : ℝ) : ℂ) *
          sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ * ν / rowSq r))) := by
    funext t; rw [linePair]; ring
  rw [hpt]
  refine ⟨(W.integrable_h.const_mul _).add (hint.const_mul 2), ?_⟩
  rw [integral_add (W.integrable_h.const_mul _) (hint.const_mul 2), integral_const_mul,
    integral_const_mul, heq, weightRow]

/-! ## The bilinear pairing of two families -/

/-- **`⟨F_t, G_t⟩ = Σ_{k,l} b̄_k b'_l (2 diag_{kl} + 2 R_{kl}(t))`.** -/
theorem inner_famL2_famL2 {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (s s' : Finset ι) {μ μ' : ι → ℝ}
    (hμ : ∀ k, 0 < μ k) (hμ' : ∀ k, 0 < μ' k) {v v' : ι → DeckSpace N}
    (hv : ∀ k, IsCuspEigen (μ k) (v k)) (hv' : ∀ k, IsCuspEigen (μ' k) (v' k)) (b b' : ι → ℂ) :
    ⟪famL2 hσ t s hμ v b, famL2 hσ t s' hμ' v' b'⟫_ℂ =
      ∑ k ∈ s, ∑ l ∈ s', conj (b k) * b' l * linePair σ t (μ k) (μ' l) (v k) (v' l) := by
  rw [famL2, famL2, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_toDeckL2_toDeckL2,
    integral_inner_poincSeries_line hσ t (hμ k) (hμ' l) (hv k) (hv' l), map_mul, linePair]
  have h1 := phase_cancel (hμ k) (hμ' l) t
  have h2 := phase_mul_diagPlus (N := N) (ν := μ' l) (hμ k) σ t (v k) (v' l)
  set P := conj (((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I)))
  set Q := ((2 * Real.pi * μ' l : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I))
  set E := (((μ' l / μ k : ℝ)) : ℂ) ^ ((t : ℂ) * Complex.I)
  set D := diagPlus (σ : ℂ) σ (μ k) (μ' l) (v k) (v' l)
  set R := ∑' r : ReducedRow, rowWeightPlus (μ k) (μ' l) (v k) (v' l) r.1 *
    ((rowSq r ^ (-σ) : ℝ) : ℂ) * sameSignKernel σ t (4 * Real.pi * Real.sqrt (μ k * μ' l / rowSq r))
  calc conj (b k) * P * (b' l * Q * (2 * D + 2 * (E * R)))
      = conj (b k) * b' l * (2 * (P * Q * D) + 2 * ((P * Q * E) * R)) := by ring
    _ = conj (b k) * b' l * (2 * D + 2 * R) := by rw [h1, h2, one_mul]

/-- `‖F_t‖ ≤ Σ_k |b_k| ‖v_k‖ ‖A_σ‖₂`, uniformly in `t`. -/
theorem norm_famL2_le {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (s : Finset ι) {μ : ι → ℝ}
    (hμ : ∀ k, 0 < μ k) (v : ι → DeckSpace N) (b : ι → ℂ) :
    ‖famL2 hσ t s hμ v b‖ ≤ ∑ k ∈ s, ‖b k‖ * (‖v k‖ * poincMajorantNorm σ (μ k)) := by
  rw [famL2]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_smul, norm_mul]
  have hx : (0 : ℝ) < 2 * Real.pi * μ k := by have := hμ k; positivity
  have h1 : ‖((2 * Real.pi * μ k : ℝ) : ℂ) ^ (-((t : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
  rw [h1, mul_one]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h2 := norm_poincL2_le (s := (σ : ℂ) - t * Complex.I) (by simpa using hσ) (hμ k) (v k)
  simpa using h2

/-- The Eisenstein part of `⟨F_t, G_t⟩`: `⟨T̄F_t, T̄G_t⟩ = ∫ Σ_i |W(σ+it, ir)|² B_i B̄'_i dr`. -/
theorem inner_eisTransformL2_famL2 (hN : 2 ≤ N) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (s s' : Finset ι)
    {μ μ' : ι → ℝ} (hμ : ∀ k, 0 < μ k) (hμ' : ∀ k, 0 < μ' k) {v v' : ι → DeckSpace N}
    (hv : ∀ k, IsCuspEigen (μ k) (v k)) (hv' : ∀ k, IsCuspEigen (μ' k) (v' k))
    {n n' : ι → ℤ} (hn : ∀ k, μ k * ((N + 1 : ℕ) : ℝ) = n k)
    (hn' : ∀ k, μ' k * ((N + 1 : ℕ) : ℝ) = n' k) (b b' : ι → ℂ) :
    ⟪eisTransformL2 hN (famL2 hσ t s hμ v b), eisTransformL2 hN (famL2 hσ t s' hμ' v' b')⟫_ℂ =
      ∫ r : ℝ, ∑ i, ((‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 : ℝ) : ℂ) *
        (eisSpecCoeff i σ r s μ v n b * conj (eisSpecCoeff i σ r s' μ' v' n' b')) := by
  set X := eisTransformL2 hN (famL2 hσ t s hμ v b)
  set Y := eisTransformL2 hN (famL2 hσ t s' hμ' v' b')
  have hX := eisTransformL2_mem_symSpace hN (famL2 hσ t s hμ v b)
  have hY := eisTransformL2_mem_symSpace hN (famL2 hσ t s' hμ' v' b')
  have hXi := ae_all_iff.2 fun i => eisTransformL2_famL2_inner hN hσ t s hμ hv hn b i
  have hYi := ae_all_iff.2 fun i => eisTransformL2_famL2_inner hN hσ t s' hμ' hv' hn' b' i
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY, hXi, hYi] with r h1 h2 h3 h4
  rw [inner_eq_sum_cuspBasisVec h1.1 h2.1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e3 : ⟪(X : ℝ → DeckSpace N) r, cuspBasisVec N i⟫_ℂ =
      whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I) * eisSpecCoeff i σ r s μ v n b := by
    have := h3 i
    rw [mul_assoc] at this
    exact mul_left_cancel₀ two_ne_zero this
  have e4 : ⟪(Y : ℝ → DeckSpace N) r, cuspBasisVec N i⟫_ℂ =
      whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I) * eisSpecCoeff i σ r s' μ' v' n' b' := by
    have := h4 i
    rw [mul_assoc] at this
    exact mul_left_cancel₀ two_ne_zero this
  rw [← inner_conj_symm (cuspBasisVec N i), e3, e4, map_mul, Complex.ofReal_pow,
    ← Complex.mul_conj']
  ring

/-- **Parseval for the bilinear pairing on the line.** -/
theorem inner_famL2_eq_spectral (hN : 2 ≤ N) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (s s' : Finset ι)
    {μ μ' : ι → ℝ} (hμ : ∀ k, 0 < μ k) (hμ' : ∀ k, 0 < μ' k) {v v' : ι → DeckSpace N}
    (hv : ∀ k, IsCuspEigen (μ k) (v k)) (hv' : ∀ k, IsCuspEigen (μ' k) (v' k))
    {n n' : ι → ℤ} (hn : ∀ k, μ k * ((N + 1 : ℕ) : ℝ) = n k)
    (hn' : ∀ k, μ' k * ((N + 1 : ℕ) : ℝ) = n' k) (b b' : ι → ℂ) :
    ⟪famL2 hσ t s hμ v b, famL2 hσ t s' hμ' v' b'⟫_ℂ =
      (∑' j : CuspEigenIndex N, 4 * ((‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 : ℝ) : ℂ) *
        (specCoeff j σ s μ v b * conj (specCoeff j σ s' μ' v' b'))) +
      (Real.pi : ℂ)⁻¹ * ∫ r : ℝ, ∑ i,
        ((‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 : ℝ) : ℂ) *
          (eisSpecCoeff i σ r s μ v n b * conj (eisSpecCoeff i σ r s' μ' v' n' b')) := by
  rw [inner_eq_cusp_add_eisTransform hN (famL2_mem_central hσ t s hμ hv b)
    (famL2_mem_central hσ t s' hμ' hv' b') (inner_onesL2_famL2 hσ t s' hμ' hv' b'),
    inner_eisTransformL2_famL2 hN hσ t s s' hμ hμ' hv hv' hn hn' b b']
  congr 1
  refine tsum_congr fun j => ?_
  rw [← inner_conj_symm, inner_cuspEigenBasis_famL2 hσ t s hμ hv b j,
    inner_cuspEigenBasis_famL2 hσ t s' hμ' hv' b' j]
  simp only [map_mul, Complex.conj_conj, map_ofNat]
  rw [show 2 * whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1) * specCoeff j σ s μ v b *
      (2 * conj (whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)) *
        conj (specCoeff j σ s' μ' v' b')) =
      4 * (whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1) *
        conj (whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1))) *
        (specCoeff j σ s μ v b * conj (specCoeff j σ s' μ' v' b')) by ring,
    Complex.mul_conj', Complex.ofReal_pow]


/-! ## Uniform bounds on the two spectral parts -/

/-- `‖⟨F_t, u_j⟩ ⟨u_j, G_t⟩‖ = 4 |W(σ+it, ν_j)|² |A_j Ā'_j|`. -/
theorem norm_inner_cusp_famL2 {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (s s' : Finset ι) {μ μ' : ι → ℝ}
    (hμ : ∀ k, 0 < μ k) (hμ' : ∀ k, 0 < μ' k) {v v' : ι → DeckSpace N}
    (hv : ∀ k, IsCuspEigen (μ k) (v k)) (hv' : ∀ k, IsCuspEigen (μ' k) (v' k)) (b b' : ι → ℂ)
    (j : CuspEigenIndex N) :
    ‖⟪famL2 hσ t s hμ v b, (cuspEigenBasis N j : DeckL2 N)⟫_ℂ *
        ⟪(cuspEigenBasis N j : DeckL2 N), famL2 hσ t s' hμ' v' b'⟫_ℂ‖ =
      4 * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
        ‖specCoeff j σ s μ v b * conj (specCoeff j σ s' μ' v' b')‖ := by
  rw [← inner_conj_symm, inner_cuspEigenBasis_famL2 hσ t s hμ hv b j,
    inner_cuspEigenBasis_famL2 hσ t s' hμ' hv' b' j]
  simp only [norm_mul, Complex.norm_conj, Complex.norm_two]
  ring

/-- The discrete part of the line pairing is summable, uniformly in `t`. -/
theorem summable_and_tsum_cusp_famL2_le {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (s s' : Finset ι)
    {μ μ' : ι → ℝ} (hμ : ∀ k, 0 < μ k) (hμ' : ∀ k, 0 < μ' k) {v v' : ι → DeckSpace N}
    (hv : ∀ k, IsCuspEigen (μ k) (v k)) (hv' : ∀ k, IsCuspEigen (μ' k) (v' k)) (b b' : ι → ℂ) :
    Summable (fun j : CuspEigenIndex N =>
      4 * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
        ‖specCoeff j σ s μ v b * conj (specCoeff j σ s' μ' v' b')‖) ∧
    ∑' j : CuspEigenIndex N, 4 * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
        ‖specCoeff j σ s μ v b * conj (specCoeff j σ s' μ' v' b')‖ ≤
      ((∑ k ∈ s, ‖b k‖ * (‖v k‖ * poincMajorantNorm σ (μ k))) ^ 2 +
        (∑ k ∈ s', ‖b' k‖ * (‖v' k‖ * poincMajorantNorm σ (μ' k))) ^ 2) / 2 := by
  obtain ⟨hs, hle⟩ := summable_and_tsum_norm_inner_cusp_le (famL2 hσ t s hμ v b)
    (famL2 hσ t s' hμ' v' b')
  simp_rw [norm_inner_cusp_famL2 hσ t s s' hμ hμ' hv hv' b b'] at hs hle
  refine ⟨hs, hle.trans ?_⟩
  have h1 := norm_famL2_le hσ t s hμ v b
  have h2 := norm_famL2_le hσ t s' hμ' v' b'
  gcongr

/-- The continuous part of `‖F_t‖²` is at most `π ‖F_t‖²`. -/
theorem integral_eis_famL2_le (hN : 2 ≤ N) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) (s : Finset ι)
    {μ : ι → ℝ} (hμ : ∀ k, 0 < μ k) {v : ι → DeckSpace N} (hv : ∀ k, IsCuspEigen (μ k) (v k))
    {n : ι → ℤ} (hn : ∀ k, μ k * ((N + 1 : ℕ) : ℝ) = n k) (b : ι → ℂ) :
    Integrable (fun r : ℝ => ∑ i, ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 *
      ‖eisSpecCoeff i σ r s μ v n b‖ ^ 2) ∧
    ∫ r : ℝ, ∑ i, ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 *
      ‖eisSpecCoeff i σ r s μ v n b‖ ^ 2 ≤
      Real.pi * (∑ k ∈ s, ‖b k‖ * (‖v k‖ * poincMajorantNorm σ (μ k))) ^ 2 := by
  obtain ⟨hint, hP⟩ := norm_famL2_sq_eq_parseval hN hσ t s hμ hv hn b
  refine ⟨hint, ?_⟩
  have hc : 0 ≤ ∑' j : CuspEigenIndex N, 4 *
      ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 * ‖specCoeff j σ s μ v b‖ ^ 2 :=
    tsum_nonneg fun _ => by positivity
  have hF := norm_famL2_le hσ t s hμ v b
  have hF2 : ‖famL2 hσ t s hμ v b‖ ^ 2 ≤
      (∑ k ∈ s, ‖b k‖ * (‖v k‖ * poincMajorantNorm σ (μ k))) ^ 2 := by gcongr
  have hπ := Real.pi_pos
  set I := ∫ r : ℝ, ∑ i, ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 *
      ‖eisSpecCoeff i σ r s μ v n b‖ ^ 2
  have : Real.pi⁻¹ * I ≤ ‖famL2 hσ t s hμ v b‖ ^ 2 := by linarith
  rw [inv_mul_le_iff₀ hπ] at this
  nlinarith




/-! ## Two interchange lemmas -/

/-- Term-by-term integration of `h · Σ' g_j` under a uniform bound `Σ' ‖g_j(t)‖ ≤ B`. -/
theorem integral_mul_tsum_of_bound {κ : Type*} [Countable κ] {h : ℝ → ℂ} (hh : Integrable h)
    {g : κ → ℝ → ℂ} (hg : ∀ j, AEStronglyMeasurable (g j) volume) {B : ℝ}
    (hs : ∀ t, Summable fun j => ‖g j t‖) (hB : ∀ t, ∑' j, ‖g j t‖ ≤ B) :
    Integrable (fun t => h t * ∑' j, g j t) ∧
      ∫ t, h t * ∑' j, g j t = ∑' j, ∫ t, h t * g j t := by
  have hle : ∀ j t, ‖g j t‖ ≤ B := fun j t =>
    ((hs t).le_tsum j fun _ _ => norm_nonneg _).trans (hB t)
  have hint : ∀ j, Integrable (fun t => h t * g j t) := fun j =>
    (hh.norm.mul_const B).mono' (hh.aestronglyMeasurable.mul (hg j))
      (Eventually.of_forall fun t => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hle j t) (norm_nonneg _))
  have hsum : Summable fun j => ∫ t, ‖h t * g j t‖ := by
    refine summable_of_sum_le (c := ∫ t, ‖h t‖ * B) (fun j => integral_nonneg fun _ => norm_nonneg _)
      fun u => ?_
    rw [← integral_finsetSum _ fun j _ => (hint j).norm]
    refine integral_mono (integrable_finsetSum _ fun j _ => (hint j).norm)
      (hh.norm.mul_const B) fun t => ?_
    simp only [norm_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (((hs t).sum_le_tsum u (fun _ _ => norm_nonneg _)).trans
      (hB t)) (norm_nonneg _)
  have heq : (fun t => h t * ∑' j, g j t) = fun t => ∑' j, h t * g j t :=
    funext fun t => tsum_mul_left.symm
  rw [heq]
  exact ⟨integrable_tsum_of_summable_integral_norm hint hsum,
    (integral_tsum_of_summable_integral_norm hint hsum).symm⟩

/-- Fubini for `h(t) ∫ F(t, r) dr` under a uniform bound `∫ ‖F(t, ·)‖ ≤ B`. -/
theorem integral_mul_integral_of_bound {h : ℝ → ℂ} (hh : Integrable h) {F : ℝ → ℝ → ℂ}
    (hF : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume)) {B : ℝ}
    (hi : ∀ t, Integrable (F t)) (hB : ∀ t, ∫ r, ‖F t r‖ ≤ B) :
    Integrable (fun t => h t * ∫ r, F t r) ∧
      ∫ t, h t * ∫ r, F t r = ∫ r, ∫ t, h t * F t r := by
  set Φ : ℝ × ℝ → ℂ := fun p => h p.1 * F p.1 p.2 with hΦdef
  have hΦm : AEStronglyMeasurable Φ (volume.prod volume) := hh.aestronglyMeasurable.comp_fst.mul hF
  have hΦ : Integrable Φ (volume.prod volume) := by
    rw [integrable_prod_iff hΦm]
    refine ⟨Eventually.of_forall fun t => (hi t).const_mul (h t), ?_⟩
    refine (hh.norm.mul_const B).mono' hΦm.norm.integral_prod_right'
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [hΦdef, norm_mul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hB t) (norm_nonneg _)
  have hrw : (fun t => h t * ∫ r, F t r) = fun t => ∫ r, Φ (t, r) :=
    funext fun t => (integral_const_mul _ _).symm
  rw [hrw]
  exact ⟨hΦ.integral_prod_left, integral_integral_swap hΦ⟩

/-! ## Integration against the weight -/

/-- The spectral weight `∫ h(t) |W(σ+it, ν)|² dt`. -/
def specWeight (σ : ℝ) (ν : ℂ) : ℂ :=
  ∫ t : ℝ, W.h t * ((‖whittMellin ((σ : ℂ) + t * Complex.I) ν‖ ^ 2 : ℝ) : ℂ)

/-- The bilinear geometric form `Σ_{k,l} b̄_k b'_l weightRow_{kl}`. -/
def weightForm (σ : ℝ) (s s' : Finset ι) (μ μ' : ι → ℝ) (v v' : ι → DeckSpace N)
    (b b' : ι → ℂ) : ℂ :=
  ∑ k ∈ s, ∑ l ∈ s', conj (b k) * b' l * weightRow W σ (μ k) (μ' l) (v k) (v' l)

/-- The discrete part integrated against the weight, term by term. -/
theorem integral_weight_mul_cusp_famL2 {σ : ℝ} (hσ : 1 < σ) (s s' : Finset ι)
    {μ μ' : ι → ℝ} (hμ : ∀ k, 0 < μ k) (hμ' : ∀ k, 0 < μ' k) {v v' : ι → DeckSpace N}
    (hv : ∀ k, IsCuspEigen (μ k) (v k)) (hv' : ∀ k, IsCuspEigen (μ' k) (v' k)) (b b' : ι → ℂ) :
    Integrable (fun t : ℝ => W.h t * ∑' j : CuspEigenIndex N,
      4 * ((‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 : ℝ) : ℂ) *
        (specCoeff j σ s μ v b * conj (specCoeff j σ s' μ' v' b'))) ∧
    ∫ t : ℝ, W.h t * ∑' j : CuspEigenIndex N,
      4 * ((‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 : ℝ) : ℂ) *
        (specCoeff j σ s μ v b * conj (specCoeff j σ s' μ' v' b')) =
      ∑' j : CuspEigenIndex N, 4 * (specCoeff j σ s μ v b * conj (specCoeff j σ s' μ' v' b')) *
        specWeight W σ (specParam j.1) := by
  have hcs := fun t => summable_and_tsum_cusp_famL2_le hσ t s s' hμ hμ' hv hv' b b'
  have hnorm : ∀ (j : CuspEigenIndex N) (t : ℝ),
      ‖4 * ((‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 : ℝ) : ℂ) *
        (specCoeff j σ s μ v b * conj (specCoeff j σ s' μ' v' b'))‖ =
      4 * ‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 *
        ‖specCoeff j σ s μ v b * conj (specCoeff j σ s' μ' v' b')‖ := fun j t => by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      RCLike.norm_ofNat]
  obtain ⟨hI, hV⟩ := integral_mul_tsum_of_bound W.integrable_h (g := fun (j : CuspEigenIndex N) t =>
      4 * ((‖whittMellin ((σ : ℂ) + t * Complex.I) (specParam j.1)‖ ^ 2 : ℝ) : ℂ) *
        (specCoeff j σ s μ v b * conj (specCoeff j σ s' μ' v' b')))
    (fun j => (((Complex.measurable_ofReal.comp
      (measurable_specCoeff_line j.1 (cuspEigenBasis_lam_nonneg j) hσ.le)).const_mul
        4).mul_const _).aestronglyMeasurable)
    (fun t => by simp_rw [hnorm]; exact (hcs t).1) (fun t => by simp_rw [hnorm]; exact (hcs t).2)
  refine ⟨hI, hV.trans (tsum_congr fun j => ?_)⟩
  rw [specWeight, ← integral_const_mul]
  congr 1; funext t
  ring

/-- The continuous part integrated against the weight (Fubini in `(t, r)`). -/
theorem integral_weight_mul_eis_famL2 (hN : 2 ≤ N) {σ : ℝ} (hσ : 1 < σ) (s s' : Finset ι)
    {μ μ' : ι → ℝ} (hμ : ∀ k, 0 < μ k) (hμ' : ∀ k, 0 < μ' k) {v v' : ι → DeckSpace N}
    (hv : ∀ k, IsCuspEigen (μ k) (v k)) (hv' : ∀ k, IsCuspEigen (μ' k) (v' k))
    {n n' : ι → ℤ} (hn : ∀ k, μ k * ((N + 1 : ℕ) : ℝ) = n k)
    (hn' : ∀ k, μ' k * ((N + 1 : ℕ) : ℝ) = n' k) (b b' : ι → ℂ) :
    Integrable (fun t : ℝ => W.h t * ∫ r : ℝ, ∑ i,
      ((‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 : ℝ) : ℂ) *
        (eisSpecCoeff i σ r s μ v n b * conj (eisSpecCoeff i σ r s' μ' v' n' b'))) ∧
    ∫ t : ℝ, W.h t * ∫ r : ℝ, ∑ i,
      ((‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 : ℝ) : ℂ) *
        (eisSpecCoeff i σ r s μ v n b * conj (eisSpecCoeff i σ r s' μ' v' n' b')) =
      ∫ r : ℝ, (∑ i, eisSpecCoeff i σ r s μ v n b * conj (eisSpecCoeff i σ r s' μ' v' n' b')) *
        specWeight W σ (r * Complex.I) := by
  have hWc : Continuous fun p : ℝ × ℝ =>
      whittMellin ((σ : ℂ) + p.1 * Complex.I) (p.2 * Complex.I) :=
    continuous_iff_continuousAt.2 fun p =>
      (continuousAt_whittMellin_imag (t := p.1) (r := p.2) (by linarith)).comp
        (f := fun p : ℝ × ℝ => (σ, p.1, p.2)) (by fun_prop : Continuous fun p : ℝ × ℝ =>
          ((σ, p.1, p.2) : ℝ × ℝ × ℝ)).continuousAt
  have hdm : ∀ i, AEStronglyMeasurable (fun r : ℝ => eisSpecCoeff i σ r s μ v n b *
      conj (eisSpecCoeff i σ r s' μ' v' n' b')) volume := fun i =>
    (aestronglyMeasurable_eisSpecCoeff i σ s μ v n b).mul
      (Complex.continuous_conj.comp_aestronglyMeasurable
        (aestronglyMeasurable_eisSpecCoeff i σ s' μ' v' n' b'))
  have hFm : AEStronglyMeasurable (Function.uncurry fun (t r : ℝ) => ∑ i,
      ((‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 : ℝ) : ℂ) *
        (eisSpecCoeff i σ r s μ v n b * conj (eisSpecCoeff i σ r s' μ' v' n' b')))
      (volume.prod volume) :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (Complex.continuous_ofReal.comp (hWc.norm.pow 2)).aestronglyMeasurable.mul (hdm i).comp_snd
  have hdle : ∀ t r : ℝ, ‖∑ i, ((‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 : ℝ) : ℂ) *
        (eisSpecCoeff i σ r s μ v n b * conj (eisSpecCoeff i σ r s' μ' v' n' b'))‖ ≤
      (∑ i, ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 *
          ‖eisSpecCoeff i σ r s μ v n b‖ ^ 2 +
        ∑ i, ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 *
          ‖eisSpecCoeff i σ r s' μ' v' n' b'‖ ^ 2) / 2 := fun t r => by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Complex.norm_conj]
    have hw : 0 ≤ ‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 := by positivity
    nlinarith [mul_nonneg hw (sq_nonneg (‖eisSpecCoeff i σ r s μ v n b‖ -
      ‖eisSpecCoeff i σ r s' μ' v' n' b'‖))]
  have hrow : ∀ t : ℝ, Integrable (fun r : ℝ => ∑ i,
      ((‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 : ℝ) : ℂ) *
        (eisSpecCoeff i σ r s μ v n b * conj (eisSpecCoeff i σ r s' μ' v' n' b'))) ∧
      ∫ r : ℝ, ‖∑ i, ((‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 : ℝ) : ℂ) *
        (eisSpecCoeff i σ r s μ v n b * conj (eisSpecCoeff i σ r s' μ' v' n' b'))‖ ≤
      Real.pi * ((∑ k ∈ s, ‖b k‖ * (‖v k‖ * poincMajorantNorm σ (μ k))) ^ 2 +
        (∑ k ∈ s', ‖b' k‖ * (‖v' k‖ * poincMajorantNorm σ (μ' k))) ^ 2) / 2 := fun t => by
    obtain ⟨hF, hFle⟩ := integral_eis_famL2_le hN hσ t s hμ hv hn b
    obtain ⟨hG, hGle⟩ := integral_eis_famL2_le hN hσ t s' hμ' hv' hn' b'
    have hm : AEStronglyMeasurable (fun r : ℝ => ∑ i,
        ((‖whittMellin ((σ : ℂ) + t * Complex.I) (r * Complex.I)‖ ^ 2 : ℝ) : ℂ) *
          (eisSpecCoeff i σ r s μ v n b * conj (eisSpecCoeff i σ r s' μ' v' n' b'))) volume :=
      Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        ((Complex.continuous_ofReal.comp ((hWc.comp (continuous_const.prodMk
          continuous_id)).norm.pow 2)).aestronglyMeasurable).mul (hdm i)
    have hmaj := (hF.add hG).div_const 2
    have hi := hmaj.mono' hm (Eventually.of_forall fun r => hdle t r)
    refine ⟨hi, (integral_mono hi.norm hmaj (hdle t)).trans ?_⟩
    rw [integral_div]
    simp only [Pi.add_apply]
    rw [integral_add hF hG]
    linarith
  obtain ⟨hI, hV⟩ := integral_mul_integral_of_bound W.integrable_h hFm (fun t => (hrow t).1)
    (fun t => (hrow t).2)
  refine ⟨hI, hV.trans (integral_congr_ae (Eventually.of_forall fun r => ?_))⟩
  simp only [specWeight]
  rw [← integral_const_mul]
  congr 1; funext t
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The same-sign Kuznetsov identity integrated against a weight, `σ > 1`.** -/
theorem kuznetsov_same_sign_weight_sigma (hN : 2 ≤ N) {σ : ℝ} (hσ : 1 < σ) (s s' : Finset ι)
    {μ μ' : ι → ℝ} (hμ : ∀ k, 0 < μ k) (hμ' : ∀ k, 0 < μ' k) {v v' : ι → DeckSpace N}
    (hv : ∀ k, IsCuspEigen (μ k) (v k)) (hv' : ∀ k, IsCuspEigen (μ' k) (v' k))
    {n n' : ι → ℤ} (hn : ∀ k, μ k * ((N + 1 : ℕ) : ℝ) = n k)
    (hn' : ∀ k, μ' k * ((N + 1 : ℕ) : ℝ) = n' k) (b b' : ι → ℂ) :
    weightForm W σ s s' μ μ' v v' b b' =
      (∑' j : CuspEigenIndex N, 4 * (specCoeff j σ s μ v b * conj (specCoeff j σ s' μ' v' b')) *
        specWeight W σ (specParam j.1)) +
      (Real.pi : ℂ)⁻¹ * ∫ r : ℝ, (∑ i, eisSpecCoeff i σ r s μ v n b *
        conj (eisSpecCoeff i σ r s' μ' v' n' b')) * specWeight W σ (r * Complex.I) := by
  have hgeo := fun k l => integrable_and_integral_weight_mul_linePair W hσ (hμ k) (hμ' l) (v k) (v' l)
  have hkl : ∀ k l, Integrable (fun t : ℝ =>
      W.h t * (conj (b k) * b' l * linePair σ t (μ k) (μ' l) (v k) (v' l))) := fun k l =>
    ((hgeo k l).1.const_mul (conj (b k) * b' l)).congr
      (Eventually.of_forall fun t => by simp only; ring)
  -- the geometric side
  have hG : ∫ t : ℝ, W.h t * ⟪famL2 hσ t s hμ v b, famL2 hσ t s' hμ' v' b'⟫_ℂ =
      weightForm W σ s s' μ μ' v v' b b' := by
    simp_rw [inner_famL2_famL2 hσ _ s s' hμ hμ' hv hv' b b', Finset.mul_sum]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hkl k l]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => hkl k l]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show (fun t : ℝ => W.h t * (conj (b k) * b' l * linePair σ t (μ k) (μ' l) (v k) (v' l))) =
      fun t => conj (b k) * b' l * (W.h t * linePair σ t (μ k) (μ' l) (v k) (v' l)) by
        funext t; ring, integral_const_mul, (hgeo k l).2]
  -- the spectral side
  obtain ⟨hci, hcv⟩ := integral_weight_mul_cusp_famL2 W hσ s s' hμ hμ' hv hv' b b'
  obtain ⟨hei, hev⟩ := integral_weight_mul_eis_famL2 W hN hσ s s' hμ hμ' hv hv' hn hn' b b'
  have hS : ∫ t : ℝ, W.h t * ⟪famL2 hσ t s hμ v b, famL2 hσ t s' hμ' v' b'⟫_ℂ =
      (∑' j : CuspEigenIndex N, 4 * (specCoeff j σ s μ v b * conj (specCoeff j σ s' μ' v' b')) *
        specWeight W σ (specParam j.1)) +
      (Real.pi : ℂ)⁻¹ * ∫ r : ℝ, (∑ i, eisSpecCoeff i σ r s μ v n b *
        conj (eisSpecCoeff i σ r s' μ' v' n' b')) * specWeight W σ (r * Complex.I) := by
    simp_rw [inner_famL2_eq_spectral hN hσ _ s s' hμ hμ' hv hv' hn hn' b b', mul_add]
    have hei' := hei.const_mul (Real.pi : ℂ)⁻¹
    rw [integral_add hci (hei'.congr (Eventually.of_forall fun t => by simp only; ring)), hcv]
    congr 1
    rw [← hev, ← integral_const_mul]
    congr 1; funext t; ring
  rw [← hG, hS]

end

end GaloisForLFunctions.RHTower.DeckPointPair
