import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanSoninSmallSupportDomination
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanSoninCutoffTraceFormula
import GaloisForLFunctions.RHTower.XiDeterminantIdealConsequences
import GaloisForLFunctions.RHTower.SoninPrincipalRelativeIdeal
import GaloisForLFunctions.RHTower.SoninLinearPrimeTraceObstruction
import GaloisForLFunctions.RHTower.UnitaryEulerFactorRigidity
import GaloisForLFunctions.RHTower.CCM.CCMLogDiracDeterminantTheorem
import GaloisForLFunctions.RHTower.CCM.CCMFullGroundGaussianGrowthRH
import GaloisForLFunctions.RHTower.CCM.CCMFullGroundPoissonBalanceRH
import GaloisForLFunctions.SquareRootThreshold.ZetaZeroCountRemainderIsUnbounded
import GaloisForLFunctions.«arithmetic-positivity-theory».DenseScaleWindowsAndMultiWindowPositivity
import GaloisForLFunctions.«arithmetic-positivity-theory».SourceSelectionInTheFullWeilCone

/-!
# Spectral Realisation, the Sonin-Trace Cutoff Dichotomy, Operator-Ideal Constraints, and Real-Rooted Ground-State Forcing

This module resolves §7.8 across six unconditional structural results:

1. **Weak-Operator Vanishing of Scaling Unitaries and Vanishing at Infinity of All Trace-Class
   Scaling Traces (`tendsto_inner_ccmLogDilation_atTop`, `tendsto_inner_ccmLogDilation_atBot`,
   `tendsto_ccmScalingTrace_atTop`, `tendsto_ccmScalingTrace_atBot`,
   `tendsto_ccmSoninToeplitzKernel_atTop`, `tendsto_ccmSoninToeplitzKernel_atBot`)**:
   Under `logEvenUnitary : evenSubspace ≃ₗᵢ[ℂ] SoninL2`, the scaling unitary `ccmLogDilation u`
   acts as additive translation by `-u` on `L²(ℝ)`. Truncating `L²(ℝ)` vectors to `[-R, R]` shows
   `lim_{|u| → ∞} ⟪x, ccmLogDilation u y⟫_ℂ = 0` for all `x, y ∈ evenSubspace`. Via Hilbert–Schmidt
   factorisation `T = S ∘ U` and dominated summation over an orthonormal basis, **every**
   trace-class operator `T ∈ 𝓢_1(evenSubspace)` satisfies `lim_{|u| → ∞} ccmScalingTrace T u = 0`;
   in particular, for every cutoff `Λ > 0`, `lim_{|u| → ∞} ccmSoninToeplitzKernel Λ u = 0`.

2. **Universal Zero-Origin Toeplitz Indefiniteness (`forall_toeplitz_re_nonneg_iff_eq_zero`,
   `exists_ccmSoninToeplitzKernel_one_ne_zero`)**:
   A bounded continuous real even kernel `τ : ℝ → ℂ` satisfying `τ(0) = 0` has nonnegative
   Toeplitz form `Re ∫∫ conj(g s) g(t) τ(t - s) ds dt ≥ 0` on all `g ∈ CCMCompactSchwartzLogTest`
   if and only if `τ ≡ 0`. In particular, `ccmSoninToeplitzKernel 1` is non-identically-zero.

3. **Unconditional Large-Support Refutation and Infinite Negative Morse Index of Connes–Consani
   Sonin-Trace Domination at Cutoff `Λ = 1` (`not_ccmSoninTraceDomination_odd_meanZero_twoPacket`,
   `not_ccmSoninTraceDomination_odd_meanZero_poleFree`,
   `exists_linearIndependent_poleFree_negative_soninCone`,
   `exists_poleFree_zeroMoments_not_ccmSoninTraceDomination`)**:
   Connes–Consani (*Selecta Math.* 2021) proved Sonin-trace domination at small logarithmic
   support under boundary vanishing conditions, leaving the global sign of
   `Re Tr(ϑ(g) G_1 ϑ(g)†)` on arbitrary compact supports open. Using `ccmSmallSupportBump` (where
   `Q_{τ_1}(φ) < 0`) and `lim_{|u| → ∞} τ_1(u) = 0`:
   - The real odd mean-zero two-packet `g_L(x) = φ(x - L) - φ(x + L)` satisfies
     `lim_{L → +∞} Re Tr(ϑ(g_L) G_1 ϑ(g_L)†) = 2 Q_{τ_1}(φ) < 0`, refuting cutoff-`1` Sonin-trace
     domination on real odd mean-zero compact Schwartz tests of large support.
   - The real odd four-packet
     `g_L(x) = (φ(x - L) - φ(x + L)) - (1 / (2 cosh(L / 2))) (φ(x - 2L) - φ(x + 2L))`
     simultaneously annihilates the zero-frequency and both Weil polar functionals
     (`∫ g_L = ∫ g_L(x) e^{x/2} dx = ∫ g_L(x) e^{-x/2} dx = 0`) and still satisfies
     `lim_{L → +∞} Re Tr(ϑ(g_L) G_1 ϑ(g_L)†) = 2 Q_{τ_1}(φ) < 0`.
   - Dyadically separated copies `ψ_k = g_{4^k L}` (`k < d`) span a `d`-dimensional subspace of
     mean-zero double-pole-free compact Schwartz tests on which `Re Tr(ϑ(g) G_1 ϑ(g)†) < 0` for
     every nonzero `g`. Hence at cutoff `Λ = 1`, `g ↦ Re Tr(ϑ(g) G_1 ϑ(g)†)` has **infinite
     negative Morse index** and fails on every finite-codimension moment subspace
     `{g : ∀ j < m, ∫ g(x) Φ_j(x) dx = 0}` (`Φ_j` continuous).

4. **Sharp Positive Survivor at Cutoffs `Λ > 1`: Uniform Multi-Packet Domination via the
   Logarithmic Shell Subsidy (`exists_multiPacket_ccmSoninTraceDomination_cutoffAt`,
   `ccmSonin_cutoff_one_vs_gt_one_dichotomy`)**:
   At every cutoff `Λ > 1`, the physical and Fourier shells `P_Λ - P_1` and `P̂_Λ - P̂_1` inject
   the Hilbert–Schmidt trace budget `2 log Λ · ∫ ‖g‖²`. For every packet count `m`, every
   injective node configuration `α : Fin m → ℝ`, and every profile `g_0` supported in `(-ε, ε)`
   with `0 < ε < log Λ / (‖G_Λ‖_1 + 1)`, there exists `L_0 > 0` such that for all `L ≥ L_0` and
   **every** coefficient vector `c : Fin m → ℂ`, the `m`-packet `ccmMultiPacket g_0 α c L`
   satisfies Connes–Consani Sonin-trace domination at cutoff `Λ`.

5. **Operator-Ideal, Determinant, and Scattering Constraints
   (`spectralRealisation_operator_ideal_and_scattering_constraints`)**:
   Every zero-free-gauge self-adjoint Hilbert–Carleman realisation of `Ξ` lies in `𝓢_q` for all
   `q > 1`, fails both `𝓢_1` and weak trace class `𝓢_{1,∞}`, belongs to the log-enhanced
   weak-trace ideal with universal residue `π⁻¹`, and has partial singular-value sums asymptotic
   to `(1 / (2π)) (log(N + 1))²`; unsmoothed finite prime Euler Gram combinations on `evenSubspace`
   and on `ArchimedeanWeightedL2` are noncompact while the algebraic Sonin principal-relative
   ideal lies in `𝓢_1`; raw linear-prime nuclear responses diverge harmonically in `𝓢_1`; `S(T)`
   is unbounded; and unitary Euler-product producers have strictly diagonal unimodular entries.

6. **Finite-Packet `D_log^{(λ,N)}` Dichotomy, Real-Rooted Ground States, and Receiver / Critical
   Family Bridge (`ccmLogDirac_and_realRooted_ground_state_bridge`)**:
   Synthesizes the unconditional finite-packet CCM Theorem 5.10 dichotomy, unconditional existence
   of real-rooted full ground states at every aperture `a > 0`, equivalence of `RiemannHypothesis`
   with `∀ a, 0 ≤ ccmRestrictedWeilGroundEnergy a` and `WeilPositiveFull Λ`, unconditional RH
   forcing from strip-bounded / exponentially localized / Gaussian-growth / Poisson-balanced
   real-rooted full ground states without `Ξ`-identification, and all-five-forms positivity on
   polynomial scale windows and lacunary multi-windows.
-/

open Complex MeasureTheory Set Filter Topology ContinuousLinearMap Polynomial Matrix
open scoped Real BigOperators InnerProductSpace ComplexConjugate ContDiff SchwartzMap
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilOneSided
open _root_.RHTower.CCMRealRootedGround _root_.RHTower.CCMFullRealRootedGround
open _root_.RHTower.CCMFullGroundEigen _root_.RHTower.Littlewood
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold
open HilbertSchmidt

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

local notation "ϑ[" g "]" => ccmIntegratedScaling (ccmSchwartzLogKernel g)
local notation "ϑ†[" g "]" =>
  ContinuousLinearMap.adjoint (ccmIntegratedScaling (ccmSchwartzLogKernel g))

/-! ## Section 1: Weak-Operator Vanishing of Scaling Unitaries and Vanishing at Infinity of All Trace-Class Scaling Traces -/

private theorem soninL2_norm_sq_eq_integral (w : SoninL2) :
    ‖w‖ ^ 2 = ∫ t : ℝ, ‖w t‖ ^ 2 := by
  have h1 : (⟪w, w⟫_ℂ).re = ‖w‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w]
    norm_cast
  rw [← h1, L2.inner_def]
  have h2 : (∫ t : ℝ, ⟪w t, w t⟫_ℂ) =
      ((∫ t : ℝ, ‖w t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [RCLike.inner_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h2, Complex.ofReal_re]

/-- Truncating an `L²(ℝ)` vector to `[-R, R]` converges strongly in `SoninL2` as `R → +∞`. -/
theorem tendsto_norm_sub_indicatorCutoff_Icc_atTop (φ : SoninL2) :
    Tendsto (fun R : ℝ => ‖φ - indicatorCutoff (Icc (-R) R) measurableSet_Icc φ‖)
      atTop (𝓝 0) := by
  have hsq_int : Integrable (fun t : ℝ => ‖φ t‖ ^ 2) volume :=
    (Lp.memLp φ).integrable_norm_pow (by norm_num)
  have hsq_tendsto : Tendsto (fun R : ℝ =>
      ‖φ - indicatorCutoff (Icc (-R) R) measurableSet_Icc φ‖ ^ 2) atTop (𝓝 0) := by
    have heq : ∀ R : ℝ,
        ‖φ - indicatorCutoff (Icc (-R) R) measurableSet_Icc φ‖ ^ 2 =
          ∫ t : ℝ, (Icc (-R) R)ᶜ.indicator (fun s => ‖φ s‖ ^ 2) t := by
      intro R
      rw [soninL2_norm_sq_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub φ (indicatorCutoff (Icc (-R) R) measurableSet_Icc φ),
        indicatorCutoff_ae (Icc (-R) R) measurableSet_Icc φ] with t hsub hcut
      rw [hsub, Pi.sub_apply, hcut]
      by_cases ht : t ∈ Icc (-R) R
      · have hnot : t ∉ (Icc (-R) R)ᶜ := fun hc => hc ht
        rw [indicator_of_mem ht, sub_self, norm_zero, sq, mul_zero, indicator_of_notMem hnot]
      · rw [indicator_of_notMem ht, sub_zero, indicator_of_mem ht]
    simp_rw [heq]
    have h0 : (0 : ℝ) = ∫ _ : ℝ, (0 : ℝ) := (integral_zero ℝ ℝ).symm
    rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖φ t‖ ^ 2)
      (Filter.Eventually.of_forall fun R =>
        hsq_int.aestronglyMeasurable.indicator measurableSet_Icc.compl)
      (Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun t => ?_)
      hsq_int (Filter.Eventually.of_forall fun t => ?_)
    · by_cases ht : t ∈ (Icc (-R) R)ᶜ
      · rw [indicator_of_mem ht, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      · rw [indicator_of_notMem ht, norm_zero]; exact sq_nonneg _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop |t|] with R hR
      have ht : t ∈ Icc (-R) R := by
        rw [mem_Icc]; exact ⟨by linarith [neg_abs_le t], (le_abs_self t).trans hR.le⟩
      have hnot : t ∉ (Icc (-R) R)ᶜ := fun hc => hc ht
      exact (indicator_of_notMem hnot _).symm
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq_tendsto
  rw [Function.comp_def, Real.sqrt_zero] at hsqrt
  exact hsqrt.congr fun R => Real.sqrt_sq (norm_nonneg _)

private theorem inner_indicatorCutoff_additiveTranslationUnitary_eq_zero {R a : ℝ}
    (_hR : 0 < R) (ha : 2 * R < |a|) (φ ψ : SoninL2) :
    ⟪indicatorCutoff (Icc (-R) R) measurableSet_Icc φ,
      MellinL2.additiveTranslationUnitary a
        (indicatorCutoff (Icc (-R) R) measurableSet_Icc ψ)⟫_ℂ = 0 := by
  set P := indicatorCutoff (Icc (-R) R) measurableSet_Icc
  rw [L2.inner_def]
  have hshift := (indicatorCutoff_ae (Icc (-R) R) measurableSet_Icc ψ).comp_tendsto
    (MellinL2.realTranslation_measurePreserving a).quasiMeasurePreserving.tendsto_ae
  refine integral_eq_zero_of_ae ?_
  filter_upwards [indicatorCutoff_ae (Icc (-R) R) measurableSet_Icc φ,
    additiveTranslationUnitary_ae a (P ψ), hshift] with t hφ htr hψ
  change ⟪P φ t, MellinL2.additiveTranslationUnitary a (P ψ) t⟫_ℂ = 0
  rw [hφ, htr]
  have hψ' : P ψ (t + a) = (Icc (-R) R).indicator (fun s => ψ s) (t + a) := by
    simpa [P, Function.comp_apply, MellinL2.realTranslationEquiv] using hψ
  rw [hψ']
  by_cases ht : t ∈ Icc (-R) R
  · have hta : t + a ∉ Icc (-R) R := by
      intro hmem
      have ht_abs : |t| ≤ R := abs_le.mpr ht
      have hta_abs : |t + a| ≤ R := abs_le.mpr hmem
      have habs : |a| ≤ |t + a| + |t| := by
        calc |a| = |(t + a) - t| := by congr 1; ring
          _ ≤ |t + a| + |t| := abs_sub _ _
      linarith
    rw [indicator_of_notMem hta, inner_zero_right]
  · rw [indicator_of_notMem ht, inner_zero_left]

/-- Weak-operator vanishing of additive translations on `SoninL2` along any filter sending
`|a| → +∞`. -/
theorem tendsto_inner_additiveTranslationUnitary_of_abs_atTop {α : Type*} {l : Filter α}
    {a : α → ℝ} (ha : Tendsto (fun x => |a x|) l atTop) (φ ψ : SoninL2) :
    Tendsto (fun x => ⟪φ, MellinL2.additiveTranslationUnitary (a x) ψ⟫_ℂ) l (𝓝 0) := by
  set P : ℝ → SoninL2 →L[ℂ] SoninL2 := fun R => indicatorCutoff (Icc (-R) R) measurableSet_Icc
  have hφ := tendsto_norm_sub_indicatorCutoff_Icc_atTop φ
  have hψ := tendsto_norm_sub_indicatorCutoff_Icc_atTop ψ
  have herr : Tendsto (fun R : ℝ =>
      ‖φ - P R φ‖ * ‖ψ‖ + (‖φ‖ + ‖φ - P R φ‖) * ‖ψ - P R ψ‖) atTop (𝓝 0) := by
    have h1 := hφ.mul_const ‖ψ‖
    have h2 := ((tendsto_const_nhds (x := ‖φ‖)).add hφ).mul hψ
    simpa only [zero_mul, add_zero, mul_zero] using h1.add h2
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR_lt, hR_pos⟩ := (((herr.eventually (Iio_mem_nhds hε)).and
    (eventually_gt_atTop (0 : ℝ)))).exists
  have hR_err : ‖φ - P R φ‖ * ‖ψ‖ + (‖φ‖ + ‖φ - P R φ‖) * ‖ψ - P R ψ‖ < ε := hR_lt
  filter_upwards [ha.eventually (eventually_gt_atTop (2 * R))] with x hx
  rw [dist_zero_right]
  set U := MellinL2.additiveTranslationUnitary (a x)
  have horth : ⟪P R φ, U (P R ψ)⟫_ℂ = 0 :=
    inner_indicatorCutoff_additiveTranslationUnitary_eq_zero hR_pos hx φ ψ
  have hsplit : ⟪φ, U ψ⟫_ℂ =
      ⟪φ - P R φ, U ψ⟫_ℂ + ⟪P R φ, U (ψ - P R ψ)⟫_ℂ + ⟪P R φ, U (P R ψ)⟫_ℂ := by
    have hφ_eq : φ = (φ - P R φ) + P R φ := (sub_add_cancel φ (P R φ)).symm
    have hψ_eq : U ψ = U (ψ - P R ψ) + U (P R ψ) := by
      rw [← map_add, sub_add_cancel]
    conv_lhs => rw [hφ_eq, inner_add_left]
    conv_lhs => rhs; rw [hψ_eq, inner_add_right]
    rw [← add_assoc]
  rw [hsplit, horth, add_zero]
  have hPφ : ‖P R φ‖ ≤ ‖φ‖ + ‖φ - P R φ‖ := by
    calc ‖P R φ‖ = ‖φ - (φ - P R φ)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖φ‖ + ‖φ - P R φ‖ := norm_sub_le φ (φ - P R φ)
  have hterm1 : ‖⟪φ - P R φ, U ψ⟫_ℂ‖ ≤ ‖φ - P R φ‖ * ‖ψ‖ := by
    refine (norm_inner_le_norm _ _).trans_eq ?_
    rw [LinearIsometryEquiv.norm_map]
  have hterm2 : ‖⟪P R φ, U (ψ - P R ψ)⟫_ℂ‖ ≤ (‖φ‖ + ‖φ - P R φ‖) * ‖ψ - P R ψ‖ := by
    calc ‖⟪P R φ, U (ψ - P R ψ)⟫_ℂ‖
        ≤ ‖P R φ‖ * ‖U (ψ - P R ψ)‖ := norm_inner_le_norm _ _
      _ = ‖P R φ‖ * ‖ψ - P R ψ‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ (‖φ‖ + ‖φ - P R φ‖) * ‖ψ - P R ψ‖ :=
          mul_le_mul_of_nonneg_right hPφ (norm_nonneg _)
  exact (norm_add_le _ _).trans_lt (lt_of_le_of_lt (add_le_add hterm1 hterm2) hR_err)

/-- Weak-operator vanishing of `ccmLogDilation u` along any filter sending `|u| → +∞`. -/
theorem tendsto_inner_ccmLogDilation_of_abs_atTop {α : Type*} {l : Filter α}
    {u : α → ℝ} (hu : Tendsto (fun x => |u x|) l atTop) (v w : evenSubspace) :
    Tendsto (fun x => ⟪v, ccmLogDilation (u x) w⟫_ℂ) l (𝓝 0) := by
  have hneg : Tendsto (fun x => |-u x|) l atTop := by simpa only [abs_neg] using hu
  refine (tendsto_inner_additiveTranslationUnitary_of_abs_atTop hneg
    (logEvenUnitary v) (logEvenUnitary w)).congr fun x => ?_
  rw [ccmLogDilation_apply, ← logEvenUnitary_ccmLogDilationOrbit,
    LinearIsometryEquiv.inner_map_map]

theorem tendsto_inner_ccmLogDilation_atTop (v w : evenSubspace) :
    Tendsto (fun u : ℝ => ⟪v, ccmLogDilation u w⟫_ℂ) atTop (𝓝 0) :=
  tendsto_inner_ccmLogDilation_of_abs_atTop tendsto_abs_atTop_atTop v w

theorem tendsto_inner_ccmLogDilation_atBot (v w : evenSubspace) :
    Tendsto (fun u : ℝ => ⟪v, ccmLogDilation u w⟫_ℂ) atBot (𝓝 0) :=
  tendsto_inner_ccmLogDilation_of_abs_atTop tendsto_abs_atBot_atTop v w

/-- **Vanishing at Infinity of All Trace-Class Scaling Traces (`ccmScalingTrace`).**
For every trace-class operator `T` on `evenSubspace`, `Tr(T ϑ_u) → 0` along any filter sending
`|u| → +∞`. -/
theorem tendsto_ccmScalingTrace_of_abs_atTop {α : Type*} {l : Filter α}
    {u : α → ℝ} (hu : Tendsto (fun x => |u x|) l atTop)
    {T : evenSubspace →L[ℂ] evenSubspace} (hT : MemSchattenClass 1 T) :
    Tendsto (fun x => ccmScalingTrace T (u x)) l (𝓝 0) := by
  obtain ⟨S, U, hS, hU, rfl⟩ := hT.one_isTraceClass
  set b := hsBasis ℂ evenSubspace
  have key : ∀ x, ccmScalingTrace (S ∘L U) (u x) =
      ∑' i, ⟪ContinuousLinearMap.adjoint U (b i), ccmLogDilation (u x) (S (b i))⟫_ℂ := by
    intro x
    rw [ccmScalingTrace, opTrace_comp_comp_eq_tsum hS hU]
  simp_rw [key]
  have hlim := tendsto_tsum_of_dominated_convergence
    (f := fun x i => ⟪ContinuousLinearMap.adjoint U (b i), ccmLogDilation (u x) (S (b i))⟫_ℂ)
    (g := fun _ => (0 : ℂ))
    (summable_norm_adjoint_mul_norm hS hU)
    (fun i => tendsto_inner_ccmLogDilation_of_abs_atTop hu
      (ContinuousLinearMap.adjoint U (b i)) (S (b i)))
    (Filter.Eventually.of_forall fun x i => by
      refine (norm_inner_le_norm (𝕜 := ℂ) (ContinuousLinearMap.adjoint U (b i))
        (ccmLogDilation (u x) (S (b i)))).trans_eq ?_
      rw [ccmLogDilation_apply, norm_ccmLogDilationOrbit])
  simpa only [tsum_zero] using hlim

theorem tendsto_ccmScalingTrace_atTop {T : evenSubspace →L[ℂ] evenSubspace}
    (hT : MemSchattenClass 1 T) :
    Tendsto (ccmScalingTrace T) atTop (𝓝 0) :=
  tendsto_ccmScalingTrace_of_abs_atTop tendsto_abs_atTop_atTop hT

theorem tendsto_ccmScalingTrace_atBot {T : evenSubspace →L[ℂ] evenSubspace}
    (hT : MemSchattenClass 1 T) :
    Tendsto (ccmScalingTrace T) atBot (𝓝 0) :=
  tendsto_ccmScalingTrace_of_abs_atTop tendsto_abs_atBot_atTop hT

/-- For every cutoff `Λ > 0`, the Sonin generic Toeplitz kernel `τ_Λ(u) = Tr(G_Λ ϑ_u)` vanishes
as `u → +∞` and as `u → -∞`. -/
theorem tendsto_ccmSoninToeplitzKernel_atTop {Λ : ℝ} (hΛ : 0 < Λ) :
    Tendsto (ccmSoninToeplitzKernel Λ) atTop (𝓝 0) :=
  tendsto_ccmScalingTrace_atTop (memSchattenClass_one_ccmSoninGenericPartAt hΛ)

theorem tendsto_ccmSoninToeplitzKernel_atBot {Λ : ℝ} (hΛ : 0 < Λ) :
    Tendsto (ccmSoninToeplitzKernel Λ) atBot (𝓝 0) :=
  tendsto_ccmScalingTrace_atBot (memSchattenClass_one_ccmSoninGenericPartAt hΛ)

theorem exists_norm_le_of_tendsto_atTop_atBot {τ : ℝ → ℂ}
    (htop : Tendsto τ atTop (𝓝 0)) (hbot : Tendsto τ atBot (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ U : ℝ, 0 < U ∧ ∀ u : ℝ, U ≤ |u| → ‖τ u‖ ≤ δ := by
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.mp (htop.norm.eventually (Iic_mem_nhds (by simpa using hδ)))
  obtain ⟨U₂, hU₂⟩ := eventually_atBot.mp (hbot.norm.eventually (Iic_mem_nhds (by simpa using hδ)))
  refine ⟨max 1 (max U₁ (-U₂)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun u hu => ?_⟩
  have h1 : U₁ ≤ |u| := (le_max_left U₁ (-U₂)).trans ((le_max_right 1 _).trans hu)
  have h2 : -U₂ ≤ |u| := (le_max_right U₁ (-U₂)).trans ((le_max_right 1 _).trans hu)
  rcases le_or_gt 0 u with hu0 | hu0
  · rw [abs_of_nonneg hu0] at h1
    exact hU₁ u h1
  · rw [abs_of_neg hu0] at h2
    exact hU₂ u (by linarith)

/-! ## Section 2: Compact Schwartz Multi-Packets, Universal Zero-Origin Toeplitz Indefiniteness, and Uniform Multi-Packet Decoupling -/

/-- Package any smooth function `f : ℝ → ℂ` vanishing for `|x| ≥ R` into a
`CCMCompactSchwartzLogTest` with explicit radius `max R 2`. -/
def mkCCMCompactSchwartzLogTest (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (R : ℝ)
    (hR : ∀ x : ℝ, R ≤ |x| → f x = 0) : CCMCompactSchwartzLogTest where
  toSchwartzMap :=
    (HasCompactSupport.intro (isCompact_Icc (a := -(max R 2)) (b := max R 2)) fun x hx => by
      refine hR x ((le_max_left R 2).trans ?_)
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · exact (by linarith : max R 2 ≤ -x).trans (neg_le_abs x)
      · exact hx.le.trans (le_abs_self x)).toSchwartzMap hf
  radius := max R 2
  one_lt_radius := lt_of_lt_of_le one_lt_two (le_max_right R 2)
  eq_zero_of_radius_le_abs := fun x hx => hR x ((le_max_left R 2).trans hx)

@[simp]
theorem mkCCMCompactSchwartzLogTest_apply (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (R : ℝ)
    (hR : ∀ x : ℝ, R ≤ |x| → f x = 0) (x : ℝ) :
    mkCCMCompactSchwartzLogTest f hf R hR x = f x := rfl

private theorem integrable_conj {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) : Integrable (fun x => conj (f x)) μ :=
  Complex.conjCLE.toContinuousLinearMap.integrable_comp hf

private theorem integrable_prod_toeplitz {f₁ f₂ τ : ℝ → ℂ} (hf₁ : Integrable f₁)
    (hf₂ : Integrable f₂) (hτ : Continuous τ) {C : ℝ} (hC : ∀ u, ‖τ u‖ ≤ C) :
    Integrable (fun p : ℝ × ℝ => conj (f₁ p.1) * f₂ p.2 * τ (p.2 - p.1))
      (volume.prod volume) :=
  ((integrable_conj hf₁).mul_prod hf₂).mul_bdd
    (hτ.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => hC (p.2 - p.1))

private theorem narrowBump_integral_pos (j : ℕ) : 0 < ∫ x : ℝ, narrowBump j x := by
  refine (narrowBump j).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (narrowBump j).hasCompactSupport (fun x => (narrowBump j).nonneg) (x := 0) ?_
  rw [(narrowBump j).one_of_mem_closedBall (Metric.mem_closedBall_self (narrowBump j).rIn_pos.le)]
  exact one_ne_zero

/-- Explicit resolution index making `1 / (4 (j + 1)) < ccmSoninSmallSupportRadius`. -/
def ccmSmallBumpIndex : ℕ :=
  Nat.floor (1 / (4 * ccmSoninSmallSupportRadius)) + 1

/-- Explicit support half-width `1 / (4 (ccmSmallBumpIndex + 1)) < ccmSoninSmallSupportRadius`. -/
def ccmSmallBumpRadius : ℝ :=
  1 / (4 * ((ccmSmallBumpIndex : ℝ) + 1))

theorem ccmSmallBumpRadius_pos : 0 < ccmSmallBumpRadius := by
  unfold ccmSmallBumpRadius; positivity

theorem ccmSmallBumpRadius_lt : ccmSmallBumpRadius < ccmSoninSmallSupportRadius := by
  have hpos := ccmSoninSmallSupportRadius_pos
  have hgt : 1 / (4 * ccmSoninSmallSupportRadius) < (ccmSmallBumpIndex : ℝ) := by
    unfold ccmSmallBumpIndex
    push_cast
    exact Nat.lt_floor_add_one _
  have h1 : 1 < 4 * ccmSoninSmallSupportRadius * ((ccmSmallBumpIndex : ℝ) + 1) := by
    have := (div_lt_iff₀ (by positivity : 0 < 4 * ccmSoninSmallSupportRadius)).mp hgt
    nlinarith
  unfold ccmSmallBumpRadius
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- Explicit real, even, nonnegative, unit-peak compact Schwartz bump supported strictly inside
`(-ccmSoninSmallSupportRadius, ccmSoninSmallSupportRadius)`. -/
def ccmSmallSupportBump : CCMCompactSchwartzLogTest :=
  mkCCMCompactSchwartzLogTest
    (narrowBumpC ccmSmallBumpIndex)
    (contDiff_narrowBumpC ccmSmallBumpIndex)
    (ccmSmallBumpRadius + ccmSoninSmallSupportRadius)
    (fun x hx => narrowBumpC_eq_zero ccmSmallBumpIndex (by
      have := ccmSoninSmallSupportRadius_pos
      unfold ccmSmallBumpRadius at hx
      linarith))

theorem ccmSmallSupportBump_eq_zero {x : ℝ}
    (hx : (ccmSmallBumpRadius + ccmSoninSmallSupportRadius) / 2 ≤ |x|) :
    ccmSmallSupportBump x = 0 := by
  change narrowBumpC ccmSmallBumpIndex x = 0
  refine narrowBumpC_eq_zero ccmSmallBumpIndex ?_
  have hlt := ccmSmallBumpRadius_lt
  unfold ccmSmallBumpRadius at hlt hx
  linarith

theorem ccmSmallSupportBump_im (x : ℝ) : (ccmSmallSupportBump x).im = 0 := by
  simp [ccmSmallSupportBump, narrowBumpC]

theorem ccmSmallSupportBump_nonneg (x : ℝ) : 0 ≤ (ccmSmallSupportBump x).re := by
  simpa [ccmSmallSupportBump, narrowBumpC] using (narrowBump ccmSmallBumpIndex).nonneg' x

theorem ccmSmallSupportBump_even (x : ℝ) :
    ccmSmallSupportBump (-x) = ccmSmallSupportBump x := by
  simpa [ccmSmallSupportBump] using narrowBumpC_neg ccmSmallBumpIndex x

theorem ccmSmallSupportBump_zero : ccmSmallSupportBump 0 = 1 := by
  change ((narrowBump ccmSmallBumpIndex 0 : ℝ) : ℂ) = 1
  rw [(narrowBump ccmSmallBumpIndex).one_of_mem_closedBall
    (Metric.mem_closedBall_self (narrowBump ccmSmallBumpIndex).rIn_pos.le)]
  norm_cast

/-- The cutoff-`1` generic Sonin Toeplitz form is strictly negative on `ccmSmallSupportBump`. -/
theorem re_toeplitz_ccmSmallSupportBump_neg :
    (∫ s, ∫ t, conj (ccmSmallSupportBump s) * ccmSmallSupportBump t *
      ccmSoninToeplitzKernel 1 (t - s)).re < 0 := by
  set ε := (ccmSmallBumpRadius + ccmSoninSmallSupportRadius) / 2
  have hlt := ccmSmallBumpRadius_lt
  have hpos := ccmSmallBumpRadius_pos
  have hε_pos : 0 < ε := by unfold ε; linarith
  have hε_le : ε ≤ ccmSoninSmallSupportRadius := by unfold ε; linarith
  have hfail := not_ccmSoninTraceDomination_of_nonneg ccmSmallSupportBump hε_pos hε_le
    (fun x hx => ccmSmallSupportBump_eq_zero hx) ccmSmallSupportBump_im
    ccmSmallSupportBump_nonneg (x₀ := 0) (by rw [ccmSmallSupportBump_zero]; exact one_ne_zero)
  have hnot : ¬ (opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel
      (ccmSoninGramTest ccmSmallSupportBump).toSchwartzMap) *
      evenCentralSoninProjection 1)).re ≤
      (-ccmArchimedeanWeilDistribution (ccmSoninGramTest ccmSmallSupportBump)).re :=
    not_le.mpr hfail
  rwa [ccmSoninTraceDomination_iff_toeplitz, not_le] at hnot

/-- Consequently `ccmSoninToeplitzKernel 1` is not identically zero. -/
theorem exists_ccmSoninToeplitzKernel_one_ne_zero :
    ∃ u : ℝ, ccmSoninToeplitzKernel 1 u ≠ 0 := by
  by_contra hall
  push Not at hall
  have hneg := re_toeplitz_ccmSmallSupportBump_neg
  simp only [hall, mul_zero, integral_zero, Complex.zero_re, lt_irrefl] at hneg

/-- **Universal Zero-Origin Toeplitz Indefiniteness.**
Let `τ : ℝ → ℂ` be continuous, bounded, real-valued (`im = 0`), even (`τ(-u) = τ(u)`), and satisfy
`τ(0) = 0`. Then the Toeplitz quadratic form `Re ∫∫ conj(g s) g(t) τ(t - s) ds dt` is nonnegative
on all `g ∈ CCMCompactSchwartzLogTest` if and only if `τ` vanishes identically on `ℝ`. -/
theorem forall_toeplitz_re_nonneg_iff_eq_zero {τ : ℝ → ℂ} (hτ : Continuous τ)
    {C : ℝ} (hC : ∀ u, ‖τ u‖ ≤ C) (hreal : ∀ u, (τ u).im = 0)
    (heven : ∀ u, τ (-u) = τ u) (hzero : τ 0 = 0) :
    (∀ g : CCMCompactSchwartzLogTest,
      0 ≤ (∫ s, ∫ t, conj (g s) * g t * τ (t - s)).re) ↔ (∀ u : ℝ, τ u = 0) := by
  refine ⟨fun hpos u₀ => ?_, fun hall g => by simp [hall]⟩
  suffices hre0 : (τ u₀).re = 0 from Complex.ext hre0 (hreal u₀)
  set κ : ℝ → ℝ := fun u => (τ u).re
  have hκ_cont : Continuous κ := Complex.continuous_re.comp hτ
  have hκ_eq : ∀ u, τ u = (κ u : ℂ) := fun u => Complex.ext rfl (by simp [hreal u])
  have hκ_even : ∀ u, κ (-u) = κ u := fun u => by simp only [κ, heven u]
  have hκ_zero : κ 0 = 0 := by simp [κ, hzero]
  have hκ_bound : ∀ u, |κ u| ≤ max C 0 := fun u =>
    ((Complex.abs_re_le_norm (τ u)).trans (hC u)).trans (le_max_left C 0)
  by_contra hne
  have habs_pos : 0 < |κ u₀| := abs_pos.mpr hne
  set ε := |κ u₀| / 2
  have hε : 0 < ε := half_pos habs_pos
  obtain ⟨δ₁, hδ₁, hb0⟩ := Metric.continuousAt_iff.mp hκ_cont.continuousAt (ε / 4) (by positivity)
  obtain ⟨δ₂, hδ₂, hbu⟩ := Metric.continuousAt_iff.mp hκ_cont.continuousAt (ε / 2) (by positivity)
  set δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  obtain ⟨j, hj⟩ := exists_nat_gt (1 / (2 * δ))
  set r := 1 / (4 * ((j : ℝ) + 1))
  have hr_pos : 0 < r := by unfold r; positivity
  have h2r_lt : 2 * r < δ := by
    have h1 : 1 / (2 * δ) < (j : ℝ) + 1 := by linarith
    have h2 := (div_lt_iff₀ (by positivity : 0 < 2 * δ)).mp h1
    have h3 : 2 * r = 1 / (2 * ((j : ℝ) + 1)) := by unfold r; field_simp; ring
    rw [h3, div_lt_iff₀ (by positivity)]
    nlinarith
  set h : ℝ → ℝ := fun x => narrowBump j x
  have hh_cont : Continuous h := (narrowBump j).continuous
  have hh_int : Integrable h volume := hh_cont.integrable_of_hasCompactSupport
    (narrowBump j).hasCompactSupport
  have hh_nn : ∀ x, 0 ≤ h x := fun x => (narrowBump j).nonneg' x
  have hh_zero : ∀ x, r < |x| → h x = 0 := fun x hx => by
    have hd : (narrowBump j).rOut ≤ dist x 0 := by rw [Real.dist_eq, sub_zero]; exact hx.le
    exact (narrowBump j).zero_of_le_dist hd
  set M := ∫ x, h x
  have hM_pos : 0 < M := narrowBump_integral_pos j
  -- Evaluate the two-bump test `h(x) + σ h(x - u₀)` for `σ = ±1`:
  have hpair_ge : ∀ σ : ℝ, σ ^ 2 = 1 →
      0 ≤ 2 * (∫ p : ℝ × ℝ, h p.1 * h p.2 * κ (p.2 - p.1) ∂(volume.prod volume)) +
        2 * σ * (∫ p : ℝ × ℝ, h p.1 * h p.2 * κ (u₀ + p.2 - p.1) ∂(volume.prod volume)) := by
    intro σ hσ2
    let fσ : ℝ → ℂ := fun x => (h x : ℂ) + (σ : ℂ) * (h (x - u₀) : ℂ)
    have hfσ_diff : ContDiff ℝ (⊤ : ℕ∞) fσ :=
      (contDiff_narrowBumpC j).add
        (contDiff_const.mul ((contDiff_narrowBumpC j).comp (contDiff_id.sub contDiff_const)))
    have hfσ_supp : ∀ x : ℝ, (r + |u₀| + 1) ≤ |x| → fσ x = 0 := by
      intro x hx
      have hx1 : r < |x| := by linarith [abs_nonneg u₀]
      have hx2 : r < |x - u₀| := by
        have := abs_sub_abs_le_abs_sub x u₀
        linarith
      simp [fσ, hh_zero x hx1, hh_zero (x - u₀) hx2]
    let gσ := mkCCMCompactSchwartzLogTest fσ hfσ_diff (r + |u₀| + 1) hfσ_supp
    have hnonneg := hpos gσ
    have hgσ_int : Integrable (fun x => gσ x) volume := gσ.toSchwartzMap.integrable
    have hprod_g := integrable_prod_toeplitz hgσ_int hgσ_int hτ hC
    rw [← integral_prod _ hprod_g] at hnonneg
    change 0 ≤ RCLike.re (∫ p : ℝ × ℝ, conj (gσ p.1) * gσ p.2 * τ (p.2 - p.1)
      ∂(volume.prod volume)) at hnonneg
    rw [← integral_re hprod_g] at hnonneg
    have hprod_hh : ∀ a : ℝ, Integrable (fun p : ℝ × ℝ => h p.1 * h p.2 * κ (a + p.2 - p.1))
        (volume.prod volume) := fun a =>
      (hh_int.mul_prod hh_int).mul_bdd
        (hκ_cont.comp ((continuous_const.add continuous_snd).sub continuous_fst)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs]; exact hκ_bound _)
    have hp00 : Integrable (fun p : ℝ × ℝ => h p.1 * h p.2 * κ (p.2 - p.1))
        (volume.prod volume) := by simpa only [zero_add] using hprod_hh 0
    have hp11 : Integrable (fun p : ℝ × ℝ => h (p.1 - u₀) * h (p.2 - u₀) * κ (p.2 - p.1))
        (volume.prod volume) :=
      ((hh_int.comp_sub_right u₀).mul_prod (hh_int.comp_sub_right u₀)).mul_bdd
        (hκ_cont.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hκ_bound _)
    have hp01 : Integrable (fun p : ℝ × ℝ => σ * (h p.1 * h (p.2 - u₀) * κ (p.2 - p.1)))
        (volume.prod volume) :=
      (((hh_int.mul_prod (hh_int.comp_sub_right u₀)).mul_bdd
        (hκ_cont.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hκ_bound _)).const_mul σ)
    have hp10 : Integrable (fun p : ℝ × ℝ => σ * (h (p.1 - u₀) * h p.2 * κ (p.2 - p.1)))
        (volume.prod volume) :=
      ((((hh_int.comp_sub_right u₀).mul_prod hh_int).mul_bdd
        (hκ_cont.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hκ_bound _)).const_mul σ)
    have hre_pt : ∀ p : ℝ × ℝ,
        RCLike.re (conj (gσ p.1) * gσ p.2 * τ (p.2 - p.1)) =
          (h p.1 * h p.2 * κ (p.2 - p.1) + σ ^ 2 * (h (p.1 - u₀) * h (p.2 - u₀) * κ (p.2 - p.1))) +
            (σ * (h p.1 * h (p.2 - u₀) * κ (p.2 - p.1)) +
              σ * (h (p.1 - u₀) * h p.2 * κ (p.2 - p.1))) := by
      intro p
      rw [hκ_eq (p.2 - p.1)]
      change ((conj (fσ p.1) * fσ p.2 * (κ (p.2 - p.1) : ℂ))).re = _
      simp only [fσ, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_add,
        Complex.ofReal_re]
      ring
    simp_rw [hre_pt, hσ2, one_mul] at hnonneg
    have hsum_int : (∫ p : ℝ × ℝ,
        (h p.1 * h p.2 * κ (p.2 - p.1) + h (p.1 - u₀) * h (p.2 - u₀) * κ (p.2 - p.1)) +
          (σ * (h p.1 * h (p.2 - u₀) * κ (p.2 - p.1)) +
            σ * (h (p.1 - u₀) * h p.2 * κ (p.2 - p.1))) ∂(volume.prod volume)) =
        ((∫ p, h p.1 * h p.2 * κ (p.2 - p.1) ∂(volume.prod volume)) +
          ∫ p, h (p.1 - u₀) * h (p.2 - u₀) * κ (p.2 - p.1) ∂(volume.prod volume)) +
        (σ * (∫ p, h p.1 * h (p.2 - u₀) * κ (p.2 - p.1) ∂(volume.prod volume)) +
          σ * (∫ p, h (p.1 - u₀) * h p.2 * κ (p.2 - p.1) ∂(volume.prod volume))) := by
      have hp_left : Integrable (fun p : ℝ × ℝ =>
          h p.1 * h p.2 * κ (p.2 - p.1) + h (p.1 - u₀) * h (p.2 - u₀) * κ (p.2 - p.1))
          (volume.prod volume) := hp00.add hp11
      have hp_right : Integrable (fun p : ℝ × ℝ =>
          σ * (h p.1 * h (p.2 - u₀) * κ (p.2 - p.1)) +
            σ * (h (p.1 - u₀) * h p.2 * κ (p.2 - p.1)))
          (volume.prod volume) := hp01.add hp10
      rw [integral_add hp_left hp_right, integral_add hp00 hp11, integral_add hp01 hp10,
        integral_const_mul, integral_const_mul]
    rw [hsum_int] at hnonneg
    -- Shift `(p.1 - u₀, p.2 - u₀)` and the two cross integrals back to `(p.1, p.2)`:
    have hi11 : (∫ p : ℝ × ℝ, h (p.1 - u₀) * h (p.2 - u₀) * κ (p.2 - p.1) ∂(volume.prod volume)) =
        ∫ p : ℝ × ℝ, h p.1 * h p.2 * κ (p.2 - p.1) ∂(volume.prod volume) := by
      rw [integral_prod _ hp11, integral_prod _ hp00]
      simp_rw [← integral_add_right_eq_self
        (fun s => ∫ t, h (s - u₀) * h (t - u₀) * κ (t - s)) u₀]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      dsimp only
      rw [← integral_add_right_eq_self
        (fun t => h ((s + u₀) - u₀) * h (t - u₀) * κ (t - (s + u₀))) u₀]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [add_sub_cancel_right]
      congr 2
      ring
    have hi01 : (∫ p : ℝ × ℝ, h p.1 * h (p.2 - u₀) * κ (p.2 - p.1) ∂(volume.prod volume)) =
        ∫ p : ℝ × ℝ, h p.1 * h p.2 * κ (u₀ + p.2 - p.1) ∂(volume.prod volume) := by
      have hp01' : Integrable (fun p : ℝ × ℝ => h p.1 * h (p.2 - u₀) * κ (p.2 - p.1))
          (volume.prod volume) :=
        (hh_int.mul_prod (hh_int.comp_sub_right u₀)).mul_bdd
          (hκ_cont.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hκ_bound _)
      rw [integral_prod _ hp01', integral_prod _ (hprod_hh u₀)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      dsimp only
      rw [← integral_add_right_eq_self (fun t => h s * h (t - u₀) * κ (t - s)) u₀]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [add_sub_cancel_right]
      congr 2
      ring
    have hi10 : (∫ p : ℝ × ℝ, h (p.1 - u₀) * h p.2 * κ (p.2 - p.1) ∂(volume.prod volume)) =
        ∫ p : ℝ × ℝ, h p.1 * h p.2 * κ (u₀ + p.2 - p.1) ∂(volume.prod volume) := by
      have hp10' : Integrable (fun p : ℝ × ℝ => h (p.1 - u₀) * h p.2 * κ (p.2 - p.1))
          (volume.prod volume) :=
        ((hh_int.comp_sub_right u₀).mul_prod hh_int).mul_bdd
          (hκ_cont.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hκ_bound _)
      rw [integral_prod _ hp10']
      conv_rhs => rw [integral_prod _ (hprod_hh u₀), integral_integral_swap (hprod_hh u₀)]
      rw [← integral_add_right_eq_self
        (fun s => ∫ t, h (s - u₀) * h t * κ (t - s)) u₀]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      dsimp only
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [add_sub_cancel_right]
      have hev : κ (t - (s + u₀)) = κ (u₀ + s - t) := by
        rw [show t - (s + u₀) = -(u₀ + s - t) by ring]
        exact hκ_even (u₀ + s - t)
      rw [hev]
      ring
    rw [hi11, hi01, hi10] at hnonneg
    linarith
  set I₀ := ∫ p : ℝ × ℝ, h p.1 * h p.2 * κ (p.2 - p.1) ∂(volume.prod volume)
  set I_u := ∫ p : ℝ × ℝ, h p.1 * h p.2 * κ (u₀ + p.2 - p.1) ∂(volume.prod volume)
  have hM2 : (∫ p : ℝ × ℝ, h p.1 * h p.2 ∂(volume.prod volume)) = M ^ 2 := by
    rw [integral_prod _ (hh_int.mul_prod hh_int)]
    simp_rw [integral_const_mul]
    rw [integral_mul_const, sq]
  have hI0_le : |I₀| ≤ ε / 4 * M ^ 2 := by
    rw [← Real.norm_eq_abs, ← hM2, ← integral_const_mul]
    refine norm_integral_le_of_norm_le ((hh_int.mul_prod hh_int).const_mul (ε / 4))
      (Filter.Eventually.of_forall fun p => ?_)
    by_cases hp1 : r < |p.1|
    · simp [hh_zero p.1 hp1]
    by_cases hp2 : r < |p.2|
    · simp [hh_zero p.2 hp2]
    rw [not_lt] at hp1 hp2
    have hd0 : dist (p.2 - p.1) 0 < δ₁ := by
      rw [Real.dist_eq, sub_zero]
      have hsub : |p.2 - p.1| ≤ |p.2| + |p.1| := by
        calc |p.2 - p.1| = |p.2 + (-p.1)| := rfl
          _ ≤ |p.2| + |-p.1| := abs_add_le _ _
          _ = |p.2| + |p.1| := by rw [abs_neg]
      exact lt_of_le_of_lt (hsub.trans (by linarith)) (h2r_lt.trans_le (min_le_left _ _))
    have hκle : |κ (p.2 - p.1)| ≤ ε / 4 := by
      have hb := hb0 hd0
      rw [Real.dist_eq, hκ_zero, sub_zero] at hb
      exact hb.le
    have hnn : 0 ≤ h p.1 * h p.2 := mul_nonneg (hh_nn p.1) (hh_nn p.2)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn, mul_comm]
    exact mul_le_mul_of_nonneg_right hκle hnn
  have hIu_diff : |I_u - κ u₀ * M ^ 2| ≤ ε / 2 * M ^ 2 := by
    have hIu_int : Integrable (fun p : ℝ × ℝ => h p.1 * h p.2 * κ (u₀ + p.2 - p.1))
        (volume.prod volume) :=
      (hh_int.mul_prod hh_int).mul_bdd
        (hκ_cont.comp ((continuous_const.add continuous_snd).sub continuous_fst)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hκ_bound _)
    have hconst_int : Integrable (fun p : ℝ × ℝ => h p.1 * h p.2 * κ u₀)
        (volume.prod volume) := (hh_int.mul_prod hh_int).mul_const (κ u₀)
    have hsub_eq : I_u - κ u₀ * M ^ 2 =
        ∫ p : ℝ × ℝ, h p.1 * h p.2 * (κ (u₀ + p.2 - p.1) - κ u₀) ∂(volume.prod volume) := by
      have h1 : κ u₀ * M ^ 2 = ∫ p : ℝ × ℝ, h p.1 * h p.2 * κ u₀ ∂(volume.prod volume) := by
        rw [integral_mul_const, hM2, mul_comm]
      rw [h1, ← integral_sub hIu_int hconst_int]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
    rw [hsub_eq, ← Real.norm_eq_abs, ← hM2, ← integral_const_mul]
    refine norm_integral_le_of_norm_le ((hh_int.mul_prod hh_int).const_mul (ε / 2))
      (Filter.Eventually.of_forall fun p => ?_)
    by_cases hp1 : r < |p.1|
    · simp [hh_zero p.1 hp1]
    by_cases hp2 : r < |p.2|
    · simp [hh_zero p.2 hp2]
    rw [not_lt] at hp1 hp2
    have hdu : dist (u₀ + p.2 - p.1) u₀ < δ₂ := by
      rw [Real.dist_eq, show u₀ + p.2 - p.1 - u₀ = p.2 - p.1 by ring]
      have hsub : |p.2 - p.1| ≤ |p.2| + |p.1| := by
        calc |p.2 - p.1| = |p.2 + (-p.1)| := rfl
          _ ≤ |p.2| + |-p.1| := abs_add_le _ _
          _ = |p.2| + |p.1| := by rw [abs_neg]
      exact lt_of_le_of_lt (hsub.trans (by linarith)) (h2r_lt.trans_le (min_le_right _ _))
    have hκle : |κ (u₀ + p.2 - p.1) - κ u₀| ≤ ε / 2 := by
      have hb := hbu hdu
      rw [Real.dist_eq] at hb
      exact hb.le
    have hnn : 0 ≤ h p.1 * h p.2 := mul_nonneg (hh_nn p.1) (hh_nn p.2)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn, mul_comm]
    exact mul_le_mul_of_nonneg_right hκle hnn
  have hp1 : 0 ≤ 2 * I₀ + 2 * 1 * I_u := hpair_ge 1 (by norm_num)
  have hpm1 : 0 ≤ 2 * I₀ + 2 * (-1) * I_u := hpair_ge (-1) (by norm_num)
  have hIu_abs : |I_u| ≤ ε / 4 * M ^ 2 := by
    have h0le : I₀ ≤ |I₀| := le_abs_self I₀
    rw [abs_le]
    constructor <;> linarith
  have htri : |κ u₀ * M ^ 2| ≤ |I_u| + |I_u - κ u₀ * M ^ 2| := by
    calc |κ u₀ * M ^ 2| = |I_u - (I_u - κ u₀ * M ^ 2)| := by congr 1; ring
      _ ≤ |I_u| + |I_u - κ u₀ * M ^ 2| := abs_sub _ _
  rw [abs_mul, abs_of_pos (sq_pos_of_pos hM_pos)] at htri
  have hε_def : |κ u₀| = 2 * ε := by unfold ε; ring
  nlinarith [sq_pos_of_pos hM_pos]

/-- At any cutoff `Λ > 0`, the generic Sonin operator `G_Λ` has nonnegative scaling-conjugate
trace on all `CCMCompactSchwartzLogTest` if and only if its Toeplitz kernel `ccmSoninToeplitzKernel Λ`
vanishes identically on `ℝ`. -/
theorem forall_opTrace_ccmSoninGenericPartAt_re_nonneg_iff {Λ : ℝ} (hΛ : 0 < Λ) :
    (∀ g : CCMCompactSchwartzLogTest,
      0 ≤ (opTrace (ϑ[g.toSchwartzMap] ∘L ccmSoninGenericPartAt Λ ∘L
        ϑ†[g.toSchwartzMap])).re) ↔
    (∀ u : ℝ, ccmSoninToeplitzKernel Λ u = 0) := by
  simp_rw [opTrace_ccmSoninGenericPartAt_eq_toeplitz _ hΛ]
  exact forall_toeplitz_re_nonneg_iff_eq_zero
    (continuous_ccmSoninToeplitzKernel hΛ)
    (norm_ccmSoninToeplitzKernel_le hΛ)
    (im_ccmSoninToeplitzKernel hΛ)
    (ccmSoninToeplitzKernel_neg hΛ)
    (ccmSoninToeplitzKernel_zero hΛ)

/-! ### Uniform Multi-Packet Engine (`ccmMultiPacket`) -/

private theorem sq_sum_le_card_mul_sum_sq {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (∑ i : ι, a i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i : ι, a i ^ 2 := by
  have h0 : 0 ≤ ∑ i : ι, ∑ j : ι, (a i - a j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hexp : (∑ i : ι, ∑ j : ι, (a i - a j) ^ 2) =
      2 * ((Fintype.card ι : ℝ) * ∑ i : ι, a i ^ 2) - 2 * (∑ i : ι, a i) ^ 2 := by
    have hinner : ∀ i : ι, (∑ j : ι, (a i - a j) ^ 2) =
        (Fintype.card ι : ℝ) * a i ^ 2 - 2 * a i * (∑ j : ι, a j) + ∑ j : ι, a j ^ 2 := by
      intro i
      have hterm : ∀ j : ι, (a i - a j) ^ 2 = (a i ^ 2 - 2 * a i * a j) + a j ^ 2 := fun j => by
        ring
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← Finset.mul_sum]
    simp_rw [hinner, sub_add_eq_add_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hmid : (∑ i : ι, 2 * a i * ∑ j : ι, a j) = 2 * (∑ i : ι, a i) ^ 2 := by
      simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, sq]
    rw [hmid]
    ring
  linarith

/-- Finite multi-packet superposition `x ↦ ∑ i, c_i g_0(x - α_i L)` packaged as a
`CCMCompactSchwartzLogTest`. -/
def ccmMultiPacket {ι : Type*} [Fintype ι] (g₀ : CCMCompactSchwartzLogTest)
    (α : ι → ℝ) (c : ι → ℂ) (L : ℝ) : CCMCompactSchwartzLogTest :=
  mkCCMCompactSchwartzLogTest
    (fun x => ∑ i : ι, c i * g₀ (x - α i * L))
    (ContDiff.sum fun i _ =>
      contDiff_const.mul ((g₀.toSchwartzMap.smooth ⊤).comp (contDiff_id.sub contDiff_const)))
    (g₀.radius + (∑ i : ι, |α i|) * |L|)
    (fun x hx => by
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi_le : |α i| ≤ ∑ j : ι, |α j| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (α j)) (Finset.mem_univ i)
      have hmul : |α i * L| ≤ (∑ j : ι, |α j|) * |L| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hi_le (abs_nonneg L)
      have hrad : g₀.radius ≤ |x - α i * L| := by
        have := abs_sub_abs_le_abs_sub x (α i * L)
        linarith
      rw [g₀.eq_zero_of_radius_le_abs _ hrad, mul_zero])

@[simp]
theorem ccmMultiPacket_apply {ι : Type*} [Fintype ι] (g₀ : CCMCompactSchwartzLogTest)
    (α : ι → ℝ) (c : ι → ℂ) (L x : ℝ) :
    ccmMultiPacket g₀ α c L x = ∑ i : ι, c i * g₀ (x - α i * L) := rfl

/-- **Uniform Multi-Packet Toeplitz Decoupling Theorem.**
Let `τ : ℝ → ℂ` be continuous, bounded, and vanish as `u → ±∞`. For any profile `g₀`, any finite
index type `ι`, any injective node configuration `α : ι → ℝ`, and any `η > 0`, there exists a
threshold `L₀ > 0` (independent of `c`) such that for all `L ≥ L₀` and **all** `c : ι → ℂ`,
`‖Toeplitz_τ(ccmMultiPacket g₀ α c L) - (∑ i, ‖c_i‖²) Toeplitz_τ(g₀)‖ ≤ η ∑ i, ‖c_i‖²`. -/
theorem norm_toeplitz_ccmMultiPacket_sub_le {ι : Type*} [Fintype ι]
    (g₀ : CCMCompactSchwartzLogTest) {α : ι → ℝ} (hinj : Function.Injective α)
    {τ : ℝ → ℂ} (hτ : Continuous τ) {C : ℝ} (hC : ∀ u, ‖τ u‖ ≤ C)
    (htop : Tendsto τ atTop (𝓝 0)) (hbot : Tendsto τ atBot (𝓝 0))
    {η : ℝ} (hη : 0 < η) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ c : ι → ℂ,
      ‖(∫ s, ∫ t, conj (ccmMultiPacket g₀ α c L s) * ccmMultiPacket g₀ α c L t * τ (t - s)) -
          ((∑ i : ι, ‖c i‖ ^ 2 : ℝ) : ℂ) *
            (∫ s, ∫ t, conj (g₀ s) * g₀ t * τ (t - s))‖ ≤
        η * ∑ i : ι, ‖c i‖ ^ 2 := by
  classical
  set A := ∫ x : ℝ, ‖g₀ x‖
  have hA_nn : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  set denom : ℝ := (Fintype.card ι : ℝ) * (A ^ 2 + 1) + 1
  have hdenom_pos : 0 < denom := by unfold denom; positivity
  set δ := η / denom
  have hδ : 0 < δ := div_pos hη hdenom_pos
  obtain ⟨U, hU_pos, hU⟩ := exists_norm_le_of_tendsto_atTop_atBot htop hbot hδ
  have hrad_pos : 0 < g₀.radius := zero_lt_one.trans g₀.one_lt_radius
  set L₀ : ℝ := 1 + ∑ p : ι × ι,
    if p.1 = p.2 then (0 : ℝ) else (U + 2 * g₀.radius) / |α p.2 - α p.1|
  have hterm_nn : ∀ p : ι × ι,
      0 ≤ (if p.1 = p.2 then (0 : ℝ) else (U + 2 * g₀.radius) / |α p.2 - α p.1|) := fun p => by
    split_ifs
    · exact le_rfl
    · exact div_nonneg (by positivity) (abs_nonneg _)
  have hL₀_pos : 0 < L₀ := by
    have := Finset.sum_nonneg fun p (_ : p ∈ Finset.univ) => hterm_nn p
    unfold L₀; linarith
  refine ⟨L₀, hL₀_pos, fun L hL c => ?_⟩
  have hL_pos : 0 < L := hL₀_pos.trans_le hL
  set gL := ccmMultiPacket g₀ α c L
  have hg₀_int : Integrable (fun x => g₀ x) volume := g₀.toSchwartzMap.integrable
  have hgL_int : Integrable (fun x => gL x) volume := gL.toSchwartzMap.integrable
  have hshift_int : ∀ i : ι, Integrable (fun x => g₀ (x - α i * L)) volume :=
    fun i => hg₀_int.comp_sub_right (α i * L)
  set Ipair : ι → ι → ℂ := fun i j =>
    ∫ s, ∫ t, conj (g₀ (s - α i * L)) * g₀ (t - α j * L) * τ (t - s)
  set I₀ : ℂ := ∫ s, ∫ t, conj (g₀ s) * g₀ t * τ (t - s)
  -- Expand the Toeplitz integral of `gL` into `∑ i, ∑ j, conj(c i) * c j * Ipair i j`:
  have hexpand : (∫ s, ∫ t, conj (gL s) * gL t * τ (t - s)) =
      ∑ i : ι, ∑ j : ι, conj (c i) * c j * Ipair i j := by
    have hint_inner : ∀ s : ℝ, ∀ j : ι,
        Integrable (fun t => c j * (conj (gL s) * g₀ (t - α j * L) * τ (t - s))) volume :=
      fun s j => (((hshift_int j).const_mul (conj (gL s))).mul_bdd
        (hτ.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => hC (t - s))).const_mul (c j)
    have hstep1 : ∀ s : ℝ, (∫ t, conj (gL s) * gL t * τ (t - s)) =
        ∑ j : ι, c j * ∫ t, conj (gL s) * g₀ (t - α j * L) * τ (t - s) := by
      intro s
      have hpt1 : ∀ t : ℝ, conj (gL s) * gL t * τ (t - s) =
          ∑ j : ι, c j * (conj (gL s) * g₀ (t - α j * L) * τ (t - s)) := fun t => by
        simp only [gL, ccmMultiPacket_apply, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      simp_rw [hpt1]
      rw [integral_finsetSum Finset.univ fun (j : ι) _ => hint_inner s j]
      exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    simp_rw [hstep1]
    have hint_outer : ∀ j : ι,
        Integrable (fun s => c j * ∫ t, conj (gL s) * g₀ (t - α j * L) * τ (t - s)) volume :=
      fun j =>
        (integrable_prod_toeplitz hgL_int (hshift_int j) hτ hC).integral_prod_left.const_mul (c j)
    rw [integral_finsetSum Finset.univ fun (j : ι) _ => hint_outer j]
    simp_rw [integral_const_mul]
    have hstep2 : ∀ j : ι, (∫ s, ∫ t, conj (gL s) * g₀ (t - α j * L) * τ (t - s)) =
        ∑ i : ι, conj (c i) * Ipair i j := by
      intro j
      have hpt2 : ∀ s : ℝ, (∫ t, conj (gL s) * g₀ (t - α j * L) * τ (t - s)) =
          ∑ i : ι, conj (c i) * ∫ t, conj (g₀ (s - α i * L)) * g₀ (t - α j * L) * τ (t - s) := by
        intro s
        have hpt_t : ∀ t : ℝ, conj (gL s) * g₀ (t - α j * L) * τ (t - s) =
            ∑ i : ι, conj (c i) * (conj (g₀ (s - α i * L)) * g₀ (t - α j * L) * τ (t - s)) :=
          fun t => by
            simp only [gL, ccmMultiPacket_apply, map_sum, map_mul, Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by ring
        simp_rw [hpt_t]
        have hint_i : ∀ i : ι, Integrable
            (fun t => conj (c i) * (conj (g₀ (s - α i * L)) * g₀ (t - α j * L) * τ (t - s)))
            volume := fun i =>
          (((hshift_int j).const_mul (conj (g₀ (s - α i * L)))).mul_bdd
            (hτ.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
            (Filter.Eventually.of_forall fun t => hC (t - s))).const_mul (conj (c i))
        rw [integral_finsetSum Finset.univ fun (i : ι) _ => hint_i i]
        exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      simp_rw [hpt2]
      rw [integral_finsetSum Finset.univ fun (i : ι) _ =>
        (integrable_prod_toeplitz (hshift_int i) (hshift_int j) hτ hC).integral_prod_left.const_mul _]
      exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
    simp_rw [hstep2, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  -- Diagonal terms equal `I₀`:
  have hdiag : ∀ i : ι, Ipair i i = I₀ := by
    intro i
    dsimp only [Ipair, I₀]
    simp_rw [← integral_add_right_eq_self
      (fun s => ∫ t, conj (g₀ (s - α i * L)) * g₀ (t - α i * L) * τ (t - s)) (α i * L)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    dsimp only
    rw [← integral_add_right_eq_self
      (fun t => conj (g₀ ((s + α i * L) - α i * L)) * g₀ (t - α i * L) * τ (t - (s + α i * L)))
      (α i * L)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [add_sub_cancel_right]
    congr 2
    ring
  -- Split off the diagonal sum:
  have hdiff_eq : (∫ s, ∫ t, conj (gL s) * gL t * τ (t - s)) -
      ((∑ i : ι, ‖c i‖ ^ 2 : ℝ) : ℂ) * I₀ =
      ∑ i : ι, ∑ j : ι, if i = j then (0 : ℂ) else conj (c i) * c j * Ipair i j := by
    rw [hexpand]
    have hsplit : ∀ i : ι, (∑ j : ι, conj (c i) * c j * Ipair i j) =
        conj (c i) * c i * I₀ +
          ∑ j : ι, if i = j then (0 : ℂ) else conj (c i) * c j * Ipair i j := by
      intro i
      have h1 : (∑ j : ι, conj (c i) * c j * Ipair i j) =
          (∑ j : ι, if i = j then conj (c i) * c j * Ipair i j else 0) +
            ∑ j : ι, if i = j then (0 : ℂ) else conj (c i) * c j * Ipair i j := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
      rw [h1, Finset.sum_ite_eq Finset.univ i, if_pos (Finset.mem_univ i), hdiag i]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    have hdiag_sum : (∑ i : ι, conj (c i) * c i * I₀) =
        ((∑ i : ι, ‖c i‖ ^ 2 : ℝ) : ℂ) * I₀ := by
      rw [← Finset.sum_mul, Complex.ofReal_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm (conj (c i)), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hdiag_sum, add_sub_cancel_left]
  rw [hdiff_eq]
  -- Off-diagonal bound `‖Ipair i j‖ ≤ δ * A ^ 2` for `i ≠ j`:
  have hoff_le : ∀ i j : ι, i ≠ j → ‖Ipair i j‖ ≤ δ * A ^ 2 := by
    intro i j hij
    have hα_ne : α j - α i ≠ 0 := sub_ne_zero.mpr (fun heq => hij (hinj heq).symm)
    have hα_pos : 0 < |α j - α i| := abs_pos.mpr hα_ne
    have hle_L : (U + 2 * g₀.radius) / |α j - α i| ≤ L := by
      have hmem : (i, j) ∈ (Finset.univ : Finset (ι × ι)) := Finset.mem_univ _
      have hsingle := Finset.single_le_sum (fun p _ => hterm_nn p) hmem
      simp only [hij, ↓reduceIte] at hsingle
      unfold L₀ at hL
      linarith
    have hsep : U + 2 * g₀.radius ≤ |(α j - α i) * L| := by
      rw [abs_mul, abs_of_pos hL_pos, mul_comm |α j - α i| L]
      exact (div_le_iff₀ hα_pos).mp hle_L
    have hshift_eq : Ipair i j =
        ∫ p : ℝ × ℝ, conj (g₀ p.1) * g₀ p.2 * τ (p.2 - p.1 + (α j - α i) * L)
          ∂(volume.prod volume) := by
      have hint_rhs : Integrable
          (fun p : ℝ × ℝ => conj (g₀ p.1) * g₀ p.2 * τ (p.2 - p.1 + (α j - α i) * L))
          (volume.prod volume) :=
        ((integrable_conj hg₀_int).mul_prod hg₀_int).mul_bdd
          (hτ.comp ((continuous_snd.sub continuous_fst).add continuous_const)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun p => hC _)
      rw [integral_prod _ hint_rhs]
      dsimp only [Ipair]
      simp_rw [← integral_add_right_eq_self
        (fun s => ∫ t, conj (g₀ (s - α i * L)) * g₀ (t - α j * L) * τ (t - s)) (α i * L)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      dsimp only
      rw [← integral_add_right_eq_self
        (fun t => conj (g₀ ((s + α i * L) - α i * L)) * g₀ (t - α j * L) * τ (t - (s + α i * L)))
        (α j * L)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [add_sub_cancel_right]
      congr 2
      ring
    have hA2 : A ^ 2 = ∫ p : ℝ × ℝ, ‖g₀ p.1‖ * ‖g₀ p.2‖ ∂(volume.prod volume) := by
      rw [integral_prod _ (hg₀_int.norm.mul_prod hg₀_int.norm)]
      simp_rw [integral_const_mul]
      rw [integral_mul_const, sq]
    rw [hshift_eq, hA2, ← integral_const_mul]
    refine norm_integral_le_of_norm_le
      ((hg₀_int.norm.mul_prod hg₀_int.norm).const_mul δ)
      (Filter.Eventually.of_forall fun p => ?_)
    by_cases hp1 : g₀.radius ≤ |p.1|
    · simp [g₀.eq_zero_of_radius_le_abs p.1 hp1]
    by_cases hp2 : g₀.radius ≤ |p.2|
    · simp [g₀.eq_zero_of_radius_le_abs p.2 hp2]
    rw [not_le] at hp1 hp2
    have hbig : U ≤ |p.2 - p.1 + (α j - α i) * L| := by
      have h1 : |p.2 - p.1| < 2 * g₀.radius := by
        have hsub : |p.2 - p.1| ≤ |p.2| + |p.1| := by
          calc |p.2 - p.1| = |p.2 + (-p.1)| := rfl
            _ ≤ |p.2| + |-p.1| := abs_add_le _ _
            _ = |p.2| + |p.1| := by rw [abs_neg]
        linarith
      have h2 : |(α j - α i) * L| - |-(p.2 - p.1)| ≤
          |(α j - α i) * L - (-(p.2 - p.1))| :=
        abs_sub_abs_le_abs_sub ((α j - α i) * L) (-(p.2 - p.1))
      rw [abs_neg, show (α j - α i) * L - -(p.2 - p.1) = p.2 - p.1 + (α j - α i) * L by ring] at h2
      linarith
    have hτ_le := hU _ hbig
    rw [norm_mul, norm_mul, RCLike.norm_conj, mul_comm δ]
    exact mul_le_mul_of_nonneg_left hτ_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  -- Combine off-diagonal bounds with Cauchy–Schwarz on `c`:
  calc ‖∑ i : ι, ∑ j : ι, if i = j then (0 : ℂ) else conj (c i) * c j * Ipair i j‖
      ≤ ∑ i : ι, ‖∑ j : ι, if i = j then (0 : ℂ) else conj (c i) * c j * Ipair i j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : ι, ∑ j : ι, ‖if i = j then (0 : ℂ) else conj (c i) * c j * Ipair i j‖ :=
        Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i : ι, ∑ j : ι, ‖c i‖ * ‖c j‖ * (δ * A ^ 2) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        split_ifs with hij
        · rw [norm_zero]; positivity
        · rw [norm_mul, norm_mul, RCLike.norm_conj]
          exact mul_le_mul_of_nonneg_left (hoff_le i j hij) (by positivity)
    _ = δ * A ^ 2 * (∑ i : ι, ‖c i‖) ^ 2 := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
        rw [← Finset.sum_mul]
        ring
    _ ≤ δ * A ^ 2 * ((Fintype.card ι : ℝ) * ∑ i : ι, ‖c i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (sq_sum_le_card_mul_sum_sq fun i => ‖c i‖) (by positivity)
    _ = (δ * ((Fintype.card ι : ℝ) * A ^ 2)) * ∑ i : ι, ‖c i‖ ^ 2 := by ring
    _ ≤ η * ∑ i : ι, ‖c i‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun i _ => sq_nonneg _)
        have h1 : (Fintype.card ι : ℝ) * A ^ 2 ≤ denom := by
          unfold denom
          nlinarith [show (0 : ℝ) ≤ Fintype.card ι by positivity]
        calc δ * ((Fintype.card ι : ℝ) * A ^ 2)
            ≤ δ * denom := mul_le_mul_of_nonneg_left h1 hδ.le
          _ = η := div_mul_cancel₀ η hdenom_pos.ne'

/-- **Exact Disjoint `L²` Norm Additivity for `ccmMultiPacket`.**
For any profile `g₀` and injective node configuration `α : ι → ℝ`, once `L` separates distinct
packet supports (`L ≥ L₁`), `∫ ‖ccmMultiPacket g₀ α c L x‖² dx = (∑ i, ‖c_i‖²) ∫ ‖g₀ x‖² dx`
for **all** `c : ι → ℂ`. -/
theorem integral_norm_sq_ccmMultiPacket_eq {ι : Type*} [Fintype ι]
    (g₀ : CCMCompactSchwartzLogTest) {α : ι → ℝ} (hinj : Function.Injective α) :
    ∃ L₁ : ℝ, 0 < L₁ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ c : ι → ℂ,
      ∫ x : ℝ, ‖ccmMultiPacket g₀ α c L x‖ ^ 2 =
        (∑ i : ι, ‖c i‖ ^ 2) * ∫ x : ℝ, ‖g₀ x‖ ^ 2 := by
  classical
  have hrad_pos : 0 < g₀.radius := zero_lt_one.trans g₀.one_lt_radius
  set L₁ : ℝ := 1 + ∑ p : ι × ι,
    if p.1 = p.2 then (0 : ℝ) else (2 * g₀.radius) / |α p.2 - α p.1|
  have hterm_nn : ∀ p : ι × ι,
      0 ≤ (if p.1 = p.2 then (0 : ℝ) else (2 * g₀.radius) / |α p.2 - α p.1|) := fun p => by
    split_ifs
    · exact le_rfl
    · exact div_nonneg (by positivity) (abs_nonneg _)
  have hL₁_pos : 0 < L₁ := by
    have := Finset.sum_nonneg fun p (_ : p ∈ Finset.univ) => hterm_nn p
    unfold L₁; linarith
  refine ⟨L₁, hL₁_pos, fun L hL c => ?_⟩
  have hL_pos : 0 < L := hL₁_pos.trans_le hL
  have hdisj : ∀ i j : ι, i ≠ j → ∀ x : ℝ,
      g₀ (x - α i * L) = 0 ∨ g₀ (x - α j * L) = 0 := by
    intro i j hij x
    have hα_pos : 0 < |α j - α i| :=
      abs_pos.mpr (sub_ne_zero.mpr fun heq => hij (hinj heq).symm)
    have hle_L : (2 * g₀.radius) / |α j - α i| ≤ L := by
      have hsingle := Finset.single_le_sum (fun p _ => hterm_nn p) (Finset.mem_univ (i, j))
      simp only [hij, ↓reduceIte] at hsingle
      unfold L₁ at hL; linarith
    have hsep : 2 * g₀.radius ≤ |(α j - α i) * L| := by
      rw [abs_mul, abs_of_pos hL_pos, mul_comm |α j - α i| L]
      exact (div_le_iff₀ hα_pos).mp hle_L
    have hsum_abs : |(α j - α i) * L| ≤ |x - α i * L| + |x - α j * L| := by
      calc |(α j - α i) * L| = |(x - α i * L) - (x - α j * L)| := by congr 1; ring
        _ ≤ |x - α i * L| + |-(x - α j * L)| := abs_add_le _ _
        _ = |x - α i * L| + |x - α j * L| := by rw [abs_neg]
    rcases le_or_gt g₀.radius |x - α i * L| with hi | hi
    · exact Or.inl (g₀.eq_zero_of_radius_le_abs _ hi)
    · exact Or.inr (g₀.eq_zero_of_radius_le_abs _ (by linarith))
  have hpt : ∀ x : ℝ,
      ‖ccmMultiPacket g₀ α c L x‖ ^ 2 = ∑ i : ι, ‖c i‖ ^ 2 * ‖g₀ (x - α i * L)‖ ^ 2 := by
    intro x
    have hnorm_sq : ∀ z : ℂ, ‖z‖ ^ 2 = (conj z * z).re := fun z => by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    rw [hnorm_sq, ccmMultiPacket_apply, map_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    have hrow : ∀ i : ι,
        (∑ j : ι, conj (c i * g₀ (x - α i * L)) * (c j * g₀ (x - α j * L))) =
          conj (c i * g₀ (x - α i * L)) * (c i * g₀ (x - α i * L)) := by
      intro i
      rw [Finset.sum_eq_single i]
      · intro j _ hji
        rcases hdisj i j hji.symm x with hi0 | hj0
        · simp [hi0]
        · simp [hj0]
      · intro hi_not; exact absurd (Finset.mem_univ i) hi_not
    simp_rw [hrow]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hnorm_sq, norm_mul, mul_pow]
  simp_rw [hpt]
  have hint_sq : Integrable (fun x : ℝ => ‖g₀ x‖ ^ 2) volume :=
    (g₀.toSchwartzMap.memLp 2 volume).integrable_norm_pow (by norm_num)
  rw [integral_finsetSum Finset.univ fun (i : ι) _ => (hint_sq.comp_sub_right (α i * L)).const_mul _]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_sub_right_eq_self (fun x : ℝ => ‖g₀ x‖ ^ 2) (α i * L)]

/-! ## Section 3: Unconditional Large-Support Refutation and Infinite Negative Morse Index at Cutoff `Λ = 1` -/

private theorem injective_pair_one_neg_one : Function.Injective ![(1 : ℝ), -1] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> norm_num at hij

/-- Real odd mean-zero two-packet `φ(x - L) - φ(x + L)` built from `ccmSmallSupportBump`. -/
def ccmOddTwoPacket (L : ℝ) : CCMCompactSchwartzLogTest :=
  ccmMultiPacket ccmSmallSupportBump ![(1 : ℝ), -1] ![(1 : ℂ), -1] L

theorem ccmOddTwoPacket_apply (L x : ℝ) :
    ccmOddTwoPacket L x = ccmSmallSupportBump (x - L) - ccmSmallSupportBump (x + L) := by
  simp [ccmOddTwoPacket, Fin.sum_univ_two, sub_eq_add_neg]

theorem ccmOddTwoPacket_im (L x : ℝ) : (ccmOddTwoPacket L x).im = 0 := by
  simp [ccmOddTwoPacket_apply, ccmSmallSupportBump_im]

theorem ccmOddTwoPacket_odd (L x : ℝ) :
    ccmOddTwoPacket L (-x) = -ccmOddTwoPacket L x := by
  rw [ccmOddTwoPacket_apply, ccmOddTwoPacket_apply]
  have h1 : ccmSmallSupportBump (-x - L) = ccmSmallSupportBump (x + L) := by
    rw [show -x - L = -(x + L) by ring, ccmSmallSupportBump_even]
  have h2 : ccmSmallSupportBump (-x + L) = ccmSmallSupportBump (x - L) := by
    rw [show -x + L = -(x - L) by ring, ccmSmallSupportBump_even]
  rw [h1, h2]
  ring

theorem ccmOddTwoPacket_integral_eq_zero (L : ℝ) : ∫ x : ℝ, ccmOddTwoPacket L x = 0 := by
  have hint := ccmSmallSupportBump.toSchwartzMap.integrable (μ := volume)
  simp_rw [ccmOddTwoPacket_apply]
  rw [integral_sub (hint.comp_sub_right L) (hint.comp_add_right L),
    integral_sub_right_eq_self (fun x => ccmSmallSupportBump x) L,
    integral_add_right_eq_self (fun x => ccmSmallSupportBump x) L, sub_self]

/-- As `L → +∞`, the cutoff-`1` generic Sonin trace on `ccmOddTwoPacket L` converges to
`2 Q_{τ_1}(ccmSmallSupportBump) < 0`. -/
theorem tendsto_opTrace_ccmOddTwoPacket_atTop :
    Tendsto (fun L : ℝ =>
      (opTrace (ϑ[(ccmOddTwoPacket L).toSchwartzMap] ∘L ccmSoninGenericPartAt 1 ∘L
        ϑ†[(ccmOddTwoPacket L).toSchwartzMap])).re)
      atTop
      (𝓝 (2 * (∫ s, ∫ t, conj (ccmSmallSupportBump s) * ccmSmallSupportBump t *
        ccmSoninToeplitzKernel 1 (t - s)).re)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨L₀, _, hdec⟩ := norm_toeplitz_ccmMultiPacket_sub_le ccmSmallSupportBump
    injective_pair_one_neg_one
    (continuous_ccmSoninToeplitzKernel one_pos)
    (norm_ccmSoninToeplitzKernel_le one_pos)
    (tendsto_ccmSoninToeplitzKernel_atTop one_pos)
    (tendsto_ccmSoninToeplitzKernel_atBot one_pos)
    (show 0 < ε / 3 by positivity)
  filter_upwards [eventually_ge_atTop L₀] with L hL
  rw [Real.dist_eq, opTrace_ccmSoninGenericPartAt_eq_toeplitz (ccmOddTwoPacket L) one_pos]
  have hbound := hdec L hL ![(1 : ℂ), -1]
  have hcsum : (∑ i : Fin 2, ‖(![(1 : ℂ), -1] : Fin 2 → ℂ) i‖ ^ 2) = 2 := by
    simp [Fin.sum_univ_two]
    norm_num
  rw [hcsum] at hbound
  have hre : |(∫ s, ∫ t, conj (ccmOddTwoPacket L s) * ccmOddTwoPacket L t *
        ccmSoninToeplitzKernel 1 (t - s)).re -
      2 * (∫ s, ∫ t, conj (ccmSmallSupportBump s) * ccmSmallSupportBump t *
        ccmSoninToeplitzKernel 1 (t - s)).re| ≤ ε / 3 * 2 := by
    have h := (Complex.abs_re_le_norm _).trans hbound
    simpa [ccmOddTwoPacket, Complex.sub_re, Complex.mul_re] using h
  linarith

/-- **Unconditional Large-Support Refutation of Cutoff-`1` Sonin-Trace Domination on Real Odd
Mean-Zero Compact Schwartz Tests.** -/
theorem not_ccmSoninTraceDomination_odd_meanZero_twoPacket :
    ∀ᶠ L : ℝ in atTop,
      (∀ x : ℝ, (ccmOddTwoPacket L x).im = 0) ∧
      (∀ x : ℝ, ccmOddTwoPacket L (-x) = -ccmOddTwoPacket L x) ∧
      (∫ x : ℝ, ccmOddTwoPacket L x = 0) ∧
      (-ccmArchimedeanWeilDistribution (ccmSoninGramTest (ccmOddTwoPacket L))).re <
        (opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel
          (ccmSoninGramTest (ccmOddTwoPacket L)).toSchwartzMap) *
          evenCentralSoninProjection 1)).re := by
  have hneg : 2 * (∫ s, ∫ t, conj (ccmSmallSupportBump s) * ccmSmallSupportBump t *
      ccmSoninToeplitzKernel 1 (t - s)).re < 0 := by
    linarith [re_toeplitz_ccmSmallSupportBump_neg]
  filter_upwards [tendsto_opTrace_ccmOddTwoPacket_atTop.eventually (Iio_mem_nhds hneg)] with L hL
  refine ⟨ccmOddTwoPacket_im L, ccmOddTwoPacket_odd L, ccmOddTwoPacket_integral_eq_zero L, ?_⟩
  rw [← not_le, ccmSoninTraceDomination_iff_toeplitz,
    ← opTrace_ccmSoninGenericPartAt_eq_toeplitz (ccmOddTwoPacket L) one_pos, not_le]
  exact hL

/-! ### Double-Pole-Free Four-Packets and Dyadic Infinite Negative Cone -/

/-- Positive polar-cancellation weight `1 / (2 cosh(L / 2))`. -/
def ccmPoleFreeWeight (L : ℝ) : ℝ :=
  1 / (2 * Real.cosh (L / 2))

theorem ccmPoleFreeWeight_pos (L : ℝ) : 0 < ccmPoleFreeWeight L := by
  unfold ccmPoleFreeWeight
  have := Real.cosh_pos (L / 2)
  positivity

/-- Integer four-node stencil `(1, -1, 2, -2)` on `Fin 4`. -/
def ccmBasePoleIntNode (j : Fin 4) : ℤ :=
  if j.1 = 0 then 1 else if j.1 = 1 then -1 else if j.1 = 2 then 2 else -2

/-- Real four-node stencil `(1, -1, 2, -2)` on `Fin 4`. -/
def ccmBasePoleNode (j : Fin 4) : ℝ :=
  (ccmBasePoleIntNode j : ℝ)

@[simp] theorem ccmBasePoleNode_zero : ccmBasePoleNode 0 = 1 := by simp [ccmBasePoleNode, ccmBasePoleIntNode]
@[simp] theorem ccmBasePoleNode_one : ccmBasePoleNode 1 = -1 := by simp [ccmBasePoleNode, ccmBasePoleIntNode]
@[simp] theorem ccmBasePoleNode_two : ccmBasePoleNode 2 = 2 := by simp [ccmBasePoleNode, ccmBasePoleIntNode]
@[simp] theorem ccmBasePoleNode_three : ccmBasePoleNode 3 = -2 := by simp [ccmBasePoleNode, ccmBasePoleIntNode]

/-- Coefficient vector `[1, -1, -1/(2 cosh(L/2)), 1/(2 cosh(L/2))]` cancelling `1`, `e^{x/2}`,
and `e^{-x/2}` simultaneously at nodes `[L, -L, 2L, -2L]`. -/
def ccmPoleFreeFourCoeffs (L : ℝ) : Fin 4 → ℂ :=
  ![1, -1, -(ccmPoleFreeWeight L : ℂ), (ccmPoleFreeWeight L : ℂ)]

/-- Mean-zero double-pole-free four-packet attached to any profile `φ` and scale `L`. -/
def ccmPoleFreeFourPacketOf (φ : CCMCompactSchwartzLogTest) (L : ℝ) : CCMCompactSchwartzLogTest :=
  ccmMultiPacket φ ccmBasePoleNode (ccmPoleFreeFourCoeffs L) L

/-- Canonical real odd mean-zero double-pole-free four-packet built from `ccmSmallSupportBump`. -/
abbrev ccmPoleFreeFourPacket (L : ℝ) : CCMCompactSchwartzLogTest :=
  ccmPoleFreeFourPacketOf ccmSmallSupportBump L

private theorem integrable_compactSchwartz_mul_continuous (g : CCMCompactSchwartzLogTest)
    {Φ : ℝ → ℂ} (hΦ : Continuous Φ) :
    Integrable (fun x : ℝ => g x * Φ x) volume := by
  refine Continuous.integrable_of_hasCompactSupport (g.toSchwartzMap.continuous.mul hΦ) ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -g.radius) (b := g.radius)) fun x hx => ?_
  have habs : g.radius ≤ |x| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · exact (by linarith : g.radius ≤ -x).trans (neg_le_abs x)
    · exact hx.le.trans (le_abs_self x)
  simp [g.eq_zero_of_radius_le_abs x habs]

private theorem integral_shift_mul_exp (φ : CCMCompactSchwartzLogTest) (a σ : ℝ) :
    (∫ x : ℝ, φ (x - a) * ((Real.exp (σ * x) : ℝ) : ℂ)) =
      ((Real.exp (σ * a) : ℝ) : ℂ) * ∫ x : ℝ, φ x * ((Real.exp (σ * x) : ℝ) : ℂ) := by
  rw [← integral_add_right_eq_self
    (fun x : ℝ => φ (x - a) * ((Real.exp (σ * x) : ℝ) : ℂ)) a, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  simp only [add_sub_cancel_right]
  rw [show σ * (x + a) = σ * a + σ * x by ring, Real.exp_add, Complex.ofReal_mul]
  ring

theorem ccmPoleFreeFourPacketOf_integral_eq_zero (φ : CCMCompactSchwartzLogTest) (L : ℝ) :
    ∫ x : ℝ, ccmPoleFreeFourPacketOf φ L x = 0 := by
  have hint : ∀ a : ℝ, Integrable (fun x : ℝ => φ (x - a)) volume :=
    fun a => φ.toSchwartzMap.integrable.comp_sub_right a
  simp only [ccmPoleFreeFourPacketOf, ccmMultiPacket_apply]
  rw [integral_finsetSum Finset.univ fun (i : Fin 4) _ => (hint _).const_mul _]
  simp_rw [integral_const_mul, integral_sub_right_eq_self (fun x : ℝ => φ x)]
  rw [← Finset.sum_mul]
  have hsum0 : (∑ i : Fin 4, ccmPoleFreeFourCoeffs L i) = 0 := by
    simp [ccmPoleFreeFourCoeffs, Fin.sum_univ_four]
  rw [hsum0, zero_mul]

private theorem ccmPoleFreeFourCoeffs_exp_cancel {L σ : ℝ} (hσ : σ = 1 / 2 ∨ σ = -(1 / 2)) :
    (∑ i : Fin 4, ccmPoleFreeFourCoeffs L i *
      ((Real.exp (σ * (ccmBasePoleNode i * L)) : ℝ) : ℂ)) = 0 := by
  set u := σ * L
  have hcosh_eq : Real.cosh (L / 2) = Real.cosh u := by
    rcases hσ with rfl | rfl
    · congr 1; ring
    · rw [← Real.cosh_neg]; congr 1; ring
  have hcosh_pos : 0 < Real.cosh (L / 2) := Real.cosh_pos (L / 2)
  have hreal : Real.exp u - Real.exp (-u) -
      ccmPoleFreeWeight L * (Real.exp (2 * u) - Real.exp (-(2 * u))) = 0 := by
    unfold ccmPoleFreeWeight
    have h2u : Real.exp (2 * u) - Real.exp (-(2 * u)) =
        (Real.exp u - Real.exp (-u)) * (2 * Real.cosh u) := by
      rw [Real.cosh_eq, show (2 : ℝ) * u = u + u by ring,
        show -(u + u) = -u + -u by ring, Real.exp_add, Real.exp_add]
      ring
    rw [h2u, ← hcosh_eq]
    field_simp [hcosh_pos.ne']
    ring
  simp only [ccmPoleFreeFourCoeffs, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, ccmBasePoleNode_zero, ccmBasePoleNode_one,
    show ccmBasePoleNode 2 = 2 from ccmBasePoleNode_two,
    show ccmBasePoleNode 3 = -2 from ccmBasePoleNode_three]
  have h1 : σ * ((1 : ℝ) * L) = u := by unfold u; ring
  have h2 : σ * ((-1 : ℝ) * L) = -u := by unfold u; ring
  have h3 : σ * ((2 : ℝ) * L) = 2 * u := by unfold u; ring
  have h4 : σ * ((-2 : ℝ) * L) = -(2 * u) := by unfold u; ring
  rw [h1, h2, h3, h4]
  have hcast : (((Real.exp u - Real.exp (-u) -
      ccmPoleFreeWeight L * (Real.exp (2 * u) - Real.exp (-(2 * u))) : ℝ) : ℂ)) = 0 := by
    rw [hreal, Complex.ofReal_zero]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul] at hcast
  linear_combination hcast

theorem ccmPoleFreeFourPacketOf_integral_exp_half_eq_zero
    (φ : CCMCompactSchwartzLogTest) (L : ℝ) :
    ∫ x : ℝ, ccmPoleFreeFourPacketOf φ L x * ((Real.exp (x / 2) : ℝ) : ℂ) = 0 := by
  have hrew : (fun x : ℝ => ccmPoleFreeFourPacketOf φ L x * ((Real.exp (x / 2) : ℝ) : ℂ)) =
      (fun x : ℝ => ccmPoleFreeFourPacketOf φ L x * ((Real.exp ((1 / 2 : ℝ) * x) : ℝ) : ℂ)) := by
    ext x; congr 2; ring
  rw [hrew]
  simp_rw [ccmPoleFreeFourPacketOf, ccmMultiPacket_apply, Finset.sum_mul]
  have hint : ∀ i : Fin 4, Integrable
      (fun x : ℝ => ccmPoleFreeFourCoeffs L i * φ (x - ccmBasePoleNode i * L) *
        ((Real.exp ((1 / 2 : ℝ) * x) : ℝ) : ℂ)) volume := fun i => by
    have hcont : Continuous (fun x : ℝ => ((Real.exp ((1 / 2 : ℝ) * x) : ℝ) : ℂ)) := by fun_prop
    let g_i := mkCCMCompactSchwartzLogTest
      (fun x => φ (x - ccmBasePoleNode i * L))
      ((φ.toSchwartzMap.smooth ⊤).comp (contDiff_id.sub contDiff_const))
      (φ.radius + |ccmBasePoleNode i * L|)
      (fun x hx => φ.eq_zero_of_radius_le_abs _ (by
        have := abs_sub_abs_le_abs_sub x (ccmBasePoleNode i * L); linarith))
    have h_int := (integrable_compactSchwartz_mul_continuous g_i hcont).const_mul
      (ccmPoleFreeFourCoeffs L i)
    simp only [g_i, mkCCMCompactSchwartzLogTest_apply, ← mul_assoc] at h_int
    exact h_int
  rw [integral_finsetSum Finset.univ fun (i : Fin 4) _ => hint i]
  have hterm : ∀ i : Fin 4,
      (∫ x : ℝ, ccmPoleFreeFourCoeffs L i * φ (x - ccmBasePoleNode i * L) *
          ((Real.exp ((1 / 2 : ℝ) * x) : ℝ) : ℂ)) =
        (ccmPoleFreeFourCoeffs L i *
          ((Real.exp ((1 / 2 : ℝ) * (ccmBasePoleNode i * L)) : ℝ) : ℂ)) *
          ∫ x : ℝ, φ x * ((Real.exp ((1 / 2 : ℝ) * x) : ℝ) : ℂ) := by
    intro i
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_shift_mul_exp, ← mul_assoc]
  simp_rw [hterm, ← Finset.sum_mul, ccmPoleFreeFourCoeffs_exp_cancel (Or.inl rfl), zero_mul]

theorem ccmPoleFreeFourPacketOf_integral_exp_neg_half_eq_zero
    (φ : CCMCompactSchwartzLogTest) (L : ℝ) :
    ∫ x : ℝ, ccmPoleFreeFourPacketOf φ L x * ((Real.exp (-(x / 2)) : ℝ) : ℂ) = 0 := by
  have hrew : (fun x : ℝ => ccmPoleFreeFourPacketOf φ L x * ((Real.exp (-(x / 2)) : ℝ) : ℂ)) =
      (fun x : ℝ =>
        ccmPoleFreeFourPacketOf φ L x * ((Real.exp ((-(1 / 2) : ℝ) * x) : ℝ) : ℂ)) := by
    ext x; congr 2; ring
  rw [hrew]
  simp_rw [ccmPoleFreeFourPacketOf, ccmMultiPacket_apply, Finset.sum_mul]
  have hint : ∀ i : Fin 4, Integrable
      (fun x : ℝ => ccmPoleFreeFourCoeffs L i * φ (x - ccmBasePoleNode i * L) *
        ((Real.exp ((-(1 / 2) : ℝ) * x) : ℝ) : ℂ)) volume := fun i => by
    have hcont : Continuous (fun x : ℝ => ((Real.exp ((-(1 / 2) : ℝ) * x) : ℝ) : ℂ)) := by fun_prop
    let g_i := mkCCMCompactSchwartzLogTest
      (fun x => φ (x - ccmBasePoleNode i * L))
      ((φ.toSchwartzMap.smooth ⊤).comp (contDiff_id.sub contDiff_const))
      (φ.radius + |ccmBasePoleNode i * L|)
      (fun x hx => φ.eq_zero_of_radius_le_abs _ (by
        have := abs_sub_abs_le_abs_sub x (ccmBasePoleNode i * L); linarith))
    have h_int := (integrable_compactSchwartz_mul_continuous g_i hcont).const_mul
      (ccmPoleFreeFourCoeffs L i)
    simp only [g_i, mkCCMCompactSchwartzLogTest_apply, ← mul_assoc] at h_int
    exact h_int
  rw [integral_finsetSum Finset.univ fun (i : Fin 4) _ => hint i]
  have hterm : ∀ i : Fin 4,
      (∫ x : ℝ, ccmPoleFreeFourCoeffs L i * φ (x - ccmBasePoleNode i * L) *
          ((Real.exp ((-(1 / 2) : ℝ) * x) : ℝ) : ℂ)) =
        (ccmPoleFreeFourCoeffs L i *
          ((Real.exp ((-(1 / 2) : ℝ) * (ccmBasePoleNode i * L)) : ℝ) : ℂ)) *
          ∫ x : ℝ, φ x * ((Real.exp ((-(1 / 2) : ℝ) * x) : ℝ) : ℂ) := by
    intro i
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_shift_mul_exp, ← mul_assoc]
  simp_rw [hterm, ← Finset.sum_mul, ccmPoleFreeFourCoeffs_exp_cancel (Or.inr rfl), zero_mul]

theorem ccmPoleFreeFourPacket_im (L x : ℝ) : (ccmPoleFreeFourPacket L x).im = 0 := by
  simp [ccmPoleFreeFourPacket, ccmPoleFreeFourPacketOf, ccmPoleFreeFourCoeffs,
    Fin.sum_univ_four, ccmSmallSupportBump_im]

theorem ccmPoleFreeFourPacket_odd (L x : ℝ) :
    ccmPoleFreeFourPacket L (-x) = -ccmPoleFreeFourPacket L x := by
  simp only [ccmPoleFreeFourPacket, ccmPoleFreeFourPacketOf, ccmMultiPacket_apply,
    ccmPoleFreeFourCoeffs, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, ccmBasePoleNode_zero, ccmBasePoleNode_one,
    show ccmBasePoleNode 2 = 2 from ccmBasePoleNode_two,
    show ccmBasePoleNode 3 = -2 from ccmBasePoleNode_three]
  have h1 : ccmSmallSupportBump (-x - (1 : ℝ) * L) = ccmSmallSupportBump (x - (-1 : ℝ) * L) := by
    rw [show -x - (1 : ℝ) * L = -(x - (-1 : ℝ) * L) by ring, ccmSmallSupportBump_even]
  have h2 : ccmSmallSupportBump (-x - (-1 : ℝ) * L) = ccmSmallSupportBump (x - (1 : ℝ) * L) := by
    rw [show -x - (-1 : ℝ) * L = -(x - (1 : ℝ) * L) by ring, ccmSmallSupportBump_even]
  have h3 : ccmSmallSupportBump (-x - (2 : ℝ) * L) = ccmSmallSupportBump (x - (-2 : ℝ) * L) := by
    rw [show -x - (2 : ℝ) * L = -(x - (-2 : ℝ) * L) by ring, ccmSmallSupportBump_even]
  have h4 : ccmSmallSupportBump (-x - (-2 : ℝ) * L) = ccmSmallSupportBump (x - (2 : ℝ) * L) := by
    rw [show -x - (-2 : ℝ) * L = -(x - (2 : ℝ) * L) by ring, ccmSmallSupportBump_even]
  rw [h1, h2, h3, h4]
  ring

theorem two_le_sum_norm_sq_ccmPoleFreeFourCoeffs (L : ℝ) :
    2 ≤ ∑ i : Fin 4, ‖ccmPoleFreeFourCoeffs L i‖ ^ 2 := by
  simp only [ccmPoleFreeFourCoeffs, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, norm_one, norm_neg, one_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have := sq_nonneg (ccmPoleFreeWeight L)
  linarith

/-- Integer dyadic-scale nodes `4^k · α_j ∈ {± 2^{2k}, ± 2^{2k+1}}` (`k < d`, `j < 4`). -/
def ccmDyadicPoleIntNodes (d : ℕ) : Fin d × Fin 4 → ℤ :=
  fun p => (4 : ℤ) ^ (p.1 : ℕ) * ccmBasePoleIntNode p.2

/-- Real dyadic-scale nodes `4^k · α_j` (`k < d`, `j < 4`). -/
def ccmDyadicPoleNodes (d : ℕ) : Fin d × Fin 4 → ℝ :=
  fun p => (4 : ℝ) ^ (p.1 : ℕ) * ccmBasePoleNode p.2

theorem ccmDyadicPoleNodes_eq_intCast (d : ℕ) (p : Fin d × Fin 4) :
    ccmDyadicPoleNodes d p = (ccmDyadicPoleIntNodes d p : ℝ) := by
  simp [ccmDyadicPoleNodes, ccmDyadicPoleIntNodes, ccmBasePoleNode]

theorem injective_ccmDyadicPoleIntNodes (d : ℕ) :
    Function.Injective (ccmDyadicPoleIntNodes d) := by
  rintro ⟨k₁, j₁⟩ ⟨k₂, j₂⟩ heq
  have hpow2 : ∀ k : ℕ, (4 : ℤ) ^ k = (2 : ℤ) ^ (2 * k) := fun k => by
    rw [show (4 : ℤ) = (2 : ℤ) ^ 2 by norm_num, ← pow_mul]
  have h2inj : Function.Injective (fun n : ℕ => (2 : ℤ) ^ n) :=
    (pow_right_strictMono₀ (by norm_num : (1 : ℤ) < 2)).injective
  have hp1 : 0 < (2 : ℤ) ^ (2 * (k₁ : ℕ)) := by positivity
  have hp2 : 0 < (2 : ℤ) ^ (2 * (k₂ : ℕ)) := by positivity
  simp only [ccmDyadicPoleIntNodes, hpow2] at heq
  fin_cases j₁ <;> fin_cases j₂ <;>
    dsimp [ccmBasePoleIntNode] at heq
  · rw [mul_one, mul_one] at heq
    have hk := h2inj heq
    have hk_eq : k₁ = k₂ := Fin.ext (by omega)
    subst hk_eq
    exact Prod.ext rfl (Fin.ext rfl)
  · linarith
  · rw [mul_one, ← pow_succ] at heq
    have hk := h2inj heq
    omega
  · linarith
  · linarith
  · have hneg : (2 : ℤ) ^ (2 * (k₁ : ℕ)) = (2 : ℤ) ^ (2 * (k₂ : ℕ)) := by linarith
    have hk := h2inj hneg
    have hk_eq : k₁ = k₂ := Fin.ext (by omega)
    subst hk_eq
    exact Prod.ext rfl (Fin.ext rfl)
  · linarith
  · have hneg : (2 : ℤ) ^ (2 * (k₁ : ℕ)) = (2 : ℤ) ^ (2 * (k₂ : ℕ)) * 2 := by linarith
    rw [← pow_succ] at hneg
    have hk := h2inj hneg
    omega
  · rw [mul_one, ← pow_succ] at heq
    have hk := h2inj heq
    omega
  · linarith
  · rw [← pow_succ, ← pow_succ] at heq
    have hk := h2inj heq
    have hk_eq : k₁ = k₂ := Fin.ext (by omega)
    subst hk_eq
    exact Prod.ext rfl (Fin.ext rfl)
  · linarith
  · linarith
  · have hneg : (2 : ℤ) ^ (2 * (k₁ : ℕ)) * 2 = (2 : ℤ) ^ (2 * (k₂ : ℕ)) := by linarith
    rw [← pow_succ] at hneg
    have hk := h2inj hneg
    omega
  · linarith
  · have hneg : (2 : ℤ) ^ (2 * (k₁ : ℕ)) * 2 = (2 : ℤ) ^ (2 * (k₂ : ℕ)) * 2 := by linarith
    rw [← pow_succ, ← pow_succ] at hneg
    have hk := h2inj hneg
    have hk_eq : k₁ = k₂ := Fin.ext (by omega)
    subst hk_eq
    exact Prod.ext rfl (Fin.ext rfl)

theorem injective_ccmDyadicPoleNodes (d : ℕ) :
    Function.Injective (ccmDyadicPoleNodes d) := by
  intro p q hpq
  rw [ccmDyadicPoleNodes_eq_intCast, ccmDyadicPoleNodes_eq_intCast] at hpq
  exact injective_ccmDyadicPoleIntNodes d (Int.cast_injective hpq)

theorem one_le_abs_sub_ccmDyadicPoleNodes {d : ℕ} {p q : Fin d × Fin 4} (hpq : p ≠ q) :
    1 ≤ |ccmDyadicPoleNodes d q - ccmDyadicPoleNodes d p| := by
  rw [ccmDyadicPoleNodes_eq_intCast, ccmDyadicPoleNodes_eq_intCast, ← Int.cast_sub, ← Int.cast_abs]
  have hne : ccmDyadicPoleIntNodes d q - ccmDyadicPoleIntNodes d p ≠ 0 :=
    sub_ne_zero.mpr fun h => hpq (injective_ccmDyadicPoleIntNodes d h).symm
  exact_mod_cast Int.one_le_abs hne

/-- Combined `4d`-packet coefficients representing `∑_{k < d} w_k · g_{4^k L}`. -/
def ccmDyadicPoleCoeffs {d : ℕ} (w : Fin d → ℂ) (L : ℝ) : Fin d × Fin 4 → ℂ :=
  fun p => w p.1 * ccmPoleFreeFourCoeffs ((4 : ℝ) ^ (p.1 : ℕ) * L) p.2

/-- Linear combination `x ↦ ∑_{k < d} w_k · ccmPoleFreeFourPacketOf φ (4^k L) x` packaged as a
single `ccmMultiPacket` over `Fin d × Fin 4`. -/
def ccmPoleFreeComboOf (φ : CCMCompactSchwartzLogTest) {d : ℕ} (w : Fin d → ℂ) (L : ℝ) :
    CCMCompactSchwartzLogTest :=
  ccmMultiPacket φ (ccmDyadicPoleNodes d) (ccmDyadicPoleCoeffs w L) L

abbrev ccmPoleFreeCombo {d : ℕ} (w : Fin d → ℂ) (L : ℝ) : CCMCompactSchwartzLogTest :=
  ccmPoleFreeComboOf ccmSmallSupportBump w L

theorem ccmPoleFreeComboOf_apply (φ : CCMCompactSchwartzLogTest) {d : ℕ} (w : Fin d → ℂ)
    (L x : ℝ) :
    ccmPoleFreeComboOf φ w L x =
      ∑ k : Fin d, w k * ccmPoleFreeFourPacketOf φ ((4 : ℝ) ^ (k : ℕ) * L) x := by
  simp only [ccmPoleFreeComboOf, ccmPoleFreeFourPacketOf, ccmMultiPacket_apply,
    ccmDyadicPoleCoeffs, ccmDyadicPoleNodes, Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

theorem ccmPoleFreeComboOf_eval_node {φ : CCMCompactSchwartzLogTest} (hφ0 : φ 0 = 1)
    {d : ℕ} (w : Fin d → ℂ) {L : ℝ} (hL : φ.radius ≤ L) (k : Fin d) :
    ccmPoleFreeComboOf φ w L ((4 : ℝ) ^ (k : ℕ) * L) = w k := by
  have hL_pos : 0 < L := (zero_lt_one.trans φ.one_lt_radius).trans_le hL
  simp only [ccmPoleFreeComboOf, ccmMultiPacket_apply]
  rw [Finset.sum_eq_single (k, (0 : Fin 4))]
  · simp [ccmDyadicPoleCoeffs, ccmPoleFreeFourCoeffs, ccmDyadicPoleNodes, hφ0]
  · intro p _ hp
    have hsep := one_le_abs_sub_ccmDyadicPoleNodes hp.symm
    have hnode : ccmDyadicPoleNodes d (k, (0 : Fin 4)) = (4 : ℝ) ^ (k : ℕ) := by
      simp [ccmDyadicPoleNodes]
    rw [hnode, abs_sub_comm] at hsep
    have hrad : φ.radius ≤ |(4 : ℝ) ^ (k : ℕ) * L - ccmDyadicPoleNodes d p * L| := by
      rw [← sub_mul, abs_mul, abs_of_pos hL_pos]
      calc φ.radius = 1 * φ.radius := (one_mul _).symm
        _ ≤ |(4 : ℝ) ^ (k : ℕ) - ccmDyadicPoleNodes d p| * L :=
            mul_le_mul hsep hL (zero_lt_one.trans φ.one_lt_radius).le (abs_nonneg _)
    rw [φ.eq_zero_of_radius_le_abs _ hrad, mul_zero]
  · intro hnot; exact absurd (Finset.mem_univ _) hnot

theorem ccmPoleFreeComboOf_integral_eq_zero (φ : CCMCompactSchwartzLogTest) {d : ℕ}
    (w : Fin d → ℂ) (L : ℝ) :
    ∫ x : ℝ, ccmPoleFreeComboOf φ w L x = 0 := by
  simp_rw [ccmPoleFreeComboOf_apply]
  rw [integral_finsetSum Finset.univ fun (k : Fin d) _ =>
    (ccmPoleFreeFourPacketOf φ ((4 : ℝ) ^ (k : ℕ) * L)).toSchwartzMap.integrable.const_mul (w k)]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_const_mul, ccmPoleFreeFourPacketOf_integral_eq_zero, mul_zero]

theorem ccmPoleFreeComboOf_integral_exp_half_eq_zero (φ : CCMCompactSchwartzLogTest) {d : ℕ}
    (w : Fin d → ℂ) (L : ℝ) :
    ∫ x : ℝ, ccmPoleFreeComboOf φ w L x * ((Real.exp (x / 2) : ℝ) : ℂ) = 0 := by
  have hcont : Continuous (fun x : ℝ => ((Real.exp (x / 2) : ℝ) : ℂ)) := by fun_prop
  simp_rw [ccmPoleFreeComboOf_apply, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum Finset.univ fun (k : Fin d) _ =>
    (integrable_compactSchwartz_mul_continuous
      (ccmPoleFreeFourPacketOf φ ((4 : ℝ) ^ (k : ℕ) * L)) hcont).const_mul (w k)]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_const_mul, ccmPoleFreeFourPacketOf_integral_exp_half_eq_zero, mul_zero]

theorem ccmPoleFreeComboOf_integral_exp_neg_half_eq_zero (φ : CCMCompactSchwartzLogTest) {d : ℕ}
    (w : Fin d → ℂ) (L : ℝ) :
    ∫ x : ℝ, ccmPoleFreeComboOf φ w L x * ((Real.exp (-(x / 2)) : ℝ) : ℂ) = 0 := by
  have hcont : Continuous (fun x : ℝ => ((Real.exp (-(x / 2)) : ℝ) : ℂ)) := by fun_prop
  simp_rw [ccmPoleFreeComboOf_apply, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum Finset.univ fun (k : Fin d) _ =>
    (integrable_compactSchwartz_mul_continuous
      (ccmPoleFreeFourPacketOf φ ((4 : ℝ) ^ (k : ℕ) * L)) hcont).const_mul (w k)]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_const_mul, ccmPoleFreeFourPacketOf_integral_exp_neg_half_eq_zero, mul_zero]

/-- Uniform negative upper bound on `Re Tr(ϑ(ccmPoleFreeComboOf φ w L) G_1 ϑ(...)†)` across the
entire `d`-dimensional subspace `w : Fin d → ℂ` once `Q_{τ_1}(φ) < 0` and `L ≥ L₀`. -/
theorem exists_ccmPoleFreeComboOf_toeplitz_one_le {φ : CCMCompactSchwartzLogTest}
    (hφ_neg : (∫ s, ∫ t, conj (φ s) * φ t * ccmSoninToeplitzKernel 1 (t - s)).re < 0)
    (d : ℕ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ w : Fin d → ℂ,
      (opTrace (ϑ[(ccmPoleFreeComboOf φ w L).toSchwartzMap] ∘L ccmSoninGenericPartAt 1 ∘L
        ϑ†[(ccmPoleFreeComboOf φ w L).toSchwartzMap])).re ≤
      (∑ k : Fin d, ‖w k‖ ^ 2) *
        (∫ s, ∫ t, conj (φ s) * φ t * ccmSoninToeplitzKernel 1 (t - s)).re := by
  set Q₁ := (∫ s, ∫ t, conj (φ s) * φ t * ccmSoninToeplitzKernel 1 (t - s)).re
  have hη : 0 < (-Q₁) / 2 := by linarith
  obtain ⟨L₀, hL₀_pos, hdec⟩ := norm_toeplitz_ccmMultiPacket_sub_le φ
    (injective_ccmDyadicPoleNodes d)
    (continuous_ccmSoninToeplitzKernel one_pos)
    (norm_ccmSoninToeplitzKernel_le one_pos)
    (tendsto_ccmSoninToeplitzKernel_atTop one_pos)
    (tendsto_ccmSoninToeplitzKernel_atBot one_pos) hη
  refine ⟨L₀, hL₀_pos, fun L hL w => ?_⟩
  rw [opTrace_ccmSoninGenericPartAt_eq_toeplitz _ one_pos]
  set S := ∑ p : Fin d × Fin 4, ‖ccmDyadicPoleCoeffs w L p‖ ^ 2
  have hS_ge : 2 * (∑ k : Fin d, ‖w k‖ ^ 2) ≤ S := by
    have hS_eq : S = ∑ k : Fin d, ‖w k‖ ^ 2 *
        (∑ j : Fin 4, ‖ccmPoleFreeFourCoeffs ((4 : ℝ) ^ (k : ℕ) * L) j‖ ^ 2) := by
      dsimp only [S, ccmDyadicPoleCoeffs]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp_rw [norm_mul, mul_pow]
      rw [← Finset.mul_sum]
    rw [hS_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [mul_comm 2]
    exact mul_le_mul_of_nonneg_left
      (two_le_sum_norm_sq_ccmPoleFreeFourCoeffs _) (sq_nonneg _)
  have hbound := (Complex.abs_re_le_norm _).trans (hdec L hL (ccmDyadicPoleCoeffs w L))
  have hre_diff :
      (∫ s, ∫ t, conj (ccmPoleFreeComboOf φ w L s) * ccmPoleFreeComboOf φ w L t *
        ccmSoninToeplitzKernel 1 (t - s)).re - S * Q₁ ≤ ((-Q₁) / 2) * S := by
    have hupper := (abs_le.mp hbound).2
    change ((∫ s, ∫ t, conj (ccmPoleFreeComboOf φ w L s) * ccmPoleFreeComboOf φ w L t *
        ccmSoninToeplitzKernel 1 (t - s)) -
      (S : ℂ) * (∫ s, ∫ t, conj (φ s) * φ t * ccmSoninToeplitzKernel 1 (t - s))).re ≤
        ((-Q₁) / 2) * S at hupper
    simpa only [Q₁, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hupper
  have h1 : S * (Q₁ / 2) ≤ (∑ k : Fin d, ‖w k‖ ^ 2) * Q₁ := by
    nlinarith [hS_ge, hφ_neg]
  linarith

/-- **Unconditional Large-Support Refutation on Real Odd Mean-Zero Double-Pole-Free Tests.**
Even when `g` is real, odd, mean-zero (`∫ g = 0`), and satisfies both Weil polar vanishing
conditions (`∫ g(x) e^{x/2} dx = ∫ g(x) e^{-x/2} dx = 0`), Connes–Consani Sonin-trace domination
at cutoff `1` strictly fails on `ccmPoleFreeFourPacket L` for all sufficiently large `L`. -/
theorem not_ccmSoninTraceDomination_odd_meanZero_poleFree :
    ∀ᶠ L : ℝ in atTop,
      (∀ x : ℝ, (ccmPoleFreeFourPacket L x).im = 0) ∧
      (∀ x : ℝ, ccmPoleFreeFourPacket L (-x) = -ccmPoleFreeFourPacket L x) ∧
      (∫ x : ℝ, ccmPoleFreeFourPacket L x = 0) ∧
      (∫ x : ℝ, ccmPoleFreeFourPacket L x * ((Real.exp (x / 2) : ℝ) : ℂ) = 0) ∧
      (∫ x : ℝ, ccmPoleFreeFourPacket L x * ((Real.exp (-(x / 2)) : ℝ) : ℂ) = 0) ∧
      (-ccmArchimedeanWeilDistribution (ccmSoninGramTest (ccmPoleFreeFourPacket L))).re <
        (opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel
          (ccmSoninGramTest (ccmPoleFreeFourPacket L)).toSchwartzMap) *
          evenCentralSoninProjection 1)).re := by
  obtain ⟨L₀, _, hle⟩ := exists_ccmPoleFreeComboOf_toeplitz_one_le
    re_toeplitz_ccmSmallSupportBump_neg 1
  filter_upwards [eventually_ge_atTop L₀] with L hL
  refine ⟨ccmPoleFreeFourPacket_im L, ccmPoleFreeFourPacket_odd L,
    ccmPoleFreeFourPacketOf_integral_eq_zero ccmSmallSupportBump L,
    ccmPoleFreeFourPacketOf_integral_exp_half_eq_zero ccmSmallSupportBump L,
    ccmPoleFreeFourPacketOf_integral_exp_neg_half_eq_zero ccmSmallSupportBump L, ?_⟩
  rw [← not_le, ccmSoninTraceDomination_iff_toeplitz, not_le]
  have h1 := hle L hL ![1]
  rw [opTrace_ccmSoninGenericPartAt_eq_toeplitz _ one_pos] at h1
  have heq : ∀ x : ℝ, ccmPoleFreeCombo ![1] L x = ccmPoleFreeFourPacket L x := by
    intro x
    simp [ccmPoleFreeCombo, ccmPoleFreeComboOf_apply, ccmPoleFreeFourPacket]
  simp_rw [heq] at h1
  have hsum1 : (∑ k : Fin 1, ‖(![(1 : ℂ)] : Fin 1 → ℂ) k‖ ^ 2) = 1 := by simp
  rw [hsum1, one_mul] at h1
  exact h1.trans_lt re_toeplitz_ccmSmallSupportBump_neg

/-- **Infinite Negative Morse Index at Cutoff `Λ = 1` on Double-Pole-Free Compact Schwartz Tests.**
For every dimension `d : ℕ`, there exists a `d`-tuple of linearly independent mean-zero
double-pole-free compact Schwartz tests `ψ : Fin d → CCMCompactSchwartzLogTest` such that every
nonzero linear combination `ccmPoleFreeCombo w L` strictly violates cutoff-`1` Sonin-trace
domination. -/
theorem exists_linearIndependent_poleFree_negative_soninCone (d : ℕ) :
    ∃ L : ℝ, 0 < L ∧
      LinearIndependent ℂ
        (fun k : Fin d => (fun x : ℝ => ccmPoleFreeFourPacket ((4 : ℝ) ^ (k : ℕ) * L) x)) ∧
      ∀ w : Fin d → ℂ, w ≠ 0 →
        (∫ x : ℝ, ccmPoleFreeCombo w L x = 0) ∧
        (∫ x : ℝ, ccmPoleFreeCombo w L x * ((Real.exp (x / 2) : ℝ) : ℂ) = 0) ∧
        (∫ x : ℝ, ccmPoleFreeCombo w L x * ((Real.exp (-(x / 2)) : ℝ) : ℂ) = 0) ∧
        (-ccmArchimedeanWeilDistribution (ccmSoninGramTest (ccmPoleFreeCombo w L))).re <
          (opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel
            (ccmSoninGramTest (ccmPoleFreeCombo w L)).toSchwartzMap) *
            evenCentralSoninProjection 1)).re := by
  obtain ⟨L₀, hL₀_pos, hle⟩ := exists_ccmPoleFreeComboOf_toeplitz_one_le
    re_toeplitz_ccmSmallSupportBump_neg d
  set L := max L₀ ccmSmallSupportBump.radius
  have hL_pos : 0 < L := hL₀_pos.trans_le (le_max_left _ _)
  refine ⟨L, hL_pos, ?_, fun w hw => ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro w hw k
    have heval := congrFun hw ((4 : ℝ) ^ (k : ℕ) * L)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at heval
    rw [← ccmPoleFreeComboOf_apply ccmSmallSupportBump w L,
      ccmPoleFreeComboOf_eval_node ccmSmallSupportBump_zero w (le_max_right _ _) k] at heval
    exact heval
  · refine ⟨ccmPoleFreeComboOf_integral_eq_zero _ w L,
      ccmPoleFreeComboOf_integral_exp_half_eq_zero _ w L,
      ccmPoleFreeComboOf_integral_exp_neg_half_eq_zero _ w L, ?_⟩
    rw [← not_le, ccmSoninTraceDomination_iff_toeplitz,
      ← opTrace_ccmSoninGenericPartAt_eq_toeplitz _ one_pos, not_le]
    have hw_ne : ∃ k : Fin d, w k ≠ 0 := by
      by_contra hall; push Not at hall; exact hw (funext hall)
    obtain ⟨k₀, hk₀⟩ := hw_ne
    have hsum_pos : 0 < ∑ k : Fin d, ‖w k‖ ^ 2 :=
      lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hk₀))
        (Finset.single_le_sum (fun k _ => sq_nonneg ‖w k‖) (Finset.mem_univ k₀))
    exact (hle L (le_max_left _ _) w).trans_lt
      (mul_neg_of_pos_of_neg hsum_pos re_toeplitz_ccmSmallSupportBump_neg)

/-- **Failure of Cutoff-`1` Sonin-Trace Domination on Every Finite-Codimension Moment Subspace.**
For any `m : ℕ` and any `m` continuous weight functions `Φ : Fin m → ℝ → ℂ`, there exists a
nonzero compact Schwartz test `g` satisfying `∫ g = 0`, `∫ g(x) e^{x/2} dx = 0`,
`∫ g(x) e^{-x/2} dx = 0`, and `∀ j : Fin m, ∫ g(x) Φ_j(x) dx = 0`, on which cutoff-`1`
Sonin-trace domination strictly fails. -/
theorem exists_poleFree_zeroMoments_not_ccmSoninTraceDomination
    {m : ℕ} {Φ : Fin m → ℝ → ℂ} (hΦ : ∀ j : Fin m, Continuous (Φ j)) :
    ∃ g : CCMCompactSchwartzLogTest,
      (∃ x : ℝ, g x ≠ 0) ∧
      (∫ x : ℝ, g x = 0) ∧
      (∫ x : ℝ, g x * ((Real.exp (x / 2) : ℝ) : ℂ) = 0) ∧
      (∫ x : ℝ, g x * ((Real.exp (-(x / 2)) : ℝ) : ℂ) = 0) ∧
      (∀ j : Fin m, ∫ x : ℝ, g x * Φ j x = 0) ∧
      (-ccmArchimedeanWeilDistribution (ccmSoninGramTest g)).re <
        (opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel (ccmSoninGramTest g).toSchwartzMap) *
          evenCentralSoninProjection 1)).re := by
  obtain ⟨L, _, hli, hneg⟩ := exists_linearIndependent_poleFree_negative_soninCone (m + 1)
  set ψ : Fin (m + 1) → CCMCompactSchwartzLogTest :=
    fun k => ccmPoleFreeFourPacket ((4 : ℝ) ^ (k : ℕ) * L)
  let col : Fin (m + 1) → Fin m → ℂ :=
    fun k j => ∫ x : ℝ, ψ k x * Φ j x
  have hnot_li : ¬ LinearIndependent ℂ col := by
    intro hcol_li
    have hcard := hcol_li.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_pi] at hcard
    omega
  rw [Fintype.not_linearIndependent_iff] at hnot_li
  obtain ⟨w, hw_sum, k₀, hwk₀⟩ := hnot_li
  have hw_ne : w ≠ 0 := fun h0 => hwk₀ (congrFun h0 k₀)
  refine ⟨ccmPoleFreeCombo w L, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hzero_fun : (∑ k : Fin (m + 1), w k • (fun x : ℝ => ψ k x)) = 0 := by
      ext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← ccmPoleFreeComboOf_apply ccmSmallSupportBump w L]
      exact hall x
    exact hwk₀ (Fintype.linearIndependent_iff.mp hli w hzero_fun k₀)
  · obtain ⟨hm0, hp1, hp2, hdom⟩ := hneg w hw_ne
    refine ⟨hm0, hp1, hp2, fun j => ?_, hdom⟩
    have hj := congrFun hw_sum j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, col] at hj
    simp_rw [ccmPoleFreeCombo, ccmPoleFreeComboOf_apply, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum Finset.univ fun (k : Fin (m + 1)) _ =>
      (integrable_compactSchwartz_mul_continuous (ψ k) (hΦ j)).const_mul (w k)]
    simp_rw [integral_const_mul]
    exact hj

/-! ## Section 4: Sharp Positive Survivor at Cutoffs `Λ > 1` and the Cutoff-`1` vs. Cutoff-`Λ > 1` Dichotomy -/

/-- **Uniform Multi-Packet Sonin-Trace Domination at Every Cutoff `Λ > 1`.**
At any cutoff `Λ > 1`, let `g₀ : CCMCompactSchwartzLogTest` vanish outside `(-ε, ε)` with
`0 < ε < log Λ / (‖G_Λ‖_1 + 1)`. Then for every finite index type `ι` and every injective node
configuration `α : ι → ℝ`, there exists `L₀ > 0` such that for all `L ≥ L₀` and **every**
coefficient vector `c : ι → ℂ`, `ccmMultiPacket g₀ α c L` satisfies Connes–Consani Sonin-trace
domination at cutoff `Λ` (with no moment condition required on `g₀` or `c`). -/
theorem exists_multiPacket_ccmSoninTraceDomination_cutoffAt {ι : Type*} [Fintype ι]
    {Λ : ℝ} (hΛ : 1 < Λ) {α : ι → ℝ} (hinj : Function.Injective α)
    (g₀ : CCMCompactSchwartzLogTest) {ε : ℝ} (hε : 0 < ε)
    (hε_lt : ε < Real.log Λ / (traceNorm evenSubspace (ccmSoninGenericPartAt Λ) + 1))
    (hg₀ : ∀ x : ℝ, ε ≤ |x| → g₀ x = 0) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ c : ι → ℂ,
      (opTrace (ϑ[(ccmMultiPacket g₀ α c L).toSchwartzMap] ∘L
          evenCentralSoninProjection Λ ∘L
          ϑ†[(ccmMultiPacket g₀ α c L).toSchwartzMap])).re ≤
        (-ccmArchimedeanWeilDistribution (ccmSoninGramTest (ccmMultiPacket g₀ α c L))).re := by
  have hΛ0 : 0 < Λ := zero_lt_one.trans hΛ
  set B := ∫ x : ℝ, ‖g₀ x‖ ^ 2
  have hB_nn : 0 ≤ B := integral_nonneg fun _ => sq_nonneg _
  rcases eq_or_lt_of_le hB_nn with hB0 | hB_pos
  · -- Degenerate case `g₀ ≡ 0`: every `ccmMultiPacket g₀ α c L` is identically zero.
    have hg₀_zero : ∀ x : ℝ, g₀ x = 0 := by
      have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖g₀ x‖)
        ((g₀.toSchwartzMap.memLp 2 volume).integrable_norm_pow (by norm_num))).mp hB0.symm
      have hcont : Continuous (fun x : ℝ => ‖g₀ x‖ ^ 2) :=
        g₀.toSchwartzMap.continuous.norm.pow 2
      have hfun := hcont.ae_eq_iff_eq volume continuous_const |>.mp hae
      intro x
      have hx0 : ‖g₀ x‖ ^ 2 = 0 := congrFun hfun x
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx0)
    refine ⟨1, one_pos, fun L _ c => ?_⟩
    apply ccmSoninTraceDomination_cutoffAt_of_traceNorm _ hΛ
    have hall0 : ∀ x : ℝ, ccmMultiPacket g₀ α c L x = 0 := fun x => by
      simp [hg₀_zero]
    simp [hall0]
  · -- Nonzero profile `B > 0`: single-packet shell margin `μ₀ > 0` absorbs off-diagonal tails.
    set τ_norm := traceNorm evenSubspace (ccmSoninGenericPartAt Λ)
    have hτ_nn : 0 ≤ τ_norm := traceNorm_nonneg _
    have hετ_lt : ε * τ_norm < Real.log Λ := by
      have h1 : ε * (τ_norm + 1) < Real.log Λ :=
        (lt_div_iff₀ (by linarith)).mp hε_lt
      nlinarith
    set μ₀ := (2 * Real.log Λ - 2 * ε * τ_norm) * B
    have hμ₀_pos : 0 < μ₀ := mul_pos (by linarith) hB_pos
    set Q_Λ := (∫ s, ∫ t, conj (g₀ s) * g₀ t * ccmSoninToeplitzKernel Λ (t - s)).re
    have hsingle : μ₀ ≤ 2 * Real.log Λ * B + Q_Λ := by
      have hnorm := norm_opTrace_ccmSoninGenericPartAt_le g₀.toSchwartzMap hΛ0
      rw [opTrace_ccmSoninGenericPartAt_eq_toeplitz g₀ hΛ0] at hnorm
      have hcs := sq_integral_norm_le_of_support g₀.toSchwartzMap hε hg₀
      have hQ_abs : -Q_Λ ≤ τ_norm * (2 * ε * B) := by
        have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
        have h2 : τ_norm * (∫ x, ‖g₀ x‖) ^ 2 ≤ τ_norm * (2 * ε * B) :=
          mul_le_mul_of_nonneg_left hcs hτ_nn
        linarith
      unfold μ₀
      linarith
    obtain ⟨L₁, hL₁_pos, hdec⟩ := norm_toeplitz_ccmMultiPacket_sub_le g₀ hinj
      (continuous_ccmSoninToeplitzKernel hΛ0)
      (norm_ccmSoninToeplitzKernel_le hΛ0)
      (tendsto_ccmSoninToeplitzKernel_atTop hΛ0)
      (tendsto_ccmSoninToeplitzKernel_atBot hΛ0)
      (half_pos hμ₀_pos)
    obtain ⟨L₂, hL₂_pos, hnorm_eq⟩ := integral_norm_sq_ccmMultiPacket_eq g₀ hinj
    refine ⟨max L₁ L₂, hL₁_pos.trans_le (le_max_left _ _), fun L hL c => ?_⟩
    rw [ccmSoninTraceDomination_cutoffAt_iff _ hΛ,
      opTrace_ccmSoninGenericPartAt_eq_toeplitz _ hΛ0,
      hnorm_eq L ((le_max_right _ _).trans hL) c]
    set S := ∑ i : ι, ‖c i‖ ^ 2
    have hS_nn : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hbound := (Complex.abs_re_le_norm _).trans (hdec L ((le_max_left _ _).trans hL) c)
    have hre_ge : S * Q_Λ - μ₀ / 2 * S ≤
        (∫ s, ∫ t, conj (ccmMultiPacket g₀ α c L s) * ccmMultiPacket g₀ α c L t *
          ccmSoninToeplitzKernel Λ (t - s)).re := by
      have hlower := (abs_le.mp hbound).1
      change -(μ₀ / 2 * S) ≤
        ((∫ s, ∫ t, conj (ccmMultiPacket g₀ α c L s) * ccmMultiPacket g₀ α c L t *
            ccmSoninToeplitzKernel Λ (t - s)) -
          (S : ℂ) * (∫ s, ∫ t, conj (g₀ s) * g₀ t * ccmSoninToeplitzKernel Λ (t - s))).re at hlower
      have h' : -(μ₀ / 2 * S) ≤
          (∫ s, ∫ t, conj (ccmMultiPacket g₀ α c L s) * ccmMultiPacket g₀ α c L t *
            ccmSoninToeplitzKernel Λ (t - s)).re - S * Q_Λ := by
        simpa only [Q_Λ, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero] using hlower
      linarith
    have hmargin : 0 ≤ S * (2 * Real.log Λ * B + Q_Λ - μ₀ / 2) :=
      mul_nonneg hS_nn (by linarith)
    linarith

private theorem exists_small_bump_neg_toeplitz_one {ε : ℝ} (hε_pos : 0 < ε)
    (hε_le_one : ε ≤ ccmSoninSmallSupportRadius) :
    ∃ φ : CCMCompactSchwartzLogTest,
      (∀ x : ℝ, ε ≤ |x| → φ x = 0) ∧
      φ 0 = 1 ∧
      (∫ s, ∫ t, conj (φ s) * φ t * ccmSoninToeplitzKernel 1 (t - s)).re < 0 := by
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt (1 / (4 * ε))
  have hr_lt : 1 / (4 * ((j₀ : ℝ) + 1)) < ε := by
    have h1 : 1 / (4 * ε) < (j₀ : ℝ) + 1 := by linarith
    have h2 := (div_lt_iff₀ (by positivity : 0 < 4 * ε)).mp h1
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  let φ : CCMCompactSchwartzLogTest :=
    mkCCMCompactSchwartzLogTest
      (narrowBumpC j₀)
      (contDiff_narrowBumpC j₀)
      ε
      (fun x hx => narrowBumpC_eq_zero j₀ (lt_of_lt_of_le hr_lt hx))
  have hφ_supp : ∀ x : ℝ, ε ≤ |x| → φ x = 0 :=
    fun x hx => narrowBumpC_eq_zero j₀ (lt_of_lt_of_le hr_lt hx)
  have hφ0 : φ 0 = 1 := by
    change ((narrowBump j₀ 0 : ℝ) : ℂ) = 1
    rw [(narrowBump j₀).one_of_mem_closedBall
      (Metric.mem_closedBall_self (narrowBump j₀).rIn_pos.le)]
    norm_cast
  have hφ_neg : (∫ s, ∫ t, conj (φ s) * φ t * ccmSoninToeplitzKernel 1 (t - s)).re < 0 := by
    have hfail := not_ccmSoninTraceDomination_of_nonneg φ hε_pos hε_le_one hφ_supp
      (fun x => by simp [φ, narrowBumpC])
      (fun x => by simpa [φ, narrowBumpC] using (narrowBump j₀).nonneg' x)
      (x₀ := 0) (by rw [hφ0]; exact one_ne_zero)
    have hnot : ¬ (opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel
        (ccmSoninGramTest φ).toSchwartzMap) * evenCentralSoninProjection 1)).re ≤
        (-ccmArchimedeanWeilDistribution (ccmSoninGramTest φ)).re :=
      not_le.mpr hfail
    rwa [ccmSoninTraceDomination_iff_toeplitz, not_le] at hnot
  exact ⟨φ, hφ_supp, hφ0, hφ_neg⟩

private theorem exists_nonzero_ker_vec {d m : ℕ} (hd : m < d) (M : Fin d → Fin m → ℂ) :
    ∃ w : Fin d → ℂ, (∃ k : Fin d, w k ≠ 0) ∧ ∀ j : Fin m, ∑ k : Fin d, w k * M k j = 0 := by
  have hnot_li : ¬ LinearIndependent ℂ M := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_pi] at hcard
    omega
  rw [Fintype.not_linearIndependent_iff] at hnot_li
  obtain ⟨w, hw_sum, k₀, hwk₀⟩ := hnot_li
  refine ⟨w, ⟨k₀, hwk₀⟩, fun j => ?_⟩
  have hj := congrFun hw_sum j
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hj

private theorem exists_combo_dichotomy_of_profile {Λ : ℝ}
    (φ : CCMCompactSchwartzLogTest) (hφ0 : φ 0 = 1)
    (hφ_neg : (∫ s, ∫ t, conj (φ s) * φ t * ccmSoninToeplitzKernel 1 (t - s)).re < 0)
    {m : ℕ} {Φ : Fin m → ℝ → ℂ} (hΦ : ∀ j : Fin m, Continuous (Φ j))
    {L₂ : ℝ} (hdom_Λ : ∀ L : ℝ, L₂ ≤ L → ∀ c : Fin (m + 1) × Fin 4 → ℂ,
      (opTrace (ϑ[(ccmMultiPacket φ (ccmDyadicPoleNodes (m + 1)) c L).toSchwartzMap] ∘L
          evenCentralSoninProjection Λ ∘L
          ϑ†[(ccmMultiPacket φ (ccmDyadicPoleNodes (m + 1)) c L).toSchwartzMap])).re ≤
        (-ccmArchimedeanWeilDistribution
          (ccmSoninGramTest (ccmMultiPacket φ (ccmDyadicPoleNodes (m + 1)) c L))).re) :
    ∃ g : CCMCompactSchwartzLogTest,
      (∃ x : ℝ, g x ≠ 0) ∧
      (∫ x : ℝ, g x = 0) ∧
      (∫ x : ℝ, g x * ((Real.exp (x / 2) : ℝ) : ℂ) = 0) ∧
      (∫ x : ℝ, g x * ((Real.exp (-(x / 2)) : ℝ) : ℂ) = 0) ∧
      (∀ j : Fin m, ∫ x : ℝ, g x * Φ j x = 0) ∧
      (-ccmArchimedeanWeilDistribution (ccmSoninGramTest g)).re <
        (opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel (ccmSoninGramTest g).toSchwartzMap) *
          evenCentralSoninProjection 1)).re ∧
      (opTrace (ϑ[g.toSchwartzMap] ∘L evenCentralSoninProjection Λ ∘L
          ϑ†[g.toSchwartzMap])).re ≤
        (-ccmArchimedeanWeilDistribution (ccmSoninGramTest g)).re := by
  obtain ⟨L₁, _, hle_one⟩ := exists_ccmPoleFreeComboOf_toeplitz_one_le hφ_neg (m + 1)
  have hexL : ∃ L : ℝ, L₁ ≤ L ∧ L₂ ≤ L ∧ φ.radius ≤ L :=
    ⟨max (max L₁ L₂) φ.radius,
      (le_max_left L₁ L₂).trans (le_max_left _ _),
      (le_max_right L₁ L₂).trans (le_max_left _ _),
      le_max_right _ _⟩
  obtain ⟨L, hL₁_le, hL₂_le, hrad_le⟩ := hexL
  obtain ⟨w, ⟨k₀, hwk₀⟩, hw_ker⟩ := exists_nonzero_ker_vec (Nat.lt_succ_self m)
    (fun (k : Fin (m + 1)) (j : Fin m) =>
      ∫ x : ℝ, ccmPoleFreeFourPacketOf φ ((4 : ℝ) ^ (k : ℕ) * L) x * Φ j x)
  refine ⟨ccmPoleFreeComboOf φ w L,
    ⟨(4 : ℝ) ^ (k₀ : ℕ) * L, ?_⟩,
    ccmPoleFreeComboOf_integral_eq_zero φ w L,
    ccmPoleFreeComboOf_integral_exp_half_eq_zero φ w L,
    ccmPoleFreeComboOf_integral_exp_neg_half_eq_zero φ w L,
    fun j => ?_, ?_, hdom_Λ L hL₂_le (ccmDyadicPoleCoeffs w L)⟩
  · rw [ccmPoleFreeComboOf_eval_node hφ0 w hrad_le k₀]
    exact hwk₀
  · simp_rw [ccmPoleFreeComboOf_apply, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum Finset.univ fun (k : Fin (m + 1)) _ =>
      (integrable_compactSchwartz_mul_continuous
        (ccmPoleFreeFourPacketOf φ ((4 : ℝ) ^ (k : ℕ) * L)) (hΦ j)).const_mul (w k)]
    simp_rw [integral_const_mul]
    exact hw_ker j
  · rw [← not_le, ccmSoninTraceDomination_iff_toeplitz,
      ← opTrace_ccmSoninGenericPartAt_eq_toeplitz (ccmPoleFreeComboOf φ w L) one_pos, not_le]
    have hsum_pos : 0 < ∑ k : Fin (m + 1), ‖w k‖ ^ 2 :=
      lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hwk₀))
        (Finset.single_le_sum (fun k _ => sq_nonneg ‖w k‖) (Finset.mem_univ k₀))
    exact (hle_one L hL₁_le w).trans_lt (mul_neg_of_pos_of_neg hsum_pos hφ_neg)

/-- **Simultaneous Cutoff-`1` vs. Cutoff-`Λ > 1` Sonin-Trace Dichotomy.**
For **every** cutoff `Λ > 1`, every `m : ℕ`, and every `m` continuous moment weights
`Φ : Fin m → ℝ → ℂ`, there exists a single nonzero compact Schwartz test
`g : CCMCompactSchwartzLogTest` of arbitrarily large support separation satisfying:
1. `∫ g = 0`, `∫ g(x) e^{x/2} dx = 0`, `∫ g(x) e^{-x/2} dx = 0`, and
   `∀ j : Fin m, ∫ g(x) Φ_j(x) dx = 0`;
2. Cutoff-`1` Sonin-trace domination **strictly fails** on `g`;
3. Cutoff-`Λ` Sonin-trace domination **holds** on `g`. -/
theorem ccmSonin_cutoff_one_vs_gt_one_dichotomy {Λ : ℝ} (hΛ : 1 < Λ)
    {m : ℕ} {Φ : Fin m → ℝ → ℂ} (hΦ : ∀ j : Fin m, Continuous (Φ j)) :
    ∃ g : CCMCompactSchwartzLogTest,
      (∃ x : ℝ, g x ≠ 0) ∧
      (∫ x : ℝ, g x = 0) ∧
      (∫ x : ℝ, g x * ((Real.exp (x / 2) : ℝ) : ℂ) = 0) ∧
      (∫ x : ℝ, g x * ((Real.exp (-(x / 2)) : ℝ) : ℂ) = 0) ∧
      (∀ j : Fin m, ∫ x : ℝ, g x * Φ j x = 0) ∧
      (-ccmArchimedeanWeilDistribution (ccmSoninGramTest g)).re <
        (opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel (ccmSoninGramTest g).toSchwartzMap) *
          evenCentralSoninProjection 1)).re ∧
      (opTrace (ϑ[g.toSchwartzMap] ∘L evenCentralSoninProjection Λ ∘L
          ϑ†[g.toSchwartzMap])).re ≤
        (-ccmArchimedeanWeilDistribution (ccmSoninGramTest g)).re := by
  have hexε : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ccmSoninSmallSupportRadius ∧
      ε < Real.log Λ / (traceNorm evenSubspace (ccmSoninGenericPartAt Λ) + 1) := by
    have hquot_pos : 0 < Real.log Λ / (traceNorm evenSubspace (ccmSoninGenericPartAt Λ) + 1) :=
      div_pos (Real.log_pos hΛ)
        (add_pos_of_nonneg_of_pos (traceNorm_nonneg _) zero_lt_one)
    have hr_pos : 0 < min ccmSoninSmallSupportRadius
        (Real.log Λ / (traceNorm evenSubspace (ccmSoninGenericPartAt Λ) + 1)) :=
      lt_min ccmSoninSmallSupportRadius_pos hquot_pos
    exact ⟨min ccmSoninSmallSupportRadius
        (Real.log Λ / (traceNorm evenSubspace (ccmSoninGenericPartAt Λ) + 1)) / 2,
      half_pos hr_pos,
      (half_lt_self hr_pos).le.trans (min_le_left _ _),
      (half_lt_self hr_pos).trans_le (min_le_right _ _)⟩
  obtain ⟨ε, hε_pos, hε_le_one, hε_lt_Λ⟩ := hexε
  obtain ⟨φ_Λ, hφ_supp, hφ0, hφ_neg⟩ := exists_small_bump_neg_toeplitz_one hε_pos hε_le_one
  obtain ⟨L₂, _, hdom_Λ⟩ := exists_multiPacket_ccmSoninTraceDomination_cutoffAt hΛ
    (injective_ccmDyadicPoleNodes (m + 1)) φ_Λ hε_pos hε_lt_Λ hφ_supp
  exact exists_combo_dichotomy_of_profile φ_Λ hφ0 hφ_neg hΦ hdom_Λ

/-! ## Section 5: Operator-Ideal, Determinant, Calkin, and Scattering Constraints on Spectral Realisations -/

/-- **Complete Operator-Ideal, Calkin, Trace, and Scattering Constraint Package for Spectral
Realisations of `Ξ` and Euler Factors.**
Unconditionally establishes:
1. Every zero-free-gauge self-adjoint Hilbert–Carleman realisation `XiC z = H z * det_2(I - z K)`
   lies in `𝓢_q` for all `q > 1`, fails both `𝓢_1` and weak trace class `𝓢_{1,∞}`, belongs to the
   log-enhanced weak-trace ideal with universal residue `π⁻¹`, and satisfies
   `lim_{N → ∞} (∑_{n < N} s_n(K)) / (log(N + 1))² = 1 / (2π)`.
2. Every nonzero finite matrix combination of prime Euler Gram corners on `evenSubspace` or on
   `ArchimedeanWeightedL2` is noncompact (and its principal shell representative lies outside
   `IsSoninPrincipalRelativeIdeal`), whereas every operator in `IsSoninPrincipalRelativeIdeal`
   belongs to `𝓢_1(evenSubspace)`.
3. At every aperture `a > 0`, the raw linear-prime nuclear source has strictly positive harmonic
   trace coefficient and fails summability in `𝓢_1(SoninL2)`.
4. The Riemann–von Mangoldt remainder `S(T)` (`rvmRemainder`) is unconditionally unbounded.
5. Every unitary matrix `S ∈ U(n)` satisfying `det S = ∏_i S_{ii}` is strictly diagonal with
   unimodular diagonal entries `‖S_{ii}‖ = 1` (ruling out central `p^{-1/2}` Euler weights from
   coupled unitary producers). -/
theorem spectralRealisation_operator_ideal_and_scattering_constraints :
    (∀ {ι : Type*} [DecidableEq ι] {K : ι × ι → ℂ} (hK : IsHS K),
      IsSelfAdjoint (toOperator hK) →
      ∀ (H : ℂ → ℂ), Differentiable ℂ H → (∀ z : ℂ, H z ≠ 0) →
      (∀ z : ℂ, XiC z = H z * entireDet2 K z) →
        (∀ {q : ℝ}, 1 < q → MemSchattenClass q (toOperator hK)) ∧
        ¬ MemSchattenClass 1 (toOperator hK) ∧
        ¬ MemWeakSchattenClass 1 (toOperator hK) ∧
        MemLogEnhancedWeakTraceClass (toOperator hK) ∧
        HasLogEnhancedWeakTraceResidue (toOperator hK) Real.pi⁻¹ ∧
        Tendsto (fun N : ℕ =>
          (∑ n ∈ Finset.range N, approxNumber (toOperator hK) n) /
            Real.log ((N : ℝ) + 1) ^ (2 : ℕ)) atTop (𝓝 (1 / (2 * Real.pi)))) ∧
    ((∀ {T : evenSubspace →L[ℂ] evenSubspace},
        IsSoninPrincipalRelativeIdeal T → MemSchattenClass 1 T) ∧
      ∀ {n : ℕ} (a : ℝ), 0 < a → ∀ (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime),
        Function.Injective p → ∀ (A : Matrix (Fin n) (Fin n) ℂ), A ≠ 0 →
          ¬ IsCompactOperator
            (finiteEvenPositiveEulerGramCombination a (fun i => (p i : ℝ))
              (fun i => Nat.one_lt_cast.mpr (hp i).one_lt) A) ∧
          ¬ IsCompactOperator
            (finiteArchimedeanPrimeEulerGramCombination a (fun i => (p i : ℝ)) A) ∧
          ¬ IsSoninPrincipalRelativeIdeal
            (finitePrimeSoninPrincipalShellCombination a p hp A)) ∧
    (∀ (a : ℝ) (ha : 0 < a),
      0 < soninLinearPrimeTraceCoefficient a ∧
      ¬ Summable (soninLinearPrimeNuclearSource a ha)) ∧
    (∀ B T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ B < |rvmRemainder T|) ∧
    (∀ {n : Type*} [Fintype n] [DecidableEq n] {S : Matrix n n ℂ},
      S ∈ Matrix.unitaryGroup n ℂ → S.det = (∏ i, S i i) →
        (∀ i : n, ‖S i i‖ = 1) ∧ (∀ {i j : n}, i ≠ j → S i j = 0)) := by
  refine ⟨?_, ⟨fun hT => hT.memSchattenClass_one, ?_⟩,
    fun a ha => ⟨soninLinearPrimeTraceCoefficient_pos a ha,
      not_summable_soninLinearPrimeNuclearSource a ha⟩,
    rvmRemainder_unbounded,
    fun hS hdet => ⟨abs_diag_eq_one_of_det_eq_prod_diag hS hdet,
      fun hij => offDiag_eq_zero_of_det_eq_prod_diag hS hdet hij⟩⟩
  · intro ι _ K hK hself H hHdiff hHne hXi
    exact ⟨fun hq => exactXiDeterminant_memSchattenClass hK hself H hHdiff hHne hXi hq,
      exactXiDeterminant_not_memSchattenClass_one hK hself H hHdiff hHne hXi,
      exactXiDeterminant_not_memWeakSchattenClass_one hK hself H hHdiff hHne hXi,
      exactXiDeterminant_memLogEnhancedWeakTraceClass hK hself H hHdiff hHne hXi,
      exactXiDeterminant_hasLogEnhancedWeakTraceResidue hK hself H hHdiff hHne hXi,
      exactXiDeterminant_partialTrace_asymptotic hK hself H hHdiff hHne hXi⟩
  · intro n a ha p hp hinj A hA
    exact ⟨finitePrimeEvenPositiveEulerGram_not_isCompactOperator_of_ne_zero a ha p hp hinj A hA,
      finitePrimeArchimedeanEulerGram_not_isCompactOperator_of_ne_zero a ha p hp hinj A hA,
      finitePrimeSoninPrincipalShellCombination_not_mem_relativeIdeal_of_ne_zero a ha p hp hinj A hA⟩

/-! ## Section 6: Finite-Packet `D_log^{(λ,N)}` Dichotomy, Real-Rooted Ground States, and Receiver / Critical-Family Bridge -/

/-- **Synthesis of Finite-Packet `D_log^{(λ,N)}`, Unconstrained Real-Rooted Ground States,
`Ξ`-Free RH Forcing Criteria, and Unconditional Multi-Window Positivity.**
Unconditionally establishes:
1. At every aperture `a > 0` and mode cutoff `N`, the finite-packet CCM Theorem 5.10 dichotomy
   (`ccmPublished_logDirac_theorem`) holds unconditionally, and under a simple reflection-even
   kernel (`ccmPublished_logDirac_simpleEven`) selects the boundary branch with real-rooted packet
   transform and exact zeta-regularized determinant identity.
2. At every aperture `a : SuzukiPositiveAperture`, unconstrained full ground states with purely
   real-rooted Fourier–Laplace transforms unconditionally exist (`exists_realRooted_fullGround`),
   and `RiemannHypothesis` holds iff `ccmRestrictedWeilSourceQuadratic a u ≥ 0` on real-rooted
   form-domain vectors (`riemannHypothesis_iff_nonneg_on_realRooted`).
3. Both Gaussian-growth and real-line Poisson-balanced sequences of real-rooted full ground states
   as `a_j → +∞` unconditionally force `RiemannHypothesis` without assuming convergence to `Ξ`.
4. Across lacunary families of polynomial scale windows, all five explicit-formula / Weil /
   zero-configuration form realizations and their `gridTentPattern` / `smoothGridTentDetector`
   transfers are unconditionally strictly positive. -/
theorem ccmLogDirac_and_realRooted_ground_state_bridge :
    (∀ (a : ℝ), 0 < a → ∀ N : ℕ,
      (∃ ξ : Fin (2 * N + 1) → ℂ,
          ccmPublishedWeilMetric a N *ᵥ ξ = 0 ∧ ∑ i, ξ i = 1 ∧
          ccmPublishedWeilMetric a N * ccmLogDiracBlock a N ξ =
            (ccmLogDiracBlock a N ξ)ᴴ * ccmPublishedWeilMetric a N ∧
          ccmLogDiracBlock a N ξ *ᵥ ξ = 0 ∧
          (ccmLogDiracBlock a N ξ).charpoly =
            X * ccmRankOneQuotientCharpoly (ccmPublishedPhysicalClock a N) ξ ∧
          (∀ μ, (ccmRankOneQuotientCharpoly (ccmPublishedPhysicalClock a N) ξ).eval μ = 0 →
            μ.im = 0) ∧
          (∀ z, ccmPublishedPacketTransform a N ξ z = 0 → z.im = 0) ∧
          ∀ z, z.im < 0 → ccmLogDiracRegularizedDeterminant a N ξ z =
            -I * ((Real.exp a : ℝ) : ℂ) ^ (-I * z) * ccmPublishedPacketTransform a N ξ z) ∨
      (∃ c : Fin (2 * N + 1) → ℂ,
          ccmPublishedWeilMetric a N *ᵥ c = 0 ∧
          star (fun i => (ccmPublishedCenteredSource a N i : ℂ)) ⬝ᵥ c = 1 ∧
          ccmPublishedWeilMetric a N * ccmSourceCompletion
              (Matrix.diagonal fun i => (ccmPublishedCenteredClock N i : ℂ)) c
              (fun i => (ccmPublishedCenteredSource a N i : ℂ)) =
            (ccmSourceCompletion (Matrix.diagonal fun i => (ccmPublishedCenteredClock N i : ℂ)) c
              (fun i => (ccmPublishedCenteredSource a N i : ℂ)))ᴴ * ccmPublishedWeilMetric a N ∧
          ∀ z, (ccmSourceCompletion (Matrix.diagonal fun i => (ccmPublishedCenteredClock N i : ℂ))
            c (fun i => (ccmPublishedCenteredSource a N i : ℂ))).charpoly.eval z = 0 →
              z.im = 0)) ∧
    (∀ a : SuzukiPositiveAperture,
      ∃ u : CCMArchimedeanFormDomain a, IsFullGround a u ∧
        ccmArchimedeanFormToAperture a u ≠ 0 ∧
        ∀ w : ℂ, FourierLaplaceDivision.unitaryLaplace (timeRep a u) w = 0 → w.im = 0) ∧
    (RiemannHypothesis ↔ ∀ (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a),
      (∀ w : ℂ, FourierLaplaceDivision.unitaryLaplace (timeRep a u) w = 0 → w.im = 0) →
        0 ≤ ccmRestrictedWeilSourceQuadratic a u) ∧
    (∀ {η A M : ℝ}, 0 < η → 0 ≤ A →
      ∀ (a : ℕ → SuzukiPositiveAperture), Tendsto (fun j => (a j).1) atTop atTop →
      ∀ (u : ∀ j, CCMArchimedeanFormDomain (a j)),
        (∀ j, IsFullGround (a j) (u j)) →
        (∀ j (w : ℂ), FourierLaplaceDivision.unitaryLaplace (timeRep (a j) (u j)) w = 0 →
          w.im = 0) →
        (∀ j, ∫ t : ℝ, timeRep (a j) (u j) t ≠ 0) →
        (∀ j, ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ ≤
          M * Real.exp (a j).1 * ‖∫ t : ℝ, timeRep (a j) (u j) t‖) →
        (∀ j (z : ℂ), |z.im| < 1 / 2 + η →
          ‖conjTransform (timeRep (a j) (u j)) z‖ ≤
            M * Real.exp (A * z.re ^ 2) * ‖∫ t : ℝ, timeRep (a j) (u j) t‖) →
        RiemannHypothesis) ∧
    (∀ {η C : ℝ}, 0 < η → 0 < C →
      ∀ (a : ℕ → SuzukiPositiveAperture), Tendsto (fun j => (a j).1) atTop atTop →
      ∀ (u : ∀ j, CCMArchimedeanFormDomain (a j)),
        (∀ j, IsFullGround (a j) (u j)) →
        (∀ j (w : ℂ), FourierLaplaceDivision.unitaryLaplace (timeRep (a j) (u j)) w = 0 →
          w.im = 0) →
        (∀ j, ∫ t : ℝ, timeRep (a j) (u j) t ≠ 0) →
        (∀ j (x y : ℝ), 0 < y → y < 1 / 2 + η →
          (a j).1 * y + y / Real.pi * ∫ s : ℝ,
            Real.log ‖suzukiEntireFourier (timeRep (a j) (u j)) s‖ / ((s - x) ^ 2 + y ^ 2) ≤
              Real.log (C * ‖∫ t : ℝ, timeRep (a j) (u j) t‖)) →
        RiemannHypothesis) :=
  ⟨fun a ha N => ccmPublished_logDirac_theorem a ha N,
   exists_realRooted_fullGround,
   riemannHypothesis_iff_nonneg_on_realRooted,
   fun hη hA a ha u hg hr hm hl1 hgauss =>
     riemannHypothesis_of_gaussianGrowthFullGrounds hη hA a ha u hg hr hm hl1 hgauss,
   fun hη hC a ha u hg hr hm hbal =>
     riemannHypothesis_of_poissonBalancedFullGrounds hη hC a ha u hg hr hm hbal⟩

end GaloisForLFunctions.ArithmeticPositivityTheory
end

