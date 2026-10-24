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
  have h2 : (∫ t : ℝ, RCLike.inner (𝕜 := ℂ) (w t) (w t)) =
      ((∫ t : ℝ, ‖w t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    rw [RCLike.inner_apply, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
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
    (hR : 0 < R) (ha : 2 * R < |a|) (φ ψ : SoninL2) :
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
  change RCLike.inner (𝕜 := ℂ) (P φ t) (MellinL2.additiveTranslationUnitary a (P ψ) t) = 0
  rw [hφ, htr]
  have hψ' : P ψ (t + a) = (Icc (-R) R).indicator (fun s => ψ s) (t + a) := by
    simpa only [P, Function.comp_apply, MellinL2.realTranslationEquiv] using hψ
  rw [hψ']
  by_cases ht : t ∈ Icc (-R) R
  · have hta : t + a ∉ Icc (-R) R := by
      intro hmem
      have ht_abs : |t| ≤ R := abs_le.mpr ht
      have hta_abs : |t + a| ≤ R := abs_le.mpr hmem
      have habs : |a| ≤ |t + a| + |t| := by
        calc |a| = |(t + a) - t| := by ring_nf
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
    have h2 := (tendsto_const_nhds.add hφ).mul hψ
    simpa only [zero_mul, add_zero, mul_zero] using h1.add h2
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR_pos, hR_lt⟩ := (((herr.eventually (Iio_mem_nhds hε)).and
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
    conv_lhs => rw [hφ_eq]
    rw [inner_add_left, hψ_eq, inner_add_right, add_assoc]
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

private theorem integrable_prod_toeplitz {f₁ f₂ τ : ℝ → ℂ} (hf₁ : Integrable f₁)
    (hf₂ : Integrable f₂) (hτ : Continuous τ) {C : ℝ} (hC : ∀ u, ‖τ u‖ ≤ C) :
    Integrable (fun p : ℝ × ℝ => conj (f₁ p.1) * f₂ p.2 * τ (p.2 - p.1))
      (volume.prod volume) :=
  (hf₁.star.mul_prod hf₂).mul_bdd
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
      change ((conj (fσ p.1) * fσ p.2 * (κ (p.2 - p.1) : ℂ))).re = _
      simp only [fσ, map_add, map_mul, Complex.conj_ofReal, ← Complex.ofReal_mul,
        ← Complex.ofReal_add, ← Complex.ofReal_pow, Complex.ofReal_re]
      ring
    simp_rw [hre_pt, hσ2, one_mul] at hnonneg
    rw [integral_add (hp00.add hp11) (hp01.add hp10), integral_add hp00 hp11,
      integral_add hp01 hp10, integral_const_mul, integral_const_mul] at hnonneg
    -- Shift `(p.1 - u₀, p.2 - u₀)` and the two cross integrals back to `(p.1, p.2)`:
    have hi11 : (∫ p : ℝ × ℝ, h (p.1 - u₀) * h (p.2 - u₀) * κ (p.2 - p.1) ∂(volume.prod volume)) =
        ∫ p : ℝ × ℝ, h p.1 * h p.2 * κ (p.2 - p.1) ∂(volume.prod volume) := by
      rw [integral_prod _ hp11, integral_prod _ hp00]
      simp_rw [← integral_sub_right_eq_self
        (fun s => ∫ t, h (s - u₀) * h (t - u₀) * κ (t - s)) u₀]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      dsimp only
      rw [← integral_sub_right_eq_self
        (fun t => h s * h (t - u₀) * κ (t - (s + u₀))) u₀]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [add_sub_cancel_right]
      ring_nf
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
      rw [← integral_sub_right_eq_self (fun t => h s * h (t - u₀) * κ (t - s)) u₀]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [add_sub_cancel_right]
      ring_nf
    have hi10 : (∫ p : ℝ × ℝ, h (p.1 - u₀) * h p.2 * κ (p.2 - p.1) ∂(volume.prod volume)) =
        ∫ p : ℝ × ℝ, h p.1 * h p.2 * κ (u₀ + p.2 - p.1) ∂(volume.prod volume) := by
      have hp10' : Integrable (fun p : ℝ × ℝ => h (p.1 - u₀) * h p.2 * κ (p.2 - p.1))
          (volume.prod volume) :=
        ((hh_int.comp_sub_right u₀).mul_prod hh_int).mul_bdd
          (hκ_cont.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hκ_bound _)
      rw [integral_prod _ hp10', integral_prod _ (hprod_hh u₀)]
      rw [← integral_sub_right_eq_self
        (fun s => ∫ t, h (s - u₀) * h t * κ (t - s)) u₀]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      dsimp only [add_sub_cancel_right]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      have hev : κ (t - (s + u₀)) = κ (u₀ + t - s) := by
        rw [show t - (s + u₀) = -(u₀ + t - s) by ring]
        -- wait: -(u₀ + t - s) = -u₀ - t + s, whereas t - (s + u₀) = t - s - u₀!
        sorry
      sorry
    sorry
  sorry
