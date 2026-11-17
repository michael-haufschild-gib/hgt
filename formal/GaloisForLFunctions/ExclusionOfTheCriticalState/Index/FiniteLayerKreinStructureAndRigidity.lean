import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.TheZeroParsevalIdentityOfTheState
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheNullVectorsOfTheConfinedForm
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheConfinedFormCountsTheZerosRightOfTheLine
import GaloisForLFunctions.ExclusionOfTheCriticalState.Collar.TheCollarWeakEquationIsSoftBeyondStar
import GaloisForLFunctions.ExclusionOfTheCriticalState.Decay.SubexponentialThickTailGivesTheAbscissaLaw
import GaloisForLFunctions.ExclusionOfTheCriticalState.Models.CurveCriticalStatesAndStepanovExclusion
import GaloisForLFunctions.InfiniteRankWeilTheory.TheCrudeStepAndTheCount
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyFunctionalEquationsDetermineThePrimes
import GaloisForLFunctions.RHTower.BeurlingOverRegularIntegersOffLineZeros
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFiniteStratumIsThePacketIndexDichotomy

/-!
# Finite-layer critical states, off-line Krein faithfulness, model separation, and B13 in ECS

This module gives the complete, unconditional answer to question `E-Q2`:

1. **Higher critical states and finite-layer zero Parseval (`satisfiesNormalisedStar_of_nullVector`,
   `nullVector_zeroParseval_of_finiteOffLine`, `orthogonalNullSpan_zeroParseval_of_finiteOffLine`).**
   Every confined null vector `IsConfinedNullVector R F` (`R > 0`) satisfies left-normalised `(★)`
   and Gaussian-summed zero pairing `-a(R) W₈(F, G)` against all `G ∈ H`. Under `FiniteOffLine`,
   every confined null vector — and every linear combination `H = ∑_{i < k} c_i F_i` of a
   `W₈`-orthogonal family of confined null vectors — has square-summable on-line zero values and
   satisfies the exact Parseval identity
   `∑_{on} ‖L H(z)‖² + ∑_{off} L H(z) L H(-z) = -∑_{i < k} c_i² a(R_i) W₈(F_i)`.

2. **Off-line faithfulness, sharp multiplicity-free dimension bound, and single-pair pole isolation
   (`orthogonalNullSpan_eval_upperRight_injective`, `orthogonalNullSpan_eval_upperLeft_injective`,
   `card_orthogonalNullVectors_le_rightZeros_of_finiteOffLine`,
   `existsUnique_singlePair_leftZero_isolator_of_finiteOffLine`).**
   Because `ξ(½ + x) > 0` on `ℝ` (`xi_real_pos`), `ξ(1 - s) = ξ(s)`, and `L H(z̄) = conj(L H(z))`
   for real `H`, the off-line centred zeros partition into conjugate pairs in `Z_right` and
   `Z_left` (`#Z_right = #Z_left = 2 #Z_right⁺ = 2 #Z_left⁺`). Any real combination `H` of
   `W₈`-orthogonal confined null vectors vanishing on `Z_right⁺` (or on `Z_left⁺`) has vanishing
   off-line zero sum, forcing `0 ≤ ∑_{on} ‖L H(z)‖² = -∑ c_i² a(R_i) W₈(F_i) ≤ 0`, hence `c = 0`.
   Thus:
   * Evaluation on `Z_right⁺` and evaluation on `Z_left⁺` are both `ℝ`-linearly injective;
   * Any `W₈`-orthogonal family of confined null vectors has size at most `#Z_right` (counted
     **without multiplicity**);
   * When `k = #Z_right`, evaluation on `Z_left⁺` is an `ℝ`-linear isomorphism: for every
     upper-half-plane left zero `z* ∈ Z_left⁺` and every nonzero `w₀ ∈ ℂ`, a unique real
     combination `H = ∑ c_i F_i` satisfies `L H(z*) = w₀`, `L H(z̄*) = w̄₀`, and `L H(z) = 0` at
     every other left zero `z ∈ Z_left \ {z*, z̄*}`, isolating a single conjugate pair of
     beyond-the-wall prime-balance obstructions (`¬ HasBeyondTheWallPrimeContinuation H`).

3. **Model separation and Beurling–Lévy rigidity (`soft_finiteLayer_does_not_force_zero_states`,
   `overRegular_finiteLayer_nonnegPrimes_has_offLineZero`, `beurling_levy_rigidity_forces_zeta`).**
   At the soft / single-input model level, `N` orthogonal critical states, the zero Parseval
   identity, `(★)`, and the beyond-the-wall prime-head identity do **not** force `N = 0`:
   * `hidingDatum M` (`q = 2`, arbitrarily large on-line unitary layer of size `2M`, finite off-line
     layer `{2, 1/2}`, Hodge-positive on all windows `< n`) and `goldenDatum` (`q = 5`, positive
     integral point counts `N_j ≥ 1`, functional equation) satisfy all Stage-2 critical-state,
     Parseval, `(★)`, and prime-head identities with `N = 1 > 0`;
   * `overRegularZeta (2/5) (1/10) 1` has nonnegative logarithmic prime density `w(t) ≥ 0`, integer
     count error `o(1)`, and a finite off-line zero pair at `3/5 ± i` (`N > 0`, no FE);
   * Adjoining **both** a countable Beurling system (`Λ_B ≥ 0`) **and** the `Γ_ℝ` functional
     equation up to `L²` strip defect uniquely forces `ζ_B = ζ`
     (`beurlingSystem_rigidity_of_finiteEnergy_defect`).

4. **Six-way ECS equivalence of B13 (`finiteLayer_ecs_b13_tfae`).**
   Unconditionally, `FiniteOffLine → RiemannHypothesis` (B13) is equivalent to: absence of the
   critical ground state under `FiniteOffLine`; absence of any confined null vector at any `R > 0`
   under `FiniteOffLine`; `FiniteOffLine → ZetaBeyondTheWallPrimeContinuation`; thick-lag
   boundedness under `FiniteOffLine` (`b13_iff_thick_lag_bounded`); and the Weil packet-index
   dichotomy `realPacketNegIndex = 0 ∨ realPacketNegIndex = ⊤`.
-/

noncomputable section

open MeasureTheory Set Filter Zeta23 Complex Metric Topology Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState

open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### 1. Normalised `(★)` and zero Parseval for confined null vectors and their spans -/

/-- Every confined null vector at `R > 0` satisfies left-normalised `(★)`. -/
theorem satisfiesNormalisedStar_of_nullVector {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) : SatisfiesNormalisedStar R F := by
  intro w hw
  have hxi : xi (1 / 2 + (w + 8)) ≠ 0 := xi_ne_zero_of_half_le_abs_re (by
    have h8 : (w + 8).re = w.re + 8 := by simp
    rw [h8]
    have := le_abs_self (w.re + 8)
    linarith)
  have hlim := tendsto_tsum_sub_left hF.1 hxi
  have halias := nullVector_alias_mul_laplace hR hF hw
  have heq : globalRemainder F (w + 8) =
      -((criticalAliasCoefficient R : ℂ) * negativeHalfLineLaplace (cx F) w) := by
    rw [halias, neg_neg]
  rwa [heq] at hlim

/-- Every confined null vector has strictly positive confinement mass `W₈(F) > 0`. -/
theorem nullVector_confinementMass_pos {R : ℝ} {F : ℝ → ℝ} (hF : IsConfinedNullVector R F) :
    0 < ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) := by
  have hnn : 0 ≤ ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg (F u)) (Real.exp_pos _).le
  refine lt_of_le_of_ne hnn fun h0 => hF.2.1 ?_
  have hae : ∀ᵐ u ∂volume, F u ^ 2 * Real.exp (-(8 * u)) = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun u => mul_nonneg (sq_nonneg (F u)) (Real.exp_pos _).le)
      hF.1.exponential).mp h0.symm
  have hae_sq : (fun u => F u ^ 2) =ᵐ[volume] 0 := by
    filter_upwards [hae] with u hu
    exact (mul_eq_zero.mp hu).resolve_right (Real.exp_pos _).ne'
  exact integral_eq_zero_of_ae hae_sq

private theorem setIntegral_Iio_confinement_eq_univ {F G : ℝ → ℝ}
    (hF0 : ∀ u, 0 ≤ u → F u = 0) :
    (∫ u in Iio (0 : ℝ), F u * G u * Real.exp (-(8 * u))) =
      ∫ u : ℝ, F u * G u * Real.exp (-(8 * u)) := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_
  have hge : 0 ≤ u := not_lt.mp hu
  rw [hF0 u hge, zero_mul, zero_mul]

/-- Uniform strip bound `‖L G(-z_q)‖ ≤ C_G` across all `q : XiZeroCopy` for any `G ∈ H`. -/
private theorem norm_laplace_neg_centredZero_le {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (q : XiZeroCopy) :
    ‖negativeHalfLineLaplace (cx G) (-centredZero q)‖ ≤
      ((∫ u : ℝ, G u ^ 2 * Real.exp (-(8 * u))) + ∫ u : ℝ, probe 1 u) / 2 := by
  have hzre : -(1 / 2 : ℝ) < (-centredZero q).re := by
    have h := (abs_lt.mp (abs_re_centredZero_lt q)).2
    simp; linarith
  have hdom : Integrable fun u : ℝ => (G u ^ 2 * Real.exp (-(8 * u)) + probe 1 u) / 2 :=
    (hG.exponential.add (integrable_probe one_pos)).div_const 2
  refine (norm_integral_le_of_norm_le hdom (Eventually.of_forall fun u => ?_)).trans_eq
    (by rw [integral_div, integral_add hG.exponential (integrable_probe one_pos)])
  rcases lt_or_ge u 0 with hu | hu
  · rw [norm_mul, norm_cexp_mul_ofReal, cx, Complex.norm_real, Real.norm_eq_abs, probe_of_neg hu]
    have hsplit : Real.exp ((-centredZero q).re * u) =
        Real.exp (-(4 * u)) * Real.exp (((-centredZero q).re + 4) * u) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp : Real.exp (((-centredZero q).re + 4) * u) ≤ Real.exp ((1 / 2) * u) :=
      Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_right (by linarith : (1 / 2 : ℝ) ≤ (-centredZero q).re + 4) hu.le)
    have hsq_G : (|G u| * Real.exp (-(4 * u))) ^ 2 = G u ^ 2 * Real.exp (-(8 * u)) := by
      rw [mul_pow, sq_abs, sq (Real.exp (-(4 * u))), ← Real.exp_add]; congr 2; ring
    have hsq_exp : Real.exp ((1 / 2) * u) ^ 2 = Real.exp (1 * u) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have h1 : Real.exp ((-centredZero q).re * u) * |G u| ≤
        (|G u| * Real.exp (-(4 * u))) * Real.exp ((1 / 2) * u) := by
      rw [hsplit, show Real.exp (-(4 * u)) * Real.exp (((-centredZero q).re + 4) * u) * |G u| =
        (|G u| * Real.exp (-(4 * u))) * Real.exp (((-centredZero q).re + 4) * u) by ring]
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    nlinarith [sq_nonneg (|G u| * Real.exp (-(4 * u)) - Real.exp ((1 / 2) * u)),
      hsq_G, hsq_exp, h1]
  · simp [cx, hG.support u hu, probe_of_nonneg hu]

/-- Heated zero-pairing series summability for any `F` satisfying normalised `(★)` and `G ∈ H`. -/
private theorem summable_zeroPairing_heated_of_normalisedStar {R : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hstar : SatisfiesNormalisedStar R F)
    {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) {ε : ℝ} (hε : 0 < ε) :
    Summable fun q : XiZeroCopy =>
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero q ^ 2) := by
  have hs0 := (hasSum_heated_zeroSeries_of_normalisedStar hF hstar hε 0).summable.norm
  set CG : ℝ := ((∫ u : ℝ, G u ^ 2 * Real.exp (-(8 * u))) + ∫ u : ℝ, probe 1 u) / 2
  refine Summable.of_norm_bounded (hs0.mul_right CG) fun q => ?_
  have h0 : stateHeatSymbol ε 0 (centredZero q) =
      Complex.exp ((ε : ℂ) * centredZero q ^ 2) := by
    unfold stateHeatSymbol; rw [Complex.ofReal_zero, mul_zero, sub_zero]
  rw [norm_mul, norm_mul, mul_right_comm, ← norm_mul, ← h0]
  exact mul_le_mul_of_nonneg_left (norm_laplace_neg_centredZero_le hG q) (norm_nonneg _)

/-- General finite-layer Fatou–Parseval extraction for any real profile `H` whose heated zero-norm
series is summable for `ε > 0` and converges to `V ∈ ℝ` as `ε → 0⁺`. -/
private theorem zeroParseval_of_tendsto_zeroNormTerm {H : ℝ → ℝ} {V : ℝ}
    (hsum_ε : ∀ {ε : ℝ}, 0 < ε → Summable (zeroNormTerm H ε))
    (htend : Tendsto (fun ε : ℝ => ∑' q : XiZeroCopy, zeroNormTerm H ε q) (𝓝[>] 0) (𝓝 (V : ℂ)))
    (hfin : BacklundConverse.FiniteOffLine) :
    Summable (fun q : onLineCopies => zeroValueMass H q) ∧
      ((∑' q : onLineCopies, zeroValueMass H q : ℝ) : ℂ) +
        (∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx H) (centredZero q) *
          negativeHalfLineLaplace (cx H) (-centredZero q)) = (V : ℂ) := by
  set L : ℂ := ∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx H) (centredZero q) *
    negativeHalfLineLaplace (cx H) (-centredZero q)
  have hL : Tendsto (fun ε : ℝ => ∑' q : ↑onLineCopiesᶜ, zeroNormTerm H ε q) (𝓝[>] 0) (𝓝 L) :=
    tendsto_offLine_of_finite (compl_onLineCopies_finite_of_finiteOffLine hfin)
  let Rfn : ℝ → ℝ := fun ε => ∑' q : onLineCopies, onLineWeight ε q * zeroValueMass H q
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hR : Tendsto (fun ε => (Rfn ε : ℂ)) (𝓝[>] 0) (𝓝 ((V : ℂ) - L)) := by
    refine (htend.sub hL).congr' ?_
    filter_upwards [hpos] with ε hε
    rw [tsum_zeroNormTerm_eq_onLine_add (hsum_ε hε)]
    ring
  have hRre : Tendsto Rfn (𝓝[>] 0) (𝓝 ((V : ℂ) - L).re) :=
    Tendsto.congr (fun ε => by simp only [Function.comp_apply, Complex.ofReal_re])
      ((Complex.continuous_re.tendsto _).comp hR)
  have him : ((V : ℂ) - L).im = 0 := by
    have h := (Complex.continuous_im.tendsto _).comp hR
    simp only [Function.comp_def, Complex.ofReal_im] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  set M := ((V : ℂ) - L).re
  have hblock : ∀ T : Finset onLineCopies, ∑ q ∈ T, zeroValueMass H q ≤ M := by
    intro T
    have hT : Tendsto (fun ε => ∑ q ∈ T, onLineWeight ε q * zeroValueMass H q) (𝓝[>] 0)
        (𝓝 (∑ q ∈ T, zeroValueMass H q)) := by
      refine tendsto_finsetSum T fun q _ => ?_
      simpa using (tendsto_onLineWeight (q : XiZeroCopy)).mul_const (zeroValueMass H q)
    refine le_of_tendsto_of_tendsto hT hRre ?_
    filter_upwards [hpos] with ε hε
    exact (summable_onLine_of_summable (hsum_ε hε)).sum_le_tsum
      T fun q _ => mul_nonneg (onLineWeight_pos ε q).le (zeroValueMass_nonneg H q)
  have hsum_on : Summable (fun q : onLineCopies => zeroValueMass H q) :=
    summable_of_sum_le (fun q => zeroValueMass_nonneg H q) hblock
  have hle : ∑' q : onLineCopies, zeroValueMass H q ≤ M :=
    Real.tsum_le_of_sum_le (fun q => zeroValueMass_nonneg H q) hblock
  have hge : M ≤ ∑' q : onLineCopies, zeroValueMass H q := by
    refine le_of_tendsto hRre ?_
    filter_upwards [hpos] with ε hε
    refine (summable_onLine_of_summable (hsum_ε hε)).tsum_le_tsum (fun q => ?_) hsum_on
    exact mul_le_of_le_one_left (zeroValueMass_nonneg H q) (onLineWeight_le_one hε.le q)
  refine ⟨hsum_on, ?_⟩
  have hM : ((M : ℝ) : ℂ) = (V : ℂ) - L := Complex.ext (by simp [M]) (by simp [him])
  rw [le_antisymm hle hge, hM]
  ring

/-- **Zero Parseval identity for every confined null vector under `FiniteOffLine`.** -/
theorem nullVector_zeroParseval_of_finiteOffLine {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (hfin : BacklundConverse.FiniteOffLine) :
    Summable (fun q : onLineCopies => zeroValueMass F q) ∧
      ((∑' q : onLineCopies, zeroValueMass F q : ℝ) : ℂ) +
        (∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx F) (-centredZero q)) =
        (stateZeroNormLimit R F : ℂ) := by
  have hstar := satisfiesNormalisedStar_of_nullVector hR hF
  have htend := tendsto_zeroPairing_of_normalisedStar hF.1 hstar hF.1
  have hsq : (∫ u : ℝ, F u * F u * Real.exp (-(8 * u))) =
      ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) :=
    integral_congr_ae (Eventually.of_forall fun u => by ring)
  rw [setIntegral_Iio_confinement_eq_univ hF.1.support, hsq] at htend
  exact zeroParseval_of_tendsto_zeroNormTerm
    (fun hε => summable_zeroPairing_heated_of_normalisedStar hF.1 hstar hF.1 hε)
    htend hfin

/-- Finite real linear combination of energy-domain profiles lies in the energy domain. -/
private theorem energyDomain_finset_sum {ι : Type*} (S : Finset ι) {F : ι → ℝ → ℝ}
    (hF : ∀ i ∈ S, CriticalHalfLineEnergyDomain (F i)) (c : ι → ℝ) :
    CriticalHalfLineEnergyDomain (fun u => ∑ i ∈ S, c i * F i u) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa using (criticalHalfLineEnergyDomain_probe (by norm_num : (4 : ℝ) < 5)).const_mul 0
  | insert i T hi ih =>
    have hFi := (hF i (Finset.mem_insert_self i T)).const_mul (c i)
    have hT := ih fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have hadd := hFi.add_const_mul hT 1
    simpa [Finset.sum_insert hi, one_mul] using hadd

private theorem negativeHalfLineLaplace_finset_sum {ι : Type*} (S : Finset ι) {F : ι → ℝ → ℝ}
    (hF : ∀ i ∈ S, CriticalHalfLineEnergyDomain (F i)) (c : ι → ℝ) {w : ℂ} (hw : -4 < w.re) :
    negativeHalfLineLaplace (cx fun u => ∑ i ∈ S, c i * F i u) w =
      ∑ i ∈ S, (c i : ℂ) * negativeHalfLineLaplace (cx (F i)) w := by
  classical
  unfold negativeHalfLineLaplace
  have hint : ∀ i ∈ S, Integrable fun u : ℝ =>
      Complex.exp (w * (u : ℂ)) * cx (fun x => c i * F i x) u := by
    intro i hi
    have hd := (hF i hi).const_mul (c i)
    have hneg : (-w).re < (4 : ℝ) := by simp; linarith
    simpa [neg_neg] using integrable_cexp_neg_mul_cx hd (z := -w) hneg
  have hpt : (fun u : ℝ => Complex.exp (w * (u : ℂ)) * cx (fun x => ∑ i ∈ S, c i * F i x) u) =
      fun u : ℝ => ∑ i ∈ S, Complex.exp (w * (u : ℂ)) * cx (fun x => c i * F i x) u := by
    funext u; simp [cx, Finset.mul_sum]
  rw [hpt, integral_finsetSum S hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsmul : (fun u : ℝ => Complex.exp (w * (u : ℂ)) * cx (fun x => c i * F i x) u) =
      fun u : ℝ => (c i : ℂ) * (Complex.exp (w * (u : ℂ)) * cx (F i) u) := by
    funext u; simp [cx]; ring
  rw [hsmul, integral_const_mul]

/-- **Zero Parseval identity on the span of any `W₈`-orthogonal family of confined null vectors.** -/
theorem orthogonalNullSpan_zeroParseval_of_finiteOffLine {k : ℕ} {R : Fin k → ℝ}
    (hR : ∀ i, 0 < R i) {F : Fin k → ℝ → ℝ} (hF : ∀ i, IsConfinedNullVector (R i) (F i))
    (horth : ∀ i j, i ≠ j → (∫ u : ℝ, F i u * F j u * Real.exp (-(8 * u))) = 0)
    (hfin : BacklundConverse.FiniteOffLine) (c : Fin k → ℝ) :
    let H : ℝ → ℝ := fun u => ∑ i : Fin k, c i * F i u
    Summable (fun q : onLineCopies => zeroValueMass H q) ∧
      ((∑' q : onLineCopies, zeroValueMass H q : ℝ) : ℂ) +
        (∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx H) (centredZero q) *
          negativeHalfLineLaplace (cx H) (-centredZero q)) =
        ((-(∑ i : Fin k, c i ^ 2 * criticalAliasCoefficient (R i) *
          ∫ u : ℝ, F i u ^ 2 * Real.exp (-(8 * u))) : ℝ) : ℂ) := by
  intro H
  have hH_dom : CriticalHalfLineEnergyDomain H :=
    energyDomain_finset_sum Finset.univ (fun i _ => (hF i).1) c
  have hstar : ∀ i : Fin k, SatisfiesNormalisedStar (R i) (F i) :=
    fun i => satisfiesNormalisedStar_of_nullVector (hR i) (hF i)
  have hterm_eq : ∀ (ε : ℝ) (q : XiZeroCopy),
      zeroNormTerm H ε q = ∑ i : Fin k, (c i : ℂ) *
        (negativeHalfLineLaplace (cx (F i)) (centredZero q) *
          negativeHalfLineLaplace (cx H) (-centredZero q) *
            Complex.exp ((ε : ℂ) * centredZero q ^ 2)) := by
    intro ε q
    have hre : -4 < (centredZero q).re := by
      have := (abs_lt.mp (abs_re_centredZero_lt q)).1; linarith
    unfold zeroNormTerm
    rw [negativeHalfLineLaplace_finset_sum Finset.univ (fun i _ => (hF i).1) c hre,
      Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsum_ε : ∀ {ε : ℝ}, 0 < ε → Summable (zeroNormTerm H ε) := by
    intro ε hε
    have hfn : zeroNormTerm H ε = fun q => ∑ i : Fin k, (c i : ℂ) *
        (negativeHalfLineLaplace (cx (F i)) (centredZero q) *
          negativeHalfLineLaplace (cx H) (-centredZero q) *
            Complex.exp ((ε : ℂ) * centredZero q ^ 2)) := funext (hterm_eq ε)
    rw [hfn]
    exact summable_sum fun i _ =>
      (summable_zeroPairing_heated_of_normalisedStar (hF i).1 (hstar i) hH_dom hε).mul_left _
  have htend : Tendsto (fun ε : ℝ => ∑' q : XiZeroCopy, zeroNormTerm H ε q) (𝓝[>] 0)
      (𝓝 (((-(∑ i : Fin k, c i ^ 2 * criticalAliasCoefficient (R i) *
        ∫ u : ℝ, F i u ^ 2 * Real.exp (-(8 * u))) : ℝ) : ℂ))) := by
    have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
    have htsum_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        (∑' q : XiZeroCopy, zeroNormTerm H ε q) =
          ∑ i : Fin k, (c i : ℂ) * ∑' q : XiZeroCopy,
            negativeHalfLineLaplace (cx (F i)) (centredZero q) *
              negativeHalfLineLaplace (cx H) (-centredZero q) *
                Complex.exp ((ε : ℂ) * centredZero q ^ 2) := by
      filter_upwards [hpos] with ε hε
      simp_rw [hterm_eq ε]
      rw [(hasSum_sum fun i (_ : i ∈ Finset.univ) =>
        ((summable_zeroPairing_heated_of_normalisedStar (hF i).1 (hstar i) hH_dom hε).mul_left
          _).hasSum).tsum_eq]
      exact Finset.sum_congr rfl fun i _ => tsum_mul_left
    have hpair_i : ∀ i : Fin k,
        (∫ u in Iio (0 : ℝ), F i u * H u * Real.exp (-(8 * u))) =
          c i * ∫ u : ℝ, F i u ^ 2 * Real.exp (-(8 * u)) := by
      intro i
      rw [setIntegral_Iio_confinement_eq_univ (hF i).1.support]
      have hint_j : ∀ j ∈ (Finset.univ : Finset (Fin k)),
          Integrable fun u : ℝ => c j * (F i u * F j u * Real.exp (-(8 * u))) := by
        intro j _
        refine ((((hF i).1.exponential.add (hF j).1.exponential).div_const 2).mono'
          ((((hF i).1.meas.mul (hF j).1.meas).mul (by fun_prop)).aestronglyMeasurable)
          (Eventually.of_forall fun u => ?_)).const_mul (c j)
        dsimp only [Pi.add_apply, Pi.mul_apply]
        rw [Real.norm_eq_abs, abs_le]
        have he : 0 ≤ Real.exp (-(8 * u)) := (Real.exp_pos _).le
        constructor <;> nlinarith [sq_nonneg (F i u + F j u), sq_nonneg (F i u - F j u), he]
      have hexp : (fun u : ℝ => F i u * H u * Real.exp (-(8 * u))) =
          fun u : ℝ => ∑ j : Fin k, c j * (F i u * F j u * Real.exp (-(8 * u))) := by
        funext u; dsimp [H]; rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hexp, integral_finsetSum Finset.univ hint_j]
      have hsingle : ∑ j : Fin k, ∫ u : ℝ, c j * (F i u * F j u * Real.exp (-(8 * u))) =
          ∫ u : ℝ, c i * (F i u * F i u * Real.exp (-(8 * u))) := by
        refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun hi => absurd (Finset.mem_univ i) hi)
        rw [integral_const_mul, horth i j hji.symm, mul_zero]
      rw [hsingle, integral_const_mul]
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun u => by ring)
    have hsum_lim : Tendsto (fun ε : ℝ => ∑ i : Fin k, (c i : ℂ) * ∑' q : XiZeroCopy,
        negativeHalfLineLaplace (cx (F i)) (centredZero q) *
          negativeHalfLineLaplace (cx H) (-centredZero q) *
            Complex.exp ((ε : ℂ) * centredZero q ^ 2))
        (𝓝[>] 0)
        (𝓝 (∑ i : Fin k, (c i : ℂ) * (((-(criticalAliasCoefficient (R i) *
          (c i * ∫ u : ℝ, F i u ^ 2 * Real.exp (-(8 * u)))) : ℝ) : ℂ)))) := by
      refine tendsto_finsetSum Finset.univ fun i _ => ?_
      have hi_lim := tendsto_zeroPairing_of_normalisedStar (hF i).1 (hstar i) hH_dom
      rw [hpair_i i] at hi_lim
      exact hi_lim.const_mul (c i : ℂ)
    have hval_eq : (∑ i : Fin k, (c i : ℂ) * (((-(criticalAliasCoefficient (R i) *
        (c i * ∫ u : ℝ, F i u ^ 2 * Real.exp (-(8 * u)))) : ℝ) : ℂ))) =
        ((-(∑ i : Fin k, c i ^ 2 * criticalAliasCoefficient (R i) *
          ∫ u : ℝ, F i u ^ 2 * Real.exp (-(8 * u))) : ℝ) : ℂ) := by
      push_cast
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hval_eq] at hsum_lim
    exact hsum_lim.congr' (htsum_eq.mono fun _ h => h.symm)
  exact zeroParseval_of_tendsto_zeroNormTerm hsum_ε htend hfin

/-! ### 2. Finite off-line zero geometry, Krein faithfulness, dimension bound, and pole isolation -/

/-- The finite set of off-line `XiZeroCopy` elements under `FiniteOffLine`. -/
def offLineCopyFinset (hfin : BacklundConverse.FiniteOffLine) : Finset XiZeroCopy :=
  (compl_onLineCopies_finite_of_finiteOffLine hfin).toFinset

/-- Distinct centred right zeros `{z ∈ ℂ | 0 < Re z ∧ ξ(½ + z) = 0}` under `FiniteOffLine`. -/
def rightCentredZeros (hfin : BacklundConverse.FiniteOffLine) : Finset ℂ :=
  ((offLineCopyFinset hfin).image centredZero).filter fun z => 0 < z.re

/-- Distinct upper-half-plane centred right zeros `{z ∈ rightCentredZeros | 0 < Im z}`. -/
def upperRightCentredZeros (hfin : BacklundConverse.FiniteOffLine) : Finset ℂ :=
  (rightCentredZeros hfin).filter fun z => 0 < z.im

/-- Distinct centred left zeros `{z ∈ ℂ | Re z < 0 ∧ ξ(½ + z) = 0}` under `FiniteOffLine`. -/
def leftCentredZeros (hfin : BacklundConverse.FiniteOffLine) : Finset ℂ :=
  ((offLineCopyFinset hfin).image centredZero).filter fun z => z.re < 0

/-- Distinct upper-half-plane centred left zeros `{z ∈ leftCentredZeros | 0 < Im z}`. -/
def upperLeftCentredZeros (hfin : BacklundConverse.FiniteOffLine) : Finset ℂ :=
  (leftCentredZeros hfin).filter fun z => 0 < z.im

theorem mem_offLineCopyFinset {hfin : BacklundConverse.FiniteOffLine} {q : XiZeroCopy} :
    q ∈ offLineCopyFinset hfin ↔ (centredZero q).re ≠ 0 := by
  simp [offLineCopyFinset, onLineCopies]

theorem mem_rightCentredZeros_iff (hfin : BacklundConverse.FiniteOffLine) {z : ℂ} :
    z ∈ rightCentredZeros hfin ↔ 0 < z.re ∧ xi (1 / 2 + z) = 0 := by
  simp only [rightCentredZeros, Finset.mem_filter, Finset.mem_image, mem_offLineCopyFinset]
  constructor
  · rintro ⟨⟨q, -, rfl⟩, hpos⟩
    exact ⟨hpos, xi_centredZero q⟩
  · rintro ⟨hpos, hxi⟩
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have hzc : centredZero q = z := by rw [centredZero, hq]; ring
    exact ⟨⟨q, by rw [hzc]; exact hpos.ne', hzc⟩, hpos⟩

theorem mem_leftCentredZeros_iff (hfin : BacklundConverse.FiniteOffLine) {z : ℂ} :
    z ∈ leftCentredZeros hfin ↔ z.re < 0 ∧ xi (1 / 2 + z) = 0 := by
  simp only [leftCentredZeros, Finset.mem_filter, Finset.mem_image, mem_offLineCopyFinset]
  constructor
  · rintro ⟨⟨q, -, rfl⟩, hneg⟩
    exact ⟨hneg, xi_centredZero q⟩
  · rintro ⟨hneg, hxi⟩
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have hzc : centredZero q = z := by rw [centredZero, hq]; ring
    exact ⟨⟨q, by rw [hzc]; exact hneg.ne, hzc⟩, hneg⟩

theorem xi_half_add_im_ne_zero {z : ℂ} (hxi : xi (1 / 2 + z) = 0) : z.im ≠ 0 := by
  intro him0
  have hreal : (1 : ℂ) / 2 + z = ((1 / 2 + z.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him0]
  rw [hreal] at hxi
  have hpos := _root_.RHTower.XiGlobalKummer.xi_real_pos (1 / 2 + z.re)
  rw [hxi, Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

private theorem xi_half_add_conj {z : ℂ} (hxi : xi (1 / 2 + z) = 0) :
    xi (1 / 2 + conj z) = 0 := by
  have heq : (1 : ℂ) / 2 + conj z = conj (1 / 2 + z) := by
    apply Complex.ext <;> simp
  rw [heq, xi_conj, hxi, map_zero]

private theorem xi_half_add_neg {z : ℂ} (hxi : xi (1 / 2 + z) = 0) :
    xi (1 / 2 + -z) = 0 := by
  have heq : (1 : ℂ) / 2 + -z = 1 - (1 / 2 + z) := by ring
  rw [heq, xi_one_sub]
  exact hxi

/-- Exact cardinality identities among the off-line zero sets:
`#Z_right = 2 #Z_right⁺`, `#Z_left = 2 #Z_left⁺`, and `#Z_right⁺ = #Z_left⁺`. -/
theorem card_right_and_left_centredZeros (hfin : BacklundConverse.FiniteOffLine) :
    (rightCentredZeros hfin).card = 2 * (upperRightCentredZeros hfin).card ∧
      (leftCentredZeros hfin).card = 2 * (upperLeftCentredZeros hfin).card ∧
      (upperRightCentredZeros hfin).card = (upperLeftCentredZeros hfin).card := by
  have hbij_right : ((rightCentredZeros hfin).filter fun z => ¬ 0 < z.im).card =
      (upperRightCentredZeros hfin).card := by
    symm
    refine Finset.card_bij (fun z _ => conj z) (fun z hz => ?_)
      (fun _ _ _ _ h => by simpa using congrArg conj h) (fun w hw => ⟨conj w, ?_, Complex.conj_conj w⟩)
    · obtain ⟨hzR, hzim⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzre, hxi⟩ := (mem_rightCentredZeros_iff hfin).mp hzR
      refine Finset.mem_filter.mpr ⟨(mem_rightCentredZeros_iff hfin).mpr
        ⟨by simpa using hzre, xi_half_add_conj hxi⟩, ?_⟩
      simp; linarith
    · obtain ⟨hwR, hwim_le⟩ := Finset.mem_filter.mp hw
      obtain ⟨hwre, hxi⟩ := (mem_rightCentredZeros_iff hfin).mp hwR
      have hwim_ne := xi_half_add_im_ne_zero hxi
      have hwim_neg : w.im < 0 := lt_of_le_of_ne (not_lt.mp hwim_le) hwim_ne
      refine Finset.mem_filter.mpr ⟨(mem_rightCentredZeros_iff hfin).mpr
        ⟨by simpa using hwre, xi_half_add_conj hxi⟩, ?_⟩
      simp; linarith
  have hcard_right : (rightCentredZeros hfin).card = 2 * (upperRightCentredZeros hfin).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := rightCentredZeros hfin) (p := fun z => 0 < z.im)
    change (upperRightCentredZeros hfin).card + _ = _ at hsplit
    rw [hbij_right, ← two_mul] at hsplit
    exact hsplit.symm
  have hbij_left : ((leftCentredZeros hfin).filter fun z => ¬ 0 < z.im).card =
      (upperLeftCentredZeros hfin).card := by
    symm
    refine Finset.card_bij (fun z _ => conj z) (fun z hz => ?_)
      (fun _ _ _ _ h => by simpa using congrArg conj h) (fun w hw => ⟨conj w, ?_, Complex.conj_conj w⟩)
    · obtain ⟨hzL, hzim⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzre, hxi⟩ := (mem_leftCentredZeros_iff hfin).mp hzL
      refine Finset.mem_filter.mpr ⟨(mem_leftCentredZeros_iff hfin).mpr
        ⟨by simpa using hzre, xi_half_add_conj hxi⟩, ?_⟩
      simp; linarith
    · obtain ⟨hwL, hwim_le⟩ := Finset.mem_filter.mp hw
      obtain ⟨hwre, hxi⟩ := (mem_leftCentredZeros_iff hfin).mp hwL
      have hwim_ne := xi_half_add_im_ne_zero hxi
      have hwim_neg : w.im < 0 := lt_of_le_of_ne (not_lt.mp hwim_le) hwim_ne
      refine Finset.mem_filter.mpr ⟨(mem_leftCentredZeros_iff hfin).mpr
        ⟨by simpa using hwre, xi_half_add_conj hxi⟩, ?_⟩
      simp; linarith
  have hcard_left : (leftCentredZeros hfin).card = 2 * (upperLeftCentredZeros hfin).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := leftCentredZeros hfin) (p := fun z => 0 < z.im)
    change (upperLeftCentredZeros hfin).card + _ = _ at hsplit
    rw [hbij_left, ← two_mul] at hsplit
    exact hsplit.symm
  have hbij_rl : (upperRightCentredZeros hfin).card = (upperLeftCentredZeros hfin).card := by
    refine Finset.card_bij (fun z _ => -conj z) (fun z hz => ?_)
      (fun a _ b _ h => by simpa using congrArg conj (neg_inj.mp h))
      (fun w hw => ⟨-conj w, ?_, by simp⟩)
    · obtain ⟨hzR, hzim⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzre, hxi⟩ := (mem_rightCentredZeros_iff hfin).mp hzR
      refine Finset.mem_filter.mpr ⟨(mem_leftCentredZeros_iff hfin).mpr
        ⟨by simp; linarith, xi_half_add_neg (xi_half_add_conj hxi)⟩, by simpa using hzim⟩
    · obtain ⟨hwL, hwim⟩ := Finset.mem_filter.mp hw
      obtain ⟨hwre, hxi⟩ := (mem_leftCentredZeros_iff hfin).mp hwL
      refine Finset.mem_filter.mpr ⟨(mem_rightCentredZeros_iff hfin).mpr
        ⟨by simp; linarith, xi_half_add_neg (xi_half_add_conj hxi)⟩, by simpa using hwim⟩
  exact ⟨hcard_right, hcard_left, hbij_rl⟩

/-- Bijection between `rightCentredZeros hfin` and `{ρ ∈ zetaZeroConfig.carrier | ½ < Re ρ}`. -/
theorem encard_zetaRightZeros_eq_card_rightCentredZeros (hfin : BacklundConverse.FiniteOffLine) :
    {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard = (rightCentredZeros hfin).card := by
  have heq : {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re} =
      ((rightCentredZeros hfin).image fun z : ℂ => 1 / 2 + z) := by
    ext ρ
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      mem_rightCentredZeros_iff]
    constructor
    · rintro ⟨hmem, hgt⟩
      refine ⟨ρ - 1 / 2, ⟨by simp; linarith, ?_⟩, by ring⟩
      obtain ⟨hζ, hstrip⟩ := hmem
      have hne1 : ρ ≠ 1 := by intro h1; rw [h1] at hstrip; norm_num at hstrip
      have hxi0 := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos (by linarith) hne1).mpr hζ
      rwa [show (1 : ℂ) / 2 + (ρ - 1 / 2) = ρ by ring]
    · rintro ⟨z, ⟨hzre, hxi⟩, rfl⟩
      have hre_gt : 1 / 2 < ((1 : ℂ) / 2 + z).re := by simp; linarith
      have hxi_lt1 : ((1 : ℂ) / 2 + z).re < 1 := by
        obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
        rw [← hq]
        exact xiZeroCopy_re_lt_one q
      have hne1 : (1 : ℂ) / 2 + z ≠ 1 := by intro h1; rw [h1] at hxi_lt1; norm_num at hxi_lt1
      have hζ : riemannZeta (1 / 2 + z) = 0 :=
        (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos (by linarith) hne1).mp hxi
      exact ⟨⟨hζ, by linarith, hxi_lt1⟩, hre_gt⟩
  rw [heq, Set.encard_coe_eq_coe_finsetCard,
    Finset.card_image_of_injective _ fun a b h => add_left_cancel h]

/-- Real-linear evaluation map on `upperRightCentredZeros hfin` attached to `(k, F)`. -/
def upperRightEvalMap {k : ℕ} {F : Fin k → ℝ → ℝ}
    (hF : ∀ i, CriticalHalfLineEnergyDomain (F i))
    (hfin : BacklundConverse.FiniteOffLine) :
    (Fin k → ℝ) →ₗ[ℝ] (upperRightCentredZeros hfin → ℝ × ℝ) where
  toFun c z :=
    let v := negativeHalfLineLaplace (cx fun u => ∑ i : Fin k, c i * F i u) z.1
    (v.re, v.im)
  map_add' c₁ c₂ := by
    funext z
    have hz : -4 < z.1.re := by
      have := ((mem_rightCentredZeros_iff hfin).mp (Finset.mem_filter.mp z.2).1).1
      linarith
    rw [Pi.add_apply]
    dsimp only
    rw [negativeHalfLineLaplace_finset_sum Finset.univ (fun i _ => hF i) (c₁ + c₂) hz,
      negativeHalfLineLaplace_finset_sum Finset.univ (fun i _ => hF i) c₁ hz,
      negativeHalfLineLaplace_finset_sum Finset.univ (fun i _ => hF i) c₂ hz]
    ext <;> simp [Complex.re_sum, Complex.im_sum, add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    funext z
    have hz : -4 < z.1.re := by
      have := ((mem_rightCentredZeros_iff hfin).mp (Finset.mem_filter.mp z.2).1).1
      linarith
    rw [Pi.smul_apply, RingHom.id_apply]
    dsimp only
    rw [negativeHalfLineLaplace_finset_sum Finset.univ (fun i _ => hF i) (r • c) hz,
      negativeHalfLineLaplace_finset_sum Finset.univ (fun i _ => hF i) c hz]
    ext <;> simp [Complex.re_sum, Complex.im_sum, mul_assoc, Finset.mul_sum]

/-- Real-linear evaluation map on `upperLeftCentredZeros hfin` attached to `(k, F)`. -/
def upperLeftEvalMap {k : ℕ} {F : Fin k → ℝ → ℝ}
    (hF : ∀ i, CriticalHalfLineEnergyDomain (F i))
    (hfin : BacklundConverse.FiniteOffLine) :
    (Fin k → ℝ) →ₗ[ℝ] (upperLeftCentredZeros hfin → ℝ × ℝ) where
  toFun c z :=
    let v := negativeHalfLineLaplace (cx fun u => ∑ i : Fin k, c i * F i u) z.1
    (v.re, v.im)
  map_add' c₁ c₂ := by
    funext z
    have hz : -4 < z.1.re := by
      obtain ⟨_, hxi⟩ := (mem_leftCentredZeros_iff hfin).mp (Finset.mem_filter.mp z.2).1
      obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
      have hzc : centredZero q = z.1 := by rw [centredZero, hq]; ring
      have := (abs_lt.mp (abs_re_centredZero_lt q)).1
      rw [hzc] at this; linarith
    rw [Pi.add_apply]
    dsimp only
    rw [negativeHalfLineLaplace_finset_sum Finset.univ (fun i _ => hF i) (c₁ + c₂) hz,
      negativeHalfLineLaplace_finset_sum Finset.univ (fun i _ => hF i) c₁ hz,
      negativeHalfLineLaplace_finset_sum Finset.univ (fun i _ => hF i) c₂ hz]
    ext <;> simp [Complex.re_sum, Complex.im_sum, add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    funext z
    have hz : -4 < z.1.re := by
      obtain ⟨_, hxi⟩ := (mem_leftCentredZeros_iff hfin).mp (Finset.mem_filter.mp z.2).1
      obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
      have hzc : centredZero q = z.1 := by rw [centredZero, hq]; ring
      have := (abs_lt.mp (abs_re_centredZero_lt q)).1
      rw [hzc] at this; linarith
    rw [Pi.smul_apply, RingHom.id_apply]
    dsimp only
    rw [negativeHalfLineLaplace_finset_sum Finset.univ (fun i _ => hF i) (r • c) hz,
      negativeHalfLineLaplace_finset_sum Finset.univ (fun i _ => hF i) c hz]
    ext <;> simp [Complex.re_sum, Complex.im_sum, mul_assoc, Finset.mul_sum]

/-- **Upper-right zero evaluation is injective** on the span of any `W₈`-orthogonal family of
confined null vectors under `FiniteOffLine`. -/
theorem orthogonalNullSpan_eval_upperRight_injective {k : ℕ} {R : Fin k → ℝ}
    (hR : ∀ i, 0 < R i) {F : Fin k → ℝ → ℝ} (hF : ∀ i, IsConfinedNullVector (R i) (F i))
    (horth : ∀ i j, i ≠ j → (∫ u : ℝ, F i u * F j u * Real.exp (-(8 * u))) = 0)
    (hfin : BacklundConverse.FiniteOffLine) :
    Function.Injective (upperRightEvalMap (fun i => (hF i).1) hfin) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  rw [LinearMap.mem_ker] at hc
  set H : ℝ → ℝ := fun u => ∑ i : Fin k, c i * F i u
  have hvan_upper : ∀ z ∈ upperRightCentredZeros hfin,
      negativeHalfLineLaplace (cx H) z = 0 := by
    intro z hz
    have hz0 := congrFun hc ⟨z, hz⟩
    dsimp [upperRightEvalMap, H] at hz0
    exact Complex.ext (congrArg Prod.fst hz0) (congrArg Prod.snd hz0)
  have hvan_right : ∀ z ∈ rightCentredZeros hfin,
      negativeHalfLineLaplace (cx H) z = 0 := by
    intro z hz
    obtain ⟨hzre, hxi⟩ := (mem_rightCentredZeros_iff hfin).mp hz
    rcases lt_trichotomy z.im 0 with hlt | heq | hgt
    · have hconj_mem : conj z ∈ upperRightCentredZeros hfin :=
        Finset.mem_filter.mpr ⟨(mem_rightCentredZeros_iff hfin).mpr
          ⟨by simpa using hzre, xi_half_add_conj hxi⟩, by simp; linarith⟩
      have h0 := hvan_upper (conj z) hconj_mem
      rw [show cx H = fun u => (H u : ℂ) from rfl, negativeHalfLineLaplace_real_conj] at h0
      have hc0 := congrArg conj h0
      rw [Complex.conj_conj, map_zero] at hc0
      exact hc0
    · exact absurd heq (xi_half_add_im_ne_zero hxi)
    · exact hvan_upper z (Finset.mem_filter.mpr ⟨hz, hgt⟩)
  have hoff_zero : (∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx H) (centredZero q) *
      negativeHalfLineLaplace (cx H) (-centredZero q)) = 0 := by
    have hterm0 : (fun q : ↑onLineCopiesᶜ => negativeHalfLineLaplace (cx H) (centredZero q) *
        negativeHalfLineLaplace (cx H) (-centredZero q)) = fun _ => 0 := by
      funext q
      have hne : (centredZero q.1).re ≠ 0 := q.2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hmem : -centredZero q.1 ∈ rightCentredZeros hfin :=
          (mem_rightCentredZeros_iff hfin).mpr
            ⟨by simp; linarith, xi_half_add_neg (xi_centredZero q.1)⟩
        rw [hvan_right _ hmem, mul_zero]
      · have hmem : centredZero q.1 ∈ rightCentredZeros hfin :=
          (mem_rightCentredZeros_iff hfin).mpr ⟨hgt, xi_centredZero q.1⟩
        rw [hvan_right _ hmem, zero_mul]
    rw [hterm0, tsum_zero]
  obtain ⟨-, hpar⟩ := orthogonalNullSpan_zeroParseval_of_finiteOffLine hR hF horth hfin c
  rw [hoff_zero, add_zero] at hpar
  have hreal_eq := Complex.ofReal_injective hpar
  have hon_nn : 0 ≤ ∑' q : onLineCopies, zeroValueMass H q :=
    tsum_nonneg fun q => zeroValueMass_nonneg H q
  have hsum_nn : 0 ≤ ∑ i : Fin k, c i ^ 2 * criticalAliasCoefficient (R i) *
      ∫ u : ℝ, F i u ^ 2 * Real.exp (-(8 * u)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg
      (mul_nonneg (sq_nonneg (c i)) (criticalAliasCoefficient_positive (hR i)).le)
      (nullVector_confinementMass_pos (hF i)).le
  have hsum0 : ∑ i : Fin k, c i ^ 2 * criticalAliasCoefficient (R i) *
      (∫ u : ℝ, F i u ^ 2 * Real.exp (-(8 * u))) = 0 := by linarith
  funext i
  by_contra hci
  have hpos_i : 0 < c i ^ 2 * criticalAliasCoefficient (R i) *
      ∫ u : ℝ, F i u ^ 2 * Real.exp (-(8 * u)) :=
    mul_pos (mul_pos (sq_pos_of_ne_zero hci) (criticalAliasCoefficient_positive (hR i)))
      (nullVector_confinementMass_pos (hF i))
  have hle_i : c i ^ 2 * criticalAliasCoefficient (R i) *
      (∫ u : ℝ, F i u ^ 2 * Real.exp (-(8 * u))) ≤
      ∑ j : Fin k, c j ^ 2 * criticalAliasCoefficient (R j) *
        ∫ u : ℝ, F j u ^ 2 * Real.exp (-(8 * u)) :=
    Finset.single_le_sum (fun j _ => mul_nonneg
      (mul_nonneg (sq_nonneg (c j)) (criticalAliasCoefficient_positive (hR j)).le)
      (nullVector_confinementMass_pos (hF j)).le) (Finset.mem_univ i)
  linarith

/-- **Upper-left zero evaluation is injective** on the span of any `W₈`-orthogonal family of
confined null vectors under `FiniteOffLine`. -/
theorem orthogonalNullSpan_eval_upperLeft_injective {k : ℕ} {R : Fin k → ℝ}
    (hR : ∀ i, 0 < R i) {F : Fin k → ℝ → ℝ} (hF : ∀ i, IsConfinedNullVector (R i) (F i))
    (horth : ∀ i j, i ≠ j → (∫ u : ℝ, F i u * F j u * Real.exp (-(8 * u))) = 0)
    (hfin : BacklundConverse.FiniteOffLine) :
    Function.Injective (upperLeftEvalMap (fun i => (hF i).1) hfin) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  rw [LinearMap.mem_ker] at hc
  set H : ℝ → ℝ := fun u => ∑ i : Fin k, c i * F i u
  have hvan_upper : ∀ z ∈ upperLeftCentredZeros hfin,
      negativeHalfLineLaplace (cx H) z = 0 := by
    intro z hz
    have hz0 := congrFun hc ⟨z, hz⟩
    dsimp [upperLeftEvalMap, H] at hz0
    exact Complex.ext (congrArg Prod.fst hz0) (congrArg Prod.snd hz0)
  have hvan_left : ∀ z ∈ leftCentredZeros hfin,
      negativeHalfLineLaplace (cx H) z = 0 := by
    intro z hz
    obtain ⟨hzre, hxi⟩ := (mem_leftCentredZeros_iff hfin).mp hz
    rcases lt_trichotomy z.im 0 with hlt | heq | hgt
    · have hconj_mem : conj z ∈ upperLeftCentredZeros hfin :=
        Finset.mem_filter.mpr ⟨(mem_leftCentredZeros_iff hfin).mpr
          ⟨by simpa using hzre, xi_half_add_conj hxi⟩, by simp; linarith⟩
      have h0 := hvan_upper (conj z) hconj_mem
      rw [show cx H = fun u => (H u : ℂ) from rfl, negativeHalfLineLaplace_real_conj] at h0
      have hc0 := congrArg conj h0
      rw [Complex.conj_conj, map_zero] at hc0
      exact hc0
    · exact absurd heq (xi_half_add_im_ne_zero hxi)
    · exact hvan_upper z (Finset.mem_filter.mpr ⟨hz, hgt⟩)
  have hoff_zero : (∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx H) (centredZero q) *
      negativeHalfLineLaplace (cx H) (-centredZero q)) = 0 := by
    have hterm0 : (fun q : ↑onLineCopiesᶜ => negativeHalfLineLaplace (cx H) (centredZero q) *
        negativeHalfLineLaplace (cx H) (-centredZero q)) = fun _ => 0 := by
      funext q
      have hne : (centredZero q.1).re ≠ 0 := q.2
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hmem : centredZero q.1 ∈ leftCentredZeros hfin :=
          (mem_leftCentredZeros_iff hfin).mpr ⟨hlt, xi_centredZero q.1⟩
        rw [hvan_left _ hmem, zero_mul]
      · have hmem : -centredZero q.1 ∈ leftCentredZeros hfin :=
          (mem_leftCentredZeros_iff hfin).mpr
            ⟨by simp; linarith, xi_half_add_neg (xi_centredZero q.1)⟩
        rw [hvan_left _ hmem, mul_zero]
    rw [hterm0, tsum_zero]
  obtain ⟨-, hpar⟩ := orthogonalNullSpan_zeroParseval_of_finiteOffLine hR hF horth hfin c
  rw [hoff_zero, add_zero] at hpar
  have hreal_eq := Complex.ofReal_injective hpar
  have hon_nn : 0 ≤ ∑' q : onLineCopies, zeroValueMass H q :=
    tsum_nonneg fun q => zeroValueMass_nonneg H q
  have hsum0 : ∑ i : Fin k, c i ^ 2 * criticalAliasCoefficient (R i) *
      (∫ u : ℝ, F i u ^ 2 * Real.exp (-(8 * u))) = 0 := by
    have hsum_nn : 0 ≤ ∑ i : Fin k, c i ^ 2 * criticalAliasCoefficient (R i) *
        ∫ u : ℝ, F i u ^ 2 * Real.exp (-(8 * u)) :=
      Finset.sum_nonneg fun i _ => mul_nonneg
        (mul_nonneg (sq_nonneg (c i)) (criticalAliasCoefficient_positive (hR i)).le)
        (nullVector_confinementMass_pos (hF i)).le
    linarith
  funext i
  by_contra hci
  have hpos_i : 0 < c i ^ 2 * criticalAliasCoefficient (R i) *
      ∫ u : ℝ, F i u ^ 2 * Real.exp (-(8 * u)) :=
    mul_pos (mul_pos (sq_pos_of_ne_zero hci) (criticalAliasCoefficient_positive (hR i)))
      (nullVector_confinementMass_pos (hF i))
  have hle_i : c i ^ 2 * criticalAliasCoefficient (R i) *
      (∫ u : ℝ, F i u ^ 2 * Real.exp (-(8 * u))) ≤
      ∑ j : Fin k, c j ^ 2 * criticalAliasCoefficient (R j) *
        ∫ u : ℝ, F j u ^ 2 * Real.exp (-(8 * u)) :=
    Finset.single_le_sum (fun j _ => mul_nonneg
      (mul_nonneg (sq_nonneg (c j)) (criticalAliasCoefficient_positive (hR j)).le)
      (nullVector_confinementMass_pos (hF j)).le) (Finset.mem_univ i)
  linarith

private theorem finrank_upperLeftTarget (hfin : BacklundConverse.FiniteOffLine) :
    Module.finrank ℝ (upperLeftCentredZeros hfin → ℝ × ℝ) = (rightCentredZeros hfin).card := by
  obtain ⟨hR_card, _, hRL_card⟩ := card_right_and_left_centredZeros hfin
  rw [Module.finrank_pi_fintype ℝ, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    smul_eq_mul, Module.finrank_prod, Module.finrank_self]
  omega

/-- **Sharp multiplicity-free dimension bound on higher critical states.**
Under `FiniteOffLine`, any `W₈`-orthogonal family of `k` confined null vectors has size at most
the number `#Z_right` of **distinct** zeros of `ζ` right of the critical line. -/
theorem card_orthogonalNullVectors_le_rightZeros_of_finiteOffLine {k : ℕ} {R : Fin k → ℝ}
    (hR : ∀ i, 0 < R i) {F : Fin k → ℝ → ℝ} (hF : ∀ i, IsConfinedNullVector (R i) (F i))
    (horth : ∀ i j, i ≠ j → (∫ u : ℝ, F i u * F j u * Real.exp (-(8 * u))) = 0)
    (hfin : BacklundConverse.FiniteOffLine) :
    k ≤ (rightCentredZeros hfin).card ∧
      (k : ℕ∞) ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard := by
  have hinj := orthogonalNullSpan_eval_upperLeft_injective hR hF horth hfin
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fin_fun ℝ, finrank_upperLeftTarget hfin] at hle
  refine ⟨hle, ?_⟩
  rw [encard_zetaRightZeros_eq_card_rightCentredZeros hfin]
  exact_mod_cast hle

/-- **Single-conjugate-pair beyond-the-wall pole isolation.**
When a `W₈`-orthogonal family of confined null vectors achieves full dimension
`k = (rightCentredZeros hfin).card`, for every upper-half-plane left zero
`z* ∈ upperLeftCentredZeros hfin` and every `w₀ ∈ ℂ` (`w₀ ≠ 0`), there exists a **unique** real
combination `c : Fin k → ℝ` whose profile `H = ∑_i c_i F_i` satisfies:
1. `L H(z*) = w₀` and `L H(conj z*) = conj w₀`;
2. `L H(z) = 0` at every other left zero `z ∈ leftCentredZeros hfin \ {z*, conj z*}`;
3. `¬ HasBeyondTheWallPrimeContinuation H`. -/
theorem existsUnique_singlePair_leftZero_isolator_of_finiteOffLine {k : ℕ} {R : Fin k → ℝ}
    (hR : ∀ i, 0 < R i) {F : Fin k → ℝ → ℝ} (hF : ∀ i, IsConfinedNullVector (R i) (F i))
    (horth : ∀ i j, i ≠ j → (∫ u : ℝ, F i u * F j u * Real.exp (-(8 * u))) = 0)
    (hfin : BacklundConverse.FiniteOffLine)
    (hfull : k = (rightCentredZeros hfin).card)
    {z_star : ℂ} (hz_star : z_star ∈ upperLeftCentredZeros hfin) {w₀ : ℂ} (hw₀ : w₀ ≠ 0) :
    ∃! c : Fin k → ℝ,
      let H : ℝ → ℝ := fun u => ∑ i : Fin k, c i * F i u
      negativeHalfLineLaplace (cx H) z_star = w₀ ∧
      negativeHalfLineLaplace (cx H) (conj z_star) = conj w₀ ∧
      (∀ z ∈ leftCentredZeros hfin, z ≠ z_star → z ≠ conj z_star →
        negativeHalfLineLaplace (cx H) z = 0) ∧
      ¬ HasBeyondTheWallPrimeContinuation H := by
  classical
  let E := upperLeftEvalMap (fun i => (hF i).1) hfin
  have hinj : Function.Injective E :=
    orthogonalNullSpan_eval_upperLeft_injective hR hF horth hfin
  have hrank_eq : Module.finrank ℝ (LinearMap.range E) =
      Module.finrank ℝ (upperLeftCentredZeros hfin → ℝ × ℝ) := by
    rw [← (LinearEquiv.ofInjective E hinj).finrank_eq, Module.finrank_fin_fun ℝ,
      finrank_upperLeftTarget hfin, hfull]
  have hsurj : Function.Surjective E := by
    rw [← LinearMap.range_eq_top]
    exact Submodule.eq_top_of_finrank_eq hrank_eq
  let target : upperLeftCentredZeros hfin → ℝ × ℝ := fun z =>
    if z.1 = z_star then (w₀.re, w₀.im) else (0, 0)
  obtain ⟨c, hc⟩ := hsurj target
  have hH_val : ∀ z ∈ upperLeftCentredZeros hfin,
      negativeHalfLineLaplace (cx fun u => ∑ i : Fin k, c i * F i u) z =
        if z = z_star then w₀ else 0 := by
    intro z hz
    have hz_eq := congrFun hc ⟨z, hz⟩
    dsimp [E, upperLeftEvalMap, target] at hz_eq
    by_cases hzz : z = z_star
    · rw [if_pos hzz] at hz_eq ⊢
      exact Complex.ext (congrArg Prod.fst hz_eq) (congrArg Prod.snd hz_eq)
    · rw [if_neg hzz] at hz_eq ⊢
      exact Complex.ext (congrArg Prod.fst hz_eq) (congrArg Prod.snd hz_eq)
  refine ⟨c, ?_, ?_⟩
  · dsimp only
    have h1 : negativeHalfLineLaplace (cx fun u => ∑ i : Fin k, c i * F i u) z_star = w₀ := by
      simpa using hH_val z_star hz_star
    have h2 : negativeHalfLineLaplace (cx fun u => ∑ i : Fin k, c i * F i u) (conj z_star) =
        conj w₀ := by
      rw [show (cx fun u => ∑ i : Fin k, c i * F i u) =
        fun u => ((∑ i : Fin k, c i * F i u : ℝ) : ℂ) from rfl,
        negativeHalfLineLaplace_real_conj]
      exact congrArg conj h1
    refine ⟨h1, h2, fun z hz hne1 hne2 => ?_, ?_⟩
    · obtain ⟨hzre, hxi⟩ := (mem_leftCentredZeros_iff hfin).mp hz
      rcases lt_trichotomy z.im 0 with hlt | heq | hgt
      · have hconj_mem : conj z ∈ upperLeftCentredZeros hfin :=
          Finset.mem_filter.mpr ⟨(mem_leftCentredZeros_iff hfin).mpr
            ⟨by simpa using hzre, xi_half_add_conj hxi⟩, by simp; linarith⟩
        have hcz_ne : conj z ≠ z_star := fun h => hne2 (by rw [← h, Complex.conj_conj])
        have h0 := hH_val (conj z) hconj_mem
        rw [if_neg hcz_ne, show (cx fun u => ∑ i : Fin k, c i * F i u) =
          fun u => ((∑ i : Fin k, c i * F i u : ℝ) : ℂ) from rfl,
          negativeHalfLineLaplace_real_conj] at h0
        have hc0 := congrArg conj h0
        rw [Complex.conj_conj, map_zero] at hc0
        exact hc0
      · exact absurd heq (xi_half_add_im_ne_zero hxi)
      · have h0 := hH_val z (Finset.mem_filter.mpr ⟨hz, hgt⟩)
        rwa [if_neg hne1] at h0
    · obtain ⟨hzL, -⟩ := Finset.mem_filter.mp hz_star
      obtain ⟨hzre, hxi⟩ := (mem_leftCentredZeros_iff hfin).mp hzL
      obtain ⟨q_star, hq_star⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
      have hzc : centredZero q_star = z_star := by rw [centredZero, hq_star]; ring
      exact not_wallPrimeBalance_continues_of_seen_zero
        (energyDomain_finset_sum Finset.univ (fun i _ => (hF i).1) c)
        (by norm_num : (0 : ℝ) ≤ 5 / 2)
        (c := q_star) (by rwa [hzc]) (by rwa [hzc, h1])
  · intro c' hc'
    dsimp only at hc'
    apply hinj
    rw [hc]
    funext z
    dsimp [E, upperLeftEvalMap, target]
    by_cases hzz : z.1 = z_star
    · rw [if_pos hzz, hzz, hc'.1]
    · have hzL : z.1 ∈ leftCentredZeros hfin := (Finset.mem_filter.mp z.2).1
      have hzim : 0 < z.1.im := (Finset.mem_filter.mp z.2).2
      have hne_conj : z.1 ≠ conj z_star := by
        intro h
        have hzs_im : 0 < z_star.im := (Finset.mem_filter.mp hz_star).2
        have := congrArg Complex.im h
        simp at this
        linarith
      have h0 := hc'.2.2.1 z.1 hzL hzz hne_conj
      rw [if_neg hzz, h0]
      simp

/-! ### 3. Model refutations without joint `(atomic Λ_B ≥ 0) ∧ (Lévy FE)` and Beurling–Lévy rigidity -/

/-- **Model separation (Answer to E-Q2 at the soft / single-input level: NO).**
For every finite window length `n` and arbitrarily large on-line unitary layer `2M`
(`M = n * 2^n + n + 1`), the curve datum `hidingDatum M` (`q = 2`) has:
1. Hodge positivity on all span classes of degree `< n` (not decided by any finite window, T4);
2. `2M` unitary on-line roots together with a finite off-line layer `{2, 1/2}` (`N = 1 > 0`);
3. A unit confined critical ground state `f*` at `a* > 0` satisfying exact zero Parseval, curve
   `(★)`, and the exact rational beyond-the-wall prime-head identity. -/
theorem soft_finiteLayer_does_not_force_zero_states (n : ℕ) :
    let M : ℕ := n * 2 ^ n + n + 1
    let D := hidingDatum M
    CurveModels.InFourStrip D ∧
    (∀ S ⊆ Finset.range n, ∀ d, 0 ≤ D.spanDefect S d) ∧
    D.outerSpectrum.card = 1 ∧
    ∃ (a : ℝ) (f : ℕ → ℝ),
      CurveModels.curveConfinementMass D f = 1 ∧
      CurveModels.IsCurveCriticalState D a f ∧
      (∑ i ∈ Finset.univ.filter (fun i => ‖D.β i‖ = 1), ‖CurveModels.curveLaplace f (D.β i)‖ ^ 2) +
        (∑ i ∈ Finset.univ.filter (fun i => ‖D.β i‖ ≠ 1),
          (CurveModels.curveLaplace f (D.β i) * CurveModels.curveLaplace f (D.β i)⁻¹).re) =
        -a ∧
      ¬ CurveModels.CurveBeyondTheWallPrimeContinuation D := by
  intro M D
  haveI : NeZero M := ⟨by dsimp [M]; omega⟩
  have hn : ∀ k : ℕ, ‖Complex.exp (2 * Real.pi * I / M) ^ k‖ = 1 := fun k => by
    rw [norm_pow, Complex.norm_exp]; simp
  have hfour : CurveModels.InFourStrip D := by
    intro x
    change ‖(hidingDatum M).β x‖ < (2 : ℝ) ^ 4
    rcases x with b | ⟨k, b⟩ <;> cases b
    · simp [hidingDatum]; norm_num
    · simp [hidingDatum]; norm_num
    · change ‖conj (Complex.exp (2 * Real.pi * I / M) ^ (k : ℕ))‖ < (2 : ℝ) ^ 4
      rw [Complex.norm_conj, hn]; norm_num
    · change ‖Complex.exp (2 * Real.pi * I / M) ^ (k : ℕ)‖ < (2 : ℝ) ^ 4
      rw [hn]; norm_num
  have hnotU : ¬ ∀ x, ‖D.β x‖ = 1 := by
    intro h
    have h2 := h (Sum.inl true)
    simp [D, hidingDatum] at h2
  have hout : D.outerSpectrum.card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨(2 : ℂ), Finset.ext fun z => ?_⟩
    simp only [CurveDatum.outerSpectrum, CurveDatum.spectrum, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨x, rfl⟩, hz⟩
      rcases x with b | ⟨k, b⟩ <;> cases b
      · simp [D, hidingDatum] at hz; norm_num at hz
      · simp [D, hidingDatum]
      · change 1 < ‖conj (Complex.exp (2 * Real.pi * I / M) ^ (k : ℕ))‖ at hz
        rw [Complex.norm_conj, hn] at hz
        exact absurd hz (lt_irrefl _)
      · change 1 < ‖Complex.exp (2 * Real.pi * I / M) ^ (k : ℕ)‖ at hz
        rw [hn] at hz
        exact absurd hz (lt_irrefl _)
    · rintro rfl
      exact ⟨⟨Sum.inl true, by simp [D, hidingDatum]⟩, by norm_num⟩
  -- Window positivity `< n`: reuse `exists_hidden_on_window` bound directly on `hidingDatum M`.
  have hwin : ∀ S ⊆ Finset.range n, ∀ d, 0 ≤ D.spanDefect S d := by
    intro S hS d
    rw [D.spanDefect_eq_toeplitz]
    set e : ℕ → ℝ := fun k => d k * D.sqrtq ^ k
    by_cases hS0 : S = ∅
    · simp [hS0, CurveDatum.toeplitz]
    have hcardS : S.card ≤ n := (Finset.card_le_card hS).trans (by simp)
    -- Diagonal `2 + 2M` vs off-diagonal `|trace j| = 2^j + 2^{-j} ≤ 2^n + 1` (`0 < j < n`).
    have hoff_eq : D.toeplitz S e =
        (2 + 2 * (M : ℝ)) * (∑ k ∈ S, e k ^ 2) +
          ∑ k ∈ S, ∑ l ∈ S, e k * e l *
            (if k = l then 0 else D.trace (Nat.dist k l)) := by
      unfold CurveDatum.toeplitz
      have h0 : D.trace 0 = 2 + 2 * (M : ℝ) := by
        rw [D.trace_zero, card_hiding M]; push_cast; ring
      have hsum_diag : (2 + 2 * (M : ℝ)) * (∑ k ∈ S, e k ^ 2) =
          ∑ k ∈ S, ∑ l ∈ S, if k = l then e k * e l * D.trace (Nat.dist k l) else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.sum_ite_eq S k, if_pos hk, Nat.dist_self, h0]; ring
      rw [hsum_diag, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs <;> ring
    have hbound_c : ∀ k ∈ S, ∀ l ∈ S,
        |(if k = l then (0 : ℝ) else D.trace (Nat.dist k l))| ≤ (2 : ℝ) ^ n + 1 := by
      intro k hk l hl
      split_ifs with hkl
      · simp; positivity
      · have hk_lt : k < n := Finset.mem_range.mp (hS hk)
        have hl_lt : l < n := Finset.mem_range.mp (hS hl)
        have hdist_pos : Nat.dist k l ≠ 0 := by rw [Nat.dist]; omega
        have hdist_lt : Nat.dist k l < n := by
          rcases le_total k l with h | h
          · rw [Nat.dist_eq_sub_of_le h]; omega
          · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]; omega
        have hdist_M : Nat.dist k l < M := by dsimp [M]; omega
        rw [hidingDatum_trace hdist_pos hdist_M, abs_of_nonneg (by positivity)]
        have hp1 : (2 : ℝ) ^ Nat.dist k l ≤ (2 : ℝ) ^ n :=
          pow_le_pow_right₀ (by norm_num) hdist_lt.le
        have hp2 : (1 / 2 : ℝ) ^ Nat.dist k l ≤ 1 :=
          pow_le_one₀ (by positivity) (by norm_num)
        linarith
    have hlow := sum_mul_ge_of_abs_le S e
      (fun k l => if k = l then 0 else D.trace (Nat.dist k l))
      (C := (2 : ℝ) ^ n + 1) (by positivity) hbound_c
    have hcoef : ((2 : ℝ) ^ n + 1) * S.card ≤ 2 + 2 * (M : ℝ) := by
      have hSc : (S.card : ℝ) ≤ n := by exact_mod_cast hcardS
      have hM_val : (M : ℝ) = (n : ℝ) * (2 : ℝ) ^ n + n + 1 := by dsimp [M]; push_cast; ring
      have hprod : ((2 : ℝ) ^ n + 1) * S.card ≤ ((2 : ℝ) ^ n + 1) * n :=
        mul_le_mul_of_nonneg_left hSc (by positivity)
      linarith
    have hsq_sum : 0 ≤ ∑ k ∈ S, e k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hcoef hsq_sum
    linarith
  obtain ⟨a, f, hmass, hcrit, -⟩ :=
    CurveModels.exists_curveGroundState_of_not_unitary D hfour hnotU
  obtain ⟨hpar, -⟩ := CurveModels.curveCriticalState_zeroParseval D hcrit
  rw [hmass, mul_one] at hpar
  exact ⟨hfour, hwin, hout, a, f, hmass, hcrit, hpar, fun hcont =>
    CurveModels.not_isCurveCriticalState_of_beyondWallContinuation D hfour hcont a f hcrit⟩

/-- **Continuous half-line refutation without the Lévy functional equation (`overRegularZeta`).**
There exists an explicit continuous Beurling zeta function (`μ = 2/5, ν = 1/10, γ = 1`) with
nonnegative prime density `w(t) ≥ 0` on `(0, ∞)`, nonnegative integer density, integer count error
`N(x) - ρ x - C → 0`, and a genuine off-line zero at `3/5 + i` (`1/2 < 3/5 < 1`). -/
theorem overRegular_finiteLayer_nonnegPrimes_has_offLineZero :
    (∀ t : ℝ, 0 < t → 0 ≤ BeurlingOverRegularIntegers.primeDensity (2 / 5) (1 / 10) 1 t) ∧
      BeurlingOverRegularIntegers.overRegularZeta (2 / 5) (1 / 10) 1 ((3 / 5 : ℝ) + I) = 0 ∧
      ((((3 / 5 : ℝ) : ℂ) + I - 1) * (((3 / 5 : ℝ) : ℂ) + I + (1 / 10 : ℝ)) *
        (((3 / 5 : ℝ) : ℂ) + I + (3 / 10 : ℝ)) ≠ 0) := by
  have h := BeurlingOverRegularIntegers.overRegular_integers_do_not_constrain_zeros
    (μ := 2 / 5) (ν := 1 / 10) (γ := 1) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨h.1, ?_, ?_⟩
  · convert h.2.2.2.2.2.2.2.1 using 2; norm_num
  · convert h.2.2.2.2.2.2.2.2.2 using 2 <;> norm_num

/-- **Beurling–Lévy rigidity bridge (`beurlingSystem_rigidity_of_finiteEnergy_defect`).**
Every countable Beurling system (`Λ_B ≥ 0`) satisfying the `Γ_ℝ` functional equation up to an `L²`
strip defect coincides with `riemannZeta` on `Re s > 1` and its prime norms biject with the
rational primes — explaining why any Stage-2 contradiction using both countable `Λ_B ≥ 0` and the
exact `Γ_ℝ` functional equation applies exclusively to `ζ`. -/
theorem beurling_levy_rigidity_forces_zeta
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hBsum : Summable fun x : B.Integer => B.intNorm x ^ (-(3 / 2 : ℝ)))
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {Ng : ℕ}
    (hEc : ContinuousOn E (HTGeometry.verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ HTGeometry.verticalStrip (1 / 2) (3 / 2),
      ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * ArithmeticPositiveDuality.beurlingZeta B s =
        E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
    (hgm : Measurable g) (hgb : ∀ t : ℝ, ‖g t‖ ≤ Cg * (1 + |t|) ^ Ng)
    (hg : MemLp g 2 (volume : Measure ℝ)) :
    (∀ s : ℂ, 1 < s.re → ArithmeticPositiveDuality.beurlingZeta B s = riemannZeta s) ∧
      Nonempty {e : B.Label ≃ {p : ℕ // Nat.Prime p} //
        ∀ l : B.Label, B.labelNorm l = ((e l : ℕ) : ℝ)} := by
  have h := EulerFETransportTheory.beurlingSystem_rigidity_of_finiteEnergy_defect
    B hBsum hEc hEd hdecay hR hC hgm hgb hg
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩

/-! ### 4. Complete six-way ECS equivalence of B13 (`FiniteOffLine → RiemannHypothesis`) -/

private theorem infiniteRank_finiteOffLine_iff_backlund :
    InfiniteRankWeilTheory.FiniteOffLine ↔ BacklundConverse.FiniteOffLine := by
  unfold InfiniteRankWeilTheory.FiniteOffLine BacklundConverse.FiniteOffLine
  have heq : {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2} =
      {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0} := by
    ext q
    have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
      simp [xiSpectralPoint, Complex.mul_im]
    simp only [Set.mem_setOf_eq, him]
    constructor <;> intro h h0 <;> apply h <;> linarith
  rw [heq]

/-- **Complete ECS equivalence of Stage 2 / B13.**
Unconditionally, the following six statements are equivalent:
1. `BacklundConverse.FiniteOffLine → RiemannHypothesis` (**B13**);
2. `BacklundConverse.FiniteOffLine → ¬ ∃ W₀ F, 0 < W₀ ∧ (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = W₀ ∧ IsCriticalHalfLineGroundState W₀ F` (**no critical ground state in the finite stratum**);
3. `BacklundConverse.FiniteOffLine → ∀ R > 0, ∀ F, ¬ IsConfinedNullVector R F` (**no confined null vector at any positive ratio in the finite stratum**);
4. `BacklundConverse.FiniteOffLine → ZetaBeyondTheWallPrimeContinuation` (**beyond-the-wall prime-head continuation in the finite stratum**);
5. `BacklundConverse.FiniteOffLine → ∃ ℓ > 0, ∃ G : Set ℕ, Thick G ∧ ∃ C : ℝ, ∀ ν ∈ G, ‖weilLagFunction (ν * ℓ)‖ ≤ C` (**thick-lag boundedness in the finite stratum**);
6. `realPacketNegIndex = 0 ∨ realPacketNegIndex = ⊤` (**zero-or-infinite Weil packet-index dichotomy**). -/
theorem finiteLayer_ecs_b13_tfae :
    [BacklundConverse.FiniteOffLine → RiemannHypothesis,
      BacklundConverse.FiniteOffLine →
        ¬ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
          (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
          IsCriticalHalfLineGroundState W₀ F,
      BacklundConverse.FiniteOffLine →
        ∀ (R : ℝ), 0 < R → ∀ F : ℝ → ℝ, ¬ IsConfinedNullVector R F,
      BacklundConverse.FiniteOffLine → ZetaBeyondTheWallPrimeContinuation,
      BacklundConverse.FiniteOffLine →
        ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ G : Set ℕ, InfiniteRankWeilTheory.Thick G ∧ ∃ C : ℝ,
          ∀ ν ∈ G, ‖weilLagFunction (ν * ℓ)‖ ≤ C,
      realPacketNegIndex = 0 ∨ realPacketNegIndex = ⊤].TFAE := by
  tfae_have 1 ↔ 4 := by
    constructor <;> intro h hfin
    · exact zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis.mpr (h hfin)
    · exact zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis.mp (h hfin)
  tfae_have 4 ↔ 2 := by
    constructor <;> intro h hfin
    · exact zetaBeyondTheWallPrimeContinuation_iff_no_criticalState.mp (h hfin)
    · exact zetaBeyondTheWallPrimeContinuation_iff_no_criticalState.mpr (h hfin)
  tfae_have 3 → 2 := by
    intro h hfin ⟨W₀, F, hW, ht, hF⟩
    exact h hfin W₀ hW F (isConfinedNullVector_of_groundState hW ht hF)
  tfae_have 1 → 3 := by
    intro h hfin R hR F hnull
    have hRH : RiemannHypothesis := h hfin
    -- A single null vector (`k = 1`) injects into `rightCentredZeros hfin`, forcing `1 ≤ #Z_right`.
    have hle := (card_orthogonalNullVectors_le_rightZeros_of_finiteOffLine
      (k := 1) (R := fun _ => R) (fun _ => hR) (F := fun _ => F) (fun _ => hnull)
      (fun i j hij => absurd (Subsingleton.elim i j) hij) hfin).2
    obtain ⟨ρ, ⟨⟨hζ, h0, h1⟩, hgt⟩⟩ :
        (∃ ρ, ρ ∈ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}) := by
      by_contra hempty
      push Not at hempty
      have hset0 : {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re} = ∅ :=
        Set.eq_empty_of_forall_notMem hempty
      rw [hset0, Set.encard_empty] at hle
      exact absurd hle (by decide)
    have hre_half : ρ.re = 1 / 2 := by
      refine hRH ρ hζ ?_ ?_
      · rintro ⟨n, hn⟩
        rw [hn] at h0; simp at h0
        linarith [Nat.cast_nonneg (α := ℝ) n]
      · intro heq1; rw [heq1] at h1; norm_num at h1
    linarith
  tfae_have 1 ↔ 5 := by
    have hb13 := InfiniteRankWeilTheory.b13_iff_thick_lag_bounded
    rw [infiniteRank_finiteOffLine_iff_backlund] at hb13
    exact hb13
  tfae_have 1 ↔ 6 :=
    ArithmeticCastelnuovoSeveri.finiteOffLine_imp_rh_iff_packetIndex_zero_or_infinite
  tfae_finish

#print axioms nullVector_zeroParseval_of_finiteOffLine
#print axioms orthogonalNullSpan_zeroParseval_of_finiteOffLine
#print axioms orthogonalNullSpan_eval_upperRight_injective
#print axioms orthogonalNullSpan_eval_upperLeft_injective
#print axioms card_orthogonalNullVectors_le_rightZeros_of_finiteOffLine
#print axioms existsUnique_singlePair_leftZero_isolator_of_finiteOffLine
#print axioms soft_finiteLayer_does_not_force_zero_states
#print axioms overRegular_finiteLayer_nonnegPrimes_has_offLineZero
#print axioms beurling_levy_rigidity_forces_zeta
#print axioms finiteLayer_ecs_b13_tfae

end GaloisForLFunctions.ExclusionOfTheCriticalState
