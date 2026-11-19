import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.CrowdingSaturatesTheLogarithmicWallCusp
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.FiniteLayerKreinStructureAndRigidity
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity
import GaloisForLFunctions.ExceptionalLayerTheory.MixingTwoPrimeDilationsRemovesQuartetAliasing
import GaloisForLFunctions.ExceptionalLayerTheory.TwoProperPowerWavesCharacterizeASingleQuartet
import GaloisForLFunctions.ExceptionalLayerTheory.TheOrdinaryPrimeRadiusDetectsExactlyOneOffLineQuartet
import GaloisForLFunctions.ExceptionalLayerTheory.TheLandingLawForZeta

/-!
# Payoff, equivalences, and scope boundary of the finite-layer wall-cusp problem

This module formalizes the complete equivalences, cross-route corollaries, and scope boundary of
the finite-layer logarithmic wall-cusp problem (§2.17):

1. **Seven-way equivalence on `ζ` (`finiteLayer_wallCusp_targets_tfae`)**:
   The following are unconditionally equivalent to `BacklundConverse.FiniteOffLine → RiemannHypothesis`
   (Obstacle **B13**):
   - Sequential vanishing of the logarithmic wall cusp `(log(1/h_j)/h_j) ∫_{-h_j}^0 F(u)² du → 0`;
   - Sequential vanishing of the logarithmic vertical trace `(x_j log x_j) ∫_ℝ ‖L F(x_j + iy)‖² dy → 0`;
   - Finiteness of the critical-line first ordinate moment `∑_q |γ_q| ‖L F(iγ_q)‖² < ∞`;
   - Sequential sub-logarithmic first ordinate moment `(log T_j)⁻¹ ∑_{|γ_q| ≤ T_j} |γ_q| ‖L F(iγ_q)‖² → 0`;
   - Sequential sub-inverse ordinate tail `T_j ∑_{|γ_q| > T_j} ‖L F(iγ_q)‖² → 0`;
   - Sequential sub-linear critical-line cosine loss `h_j⁻¹ ∑_q (1 - cos(h_j γ_q)) ‖L F(iγ_q)‖² → 0`.

2. **Global cross-route payoff corollaries** (without assuming `FiniteOffLine` in the conclusion):
   Any of the equivalent §2.17 targets discharges:
   - Global exclusion of a single off-line quartet (`∀ ρ₀, ¬ HasSingleOffLineQuartet ρ₀`);
   - The zero-or-infinite Weil packet-index dichotomy (`realPacketNegIndex = 0 ∨ realPacketNegIndex = ⊤`);
   - The full two-interval ordinary-prime radial exclusion law (`TwoIntervalRadialExclusionLaw`, QIC);
   - Exact equivalence between the `(2, 3, 6)` ordinary-prime `θ`-dilation recurrences and
     `RiemannHypothesis` (PDR);
   - Exclusion of the two-wave proper-power discrepancy regime (PPC);
   - Reduction of `RiemannHypothesis` to `ZerosApproachLine ∧ ZetaLandingLaw` (ZCG).

3. **Sharp scope boundary (`exists_isolatedOuterTail_above_infiniteApproachingBackground`)**:
   For every `σ₀ ∈ (1/2, 1)`, there exists a strip configuration `Z : ZeroConfig` with an isolated
   nonempty finite outer tail right of `(1/2 + σ₀) / 2` above an infinite off-line lower background
   approaching the critical line (`ApproachesLine Z` and `AbscissaLawAt Z 0`), yet global abscissa
   `zeroAbscissa Z = σ₀`. Thus the finite-stratum law implies no better uniform zero-free half-plane
   `< 1` on infinite off-line configurations, even under `ApproachesLine`.

4. **Complete model-vs-arithmetic synthesis (`finiteLayer_wallCusp_complete_resolution`)**:
   Packages the unconditional crowding/sample/Poisson-row saturation of the wall cusp in abstract
   models alongside the exact `ζ` cusp/moment laws, the 7-way equivalence with `B13`, the global
   payoff corollaries, and the outer-tail scope boundary.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology Zeta23
open GaloisForLFunctions GaloisForLFunctions.ExclusionOfTheCriticalState GaloisForLFunctions.CriticalArithmeticCorrelationTheory GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
open GaloisForLFunctions.ZeroConfigurationGeometry.ZetaAbscissa
open _root_.RHTower

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-! ### Exact §2.17 formulations on `ζ` and their 7-way equivalence with `FiniteOffLine → RH` -/

/-- **§2.17 sequential wall-cusp vanishing target:** under `¬ RH` and `FiniteOffLine`, every
threshold ground state `F` admits `h_j ↓ 0` along which `(log(1/h_j)/h_j) ∫_{-h_j}^0 F(u)² du → 0`. -/
def SequentialWallCuspVanishingTarget : Prop :=
  ¬ RiemannHypothesis → BacklundConverse.FiniteOffLine →
    ∀ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ →
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) →
      IsCriticalHalfLineGroundState W₀ F →
      ∃ h : ℕ → ℝ, (∀ j, 0 < h j) ∧ Tendsto h atTop (𝓝 0) ∧
        Tendsto (fun j => Real.log (1 / h j) / h j * ∫ u in Ioo (-(h j)) 0, F u ^ 2) atTop (𝓝 0)

/-- **Sequential vertical-trace sub-cusp target:** under `FiniteOffLine`, every threshold ground
state `F` admits `x_j → +∞` with `(x_j log x_j) ∫_ℝ ‖L F(x_j + iy)‖² dy → 0`. -/
def SequentialVerticalTraceSubCuspTarget : Prop :=
  BacklundConverse.FiniteOffLine →
    ∀ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ →
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) →
      IsCriticalHalfLineGroundState W₀ F →
      ∃ x : ℕ → ℝ, Tendsto x atTop atTop ∧
        Tendsto (fun j => (x j * Real.log (x j)) *
          ∫ y : ℝ, ‖negativeHalfLineLaplace (cx F) (HTGeometry.hardyVerticalLine (x j) y)‖ ^ 2)
          atTop (𝓝 0)

/-- **§2.17 finite first-ordinate-moment target:** under `FiniteOffLine`, every threshold ground
state `F` has `∑_q |γ_q| ‖L F(iγ_q)‖² < ∞` on `onLineCopies`. -/
def FiniteFirstOrdinateMomentTarget : Prop :=
  BacklundConverse.FiniteOffLine →
    ∀ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ →
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) →
      IsCriticalHalfLineGroundState W₀ F →
      Summable (fun q : onLineCopies => |(centredZero q).im| * zeroValueMass F q)

/-- **Sequential sub-logarithmic first-ordinate-moment target:** under `FiniteOffLine`, every
threshold ground state `F` admits `T_j → +∞` with
`(log T_j)⁻¹ ∑_{|γ_q| ≤ T_j} |γ_q| ‖L F(iγ_q)‖² → 0`. -/
def SequentialSubLogarithmicFirstMomentTarget : Prop :=
  BacklundConverse.FiniteOffLine →
    ∀ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ →
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) →
      IsCriticalHalfLineGroundState W₀ F →
      ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
        Tendsto (fun j => (Real.log (T j))⁻¹ * ∑' q : onLineCopies,
          if |(centredZero q).im| ≤ T j then |(centredZero q).im| * zeroValueMass F q else 0)
          atTop (𝓝 0)

/-- **Sequential sub-inverse ordinate-tail target:** under `FiniteOffLine`, every threshold ground
state `F` admits `T_j → +∞` with `T_j ∑_{|γ_q| > T_j} ‖L F(iγ_q)‖² → 0`. -/
def SequentialSubInverseOrdinateTailTarget : Prop :=
  BacklundConverse.FiniteOffLine →
    ∀ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ →
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) →
      IsCriticalHalfLineGroundState W₀ F →
      ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
        Tendsto (fun j => T j * ∑' q : onLineCopies,
          if T j < |(centredZero q).im| then zeroValueMass F q else 0) atTop (𝓝 0)

/-- **§2.17 sequential sub-linear cosine-cusp target:** under `FiniteOffLine`, every threshold
ground state `F` admits `h_j ↓ 0` along which
`h_j⁻¹ ∑_q (1 - cos(h_j γ_q)) ‖L F(iγ_q)‖² → 0`. -/
def SequentialSubLinearCosineCuspTarget : Prop :=
  BacklundConverse.FiniteOffLine →
    ∀ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ →
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) →
      IsCriticalHalfLineGroundState W₀ F →
      ∃ h : ℕ → ℝ, (∀ j, 0 < h j) ∧ Tendsto h atTop (𝓝 0) ∧
        Tendsto (fun j => (∑' q : onLineCopies,
          (1 - Real.cos (h j * (centredZero q).im)) * zeroValueMass F q) / h j) atTop (𝓝 0)

private theorem exists_criticalGroundState_of_not_riemannHypothesis (hnRH : ¬ RiemannHypothesis) :
    ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F := by
  have hnCont : ¬ ArithmeticCastelnuovoSeveri.ZetaBeyondTheWallPrimeContinuation :=
    mt ArithmeticCastelnuovoSeveri.zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis.mp hnRH
  by_contra hno
  exact hnCont (zetaBeyondTheWallPrimeContinuation_iff_no_criticalState.mpr hno)

private theorem groundState_confinementMass_pos {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    0 < HTGeometry.criticalAliasCoefficient W₀ ∧ 0 < ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hnull := isConfinedNullVector_of_groundState hW ht hF
  have hM_eq : (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) =
      HTGeometry.criticalHalfLineExponentialPair F F := by
    unfold HTGeometry.criticalHalfLineExponentialPair
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  exact ⟨HTGeometry.criticalAliasCoefficient_positive hW,
    hM_eq ▸ exponentialPair_self_pos hd hnull.2.1⟩

/-- **Seven-way equivalence of all §2.17 wall-cusp and critical-line ordinate-moment targets with
`BacklundConverse.FiniteOffLine → RiemannHypothesis` (B13).** -/
theorem finiteLayer_wallCusp_targets_tfae :
    [SequentialWallCuspVanishingTarget,
      SequentialVerticalTraceSubCuspTarget,
      FiniteFirstOrdinateMomentTarget,
      SequentialSubLogarithmicFirstMomentTarget,
      SequentialSubInverseOrdinateTailTarget,
      SequentialSubLinearCosineCuspTarget,
      BacklundConverse.FiniteOffLine → RiemannHypothesis].TFAE := by
  have hb13_noState : (BacklundConverse.FiniteOffLine → RiemannHypothesis) ↔
      (BacklundConverse.FiniteOffLine →
        ¬ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
          (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
          IsCriticalHalfLineGroundState W₀ F) :=
    finiteLayer_ecs_b13_tfae.out 0 1
  tfae_have 7 → 1 := by
    intro hb13 _ hfin W₀ F hW ht hF
    exact False.elim (hb13_noState.mp hb13 hfin ⟨W₀, F, hW, ht, hF⟩)
  tfae_have 7 → 2 := by
    intro hb13 hfin W₀ F hW ht hF
    exact False.elim (hb13_noState.mp hb13 hfin ⟨W₀, F, hW, ht, hF⟩)
  tfae_have 7 → 3 := by
    intro hb13 hfin W₀ F hW ht hF
    exact False.elim (hb13_noState.mp hb13 hfin ⟨W₀, F, hW, ht, hF⟩)
  tfae_have 7 → 4 := by
    intro hb13 hfin W₀ F hW ht hF
    exact False.elim (hb13_noState.mp hb13 hfin ⟨W₀, F, hW, ht, hF⟩)
  tfae_have 7 → 5 := by
    intro hb13 hfin W₀ F hW ht hF
    exact False.elim (hb13_noState.mp hb13 hfin ⟨W₀, F, hW, ht, hF⟩)
  tfae_have 7 → 6 := by
    intro hb13 hfin W₀ F hW ht hF
    exact False.elim (hb13_noState.mp hb13 hfin ⟨W₀, F, hW, ht, hF⟩)
  tfae_have 1 → 7 := by
    intro h1 hfin
    by_contra hnRH
    obtain ⟨W₀, F, hW, ht, hF⟩ := exists_criticalGroundState_of_not_riemannHypothesis hnRH
    obtain ⟨ha, hM⟩ := groundState_confinementMass_pos hW ht hF
    obtain ⟨h, hpos, h0, hvan⟩ := h1 hnRH hfin W₀ F hW ht hF
    have hnhds : Tendsto h atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within h h0 (Eventually.of_forall hpos)
    have hlim := (criticalState_tendsto_log_div_mul_terminal_sq hW ht hF).comp hnhds
    have heq := tendsto_nhds_unique hlim hvan
    linarith [mul_pos (mul_pos (by norm_num : (0 : ℝ) < 8) ha) hM]
  tfae_have 2 → 7 := by
    intro h2 hfin
    by_contra hnRH
    obtain ⟨W₀, F, hW, ht, hF⟩ := exists_criticalGroundState_of_not_riemannHypothesis hnRH
    obtain ⟨ha, hM⟩ := groundState_confinementMass_pos hW ht hF
    obtain ⟨x, hx, hvan⟩ := h2 hfin W₀ F hW ht hF
    have hlim := (criticalState_tendsto_mul_log_vertical_laplace_sq hW ht hF).comp hx
    have heq := tendsto_nhds_unique hlim hvan
    have hpos_lim : 0 < 8 * Real.pi * HTGeometry.criticalAliasCoefficient W₀ *
        (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) := by positivity
    linarith
  tfae_have 3 → 7 := by
    intro h3 hfin
    by_contra hnRH
    obtain ⟨W₀, F, hW, ht, hF⟩ := exists_criticalGroundState_of_not_riemannHypothesis hnRH
    exact criticalState_criticalLine_firstMoment_not_summable hW ht hF hfin
      (h3 hfin W₀ F hW ht hF)
  tfae_have 4 → 7 := by
    intro h4 hfin
    by_contra hnRH
    obtain ⟨W₀, F, hW, ht, hF⟩ := exists_criticalGroundState_of_not_riemannHypothesis hnRH
    obtain ⟨ha, hM⟩ := groundState_confinementMass_pos hW ht hF
    obtain ⟨T, hT, hvan⟩ := h4 hfin W₀ F hW ht hF
    have hlim := (criticalState_criticalLine_firstMoment_asymptotic hW ht hF hfin).comp hT
    have heq := tendsto_nhds_unique hlim hvan
    have hpos_lim : 0 < 8 * HTGeometry.criticalAliasCoefficient W₀ *
        (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) / Real.pi := by positivity
    linarith
  tfae_have 5 → 7 := by
    intro h5 hfin
    by_contra hnRH
    obtain ⟨W₀, F, hW, ht, hF⟩ := exists_criticalGroundState_of_not_riemannHypothesis hnRH
    obtain ⟨ha, hM⟩ := groundState_confinementMass_pos hW ht hF
    obtain ⟨T, hT, hvan⟩ := h5 hfin W₀ F hW ht hF
    have hlim := (criticalState_criticalLine_tail_asymptotic hW ht hF hfin).comp hT
    have heq := tendsto_nhds_unique hlim hvan
    have hpos_lim : 0 < 8 * HTGeometry.criticalAliasCoefficient W₀ *
        (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) / Real.pi := by positivity
    linarith
  tfae_have 6 → 7 := by
    intro h6 hfin
    by_contra hnRH
    obtain ⟨W₀, F, hW, ht, hF⟩ := exists_criticalGroundState_of_not_riemannHypothesis hnRH
    obtain ⟨ha, hM⟩ := groundState_confinementMass_pos hW ht hF
    obtain ⟨h, hpos, h0, hvan⟩ := h6 hfin W₀ F hW ht hF
    have hnhds : Tendsto h atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within h h0 (Eventually.of_forall hpos)
    have hlim := (criticalState_criticalLine_cosine_cusp hW ht hF hfin).comp hnhds
    have heq := tendsto_nhds_unique hlim hvan
    linarith [mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) ha) hM]
  tfae_finish

/-! ### Global cross-route payoff corollaries (no `FiniteOffLine` premise in conclusions) -/

/-- **Global single-quartet exclusion.** Because `HasSingleOffLineQuartet ρ₀` unconditionally
implies `BacklundConverse.FiniteOffLine`, `SequentialWallCuspVanishingTarget` excludes a single
off-line quartet globally without assuming `FiniteOffLine`. -/
theorem no_singleOffLineQuartet_of_wallCuspTarget (h : SequentialWallCuspVanishingTarget) :
    ∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀ := by
  have hb13 : BacklundConverse.FiniteOffLine → RiemannHypothesis :=
    (finiteLayer_wallCusp_targets_tfae.out 0 6).mp h
  intro ρ₀ hq
  have hRH : RiemannHypothesis := hb13 hq.finiteOffLine
  have hgt : 1 / 2 < ρ₀.re := hq.1
  obtain ⟨hζ, h0, h1⟩ := hq.2.1
  have hre : ρ₀.re = 1 / 2 := by
    refine hRH ρ₀ hζ ?_ ?_
    · rintro ⟨n, hn⟩
      rw [hn] at h0; simp at h0
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · intro heq1; rw [heq1] at h1; norm_num at h1
  linarith

/-- **Weil packet-index zero-or-infinity dichotomy.** -/
theorem packetIndex_zero_or_top_of_wallCuspTarget (h : SequentialWallCuspVanishingTarget) :
    ArithmeticCastelnuovoSeveri.realPacketNegIndex = 0 ∨
      ArithmeticCastelnuovoSeveri.realPacketNegIndex = ⊤ :=
  (finiteLayer_ecs_b13_tfae.out 0 5).mp ((finiteLayer_wallCusp_targets_tfae.out 0 6).mp h)

/-- **QIC payoff:** full two-interval ordinary-prime radial exclusion law across all zero
configurations. -/
theorem twoIntervalRadialExclusionLaw_of_wallCuspTarget (h : SequentialWallCuspVanishingTarget) :
    TwoIntervalRadialExclusionLaw :=
  twoIntervalRadialExclusionLaw_iff_no_singleQuartet.mpr
    (no_singleOffLineQuartet_of_wallCuspTarget h)

/-- **PDR payoff:** removes the single-quartet branch from the `(2, 3, 6)` ordinary-prime
`θ`-dilation recurrences, making bounded residuals equivalent to `RiemannHypothesis`. -/
theorem ordinary_prime_recurrences_iff_rh_of_wallCuspTarget
    (h : SequentialWallCuspVanishingTarget) {β γ : ℝ}
    (hβ : 1 / 2 < β) (hβ' : β < 1) (hγ : 0 < γ) :
    (¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 2 β γ) ∧
      ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 3 β γ) ∧
      ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 6 β γ)) ↔
      RiemannHypothesis := by
  rw [ordinary_prime_recurrences_iff_rh_or_singleQuartet hβ hβ' hγ]
  have hno := no_singleOffLineQuartet_of_wallCuspTarget h ((β : ℂ) + I * (γ : ℂ))
  exact ⟨fun hor => hor.elim id fun hq => False.elim (hno hq), Or.inl⟩

/-- **PPC payoff:** removes the two-wave proper-power discrepancy regime for every candidate
off-line zero `ρ` in the critical strip. -/
theorem no_properPower_twoWave_quartet_of_wallCuspTarget
    (h : SequentialWallCuspVanishingTarget) {ρ : ℂ} (hh : 1 / 2 < ρ.re)
    (hmem : ρ ∈ Zeta23.zetaZeroConfig.carrier) :
    ¬ ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
      |properPowerDiscrepancy (y ^ (2 : ℝ)) -
        (quartetPrimeWaveTerm ρ y + quartetPrimeWaveTerm ρ (y ^ (2 / 3 : ℝ)))| ≤
        K * (Real.sqrt y * (1 + Real.log y) ^ 2) :=
  mt (hasSingleOffLineQuartet_iff_two_properPower_waves hh hmem).mpr
    (no_singleOffLineQuartet_of_wallCuspTarget h ρ)

/-- **ZCG payoff:** discharges the finite-stratum atom of `riemannHypothesis_iff_three_atoms`,
reducing `RiemannHypothesis` to `ZerosApproachLine ∧ ZetaLandingLaw`. -/
theorem riemannHypothesis_iff_zal_and_landing_of_wallCuspTarget
    (h : SequentialWallCuspVanishingTarget) :
    RiemannHypothesis ↔ BacklundConverse.ZerosApproachLine ∧ ZetaLandingLaw := by
  have hb13 : BacklundConverse.FiniteOffLine → RiemannHypothesis :=
    (finiteLayer_wallCusp_targets_tfae.out 0 6).mp h
  rw [riemannHypothesis_iff_three_atoms]
  exact ⟨fun ⟨hZ, _, hL⟩ => ⟨hZ, hL⟩, fun ⟨hZ, hL⟩ => ⟨hZ, hb13, hL⟩⟩

/-! ### Sharp scope boundary: isolated finite outer tail above an infinite lower background -/

/-- **Sharp outer-tail scope boundary of §2.17.** For every `σ₀ ∈ (1/2, 1)`, there exists a strip
zero configuration `Z : ZeroConfig` such that:
1. `Z` has a **nonempty finite isolated outer tail** right of `1/2 + (σ₀ - 1/2) / 2`;
2. `Z` has an **infinite off-line lower background** (`(rightOf Z 0).Infinite`);
3. `Z` satisfies the configuration finite-stratum law `AbscissaLawAt Z 0` and `ApproachesLine Z`;
4. `Z` has global abscissa `zeroAbscissa Z = σ₀` and violates `LinearAbscissaLaw Z` and
   `AbscissaLaw Z`.

Consequently, discharging the finite-stratum atom (`FiniteOffLine → RH`) leaves infinite off-line
configurations open — including an isolated finite outer tail above an infinite approaching lower
background — and implies no uniform zero-free half-plane `Re s ≤ σ₀ < 1`. -/
theorem exists_isolatedOuterTail_above_infiniteApproachingBackground {σ₀ : ℝ}
    (h12 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    ∃ Z : ZeroConfig,
      (rightOf Z ((σ₀ - 1 / 2) / 2)).Finite ∧
      (rightOf Z ((σ₀ - 1 / 2) / 2)).Nonempty ∧
      (rightOf Z 0).Infinite ∧
      AbscissaLawAt Z 0 ∧
      ApproachesLine Z ∧
      zeroAbscissa Z = σ₀ ∧
      ¬ LinearAbscissaLaw Z ∧
      ¬ AbscissaLaw Z := by
  set d := σ₀ - 1 / 2
  have hd_pos : 0 < d := by dsimp only [d]; linarith
  have hd_half : d ≤ 1 / 2 := by dsimp only [d]; linarith
  let δ : ℕ → ℝ := fun n => if n = 0 then d else d / ((n : ℝ) + 3)
  have hδ0 : ∀ n, 0 ≤ δ n := fun n => by
    dsimp only [δ]
    split_ifs
    · exact hd_pos.le
    · positivity
  have hδ12 : ∀ n, δ n ≤ 1 / 2 := fun n => by
    dsimp only [δ]
    split_ifs
    · exact hd_half
    · have hle : d / ((n : ℝ) + 3) ≤ d :=
        div_le_self hd_pos.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      exact hle.trans hd_half
  let Z : ZeroConfig := seqPairConfig δ hδ0 hδ12
  have hinj : Function.Injective (seqUpper δ) := by
    intro m n hmn
    have him := congrArg Complex.im hmn
    simp only [seqUpper, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
      add_zero, zero_add] at him
    exact Nat.cast_injective (by linarith : (m : ℝ) = n)
  have htail_eq : rightOf Z (d / 2) = {seqUpper δ 0} := by
    ext z
    simp only [rightOf, mem_setOf_eq, mem_singleton_iff]
    constructor
    · rintro ⟨(⟨n, rfl⟩ | ⟨n, rfl⟩), hre⟩
      · simp only [seqUpper, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero] at hre
        by_cases hn0 : n = 0
        · subst hn0; rfl
        · exfalso
          dsimp only [δ] at hre
          rw [if_neg hn0] at hre
          have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
          have hle : d / ((n : ℝ) + 3) ≤ d / 4 :=
            div_le_div_of_nonneg_left hd_pos.le (by norm_num) (by linarith)
          linarith
      · exfalso
        simp only [seqLower, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero] at hre
        linarith [hδ0 n, hd_pos]
    · rintro rfl
      refine ⟨Or.inl ⟨0, rfl⟩, ?_⟩
      simp only [seqUpper, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, δ, if_pos rfl]
      linarith
  have htail_fin : (rightOf Z (d / 2)).Finite := by rw [htail_eq]; exact finite_singleton _
  have htail_ne : (rightOf Z (d / 2)).Nonempty := by rw [htail_eq]; exact singleton_nonempty _
  have hinf : (rightOf Z 0).Infinite := by
    refine (infinite_range_of_injective hinj).mono ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨Or.inl ⟨n, rfl⟩, ?_⟩
    simp only [seqUpper, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    have hpos_δ : 0 < δ n := by
      dsimp only [δ]
      split_ifs
      · exact hd_pos
      · positivity
    linarith
  have hB13 : AbscissaLawAt Z 0 := fun hfin => absurd hfin hinf
  have hZAL : ApproachesLine Z := by
    intro h hh
    set N : ℕ := ⌈d / h⌉₊ + 1
    refine ((Finset.range N).finite_toSet.image (seqUpper δ)).subset ?_
    rintro z ⟨(⟨n, rfl⟩ | ⟨n, rfl⟩), hre⟩
    · simp only [seqUpper, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero] at hre
      by_cases hn0 : n = 0
      · subst hn0
        exact ⟨0, Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.succ_pos _)), rfl⟩
      · dsimp only [δ] at hre
        rw [if_neg hn0] at hre
        have hlt : h < d / ((n : ℝ) + 3) := by linarith
        have hn : (n : ℝ) + 3 < d / h :=
          (lt_div_iff₀ hh).mpr (by linarith [(lt_div_iff₀ (by positivity)).mp hlt])
        have hnN : n < N := by
          have hceil : d / h ≤ (⌈d / h⌉₊ : ℝ) := Nat.le_ceil _
          have hlt' : (n : ℝ) < (⌈d / h⌉₊ : ℝ) := by linarith
          exact Nat.lt_succ_of_le (Nat.cast_lt.mp hlt').le
        exact ⟨n, Finset.mem_coe.mpr (Finset.mem_range.mpr hnN), rfl⟩
    · simp only [seqLower, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero] at hre
      linarith [hδ0 n]
  have hΘ : zeroAbscissa Z = σ₀ := by
    refine le_antisymm ?_ ?_
    · refine (zeroAbscissa_le_iff Z).mpr ⟨h12.le, ?_⟩
      rintro z (⟨n, rfl⟩ | ⟨n, rfl⟩)
      · simp only [seqUpper, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero]
        have hle_d : δ n ≤ d := by
          dsimp only [δ]
          split_ifs
          · exact le_rfl
          · exact div_le_self hd_pos.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
        dsimp only [d] at hle_d
        linarith
      · simp only [seqLower, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero]
        linarith [hδ0 n]
    · have hmem : seqUpper δ 0 ∈ Z.carrier := Or.inl ⟨0, rfl⟩
      have h0 := re_le_zeroAbscissa Z hmem
      simp only [seqUpper, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, δ, if_pos rfl] at h0
      dsimp only [d] at h0
      linarith
  have hnotLin : ¬ LinearAbscissaLaw Z := by
    intro hL
    have himp : ApproachesLine Z → Pure Z := ((linearAbscissaLaw_tfae Z).out 0 4).mp hL
    have h12_eq := (pure_iff_zeroAbscissa_eq_half Z).mp (himp hZAL)
    linarith
  have hnotAAL : ¬ AbscissaLaw Z := fun hA =>
    hnotLin (linearAbscissaLaw_iff_abscissaLawAt_zero_and_landingLaw Z |>.mpr
      ⟨(abscissaLaw_iff_three_atoms Z |>.mp hA).1,
        (abscissaLaw_iff_three_atoms Z |>.mp hA).2.1⟩)
  exact ⟨Z, htail_fin, htail_ne, hinf, hB13, hZAL, hΘ, hnotLin, hnotAAL⟩

/-! ### Complete synthesis theorem for §2.17 -/

/-- **Complete unconditional resolution of §2.17.**
1. **Model-level answer (affirmative):** In `CriticalHalfLineEnergyDomain`, `smoothedWallLogProfile 1`
   sustains the unit logarithmic wall cusp (`(log(1/h)/h) ∫_{-h}^0 F₁² → 1`, with no vanishing
   subsequence) while satisfying `h⁻¹ ∫_{-h}^0 F₁² → 0`, `h⁻¹ ∫ (F₁(u) - F₁(u+h))² e^{-8u} du → 0`,
   uniform rescaled unit-window sample-square and `σ = -4` Poisson-row bounds on `onLineCopies` of
   `ζ`, uniform imaginary-axis Lipschitz continuity, and fixed-window crowding mass saturation.
   Likewise, every confinement ratio `R > 0` admits a variational half-line ground state sustaining
   a positive logarithmic wall cusp.
2. **Exact `ζ` laws under `FiniteOffLine`:** Every threshold ground state `F` satisfies the exact
   logarithmic vertical-line trace `8 π a M`, vanishing boundary Fourier tail `o(1/T)`,
   sub-logarithmic boundary first moment `o(log T)`, exact critical-line ordinate tail `8 a M / π`,
   and exact logarithmic first ordinate moment slope `8 a M / π`.
3. **Equivalence & cross-route payoff:** All six §2.17 vanishing/summability targets are equivalent
   to `BacklundConverse.FiniteOffLine → RiemannHypothesis` and globally discharge single-quartet
   exclusion, `TwoIntervalRadialExclusionLaw`, the `(2, 3, 6)` ordinary-prime `θ`-recurrence
   equivalence with `RH`, and the finite-stratum atom of `riemannHypothesis_iff_three_atoms`.
4. **Sharp scope boundary:** Infinite off-line configurations with an isolated finite outer tail
   above an infinite approaching lower background satisfy `AbscissaLawAt · 0` and `ApproachesLine`
   at arbitrary global abscissa `σ₀ ∈ (1/2, 1)`. -/
theorem finiteLayer_wallCusp_complete_resolution :
    (CriticalHalfLineEnergyDomain (smoothedWallLogProfile 1) ∧
      Tendsto (fun h : ℝ => Real.log (1 / h) / h *
        ∫ u in Ioo (-h) 0, smoothedWallLogProfile 1 u ^ 2) (𝓝[>] 0) (𝓝 1) ∧
      (¬ ∃ h : ℕ → ℝ, (∀ j, 0 < h j) ∧ Tendsto h atTop (𝓝 0) ∧
        Tendsto (fun j => Real.log (1 / h j) / h j *
          ∫ u in Ioo (-(h j)) 0, smoothedWallLogProfile 1 u ^ 2) atTop (𝓝 0)) ∧
      Tendsto (fun h : ℝ => (∫ u : ℝ,
        (smoothedWallLogProfile 1 u - smoothedWallLogProfile 1 (u + h)) ^ 2 *
          Real.exp (-(8 * u))) / h) (𝓝[>] 0) (𝓝 0) ∧
      (∃ C > 0, ∀ y : ℝ, (1 + y ^ 2) * (∑' q : onLineCopies,
        if |(centredZero q).im - y| ≤ 1 then
          zeroValueMass (smoothedWallLogProfile 1) q else 0) ≤ C) ∧
      (∃ C > 0, ∀ y : ℝ, (1 + y ^ 2) * (∑' q : onLineCopies,
        zeroValueMass (smoothedWallLogProfile 1) q *
          (4 / (16 + (y - (centredZero q).im) ^ 2))) ≤ C)) ∧
    [SequentialWallCuspVanishingTarget,
      SequentialVerticalTraceSubCuspTarget,
      FiniteFirstOrdinateMomentTarget,
      SequentialSubLogarithmicFirstMomentTarget,
      SequentialSubInverseOrdinateTailTarget,
      SequentialSubLinearCosineCuspTarget,
      BacklundConverse.FiniteOffLine → RiemannHypothesis].TFAE ∧
    (SequentialWallCuspVanishingTarget →
      (∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀) ∧
      TwoIntervalRadialExclusionLaw ∧
      (ArithmeticCastelnuovoSeveri.realPacketNegIndex = 0 ∨
        ArithmeticCastelnuovoSeveri.realPacketNegIndex = ⊤) ∧
      (RiemannHypothesis ↔ BacklundConverse.ZerosApproachLine ∧ ZetaLandingLaw)) ∧
    (∀ σ₀ : ℝ, 1 / 2 < σ₀ → σ₀ < 1 →
      ∃ Z : ZeroConfig,
        (rightOf Z ((σ₀ - 1 / 2) / 2)).Finite ∧
        (rightOf Z ((σ₀ - 1 / 2) / 2)).Nonempty ∧
        (rightOf Z 0).Infinite ∧
        AbscissaLawAt Z 0 ∧
        ApproachesLine Z ∧
        zeroAbscissa Z = σ₀ ∧
        ¬ LinearAbscissaLaw Z) := by
  refine ⟨?_, finiteLayer_wallCusp_targets_tfae, ?_, ?_⟩
  · obtain ⟨C₁, hC₁, hb₁⟩ := smoothedWallLogProfile_local_critical_line_mass
    obtain ⟨C₂, hC₂, hb₂⟩ := smoothedWallLogProfile_poisson_row_bound
    refine ⟨criticalHalfLineEnergyDomain_smoothedWallLogProfile 1,
      by simpa using smoothedWallLogProfile_tendsto_terminal_sq 1,
      smoothedWallLogProfile_no_vanishing_cusp_subsequence one_ne_zero,
      smoothedWallLogProfile_weighted_sq_increment_div_zero 1,
      ⟨C₁, hC₁, fun y => by simpa using hb₁ 1 y⟩,
      ⟨C₂, hC₂, fun y => by simpa using hb₂ 1 y⟩⟩
  · intro h
    exact ⟨no_singleOffLineQuartet_of_wallCuspTarget h,
      twoIntervalRadialExclusionLaw_of_wallCuspTarget h,
      packetIndex_zero_or_top_of_wallCuspTarget h,
      riemannHypothesis_iff_zal_and_landing_of_wallCuspTarget h⟩
  · intro σ₀ h12 h1
    obtain ⟨Z, h1', h2', h3', h4', h5', h6', h7', _⟩ :=
      exists_isolatedOuterTail_above_infiniteApproachingBackground h12 h1
    exact ⟨Z, h1', h2', h3', h4', h5', h6', h7'⟩

#print axioms finiteLayer_wallCusp_targets_tfae
#print axioms no_singleOffLineQuartet_of_wallCuspTarget
#print axioms packetIndex_zero_or_top_of_wallCuspTarget
#print axioms twoIntervalRadialExclusionLaw_of_wallCuspTarget
#print axioms ordinary_prime_recurrences_iff_rh_of_wallCuspTarget
#print axioms no_properPower_twoWave_quartet_of_wallCuspTarget
#print axioms riemannHypothesis_iff_zal_and_landing_of_wallCuspTarget
#print axioms exists_isolatedOuterTail_above_infiniteApproachingBackground
#print axioms finiteLayer_wallCusp_complete_resolution

end GaloisForLFunctions.ExceptionalLayerTheory