import GaloisForLFunctions.CountingHolography.Sections.PrimeDisplacementGramAndModeQuotients
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheIndexExit
import GaloisForLFunctions.ExceptionalLayerTheory.TheFiniteLayerWallCuspPayoff
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.StageTwoHasPrimeSideRows
import GaloisForLFunctions.InfiniteRankWeilTheory.TheFiniteStratumIsAMetricZeroOneLaw

/-!
# Prime-displacement index amplification, rank thresholds, and cross-route payoffs

This module establishes the rank-threshold equivalences and cross-route consequences of amplifying
a single negative prime-displacement witness into multi-probe negative-definite Gram matrices:

1. **Three-probe threshold (`ThreeProbeAmplificationLaw`) and single-quartet exclusion:**
   Amplifying a single signed prime-supported negative witness into `m = 3` pairwise-disjoint
   signed prime-supported probes with negative-definite Gram matrix (`hermNegIndex = 3`) is
   unconditionally equivalent to global exclusion of a single off-line quartet
   (`∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀`), upgrades automatically to `m = 4` probes with
   normalized off-diagonal row sums `< ε` by conjugate-pair parity, and already discharges:
   - `TwoIntervalRadialExclusionLaw` across all zero configurations;
   - Exact equivalence between bounded `(2, 3, 6)` ordinary-prime `θ`-dilation residuals and
     `RiemannHypothesis`;
   - Exclusion of the two-wave proper-power discrepancy regime for every candidate off-line zero.

2. **Ten-way equivalence for all-`m` amplification (`primeDisplacement_amplification_tfae`):**
   Unbounded prime-submatrix negative index from one negative witness, all-`m` negative-definite
   disjoint prime-probe construction, all-`m` Gershgorin row-sum `< ε` prime-probe construction,
   two-prime-difference witness amplification, `BacklundConverse.FiniteOffLine → RiemannHypothesis`,
   the packet-index zero-or-infinity dichotomy, sequential sub-inverse critical-line ordinate tail
   vanishing, empty-wave reduction of finite-wave `ψ` laws, positive measure of
   `subexponentialLagBases` on the finite stratum, and finite-mode near-annihilator persistence
   are all unconditionally equivalent.

3. **Global ZCG reduction, unconditional calibration, and infinite-background scope boundary
   (`primeDisplacement_complete_resolution`):**
   Combines the unconditional `m = 2` Gershgorin solution on `ζ`, universal cross-scale
   off-diagonal blowup under asymptotic shell separation, the `m = 3` single-quartet threshold,
   the 10-way all-`m` equivalence, reduction of `RiemannHypothesis` to
   `ZerosApproachLine ∧ ZetaLandingLaw`, and the existence of infinite off-line configurations with
   isolated finite outer tails at arbitrary abscissa `σ₀ ∈ (1/2, 1)`.
-/

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section
open MeasureTheory Set Filter Complex Topology Finset Matrix Zeta23
open scoped ComplexConjugate Real
open GaloisForLFunctions
open GaloisForLFunctions.CountingHolography.Sections
open GaloisForLFunctions.ArithmeticScatteringHolography
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticOrientationGeometry
open GaloisForLFunctions.ExclusionOfTheCriticalState
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
open _root_.RHTower

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-! ### 1. Exact amplification laws at rank `m = 3` and across all ranks `m` -/

/-- **Unbounded prime-submatrix index from one negative prime-displacement witness:**
every signed prime-supported probe with `integerProbe N₀ a₀ < 0` forces prime-supported submatrices
of `atomGram` above every cutoff `P₀` to have infinite supremal negative index. -/
def NegativePrimeWitnessForcesUnboundedIndex : Prop :=
  ∀ (N₀ : ℕ) (a₀ : Fin N₀ → ℤ),
    isSignedPrimeSupported a₀ → integerProbe N₀ a₀ < 0 →
    ∀ P₀ : ℕ,
      (⨆ (M : ℕ) (N : ℕ) (ι : PrimeConductorEmbedding M N P₀),
        (hermNegIndex ((atomGram N).submatrix ι.val ι.val) : ℕ∞)) = ⊤

/-- **All-`m` negative-definite prime-probe amplification:**
given one signed prime-supported negative witness, for every `m` and every cutoff `P₀` there exist
`m` pairwise-disjoint signed prime-supported probes above `P₀` whose `m × m` Gram matrix is
negative definite (`hermNegIndex = m`). -/
def NegativePrimeWitnessForcesMProbes : Prop :=
  ∀ (N₀ : ℕ) (a₀ : Fin N₀ → ℤ),
    isSignedPrimeSupported a₀ → integerProbe N₀ a₀ < 0 →
    ∀ (m P₀ : ℕ),
      ∃ (N : ℕ) (a : Fin m → (Fin N → ℤ)),
        P₀ < N ∧
        (∀ r : Fin m, isSignedPrimeSupported (a r)) ∧
        (∀ (r : Fin m) (ℓ : Fin N), a r ℓ ≠ 0 → P₀ < ℓ.val + 1) ∧
        (∀ r s : Fin m, r ≠ s → Disjoint (activeConductors (a r)) (activeConductors (a s))) ∧
        hermNegIndex (probeGramMatrix N a) = m

/-- **All-`m` Gershgorin row-sum `< ε` prime-probe amplification:**
given one signed prime-supported negative witness, for every `m`, cutoff `P₀`, and `ε ∈ (0, 1]`,
there exist `m` pairwise-disjoint signed prime-supported probes above `P₀` with `G_{rr} < 0` and
normalized off-diagonal row sums `< ε`. -/
def NegativePrimeWitnessForcesGershgorinProbes : Prop :=
  ∀ (N₀ : ℕ) (a₀ : Fin N₀ → ℤ),
    isSignedPrimeSupported a₀ → integerProbe N₀ a₀ < 0 →
    ∀ (m P₀ : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∃ (N : ℕ) (a : Fin m → (Fin N → ℤ)),
        P₀ < N ∧
        (∀ r : Fin m, isSignedPrimeSupported (a r)) ∧
        (∀ (r : Fin m) (ℓ : Fin N), a r ℓ ≠ 0 → P₀ < ℓ.val + 1) ∧
        (∀ r s : Fin m, r ≠ s → Disjoint (activeConductors (a r)) (activeConductors (a s))) ∧
        (∀ r : Fin m, probePairing N (a r) (a r) < 0) ∧
        (∀ r : Fin m,
          ∑ s ∈ Finset.univ.erase r,
            |probePairing N (a r) (a s)| /
              Real.sqrt (probePairing N (a r) (a r) * probePairing N (a s) (a s)) < ε)

/-- **Two-prime-difference witness amplification:**
even restricting the initial negative witness to a two-prime difference (`|activeConductors a₀| = 2`),
every `m` and cutoff `P₀` admit `m` pairwise-disjoint signed prime-supported negative-definite probes. -/
def TwoPrimeDiffWitnessForcesUnboundedProbes : Prop :=
  ∀ (N₀ : ℕ) (a₀ : Fin N₀ → ℤ),
    isSignedPrimeSupported a₀ → (activeConductors a₀).card = 2 →
    integerProbe N₀ a₀ < 0 →
    ∀ (m P₀ : ℕ),
      ∃ (N : ℕ) (a : Fin m → (Fin N → ℤ)),
        P₀ < N ∧
        (∀ r : Fin m, isSignedPrimeSupported (a r)) ∧
        (∀ (r : Fin m) (ℓ : Fin N), a r ℓ ≠ 0 → P₀ < ℓ.val + 1) ∧
        (∀ r s : Fin m, r ≠ s → Disjoint (activeConductors (a r)) (activeConductors (a s))) ∧
        hermNegIndex (probeGramMatrix N a) = m

/-- **Three-probe amplification law (`m = 3` threshold):**
given one signed prime-supported negative witness, above every cutoff `P₀` there exist three
pairwise-disjoint signed prime-supported probes whose `3 × 3` Gram matrix is negative definite. -/
def ThreeProbeAmplificationLaw : Prop :=
  ∀ (N₀ : ℕ) (a₀ : Fin N₀ → ℤ),
    isSignedPrimeSupported a₀ → integerProbe N₀ a₀ < 0 →
    ∀ P₀ : ℕ,
      ∃ (N : ℕ) (a : Fin 3 → (Fin N → ℤ)),
        P₀ < N ∧
        (∀ r : Fin 3, isSignedPrimeSupported (a r)) ∧
        (∀ (r : Fin 3) (ℓ : Fin N), a r ℓ ≠ 0 → P₀ < ℓ.val + 1) ∧
        (∀ r s : Fin 3, r ≠ s → Disjoint (activeConductors (a r)) (activeConductors (a s))) ∧
        hermNegIndex (probeGramMatrix N a) = 3

/-- **Finite-mode quotient persistence law:**
given one signed prime-supported negative witness, for every conjugation-closed finite set
`S₀ ⊆ {s : 1/2 < Re s}`, cutoff `P₀`, and `δ > 0`, there exists a signed prime-supported negative
probe above `P₀` whose normalized mode pair products across `S₀` are all `< δ`. -/
def ModeQuotientPersistenceLaw : Prop :=
  ∀ (N₀ : ℕ) (a₀ : Fin N₀ → ℤ),
    isSignedPrimeSupported a₀ → integerProbe N₀ a₀ < 0 →
    ∀ (S₀ : Finset ℂ),
      (∀ ρ ∈ S₀, 1 / 2 < ρ.re) →
      (∀ ρ ∈ S₀, conj ρ ∈ S₀) →
      ∀ (P₀ : ℕ) (δ : ℝ), 0 < δ →
        ∃ (N : ℕ) (a : Fin N → ℤ),
          P₀ < N ∧ isSignedPrimeSupported a ∧
          (∀ ℓ : Fin N, a ℓ ≠ 0 → P₀ < ℓ.val + 1) ∧
          integerProbe N a < 0 ∧
          ∀ ρ ∈ S₀, modePairProduct ρ N (fun i => (a i : ℂ)) < δ * (-integerProbe N a)

/-! ### 2. The `m = 3` amplification threshold and its immediate cross-route payoffs -/

/-- **Exact characterization of `ThreeProbeAmplificationLaw` (`m = 3`).**
Building three negative-definite disjoint high-prime probes from one negative witness is
unconditionally equivalent to global exclusion of a single off-line quartet (`∀ ρ₀, ¬ HasSingleOffLineQuartet ρ₀`). -/
theorem threeProbeAmplificationLaw_iff_no_singleQuartet :
    ThreeProbeAmplificationLaw ↔ ∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀ := by
  rw [no_singleOffLineQuartet_iff_rh_or_four_le_rightZeros]
  constructor
  · intro h3
    by_cases hRH : RiemannHypothesis
    · exact Or.inl hRH
    · right
      obtain ⟨N₀, a₀, _, _, hsig₀, _, _, _, _, _, _, _, hneg₀⟩ :=
        exists_twoPrime_diff_neg_integerProbe_of_not_rh hRH 0
      obtain ⟨N₁, a₁, _, _, _, _, hidx3⟩ := h3 N₀ a₀ hsig₀ hneg₀ 0
      obtain ⟨N₂, a₂, hN₂, hsig₂, hgt₂, hdisj₂, _, _, hidx4⟩ :=
        odd_probe_rank_forces_even_succ (k := 1) a₁ hidx3 0 one_pos le_rfl
      exact (disjoint_signedPrimeProbes_gershgorin_iff_rightZeros_ge 4 0 one_pos le_rfl).2.mpr
        ⟨N₂, a₂, hN₂, hsig₂, hgt₂, hdisj₂, hidx4⟩
  · rintro (hRH | hge4) N₀ a₀ _ hneg₀ P₀
    · exact False.elim ((not_lt_of_ge (riemannHypothesis_iff_integerProbes.mp hRH N₀ a₀)) hneg₀)
    · have hge3 : ((3 : ℕ) : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard :=
        le_trans (by norm_num : ((3 : ℕ) : ℕ∞) ≤ 4) hge4
      exact (disjoint_signedPrimeProbes_gershgorin_iff_rightZeros_ge 3 P₀ one_pos le_rfl).2.mp hge3

/-- **Parity upgrade from `m = 3` to `m = 4` Gershgorin probes.**
`ThreeProbeAmplificationLaw` automatically upgrades any negative witness to four pairwise-disjoint
signed prime-supported probes above `P₀` with normalized off-diagonal row sums `< ε`. -/
theorem four_gershgorin_probes_of_threeProbeAmplificationLaw
    (h3 : ThreeProbeAmplificationLaw) {N₀ : ℕ} {a₀ : Fin N₀ → ℤ}
    (hsig₀ : isSignedPrimeSupported a₀) (hneg₀ : integerProbe N₀ a₀ < 0)
    (P₀ : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (N : ℕ) (a : Fin 4 → (Fin N → ℤ)),
      P₀ < N ∧
      (∀ r : Fin 4, isSignedPrimeSupported (a r)) ∧
      (∀ (r : Fin 4) (ℓ : Fin N), a r ℓ ≠ 0 → P₀ < ℓ.val + 1) ∧
      (∀ r s : Fin 4, r ≠ s → Disjoint (activeConductors (a r)) (activeConductors (a s))) ∧
      (∀ r : Fin 4, probePairing N (a r) (a r) < 0) ∧
      (∀ r : Fin 4,
        ∑ s ∈ Finset.univ.erase r,
          |probePairing N (a r) (a s)| /
            Real.sqrt (probePairing N (a r) (a r) * probePairing N (a s) (a s)) < ε) ∧
      hermNegIndex (probeGramMatrix N a) = 4 := by
  obtain ⟨N₁, a₁, _, _, _, _, hidx3⟩ := h3 N₀ a₀ hsig₀ hneg₀ P₀
  exact odd_probe_rank_forces_even_succ (k := 1) a₁ hidx3 P₀ hε hε1

/-- **QIC payoff at `m = 3`:** `ThreeProbeAmplificationLaw` already discharges
`TwoIntervalRadialExclusionLaw` across all zero configurations. -/
theorem twoIntervalRadialExclusionLaw_of_threeProbeAmplificationLaw
    (h3 : ThreeProbeAmplificationLaw) :
    TwoIntervalRadialExclusionLaw :=
  twoIntervalRadialExclusionLaw_iff_no_singleQuartet.mpr
    (threeProbeAmplificationLaw_iff_no_singleQuartet.mp h3)

/-- **PDR payoff at `m = 3`:** `ThreeProbeAmplificationLaw` already removes the single-quartet
branch from the `(2, 3, 6)` ordinary-prime `θ`-dilation recurrences, making bounded residuals
unambiguously equivalent to `RiemannHypothesis`. -/
theorem ordinary_prime_recurrences_iff_rh_of_threeProbeAmplificationLaw
    (h3 : ThreeProbeAmplificationLaw) {β γ : ℝ}
    (hβ : 1 / 2 < β) (hβ' : β < 1) (hγ : 0 < γ) :
    (¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 2 β γ) ∧
      ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 3 β γ) ∧
      ¬ IsSqrtLogSqUnbounded (ordinaryThetaDilationResidual 6 β γ)) ↔
      RiemannHypothesis := by
  rw [ordinary_prime_recurrences_iff_rh_or_singleQuartet hβ hβ' hγ]
  have hno := threeProbeAmplificationLaw_iff_no_singleQuartet.mp h3 ((β : ℂ) + I * (γ : ℂ))
  exact ⟨fun hor => hor.elim id fun hq => False.elim (hno hq), Or.inl⟩

/-- **PPC payoff at `m = 3`:** `ThreeProbeAmplificationLaw` already excludes the two-wave
proper-power discrepancy regime for every candidate off-line zero `ρ` of `ζ`. -/
theorem no_properPower_twoWave_quartet_of_threeProbeAmplificationLaw
    (h3 : ThreeProbeAmplificationLaw) {ρ : ℂ} (hh : 1 / 2 < ρ.re)
    (hmem : ρ ∈ Zeta23.zetaZeroConfig.carrier) :
    ¬ ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
      |properPowerDiscrepancy (y ^ (2 : ℝ)) -
        (quartetPrimeWaveTerm ρ y + quartetPrimeWaveTerm ρ (y ^ (2 / 3 : ℝ)))| ≤
        K * (Real.sqrt y * (1 + Real.log y) ^ 2) :=
  mt (hasSingleOffLineQuartet_iff_two_properPower_waves hh hmem).mpr
    (threeProbeAmplificationLaw_iff_no_singleQuartet.mp h3 ρ)

/-! ### 3. Ten-way equivalence for all-`m` amplification -/

/-- **Ten-way equivalence of all-`m` prime-displacement index amplification across routes.** -/
theorem primeDisplacement_amplification_tfae :
    [NegativePrimeWitnessForcesUnboundedIndex,
      NegativePrimeWitnessForcesMProbes,
      NegativePrimeWitnessForcesGershgorinProbes,
      TwoPrimeDiffWitnessForcesUnboundedProbes,
      BacklundConverse.FiniteOffLine → RiemannHypothesis,
      ArithmeticCastelnuovoSeveri.realPacketNegIndex = 0 ∨
        ArithmeticCastelnuovoSeveri.realPacketNegIndex = ⊤,
      SequentialSubInverseOrdinateTailTarget,
      (∃ (S : Finset XiZeroCopy) (K : ℝ), FiniteWaveLaw S K) → ∃ K : ℝ, FiniteWaveLaw ∅ K,
      BacklundConverse.FiniteOffLine → 0 < volume InfiniteRankWeilTheory.subexponentialLagBases,
      ModeQuotientPersistenceLaw].TFAE := by
  tfae_have 3 → 2 := by
    intro h3 N₀ a₀ hsig₀ hneg₀ m P₀
    obtain ⟨N, a, hN, hsig, hgt, hdisj, hdiag, hrow⟩ :=
      h3 N₀ a₀ hsig₀ hneg₀ m P₀ 1 one_pos le_rfl
    exact ⟨N, a, hN, hsig, hgt, hdisj, hermNegIndex_eq_of_gershgorin_row_lt_one a hdiag hrow⟩
  tfae_have 2 → 4 := by
    intro h2 N₀ a₀ hsig₀ _ hneg₀ m P₀
    exact h2 N₀ a₀ hsig₀ hneg₀ m P₀
  tfae_have 4 → 1 := by
    intro h4 N₀ a₀ _ hneg₀ P₀
    have hnRH : ¬ RiemannHypothesis := fun hRH =>
      (not_lt_of_ge (riemannHypothesis_iff_integerProbes.mp hRH N₀ a₀)) hneg₀
    obtain ⟨N₁, b₁, _, _, hsig₁, hcard₁, _, _, _, _, _, _, hneg₁⟩ :=
      exists_twoPrime_diff_neg_integerProbe_of_not_rh hnRH 0
    rw [← rightZeros_encard_eq_iSup_primeSubmatrix P₀]
    refine eq_top_iff.mpr (ENat.forall_natCast_le_iff_le.mp fun m _ => ?_)
    exact (disjoint_signedPrimeProbes_gershgorin_iff_rightZeros_ge m P₀ one_pos le_rfl).2.mpr
      (h4 N₁ b₁ hsig₁ hcard₁ hneg₁ m P₀)
  tfae_have 1 → 5 := by
    intro h1 hfin
    by_contra hnRH
    obtain ⟨N₀, a₀, _, _, hsig₀, _, _, _, _, _, _, _, hneg₀⟩ :=
      exists_twoPrime_diff_neg_integerProbe_of_not_rh hnRH 0
    have htop := h1 N₀ a₀ hsig₀ hneg₀ 0
    rw [← rightZeros_encard_eq_iSup_primeSubmatrix 0] at htop
    have hf : (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).Finite :=
      rightZeros_zeta_finite_iff_finiteOffLine.mpr hfin
    exact hf.encard_lt_top.ne htop
  tfae_have 5 → 3 := by
    intro hb13 N₀ a₀ _ hneg₀ m P₀ ε hε hε1
    have hnRH : ¬ RiemannHypothesis := fun hRH =>
      (not_lt_of_ge (riemannHypothesis_iff_integerProbes.mp hRH N₀ a₀)) hneg₀
    have hnfin : ¬ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).Finite := fun hf =>
      hnRH (hb13 (rightZeros_zeta_finite_iff_finiteOffLine.mp hf))
    have hinf : (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).Infinite := hnfin
    have hge : (m : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard := by
      rw [hinf.encard_eq]; exact le_top
    exact (disjoint_signedPrimeProbes_gershgorin_iff_rightZeros_ge m P₀ hε hε1).1.mp hge
  tfae_have 5 ↔ 6 := ArithmeticCastelnuovoSeveri.finiteOffLine_imp_rh_iff_packetIndex_zero_or_infinite
  tfae_have 5 ↔ 7 := (finiteLayer_wallCusp_targets_tfae.out 4 6).symm
  tfae_have 5 ↔ 8 := stageTwo_primeSide_tfae.out 0 3
  tfae_have 5 ↔ 9 := by
    have hf_iff : BacklundConverse.FiniteOffLine ↔ InfiniteRankWeilTheory.FiniteOffLine :=
      finiteOffLine_iff_finite_re_ne_half
    simpa only [hf_iff] using InfiniteRankWeilTheory.b13_iff_pos_volume_subexponentialLagBases
  tfae_have 5 → 10 := by
    intro hb13 N₀ a₀ _ hneg₀ S₀ hS₀_re hS₀_conj P₀ δ hδ
    have hnRH : ¬ RiemannHypothesis := fun hRH =>
      (not_lt_of_ge (riemannHypothesis_iff_integerProbes.mp hRH N₀ a₀)) hneg₀
    have hinf : (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).Infinite := fun hf =>
      hnRH (hb13 (rightZeros_zeta_finite_iff_finiteOffLine.mp hf))
    have hnot_sub : ¬ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig ⊆ (S₀ : Set ℂ)) :=
      fun hsub => hinf (S₀.finite_toSet.subset hsub)
    obtain ⟨ρ_star, hstar, hnot1⟩ := Set.not_subset.mp hnot_sub
    have hnot1' : ρ_star ∉ S₀ := hnot1
    have hnot2' : conj ρ_star ∉ S₀ := fun hc => hnot1' (by simpa using hS₀_conj _ hc)
    exact exists_signedPrimeProbe_nearAnnihilating_of_not_mem_pair hS₀_re hstar hnot1' hnot2' P₀ hδ
  tfae_have 10 → 5 := by
    intro h10 hfin
    by_contra hnRH
    obtain ⟨N₀, a₀, _, _, hsig₀, _, _, _, _, _, _, _, hneg₀⟩ :=
      exists_twoPrime_diff_neg_integerProbe_of_not_rh hnRH 0
    have hf : (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).Finite :=
      rightZeros_zeta_finite_iff_finiteOffLine.mpr hfin
    let S₀ : Finset ℂ := hf.toFinset
    have hsub : ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig ⊆ (S₀ : Set ℂ) :=
      fun ρ hρ => hf.mem_toFinset.mpr hρ
    have hS₀_re : ∀ ρ ∈ S₀, 1 / 2 < ρ.re :=
      fun ρ hρ => (hf.mem_toFinset.mp hρ).2
    have hS₀_conj : ∀ ρ ∈ S₀, conj ρ ∈ S₀ := by
      intro ρ hρ
      obtain ⟨hcar, hre⟩ := hf.mem_toFinset.mp hρ
      exact hf.mem_toFinset.mpr ⟨fesSymmetric_zetaZeroConfig.conj_mem hcar, by simpa using hre⟩
    obtain ⟨η, hη, hlow⟩ := exists_uniform_modePair_lower_of_rightZeros_subset hsub
    obtain ⟨N, a, _, _, _, hneg_a, hmp_lt⟩ :=
      h10 N₀ a₀ hsig₀ hneg₀ S₀ hS₀_re hS₀_conj 0 η hη
    obtain ⟨ρ, hρ, hge⟩ := hlow N a hneg_a
    exact (not_lt_of_ge hge) (hmp_lt ρ hρ)
  tfae_finish

/-- All-`m` amplification strictly implies the `m = 3` amplification threshold. -/
theorem threeProbeAmplificationLaw_of_unboundedIndex
    (h : NegativePrimeWitnessForcesUnboundedIndex) :
    ThreeProbeAmplificationLaw := by
  have h2 : NegativePrimeWitnessForcesMProbes :=
    (primeDisplacement_amplification_tfae.out 0 1).mp h
  exact fun N₀ a₀ hsig₀ hneg₀ P₀ => h2 N₀ a₀ hsig₀ hneg₀ 3 P₀

/-- **ZCG payoff:** `NegativePrimeWitnessForcesUnboundedIndex` reduces `RiemannHypothesis` to
`BacklundConverse.ZerosApproachLine ∧ ZetaLandingLaw`. -/
theorem riemannHypothesis_iff_zal_and_landing_of_unboundedIndex
    (h : NegativePrimeWitnessForcesUnboundedIndex) :
    RiemannHypothesis ↔ BacklundConverse.ZerosApproachLine ∧ ZetaLandingLaw := by
  have hwall : SequentialWallCuspVanishingTarget :=
    (finiteLayer_wallCusp_targets_tfae.out 6 0).mp
      ((primeDisplacement_amplification_tfae.out 0 4).mp h)
  exact riemannHypothesis_iff_zal_and_landing_of_wallCuspTarget hwall

/-! ### 4. Complete synthesis of unconditional solutions, equivalences, and scope boundaries -/

/-- **Complete structural resolution of prime-displacement Gram separation and index amplification:**
1. **Unconditional `m = 2` Gershgorin and determinant separation for `ζ`:** every negative integer
   probe yields two disjoint signed high-prime probes satisfying `G₁₁ < 0`, `G₂₂ < 0`,
   `|G₁₂| < ε √(G₁₁ G₂₂)`, and `G₁₂² < G₁₁ G₂₂`.
2. **Unconditional failure of naive prime-scale separation (`Δ → +∞`):** transporting any zero-sum
   negative witness to prime shells separated by multiplicative ratio `R ≥ 2` yields `G₁₁ < 0`,
   `G₂₂ < 0`, and `G₁₂² > B · G₁₁ G₂₂` for every `B > 0`.
3. **Exact `m = 3` single-quartet threshold:** `ThreeProbeAmplificationLaw` is equivalent to
   `∀ ρ₀, ¬ HasSingleOffLineQuartet ρ₀`, upgrades to `m = 4` Gershgorin probes, and discharges
   `TwoIntervalRadialExclusionLaw` together with the single-quartet branches of PDR and PPC.
4. **Ten-way all-`m` equivalence and ZCG reduction:** `primeDisplacement_amplification_tfae` links
   all-`m` probe amplification, finite-mode quotient persistence, `FiniteOffLine → RiemannHypothesis`,
   the critical-state tail law, finite-wave `ψ` exclusion, and metric lag positivity, reducing
   `RiemannHypothesis` to `ZerosApproachLine ∧ ZetaLandingLaw`.
5. **Infinite-configuration scope boundary:** infinite off-line configurations with isolated finite
   outer tails attain every abscissa `σ₀ ∈ (1/2, 1)` even under `ApproachesLine`. -/
theorem primeDisplacement_complete_resolution :
    (∀ {N₀ : ℕ} {a₀ : Fin N₀ → ℤ}, integerProbe N₀ a₀ < 0 →
      ∀ (P₀ : ℕ) {ε : ℝ}, 0 < ε → ε ≤ 1 →
        ∃ (N : ℕ) (a₁ a₂ : Fin N → ℤ),
          P₀ < N ∧ isSignedPrimeSupported a₁ ∧ isSignedPrimeSupported a₂ ∧
          (∀ i : Fin N, a₁ i ≠ 0 → P₀ < i.val + 1) ∧
          (∀ j : Fin N, a₂ j ≠ 0 → P₀ < j.val + 1) ∧
          Disjoint (activeConductors a₁) (activeConductors a₂) ∧
          probePairing N a₁ a₁ < 0 ∧ probePairing N a₂ a₂ < 0 ∧
          |probePairing N a₁ a₂| < ε * Real.sqrt (probePairing N a₁ a₁ * probePairing N a₂ a₂) ∧
          (probePairing N a₁ a₂) ^ 2 < probePairing N a₁ a₁ * probePairing N a₂ a₂ ∧
          hermNegIndex (probeGramMatrix N ![a₁, a₂]) = 2) ∧
    (∀ {M : ℕ} {u : Fin M → ℤ}, integerProbe M u < 0 → (∑ i : Fin M, u i) = 0 →
      ∀ (P₀ R : ℕ), 2 ≤ R → ∀ {B : ℝ}, 0 < B →
        ∃ (N : ℕ) (a₁ a₂ : Fin N → ℤ),
          P₀ < N ∧ isSignedPrimeSupported a₁ ∧ isSignedPrimeSupported a₂ ∧
          (∀ i : Fin N, a₁ i ≠ 0 → P₀ < i.val + 1) ∧
          (∀ j : Fin N, a₂ j ≠ 0 → P₀ < j.val + 1) ∧
          (∀ i j : Fin N, a₁ i ≠ 0 → a₂ j ≠ 0 → R * (i.val + 1) < j.val + 1) ∧
          Disjoint (activeConductors a₁) (activeConductors a₂) ∧
          probePairing N a₁ a₁ < 0 ∧ probePairing N a₂ a₂ < 0 ∧
          B * (probePairing N a₁ a₁ * probePairing N a₂ a₂) < (probePairing N a₁ a₂) ^ 2) ∧
    (ThreeProbeAmplificationLaw ↔ ∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀) ∧
    (ThreeProbeAmplificationLaw → TwoIntervalRadialExclusionLaw) ∧
    [NegativePrimeWitnessForcesUnboundedIndex,
      NegativePrimeWitnessForcesMProbes,
      NegativePrimeWitnessForcesGershgorinProbes,
      TwoPrimeDiffWitnessForcesUnboundedProbes,
      BacklundConverse.FiniteOffLine → RiemannHypothesis,
      ArithmeticCastelnuovoSeveri.realPacketNegIndex = 0 ∨
        ArithmeticCastelnuovoSeveri.realPacketNegIndex = ⊤,
      SequentialSubInverseOrdinateTailTarget,
      (∃ (S : Finset XiZeroCopy) (K : ℝ), FiniteWaveLaw S K) → ∃ K : ℝ, FiniteWaveLaw ∅ K,
      BacklundConverse.FiniteOffLine → 0 < volume InfiniteRankWeilTheory.subexponentialLagBases,
      ModeQuotientPersistenceLaw].TFAE ∧
    (NegativePrimeWitnessForcesUnboundedIndex →
      (RiemannHypothesis ↔ BacklundConverse.ZerosApproachLine ∧ ZetaLandingLaw)) ∧
    (∀ {σ₀ : ℝ}, 1 / 2 < σ₀ → σ₀ < 1 →
      ∃ Z : ZeroConfig,
        (rightOf Z ((σ₀ - 1 / 2) / 2)).Finite ∧
        (rightOf Z ((σ₀ - 1 / 2) / 2)).Nonempty ∧
        (rightOf Z 0).Infinite ∧
        AbscissaLawAt Z 0 ∧
        ApproachesLine Z ∧
        zeroAbscissa Z = σ₀) := by
  refine ⟨fun hneg P₀ _ hε hε1 => twoProbe_gershgorin_and_det_of_neg_integerProbe hneg P₀ hε hε1,
    fun hneg hsum P₀ R hR _ hB =>
      exists_scaleSeparated_primeCopies_violating_det hneg hsum P₀ R hR hB,
    threeProbeAmplificationLaw_iff_no_singleQuartet,
    twoIntervalRadialExclusionLaw_of_threeProbeAmplificationLaw,
    primeDisplacement_amplification_tfae,
    riemannHypothesis_iff_zal_and_landing_of_unboundedIndex,
    fun h12 h1 => ?_⟩
  obtain ⟨Z, hfin, hne, hinf, hab0, happ, habs, _, _⟩ :=
    exists_isolatedOuterTail_above_infiniteApproachingBackground h12 h1
  exact ⟨Z, hfin, hne, hinf, hab0, happ, habs⟩

end GaloisForLFunctions.ExceptionalLayerTheory
