import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFERegularFockVacuumObstruction
import GaloisForLFunctions.HTGeometry.LpReindexCompactDichotomy

/-!
# Source-FE finite-mode Fock-vacuum orthogonality catastrophe

HC82 proves directly that a repeated nonzero source-FE pair ratio has no nonzero normalizable
infinite-mode recurrence vacuum. A possible escape remains: every finite cutoff may have a perfectly
regular vacuum, and those cutoff vacua might converge inside the ordinary occupation Hilbert space.

This module constructs the cutoff family explicitly in one common `BosonicFock Nat`. For a complex
ratio `r`, its `N`-mode vector is the normalized sum over Boolean pair occupations

`c(r)^N sum_{S subset range N} r^|S| e_(2 1_S)`,

where `c(r) = (1 + ‖r‖²)^(-1/2)`. Pair occupations are injective, finite Pythagoras and the subset
product identity give exact unit norm, and the vectors satisfy the admitted finite-mode pair
recurrence.

For nonzero `r`, every fixed occupation coefficient tends to zero while every cutoff norm remains
one. Completeness and continuous coordinate evaluation therefore show the sequence cannot be
Cauchy. For `r=0` it is the constant ordinary vacuum. Thus common-Fock Cauchy convergence holds
exactly at zero ratio. Specializing to the literal source-FE ratio gives critical-wall placement,
globally RH, and the HB, Deninger/FZZ-P, PW-B, and canonical-copy RBH receivers.

The conclusion does not rule out a von Neumann incomplete tensor-product or other nonregular
sector. It proves that such a sector is not the norm completion of these vectors in reference Fock.

`[NEW] [ORTHOGONALITY CATASTROPHE] [COMMON FOCK] [CAUCHY IFF RH] [LEAN-PROVED]`
-/

open Complex Real Filter Topology
open scoped ENNReal BigOperators

namespace RHTower

noncomputable section

/-- Occupation with two particles in exactly the modes of `S`. -/
def pairOccupation (S : Finset ℕ) : ℕ →₀ ℕ :=
  Finsupp.onFinset S (fun n => if n ∈ S then 2 else 0) (by
    intro n hn
    by_contra hmem
    simp [hmem] at hn)

@[simp] theorem pairOccupation_apply (S : Finset ℕ) (n : ℕ) :
    pairOccupation S n = if n ∈ S then 2 else 0 := by
  exact Finsupp.onFinset_apply

theorem pairOccupation_apply_eq_two_iff (S : Finset ℕ) (n : ℕ) :
    pairOccupation S n = 2 ↔ n ∈ S := by
  simp [pairOccupation_apply]

/-- Pair occupations remember their mode set. -/
theorem pairOccupation_injective : Function.Injective pairOccupation := by
  intro S T hST
  apply Finset.ext
  intro n
  rw [← pairOccupation_apply_eq_two_iff, ← pairOccupation_apply_eq_two_iff, hST]

/-- Unnormalized finite-mode pair product in the common occupation Hilbert space. -/
def finitePairFockRaw (r : ℂ) (N : ℕ) : HTGeometry.BosonicFock ℕ :=
  ∑ S ∈ (Finset.range N).powerset,
    lp.single 2 (pairOccupation S) (r ^ S.card)

theorem norm_finitePairFockRaw_sq (r : ℂ) (N : ℕ) :
    ‖finitePairFockRaw r N‖ ^ 2 = (1 + ‖r‖ ^ 2) ^ N := by
  rw [finitePairFockRaw,
    GaloisForLFunctions.HTGeometry.LpDiagonal.norm_sq_sum_single
      (Finset.range N).powerset pairOccupation pairOccupation_injective.injOn
      (fun S => r ^ S.card)]
  have hterm : ∀ S ∈ (Finset.range N).powerset,
      ‖r ^ S.card‖ ^ 2 = ∏ _n ∈ S, ‖r‖ ^ 2 := by
    intro S hS
    simp [norm_pow, ← pow_mul, Nat.mul_comm]
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.prod_one_add]
  simp

/-- Exact raw coefficient at a pair occupation lying below the cutoff. -/
theorem finitePairFockRaw_apply_pairOccupation
    (r : ℂ) (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range N) :
    finitePairFockRaw r N (pairOccupation S) = r ^ S.card := by
  rw [finitePairFockRaw,
    GaloisForLFunctions.HTGeometry.LpDiagonal.coe_sum_single]
  rw [Finset.sum_eq_single S]
  · simp
  · intro T hT hTS
    rw [if_neg]
    exact fun hocc => hTS (pairOccupation_injective hocc)
  · intro hnot
    exact (hnot (Finset.mem_powerset.mpr hS)).elim

/-- Raw coefficients vanish away from pair occupations. -/
theorem finitePairFockRaw_apply_eq_zero_of_not_pairOccupation
    (r : ℂ) (N : ℕ) (μ : ℕ →₀ ℕ)
    (hμ : ¬ ∃ S : Finset ℕ, pairOccupation S = μ) :
    finitePairFockRaw r N μ = 0 := by
  rw [finitePairFockRaw,
    GaloisForLFunctions.HTGeometry.LpDiagonal.coe_sum_single]
  apply Finset.sum_eq_zero
  intro S hS
  rw [if_neg]
  exact fun hocc => hμ ⟨S, hocc⟩

/-- One-site normalization factor of a pair product. -/
def finitePairFockFactor (r : ℂ) : ℝ :=
  (Real.sqrt (1 + ‖r‖ ^ 2))⁻¹

theorem finitePairFockFactor_nonneg (r : ℂ) : 0 ≤ finitePairFockFactor r := by
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem finitePairFockFactor_pos (r : ℂ) : 0 < finitePairFockFactor r := by
  rw [finitePairFockFactor]
  exact inv_pos.mpr (Real.sqrt_pos.2 (by positivity))

/-- A nontrivial local pair makes the one-site overlap strictly contractive. -/
theorem finitePairFockFactor_lt_one (r : ℂ) (hr : r ≠ 0) :
    finitePairFockFactor r < 1 := by
  rw [finitePairFockFactor, inv_lt_one₀ (Real.sqrt_pos.2 (by positivity))]
  rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
  nlinarith [norm_pos_iff.mpr hr]

theorem finitePairFockFactor_sq_mul (r : ℂ) :
    finitePairFockFactor r ^ 2 * (1 + ‖r‖ ^ 2) = 1 := by
  have hpos : 0 < 1 + ‖r‖ ^ 2 := by positivity
  rw [finitePairFockFactor, inv_pow, Real.sq_sqrt hpos.le]
  exact inv_mul_cancel₀ hpos.ne'

/-- Normalized finite-mode pair product in one common occupation Hilbert space. -/
def finitePairFockVacuum (r : ℂ) (N : ℕ) : HTGeometry.BosonicFock ℕ :=
  ((finitePairFockFactor r ^ N : ℝ) : ℂ) • finitePairFockRaw r N

theorem norm_finitePairFockVacuum_sq (r : ℂ) (N : ℕ) :
    ‖finitePairFockVacuum r N‖ ^ 2 = 1 := by
  rw [finitePairFockVacuum, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (finitePairFockFactor_nonneg r) N),
    norm_finitePairFockRaw_sq]
  rw [show (finitePairFockFactor r ^ N) ^ 2 =
      (finitePairFockFactor r ^ 2) ^ N by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega]
  rw [← mul_pow, finitePairFockFactor_sq_mul, one_pow]

theorem norm_finitePairFockVacuum (r : ℂ) (N : ℕ) :
    ‖finitePairFockVacuum r N‖ = 1 := by
  nlinarith [norm_finitePairFockVacuum_sq r N,
    norm_nonneg (finitePairFockVacuum r N)]

/-- Exact normalized coefficient at a pair occupation below the cutoff. -/
theorem finitePairFockVacuum_apply_pairOccupation
    (r : ℂ) (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range N) :
    finitePairFockVacuum r N (pairOccupation S) =
      (finitePairFockFactor r ^ N : ℂ) * r ^ S.card := by
  simp [finitePairFockVacuum,
    finitePairFockRaw_apply_pairOccupation r N S hS]

/-- Exact finite-mode pair recurrence on every admitted Boolean-pair occupation. -/
theorem finitePairFockVacuum_pairRecurrence
    (r : ℂ) (N n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range N) (hn : n < N) (hnS : n ∉ S) :
    finitePairFockVacuum r N (pairOccupation (insert n S)) =
      r * finitePairFockVacuum r N (pairOccupation S) := by
  have hins : insert n S ⊆ Finset.range N := by
    intro k hk
    rw [Finset.mem_insert] at hk
    rcases hk with rfl | hk
    · exact Finset.mem_range.mpr hn
    · exact hS hk
  rw [finitePairFockVacuum_apply_pairOccupation r N (insert n S) hins,
    finitePairFockVacuum_apply_pairOccupation r N S hS,
    Finset.card_insert_of_notMem hnS, pow_succ]
  ring

/-- Normalized coefficients vanish away from pair occupations. -/
theorem finitePairFockVacuum_apply_eq_zero_of_not_pairOccupation
    (r : ℂ) (N : ℕ) (μ : ℕ →₀ ℕ)
    (hμ : ¬ ∃ S : Finset ℕ, pairOccupation S = μ) :
    finitePairFockVacuum r N μ = 0 := by
  simp [finitePairFockVacuum,
    finitePairFockRaw_apply_eq_zero_of_not_pairOccupation r N μ hμ]

/-- Every fixed coefficient of a nontrivial finite-mode pair product vanishes at infinite cutoff. -/
theorem finitePairFockVacuum_apply_tendsto_zero_of_ne
    (r : ℂ) (hr : r ≠ 0) (μ : ℕ →₀ ℕ) :
    Tendsto (fun N : ℕ => finitePairFockVacuum r N μ) atTop (𝓝 0) := by
  have hpowR : Tendsto (fun N : ℕ => finitePairFockFactor r ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (finitePairFockFactor_nonneg r) (finitePairFockFactor_lt_one r hr)
  have hpowC : Tendsto (fun N : ℕ => (finitePairFockFactor r ^ N : ℂ))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hpowR)
  by_cases hpair : ∃ S : Finset ℕ, pairOccupation S = μ
  · obtain ⟨S, hSμ⟩ := hpair
    obtain ⟨N₀, hSN₀⟩ := Finset.exists_nat_subset_range S
    have hmodel : Tendsto
        (fun N : ℕ => (finitePairFockFactor r ^ N : ℂ) * r ^ S.card)
        atTop (𝓝 0) := by
      simpa using hpowC.mul_const (r ^ S.card)
    apply hmodel.congr'
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hSN : S ⊆ Finset.range N :=
      hSN₀.trans (Finset.range_mono hN)
    rw [← hSμ, finitePairFockVacuum_apply_pairOccupation r N S hSN]
  · have hzero : (fun N : ℕ => finitePairFockVacuum r N μ) = fun _N => 0 := by
      funext N
      exact finitePairFockVacuum_apply_eq_zero_of_not_pairOccupation r N μ hpair
    rw [hzero]
    exact tendsto_const_nhds

/-- With zero pair ratio every raw cutoff vector is the ordinary vacuum. -/
theorem finitePairFockRaw_zero (N : ℕ) :
    finitePairFockRaw 0 N = lp.single 2 (0 : ℕ →₀ ℕ) (1 : ℂ) := by
  have hempty : pairOccupation ∅ = (0 : ℕ →₀ ℕ) := by
    ext n
    simp
  rw [finitePairFockRaw]
  rw [Finset.sum_eq_single (∅ : Finset ℕ)]
  · rw [hempty]
    simp
  · intro S hS hSne
    have hcard : S.card ≠ 0 :=
      Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hSne)
    simp [hcard]
  · simp

/-- With zero pair ratio every normalized cutoff vector is the ordinary vacuum. -/
theorem finitePairFockVacuum_zero (N : ℕ) :
    finitePairFockVacuum 0 N = lp.single 2 (0 : ℕ →₀ ℕ) (1 : ℂ) := by
  simp [finitePairFockVacuum, finitePairFockFactor, finitePairFockRaw_zero]

/-- The common-Fock finite-mode vacuum family is Cauchy exactly for zero pair ratio. -/
theorem cauchySeq_finitePairFockVacuum_iff (r : ℂ) :
    CauchySeq (finitePairFockVacuum r) ↔ r = 0 := by
  constructor
  · intro hc
    by_contra hr
    obtain ⟨ψ, hψ⟩ := cauchySeq_tendsto_of_complete hc
    have hψzero : ψ = 0 := by
      apply lp.ext
      funext μ
      have hcoord : Tendsto (fun N : ℕ => finitePairFockVacuum r N μ)
          atTop (𝓝 (ψ μ)) := by
        have hmap :=
          ((lp.evalCLM ℂ (fun _ : ℕ →₀ ℕ => ℂ) 2 μ).continuous.continuousAt.tendsto).comp hψ
        exact hmap
      exact tendsto_nhds_unique hcoord
        (finitePairFockVacuum_apply_tendsto_zero_of_ne r hr μ)
    have hnorm : Tendsto (fun N : ℕ => ‖finitePairFockVacuum r N‖)
        atTop (𝓝 ‖ψ‖) := hψ.norm
    have hone : Tendsto (fun _N : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hnormeq : ‖ψ‖ = 1 := by
      apply tendsto_nhds_unique hnorm
      simpa only [norm_finitePairFockVacuum] using hone
    rw [hψzero, norm_zero] at hnormeq
    norm_num at hnormeq
  · intro hr
    subst r
    have hconst : finitePairFockVacuum 0 =
        fun _N : ℕ => lp.single 2 (0 : ℕ →₀ ℕ) (1 : ℂ) := by
      funext N
      exact finitePairFockVacuum_zero N
    rw [hconst]
    exact cauchySeq_const _

/-- Literal source-FE finite-mode vacuum inside the common occupation Hilbert space. -/
def hbXiPeierlsUnitSourceFEFiniteModeFockVacuum
    (q : XiZeroCopy) (N : ℕ) : HTGeometry.BosonicFock ℕ :=
  finitePairFockVacuum (hbXiPeierlsUnitSourceFEFockVacuumPairRatio q) N

/-- Every source-FE cutoff vacuum is exactly normalized. -/
theorem norm_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_sq
    (q : XiZeroCopy) (N : ℕ) :
    ‖hbXiPeierlsUnitSourceFEFiniteModeFockVacuum q N‖ ^ 2 = 1 :=
  norm_finitePairFockVacuum_sq _ N

/-- Common-Fock cutoff vacua are Cauchy exactly when the source pair amplitude vanishes. -/
theorem cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_pair_eq_zero
    (q : XiZeroCopy) :
    CauchySeq (hbXiPeierlsUnitSourceFEFiniteModeFockVacuum q) ↔
      hbXiPeierlsUnitSourceFEOrbitBogoliubovPair q = 0 := by
  exact (cauchySeq_finitePairFockVacuum_iff
    (hbXiPeierlsUnitSourceFEFockVacuumPairRatio q)).trans
      (hbXiPeierlsUnitSourceFEFockVacuumPairRatio_eq_zero_iff_pair_eq_zero q)

/-- Common-Fock cutoff vacua are Cauchy exactly in partner vacuum. -/
theorem cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_partnerNumber_eq_zero
    (q : XiZeroCopy) :
    CauchySeq (hbXiPeierlsUnitSourceFEFiniteModeFockVacuum q) ↔
      hbXiPeierlsUnitSourceFEOrbitPartnerNumber q = 0 :=
  (cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_pair_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitBogoliubovPair_eq_zero_iff_partnerNumber_eq_zero q)

/-- Common-Fock cutoff vacua are Cauchy exactly on the critical wall. -/
theorem cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_re_eq_half
    (q : XiZeroCopy) :
    CauchySeq (hbXiPeierlsUnitSourceFEFiniteModeFockVacuum q) ↔
      (q.1 : ℂ).re = 1 / 2 :=
  (cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_partnerNumber_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff q)

/-- Off wall, perfectly normalized finite-mode vacua are not Cauchy in the reference Fock sector. -/
theorem not_cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_of_offWall
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2) :
    ¬ CauchySeq (hbXiPeierlsUnitSourceFEFiniteModeFockVacuum q) :=
  (cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_re_eq_half q).not.mpr hq

/-- Every actual occupation coefficient of an off-wall cutoff vacuum vanishes in the infinite-mode
limit, despite unit norm at every cutoff. -/
theorem hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_apply_tendsto_zero_of_offWall
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2) (μ : ℕ →₀ ℕ) :
    Tendsto (fun N : ℕ => hbXiPeierlsUnitSourceFEFiniteModeFockVacuum q N μ)
      atTop (𝓝 0) := by
  apply finitePairFockVacuum_apply_tendsto_zero_of_ne
  exact (hbXiPeierlsUnitSourceFEFockVacuumPairRatio_eq_zero_iff_pair_eq_zero q).not.mpr
    ((hbXiPeierlsUnitSourceFEOrbitBogoliubovPair_eq_zero_iff_partnerNumber_eq_zero q).not.mpr
      ((hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff q).not.mpr hq))

/-- Universal common-Fock Cauchy convergence of the source-FE cutoff vacua. -/
def HBXiPeierlsUnitSourceFEGlobalFiniteModeFockCauchy : Prop :=
  ∀ q : XiZeroCopy,
    CauchySeq (hbXiPeierlsUnitSourceFEFiniteModeFockVacuum q)

/-- Universal common-Fock convergence of finite-mode source vacua is exactly RH. -/
theorem hbXiPeierlsUnitSourceFEGlobalFiniteModeFockCauchy_iff_rh :
    HBXiPeierlsUnitSourceFEGlobalFiniteModeFockCauchy ↔ RiemannHypothesis := by
  rw [HBXiPeierlsUnitSourceFEGlobalFiniteModeFockCauchy,
    ← forall_hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_rh]
  exact forall_congr' fun q =>
    cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_partnerNumber_eq_zero q

/-- Common-Fock cutoff-vacuum convergence is HB optical darkness. -/
theorem cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_opticalPower_zero
    (n : ℕ) (q : XiZeroCopy) :
    CauchySeq (hbXiPeierlsUnitSourceFEFiniteModeFockVacuum q) ↔
      hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0 :=
  (cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_partnerNumber_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_opticalPower_zero n q)

/-- Common-Fock cutoff-vacuum convergence is Deninger Ward cancellation. -/
theorem cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_sharedWardCharge_zero
    (n : ℕ) (q : XiZeroCopy) :
    CauchySeq (hbXiPeierlsUnitSourceFEFiniteModeFockVacuum q) ↔
      fzzCigarParityDeningerReflectGaugeWardCharge q = 0 :=
  (cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_partnerNumber_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_sharedWardCharge_zero n q)

/-- Common-Fock cutoff-vacuum convergence is FZZ-P information equilibrium. -/
theorem cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_informationForce_zero
    (n : ℕ) (q : XiZeroCopy) :
    CauchySeq (hbXiPeierlsUnitSourceFEFiniteModeFockVacuum q) ↔
      fzzCigarParityReflectedFermiInformationForce
          (deningerDivisorThetaEigen q).re = 0 :=
  (cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_partnerNumber_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_informationForce_zero n q)

/-- Common-Fock cutoff-vacuum convergence is every-grade PW-B balance. -/
theorem cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_pwBalance_zero
    (n : ℕ) (q : XiZeroCopy) (k : ℕ) :
    CauchySeq (hbXiPeierlsUnitSourceFEFiniteModeFockVacuum q) ↔
      schwarzschildParikhWilczekBorelPartnerRealImbalance
          (deningerDivisorThetaEigen q) k = 0 :=
  (cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_partnerNumber_eq_zero q).trans
    (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff_pwBalance_zero n q k)

/-- On the canonical divisor copy, common-Fock cutoff-vacuum convergence is RBH balance. -/
theorem cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_firstCopy_iff_rbhBalance_zero
    (n : ℕ) (rho : XiDivisorSupport) :
    CauchySeq (hbXiPeierlsUnitSourceFEFiniteModeFockVacuum
      (reflectedBiHeatFirstDivisorCopy rho)) ↔
      reflectedBiHeatMultiplicityLeadingJetNormImbalance rho = 0 :=
  (cauchySeq_hbXiPeierlsUnitSourceFEFiniteModeFockVacuum_iff_partnerNumber_eq_zero
    (reflectedBiHeatFirstDivisorCopy rho)).trans
      (hbXiPeierlsUnitSourceFEOrbitPartnerNumber_firstCopy_eq_zero_iff_rbhBalance_zero n rho)

end

end RHTower
