import GaloisForLFunctions.RHTower.DeningerBigWittFrobeniusCrossPairSingularOneLegGraphCompletion
import GaloisForLFunctions.RHTower.FrankensteinThetaTerminalGammaSharedGhost

/-!
# Big-Witt singular source forces prime-independent Gamma descent

Finite packets with any fixed left prime have unit one-leg trace and vanish in the ambient
Calderon--Witt edge Hilbert space.  Hence all fixed-left families converge to the same vertical
generator in the genuine singular graph completion.

The coefficient-faithful inverse-Gamma reporter assigns the fixed-left family at `p` the constant
value `p^(-t)`.  A continuous extension to the common source graph must therefore identify the
values at every two retained prime labels.  Two distinct labels force `t = 0`.  Conversely, at
`t = 0` the reporter is exactly the already constructed continuous singular trace.

Thus prime-independent shared-ghost existence is no longer an arbitrary scalar premise: it is
equivalent to continuity of a literal finite Gamma reporter on a common completed Big-Witt source
carrier.  The final Xi statements preserve divisor support and multiplicity.  No RH, zero-location,
positivity, spectral-synthesis, or computation premise occurs.
-/

open Complex Filter Function Set Topology
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

noncomputable local instance instDecidableEqBigWittSingularGammaReporterIndex :
    DecidableEq DeningerCalderonWittCrossPrimePacketIndex :=
  Classical.decEq _

/-- Infinite ordered-edge family with one fixed left prime. -/
def deningerBigWittCrossPairFixedLeftPacketEmbedding
    (a : ℕ) : ℕ ↪ DeningerCalderonWittCrossPrimePacketIndex where
  toFun n :=
    ⟨(deningerBigWittCrossPairNthPrime a,
        deningerBigWittCrossPairNthPrime (a + n + 1)), by
      intro h
      have hv := congrArg Subtype.val h
      exact (Nat.ne_of_lt
        (deningerBigWittCrossPairNthPrime_val_strictMono (by omega))) hv⟩
  inj' := by
    intro m n h
    have hr : deningerBigWittCrossPairNthPrime (a + m + 1) =
        deningerBigWittCrossPairNthPrime (a + n + 1) :=
      congrArg (fun i : DeningerCalderonWittCrossPrimePacketIndex => i.1.2) h
    have hi : a + m + 1 = a + n + 1 :=
      deningerBigWittCrossPairNthPrime_val_strictMono.injective
        (congrArg Subtype.val hr)
    omega

/-- First `n+1` ordered edges in the fixed-left family. -/
def deningerBigWittCrossPairFixedLeftPacketPrefix
    (a n : ℕ) : Finset DeningerCalderonWittCrossPrimePacketIndex :=
  (Finset.range (n + 1)).map (deningerBigWittCrossPairFixedLeftPacketEmbedding a)

@[simp] theorem deningerBigWittCrossPairFixedLeftPacketPrefix_card
    (a n : ℕ) :
    (deningerBigWittCrossPairFixedLeftPacketPrefix a n).card = n + 1 := by
  rw [deningerBigWittCrossPairFixedLeftPacketPrefix, Finset.card_map,
    Finset.card_range]

theorem deningerBigWittCrossPairFixedLeftPacketPrefix_left
    {a n : ℕ} {i : DeningerCalderonWittCrossPrimePacketIndex}
    (hi : i ∈ deningerBigWittCrossPairFixedLeftPacketPrefix a n) :
    i.1.1 = deningerBigWittCrossPairNthPrime a := by
  rw [deningerBigWittCrossPairFixedLeftPacketPrefix, Finset.mem_map] at hi
  obtain ⟨k, _hk, rfl⟩ := hi
  rfl

/-- Unit-trace average on a fixed left-prime fibre. -/
def deningerBigWittCrossPairFixedLeftAveragingPacket
    (a n : ℕ) : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  (deningerBigWittCrossPairFixedLeftPacketPrefix a n).sum fun i =>
    Finsupp.single i (((n + 1 : ℝ) : ℂ)⁻¹)

@[simp] theorem deningerBigWittCrossPairFixedLeftAveragingPacket_apply
    (a n : ℕ) (j : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittCrossPairFixedLeftAveragingPacket a n j =
      if j ∈ deningerBigWittCrossPairFixedLeftPacketPrefix a n then
        (((n + 1 : ℝ) : ℂ)⁻¹) else 0 := by
  classical
  simp [deningerBigWittCrossPairFixedLeftAveragingPacket, Finsupp.single_apply]

@[simp] theorem deningerBigWittCrossPairAlgebraicOneLegTrace_fixedLeftAveragingPacket
    (a n : ℕ) :
    deningerBigWittCrossPairAlgebraicOneLegTrace
        (deningerBigWittCrossPairFixedLeftAveragingPacket a n) = 1 := by
  classical
  rw [deningerBigWittCrossPairFixedLeftAveragingPacket, map_sum]
  simp only [deningerBigWittCrossPairAlgebraicOneLegTrace_single,
    Finset.sum_const, nsmul_eq_mul,
    deningerBigWittCrossPairFixedLeftPacketPrefix_card]
  have hne : ((((n : ℝ) + 1 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (by positivity : (n + 1 : ℝ) ≠ 0)
  rw [show ((n + 1 : ℕ) : ℂ) = ((((n : ℝ) + 1 : ℝ) : ℂ)) by
    norm_cast]
  exact mul_inv_cancel₀ hne

theorem norm_sq_deningerBigWittCrossPairFinitePacketAdmission_fixedLeftAveragingPacket
    (a n : ℕ) :
    ‖deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittCrossPairFixedLeftAveragingPacket a n)‖ ^ 2 =
      (n + 1 : ℝ)⁻¹ := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  rw [show (fun j : DeningerCalderonWittCrossPrimePacketIndex =>
      ‖(deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittCrossPairFixedLeftAveragingPacket a n) :
          DeningerCalderonWittCrossPrimePacketIndex → ℂ) j‖ ^ 2) =
      fun j => if j ∈ deningerBigWittCrossPairFixedLeftPacketPrefix a n then
        ((n + 1 : ℝ)⁻¹) ^ 2 else 0 by
    funext j
    rw [show (deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittCrossPairFixedLeftAveragingPacket a n)) j =
        deningerBigWittCrossPairFixedLeftAveragingPacket a n j by
      exact deningerBigWittCrossPairFinitePacketAdmissionToFun_apply _ _]
    rw [deningerBigWittCrossPairFixedLeftAveragingPacket_apply]
    by_cases hj : j ∈ deningerBigWittCrossPairFixedLeftPacketPrefix a n
    · simp only [if_pos hj]
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
    · simp [hj]]
  rw [tsum_eq_sum (s := deningerBigWittCrossPairFixedLeftPacketPrefix a n)
    (fun j hj => by simp [hj])]
  rw [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const,
    deningerBigWittCrossPairFixedLeftPacketPrefix_card, nsmul_eq_mul]
  have hne : (n + 1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem tendsto_deningerBigWittCrossPairFinitePacketAdmission_fixedLeftAveragingPacket
    (a : ℕ) :
    Tendsto (fun n => deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittCrossPairFixedLeftAveragingPacket a n))
      atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / epsilon ^ 2)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hsq :
      ‖deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittCrossPairFixedLeftAveragingPacket a n)‖ ^ 2 <
        epsilon ^ 2 := by
    rw [norm_sq_deningerBigWittCrossPairFinitePacketAdmission_fixedLeftAveragingPacket]
    have hn1 : 1 / epsilon ^ 2 < (n + 1 : ℝ) := by
      calc
        1 / epsilon ^ 2 < (N : ℝ) := by exact_mod_cast hN
        _ ≤ n := by exact_mod_cast hn
        _ < n + 1 := by norm_num
    have hnpos : (0 : ℝ) < n + 1 := by positivity
    rw [inv_lt_iff_one_lt_mul₀ hnpos]
    have heps : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
    have hprod : 1 < (n + 1 : ℝ) * epsilon ^ 2 :=
      (div_lt_iff₀ heps).mp hn1
    nlinarith
  nlinarith [norm_nonneg (deningerBigWittCrossPairFinitePacketAdmission
    (deningerBigWittCrossPairFixedLeftAveragingPacket a n))]

/-- All fixed-left prime families converge to one common vertical source class. -/
theorem tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_fixedLeftAveragingPacket
    (a : ℕ) :
    Tendsto (fun n => deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerBigWittCrossPairFixedLeftAveragingPacket a n))
      atTop (nhds deningerBigWittCrossPairOneLegGraphSingularVector) := by
  have hpair : Tendsto
      (fun n =>
        (deningerBigWittCrossPairFinitePacketAdmission
            (deningerBigWittCrossPairFixedLeftAveragingPacket a n),
          deningerBigWittCrossPairAlgebraicOneLegTrace
            (deningerBigWittCrossPairFixedLeftAveragingPacket a n)))
      atTop (nhds ((0 : DeningerCalderonWittCrossPrimePacketHilbert), (1 : ℂ))) := by
    simpa only [nhds_prod_eq] using
      (tendsto_deningerBigWittCrossPairFinitePacketAdmission_fixedLeftAveragingPacket a).prodMk
        (by simpa only
          [deningerBigWittCrossPairAlgebraicOneLegTrace_fixedLeftAveragingPacket]
          using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1)))
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ
    DeningerCalderonWittCrossPrimePacketHilbert ℂ).symm.continuous.tendsto _).comp hpair

/-- Literal inverse-Gamma reporter on finite ordered-prime source packets. -/
def deningerBigWittCrossPairFiniteInverseGammaReporter
    (t : ℝ) :
    (DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun i => LinearMap.toSpanSingleton ℂ ℂ
    (primeGammaLocalInverseOrientedGhost t i.1.1 : ℂ)

@[simp] theorem deningerBigWittCrossPairFiniteInverseGammaReporter_single
    (t : ℝ) (i : DeningerCalderonWittCrossPrimePacketIndex) (z : ℂ) :
    deningerBigWittCrossPairFiniteInverseGammaReporter t (Finsupp.single i z) =
      (primeGammaLocalInverseOrientedGhost t i.1.1 : ℂ) * z := by
  classical
  simp [deningerBigWittCrossPairFiniteInverseGammaReporter, Finsupp.lsum_apply,
    LinearMap.toSpanSingleton, mul_comm]

/-- A fixed-left average retains exactly its left-prime inverse-Gamma coefficient. -/
@[simp] theorem deningerBigWittCrossPairFiniteInverseGammaReporter_fixedLeftAveragingPacket
    (t : ℝ) (a n : ℕ) :
    deningerBigWittCrossPairFiniteInverseGammaReporter t
        (deningerBigWittCrossPairFixedLeftAveragingPacket a n) =
      (primeGammaLocalInverseOrientedGhost t
        (deningerBigWittCrossPairNthPrime a) : ℂ) := by
  classical
  rw [deningerBigWittCrossPairFixedLeftAveragingPacket, map_sum]
  have hsum :
      (∑ i ∈ deningerBigWittCrossPairFixedLeftPacketPrefix a n,
        deningerBigWittCrossPairFiniteInverseGammaReporter t
          (Finsupp.single i (((n + 1 : ℝ) : ℂ)⁻¹))) =
      ∑ _i ∈ deningerBigWittCrossPairFixedLeftPacketPrefix a n,
        (primeGammaLocalInverseOrientedGhost t
          (deningerBigWittCrossPairNthPrime a) : ℂ) *
            (((n + 1 : ℝ) : ℂ)⁻¹) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [deningerBigWittCrossPairFiniteInverseGammaReporter_single,
      deningerBigWittCrossPairFixedLeftPacketPrefix_left hi]
  rw [hsum, Finset.sum_const, nsmul_eq_mul,
    deningerBigWittCrossPairFixedLeftPacketPrefix_card]
  have hne : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : n + 1 ≠ 0)
  have hcast : ((n + 1 : ℕ) : ℂ) = (((n + 1 : ℝ) : ℂ)) := by
    norm_cast
  have hne' : (((n + 1 : ℝ) : ℂ)) ≠ 0 := by
    intro hz
    exact hne (hcast.trans hz)
  rw [hcast]
  calc
    (((n + 1 : ℝ) : ℂ)) *
        ((primeGammaLocalInverseOrientedGhost t
          (deningerBigWittCrossPairNthPrime a) : ℂ) *
            (((n + 1 : ℝ) : ℂ))⁻¹) =
      (primeGammaLocalInverseOrientedGhost t
        (deningerBigWittCrossPairNthPrime a) : ℂ) *
          ((((n + 1 : ℝ) : ℂ)) * (((n + 1 : ℝ) : ℂ))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hne', mul_one]

/-- Source-selected Gamma descent means that the literal finite coefficient reporter extends
continuously to the common singular Big-Witt source graph. -/
def DeningerBigWittInverseGammaReporterDescends (t : ℝ) : Prop :=
  ∃ reporter : DeningerBigWittCrossPairSingularOneLegGraph →L[ℂ] ℂ,
    ∀ c : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ,
      reporter (deningerBigWittCrossPairFiniteOneLegGraphAdmission c) =
        deningerBigWittCrossPairFiniteInverseGammaReporter t c

theorem deningerBigWittInverseGammaReporterDescends_of_eq_zero
    {t : ℝ} (ht : t = 0) :
    DeningerBigWittInverseGammaReporterDescends t := by
  subst t
  refine ⟨deningerBigWittCrossPairOneLegGraphTrace, ?_⟩
  intro c
  rw [deningerBigWittCrossPairOneLegGraphTrace_finiteAdmission]
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single i z =>
      rw [deningerBigWittCrossPairAlgebraicOneLegTrace_single,
        deningerBigWittCrossPairFiniteInverseGammaReporter_single]
      simp [primeGammaLocalInverseOrientedGhost]

theorem deningerBigWittInverseGammaReporterDescends_eq_zero
    {t : ℝ} (h : DeningerBigWittInverseGammaReporterDescends t) :
    t = 0 := by
  rcases h with ⟨reporter, hreporter⟩
  have hlimit (a : ℕ) :
      (primeGammaLocalInverseOrientedGhost t
          (deningerBigWittCrossPairNthPrime a) : ℂ) =
        reporter deningerBigWittCrossPairOneLegGraphSingularVector := by
    have htend := reporter.continuous.tendsto
      deningerBigWittCrossPairOneLegGraphSingularVector
    have hsource :=
      tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_fixedLeftAveragingPacket a
    have hreported : Tendsto
        (fun n => reporter (deningerBigWittCrossPairFiniteOneLegGraphAdmission
          (deningerBigWittCrossPairFixedLeftAveragingPacket a n)))
        atTop (nhds (reporter deningerBigWittCrossPairOneLegGraphSingularVector)) :=
      htend.comp hsource
    have hconstant : Tendsto
        (fun _n : ℕ => (primeGammaLocalInverseOrientedGhost t
          (deningerBigWittCrossPairNthPrime a) : ℂ))
        atTop (nhds (primeGammaLocalInverseOrientedGhost t
          (deningerBigWittCrossPairNthPrime a) : ℂ)) := tendsto_const_nhds
    have hreported' : Tendsto
        (fun _n : ℕ => (primeGammaLocalInverseOrientedGhost t
          (deningerBigWittCrossPairNthPrime a) : ℂ))
        atTop (nhds (reporter deningerBigWittCrossPairOneLegGraphSingularVector)) := by
      convert hreported using 1
      funext n
      rw [hreporter,
        deningerBigWittCrossPairFiniteInverseGammaReporter_fixedLeftAveragingPacket]
    exact tendsto_nhds_unique hconstant hreported'
  have hpowersComplex :
      (primeGammaLocalInverseOrientedGhost t
          (deningerBigWittCrossPairNthPrime 0) : ℂ) =
        (primeGammaLocalInverseOrientedGhost t
          (deningerBigWittCrossPairNthPrime 1) : ℂ) :=
    (hlimit 0).trans (hlimit 1).symm
  have hpowers :
      primeGammaLocalInverseOrientedGhost t
          (deningerBigWittCrossPairNthPrime 0) =
        primeGammaLocalInverseOrientedGhost t
          (deningerBigWittCrossPairNthPrime 1) := by
    exact_mod_cast hpowersComplex
  have hp0 : 0 < (deningerBigWittCrossPairNthPrime 0 : ℝ) := by
    exact_mod_cast (deningerBigWittCrossPairNthPrime 0).2.pos
  have hp1 : 0 < (deningerBigWittCrossPairNthPrime 1 : ℝ) := by
    exact_mod_cast (deningerBigWittCrossPairNthPrime 1).2.pos
  change (deningerBigWittCrossPairNthPrime 0 : ℝ) ^ (-t) =
    (deningerBigWittCrossPairNthPrime 1 : ℝ) ^ (-t) at hpowers
  have hlogs := congrArg Real.log hpowers
  rw [Real.log_rpow hp0, Real.log_rpow hp1] at hlogs
  have hprimeLt : (deningerBigWittCrossPairNthPrime 0 : ℝ) <
      (deningerBigWittCrossPairNthPrime 1 : ℝ) := by
    exact_mod_cast deningerBigWittCrossPairNthPrime_val_strictMono (by omega)
  have hlogLt : Real.log (deningerBigWittCrossPairNthPrime 0 : ℝ) <
      Real.log (deningerBigWittCrossPairNthPrime 1 : ℝ) :=
    Real.strictMonoOn_log hp0 hp1 hprimeLt
  have hdiff : Real.log (deningerBigWittCrossPairNthPrime 0 : ℝ) -
      Real.log (deningerBigWittCrossPairNthPrime 1 : ℝ) ≠ 0 :=
    sub_ne_zero.mpr hlogLt.ne
  have hmul : (-t) *
      (Real.log (deningerBigWittCrossPairNthPrime 0 : ℝ) -
        Real.log (deningerBigWittCrossPairNthPrime 1 : ℝ)) = 0 := by
    linear_combination hlogs
  have ht : -t = 0 := (mul_eq_zero.mp hmul).resolve_right hdiff
  linarith

/-- Exact classification: common-source continuous Gamma reporter descent is neutral grade. -/
theorem deningerBigWittInverseGammaReporterDescends_iff (t : ℝ) :
    DeningerBigWittInverseGammaReporterDescends t ↔ t = 0 :=
  ⟨deningerBigWittInverseGammaReporterDescends_eq_zero,
    deningerBigWittInverseGammaReporterDescends_of_eq_zero⟩

/-- Pointwise common-source reporter target on one retained Xi divisor. -/
def FrankensteinXiBigWittInverseGammaReporterDescendsAt
    (rho : XiDivisorSupport) : Prop :=
  DeningerBigWittInverseGammaReporterDescends
    (primeDepthBVWoldXiCenteredRate rho)

theorem frankensteinXiBigWittInverseGammaReporterDescendsAt_iff_line
    (rho : XiDivisorSupport) :
    FrankensteinXiBigWittInverseGammaReporterDescendsAt rho ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [FrankensteinXiBigWittInverseGammaReporterDescendsAt,
    deningerBigWittInverseGammaReporterDescends_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- The source-graph reporter constructs the earlier coefficient-faithful natural reporter. -/
theorem frankensteinXiBigWittInverseGammaReporterDescendsAt_constructs_naturalReporter
    (rho : XiDivisorSupport)
    (h : FrankensteinXiBigWittInverseGammaReporterDescendsAt rho) :
    Nonempty (PrimeGammaTwoThreeSourceNaturalReporter
      (primeDepthBVWoldXiCenteredRate rho)) := by
  have ht : primeDepthBVWoldXiCenteredRate rho = 0 :=
    (deningerBigWittInverseGammaReporterDescends_iff _).1 h
  apply (primeGammaTwoThreeSourceNaturalReporter_nonempty_iff _).2
  rw [primeGammaTwoThreeSourceNaturalInverseGhost_iff]
  exact ht

def EveryFrankensteinXiBigWittInverseGammaReporterDescends : Prop :=
  ∀ rho : XiDivisorSupport,
    FrankensteinXiBigWittInverseGammaReporterDescendsAt rho

theorem everyFrankensteinXiBigWittInverseGammaReporterDescends_iff_riemannHypothesis :
    EveryFrankensteinXiBigWittInverseGammaReporterDescends ↔ RiemannHypothesis := by
  rw [← everyFrankensteinSourceSelectedGammaWardSharedGhostDescends_iff_riemannHypothesis]
  unfold EveryFrankensteinXiBigWittInverseGammaReporterDescends
    EveryFrankensteinSourceSelectedGammaWardSharedGhostDescends
  apply forall_congr'
  intro rho
  exact (frankensteinXiBigWittInverseGammaReporterDescendsAt_iff_line rho).trans
    (frankensteinSourceSelectedGammaWardSharedGhostDescendsAt_iff rho).symm

end

end RHTower
