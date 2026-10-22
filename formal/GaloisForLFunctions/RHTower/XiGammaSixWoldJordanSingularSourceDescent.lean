import GaloisForLFunctions.RHTower.XiGammaSixWoldJordanHessianDomination
import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittCrossPrimeHarmonicSingularGraphSource

/-!
# Literal Wold--Jordan square on genuine all-left Big-Witt source rows

The existing harmonic singular-source construction used only the row with left prime two.  This
module constructs corresponding raw Big-Witt horizon row for every left prime.  Each row has
divergent algebraic trace and bounded ambient `ℓ²` norm; trace normalization therefore makes all
rows converge to same nonzero vertical vector in singular one-leg graph.

The literal nonlinear Wold--Jordan energy reporter reads normalized row at left prime `p` as
exactly `A(q) / p`.  Consequently even weakest continuous descent agreeing only on these genuine
source rows exists precisely when `A(q) = 0`, hence precisely on critical line.  Globally this
actual-source descent is equivalent to RH.

All constructions and equivalences are unconditional.  Module does not assert missing descent;
it identifies its minimal coefficient-faithful form and replaces arbitrary averaging packets by
genuine Big-Witt source packets.
-/

open Complex Filter Function Set Topology
open scoped BigOperators ENNReal

namespace RHTower.HedenmalmThetaSource

noncomputable section

noncomputable local instance instDecidableEqWoldJordanSingularSourceIndex :
    DecidableEq DeningerCalderonWittCrossPrimePacketIndex :=
  Classical.decEq _

/-- Ordered row of genuine Big-Witt atoms with one fixed left prime. -/
def deningerBigWittWoldFixedLeftRightEdgeEmbedding
    (a : ℕ) : ℕ ↪ DeningerCalderonWittCrossPrimePacketIndex where
  toFun n :=
    ⟨(nthPrimeSubtype a, nthPrimeSubtype (a + n + 1)), by
      intro h
      have hi : a = a + n + 1 := nthPrimeSubtype_injective h
      omega⟩
  inj' := by
    intro m n h
    have hr : nthPrimeSubtype (a + m + 1) = nthPrimeSubtype (a + n + 1) :=
      congrArg (fun i : DeningerCalderonWittCrossPrimePacketIndex => i.1.2) h
    have hi : a + m + 1 = a + n + 1 := nthPrimeSubtype_injective hr
    omega

/-- Literal positive Big-Witt coefficient on fixed-left row. -/
def deningerBigWittWoldFixedLeftRightEdgeWeight (a n : ℕ) : ℝ :=
  ((nthPrimeSubtype a : ℝ) * (nthPrimeSubtype (a + n + 1) : ℝ))⁻¹

theorem deningerBigWittWoldFixedLeftRightEdgeWeight_pos (a n : ℕ) :
    0 < deningerBigWittWoldFixedLeftRightEdgeWeight a n := by
  rw [deningerBigWittWoldFixedLeftRightEdgeWeight]
  exact inv_pos.mpr
    (mul_pos (nthPrimeSubtype_pos a) (nthPrimeSubtype_pos (a + n + 1)))

theorem deningerBigWittCrossPrimePacketRawCoefficient_woldFixedLeftRightEdge
    (a n : ℕ) :
    deningerBigWittCrossPrimePacketRawCoefficient
        (deningerBigWittWoldFixedLeftRightEdgeEmbedding a n) =
      (deningerBigWittWoldFixedLeftRightEdgeWeight a n : ℂ) := by
  simp [deningerBigWittCrossPrimePacketRawCoefficient,
    deningerBigWittCrossPrimeAtom, deningerBigWittPrimeFace,
    deningerBigWittWoldFixedLeftRightEdgeWeight,
    deningerBigWittWoldFixedLeftRightEdgeEmbedding, mul_comm]

/-- Every fixed-left raw Big-Witt row has divergent algebraic trace. -/
theorem not_summable_deningerBigWittWoldFixedLeftRightEdgeWeight (a : ℕ) :
    ¬ Summable (deningerBigWittWoldFixedLeftRightEdgeWeight a) := by
  intro h
  have hconst : (nthPrimeSubtype a : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (nthPrimeSubtype_pos a))
  have htail : Summable
      (fun n : ℕ => (nthPrimeSubtype (a + n + 1) : ℝ)⁻¹) := by
    apply (summable_mul_left_iff hconst).mp
    apply h.congr
    intro n
    rw [deningerBigWittWoldFixedLeftRightEdgeWeight, mul_inv]
  have htail' : Summable
      (fun n : ℕ => (nthPrimeSubtype (n + (a + 1)) : ℝ)⁻¹) := by
    apply htail.congr
    intro n
    have hi : n + (a + 1) = a + n + 1 := by omega
    rw [hi]
  have hall : Summable (fun n : ℕ => (nthPrimeSubtype n : ℝ)⁻¹) :=
    (summable_nat_add_iff (a + 1)).mp htail'
  apply not_summable_nthPrime_reciprocal
  simpa [one_div] using hall

def deningerBigWittWoldFixedLeftRightEdgeMass (a n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, deningerBigWittWoldFixedLeftRightEdgeWeight a k

theorem tendsto_deningerBigWittWoldFixedLeftRightEdgeMass_atTop (a : ℕ) :
    Tendsto (deningerBigWittWoldFixedLeftRightEdgeMass a) atTop atTop := by
  change Tendsto
    (fun n : ℕ => ∑ k ∈ Finset.range n,
      deningerBigWittWoldFixedLeftRightEdgeWeight a k) atTop atTop
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => (deningerBigWittWoldFixedLeftRightEdgeWeight_pos a n).le)).mp
      (not_summable_deningerBigWittWoldFixedLeftRightEdgeWeight a)

theorem deningerBigWittWoldFixedLeftRightEdgeMass_pos (a n : ℕ) :
    0 < deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1) := by
  rw [deningerBigWittWoldFixedLeftRightEdgeMass, Finset.sum_range_succ]
  exact add_pos_of_nonneg_of_pos
    (Finset.sum_nonneg fun i _ =>
      (deningerBigWittWoldFixedLeftRightEdgeWeight_pos a i).le)
    (deningerBigWittWoldFixedLeftRightEdgeWeight_pos a n)

def deningerBigWittWoldFixedLeftRightEdgePrefix
    (a n : ℕ) : Finset DeningerCalderonWittCrossPrimePacketIndex :=
  (Finset.range n).map (deningerBigWittWoldFixedLeftRightEdgeEmbedding a)

theorem deningerBigWittWoldFixedLeftRightEdgePrefix_left
    {a n : ℕ} {i : DeningerCalderonWittCrossPrimePacketIndex}
    (hi : i ∈ deningerBigWittWoldFixedLeftRightEdgePrefix a n) :
    i.1.1 = nthPrimeSubtype a := by
  rw [deningerBigWittWoldFixedLeftRightEdgePrefix, Finset.mem_map] at hi
  obtain ⟨k, _hk, rfl⟩ := hi
  rfl

/-- Finite truncation of genuine raw Big-Witt horizon on fixed-left row. -/
def deningerBigWittWoldFixedLeftRightEdgeRawPacket
    (a n : ℕ) : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  (deningerBigWittWoldFixedLeftRightEdgePrefix a n).sum fun i =>
    Finsupp.single i (deningerBigWittCrossPrimePacketRawCoefficient i)

@[simp] theorem deningerBigWittWoldFixedLeftRightEdgeRawPacket_apply
    (a n : ℕ) (j : DeningerCalderonWittCrossPrimePacketIndex) :
    deningerBigWittWoldFixedLeftRightEdgeRawPacket a n j =
      if j ∈ deningerBigWittWoldFixedLeftRightEdgePrefix a n then
        deningerBigWittCrossPrimePacketRawCoefficient j else 0 := by
  classical
  simp [deningerBigWittWoldFixedLeftRightEdgeRawPacket, Finsupp.single_apply]

theorem deningerBigWittCrossPairAlgebraicOneLegTrace_woldFixedLeftRightEdgeRawPacket
    (a n : ℕ) :
    deningerBigWittCrossPairAlgebraicOneLegTrace
        (deningerBigWittWoldFixedLeftRightEdgeRawPacket a n) =
      (deningerBigWittWoldFixedLeftRightEdgeMass a n : ℂ) := by
  classical
  rw [deningerBigWittWoldFixedLeftRightEdgeRawPacket, map_sum]
  simp only [deningerBigWittCrossPairAlgebraicOneLegTrace_single]
  rw [deningerBigWittWoldFixedLeftRightEdgePrefix, Finset.sum_map,
    deningerBigWittWoldFixedLeftRightEdgeMass]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  exact deningerBigWittCrossPrimePacketRawCoefficient_woldFixedLeftRightEdge a k

theorem norm_deningerBigWittCrossPairFinitePacketAdmission_woldFixedLeftRightEdgeRawPacket_le
    (a n : ℕ) :
    ‖deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittWoldFixedLeftRightEdgeRawPacket a n)‖ ≤
      ‖deningerBigWittCrossPrimePacketRawHorizon‖ := by
  apply lp.norm_mono (by norm_num)
  intro j
  rw [show (deningerBigWittCrossPairFinitePacketAdmission
      (deningerBigWittWoldFixedLeftRightEdgeRawPacket a n)) j =
        deningerBigWittWoldFixedLeftRightEdgeRawPacket a n j by
      exact deningerBigWittCrossPairFinitePacketAdmissionToFun_apply _ _,
    deningerBigWittWoldFixedLeftRightEdgeRawPacket_apply,
    deningerBigWittCrossPrimePacketRawHorizon_apply]
  by_cases hj : j ∈ deningerBigWittWoldFixedLeftRightEdgePrefix a n <;> simp [hj]

/-- Actual fixed-left row normalized by its nonzero algebraic trace. -/
def deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket
    (a n : ℕ) : DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ :=
  ((deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1) : ℂ)⁻¹) •
    deningerBigWittWoldFixedLeftRightEdgeRawPacket a (n + 1)

@[simp] theorem
    deningerBigWittCrossPairAlgebraicOneLegTrace_woldFixedLeftRightEdgeNormalizedPacket
    (a n : ℕ) :
    deningerBigWittCrossPairAlgebraicOneLegTrace
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n) = 1 := by
  rw [deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket, map_smul,
    deningerBigWittCrossPairAlgebraicOneLegTrace_woldFixedLeftRightEdgeRawPacket]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (deningerBigWittWoldFixedLeftRightEdgeMass_pos a n)))

theorem norm_deningerBigWittCrossPairFinitePacketAdmission_woldFixedLeftRightEdgeNormalizedPacket_le
    (a n : ℕ) :
    ‖deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)‖ ≤
      (deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1))⁻¹ *
        ‖deningerBigWittCrossPrimePacketRawHorizon‖ := by
  rw [deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket, map_smul, norm_smul,
    norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (deningerBigWittWoldFixedLeftRightEdgeMass_pos a n)]
  exact mul_le_mul_of_nonneg_left
    (norm_deningerBigWittCrossPairFinitePacketAdmission_woldFixedLeftRightEdgeRawPacket_le
      a (n + 1))
    (inv_nonneg.mpr (deningerBigWittWoldFixedLeftRightEdgeMass_pos a n).le)

theorem tendsto_deningerBigWittCrossPairFinitePacketAdmission_woldFixedLeftRightEdgeNormalizedPacket
    (a : ℕ) :
    Tendsto (fun n => deningerBigWittCrossPairFinitePacketAdmission
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n))
      atTop (nhds 0) := by
  have hmass : Tendsto
      (fun n => deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1)) atTop atTop :=
    (tendsto_deningerBigWittWoldFixedLeftRightEdgeMass_atTop a).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hmaj : Tendsto
      (fun n => (deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1))⁻¹ *
        ‖deningerBigWittCrossPrimePacketRawHorizon‖) atTop (nhds 0) := by
    simpa [mul_comm] using
      hmass.inv_tendsto_atTop.const_mul ‖deningerBigWittCrossPrimePacketRawHorizon‖
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hmaj
  exact Eventually.of_forall
    (norm_deningerBigWittCrossPairFinitePacketAdmission_woldFixedLeftRightEdgeNormalizedPacket_le a)

/-- Every genuine fixed-left raw row converges to same vertical source generator. -/
theorem tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_woldFixedLeftRightEdgeNormalizedPacket
    (a : ℕ) :
    Tendsto (fun n => deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n))
      atTop (nhds deningerBigWittCrossPairOneLegGraphSingularVector) := by
  have hpair : Tendsto
      (fun n =>
        (deningerBigWittCrossPairFinitePacketAdmission
            (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n),
          deningerBigWittCrossPairAlgebraicOneLegTrace
            (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)))
      atTop (nhds ((0 : DeningerCalderonWittCrossPrimePacketHilbert), (1 : ℂ))) := by
    simpa only [nhds_prod_eq] using
      (tendsto_deningerBigWittCrossPairFinitePacketAdmission_woldFixedLeftRightEdgeNormalizedPacket a).prodMk
        (by simpa only
          [deningerBigWittCrossPairAlgebraicOneLegTrace_woldFixedLeftRightEdgeNormalizedPacket]
          using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1)))
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ
    DeningerCalderonWittCrossPrimePacketHilbert ℂ).symm.continuous.tendsto _).comp hpair

/-- Literal nonlinear Wold--Jordan energy reporter on finite ordered-prime source packets. -/
def deningerBigWittCrossPairFiniteWoldJordanEnergyReporter
    (q : XiZeroCopy) :
    (DeningerCalderonWittCrossPrimePacketIndex →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun i => LinearMap.toSpanSingleton ℂ ℂ
    ((thetaGammaSixWoldHorizontalCarrier i.1.1 q ^ 2 : ℝ) : ℂ)

@[simp] theorem deningerBigWittCrossPairFiniteWoldJordanEnergyReporter_single
    (q : XiZeroCopy) (i : DeningerCalderonWittCrossPrimePacketIndex) (z : ℂ) :
    deningerBigWittCrossPairFiniteWoldJordanEnergyReporter q (Finsupp.single i z) =
      ((thetaGammaSixWoldHorizontalCarrier i.1.1 q ^ 2 : ℝ) : ℂ) * z := by
  classical
  simp [deningerBigWittCrossPairFiniteWoldJordanEnergyReporter, Finsupp.lsum_apply,
    LinearMap.toSpanSingleton, mul_comm]

/-- Trace-normalized genuine Big-Witt rows retain literal Wold--Jordan energy at left prime. -/
@[simp] theorem
    deningerBigWittCrossPairFiniteWoldJordanEnergyReporter_woldFixedLeftRightEdgeNormalizedPacket
    (q : XiZeroCopy) (a n : ℕ) :
    deningerBigWittCrossPairFiniteWoldJordanEnergyReporter q
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n) =
      ((thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype a) q ^ 2 : ℝ) : ℂ) := by
  classical
  let M := deningerBigWittWoldFixedLeftRightEdgeMass a (n + 1)
  have hM : (M : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (deningerBigWittWoldFixedLeftRightEdgeMass_pos a n))
  have hraw :
      deningerBigWittCrossPairFiniteWoldJordanEnergyReporter q
          (deningerBigWittWoldFixedLeftRightEdgeRawPacket a (n + 1)) =
        ((thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype a) q ^ 2 : ℝ) : ℂ) *
          (M : ℂ) := by
    rw [deningerBigWittWoldFixedLeftRightEdgeRawPacket, map_sum,
      deningerBigWittWoldFixedLeftRightEdgePrefix, Finset.sum_map]
    have hsum :
        (∑ k ∈ Finset.range (n + 1),
          deningerBigWittCrossPairFiniteWoldJordanEnergyReporter q
            (Finsupp.single (deningerBigWittWoldFixedLeftRightEdgeEmbedding a k)
              (deningerBigWittCrossPrimePacketRawCoefficient
                (deningerBigWittWoldFixedLeftRightEdgeEmbedding a k)))) =
        ∑ k ∈ Finset.range (n + 1),
          ((thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype a) q ^ 2 : ℝ) : ℂ) *
            (deningerBigWittWoldFixedLeftRightEdgeWeight a k : ℂ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [deningerBigWittCrossPairFiniteWoldJordanEnergyReporter_single,
        deningerBigWittCrossPrimePacketRawCoefficient_woldFixedLeftRightEdge]
      rfl
    rw [hsum, ← Finset.mul_sum]
    dsimp only [M]
    rw [deningerBigWittWoldFixedLeftRightEdgeMass]
    push_cast
    rfl
  rw [deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket, map_smul, hraw]
  change (M : ℂ)⁻¹ *
      (((thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype a) q ^ 2 : ℝ) : ℂ) *
        (M : ℂ)) = _
  field_simp

/-- Source-selected nonlinear descent asks only for compatibility on genuine raw Big-Witt rows,
not arbitrary finite-support packets. All fixed-left rows meet one completed vertical class. -/
def DeningerBigWittWoldJordanActualSourceEnergyDescends (q : XiZeroCopy) : Prop :=
  ∃ reporter : DeningerBigWittCrossPairSingularOneLegGraph →L[ℂ] ℂ,
    ∀ a n : ℕ,
      reporter (deningerBigWittCrossPairFiniteOneLegGraphAdmission
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)) =
      deningerBigWittCrossPairFiniteWoldJordanEnergyReporter q
        (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)

theorem deningerBigWittWoldJordanActualSourceEnergyDescends_of_rate_eq_zero
    (q : XiZeroCopy) (ht : primeDepthBVWoldXiCenteredRate q.1 = 0) :
    DeningerBigWittWoldJordanActualSourceEnergyDescends q := by
  refine ⟨0, ?_⟩
  intro a n
  rw [deningerBigWittCrossPairFiniteWoldJordanEnergyReporter_woldFixedLeftRightEdgeNormalizedPacket]
  have hcarrier : thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype a) q = 0 :=
    (thetaGammaSixWoldHorizontalCarrier_eq_zero_iff (nthPrimeSubtype a) q).2 ht
  simp [hcarrier]

theorem deningerBigWittWoldJordanActualSourceEnergyDescends_rate_eq_zero
    (q : XiZeroCopy) (h : DeningerBigWittWoldJordanActualSourceEnergyDescends q) :
    primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  rcases h with ⟨reporter, hreporter⟩
  have hlimit (a : ℕ) :
      ((thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype a) q ^ 2 : ℝ) : ℂ) =
        reporter deningerBigWittCrossPairOneLegGraphSingularVector := by
    have hreported : Tendsto
        (fun n => reporter (deningerBigWittCrossPairFiniteOneLegGraphAdmission
          (deningerBigWittWoldFixedLeftRightEdgeNormalizedPacket a n)))
        atTop (nhds (reporter deningerBigWittCrossPairOneLegGraphSingularVector)) :=
      reporter.continuous.tendsto
        deningerBigWittCrossPairOneLegGraphSingularVector |>.comp
          (tendsto_deningerBigWittCrossPairFiniteOneLegGraphAdmission_woldFixedLeftRightEdgeNormalizedPacket a)
    have hconstant : Tendsto
        (fun _n : ℕ =>
          ((thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype a) q ^ 2 : ℝ) : ℂ))
        atTop (nhds
          ((thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype a) q ^ 2 : ℝ) : ℂ)) :=
      tendsto_const_nhds
    have hreported' : Tendsto
        (fun _n : ℕ =>
          ((thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype a) q ^ 2 : ℝ) : ℂ))
        atTop (nhds (reporter deningerBigWittCrossPairOneLegGraphSingularVector)) := by
      convert hreported using 1
      funext n
      rw [hreporter,
        deningerBigWittCrossPairFiniteWoldJordanEnergyReporter_woldFixedLeftRightEdgeNormalizedPacket]
    exact tendsto_nhds_unique hconstant hreported'
  have hsquaresComplex :
      ((thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype 0) q ^ 2 : ℝ) : ℂ) =
      ((thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype 1) q ^ 2 : ℝ) : ℂ) :=
    (hlimit 0).trans (hlimit 1).symm
  have hsquares :
      thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype 0) q ^ 2 =
        thetaGammaSixWoldHorizontalCarrier (nthPrimeSubtype 1) q ^ 2 := by
    exact_mod_cast hsquaresComplex
  rw [thetaGammaSixWoldHorizontalCarrier_sq_eq_weight_div,
    thetaGammaSixWoldHorizontalCarrier_sq_eq_weight_div] at hsquares
  have hp0 : 0 < (nthPrimeSubtype 0 : ℝ) := nthPrimeSubtype_pos 0
  have hp1 : 0 < (nthPrimeSubtype 1 : ℝ) := nthPrimeSubtype_pos 1
  have hprimeLt : (nthPrimeSubtype 0 : ℝ) < (nthPrimeSubtype 1 : ℝ) := by
    exact_mod_cast nthPrimeSubtype_strictMono (by omega)
  have hweight : xiGammaSixWoldJordanHarmonicWeight q = 0 := by
    have hp0ne := ne_of_gt hp0
    have hp1ne := ne_of_gt hp1
    field_simp [hp0ne, hp1ne] at hsquares
    nlinarith [xiGammaSixWoldJordanHarmonicWeight_nonneg q]
  exact (xiGammaSixWoldJordanHarmonicWeight_eq_zero_iff q).1 hweight

theorem deningerBigWittWoldJordanActualSourceEnergyDescends_iff
    (q : XiZeroCopy) :
    DeningerBigWittWoldJordanActualSourceEnergyDescends q ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 :=
  ⟨deningerBigWittWoldJordanActualSourceEnergyDescends_rate_eq_zero q,
    deningerBigWittWoldJordanActualSourceEnergyDescends_of_rate_eq_zero q⟩

theorem deningerBigWittWoldJordanActualSourceEnergyDescends_iff_line
    (q : XiZeroCopy) :
    DeningerBigWittWoldJordanActualSourceEnergyDescends q ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [deningerBigWittWoldJordanActualSourceEnergyDescends_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

theorem everyDeningerBigWittWoldJordanActualSourceEnergyDescends_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, DeningerBigWittWoldJordanActualSourceEnergyDescends q) ↔
      RiemannHypothesis := by
  rw [← all_summable_sq_thetaGammaSixWoldHorizontalCarrier_iff_riemannHypothesis]
  exact forall_congr' fun q =>
    (deningerBigWittWoldJordanActualSourceEnergyDescends_iff q).trans
      (summable_sq_thetaGammaSixWoldHorizontalCarrier_iff q).symm

end

end RHTower.HedenmalmThetaSource
