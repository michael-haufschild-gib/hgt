import GaloisForLFunctions.HTGeometry.SpectralClusterTransfer
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Exact analytic birth valuation of observer-time sectors

A Big-O onset bound does not identify the actual order at which a spectral
sector appears: selection rules may delay it or kill it. This file supplies
the exact invariant.

Every scalar ray through an analytic interaction-packet response has a unique
Taylor series. If the response is an active germ, its first nonzero
coefficient defines an intrinsic birth depth. The response is exactly the
corresponding power of the coupling times a nonvanishing analytic unit.
Moreover, Boolean interaction selection proves that this exact depth cannot
be smaller than the number of indispensable control labels.
-/

open Filter Topology Asymptotics
open scoped BigOperators
open IncidenceAlgebra

namespace GaloisForLFunctions.HTGeometry

/-- Continuous linear parametrization of the scalar ray through `z`. -/
noncomputable def scalarRayCLM
    {E : Type*} [Fintype E] (z : E → ℂ) :
    ℂ →L[ℂ] (E → ℂ) :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) z

@[simp]
theorem scalarRayCLM_apply
    {E : Type*} [Fintype E] (z : E → ℂ) (g : ℂ) :
    scalarRayCLM z g = g • z := by
  rfl

/-- Scalar Taylor series of the Boolean interaction packet on the ray
`g ↦ g • z`. -/
noncomputable def packetRaySeries
    {E : Type*} [Fintype E] [DecidableEq E]
    (series : FormalMultilinearSeries ℂ (E → ℂ) ℂ)
    (z : E → ℂ) (packet : Finset E) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  ∑ active ∈ Finset.Iic packet,
    (mu ℂ active packet) •
      series.compContinuousLinearMap
        (scalarRayCLM (restrictInteractionPacket active z))

/-- The explicit packet-ray series represents the scalar packet response. -/
theorem hasFPowerSeriesAt_packetRaySeries
    {E : Type*} [Fintype E] [DecidableEq E]
    {f : (E → ℂ) → ℂ}
    {series : FormalMultilinearSeries ℂ (E → ℂ) ℂ}
    (hf : HasFPowerSeriesAt f series 0)
    (z : E → ℂ) (packet : Finset E) :
    HasFPowerSeriesAt
      (fun g : ℂ =>
        posetMobiusProbe (R := ℂ) packet
          (fun active =>
            f (g • restrictInteractionPacket active z)))
      (packetRaySeries series z packet) 0 := by
  classical
  unfold packetRaySeries posetMobiusProbe
  induction Finset.Iic packet using Finset.induction_on with
  | empty =>
      simpa using
        (hasFPowerSeriesAt_const
          (𝕜 := ℂ) (c := (0 : ℂ)) (e := (0 : ℂ)))
  | @insert active states hactive ih =>
      have hcomp :
          HasFPowerSeriesAt
            (fun g : ℂ =>
              f (g • restrictInteractionPacket active z))
            (series.compContinuousLinearMap
              (scalarRayCLM (restrictInteractionPacket active z))) 0 := by
        have hf' :
            HasFPowerSeriesAt f series
              (scalarRayCLM (restrictInteractionPacket active z) 0) := by
          simpa using hf
        simpa [Function.comp_def] using
          (HasFPowerSeriesAt.compContinuousLinearMap
            (u := scalarRayCLM (restrictInteractionPacket active z))
            (x := (0 : ℂ)) hf')
      have hterm :=
        hcomp.const_smul (c := mu ℂ active packet)
      have hsmulFun :
          ((mu ℂ active packet) •
              (fun g : ℂ =>
                f (g • restrictInteractionPacket active z))) =
            (fun g : ℂ =>
              mu ℂ active packet *
                f (g • restrictInteractionPacket active z)) := by
        funext g
        change
          mu ℂ active packet •
              f (g • restrictInteractionPacket active z) =
            mu ℂ active packet *
              f (g • restrictInteractionPacket active z)
        exact smul_eq_mul _ _
      rw [hsmulFun] at hterm
      rw [Finset.sum_insert hactive]
      convert hterm.add ih using 1
      funext g
      simp [Finset.sum_insert hactive]

/-- The scalar coefficient of the packet-ray series is exactly the
multivariate interaction Möbius coefficient evaluated on the ray. -/
theorem packetRaySeries_coeff_eq_interactionMobiusTaylorCoefficient
    {E : Type*} [Fintype E] [DecidableEq E]
    (series : FormalMultilinearSeries ℂ (E → ℂ) ℂ)
    (z : E → ℂ) (packet : Finset E) (n : ℕ) :
    (packetRaySeries series z packet).coeff n =
      interactionMobiusTaylorCoefficient series n z packet := by
  classical
  have hsum :
      ∀ states : Finset (Finset E),
        (∑ active ∈ states,
          (mu ℂ active packet) •
            series.compContinuousLinearMap
              (scalarRayCLM (restrictInteractionPacket active z))).coeff n =
          ∑ active ∈ states,
            mu ℂ active packet *
              series n (fun _ => restrictInteractionPacket active z) := by
    intro states
    induction states using Finset.induction_on with
    | empty =>
        unfold FormalMultilinearSeries.coeff
        rfl
    | @insert active states hactive ih =>
        rw [Finset.sum_insert hactive, Finset.sum_insert hactive]
        unfold FormalMultilinearSeries.coeff at ih ⊢
        rw [FormalMultilinearSeries.add_apply,
          FormalMultilinearSeries.smul_apply,
          ContinuousMultilinearMap.add_apply,
          ContinuousMultilinearMap.smul_apply]
        rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
        simp only [smul_eq_mul]
        have hone :
            (⇑(scalarRayCLM (restrictInteractionPacket active z)) ∘
                (1 : Fin n → ℂ)) =
              (fun _ : Fin n => restrictInteractionPacket active z) := by
          funext i
          simp [Function.comp_apply]
        rw [hone]
        change
          mu ℂ active packet *
                series n (fun _ => restrictInteractionPacket active z) +
              ((∑ x ∈ states,
                  (mu ℂ x packet) •
                    series.compContinuousLinearMap
                      (scalarRayCLM (restrictInteractionPacket x z))) n) 1 =
            mu ℂ active packet *
                series n (fun _ => restrictInteractionPacket active z) +
              ∑ x ∈ states,
                mu ℂ x packet *
                  series n (fun _ => restrictInteractionPacket x z)
        rw [ih]
  rw [packetRaySeries, hsum]
  rfl

/-- A scalar analytic response is active when it is not the zero germ. -/
def AnalyticSectorActive (f : ℂ → ℂ) : Prop :=
  ¬f =ᶠ[𝓝 0] (fun _ : ℂ => 0)

/-- Exact analytic birth depth of a scalar response represented by `series`. -/
noncomputable def analyticBirthOrder
    (series : FormalMultilinearSeries ℂ ℂ ℂ) : ℕ :=
  series.order

/-- Analytic unit left after removing the exact birth monomial. -/
noncomputable def analyticBirthUnit
    (f : ℂ → ℂ) (series : FormalMultilinearSeries ℂ ℂ ℂ) : ℂ → ℂ :=
  (Function.swap dslope 0)^[series.order] f

/-- An active analytic germ cannot have the zero Taylor series. -/
theorem series_ne_zero_of_analyticSectorActive
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0)
    (hactive : AnalyticSectorActive f) :
    series ≠ 0 := by
  intro hzero
  apply hactive
  exact HasFPowerSeriesAt.eventually_eq_zero (by simpa [hzero] using hf)

/-- An active response vanishing at zero has positive birth depth. -/
theorem analyticBirthOrder_pos
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0)
    (hf0 : f 0 = 0)
    (hactive : AnalyticSectorActive f) :
    0 < analyticBirthOrder series := by
  have hseries := series_ne_zero_of_analyticSectorActive hf hactive
  have hcoeff0 : series.coeff 0 = 0 := by
    simpa [hf0] using hf.coeff_zero 1
  have hseries0 : series 0 = 0 :=
    FormalMultilinearSeries.coeff_eq_zero.mp hcoeff0
  apply Nat.pos_of_ne_zero
  intro horder
  have hnonzero := FormalMultilinearSeries.apply_order_ne_zero hseries
  rw [analyticBirthOrder] at horder
  rw [horder] at hnonzero
  exact hnonzero hseries0

/-- Coefficient at the exact birth depth is nonzero. -/
theorem analyticBirthCoefficient_ne_zero
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0)
    (hactive : AnalyticSectorActive f) :
    series series.order ≠ 0 :=
  FormalMultilinearSeries.apply_order_ne_zero
    (series_ne_zero_of_analyticSectorActive hf hactive)

/-- Every coefficient below exact birth depth vanishes. -/
theorem analyticBirthCoefficient_eq_zero_below
    (series : FormalMultilinearSeries ℂ ℂ ℂ)
    {n : ℕ} (hn : n < analyticBirthOrder series) :
    series n = 0 :=
  FormalMultilinearSeries.apply_eq_zero_of_lt_order
    (by simpa [analyticBirthOrder] using hn)

/-- The factor left after removing the exact birth monomial is analytic. -/
theorem analyticBirthUnit_analyticAt
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0) :
    AnalyticAt ℂ (analyticBirthUnit f series) 0 := by
  exact
    (hf.has_fpower_series_iterate_dslope_fslope series.order).analyticAt

/-- The analytic birth unit is nonzero at the uncoupled point. -/
theorem analyticBirthUnit_zero_ne
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0)
    (hactive : AnalyticSectorActive f) :
    analyticBirthUnit f series 0 ≠ 0 := by
  exact hf.iterate_dslope_fslope_ne_zero
    (series_ne_zero_of_analyticSectorActive hf hactive)

/-- **Exact analytic birth factorization.** Every active analytic response
is its birth monomial times a nonvanishing analytic unit. -/
theorem analytic_eq_pow_birthOrder_mul_birthUnit
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0) (g : ℂ) :
    f g =
      g ^ analyticBirthOrder series * analyticBirthUnit f series g := by
  simpa [analyticBirthOrder, analyticBirthUnit, smul_eq_mul] using
    hf.eq_pow_order_mul_iterate_dslope g

/-- **Exact packet-depth lower law.** The analytic birth depth of an active
interaction packet cannot be smaller than the number of independently
indispensable labels. -/
theorem packetRaySeries_card_le_order
    {E : Type*} [Fintype E] [DecidableEq E]
    {f : (E → ℂ) → ℂ}
    {series : FormalMultilinearSeries ℂ (E → ℂ) ℂ}
    (hf : HasFPowerSeriesAt f series 0)
    (z : E → ℂ) (packet : Finset E)
    (hactive :
      AnalyticSectorActive
        (fun g : ℂ =>
          posetMobiusProbe (R := ℂ) packet
            (fun active =>
              f (g • restrictInteractionPacket active z)))) :
    packet.card ≤ (packetRaySeries series z packet).order := by
  let response : ℂ → ℂ :=
    fun g =>
      posetMobiusProbe (R := ℂ) packet
        (fun active => f (g • restrictInteractionPacket active z))
  have hresponse :
      HasFPowerSeriesAt response (packetRaySeries series z packet) 0 :=
    hasFPowerSeriesAt_packetRaySeries hf z packet
  have hseries :
      packetRaySeries series z packet ≠ 0 :=
    series_ne_zero_of_analyticSectorActive hresponse hactive
  by_contra hnot
  have hlt :
      (packetRaySeries series z packet).order < packet.card := by
    omega
  have hmobius :
      interactionMobiusTaylorCoefficient series
        (packetRaySeries series z packet).order z packet = 0 :=
    interactionMobiusTaylorCoefficient_eq_zero_of_lt_card
      series z packet hlt
  have hcoeff :
      (packetRaySeries series z packet).coeff
          (packetRaySeries series z packet).order = 0 := by
    rw [packetRaySeries_coeff_eq_interactionMobiusTaylorCoefficient]
    exact hmobius
  have hzero :
      packetRaySeries series z packet
          (packetRaySeries series z packet).order = 0 :=
    FormalMultilinearSeries.coeff_eq_zero.mp hcoeff
  exact
    (FormalMultilinearSeries.apply_order_ne_zero hseries) hzero

/-- Exact leading magnitude after dividing by the birth power. -/
theorem tendsto_norm_div_norm_pow_analyticBirthOrder
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0) :
    Tendsto
      (fun g : ℂ =>
        ‖f g‖ / ‖g‖ ^ analyticBirthOrder series)
      (𝓝[≠] 0)
      (𝓝 ‖analyticBirthUnit f series 0‖) := by
  have hunit :
      Tendsto
        (fun g : ℂ => ‖analyticBirthUnit f series g‖)
        (𝓝[≠] 0)
        (𝓝 ‖analyticBirthUnit f series 0‖) :=
    (analyticBirthUnit_analyticAt hf).continuousAt.norm.mono_left
      inf_le_left
  apply hunit.congr'
  filter_upwards [self_mem_nhdsWithin] with g hg
  have hg0 : g ≠ 0 := by
    simpa using hg
  rw [analytic_eq_pow_birthOrder_mul_birthUnit hf]
  rw [norm_mul, norm_pow]
  have hnorm : ‖g‖ ^ analyticBirthOrder series ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hg0)
  exact (mul_div_cancel_left₀ _ hnorm).symm

/-- **Exact inverse-detuning horizon law.** Coupling to the birth power
times inverse response magnitude has a finite nonzero limit. -/
theorem tendsto_norm_pow_div_norm_analyticBirthOrder
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0)
    (hactive : AnalyticSectorActive f) :
    Tendsto
      (fun g : ℂ =>
        ‖g‖ ^ analyticBirthOrder series / ‖f g‖)
      (𝓝[≠] 0)
      (𝓝 (‖analyticBirthUnit f series 0‖)⁻¹) := by
  have hlead :=
    tendsto_norm_div_norm_pow_analyticBirthOrder hf
  have hleadInv :=
    hlead.inv₀
      (norm_ne_zero_iff.mpr
        (analyticBirthUnit_zero_ne hf hactive))
  have hfNonzero :
      ∀ᶠ g in 𝓝[≠] (0 : ℂ), f g ≠ 0 :=
    hf.locally_ne_zero
      (series_ne_zero_of_analyticSectorActive hf hactive)
  apply hleadInv.congr'
  filter_upwards [self_mem_nhdsWithin, hfNonzero] with g hg hfg
  have hg0 : g ≠ 0 := by
    simpa using hg
  have hnorm : ‖g‖ ^ analyticBirthOrder series ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hg0)
  have hfFactor :=
    analytic_eq_pow_birthOrder_mul_birthUnit hf g
  rw [hfFactor, norm_mul, norm_pow]
  have hfNorm : ‖f g‖ ≠ 0 := norm_ne_zero_iff.mpr hfg
  field_simp

/-- **Analytic onset rigidity.** If an active analytic response is
`O (‖g‖ ^ r)`, its exact birth valuation is at least `r`. Thus a geometric
or locality-derived Big-O onset cannot conceal an earlier Taylor birth. -/
theorem le_analyticBirthOrder_of_isBigO_norm_pow
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f series 0)
    (hactive : AnalyticSectorActive f)
    (r : ℕ)
    (hO : f =O[𝓝 0] fun g : ℂ => ‖g‖ ^ r) :
    r ≤ analyticBirthOrder series := by
  by_contra hnot
  have hlt : analyticBirthOrder series < r := by
    omega
  have hlittle :
      f =o[𝓝 0]
        (fun g : ℂ =>
          ‖g‖ ^ analyticBirthOrder series) :=
    hO.trans_isLittleO
      (isLittleO_norm_pow_norm_pow hlt)
  have hlead :=
    tendsto_norm_div_norm_pow_analyticBirthOrder hf
  have hlead0 :
      ‖analyticBirthUnit f series 0‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (analyticBirthUnit_zero_ne hf hactive)
  have hreverse :
      (fun g : ℂ =>
        ‖g‖ ^ analyticBirthOrder series)
        =O[𝓝[≠] 0] fun g => ‖f g‖ :=
    isBigO_of_div_tendsto_nhds_of_ne_zero
      hlead hlead0
  have hlittle' :
      f =o[𝓝[≠] 0]
        (fun g : ℂ =>
          ‖g‖ ^ analyticBirthOrder series) :=
    hlittle.mono inf_le_left
  have hfreq :
      ∃ᶠ g in 𝓝[≠] (0 : ℂ),
        ‖g‖ ^ analyticBirthOrder series ≠ 0 := by
    have hev :
        ∀ᶠ g in 𝓝[≠] (0 : ℂ),
          ‖g‖ ^ analyticBirthOrder series ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with g hg
      exact
        pow_ne_zero _
          (norm_ne_zero_iff.mpr (by simpa using hg))
    exact hev.frequently
  exact
    (hreverse.not_isLittleO hfreq)
      hlittle'.norm_left

end GaloisForLFunctions.HTGeometry
