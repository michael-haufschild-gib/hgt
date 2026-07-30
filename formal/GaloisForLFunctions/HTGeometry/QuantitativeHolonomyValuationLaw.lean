import GaloisForLFunctions.HTGeometry.ObserverTemporalBirthValuationLaw

/-!
# Quantitative holonomy valuation transgression

The qualitative Möbius--holonomy law only says that some full interaction
packet survives.  This file proves the exact graded statement behind it.

If a difference has a nonzero coefficient at grade `n`, while each of two
candidate sectors vanishes below grade `n`, then one candidate has exact
birth grade `n`.  Applied to Boolean interaction packets, every coefficient
below the number of indispensable labels vanishes identically.  Therefore
an order-`n` holonomy obstruction across an `n`-label packet forces exact
order `n` in at least one packet sector.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A formal series whose `n`th coefficient is nonzero and whose lower
coefficients vanish has exact order `n`. -/
theorem formalMultilinearSeries_order_eq_of_exact_coefficient
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ)
    (hn : p n ≠ 0)
    (hbelow : ∀ m < n, p m = 0) :
    p.order = n := by
  have hp : p ≠ 0 := by
    intro hzero
    rw [hzero] at hn
    exact hn rfl
  apply le_antisymm
  · by_contra hnot
    have hlt : n < p.order := Nat.lt_of_not_ge hnot
    exact hn (FormalMultilinearSeries.apply_eq_zero_of_lt_order hlt)
  · by_contra hnot
    have hlt : p.order < n := Nat.lt_of_not_ge hnot
    exact
      (FormalMultilinearSeries.apply_order_ne_zero hp)
        (hbelow p.order hlt)

/-- **Exact difference-to-sector valuation law.** If `p - q` has exact
grade `n` and both sectors vanish below `n`, at least one sector has exact
grade `n`. -/
theorem one_order_eq_of_sub_exact_order
    (p q : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ)
    (hsub : p - q ≠ 0)
    (horder : (p - q).order = n)
    (hpbelow : ∀ m < n, p m = 0)
    (hqbelow : ∀ m < n, q m = 0) :
    p.order = n ∨ q.order = n := by
  have hdiff :
      (p - q) n ≠ 0 := by
    rw [← horder]
    exact FormalMultilinearSeries.apply_order_ne_zero hsub
  have hpq : p n ≠ 0 ∨ q n ≠ 0 := by
    by_contra h
    push Not at h
    apply hdiff
    simp [h.1, h.2]
  rcases hpq with hp | hq
  · exact Or.inl
      (formalMultilinearSeries_order_eq_of_exact_coefficient
        p n hp hpbelow)
  · exact Or.inr
      (formalMultilinearSeries_order_eq_of_exact_coefficient
        q n hq hqbelow)

/-- Boolean packet projection kills every homogeneous coefficient below
the number of indispensable labels, independently of whether the full
packet is active. -/
theorem packetRaySeries_apply_eq_zero_of_lt_card
    {E : Type*} [Fintype E] [DecidableEq E]
    (series : FormalMultilinearSeries ℂ (E → ℂ) ℂ)
    (z : E → ℂ) (packet : Finset E)
    (n : ℕ) (hn : n < packet.card) :
    packetRaySeries series z packet n = 0 := by
  apply FormalMultilinearSeries.coeff_eq_zero.mp
  rw [packetRaySeries_coeff_eq_interactionMobiusTaylorCoefficient]
  exact
    interactionMobiusTaylorCoefficient_eq_zero_of_lt_card
      series z packet hn

/-- **Quantitative packet transgression.** If the difference of two
full-packet ray series has exact order equal to packet cardinality, then
one of those two packet series is born at exactly that order. -/
theorem one_packetRaySeries_order_eq_card_of_holonomyDifference
    {E : Type*} [Fintype E] [DecidableEq E]
    (series : FormalMultilinearSeries ℂ (E → ℂ) ℂ)
    (positive negative : E → ℂ) (packet : Finset E)
    (hsub :
      packetRaySeries series positive packet -
          packetRaySeries series negative packet ≠ 0)
    (horder :
      (packetRaySeries series positive packet -
          packetRaySeries series negative packet).order =
        packet.card) :
    (packetRaySeries series positive packet).order = packet.card ∨
      (packetRaySeries series negative packet).order = packet.card := by
  apply one_order_eq_of_sub_exact_order
    (packetRaySeries series positive packet)
    (packetRaySeries series negative packet)
    packet.card hsub horder
  · intro m hm
    exact packetRaySeries_apply_eq_zero_of_lt_card
      series positive packet m hm
  · intro m hm
    exact packetRaySeries_apply_eq_zero_of_lt_card
      series negative packet m hm

/-- Full-support analytic monomial on a finite control family. -/
def fullSupportControlMonomial
    {E : Type*} [Fintype E] (z : E → ℂ) : ℂ :=
  ∏ e, z e

/-- Boolean Möbius projection of the full-support monomial along the unit
ray is exactly the corresponding scalar power. -/
theorem fullSupportControlMonomial_packetRay
    {E : Type*} [Fintype E] [DecidableEq E]
    (g : ℂ) :
    posetMobiusProbe (R := ℂ) (Finset.univ : Finset E)
        (fun active =>
          fullSupportControlMonomial
            (g • restrictInteractionPacket active
              (fun _ : E => (1 : ℂ)))) =
      g ^ Fintype.card E := by
  have hresponse : ∀ active : Finset E,
      fullSupportControlMonomial
          (g • restrictInteractionPacket active
            (fun _ : E => (1 : ℂ))) =
        if active = Finset.univ then
          g ^ Fintype.card E
        else 0 := by
    intro active
    by_cases hfull : active = Finset.univ
    · subst active
      simp [fullSupportControlMonomial, restrictInteractionPacket,
        Finset.card_univ]
    · have hmissing : ∃ e : E, e ∉ active := by
        by_contra h
        push Not at h
        apply hfull
        ext e
        simp [h e]
      obtain ⟨e, he⟩ := hmissing
      rw [if_neg hfull]
      unfold fullSupportControlMonomial
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [restrictInteractionPacket, he]
  unfold posetMobiusProbe
  rw [Finset.sum_eq_single (Finset.univ : Finset E)]
  · change
      IncidenceAlgebra.mu ℂ
          (Finset.univ : Finset E) Finset.univ *
        fullSupportControlMonomial
          (g • restrictInteractionPacket Finset.univ
            (fun _ : E => (1 : ℂ))) =
        g ^ Fintype.card E
    rw [hresponse, if_pos rfl]
    simp
  · intro active hactive hne
    change
      IncidenceAlgebra.mu ℂ active Finset.univ *
        fullSupportControlMonomial
          (g • restrictInteractionPacket active
            (fun _ : E => (1 : ℂ))) = 0
    rw [hresponse, if_neg hne]
    simp
  · simp

/-- The full-support monomial is analytic at the uncoupled point. -/
theorem fullSupportControlMonomial_analyticAt
    {E : Type*} [Fintype E] :
    AnalyticAt ℂ
      (fullSupportControlMonomial : (E → ℂ) → ℂ) 0 := by
  classical
  unfold fullSupportControlMonomial
  apply Finset.analyticAt_fun_prod
  intro e he
  exact
    (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : E => ℂ) e).analyticAt 0

/-- **All-orders sharpness of Boolean valuation.** For every finite control
family, the packet-cardinality lower bound is attained exactly by the
full-support analytic monomial. -/
theorem fullSupportControlMonomial_packetRaySeries_order
    {E : Type*} [Fintype E] [DecidableEq E]
    (series : FormalMultilinearSeries ℂ (E → ℂ) ℂ)
    (hseries :
      HasFPowerSeriesAt
        (fullSupportControlMonomial : (E → ℂ) → ℂ)
        series 0) :
    (packetRaySeries series (fun _ : E => (1 : ℂ))
      (Finset.univ : Finset E)).order =
        Fintype.card E := by
  let response : ℂ → ℂ :=
    fun g =>
      posetMobiusProbe (R := ℂ) (Finset.univ : Finset E)
        (fun active =>
          fullSupportControlMonomial
            (g • restrictInteractionPacket active
              (fun _ : E => (1 : ℂ))))
  let responseSeries :=
    packetRaySeries series (fun _ : E => (1 : ℂ))
      (Finset.univ : Finset E)
  have hresponse :
      HasFPowerSeriesAt response responseSeries 0 :=
    hasFPowerSeriesAt_packetRaySeries hseries
      (fun _ : E => (1 : ℂ)) Finset.univ
  have hresponseEq :
      response = fun g : ℂ => g ^ Fintype.card E := by
    funext g
    exact fullSupportControlMonomial_packetRay g
  have hactive : AnalyticSectorActive response := by
    intro hzero
    have hzero' :=
      hzero.filter_mono (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from inf_le_left)
    have hnonzero :
        ∀ᶠ g in 𝓝[≠] (0 : ℂ), response g ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with g hg
      rw [hresponseEq]
      exact pow_ne_zero _ (by simpa using hg)
    obtain ⟨g, hg, hgne⟩ := (hzero'.and hnonzero).exists
    exact hgne hg
  have hfirst :
      ∃ unit : ℂ → ℂ,
        AnalyticAt ℂ unit 0 ∧ unit 0 ≠ 0 ∧
          ∀ᶠ g in 𝓝 (0 : ℂ),
            response g =
              (g - 0) ^ Fintype.card E • unit g := by
    refine ⟨fun _ => (1 : ℂ), analyticAt_const, one_ne_zero, ?_⟩
    filter_upwards [] with g
    rw [hresponseEq]
    simp [smul_eq_mul]
  have hsecond :
      ∃ unit : ℂ → ℂ,
        AnalyticAt ℂ unit 0 ∧ unit 0 ≠ 0 ∧
          ∀ᶠ g in 𝓝 (0 : ℂ),
            response g =
              (g - 0) ^ responseSeries.order • unit g := by
    refine
      ⟨analyticBirthUnit response responseSeries,
        analyticBirthUnit_analyticAt hresponse,
        analyticBirthUnit_zero_ne hresponse hactive, ?_⟩
    filter_upwards [] with g
    simpa [analyticBirthOrder, smul_eq_mul] using
      analytic_eq_pow_birthOrder_mul_birthUnit hresponse g
  exact
    (AnalyticAt.unique_eventuallyEq_pow_smul_nonzero
      (f := response) (z₀ := (0 : ℂ))
      (m := Fintype.card E) (n := responseSeries.order)
      hfirst hsecond).symm

end

end GaloisForLFunctions.HTGeometry
