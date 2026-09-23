import GaloisForLFunctions.RHTower.SoninBoundedCompletionFails

/-!
# A bounded contribution sequence, and the packets' own size

The failure needs nothing of the contribution but that it stay below a fixed level: the energy along
the schedule diverges, so a bounded sequence eventually trails it by one.  Stating it for a sequence
rather than a function of the scale is what lets an operator family supply the contribution.

For such a family the pairing is bounded once the packets are, and they are: with the mean below one
the packet's energy is at most four times the squared profile's mass.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology InnerProduct InnerProductSpace

/-- The packet's square is integrable. -/
theorem integrable_soninScaledPacket_sq (m δ κ : ℝ) (hδ : 0 < δ) :
    Integrable fun x : ℝ => soninScaledPacket m δ κ x ^ (2 : ℕ) := by
  have hcont : Continuous fun x : ℝ => soninScaledPacket m δ κ x ^ (2 : ℕ) :=
    (continuous_soninScaledPacket m δ κ hδ).pow 2
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_soninScaledPacket m δ κ hδ) ?_
  intro x hx
  refine subset_tsupport _ ?_
  intro h0
  exact hx (by simp [h0])

/-- **The packet is no larger than four profiles.**  With the mean below one the packet's energy is
at most four times the squared profile's mass. -/
theorem norm_sq_soninScaledPacketEven_le (m δ w : ℝ) (hδ : 0 < δ) (hm : δ < m)
    (hmean : |soninScaledPacketMean m δ (2 * Real.pi * w)| ≤ 1) :
    ‖soninScaledPacketEven m δ (2 * Real.pi * w) hδ‖ ^ (2 : ℕ) ≤
      8 * δ * ∫ y : ℝ, soninUnitBumpSq y := by
  have hpt : ∀ x : ℝ, soninScaledPacket m δ (2 * Real.pi * w) x ^ (2 : ℕ) ≤
      4 * soninScaledAnnulusBump m δ x ^ (2 : ℕ) := by
    intro x
    have hcos : |Real.cos (2 * Real.pi * w * x)| ≤ 1 := Real.abs_cos_le_one _
    have hfac : (Real.cos (2 * Real.pi * w * x) -
        soninScaledPacketMean m δ (2 * Real.pi * w)) ^ (2 : ℕ) ≤ 4 := by
      rcases abs_le.mp hcos with ⟨hc1, hc2⟩
      rcases abs_le.mp hmean with ⟨hm1, hm2⟩
      nlinarith [hc1, hc2, hm1, hm2]
    rw [soninScaledPacket, mul_pow]
    nlinarith [hfac, sq_nonneg (soninScaledAnnulusBump m δ x)]
  have hint₁ := integrable_soninScaledPacket_sq m δ (2 * Real.pi * w) hδ
  have hint₂ := (integrable_soninScaledAnnulusBump_sq m δ hδ).const_mul 4
  have hmono : (∫ x : ℝ, soninScaledPacket m δ (2 * Real.pi * w) x ^ (2 : ℕ)) ≤
      ∫ x : ℝ, 4 * soninScaledAnnulusBump m δ x ^ (2 : ℕ) :=
    integral_mono hint₁ hint₂ hpt
  rw [norm_sq_soninScaledPacketEven m δ (2 * Real.pi * w) hδ]
  rw [integral_const_mul, integral_soninScaledAnnulusBump_sq_eq m δ hδ hm] at hmono
  linarith [hmono]

/-- **No bounded contribution sequence restores the floor.**  Only divergence of the energy is
used, so the contribution may be any sequence staying below a level. -/
theorem not_bddBelow_soninCompletedPacketValueVar_of_bddAbove_seq (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) (g : ℕ → ℝ) (Bnd : ℝ) (hg : ∀ i, g i ≤ Bnd) :
    ∃ (κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValueVar s a b c
          (fun i => soninShellCutScale b c (Nstart + i) κ) hp g := by
  obtain ⟨κ, Nstart, hp, hκ, hcp, henergy⟩ :=
    exists_scale_sequence_of_schedule N₀ hN₀ a b c q hbc ha hab.le hb haq hqb
  refine ⟨κ, Nstart, hp, ?_⟩
  set Dis : ℝ := 2 * hsNormSq (evenSoninProjectionCorrection b) +
    hsNormSq (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) with hDis
  have hcount : Tendsto (fun i : ℕ => ((Nstart + i : ℕ) : ℝ) / 4 - 36 * Dis) atTop atTop := by
    have hadd : Tendsto (fun i : ℕ => ((Nstart + i : ℕ) : ℝ)) atTop atTop := by
      have : Tendsto (fun i : ℕ => Nstart + i) atTop atTop := by
        simpa [Nat.add_comm] using tendsto_add_atTop_nat Nstart
      exact tendsto_natCast_atTop_atTop.comp this
    have hdiv : Tendsto (fun i : ℕ => ((Nstart + i : ℕ) : ℝ) / 4) atTop atTop :=
      hadd.atTop_div_const (by norm_num : (0 : ℝ) < 4)
    refine (tendsto_atTop_add_const_right atTop (-(36 * Dis)) hdiv).congr fun i => ?_
    ring
  have hshort : ∀ᶠ i : ℕ in atTop, g i + 1 ≤
      hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c
        (soninShellCutScale b c (Nstart + i) κ) (hp i)) := by
    filter_upwards [hcount.eventually_ge_atTop (Bnd + 1)] with i hi
    exact le_trans (by linarith [hg i]) (le_trans hi (henergy i))
  exact not_bddBelow_soninCompletedPacketValueVar_of_shortfall ha hab hbc
    (fun i => soninShellCutScale b c (Nstart + i) κ) hp hcp g 1 one_pos hshort

end RHTower
