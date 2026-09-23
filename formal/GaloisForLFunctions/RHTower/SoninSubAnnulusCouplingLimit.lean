import GaloisForLFunctions.RHTower.SoninCouplingNonannihilation

/-!
# The coupling carries every sub-annulus wavepacket to its dilate

The two-branch estimate only sees the wavepacket through two support facts: it vanishes inside the
inner aperture and is supported inside the outer one.  A packet built on any sub-annulus of the
aperture window has both, so the transition limit holds for it with the same proof, with the
aperture flag and the packet annulus now independent.

This is what makes several packets available at one flag: disjoint sub-annuli give several
wavepackets, each carried by the coupling to its own dilate.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology

/-- **Sub-annulus transition limit.**  For a packet built on any annulus inside the aperture
window, the coupling carries it to its inverse dilate. -/
theorem tendsto_norm_soninApertureCoupling_soninPacketEven_sub_subAnnulus
    (a b c β γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c)
    (hβ : 0 < β) (hβγ : β < γ) (hbβ : b ≤ β) (hγc : γ ≤ c)
    (q : ℝ) (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c ≤ r n * a)
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
            (soninPacketEven β γ hβ hβγ (2 * Real.pi * (r n * q))) -
          soninDilatedPacket β γ hβ hβγ (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖)
      atTop (𝓝 0) := by
  have hq : 0 < q := ha.trans haq
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hq hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  have hLayer := tendsto_norm_evenSoninApertureLayer_soninDilatedPacket_sub β γ hβ hβγ q a b
    ha haq hqb r hrpos hr
  have hBand := tendsto_norm_evenFourierCutoff_soninPacketEven β γ hβ hβγ b
    (fun n : ℕ => 2 * Real.pi * (r n * q)) hfreq
  have hCorr := tendsto_norm_evenSoninProjectionCorrection_apply_soninPacketEven β γ b
    hβ hβγ hb (fun n : ℕ => 2 * Real.pi * (r n * q)) hfreq
  have hmaj : Tendsto (fun n : ℕ =>
      2 * ‖evenSoninProjectionCorrection b
            (soninPacketEven β γ hβ hβγ (2 * Real.pi * (r n * q)))‖ +
        (‖evenSoninApertureLayer a b
              (soninDilatedPacket β γ hβ hβγ (2 * Real.pi * (r n * q)) (r n) (hrpos n)) -
            soninDilatedPacket β γ hβ hβγ (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖ +
          ‖evenFourierCutoff b
            (soninPacketEven β γ hβ hβγ (2 * Real.pi * (r n * q)))‖)) atTop (𝓝 0) := by
    simpa using (hCorr.const_mul (2 : ℝ)).add (hLayer.add hBand)
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hmaj
  set w : evenSubspace := soninPacketEven β γ hβ hβγ (2 * Real.pi * (r n * q)) with hw
  set v : evenSubspace :=
    soninDilatedPacket β γ hβ hβγ (2 * Real.pi * (r n * q)) (r n) (hrpos n) with hv
  have hvdef : v = evenDilationCLM (r n)⁻¹ (inv_pos.mpr (hrpos n)) w := rfl
  have hlow : evenIndicatorCutoff b w = 0 :=
    evenIndicatorCutoff_soninPacketEven_eq_zero_of_le β γ hβ hβγ
      (2 * Real.pi * (r n * q)) b hbβ
  have hhigh : evenIndicatorCutoff c w = w :=
    evenIndicatorCutoff_soninPacketEven_eq_self_of_le β γ hβ hβγ
      (2 * Real.pi * (r n * q)) c hγc
  have hbranch := norm_evenSoninApertureSuccessiveLayerTransition_sub_branches_le
    hab.le hbc.le (hrgt n) (hcr n) hlow hhigh
  have hexp : ‖evenSoninApertureLayer a b
      (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n)) (evenFourierCutoff b w))‖ ≤
      ‖evenFourierCutoff b w‖ := by
    calc ‖evenSoninApertureLayer a b
          (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n)) (evenFourierCutoff b w))‖
        ≤ ‖evenDilationCLM (r n) (zero_lt_one.trans (hrgt n)) (evenFourierCutoff b w)‖ :=
          norm_evenSoninApertureLayer_apply_le hab.le _
      _ = ‖evenFourierCutoff b w‖ :=
          norm_evenDilationCLM_apply (r n) (zero_lt_one.trans (hrgt n)) _
  calc ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) w - v‖
      ≤ ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) w -
            (evenSoninApertureLayer a b
                (evenDilationCLM (r n)⁻¹ (inv_pos.mpr (zero_lt_one.trans (hrgt n))) w) -
              evenSoninApertureLayer a b
                (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n))
                  (evenFourierCutoff b w)))‖ +
          ‖(evenSoninApertureLayer a b
                (evenDilationCLM (r n)⁻¹ (inv_pos.mpr (zero_lt_one.trans (hrgt n))) w) -
              evenSoninApertureLayer a b
                (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n))
                  (evenFourierCutoff b w))) - v‖ := by
        simpa using norm_sub_le_norm_sub_add_norm_sub
          (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) w)
          (evenSoninApertureLayer a b
              (evenDilationCLM (r n)⁻¹ (inv_pos.mpr (zero_lt_one.trans (hrgt n))) w) -
            evenSoninApertureLayer a b
              (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n)) (evenFourierCutoff b w))) v
    _ ≤ 2 * ‖evenSoninProjectionCorrection b w‖ +
          (‖evenSoninApertureLayer a b v - v‖ + ‖evenFourierCutoff b w‖) := by
        refine add_le_add hbranch ?_
        calc ‖(evenSoninApertureLayer a b
                  (evenDilationCLM (r n)⁻¹ (inv_pos.mpr (zero_lt_one.trans (hrgt n))) w) -
                evenSoninApertureLayer a b
                  (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n))
                    (evenFourierCutoff b w))) - v‖
              = ‖(evenSoninApertureLayer a b v - v) -
                  evenSoninApertureLayer a b
                    (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n))
                      (evenFourierCutoff b w))‖ := by
                rw [hvdef]
                congr 1
                abel
          _ ≤ ‖evenSoninApertureLayer a b v - v‖ +
                ‖evenSoninApertureLayer a b
                    (evenDilationCLM (r n) (zero_lt_one.trans (hrgt n))
                      (evenFourierCutoff b w))‖ := norm_sub_le _ _
          _ ≤ ‖evenSoninApertureLayer a b v - v‖ + ‖evenFourierCutoff b w‖ := by
              gcongr

/-- **Sub-annulus norm limit.**  The coupling's action on a sub-annulus packet family has that
packet's own limiting norm. -/
theorem tendsto_norm_soninApertureCoupling_apply_soninPacketEven_subAnnulus
    (a b c β γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c)
    (hβ : 0 < β) (hβγ : β < γ) (hbβ : b ≤ β) (hγc : γ ≤ c)
    (q : ℝ) (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c ≤ r n * a)
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
          (soninPacketEven β γ hβ hβγ (2 * Real.pi * (r n * q)))‖) atTop
      (𝓝 (Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump β γ hβγ x ^ (2 : ℕ)))) := by
  have hq : 0 < q := ha.trans haq
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hq hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  have hdiff := tendsto_norm_soninApertureCoupling_soninPacketEven_sub_subAnnulus a b c β γ
    ha hb hab hbc hβ hβγ hbβ hγc q haq hqb r hrpos hrgt hcr hr
  have hpacket := tendsto_norm_soninPacketEven β γ hβ hβγ
    (fun n : ℕ => 2 * Real.pi * (r n * q)) hfreq
  have hdil : Tendsto (fun n : ℕ =>
      ‖soninDilatedPacket β γ hβ hβγ (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖) atTop
      (𝓝 (Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump β γ hβγ x ^ (2 : ℕ)))) := by
    refine hpacket.congr fun n => ?_
    exact (norm_soninDilatedPacket β γ hβ hβγ (2 * Real.pi * (r n * q)) (r n) (hrpos n)).symm
  have hclose : Tendsto (fun n : ℕ =>
      ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
          (soninPacketEven β γ hβ hβγ (2 * Real.pi * (r n * q)))‖ -
        ‖soninDilatedPacket β γ hβ hβγ (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hdiff
    exact abs_norm_sub_norm_le _ _
  have hsum := hclose.add hdil
  simpa using hsum

end RHTower
