import GaloisForLFunctions.HTGeometry.LogBelowLinear
import GaloisForLFunctions.RHTower.SoninBurnolFrequencyLogOrder
import GaloisForLFunctions.RHTower.SoninScheduleSequence
import GaloisForLFunctions.RHTower.SoninCompletionRateTest

/-!
# Burnol's logarithmic shell conductor cannot restore the Sonin floor

The preceding exact order theorem is now handed to the actual Sonin curvature source.  Along its
explicit schedule, curvature energy has positive linear order in dilation scale.  An affine
logarithm of that scale falls short by a fixed amount.  This remains true for every choice of the
finite conductor height at every scale.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology InnerProduct InnerProductSpace

/-- An affine logarithm of a positive multiple is eventually below every positive linear slope. -/
theorem eventually_affine_log_mul_add_le_linear
    {s q C₀ C₁ δ : ℝ} (hs : 0 < s) (hq : 0 < q) (hC₁ : 0 ≤ C₁) :
    ∀ᶠ x : ℝ in atTop, C₀ + C₁ * Real.log (x * q) + δ ≤ s * x := by
  rcases hC₁.eq_or_lt with hzero | hpos
  · rw [← hzero]
    simp only [zero_mul, add_zero]
    filter_upwards [eventually_ge_atTop ((C₀ + δ) / s)] with x hx
    have hm := (div_le_iff₀ hs).mp hx
    linarith
  · have hs' : 0 < s / C₁ := div_pos hs hpos
    have hev := GaloisForLFunctions.HTGeometry.eventually_log_add_le_linear
      hs' 0 ((C₀ + C₁ * Real.log q + δ) / C₁)
    filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
    have hlog : Real.log (x * q) = Real.log x + Real.log q :=
      Real.log_mul hxpos.ne' hq.ne'
    have hmul := mul_le_mul_of_nonneg_left hx hpos.le
    have hleft : C₁ *
        (Real.log x + (C₀ + C₁ * Real.log q + δ) / C₁) =
          C₀ + C₁ * Real.log (x * q) + δ := by
      rw [hlog]
      field_simp
      ring
    have hright : C₁ * ((s / C₁) * x - 0) = s * x := by
      field_simp
      ring
    rwa [hleft, hright] at hmul

/-- **Terminal Route F no-go.**  For every geometric Burnol shell conductor and every schedule of
finite tower heights, the literal conductor pairing on the canonical source packets fails to
restore a lower floor.  The witness is the source's own explicit linear-energy schedule. -/
theorem not_bddBelow_soninCompletedPacketValueVar_soninBurnolLogShellConductorFamily
    (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b)
    (haq : a < q) (hqb : 2 * q ≤ b)
    (a₀ r₀ : ℝ) (ha₀ : 0 < a₀) (hr₀ : 1 < r₀) (height : ℕ → ℕ) :
    ∃ (κ : ℝ) (Nstart : ℕ)
      (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValueVar s a b c
          (fun i => soninShellCutScale b c (Nstart + i) κ) hp
          (fun i =>
            (⟪soninPacketEven b c hb hbc
                (2 * Real.pi * (soninShellCutScale b c (Nstart + i) κ * q)),
              soninBurnolLogShellConductor a₀ r₀ (height i)
                (soninPacketEven b c hb hbc
                  (2 * Real.pi * (soninShellCutScale b c (Nstart + i) κ * q)))⟫_ℂ).re) := by
  obtain ⟨C₀, C₁, hC₀0, hC₁0, hcap⟩ :=
    exists_re_inner_soninPacketEven_soninBurnolLogShellConductor_le_log
      b c hb hbc a₀ r₀ ha₀ hr₀
  obtain ⟨κ, Nstart, hp, hκ, hcp, henergy⟩ :=
    exists_scale_sequence_of_schedule N₀ hN₀ a b c q hbc ha hab.le hb haq hqb
  refine ⟨κ, Nstart, hp, ?_⟩
  set p : ℕ → ℝ := fun i => soninShellCutScale b c (Nstart + i) κ with hpdef
  set g : ℕ → ℝ := fun i =>
    (⟪soninPacketEven b c hb hbc (2 * Real.pi * (p i * q)),
      soninBurnolLogShellConductor a₀ r₀ (height i)
        (soninPacketEven b c hb hbc (2 * Real.pi * (p i * q)))⟫_ℂ).re with hgdef
  set Dis : ℝ := 2 * hsNormSq (evenSoninProjectionCorrection b) +
    hsNormSq (evenSoninProjectionCorrection a - evenSoninProjectionCorrection b) with hDis
  set slope : ℝ := (c - b) / (8 * κ) with hslope
  have hq : 0 < q := ha.trans haq
  have hslopepos : 0 < slope := by
    have : 0 < c - b := sub_pos.mpr hbc
    rw [hslope]
    positivity
  have hadd : Tendsto (fun i : ℕ => Nstart + i) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat Nstart
  have hpdiv : Tendsto p atTop atTop := by
    rw [hpdef]
    exact (tendsto_soninShellCutScale_atTop b c hbc hκ).comp hadd
  have hAdiv : Tendsto (fun i => p i * q) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hq hpdiv
  have hlogevent : ∀ᶠ i : ℕ in atTop,
      C₀ + C₁ * Real.log (p i * q) + (1 + 36 * Dis) ≤ slope * p i :=
    hpdiv.eventually
      (eventually_affine_log_mul_add_le_linear hslopepos hq hC₁0)
  have hshort : ∀ᶠ i : ℕ in atTop, g i + 1 ≤
      hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i)) := by
    filter_upwards [hlogevent, hAdiv.eventually_ge_atTop 1] with i hlog hA
    have hcapᵢ : g i ≤ C₀ + C₁ * Real.log (p i * q) := by
      rw [hgdef]
      exact hcap (p i * q) (height i) hA
    have hposN : 0 < Nstart + i := by
      rcases Nat.eq_zero_or_pos (Nstart + i) with hzero | hpos
      · exfalso
        have := hp i
        rw [hzero, soninShellCutScale] at this
        norm_num at this
      · exact hpos
    have hlin : ((Nstart + i : ℕ) : ℝ) / 4 = slope * p i := by
      have hmul := soninShellCutScale_mul_slope b c hbc hposN hκ
      rw [hslope, hpdef]
      calc ((Nstart + i : ℕ) : ℝ) / 4
          = ((c - b) / (2 * κ) * soninShellCutScale b c (Nstart + i) κ) / 4 := by
              rw [hmul]
        _ = (c - b) / (8 * κ) * soninShellCutScale b c (Nstart + i) κ := by ring
    have hE : slope * p i - 36 * Dis ≤
        hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i)) := by
      simpa only [hpdef, hlin] using henergy i
    calc g i + 1 ≤ C₀ + C₁ * Real.log (p i * q) + 1 := by linarith
      _ ≤ slope * p i - 36 * Dis := by linarith
      _ ≤ hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c (p i) (hp i)) := hE
  have hresult := not_bddBelow_soninCompletedPacketValueVar_of_shortfall ha hab hbc
    (fun i => soninShellCutScale b c (Nstart + i) κ) hp hcp g 1 one_pos hshort
  simpa only [hgdef, hpdef] using hresult

end RHTower
