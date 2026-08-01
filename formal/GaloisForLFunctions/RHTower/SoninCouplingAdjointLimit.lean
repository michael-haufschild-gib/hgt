import GaloisForLFunctions.RHTower.SoninDoublyContractedPacket

/-!
# The adjoint coupling returns the wavepacket

Reading the coupling backwards, the inner layer fixes the dilated packet, the dilation sum splits
it into the original packet and a doubly contracted copy, the outer layer fixes the former and
kills the latter.  So the adjoint coupling sends the dilated packet back to the packet.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology

/-- **`(4a)`.**  The adjoint coupling carries the dilated wavepacket back to the wavepacket. -/
theorem tendsto_norm_adjoint_soninApertureCoupling_soninDilatedPacket_sub
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n)
    (hsq : ∀ n, 0 < r n ^ 2) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖ContinuousLinearMap.adjoint
            (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n))
            (soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)) -
          soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))‖) atTop (𝓝 0) := by
  have hq : 0 < q := ha.trans haq
  have hA : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hq hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  have hInner := tendsto_norm_evenSoninApertureLayer_soninDilatedPacket_sub b c hb hbc q a b
    ha haq hqb r hrpos hr
  have hOuter := tendsto_norm_evenSoninApertureLayer_soninPacketEven_sub b c hb hbc
    (fun n : ℕ => 2 * Real.pi * (r n * q)) hA
  have hDouble := tendsto_norm_evenSoninApertureLayer_doublyContracted b c hb hbc q hq r hsq hr
  have hmaj : Tendsto (fun n : ℕ =>
      2 * ‖evenSoninApertureLayer a b
            (soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)) -
          soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖ +
        (‖evenSoninApertureLayer b c (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))) -
            soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))‖ +
          ‖evenSoninApertureLayer b c
            (soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n ^ 2) (hsq n))‖))
      atTop (𝓝 0) := by
    simpa using (hInner.const_mul (2 : ℝ)).add (hOuter.add hDouble)
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hmaj
  set w : evenSubspace := soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)) with hw
  set v : evenSubspace :=
    soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n) with hv
  set z : evenSubspace :=
    soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n ^ 2) (hsq n) with hz
  set e : evenSubspace := evenSoninApertureLayer a b v - v with he
  -- the adjoint, applied
  have hadj : ContinuousLinearMap.adjoint
      (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)) v =
      evenSoninApertureLayer b c
        (evenDilationSum (r n) (hrgt n) (evenSoninApertureLayer a b v)) := by
    rw [adjoint_evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n),
      mul_apply_eq_comp, mul_apply_eq_comp]
  -- the dilation sum on the inverse dilate
  have hDv : evenDilationSum (r n) (hrgt n) v = w + z := by
    rw [hv, hz]
    exact evenDilationSum_evenDilationCLM_inv_apply (r n) (hrgt n) (inv_pos.mpr (hsq n)) w
  have hstep : ContinuousLinearMap.adjoint
      (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)) v - w =
      evenSoninApertureLayer b c (evenDilationSum (r n) (hrgt n) e) +
        ((evenSoninApertureLayer b c w - w) + evenSoninApertureLayer b c z) := by
    rw [hadj]
    have hlin : evenSoninApertureLayer a b v = v + e := by
      rw [he]; abel
    rw [hlin, map_add, map_add, hDv, map_add]
    abel
  rw [hstep]
  calc ‖evenSoninApertureLayer b c (evenDilationSum (r n) (hrgt n) e) +
          ((evenSoninApertureLayer b c w - w) + evenSoninApertureLayer b c z)‖
      ≤ ‖evenSoninApertureLayer b c (evenDilationSum (r n) (hrgt n) e)‖ +
          ‖(evenSoninApertureLayer b c w - w) + evenSoninApertureLayer b c z‖ :=
        norm_add_le _ _
    _ ≤ 2 * ‖e‖ + (‖evenSoninApertureLayer b c w - w‖ + ‖evenSoninApertureLayer b c z‖) := by
        gcongr
        · calc ‖evenSoninApertureLayer b c (evenDilationSum (r n) (hrgt n) e)‖
              ≤ ‖evenDilationSum (r n) (hrgt n) e‖ :=
                norm_evenSoninApertureLayer_apply_le hbc.le _
            _ ≤ 2 * ‖e‖ := norm_evenDilationSum_apply_le (r n) (hrgt n) e
        · exact norm_add_le _ _

end RHTower
