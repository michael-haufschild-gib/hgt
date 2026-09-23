import GaloisForLFunctions.RHTower.SoninCouplingAdjointLimit

/-!
# The coupling is a partial unitary on the packet classes

The coupling and its adjoint are both bounded by two, and each carries one packet class to the
other.  Composing them therefore returns each class to itself, so on these two classes the boundary
transition is a genuine partial unitary and the Hilbert adjoint is its inverse.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology

/-- The coupling is a contraction up to the factor two. -/
theorem norm_evenSoninApertureSuccessiveLayerTransition_apply_le
    {a b c r : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) (x : evenSubspace) :
    ‖evenSoninApertureSuccessiveLayerTransition a b c r hr x‖ ≤ 2 * ‖x‖ := by
  have happ : evenSoninApertureSuccessiveLayerTransition a b c r hr x =
      evenSoninApertureLayer a b
        (evenDilationSum r hr (evenSoninApertureLayer b c x)) := by
    unfold evenSoninApertureSuccessiveLayerTransition
    rw [mul_apply_eq_comp, mul_apply_eq_comp]
  rw [happ]
  calc ‖evenSoninApertureLayer a b (evenDilationSum r hr (evenSoninApertureLayer b c x))‖
      ≤ ‖evenDilationSum r hr (evenSoninApertureLayer b c x)‖ :=
        norm_evenSoninApertureLayer_apply_le hab _
    _ ≤ 2 * ‖evenSoninApertureLayer b c x‖ :=
        norm_evenDilationSum_apply_le r hr _
    _ ≤ 2 * ‖x‖ := by
        gcongr
        exact norm_evenSoninApertureLayer_apply_le hbc x

/-- The adjoint coupling is a contraction up to the factor two. -/
theorem norm_adjoint_evenSoninApertureSuccessiveLayerTransition_apply_le
    {a b c r : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) (x : evenSubspace) :
    ‖ContinuousLinearMap.adjoint
        (evenSoninApertureSuccessiveLayerTransition a b c r hr) x‖ ≤ 2 * ‖x‖ := by
  have happ : ContinuousLinearMap.adjoint
      (evenSoninApertureSuccessiveLayerTransition a b c r hr) x =
      evenSoninApertureLayer b c
        (evenDilationSum r hr (evenSoninApertureLayer a b x)) := by
    rw [adjoint_evenSoninApertureSuccessiveLayerTransition a b c r hr,
      mul_apply_eq_comp, mul_apply_eq_comp]
  rw [happ]
  calc ‖evenSoninApertureLayer b c (evenDilationSum r hr (evenSoninApertureLayer a b x))‖
      ≤ ‖evenDilationSum r hr (evenSoninApertureLayer a b x)‖ :=
        norm_evenSoninApertureLayer_apply_le hbc _
    _ ≤ 2 * ‖evenSoninApertureLayer a b x‖ :=
        norm_evenDilationSum_apply_le r hr _
    _ ≤ 2 * ‖x‖ := by
        gcongr
        exact norm_evenSoninApertureLayer_apply_le hab x

/-- **`(4b)`, first half.**  The adjoint coupling inverts the coupling on the packet class. -/
theorem tendsto_norm_adjoint_mul_soninApertureCoupling_soninPacketEven_sub
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n)
    (hsq : ∀ n, 0 < r n ^ (2 : ℕ)) (hcr : ∀ n, c ≤ r n * a) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖ContinuousLinearMap.adjoint
            (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n))
            (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
              (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))) -
          soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))‖) atTop (𝓝 0) := by
  have hforward := tendsto_norm_soninApertureCoupling_soninPacketEven_sub a b c ha hb hab hbc q
    haq hqb r hrpos hrgt hcr hr
  have hback := tendsto_norm_adjoint_soninApertureCoupling_soninDilatedPacket_sub a b c ha hb
    hbc q haq hqb r hrpos hrgt hsq hr
  have hmaj : Tendsto (fun n : ℕ =>
      2 * ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
            (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))) -
          soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖ +
        ‖ContinuousLinearMap.adjoint
            (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n))
            (soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)) -
          soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))‖) atTop (𝓝 0) := by
    simpa using (hforward.const_mul (2 : ℝ)).add hback
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hmaj
  set w : evenSubspace := soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)) with hw
  set v : evenSubspace :=
    soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n) with hv
  set Z := evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) with hZ
  have hsplit : ContinuousLinearMap.adjoint Z (Z w) - w =
      ContinuousLinearMap.adjoint Z (Z w - v) +
        (ContinuousLinearMap.adjoint Z v - w) := by
    rw [map_sub]
    abel
  rw [hsplit]
  calc ‖ContinuousLinearMap.adjoint Z (Z w - v) + (ContinuousLinearMap.adjoint Z v - w)‖
      ≤ ‖ContinuousLinearMap.adjoint Z (Z w - v)‖ + ‖ContinuousLinearMap.adjoint Z v - w‖ :=
        norm_add_le _ _
    _ ≤ 2 * ‖Z w - v‖ + ‖ContinuousLinearMap.adjoint Z v - w‖ := by
        gcongr
        exact norm_adjoint_evenSoninApertureSuccessiveLayerTransition_apply_le hab.le hbc.le
          (hrgt n) _

/-- **`(4b)`, second half.**  The coupling inverts its adjoint on the dilated packet class. -/
theorem tendsto_norm_soninApertureCoupling_adjoint_soninDilatedPacket_sub
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n)
    (hsq : ∀ n, 0 < r n ^ (2 : ℕ)) (hcr : ∀ n, c ≤ r n * a) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
            (ContinuousLinearMap.adjoint
              (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n))
              (soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n))) -
          soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖)
      atTop (𝓝 0) := by
  have hforward := tendsto_norm_soninApertureCoupling_soninPacketEven_sub a b c ha hb hab hbc q
    haq hqb r hrpos hrgt hcr hr
  have hback := tendsto_norm_adjoint_soninApertureCoupling_soninDilatedPacket_sub a b c ha hb
    hbc q haq hqb r hrpos hrgt hsq hr
  have hmaj : Tendsto (fun n : ℕ =>
      2 * ‖ContinuousLinearMap.adjoint
              (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n))
              (soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)) -
            soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))‖ +
        ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
            (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))) -
          soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖)
      atTop (𝓝 0) := by
    simpa using (hback.const_mul (2 : ℝ)).add hforward
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hmaj
  set w : evenSubspace := soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)) with hw
  set v : evenSubspace :=
    soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n) with hv
  set Z := evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) with hZ
  have hsplit : Z (ContinuousLinearMap.adjoint Z v) - v =
      Z (ContinuousLinearMap.adjoint Z v - w) + (Z w - v) := by
    rw [map_sub]
    abel
  rw [hsplit]
  calc ‖Z (ContinuousLinearMap.adjoint Z v - w) + (Z w - v)‖
      ≤ ‖Z (ContinuousLinearMap.adjoint Z v - w)‖ + ‖Z w - v‖ := norm_add_le _ _
    _ ≤ 2 * ‖ContinuousLinearMap.adjoint Z v - w‖ + ‖Z w - v‖ := by
        gcongr
        exact norm_evenSoninApertureSuccessiveLayerTransition_apply_le hab.le hbc.le
          (hrgt n) _

end RHTower
