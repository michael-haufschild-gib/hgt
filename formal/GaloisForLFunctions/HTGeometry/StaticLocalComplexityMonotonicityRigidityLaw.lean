import GaloisForLFunctions.HTGeometry.StaticLocalNestedThermodynamicRampReturnLaw

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal
open Matrix Set

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-- Any monotone map into an ordered space with a least element collapses on an interval if its
right endpoint is the least element. -/
theorem eq_bot_on_Icc_of_monotoneOn_of_right_eq_bot
    {α β : Type*} [Preorder α] [PartialOrder β] [OrderBot β]
    (f : α → β) {a b : α} (hab : a ≤ b)
    (hmono : MonotoneOn f (Icc a b)) (hb : f b = ⊥) :
    ∀ x ∈ Icc a b, f x = ⊥ := by
  intro x hx
  apply bot_unique
  rw [← hb]
  exact hmono hx (right_mem_Icc.mpr hab) hx.2

/-- Dual endpoint rigidity for an antitone map whose left endpoint is least. -/
theorem eq_bot_on_Icc_of_antitoneOn_of_left_eq_bot
    {α β : Type*} [Preorder α] [PartialOrder β] [OrderBot β]
    (f : α → β) {a b : α} (hab : a ≤ b)
    (hanti : AntitoneOn f (Icc a b)) (ha : f a = ⊥) :
    ∀ x ∈ Icc a b, f x = ⊥ := by
  intro x hx
  apply bot_unique
  rw [← ha]
  exact hanti (left_mem_Icc.mpr hab) hx hx.1

/-- The empty circuit certifies zero two-qubit complexity at the exact return. -/
theorem nestedOperatorTwoGateComplexity_return_eq_zero
    (L : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    nestedOperatorTwoGateComplexity L ε (nestedInversePowerReturnPeriod L) = 0 := by
  apply le_antisymm
  · apply nestedOperatorTwoGateComplexity_le_of_circuit (c := [])
    unfold NestedOperatorApproximates
    rw [nestedInversePowerChain_exact_return]
    simp [circuitMatrix, hε]
  · exact bot_le

/-- The empty circuit also certifies zero complexity at time zero. -/
theorem nestedOperatorTwoGateComplexity_zero_eq_zero
    (L : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    nestedOperatorTwoGateComplexity L ε 0 = 0 := by
  have href := nestedOperatorTwoGateComplexity_exact_return_reflect L ε 0
  rw [sub_zero, nestedOperatorTwoGateComplexity_return_eq_zero L hε] at href
  exact href.symm

theorem nestedInversePowerReturnPeriod_nonneg (L : ℕ) :
    0 ≤ nestedInversePowerReturnPeriod L := by
  unfold nestedInversePowerReturnPeriod
  positivity

/-- Exact-return rigidity for the actual, discontinuous circuit complexity: global monotonicity
on a return cycle is possible only for the identically-zero history. -/
theorem nestedOperatorTwoGateComplexity_eq_zero_of_cycle_monotone
    (L : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hmono : MonotoneOn (nestedOperatorTwoGateComplexity L ε)
      (Icc 0 (nestedInversePowerReturnPeriod L))) :
    ∀ t ∈ Icc 0 (nestedInversePowerReturnPeriod L),
      nestedOperatorTwoGateComplexity L ε t = 0 := by
  exact eq_bot_on_Icc_of_monotoneOn_of_right_eq_bot
    (nestedOperatorTwoGateComplexity L ε)
    (nestedInversePowerReturnPeriod_nonneg L) hmono
    (nestedOperatorTwoGateComplexity_return_eq_zero L hε)

/-- Global antitonicity on a return cycle also forces the complexity history to vanish. -/
theorem nestedOperatorTwoGateComplexity_eq_zero_of_cycle_antitone
    (L : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hanti : AntitoneOn (nestedOperatorTwoGateComplexity L ε)
      (Icc 0 (nestedInversePowerReturnPeriod L))) :
    ∀ t ∈ Icc 0 (nestedInversePowerReturnPeriod L),
      nestedOperatorTwoGateComplexity L ε t = 0 := by
  exact eq_bot_on_Icc_of_antitoneOn_of_left_eq_bot
    (nestedOperatorTwoGateComplexity L ε)
    (nestedInversePowerReturnPeriod_nonneg L) hanti
    (nestedOperatorTwoGateComplexity_zero_eq_zero L hε)

/-- Every time in the laboratory ramp precedes the factorial-four exact return. -/
theorem laboratory_time_le_nestedInversePowerReturnPeriod
    {L : ℕ} {t ε : ℝ} (hε : 0 < ε) (hεmax : ε ≤ 1 / 100)
    (htLab : t ≤ ε * L / 2) :
    t ≤ nestedInversePowerReturnPeriod L := by
  have hmul : ε * (L : ℝ) ≤ (1 / 100 : ℝ) * L :=
    mul_le_mul_of_nonneg_right hεmax (by positivity)
  have htL : t ≤ (L : ℝ) / 200 := by linarith
  have hfacNat : L ≤ L.factorial := Nat.self_le_factorial L
  have hfac : (L : ℝ) ≤ (L.factorial : ℝ) := by exact_mod_cast hfacNat
  have hfac1 : (1 : ℝ) ≤ (L.factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_pos L)
  have hpow : (L : ℝ) ≤ (L.factorial : ℝ) ^ 4 := by
    calc
      (L : ℝ) ≤ (L.factorial : ℝ) := hfac
      _ ≤ (L.factorial : ℝ) ^ 4 := by nlinarith [sq_nonneg ((L.factorial : ℝ) ^ 2 - 1)]
  have hcoef : (1 / 200 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  calc
    t ≤ (L : ℝ) / 200 := htL
    _ ≤ (2 * Real.pi) * L := by
      simpa [div_eq_mul_inv, mul_comm] using
        (mul_le_mul_of_nonneg_right hcoef (show 0 ≤ (L : ℝ) by positivity))
    _ ≤ (2 * Real.pi) * (L.factorial : ℝ) ^ 4 := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = nestedInversePowerReturnPeriod L := by
      simp [nestedInversePowerReturnPeriod, mul_assoc]

/-- The laboratory ramp is nontrivial: its actual complexity is at least eight. -/
theorem eight_le_nestedOperatorTwoGateComplexity_of_laboratory_time
    {L : ℕ} {t ε : ℝ} (hε : 0 < ε) (hεmax : ε ≤ 1 / 100)
    (htMin : 1024 * Real.pi * ε ≤ t) (htLab : t ≤ ε * L / 2) :
    (8 : ℕ∞) ≤ nestedOperatorTwoGateComplexity L ε t := by
  have hb := (nestedOperatorComplexity_floor_twoCeil hε hεmax htMin htLab).1
  have hden : 0 < 128 * Real.pi * ε := by positivity
  have hratio : (8 : ℝ) ≤ t / (128 * Real.pi * ε) := by
    rw [le_div_iff₀ hden]
    nlinarith [htMin]
  have hfloor : (8 : ℕ) ≤ ⌊t / (128 * Real.pi * ε)⌋₊ :=
    Nat.le_floor (by exact_mod_cast hratio)
  exact le_trans (by exact_mod_cast hfloor) hb

/-- A nontrivial laboratory ramp rules out literal global monotonicity over the return cycle. -/
theorem nestedOperatorTwoGateComplexity_not_monotoneOn_returnCycle
    {L : ℕ} {t ε : ℝ} (hε : 0 < ε) (hεmax : ε ≤ 1 / 100)
    (htMin : 1024 * Real.pi * ε ≤ t) (htLab : t ≤ ε * L / 2) :
    ¬ MonotoneOn (nestedOperatorTwoGateComplexity L ε)
      (Icc 0 (nestedInversePowerReturnPeriod L)) := by
  intro hmono
  have ht0 : 0 ≤ t := le_trans (by positivity) htMin
  have htR := laboratory_time_le_nestedInversePowerReturnPeriod hε hεmax htLab
  have hzero := nestedOperatorTwoGateComplexity_eq_zero_of_cycle_monotone
    L hε.le hmono t ⟨ht0, htR⟩
  have heighth := eight_le_nestedOperatorTwoGateComplexity_of_laboratory_time
    hε hεmax htMin htLab
  rw [hzero] at heighth
  norm_num at heighth

/-- A nontrivial laboratory ramp also rules out literal global antitonicity. -/
theorem nestedOperatorTwoGateComplexity_not_antitoneOn_returnCycle
    {L : ℕ} {t ε : ℝ} (hε : 0 < ε) (hεmax : ε ≤ 1 / 100)
    (htMin : 1024 * Real.pi * ε ≤ t) (htLab : t ≤ ε * L / 2) :
    ¬ AntitoneOn (nestedOperatorTwoGateComplexity L ε)
      (Icc 0 (nestedInversePowerReturnPeriod L)) := by
  intro hanti
  have ht0 : 0 ≤ t := le_trans (by positivity) htMin
  have htR := laboratory_time_le_nestedInversePowerReturnPeriod hε hεmax htLab
  have hzero := nestedOperatorTwoGateComplexity_eq_zero_of_cycle_antitone
    L hε.le hanti t ⟨ht0, htR⟩
  have heighth := eight_le_nestedOperatorTwoGateComplexity_of_laboratory_time
    hε hεmax htMin htLab
  rw [hzero] at heighth
  norm_num at heighth

/-- The exact circuit-complexity history has a literal positive excursion: it rises strictly from
zero to every laboratory-ramp point and later falls strictly back to zero at the exact return. -/
theorem nestedOperatorTwoGateComplexity_literal_rise_and_return_drop
    {L : ℕ} {t ε : ℝ} (hε : 0 < ε) (hεmax : ε ≤ 1 / 100)
    (htMin : 1024 * Real.pi * ε ≤ t) (htLab : t ≤ ε * L / 2) :
    0 < t ∧ t < nestedInversePowerReturnPeriod L ∧
      nestedOperatorTwoGateComplexity L ε 0 <
        nestedOperatorTwoGateComplexity L ε t ∧
      nestedOperatorTwoGateComplexity L ε (nestedInversePowerReturnPeriod L) <
        nestedOperatorTwoGateComplexity L ε t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) htMin
  have htRle := laboratory_time_le_nestedInversePowerReturnPeriod hε hεmax htLab
  have heighth := eight_le_nestedOperatorTwoGateComplexity_of_laboratory_time
    hε hεmax htMin htLab
  have hcomplexityPos : 0 < nestedOperatorTwoGateComplexity L ε t :=
    lt_of_lt_of_le (by norm_num) heighth
  have hzero := nestedOperatorTwoGateComplexity_zero_eq_zero L hε.le
  have hreturn := nestedOperatorTwoGateComplexity_return_eq_zero L hε.le
  have htR : t < nestedInversePowerReturnPeriod L := by
    apply lt_of_le_of_ne htRle
    intro heq
    rw [heq, hreturn] at hcomplexityPos
    exact (lt_irrefl 0 hcomplexityPos)
  exact ⟨ht0, htR, by simpa [hzero], by simpa [hreturn]⟩

/-- Scale-separated literal comparison inside the laboratory window.  This compares the actual
infimal circuit complexities, not only their envelopes: once the later time is at least
`1024π` times the earlier time, its complexity cannot be smaller. -/
theorem nestedOperatorTwoGateComplexity_le_of_scaleSeparated
    {L : ℕ} {s t ε : ℝ} (hε : 0 < ε) (hεmax : ε ≤ 1 / 100)
    (hsMin : 1024 * Real.pi * ε ≤ s) (hsLab : s ≤ ε * L / 2)
    (htMin : 1024 * Real.pi * ε ≤ t) (htLab : t ≤ ε * L / 2)
    (hsep : 1024 * Real.pi * s ≤ t) :
    nestedOperatorTwoGateComplexity L ε s ≤
      nestedOperatorTwoGateComplexity L ε t := by
  have hsBound := nestedOperatorComplexity_floor_twoCeil hε hεmax hsMin hsLab
  have htBound := nestedOperatorComplexity_floor_twoCeil hε hεmax htMin htLab
  have hden : 0 < 128 * Real.pi * ε := by positivity
  have hs0 : 0 ≤ 2 * s / ε := by
    have hspos : 0 < s := lt_of_lt_of_le (by positivity) hsMin
    positivity
  have hceil := Nat.ceil_lt_add_one hs0
  have hceilCast :
      (((2 * ⌈2 * s / ε⌉₊ : ℕ) : ℕ) : ℝ) < 4 * s / ε + 2 := by
    calc
      (((2 * ⌈2 * s / ε⌉₊ : ℕ) : ℕ) : ℝ) =
          2 * (⌈2 * s / ε⌉₊ : ℝ) := by push_cast; ring
      _ < 2 * (2 * s / ε + 1) :=
        mul_lt_mul_of_pos_left hceil (by norm_num)
      _ = 4 * s / ε + 2 := by ring
  have hsRatio : 1 ≤ s / ε := by
    rw [le_div_iff₀ hε]
    have hscale : 1 ≤ 1024 * Real.pi := by nlinarith [Real.pi_gt_three]
    have := mul_le_mul_of_nonneg_right hscale hε.le
    linarith
  have hfour : (4 : ℝ) ≤ 4 * (s / ε) :=
    by simpa using
      (mul_le_mul_of_nonneg_left hsRatio (show (0 : ℝ) ≤ 4 by norm_num))
  have hupperRatio : 4 * s / ε + 2 ≤ 8 * s / ε := by
    rw [show 4 * s / ε = 4 * (s / ε) by ring,
      show 8 * s / ε = 8 * (s / ε) by ring]
    linarith
  have hsepRatio : 8 * s / ε ≤ t / (128 * Real.pi * ε) := by
    rw [le_div_iff₀ hden]
    calc
      8 * s / ε * (128 * Real.pi * ε) = 1024 * Real.pi * s := by
        field_simp
        ring
      _ ≤ t := hsep
  have hNat : 2 * ⌈2 * s / ε⌉₊ ≤ ⌊t / (128 * Real.pi * ε)⌋₊ := by
    apply Nat.le_floor
    exact le_of_lt (lt_of_lt_of_le hceilCast (hupperRatio.trans hsepRatio))
  exact hsBound.2.trans (le_trans (by exact_mod_cast hNat) htBound.1)

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
