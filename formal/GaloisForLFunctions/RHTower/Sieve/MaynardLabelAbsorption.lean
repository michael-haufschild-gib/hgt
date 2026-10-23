import GaloisForLFunctions.RHTower.Sieve.MaynardFibreCount

/-!
# Absorbing dyadic selection labels

The degree-sixty label count costs a fixed multiple of `(log T)^120`.
Absorbing this factor into `T^(1/100)` gives the global cardinality bound.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

theorem natLogTwo_add_one_cast_le
    {N : ℕ} (hN : 1 ≤ N) :
    ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ 1 + 2 * Real.log N := by
  have hpowNat : 2 ^ Nat.log 2 N ≤ N :=
    Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  have hpow : (((2 ^ Nat.log 2 N : ℕ) : ℝ)) ≤ (N : ℝ) := by
    exact_mod_cast hpowNat
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Nat.cast_pow, Real.log_pow] at hlog
  have hlog2 := Real.log_two_gt_d9
  have hlog2half : (1 / 2 : ℝ) ≤ Real.log 2 := by
    exact (show (1 / 2 : ℝ) < 0.6931471803 by norm_num).trans hlog2 |>.le
  have hq0 : 0 ≤ ((Nat.log 2 N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hhalf : ((Nat.log 2 N : ℕ) : ℝ) / 2 ≤
      (Nat.log 2 N : ℝ) * Real.log 2 := by
    linarith [mul_le_mul_of_nonneg_left hlog2half hq0]
  norm_num at hlog
  have hqhalf : ((Nat.log 2 N : ℕ) : ℝ) / 2 ≤ Real.log N :=
    hhalf.trans hlog
  have hq : ((Nat.log 2 N : ℕ) : ℝ) ≤ 2 * Real.log N := by
    linarith
  push_cast
  linarith

theorem heathBrownSelectionLabel_sixty_polylog_bound
    {T mu t : ℝ} (hT : 0 < T) (hlogT : 1 ≤ Real.log T)
    (hmu : mu ≤ 19 / 9) (ht : t = mu / 120)
    {X L : ℕ} (hX : 1 ≤ X) (hL : 1 ≤ L)
    (hXscale : (X : ℝ) ≤ T ^ mu) (hLscale : (L : ℝ) ≤ T ^ (2 * t)) :
    (Fintype.card (HeathBrownSelectionLabel L X 60) : ℝ) ≤
      (60 : ℝ) * (2 : ℝ) ^ 120 * (6 : ℝ) ^ 60 * (2 : ℝ) ^ 60 *
        (Real.log T) ^ 120 := by
  have hlogT0 : 0 ≤ Real.log T := by linarith
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hTmuPos : 0 < T ^ mu := Real.rpow_pos_of_pos hT _
  have hlogX : Real.log X ≤ mu * Real.log T := by
    have h := Real.log_le_log hXpos hXscale
    rwa [Real.log_rpow hT] at h
  have hXlog : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ 6 * Real.log T := by
    have hnat := natLogTwo_add_one_cast_le hX
    have hmumul : mu * Real.log T ≤ (19 / 9 : ℝ) * Real.log T :=
      mul_le_mul_of_nonneg_right hmu hlogT0
    linarith
  have htwice : 2 * t = mu / 60 := by rw [ht]; ring
  have hlogL : Real.log L ≤ (mu / 60) * Real.log T := by
    have h := Real.log_le_log hLpos hLscale
    rw [Real.log_rpow hT, htwice] at h
    exact h
  have hLlog : ((Nat.log 2 L + 1 : ℕ) : ℝ) ≤ 2 * Real.log T := by
    have hnat := natLogTwo_add_one_cast_le hL
    have hmudiv : (mu / 60) * Real.log T ≤ (19 / 540 : ℝ) * Real.log T := by
      have hmudiv' : mu / 60 ≤ (19 / 540 : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_right hmudiv' hlogT0
    linarith
  have hcardNat := card_heathBrownSelectionLabel_sixty_le L X
  have hcard : (Fintype.card (HeathBrownSelectionLabel L X 60) : ℝ) ≤
      (60 : ℝ) * ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60 *
        ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 60 * (2 : ℝ) ^ 120 := by
    exact_mod_cast hcardNat
  have hXpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hXlog 60
  have hLpow := pow_le_pow_left₀ (Nat.cast_nonneg _) hLlog 60
  have hprod :
      ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60 *
          ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 60 ≤
        (6 * Real.log T) ^ 60 * (2 * Real.log T) ^ 60 := by
    calc
      ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60 *
            ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 60 ≤
          (6 * Real.log T) ^ 60 *
            ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 60 :=
        mul_le_mul_of_nonneg_right hXpow
          (pow_nonneg (Nat.cast_nonneg _) 60)
      _ ≤ (6 * Real.log T) ^ 60 * (2 * Real.log T) ^ 60 :=
        mul_le_mul_of_nonneg_left hLpow
          (pow_nonneg (mul_nonneg (by norm_num) hlogT0) 60)
  calc
    (Fintype.card (HeathBrownSelectionLabel L X 60) : ℝ) ≤
        (60 : ℝ) * ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60 *
          ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 60 * (2 : ℝ) ^ 120 := hcard
    _ ≤ (60 : ℝ) * (6 * Real.log T) ^ 60 *
          (2 * Real.log T) ^ 60 * (2 : ℝ) ^ 120 := by
      calc
        (60 : ℝ) * ((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60 *
              ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 60 * (2 : ℝ) ^ 120 =
            ((60 : ℝ) * (2 : ℝ) ^ 120) *
              (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60 *
                ((Nat.log 2 L + 1 : ℕ) : ℝ) ^ 60) := by ring
        _ ≤ ((60 : ℝ) * (2 : ℝ) ^ 120) *
              ((6 * Real.log T) ^ 60 * (2 * Real.log T) ^ 60) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = (60 : ℝ) * (6 * Real.log T) ^ 60 *
              (2 * Real.log T) ^ 60 * (2 : ℝ) ^ 120 := by ring
    _ = (60 : ℝ) * (2 : ℝ) ^ 120 * (6 : ℝ) ^ 60 * (2 : ℝ) ^ 60 *
          (Real.log T) ^ 120 := by ring

def maynardLabelPolylogConstant : ℝ :=
  (60 : ℝ) * (2 : ℝ) ^ 120 * (6 : ℝ) ^ 60 * (2 : ℝ) ^ 60

def maynardCountingPolylogConstant : ℝ :=
  2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant *
    maynardLabelPolylogConstant

theorem maynardCountingPolylogConstant_pos :
    0 < maynardCountingPolylogConstant := by
  dsimp only [maynardCountingPolylogConstant, maynardLabelPolylogConstant]
  exact mul_pos
    (mul_pos
      (mul_pos (by norm_num) (pow_pos (by norm_num) 2))
      maynardUniformEnergyConstant_pos)
    (mul_pos
      (mul_pos
        (mul_pos (by norm_num) (pow_pos (by norm_num) 120))
        (pow_pos (by norm_num) 60))
      (pow_pos (by norm_num) 60))

theorem eventually_maynardCounting_polylog_absorbed :
    ∀ᶠ T : ℝ in Filter.atTop,
      1 ≤ Real.log T ∧
        maynardCountingPolylogConstant * (Real.log T) ^ 120 ≤
          T ^ (1 / 100 : ℝ) := by
  let C := maynardCountingPolylogConstant
  have hC : 0 < C := maynardCountingPolylogConstant_pos
  have heps : (0 : ℝ) < 1 / 100 := by norm_num
  have hlo := (_root_.isLittleO_log_rpow_rpow_atTop 120 heps).def
    (show (0 : ℝ) < 1 / (2 * C) by positivity)
  filter_upwards [hlo, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_gt_atTop (0 : ℝ)] with T hsmall hlogT hT
  have hlog0 : 0 ≤ Real.log T := by linarith
  have hTpow : 0 < T ^ (1 / 100 : ℝ) := Real.rpow_pos_of_pos hT _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ Real.log T ^ (120 : ℝ)),
    abs_of_nonneg hTpow.le] at hsmall
  have hlogpow : Real.log T ^ (120 : ℝ) = Real.log T ^ (120 : ℕ) :=
    Real.rpow_natCast _ _
  rw [hlogpow] at hsmall
  have hscaled := mul_le_mul_of_nonneg_left hsmall hC.le
  have hcancel : C * (1 / (2 * C)) = 1 / 2 := by
    field_simp [hC.ne']
  rw [← mul_assoc, hcancel] at hscaled
  have hhalfT : (1 / 2 : ℝ) * T ^ (1 / 100 : ℝ) ≤
      T ^ (1 / 100 : ℝ) := by
    linarith only [hTpow]
  refine ⟨hlogT, ?_⟩
  change C * Real.log T ^ 120 ≤ T ^ (1 / 100 : ℝ)
  exact hscaled.trans hhalfT

def IsMaynardRouteTCountingReady (T : ℝ) : Prop :=
  IsMaynardRouteTScaleReady T ∧
  1 ≤ Real.log T ∧
  maynardCountingPolylogConstant * (Real.log T) ^ 120 ≤ T ^ (1 / 100 : ℝ)

theorem eventually_isMaynardRouteTCountingReady :
    ∀ᶠ T : ℝ in Filter.atTop, IsMaynardRouteTCountingReady T := by
  filter_upwards [eventually_isMaynardRouteTScaleReady,
    eventually_maynardCounting_polylog_absorbed] with T hroute hcount
  exact ⟨hroute, hcount⟩

/-- **Canonical degree-`60` counting costs only a tiny power.**  Once the fixed label
multiplicity is absorbed into `T0^(1/100)`, the complete large-ordinate set has exponent
`2231/86400`; there is no residual color-count obstruction. -/
theorem exists_canonical_sixty_power_card_bound_of_counting_ready
    {X K : ℕ} {T0 t mu sigma V delta : ℝ}
    (hready : IsMaynardRouteTCountingReady T0)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (hX : 1 ≤ X) (hXscale : (X : ℝ) ≤ T0 ^ mu)
    (hsigma : 1 / 2 ≤ sigma) (hV : 0 < V) (hdelta : 0 < delta)
    (S : Finset ℕ) (hS : S ⊆ Finset.range K) (lam : ℕ → ℝ)
    (hband : ∀ r ∈ S, T0 ≤ lam r ∧ lam r ≤ 2 * T0)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T0)
    (haggregate : ∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
      ∀ r ∈ S, V ≤ ‖heathBrownEligibleDyadicAggregate L X 60 T0 t
        ((sigma : ℂ) + (lam r : ℝ) * Complex.I)‖)
    (hreserve : ∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
      ∀ c : HeathBrownBoxChoice L X 60,
        IsHeathBrownBoxEligible L X 60 T0 t c →
          heathBrownEligibleBoxCost L X 60 *
            (groupedDyadicLower
              (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ (1 - sigma) ≤ V) :
    ∃ L : ℕ, 1 ≤ L ∧ X < (L + 1) ^ 60 ∧ (L : ℝ) ≤ T0 ^ (2 * t) ∧
      (S.card : ℝ) ≤
        maynardHarmonicFactor K delta * T0 ^ (2231 / 86400 : ℝ) := by
  obtain ⟨L, hL, hXL, hcut, hcard⟩ :=
    exists_canonical_sixty_global_card_bound_of_ready_scale
      hready.1 hmu_lo hmu_hi ht hX hXscale hsigma hV hdelta
        S hS lam hband hgap hdiam haggregate hreserve
  refine ⟨L, hL, hXL, hcut, ?_⟩
  have hT0 : 0 < T0 := by linarith [hready.1.1.1]
  have hlabel := heathBrownSelectionLabel_sixty_polylog_bound
    hT0 hready.2.1 hmu_hi ht hX hL hXscale hcut
  let E : ℝ := 2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant
  let A : ℝ := maynardLabelPolylogConstant
  let HF : ℝ := maynardHarmonicFactor K delta
  have hE : 0 < E := by
    dsimp only [E]
    exact mul_pos
      (mul_pos (by norm_num) (pow_pos (by norm_num) 2))
      maynardUniformEnergyConstant_pos
  have hHF : 0 < HF := maynardHarmonicFactor_pos K hdelta
  have hlabel' :
      (Fintype.card (HeathBrownSelectionLabel L X 60) : ℝ) ≤
        A * Real.log T0 ^ 120 := by
    simpa only [A, maynardLabelPolylogConstant] using hlabel
  have hcoeff :
      (Fintype.card (HeathBrownSelectionLabel L X 60) : ℝ) * E ≤
        T0 ^ (1 / 100 : ℝ) := by
    calc
      (Fintype.card (HeathBrownSelectionLabel L X 60) : ℝ) * E ≤
          (A * Real.log T0 ^ 120) * E :=
        mul_le_mul_of_nonneg_right hlabel' hE.le
      _ = maynardCountingPolylogConstant * Real.log T0 ^ 120 := by
        dsimp only [E, A, maynardCountingPolylogConstant]
        ring
      _ ≤ T0 ^ (1 / 100 : ℝ) := hready.2.2
  have hrest : 0 ≤ HF * T0 ^ (1367 / 86400 : ℝ) :=
    mul_nonneg hHF.le (Real.rpow_nonneg hT0.le _)
  have hcard' : (S.card : ℝ) ≤
      ((Fintype.card (HeathBrownSelectionLabel L X 60) : ℝ) * E) *
        (HF * T0 ^ (1367 / 86400 : ℝ)) := by
    calc
      (S.card : ℝ) ≤
          (Fintype.card (HeathBrownSelectionLabel L X 60) : ℝ) *
            (2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant *
              maynardHarmonicFactor K delta *
                T0 ^ (1367 / 86400 : ℝ)) := hcard
      _ = ((Fintype.card (HeathBrownSelectionLabel L X 60) : ℝ) * E) *
            (HF * T0 ^ (1367 / 86400 : ℝ)) := by
        dsimp only [E, HF]
        ring
  calc
    (S.card : ℝ) ≤
        ((Fintype.card (HeathBrownSelectionLabel L X 60) : ℝ) * E) *
          (HF * T0 ^ (1367 / 86400 : ℝ)) := hcard'
    _ ≤ T0 ^ (1 / 100 : ℝ) *
          (HF * T0 ^ (1367 / 86400 : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoeff hrest
    _ = HF * T0 ^ (2231 / 86400 : ℝ) := by
      rw [show (2231 / 86400 : ℝ) = 1 / 100 + 1367 / 86400 by norm_num,
        Real.rpow_add hT0]
      ring
    _ = maynardHarmonicFactor K delta *
          T0 ^ (2231 / 86400 : ℝ) := rfl

end RHTower.Sieve
