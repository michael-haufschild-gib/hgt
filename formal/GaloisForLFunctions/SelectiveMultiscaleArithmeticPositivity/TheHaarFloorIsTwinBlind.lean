import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellEffectivity
import GaloisForLFunctions.ArithmeticElectrostatics.TheGaugeIsInvisibleAtAtomicResolution
import GaloisForLFunctions.ArithmeticLorentzianGeometry.HyperbolicityIsBlindTheSignIsNot

/-!
# The Haar floor is twin-blind

On balanced complete-cell sections above one fixed arithmetic index, the full signed Weil form of
`ζ` has a unit floor uniformly in the upper horizon (ArithmeticCastelnuovoSeveri). The prime part of
that floor is a row-and-column estimate of a nonnegative matrix: it never uses the sign of a prime
term. This file proves the floor for every twist `ωΛ` with `|ω| ≤ 1`, with the *same* lower index.

* **The twisted prime sum of a Haar section** (`twistedPrimeSum_haarSectionProfile`): it is the
  quadratic form of the matrix `Σ_m ω(m) e_m(a, b)`, the entries `e_m` of `ζ`'s prime matrix
  weighted by the twist.
* **The prime bound is twin-blind** (`twistedPrimeSum_haarSectionProfile_le`): for `|ω| ≤ 1` the
  twisted prime charge obeys `ζ`'s bound `Σ_a (16 + log(2a+1)/√2) h_a c_a²`.
* **The floor is twin-blind** (`haarSectionProfile_roughWeilTw_ge`,
  `exists_haarTail_roughWeilTw_floor`): one lower index `A` gives
  `W_ω(f_c) ≥ Σ_a h_a c_a²` on every high signed section, for every such twist at once
  (`liouville_haarTail_roughWeilTw_floor` for the Liouville twin).

The Liouville twin is not Weil-positive and fails on atomic families at every root
(`PositivityAtEveryRootSelectsTheVonMangoldtWeight`). The high-detail floor holds for it all the
same, so the floor carries no selective information: a complete-source positivity proof must pay the
coarse and low-index residual with an input that distinguishes `Λ` from its twins.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
  GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.ArithmeticLorentzianGeometry

/-- The full signed form of the twist `ωΛ`, evaluated directly on a compact BV source. -/
def roughWeilTw (ω : ArithmeticFunction ℝ) (f : ℝ → ℝ) : ℝ :=
  2 * gammaHardyPhaseRate 0 * (∫ x, f x ^ 2) + levyEnergy f - twistedPrimeSum ω f +
    (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2)

/-- The two Hecke pairings of a real function coincide. -/
theorem pairing_eq_two_mul (f : ℝ → ℝ) (L : ℝ) :
    (∫ t, f t * f (t - L)) + ∫ t, f t * f (t + L) = 2 * ∫ t, f t * f (t + L) := by
  have h := integral_sub_right_eq_self (μ := volume) (fun t => f (t + L) * f t) L
  simp only [sub_add_cancel] at h
  have h' : (∫ t, f t * f (t - L)) = ∫ t, f t * f (t + L) :=
    h.trans (integral_congr_ae (Filter.Eventually.of_forall fun t => mul_comm _ _))
  rw [h']
  ring

/-- **The twisted prime sum of a balanced section** is the quadratic form of the twisted prime
matrix `Σ_m ω(m) e_m(a, b)`. -/
theorem twistedPrimeSum_haarSectionProfile (ω : ArithmeticFunction ℝ) (c : ℕ → ℝ) (X : ℕ) :
    twistedPrimeSum ω (haarSectionProfile c X) =
      ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        2 * (∑ m ∈ Icc 2 (2 * X + 1), ω m * haarPrimeEntry a b m) * c a * c b := by
  classical
  unfold twistedPrimeSum
  rw [tsum_eq_sum (s := Icc 2 (2 * X + 1))]
  · simp_rw [pairing_eq_two_mul, ← inner_shift_haarSectionProfile]
    calc ∑ m ∈ Icc 2 (2 * X + 1), ω m * vonMangoldtAtom m *
          (2 * (inner ℂ (halfLineRightShift (Real.log m) (haarSection c X)) (haarSection c X)).re)
        = ∑ m ∈ Icc 2 (2 * X + 1), ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
            2 * (ω m * haarPrimeEntry a b m) * c a * c b := by
          refine sum_congr rfl fun m hm => ?_
          have hm2 := (mem_Icc.mp hm).1
          rw [inner_shift_haarSection c c X hm2, vonMangoldtAtom, if_pos hm2, mul_sum, mul_sum]
          refine sum_congr rfl fun a _ => ?_
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun b _ => ?_
          unfold haarPrimeEntry
          split_ifs <;> ring
      _ = _ := by
          rw [sum_comm]
          refine sum_congr rfl fun a _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun b _ => ?_
          rw [mul_sum, sum_mul, sum_mul]
  · intro m hm
    by_cases hm2 : 2 ≤ m
    · have hmX : 2 * X + 1 < m := by simp only [mem_Icc] at hm; omega
      rw [pairing_eq_two_mul, ← inner_shift_haarSectionProfile,
        inner_shift_haarSection_eq_zero c c X hmX]
      ring
    · simp [vonMangoldtAtom, hm2]

/-- **The prime bound is twin-blind**: every twist with `|ω| ≤ 1` has the prime charge bound of
`ζ` on balanced sections. -/
theorem twistedPrimeSum_haarSectionProfile_le {ω : ArithmeticFunction ℝ} (hω : ∀ m, |ω m| ≤ 1)
    (c : ℕ → ℝ) (X : ℕ) :
    twistedPrimeSum ω (haarSectionProfile c X) ≤ ∑ a ∈ Icc 1 X,
      (16 + Real.log ((2 * a + 1 : ℕ) : ℝ) / Real.sqrt 2) * haarMass a * c a ^ 2 := by
  rw [twistedPrimeSum_haarSectionProfile]
  set K := haarPrimeMatrix (2 * X + 1)
  -- the twisted entries are dominated by the actual nonnegative matrix
  have hK : ∀ a ∈ Icc 1 X, ∀ b ∈ Icc 1 X,
      |∑ m ∈ Icc 2 (2 * X + 1), ω m * haarPrimeEntry a b m| ≤ K a b := by
    intro a _ b hb
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => ?_)
    have he := haarPrimeEntry_nonneg a m (mem_Icc.mp hb).1
    rw [abs_mul, abs_of_nonneg he]
    exact mul_le_of_le_one_left he (hω m)
  calc ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        2 * (∑ m ∈ Icc 2 (2 * X + 1), ω m * haarPrimeEntry a b m) * c a * c b
      ≤ ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, (K a b * c a ^ 2 + K a b * c b ^ 2) := by
        refine sum_le_sum fun a ha => sum_le_sum fun b hb => ?_
        have h := abs_le.mp (hK a ha b hb)
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ K a b + ∑ m ∈ Icc 2 (2 * X + 1),
            ω m * haarPrimeEntry a b m) (sq_nonneg (c a - c b)),
          mul_nonneg (by linarith : (0 : ℝ) ≤ K a b - ∑ m ∈ Icc 2 (2 * X + 1),
            ω m * haarPrimeEntry a b m) (sq_nonneg (c a + c b))]
    _ = (∑ a ∈ Icc 1 X, (∑ b ∈ Icc 1 X, K a b) * c a ^ 2) +
        ∑ b ∈ Icc 1 X, (∑ a ∈ Icc 1 X, K a b) * c b ^ 2 := by
        simp only [sum_add_distrib]
        congr 1
        · simp only [sum_mul]
        · rw [sum_comm]
          simp only [sum_mul]
    _ = ∑ a ∈ Icc 1 X, ((∑ b ∈ Icc 1 X, K a b) + (∑ b ∈ Icc 1 X, K b a)) * c a ^ 2 := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun a _ => by ring
    _ ≤ _ := by
        refine sum_le_sum fun a ha => ?_
        have ha1 := (mem_Icc.mp ha).1
        have h' : (∑ b ∈ Icc 1 X, K a b) + (∑ b ∈ Icc 1 X, K b a) ≤
            (16 + Real.log ((2 * a + 1 : ℕ) : ℝ) / Real.sqrt 2) * haarMass a :=
          (add_le_add (haarPrimeMatrix_row_le ha1 X (2 * X + 1))
            (haarPrimeMatrix_column_le ha1 X (2 * X + 1))).trans_eq (by ring)
        exact mul_le_mul_of_nonneg_right h' (sq_nonneg _)

theorem log_two_mul_add_one_le {a : ℕ} (ha : 1 ≤ a) :
    Real.log ((2 * a + 1 : ℕ) : ℝ) ≤ Real.log (a : ℝ) + 2 := by
  have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have ho : (0 : ℝ) < ((2 * a + 1 : ℕ) : ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos ho ha0)
  rw [Real.log_div ho.ne' ha0.ne'] at h
  have hd : ((2 * a + 1 : ℕ) : ℝ) / (a : ℝ) ≤ 3 := by
    rw [div_le_iff₀ ha0]
    exact_mod_cast (show 2 * a + 1 ≤ 3 * a by omega)
  linarith

/-- **The growing floor holds for every twist**: for `|ω| ≤ 1`,
`W_ω(f_c) ≥ Σ_a ((1 − 1/√2) log a + 2θ′(0) − 20) h_a c_a²` on every balanced section. -/
theorem haarSectionProfile_roughWeilTw_ge {ω : ArithmeticFunction ℝ} (hω : ∀ m, |ω m| ≤ 1)
    (c : ℕ → ℝ) (X : ℕ) :
    (∑ a ∈ Icc 1 X,
      ((1 - 1 / Real.sqrt 2) * Real.log (a : ℝ) + 2 * gammaHardyPhaseRate 0 - 20) *
        haarMass a * c a ^ 2) ≤ roughWeilTw ω (haarSectionProfile c X) := by
  have hgamma := haarSectionProfile_levyEnergy_ge c X
  have hprime := twistedPrimeSum_haarSectionProfile_le hω c X
  have hpole := haarSectionProfile_pole_ge c X
  -- the prime coefficient `16 + log(2a+1)/√2` is at most `18 + log a/√2`
  have hprime' : twistedPrimeSum ω (haarSectionProfile c X) ≤
      ∑ a ∈ Icc 1 X, (18 + Real.log (a : ℝ) / Real.sqrt 2) * haarMass a * c a ^ 2 := by
    refine hprime.trans (sum_le_sum fun a ha => ?_)
    have ha1 := (mem_Icc.mp ha).1
    have hd := div_le_div_of_nonneg_right (log_two_mul_add_one_le ha1) (Real.sqrt_nonneg 2)
    rw [add_div] at hd
    have htwo : (2 : ℝ) / Real.sqrt 2 ≤ 2 := by
      have := haarPrime_log_coefficient_lt_one.le
      calc (2 : ℝ) / Real.sqrt 2 = 2 * (1 / Real.sqrt 2) := by ring
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left this (by norm_num)
        _ = 2 := by ring
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith)
      (haarMass_pos ha1).le) (sq_nonneg _)
  have he (a : ℕ) :
      ((1 - 1 / Real.sqrt 2) * Real.log (a : ℝ) + 2 * gammaHardyPhaseRate 0 - 20) *
        haarMass a * c a ^ 2 =
      2 * gammaHardyPhaseRate 0 * (haarMass a * c a ^ 2) +
        Real.log (a : ℝ) * haarMass a * c a ^ 2 -
        (18 + Real.log (a : ℝ) / Real.sqrt 2) * haarMass a * c a ^ 2 -
        2 * (haarMass a * c a ^ 2) := by ring
  simp_rw [he, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  unfold roughWeilTw
  rw [integral_haarSectionProfile_sq]
  linarith

/-- **One lower index for every twist**: there is `A ≥ 1` such that for every twist `|ω| ≤ 1`,
every signed section supported at indices `a ≥ A` has `W_ω(f_c) ≥ Σ_a h_a c_a²`, for every horizon.
-/
theorem exists_haarTail_roughWeilTw_floor : ∃ A : ℕ, 1 ≤ A ∧ ∀ (ω : ArithmeticFunction ℝ),
    (∀ m, |ω m| ≤ 1) → ∀ (c : ℕ → ℝ) (X : ℕ),
      (∑ a ∈ Icc 1 X, haarMass a * haarTailCoeffs A c a ^ 2) ≤
        roughWeilTw ω (haarSectionProfile (haarTailCoeffs A c) X) := by
  let κ : ℝ := 1 - 1 / Real.sqrt 2
  have hκ : 0 < κ := sub_pos.mpr haarPrime_log_coefficient_lt_one
  let T : ℝ := (21 - 2 * gammaHardyPhaseRate 0) / κ
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp T)
  have hA1 : 1 ≤ A := by
    have hpos : (0 : ℝ) < A := (Real.exp_pos T).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hpos.ne')
  have hcoeff (a : ℕ) (ha : A ≤ a) :
      1 ≤ κ * Real.log (a : ℝ) + 2 * gammaHardyPhaseRate 0 - 20 := by
    have haR : (A : ℝ) ≤ a := by exact_mod_cast ha
    have hlog : T < Real.log (a : ℝ) := by
      have := Real.log_lt_log (Real.exp_pos T) (hA.trans_le haR)
      simpa only [Real.log_exp] using this
    have hmul := mul_le_mul_of_nonneg_left hlog.le hκ.le
    have he : κ * T = 21 - 2 * gammaHardyPhaseRate 0 := by
      dsimp only [T]
      field_simp [hκ.ne']
    linarith
  refine ⟨A, hA1, fun ω hω c X => ?_⟩
  refine le_trans ?_ (haarSectionProfile_roughWeilTw_ge hω (haarTailCoeffs A c) X)
  refine sum_le_sum fun a ha => ?_
  by_cases hAa : A ≤ a
  · have hnonneg : 0 ≤ haarMass a * haarTailCoeffs A c a ^ 2 :=
      mul_nonneg (haarMass_pos (mem_Icc.mp ha).1).le (sq_nonneg _)
    simpa only [κ, one_mul, mul_assoc] using mul_le_mul_of_nonneg_right (hcoeff a hAa) hnonneg
  · simp only [haarTailCoeffs, if_neg hAa, zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]

/-- The Liouville gauge is bounded by one. -/
theorem abs_liouvilleTwin_le_one (m : ℕ) : |liouvilleTwin m| ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rcases liouvilleTwin_sign m hm with h | h <;> rw [h] <;> norm_num

/-- **The Liouville twin has the high-detail floor**: with the same lower index as `ζ`, its full
signed form is at least the mass on every high balanced section. -/
theorem liouville_haarTail_roughWeilTw_floor : ∃ A : ℕ, 1 ≤ A ∧ ∀ (c : ℕ → ℝ) (X : ℕ),
    (∑ a ∈ Icc 1 X, haarMass a * haarTailCoeffs A c a ^ 2) ≤
      roughWeilTw liouvilleTwin (haarSectionProfile (haarTailCoeffs A c) X) := by
  obtain ⟨A, hA, h⟩ := exists_haarTail_roughWeilTw_floor
  exact ⟨A, hA, h liouvilleTwin abs_liouvilleTwin_le_one⟩

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
