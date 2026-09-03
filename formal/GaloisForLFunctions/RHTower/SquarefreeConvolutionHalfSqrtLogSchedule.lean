import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfBoundaryTwoFactorCeiling

/-!
# Square-root logarithmic Cayley schedule

The degree schedule `log_4(sqrt N + 1) + 6` tends to infinity, so local boundedness of the
corresponding scheduled Cayley--Dirichlet products still forces `RHLadder 1`.  Unlike the
previous `log_2(N+1)+3` schedule, this slower schedule also satisfies the sharp two-factor
boundary scale law at `s = 6/11`.

Precisely, its boundary growth is at most `2 N^(6/11)`, and its earlier one-factor normalized
prime scale is uniformly bounded.  Thus neither proved prime-jump obstruction retires this
source-defined sequence.  Local boundedness remains the exact open analytic obligation.
-/

open Complex Filter Metric Set Topology

namespace RHTower

noncomputable section

/-- Cayley degree growing logarithmically in the square-root Dirichlet cutoff. -/
def sqrtLogarithmicCayleySchedule (N : ℕ) : ℕ :=
  Nat.log 4 (Nat.sqrt N + 1) + 6

theorem sqrtLogarithmicCayleySchedule_ge_six (N : ℕ) :
    6 ≤ sqrtLogarithmicCayleySchedule N := by
  simp [sqrtLogarithmicCayleySchedule]

theorem tendsto_sqrtLogarithmicCayleySchedule_atTop :
    Tendsto sqrtLogarithmicCayleySchedule atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨(4 ^ b) ^ 2, fun N hN => ?_⟩
  have hsqrt : 4 ^ b ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by simpa [pow_two] using hN)
  have hpow : 4 ^ b ≤ Nat.sqrt N + 1 := hsqrt.trans (Nat.le_add_right _ 1)
  have hblog : b ≤ Nat.log 4 (Nat.sqrt N + 1) :=
    Nat.le_log_of_pow_le (by norm_num) hpow
  exact hblog.trans (Nat.le_add_right _ 6)

private theorem cast_natSqrt_le_realSqrt (N : ℕ) :
    ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
  exact Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' N)

private theorem natSqrt_add_one_le_two_rpow_six_elevenths
    {N : ℕ} (hN : 1 ≤ N) :
    ((Nat.sqrt N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ (6 / 11 : ℝ) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsqrt : ((Nat.sqrt N : ℕ) : ℝ) ≤ (N : ℝ) ^ (6 / 11 : ℝ) := by
    calc
      ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := cast_natSqrt_le_realSqrt N
      _ = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      _ ≤ (N : ℝ) ^ (6 / 11 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNreal (by norm_num)
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ (6 / 11 : ℝ) := by
    simpa only [Real.one_rpow] using
      (Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hNreal
        (by norm_num : (0 : ℝ) ≤ 6 / 11))
  norm_num only [Nat.cast_add, Nat.cast_one]
  nlinarith

/-- Strongest known boundary prime-jump scale is obeyed with constant two. -/
theorem sqrtLogarithmicCayleySchedule_boundaryScale_le
    {N : ℕ} (hN : 1 ≤ N) :
    (4 : ℝ) ^
        min (sqrtLogarithmicCayleySchedule N - 6)
          (sqrtLogarithmicCayleySchedule (N + 1) - 6) ≤
      2 * (N : ℝ) ^ (6 / 11 : ℝ) := by
  let e : ℕ := min (sqrtLogarithmicCayleySchedule N - 6)
    (sqrtLogarithmicCayleySchedule (N + 1) - 6)
  have he : e ≤ Nat.log 4 (Nat.sqrt N + 1) := by
    calc
      e ≤ sqrtLogarithmicCayleySchedule N - 6 := min_le_left _ _
      _ = Nat.log 4 (Nat.sqrt N + 1) := by simp [sqrtLogarithmicCayleySchedule]
  have hdegree : (4 : ℝ) ^ e ≤
      (4 : ℝ) ^ Nat.log 4 (Nat.sqrt N + 1) :=
    pow_le_pow_right₀ (by norm_num) he
  have hnat : 4 ^ Nat.log 4 (Nat.sqrt N + 1) ≤ Nat.sqrt N + 1 :=
    Nat.pow_log_le_self 4 (by omega)
  have hnatReal : (4 : ℝ) ^ Nat.log 4 (Nat.sqrt N + 1) ≤
      ((Nat.sqrt N + 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hdegree.trans
    (hnatReal.trans (natSqrt_add_one_le_two_rpow_six_elevenths hN))

theorem not_sqrtLogarithmicCayleySchedule_boundaryPrimeScaleDiverges :
    ¬ BoundaryCayleySchedulePrimeScaleDiverges sqrtLogarithmicCayleySchedule := by
  intro hdiv
  have heventually : ∀ᶠ N : ℕ in atTop,
      2 < (4 : ℝ) ^
        min (sqrtLogarithmicCayleySchedule N - 6)
          (sqrtLogarithmicCayleySchedule (N + 1) - 6) /
            (N : ℝ) ^ (6 / 11 : ℝ) :=
    hdiv.eventually_gt_atTop 2
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp heventually
  let N := max N₀ 1
  have hlarge := hN₀ N (le_max_left _ _)
  have hscale := sqrtLogarithmicCayleySchedule_boundaryScale_le
    (N := N) (le_max_right _ _)
  have hpowpos : 0 < (N : ℝ) ^ (6 / 11 : ℝ) := by
    exact Real.rpow_pos_of_pos
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_right N₀ 1))) _
  have hsmall : (4 : ℝ) ^
        min (sqrtLogarithmicCayleySchedule N - 6)
          (sqrtLogarithmicCayleySchedule (N + 1) - 6) /
            (N : ℝ) ^ (6 / 11 : ℝ) ≤ 2 :=
    (div_le_iff₀ hpowpos).2 hscale
  exact (not_lt_of_ge hsmall) hlarge

/-- Earlier one-factor prime-jump scale is uniformly bounded as well. -/
theorem sqrtLogarithmicCayleySchedule_primeScale_le
    {N : ℕ} (hN : 1 ≤ N) :
    (5 / 4 : ℝ) ^
        min (sqrtLogarithmicCayleySchedule N - 1)
          (sqrtLogarithmicCayleySchedule (N + 1) - 1) / N ≤ 2048 := by
  let e : ℕ := min (sqrtLogarithmicCayleySchedule N - 1)
    (sqrtLogarithmicCayleySchedule (N + 1) - 1)
  have he : e ≤ Nat.log 4 (Nat.sqrt N + 1) + 5 := by
    calc
      e ≤ sqrtLogarithmicCayleySchedule N - 1 := min_le_left _ _
      _ = Nat.log 4 (Nat.sqrt N + 1) + 5 := by simp [sqrtLogarithmicCayleySchedule]
  have hbase : (5 / 4 : ℝ) ^ e ≤ (4 : ℝ) ^ e :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hdegree : (4 : ℝ) ^ e ≤
      (4 : ℝ) ^ (Nat.log 4 (Nat.sqrt N + 1) + 5) :=
    pow_le_pow_right₀ (by norm_num) he
  have hnat : 4 ^ Nat.log 4 (Nat.sqrt N + 1) ≤ Nat.sqrt N + 1 :=
    Nat.pow_log_le_self 4 (by omega)
  have hnatReal : (4 : ℝ) ^ Nat.log 4 (Nat.sqrt N + 1) ≤
      ((Nat.sqrt N + 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hsqrtN : Nat.sqrt N + 1 ≤ 2 * N := by
    have hs := Nat.sqrt_le_self N
    omega
  have hsqrtNReal : ((Nat.sqrt N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hsqrtN
  have hnum : (5 / 4 : ℝ) ^ e ≤ 2048 * (N : ℝ) := by
    calc
      (5 / 4 : ℝ) ^ e ≤ (4 : ℝ) ^ e := hbase
      _ ≤ (4 : ℝ) ^ (Nat.log 4 (Nat.sqrt N + 1) + 5) := hdegree
      _ = 1024 * (4 : ℝ) ^ Nat.log 4 (Nat.sqrt N + 1) := by
        rw [pow_add]
        norm_num
        ring
      _ ≤ 1024 * ((Nat.sqrt N + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hnatReal (by norm_num)
      _ ≤ 2048 * (N : ℝ) := by nlinarith
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  change (5 / 4 : ℝ) ^ e / N ≤ 2048
  exact (div_le_iff₀ hNpos).2 hnum

theorem not_sqrtLogarithmicCayleySchedule_primeScaleDiverges :
    ¬ CayleySchedulePrimeScaleDiverges sqrtLogarithmicCayleySchedule := by
  intro hdiv
  have heventually : ∀ᶠ N : ℕ in atTop,
      2048 < (5 / 4 : ℝ) ^
        min (sqrtLogarithmicCayleySchedule N - 1)
          (sqrtLogarithmicCayleySchedule (N + 1) - 1) / N :=
    hdiv.eventually_gt_atTop 2048
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp heventually
  let N := max N₀ 1
  have hlarge := hN₀ N (le_max_left _ _)
  have hsmall := sqrtLogarithmicCayleySchedule_primeScale_le
    (N := N) (le_max_right _ _)
  exact (not_lt_of_ge hsmall) hlarge

/-- Surviving exact endpoint: local boundedness of this schedule implies the first RH rung. -/
theorem rhLadder_one_of_sqrtLogarithmicCayleySchedule_locallyBounded
    (hloc : PoleClearedFirstTraceScheduledLocallyBounded
      sqrtLogarithmicCayleySchedule) :
    RHLadder 1 :=
  rhLadder_one_of_poleClearedFirstTraceScheduledLocallyBounded
    tendsto_sqrtLogarithmicCayleySchedule_atTop hloc

end

end RHTower
