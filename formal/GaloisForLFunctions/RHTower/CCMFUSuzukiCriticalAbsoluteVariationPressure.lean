import GaloisForLFunctions.RHTower.CCMFUSuzukiCriticalCellSign
import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeCesaroAnchoredMoment
import GaloisForLFunctions.RHTower.RouteEGibbsPrefixPhase
import GaloisForLFunctions.RHTower.Sieve.PrimeRangeSplit
import GaloisForLFunctions.RHTower.MassBesselRadiationDivergence

/-!
# Absolute-variation pressure in the critical FU reporter

The critical FU multiplier is positive in the first half of its triangular aperture.  Combined
with the exact prime-cell lower bound, this gives an unconditional positive pressure from every
large prime in that half.  The normalized mass of the fixed multiplicative prime window `(2Y,3Y]`
is also made explicit.  These facts rule out any proof that separates prime cells by absolute
values: a valid FU mechanism must retain signed transport between distinct cells.

This file deliberately does not claim a bound for the signed reporter, which is RH-bearing.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Dependency-light copy of the literal critical FU multiplier.  The formula is definitionally
the checkpoint multiplier used by the full remainder-variation criterion; isolating it here keeps
the unconditional prime-cell pressure independent of that RH-equivalent criterion. -/
def suzukiCheckpointCriticalTriangularMultiplierCore (H : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt ((n + 3 : ℕ) : ℝ) *
    GaloisForLFunctions.RHTower.ccmGuinandWeilThirdGradeCesaroTriangularWeight H
      (Real.log ((n + 3 : ℕ) : ℝ))

/-- In the first half of a positive triangular aperture, the literal critical multiplier at a
large prime cell retains at least half of its cubic-log carrier. -/
theorem suzukiCheckpointCriticalTriangularMultiplierCore_prime_lower
    {H : ℝ} {p : ℕ} (hp27 : 27 ≤ p) (hH : 0 < H)
    (hlogH : Real.log (p : ℝ) ≤ H / 2) :
    16 * Real.sqrt (p : ℝ) / Real.log (p : ℝ) ^ 3 ≤
      suzukiCheckpointCriticalTriangularMultiplierCore H (p - 3) := by
  have hp0 : (0 : ℝ) < p := by positivity
  have hlog0 : (0 : ℝ) < Real.log p :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hratio : Real.log (p : ℝ) / H ≤ 1 / 2 := by
    rw [div_le_iff₀ hH]
    linarith
  have hfactor : (1 : ℝ) / 2 ≤ 1 - Real.log (p : ℝ) / H := by
    linarith
  have hbase0 : 0 ≤ Real.sqrt (p : ℝ) * (32 / Real.log (p : ℝ) ^ 3) := by
    positivity
  unfold suzukiCheckpointCriticalTriangularMultiplierCore
    GaloisForLFunctions.RHTower.ccmGuinandWeilThirdGradeCesaroTriangularWeight
    ccmGuinandWeilThirdGradeWeight
  rw [show p - 3 + 3 = p by omega]
  calc
    16 * Real.sqrt (p : ℝ) / Real.log (p : ℝ) ^ 3 =
        (Real.sqrt (p : ℝ) * (32 / Real.log (p : ℝ) ^ 3)) * (1 / 2) := by
          ring
    _ ≤ (Real.sqrt (p : ℝ) * (32 / Real.log (p : ℝ) ^ 3)) *
        (1 - Real.log (p : ℝ) / H) :=
      mul_le_mul_of_nonneg_left hfactor hbase0
    _ = Real.sqrt (p : ℝ) *
        (32 / Real.log (p : ℝ) ^ 3 * (1 - Real.log (p : ℝ) / H)) := by ring

/-- A large prime cell has unavoidable positive absolute mass under every critical multiplier
whose aperture contains that cell in its first half. -/
theorem suzukiCheckpointCriticalPrimeCell_abs_weighted_lower
    {H : ℝ} {p : ℕ} (hp : p.Prime) (hp27 : 27 ≤ p) (hH : 0 < H)
    (hlogH : Real.log (p : ℝ) ≤ H / 2) :
    8 * Real.sqrt (p : ℝ) / ((p : ℝ) * Real.log (p : ℝ) ^ 2) ≤
      |(suzukiCheckpointCriticalMertensDeviationCore (p - 2) -
          suzukiCheckpointCriticalMertensDeviationCore (p - 3)) *
        suzukiCheckpointCriticalTriangularMultiplierCore H (p - 3)| := by
  have hcell := suzukiCheckpointCriticalMertensDeviationCore_prime_cell_lower hp hp27
  have hmult := suzukiCheckpointCriticalTriangularMultiplierCore_prime_lower hp27 hH hlogH
  have hp0 : (0 : ℝ) < p := by positivity
  have hlog0 : (0 : ℝ) < Real.log p :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hcell0 : 0 ≤ suzukiCheckpointCriticalMertensDeviationCore (p - 2) -
      suzukiCheckpointCriticalMertensDeviationCore (p - 3) := by
    exact hcell.trans' (by positivity)
  have hmult0 : 0 ≤ suzukiCheckpointCriticalTriangularMultiplierCore H (p - 3) := by
    exact hmult.trans' (by positivity)
  rw [abs_of_nonneg (mul_nonneg hcell0 hmult0)]
  calc
    8 * Real.sqrt (p : ℝ) / ((p : ℝ) * Real.log (p : ℝ) ^ 2) =
        (Real.log (p : ℝ) / (2 * p)) *
          (16 * Real.sqrt (p : ℝ) / Real.log (p : ℝ) ^ 3) := by
          field_simp
          ring
    _ ≤ (suzukiCheckpointCriticalMertensDeviationCore (p - 2) -
          suzukiCheckpointCriticalMertensDeviationCore (p - 3)) *
        suzukiCheckpointCriticalTriangularMultiplierCore H (p - 3) :=
      mul_le_mul hcell hmult (by positivity) hcell0

/-- The same prime-cell pressure at the exact prefix-phase scale.  It is this form that can be
summed over multiplicative prime windows without discarding the moving-triangular geometry. -/
theorem suzukiCheckpointCriticalPrimeCell_prefixWeight_lower
    {H : ℝ} {p : ℕ} (hp : p.Prime) (hp27 : 27 ≤ p) (hH : 0 < H)
    (hlogH : Real.log (p : ℝ) ≤ H / 2) :
    (32 / H ^ 3) * (Real.sqrt (p : ℝ) * Real.log (p : ℝ) / ((p : ℝ) - 1)) ≤
      |(suzukiCheckpointCriticalMertensDeviationCore (p - 2) -
          suzukiCheckpointCriticalMertensDeviationCore (p - 3)) *
        suzukiCheckpointCriticalTriangularMultiplierCore H (p - 3)| := by
  have hprevious := suzukiCheckpointCriticalPrimeCell_abs_weighted_lower hp hp27 hH hlogH
  have hp0 : (0 : ℝ) < p := by positivity
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have hlog0 : (0 : ℝ) < Real.log p :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hcube : Real.log (p : ℝ) ^ 3 ≤ (H / 2) ^ 3 :=
    pow_le_pow_left₀ hlog0.le hlogH 3
  have hHcube : 8 * Real.log (p : ℝ) ^ 3 ≤ H ^ 3 := by
    nlinarith
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlogcube0 : 0 ≤ Real.log (p : ℝ) ^ 3 := pow_nonneg hlog0.le 3
  have hfirst : 4 * (p : ℝ) * Real.log (p : ℝ) ^ 3 ≤
      8 * Real.log (p : ℝ) ^ 3 * ((p : ℝ) - 1) := by
    nlinarith
  have hsecond : 8 * Real.log (p : ℝ) ^ 3 * ((p : ℝ) - 1) ≤
      H ^ 3 * ((p : ℝ) - 1) :=
    mul_le_mul_of_nonneg_right hHcube hp1.le
  have hcore : 4 * (p : ℝ) * Real.log (p : ℝ) ^ 3 ≤
      H ^ 3 * ((p : ℝ) - 1) := hfirst.trans hsecond
  calc
    (32 / H ^ 3) * (Real.sqrt (p : ℝ) * Real.log (p : ℝ) / ((p : ℝ) - 1))
        ≤ 8 * Real.sqrt (p : ℝ) / ((p : ℝ) * Real.log (p : ℝ) ^ 2) := by
          field_simp [hH.ne', hp1.ne', hlog0.ne']
          nlinarith [hcore]
    _ ≤ _ := hprevious

/-- The exact prefix-phase mass carried by the multiplicative prime window `(2N,3N]`. -/
theorem sum_bigPrimeSet_prefixPhaseWeight (N : ℕ) :
    ∑ p ∈ Sieve.bigPrimeSet (2 * N) (3 * N),
      Real.sqrt (p : ℝ) * Real.log (p : ℝ) / ((p : ℝ) - 1) =
      prefixPhaseWeight ((3 * N : ℕ) : ℝ) -
        prefixPhaseWeight ((2 * N : ℕ) : ℝ) := by
  have hsplit := Sieve.sum_primesLE_split (show 2 * N ≤ 3 * N by omega)
    (fun p : ℕ => Real.sqrt (p : ℝ) * Real.log (p : ℝ) / ((p : ℝ) - 1))
  have hthree : prefixPhaseWeight ((3 * N : ℕ) : ℝ) =
      ∑ p ∈ Nat.primesLE (3 * N),
        Real.sqrt (p : ℝ) * Real.log (p : ℝ) / ((p : ℝ) - 1) := by
    simp only [prefixPhaseWeight]
    rw [Nat.floor_natCast]
  have htwo : prefixPhaseWeight ((2 * N : ℕ) : ℝ) =
      ∑ p ∈ Nat.primesLE (2 * N),
        Real.sqrt (p : ℝ) * Real.log (p : ℝ) / ((p : ℝ) - 1) := by
    simp only [prefixPhaseWeight]
    rw [Nat.floor_natCast]
  rw [hthree, htwo]
  linarith

/-- Total variation obtained by taking absolute values of the literal critical FU cell
increments.  It is not the signed reporter: this is the diagnostic quantity that records exactly
what an absolute-value argument would have to pay. -/
def suzukiCheckpointCriticalAbsoluteVariationCore (H : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (⌊Real.exp H⌋₊ - 2),
    |(suzukiCheckpointCriticalMertensDeviationCore (j + 1) -
        suzukiCheckpointCriticalMertensDeviationCore j) *
      suzukiCheckpointCriticalTriangularMultiplierCore H j|

/-- If a multiplicative prime window is active in the first half of the literal triangular
aperture, its complete prefix-phase mass is a lower bound for absolute FU variation. -/
theorem suzukiCheckpointCriticalAbsoluteVariationCore_ge_prime_window
    {H : ℝ} {N : ℕ} (hN : 14 ≤ N) (hH : 0 < H)
    (hhalf : ∀ p ∈ Sieve.bigPrimeSet (2 * N) (3 * N),
      Real.log (p : ℝ) ≤ H / 2)
    (hactive : ∀ p ∈ Sieve.bigPrimeSet (2 * N) (3 * N),
      p - 3 < ⌊Real.exp H⌋₊ - 2) :
    (32 / H ^ 3) *
        (prefixPhaseWeight ((3 * N : ℕ) : ℝ) -
          prefixPhaseWeight ((2 * N : ℕ) : ℝ)) ≤
      suzukiCheckpointCriticalAbsoluteVariationCore H := by
  let P := Sieve.bigPrimeSet (2 * N) (3 * N)
  let g : ℕ → ℝ := fun j =>
    |(suzukiCheckpointCriticalMertensDeviationCore (j + 1) -
        suzukiCheckpointCriticalMertensDeviationCore j) *
      suzukiCheckpointCriticalTriangularMultiplierCore H j|
  have hcell : ∀ p ∈ P,
      (32 / H ^ 3) * (Real.sqrt (p : ℝ) * Real.log (p : ℝ) / ((p : ℝ) - 1)) ≤
        g (p - 3) := by
    intro p hp
    have hpdata : p ∈ Sieve.bigPrimeSet (2 * N) (3 * N) := hp
    rw [Sieve.bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hpdata
    have hp27 : 27 ≤ p := by omega
    dsimp only [g]
    rw [show p - 3 + 1 = p - 2 by omega]
    exact suzukiCheckpointCriticalPrimeCell_prefixWeight_lower hpdata.2 hp27 hH (hhalf p hp)
  have hsumcell :
      (32 / H ^ 3) *
        (∑ p ∈ P, Real.sqrt (p : ℝ) * Real.log (p : ℝ) / ((p : ℝ) - 1)) ≤
      ∑ p ∈ P, g (p - 3) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => hcell p hp
  have hinj : ∀ a ∈ P, ∀ b ∈ P, a - 3 = b - 3 → a = b := by
    intro a ha b hb hab
    have ha' : a ∈ Sieve.bigPrimeSet (2 * N) (3 * N) := ha
    have hb' : b ∈ Sieve.bigPrimeSet (2 * N) (3 * N) := hb
    rw [Sieve.bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at ha' hb'
    omega
  have himage : ∑ j ∈ P.image (fun p => p - 3), g j = ∑ p ∈ P, g (p - 3) := by
    rw [Finset.sum_image hinj]
  have hsubset : P.image (fun p => p - 3) ⊆
      Finset.range (⌊Real.exp H⌋₊ - 2) := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
    exact Finset.mem_range.mpr (hactive p hp)
  have hwindow : ∑ p ∈ P, g (p - 3) ≤
      ∑ j ∈ Finset.range (⌊Real.exp H⌋₊ - 2), g j := by
    rw [← himage]
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro j _ _
    exact abs_nonneg _
  unfold suzukiCheckpointCriticalAbsoluteVariationCore
  rw [← sum_bigPrimeSet_prefixPhaseWeight N]
  exact hsumcell.trans hwindow

/-- The weighted prime mass in `(2Y,3Y]` has a strictly positive square-root-scale limit. -/
theorem tendsto_prefixPhaseWeight_triple_sub_double :
    Tendsto (fun Y : ℝ =>
      (prefixPhaseWeight (3 * Y) - prefixPhaseWeight (2 * Y)) /
        Y ^ ((1 : ℝ) / 2)) atTop
      (nhds (2 * (Real.sqrt 3 - Real.sqrt 2))) := by
  have hscale3 : Tendsto (fun Y : ℝ => 3 * Y) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have hscale2 : Tendsto (fun Y : ℝ => 2 * Y) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have h3raw := tendsto_prefixPhaseWeight.comp hscale3
  have h2raw := tendsto_prefixPhaseWeight.comp hscale2
  have h3 : Tendsto (fun Y : ℝ => prefixPhaseWeight (3 * Y) /
      Y ^ ((1 : ℝ) / 2)) atTop (nhds (2 * Real.sqrt 3)) := by
    have h := h3raw.const_mul (3 ^ ((1 : ℝ) / 2))
    have hlim : 3 ^ ((1 : ℝ) / 2) * 2 = 2 * Real.sqrt 3 := by
      rw [← Real.sqrt_eq_rpow]
      ring
    rw [hlim] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    change 3 ^ ((1 : ℝ) / 2) *
      (prefixPhaseWeight (3 * Y) / (3 * Y) ^ ((1 : ℝ) / 2)) =
        prefixPhaseWeight (3 * Y) / Y ^ ((1 : ℝ) / 2)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hY.le]
    field_simp [Real.rpow_pos_of_pos hY _]
  have h2 : Tendsto (fun Y : ℝ => prefixPhaseWeight (2 * Y) /
      Y ^ ((1 : ℝ) / 2)) atTop (nhds (2 * Real.sqrt 2)) := by
    have h := h2raw.const_mul (2 ^ ((1 : ℝ) / 2))
    have hlim : 2 ^ ((1 : ℝ) / 2) * 2 = 2 * Real.sqrt 2 := by
      rw [← Real.sqrt_eq_rpow]
      ring
    rw [hlim] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    change 2 ^ ((1 : ℝ) / 2) *
      (prefixPhaseWeight (2 * Y) / (2 * Y) ^ ((1 : ℝ) / 2)) =
        prefixPhaseWeight (2 * Y) / Y ^ ((1 : ℝ) / 2)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hY.le]
    field_simp [Real.rpow_pos_of_pos hY _]
  have h := h3.sub h2
  have hlim : 2 * Real.sqrt 3 - 2 * Real.sqrt 2 =
      2 * (Real.sqrt 3 - Real.sqrt 2) := by ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards with Y
  ring

/-- A canonical cofinal clock: its exponential cutoff is exactly the square of `4N`. -/
def suzukiCheckpointCriticalPressureSchedule (N : ℕ) : ℝ :=
  2 * Real.log ((4 * N : ℕ) : ℝ)

theorem exp_suzukiCheckpointCriticalPressureSchedule {N : ℕ} (hN : 1 ≤ N) :
    Real.exp (suzukiCheckpointCriticalPressureSchedule N) = ((4 * N : ℕ) : ℝ) ^ 2 := by
  have hpos : (0 : ℝ) < ((4 * N : ℕ) : ℝ) := by positivity
  unfold suzukiCheckpointCriticalPressureSchedule
  rw [show (2 : ℝ) * Real.log ((4 * N : ℕ) : ℝ) =
      (2 : ℕ) * Real.log ((4 * N : ℕ) : ℝ) by norm_num,
    Real.exp_nat_mul, Real.exp_log hpos]

theorem floor_exp_suzukiCheckpointCriticalPressureSchedule {N : ℕ} (hN : 1 ≤ N) :
    ⌊Real.exp (suzukiCheckpointCriticalPressureSchedule N)⌋₊ = (4 * N) ^ 2 := by
  rw [exp_suzukiCheckpointCriticalPressureSchedule hN]
  rw [← Nat.cast_pow, Nat.floor_natCast]

theorem suzukiCheckpointCriticalPressureSchedule_pos {N : ℕ} (hN : 1 ≤ N) :
    0 < suzukiCheckpointCriticalPressureSchedule N := by
  unfold suzukiCheckpointCriticalPressureSchedule
  have hfour : (1 : ℝ) < ((4 * N : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < 4 * N by omega)
  have hlog := Real.log_pos hfour
  nlinarith

theorem suzukiCheckpointCriticalPressureSchedule_window_half
    {N p : ℕ} (hp : p ∈ Sieve.bigPrimeSet (2 * N) (3 * N)) :
    Real.log (p : ℝ) ≤ suzukiCheckpointCriticalPressureSchedule N / 2 := by
  rw [Sieve.bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
  unfold suzukiCheckpointCriticalPressureSchedule
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hle : p ≤ 4 * N := by omega
  rw [show 2 * Real.log ((4 * N : ℕ) : ℝ) / 2 =
      Real.log ((4 * N : ℕ) : ℝ) by ring]
  exact Real.log_le_log hp0 (by exact_mod_cast hle)

theorem suzukiCheckpointCriticalPressureSchedule_window_active
    {N p : ℕ} (hN : 14 ≤ N) (hp : p ∈ Sieve.bigPrimeSet (2 * N) (3 * N)) :
    p - 3 < ⌊Real.exp (suzukiCheckpointCriticalPressureSchedule N)⌋₊ - 2 := by
  rw [floor_exp_suzukiCheckpointCriticalPressureSchedule (by omega : 1 ≤ N)]
  rw [Sieve.bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hp
  have hpbound : p ≤ 3 * N := hp.1.2
  have hquad : 3 * N - 3 < (4 * N) ^ 2 - 2 := by
    have hsqNat : 2 ≤ (4 * N) ^ 2 := by
      calc
        2 ≤ 4 * N := by omega
        _ ≤ (4 * N) * (4 * N) := Nat.le_mul_of_pos_right _ (by omega)
        _ = (4 * N) ^ 2 := by ring
    have hNreal : (14 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hsquare : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
    have hquadReal : ((3 * N - 3 : ℕ) : ℝ) < (((4 * N) ^ 2 - 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 3 ≤ 3 * N),
        Nat.cast_sub hsqNat]
      push_cast
      nlinarith
    exact_mod_cast hquadReal
  exact (Nat.sub_le_sub_right hpbound 3).trans_lt hquad

/-- On the canonical cofinal clock, the literal absolute variation dominates the prime window. -/
theorem suzukiCheckpointCriticalAbsoluteVariation_schedule_lower (N : ℕ) (hN : 14 ≤ N) :
    (32 / suzukiCheckpointCriticalPressureSchedule N ^ 3) *
        (prefixPhaseWeight ((3 * N : ℕ) : ℝ) -
          prefixPhaseWeight ((2 * N : ℕ) : ℝ)) ≤
      suzukiCheckpointCriticalAbsoluteVariationCore (suzukiCheckpointCriticalPressureSchedule N) := by
  apply suzukiCheckpointCriticalAbsoluteVariationCore_ge_prime_window hN
    (suzukiCheckpointCriticalPressureSchedule_pos (by omega : 1 ≤ N))
  · intro p hp
    exact suzukiCheckpointCriticalPressureSchedule_window_half hp
  · intro p hp
    exact suzukiCheckpointCriticalPressureSchedule_window_active hN hp

theorem tendsto_sqrt_div_suzukiCheckpointCriticalPressureSchedule_pow_atTop :
    Tendsto (fun N : ℕ =>
      Real.sqrt (N : ℝ) / suzukiCheckpointCriticalPressureSchedule N ^ 3) atTop atTop := by
  have hscale : Tendsto (fun N : ℕ => 4 * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hgrow := ((tendsto_sqrt_div_log_pow_atTop 3).comp hscale).const_mul_atTop
    (show (0 : ℝ) < 1 / 16 by norm_num)
  refine hgrow.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNone : 1 ≤ N := by omega
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hNone
  have hlog : 0 < Real.log (4 * (N : ℝ)) := by
    apply Real.log_pos
    nlinarith
  change (1 / 16 : ℝ) * (Real.sqrt (4 * (N : ℝ)) /
      Real.log (4 * (N : ℝ)) ^ 3) =
    Real.sqrt (N : ℝ) / suzukiCheckpointCriticalPressureSchedule N ^ 3
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  unfold suzukiCheckpointCriticalPressureSchedule
  push_cast
  field_simp [hlog.ne']
  ring

theorem tendsto_prefixPhaseWeight_triple_sub_double_nat :
    Tendsto (fun N : ℕ =>
      (prefixPhaseWeight ((3 * N : ℕ) : ℝ) -
        prefixPhaseWeight ((2 * N : ℕ) : ℝ)) /
        (N : ℝ) ^ ((1 : ℝ) / 2)) atTop
      (nhds (2 * (Real.sqrt 3 - Real.sqrt 2))) := by
  have h := tendsto_prefixPhaseWeight_triple_sub_double.comp tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards with N
  simp only [Function.comp_apply]
  push_cast
  rfl

theorem tendsto_suzukiCheckpointCriticalPrimePressure_atTop :
    Tendsto (fun N : ℕ =>
      (32 / suzukiCheckpointCriticalPressureSchedule N ^ 3) *
        (prefixPhaseWeight ((3 * N : ℕ) : ℝ) -
          prefixPhaseWeight ((2 * N : ℕ) : ℝ))) atTop atTop := by
  let C : ℝ := 2 * (Real.sqrt 3 - Real.sqrt 2)
  have hsqrt : Real.sqrt 2 < Real.sqrt 3 := by
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hC : 0 < C := by
    dsimp only [C]
    nlinarith
  have hphase := tendsto_prefixPhaseWeight_triple_sub_double_nat
  have hneigh : Set.Ioi (C / 2) ∈ nhds (2 * (Real.sqrt 3 - Real.sqrt 2)) := by
    apply Ioi_mem_nhds
    dsimp only [C]
    linarith
  have hphaseLower : ∀ᶠ N : ℕ in atTop,
      C / 2 ≤
        (prefixPhaseWeight ((3 * N : ℕ) : ℝ) -
          prefixPhaseWeight ((2 * N : ℕ) : ℝ)) /
          (N : ℝ) ^ ((1 : ℝ) / 2) := by
    filter_upwards [hphase.eventually hneigh] with N hN
    exact hN.le
  have hbase := tendsto_sqrt_div_suzukiCheckpointCriticalPressureSchedule_pow_atTop
  have hgrow := hbase.const_mul_atTop (show (0 : ℝ) < 16 * C by positivity)
  refine tendsto_atTop_mono' _ ?_ hgrow
  filter_upwards [hphaseLower, eventually_ge_atTop (1 : ℕ)] with N hphaseN hN
  have hH : 0 < suzukiCheckpointCriticalPressureSchedule N :=
    suzukiCheckpointCriticalPressureSchedule_pos hN
  have hbase0 : 0 ≤ Real.sqrt (N : ℝ) /
      suzukiCheckpointCriticalPressureSchedule N ^ 3 := by positivity
  have hmult : 16 * C ≤
      32 * ((prefixPhaseWeight ((3 * N : ℕ) : ℝ) -
        prefixPhaseWeight ((2 * N : ℕ) : ℝ)) /
          (N : ℝ) ^ ((1 : ℝ) / 2)) := by
    nlinarith
  calc
    (16 * C) * (Real.sqrt (N : ℝ) /
        suzukiCheckpointCriticalPressureSchedule N ^ 3) ≤
      (32 * ((prefixPhaseWeight ((3 * N : ℕ) : ℝ) -
        prefixPhaseWeight ((2 * N : ℕ) : ℝ)) /
          (N : ℝ) ^ ((1 : ℝ) / 2))) *
        (Real.sqrt (N : ℝ) /
          suzukiCheckpointCriticalPressureSchedule N ^ 3) :=
      mul_le_mul_of_nonneg_right hmult hbase0
    _ = (32 / suzukiCheckpointCriticalPressureSchedule N ^ 3) *
        (prefixPhaseWeight ((3 * N : ℕ) : ℝ) -
          prefixPhaseWeight ((2 * N : ℕ) : ℝ)) := by
      rw [← Real.sqrt_eq_rpow]
      field_simp [hH.ne']

/-- Literal critical FU absolute variation diverges on its canonical cofinal clock.  Thus no
proof that bounds the reporter after taking absolute values cellwise can establish its RH-bearing
signed bound. -/
theorem tendsto_suzukiCheckpointCriticalAbsoluteVariation_schedule_atTop :
    Tendsto (fun N : ℕ =>
      suzukiCheckpointCriticalAbsoluteVariationCore
        (suzukiCheckpointCriticalPressureSchedule N)) atTop atTop := by
  apply tendsto_atTop_mono' _
  filter_upwards [eventually_ge_atTop (14 : ℕ)] with N hN
  exact suzukiCheckpointCriticalAbsoluteVariation_schedule_lower N hN
  exact tendsto_suzukiCheckpointCriticalPrimePressure_atTop

end

end RHTower
