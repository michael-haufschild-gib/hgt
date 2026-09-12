import GaloisForLFunctions.RHTower.SteinhausLargestPrimeDecomposition
import GaloisForLFunctions.RHTower.PrimeRecipBelowWindow

/-!
# Power mass in a largest-prime channel

For a right-strip dual AFE coefficient at `Re(s)=1/2+d`, the normalized square profile is

```text
N^(-2d) * n^(-(1-2d)).
```

A fixed cofactor loses a power of the conductor.  The upper dyadic half of the complete cofactor
range does not: if `M = N/p`, then its `m^(-(1-2d))` mass is at least `(1/2) M^(2d)`.
This is the elementary cancellation needed before reciprocal-prime mass can be summed over the
large-prime channels.
-/

namespace RHTower

open Finset Nat

noncomputable section

/-- Upper dyadic half of the complete cofactor range in the `p`-channel. -/
def dyadicCofactorBlock (N p : ℕ) : Finset ℕ :=
  Finset.Icc (N / p / 2 + 1) (N / p)

/-- Normalized square profile of a right-strip reflected Dirichlet coefficient. -/
def terminalPowerSquareWeight (d : ℝ) (N n : ℕ) : ℝ :=
  (N : ℝ) ^ (-2 * d) * (n : ℝ) ^ (-(1 - 2 * d))

/-- The upper half of `[1,M]` already contains a fixed fraction of the full subcritical power
mass.  This is uniform in `M`; no asymptotic power-sum estimate is used. -/
theorem half_rpow_two_mul_le_sum_dyadicCofactor
    {d : ℝ} (hdhalf : d < 1 / 2) {M : ℕ} (hM : 1 ≤ M) :
    (1 / 2 : ℝ) * (M : ℝ) ^ (2 * d) ≤
      ∑ m ∈ Finset.Icc (M / 2 + 1) M, (m : ℝ) ^ (-(1 - 2 * d)) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hexp : -(1 - 2 * d) ≤ 0 := by linarith
  have hterm : ∀ m ∈ Finset.Icc (M / 2 + 1) M,
      (M : ℝ) ^ (-(1 - 2 * d)) ≤ (m : ℝ) ^ (-(1 - 2 * d)) := by
    intro m hm
    have hmlo := (Finset.mem_Icc.1 hm).1
    have hm1 : 1 ≤ m := by omega
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm1)
    exact Real.rpow_le_rpow_of_nonpos hmpos (by exact_mod_cast (Finset.mem_Icc.1 hm).2) hexp
  have hcardNat : M ≤ 2 * (M + 1 - (M / 2 + 1)) := by omega
  have hcard : (M : ℝ) / 2 ≤ ((Finset.Icc (M / 2 + 1) M).card : ℝ) := by
    rw [Nat.card_Icc]
    have hcardCast : (M : ℝ) ≤ 2 * ((M + 1 - (M / 2 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hcardNat
    linarith
  have hpow : (M : ℝ) ^ (2 * d) =
      (M : ℝ) * (M : ℝ) ^ (-(1 - 2 * d)) := by
    calc
      (M : ℝ) ^ (2 * d) = (M : ℝ) ^ (1 + (-(1 - 2 * d))) := by ring_nf
      _ = (M : ℝ) ^ (1 : ℝ) * (M : ℝ) ^ (-(1 - 2 * d)) :=
        Real.rpow_add hMpos 1 (-(1 - 2 * d))
      _ = (M : ℝ) * (M : ℝ) ^ (-(1 - 2 * d)) := by rw [Real.rpow_one]
  calc
    (1 / 2 : ℝ) * (M : ℝ) ^ (2 * d) =
        ((M : ℝ) / 2) * (M : ℝ) ^ (-(1 - 2 * d)) := by rw [hpow]; ring
    _ ≤ ((Finset.Icc (M / 2 + 1) M).card : ℝ) *
          (M : ℝ) ^ (-(1 - 2 * d)) := by
        exact mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (Nat.cast_nonneg M) _)
    _ = ∑ _m ∈ Finset.Icc (M / 2 + 1) M,
          (M : ℝ) ^ (-(1 - 2 * d)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ Finset.Icc (M / 2 + 1) M,
          (m : ℝ) ^ (-(1 - 2 * d)) := Finset.sum_le_sum hterm

/-- The natural quotient retains at least half of the corresponding real quotient. -/
theorem half_real_div_le_nat_div {N p : ℕ} (hp : 0 < p) (hpN : p ≤ N) :
    (N : ℝ) / (2 * (p : ℝ)) ≤ ((N / p : ℕ) : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hratio : (1 : ℝ) ≤ (N : ℝ) / (p : ℝ) :=
    (le_div_iff₀ hpR).2 (by rw [one_mul]; exact_mod_cast hpN)
  have hfloor := Nat.div_two_lt_floor hratio
  rw [Nat.floor_div_eq_div (K := ℝ)] at hfloor
  calc
    (N : ℝ) / (2 * (p : ℝ)) = ((N : ℝ) / (p : ℝ)) / 2 := by ring
    _ ≤ ((N / p : ℕ) : ℝ) := hfloor.le

/-- One complete large-prime channel retains the conductor power through its variable cofactor
range.  The right side is arranged so that its powers simplify to a constant multiple of `1/p`. -/
theorem normalized_power_channel_lower
    {d : ℝ} (hd0 : 0 < d) (hdhalf : d < 1 / 2)
    {N p : ℕ} (hp : 0 < p) (h2p : 2 * p ≤ N) :
    (N : ℝ) ^ (-2 * d) * (p : ℝ) ^ (-(1 - 2 * d)) *
        ((1 / 2 : ℝ) * ((N : ℝ) / (2 * (p : ℝ))) ^ (2 * d)) ≤
      ∑ m ∈ dyadicCofactorBlock N p, terminalPowerSquareWeight d N (p * m) := by
  have hpN : p ≤ N := by omega
  have hM : 1 ≤ N / p := Nat.div_pos hpN hp
  have hquot := half_real_div_le_nat_div hp hpN
  have hpowquot : ((N : ℝ) / (2 * (p : ℝ))) ^ (2 * d) ≤
      ((N / p : ℕ) : ℝ) ^ (2 * d) :=
    Real.rpow_le_rpow (by positivity) hquot (by positivity)
  have hcofactor := half_rpow_two_mul_le_sum_dyadicCofactor hdhalf hM
  have hscale0 : 0 ≤
      (N : ℝ) ^ (-2 * d) * (p : ℝ) ^ (-(1 - 2 * d)) := by positivity
  calc
    (N : ℝ) ^ (-2 * d) * (p : ℝ) ^ (-(1 - 2 * d)) *
        ((1 / 2 : ℝ) * ((N : ℝ) / (2 * (p : ℝ))) ^ (2 * d))
        ≤ (N : ℝ) ^ (-2 * d) * (p : ℝ) ^ (-(1 - 2 * d)) *
          ((1 / 2 : ℝ) * ((N / p : ℕ) : ℝ) ^ (2 * d)) := by
            gcongr
    _ ≤ (N : ℝ) ^ (-2 * d) * (p : ℝ) ^ (-(1 - 2 * d)) *
          (∑ m ∈ Finset.Icc (N / p / 2 + 1) (N / p),
            (m : ℝ) ^ (-(1 - 2 * d))) :=
        mul_le_mul_of_nonneg_left hcofactor hscale0
    _ = ∑ m ∈ dyadicCofactorBlock N p, terminalPowerSquareWeight d N (p * m) := by
      rw [Finset.mul_sum]
      unfold dyadicCofactorBlock terminalPowerSquareWeight
      refine Finset.sum_congr rfl (fun m hm => ?_)
      have hmlo := (Finset.mem_Icc.1 hm).1
      have hm1 : 1 ≤ m := by omega
      have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
      have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm1)
      rw [Nat.cast_mul, Real.mul_rpow hpR.le hmR.le]
      ring

/-- The normalized conductor, prime, and cofactor powers cancel exactly, leaving a reciprocal
prime. -/
theorem normalized_power_channel_factor_eq
    (d : ℝ) {N p : ℕ} (hN : 0 < N) (hp : 0 < p) :
    (N : ℝ) ^ (-2 * d) * (p : ℝ) ^ (-(1 - 2 * d)) *
        ((1 / 2 : ℝ) * ((N : ℝ) / (2 * (p : ℝ))) ^ (2 * d)) =
      ((1 / 2 : ℝ) / (2 : ℝ) ^ (2 * d)) * ((p : ℝ)⁻¹) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hNcancel : (N : ℝ) ^ (-(2 * d)) * (N : ℝ) ^ (2 * d) = 1 := by
    rw [← Real.rpow_add hNR]
    norm_num
  have hpSplit : (p : ℝ) ^ (-(1 - 2 * d)) =
      (p : ℝ) ^ (2 * d) * (p : ℝ) ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hpR]
    congr 1
    ring
  have hpInv : (p : ℝ) ^ (-1 : ℝ) = (p : ℝ)⁻¹ := by
    rw [Real.rpow_neg_one]
  rw [Real.div_rpow hNR.le (mul_nonneg (by norm_num) hpR.le),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hpR.le, hpSplit, hpInv]
  have h2pow : (2 : ℝ) ^ (2 * d) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hppow : (p : ℝ) ^ (2 * d) ≠ 0 := (Real.rpow_pos_of_pos hpR _).ne'
  field_simp [h2pow, hppow]
  nlinarith [hNcancel]

/-- Pointwise reciprocal-prime lower bound for one normalized channel. -/
theorem normalized_power_channel_lower_recip
    {d : ℝ} (hd0 : 0 < d) (hdhalf : d < 1 / 2)
    {N p : ℕ} (hp : 0 < p) (h2p : 2 * p ≤ N) :
    ((1 / 2 : ℝ) / (2 : ℝ) ^ (2 * d)) * ((p : ℝ)⁻¹) ≤
      ∑ m ∈ dyadicCofactorBlock N p, terminalPowerSquareWeight d N (p * m) := by
  rw [← normalized_power_channel_factor_eq d (N := N) (p := p) (by omega) hp]
  exact normalized_power_channel_lower hd0 hdhalf hp h2p

/-- Sum of the pointwise channel bounds over any admitted prime set. -/
theorem normalized_power_channels_lower_recip
    {d : ℝ} (hd0 : 0 < d) (hdhalf : d < 1 / 2)
    {N : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, 0 < p ∧ 2 * p ≤ N) :
    ((1 / 2 : ℝ) / (2 : ℝ) ^ (2 * d)) * (∑ p ∈ P, ((p : ℝ)⁻¹)) ≤
      ∑ p ∈ P, ∑ m ∈ dyadicCofactorBlock N p,
        terminalPowerSquareWeight d N (p * m) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun p hp =>
    normalized_power_channel_lower_recip hd0 hdhalf (hP p hp).1 (hP p hp).2

/-! ## A fixed power window of terminal primes -/

/-- Primes strictly above the half-power cut and below the two-thirds-power cut. -/
def terminalPrimePowerWindow (N : ℕ) : Finset ℕ :=
  Nat.primesBelow (powerWindowIndex (2 / 3 : ℝ) N) \
    Nat.primesBelow (powerWindowIndex (1 / 2 : ℝ) N + 1)

theorem mem_terminalPrimePowerWindow {N p : ℕ} :
    p ∈ terminalPrimePowerWindow N ↔
      p.Prime ∧ powerWindowIndex (1 / 2 : ℝ) N < p ∧
        p < powerWindowIndex (2 / 3 : ℝ) N := by
  rw [terminalPrimePowerWindow, Finset.mem_sdiff, Nat.mem_primesBelow,
    Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hpupper, hpprime⟩, hplower⟩
    refine ⟨hpprime, ?_, hpupper⟩
    by_contra hp
    exact hplower ⟨by omega, hpprime⟩
  · rintro ⟨hpprime, hplower, hpupper⟩
    exact ⟨⟨hpupper, hpprime⟩, fun hp => by omega⟩

/-- Successor formula for the half-open reciprocal-prime sum. -/
theorem primeRecipBelow_succ (N : ℕ) :
    primeRecipBelow (N + 1) = primeRecipBelow N + primeRecipWeight N := by
  rw [primeRecipBelow_eq_sum_weight, primeRecipBelow_eq_sum_weight,
    Finset.sum_range_succ]

/-- The half-power boundary is eventually strictly below the two-thirds-power boundary. -/
theorem eventually_halfPowerWindowIndex_lt_twoThirds :
    ∀ᶠ N : ℕ in Filter.atTop,
      powerWindowIndex (1 / 2 : ℝ) N < powerWindowIndex (2 / 3 : ℝ) N := by
  have hhalf :=
    (tendsto_log_powerWindowIndex_div (θ := (1 / 2 : ℝ)) (by norm_num)).eventually_lt_const
      (by norm_num : (1 / 2 : ℝ) < 7 / 12)
  have htwoThirds :=
    (tendsto_log_powerWindowIndex_div (θ := (2 / 3 : ℝ)) (by norm_num)).eventually_const_lt
      (by norm_num : (7 / 12 : ℝ) < 2 / 3)
  filter_upwards [hhalf, htwoThirds, Filter.eventually_ge_atTop 2] with N hhalfN htwoN hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hratio :
      Real.log ((powerWindowIndex (1 / 2 : ℝ) N : ℕ) : ℝ) / Real.log N <
        Real.log ((powerWindowIndex (2 / 3 : ℝ) N : ℕ) : ℝ) / Real.log N :=
    lt_trans hhalfN htwoN
  have hlog :
      Real.log ((powerWindowIndex (1 / 2 : ℝ) N : ℕ) : ℝ) <
        Real.log ((powerWindowIndex (2 / 3 : ℝ) N : ℕ) : ℝ) :=
    (div_lt_div_iff_of_pos_right hlogN).mp hratio
  have hleft : (0 : ℝ) < ((powerWindowIndex (1 / 2 : ℝ) N : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_powerWindowIndex _ _))
  have hright : (0 : ℝ) < ((powerWindowIndex (2 / 3 : ℝ) N : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_powerWindowIndex _ _))
  exact_mod_cast (Real.log_lt_log_iff hleft hright).mp hlog

/-- The two-thirds-power boundary is eventually below half the conductor. -/
theorem eventually_two_mul_twoThirdsPowerWindowIndex_le :
    ∀ᶠ N : ℕ in Filter.atTop,
      2 * powerWindowIndex (2 / 3 : ℝ) N ≤ N := by
  have hsmall : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 3 : ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hsmall.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4),
    Filter.eventually_ge_atTop 1] with N hsmallN hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hpower : (N : ℝ) ^ (2 / 3 : ℝ) =
      (N : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by
    calc
      (N : ℝ) ^ (2 / 3 : ℝ) = (N : ℝ) ^ (1 + (-(1 / 3 : ℝ))) := by ring_nf
      _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_add hNR 1 (-(1 / 3 : ℝ))
      _ = (N : ℝ) * (N : ℝ) ^ (-(1 / 3 : ℝ)) := by rw [Real.rpow_one]
  have hgrowth : 4 * (N : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) := by
    rw [hpower]
    nlinarith
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hindex := powerWindowIndex_le_two_mul (θ := (2 / 3 : ℝ)) (N := N) hone
  have hreal : (2 : ℝ) * ((powerWindowIndex (2 / 3 : ℝ) N : ℕ) : ℝ) ≤ (N : ℝ) := by
    nlinarith
  exact_mod_cast hreal

/-- Reciprocal-prime mass of the terminal power window. -/
def terminalPrimePowerWindowMass (N : ℕ) : ℝ :=
  ∑ p ∈ terminalPrimePowerWindow N, ((p : ℝ)⁻¹)

theorem terminalPrimePowerWindowMass_eq
    {N : ℕ}
    (hindex : powerWindowIndex (1 / 2 : ℝ) N + 1 ≤
      powerWindowIndex (2 / 3 : ℝ) N) :
    terminalPrimePowerWindowMass N =
      primeRecipBelow (powerWindowIndex (2 / 3 : ℝ) N) -
        primeRecipBelow (powerWindowIndex (1 / 2 : ℝ) N + 1) := by
  have hsub : Nat.primesBelow (powerWindowIndex (1 / 2 : ℝ) N + 1) ⊆
      Nat.primesBelow (powerWindowIndex (2 / 3 : ℝ) N) :=
    Nat.primesBelow_mono hindex
  have hsum := Finset.sum_sdiff hsub
    (f := fun p : ℕ => ((p : ℝ)⁻¹))
  unfold terminalPrimePowerWindowMass terminalPrimePowerWindow primeRecipBelow
  linarith

/-- Exact limiting reciprocal-prime mass of the fixed power window. -/
theorem tendsto_terminalPrimePowerWindowMass :
    Filter.Tendsto terminalPrimePowerWindowMass Filter.atTop
      (nhds (-Real.log (1 / 2 : ℝ) - (-Real.log (2 / 3 : ℝ)))) := by
  have hhalf := tendsto_primeRecipBelow_window (θ := (1 / 2 : ℝ)) (by norm_num)
  have htwo := tendsto_primeRecipBelow_window (θ := (2 / 3 : ℝ)) (by norm_num)
  have hbase : Filter.Tendsto (fun N : ℕ =>
      primeRecipBelow (powerWindowIndex (2 / 3 : ℝ) N) -
        primeRecipBelow (powerWindowIndex (1 / 2 : ℝ) N)) Filter.atTop
      (nhds (-Real.log (1 / 2 : ℝ) - (-Real.log (2 / 3 : ℝ)))) := by
    have h := hhalf.sub htwo
    exact h.congr fun N => by ring
  have hweight : Filter.Tendsto
      (fun N : ℕ => primeRecipWeight (powerWindowIndex (1 / 2 : ℝ) N))
      Filter.atTop (nhds 0) :=
    tendsto_primeRecipWeight.comp (tendsto_powerWindowIndex (by norm_num))
  have hsucc : Filter.Tendsto (fun N : ℕ =>
      primeRecipBelow (powerWindowIndex (2 / 3 : ℝ) N) -
        primeRecipBelow (powerWindowIndex (1 / 2 : ℝ) N + 1)) Filter.atTop
      (nhds (-Real.log (1 / 2 : ℝ) - (-Real.log (2 / 3 : ℝ)))) := by
    have h := hbase.sub hweight
    have h' : Filter.Tendsto (fun N : ℕ =>
        primeRecipBelow (powerWindowIndex (2 / 3 : ℝ) N) -
          primeRecipBelow (powerWindowIndex (1 / 2 : ℝ) N) -
          primeRecipWeight (powerWindowIndex (1 / 2 : ℝ) N)) Filter.atTop
        (nhds (-Real.log (1 / 2 : ℝ) - (-Real.log (2 / 3 : ℝ)))) := by
      simpa only [sub_zero] using h
    refine h'.congr fun N => ?_
    rw [primeRecipBelow_succ]
    ring
  refine hsucc.congr' ?_
  filter_upwards [eventually_halfPowerWindowIndex_lt_twoThirds] with N hN
  exact (terminalPrimePowerWindowMass_eq (Nat.succ_le_iff.mpr hN)).symm

/-- The limiting reciprocal-prime mass is strictly positive. -/
theorem terminalPrimePowerWindowMass_limit_pos :
    0 < -Real.log (1 / 2 : ℝ) - (-Real.log (2 / 3 : ℝ)) := by
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 2 / 3)
  linarith

/-- **Terminal channel mass floor.**  The dyadic variable-cofactor pieces of primes between the
half- and two-thirds-power cuts retain a positive normalized mass, uniformly for large `N`. -/
theorem eventually_normalized_power_terminal_channels_lower
    {d : ℝ} (hd0 : 0 < d) (hdhalf : d < 1 / 2) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((1 / 2 : ℝ) / (2 : ℝ) ^ (2 * d)) *
          ((-Real.log (1 / 2 : ℝ) - (-Real.log (2 / 3 : ℝ))) / 2) ≤
        ∑ p ∈ terminalPrimePowerWindow N,
          ∑ m ∈ dyadicCofactorBlock N p,
            terminalPowerSquareWeight d N (p * m) := by
  have hmass := tendsto_terminalPrimePowerWindowMass.eventually_const_lt
    (by linarith [terminalPrimePowerWindowMass_limit_pos] :
      (-Real.log (1 / 2 : ℝ) - (-Real.log (2 / 3 : ℝ))) / 2 <
        -Real.log (1 / 2 : ℝ) - (-Real.log (2 / 3 : ℝ)))
  filter_upwards [hmass, eventually_two_mul_twoThirdsPowerWindowIndex_le] with N hmassN hupper
  have hP : ∀ p ∈ terminalPrimePowerWindow N, 0 < p ∧ 2 * p ≤ N := by
    intro p hp
    have hmem := mem_terminalPrimePowerWindow.1 hp
    exact ⟨hmem.1.pos, by omega⟩
  have hsum := normalized_power_channels_lower_recip hd0 hdhalf hP
  have hconst : 0 ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ (2 * d) := by positivity
  exact (mul_le_mul_of_nonneg_left hmassN.le hconst).trans hsum

end

end RHTower
