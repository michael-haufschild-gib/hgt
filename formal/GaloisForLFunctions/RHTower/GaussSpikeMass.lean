import Mathlib

/-!
# The mass of a moving spike, and what a harmonic kernel does to it

A Fourier multiplier with symbol `‖d_{n+j}‖/‖d_n‖` leaves the bulk of a harmonic coefficient
sequence alone but inflates it near the moving frequency `-n`, by a factor `(n/|n+j|)^c`.  The
resulting *spike* is not controlled by any uniform harmonic bound, so it has to be carried as a
separate piece of the invariant decay class.

Two estimates control it.  Its total mass is `n^c` times a head sum of `r^{-c}`, which the integral
comparison bounds by `1 + N^{1-c}/(1-c)`; over `0 < r < n` that is comparable to `n`.  And a kernel
with harmonic decay sees the spike only from a distance: if the spike sits at distance at least `D`
from the origin and the output frequency is within `D/2`, every kernel value used is at most
`K/(1 + D/2)`, so the whole spike contributes at most its mass times that factor.  With mass `≍ n`
and factor `≍ 1/n` the spike passes into the bulk with a bounded constant.
-/

namespace RHTower

open Finset

/-- **The head of a `p`-series with exponent below one.**  Integral comparison on `[1, N]`. -/
theorem sum_rpow_neg_head_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (N : ℕ) :
    ∑ r ∈ Finset.Icc 1 N, ((r : ℝ)) ^ (-c) ≤ 1 + (N : ℝ) ^ (1 - c) / (1 - c) := by
  have hpos : (0 : ℝ) < 1 - c := by linarith
  have hNnn : (0 : ℝ) ≤ (N : ℝ) ^ (1 - c) := Real.rpow_nonneg (by positivity) _
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : Finset.Icc 1 0 = (∅ : Finset ℕ) :=
      Finset.eq_empty_of_forall_notMem fun x hx => by
        rw [Finset.mem_Icc] at hx; omega
    rw [h0, Finset.sum_empty]
    positivity
  -- rewrite the sum over `Icc 1 N` as a sum over `range N`
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hrange : ∑ r ∈ Finset.Icc 1 N, ((r : ℝ)) ^ (-c)
      = ∑ i ∈ Finset.range N, (((1 + i : ℕ) : ℝ)) ^ (-c) := by
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    simp
  -- peel off the first term
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hpeel : ∑ i ∈ Finset.range (M + 1), (((1 + i : ℕ) : ℝ)) ^ (-c)
      = (∑ i ∈ Finset.range M, (((1 + (i + 1) : ℕ) : ℝ)) ^ (-c)) + ((1 : ℝ)) ^ (-c) := by
    rw [Finset.sum_range_succ']
    norm_num
  -- integral comparison for the tail
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-c)) (Set.Icc (1 : ℝ) (1 + (M : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hx.1) hxy (by linarith)
  have hsum := AntitoneOn.sum_le_integral (x₀ := (1 : ℝ)) (a := M)
    (f := fun x : ℝ => x ^ (-c)) hanti
  have hint : ∫ x : ℝ in (1 : ℝ)..(1 + (M : ℝ)), x ^ (-c)
      = ((1 + (M : ℝ)) ^ (-c + 1) - (1 : ℝ) ^ (-c + 1)) / (-c + 1) :=
    integral_rpow (Or.inl (by linarith))
  have hone : ((1 : ℝ)) ^ (-c + 1) = 1 := Real.one_rpow _
  have hcast : ((1 + (M : ℝ))) = (((M + 1 : ℕ)) : ℝ) := by push_cast; ring
  have hcastsum : ∑ i ∈ Finset.range M, (((1 + (i + 1) : ℕ) : ℝ)) ^ (-c)
      = ∑ i ∈ Finset.range M, ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-c) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring_nf
  rw [hint, hone, hcast] at hsum
  rw [hrange, hpeel, Real.one_rpow, hcastsum]
  have hsub : ((((M + 1 : ℕ)) : ℝ) ^ (-c + 1) - 1) / (-c + 1)
      = (((M + 1 : ℕ) : ℝ)) ^ (-c + 1) / (-c + 1) - 1 / (-c + 1) := by ring
  have hexp : (-c + 1 : ℝ) = 1 - c := by ring
  have h1d : (0 : ℝ) < 1 / (1 - c) := by positivity
  rw [hsub, hexp] at hsum
  linarith [hsum]

/-- **A harmonic kernel sees a distant spike only through its total mass.**  If the spike is
supported at distance at least `D` from the origin and the output frequency is within `D/2`, every
kernel value used is at most `K/(1 + D/2)`. -/
theorem sum_kernel_mul_spike_le {K D S : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D)
    {κ : ℤ → ℂ} (hκ : ∀ l : ℤ, ‖κ l‖ ≤ K / (1 + (l.natAbs : ℝ)))
    {s : ℤ → ℂ} {T : Finset ℤ} (hT : ∀ l ∈ T, D ≤ (l.natAbs : ℝ))
    (hS : ∑ l ∈ T, ‖s l‖ ≤ S) {j : ℤ} (hj : (j.natAbs : ℝ) ≤ D / 2) :
    ∑ l ∈ T, ‖κ (j - l)‖ * ‖s l‖ ≤ K / (1 + D / 2) * S := by
  have hden : (0 : ℝ) < 1 + D / 2 := by linarith
  have hstep : ∀ l ∈ T, ‖κ (j - l)‖ * ‖s l‖ ≤ K / (1 + D / 2) * ‖s l‖ := by
    intro l hl
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine le_trans (hκ (j - l)) ?_
    have hnat : (l.natAbs : ℝ) ≤ (j.natAbs : ℝ) + ((j - l).natAbs : ℝ) := by
      have h : l.natAbs ≤ j.natAbs + (j - l).natAbs := by
        have := Int.natAbs_sub_le j (j - l)
        simpa using this
      exact_mod_cast h
    have hfar : D / 2 ≤ ((j - l).natAbs : ℝ) := by
      have := hT l hl
      linarith
    refine div_le_div_of_nonneg_left hK hden ?_
    linarith
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hS (by positivity)

/-- **The total mass of a moving spike.**  Summing `(n/r)^c` over `0 < r ≤ N ≤ n` costs `n^c` times
the head sum, hence at most `n^c + n/(1-c)`: comparable to `n`, not to `n^{1+c}`. -/
theorem spike_mass_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) {n N : ℕ} (hNn : N ≤ n) :
    ∑ r ∈ Finset.Icc 1 N, ((n : ℝ) / (r : ℝ)) ^ c ≤ (n : ℝ) ^ c + (n : ℝ) / (1 - c) := by
  have hpos : (0 : ℝ) < 1 - c := by linarith
  have hncnn : (0 : ℝ) ≤ (n : ℝ) ^ c := Real.rpow_nonneg (by positivity) _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hN0 : N = 0 := by omega
    subst hN0
    have h0 : Finset.Icc 1 0 = (∅ : Finset ℕ) :=
      Finset.eq_empty_of_forall_notMem fun x hx => by
        rw [Finset.mem_Icc] at hx; omega
    rw [h0, Finset.sum_empty]
    positivity
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hterm : ∀ r ∈ Finset.Icc 1 N, ((n : ℝ) / (r : ℝ)) ^ c = (n : ℝ) ^ c * ((r : ℝ)) ^ (-c) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.1
    rw [Real.div_rpow hnR.le hrpos.le, Real.rpow_neg hrpos.le, div_eq_mul_inv]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hhead := sum_rpow_neg_head_le hc0 hc1 N
  have hstep : (n : ℝ) ^ c * ∑ r ∈ Finset.Icc 1 N, ((r : ℝ)) ^ (-c)
      ≤ (n : ℝ) ^ c * (1 + (N : ℝ) ^ (1 - c) / (1 - c)) :=
    mul_le_mul_of_nonneg_left hhead hncnn
  have hNle : ((N : ℝ)) ^ (1 - c) ≤ ((n : ℝ)) ^ (1 - c) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hNn) hpos.le
  have hmul : (n : ℝ) ^ c * ((n : ℝ)) ^ (1 - c) = (n : ℝ) := by
    rw [← Real.rpow_add hnR]
    norm_num
  have hfinal : (n : ℝ) ^ c * (1 + (N : ℝ) ^ (1 - c) / (1 - c))
      ≤ (n : ℝ) ^ c + (n : ℝ) / (1 - c) := by
    have hle : (n : ℝ) ^ c * ((N : ℝ) ^ (1 - c) / (1 - c))
        ≤ (n : ℝ) ^ c * (((n : ℝ)) ^ (1 - c) / (1 - c)) := by
      refine mul_le_mul_of_nonneg_left ?_ hncnn
      exact div_le_div_of_nonneg_right hNle hpos.le
    have heq : (n : ℝ) ^ c * (((n : ℝ)) ^ (1 - c) / (1 - c)) = (n : ℝ) / (1 - c) := by
      rw [← mul_div_assoc, hmul]
    nlinarith [hle, heq]
  linarith [hstep, hfinal]

/-- **The spike-to-bulk transfer, in the form the iteration uses.**  A spike of height `B` at the
moving frequency `-n`, indexed by its distance `r` from that frequency, is seen by a harmonic
kernel from distance at least `n/4`, so its whole contribution to a bulk frequency is at most the
kernel value there times the spike mass. -/
theorem sum_kernel_mul_spike_band_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) {n N : ℕ} (hN : 2 * N ≤ n)
    {κ : ℤ → ℂ} (hκ : ∀ l : ℤ, ‖κ l‖ ≤ K / (1 + (l.natAbs : ℝ)))
    {j : ℤ} (hj : 4 * (j.natAbs : ℝ) ≤ (n : ℝ))
    (ε : ℤ → ℤ) (hε : ∀ r ∈ Finset.Icc 1 N, (n : ℝ) / 2 ≤ ((ε r).natAbs : ℝ)) :
    ∑ r ∈ Finset.Icc 1 N, ‖κ (j - ε r)‖ * (B * ((n : ℝ) / (r : ℝ)) ^ c)
      ≤ K / (1 + (n : ℝ) / 4) * (B * ((n : ℝ) ^ c + (n : ℝ) / (1 - c))) := by
  have hnnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hden : (0 : ℝ) < 1 + (n : ℝ) / 4 := by linarith
  have hjq : (j.natAbs : ℝ) ≤ (n : ℝ) / 4 := by linarith
  have hstep : ∀ r ∈ Finset.Icc 1 N,
      ‖κ (j - ε r)‖ * (B * ((n : ℝ) / (r : ℝ)) ^ c)
        ≤ K / (1 + (n : ℝ) / 4) * (B * ((n : ℝ) / (r : ℝ)) ^ c) := by
    intro r hr
    have hnonneg : (0 : ℝ) ≤ B * ((n : ℝ) / (r : ℝ)) ^ c :=
      mul_nonneg hB (Real.rpow_nonneg (by positivity) _)
    refine mul_le_mul_of_nonneg_right ?_ hnonneg
    refine le_trans (hκ (j - ε r)) ?_
    have hnat : ((ε r).natAbs : ℝ) ≤ (j.natAbs : ℝ) + ((j - ε r).natAbs : ℝ) := by
      have h : (ε r).natAbs ≤ j.natAbs + (j - ε r).natAbs := by
        have := Int.natAbs_sub_le j (j - ε r)
        simpa using this
      exact_mod_cast h
    have hfar : (n : ℝ) / 4 ≤ ((j - ε r).natAbs : ℝ) := by
      have := hε r hr
      linarith
    refine div_le_div_of_nonneg_left hK hden ?_
    linarith
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact mul_le_mul_of_nonneg_left (spike_mass_le hc0 hc1 (by omega)) hB


/-! ### The two-piece amplitude class -/

/-- The spike carried at the moving frequency `-n`: height `B (n / (1 + |n + l|))^c` inside the band
`2|n + l| < n`, and nothing outside it. -/
noncomputable def spikeProfile (B c : ℝ) (n : ℕ) (l : ℤ) : ℝ :=
  if 2 * ((((n : ℤ) + l).natAbs : ℝ)) < (n : ℝ)
    then B * ((n : ℝ) / (1 + (((n : ℤ) + l).natAbs : ℝ))) ^ c else 0

theorem spikeProfile_nonneg {B c : ℝ} (hB : 0 ≤ B) (n : ℕ) (l : ℤ) :
    0 ≤ spikeProfile B c n l := by
  rw [spikeProfile]
  split_ifs with h
  · positivity
  · exact le_rfl

/-- **The two-piece amplitude class.**  A uniform harmonic part plus a spike at the moving
frequency.  A uniform bound alone is not preserved by the Fourier multiplier `‖d_(n+j)‖/‖d_n‖`,
because the damage is localised at a moving frequency rather than spread over the tail. -/
def TwoPieceAmplitude (A θ B c : ℝ) (n : ℕ) (g : ℤ → ℂ) : Prop :=
  ∀ j : ℤ, ‖g j‖ ≤ A / (1 + (j.natAbs : ℝ)) ^ θ + spikeProfile B c n j

theorem TwoPieceAmplitude.uniform {A θ B c : ℝ} {n : ℕ} {g : ℤ → ℂ}
    (h : ∀ j : ℤ, ‖g j‖ ≤ A / (1 + (j.natAbs : ℝ)) ^ θ) (hB : 0 ≤ B) :
    TwoPieceAmplitude A θ B c n g := by
  intro j
  have := spikeProfile_nonneg (B := B) (c := c) hB n j
  linarith [h j]

/-! ### The spike profile on the two sides of the band -/

theorem spikeProfile_pos_side {B c : ℝ} (hB : 0 ≤ B) (hc0 : 0 < c) (n r : ℕ) (hr : 1 ≤ r) :
    spikeProfile B c n (-(n : ℤ) + (r : ℤ)) ≤ B * ((n : ℝ) / (r : ℝ)) ^ c := by
  have hnat : (((n : ℤ) + (-(n : ℤ) + (r : ℤ))).natAbs : ℝ) = (r : ℝ) := by
    have h : ((n : ℤ) + (-(n : ℤ) + (r : ℤ))) = (r : ℤ) := by ring
    rw [h]
    simp
  rw [spikeProfile, hnat]
  split_ifs with h
  · refine mul_le_mul_of_nonneg_left ?_ hB
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    refine Real.rpow_le_rpow (by positivity) ?_ hc0.le
    refine div_le_div_of_nonneg_left (by positivity) hr0 ?_
    linarith
  · positivity

theorem spikeProfile_neg_side {B c : ℝ} (hB : 0 ≤ B) (hc0 : 0 < c) (n r : ℕ) (hr : 1 ≤ r) :
    spikeProfile B c n (-(n : ℤ) - (r : ℤ)) ≤ B * ((n : ℝ) / (r : ℝ)) ^ c := by
  have hnat : (((n : ℤ) + (-(n : ℤ) - (r : ℤ))).natAbs : ℝ) = (r : ℝ) := by
    have h : ((n : ℤ) + (-(n : ℤ) - (r : ℤ))) = -(r : ℤ) := by ring
    rw [h]
    simp
  rw [spikeProfile, hnat]
  split_ifs with h
  · refine mul_le_mul_of_nonneg_left ?_ hB
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    refine Real.rpow_le_rpow (by positivity) ?_ hc0.le
    refine div_le_div_of_nonneg_left (by positivity) hr0 ?_
    linarith
  · positivity

/-- The peak of the spike. -/
theorem spikeProfile_peak_le {B c : ℝ} (hB : 0 ≤ B) (hc0 : 0 < c) (n : ℕ) :
    spikeProfile B c n (-(n : ℤ)) ≤ B * (n : ℝ) ^ c := by
  have hnat : (((n : ℤ) + (-(n : ℤ))).natAbs : ℝ) = 0 := by simp
  rw [spikeProfile, hnat]
  split_ifs with h
  · refine mul_le_mul_of_nonneg_left ?_ hB
    refine Real.rpow_le_rpow (by positivity) ?_ hc0.le
    simp
  · positivity

/-! ### The harmonic kernel transfers the whole spike with a bounded constant -/

/-- **One side of the spike passes into the bulk with a bounded constant.**  Frequencies
`-n + r`, `1 ≤ r ≤ N ≤ n/2`, sit at distance at least `n/2` from the origin, so a harmonic kernel
reads them with weight at most `K/(1 + n/4)`, while their total spike mass is at most
`B (n^c + n/(1-c))`. -/
theorem sum_kernel_mul_spikeProfile_pos_side_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) {n N : ℕ} (hN : 2 * N ≤ n)
    {κ : ℤ → ℂ} (hκ : ∀ l : ℤ, ‖κ l‖ ≤ K / (1 + (l.natAbs : ℝ)))
    {j : ℤ} (hj : 4 * (j.natAbs : ℝ) ≤ (n : ℝ)) :
    ∑ r ∈ Finset.Icc 1 N, ‖κ (j - (-(n : ℤ) + (r : ℤ)))‖ * spikeProfile B c n (-(n : ℤ) + (r : ℤ))
      ≤ K / (1 + (n : ℝ) / 4) * (B * ((n : ℝ) ^ c + (n : ℝ) / (1 - c))) := by
  refine le_trans (Finset.sum_le_sum fun r hr => ?_)
    (sum_kernel_mul_spike_band_le hc0 hc1 hK hB hN hκ hj (fun r => -(n : ℤ) + (r : ℤ)) ?_)
  · rw [Finset.mem_Icc] at hr
    exact mul_le_mul_of_nonneg_left (spikeProfile_pos_side hB hc0 n r hr.1) (norm_nonneg _)
  · intro r hr
    rw [Finset.mem_Icc] at hr
    have hrn : (r : ℝ) ≤ (n : ℝ) / 2 := by
      have : (2 * r : ℕ) ≤ n := le_trans (by omega) hN
      have hcast : (2 : ℝ) * (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
      linarith
    have hnat : ((-(n : ℤ) + (r : ℤ)).natAbs : ℝ) = (n : ℝ) - (r : ℝ) := by
      have hle : (r : ℤ) ≤ (n : ℤ) := by
        have : r ≤ n := by omega
        exact_mod_cast this
      have h : (-(n : ℤ) + (r : ℤ)).natAbs = n - r := by omega
      rw [h]
      have : r ≤ n := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hnat]
    linarith

/-- The mirror side. -/
theorem sum_kernel_mul_spikeProfile_neg_side_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) {n N : ℕ} (hN : 2 * N ≤ n)
    {κ : ℤ → ℂ} (hκ : ∀ l : ℤ, ‖κ l‖ ≤ K / (1 + (l.natAbs : ℝ)))
    {j : ℤ} (hj : 4 * (j.natAbs : ℝ) ≤ (n : ℝ)) :
    ∑ r ∈ Finset.Icc 1 N, ‖κ (j - (-(n : ℤ) - (r : ℤ)))‖ * spikeProfile B c n (-(n : ℤ) - (r : ℤ))
      ≤ K / (1 + (n : ℝ) / 4) * (B * ((n : ℝ) ^ c + (n : ℝ) / (1 - c))) := by
  refine le_trans (Finset.sum_le_sum fun r hr => ?_)
    (sum_kernel_mul_spike_band_le hc0 hc1 hK hB hN hκ hj (fun r => -(n : ℤ) - (r : ℤ)) ?_)
  · rw [Finset.mem_Icc] at hr
    exact mul_le_mul_of_nonneg_left (spikeProfile_neg_side hB hc0 n r hr.1) (norm_nonneg _)
  · intro r hr
    rw [Finset.mem_Icc] at hr
    have hnat : ((-(n : ℤ) - (r : ℤ)).natAbs : ℝ) = (n : ℝ) + (r : ℝ) := by
      have h : (-(n : ℤ) - (r : ℤ)).natAbs = n + r := by omega
      rw [h]
      push_cast
      ring
    rw [hnat]
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
    linarith

/-- **The peak term passes with the same constant.** -/
theorem kernel_mul_spikeProfile_peak_le {c : ℝ} (hc0 : 0 < c) {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    {n : ℕ} {κ : ℤ → ℂ} (hκ : ∀ l : ℤ, ‖κ l‖ ≤ K / (1 + (l.natAbs : ℝ)))
    {j : ℤ} (hj : 4 * (j.natAbs : ℝ) ≤ (n : ℝ)) :
    ‖κ (j - -(n : ℤ))‖ * spikeProfile B c n (-(n : ℤ)) ≤ K / (1 + (n : ℝ) / 4) * (B * (n : ℝ) ^ c)
      := by
  have hden : (0 : ℝ) < 1 + (n : ℝ) / 4 := by positivity
  have hnat : (n : ℝ) - (j.natAbs : ℝ) ≤ ((j - -(n : ℤ)).natAbs : ℝ) := by
    have h : (n : ℤ).natAbs ≤ j.natAbs + (j - -(n : ℤ)).natAbs := by
      have := Int.natAbs_sub_le (-(j : ℤ)) (-(j : ℤ) - (n : ℤ))
      omega
    have hcast : ((n : ℤ).natAbs : ℝ) ≤ (j.natAbs : ℝ) + ((j - -(n : ℤ)).natAbs : ℝ) := by
      exact_mod_cast h
    rw [Int.natAbs_natCast] at hcast
    linarith
  have hker : ‖κ (j - -(n : ℤ))‖ ≤ K / (1 + (n : ℝ) / 4) := by
    refine le_trans (hκ _) ?_
    refine div_le_div_of_nonneg_left hK hden ?_
    have hjn : (j.natAbs : ℝ) ≤ (n : ℝ) / 4 := by linarith
    linarith
  refine le_trans (mul_le_mul hker (spikeProfile_peak_le hB hc0 n)
    (spikeProfile_nonneg hB n _) (by positivity)) (le_of_eq rfl)


/-! ### The class is stable under a Fourier multiplier with a two-regime bound -/

/-- Inside the band the frequency is far from the origin. -/
theorem half_le_natAbs_of_mem_band {n : ℕ} {j : ℤ}
    (hj : 2 * ((((n : ℤ) + j).natAbs : ℝ)) < (n : ℝ)) : (n : ℝ) / 2 ≤ (j.natAbs : ℝ) := by
  have htri : (n : ℝ) ≤ (((n : ℤ) + j).natAbs : ℝ) + (j.natAbs : ℝ) := by
    have h : (n : ℤ).natAbs ≤ ((n : ℤ) + j).natAbs + j.natAbs := by omega
    have hcast : ((n : ℤ).natAbs : ℝ) ≤ ((((n : ℤ) + j).natAbs : ℝ)) + (j.natAbs : ℝ) := by
      exact_mod_cast h
    rwa [Int.natAbs_natCast] at hcast
  linarith

/-- Inside the band the spike base exceeds one. -/
theorem one_le_spikeBase {n : ℕ} (hn : 2 ≤ n) {j : ℤ}
    (hj : 2 * ((((n : ℤ) + j).natAbs : ℝ)) < (n : ℝ)) :
    (1 : ℝ) ≤ (n : ℝ) / (1 + (((n : ℤ) + j).natAbs : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : (0 : ℝ) < 1 + (((n : ℤ) + j).natAbs : ℝ) := by positivity
  rw [le_div_iff₀ hden]
  linarith

/-- **The two-piece class is stable under a Fourier multiplier.**  A multiplier bounded in the bulk
and by the spike profile inside the band keeps the class, at the cost of adding the multiplier's
exponent to the spike exponent and moving the uniform mass of the band into the spike. -/
theorem TwoPieceAmplitude.mul_multiplier {A θ B c c' K₁ K₂ : ℝ} {n : ℕ} {g : ℤ → ℂ}
    (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hc0 : 0 < c)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hn : 2 ≤ n)
    (hg : TwoPieceAmplitude A θ B c n g) (ρ : ℤ → ℂ)
    (hρbulk : ∀ j : ℤ, ¬ (2 * ((((n : ℤ) + j).natAbs : ℝ)) < (n : ℝ)) → ‖ρ j‖ ≤ K₁)
    (hρband : ∀ j : ℤ, 2 * ((((n : ℤ) + j).natAbs : ℝ)) < (n : ℝ) →
      ‖ρ j‖ ≤ K₂ * ((n : ℝ) / (1 + (((n : ℤ) + j).natAbs : ℝ))) ^ c') :
    TwoPieceAmplitude (K₁ * A) θ (K₂ * (A / (1 + (n : ℝ) / 2) ^ θ + B)) (c + c') n
      (fun j => ρ j * g j) := by
  intro j
  by_cases hband : 2 * ((((n : ℤ) + j).natAbs : ℝ)) < (n : ℝ)
  · set u : ℝ := (n : ℝ) / (1 + (((n : ℤ) + j).natAbs : ℝ)) with hu
    have hu1 : (1 : ℝ) ≤ u := one_le_spikeBase hn hband
    have hu0 : (0 : ℝ) < u := by linarith
    have hjfar : (n : ℝ) / 2 ≤ (j.natAbs : ℝ) := half_le_natAbs_of_mem_band hband
    have huni : A / (1 + (j.natAbs : ℝ)) ^ θ ≤ A / (1 + (n : ℝ) / 2) ^ θ := by
      have hpos : (0 : ℝ) < (1 + (n : ℝ) / 2) ^ θ := by positivity
      refine div_le_div_of_nonneg_left hA hpos ?_
      exact Real.rpow_le_rpow (by positivity) (by linarith) hθ
    have hgj : ‖g j‖ ≤ A / (1 + (n : ℝ) / 2) ^ θ + B * u ^ c := by
      have h := hg j
      rw [spikeProfile, if_pos hband] at h
      linarith
    have hρj : ‖ρ j‖ ≤ K₂ * u ^ c' := hρband j hband
    have hexp : u ^ c' ≤ u ^ (c + c') := Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
    have hexp2 : u ^ c * u ^ c' = u ^ (c + c') := by
      rw [← Real.rpow_add hu0]
    have hprod : ‖ρ j * g j‖ ≤ (K₂ * u ^ c') * (A / (1 + (n : ℝ) / 2) ^ θ + B * u ^ c) := by
      rw [norm_mul]
      refine mul_le_mul hρj hgj (norm_nonneg _) (by positivity)
    have hAterm : K₂ * u ^ c' * (A / (1 + (n : ℝ) / 2) ^ θ)
        ≤ K₂ * (A / (1 + (n : ℝ) / 2) ^ θ) * u ^ (c + c') := by
      have hnn : (0 : ℝ) ≤ K₂ * (A / (1 + (n : ℝ) / 2) ^ θ) := by positivity
      nlinarith [hexp, hnn]
    have hBterm : K₂ * u ^ c' * (B * u ^ c) = K₂ * B * u ^ (c + c') := by
      rw [← hexp2]; ring
    have hfinal : (K₂ * u ^ c') * (A / (1 + (n : ℝ) / 2) ^ θ + B * u ^ c)
        ≤ K₂ * (A / (1 + (n : ℝ) / 2) ^ θ + B) * u ^ (c + c') := by
      nlinarith [hAterm, hBterm]
    rw [spikeProfile, if_pos hband, ← hu]
    have hpos : (0 : ℝ) ≤ K₁ * A / (1 + (j.natAbs : ℝ)) ^ θ := by positivity
    linarith [hprod, hfinal]
  · have hgj : ‖g j‖ ≤ A / (1 + (j.natAbs : ℝ)) ^ θ := by
      have h := hg j
      rw [spikeProfile, if_neg hband] at h
      linarith
    have hρj : ‖ρ j‖ ≤ K₁ := hρbulk j hband
    have hprod : ‖ρ j * g j‖ ≤ K₁ * (A / (1 + (j.natAbs : ℝ)) ^ θ) := by
      rw [norm_mul]
      refine mul_le_mul hρj hgj (norm_nonneg _) hK₁
    rw [spikeProfile, if_neg hband]
    have hrw : K₁ * (A / (1 + (j.natAbs : ℝ)) ^ θ) = K₁ * A / (1 + (j.natAbs : ℝ)) ^ θ := by
      ring
    rw [hrw] at hprod
    linarith

end RHTower
