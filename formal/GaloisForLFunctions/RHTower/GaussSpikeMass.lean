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

end RHTower
