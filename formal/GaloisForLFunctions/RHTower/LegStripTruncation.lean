/-
# The truncation asymptotic `A_trunc/i ≲ i/d` — the rational envelope

The edge-law margin `g(i)/i = A_trunc/i − ε(i)` has a truncation term `A_trunc/i → i/d`: the finite pole
count `d` cuts the ahead train at rank `d − i`, removing `A_trunc = Σ_{k ≥ d−i} poleExcess(ahead_k)`.
This file bounds that removed tail by the exact **digamma partial-fraction envelope**, reusing the
harmonic-log primitives (`sum_log_step`, `log_step_bounds`).

The mechanism: the harmonic ahead distance dominates a logarithm (`aheadHarm_ge_log`,
`Σ_{j<k}1/(i+j+1) ≥ log((i+k+1)/(i+1))`), so `exp(ahead_k) ≥ ((i+k+1)/(i+1))²` and the `coth`-excess
`poleExcess(ahead_k)` is below the rational `(i+1)²/(k(k+2i+2))` (`poleExcess_ahead_le_rational`); its
tail telescopes (partial fraction, shift `2i+2`) to `(i+1)²/M` (`trunc_rational_tail_le`), so
`A_trunc = Σ_{k≥d−i} poleExcess(ahead_k) ≤ (i+1)²/(d−i)` (`trunc_ahead_le`) — the `i²/d` scale.
-/
import GaloisForLFunctions.RHTower.LegStripThreshold
import GaloisForLFunctions.RHTower.DigammaAsymptotic
open Real Filter Topology
noncomputable section
namespace RHTower

/-- **The harmonic ahead distance dominates a logarithm.** `Σ_{j<k} 1/(i+j+1) ≥ log((i+k+1)/(i+1))`:
each step `1/(i+j+1) ≥ log((i+j+2)/(i+j+1))`, telescoping (the reverse of `harmonic_log_lower`). -/
theorem aheadHarm_ge_log (i k : ℕ) :
    Real.log (((i:ℝ)+k+1)/((i:ℝ)+1)) ≤ ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1) := by
  rw [show ((i:ℝ)+k+1)/((i:ℝ)+1) = (((i+1:ℕ):ℝ)+k)/((i+1:ℕ):ℝ) by push_cast; ring,
    ← sum_log_step (i+1) (by omega) k]
  apply Finset.sum_le_sum
  intro j _
  have hy : (0:ℝ) < (i:ℝ)+j+1 := by positivity
  have hstep := (log_step_bounds hy).2
  rw [show (((i+1:ℕ):ℝ)+j+1)/(((i+1:ℕ):ℝ)+j) = ((i:ℝ)+j+1+1)/((i:ℝ)+j+1) by push_cast; ring]
  exact hstep

/-- **The rational envelope for one ahead `coth`-excess.** For the harmonic ahead distance
`u = 1/i + 2·Σ_{j<k}1/(i+j+1)` (the `c=2` pole-model ahead distance), `poleExcess(u) ≤ (i+1)²/(k(k+2i+2))`:
from `u ≥ 2·log((i+k+1)/(i+1))`, `exp(u) − 1 ≥ (k(k+2i+2))/(i+1)²`. -/
theorem poleExcess_ahead_le_rational (i k : ℕ) (hi : 1 ≤ i) (hk : 1 ≤ k) :
    poleExcess (1/(i:ℝ) + 2 * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1))
      ≤ (((i:ℝ)+1)^2)/((k:ℝ)*((k:ℝ)+2*(i:ℝ)+2)) := by
  have hipos : (0:ℝ) < (i:ℝ) := by exact_mod_cast hi
  have hi1 : (0:ℝ) < (i:ℝ)+1 := by positivity
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hlog := aheadHarm_ge_log i k
  set u := 1/(i:ℝ) + 2 * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1) with hu
  have hsum_nonneg : (0:ℝ) ≤ ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1) := by
    apply Finset.sum_nonneg; intro j _
    have : (0:ℝ) < (i:ℝ)+j+1 := by positivity
    positivity
  have hupos : (0:ℝ) < u := by rw [hu]; positivity
  have hu_ge : 2 * Real.log (((i:ℝ)+k+1)/((i:ℝ)+1)) ≤ u := by
    rw [hu]; linarith [hlog, (show (0:ℝ) ≤ 1/(i:ℝ) by positivity)]
  have hexp : (((i:ℝ)+k+1)/((i:ℝ)+1))^2 ≤ Real.exp u := by
    calc (((i:ℝ)+k+1)/((i:ℝ)+1))^2
        = Real.exp (2 * Real.log (((i:ℝ)+k+1)/((i:ℝ)+1))) := by
          rw [show (2:ℝ) * Real.log (((i:ℝ)+k+1)/((i:ℝ)+1))
              = Real.log (((i:ℝ)+k+1)/((i:ℝ)+1)) + Real.log (((i:ℝ)+k+1)/((i:ℝ)+1)) by ring,
            Real.exp_add, Real.exp_log (by positivity)]; ring
      _ ≤ Real.exp u := Real.exp_le_exp.mpr hu_ge
  have hsq : (((i:ℝ)+k+1)/((i:ℝ)+1))^2 - 1 = ((k:ℝ)*((k:ℝ)+2*(i:ℝ)+2))/(((i:ℝ)+1)^2) := by
    field_simp; ring
  have hden : ((k:ℝ)*((k:ℝ)+2*(i:ℝ)+2))/(((i:ℝ)+1)^2) ≤ Real.exp u - 1 := by linarith [hexp, hsq]
  have hepos : (0:ℝ) < Real.exp u - 1 := by linarith [Real.one_lt_exp_iff.mpr hupos]
  have hnpos : (0:ℝ) < (k:ℝ)*((k:ℝ)+2*(i:ℝ)+2) := by positivity
  rw [poleExcess, div_le_div_iff₀ hepos hnpos, one_mul]
  have hi1sq : (0:ℝ) < ((i:ℝ)+1)^2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hden hi1sq.le
  have hcancel : ((i:ℝ)+1)^2 * (((k:ℝ)*((k:ℝ)+2*(i:ℝ)+2))/(((i:ℝ)+1)^2))
      = (k:ℝ)*((k:ℝ)+2*(i:ℝ)+2) := by field_simp
  rw [hcancel] at hmul
  linarith [hmul]

/-- **The rational envelope tail bound.** `Σ_{M≤k<N} (i+1)²/(k(k+2i+2)) ≤ (i+1)²/(M−1)`: each term is
below `(i+1)²/k²`, whose tail sums (telescoping, `sum_inv_sq_shift_le`) to `1/(M−1)`. -/
theorem trunc_rational_tail_le (i M N : ℕ) (hM : 2 ≤ M) :
    (∑ k ∈ Finset.Ico M N, (((i:ℝ)+1)^2)/((k:ℝ)*((k:ℝ)+2*(i:ℝ)+2)))
      ≤ (((i:ℝ)+1)^2)/((M:ℝ)-1) := by
  have hi1sq : (0:ℝ) ≤ ((i:ℝ)+1)^2 := by positivity
  have hstep : (∑ k ∈ Finset.Ico M N, (((i:ℝ)+1)^2)/((k:ℝ)*((k:ℝ)+2*(i:ℝ)+2)))
      ≤ ∑ k ∈ Finset.Ico M N, (((i:ℝ)+1)^2)/((k:ℝ)^2) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
    gcongr
    nlinarith [hkpos]
  have hfac : (∑ k ∈ Finset.Ico M N, (((i:ℝ)+1)^2)/((k:ℝ)^2))
      = ((i:ℝ)+1)^2 * ∑ k ∈ Finset.Ico M N, (1:ℝ)/(k:ℝ)^2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  have hsq : (∑ k ∈ Finset.Ico M N, (1:ℝ)/(k:ℝ)^2) ≤ 1/((M:ℝ)-1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hM1 : 1 ≤ M - 1 := by omega
    have hshift := sum_inv_sq_shift_le hM1 (N - M)
    have hcastM : ((M - 1 : ℕ):ℝ) = (M:ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hcastM] at hshift
    refine le_trans (le_of_eq ?_) hshift
    apply Finset.sum_congr rfl
    intro r _
    have : ((M + r : ℕ):ℝ) = (M:ℝ) - 1 + 1 + (r:ℝ) := by push_cast; ring
    rw [this]
  calc (∑ k ∈ Finset.Ico M N, (((i:ℝ)+1)^2)/((k:ℝ)*((k:ℝ)+2*(i:ℝ)+2)))
      ≤ ∑ k ∈ Finset.Ico M N, (((i:ℝ)+1)^2)/((k:ℝ)^2) := hstep
    _ = ((i:ℝ)+1)^2 * ∑ k ∈ Finset.Ico M N, (1:ℝ)/(k:ℝ)^2 := hfac
    _ ≤ ((i:ℝ)+1)^2 * (1/((M:ℝ)-1)) := by gcongr
    _ = (((i:ℝ)+1)^2)/((M:ℝ)-1) := by ring

/-- **The truncation bound.** The ahead excess removed by the finite pole count `d` — the sum over the
far-ahead poles `k ∈ [d−i, N)` — is at most `(i+1)²/(d−i−1)`:
`A_trunc = Σ poleExcess(ahead_k) ≤ Σ (i+1)²/(k(k+2i+2)) ≤ (i+1)²/(d−i−1)`. Dividing by `i`, the removed
mass scales as `i/d` — the truncation term of `g(i)/i`. -/
theorem trunc_ahead_le (i M N : ℕ) (hi : 1 ≤ i) (hM : 2 ≤ M) :
    (∑ k ∈ Finset.Ico M N,
        poleExcess (1/(i:ℝ) + 2 * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)))
      ≤ (((i:ℝ)+1)^2)/((M:ℝ)-1) := by
  refine le_trans (Finset.sum_le_sum (fun k hk => ?_)) (trunc_rational_tail_le i M N hM)
  rw [Finset.mem_Ico] at hk
  exact poleExcess_ahead_le_rational i k hi (by omega)

/-- `exp(1/i) ≤ i/(i−1)` for `i ≥ 2` — from `1 − x ≤ e^{−x}` (`add_one_le_exp`) reciprocated. -/
theorem exp_inv_le {i : ℕ} (hi : 2 ≤ i) : Real.exp (1/(i:ℝ)) ≤ (i:ℝ)/((i:ℝ)-1) := by
  have hir : (2:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
  have hi1 : (0:ℝ) < (i:ℝ)-1 := by linarith
  have hipos : (0:ℝ) < (i:ℝ) := by linarith
  have h1 : ((i:ℝ)-1)/(i:ℝ) ≤ Real.exp (-(1/(i:ℝ))) := by
    have hb := Real.add_one_le_exp (-(1/(i:ℝ)))
    have he : ((i:ℝ)-1)/(i:ℝ) = 1 + (-(1/(i:ℝ))) := by
      field_simp; ring
    rw [he]; linarith
  have h2 : Real.exp (1/(i:ℝ)) = (Real.exp (-(1/(i:ℝ))))⁻¹ := by rw [Real.exp_neg, inv_inv]
  rw [h2, show (i:ℝ)/((i:ℝ)-1) = (((i:ℝ)-1)/(i:ℝ))⁻¹ by rw [inv_div]]
  exact inv_anti₀ (by positivity) h1

/-- **The rational envelope from below.** `poleExcess(ahead_k) ≥ i(i−1)/(k(k+2i)+i)` (`i ≥ 2`, `k ≥ 1`):
from `Σ_{j<k}1/(i+j+1) ≤ log((i+k)/i)` (`harmonic_log_lower`) and `e^{1/i} ≤ i/(i−1)`, the excess
`e^{ahead_k} − 1 ≤ (k(k+2i)+i)/(i(i−1))`. Paired with `poleExcess_ahead_le_rational`, it sandwiches the
exact `poleExcess`, both sides `→ i²/(k(k+2i))`. -/
theorem poleExcess_ahead_ge_rational (i k : ℕ) (hi : 2 ≤ i) (hk : 1 ≤ k) :
    ((i:ℝ)*((i:ℝ)-1))/((k:ℝ)*((k:ℝ)+2*(i:ℝ)) + (i:ℝ))
      ≤ poleExcess (1/(i:ℝ) + 2 * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)) := by
  have hir : (2:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
  have hi1 : (0:ℝ) < (i:ℝ)-1 := by linarith
  have hipos : (0:ℝ) < (i:ℝ) := by linarith
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hlog := harmonic_log_lower i (by omega) k
  set u := 1/(i:ℝ) + 2 * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1) with hu
  have hsum_nonneg : (0:ℝ) ≤ ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1) := by
    apply Finset.sum_nonneg; intro j _
    have : (0:ℝ) < (i:ℝ)+j+1 := by positivity
    positivity
  have hupos : (0:ℝ) < u := by rw [hu]; positivity
  -- u ≤ 1/i + 2 log((i+k)/i)
  have hu_le : u ≤ 1/(i:ℝ) + 2 * Real.log (((i:ℝ)+k)/(i:ℝ)) := by rw [hu]; linarith [hlog]
  -- e^u ≤ e^{1/i} · ((i+k)/i)² ≤ (i/(i-1)) ((i+k)/i)²
  have hlogpos : (0:ℝ) < ((i:ℝ)+k)/(i:ℝ) := by positivity
  have hexp_u : Real.exp u ≤ ((i:ℝ)/((i:ℝ)-1)) * (((i:ℝ)+k)/(i:ℝ))^2 := by
    calc Real.exp u ≤ Real.exp (1/(i:ℝ) + 2 * Real.log (((i:ℝ)+k)/(i:ℝ))) :=
          Real.exp_le_exp.mpr hu_le
      _ = Real.exp (1/(i:ℝ)) * (((i:ℝ)+k)/(i:ℝ))^2 := by
          rw [Real.exp_add, show (2:ℝ) * Real.log (((i:ℝ)+k)/(i:ℝ))
              = Real.log (((i:ℝ)+k)/(i:ℝ)) + Real.log (((i:ℝ)+k)/(i:ℝ)) by ring,
            Real.exp_add, Real.exp_log hlogpos]; ring
      _ ≤ ((i:ℝ)/((i:ℝ)-1)) * (((i:ℝ)+k)/(i:ℝ))^2 := by
          apply mul_le_mul_of_nonneg_right (exp_inv_le hi) (by positivity)
  -- e^u − 1 ≤ (k(k+2i)+i)/(i(i-1))
  have hbound : Real.exp u - 1 ≤ ((k:ℝ)*((k:ℝ)+2*(i:ℝ)) + (i:ℝ))/((i:ℝ)*((i:ℝ)-1)) := by
    have hine : (i:ℝ) ≠ 0 := ne_of_gt hipos
    have hi1ne : (i:ℝ)-1 ≠ 0 := ne_of_gt hi1
    have hrw : ((i:ℝ)/((i:ℝ)-1)) * (((i:ℝ)+k)/(i:ℝ))^2 - 1
        = ((k:ℝ)*((k:ℝ)+2*(i:ℝ)) + (i:ℝ))/((i:ℝ)*((i:ℝ)-1)) := by
      field_simp; ring
    linarith [hexp_u, hrw]
  have hepos : (0:ℝ) < Real.exp u - 1 := by linarith [Real.one_lt_exp_iff.mpr hupos]
  have hnpos : (0:ℝ) < (k:ℝ)*((k:ℝ)+2*(i:ℝ)) + (i:ℝ) := by positivity
  rw [poleExcess]
  rw [div_le_div_iff₀ hnpos hepos, one_mul]
  have hmul := mul_le_mul_of_nonneg_left hbound (show (0:ℝ) ≤ (i:ℝ)*((i:ℝ)-1) by positivity)
  have hcancel : (i:ℝ)*((i:ℝ)-1) * (((k:ℝ)*((k:ℝ)+2*(i:ℝ)) + (i:ℝ))/((i:ℝ)*((i:ℝ)-1)))
      = (k:ℝ)*((k:ℝ)+2*(i:ℝ)) + (i:ℝ) := by field_simp
  rw [hcancel] at hmul
  nlinarith [hmul, hepos, hi1, hipos]

/-- **The shift telescope.** `Σ_{M≤k<N} (f k − f(k+m)) = Σ_{M≤k<M+m} f − Σ_{N≤k<N+m} f` for `M+m ≤ N`:
the middle block `Ico(M+m) N` cancels. -/
theorem sum_shift_telescope (f : ℕ → ℝ) (M N m : ℕ) (hMN : M + m ≤ N) :
    (∑ k ∈ Finset.Ico M N, (f k - f (k+m)))
      = (∑ k ∈ Finset.Ico M (M+m), f k) - ∑ k ∈ Finset.Ico N (N+m), f k := by
  rw [Finset.sum_sub_distrib]
  have hshift : (∑ k ∈ Finset.Ico M N, f (k+m)) = ∑ k ∈ Finset.Ico (M+m) (N+m), f k := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_add_right]
    apply Finset.sum_congr rfl; intro j _; congr 1; omega
  rw [hshift]
  have h1 : (∑ k ∈ Finset.Ico M (M+m), f k) + ∑ k ∈ Finset.Ico (M+m) N, f k
      = ∑ k ∈ Finset.Ico M N, f k := Finset.sum_Ico_consecutive f (by omega) hMN
  have h2 : (∑ k ∈ Finset.Ico (M+m) N, f k) + ∑ k ∈ Finset.Ico N (N+m), f k
      = ∑ k ∈ Finset.Ico (M+m) (N+m), f k := Finset.sum_Ico_consecutive f hMN (by omega)
  linarith [h1, h2]

/-- **The exact upper-envelope sum (digamma partial fraction).** With `m = 2i+2`,
`Σ_{M≤k<N} (i+1)²/(k(k+2i+2)) = ((i+1)/2)·(Σ_{M≤k<M+m} 1/k − Σ_{N≤k<N+m} 1/k)` — the rational tail is
`((i+1)/2)` times a harmonic block of `2i+2` terms near `M`, which is the `~ i²/d` truncation mass. -/
theorem trunc_upper_sum_eq (i M N : ℕ) (hi : 1 ≤ i) (hMN : M + (2*i+2) ≤ N) (hM : 1 ≤ M) :
    (∑ k ∈ Finset.Ico M N, (((i:ℝ)+1)^2)/((k:ℝ)*((k:ℝ)+2*(i:ℝ)+2)))
      = ((i:ℝ)+1)/2 * ((∑ k ∈ Finset.Ico M (M+(2*i+2)), 1/(k:ℝ))
          - ∑ k ∈ Finset.Ico N (N+(2*i+2)), 1/(k:ℝ)) := by
  have hpf : ∀ k ∈ Finset.Ico M N, (((i:ℝ)+1)^2)/((k:ℝ)*((k:ℝ)+2*(i:ℝ)+2))
      = ((i:ℝ)+1)/2 * (1/(k:ℝ) - 1/((k:ℝ)+2*(i:ℝ)+2)) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hkden : (0:ℝ) < (k:ℝ)+2*(i:ℝ)+2 := by positivity
    field_simp
    ring
  rw [Finset.sum_congr rfl hpf, ← Finset.mul_sum]
  congr 1
  have hcast : ∀ k : ℕ, (1:ℝ)/((k:ℝ)+2*(i:ℝ)+2) = 1/((k + (2*i+2) : ℕ):ℝ) := by
    intro k; congr 1; push_cast; ring
  rw [Finset.sum_congr rfl (fun k _ => by rw [hcast k])]
  exact sum_shift_telescope (fun k => 1/(k:ℝ)) M N (2*i+2) hMN

/-- **Harmonic block, upper.** `Σ_{M≤k<M+m} 1/k ≤ m/M` — each of the `m` terms is `≤ 1/M`. -/
theorem harmonic_block_le (M m : ℕ) (hM : 1 ≤ M) :
    (∑ k ∈ Finset.Ico M (M+m), 1/(k:ℝ)) ≤ (m:ℝ)/(M:ℝ) := by
  have hMr : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hle : (∑ k ∈ Finset.Ico M (M+m), 1/(k:ℝ)) ≤ ∑ _k ∈ Finset.Ico M (M+m), 1/(M:ℝ) := by
    apply Finset.sum_le_sum; intro k hk; rw [Finset.mem_Ico] at hk
    have hk' : (M:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
    exact one_div_le_one_div_of_le hMr hk'
  rw [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul, mul_one_div] at hle
  exact hle

/-- **Harmonic block, lower.** `m/(M+m) ≤ Σ_{M≤k<M+m} 1/k` — each of the `m` terms is `≥ 1/(M+m)`. -/
theorem harmonic_block_ge (M m : ℕ) (hM : 1 ≤ M) :
    (m:ℝ)/((M:ℝ)+(m:ℝ)) ≤ ∑ k ∈ Finset.Ico M (M+m), 1/(k:ℝ) := by
  have hMm : (0:ℝ) < (M:ℝ)+(m:ℝ) := by
    have : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
    positivity
  have hge : (∑ _k ∈ Finset.Ico M (M+m), 1/((M:ℝ)+(m:ℝ))) ≤ ∑ k ∈ Finset.Ico M (M+m), 1/(k:ℝ) := by
    apply Finset.sum_le_sum; intro k hk; rw [Finset.mem_Ico] at hk
    have hk' : (k:ℝ) ≤ (M:ℝ)+(m:ℝ) := by
      have : (k:ℝ) < ((M+m:ℕ):ℝ) := by exact_mod_cast hk.2
      push_cast at this; linarith
    have hkpos : (0:ℝ) < (k:ℝ) := by
      have : (M:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
      have : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
      linarith
    exact one_div_le_one_div_of_le hkpos hk'
  rw [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul, mul_one_div] at hge
  exact hge

/-- The lower rational in telescoping form: `poleExcess(ahead_k) ≥ i(i−1)/((k+1)(k+2i+1))`, since
`k(k+2i)+i ≤ (k+1)(k+2i+1)`. -/
theorem poleExcess_ahead_ge_rational_tel (i k : ℕ) (hi : 2 ≤ i) (hk : 1 ≤ k) :
    ((i:ℝ)*((i:ℝ)-1))/(((k:ℝ)+1)*((k:ℝ)+2*(i:ℝ)+1))
      ≤ poleExcess (1/(i:ℝ) + 2 * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)) := by
  refine le_trans ?_ (poleExcess_ahead_ge_rational i k hi hk)
  have hir : (2:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hn1 : (0:ℝ) < (k:ℝ)*((k:ℝ)+2*(i:ℝ)) + (i:ℝ) := by positivity
  have hn2 : (0:ℝ) < ((k:ℝ)+1)*((k:ℝ)+2*(i:ℝ)+1) := by positivity
  have hnum : (0:ℝ) ≤ (i:ℝ)*((i:ℝ)-1) := by nlinarith [hir]
  apply div_le_div_of_nonneg_left hnum hn1
  nlinarith [hkpos, hir]

/-- **The exact lower-envelope sum.** `Σ_{M≤k<N} i(i−1)/((k+1)(k+2i+1))
= ((i−1)/2)·(Σ_{M≤k<M+2i} 1/(k+1) − Σ_{N≤k<N+2i} 1/(k+1))`. -/
theorem trunc_lower_sum_eq (i M N : ℕ) (hi : 1 ≤ i) (hMN : M + 2*i ≤ N) :
    (∑ k ∈ Finset.Ico M N, ((i:ℝ)*((i:ℝ)-1))/(((k:ℝ)+1)*((k:ℝ)+2*(i:ℝ)+1)))
      = ((i:ℝ)-1)/2 * ((∑ k ∈ Finset.Ico M (M+2*i), 1/((k:ℝ)+1))
          - ∑ k ∈ Finset.Ico N (N+2*i), 1/((k:ℝ)+1)) := by
  have hir : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
  have hipos : (0:ℝ) < (i:ℝ) := by linarith
  have hpf : ∀ k ∈ Finset.Ico M N, ((i:ℝ)*((i:ℝ)-1))/(((k:ℝ)+1)*((k:ℝ)+2*(i:ℝ)+1))
      = ((i:ℝ)-1)/2 * (1/((k:ℝ)+1) - 1/((k:ℝ)+2*(i:ℝ)+1)) := by
    intro k _
    have hk1 : (0:ℝ) < (k:ℝ)+1 := by positivity
    have hk2 : (0:ℝ) < (k:ℝ)+2*(i:ℝ)+1 := by positivity
    field_simp
    ring
  rw [Finset.sum_congr rfl hpf, ← Finset.mul_sum]
  congr 1
  have hcast : ∀ k : ℕ, (1:ℝ)/((k:ℝ)+2*(i:ℝ)+1) = 1/(((k + 2*i : ℕ):ℝ)+1) := by
    intro k; congr 1; push_cast; ring
  rw [Finset.sum_congr rfl (fun k _ => by rw [hcast k])]
  exact sum_shift_telescope (fun k => 1/((k:ℝ)+1)) M N (2*i) hMN

/-- **The truncation mass, two-sided.** The removed ahead excess `A_trunc = Σ_{M≤k<N} poleExcess(ahead_k)`
is trapped between two explicit rationals, both `~ i²/d` at `M = d−i`:

> `((i−1)/2)·(Σ_{M≤k<M+2i}1/(k+1) − Σ_{N≤k<N+2i}1/(k+1)) ≤ A_trunc ≤ (i+1)²/(M−1)`.

The lower is the exact digamma partial-fraction sum of `poleExcess_ahead_ge_rational_tel`; the upper is
`trunc_ahead_le`. Both harmonic blocks are `≤ 2i/M` (`harmonic_block_le`) and `≥ 2i/(M+2i)`
(`harmonic_block_ge`), so `A_trunc = (i²/d)(1 + o(1))` in the joint `i,d → ∞` limit. -/
theorem trunc_ahead_two_sided (i M N : ℕ) (hi : 2 ≤ i) (hM : 2 ≤ M) (hMN : M + 2*i ≤ N) :
    ((i:ℝ)-1)/2 * ((∑ k ∈ Finset.Ico M (M+2*i), 1/((k:ℝ)+1))
        - ∑ k ∈ Finset.Ico N (N+2*i), 1/((k:ℝ)+1))
      ≤ (∑ k ∈ Finset.Ico M N,
          poleExcess (1/(i:ℝ) + 2 * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)))
    ∧ (∑ k ∈ Finset.Ico M N,
          poleExcess (1/(i:ℝ) + 2 * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)))
      ≤ (((i:ℝ)+1)^2)/((M:ℝ)-1) := by
  refine ⟨?_, trunc_ahead_le i M N (by omega) hM⟩
  rw [← trunc_lower_sum_eq i M N (by omega) hMN]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_Ico] at hk
  exact poleExcess_ahead_ge_rational_tel i k hi (by omega)

end RHTower
end
