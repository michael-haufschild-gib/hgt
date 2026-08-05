import GaloisForLFunctions.HTGeometry.RatioBoundedWindowLanding
import GaloisForLFunctions.RHTower.Sieve.DirichletBlockSaving

/-!
# The order schedule for a dyadic Dirichlet block

The derivative scale of the `k`-th derivative test on a block based at `N` is

```text
λ_k = (t / 2π) · (k-1)! / (2N)^k,
```

and raising the order by one multiplies it by `(k-1)/(2N)`.  For orders at least three the factor is
at least `1/N`, so the scale never falls by more than a factor `N` in a single step.  The saving
window `[N^(-5/3), N^(-1/3)]` of `block_saving_wide` is `N^(4/3)` wide, hence wider than one step,
and the window-landing principle produces an admissible order outright.

Combining with the normalised block bound gives the per-block estimate the dyadic assembly needs: on
every block carrying a schedulable order the Dirichlet sum on the line `Re s = 1` is at most
`2560 · N^(-1/(3·2^k))`.
-/

namespace RHTower.Sieve

open GaloisForLFunctions.HTGeometry

/-- The derivative scale of the `k`-th derivative test on the block based at `N`. -/
noncomputable def blockLambda (t : ℝ) (N k : ℕ) : ℝ :=
  t / (2 * Real.pi) * (Nat.factorial (k - 1) : ℝ) / (2 * (N : ℝ)) ^ k

theorem blockLambda_pos {t : ℝ} (ht : 0 < t) {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    0 < blockLambda t N k := by
  have hπ := Real.pi_pos
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hfac : (0 : ℝ) < (Nat.factorial (k - 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (k - 1)
  have hden : (0 : ℝ) < (2 * (N : ℝ)) ^ k := by positivity
  rw [blockLambda]
  positivity

/-- Raising the order multiplies the scale by `(k-1)/(2N)`; from order three on this is at least
`1/N`. -/
theorem blockLambda_ratio {t : ℝ} (ht : 0 < t) {N : ℕ} (hN : 1 ≤ N) {m : ℕ} (hm : 2 < m) :
    (1 / (N : ℝ)) * blockLambda t N (m - 1) ≤ blockLambda t N m := by
  have hπ := Real.pi_pos
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 2 := ⟨m - 2, by omega⟩
  have hi : 1 ≤ i := by omega
  have hred : i + 2 - 1 = i + 1 := by omega
  have hred2 : i + 1 - 1 = i := by omega
  have hstep : blockLambda t N (i + 2)
      = blockLambda t N (i + 1) * (((i : ℝ) + 1) / (2 * (N : ℝ))) := by
    simp only [blockLambda, hred, hred2]
    have hfac : (Nat.factorial (i + 1) : ℝ) = ((i : ℝ) + 1) * (Nat.factorial i : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hden : ((2 : ℝ) * (N : ℝ)) ^ (i + 2)
        = ((2 : ℝ) * (N : ℝ)) ^ (i + 1) * (2 * (N : ℝ)) := pow_succ _ _
    have h2N : ((2 : ℝ) * (N : ℝ)) ≠ 0 := by positivity
    have hpow : (((2 : ℝ) * (N : ℝ)) ^ (i + 1)) ≠ 0 := by positivity
    rw [hfac, hden]
    field_simp
  have hbase : 0 < blockLambda t N (i + 1) := blockLambda_pos ht hN (i + 1)
  have hcmp : (1 : ℝ) / (N : ℝ) ≤ ((i : ℝ) + 1) / (2 * (N : ℝ)) := by
    rw [div_le_div_iff₀ hN0 (by positivity)]
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    nlinarith [hN0]
  rw [hred, hstep]
  calc (1 / (N : ℝ)) * blockLambda t N (i + 1)
      = blockLambda t N (i + 1) * (1 / (N : ℝ)) := by ring
    _ ≤ blockLambda t N (i + 1) * (((i : ℝ) + 1) / (2 * (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hcmp hbase.le

/-- **Schedulable order.**  If the scale starts above the window bottom and reaches the window top
at order `k₀`, some order at most `k₀` lands inside the saving window. -/
theorem exists_blockLambda_in_window {t : ℝ} (ht : 0 < t) {N k₀ : ℕ} (hN : 1 ≤ N)
    (hk₀ : 2 ≤ k₀)
    (hstart : (N : ℝ) ^ (-(5 / 3) : ℝ) ≤ blockLambda t N 2)
    (hdrop : blockLambda t N k₀ ≤ (N : ℝ) ^ (-(1 / 3) : ℝ)) :
    ∃ k, 2 ≤ k ∧ k ≤ k₀ ∧ (N : ℝ) ^ (-(5 / 3) : ℝ) ≤ blockLambda t N k
      ∧ blockLambda t N k ≤ (N : ℝ) ^ (-(1 / 3) : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hwidth : (N : ℝ) ^ (-(5 / 3) : ℝ) ≤ (1 / (N : ℝ)) * (N : ℝ) ^ (-(1 / 3) : ℝ) := by
    have hinv : (1 : ℝ) / (N : ℝ) = (N : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, one_div]
    rw [hinv, ← Real.rpow_add hN0]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    norm_num
  exact exists_mem_window_of_ratio_lower_bound (by positivity)
    (fun m hm => blockLambda_ratio ht hN hm) hstart hwidth hk₀ hdrop

/-! ## Discharging the two schedule hypotheses -/

/-- The scale at order two exceeds the window bottom as soon as `t` is at least `8π N^(1/3)`. -/
theorem blockLambda_two_ge {t : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (ht : 8 * Real.pi * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ t) :
    (N : ℝ) ^ (-(5 / 3) : ℝ) ≤ blockLambda t N 2 := by
  have hπ := Real.pi_pos
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hval : blockLambda t N 2 = t / (8 * Real.pi * (N : ℝ) ^ (2 : ℕ)) := by
    simp only [blockLambda]
    norm_num [Nat.factorial]
    rw [mul_pow]
    field_simp
    norm_num
  have hsq : (N : ℝ) ^ (2 : ℕ) * (N : ℝ) ^ (-(5 / 3) : ℝ) = (N : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_add hN0]
    norm_num
  rw [hval, le_div_iff₀ (by positivity)]
  calc (N : ℝ) ^ (-(5 / 3) : ℝ) * (8 * Real.pi * (N : ℝ) ^ (2 : ℕ))
      = 8 * Real.pi * ((N : ℝ) ^ (2 : ℕ) * (N : ℝ) ^ (-(5 / 3) : ℝ)) := by ring
    _ = 8 * Real.pi * (N : ℝ) ^ ((1 : ℝ) / 3) := by rw [hsq]
    _ ≤ t := ht

/-- The scale at order `k` falls below the window top as soon as `t` is at most
`2π · 2^k · N^(2/3)`, provided the order does not exceed `N + 1`. -/
theorem blockLambda_le_of_order {t : ℝ} (ht : 0 < t) {N k : ℕ} (hN : 1 ≤ N) (hk : 2 ≤ k)
    (hkN : k - 1 ≤ N) (htk : t ≤ 2 * Real.pi * 2 ^ k * (N : ℝ) ^ ((2 : ℝ) / 3)) :
    blockLambda t N k ≤ (N : ℝ) ^ (-(1 / 3) : ℝ) := by
  have hπ := Real.pi_pos
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj : 1 ≤ j := by omega
  have hjN : j ≤ N := by omega
  have hfacnat : Nat.factorial j ≤ N ^ j := by
    calc Nat.factorial j ≤ j ^ j := Nat.factorial_le_pow j
      _ ≤ N ^ j := Nat.pow_le_pow_left hjN j
  have hfac : (Nat.factorial j : ℝ) ≤ (N : ℝ) ^ j := by exact_mod_cast hfacnat
  have hden : ((2 : ℝ) * (N : ℝ)) ^ (j + 1) = 2 ^ (j + 1) * (N : ℝ) ^ (j + 1) := mul_pow 2 _ _
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (j + 1) * (N : ℝ) ^ (j + 1) := by positivity
  have hstep : blockLambda t N (j + 1)
      ≤ t / (2 * Real.pi) * (N : ℝ) ^ j / (2 ^ (j + 1) * (N : ℝ) ^ (j + 1)) := by
    simp only [blockLambda, Nat.add_sub_cancel, hden]
    gcongr
  have hcollapse : t / (2 * Real.pi) * (N : ℝ) ^ j / (2 ^ (j + 1) * (N : ℝ) ^ (j + 1))
      = t / (2 * Real.pi * 2 ^ (j + 1) * (N : ℝ)) := by
    field_simp
    ring
  have hNsplit : (N : ℝ) * (N : ℝ) ^ (-(1 / 3) : ℝ) = (N : ℝ) ^ ((2 : ℝ) / 3) := by
    nth_rewrite 1 [show (N : ℝ) = (N : ℝ) ^ (1 : ℝ) from (Real.rpow_one _).symm]
    rw [← Real.rpow_add hN0]
    norm_num
  refine le_trans (hstep.trans_eq hcollapse) ?_
  rw [div_le_iff₀ (by positivity)]
  calc t ≤ 2 * Real.pi * 2 ^ (j + 1) * (N : ℝ) ^ ((2 : ℝ) / 3) := htk
    _ = (N : ℝ) ^ (-(1 / 3) : ℝ) * (2 * Real.pi * 2 ^ (j + 1) * (N : ℝ)) := by
        rw [← hNsplit]; ring

/-- **Exact arithmetic form of the window-top condition.**  The bound `lam_k ≤ U` is equivalent to a
plain inequality between `t · (k-1)!` and `2π (2N)^k U`, with no estimate of the factorial baked in.
This is the interface the schedule should use: the caller supplies whichever factorial estimate its
range of `k` supports. -/
theorem blockLambda_le_iff {t : ℝ} {N : ℕ} (hN : 1 ≤ N) (k : ℕ) (U : ℝ) :
    blockLambda t N k ≤ U ↔
      t * (Nat.factorial (k - 1) : ℝ) ≤ 2 * Real.pi * (2 * (N : ℝ)) ^ k * U := by
  have hπ := Real.pi_pos
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (2 * (N : ℝ)) ^ k := by positivity
  rw [blockLambda, div_le_iff₀ hden, div_mul_eq_mul_div,
    div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
  constructor <;> intro h <;> nlinarith [h]

/-- The crude factorial estimate `(k-1)! ≤ N^(k-1)`, valid for `k - 1 ≤ N`, is lossy: it forces
`2 ^ k ≳ t / N^(2/3)`, hence `k ≈ log₂ t` rather than the classical `k ≈ log t / log N`.  Use
`blockLambda_le_iff` with a sharper factorial estimate whenever the range of `k` allows it. -/
theorem blockLambda_le_of_factorial_bound {t : ℝ} {N k : ℕ} (hN : 1 ≤ N)
    (h : t * (Nat.factorial (k - 1) : ℝ)
      ≤ 2 * Real.pi * (2 * (N : ℝ)) ^ k * (N : ℝ) ^ (-(1 / 3) : ℝ)) :
    blockLambda t N k ≤ (N : ℝ) ^ (-(1 / 3) : ℝ) :=
  (blockLambda_le_iff hN k _).mpr h

/-- **Usable window-top condition.**  Once the factorial `(k-1)!` is at most the base point `N`,
the window-top hypothesis holds under `t ≤ 2π · 2^k · N^(k-1) · N^(-1/3)`.  This is the classical
scale: it reads `t ≈ N^(k - 4/3)`, i.e. `k ≈ log t / log N + 4/3`.  In the range the dyadic assembly
uses — `N ≥ t^(1/m)` with `m ≈ log log t`, so `k ≤ m` — the hypothesis `(k-1)! ≤ N` is comfortable,
since `(k-1)!` is `(log t)^(o(1))` while `N` is `exp(log t / m)`. -/
theorem blockLambda_le_of_small_factorial {t : ℝ} (ht : 0 < t) {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k)
    (hfac : Nat.factorial (k - 1) ≤ N)
    (htk : t ≤ 2 * Real.pi * 2 ^ k * (N : ℝ) ^ (k - 1) * (N : ℝ) ^ (-(1 / 3) : ℝ)) :
    blockLambda t N k ≤ (N : ℝ) ^ (-(1 / 3) : ℝ) := by
  have hπ := Real.pi_pos
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  refine blockLambda_le_of_factorial_bound hN ?_
  have hfacR : (Nat.factorial (k - 1) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hfac
  have hfacpos : (0 : ℝ) < (Nat.factorial (k - 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (k - 1)
  have hNk : (N : ℝ) ^ k = (N : ℝ) ^ (k - 1) * (N : ℝ) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp [pow_succ]
  have hsplit : ((2 : ℝ) * (N : ℝ)) ^ k = 2 ^ k * (N : ℝ) ^ (k - 1) * (N : ℝ) := by
    rw [mul_pow, hNk, ← mul_assoc]
  calc t * (Nat.factorial (k - 1) : ℝ) ≤ t * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_left hfacR ht.le
    _ ≤ (2 * Real.pi * 2 ^ k * (N : ℝ) ^ (k - 1) * (N : ℝ) ^ (-(1 / 3) : ℝ)) * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right htk hN0.le
    _ = 2 * Real.pi * ((2 : ℝ) * (N : ℝ)) ^ k * (N : ℝ) ^ (-(1 / 3) : ℝ) := by
        rw [hsplit]; ring

/-! ## The per-block estimate -/

/-- **Per-block estimate with explicit hypotheses.**  On a dyadic block whose base point and the
frequency satisfy `8π N^(1/3) ≤ t ≤ 2π 2^(k₀) N^(2/3)` with `k₀ ≤ N + 1`, the Dirichlet sum on the
line `Re s = 1` is at most `2560 · N ^ (-1/(3·2^(k₀)))`. -/
theorem dirichlet_block_saving_of_range {t : ℝ} (ht : 0 < t) {N M k₀ : ℕ} (hN : 1 ≤ N)
    (hNM : N ≤ M) (hM : M ≤ 2 * N + 1) (hk₀ : 2 ≤ k₀) (hk₀N : k₀ - 1 ≤ N)
    (hlow : 8 * Real.pi * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : t ≤ 2 * Real.pi * 2 ^ k₀ * (N : ℝ) ^ ((2 : ℝ) / 3)) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 2560 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  obtain ⟨k, hk, hkle, hlowk, hhighk⟩ :=
    exists_blockLambda_in_window ht hN hk₀ (blockLambda_two_ge hN hlow)
      (blockLambda_le_of_order ht hN hk₀ hk₀N hhigh)
  have hlam0 : 0 < blockLambda t N k := blockLambda_pos ht hN k
  have hlam1 : blockLambda t N k ≤ 1 :=
    hhighk.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num))
  have hmono : (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) ≤ (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) := by
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have hpk : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k₀ := pow_le_pow_right₀ (by norm_num) hkle
    have hpos : (0 : ℝ) < 3 * (2 : ℝ) ^ k := by positivity
    have hpos0 : (0 : ℝ) < 3 * (2 : ℝ) ^ k₀ := by positivity
    have : 1 / (3 * (2 : ℝ) ^ k₀) ≤ 1 / (3 * (2 : ℝ) ^ k) :=
      one_div_le_one_div_of_le hpos (by linarith)
    linarith
  calc ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 512 * ((4 : ℝ) ^ k * blockLambda t N k) ^ (1 / ((2 : ℝ) ^ k - 2))
          + 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k))
            * blockLambda t N k ^ (-(2 / (2 : ℝ) ^ k)) :=
        dirichlet_block_one_normalized t ht k N M hk hN hNM hM hlam1
    _ ≤ 2560 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) :=
        block_saving_wide k N hk hN _ hlam0 hhighk hlowk
    _ ≤ 2560 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) := by
        exact mul_le_mul_of_nonneg_left hmono (by norm_num)


/-- **Per-block estimate, sharp interface.**  Same conclusion as `dirichlet_block_saving_of_range`
but with the window-top hypothesis in its exact arithmetic form, so no factorial estimate is fixed
in advance. -/
theorem dirichlet_block_saving_of_factorial_range {t : ℝ} (ht : 0 < t) {N M k₀ : ℕ} (hN : 1 ≤ N)
    (hNM : N ≤ M) (hM : M ≤ 2 * N + 1) (hk₀ : 2 ≤ k₀)
    (hlow : 8 * Real.pi * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : t * (Nat.factorial (k₀ - 1) : ℝ)
      ≤ 2 * Real.pi * (2 * (N : ℝ)) ^ k₀ * (N : ℝ) ^ (-(1 / 3) : ℝ)) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 2560 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  obtain ⟨k, hk, hkle, hlowk, hhighk⟩ :=
    exists_blockLambda_in_window ht hN hk₀ (blockLambda_two_ge hN hlow)
      (blockLambda_le_of_factorial_bound hN hhigh)
  have hlam0 : 0 < blockLambda t N k := blockLambda_pos ht hN k
  have hlam1 : blockLambda t N k ≤ 1 :=
    hhighk.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num))
  have hmono : (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) ≤ (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) := by
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have hpk : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k₀ := pow_le_pow_right₀ (by norm_num) hkle
    have hpos : (0 : ℝ) < 3 * (2 : ℝ) ^ k := by positivity
    have hle : 1 / (3 * (2 : ℝ) ^ k₀) ≤ 1 / (3 * (2 : ℝ) ^ k) :=
      one_div_le_one_div_of_le hpos (by linarith)
    linarith
  calc ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 512 * ((4 : ℝ) ^ k * blockLambda t N k) ^ (1 / ((2 : ℝ) ^ k - 2))
          + 512 * (N : ℝ) ^ (-(4 / (2 : ℝ) ^ k))
            * blockLambda t N k ^ (-(2 / (2 : ℝ) ^ k)) :=
        dirichlet_block_one_normalized t ht k N M hk hN hNM hM hlam1
    _ ≤ 2560 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k))) :=
        block_saving_wide k N hk hN _ hlam0 hhighk hlowk
    _ ≤ 2560 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)


/-- **Per-block estimate at the classical scale.**  On a dyadic block whose factorial fits under the
base point, the Dirichlet sum on the line `Re s = 1` obeys the saving with `k₀` at the classical
scale `t ≈ N^(k₀ - 4/3)`. -/
theorem dirichlet_block_saving_of_small_factorial {t : ℝ} (ht : 0 < t) {N M k₀ : ℕ} (hN : 1 ≤ N)
    (hNM : N ≤ M) (hM : M ≤ 2 * N + 1) (hk₀ : 2 ≤ k₀)
    (hfac : Nat.factorial (k₀ - 1) ≤ N)
    (hlow : 8 * Real.pi * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : t ≤ 2 * Real.pi * 2 ^ k₀ * (N : ℝ) ^ (k₀ - 1) * (N : ℝ) ^ (-(1 / 3) : ℝ)) :
    ‖∑ n ∈ Finset.Ico N M, (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 2560 * (N : ℝ) ^ (-(1 / (3 * (2 : ℝ) ^ k₀))) := by
  refine dirichlet_block_saving_of_factorial_range ht hN hNM hM hk₀ hlow ?_
  exact (blockLambda_le_iff hN k₀ _).mp
    (blockLambda_le_of_small_factorial ht hN (by omega) hfac hhigh)

end RHTower.Sieve
