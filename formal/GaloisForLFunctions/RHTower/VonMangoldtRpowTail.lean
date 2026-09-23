import GaloisForLFunctions.RHTower.PrimeLogRpowTail
import GaloisForLFunctions.RHTower.VonMangoldtLogSummatory

/-!
# The von Mangoldt tail at a real cutoff

The Chebyshev tail of `(log p)·p^{-1-δ}` over primes has a von Mangoldt companion over all
integers, with the same clean power decay: Chebyshev's `ψ(x) ≤ 7x` replaces `θ(x) ≤ x log 4` in the
dyadic block estimate, so no logarithmic factor appears.  This is what an exterior atom tail needs
when the sum runs over prime powers rather than primes.
-/

namespace RHTower

open ArithmeticFunction Finset

/-- The geometric constant of the von Mangoldt dyadic tail. -/
noncomputable def vonMangoldtRpowTailConstant (δ : ℝ) : ℝ :=
  14 / (1 - (2 : ℝ) ^ (-δ))

theorem vonMangoldtRpowTailConstant_nonneg {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ vonMangoldtRpowTailConstant δ := by
  rw [vonMangoldtRpowTailConstant]
  have h1 : (2 : ℝ) ^ (-δ) < 1 := two_rpow_neg_lt_one_primeLogRpowTail hδ
  have : (0 : ℝ) < 1 - (2 : ℝ) ^ (-δ) := by linarith
  positivity

theorem sum_vonMangoldt_rpow_dyadic_block_le {δ : ℝ} (hδ : 0 < δ) (j N : ℕ) :
    ∑ n ∈ {n ∈ Finset.Icc 1 N | Nat.log 2 n = j},
        (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + δ))
      ≤ 14 * ((2 : ℝ) ^ (-δ)) ^ j := by
  classical
  set B := {n ∈ Finset.Icc 1 N | Nat.log 2 n = j} with hB
  have hmem : ∀ n ∈ B, 2 ^ j ≤ n ∧ n < 2 ^ (j + 1) ∧ 1 ≤ n := by
    intro n hn
    obtain ⟨hnmem, hlog⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnmem
    refine ⟨?_, ?_, hn1⟩
    · rw [← hlog]
      exact Nat.pow_log_le_self 2 (by omega)
    · rw [← hlog]
      exact Nat.lt_pow_succ_log_self one_lt_two n
  have hweight : ∀ n ∈ B, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + δ))
      ≤ ((2 : ℝ) ^ j) ^ (-(1 + δ)) * (vonMangoldt n : ℝ) := by
    intro n hn
    obtain ⟨hlow, -, hn1⟩ := hmem n hn
    have hp0 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hcast : ((2 : ℝ) ^ j) ≤ (n : ℝ) := by exact_mod_cast hlow
    have hpow : ((2 : ℝ) ^ j) ^ (1 + δ) ≤ (n : ℝ) ^ (1 + δ) :=
      Real.rpow_le_rpow hp0.le hcast (by linarith)
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hp0 hcast
    have hinv : (n : ℝ) ^ (-(1 + δ)) ≤ ((2 : ℝ) ^ j) ^ (-(1 + δ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg hp0.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hp0 _) hpow
    have hvm : (0 : ℝ) ≤ (vonMangoldt n : ℝ) := vonMangoldt_nonneg
    calc (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + δ))
        ≤ (vonMangoldt n : ℝ) * ((2 : ℝ) ^ j) ^ (-(1 + δ)) :=
          mul_le_mul_of_nonneg_left hinv hvm
      _ = ((2 : ℝ) ^ j) ^ (-(1 + δ)) * (vonMangoldt n : ℝ) := by ring
  have hcheb : ∑ n ∈ B, (vonMangoldt n : ℝ) ≤ 7 * (2 : ℝ) ^ (j + 1) := by
    have hsub : B ⊆ Finset.Icc 1 (2 ^ (j + 1) - 1) := by
      intro n hn
      obtain ⟨-, hup, hn1⟩ := hmem n hn
      exact Finset.mem_Icc.mpr ⟨hn1, by omega⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => vonMangoldt_nonneg)) ?_
    have hpsi : ∑ n ∈ Finset.Icc 1 (2 ^ (j + 1) - 1), (vonMangoldt n : ℝ)
        = chebyshevPsi (2 ^ (j + 1) - 1) := rfl
    rw [hpsi]
    refine le_trans (chebyshevPsi_le_seven (2 ^ (j + 1) - 1)) ?_
    have hcast : ((2 ^ (j + 1) - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      linarith
    linarith
  have hcoef : (0 : ℝ) ≤ ((2 : ℝ) ^ j) ^ (-(1 + δ)) :=
    (Real.rpow_pos_of_pos (by positivity) _).le
  calc ∑ n ∈ B, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + δ))
      ≤ ∑ n ∈ B, ((2 : ℝ) ^ j) ^ (-(1 + δ)) * (vonMangoldt n : ℝ) :=
        Finset.sum_le_sum hweight
    _ = ((2 : ℝ) ^ j) ^ (-(1 + δ)) * ∑ n ∈ B, (vonMangoldt n : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) ^ j) ^ (-(1 + δ)) * (7 * (2 : ℝ) ^ (j + 1)) :=
        mul_le_mul_of_nonneg_left hcheb hcoef
    _ = 14 * ((2 : ℝ) ^ (-δ)) ^ j := by
        have h2 : (0 : ℝ) < 2 := by norm_num
        have e1 : ((2 : ℝ) ^ j) ^ (-(1 + δ)) = (2 : ℝ) ^ ((j : ℝ) * -(1 + δ)) := by
          rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul h2.le]
        have e2 : ((2 : ℝ) ^ (j + 1) : ℝ) = (2 : ℝ) ^ ((j : ℝ) + 1) := by
          rw [← Real.rpow_natCast (2 : ℝ) (j + 1)]
          push_cast
          ring_nf
        have e3 : ((2 : ℝ) ^ (-δ)) ^ j = (2 : ℝ) ^ (-δ * (j : ℝ)) := by
          rw [← Real.rpow_natCast ((2 : ℝ) ^ (-δ)) j, ← Real.rpow_mul h2.le]
        rw [e1, e2, e3,
          show (2 : ℝ) ^ ((j : ℝ) * -(1 + δ)) * (7 * (2 : ℝ) ^ ((j : ℝ) + 1))
            = 7 * ((2 : ℝ) ^ ((j : ℝ) * -(1 + δ)) * (2 : ℝ) ^ ((j : ℝ) + 1)) from by ring,
          ← Real.rpow_add h2,
          show (j : ℝ) * -(1 + δ) + ((j : ℝ) + 1) = 1 + -δ * (j : ℝ) from by ring,
          Real.rpow_add h2, Real.rpow_one]
        ring

theorem sum_vonMangoldt_rpow_dyadic_tail_le {δ : ℝ} (hδ : 0 < δ) (m N : ℕ) :
    ∑ n ∈ {n ∈ Finset.Icc 1 N | 2 ^ m ≤ n}, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + δ))
      ≤ vonMangoldtRpowTailConstant δ * ((2 : ℝ) ^ (-δ)) ^ m := by
  classical
  set r : ℝ := (2 : ℝ) ^ (-δ) with hr
  have hr0 : 0 < r := two_rpow_neg_pos δ
  have hr1 : r < 1 := two_rpow_neg_lt_one_primeLogRpowTail hδ
  set S := {n ∈ Finset.Icc 1 N | 2 ^ m ≤ n} with hS
  by_cases hmN : m ≤ Nat.log 2 N
  · have hmaps : ∀ n ∈ S, Nat.log 2 n ∈ Finset.Icc m (Nat.log 2 N) := by
      intro n hn
      obtain ⟨hnmem, hlow⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnmem
      refine Finset.mem_Icc.mpr ⟨?_, Nat.log_mono_right hnN⟩
      calc m = Nat.log 2 (2 ^ m) := (Nat.log_pow one_lt_two m).symm
        _ ≤ Nat.log 2 n := Nat.log_mono_right hlow
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hblock : ∀ j ∈ Finset.Icc m (Nat.log 2 N),
        ∑ n ∈ {n ∈ S | Nat.log 2 n = j}, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + δ))
          ≤ 14 * r ^ j := by
      intro j _
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
        (sum_vonMangoldt_rpow_dyadic_block_le hδ j N)
      · intro n hn
        obtain ⟨hnS, hlog⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hnS).1, hlog⟩
      · intro n hn _
        obtain ⟨hnmem, -⟩ := Finset.mem_filter.mp hn
        obtain ⟨hn1, -⟩ := Finset.mem_Icc.mp hnmem
        have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        exact mul_nonneg vonMangoldt_nonneg (Real.rpow_pos_of_pos hn0 _).le
    refine le_trans (Finset.sum_le_sum hblock) ?_
    rw [← Finset.mul_sum]
    have hgeom : ∑ j ∈ Finset.Icc m (Nat.log 2 N), r ^ j ≤ r ^ m / (1 - r) := by
      rw [show Finset.Icc m (Nat.log 2 N) = Finset.Ico m (Nat.log 2 N + 1) from by
        ext x; simp]
      rw [geom_sum_Ico (by linarith) (by omega)]
      have hden : (0 : ℝ) < 1 - r := by linarith
      have hnum : (0 : ℝ) ≤ r ^ (Nat.log 2 N + 1) := by positivity
      have heq : (r ^ (Nat.log 2 N + 1) - r ^ m) / (r - 1)
          = (r ^ m - r ^ (Nat.log 2 N + 1)) / (1 - r) := by
        rw [div_eq_div_iff (by linarith) (by linarith)]
        ring
      rw [heq, div_le_div_iff₀ hden hden]
      nlinarith
    calc (14 : ℝ) * ∑ j ∈ Finset.Icc m (Nat.log 2 N), r ^ j
        ≤ 14 * (r ^ m / (1 - r)) := mul_le_mul_of_nonneg_left hgeom (by norm_num)
      _ = vonMangoldtRpowTailConstant δ * r ^ m := by
          rw [vonMangoldtRpowTailConstant, ← hr]
          field_simp
  · have hempty : S = ∅ := by
      rw [hS]
      refine Finset.filter_eq_empty_iff.2 fun n hn hlow => ?_
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
      have hmle : m ≤ Nat.log 2 n := by
        calc m = Nat.log 2 (2 ^ m) := (Nat.log_pow one_lt_two m).symm
          _ ≤ Nat.log 2 n := Nat.log_mono_right hlow
      have : Nat.log 2 n ≤ Nat.log 2 N := Nat.log_mono_right hnN
      omega
    rw [hempty, Finset.sum_empty]
    exact mul_nonneg (vonMangoldtRpowTailConstant_nonneg hδ) (by positivity)

/-- **The von Mangoldt tail at a real cutoff.**  For every `X ≥ 1`,
`∑_{n > X} Λ(n)·n^{-1-δ} ≤ 2^δ · C_δ · X^{-δ}`. -/
theorem sum_vonMangoldt_rpow_tail_le {δ X : ℝ} (hδ : 0 < δ) (hX : 1 ≤ X) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => X < (n : ℝ)),
        (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + δ))
      ≤ (2 : ℝ) ^ δ * vonMangoldtRpowTailConstant δ * X ^ (-δ) := by
  classical
  set m : ℕ := Nat.log 2 ⌊X⌋₊ with hm
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX
  have hfloor : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  have hpowle : (2 : ℕ) ^ m ≤ ⌊X⌋₊ := Nat.pow_log_le_self 2 (by omega)
  have hfloorX : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le hX0.le
  have hXlt : X < (2 : ℝ) ^ (m + 1) := by
    have h1 : ⌊X⌋₊ < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self one_lt_two _
    have h2 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
    have h3 : ((⌊X⌋₊ : ℕ) : ℝ) + 1 ≤ ((2 ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    have h4 : ((2 ^ (m + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (m + 1) := by push_cast; ring
    linarith [h4 ▸ h3]
  have hsub : (Finset.Icc 1 N).filter (fun n : ℕ => X < (n : ℝ))
      ⊆ {n ∈ Finset.Icc 1 N | 2 ^ m ≤ n} := by
    intro n hn
    obtain ⟨hnmem, hgt⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨hnmem, ?_⟩
    have hcast : ((2 ^ m : ℕ) : ℝ) ≤ ((⌊X⌋₊ : ℕ) : ℝ) := by exact_mod_cast hpowle
    have hlt : ((2 ^ m : ℕ) : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast hlt.le
  have hnn : ∀ n ∈ {n ∈ Finset.Icc 1 N | 2 ^ m ≤ n},
      n ∉ (Finset.Icc 1 N).filter (fun n : ℕ => X < (n : ℝ)) →
      0 ≤ (vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + δ)) := by
    intro n hn _
    obtain ⟨hnmem, -⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, -⟩ := Finset.mem_Icc.mp hnmem
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    exact mul_nonneg vonMangoldt_nonneg (Real.rpow_pos_of_pos hn0 _).le
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn) ?_
  refine le_trans (sum_vonMangoldt_rpow_dyadic_tail_le hδ m N) ?_
  have hpowm : ((2 : ℝ) ^ (-δ)) ^ m = ((2 : ℝ) ^ (m : ℕ)) ^ (-δ) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-δ)) m, ← Real.rpow_natCast (2 : ℝ) m,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
    ring_nf
  have hcmp : ((2 : ℝ) ^ (m : ℕ)) ^ (-δ) ≤ (2 : ℝ) ^ δ * X ^ (-δ) := by
    have hhalf : X / 2 < (2 : ℝ) ^ (m : ℕ) := by
      have : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by ring
      linarith [hXlt, this]
    have hpos : (0 : ℝ) < X / 2 := by linarith
    have hmono : ((2 : ℝ) ^ (m : ℕ)) ^ (-δ) ≤ (X / 2) ^ (-δ) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg hpos.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hpos _)
        (Real.rpow_le_rpow hpos.le hhalf.le hδ.le)
    refine hmono.trans ?_
    rw [Real.div_rpow hX0.le (by norm_num), Real.rpow_neg hX0.le, Real.rpow_neg (by norm_num),
      div_eq_mul_inv, inv_inv]
    exact le_of_eq (by ring)
  rw [hpowm]
  have hC := vonMangoldtRpowTailConstant_nonneg hδ
  calc vonMangoldtRpowTailConstant δ * ((2 : ℝ) ^ (m : ℕ)) ^ (-δ)
      ≤ vonMangoldtRpowTailConstant δ * ((2 : ℝ) ^ δ * X ^ (-δ)) :=
        mul_le_mul_of_nonneg_left hcmp hC
    _ = (2 : ℝ) ^ δ * vonMangoldtRpowTailConstant δ * X ^ (-δ) := by ring

end RHTower
