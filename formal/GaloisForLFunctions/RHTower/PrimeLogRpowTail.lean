import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass

/-!
# The Chebyshev tail of `(log p) p^{-1-δ}`

For every positive `δ` the prime tail

`∑_{p > X} (log p) p^{-1-δ}`

is bounded by a constant multiple of `X^{-δ}`, with no logarithmic loss.  The absence of the
logarithm is exactly Chebyshev's bound `∑_{p ≤ x} log p ≤ x log 4`: summing over integers instead
of primes would produce an extra factor `log X`.

The proof is a dyadic decomposition.  On the block `2^j ≤ p < 2^{j+1}` Chebyshev gives total
logarithmic mass at most `2^{j+1} log 4`, while `p^{-1-δ} ≤ 2^{-j(1+δ)}`, so the block carries at
most `2 log 4 · 2^{-jδ}`.  The blocks form a geometric series in `2^{-δ}`.
-/

open Finset

namespace RHTower

/-- The dyadic constant governing the prime tail of `(log p)·p^{-1-δ}`. -/
noncomputable def primeLogRpowTailConstant (δ : ℝ) : ℝ :=
  2 * Real.log 4 / (1 - (2 : ℝ) ^ (-δ))

theorem two_rpow_neg_lt_one {δ : ℝ} (hδ : 0 < δ) : (2 : ℝ) ^ (-δ) < 1 := by
  rw [Real.rpow_neg (by norm_num), inv_lt_one_iff₀]
  right
  exact Real.one_lt_rpow_iff_of_pos (by norm_num) |>.2 (Or.inl ⟨by norm_num, hδ⟩)

theorem two_rpow_neg_pos (δ : ℝ) : (0 : ℝ) < (2 : ℝ) ^ (-δ) :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem primeLogRpowTailConstant_nonneg {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ primeLogRpowTailConstant δ := by
  have h := two_rpow_neg_lt_one hδ
  rw [primeLogRpowTailConstant]
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  positivity

/-- One dyadic block of the tail carries at most `2 log 4 · 2^{-jδ}`. -/
theorem sum_prime_log_rpow_dyadic_block_le {δ : ℝ} (hδ : 0 < δ) (j N : ℕ) :
    ∑ p ∈ {p ∈ Nat.primesBelow (N + 1) | Nat.log 2 p = j},
        Real.log p * (p : ℝ) ^ (-(1 + δ))
      ≤ 2 * Real.log 4 * ((2 : ℝ) ^ (-δ)) ^ j := by
  classical
  set B := {p ∈ Nat.primesBelow (N + 1) | Nat.log 2 p = j} with hB
  have hmem : ∀ p ∈ B, 2 ^ j ≤ p ∧ p < 2 ^ (j + 1) ∧ p.Prime := by
    intro p hp
    obtain ⟨hpmem, hlog⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hpp⟩ := Nat.mem_primesBelow.mp hpmem
    refine ⟨?_, ?_, hpp⟩
    · rw [← hlog]
      exact Nat.pow_log_le_self 2 hpp.pos.ne'
    · rw [← hlog]
      exact Nat.lt_pow_succ_log_self one_lt_two p
  have hweight : ∀ p ∈ B, Real.log p * (p : ℝ) ^ (-(1 + δ))
      ≤ ((2 : ℝ) ^ j) ^ (-(1 + δ)) * Real.log p := by
    intro p hp
    obtain ⟨hlow, -, hpp⟩ := hmem p hp
    have hp0 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hcast : ((2 : ℝ) ^ j) ≤ (p : ℝ) := by exact_mod_cast hlow
    have hpow : ((2 : ℝ) ^ j) ^ (1 + δ) ≤ (p : ℝ) ^ (1 + δ) :=
      Real.rpow_le_rpow hp0.le hcast (by linarith)
    have hinv : (p : ℝ) ^ (-(1 + δ)) ≤ ((2 : ℝ) ^ j) ^ (-(1 + δ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg hp0.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hp0 _) hpow
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    calc Real.log p * (p : ℝ) ^ (-(1 + δ))
        ≤ Real.log p * ((2 : ℝ) ^ j) ^ (-(1 + δ)) :=
          mul_le_mul_of_nonneg_left hinv hlogp
      _ = ((2 : ℝ) ^ j) ^ (-(1 + δ)) * Real.log p := by ring
  have hchebyshev : ∑ p ∈ B, Real.log p ≤ (2 : ℝ) ^ (j + 1) * Real.log 4 := by
    have hsub : B ⊆ Nat.primesBelow (2 ^ (j + 1) - 1 + 1) := by
      intro p hp
      obtain ⟨-, hup, hpp⟩ := hmem p hp
      exact Nat.mem_primesBelow.mpr ⟨by omega, hpp⟩
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
      Real.log_nonneg (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_lt.le)) ?_
    refine le_trans (sum_primesBelow_log_le (2 ^ (j + 1) - 1)) ?_
    have hcast : ((2 ^ (j + 1) - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      linarith
    exact mul_le_mul_of_nonneg_right hcast (Real.log_nonneg (by norm_num))
  have hcoef : (0 : ℝ) ≤ ((2 : ℝ) ^ j) ^ (-(1 + δ)) :=
    (Real.rpow_pos_of_pos (by positivity) _).le
  calc ∑ p ∈ B, Real.log p * (p : ℝ) ^ (-(1 + δ))
      ≤ ∑ p ∈ B, ((2 : ℝ) ^ j) ^ (-(1 + δ)) * Real.log p :=
        Finset.sum_le_sum hweight
    _ = ((2 : ℝ) ^ j) ^ (-(1 + δ)) * ∑ p ∈ B, Real.log p := by
        rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) ^ j) ^ (-(1 + δ)) * ((2 : ℝ) ^ (j + 1) * Real.log 4) :=
        mul_le_mul_of_nonneg_left hchebyshev hcoef
    _ = 2 * Real.log 4 * ((2 : ℝ) ^ (-δ)) ^ j := by
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
          show (2 : ℝ) ^ ((j : ℝ) * -(1 + δ)) * ((2 : ℝ) ^ ((j : ℝ) + 1) * Real.log 4)
            = ((2 : ℝ) ^ ((j : ℝ) * -(1 + δ)) * (2 : ℝ) ^ ((j : ℝ) + 1)) * Real.log 4 from by ring,
          ← Real.rpow_add h2,
          show (j : ℝ) * -(1 + δ) + ((j : ℝ) + 1) = 1 + -δ * (j : ℝ) from by ring,
          Real.rpow_add h2, Real.rpow_one]
        ring

/-- **The dyadic Chebyshev tail.**  Above a dyadic threshold the tail of `(log p)·p^{-1-δ}` is at
most a fixed multiple of `2^{-mδ}`. -/
theorem sum_prime_log_rpow_dyadic_tail_le {δ : ℝ} (hδ : 0 < δ) (m N : ℕ) :
    ∑ p ∈ {p ∈ Nat.primesBelow (N + 1) | 2 ^ m ≤ p}, Real.log p * (p : ℝ) ^ (-(1 + δ))
      ≤ primeLogRpowTailConstant δ * ((2 : ℝ) ^ (-δ)) ^ m := by
  classical
  set r : ℝ := (2 : ℝ) ^ (-δ) with hr
  have hr0 : 0 < r := two_rpow_neg_pos δ
  have hr1 : r < 1 := two_rpow_neg_lt_one hδ
  set S := {p ∈ Nat.primesBelow (N + 1) | 2 ^ m ≤ p} with hS
  by_cases hmN : m ≤ Nat.log 2 N
  · have hmaps : ∀ p ∈ S, Nat.log 2 p ∈ Finset.Icc m (Nat.log 2 N) := by
      intro p hp
      obtain ⟨hpmem, hlow⟩ := Finset.mem_filter.mp hp
      obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hpmem
      refine Finset.mem_Icc.mpr ⟨?_, Nat.log_mono_right (by omega)⟩
      calc m = Nat.log 2 (2 ^ m) := (Nat.log_pow one_lt_two m).symm
        _ ≤ Nat.log 2 p := Nat.log_mono_right hlow
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hblock : ∀ j ∈ Finset.Icc m (Nat.log 2 N),
        ∑ p ∈ {p ∈ S | Nat.log 2 p = j}, Real.log p * (p : ℝ) ^ (-(1 + δ))
          ≤ 2 * Real.log 4 * r ^ j := by
      intro j _
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
        (sum_prime_log_rpow_dyadic_block_le hδ j N)
      · intro p hp
        obtain ⟨hpS, hlog⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hpS).1, hlog⟩
      · intro p hp _
        obtain ⟨hpmem, -⟩ := Finset.mem_filter.mp hp
        have hpp := (Nat.mem_primesBelow.mp hpmem).2
        exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))
          (Real.rpow_pos_of_pos (by exact_mod_cast hpp.pos) _).le
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
    have hcoef : (0 : ℝ) ≤ 2 * Real.log 4 := by
      have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      linarith
    calc 2 * Real.log 4 * ∑ j ∈ Finset.Icc m (Nat.log 2 N), r ^ j
        ≤ 2 * Real.log 4 * (r ^ m / (1 - r)) := mul_le_mul_of_nonneg_left hgeom hcoef
      _ = primeLogRpowTailConstant δ * r ^ m := by
          rw [primeLogRpowTailConstant, ← hr]
          field_simp
  · have hempty : S = ∅ := by
      rw [hS]
      refine Finset.filter_eq_empty_iff.2 fun p hp hlow => ?_
      obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hp
      have hmle : m ≤ Nat.log 2 p := by
        calc m = Nat.log 2 (2 ^ m) := (Nat.log_pow one_lt_two m).symm
          _ ≤ Nat.log 2 p := Nat.log_mono_right hlow
      have : Nat.log 2 p ≤ Nat.log 2 N := Nat.log_mono_right (by omega)
      omega
    rw [hempty, Finset.sum_empty]
    have : (0 : ℝ) ≤ primeLogRpowTailConstant δ * r ^ m :=
      mul_nonneg (primeLogRpowTailConstant_nonneg hδ) (by positivity)
    exact this

/-- **The Chebyshev tail at a real cutoff.**  For every `X ≥ 1`,
`∑_{p > X} (log p)·p^{-1-δ} ≤ 2^δ · C_δ · X^{-δ}`. -/
theorem sum_prime_log_rpow_tail_le {δ X : ℝ} (hδ : 0 < δ) (hX : 1 ≤ X) (N : ℕ) :
    ∑ p ∈ (Nat.primesBelow (N + 1)).filter (fun p : ℕ => X < (p : ℝ)),
        Real.log p * (p : ℝ) ^ (-(1 + δ))
      ≤ (2 : ℝ) ^ δ * primeLogRpowTailConstant δ * X ^ (-δ) := by
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
  have hsub : (Nat.primesBelow (N + 1)).filter (fun p : ℕ => X < (p : ℝ))
      ⊆ {p ∈ Nat.primesBelow (N + 1) | 2 ^ m ≤ p} := by
    intro p hp
    obtain ⟨hpmem, hgt⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hpmem, ?_⟩
    have hcast : ((2 ^ m : ℕ) : ℝ) ≤ ((⌊X⌋₊ : ℕ) : ℝ) := by exact_mod_cast hpowle
    have hlt : ((2 ^ m : ℕ) : ℝ) < (p : ℝ) := by linarith
    exact_mod_cast hlt.le
  have hnn : ∀ p ∈ {p ∈ Nat.primesBelow (N + 1) | 2 ^ m ≤ p},
      p ∉ (Nat.primesBelow (N + 1)).filter (fun p : ℕ => X < (p : ℝ)) →
      0 ≤ Real.log p * (p : ℝ) ^ (-(1 + δ)) := by
    intro p hp _
    obtain ⟨hpmem, -⟩ := Finset.mem_filter.mp hp
    have hpp := (Nat.mem_primesBelow.mp hpmem).2
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))
      (Real.rpow_pos_of_pos (by exact_mod_cast hpp.pos) _).le
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn) ?_
  refine le_trans (sum_prime_log_rpow_dyadic_tail_le hδ m N) ?_
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
  have hC := primeLogRpowTailConstant_nonneg hδ
  calc primeLogRpowTailConstant δ * ((2 : ℝ) ^ (m : ℕ)) ^ (-δ)
      ≤ primeLogRpowTailConstant δ * ((2 : ℝ) ^ δ * X ^ (-δ)) :=
        mul_le_mul_of_nonneg_left hcmp hC
    _ = (2 : ℝ) ^ δ * primeLogRpowTailConstant δ * X ^ (-δ) := by ring

end RHTower
