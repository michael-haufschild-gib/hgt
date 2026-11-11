import GaloisForLFunctions.ShortIntervalPrimesInProgressions.ZeroDetectionForACharacter
import GaloisForLFunctions.RHTower.Sieve.JutilaLocalLargeValues
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedDivisorMoment

/-!
# A zero-density estimate for Dirichlet `L`-functions

For a nonprincipal character `χ` modulo `q` there are `D` and `T₀` with

`#{ρ : σ ≤ Re ρ, |Im ρ| ≤ T} ≤ D (1 + log T)^{11} T^{12(1 − σ)}`   (`T ≥ T₀`, `½ ≤ σ ≤ 1`),

zeros of `Λ(s, χ)` counted with multiplicity (`exists_zeroDensity_character`).

Every such zero is detected by a class `(slab, block, Taylor order)`
(`exists_class_of_detected`); there are `O(log³ T)` classes.  In the fullest class a maximal
`1`-separated set of ordinates keeps a `1/O(log T)` share (local zero count), and the discrete
mean value theorem bounds it by the block mean square `≤ 2^{−2jσ₀} L (1 + log L)³`, `L = 2^{j+1}`
(`card_mul_sq_le_of_taylor_large`).  A block meeting the support of the detection coefficients
starts above `y = ⌈T⌉`, and the support ends at `Xy ≤ T⁶`; the two terms of the mean value theorem
are then `T^{2(1−σ)}` and `T^{12(1−σ)}`.
-/

open Complex Finset RHTower.Sieve

namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

/-! ### The large-values count of one class -/

/-- `k^{−ix}` is the conjugate of the phase `e^{ix log k}`. -/
theorem natCast_cpow_neg_mul_I (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    (k : ℂ) ^ (-((x : ℂ) * I)) = (starRingEnd ℂ) (Complex.exp (((x * Real.log k : ℝ) : ℂ) * I)) := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← Complex.exp_conj, Complex.cpow_def_of_ne_zero hk0, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg k)]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Reindexing a sum over `Fin L` against a block `B ⊆ [1, L]`. -/
theorem sum_fin_block_eq {L : ℕ} {B : Finset ℕ} (hB : ∀ k ∈ B, 1 ≤ k ∧ k ≤ L) (G : ℕ → ℂ) :
    ∑ n : Fin L, (if (n : ℕ) + 1 ∈ B then G ((n : ℕ) + 1) else 0) = ∑ k ∈ B, G k := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun n => if n + 1 ∈ B then G (n + 1) else 0) L]
  have h1 : ∑ n ∈ Finset.range L, (if n + 1 ∈ B then G (n + 1) else 0)
      = ∑ k ∈ Finset.Ico 1 (L + 1), (if k ∈ B then G k else 0) := by
    rw [Finset.sum_Ico_eq_sum_range, show L + 1 - 1 = L by omega]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [add_comm 1 n]
  rw [h1, Finset.sum_ite_mem]
  congr 1
  ext k
  simp only [Finset.mem_inter, Finset.mem_Ico]
  constructor
  · exact fun h => h.2
  · intro h; have := hB k h; exact ⟨⟨this.1, by omega⟩, h⟩

/-- The dyadic weight bound `k^{−σ₀} ≤ (2^j)^{−σ₀}` on a block. -/
theorem rpow_neg_le_of_two_pow_le {j k : ℕ} (hk : 2 ^ j ≤ k) {σ₀ : ℝ} (hσ₀ : 0 ≤ σ₀) :
    (k : ℝ) ^ (-σ₀) ≤ ((2 : ℝ) ^ j) ^ (-σ₀) :=
  Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast hk) (by linarith)

/-- **The large-values count of a class.**  If the companion polynomial `P_{j,m}` of a dyadic
block `[2^j, 2^{j+1})`, with coefficients bounded by the divisor function, is at least `V` at the
points of a `1`-separated set `S ⊆ [−T, T]`, then
`|S| V² ≤ (2T + 1 + 4L(1 + log L))(1 + 2 log L) · (2^j)^{−2σ₀} · L (1 + log L)³`, `L = 2^{j+1}`. -/
theorem card_mul_sq_le_of_taylor_large {B : Finset ℕ} {j : ℕ}
    (hB : ∀ k ∈ B, 2 ^ j ≤ k ∧ k < 2 ^ (j + 1)) {c : ℕ → ℂ}
    (hc : ∀ k ∈ B, ‖c k‖ ≤ (k.divisors.card : ℝ)) {Λ σ₀ T V : ℝ} {m : ℕ}
    (hΛ : ∀ k ∈ B, Real.log k ≤ Λ) (hσ₀ : 0 ≤ σ₀) (hT : 0 ≤ T) {S : Finset ℝ}
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) (hST : ∀ x ∈ S, |x| ≤ T)
    (hV : ∀ x ∈ S, V ≤ ‖abscissaTaylorPoly B c Λ m σ₀ x‖) (hV0 : 0 ≤ V) :
    (S.card : ℝ) * V ^ 2 ≤
      (2 * T + 1 + 4 * ((2 ^ (j + 1) : ℕ) : ℝ) * (1 + Real.log ((2 ^ (j + 1) : ℕ) : ℝ))) *
        (1 + 2 * Real.log ((2 ^ (j + 1) : ℕ) : ℝ)) *
        ((((2 : ℝ) ^ j) ^ (-σ₀)) ^ 2 *
          (((2 ^ (j + 1) : ℕ) : ℝ) * (1 + Real.log ((2 ^ (j + 1) : ℕ) : ℝ)) ^ 3)) := by
  classical
  set L : ℕ := 2 ^ (j + 1) with hL
  have hL2 : 2 ≤ L := by
    rw [hL]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB1 : ∀ k ∈ B, 1 ≤ k ∧ k ≤ L := by
    intro k hk
    have := hB k hk
    exact ⟨le_trans Nat.one_le_two_pow this.1, this.2.le⟩
  -- the block values as conjugate Dirichlet polynomials
  set g : ℕ → ℂ := fun k => c k * (((Real.log k / Λ) ^ m : ℝ) : ℂ) * (k : ℂ) ^ (-(σ₀ : ℂ))
    with hg
  set a : Fin L → ℂ := fun n =>
    (starRingEnd ℂ) (if (n : ℕ) + 1 ∈ B then g ((n : ℕ) + 1) else 0) with ha
  have hval : ∀ x : ℝ, ‖abscissaTaylorPoly B c Λ m σ₀ x‖ = ‖dirPoly L a x‖ := by
    intro x
    have h1 : abscissaTaylorPoly B c Λ m σ₀ x
        = ∑ k ∈ B, g k * (starRingEnd ℂ) (Complex.exp (((x * Real.log k : ℝ) : ℂ) * I)) := by
      unfold abscissaTaylorPoly
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 := (hB1 k hk).1
      have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [hg, ← natCast_cpow_neg_mul_I k hk1 x,
        show -((σ₀ : ℂ) + (x : ℂ) * I) = -(σ₀ : ℂ) + -((x : ℂ) * I) by ring,
        Complex.cpow_add _ _ hk0]
      ring
    have h2 : dirPoly L a x = (starRingEnd ℂ) (∑ n : Fin L,
        (if (n : ℕ) + 1 ∈ B then g ((n : ℕ) + 1) *
          (starRingEnd ℂ) (Complex.exp (((x * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * I)) else 0)) := by
      unfold dirPoly
      rw [map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [ha]
      split_ifs <;> simp
    rw [h2, RCLike.norm_conj, h1]
    congr 1
    have h3 := sum_fin_block_eq hB1
      (fun k => g k * (starRingEnd ℂ) (Complex.exp (((x * Real.log k : ℝ) : ℂ) * I)))
    rw [← h3]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    rfl
  -- the mean square of the coefficients
  have hmass : ∑ n : Fin L, ‖a n‖ ^ (2 : ℕ)
      ≤ (((2 : ℝ) ^ j) ^ (-σ₀)) ^ 2 * ((L : ℝ) * (1 + Real.log L) ^ 3) := by
    have h1 : ∑ n : Fin L, ‖a n‖ ^ (2 : ℕ) = ∑ k ∈ B, ((‖g k‖ ^ 2 : ℝ) : ℂ).re := by
      have := sum_fin_block_eq hB1 (fun k => ((‖g k‖ ^ 2 : ℝ) : ℂ))
      rw [← Complex.re_sum, ← this, Complex.re_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [ha, RCLike.norm_conj]
      split_ifs <;> simp
    rw [h1]
    simp only [Complex.ofReal_re]
    have h2 : ∀ k ∈ B, ‖g k‖ ^ 2 ≤ (((2 : ℝ) ^ j) ^ (-σ₀)) ^ 2 * ((k.divisors.card : ℝ) ^ 2) := by
      intro k hk
      have hk1 := (hB1 k hk).1
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hlog0 : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
      have hΛ0 : 0 ≤ Λ := hlog0.trans (hΛ k hk)
      have hw : |(Real.log k / Λ) ^ m| ≤ 1 := by
        rw [abs_pow]
        refine pow_le_one₀ (abs_nonneg _) ?_
        rcases eq_or_lt_of_le hΛ0 with h | h
        · rw [← h, div_zero, abs_zero]; norm_num
        · rw [abs_div, abs_of_nonneg hlog0, abs_of_pos h, div_le_one h]; exact hΛ k hk
      have hgk : ‖g k‖ ≤ (k.divisors.card : ℝ) * ((2 : ℝ) ^ j) ^ (-σ₀) := by
        rw [hg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_natCast_cpow_of_pos (by omega)]
        simp only [neg_re, ofReal_re]
        calc ‖c k‖ * |(Real.log k / Λ) ^ m| * (k : ℝ) ^ (-σ₀)
            ≤ (k.divisors.card : ℝ) * 1 * ((2 : ℝ) ^ j) ^ (-σ₀) := by
              gcongr
              · exact hc k hk
              · exact rpow_neg_le_of_two_pow_le (hB k hk).1 hσ₀
          _ = _ := by ring
      calc ‖g k‖ ^ 2 ≤ ((k.divisors.card : ℝ) * ((2 : ℝ) ^ j) ^ (-σ₀)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hgk 2
        _ = _ := by ring
    refine (Finset.sum_le_sum h2).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hsub : B ⊆ Finset.Icc 1 L := fun k hk => Finset.mem_Icc.mpr (hB1 k hk)
    calc ∑ k ∈ B, (k.divisors.card : ℝ) ^ 2 ≤ ∑ k ∈ Finset.Icc 1 L, (k.divisors.card : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ ≤ (L : ℝ) * (1 + Real.log L) ^ (2 ^ 2 - 1) :=
          sum_card_divisors_pow_le_polylog 2 L (by omega)
      _ = (L : ℝ) * (1 + Real.log L) ^ 3 := by norm_num
  -- the discrete mean value theorem
  have hmvt := sum_normSq_dirPoly_finset_le L hL2 a (W := 2 * T) (by positivity) hsep
    (fun x hx y hy => by
      have h1 := hST x hx; have h2 := hST y hy
      rw [abs_le] at h1 h2 ⊢; constructor <;> linarith)
  have hlow : (S.card : ℝ) * V ^ 2 ≤ ∑ x ∈ S, ‖dirPoly L a x‖ ^ (2 : ℕ) := by
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun x hx => ?_
    rw [← hval x]
    exact pow_le_pow_left₀ hV0 (hV x hx) 2
  refine hlow.trans (hmvt.trans ?_)
  refine mul_le_mul_of_nonneg_left hmass ?_
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ L by omega))
  positivity

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
