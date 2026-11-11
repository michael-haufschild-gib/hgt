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

open Complex Finset RHTower RHTower.Sieve

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
theorem sum_fin_block_eq {M : Type*} [AddCommMonoid M] {L : ℕ} {B : Finset ℕ}
    (hB : ∀ k ∈ B, 1 ≤ k ∧ k ≤ L) (G : ℕ → M) :
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
      by_cases h : (n : ℕ) + 1 ∈ B
      · simp only [ha, if_pos h, map_mul, Complex.conj_conj]
      · simp only [ha, if_neg h, map_zero, zero_mul]
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
    have h1 : ∑ n : Fin L, ‖a n‖ ^ (2 : ℕ) = ∑ k ∈ B, ‖g k‖ ^ 2 := by
      rw [← sum_fin_block_eq hB1 (fun k => ‖g k‖ ^ 2)]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases h : (n : ℕ) + 1 ∈ B
      · simp only [ha, if_pos h, RCLike.norm_conj]
      · simp only [ha, if_neg h, map_zero, norm_zero]; norm_num
    rw [h1]
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
            ≤ (k.divisors.card : ℝ) * 1 * ((2 : ℝ) ^ j) ^ (-σ₀) :=
              mul_le_mul (mul_le_mul (hc k hk) hw (abs_nonneg _) (Nat.cast_nonneg _))
                (rpow_neg_le_of_two_pow_le (hB k hk).1 hσ₀) (by positivity) (by positivity)
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
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun x hx => ?_
    rw [← hval x]
    exact pow_le_pow_left₀ hV0 (hV x hx) 2
  refine hlow.trans (hmvt.trans ?_)
  refine mul_le_mul_of_nonneg_left hmass ?_
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ L by omega))
  positivity

/-! ### The arithmetic of one class -/

/-- **The class bound in powers of `T`.**  For a block `[2^j, 2^{j+1})` with `T/2 < 2^j ≤ T⁶` and
`σ ≤ σ₀ ≤ 1`, the large-values bound of `card_mul_sq_le_of_taylor_large` is at most
`1075200 (1 + log T)⁵ T^{12(1 − σ)}`. -/
theorem class_bound_le {T σ σ₀ : ℝ} (hT : 2 ≤ T) {j : ℕ} (hjlow : T / 2 < (2 : ℝ) ^ j)
    (hjhigh : (2 : ℝ) ^ j ≤ T ^ 6) (hσ : 1 / 2 ≤ σ) (hσσ₀ : σ ≤ σ₀) (hσ₀ : σ₀ ≤ 1) :
    (2 * T + 1 + 4 * ((2 ^ (j + 1) : ℕ) : ℝ) * (1 + Real.log ((2 ^ (j + 1) : ℕ) : ℝ))) *
        (1 + 2 * Real.log ((2 ^ (j + 1) : ℕ) : ℝ)) *
        ((((2 : ℝ) ^ j) ^ (-σ₀)) ^ 2 *
          (((2 ^ (j + 1) : ℕ) : ℝ) * (1 + Real.log ((2 ^ (j + 1) : ℕ) : ℝ)) ^ 3))
      ≤ 1075200 * (1 + Real.log T) ^ 5 * T ^ (12 * (1 - σ)) := by
  set P : ℝ := (2 : ℝ) ^ j with hP
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hP0 : 0 < P := by positivity
  have hP1 : 1 ≤ P := one_le_pow₀ (by norm_num)
  have hL : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * P := by push_cast; rw [hP, pow_succ]; ring
  rw [hL]
  set ℓT := Real.log T with hℓT
  have hℓT0 : 0 ≤ ℓT := Real.log_nonneg hT1
  have hl2 := Real.log_two_lt_d9
  -- `log L ≤ 7(1 + log T)`
  have hlogL : Real.log (2 * P) ≤ 7 * (1 + ℓT) := by
    have h1 : Real.log (2 * P) ≤ Real.log (2 * T ^ 6) :=
      Real.log_le_log (by positivity) (by linarith)
    have h2 : Real.log (2 * T ^ 6) = Real.log 2 + 6 * ℓT := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    linarith
  have hlogL0 : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by linarith)
  -- the two terms
  have hsq : (P ^ (-σ₀)) ^ 2 = P ^ (-2 * σ₀) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]; ring_nf
  have hA1 : (2 * T + 1) * (P ^ (-2 * σ₀) * (2 * P)) ≤ 12 * T ^ (12 * (1 - σ)) := by
    have h1 : P ^ (-2 * σ₀) * P = P ^ (1 - 2 * σ₀) := by
      rw [show 1 - 2 * σ₀ = -2 * σ₀ + 1 by ring, Real.rpow_add hP0, Real.rpow_one]
    have h2 : P ^ (1 - 2 * σ₀) ≤ (T / 2) ^ (1 - 2 * σ₀) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hjlow.le (by linarith)
    have h3 : (T / 2) ^ (1 - 2 * σ₀) ≤ 2 * T ^ (1 - 2 * σ₀) := by
      rw [Real.div_rpow hT0.le (by norm_num)]
      rw [div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ 2 * (2 : ℝ) ^ (1 - 2 * σ₀) := by
        have h4 : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ (1 - 2 * σ₀) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        rw [Real.rpow_neg_one] at h4
        linarith
      have hTp : 0 < T ^ (1 - 2 * σ₀) := Real.rpow_pos_of_pos hT0 _
      nlinarith
    have h4 : T * T ^ (1 - 2 * σ₀) ≤ T ^ (12 * (1 - σ)) := by
      rw [show T * T ^ (1 - 2 * σ₀) = T ^ (2 - 2 * σ₀) by
        rw [show 2 - 2 * σ₀ = 1 + (1 - 2 * σ₀) by ring, Real.rpow_add hT0, Real.rpow_one]]
      exact Real.rpow_le_rpow_of_exponent_le hT1 (by nlinarith)
    calc (2 * T + 1) * (P ^ (-2 * σ₀) * (2 * P)) = 2 * (2 * T + 1) * P ^ (1 - 2 * σ₀) := by
          rw [← h1]; ring
      _ ≤ 2 * (3 * T) * (2 * T ^ (1 - 2 * σ₀)) := by
          have hp : 0 ≤ P ^ (1 - 2 * σ₀) := Real.rpow_nonneg hP0.le _
          gcongr
          · linarith
          · exact h2.trans h3
      _ = 12 * (T * T ^ (1 - 2 * σ₀)) := by ring
      _ ≤ 12 * T ^ (12 * (1 - σ)) := by linarith
  have hA2 : 4 * (2 * P) * (1 + Real.log (2 * P)) * (P ^ (-2 * σ₀) * (2 * P))
      ≤ 128 * (1 + ℓT) * T ^ (12 * (1 - σ)) := by
    have h1 : P * (P ^ (-2 * σ₀) * P) = P ^ (2 - 2 * σ₀) := by
      rw [show 2 - 2 * σ₀ = 1 + (-2 * σ₀ + 1) by ring, Real.rpow_add hP0, Real.rpow_add hP0,
        Real.rpow_one]
    have h2 : P ^ (2 - 2 * σ₀) ≤ (T ^ 6) ^ (2 - 2 * σ₀) :=
      Real.rpow_le_rpow hP0.le hjhigh (by linarith)
    have h3 : (T ^ 6) ^ (2 - 2 * σ₀) ≤ T ^ (12 * (1 - σ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
      exact Real.rpow_le_rpow_of_exponent_le hT1 (by push_cast; nlinarith)
    have hTp : 0 ≤ T ^ (12 * (1 - σ)) := Real.rpow_nonneg hT0.le _
    calc 4 * (2 * P) * (1 + Real.log (2 * P)) * (P ^ (-2 * σ₀) * (2 * P))
        = 16 * (1 + Real.log (2 * P)) * (P * (P ^ (-2 * σ₀) * P)) := by ring
      _ ≤ 16 * (8 * (1 + ℓT)) * T ^ (12 * (1 - σ)) := by
          rw [h1]
          gcongr
          · linarith
          · exact h2.trans h3
      _ = 128 * (1 + ℓT) * T ^ (12 * (1 - σ)) := by ring
  have hTp : 0 ≤ T ^ (12 * (1 - σ)) := Real.rpow_nonneg hT0.le _
  rw [hsq]
  have hsum : (2 * T + 1 + 4 * (2 * P) * (1 + Real.log (2 * P))) * (P ^ (-2 * σ₀) * (2 * P))
      ≤ 140 * (1 + ℓT) * T ^ (12 * (1 - σ)) := by
    have : 12 * T ^ (12 * (1 - σ)) ≤ 12 * (1 + ℓT) * T ^ (12 * (1 - σ)) := by
      have := mul_le_mul_of_nonneg_right (show (12 : ℝ) ≤ 12 * (1 + ℓT) by nlinarith) hTp
      linarith
    nlinarith
  have hmid : 1 + 2 * Real.log (2 * P) ≤ 15 * (1 + ℓT) := by linarith
  have hcube : (1 + Real.log (2 * P)) ^ 3 ≤ (8 * (1 + ℓT)) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hpos1 : 0 ≤ (P ^ (-2 * σ₀) * (2 * P)) := by positivity
  calc (2 * T + 1 + 4 * (2 * P) * (1 + Real.log (2 * P))) * (1 + 2 * Real.log (2 * P)) *
        (P ^ (-2 * σ₀) * ((2 * P) * (1 + Real.log (2 * P)) ^ 3))
      = ((2 * T + 1 + 4 * (2 * P) * (1 + Real.log (2 * P))) * (P ^ (-2 * σ₀) * (2 * P))) *
          (1 + 2 * Real.log (2 * P)) * (1 + Real.log (2 * P)) ^ 3 := by ring
    _ ≤ (140 * (1 + ℓT) * T ^ (12 * (1 - σ))) * (15 * (1 + ℓT)) * (8 * (1 + ℓT)) ^ 3 := by
        gcongr
    _ = 1075200 * (1 + ℓT) ^ 5 * T ^ (12 * (1 - σ)) := by ring

/-! ### The detection parameters -/

/-- The mollifier length `y = ⌈T⌉`. -/
def molLength (T : ℝ) : ℕ := ⌈T⌉₊

/-- The truncation length `X = ⌈(4q(2T + 3)y)²⌉`. -/
def truncLength (q : ℕ) (T : ℝ) : ℕ := ⌈(4 * q * (2 * T + 3) * (molLength T : ℝ)) ^ 2⌉₊

theorem detection_parameters {q : ℕ} (hq : 1 ≤ q) {T : ℝ} (hT : 2050 * (q : ℝ) ^ 2 ≤ T) :
    1 ≤ molLength T ∧ T ≤ (molLength T : ℝ) ∧ 1 ≤ truncLength q T ∧
      molLength T ≤ truncLength q T ∧
      (4 * q * (2 * T + 3) * (molLength T : ℝ)) ^ 2 ≤ (truncLength q T : ℝ) + 1 ∧
      2 ≤ truncLength q T * molLength T ∧
      ((truncLength q T * molLength T : ℕ) : ℝ) ≤ T ^ 6 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hT2 : 2050 ≤ T := by nlinarith
  unfold truncLength molLength
  set y := ⌈T⌉₊ with hy
  have hyT : T ≤ (y : ℝ) := Nat.le_ceil T
  have hyT2 : (y : ℝ) ≤ 2 * T := by
    have h : (y : ℝ) < T + 1 := Nat.ceil_lt_add_one (show 0 ≤ T by linarith)
    linarith
  have hy1 : 1 ≤ y := by
    have : (1 : ℝ) ≤ y := by linarith
    exact_mod_cast this
  set A : ℝ := 4 * q * (2 * T + 3) * (y : ℝ) with hA
  set X := ⌈A ^ 2⌉₊ with hX
  have hA1 : (y : ℝ) ≤ A ^ 2 := by
    have h1 : (y : ℝ) ≤ A := by
      rw [hA]
      have : 1 ≤ 4 * (q : ℝ) * (2 * T + 3) := by nlinarith
      nlinarith
    nlinarith
  have hXA : A ^ 2 ≤ (X : ℝ) := Nat.le_ceil _
  have hXA' : (X : ℝ) ≤ A ^ 2 + 1 := by
    have h : (X : ℝ) < A ^ 2 + 1 := Nat.ceil_lt_add_one (sq_nonneg A)
    linarith
  have hyX : y ≤ X := by
    have : (y : ℝ) ≤ X := hA1.trans hXA
    exact_mod_cast this
  refine ⟨hy1, hyT, le_trans hy1 hyX, hyX, by show A ^ 2 ≤ (X : ℝ) + 1; linarith, ?_, ?_⟩
  · have hX2 : (2 : ℝ) ≤ X := by
      have : (2 : ℝ) ≤ A ^ 2 := by
        have : (2 : ℝ) ≤ A := by
          have h1 : (2 : ℝ) ≤ 4 * q * (2 * T + 3) := by nlinarith
          have hy1' : (1 : ℝ) ≤ y := by exact_mod_cast hy1
          rw [hA]
          nlinarith [mul_le_mul h1 hy1' zero_le_one (by linarith)]
        nlinarith
      linarith
    have : (2 : ℝ) ≤ ((X * y : ℕ) : ℝ) := by
      push_cast
      have : (1 : ℝ) ≤ y := by exact_mod_cast hy1
      nlinarith
    exact_mod_cast this
  · push_cast
    have hA2 : A ^ 2 ≤ 1024 * (q : ℝ) ^ 2 * T ^ 4 := by
      have h1 : A ≤ 32 * q * T ^ 2 := by
        rw [hA]
        have : 2 * T + 3 ≤ 4 * T := by linarith
        have hq0 : (0 : ℝ) ≤ q := by linarith
        calc 4 * (q : ℝ) * (2 * T + 3) * y ≤ 4 * q * (4 * T) * (2 * T) := by gcongr
          _ = 32 * q * T ^ 2 := by ring
      have hA0 : 0 ≤ A := by positivity
      nlinarith
    have hX4 : (X : ℝ) ≤ 1025 * (q : ℝ) ^ 2 * T ^ 4 := by
      have : (1 : ℝ) ≤ (q : ℝ) ^ 2 * T ^ 4 := by
        have : (1 : ℝ) ≤ T ^ 4 := one_le_pow₀ (by linarith)
        nlinarith
      linarith
    have hT0 : 0 ≤ T := by linarith
    calc (X : ℝ) * y ≤ 1025 * (q : ℝ) ^ 2 * T ^ 4 * (2 * T) :=
          mul_le_mul hX4 hyT2 (by positivity) (by positivity)
      _ = (2050 * (q : ℝ) ^ 2) * T ^ 5 := by ring
      _ ≤ T * T ^ 5 := mul_le_mul_of_nonneg_right hT (by positivity)
      _ = T ^ 6 := by ring

/-- The logarithmic sizes: `Λ = log(Xy) ≤ 6 log T`, `J ≤ 2Λ + 1`. -/
theorem natLog_two_le_two_mul_log {n : ℕ} (hn : 1 ≤ n) :
    ((Nat.log 2 n : ℕ) : ℝ) ≤ 2 * Real.log n := by
  have h1 : 2 ^ (Nat.log 2 n) ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ) ^ (Nat.log 2 n)) ≤ (n : ℝ) := by exact_mod_cast h1
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  have h4 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 n)]

/-! ### Zeros, classes and the count -/

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- Zeros of `Λ(s, χ)` right of the imaginary axis are zeros of `L(s, χ)`. -/
theorem LFunction_point_eq_zero (hχ : χ ≠ 1) (r : LZero χ) (hr : 0 < r.point.re) :
    DirichletCharacter.LFunction χ r.point = 0 := by
  have h := completedLFunction_point hχ r
  rw [completedLFunction_eq_mul hr] at h
  exact (mul_eq_zero.mp h).resolve_left (gammaFactor_ne_zero hr)

/-- **Every zero has a class.** -/
theorem exists_class_of_zero (hχ : χ ≠ 1) {T σ : ℝ} (hT : 2050 * (q : ℝ) ^ 2 ≤ T)
    (hσ : 1 / 2 ≤ σ) (r : LZero χ) (hr : σ ≤ r.point.re ∧ |r.point.im| ≤ T) :
    ∃ i < ⌊Real.log ((truncLength q T * molLength T : ℕ) : ℝ)⌋₊ + 1,
      σ + i / Real.log ((truncLength q T * molLength T : ℕ) : ℝ) ≤ r.point.re ∧
      ∃ j < detBlockCount (truncLength q T) (molLength T),
        ∃ m < detBlockCount (truncLength q T) (molLength T) + 8,
          1 / (12 * detBlockCount (truncLength q T) (molLength T)) ≤
            ‖abscissaTaylorPoly (detDyadicBlock (truncLength q T) (molLength T) j)
              (detCoeffChi χ (truncLength q T) (molLength T))
              (Real.log ((truncLength q T * molLength T : ℕ) : ℝ)) m
              (σ + i / Real.log ((truncLength q T * molLength T : ℕ) : ℝ)) r.point.im‖ := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  obtain ⟨hy1, hyT, hX1, _, hXbig, hXy2, _⟩ := detection_parameters hq hT
  have hT0 : 0 ≤ T := by
    have : (0 : ℝ) ≤ 2050 * (q : ℝ) ^ 2 := by positivity
    linarith
  have hβ1 : r.point.re ≤ 1 := (point_re_lt_one hχ r).le
  have hz := LFunction_point_eq_zero hχ r (by linarith)
  have hρT : ‖r.point‖ ≤ T + 1 := by
    have h := Complex.norm_le_abs_re_add_abs_im r.point
    have h1 : |r.point.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    linarith [hr.2]
  have hdet := half_le_norm_detPolyChi hχ hX1 hy1 hT0 hXbig (by linarith) hρT hz
  rw [← Complex.re_add_im r.point] at hdet
  exact exists_class_of_detected χ hXy2 (by linarith) hr.1 hβ1 hdet

/-- **The local count inside a set of zeros.** -/
theorem card_filter_window_le {Cl : ℝ} (hCl : 0 ≤ Cl)
    (hloc : ∀ t : ℝ,
      {r : LZero χ | 1 / 2 ≤ r.point.re ∧ |r.point.im - t| ≤ 1}.Finite ∧
      ({r : LZero χ | 1 / 2 ≤ r.point.re ∧ |r.point.im - t| ≤ 1}.ncard : ℝ) ≤
        Cl * Real.log (|t| + 3))
    {T : ℝ} (hT : 0 ≤ T) {Zc : Finset (LZero χ)}
    (hZc : ∀ r ∈ Zc, 1 / 2 ≤ r.point.re ∧ |r.point.im| ≤ T) (t : ℝ) :
    ((Zc.filter (fun r => |r.point.im - t| ≤ 1)).card : ℝ) ≤ Cl * Real.log (T + 4) := by
  classical
  have hK0 : 0 ≤ Cl * Real.log (T + 4) := mul_nonneg hCl (Real.log_nonneg (by linarith))
  by_cases ht : |t| ≤ T + 1
  · obtain ⟨hfin, hcount⟩ := hloc t
    have hsub : ((Zc.filter (fun r => |r.point.im - t| ≤ 1) : Finset (LZero χ)) : Set (LZero χ))
        ⊆ {r : LZero χ | 1 / 2 ≤ r.point.re ∧ |r.point.im - t| ≤ 1} := by
      intro r hr
      rw [Finset.coe_filter] at hr
      exact ⟨(hZc r hr.1).1, hr.2⟩
    have h1 := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at h1
    have h2 : Real.log (|t| + 3) ≤ Real.log (T + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    calc ((Zc.filter (fun r => |r.point.im - t| ≤ 1)).card : ℝ)
        ≤ ({r : LZero χ | 1 / 2 ≤ r.point.re ∧ |r.point.im - t| ≤ 1}.ncard : ℝ) := by
          exact_mod_cast h1
      _ ≤ Cl * Real.log (|t| + 3) := hcount
      _ ≤ Cl * Real.log (T + 4) := mul_le_mul_of_nonneg_left h2 hCl
  · have hempty : Zc.filter (fun r => |r.point.im - t| ≤ 1) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun r hr hrt => ht ?_
      have h1 := (hZc r hr).2
      have h2 := abs_sub_abs_le_abs_sub t r.point.im
      rw [abs_sub_comm] at hrt
      linarith
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact hK0

/-- **The count of one class.**  A nonempty set of zeros sharing a class `(i, j, m)` has at most
`K · 144 J² · 1075200 (1 + log T)⁵ T^{12(1 − σ)}` elements, `K` the local count. -/
theorem card_class_le (hχ : χ ≠ 1) {T σ K : ℝ} (hT : 2050 * (q : ℝ) ^ 2 ≤ T) (hσ : 1 / 2 ≤ σ)
    {i j m : ℕ} {Zc : Finset (LZero χ)} (hne : Zc.Nonempty)
    (hprop : ∀ r ∈ Zc, |r.point.im| ≤ T ∧
      σ + i / Real.log ((truncLength q T * molLength T : ℕ) : ℝ) ≤ r.point.re ∧
      1 / (12 * detBlockCount (truncLength q T) (molLength T)) ≤
        ‖abscissaTaylorPoly (detDyadicBlock (truncLength q T) (molLength T) j)
          (detCoeffChi χ (truncLength q T) (molLength T))
          (Real.log ((truncLength q T * molLength T : ℕ) : ℝ)) m
          (σ + i / Real.log ((truncLength q T * molLength T : ℕ) : ℝ)) r.point.im‖)
    (hK : ∀ t : ℝ, ((Zc.filter (fun r => |r.point.im - t| ≤ 1)).card : ℝ) ≤ K) :
    (Zc.card : ℝ) ≤ K * (144 * (detBlockCount (truncLength q T) (molLength T) : ℝ) ^ 2) *
      (1075200 * (1 + Real.log T) ^ 5 * T ^ (12 * (1 - σ))) := by
  classical
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  obtain ⟨hy1, hyT, hX1, hyX, _, hXy2, hXy6⟩ := detection_parameters hq hT
  set X := truncLength q T with hX
  set y := molLength T with hy
  set Λ := Real.log ((X * y : ℕ) : ℝ) with hΛ
  set J := detBlockCount X y with hJ
  set σ₀ := σ + i / Λ with hσ₀
  have hT2 : 2 ≤ T := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have hΛ0 : 0 < Λ := Real.log_pos (by exact_mod_cast (show 1 < X * y by omega))
  have hJ1 : (1 : ℝ) ≤ J := by
    have : 1 ≤ J := by rw [hJ, detBlockCount]; omega
    exact_mod_cast this
  -- the block at a member of the class
  obtain ⟨r₀, hr₀⟩ := hne
  obtain ⟨_, hσ₀r, hbig⟩ := hprop r₀ hr₀
  have hσσ₀ : σ ≤ σ₀ := by
    have : 0 ≤ (i : ℝ) / Λ := by positivity
    rw [hσ₀]; linarith
  have hσ₀1 : σ₀ ≤ 1 := hσ₀r.trans (point_re_lt_one hχ r₀).le
  have hσ₀0 : 0 ≤ σ₀ := by linarith
  have hblock : T / 2 < (2 : ℝ) ^ j ∧ (2 : ℝ) ^ j ≤ T ^ 6 := by
    have hpos : 0 < ‖abscissaTaylorPoly (detDyadicBlock X y j) (detCoeffChi χ X y) Λ m σ₀
        r₀.point.im‖ := lt_of_lt_of_le (by positivity) hbig
    obtain ⟨k, hk, hck⟩ : ∃ k ∈ detDyadicBlock X y j, detCoeffChi χ X y k ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hpos.ne'
      unfold abscissaTaylorPoly
      rw [Finset.sum_eq_zero fun k hk => by rw [hcon k hk]; ring, norm_zero]
    have hkb := mem_detDyadicBlock_bounds hk
    have hks := mem_detSupport_le (Finset.mem_filter.mp hk).1
    have hky : y < k := by
      by_contra hle
      push Not at hle
      apply hck
      unfold detCoeffChi
      rw [detCoeff_eq_zero_of_le hks.1 (hle.trans hyX) hle]
      simp
    have h1 : (T : ℝ) < 2 ^ (j + 1) := by
      have : (y : ℝ) < (2 ^ (j + 1) : ℕ) := by exact_mod_cast hky.trans hkb.2
      push_cast at this
      linarith
    have h2 : ((2 ^ j : ℕ) : ℝ) ≤ ((X * y : ℕ) : ℝ) := by exact_mod_cast hkb.1.trans hks.2
    push_cast at h2
    refine ⟨?_, ?_⟩
    · rw [pow_succ] at h1; linarith
    · push_cast at hXy6; linarith
  -- a maximal separated subset
  obtain ⟨S, hSZ, hsep, hZS⟩ := RHTower.exists_separated_subset_card_le Zc
    (fun r => r.point.im) hK
  set S' := S.image (fun r => r.point.im) with hS'
  have hinj : Set.InjOn (fun r : LZero χ => r.point.im) S := by
    intro a ha b hb hab
    by_contra hne
    have := hsep a ha b hb hne
    simp only at hab
    rw [hab, sub_self, abs_zero] at this
    linarith
  have hcard : S'.card = S.card := Finset.card_image_of_injOn hinj
  have hsep' : ∀ x ∈ S', ∀ x' ∈ S', x ≠ x' → 1 ≤ |x - x'| := by
    intro x hx x' hx' hxx'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx'
    exact hsep a ha b hb (fun h => hxx' (by rw [h]))
  have hST : ∀ x ∈ S', |x| ≤ T := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact (hprop a (hSZ ha)).1
  have hV : ∀ x ∈ S', 1 / (12 * (J : ℝ)) ≤
      ‖abscissaTaylorPoly (detDyadicBlock X y j) (detCoeffChi χ X y) Λ m σ₀ x‖ := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact (hprop a (hSZ ha)).2.2
  have hc : ∀ k ∈ detDyadicBlock X y j, ‖detCoeffChi χ X y k‖ ≤ (k.divisors.card : ℝ) := by
    intro k hk
    have hks := mem_detSupport_le (Finset.mem_filter.mp hk).1
    unfold detCoeffChi
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖χ k‖ * |detCoeff X y k| ≤ 1 * (k.divisors.card : ℝ) :=
          mul_le_mul (DirichletCharacter.norm_le_one χ k)
            (abs_detCoeff_le_divisors hX1 hy1 hks.1) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hΛk : ∀ k ∈ detDyadicBlock X y j, Real.log k ≤ Λ := by
    intro k hk
    have hks := mem_detSupport_le (Finset.mem_filter.mp hk).1
    exact Real.log_le_log (by exact_mod_cast (show 0 < k by omega)) (by exact_mod_cast hks.2)
  have hLV := card_mul_sq_le_of_taylor_large (fun k hk => mem_detDyadicBlock_bounds hk) hc hΛk
    hσ₀0 (by linarith) hsep' hST hV (by positivity)
  have hM := class_bound_le hT2 hblock.1 hblock.2 hσ hσσ₀ hσ₀1
  have hSbound : (S.card : ℝ) ≤ 144 * (J : ℝ) ^ 2 *
      (1075200 * (1 + Real.log T) ^ 5 * T ^ (12 * (1 - σ))) := by
    rw [hcard] at hLV
    have h1 := hLV.trans hM
    have hV2 : (1 / (12 * (J : ℝ))) ^ 2 = 1 / (144 * (J : ℝ) ^ 2) := by ring
    rw [hV2, mul_one_div, div_le_iff₀ (by positivity)] at h1
    linarith
  have hKS := hZS
  have hK0 : 0 ≤ K := le_trans (Nat.cast_nonneg _) (hK 0)
  calc (Zc.card : ℝ) ≤ K * S.card := hKS
    _ ≤ K * (144 * (J : ℝ) ^ 2 * (1075200 * (1 + Real.log T) ^ 5 * T ^ (12 * (1 - σ)))) :=
        mul_le_mul_of_nonneg_left hSbound hK0
    _ = _ := by ring

/-- **The zero-density estimate for a Dirichlet `L`-function.**  For a nonprincipal character `χ`
modulo `q` there is `D` with
`#{ρ : σ ≤ Re ρ, |Im ρ| ≤ T} ≤ D (1 + log T)^{11} T^{12(1 − σ)}`
for all `T ≥ 2050 q²` and `½ ≤ σ ≤ 1`, zeros of `Λ(s, χ)` counted with multiplicity. -/
theorem exists_zeroDensity_character (hχ : χ ≠ 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ T σ : ℝ, 2050 * (q : ℝ) ^ 2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
      {r : LZero χ | σ ≤ r.point.re ∧ |r.point.im| ≤ T}.Finite ∧
      ({r : LZero χ | σ ≤ r.point.re ∧ |r.point.im| ≤ T}.ncard : ℝ) ≤
        D * (1 + Real.log T) ^ 11 * T ^ (12 * (1 - σ)) := by
  classical
  obtain ⟨Cl, hCl, hloc⟩ := card_zeros_near_le hχ
  refine ⟨6 * 12 * 20 * (2 * Cl) * (144 * 144) * 1075200, by positivity,
    fun T σ hT hσ hσ1 => ?_⟩
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  obtain ⟨hy1, hyT, hX1, hyX, _, hXy2, hXy6⟩ := detection_parameters hq hT
  set X := truncLength q T with hX
  set y := molLength T with hy
  set Λ := Real.log ((X * y : ℕ) : ℝ) with hΛ
  set J := detBlockCount X y with hJ
  have hT2 : 2 ≤ T := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have hT0 : 0 < T := by linarith
  set lT := Real.log T with hlT
  have hlT0 : 0 ≤ lT := Real.log_nonneg (by linarith)
  -- finiteness
  have hfin : {r : LZero χ | σ ≤ r.point.re ∧ |r.point.im| ≤ T}.Finite := by
    refine (GaloisForLFunctions.EntireZeroDivisor.locallyFinite_zeroCopyPoint
      (analyticOnNhd_shiftedL hχ) (T + 3)).subset fun r hr => ?_
    obtain ⟨hre, him⟩ := hr
    have hlt := point_re_lt_one hχ r
    simp only [Set.mem_setOf_eq]
    have hz : GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint (shiftedL χ) r
        = r.point - 2 := by simp [LZero.point]
    rw [hz]
    calc ‖r.point - 2‖ ≤ |(r.point - 2).re| + |(r.point - 2).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 2 + T := by
          simp only [sub_re, sub_im, Complex.re_ofNat, Complex.im_ofNat, sub_zero]
          have : |r.point.re - 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith
          linarith
      _ ≤ T + 3 := by linarith
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  set Z := hfin.toFinset with hZ
  have hmemZ : ∀ r ∈ Z, σ ≤ r.point.re ∧ |r.point.im| ≤ T := by
    intro r hr; rwa [hZ, Set.Finite.mem_toFinset] at hr
  -- the classes
  set C : Finset (ℕ × ℕ × ℕ) := range (⌊Λ⌋₊ + 1) ×ˢ (range J ×ˢ range (J + 8)) with hC
  have hcls : ∀ r ∈ Z, ∃ c ∈ C, σ + c.1 / Λ ≤ r.point.re ∧
      1 / (12 * (J : ℝ)) ≤ ‖abscissaTaylorPoly (detDyadicBlock X y c.2.1)
        (detCoeffChi χ X y) Λ c.2.2 (σ + c.1 / Λ) r.point.im‖ := by
    intro r hr
    obtain ⟨i, hi, hiσ, j, hj, m, hm, hbig⟩ := exists_class_of_zero hχ hT hσ r (hmemZ r hr)
    exact ⟨(i, j, m), by simp [hC, hi, hj, hm], hiσ, hbig⟩
  set cls : LZero χ → ℕ × ℕ × ℕ := fun r =>
    if h : r ∈ Z then Classical.choose (hcls r h) else (0, 0, 0) with hclsdef
  have hclsC : ∀ r ∈ Z, cls r ∈ C ∧ σ + (cls r).1 / Λ ≤ r.point.re ∧
      1 / (12 * (J : ℝ)) ≤ ‖abscissaTaylorPoly (detDyadicBlock X y (cls r).2.1)
        (detCoeffChi χ X y) Λ (cls r).2.2 (σ + (cls r).1 / Λ) r.point.im‖ := by
    intro r hr
    have h := Classical.choose_spec (hcls r hr)
    simp only [hclsdef, dif_pos hr]
    exact h
  have hJ1 : 1 ≤ J := by rw [hJ, detBlockCount]; omega
  have hCne : C.Nonempty := ⟨(0, 0, 0), by simp [hC]; omega⟩
  obtain ⟨κ, _, hκ⟩ := RHTower.exists_fiber_card_ge Z C cls (fun r hr => (hclsC r hr).1) hCne
  set Zκ := Z.filter (fun r => cls r = κ) with hZκ
  -- the polylogarithmic sizes
  have hΛT : Λ ≤ 6 * lT := by
    have h := Real.log_le_log (by exact_mod_cast (show 0 < X * y by omega)) hXy6
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hΛ0 : 0 ≤ Λ := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X * y by omega))
  have hCcard : (C.card : ℝ) ≤ (6 * (1 + lT)) * ((12 * (1 + lT)) * (20 * (1 + lT))) := by
    have hJb : (J : ℝ) ≤ 12 * (1 + lT) := by
      have h := natLog_two_le_two_mul_log (n := X * y) (by omega)
      rw [hJ, detBlockCount]
      push_cast
      linarith
    rw [hC, Finset.card_product, Finset.card_product, Finset.card_range, Finset.card_range,
      Finset.card_range]
    push_cast
    have h1 : ((⌊Λ⌋₊ : ℕ) : ℝ) + 1 ≤ 6 * (1 + lT) := by
      have := Nat.floor_le hΛ0
      linarith
    have h2 : (J : ℝ) + 8 ≤ 20 * (1 + lT) := by linarith
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    have : (J : ℝ) * ((J : ℝ) + 8) ≤ (12 * (1 + lT)) * (20 * (1 + lT)) :=
      mul_le_mul hJb h2 (by positivity) (by positivity)
    exact mul_le_mul h1 this (by positivity) (by positivity)
  have hKb : Cl * Real.log (T + 4) ≤ 2 * Cl * (1 + lT) := by
    have h1 : Real.log (T + 4) ≤ Real.log 3 + lT := by
      rw [← Real.log_mul (by norm_num) hT0.ne']
      exact Real.log_le_log (by positivity) (by linarith)
    have h3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
    nlinarith
  have hJ2 : 144 * (J : ℝ) ^ 2 ≤ 144 * 144 * (1 + lT) ^ 2 := by
    have hJb : (J : ℝ) ≤ 12 * (1 + lT) := by
      have h := natLog_two_le_two_mul_log (n := X * y) (by omega)
      rw [hJ, detBlockCount]
      push_cast
      linarith
    have := pow_le_pow_left₀ (Nat.cast_nonneg _) hJb 2
    nlinarith
  have hB0 : 0 ≤ 1075200 * (1 + lT) ^ 5 * T ^ (12 * (1 - σ)) := by positivity
  have hrhs0 : 0 ≤ 6 * 12 * 20 * (2 * Cl) * (144 * 144) * 1075200 * (1 + lT) ^ 11 *
      T ^ (12 * (1 - σ)) := by positivity
  by_cases hne : Zκ.Nonempty
  · have hprop : ∀ r ∈ Zκ, |r.point.im| ≤ T ∧ σ + κ.1 / Λ ≤ r.point.re ∧
        1 / (12 * (J : ℝ)) ≤ ‖abscissaTaylorPoly (detDyadicBlock X y κ.2.1)
          (detCoeffChi χ X y) Λ κ.2.2 (σ + κ.1 / Λ) r.point.im‖ := by
      intro r hr
      rw [hZκ, Finset.mem_filter] at hr
      obtain ⟨_, h1, h2⟩ := hclsC r hr.1
      rw [hr.2] at h1 h2
      exact ⟨(hmemZ r hr.1).2, h1, h2⟩
    have hK := card_filter_window_le hCl hloc hT0.le (Zc := Zκ) (fun r hr => by
      rw [hZκ, Finset.mem_filter] at hr
      exact ⟨by linarith [(hmemZ r hr.1).1], (hmemZ r hr.1).2⟩)
    have hcount := card_class_le hχ hT hσ hne hprop hK
    calc (Z.card : ℝ) ≤ C.card * Zκ.card := hκ
      _ ≤ ((6 * (1 + lT)) * ((12 * (1 + lT)) * (20 * (1 + lT)))) *
            ((2 * Cl * (1 + lT)) * (144 * 144 * (1 + lT) ^ 2) *
              (1075200 * (1 + lT) ^ 5 * T ^ (12 * (1 - σ)))) := by
          refine mul_le_mul hCcard (hcount.trans ?_) (Nat.cast_nonneg _) (by positivity)
          refine mul_le_mul_of_nonneg_right (mul_le_mul hKb hJ2 (by positivity)
            (by positivity)) hB0
      _ = 6 * 12 * 20 * (2 * Cl) * (144 * 144) * 1075200 * (1 + lT) ^ 11 *
            T ^ (12 * (1 - σ)) := by ring
  · have hempty : Zκ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty, Finset.card_empty, Nat.cast_zero, mul_zero] at hκ
    linarith

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
