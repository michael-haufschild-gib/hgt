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
  set y := molLength T with hy
  set X := truncLength q T with hX
  have hyT : T ≤ (y : ℝ) := Nat.le_ceil T
  have hyT2 : (y : ℝ) ≤ 2 * T := by
    have := Nat.ceil_lt_add_one (show 0 ≤ T by linarith)
    rw [← hy] at this
    linarith
  have hy1 : 1 ≤ y := by
    have : (1 : ℝ) ≤ y := by linarith
    exact_mod_cast this
  set A : ℝ := 4 * q * (2 * T + 3) * (y : ℝ) with hA
  have hA1 : (y : ℝ) ≤ A ^ 2 := by
    have h1 : (y : ℝ) ≤ A := by
      rw [hA]
      have : 1 ≤ 4 * (q : ℝ) * (2 * T + 3) := by nlinarith
      nlinarith
    nlinarith
  have hXA : A ^ 2 ≤ (X : ℝ) := Nat.le_ceil _
  have hXA' : (X : ℝ) ≤ A ^ 2 + 1 := by
    have := Nat.ceil_lt_add_one (sq_nonneg A)
    rw [← hX] at this
    linarith
  have hyX : y ≤ X := by
    have : (y : ℝ) ≤ X := hA1.trans hXA
    exact_mod_cast this
  refine ⟨hy1, hyT, le_trans hy1 hyX, hyX, by linarith, ?_, ?_⟩
  · have hX2 : (2 : ℝ) ≤ X := by
      have : (2 : ℝ) ≤ A ^ 2 := by
        have : (2 : ℝ) ≤ A := by rw [hA]; nlinarith
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

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
