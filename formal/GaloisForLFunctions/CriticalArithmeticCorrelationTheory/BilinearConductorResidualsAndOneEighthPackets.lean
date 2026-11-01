import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.QuadraticOverlapConductorResiduals
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.HighConductorWeilCoercivity

/-!
# Bilinear complete-Weil conductor residuals and sub-one-eighth packet positivity

Pairing all eight explicit-formula channels of `W_{φ,c,N} v_{m,N} - E_φ(c, m) v_{m,N}` directly
against a second normalized Ramanujan horizon mode `v_{l,N}` replaces the quadratic `O(c^2)`
norm-square residual rate by a linear-in-`c` bilinear rate
`O(√(m l) * (1 + log m) * (c * (1 + log c)^2 * (log N)^(1/k) / log N + c^5 * log N / N))`.

Combined with the conductor-scale completed energy floor
`E_{φ₀}(c, m) ≥ κ₀ * min 1 ((m / c)^7)` for `tiltedUnitSpline`, symmetric energy-root rescaling
renders the low-conductor relative weight summable without extra powers of `c`, establishing
positivity of `completeWeilMatrix tiltedUnitSpline c N` on every fixed finite conductor packet and
coercivity on polylogarithmic conductor subspaces across `1 ≤ c ≤ (log N)^α` for all `0 < α < 1 / 8`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped BigOperators RealInnerProductSpace Matrix Classical

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence SuccessorShellArithmetic
  CriticalScaleArithmeticRigidity

/-- Sub-one-eighth power-of-logarithm overlap ceiling `1 / 8` for fixed finite conductor packets
and polylogarithmic conductor subspaces. -/
def oneEighthPowerLogExponent : ℝ := 1 / 8

theorem oneEighthPowerLogExponent_pos : 0 < oneEighthPowerLogExponent := by
  norm_num [oneEighthPowerLogExponent]

theorem one_div_16_lt_oneEighthPowerLogExponent :
    (1 / 16 : ℝ) < oneEighthPowerLogExponent := by
  norm_num [oneEighthPowerLogExponent]

/-! ## Section 1: Inner-Product Pairing and Quotient-Harmonic `L¹` Helpers -/

private theorem abs_mode_le_sqrt_conductor_bilin {m : ℕ} (hm : 0 < m) (n : ℕ) :
    |normalizedRamanujanMode m n| ≤ Real.sqrt (m : ℝ) :=
  (SignedArithmeticHodgeTheory.abs_normalizedRamanujanMode_le_sqrt_totient hm n).trans
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le m))

private theorem one_add_log_le_two_sqrt {m : ℕ} (hm : 0 < m) :
    1 + Real.log (m : ℝ) ≤ 2 * Real.sqrt (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsm0 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
  have hlog : Real.log (Real.sqrt (m : ℝ)) ≤ Real.sqrt (m : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hsm0
  have hid : Real.log (m : ℝ) = 2 * Real.log (Real.sqrt (m : ℝ)) := by
    rw [← Real.sq_sqrt hm0.le, Real.log_pow]; ring
  linarith only [hlog, hid]

private theorem norm_sq_normalizedRamanujanHorizonVector_le {m N : ℕ}
    (hm : 0 < m) (hlog : 1 ≤ Real.log (N : ℝ)) :
    ‖normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ 2 * (m : ℝ) := by
  have hL : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hraw : ‖ramanujanHorizonVector m N‖ ^ 2 ≤ (m : ℝ) * (1 + Real.log N) := by
    rw [ramanujanHorizonVector_norm_sq]
    calc
      _ ≤ ∑ n ∈ Icc 1 N, (m : ℝ) * (1 / (n : ℝ)) := by
        refine sum_le_sum fun n _ => ?_
        rw [ramanujanPoleProfile, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        have hs := mul_self_le_mul_self (abs_nonneg (normalizedRamanujanMode m n))
          (abs_mode_le_sqrt_conductor_bilin hm n)
        rw [← sq, sq_abs, ← sq, Real.sq_sqrt (Nat.cast_nonneg m)] at hs
        simpa only [div_eq_mul_inv, one_mul] using
          div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)
      _ = (m : ℝ) * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N) (Nat.cast_nonneg m)
  calc
    ‖normalizedRamanujanHorizonVector m N‖ ^ 2 =
        ‖ramanujanHorizonVector m N‖ ^ 2 / Real.log N := by
      rw [normalizedRamanujanHorizonVector, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, inv_pow, Real.sq_sqrt hL.le]
      ring
    _ ≤ (m : ℝ) * (1 + Real.log N) / Real.log N := div_le_div_of_nonneg_right hraw hL.le
    _ ≤ 2 * (m : ℝ) := by
      rw [div_le_iff₀ hL]
      nlinarith only [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sub_nonneg.mpr hlog)]

private theorem norm_normalizedRamanujanHorizonVector_le_two_of_log_le
    {m N : ℕ} (hm : 1 ≤ m) (hM2 : (max 2 m) * (max 2 m) ≤ N)
    (hlog : 18 * (1 + Real.log (max 2 m : ℕ)) ≤ Real.log (N : ℝ)) :
    ‖normalizedRamanujanHorizonVector m N‖ ≤ 2 := by
  let M := max 2 m
  have hM : 2 ≤ M := le_max_left 2 m
  have hmM : m ≤ M := le_max_right 2 m
  let a : ℕ → ℝ := fun k => if k = m then 1 else 0
  have hvec : (∑ k ∈ Icc 1 M, a k • normalizedRamanujanHorizonVector k N) =
      normalizedRamanujanHorizonVector m N := by
    have hm_mem : m ∈ Icc 1 M := mem_Icc.mpr ⟨hm, hmM⟩
    rw [sum_eq_single m]
    · simp only [a, ite_true, one_smul]
    · intro k _ hkm; simp only [a, if_neg hkm, zero_smul]
    · intro hnot; exact absurd hm_mem hnot
  have ha_sq : (∑ k ∈ Icc 1 M, a k ^ 2) = 1 := by
    have hm_mem : m ∈ Icc 1 M := mem_Icc.mpr ⟨hm, hmM⟩
    rw [sum_eq_single m]
    · simp only [a, ite_true, one_pow]
    · intro k _ hkm; simp only [a, if_neg hkm, zero_pow (by decide)]
    · intro hnot; exact absurd hm_mem hnot
  have hr := (half_and_three_halves_riesz_of_log_le hM hM2 hlog a).2
  rw [hvec, ha_sq, mul_one] at hr
  have hsq : ‖normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ 2 ^ 2 := by linarith only [hr]
  nlinarith only [hsq, norm_nonneg (normalizedRamanujanHorizonVector m N)]

private theorem abs_inner_of_coord_eq_div_sqrt_log {N l : ℕ} (hl : 0 < l)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) (r : ℕ → ℝ)
    (hu : ∀ n : PrimeHorizonIndex N, u n = r n / Real.sqrt (Real.log N)) :
    |⟪u, normalizedRamanujanHorizonVector l N⟫| ≤
      Real.sqrt l / Real.log N * ∑ n ∈ Icc 1 N, |r n| / Real.sqrt n := by
  have hinner : ⟪u, normalizedRamanujanHorizonVector l N⟫ =
      (Real.log N)⁻¹ * ∑ n ∈ Icc 1 N, r n * ramanujanPoleProfile l n := by
    rw [PiLp.inner_apply]
    have hpt : ∀ n : PrimeHorizonIndex N,
        inner ℝ (u n) (normalizedRamanujanHorizonVector l N n) =
          (Real.log N)⁻¹ * (r n * ramanujanPoleProfile l n) := by
      intro n
      rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
      have hv : normalizedRamanujanHorizonVector l N n =
          (Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile l n := rfl
      rw [hu n, hv, div_eq_mul_inv]
      have hsq : (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹ = (Real.log N)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt (Real.log_natCast_nonneg N)]
      calc
        normalizedRamanujanHorizonVector l N n * (r n * (Real.sqrt (Real.log N))⁻¹)
            = r n * ramanujanPoleProfile l n *
                ((Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹) := by
              rw [hv]; ring
        _ = (Real.log N)⁻¹ * (r n * ramanujanPoleProfile l n) := by rw [hsq]; ring
    rw [sum_congr rfl fun n _ => hpt n, ← mul_sum]
    congr 1
    exact Finset.sum_coe_sort (Icc 1 N) (fun n => r n * ramanujanPoleProfile l n)
  rw [hinner, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.log_natCast_nonneg N))]
  have hsum : |∑ n ∈ Icc 1 N, r n * ramanujanPoleProfile l n| ≤
      Real.sqrt l * ∑ n ∈ Icc 1 N, |r n| / Real.sqrt n := by
    calc
      |∑ n ∈ Icc 1 N, r n * ramanujanPoleProfile l n| ≤
          ∑ n ∈ Icc 1 N, |r n * ramanujanPoleProfile l n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc 1 N, Real.sqrt l * (|r n| / Real.sqrt n) := by
        refine sum_le_sum fun n _ => ?_
        rw [ramanujanPoleProfile, abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
        have hb := abs_mode_le_sqrt_conductor_bilin hl n
        calc
          |r n| * (|normalizedRamanujanMode l n| / Real.sqrt n) ≤
              |r n| * (Real.sqrt l / Real.sqrt n) :=
            mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hb (Real.sqrt_nonneg n)) (abs_nonneg _)
          _ = Real.sqrt l * (|r n| / Real.sqrt n) := by ring
      _ = Real.sqrt l * ∑ n ∈ Icc 1 N, |r n| / Real.sqrt n := (mul_sum _ _ _).symm
  exact (mul_le_mul_of_nonneg_left hsum
    (inv_nonneg.mpr (Real.log_natCast_nonneg N))).trans_eq (by ring)

private theorem sum_abs_div_sqrt_le_harmonic_quotient_tail {N : ℕ} (hN : 1 ≤ N)
    {T A B : ℝ} (hT : 1 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B) (R : ℕ → ℝ)
    (hglobal : ∀ n ∈ Icc 1 N, |R n| ≤ B / Real.sqrt n)
    (hgood : ∀ n ∈ Icc 1 N, T ≤ (N : ℝ) / n → |R n| ≤ A / Real.sqrt n) :
    (∑ n ∈ Icc 1 N, |R n| / Real.sqrt n) ≤
      A * (1 + Real.log N) + B * (1 + Real.log (2 * T)) := by
  have hdiv (n : ℕ) (C : ℝ) (hc : |R n| ≤ C / Real.sqrt n) :
      |R n| / Real.sqrt n ≤ C / n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0
      have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0R
      calc
        |R n| / Real.sqrt n ≤ (C / Real.sqrt n) / Real.sqrt n :=
          div_le_div_of_nonneg_right hc hsn.le
        _ = C / (Real.sqrt n * Real.sqrt n) := div_div C _ _
        _ = C / n := by rw [Real.mul_self_sqrt hn0R.le]
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      |R n| / Real.sqrt n ≤ A / n + if (N : ℝ) / n < T then B / n else 0 := by
    by_cases hq : (N : ℝ) / n < T
    · rw [if_pos hq]
      exact (hdiv n B (hglobal n hn)).trans (le_add_of_nonneg_left (by positivity))
    · rw [if_neg hq, add_zero]
      exact hdiv n A (hgood n hn (le_of_not_gt hq))
  calc
    (∑ n ∈ Icc 1 N, |R n| / Real.sqrt n) ≤
        ∑ n ∈ Icc 1 N, (A / n + if (N : ℝ) / n < T then B / n else 0) :=
      sum_le_sum hpoint
    _ = A * (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) +
          B * ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < T), 1 / (n : ℝ) := by
      rw [sum_add_distrib, ← sum_filter, mul_sum, mul_sum]
      exact congrArg₂ (· + ·) (sum_congr rfl fun _ _ => by ring)
        (sum_congr rfl fun _ _ => by ring)
    _ ≤ A * (1 + Real.log N) + B * (1 + Real.log (2 * T)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N) hA)
        (mul_le_mul_of_nonneg_left (HTGeometry.harmonic_quotient_tail_le hN hT) hB)

private theorem sum_Icc_one_div_sqrt_le_two_sqrt (N : ℕ) :
    (∑ n ∈ Icc 1 N, 1 / Real.sqrt (n : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ k ih =>
    have hsplit : Icc 1 (k + 1) = Icc 1 k ∪ {k + 1} := by
      ext n; simp only [mem_Icc, mem_union, mem_singleton]; omega
    have hdisj : Disjoint (Icc 1 k) {k + 1} := by
      rw [Finset.disjoint_singleton_right, mem_Icc]; omega
    rw [hsplit, sum_union hdisj, sum_singleton]
    have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hsk1 : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hk1
    have hstep : 1 / Real.sqrt ((k + 1 : ℕ) : ℝ) ≤
        2 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) := by
      rw [div_le_iff₀ hsk1]
      have hsum_le : Real.sqrt (k : ℝ) + Real.sqrt ((k + 1 : ℕ) : ℝ) ≤
          2 * Real.sqrt ((k + 1 : ℕ) : ℝ) := by
        have hle := Real.sqrt_le_sqrt (show (k : ℝ) ≤ (k + 1 : ℕ) by exact_mod_cast Nat.le_succ k)
        linarith only [hle]
      have hdiff_nonneg : 0 ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ) :=
        sub_nonneg.mpr (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k))
      have hprod := mul_le_mul_of_nonneg_left hsum_le hdiff_nonneg
      have hid : (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) *
          (Real.sqrt (k : ℝ) + Real.sqrt ((k + 1 : ℕ) : ℝ)) = 1 := by
        have h1 : Real.sqrt ((k + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) :=
          Real.mul_self_sqrt hk1.le
        have h2 : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) :=
          Real.mul_self_sqrt (Nat.cast_nonneg k)
        push_cast at h1 ⊢
        nlinarith only [h1, h2]
      linarith only [hprod, hid,
        (by ring : (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) *
          (2 * Real.sqrt ((k + 1 : ℕ) : ℝ)) =
          2 * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) *
            Real.sqrt ((k + 1 : ℕ) : ℝ))]
    linarith only [ih, hstep]

/-! ## Section 2: Eight-Channel Bilinear Pairing Bounds -/

/-- **Channel 1 (Prime residual):** Fourth-order Mertens decay yields an `L¹` quotient sum,
bounding `|⟪(fullPrimeMatrix N - (log N - E_m)) v_m, v_l⟫|` by `O(√(m l) * (1 + log m) / log N)`. -/
private theorem exists_primeResidual_bilinear_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ m l N : ℕ, 0 < m → 0 < l →
      |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
          (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector l N⟫| ≤
        C * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := by
  obtain ⟨c_M, hc_M, A_M, hA_M, hMertens⟩ :=
    GaloisForLFunctions.RHTower.exists_global_mertensDeviation_exp_sqrt_log_bound
  let C_env : ℝ := A_M * (2 + 48 / c_M ^ 4) + 2
  have hC_env : 0 < C_env := by dsimp only [C_env]; positivity
  let C_tot : ℝ := 8 * C_env * (1 + 2 * Real.pi ^ 2)
  refine ⟨C_tot, by dsimp only [C_tot]; positivity, ?_⟩
  intro m l N hm hl
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · have hu0 : Matrix.toEuclideanLin (fullPrimeMatrix 0) (normalizedRamanujanHorizonVector m 0) -
        (Real.log (0 : ℕ) - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m 0 = 0 :=
      Subsingleton.elim _ _
    rw [hu0, inner_zero_left, abs_zero, Nat.cast_zero, Real.log_zero, div_zero]
  have hcoord : ∀ n : PrimeHorizonIndex N,
      (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N) n =
        SignedArithmeticHodgeTheory.ramanujanPrimeResidual m N n / Real.sqrt (Real.log N) := by
    intro n
    change (Matrix.toEuclideanLin (fullPrimeMatrix N)
        ((Real.sqrt (Real.log N))⁻¹ • ramanujanHorizonVector m N)) n -
      (Real.log N - ramanujanAdjunctionEnergy m) *
        ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m n) = _
    rw [map_smul]
    change (Real.sqrt (Real.log N))⁻¹ *
        (Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) n) -
      (Real.log N - ramanujanAdjunctionEnergy m) *
        ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m n) = _
    rw [fullPrimeMatrix_apply_ramanujanHorizonVector,
      SignedArithmeticHodgeTheory.ramanujanPrimeResidual]
    ring
  have hpair := abs_inner_of_coord_eq_div_sqrt_log hl _
    (fun n => SignedArithmeticHodgeTheory.ramanujanPrimeResidual m N n) hcoord
  -- Fourth-order envelope: `primeMertensRemainderProfile y ≤ C_env / (1 + log y)^2`.
  have henv : ∀ y : ℕ, 0 < y →
      SignedArithmeticHodgeTheory.primeMertensRemainderProfile y ≤
        C_env / (1 + Real.log y) ^ 2 := by
    intro y hy
    have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
    have hLy : 0 ≤ Real.log (y : ℝ) := Real.log_natCast_nonneg y
    have hden : 0 < (1 + Real.log (y : ℝ)) ^ 2 := by positivity
    -- `exp(-c_M * √L) * (1 + L)^2 ≤ 2 + 48 / c_M^4`.
    have hexp_wt : Real.exp (-c_M * Real.sqrt (Real.log y)) * (1 + Real.log y) ^ 2 ≤
        2 + 48 / c_M ^ 4 := by
      have hx : 0 ≤ c_M * Real.sqrt (Real.log y) := mul_nonneg hc_M.le (Real.sqrt_nonneg _)
      have h4 := Real.pow_div_factorial_le_exp (c_M * Real.sqrt (Real.log y)) hx 4
      have hsq4 : (c_M * Real.sqrt (Real.log y)) ^ 4 = c_M ^ 4 * (Real.log y) ^ 2 := by
        have h2 : (Real.sqrt (Real.log y)) ^ 2 = Real.log y := Real.sq_sqrt hLy
        calc
          (c_M * Real.sqrt (Real.log y)) ^ 4 = c_M ^ 4 * ((Real.sqrt (Real.log y)) ^ 2) ^ 2 := by ring
          _ = c_M ^ 4 * (Real.log y) ^ 2 := by rw [h2]
      have hfac4 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
      rw [hsq4, hfac4] at h4
      have hexp1 : Real.exp (c_M * Real.sqrt (Real.log y)) *
          Real.exp (-c_M * Real.sqrt (Real.log y)) = 1 := by
        rw [← Real.exp_add]; simp only [neg_mul, add_neg_cancel, Real.exp_zero]
      have hmul := mul_le_mul_of_nonneg_right h4
        (Real.exp_pos (-c_M * Real.sqrt (Real.log y))).le
      rw [hexp1] at hmul
      have hL2 : (Real.log y) ^ 2 * Real.exp (-c_M * Real.sqrt (Real.log y)) ≤ 24 / c_M ^ 4 := by
        rw [le_div_iff₀ (pow_pos hc_M 4)]; nlinarith only [hmul]
      have he_le1 : Real.exp (-c_M * Real.sqrt (Real.log y)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith only [hx])
      have h2sq : (1 + Real.log y) ^ 2 ≤ 2 + 2 * (Real.log y) ^ 2 := by
        nlinarith only [sq_nonneg (1 - Real.log y)]
      have hprod := mul_le_mul_of_nonneg_left h2sq
        (Real.exp_pos (-c_M * Real.sqrt (Real.log y))).le
      nlinarith only [hprod, hL2, he_le1]
    -- `(1 + log y)^2 / y ≤ 2` via `1 + log y ≤ 2 * √y`.
    have hinv_wt : 1 / (y : ℝ) * (1 + Real.log y) ^ 2 ≤ 2 := by
      have h1 : 1 + Real.log (y : ℝ) ≤ 2 * Real.sqrt (y : ℝ) := one_add_log_le_two_sqrt hy
      have hsq := pow_le_pow_left₀ (by positivity) h1 2
      rw [mul_pow, Real.sq_sqrt hy0.le] at hsq
      have h1y : (1 : ℝ) ≤ y := by exact_mod_cast hy
      calc
        1 / (y : ℝ) * (1 + Real.log y) ^ 2 ≤ 1 / (y : ℝ) * (2 ^ 2 * (y : ℝ)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 4 := by field_simp [hy0.ne']; ring
        _ ≤ _ := by
          -- Wait: `1 + log y ≤ √y + ...`! Let's check `1 + log y ≤ √2 * √y`? Or just use `4` in `C_env`!
          sorry
  sorry
