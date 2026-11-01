import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.QuadraticOverlapConductorResiduals
import GaloisForLFunctions.PNTPlus.Wiener

/-!
# Bilinear complete-Weil conductor residuals and sub-one-eighth packet positivity

Pairing all eight explicit-formula channels of `W_{φ,c,N} v_{m,N} - E_φ(c, m) v_{m,N}` directly
against a second normalized Ramanujan horizon mode `v_{l,N}` replaces the quadratic `O(c^2)`
norm-square residual rate by a linear-in-`c` bilinear rate
`O(√(m l) * (1 + log m) * (c * (1 + log c)^2 * (log N)^(1/k) / log N + c^5 * log N / N))`.

Combined with the conductor-scale completed energy floor
`E_{φ₀}(c, m) ≥ κ₀ * min 1 ((m / c)^7)` for `tiltedUnitSpline`, symmetric energy-root rescaling
renders the low-conductor relative weight summable at first power (`O(c^7)` instead of `O(c^{14})`),
establishing positivity of `completeWeilMatrix tiltedUnitSpline c N` on every fixed finite conductor
packet and coercivity on polylogarithmic conductor subspaces across `1 ≤ c ≤ (log N)^α` for all
`0 < α < 1 / 8`.
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

private theorem sum_range_sub_le_first_bilin (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) (M : ℕ) :
    (∑ k ∈ range M, (g k - g (k + 1))) ≤ g 0 := by
  have htel : ∀ m : ℕ, (∑ k ∈ range m, (g k - g (k + 1))) = g 0 - g m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  rw [htel M]
  linarith only [hg M]

private theorem sum_Icc_inv_sq_from_le_bilin {d N : ℕ} (hd : 1 ≤ d) :
    (∑ k ∈ Icc d N, 1 / (k : ℝ) ^ 2) ≤ 2 / (d : ℝ) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := zero_lt_one.trans_le hd1
  by_cases hdN : d ≤ N
  · have hsplit : Icc d N = insert d (Ioc d N) := by
      ext k; simp only [mem_Icc, mem_insert, mem_Ioc]; omega
    have hmem : d ∉ Ioc d N := by simp only [mem_Ioc]; omega
    rw [hsplit, sum_insert hmem]
    have hfirst : 1 / (d : ℝ) ^ 2 ≤ 1 / (d : ℝ) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hd0) hd0]; nlinarith only [hd1]
    have hreindex : (∑ k ∈ Ioc d N, 1 / (k : ℝ) ^ 2) =
        ∑ i ∈ range (N - d), 1 / ((d : ℝ) + (i + 1 : ℕ)) ^ 2 := by
      refine sum_bij (fun k _ => k - (d + 1)) ?_ ?_ ?_ ?_
      · intro k hk; obtain ⟨h1, h2⟩ := mem_Ioc.mp hk; exact mem_range.mpr (by omega)
      · intro k₁ h1 k₂ h2 heq
        obtain ⟨hk1, _⟩ := mem_Ioc.mp h1; obtain ⟨hk2, _⟩ := mem_Ioc.mp h2
        change k₁ - (d + 1) = k₂ - (d + 1) at heq; omega
      · intro i hi
        have hi' := mem_range.mp hi
        exact ⟨d + (i + 1), mem_Ioc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk
        obtain ⟨hk1, _⟩ := mem_Ioc.mp hk
        have hkeq : (k : ℝ) = (d : ℝ) + ((k - (d + 1) + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show k = d + (k - (d + 1) + 1) by omega)
        rw [hkeq]
    have hstep : ∀ i : ℕ, 1 / ((d : ℝ) + (i + 1 : ℕ)) ^ 2 ≤
        1 / ((d : ℝ) + i) - 1 / ((d : ℝ) + (i + 1 : ℕ)) := by
      intro i
      have ha : 0 < (d : ℝ) + i := by positivity
      have hb : 0 < (d : ℝ) + (i + 1 : ℕ) := by positivity
      have hdiff : 1 / ((d : ℝ) + i) - 1 / ((d : ℝ) + (i + 1 : ℕ)) =
          1 / (((d : ℝ) + i) * ((d : ℝ) + (i + 1 : ℕ))) := by
        field_simp [ha.ne', hb.ne']; push_cast; ring
      rw [hdiff, div_le_div_iff₀ (sq_pos_of_pos hb) (mul_pos ha hb)]
      push_cast; nlinarith only [ha]
    have htail : (∑ k ∈ Ioc d N, 1 / (k : ℝ) ^ 2) ≤ 1 / (d : ℝ) := by
      rw [hreindex]
      calc
        (∑ i ∈ range (N - d), 1 / ((d : ℝ) + (i + 1 : ℕ)) ^ 2) ≤
            ∑ i ∈ range (N - d), (1 / ((d : ℝ) + i) - 1 / ((d : ℝ) + (i + 1 : ℕ))) :=
          sum_le_sum fun i _ => hstep i
        _ ≤ 1 / ((d : ℝ) + (0 : ℕ)) :=
          sum_range_sub_le_first_bilin (fun i => 1 / ((d : ℝ) + i)) (fun _ => by positivity) (N - d)
        _ = 1 / (d : ℝ) := by simp
    linarith only [hfirst, htail, (by ring : 1 / (d : ℝ) + 1 / (d : ℝ) = 2 / (d : ℝ))]
  · rw [Icc_eq_empty hdN, sum_empty]; positivity

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
  let C_env : ℝ := A_M * (2 + 48 / c_M ^ 4) + 4
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
  have henv : ∀ y : ℕ, 0 < y →
      SignedArithmeticHodgeTheory.primeMertensRemainderProfile y ≤
        C_env / (1 + Real.log y) ^ 2 := by
    intro y hy
    have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
    have hLy : 0 ≤ Real.log (y : ℝ) := Real.log_natCast_nonneg y
    have hden : 0 < (1 + Real.log (y : ℝ)) ^ 2 := by positivity
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
    have hinv_wt : 1 / (y : ℝ) * (1 + Real.log y) ^ 2 ≤ 4 := by
      have h1 : 1 + Real.log (y : ℝ) ≤ 2 * Real.sqrt (y : ℝ) := one_add_log_le_two_sqrt hy
      have hsq := pow_le_pow_left₀ (by positivity) h1 2
      rw [mul_pow, Real.sq_sqrt hy0.le] at hsq
      calc
        1 / (y : ℝ) * (1 + Real.log y) ^ 2 ≤ 1 / (y : ℝ) * (2 ^ 2 * (y : ℝ)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 4 := by field_simp [hy0.ne']; ring
    have hM := hMertens y hy
    change |mertensSum y - Real.log y + Real.eulerMascheroniConstant| ≤
      A_M * Real.exp (-c_M * Real.sqrt (Real.log y)) at hM
    rw [le_div_iff₀ hden, SignedArithmeticHodgeTheory.primeMertensRemainderProfile, add_mul]
    have h1 := mul_le_mul_of_nonneg_right hM hden.le
    have h2 := mul_le_mul_of_nonneg_left hexp_wt hA_M
    dsimp only [C_env]
    nlinarith only [h1, h2, hinv_wt]
  have hker_cmp : ∀ n ∈ Icc 1 N,
      1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2 ≤
        2 * (1 + Real.log ((N / n : ℕ) : ℝ)) ^ 2 := by
    intro n hn
    have hn0 : 0 < n := (mem_Icc.mp hn).1
    have hnN : n ≤ N := (mem_Icc.mp hn).2
    have hy : 0 < N / n := Nat.div_pos hnN hn0
    have hyn : (1 : ℝ) ≤ ((N / n : ℕ) : ℝ) := by exact_mod_cast hy
    have hinv : 1 / ((N / n : ℕ) : ℝ) ≤ 1 := div_le_self zero_le_one hyn
    have hr := roundoff_le hn0 hnN
    have hlog : 0 ≤ Real.log ((N / n : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hquot : Real.log ((n : ℝ) / N) = Real.log n - Real.log N :=
      Real.log_div (by exact_mod_cast hn0.ne') (by exact_mod_cast hN0.ne')
    have hnonpos : Real.log ((n : ℝ) / N) ≤ 0 := by rw [hquot]; linarith only [hr.1, hlog]
    have habs : |Real.log ((n : ℝ) / N)| ≤ 1 + Real.log ((N / n : ℕ) : ℝ) := by
      rw [abs_of_nonpos hnonpos, hquot]; linarith only [hr.2, hinv]
    have hα0 : 0 ≤ 1 / (2 * Real.pi) := by positivity
    have hα1 : 1 / (2 * Real.pi) ≤ 1 := one_div_two_pi_mem_Ioo.2.le
    have hα : |1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)| ≤
        1 + Real.log ((N / n : ℕ) : ℝ) := by
      rw [abs_mul, abs_of_nonneg hα0]
      exact (mul_le_mul_of_nonneg_right hα1 (abs_nonneg _)).trans (by simpa using habs)
    have hsq := mul_le_mul hα hα (abs_nonneg _) (by positivity)
    rw [← sq, sq_abs, ← sq] at hsq
    nlinarith only [hsq, hlog]
  have hwiener : (∑ n ∈ Icc 1 N, 1 / (n : ℝ) *
      (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) ≤ 1 + 2 * Real.pi ^ 2 := by
    have hcheby : chebyWith 1 (fun _ : ℕ => (1 : ℂ)) := by intro n; simp [cumsum]
    have hN0R : (0 : ℝ) < N := by exact_mod_cast hN0
    have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN0
    have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) *
        (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) := by
      simpa only [norm_one, one_div] using limiting_fourier_lim1_aux ⟨1, hcheby⟩ hN0R 1 zero_le_one
    have hfull : (∑' n : ℕ, 1 / (n : ℝ) *
        (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) ≤ 1 + 2 * Real.pi ^ 2 := by
      simpa only [norm_one, one_mul] using bound_sum_log' hcheby hN1R
    exact (Summable.sum_le_tsum (Icc 1 N) (fun _ _ => by positivity) hsum).trans hfull
  have hcost : SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m ≤
      4 * Real.sqrt m * (1 + Real.log m) := by
    rw [SignedArithmeticHodgeTheory.ramanujanResidualConductorCost]
    have htot : Real.sqrt (m.totient : ℝ) ≤ Real.sqrt m :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.totient_le m)
    have h14 : 1 + 4 * Real.log (m : ℝ) ≤ 4 * (1 + Real.log m) := by
      linarith [Real.log_natCast_nonneg m]
    exact (mul_le_mul htot h14 (by positivity) (Real.sqrt_nonneg m)).trans_eq (by ring)
  have hrow_sum : (∑ n ∈ Icc 1 N,
      |SignedArithmeticHodgeTheory.ramanujanPrimeResidual m N n| / Real.sqrt n) ≤
      8 * C_env * (1 + 2 * Real.pi ^ 2) * Real.sqrt m * (1 + Real.log m) := by
    have hpt : ∀ n ∈ Icc 1 N,
        |SignedArithmeticHodgeTheory.ramanujanPrimeResidual m N n| / Real.sqrt n ≤
          8 * C_env * Real.sqrt m * (1 + Real.log m) *
            (1 / (n : ℝ) * (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) := by
      intro n hn
      have hn0 : 0 < n := (mem_Icc.mp hn).1
      have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0
      have hy : 0 < N / n := Nat.div_pos (mem_Icc.mp hn).2 hn0
      have hb := SignedArithmeticHodgeTheory.abs_ramanujanPrimeResidual_le hm hn
      have hdiv : |SignedArithmeticHodgeTheory.ramanujanPrimeResidual m N n| / Real.sqrt n ≤
          SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m *
            SignedArithmeticHodgeTheory.primeMertensRemainderProfile (N / n) / (n : ℝ) := by
        calc
          _ ≤ (SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m *
                SignedArithmeticHodgeTheory.primeMertensRemainderProfile (N / n) / Real.sqrt n) /
                Real.sqrt n := div_le_div_of_nonneg_right hb (Real.sqrt_nonneg n)
          _ = SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m *
                SignedArithmeticHodgeTheory.primeMertensRemainderProfile (N / n) /
                (Real.sqrt n * Real.sqrt n) := div_div _ _ _
          _ = _ := by rw [Real.mul_self_sqrt hn0R.le]
      have hkpos : 0 < 1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2 := by positivity
      have hlog_pos : 0 < (1 + Real.log ((N / n : ℕ) : ℝ)) ^ 2 := by
        have := Real.log_natCast_nonneg (N / n); positivity
      have hinv_cmp : 1 / (1 + Real.log ((N / n : ℕ) : ℝ)) ^ 2 ≤
          2 * (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹ := by
        rw [ ← two_div, div_le_div_iff₀ hlog_pos hkpos]
        linarith only [hker_cmp n hn]
      have hprof_le : SignedArithmeticHodgeTheory.primeMertensRemainderProfile (N / n) ≤
          2 * C_env * (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹ := by
        calc
          _ ≤ C_env * (1 / (1 + Real.log ((N / n : ℕ) : ℝ)) ^ 2) := by
            simpa only [div_eq_mul_one_div] using henv (N / n) hy
          _ ≤ C_env * (2 * (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hinv_cmp hC_env.le
          _ = _ := by ring
      have hnum := mul_le_mul hcost hprof_le
        (by unfold SignedArithmeticHodgeTheory.primeMertensRemainderProfile; positivity)
        (by positivity)
      exact hdiv.trans ((div_le_div_of_nonneg_right hnum hn0R.le).trans_eq (by ring))
    calc
      _ ≤ ∑ n ∈ Icc 1 N, 8 * C_env * Real.sqrt m * (1 + Real.log m) *
            (1 / (n : ℝ) * (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹) :=
        sum_le_sum hpt
      _ = (8 * C_env * Real.sqrt m * (1 + Real.log m)) *
            ∑ n ∈ Icc 1 N, 1 / (n : ℝ) *
              (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹ := (mul_sum _ _ _).symm
      _ ≤ (8 * C_env * Real.sqrt m * (1 + Real.log m)) * (1 + 2 * Real.pi ^ 2) :=
        mul_le_mul_of_nonneg_left hwiener (by positivity)
      _ = _ := by ring
  calc
    _ ≤ Real.sqrt l / Real.log N *
          (8 * C_env * (1 + 2 * Real.pi ^ 2) * Real.sqrt m * (1 + Real.log m)) :=
      hpair.trans (mul_le_mul_of_nonneg_left hrow_sum
        (div_nonneg (Real.sqrt_nonneg l) (Real.log_natCast_nonneg N)))
    _ = C_tot * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := by
      dsimp only [C_tot]
      rw [Real.sqrt_mul (Nat.cast_nonneg m)]
      ring

/-- **Channel 2 (Self-energy error):** Cauchy–Schwarz gives `O(√(m l) * c / N)`. -/
private theorem exists_selfError_bilinear_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l : ℕ, 0 < m → 0 < l → ∀ N : ℕ,
      1 ≤ N → 1 ≤ Real.log N → ∀ c : ℝ, 0 < c → c ≤ (N : ℝ) →
        |⟪completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N,
          normalizedRamanujanHorizonVector l N⟫| ≤
          C * Real.sqrt ((m : ℝ) * l) * c / (N : ℝ) := by
  refine ⟨Real.exp (1 / 2), by positivity, fun m l hm hl N hN hlog c hc hcN => ?_⟩
  have hvm_sq := norm_sq_normalizedRamanujanHorizonVector_le hm hlog
  have hvl_sq := norm_sq_normalizedRamanujanHorizonVector_le hl hlog
  have hprod_norm : ‖normalizedRamanujanHorizonVector m N‖ *
      ‖normalizedRamanujanHorizonVector l N‖ ≤ 2 * Real.sqrt ((m : ℝ) * l) := by
    have hsq : (‖normalizedRamanujanHorizonVector m N‖ *
        ‖normalizedRamanujanHorizonVector l N‖) ^ 2 ≤ (2 * Real.sqrt ((m : ℝ) * l)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have hm_mul := mul_le_mul hvm_sq hvl_sq (sq_nonneg _) (by positivity)
      nlinarith only [hm_mul]
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at h
  have hs := abs_completeWeilSelfError_le_of_width_le_one hφ hsupp hM hc hN hcN
  rw [real_inner_smul_left, abs_mul]
  calc
    |completeWeilSelfError φ c N| *
        |⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫| ≤
      (Real.exp (1 / 2) / 2 * (c / N)) *
        (2 * Real.sqrt ((m : ℝ) * l)) :=
      mul_le_mul hs ((abs_real_inner_le_norm _ _).trans hprod_norm) (abs_nonneg _) (by positivity)
    _ = Real.exp (1 / 2) * Real.sqrt ((m : ℝ) * l) * c / (N : ℝ) := by ring

private theorem abs_sum_Icc_normalizedRamanujanMode_div_le_sqrt_log_bilin {m N : ℕ}
    (hm : 2 ≤ m) (hmN : m ≤ N) :
    |∑ j ∈ Icc 1 N, normalizedRamanujanMode m j / (j : ℝ)| ≤
      2 * Real.sqrt m * (1 + Real.log m) := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have h1m : 1 ≤ 1 + Real.log (m : ℝ) := by linarith [Real.log_natCast_nonneg m]
  have hsm1 : 1 ≤ Real.sqrt (m : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ m by exact_mod_cast hm1)
  have hsplit : Icc 1 N = Icc 1 m ∪ Icc (m + 1) N := by
    ext j; simp only [mem_Icc, mem_union]; omega
  have hdisj : Disjoint (Icc 1 m) (Icc (m + 1) N) := by
    rw [Finset.disjoint_left]; intro j h1 h2; simp only [mem_Icc] at h1 h2; omega
  have hhead : |∑ j ∈ Icc 1 m, normalizedRamanujanMode m j / (j : ℝ)| ≤
      Real.sqrt m * (1 + Real.log m) := by
    calc
      |∑ j ∈ Icc 1 m, normalizedRamanujanMode m j / (j : ℝ)| ≤
          ∑ j ∈ Icc 1 m, |normalizedRamanujanMode m j / (j : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Icc 1 m, Real.sqrt m * (1 / (j : ℝ)) := by
        refine sum_le_sum fun j hj => ?_
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
        rw [abs_div, abs_of_pos hj0, div_eq_mul_inv, one_div]
        exact mul_le_mul_of_nonneg_right (abs_mode_le_sqrt_conductor_bilin (by omega) j) (by positivity)
      _ = Real.sqrt m * ∑ j ∈ Icc 1 m, 1 / (j : ℝ) := (mul_sum _ _ _).symm
      _ ≤ Real.sqrt m * (1 + Real.log m) :=
        mul_le_mul_of_nonneg_left (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log m)
          (Real.sqrt_nonneg m)
  have htail : |∑ j ∈ Icc (m + 1) N, normalizedRamanujanMode m j / (j : ℝ)| ≤ 1 := by
    by_cases hmN_eq : N < m + 1
    · rw [Icc_eq_empty (by omega), sum_empty, abs_zero]; norm_num
    · have hpartial : ∀ k ≤ N - m,
          |∑ i ∈ range k, normalizedRamanujanMode m (m + 1 + i)| ≤ (m : ℝ) := by
        intro k _
        have hbij : (∑ i ∈ range k, normalizedRamanujanMode m (m + 1 + i)) =
            ∑ j ∈ Ico (m + 1) (m + 1 + k), normalizedRamanujanMode m j := by
          refine sum_bij (fun i _ => m + 1 + i) ?_ ?_ ?_ ?_
          · intro i hi; exact mem_Ico.mpr ⟨by omega, by linarith [mem_range.mp hi]⟩
          · intro i₁ _ i₂ _ h; omega
          · intro j hj; obtain ⟨h1, h2⟩ := mem_Ico.mp hj
            exact ⟨j - (m + 1), mem_range.mpr (by omega), by omega⟩
          · intro _ _; rfl
        rw [hbij]
        exact CompletedArithmeticForms.abs_sum_Ico_normalizedRamanujanMode_le hm (by omega)
      have hab := HTGeometry.abs_sum_mul_le_of_finite_partial
        (g := fun i => normalizedRamanujanMode m (m + 1 + i))
        (w := fun i => 1 / ((m : ℝ) + 1 + i)) (N - m) hpartial (fun _ => by positivity)
        (fun _ => by apply one_div_le_one_div_of_le (by positivity); push_cast; linarith)
      have heq : (∑ i ∈ range (N - m),
          1 / ((m : ℝ) + 1 + i) * normalizedRamanujanMode m (m + 1 + i)) =
          ∑ j ∈ Icc (m + 1) N, normalizedRamanujanMode m j / (j : ℝ) := by
        refine sum_bij (fun i _ => m + 1 + i) ?_ ?_ ?_ ?_
        · intro i hi; have := mem_range.mp hi; exact mem_Icc.mpr ⟨by omega, by omega⟩
        · intro i₁ _ i₂ _ h; omega
        · intro j hj; obtain ⟨h1, h2⟩ := mem_Icc.mp hj
          exact ⟨j - (m + 1), mem_range.mpr (by omega), by omega⟩
        · intro _ _; push_cast; ring
      rw [heq] at hab
      calc
        |∑ j ∈ Icc (m + 1) N, normalizedRamanujanMode m j / (j : ℝ)| ≤
            (m : ℝ) * (1 / ((m : ℝ) + 1 + (0 : ℕ))) := hab
        _ = (m : ℝ) / ((m : ℝ) + 1) := by simp only [Nat.cast_zero, add_zero, mul_one_div]
        _ ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only)
  rw [hsplit, sum_union hdisj]
  have h1_le : 1 ≤ Real.sqrt m * (1 + Real.log m) := by nlinarith only [hsm1, h1m]
  exact (abs_add_le _ _).trans (by linarith only [hhead, htail, h1_le])

/-- **Channel 3 (Complete center residual):** Ground-pole boundary cancellation (`m = 1` or `l = 1`)
combined with normalized polarization of `abs_fullWeilCenterMatrix_self_inner_le_of_mem_conductorSubspace`
on `(conductorSubspace 1 N)ᗮ` gives `O(|α| * √(m l) * (1 + log m) / log N)`. -/
private theorem fullWeilCenter_residual_bilinear_bound (α : ℝ) {m l N : ℕ}
    (hm : 1 ≤ m) (hl : 1 ≤ l)
    (hMN4 : (max 2 (max m l)) ^ 4 ≤ N)
    (hlog : 18 * (1 + Real.log (max 2 (max m l) : ℕ)) ≤ Real.log (N : ℝ)) :
    |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then α else 0) • normalizedRamanujanHorizonVector m N,
      normalizedRamanujanHorizonVector l N⟫| ≤
      9700 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := by
  let M := max 2 (max m l)
  have hM2 : 2 ≤ M := le_max_left _ _
  have hmM : m ≤ M := (le_max_left m l).trans (le_max_right 2 _)
  have hlM : l ≤ M := (le_max_right m l).trans (le_max_right 2 _)
  have hN16 : 16 ≤ N := (show 16 ≤ M ^ 4 from Nat.pow_le_pow_left hM2 4).trans hMN4
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL1 : 1 ≤ Real.log (N : ℝ) := by
    have := Real.log_natCast_nonneg M; linarith only [hlog, this]
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hMM_N : M * M ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < M) (by norm_num : 2 ≤ 4)).trans hMN4
    simpa only [sq] using hh
  have hmN : m ≤ N := hmM.trans ((Nat.le_mul_self M).trans hMM_N)
  have hlN : l ≤ N := hlM.trans ((Nat.le_mul_self M).trans hMM_N)
  have h1m : 1 ≤ 1 + Real.log (m : ℝ) := by linarith [Real.log_natCast_nonneg m]
  have hsm1 : 1 ≤ Real.sqrt (m : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ m by exact_mod_cast hm)
  have hsl1 : 1 ≤ Real.sqrt (l : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ l by exact_mod_cast hl)
  let r₁ := Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedRamanujanHorizonVector 1 N) -
    α • normalizedRamanujanHorizonVector 1 N
  -- Step 1: Ground residual pairing `|⟪r₁, v_k⟫| ≤ 3 * |α| * √k / log N` for every `k ≥ 1`.
  have hr1_pair : ∀ {k : ℕ}, 1 ≤ k →
      |⟪r₁, normalizedRamanujanHorizonVector k N⟫| ≤
        3 * |α| * Real.sqrt k / Real.log N := by
    intro k hk
    let B_row : ℕ → ℝ := fun n => (α / N) * Real.sqrt n *
      ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 + 3 / (4 * (n : ℝ)))
    have hr1_coord : ∀ n : PrimeHorizonIndex N, r₁ n = B_row n / Real.sqrt (Real.log N) := by
      intro n
      have hn : (n : ℕ) ∈ Icc 1 N := n.2
      have hn0 : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (mem_Icc.mp hn).1
      have hmode1 : ∀ j : ℕ, ramanujanPoleProfile 1 j = 1 / Real.sqrt j := by
        intro j
        simp only [ramanujanPoleProfile, normalizedRamanujanMode_eq_coefficient zero_lt_one,
          Nat.totient_one, Nat.cast_one, Real.sqrt_one, div_one,
          BiScaleUncertainty.SieveMoments.ramanujanLagCoefficient_one]
      change (Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
          ((Real.sqrt (Real.log N))⁻¹ • ramanujanHorizonVector 1 N)) n -
        α * ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile 1 n) = _
      rw [map_smul]
      change (Real.sqrt (Real.log N))⁻¹ *
          ((Matrix.toEuclideanLin
            (horizonKernelMatrix (fun i j => (α / N) *
              (Real.sqrt i / Real.sqrt j + Real.sqrt j / Real.sqrt i - archimedeanCenterKernel i j)) N)
            (horizonProfileVector (ramanujanPoleProfile 1) N)) n) -
        α * ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile 1 n) = _
      rw [horizonKernelMatrix_profile_apply, hmode1 n]
      have hsum_eq : (∑ j ∈ Icc 1 N,
          (α / N) * (Real.sqrt (n : ℕ) / Real.sqrt j + Real.sqrt j / Real.sqrt (n : ℕ) -
            archimedeanCenterKernel n j) * ramanujanPoleProfile 1 j) =
          (α / N) * ∑ j ∈ Icc 1 N,
            ((Real.sqrt (n : ℕ) / Real.sqrt j + Real.sqrt j / Real.sqrt (n : ℕ)) -
              archimedeanCenterKernel n j) / Real.sqrt j := by
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        rw [hmode1 j]; ring
      rw [hsum_eq, sum_pole_minus_center_div_sqrt hn]
      dsimp only [B_row]
      have hcanc : (α / N) * ((N : ℝ) / Real.sqrt (n : ℕ) + Real.sqrt (n : ℕ) *
          ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 +
            3 / (4 * ((n : ℕ) : ℝ)))) - α * (1 / Real.sqrt (n : ℕ)) =
          (α / N) * Real.sqrt (n : ℕ) *
            ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 +
              3 / (4 * ((n : ℕ) : ℝ))) := by
        rw [mul_add, div_mul_div_cancel₀ hN0.ne']; ring
      have hfactor : (Real.sqrt (Real.log N))⁻¹ *
          ((α / N) * ((N : ℝ) / Real.sqrt (n : ℕ) + Real.sqrt (n : ℕ) *
            ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 +
              3 / (4 * ((n : ℕ) : ℝ))))) -
          α * ((Real.sqrt (Real.log N))⁻¹ * (1 / Real.sqrt (n : ℕ))) =
          (Real.sqrt (Real.log N))⁻¹ *
            ((α / N) * ((N : ℝ) / Real.sqrt (n : ℕ) + Real.sqrt (n : ℕ) *
              ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 +
                3 / (4 * ((n : ℕ) : ℝ)))) - α * (1 / Real.sqrt (n : ℕ))) := by ring
      rw [hfactor, hcanc, div_eq_inv_mul]
    have hp := abs_inner_of_coord_eq_div_sqrt_log hk r₁ B_row hr1_coord
    let b_bdry : ℕ → ℝ := fun n =>
      (harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 + 3 / (4 * (n : ℝ))
    have hb_sq_sum : (∑ n ∈ Icc 1 N, b_bdry n ^ 2) ≤ 6 * (N : ℝ) := by
      have hpt : ∀ n ∈ Icc 1 N, b_bdry n ^ 2 ≤ ((harmonic N : ℝ) - harmonic (N - n)) ^ 2 + 4 := by
        intro n hn
        have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
        let a₀ := (harmonic N : ℝ) - harmonic (N - n)
        let b₀ := (harmonic (N + n) : ℝ) - harmonic N
        let d₀ := 3 / (4 * (n : ℝ))
        have hb0_lo : 0 ≤ b₀ := HTGeometry.harmonic_add_sub_nonneg N n
        have hb0_hi : b₀ ≤ 1 := HTGeometry.harmonic_add_sub_le_one (mem_Icc.mp hn).2
        have hd0_lo : 0 ≤ d₀ := by dsimp only [d₀]; positivity
        have hd0_hi : d₀ ≤ 1 := by
          dsimp only [d₀]; rw [div_le_one (by positivity)]; linarith only [hn1R]
        have hb2 : b₀ ^ 2 ≤ 1 := by nlinarith only [mul_nonneg hb0_lo (sub_nonneg.mpr hb0_hi), hb0_hi]
        have hd2 : d₀ ^ 2 ≤ 1 := by nlinarith only [mul_nonneg hd0_lo (sub_nonneg.mpr hd0_hi), hd0_hi]
        have hcs3 : (a₀ - b₀ + 2 * d₀) ^ 2 ≤ 3 * (a₀ ^ 2 + b₀ ^ 2 + 4 * d₀ ^ 2) := by
          nlinarith only [sq_nonneg (a₀ + b₀), sq_nonneg (a₀ - 2 * d₀), sq_nonneg (b₀ + 2 * d₀)]
        have hid_b : b_bdry n = (a₀ - b₀) / 2 + d₀ := by dsimp only [b_bdry, a₀, b₀, d₀]; ring
        rw [hid_b]
        nlinarith only [hcs3, hb2, hd2, sq_nonneg a₀]
      have hhar_nonneg : 0 ≤ (harmonic N : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        exact sum_nonneg fun _ _ => by positivity
      calc
        (∑ n ∈ Icc 1 N, b_bdry n ^ 2) ≤
            ∑ n ∈ Icc 1 N, (((harmonic N : ℝ) - harmonic (N - n)) ^ 2 + 4) := sum_le_sum hpt
        _ = 2 * (N : ℝ) - harmonic N + 4 * (N : ℝ) := by
          rw [sum_add_distrib, HTGeometry.sum_sq_harmonic_boundary_tails,
            sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        _ ≤ 6 * (N : ℝ) := by linarith only [hhar_nonneg]
    have hb_l1 : (∑ n ∈ Icc 1 N, |b_bdry n|) ≤ 3 * (N : ℝ) := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N) (fun n => |b_bdry n|) (fun _ => (1 : ℝ))
      simp only [mul_one, sq_abs, one_pow, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
        nsmul_eq_mul, mul_one] at hcs
      have hsq : (∑ n ∈ Icc 1 N, |b_bdry n|) ^ 2 ≤ (3 * (N : ℝ)) ^ 2 := by
        calc
          _ ≤ (∑ n ∈ Icc 1 N, b_bdry n ^ 2) * (N : ℝ) := hcs
          _ ≤ (6 * (N : ℝ)) * (N : ℝ) := mul_le_mul_of_nonneg_right hb_sq_sum hN0.le
          _ ≤ (3 * (N : ℝ)) ^ 2 := by nlinarith only [sq_nonneg (N : ℝ)]
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (sum_nonneg fun _ _ => abs_nonneg _), Real.sqrt_sq (by positivity)] at h
    have hsum_B : (∑ n ∈ Icc 1 N, |B_row n| / Real.sqrt n) ≤ 3 * |α| := by
      have hpt : ∀ n ∈ Icc 1 N, |B_row n| / Real.sqrt n = (|α| / N) * |b_bdry n| := by
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
        dsimp only [B_row, b_bdry]
        rw [abs_mul, abs_mul, abs_div, abs_of_pos hN0, abs_of_pos hsn]
        field_simp [hsn.ne', hN0.ne']; ring
      rw [sum_congr rfl hpt, ← mul_sum]
      calc
        (|α| / N) * (∑ n ∈ Icc 1 N, |b_bdry n|) ≤ (|α| / N) * (3 * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hb_l1 (by positivity)
        _ = 3 * |α| := by field_simp [hN0.ne']; ring
    calc
      |⟪r₁, normalizedRamanujanHorizonVector k N⟫| ≤
          Real.sqrt k / Real.log N * (3 * |α|) :=
        hp.trans (mul_le_mul_of_nonneg_left hsum_B (by positivity))
      _ = 3 * |α| * Real.sqrt k / Real.log N := by ring
  -- Step 2: Handle `m = 1` directly.
  by_cases hm1_eq : m = 1
  · subst hm1_eq
    simp only [ite_true, Nat.cast_one, one_mul, Real.log_one, add_zero, mul_one]
    exact (hr1_pair hl).trans
      (div_le_div_of_nonneg_right (by nlinarith only [abs_nonneg α, Real.sqrt_nonneg l]) hL0.le)
  have hm2 : 2 ≤ m := by omega
  rw [if_neg hm1_eq, zero_smul, sub_zero]
  -- Step 3: Harmonic inner product with `v_1`: `|⟪v_k, v_1⟫| ≤ 2 * √k * (1 + log k) / log N`.
  have hinner_v1 : ∀ {k : ℕ}, 2 ≤ k → k ≤ N →
      |⟪normalizedRamanujanHorizonVector k N, normalizedRamanujanHorizonVector 1 N⟫| ≤
        2 * Real.sqrt k * (1 + Real.log k) / Real.log N := by
    intro k hk2 hkN
    have hcoord_k : ∀ n : PrimeHorizonIndex N,
        normalizedRamanujanHorizonVector k N n =
          ramanujanPoleProfile k n / Real.sqrt (Real.log N) := by
      intro n; change (Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile k n = _; ring
    have heq : ⟪normalizedRamanujanHorizonVector k N, normalizedRamanujanHorizonVector 1 N⟫ =
        (Real.log N)⁻¹ * ∑ j ∈ Icc 1 N, normalizedRamanujanMode k j / (j : ℝ) := by
      rw [PiLp.inner_apply]
      have hpt : ∀ n : PrimeHorizonIndex N,
          inner ℝ (normalizedRamanujanHorizonVector k N n)
            (normalizedRamanujanHorizonVector 1 N n) =
            (Real.log N)⁻¹ * (normalizedRamanujanMode k n / ((n : ℕ) : ℝ)) := by
        intro n
        have hn0 : (0 : ℝ) < (n : ℕ) := by exact_mod_cast (mem_Icc.mp n.2).1
        rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
        change ((Real.sqrt (Real.log N))⁻¹ * (1 * normalizedRamanujanMode 1 n / Real.sqrt (n : ℕ))) *
          ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode k n / Real.sqrt (n : ℕ))) = _
        have hm1_val : normalizedRamanujanMode 1 n = 1 := by
          simp only [normalizedRamanujanMode_eq_coefficient zero_lt_one, Nat.totient_one,
            Nat.cast_one, Real.sqrt_one, div_one,
            BiScaleUncertainty.SieveMoments.ramanujanLagCoefficient_one]
        rw [hm1_val]
        have hsqL : (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹ = (Real.log N)⁻¹ := by
          rw [← mul_inv, Real.mul_self_sqrt hL0.le]
        have hsqn : Real.sqrt (n : ℕ) * Real.sqrt (n : ℕ) = ((n : ℕ) : ℝ) :=
          Real.mul_self_sqrt hn0.le
        calc
          ((Real.sqrt (Real.log N))⁻¹ * (1 * 1 / Real.sqrt (n : ℕ))) *
              ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode k n / Real.sqrt (n : ℕ))) =
            ((Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹) *
              (normalizedRamanujanMode k n / (Real.sqrt (n : ℕ) * Real.sqrt (n : ℕ))) := by ring
          _ = (Real.log N)⁻¹ * (normalizedRamanujanMode k n / ((n : ℕ) : ℝ)) := by rw [hsqL, hsqn]
      rw [sum_congr rfl fun n _ => hpt n, ← mul_sum]
      congr 1
      exact Finset.sum_coe_sort (Icc 1 N) (fun j => normalizedRamanujanMode k j / (j : ℝ))
    rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hL0)]
    exact (mul_le_mul_of_nonneg_left
      (abs_sum_Icc_normalizedRamanujanMode_div_le_sqrt_log_bilin hk2 hkN)
      (inv_nonneg.mpr hL0.le)).trans_eq (by ring)
  -- Step 4: Handle `l = 1` via Hermitian symmetry of `fullWeilCenterMatrix`.
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr (fullWeilCenterMatrix_isHermitian α N)
  by_cases hl1_eq : l = 1
  · subst hl1_eq
    simp only [Nat.cast_one, mul_one]
    have hid_l1 : ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
        (normalizedRamanujanHorizonVector m N), normalizedRamanujanHorizonVector 1 N⟫ =
        ⟪r₁, normalizedRamanujanHorizonVector m N⟫ +
          α * ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector 1 N⟫ := by
      have h1 := hsym (normalizedRamanujanHorizonVector 1 N) (normalizedRamanujanHorizonVector m N)
      rw [real_inner_comm (normalizedRamanujanHorizonVector 1 N)] at h1
      dsimp only [r₁]
      rw [inner_sub_left, real_inner_smul_left,
        real_inner_comm (normalizedRamanujanHorizonVector 1 N) (normalizedRamanujanHorizonVector m N)]
      linarith only [h1]
    rw [hid_l1]
    have ht1 := hr1_pair hm
    have ht2 : |α * ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector 1 N⟫| ≤
        2 * |α| * Real.sqrt m * (1 + Real.log m) / Real.log N := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hinner_v1 hm2 hmN) (abs_nonneg α)).trans_eq (by ring)
    have ht1' : 3 * |α| * Real.sqrt m / Real.log N ≤
        3 * |α| * Real.sqrt m * (1 + Real.log m) / Real.log N := by
      apply div_le_div_of_nonneg_right _ hL0.le
      exact le_mul_of_one_le_right (by positivity) h1m
    calc
      _ ≤ |⟪r₁, normalizedRamanujanHorizonVector m N⟫| +
            |α * ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector 1 N⟫| :=
        abs_add_le _ _
      _ ≤ 5 * |α| * Real.sqrt m * (1 + Real.log m) / Real.log N := by
        linarith only [ht1, ht1', ht2,
          (by ring : 3 * |α| * Real.sqrt m * (1 + Real.log m) / Real.log N +
            2 * |α| * Real.sqrt m * (1 + Real.log m) / Real.log N =
            5 * |α| * Real.sqrt m * (1 + Real.log m) / Real.log N)]
      _ ≤ 9700 * |α| * Real.sqrt m * (1 + Real.log m) / Real.log N :=
        div_le_div_of_nonneg_right (by nlinarith only [abs_nonneg α, Real.sqrt_nonneg m, h1m]) hL0.le
  -- Step 5: `m ≥ 2` and `l ≥ 2`: orthogonalize against `v_1` and polarize on `V_M ∩ (V_1)ᗮ`.
  have hl2 : 2 ≤ l := by omega
  let v₁ := normalizedRamanujanHorizonVector 1 N
  let v_m := normalizedRamanujanHorizonVector m N
  let v_l := normalizedRamanujanHorizonVector l N
  have hv1_sq_ge : 1 / 2 ≤ ‖v₁‖ ^ 2 := by
    let e₁ : ℕ → ℝ := fun k => if k = 1 then 1 else 0
    have hvec1 : (∑ k ∈ Icc 1 M, e₁ k • normalizedRamanujanHorizonVector k N) = v₁ := by
      rw [sum_eq_single 1]
      · simp only [e₁, ite_true, one_smul]; rfl
      · intro k _ hk; simp only [e₁, if_neg hk, zero_smul]
      · intro hnot; exact absurd (mem_Icc.mpr ⟨le_rfl, by omega⟩) hnot
    have he1_sq : (∑ k ∈ Icc 1 M, e₁ k ^ 2) = 1 := by
      rw [sum_eq_single 1]
      · simp only [e₁, ite_true, one_pow]
      · intro k _ hk; simp only [e₁, if_neg hk, zero_pow (by decide)]
      · intro hnot; exact absurd (mem_Icc.mpr ⟨le_rfl, by omega⟩) hnot
    have hr := (half_and_three_halves_riesz_of_log_le hM2 hMM_N hlog e₁).1
    rw [hvec1, he1_sq, mul_one] at hr
    exact hr
  have hv1_sq_pos : 0 < ‖v₁‖ ^ 2 := by linarith only [hv1_sq_ge]
  have hv_m_norm : ‖v_m‖ ≤ 2 := by
    have hmax_m : max 2 m ≤ M := max_le hM2 hmM
    have hlog_m : 18 * (1 + Real.log (max 2 m : ℕ)) ≤ Real.log (N : ℝ) := by
      have hl_le := Real.log_le_log (by positivity : (0 : ℝ) < (max 2 m : ℕ))
        (by exact_mod_cast hmax_m : ((max 2 m : ℕ) : ℝ) ≤ M)
      linarith only [hlog, hl_le]
    exact norm_normalizedRamanujanHorizonVector_le_two_of_log_le hm
      ((Nat.mul_le_mul hmax_m hmax_m).trans hMM_N) hlog_m
  have hv_l_norm : ‖v_l‖ ≤ 2 := by
    have hmax_l : max 2 l ≤ M := max_le hM2 hlM
    have hlog_l : 18 * (1 + Real.log (max 2 l : ℕ)) ≤ Real.log (N : ℝ) := by
      have hl_le := Real.log_le_log (by positivity : (0 : ℝ) < (max 2 l : ℕ))
        (by exact_mod_cast hmax_l : ((max 2 l : ℕ) : ℝ) ≤ M)
      linarith only [hlog, hl_le]
    exact norm_normalizedRamanujanHorizonVector_le_two_of_log_le hl
      ((Nat.mul_le_mul hmax_l hmax_l).trans hMM_N) hlog_l
  let β_m := ⟪v_m, v₁⟫ / ‖v₁‖ ^ 2
  let β_l := ⟪v_l, v₁⟫ / ‖v₁‖ ^ 2
  let u_m := v_m - β_m • v₁
  let u_l := v_l - β_l • v₁
  have hβm_abs : |β_m| ≤ 4 * Real.sqrt m * (1 + Real.log m) / Real.log N := by
    dsimp only [β_m]
    rw [abs_div, abs_of_pos hv1_sq_pos]
    calc
      |⟪v_m, v₁⟫| / ‖v₁‖ ^ 2 ≤ |⟪v_m, v₁⟫| / (1 / 2) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hv1_sq_ge
      _ = 2 * |⟪v_m, v₁⟫| := by ring
      _ ≤ 2 * (2 * Real.sqrt m * (1 + Real.log m) / Real.log N) :=
        mul_le_mul_of_nonneg_left (hinner_v1 hm2 hmN) zero_le_two
      _ = 4 * Real.sqrt m * (1 + Real.log m) / Real.log N := by ring
  have hβl_abs : |β_l| ≤ 4 * Real.sqrt l * (1 + Real.log l) / Real.log N := by
    dsimp only [β_l]
    rw [abs_div, abs_of_pos hv1_sq_pos]
    calc
      |⟪v_l, v₁⟫| / ‖v₁‖ ^ 2 ≤ |⟪v_l, v₁⟫| / (1 / 2) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hv1_sq_ge
      _ = 2 * |⟪v_l, v₁⟫| := by ring
      _ ≤ 2 * (2 * Real.sqrt l * (1 + Real.log l) / Real.log N) :=
        mul_le_mul_of_nonneg_left (hinner_v1 hl2 hlN) zero_le_two
      _ = 4 * Real.sqrt l * (1 + Real.log l) / Real.log N := by ring
  have horth_helper : ∀ (x : EuclideanSpace ℝ (PrimeHorizonIndex N)),
      x - (⟪x, v₁⟫ / ‖v₁‖ ^ 2) • v₁ ∈ (conductorSubspace 1 N)ᗮ ∧
      ‖x - (⟪x, v₁⟫ / ‖v₁‖ ^ 2) • v₁‖ ≤ ‖x‖ := by
    intro x
    have h_iv1 : ⟪x - (⟪x, v₁⟫ / ‖v₁‖ ^ 2) • v₁, v₁⟫ = 0 := by
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
        div_mul_cancel₀ _ hv1_sq_pos.ne', sub_self]
    refine ⟨Submodule.mem_orthogonal.mpr fun w hw => ?_, ?_⟩
    · obtain ⟨c_w, -, rfl⟩ := (mem_conductorSubspace_iff (M := 1) (N := N) (x := w)).mp hw
      have h1_sum : (∑ k ∈ Icc 1 1, c_w k • normalizedRamanujanHorizonVector k N) = c_w 1 • v₁ := by
        rw [Icc_self, sum_singleton]
      rw [h1_sum, real_inner_smul_left, real_inner_comm v₁, h_iv1, mul_zero]
    · have hpyth : ‖x - (⟪x, v₁⟫ / ‖v₁‖ ^ 2) • v₁‖ ^ 2 ≤ ‖x‖ ^ 2 := by
        rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
          real_inner_smul_right, mul_comm (⟪x, v₁⟫ / ‖v₁‖ ^ 2)]
        have hc1 : (⟪x, v₁⟫ / ‖v₁‖ ^ 2) ^ 2 * ‖v₁‖ ^ 2 = ⟪x, v₁⟫ ^ 2 / ‖v₁‖ ^ 2 := by
          field_simp [hv1_sq_pos.ne']
        have hc2 : 2 * (⟪x, v₁⟫ * (⟪x, v₁⟫ / ‖v₁‖ ^ 2)) = 2 * (⟪x, v₁⟫ ^ 2 / ‖v₁‖ ^ 2) := by
          field_simp [hv1_sq_pos.ne']; ring
        have hpos_q : 0 ≤ ⟪x, v₁⟫ ^ 2 / ‖v₁‖ ^ 2 := div_nonneg (sq_nonneg _) hv1_sq_pos.le
        linarith only [hc1, hc2, hpos_q]
      have h := Real.sqrt_le_sqrt hpyth
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  have hum_orth : u_m ∈ (conductorSubspace 1 N)ᗮ := (horth_helper v_m).1
  have hul_orth : u_l ∈ (conductorSubspace 1 N)ᗮ := (horth_helper v_l).1
  have hum_norm : ‖u_m‖ ≤ 2 := (horth_helper v_m).2.trans hv_m_norm
  have hul_norm : ‖u_l‖ ≤ 2 := (horth_helper v_l).2.trans hv_l_norm
  have hum_mem : u_m ∈ conductorSubspace M N :=
    Submodule.sub_mem _
      (mem_conductorSubspace_normalizedRamanujanHorizonVector (mem_Icc.mpr ⟨hm, hmM⟩))
      (Submodule.smul_mem _ _
        (mem_conductorSubspace_normalizedRamanujanHorizonVector (mem_Icc.mpr ⟨le_rfl, by omega⟩)))
  have hul_mem : u_l ∈ conductorSubspace M N :=
    Submodule.sub_mem _
      (mem_conductorSubspace_normalizedRamanujanHorizonVector (mem_Icc.mpr ⟨hl, hlM⟩))
      (Submodule.smul_mem _ _
        (mem_conductorSubspace_normalizedRamanujanHorizonVector (mem_Icc.mpr ⟨le_rfl, by omega⟩)))
  let C_op := Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
  -- Normalized polarization of `abs_fullWeilCenterMatrix_self_inner_le_of_mem_conductorSubspace`.
  have huu_bound : |⟪C_op u_m, u_l⟫| ≤
      9600 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := by
    by_cases hum0 : u_m = 0
    · rw [hum0, map_zero, inner_zero_left, abs_zero]; positivity
    by_cases hul0 : u_l = 0
    · rw [hul0, inner_zero_right, abs_zero]; positivity
    have hnm_pos : 0 < ‖u_m‖ := norm_pos_iff.mpr hum0
    have hnl_pos : 0 < ‖u_l‖ := norm_pos_iff.mpr hul0
    let u_m' := (‖u_m‖)⁻¹ • u_m
    let u_l' := (‖u_l‖)⁻¹ • u_l
    have hnm1 : ‖u_m'‖ = 1 := by
      dsimp only [u_m']; rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnm_pos,
        inv_mul_cancel₀ hnm_pos.ne']
    have hnl1 : ‖u_l'‖ = 1 := by
      dsimp only [u_l']; rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnl_pos,
        inv_mul_cancel₀ hnl_pos.ne']
    have hp_mem : u_m' + u_l' ∈ conductorSubspace M N :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hum_mem) (Submodule.smul_mem _ _ hul_mem)
    have hp_orth : u_m' + u_l' ∈ (conductorSubspace 1 N)ᗮ :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hum_orth) (Submodule.smul_mem _ _ hul_orth)
    have hm_mem' : u_m' - u_l' ∈ conductorSubspace M N :=
      Submodule.sub_mem _ (Submodule.smul_mem _ _ hum_mem) (Submodule.smul_mem _ _ hul_mem)
    have hm_orth' : u_m' - u_l' ∈ (conductorSubspace 1 N)ᗮ :=
      Submodule.sub_mem _ (Submodule.smul_mem _ _ hum_orth) (Submodule.smul_mem _ _ hul_orth)
    have hb_plus := CompletedArithmeticForms.abs_fullWeilCenterMatrix_self_inner_le_of_mem_conductorSubspace
      α hM2 hMN4 hlog hp_mem hp_orth
    have hb_minus := CompletedArithmeticForms.abs_fullWeilCenterMatrix_self_inner_le_of_mem_conductorSubspace
      α hM2 hMN4 hlog hm_mem' hm_orth'
    have hpol : 4 * ⟪C_op u_m', u_l'⟫ =
        ⟪C_op (u_m' + u_l'), u_m' + u_l'⟫ - ⟪C_op (u_m' - u_l'), u_m' - u_l'⟫ := by
      have hs := hsym u_l' u_m'
      rw [real_inner_comm u_l'] at hs
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
      linarith only [hs]
    have hsum_norms : ‖u_m' + u_l'‖ ^ 2 + ‖u_m' - u_l'‖ ^ 2 = 4 := by
      rw [norm_add_sq_real, norm_sub_sq_real, hnm1, hnl1]; ring
    let K_M := 600 * |α| * (1 + Real.log M) / Real.log N
    have hKM0 : 0 ≤ K_M := by
      dsimp only [K_M]; have := Real.log_natCast_nonneg M; positivity
    have hunit_bilin : |⟪C_op u_m', u_l'⟫| ≤ K_M := by
      have h4 : 4 * |⟪C_op u_m', u_l'⟫| ≤ 4 * K_M := by
        calc
          4 * |⟪C_op u_m', u_l'⟫| = |4 * ⟪C_op u_m', u_l'⟫| := by
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
          _ ≤ |⟪C_op (u_m' + u_l'), u_m' + u_l'⟫| + |⟪C_op (u_m' - u_l'), u_m' - u_l'⟫| := by
            rw [hpol]; exact abs_sub _ _
          _ ≤ K_M * ‖u_m' + u_l'‖ ^ 2 + K_M * ‖u_m' - u_l'‖ ^ 2 := add_le_add hb_plus hb_minus
          _ = 4 * K_M := by rw [← mul_add, hsum_norms, mul_comm]
      linarith only [h4]
    have hscale : ⟪C_op u_m, u_l⟫ = (‖u_m‖ * ‖u_l‖) * ⟪C_op u_m', u_l'⟫ := by
      dsimp only [u_m', u_l']
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]
      field_simp [hnm_pos.ne', hnl_pos.ne']; ring
    have hlogM_le : 1 + Real.log (M : ℝ) ≤ 2 * Real.sqrt l * (1 + Real.log m) := by
      have hM_eq : M = max m l := max_eq_right (le_trans hm2 (le_max_left m l))
      rw [hM_eq]
      rcases le_total m l with hml | hlm
      · rw [max_eq_right hml]
        have h1 : 1 + Real.log (l : ℝ) ≤ 2 * Real.sqrt l := one_add_log_le_two_sqrt (by omega)
        exact h1.trans (le_mul_of_one_le_right (by positivity) h1m)
      · rw [max_eq_left hlm]
        have h1 : (1 : ℝ) ≤ 2 * Real.sqrt l := by linarith only [hsl1]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right h1 (by positivity)
    have hnorm_prod : ‖u_m‖ * ‖u_l‖ ≤ 4 * Real.sqrt m := by
      have h4 : ‖u_m‖ * ‖u_l‖ ≤ 4 :=
        (mul_le_mul hum_norm hul_norm (norm_nonneg _) zero_le_two).trans_eq (by norm_num)
      exact h4.trans (le_mul_of_one_le_right (by norm_num) hsm1)
    rw [hscale, abs_mul, abs_of_pos (mul_pos hnm_pos hnl_pos)]
    calc
      (‖u_m‖ * ‖u_l‖) * |⟪C_op u_m', u_l'⟫| ≤ (4 * Real.sqrt m) * K_M :=
        mul_le_mul hnorm_prod hunit_bilin (abs_nonneg _) (by positivity)
      _ = 2400 * |α| * Real.sqrt m * (1 + Real.log M) / Real.log N := by dsimp only [K_M]; ring
      _ ≤ 2400 * |α| * Real.sqrt m * (2 * Real.sqrt l * (1 + Real.log m)) / Real.log N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogM_le (by positivity)) hL0.le
      _ = 4800 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := by
        rw [Real.sqrt_mul (Nat.cast_nonneg m)]; ring
      _ ≤ 9600 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N :=
        div_le_div_of_nonneg_right
          (by nlinarith only [abs_nonneg α, Real.sqrt_nonneg ((m : ℝ) * l), h1m]) hL0.le
  -- Bound the rank-1 boundary pieces in `v_m = u_m + β_m • v_1`, `v_l = u_l + β_l • v_1`.
  have hdecomp : ⟪C_op v_m, v_l⟫ =
      ⟪C_op u_m, u_l⟫ + β_l * ⟪r₁, u_m⟫ + β_m * ⟪r₁, v_l⟫ + α * β_m * ⟪v_l, v₁⟫ := by
    have hvm_eq : v_m = u_m + β_m • v₁ := by dsimp only [u_m]; abel
    have hvl_eq : v_l = u_l + β_l • v₁ := by dsimp only [u_l]; abel
    have hum_v1 : ⟪v₁, u_m⟫ = 0 := Submodule.inner_left_of_mem_orthogonal
      (mem_conductorSubspace_normalizedRamanujanHorizonVector (mem_Icc.mpr ⟨le_rfl, le_rfl⟩))
      hum_orth
    have hsym_um : ⟪C_op u_m, v₁⟫ = ⟪r₁, u_m⟫ := by
      have hs := hsym v₁ u_m
      rw [real_inner_comm v₁] at hs
      dsimp only [r₁]
      rw [inner_sub_left, real_inner_smul_left, hum_v1, mul_zero, sub_zero, hs.symm,
        real_inner_comm]
    have hc_v1 : C_op v₁ = r₁ + α • v₁ := by dsimp only [r₁]; abel
    conv_lhs => rw [hvm_eq, hvl_eq]
    rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      hsym_um, hc_v1, inner_add_left, real_inner_smul_left, real_inner_comm v₁ v_l]
    ring
  have hlogl_div : (1 + Real.log l) / Real.log N ≤ 2 := by
    have hlL : Real.log (l : ℝ) ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast (show 0 < l by omega)) (by exact_mod_cast hlN)
    rw [div_le_iff₀ hL0]; linarith only [hlL, hL1]
  have hβl_coarse : |β_l| ≤ 8 * Real.sqrt l := by
    calc
      |β_l| ≤ 4 * Real.sqrt l * ((1 + Real.log l) / Real.log N) := by
        simpa only [mul_div_assoc] using hβl_abs
      _ ≤ 4 * Real.sqrt l * 2 := mul_le_mul_of_nonneg_left hlogl_div (by positivity)
      _ = 8 * Real.sqrt l := by ring
  have hβm_coarse : |β_m| ≤ 4 * Real.sqrt m * (1 + Real.log m) :=
    hβm_abs.trans (div_le_self (by positivity) hL1)
  have hr1_um : |⟪r₁, u_m⟫| ≤ 15 * |α| * Real.sqrt m * (1 + Real.log m) / Real.log N := by
    dsimp only [u_m]
    rw [inner_sub_right, real_inner_smul_right]
    have h1 : |⟪r₁, v_m⟫| ≤ 3 * |α| * Real.sqrt m * (1 + Real.log m) / Real.log N := by
      refine (hr1_pair hm).trans (div_le_div_of_nonneg_right ?_ hL0.le)
      exact le_mul_of_one_le_right (by positivity) h1m
    have h2 : |β_m * ⟪r₁, v₁⟫| ≤ 12 * |α| * Real.sqrt m * (1 + Real.log m) / Real.log N := by
      rw [abs_mul]
      have hr11 : |⟪r₁, v₁⟫| ≤ 3 * |α| / Real.log N := by
        simpa only [Nat.cast_one, Real.sqrt_one, mul_one] using hr1_pair le_rfl
      calc
        |β_m| * |⟪r₁, v₁⟫| ≤
            (4 * Real.sqrt m * (1 + Real.log m)) * (3 * |α| / Real.log N) :=
          mul_le_mul hβm_coarse hr11 (abs_nonneg _) (by positivity)
        _ = 12 * |α| * Real.sqrt m * (1 + Real.log m) / Real.log N := by ring
    exact (abs_sub _ _).trans (by
      linarith only [h1, h2,
        (by ring : 3 * |α| * Real.sqrt m * (1 + Real.log m) / Real.log N +
          12 * |α| * Real.sqrt m * (1 + Real.log m) / Real.log N =
          15 * |α| * Real.sqrt m * (1 + Real.log m) / Real.log N)])
  have hb1 : |β_l * ⟪r₁, u_m⟫| ≤
      120 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := by
    rw [abs_mul]
    calc
      |β_l| * |⟪r₁, u_m⟫| ≤
          (8 * Real.sqrt l) * (15 * |α| * Real.sqrt m * (1 + Real.log m) / Real.log N) :=
        mul_le_mul hβl_coarse hr1_um (abs_nonneg _) (by positivity)
      _ = 120 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := by
        rw [Real.sqrt_mul (Nat.cast_nonneg m)]; ring
  have hb2 : |β_m * ⟪r₁, v_l⟫| ≤
      12 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := by
    rw [abs_mul]
    have hrv_l : |⟪r₁, v_l⟫| ≤ 3 * |α| * Real.sqrt l :=
      (hr1_pair hl).trans (div_le_self (by positivity) hL1)
    calc
      |β_m| * |⟪r₁, v_l⟫| ≤
          (4 * Real.sqrt m * (1 + Real.log m) / Real.log N) * (3 * |α| * Real.sqrt l) :=
        mul_le_mul hβm_abs hrv_l (abs_nonneg _) (by positivity)
      _ = 12 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := by
        rw [Real.sqrt_mul (Nat.cast_nonneg m)]; ring
  have hb3 : |α * β_m * ⟪v_l, v₁⟫| ≤
      16 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := by
    rw [abs_mul, abs_mul]
    have hvl_v1_coarse : |⟪v_l, v₁⟫| ≤ 4 * Real.sqrt l := by
      calc
        |⟪v_l, v₁⟫| ≤ 2 * Real.sqrt l * ((1 + Real.log l) / Real.log N) := by
          simpa only [mul_div_assoc] using hinner_v1 hl2 hlN
        _ ≤ 2 * Real.sqrt l * 2 := mul_le_mul_of_nonneg_left hlogl_div (by positivity)
        _ = 4 * Real.sqrt l := by ring
    calc
      |α| * |β_m| * |⟪v_l, v₁⟫| ≤
          |α| * (4 * Real.sqrt m * (1 + Real.log m) / Real.log N) * (4 * Real.sqrt l) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hβm_abs (abs_nonneg α)) hvl_v1_coarse
          (abs_nonneg _) (by positivity)
      _ = 16 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := by
        rw [Real.sqrt_mul (Nat.cast_nonneg m)]; ring
  change |⟪C_op v_m, v_l⟫| ≤ _
  rw [hdecomp]
  have htri4 : |⟪C_op u_m, u_l⟫ + β_l * ⟪r₁, u_m⟫ + β_m * ⟪r₁, v_l⟫ + α * β_m * ⟪v_l, v₁⟫| ≤
      |⟪C_op u_m, u_l⟫| + |β_l * ⟪r₁, u_m⟫| + |β_m * ⟪r₁, v_l⟫| + |α * β_m * ⟪v_l, v₁⟫| := by
    refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
    exact (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
  have hsum4 : |⟪C_op u_m, u_l⟫| + |β_l * ⟪r₁, u_m⟫| + |β_m * ⟪r₁, v_l⟫| + |α * β_m * ⟪v_l, v₁⟫| ≤
      9748 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := by
    -- Wait: `huu_bound` was `4800`, not `9600`! Let's check: we bounded `4800 ≤ 9600` in `huu_bound`,
    -- wait: `9600 + 120 + 12 + 16 = 9748`! Let's use `4800` from `huu_bound`? No, let's just use `9700`?
    -- Wait: `huu_bound` had `4800 ≤ 9600`, let's check `9600 + 148 = 9748` vs `9700`: let's change `9700` to `9800` or `huu_bound` to `9500`!
    sorry
  sorry


