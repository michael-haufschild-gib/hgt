import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.QuadraticOverlapConductorResiduals
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilMatrixIsPositiveAtPowerOfLogOverlap
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandQuadraticCenterBounds
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandOverlapAndNonRatioBounds
import GaloisForLFunctions.CompletedArithmeticForms.PrimePacketCoercivity
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
    rw [Real.log_sqrt hm0.le]; ring
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
    · intro k _ hkm; simp only [a, if_neg hkm]; norm_num
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
        (Real.log (0 : ℕ) - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m 0 = 0 := by
      ext ⟨n, hn⟩
      simp [PrimeHorizonIndex] at hn
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
      calc
        Real.exp (-c_M * Real.sqrt (Real.log y)) * (1 + Real.log y) ^ 2 ≤
            2 * Real.exp (-c_M * Real.sqrt (Real.log y)) +
              2 * ((Real.log y) ^ 2 * Real.exp (-c_M * Real.sqrt (Real.log y))) := by
          linarith only [hprod,
            (by ring : Real.exp (-c_M * Real.sqrt (Real.log y)) * (2 + 2 * (Real.log y) ^ 2) =
              2 * Real.exp (-c_M * Real.sqrt (Real.log y)) +
                2 * ((Real.log y) ^ 2 * Real.exp (-c_M * Real.sqrt (Real.log y))))]
        _ ≤ 2 * 1 + 2 * (24 / c_M ^ 4) := add_le_add
          (mul_le_mul_of_nonneg_left he_le1 zero_le_two)
          (mul_le_mul_of_nonneg_left hL2 zero_le_two)
        _ = 2 + 48 / c_M ^ 4 := by ring
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
        rw [← div_eq_mul_inv, div_le_div_iff₀ hlog_pos hkpos, one_mul]
        linarith only [hker_cmp n hn]
      have hprof_le : SignedArithmeticHodgeTheory.primeMertensRemainderProfile (N / n) ≤
          2 * C_env * (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / N)) ^ 2)⁻¹ := by
        calc
          _ ≤ C_env / (1 + Real.log ((N / n : ℕ) : ℝ)) ^ 2 := henv (N / n) hy
          _ = C_env * (1 / (1 + Real.log ((N / n : ℕ) : ℝ)) ^ 2) := div_eq_mul_one_div _ _
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
        rw [ramanujanPoleProfile, normalizedRamanujanMode, ramanujanMode_one,
          Nat.totient_one, Nat.cast_one, Real.sqrt_one, div_one]
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
      rw [horizonKernelMatrix_apply_profile, hmode1 n]
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
          ring
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
        field_simp [hsn.ne', hN0.ne']
      rw [sum_congr rfl hpt, ← mul_sum]
      calc
        (|α| / N) * (∑ n ∈ Icc 1 N, |b_bdry n|) ≤ (|α| / N) * (3 * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hb_l1 (by positivity)
        _ = 3 * |α| := by field_simp [hN0.ne']
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
        have hv1 : normalizedRamanujanHorizonVector 1 N n =
            (Real.sqrt (Real.log N))⁻¹ * (1 / Real.sqrt (n : ℕ)) := by
          change (Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile 1 n = _
          rw [ramanujanPoleProfile, normalizedRamanujanMode, ramanujanMode_one,
            Nat.totient_one, Nat.cast_one, Real.sqrt_one, div_one]
        have hvk : normalizedRamanujanHorizonVector k N n =
            (Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode k n / Real.sqrt (n : ℕ)) := rfl
        rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real, hv1, hvk]
        have hsqL : (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹ = (Real.log N)⁻¹ := by
          rw [← mul_inv, Real.mul_self_sqrt hL0.le]
        have hsqn : Real.sqrt (n : ℕ) * Real.sqrt (n : ℕ) = ((n : ℕ) : ℝ) :=
          Real.mul_self_sqrt hn0.le
        calc
          _ = ((Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹) *
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
      have h1 : ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
          (normalizedRamanujanHorizonVector m N), normalizedRamanujanHorizonVector 1 N⟫ =
          ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N)
            (normalizedRamanujanHorizonVector 1 N), normalizedRamanujanHorizonVector m N⟫ := by
        rw [hsym (normalizedRamanujanHorizonVector m N) (normalizedRamanujanHorizonVector 1 N),
          real_inner_comm]
      dsimp only [r₁]
      rw [inner_sub_left, real_inner_smul_left,
        real_inner_comm (normalizedRamanujanHorizonVector m N) (normalizedRamanujanHorizonVector 1 N)]
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
        div_le_div_of_nonneg_right (by
          have hnn : 0 ≤ |α| * Real.sqrt m * (1 + Real.log m) := by positivity
          linarith only [hnn]) hL0.le
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
      · intro k _ hk; simp only [e₁, if_neg hk]; norm_num
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
    refine ⟨(Submodule.mem_orthogonal _ _).mpr fun w hw => ?_, ?_⟩
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
      4800 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := by
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
      have hs : ⟪C_op u_l', u_m'⟫ = ⟪C_op u_m', u_l'⟫ := by
        rw [hsym u_l' u_m', real_inner_comm]
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
      field_simp [hnm_pos.ne', hnl_pos.ne']
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
  -- Bound the rank-1 boundary pieces in `v_m = u_m + β_m • v_1`, `v_l = u_l + β_l • v_1`.
  have hdecomp : ⟪C_op v_m, v_l⟫ =
      ⟪C_op u_m, u_l⟫ + β_l * ⟪r₁, u_m⟫ + β_m * ⟪r₁, v_l⟫ + α * β_m * ⟪v_l, v₁⟫ := by
    have hvm_eq : v_m = u_m + β_m • v₁ := by dsimp only [u_m]; abel
    have hvl_eq : v_l = u_l + β_l • v₁ := by dsimp only [u_l]; abel
    have hum_v1 : ⟪v₁, u_m⟫ = 0 := (Submodule.mem_orthogonal _ _).mp hum_orth v₁
      (mem_conductorSubspace_normalizedRamanujanHorizonVector (mem_Icc.mpr ⟨le_rfl, le_rfl⟩))
    have hsym_um : ⟪C_op u_m, v₁⟫ = ⟪r₁, u_m⟫ := by
      have hs : ⟪C_op u_m, v₁⟫ = ⟪C_op v₁, u_m⟫ := by
        rw [hsym u_m v₁, real_inner_comm]
      dsimp only [r₁]
      rw [inner_sub_left, real_inner_smul_left, hum_v1, mul_zero, sub_zero, hs]
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
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hsum4 : |⟪C_op u_m, u_l⟫| + |β_l * ⟪r₁, u_m⟫| + |β_m * ⟪r₁, v_l⟫| + |α * β_m * ⟪v_l, v₁⟫| ≤
      4948 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N := by
    linarith only [huu_bound, hb1, hb2, hb3,
      (by ring : 4800 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N +
        120 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N +
        12 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N +
        16 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N =
        4948 * |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N)]
  exact (htri4.trans hsum4).trans
    (div_le_div_of_nonneg_right
      (by
        have hnn : 0 ≤ |α| * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) := by positivity
        linarith only [hnn]) hL0.le)

/-- **Channel 4 (Separated cross error):** Pairing the pointwise `O(√m * c * √n / N + √m * c^2 / N)`
row envelope with `v_l` yields `O(√(m l) * c / log N)` whenever `c^2 ≤ N`. -/
private theorem exists_crossError_bilinear_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l : ℕ, 0 < m → 0 < l → ∀ c : ℝ, 1 ≤ c →
      ∀ N : ℕ, 1 ≤ N → c ^ 2 ≤ (N : ℝ) →
        |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
            (normalizedRamanujanHorizonVector m N),
          normalizedRamanujanHorizonVector l N⟫| ≤
          C * Real.sqrt ((m : ℝ) * l) * c / Real.log N := by
  let K₀ := 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)
  have hK₀0 : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  refine ⟨40 * K₀ + 1, by positivity, ?_⟩
  intro m l hm hl c hc N hN hc2N
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let E_ker : ℕ → ℕ → ℝ := fun n j =>
    if 2 * (c / N) < |Real.log j - Real.log n| then
      atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0
  let row_x : ℕ → ℝ := fun n =>
    ∑ j ∈ Icc 1 N, E_ker n j * (normalizedRamanujanMode m j / Real.sqrt j)
  have hcoord : ∀ n : PrimeHorizonIndex N,
      (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N)) n =
        row_x n / Real.sqrt (Real.log N) := by
    intro n
    rw [normalizedRamanujanHorizonVector, map_smul]
    change (Real.sqrt (Real.log N))⁻¹ *
      ((Matrix.toEuclideanLin (horizonKernelMatrix E_ker N)
        (horizonProfileVector (ramanujanPoleProfile m) N)) n) = _
    rw [horizonKernelMatrix_apply_profile, div_eq_inv_mul]
    rfl
  have hrow_abs : ∀ n ∈ Icc 1 N,
      |row_x n| ≤
        32 * K₀ * Real.sqrt m * c * Real.sqrt n / N + 4 * K₀ * Real.sqrt m * c ^ 2 / N := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    let d : ℕ := max 1 ⌈c * (n : ℝ) / N⌉₊
    have hd1 : 1 ≤ d := le_max_left _ _
    have hcd : c * (n : ℝ) / N ≤ (d : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈c * (n : ℝ) / N⌉₊))
    have hinv_d : 1 / (d : ℝ) ≤ (N : ℝ) / (c * n) := by
      have hpos : 0 < c * (n : ℝ) / N := div_pos (mul_pos hc0 hn0) hN0
      exact (one_div_le_one_div_of_le hpos hcd).trans_eq (one_div_div _ _)
    let S_mod := (Icc 1 N).filter (fun j : ℕ => 2 * (c / N) < |Real.log (j : ℝ) - Real.log n| ∧
      (n ≤ 2 * j ∧ j ≤ 2 * n))
    have hterm_pt : ∀ j ∈ Icc 1 N,
        |E_ker n j * (normalizedRamanujanMode m j / Real.sqrt j)| ≤
          K₀ * (c / N) ^ 2 * Real.sqrt m *
            ((if j ∈ S_mod then 8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 else 0) + 4) := by
      intro j hj
      have hj1 := (mem_Icc.mp hj).1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj0
      have hsj1 : 1 ≤ Real.sqrt (j : ℝ) := by
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by exact_mod_cast hj1 : (1 : ℝ) ≤ j)
      by_cases hgap : 2 * (c / N) < |Real.log j - Real.log n|
      · have hne : n ≠ j := by
          intro heq; subst heq; simp only [sub_self, abs_zero] at hgap
          linarith only [hgap, div_pos hc0 hN0]
        have hd_pos : 0 < |(n : ℝ) - j| :=
          abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne))
        have hd2 : 0 < |(n : ℝ) - j| ^ 2 := sq_pos_of_pos hd_pos
        have hm0 : 0 ≤ max (n : ℝ) j := hn0.le.trans (le_max_left _ _)
        have hentry := abs_separatedCrossError_le hφ hsupp hM hc0 hN hn hj
        change |E_ker n j| ≤ K₀ * (c / N) ^ 2 * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 at hentry
        have ha : |normalizedRamanujanMode m j / Real.sqrt j| ≤ Real.sqrt m / Real.sqrt j := by
          rw [abs_div, abs_of_pos hsj]
          exact div_le_div_of_nonneg_right (abs_mode_le_sqrt_conductor_bilin hm j) hsj.le
        have hprod := mul_le_mul hentry ha (abs_nonneg _) (by positivity)
        rw [← abs_mul] at hprod
        have hrew : K₀ * (c / N) ^ 2 * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 *
            (Real.sqrt m / Real.sqrt j) =
            K₀ * (c / N) ^ 2 * Real.sqrt m *
              ((max (n : ℝ) j) ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2)) := by ring
        rw [hrew] at hprod
        refine hprod.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        by_cases hnear : n ≤ 2 * j ∧ j ≤ 2 * n
        · rw [if_pos (mem_filter.mpr ⟨hj, hgap, hnear⟩)]
          have hnjR : (n : ℝ) ≤ 2 * j := by exact_mod_cast hnear.1
          have hjnR : (j : ℝ) ≤ 2 * n := by exact_mod_cast hnear.2
          have hs_cmp : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (j : ℝ) := by
            by_contra h
            have hlt : 2 * Real.sqrt (j : ℝ) < Real.sqrt (n : ℝ) := lt_of_not_ge h
            have hp := mul_pos (sub_pos.mpr hlt) (by positivity :
              0 < Real.sqrt (n : ℝ) + 2 * Real.sqrt (j : ℝ))
            nlinarith only [hp, Real.sq_sqrt hn0.le, Real.sq_sqrt hj0.le, hnjR, hj0]
          have hm_le : max (n : ℝ) j ≤ 2 * n := max_le (by linarith only [hn0]) hjnR
          have hm2 : (max (n : ℝ) j) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
            have hsq := mul_self_le_mul_self hm0 hm_le
            nlinarith only [hsq]
          have hnum : (max (n : ℝ) j) ^ 2 ≤ 8 * (n : ℝ) * Real.sqrt n * Real.sqrt j := by
            calc
              _ ≤ 4 * (n : ℝ) ^ 2 := hm2
              _ = (4 * (n : ℝ) * Real.sqrt n) * Real.sqrt n := by
                rw [mul_assoc (4 * (n : ℝ)), ← pow_two, Real.sq_sqrt hn0.le]; ring
              _ ≤ (4 * (n : ℝ) * Real.sqrt n) * (2 * Real.sqrt j) :=
                mul_le_mul_of_nonneg_left hs_cmp (by positivity)
              _ = _ := by ring
          have ht : (max (n : ℝ) j) ^ 2 / (Real.sqrt j * |(n : ℝ) - j| ^ 2) ≤
              8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 := by
            rw [div_le_div_iff₀ (mul_pos hsj hd2) hd2]
            nlinarith only [mul_nonneg (sub_nonneg.mpr hnum) hd2.le]
          linarith only [ht]
        · rw [if_neg (fun h => hnear (mem_filter.mp h).2.2), zero_add]
          have hm_far : max (n : ℝ) j ≤ 2 * |(n : ℝ) - j| := by
            rcases not_and_or.mp hnear with h | h
            · have hnR' : 2 * (j : ℝ) < n := by exact_mod_cast (lt_of_not_ge h)
              rw [max_eq_left (by linarith only [hnR', hj0]),
                abs_of_pos (by linarith only [hnR', hj0])]
              linarith only [hnR']
            · have hjR' : 2 * (n : ℝ) < j := by exact_mod_cast (lt_of_not_ge h)
              rw [max_eq_right (by linarith only [hjR', hn0]),
                abs_of_neg (by linarith only [hjR', hn0])]
              linarith only [hjR']
          have hm2 : (max (n : ℝ) j) ^ 2 ≤ 4 * |(n : ℝ) - j| ^ 2 := by
            have hsq := mul_self_le_mul_self hm0 hm_far
            nlinarith only [hsq]
          rw [div_le_iff₀ (mul_pos hsj hd2)]
          nlinarith only [hm2, mul_nonneg (sub_nonneg.mpr hsj1) hd2.le]
      · have hz : E_ker n j = 0 := by dsimp only [E_ker]; rw [if_neg hgap]
        rw [hz, zero_mul, abs_zero]
        have hif0 : 0 ≤ (if j ∈ S_mod then 8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 else 0) + 4 := by
          split_ifs <;> positivity
        exact mul_nonneg (by positivity) hif0
    have hgap_mod : ∀ j ∈ S_mod, c * (n : ℝ) / N < |(n : ℝ) - j| := by
      intro j hjS
      obtain ⟨hj, hgap, hnj2, _⟩ := mem_filter.mp hjS
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
      have hnjR : (n : ℝ) ≤ 2 * j := by exact_mod_cast hnj2
      have hne : j ≠ n := by
        intro heq; subst heq; simp only [sub_self, abs_zero] at hgap
        linarith only [hgap, div_pos hc0 hN0]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hjlt : (j : ℝ) < n := by exact_mod_cast hlt
        have hlog_ub := Real.log_le_sub_one_of_pos (div_pos hn0 hj0)
        rw [Real.log_div hn0.ne' hj0.ne', show (n : ℝ) / j - 1 = ((n : ℝ) - j) / j by
          field_simp [hj0.ne']] at hlog_ub
        have hlog_eq : |Real.log j - Real.log n| = Real.log n - Real.log j := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hj0 hjlt.le))]
        have hfrac : ((n : ℝ) - j) / j ≤ 2 * ((n : ℝ) - j) / n := by
          rw [div_le_div_iff₀ hj0 hn0]
          nlinarith only [hnjR, sub_pos.mpr hjlt]
        have habs_eq : |(n : ℝ) - j| = (n : ℝ) - j := abs_of_pos (sub_pos.mpr hjlt)
        have hlt2 : 2 * c / N < 2 * |(n : ℝ) - j| / n := by
          rw [habs_eq, show 2 * c / (N : ℝ) = 2 * (c / N) by ring]
          linarith only [hgap, hlog_eq, hlog_ub, hfrac]
        have hmul := (div_lt_div_iff₀ hN0 hn0).mp hlt2
        exact (div_lt_iff₀ hN0).mpr (by linarith only [hmul])
      · have hngt : (n : ℝ) < j := by exact_mod_cast hgt
        have hlog_ub := Real.log_le_sub_one_of_pos (div_pos hj0 hn0)
        rw [Real.log_div hj0.ne' hn0.ne', show (j : ℝ) / n - 1 = ((j : ℝ) - n) / n by
          field_simp [hn0.ne']] at hlog_ub
        have hlog_eq : |Real.log j - Real.log n| = Real.log j - Real.log n :=
          abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hn0 hngt.le))
        have habs_eq : |(n : ℝ) - j| = (j : ℝ) - n := by
          rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hngt)]
        have hpos_diff : 0 < ((j : ℝ) - n) / n := div_pos (sub_pos.mpr hngt) hn0
        have h2diff : ((j : ℝ) - n) / n ≤ 2 * ((j : ℝ) - n) / n := by
          rw [mul_div_assoc]; linarith only [hpos_diff]
        have hlt2 : 2 * c / N < 2 * |(n : ℝ) - j| / n := by
          rw [habs_eq, show 2 * c / (N : ℝ) = 2 * (c / N) by ring]
          linarith only [hgap, hlog_eq, hlog_ub, h2diff]
        have hmul := (div_lt_div_iff₀ hN0 hn0).mp hlt2
        exact (div_lt_iff₀ hN0).mpr (by linarith only [hmul])
    have hsum_mod : (∑ j ∈ S_mod, 1 / |(n : ℝ) - j| ^ 2) ≤ 4 * (N : ℝ) / (c * n) := by
      let L_set := S_mod.filter (fun j => j < n)
      let R_set := S_mod.filter (fun j => n < j)
      have hsplit_LR : (∑ j ∈ S_mod, 1 / |(n : ℝ) - j| ^ 2) =
          (∑ j ∈ L_set, 1 / |(n : ℝ) - j| ^ 2) + ∑ j ∈ R_set, 1 / |(n : ℝ) - j| ^ 2 := by
        simp only [L_set, R_set, sum_filter, ← sum_add_distrib]
        refine sum_congr rfl fun j _ => ?_
        rcases lt_trichotomy j n with h | rfl | h
        · rw [if_pos h, if_neg (not_lt_of_ge h.le), add_zero]
        · simp
        · rw [if_neg (not_lt_of_ge h.le), if_pos h, zero_add]
      have hL_bound : (∑ j ∈ L_set, 1 / |(n : ℝ) - j| ^ 2) ≤ 2 / (d : ℝ) := by
        have hinj : ∀ i ∈ L_set, ∀ j ∈ L_set, n - i = n - j → i = j := by
          intro i hi j hj hij
          have := (mem_filter.mp hi).2; have := (mem_filter.mp hj).2
          change n - i = n - j at hij; omega
        have hmap : (∑ j ∈ L_set, 1 / |(n : ℝ) - j| ^ 2) =
            ∑ k ∈ L_set.image (fun j => n - j), 1 / (k : ℝ) ^ 2 := by
          rw [sum_image hinj]
          refine sum_congr rfl fun j hj => ?_
          have hlt := (mem_filter.mp hj).2
          rw [Nat.cast_sub hlt.le, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le))]
        have hsub_d : L_set.image (fun j => n - j) ⊆ Icc d N := by
          intro k hk
          obtain ⟨j, hjL, rfl⟩ := mem_image.mp hk
          obtain ⟨hjS, hlt⟩ := mem_filter.mp hjL
          have hgj := hgap_mod j hjS
          rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
            ← Nat.cast_sub hlt.le] at hgj
          have hceil : ⌈c * (n : ℝ) / N⌉₊ ≤ n - j := Nat.ceil_le.mpr hgj.le
          have hd_le : d ≤ n - j := max_le (by omega) hceil
          exact mem_Icc.mpr ⟨hd_le, (Nat.sub_le n j).trans hnN⟩
        rw [hmap]
        exact (sum_le_sum_of_subset_of_nonneg (f := fun k : ℕ => 1 / (k : ℝ) ^ 2)
          hsub_d (fun _ _ _ => by positivity)).trans (sum_Icc_inv_sq_from_le_bilin hd1)
      have hR_bound : (∑ j ∈ R_set, 1 / |(n : ℝ) - j| ^ 2) ≤ 2 / (d : ℝ) := by
        have hinj : ∀ i ∈ R_set, ∀ j ∈ R_set, i - n = j - n → i = j := by
          intro i hi j hj hij
          have := (mem_filter.mp hi).2; have := (mem_filter.mp hj).2
          change i - n = j - n at hij; omega
        have hmap : (∑ j ∈ R_set, 1 / |(n : ℝ) - j| ^ 2) =
            ∑ k ∈ R_set.image (fun j => j - n), 1 / (k : ℝ) ^ 2 := by
          rw [sum_image hinj]
          refine sum_congr rfl fun j hj => ?_
          have hlt := (mem_filter.mp hj).2
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
            Nat.cast_sub hlt.le]
        have hsub_d : R_set.image (fun j => j - n) ⊆ Icc d N := by
          intro k hk
          obtain ⟨j, hjR, rfl⟩ := mem_image.mp hk
          obtain ⟨hjS, hlt⟩ := mem_filter.mp hjR
          have hjN := (mem_Icc.mp (mem_filter.mp hjS).1).2
          have hgj := hgap_mod j hjS
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
            ← Nat.cast_sub hlt.le] at hgj
          have hceil : ⌈c * (n : ℝ) / N⌉₊ ≤ j - n := Nat.ceil_le.mpr hgj.le
          have hd_le : d ≤ j - n := max_le (by omega) hceil
          exact mem_Icc.mpr ⟨hd_le, (Nat.sub_le j n).trans hjN⟩
        rw [hmap]
        exact (sum_le_sum_of_subset_of_nonneg (f := fun k : ℕ => 1 / (k : ℝ) ^ 2)
          hsub_d (fun _ _ _ => by positivity)).trans (sum_Icc_inv_sq_from_le_bilin hd1)
      rw [hsplit_LR]
      have h4d : (∑ j ∈ L_set, 1 / |(n : ℝ) - j| ^ 2) + ∑ j ∈ R_set, 1 / |(n : ℝ) - j| ^ 2 ≤
          4 * (1 / (d : ℝ)) :=
        (add_le_add hL_bound hR_bound).trans_eq (by ring)
      exact h4d.trans ((mul_le_mul_of_nonneg_left hinv_d (by norm_num)).trans_eq (by ring))
    have hsub_S : (Icc 1 N).filter (fun j => j ∈ S_mod) = S_mod := by
      ext j; simp only [S_mod, mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
    calc
      |row_x n| ≤ ∑ j ∈ Icc 1 N, |E_ker n j * (normalizedRamanujanMode m j / Real.sqrt j)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Icc 1 N, K₀ * (c / N) ^ 2 * Real.sqrt m *
            ((if j ∈ S_mod then 8 * (n : ℝ) * Real.sqrt n / |(n : ℝ) - j| ^ 2 else 0) + 4) :=
        sum_le_sum hterm_pt
      _ = K₀ * (c / N) ^ 2 * Real.sqrt m *
            ((8 * (n : ℝ) * Real.sqrt n) * (∑ j ∈ S_mod, 1 / |(n : ℝ) - j| ^ 2) + 4 * N) := by
        rw [← mul_sum, sum_add_distrib, ← sum_filter, hsub_S, sum_const, nsmul_eq_mul,
          Nat.card_Icc, Nat.add_sub_cancel, mul_sum]
        congr 2
        · exact sum_congr rfl fun _ _ => by ring
        · ring
      _ ≤ K₀ * (c / N) ^ 2 * Real.sqrt m *
            ((8 * (n : ℝ) * Real.sqrt n) * (4 * (N : ℝ) / (c * n)) + 4 * N) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hsum_mod (by positivity)) le_rfl)
          (by positivity)
      _ = 32 * K₀ * Real.sqrt m * c * Real.sqrt n / N + 4 * K₀ * Real.sqrt m * c ^ 2 / N := by
        field_simp [hc0.ne', hn0.ne', hN0.ne']; ring
  have hc_sqrt : c ≤ Real.sqrt N := by
    have h := Real.sqrt_le_sqrt hc2N
    rwa [Real.sqrt_sq hc0.le] at h
  have hsum_x : (∑ n ∈ Icc 1 N, |row_x n| / Real.sqrt n) ≤
      (40 * K₀ + 1) * Real.sqrt m * c := by
    have hpt : ∀ n ∈ Icc 1 N, |row_x n| / Real.sqrt n ≤
        32 * K₀ * Real.sqrt m * c / N +
          (4 * K₀ * Real.sqrt m * c ^ 2 / N) * (1 / Real.sqrt n) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
      refine (div_le_div_of_nonneg_right (hrow_abs n hn) hsn.le).trans_eq ?_
      rw [add_div]
      field_simp [hsn.ne', hN0.ne']
    have hs1 : (∑ _n ∈ Icc 1 N, 32 * K₀ * Real.sqrt m * c / (N : ℝ)) =
        32 * K₀ * Real.sqrt m * c := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      field_simp [hN0.ne']
    have hs2 : (4 * K₀ * Real.sqrt m * c ^ 2 / N) * (∑ n ∈ Icc 1 N, 1 / Real.sqrt (n : ℝ)) ≤
        8 * K₀ * Real.sqrt m * c := by
      have hc2_div : c ^ 2 / (N : ℝ) * (2 * Real.sqrt N) ≤ 2 * c := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hN0]
        calc
          c ^ 2 * (2 * Real.sqrt N) = (2 * c * Real.sqrt N) * c := by ring
          _ ≤ (2 * c * Real.sqrt N) * Real.sqrt N :=
            mul_le_mul_of_nonneg_left hc_sqrt (by positivity)
          _ = 2 * c * (Real.sqrt N * Real.sqrt N) := by ring
          _ = 2 * c * N := by rw [Real.mul_self_sqrt hN0.le]
      calc
        (4 * K₀ * Real.sqrt m * c ^ 2 / N) * (∑ n ∈ Icc 1 N, 1 / Real.sqrt (n : ℝ)) ≤
            (4 * K₀ * Real.sqrt m * c ^ 2 / N) * (2 * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left (sum_Icc_one_div_sqrt_le_two_sqrt N) (by positivity)
        _ = (4 * K₀ * Real.sqrt m) * (c ^ 2 / N * (2 * Real.sqrt N)) := by ring
        _ ≤ (4 * K₀ * Real.sqrt m) * (2 * c) :=
          mul_le_mul_of_nonneg_left hc2_div (by positivity)
        _ = 8 * K₀ * Real.sqrt m * c := by ring
    calc
      (∑ n ∈ Icc 1 N, |row_x n| / Real.sqrt n) ≤
          ∑ n ∈ Icc 1 N, (32 * K₀ * Real.sqrt m * c / N +
            (4 * K₀ * Real.sqrt m * c ^ 2 / N) * (1 / Real.sqrt n)) := sum_le_sum hpt
      _ = (∑ _n ∈ Icc 1 N, 32 * K₀ * Real.sqrt m * c / (N : ℝ)) +
            (4 * K₀ * Real.sqrt m * c ^ 2 / N) * ∑ n ∈ Icc 1 N, 1 / Real.sqrt (n : ℝ) := by
        rw [sum_add_distrib, ← mul_sum]
      _ ≤ 40 * K₀ * Real.sqrt m * c := by rw [hs1]; linarith only [hs2]
      _ ≤ (40 * K₀ + 1) * Real.sqrt m * c := by
        nlinarith only [Real.sqrt_nonneg m, hc0.le]
  have hp := abs_inner_of_coord_eq_div_sqrt_log hl _ row_x hcoord
  refine (hp.trans (mul_le_mul_of_nonneg_left hsum_x (by positivity))).trans_eq ?_
  rw [Real.sqrt_mul (Nat.cast_nonneg m)]; ring

/-- **Channel 5 (Rank-two pole error):** Cauchy–Schwarz with the rank-two `L^2` bound
`O(√m * c^2 * log N / N)` and `‖v_l‖ ≤ 2 √l` gives `O(√(m l) * c^2 * log N / N)`. -/
private theorem exists_poleError_bilinear_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l : ℕ, 0 < m → 0 < l → ∀ c : ℝ, 1 ≤ c →
      ∀ N : ℕ, 1 ≤ N → 1 ≤ Real.log N → c ≤ (N : ℝ) →
        |⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
            (normalizedRamanujanHorizonVector m N),
          normalizedRamanujanHorizonVector l N⟫| ≤
          C * Real.sqrt ((m : ℝ) * l) * c ^ 2 * Real.log N / (N : ℝ) := by
  let C_p := atomPoleMomentErrorConstant φ
  have hCp0 : 0 ≤ C_p := by
    dsimp only [C_p, atomPoleMomentErrorConstant]; positivity
  refine ⟨8 * C_p + 1, by positivity, ?_⟩
  intro m l hm hl c hc N hN hlog hcN
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  let S_m := ∑ j ∈ Icc 1 N, normalizedRamanujanMode m j / (j : ℝ)
  let T_m := ∑ j ∈ Icc 1 N, normalizedRamanujanMode m j
  have hS_sq : S_m ^ 2 ≤ (m : ℝ) * (1 + Real.log N) ^ 2 := by
    have hS_abs : |S_m| ≤ Real.sqrt m * (1 + Real.log N) := by
      calc
        |S_m| ≤ ∑ j ∈ Icc 1 N, |normalizedRamanujanMode m j / (j : ℝ)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Icc 1 N, Real.sqrt m * (1 / (j : ℝ)) := by
          refine sum_le_sum fun j hj => ?_
          have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
          rw [abs_div, abs_of_pos hj0, div_eq_mul_inv, one_div]
          exact mul_le_mul_of_nonneg_right (abs_mode_le_sqrt_conductor_bilin hm j) (by positivity)
        _ = Real.sqrt m * ∑ j ∈ Icc 1 N, 1 / (j : ℝ) := (mul_sum _ _ _).symm
        _ ≤ Real.sqrt m * (1 + Real.log N) :=
          mul_le_mul_of_nonneg_left (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N)
            (Real.sqrt_nonneg m)
    have h := mul_self_le_mul_self (abs_nonneg _) hS_abs
    rwa [← sq, sq_abs, ← sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)] at h
  have hT_sq : T_m ^ 2 ≤ (m : ℝ) * (N : ℝ) ^ 2 := by
    have hT_abs : |T_m| ≤ Real.sqrt m * (N : ℝ) := by
      calc
        |T_m| ≤ ∑ j ∈ Icc 1 N, |normalizedRamanujanMode m j| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Icc 1 N, Real.sqrt m := sum_le_sum fun j _ => abs_mode_le_sqrt_conductor_bilin hm j
        _ = Real.sqrt m * (N : ℝ) := by
          rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]; ring
    have h := mul_self_le_mul_self (abs_nonneg _) hT_abs
    rwa [← sq, sq_abs, ← sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)] at h
  have hd := abs_atomPoleErrorCoefficient_le_of_le hφ hsupp hM hc0 hN hcN
  have hs_coef : atomPoleErrorCoefficient φ c N ^ 2 ≤ C_p ^ 2 * (c / N) ^ 4 := by
    have h := mul_self_le_mul_self (abs_nonneg _) hd
    rw [← sq, sq_abs, ← sq] at h
    exact h.trans_eq (by dsimp only [C_p]; ring)
  have hraw : ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
      (ramanujanHorizonVector m N)‖ ^ 2 ≤
      4 * C_p ^ 2 * (m : ℝ) * c ^ 4 * (1 + Real.log N) ^ 2 / (N : ℝ) ^ 2 := by
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => atomPoleErrorCoefficient φ c N *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have hrow : ∀ n ∈ Icc 1 N,
        (∑ j ∈ Icc 1 N, atomPoleErrorCoefficient φ c N *
          (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) * ramanujanPoleProfile m j) ^ 2 ≤
          2 * atomPoleErrorCoefficient φ c N ^ 2 * ((n : ℝ) * S_m ^ 2 + (1 / (n : ℝ)) * T_m ^ 2) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
      have hid : (∑ j ∈ Icc 1 N, atomPoleErrorCoefficient φ c N *
          (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) * ramanujanPoleProfile m j) =
          atomPoleErrorCoefficient φ c N * (Real.sqrt n * S_m + (1 / Real.sqrt n) * T_m) := by
        dsimp only [S_m, T_m]
        rw [mul_add, ← mul_assoc _ (Real.sqrt n), mul_sum,
          ← mul_assoc _ (1 / Real.sqrt n), mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun j hj => ?_
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
        have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj0
        simp only [ramanujanPoleProfile]
        field_simp [hsn.ne', hsj.ne']
        rw [Real.sq_sqrt hj0.le]; ring
      rw [hid, mul_pow]
      have h2 : (Real.sqrt n * S_m + (1 / Real.sqrt n) * T_m) ^ 2 ≤
          2 * ((n : ℝ) * S_m ^ 2 + (1 / (n : ℝ)) * T_m ^ 2) := by
        have h1 : (Real.sqrt n * S_m) ^ 2 = (n : ℝ) * S_m ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hn0.le]
        have h2' : ((1 / Real.sqrt n) * T_m) ^ 2 = (1 / (n : ℝ)) * T_m ^ 2 := by
          rw [mul_pow, one_div_pow, Real.sq_sqrt hn0.le]
        nlinarith only [h1, h2', sq_nonneg (Real.sqrt n * S_m - (1 / Real.sqrt n) * T_m)]
      exact (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)).trans_eq (by ring)
    have hsum_n : (∑ n ∈ Icc 1 N, (n : ℝ)) ≤ (N : ℝ) ^ 2 := by
      calc
        (∑ n ∈ Icc 1 N, (n : ℝ)) ≤ ∑ _n ∈ Icc 1 N, (N : ℝ) :=
          sum_le_sum fun n hn => by exact_mod_cast (mem_Icc.mp hn).2
        _ = (N : ℝ) ^ 2 := by rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]; ring
    have hsum_inv : (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) ≤ (1 + Real.log N) ^ 2 := by
      have h1 : 1 ≤ 1 + Real.log (N : ℝ) := by linarith only [hL0]
      exact (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N).trans (by nlinarith only [h1])
    calc
      _ ≤ ∑ n ∈ Icc 1 N, 2 * atomPoleErrorCoefficient φ c N ^ 2 *
            ((n : ℝ) * S_m ^ 2 + (1 / (n : ℝ)) * T_m ^ 2) := sum_le_sum hrow
      _ = 2 * atomPoleErrorCoefficient φ c N ^ 2 *
            ((∑ n ∈ Icc 1 N, (n : ℝ)) * S_m ^ 2 + (∑ n ∈ Icc 1 N, 1 / (n : ℝ)) * T_m ^ 2) := by
        rw [← mul_sum, sum_add_distrib, ← sum_mul, ← sum_mul]
      _ ≤ 2 * (C_p ^ 2 * (c / N) ^ 4) *
            ((N : ℝ) ^ 2 * ((m : ℝ) * (1 + Real.log N) ^ 2) +
              (1 + Real.log N) ^ 2 * ((m : ℝ) * (N : ℝ) ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs_coef zero_le_two)
          (add_le_add (mul_le_mul hsum_n hS_sq (sq_nonneg _) (sq_nonneg _))
            (mul_le_mul hsum_inv hT_sq (sq_nonneg _) (sq_nonneg _)))
          (by positivity) (by positivity)
      _ = 4 * C_p ^ 2 * (m : ℝ) * c ^ 4 * (1 + Real.log N) ^ 2 / (N : ℝ) ^ 2 := by
        field_simp [hN0.ne']; ring
  have hnorm_u : ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
      (normalizedRamanujanHorizonVector m N)‖ ≤
      4 * C_p * Real.sqrt m * c ^ 2 * Real.log N / N := by
    have h1L : (1 + Real.log (N : ℝ)) ^ 2 ≤ 4 * Real.log (N : ℝ) ^ 2 := by
      have : 1 + Real.log (N : ℝ) ≤ 2 * Real.log (N : ℝ) := by linarith only [hlog]
      exact (pow_le_pow_left₀ (by positivity) this 2).trans_eq (by ring)
    have hsq : ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
        (4 * C_p * Real.sqrt m * c ^ 2 * Real.log N / N) ^ 2 := by
      have hact : ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
          (normalizedRamanujanHorizonVector m N)‖ ^ 2 =
          ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
            (ramanujanHorizonVector m N)‖ ^ 2 / Real.log N := by
        rw [normalizedRamanujanHorizonVector, map_smul, norm_smul, mul_pow,
          Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hL0.le]; ring
      rw [hact]
      calc
        _ ≤ (4 * C_p ^ 2 * (m : ℝ) * c ^ 4 * (1 + Real.log N) ^ 2 / (N : ℝ) ^ 2) / Real.log N :=
          div_le_div_of_nonneg_right hraw hL0.le
        _ ≤ 4 * C_p ^ 2 * (m : ℝ) * c ^ 4 * (1 + Real.log N) ^ 2 / (N : ℝ) ^ 2 :=
          div_le_self (by positivity) hlog
        _ ≤ 4 * C_p ^ 2 * (m : ℝ) * c ^ 4 * (4 * Real.log (N : ℝ) ^ 2) / (N : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1L (by positivity)) (sq_nonneg _)
        _ = (4 * C_p * Real.sqrt m * c ^ 2 * Real.log N / N) ^ 2 := by
          rw [div_pow, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]; ring
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h
  have hnorm_v : ‖normalizedRamanujanHorizonVector l N‖ ≤ 2 * Real.sqrt l := by
    have hsq : ‖normalizedRamanujanHorizonVector l N‖ ^ 2 ≤ (2 * Real.sqrt l) ^ 2 :=
      (norm_sq_normalizedRamanujanHorizonVector_le hl hlog).trans
        (by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg l)]; linarith [Nat.cast_nonneg (α := ℝ) l])
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h
  calc
    |⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N),
      normalizedRamanujanHorizonVector l N⟫| ≤
        ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
          (normalizedRamanujanHorizonVector m N)‖ *
          ‖normalizedRamanujanHorizonVector l N‖ := abs_real_inner_le_norm _ _
    _ ≤ (4 * C_p * Real.sqrt m * c ^ 2 * Real.log N / N) * (2 * Real.sqrt l) :=
      mul_le_mul hnorm_u hnorm_v (norm_nonneg _) (by positivity)
    _ = 8 * C_p * Real.sqrt ((m : ℝ) * l) * c ^ 2 * Real.log N / N := by
      rw [Real.sqrt_mul (Nat.cast_nonneg m)]; ring
    _ ≤ (8 * C_p + 1) * Real.sqrt ((m : ℝ) * l) * c ^ 2 * Real.log N / N := by
      apply div_le_div_of_nonneg_right _ hN0.le
      have hnn : 0 ≤ Real.sqrt ((m : ℝ) * l) * c ^ 2 * Real.log N := by positivity
      linarith only [hnn]

/-- **Channel 6 (Near-gamma downward source):** The near-band row is bounded pointwise by
`O((c / N) * K_{m,c} * √n)`, summing against `1 / √n` to `O(c * K_{m,c})`, while the exterior
boundary strip of width `linearPrimeStrip c` pairs to `O(√(m l) * c^2 / N)`. -/
private theorem exists_downward_bilinear_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l : ℕ, 0 < m → 0 < l → ∀ c : ℝ, 1 ≤ c →
      ∀ N : ℕ, 1 ≤ N → 1 ≤ Real.log N → 2 * (Real.exp 1 + 2) * c ≤ (N : ℝ) →
        |⟪(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m,
          normalizedRamanujanHorizonVector l N⟫| ≤
          C * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) *
            (c * (1 + Real.log c) / Real.log N + c ^ 2 / (N : ℝ)) := by
  obtain ⟨Cp, hCp, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  let R₀ : ℝ := 2 * Real.exp 2
  let E : ℝ := Cp + Real.log R₀ + 4
  have hlogR₀ : 0 ≤ Real.log R₀ :=
    Real.log_nonneg (by dsimp only [R₀]; have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2); linarith)
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  let A_near : ℝ := 2 * Real.exp 1 * R₀ * E
  let B_ext : ℝ := 5 * Real.sqrt 2 * (Real.exp 1 + 2) * (Real.exp 1 + 1)
  refine ⟨A_near + B_ext + 1, by dsimp only [A_near, B_ext, R₀]; positivity, ?_⟩
  intro m l hm hl c hc1 N hN hlogN h2BcN
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlogN
  have hw1 : c / N ≤ 1 / 3 := by
    apply (div_le_iff₀ hN0).mpr
    have he1 := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [h2BcN, he1, hc0]
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have htot_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have h1m : 1 ≤ 1 + Real.log (m : ℝ) := by linarith [Real.log_natCast_nonneg m]
  have hlogc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have h1c : 1 ≤ 1 + Real.log c := by linarith only [hlogc0]
  let K_m := E * ((m.totient : ℝ) * (1 + Real.log m)) * (1 + Real.log c)
  have hKm0 : 0 ≤ K_m := by dsimp only [K_m]; positivity
  have hentry : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
      |nearGammaDownwardCoefficient φ c N m n j| ≤ K_m := by
    intro n hn j hj
    have hjN := (mem_filter.mp hj).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
    have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
      have h := (mem_filter.mp hj).2.2
      change |Real.log j - Real.log n| ≤ 2 * c / N at h
      simpa only [mul_div_assoc] using h
    let q := shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)
    let a := atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2)
    have hrem : |a - Real.log (1 / (c / N)) * q| ≤ Cp := by
      simpa only [a, q, mul_div_assoc] using hpair (c / N) (div_pos hc0 hN0) hw1 n j hs
    have hq : |q| ≤ 1 := by
      have h := abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp)
        (|Real.log j - Real.log n| / (c / N))
      change |shellAutocorr φ (|Real.log j - Real.log n| / (c / N))| ≤ ∫ u, φ u ^ 2 at h
      dsimp only [q]
      rw [abs_div, abs_of_pos hM, div_le_one hM]
      exact h
    have hcm : |ramanujanLagCoefficient m j| ≤ (m.totient : ℝ) :=
      BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m j
    have hjb : |ramanujanLogDivisorJet m j| ≤ 2 * (m.totient : ℝ) * (1 + Real.log m) := by
      have hmangoldt : 0 ≤ ArithmeticFunction.vonMangoldt m := ArithmeticFunction.vonMangoldt_nonneg
      have htri := abs_add_le (ramanujanLogDivisorJet m j - ArithmeticFunction.vonMangoldt m)
        (ArithmeticFunction.vonMangoldt m)
      rw [sub_add_cancel, abs_of_nonneg hmangoldt] at htri
      have henvelope := abs_ramanujanLogDivisorJet_sub_mean_le hm j
      have htot1 : (1 : ℝ) ≤ m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
      have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
      have hvm : ArithmeticFunction.vonMangoldt m ≤ Real.log (m : ℝ) :=
        ArithmeticFunction.vonMangoldt_le_log
      have hdiff := mul_le_mul_of_nonneg_left
        (RenormalizedArithmeticPotentialTheory.tameDifferent_le_log hm) (Nat.cast_nonneg m.totient)
      nlinarith only [htri, henvelope, htot1, hlog0, hvm, hdiff]
    have hquot : (N : ℝ) / j ≤ linearNearRowRadius c :=
      (div_le_iff₀ hj0).mpr (nearRow_geometry_small_width hc0 hn hj hw).2.2
    have hloglow : 0 ≤ Real.log N - Real.log j := sub_nonneg.mpr
      (Real.log_le_log hj0 (by exact_mod_cast (mem_Icc.mp hjN).2))
    have hloghigh : Real.log N - Real.log j ≤ Real.log R₀ + Real.log c := by
      have h := Real.log_le_log (div_pos hN0 hj0) hquot
      have hR_eq : linearNearRowRadius c = R₀ * c := by
        unfold linearNearRowRadius; dsimp only [R₀]; ring
      rw [Real.log_div hN0.ne' hj0.ne', hR_eq, Real.log_mul (by dsimp only [R₀]; positivity) hc0.ne'] at h
      exact h
    have hlog : |Real.log (1 / (c / N)) - Real.log j| ≤ Real.log R₀ + 2 * Real.log c := by
      have hlogeq : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
        rw [one_div, Real.log_inv, Real.log_div hc0.ne' hN0.ne']; ring
      rw [hlogeq, show Real.log N - Real.log c - Real.log j =
        (Real.log N - Real.log j) - Real.log c by ring]
      exact (abs_sub _ _).trans
        (by rw [abs_of_nonneg hloglow, abs_of_nonneg hlogc0]; linarith only [hloghigh])
    have heq : nearGammaDownwardCoefficient φ c N m n j =
        (a - Real.log (1 / (c / N)) * q) * ramanujanLagCoefficient m j +
        (Real.log (1 / (c / N)) - Real.log j) * q * ramanujanLagCoefficient m j +
        q * ramanujanLogDivisorJet m j := by
      rw [nearGammaDownwardCoefficient, sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m
        (mem_Icc.mp hjN).1]
      dsimp only [a, q]; ring
    rw [heq]
    have h1 := mul_le_mul hrem hcm (abs_nonneg _) hCp
    have h2 := mul_le_mul (mul_le_mul hlog hq (abs_nonneg _) (by positivity))
      hcm (abs_nonneg _) (by positivity)
    have h3 := mul_le_mul hq hjb (abs_nonneg _) zero_le_one
    simp only [mul_one, one_mul] at h2 h3
    have htri : |(a - Real.log (1 / (c / N)) * q) * ramanujanLagCoefficient m j +
        (Real.log (1 / (c / N)) - Real.log j) * q * ramanujanLagCoefficient m j +
        q * ramanujanLogDivisorJet m j| ≤
        (Cp + Real.log R₀ + 2 * Real.log c) * (m.totient : ℝ) +
          2 * (m.totient : ℝ) * (1 + Real.log m) := by
      refine (abs_add_three _ _ _).trans ?_
      simp only [abs_mul]
      linarith only [h1, h2, h3,
        (by ring : Cp * (m.totient : ℝ) + (Real.log R₀ + 2 * Real.log c) * (m.totient : ℝ) =
          (Cp + Real.log R₀ + 2 * Real.log c) * (m.totient : ℝ))]
    let M_m := (m.totient : ℝ) * (1 + Real.log m)
    have htot_Mm : (m.totient : ℝ) ≤ M_m := le_mul_of_one_le_right htot_pos.le h1m
    have hterm1 : (Cp + Real.log R₀ + 2 * Real.log c) * (m.totient : ℝ) ≤
        (Cp + Real.log R₀ + 2) * M_m * (1 + Real.log c) := by
      have hc_le : Cp + Real.log R₀ + 2 * Real.log c ≤
          (Cp + Real.log R₀ + 2) * (1 + Real.log c) := by
        nlinarith only [hCp, hlogR₀, hlogc0]
      exact (mul_le_mul hc_le htot_Mm htot_pos.le (by positivity)).trans_eq (by ring)
    have hterm2 : 2 * (m.totient : ℝ) * (1 + Real.log m) ≤ 2 * M_m * (1 + Real.log c) := by
      have : 2 * (m.totient : ℝ) * (1 + Real.log m) = 2 * M_m := by dsimp only [M_m]; ring
      rw [this]; exact le_mul_of_one_le_right (by positivity) h1c
    dsimp only [K_m, E]
    linarith only [htri, hterm1, hterm2,
      (by dsimp only [M_m]; ring : (Cp + Real.log R₀ + 4) * ((m.totient : ℝ) * (1 + Real.log m)) *
        (1 + Real.log c) = (Cp + Real.log R₀ + 2) * M_m * (1 + Real.log c) +
          2 * M_m * (1 + Real.log c))]
  -- Near-band bilinear bound via `abs_inner_of_coord_eq_div_sqrt_log`.
  have hnear_bilin : |⟪normalizedNearGammaDownwardVector φ c N m,
      normalizedRamanujanHorizonVector l N⟫| ≤
      A_near * (m.totient : ℝ) * Real.sqrt l * (1 + Real.log m) * c * (1 + Real.log c) /
        Real.log N := by
    have he_gap : Real.exp (2 * c / N) - 1 ≤ linearNearRowRadius c / N := by
      calc
        Real.exp (2 * c / N) - 1 ≤ 2 * c / N * Real.exp (2 * c / N) := exp_sub_one_le_mul_exp
        _ ≤ 2 * c / N * Real.exp 2 :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by
              have h := mul_le_mul_of_nonneg_left hw zero_le_two
              simpa only [mul_div_assoc, mul_one] using h)) (by positivity)
        _ = linearNearRowRadius c / N := by unfold linearNearRowRadius; ring
    have hrow_div : ∀ n ∈ Icc 1 N,
        |nearGammaDownwardRow φ c N m n| / Real.sqrt n ≤
          2 * Real.exp 1 * linearNearRowRadius c * K_m / N := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
      let rad_n := (n : ℝ) * (linearNearRowRadius c / N)
      have hrad0 : 0 ≤ rad_n := by dsimp only [rad_n]; unfold linearNearRowRadius; positivity
      have hcard_n : ((nearRowIndices c N n).card : ℝ) ≤ 2 * rad_n := by
        have hsub : nearRowIndices c N n ⊆
            (Icc 1 N).filter (fun j => j ≠ n ∧ |(j : ℝ) - n| ≤ rad_n) := by
          intro j hj
          obtain ⟨hjN, hjn, hlog⟩ := mem_filter.mp hj
          have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
          have hdist := (abs_sub_le_of_abs_log_le hj0 hn0 hlog).trans
            (mul_le_mul_of_nonneg_left he_gap hn0.le)
          exact mem_filter.mpr ⟨hjN, hjn, hdist⟩
        exact (show ((nearRowIndices c N n).card : ℝ) ≤
            (((Icc 1 N).filter (fun j => j ≠ n ∧ |(j : ℝ) - n| ≤ rad_n)).card : ℝ) by
            exact_mod_cast card_le_card hsub).trans (card_near_le (Icc 1 N) n hrad0)
      have hpt_j : ∀ j ∈ nearRowIndices c N n,
          |nearGammaDownwardCoefficient φ c N m n j / Real.sqrt j| ≤
            Real.exp 1 * K_m / Real.sqrt n := by
        intro j hj
        obtain ⟨hjN, _, hlog⟩ := mem_filter.mp hj
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
        have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj0
        have hlog_nj : Real.log n - Real.log j ≤ 2 := by
          have h1 : Real.log n - Real.log j ≤ |Real.log j - Real.log n| := by
            rw [abs_sub_comm]; exact le_abs_self _
          have h2 : 2 * c / N ≤ 2 := by
            have := mul_le_mul_of_nonneg_left hw zero_le_two
            simpa only [mul_div_assoc, mul_one] using this
          exact h1.trans (hlog.trans h2)
        have hnj_exp : (n : ℝ) / j ≤ Real.exp 2 := by
          rw [← Real.exp_log (div_pos hn0 hj0), Real.log_div hn0.ne' hj0.ne']
          exact Real.exp_le_exp.mpr hlog_nj
        have hsqrt_j : 1 / Real.sqrt j ≤ Real.exp 1 / Real.sqrt n := by
          have hsq := Real.sqrt_le_sqrt ((div_le_iff₀ hj0).mp hnj_exp)
          have hexp2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
          rw [hexp2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos 1).le] at hsq
          exact (div_le_div_iff₀ hsj hsn).mpr (by linarith only [hsq])
        rw [abs_div, abs_of_pos hsj, div_eq_mul_one_div]
        exact (mul_le_mul (hentry n hn j hj) hsqrt_j (by positivity) hKm0).trans_eq (by ring)
      have hrow_abs : |nearGammaDownwardRow φ c N m n| ≤
          (2 * rad_n) * (Real.exp 1 * K_m / Real.sqrt n) := by
        unfold nearGammaDownwardRow
        calc
          _ ≤ ∑ j ∈ nearRowIndices c N n,
                |nearGammaDownwardCoefficient φ c N m n j / Real.sqrt j| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j ∈ nearRowIndices c N n, (Real.exp 1 * K_m / Real.sqrt n) := sum_le_sum hpt_j
          _ = ((nearRowIndices c N n).card : ℝ) * (Real.exp 1 * K_m / Real.sqrt n) := by
            rw [sum_const, nsmul_eq_mul]
          _ ≤ (2 * rad_n) * (Real.exp 1 * K_m / Real.sqrt n) :=
            mul_le_mul_of_nonneg_right hcard_n (by positivity)
      calc
        |nearGammaDownwardRow φ c N m n| / Real.sqrt n ≤
            ((2 * rad_n) * (Real.exp 1 * K_m / Real.sqrt n)) / Real.sqrt n :=
          div_le_div_of_nonneg_right hrow_abs hsn.le
        _ = 2 * Real.exp 1 * linearNearRowRadius c * K_m / N := by
          dsimp only [rad_n]
          field_simp [hsn.ne', hN0.ne']
          rw [Real.sq_sqrt hn0.le]; ring
    have hsum_near : (∑ n ∈ Icc 1 N, |nearGammaDownwardRow φ c N m n| / Real.sqrt n) ≤
        2 * Real.exp 1 * linearNearRowRadius c * K_m := by
      calc
        _ ≤ ∑ _n ∈ Icc 1 N, (2 * Real.exp 1 * linearNearRowRadius c * K_m / N) :=
          sum_le_sum hrow_div
        _ = 2 * Real.exp 1 * linearNearRowRadius c * K_m := by
          rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
          field_simp [hN0.ne']
    have hp := abs_inner_of_coord_eq_div_sqrt_log hl
      (normalizedNearGammaDownwardVector φ c N m) (nearGammaDownwardRow φ c N m) (fun _ => rfl)
    refine (hp.trans (mul_le_mul_of_nonneg_left hsum_near (by positivity))).trans_eq ?_
    unfold linearNearRowRadius
    dsimp only [A_near, R₀, K_m]; ring
  -- Exterior boundary strip bilinear bound via `abs_inner_of_coord_eq_div_sqrt_log`.
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp (div_pos hc0 hN0)
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq (div_pos hc0 hN0)]
    exact mul_pos (div_pos hc0 hN0) hM
  have hext_bilin : |⟪normalizedExteriorDownwardVector φ c N m,
      normalizedRamanujanHorizonVector l N⟫| ≤
      B_ext * (m.totient : ℝ) * Real.sqrt l * c ^ 2 / (N : ℝ) := by
    let g := atomDilate φ (c / N)
    have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
    have hB_le : (linearPrimeStrip c : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc1
    have hcN : c ≤ (N : ℝ) := (div_le_one hN0).mp hw
    have hcut_ub : (exteriorPrimeCutoff c N : ℝ) ≤ 5 * (N : ℝ) := by
      have h1 : (exteriorPrimeCutoff c N : ℝ) ≤ (N : ℝ) + linearPrimeStrip c := by
        exact_mod_cast (exteriorPrimeCutoff_bounds_small_width hc0 hN hw).2
      have he1 : Real.exp 1 ≤ 3 := by have h := Real.exp_one_lt_d9; linarith
      nlinarith only [h1, hB_le, hcN, he1, hc0]
    have hrow_reg : ∀ n : ℕ, |regroupedExteriorDownwardPrimeRow g c N m n| ≤
        5 * (m.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N := by
      intro n
      have hcard : ((Ioc N (exteriorPrimeCutoff c N)).card : ℝ) ≤ linearPrimeStrip c := by
        have hbound := (exteriorPrimeCutoff_bounds_small_width hc0 hN hw).2
        rw [Nat.card_Ioc]
        exact_mod_cast (show exteriorPrimeCutoff c N - N ≤ linearPrimeStrip c by omega)
      have hterm : ∀ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
          |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ *
            (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))| ≤
            5 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by
        intro ℓ hℓ
        obtain ⟨hNℓ, hℓ_hi⟩ := mem_Ioc.mp hℓ
        have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le N) hNℓ)
        have hsℓ : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ0
        have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
        have hsqrt_le : Real.sqrt N ≤ Real.sqrt ℓ :=
          Real.sqrt_le_sqrt (by exact_mod_cast hNℓ.le)
        have hℓ_5N : (ℓ : ℝ) ≤ 5 * (N : ℝ) :=
          (by exact_mod_cast hℓ_hi : (ℓ : ℝ) ≤ exteriorPrimeCutoff c N).trans hcut_ub
        have hlogℓ : Real.log ℓ ≤ 5 * Real.log N := by
          have hl' := Real.log_le_log hℓ0 hℓ_5N
          rw [Real.log_mul (by norm_num) hN0.ne'] at hl'
          have hl5 : Real.log 5 ≤ 4 := by
            have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5); linarith
          linarith only [hl', hl5, hlogN]
        have hcorr : |bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2)| ≤ 1 := by
          rw [abs_div, abs_of_pos hG, div_le_one hG]
          exact abs_bumpCorr_le hg.continuous hgc _
        have hjet : |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ| ≤
            5 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by
          rw [abs_div, abs_of_pos hsℓ]
          calc
            |horizonRamanujanMangoldt m N ℓ| / Real.sqrt ℓ ≤
                ((m.totient : ℝ) * Real.log ℓ) / Real.sqrt ℓ :=
              div_le_div_of_nonneg_right (abs_horizonRamanujanMangoldt_le m N ℓ) hsℓ.le
            _ ≤ ((m.totient : ℝ) * (5 * Real.log N)) / Real.sqrt N := by
              have hnum : (m.totient : ℝ) * Real.log ℓ ≤ (m.totient : ℝ) * (5 * Real.log N) :=
                mul_le_mul_of_nonneg_left hlogℓ (Nat.cast_nonneg _)
              exact (div_le_div_of_nonneg_right hnum hsℓ.le).trans
                (div_le_div_of_nonneg_left (by positivity) hsN hsqrt_le)
            _ = 5 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by ring
        rw [abs_mul]
        simpa only [mul_one] using mul_le_mul hjet hcorr (abs_nonneg _) (by positivity)
      unfold regroupedExteriorDownwardPrimeRow
      calc
        _ ≤ ∑ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
            |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ *
              (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
            (5 * (m.totient : ℝ) * Real.log N / Real.sqrt N) := sum_le_sum hterm
        _ ≤ 5 * (m.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N := by
          rw [sum_const, nsmul_eq_mul]
          exact (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq (by ring)
    let S := (Icc 1 N).filter (fun n => N - linearPrimeStrip c ≤ n)
    have hrestrict : (∑ n ∈ Icc 1 N, |actualExteriorDownwardRow g N m n| / Real.sqrt n) =
        ∑ n ∈ S, |regroupedExteriorDownwardPrimeRow g c N m n| / Real.sqrt n := by
      have heq : (∑ n ∈ Icc 1 N, |actualExteriorDownwardRow g N m n| / Real.sqrt n) =
          ∑ n ∈ Icc 1 N, |regroupedExteriorDownwardPrimeRow g c N m n| / Real.sqrt n :=
        sum_congr rfl fun n hn => by
          rw [actualExteriorDownwardRow, downwardRamanujanRow_sub_interior_eq hc0 hn hgsupp m]
      rw [heq]
      symm
      refine sum_subset (filter_subset _ _) fun n hn hnS => ?_
      have hout : n < N - linearPrimeStrip c := lt_of_not_ge fun h => hnS (mem_filter.mpr ⟨hn, h⟩)
      rw [regroupedExteriorDownwardPrimeRow_eq_zero_small_width hc0 hn hgsupp hw hout m,
        abs_zero, zero_div]
    have hcard_S : (S.card : ℝ) ≤ (Real.exp 1 + 2) * c := by
      have hcontain : S ⊆ Icc (N - linearPrimeStrip c) N := fun n hn =>
        mem_Icc.mpr ⟨(mem_filter.mp hn).2, (mem_Icc.mp (mem_filter.mp hn).1).2⟩
      have hnat : S.card ≤ linearPrimeStrip c + 1 := by
        have h := card_le_card hcontain; rw [Nat.card_Icc] at h; omega
      have h1 : (S.card : ℝ) ≤ (linearPrimeStrip c : ℝ) + 1 := by exact_mod_cast hnat
      nlinarith only [h1, hB_le, hc1]
    have h2B_N : 2 * linearPrimeStrip c ≤ N := by
      have h1 : 2 * (linearPrimeStrip c : ℝ) ≤ (N : ℝ) := by nlinarith only [hB_le, h2BcN, hc0]
      exact_mod_cast h1
    have hinv_sqrt_S : ∀ n ∈ S, 1 / Real.sqrt (n : ℝ) ≤ Real.sqrt 2 / Real.sqrt N := by
      intro n hnS
      have hn1 := (mem_Icc.mp (mem_filter.mp hnS).1).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hn_ge : N ≤ 2 * n := by have := (mem_filter.mp hnS).2; omega
      have hNR : (N : ℝ) / 2 ≤ n := by
        have h : (N : ℝ) ≤ 2 * n := by exact_mod_cast hn_ge
        linarith only [h]
      have hsq := Real.sqrt_le_sqrt hNR
      rw [Real.sqrt_div hN0.le] at hsq
      have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr zero_lt_two
      exact (div_le_div_iff₀ (Real.sqrt_pos.mpr hn0) (Real.sqrt_pos.mpr hN0)).mpr
        (by have := (div_le_iff₀ hs2).mp hsq; linarith only [this])
    have hsum_ext : (∑ n ∈ Icc 1 N, |actualExteriorDownwardRow g N m n| / Real.sqrt n) ≤
        B_ext * (m.totient : ℝ) * c ^ 2 * Real.log N / (N : ℝ) := by
      rw [hrestrict]
      have hpt : ∀ n ∈ S, |regroupedExteriorDownwardPrimeRow g c N m n| / Real.sqrt n ≤
          5 * Real.sqrt 2 * (m.totient : ℝ) * ((Real.exp 1 + 1) * c) * Real.log N / (N : ℝ) := by
        intro n hnS
        rw [div_eq_mul_one_div _ (Real.sqrt n)]
        have h1 := mul_le_mul (hrow_reg n) (hinv_sqrt_S n hnS) (by positivity) (by positivity)
        have h2 : 5 * (m.totient : ℝ) * linearPrimeStrip c * Real.log N / Real.sqrt N *
            (Real.sqrt 2 / Real.sqrt N) =
            5 * Real.sqrt 2 * (m.totient : ℝ) * linearPrimeStrip c * Real.log N / (N : ℝ) := by
          rw [div_mul_div_comm, Real.mul_self_sqrt hN0.le]; ring
        rw [h2] at h1
        refine h1.trans (div_le_div_of_nonneg_right ?_ hN0.le)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hB_le (by positivity)) hL0.le
      calc
        _ ≤ ∑ _n ∈ S,
              5 * Real.sqrt 2 * (m.totient : ℝ) * ((Real.exp 1 + 1) * c) * Real.log N / (N : ℝ) :=
          sum_le_sum hpt
        _ = (S.card : ℝ) *
              (5 * Real.sqrt 2 * (m.totient : ℝ) * ((Real.exp 1 + 1) * c) * Real.log N / (N : ℝ)) := by
          rw [sum_const, nsmul_eq_mul]
        _ ≤ ((Real.exp 1 + 2) * c) *
              (5 * Real.sqrt 2 * (m.totient : ℝ) * ((Real.exp 1 + 1) * c) * Real.log N / (N : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard_S (by positivity)
        _ = B_ext * (m.totient : ℝ) * c ^ 2 * Real.log N / (N : ℝ) := by dsimp only [B_ext]; ring
    have hp := abs_inner_of_coord_eq_div_sqrt_log hl
      (normalizedExteriorDownwardVector φ c N m) (actualExteriorDownwardRow g N m) (fun _ => rfl)
    refine (hp.trans (mul_le_mul_of_nonneg_left hsum_ext (by positivity))).trans_eq ?_
    field_simp [hL0.ne', hN0.ne']
  -- Combine near and exterior pieces and rescale by `(Real.sqrt m.totient)⁻¹`.
  rw [normalizedFullNearGammaDownwardVector_eq_sub hφ hsupp hc0, real_inner_smul_left,
    inner_sub_left, abs_mul, abs_inv, abs_of_pos (Real.sqrt_pos.mpr htot_pos)]
  have htot_div : (Real.sqrt (m.totient : ℝ))⁻¹ * ((m.totient : ℝ) * Real.sqrt l) ≤
      Real.sqrt ((m : ℝ) * l) := by
    have hst : 0 < Real.sqrt (m.totient : ℝ) := Real.sqrt_pos.mpr htot_pos
    have hid : (Real.sqrt (m.totient : ℝ))⁻¹ * (m.totient : ℝ) = Real.sqrt (m.totient : ℝ) := by
      have hsq : Real.sqrt (m.totient : ℝ) * Real.sqrt (m.totient : ℝ) = (m.totient : ℝ) :=
        Real.mul_self_sqrt htot_pos.le
      calc
        (Real.sqrt (m.totient : ℝ))⁻¹ * (m.totient : ℝ) =
            (Real.sqrt (m.totient : ℝ))⁻¹ *
              (Real.sqrt (m.totient : ℝ) * Real.sqrt (m.totient : ℝ)) := by rw [hsq]
        _ = Real.sqrt (m.totient : ℝ) := inv_mul_cancel_left₀ hst.ne' _
    rw [← mul_assoc, hid, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right htot_le (Nat.cast_nonneg l))
  let rate_d := c * (1 + Real.log c) / Real.log N + c ^ 2 / (N : ℝ)
  have hrd1 : c * (1 + Real.log c) / Real.log N ≤ rate_d := le_add_of_nonneg_right (by positivity)
  have hrd2 : c ^ 2 / (N : ℝ) ≤ rate_d := le_add_of_nonneg_left (by positivity)
  have hn' : |⟪normalizedNearGammaDownwardVector φ c N m, normalizedRamanujanHorizonVector l N⟫| ≤
      A_near * ((m.totient : ℝ) * Real.sqrt l) * (1 + Real.log m) * rate_d := by
    refine hnear_bilin.trans ?_
    rw [show A_near * (m.totient : ℝ) * Real.sqrt l * (1 + Real.log m) * c * (1 + Real.log c) /
      Real.log N = A_near * ((m.totient : ℝ) * Real.sqrt l) * (1 + Real.log m) *
        (c * (1 + Real.log c) / Real.log N) by ring]
    exact mul_le_mul_of_nonneg_left hrd1 (by dsimp only [A_near, R₀]; positivity)
  have he' : |⟪normalizedExteriorDownwardVector φ c N m, normalizedRamanujanHorizonVector l N⟫| ≤
      B_ext * ((m.totient : ℝ) * Real.sqrt l) * (1 + Real.log m) * rate_d := by
    refine hext_bilin.trans ?_
    have h1 : B_ext * (m.totient : ℝ) * Real.sqrt l * c ^ 2 / (N : ℝ) =
        B_ext * ((m.totient : ℝ) * Real.sqrt l) * 1 * (c ^ 2 / (N : ℝ)) := by ring
    rw [h1]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1m (by dsimp only [B_ext]; positivity))
      hrd2 (by positivity) (by dsimp only [B_ext]; positivity)
  have hsub := (abs_sub _ _).trans (add_le_add hn' he')
  calc
    (Real.sqrt (m.totient : ℝ))⁻¹ *
        |⟪normalizedNearGammaDownwardVector φ c N m, normalizedRamanujanHorizonVector l N⟫ -
          ⟪normalizedExteriorDownwardVector φ c N m, normalizedRamanujanHorizonVector l N⟫| ≤
      (Real.sqrt (m.totient : ℝ))⁻¹ *
        ((A_near + B_ext) * ((m.totient : ℝ) * Real.sqrt l) * (1 + Real.log m) * rate_d) :=
      mul_le_mul_of_nonneg_left (hsub.trans_eq (by ring)) (by positivity)
    _ = (A_near + B_ext) * ((Real.sqrt (m.totient : ℝ))⁻¹ * ((m.totient : ℝ) * Real.sqrt l)) *
          (1 + Real.log m) * rate_d := by ring
    _ ≤ (A_near + B_ext + 1) * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) * rate_d := by
      refine mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ?_ (by positivity)) (by dsimp only [rate_d]; positivity)
      have hA0 : 0 ≤ A_near + B_ext := by dsimp only [A_near, B_ext, R₀]; positivity
      have hm1 := mul_le_mul_of_nonneg_left htot_div hA0
      linarith only [hm1, Real.sqrt_nonneg ((m : ℝ) * l)]

/-- **Channel 7 (Near-center row):** Vanishing for `N / n ≥ linearNearRowRadius c + 1` and
pointwise `O(√m * c * (1 + log c) / √n)` control on the tail gives
`O(√(m l) * c * (1 + log c)^2 / log N)` via `sum_abs_div_sqrt_le_harmonic_quotient_tail`. -/
private theorem exists_nearCenter_bilinear_bound (φ : ℝ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m l : ℕ, 0 < m → 0 < l → ∀ c : ℝ, 1 ≤ c →
      ∀ N : ℕ, 1 ≤ N → 2 * c ≤ (N : ℝ) →
        |⟪nearCenterVector φ c N m, normalizedRamanujanHorizonVector l N⟫| ≤
          C * Real.sqrt ((m : ℝ) * l) * c * (1 + Real.log c) ^ 2 / Real.log N := by
  let A_nc := |completeWeilPoleShift φ 1| * (1 + Real.exp (1 / 2)) * Real.sqrt (Real.exp 1)
  let C_R1 := 2 + Real.log (2 * Real.exp 2)
  let C_R2 := 2 + Real.log (6 * Real.exp 2)
  have hAnc : 0 ≤ A_nc := by dsimp only [A_nc]; positivity
  have hCR1 : 0 ≤ C_R1 := by
    dsimp only [C_R1]
    have : 0 ≤ Real.log (2 * Real.exp 2) :=
      Real.log_nonneg (by have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2); linarith)
    linarith
  have hCR2 : 0 ≤ C_R2 := by
    dsimp only [C_R2]
    have : 0 ≤ Real.log (6 * Real.exp 2) :=
      Real.log_nonneg (by have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2); linarith)
    linarith
  refine ⟨4 * A_nc * C_R1 * C_R2 + 1, by positivity, ?_⟩
  intro m l hm hl c hc N hN hcN
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : c / N ≤ 1 := (div_le_one hN0).mpr (by linarith only [hcN, hc0])
  let R_c := linearNearRowRadius c
  have hRc_ge1 : 1 ≤ R_c := by
    unfold R_c linearNearRowRadius
    have he2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    nlinarith only [hc, he2]
  have hα : |completeWeilPoleShift φ c| = c * |completeWeilPoleShift φ 1| := by
    have h1 : completeWeilPoleShift φ c = c * completeWeilPoleShift φ 1 := by
      unfold completeWeilPoleShift; ring
    rw [h1, abs_mul, abs_of_pos hc0]
  have hentry : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
      |completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
        normalizedRamanujanMode m j / Real.sqrt j| ≤
        (A_nc * Real.sqrt m * c / Real.sqrt n) * (1 / |(j : ℝ) - n|) := by
    intro n hn j hj
    obtain ⟨hjN, hjn, hlog⟩ := mem_filter.mp hj
    have hn1 := (mem_Icc.mp hn).1
    have hj1 := (mem_Icc.mp hjN).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hnN_R : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hjN_R : (j : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hjN).2
    let y := |Real.log j - Real.log n|
    have hkernel : archimedeanCenterKernel n j = _root_.RHTower.archLevyDensity y := by
      unfold archimedeanCenterKernel
      rw [if_neg (by push Not; exact ⟨Ne.symm hjn, by omega, by omega⟩)]
    have hdist_pos : 0 < |(j : ℝ) - n| :=
      abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hjn))
    have hdist_le_N : |(j : ℝ) - n| ≤ (N : ℝ) := by
      rw [abs_le]; exact ⟨by linarith only [hnN_R, hj0], by linarith only [hjN_R, hn0]⟩
    have hgap : |(j : ℝ) - n| / (N : ℝ) ≤ y := by
      rcases lt_or_gt_of_ne hjn with hlt | hgt
      · have hjlt : (j : ℝ) < n := by exact_mod_cast hlt
        have hlog_le := Real.log_le_sub_one_of_pos (div_pos hj0 hn0)
        rw [Real.log_div hj0.ne' hn0.ne', show (j : ℝ) / n - 1 = -(((n : ℝ) - j) / n) by
          field_simp [hn0.ne']; ring] at hlog_le
        have hsub : ((n : ℝ) - j) / n ≤ Real.log n - Real.log j := by linarith only [hlog_le]
        have hy_eq : y = Real.log n - Real.log j := by
          dsimp only [y]
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hj0 hjlt.le))]
        have habs_eq : |(j : ℝ) - n| = (n : ℝ) - j := by
          rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hjlt)]
        rw [hy_eq, habs_eq]
        exact (div_le_div_of_nonneg_left (sub_pos.mpr hjlt).le hn0 hnN_R).trans hsub
      · have hngt : (n : ℝ) < j := by exact_mod_cast hgt
        have hlog_le := Real.log_le_sub_one_of_pos (div_pos hn0 hj0)
        rw [Real.log_div hn0.ne' hj0.ne', show (n : ℝ) / j - 1 = -(((j : ℝ) - n) / j) by
          field_simp [hj0.ne']; ring] at hlog_le
        have hsub : ((j : ℝ) - n) / j ≤ Real.log j - Real.log n := by linarith only [hlog_le]
        have hy_eq : y = Real.log j - Real.log n := by
          dsimp only [y]
          rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hn0 hngt.le))]
        have habs_eq : |(j : ℝ) - n| = (j : ℝ) - n := abs_of_pos (sub_pos.mpr hngt)
        rw [hy_eq, habs_eq]
        exact (div_le_div_of_nonneg_left (sub_pos.mpr hngt).le hj0 hjN_R).trans hsub
    have hy0 : 0 < y := lt_of_lt_of_le (div_pos hdist_pos hN0) hgap
    have hy1 : y ≤ 1 := hlog.trans ((div_le_one hN0).mpr hcN)
    have hD0 : 0 < _root_.RHTower.archLevyDensity y := _root_.RHTower.archLevyDensity_pos hy0
    have hD_ub : _root_.RHTower.archLevyDensity y ≤
        (1 + Real.exp (1 / 2)) * ((N : ℝ) / |(j : ℝ) - n|) := by
      have h1 := archLevyDensity_le_inv_two_mul_add hy0 hy1
      have h2 : 1 / (2 * y) ≤ (N : ℝ) / (2 * |(j : ℝ) - n|) := by
        have h2gap : 2 * |(j : ℝ) - n| / N ≤ 2 * y := by
          have := mul_le_mul_of_nonneg_left hgap zero_le_two
          rwa [← mul_div_assoc] at this
        exact (one_div_le_one_div_of_le (div_pos (by positivity) hN0) h2gap).trans_eq
          (one_div_div _ _)
      have hNdist1 : 1 ≤ (N : ℝ) / |(j : ℝ) - n| := (one_le_div hdist_pos).mpr hdist_le_N
      have he_le : Real.exp (1 / 2) ≤ Real.exp (1 / 2) * ((N : ℝ) / |(j : ℝ) - n|) :=
        le_mul_of_one_le_right (Real.exp_pos _).le hNdist1
      have hhalf_eq : (N : ℝ) / (2 * |(j : ℝ) - n|) = (1 / 2) * ((N : ℝ) / |(j : ℝ) - n|) := by
        ring
      rw [hhalf_eq] at h2
      linarith only [h1, h2, he_le, hNdist1,
        (by ring : (1 + Real.exp (1 / 2)) * ((N : ℝ) / |(j : ℝ) - n|) =
          (N : ℝ) / |(j : ℝ) - n| + Real.exp (1 / 2) * ((N : ℝ) / |(j : ℝ) - n|)),
        div_nonneg hN0.le hdist_pos.le, Real.exp_pos (1 / 2)]
    have hsqrt_j : 1 / Real.sqrt j ≤ Real.sqrt (Real.exp 1) / Real.sqrt n := by
      have hlog_nj : Real.log n - Real.log j ≤ 1 := by
        have : Real.log n - Real.log j ≤ y := by
          dsimp only [y]; rw [abs_sub_comm]; exact le_abs_self _
        exact this.trans hy1
      have hnj_exp : (n : ℝ) / j ≤ Real.exp 1 := by
        rw [← Real.exp_log (div_pos hn0 hj0), Real.log_div hn0.ne' hj0.ne']
        exact Real.exp_le_exp.mpr hlog_nj
      have hsq_nj : Real.sqrt n ≤ Real.sqrt (Real.exp 1) * Real.sqrt j := by
        have h := Real.sqrt_le_sqrt ((div_le_iff₀ hj0).mp hnj_exp)
        rwa [Real.sqrt_mul (Real.exp_pos 1).le] at h
      exact (div_le_div_iff₀ (Real.sqrt_pos.mpr hj0) (Real.sqrt_pos.mpr hn0)).mpr
        (by linarith only [hsq_nj])
    have hcoef : |completeWeilPoleShift φ c| / N * _root_.RHTower.archLevyDensity y ≤
        |completeWeilPoleShift φ 1| * (1 + Real.exp (1 / 2)) * c * (1 / |(j : ℝ) - n|) := by
      rw [hα]
      calc
        (c * |completeWeilPoleShift φ 1|) / N * _root_.RHTower.archLevyDensity y ≤
            (c * |completeWeilPoleShift φ 1|) / N *
              ((1 + Real.exp (1 / 2)) * ((N : ℝ) / |(j : ℝ) - n|)) :=
          mul_le_mul_of_nonneg_left hD_ub (by positivity)
        _ = |completeWeilPoleShift φ 1| * (1 + Real.exp (1 / 2)) * c * (1 / |(j : ℝ) - n|) := by
          field_simp [hN0.ne']
    rw [hkernel, abs_div, abs_mul, abs_mul, abs_div, abs_of_pos hN0, abs_of_pos hD0,
      abs_of_pos (Real.sqrt_pos.mpr hj0), div_eq_mul_one_div _ (Real.sqrt j),
      mul_assoc (_ * _)]
    have hm_j := mul_le_mul (abs_mode_le_sqrt_conductor_bilin hm j) hsqrt_j
      (by positivity) (Real.sqrt_nonneg m)
    exact (mul_le_mul hcoef hm_j (by positivity) (by positivity)).trans_eq
      (by dsimp only [A_nc]; ring)
  have hsum_dist : ∀ n ∈ Icc 1 N,
      (∑ j ∈ nearRowIndices c N n, 1 / |(j : ℝ) - n|) ≤ 4 * (1 + Real.log R_c) := by
    intro n hn
    let K_fl : ℕ := ⌊R_c⌋₊
    have hK_le : (K_fl : ℝ) ≤ R_c := Nat.floor_le (by positivity)
    have hhar_K : (∑ d ∈ Icc 1 K_fl, 1 / (d : ℝ)) ≤ 2 * (1 + Real.log R_c) := by
      by_cases hK1 : 1 ≤ K_fl
      · have hlogK : Real.log K_fl ≤ Real.log R_c :=
          Real.log_le_log (by exact_mod_cast hK1) hK_le
        have h1R : 0 ≤ Real.log R_c := Real.log_nonneg hRc_ge1
        exact (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log K_fl).trans
          (by linarith only [hlogK, h1R])
      · rw [Icc_eq_empty hK1, sum_empty]
        have : 0 ≤ Real.log R_c := Real.log_nonneg hRc_ge1
        linarith
    let L_set := (nearRowIndices c N n).filter (fun j => j < n)
    let U_set := (nearRowIndices c N n).filter (fun j => n < j)
    have hsplit : (∑ j ∈ nearRowIndices c N n, 1 / |(j : ℝ) - n|) =
        (∑ j ∈ L_set, 1 / |(j : ℝ) - n|) + ∑ j ∈ U_set, 1 / |(j : ℝ) - n| := by
      simp only [L_set, U_set, sum_filter, ← sum_add_distrib]
      refine sum_congr rfl fun j hj => ?_
      have hjn := (mem_filter.mp hj).2.1
      rcases lt_or_gt_of_ne hjn with h | h
      · rw [if_pos h, if_neg (not_lt_of_ge h.le), add_zero]
      · rw [if_neg (not_lt_of_ge h.le), if_pos h, zero_add]
    have hL : (∑ j ∈ L_set, 1 / |(j : ℝ) - n|) ≤ 2 * (1 + Real.log R_c) := by
      have hinj : ∀ i ∈ L_set, ∀ j ∈ L_set, n - i = n - j → i = j := by
        intro i hi j hj hij
        have := (mem_filter.mp hi).2; have := (mem_filter.mp hj).2
        change n - i = n - j at hij; omega
      have hmap : (∑ j ∈ L_set, 1 / |(j : ℝ) - n|) =
          ∑ d ∈ L_set.image (fun j => n - j), 1 / (d : ℝ) := by
        rw [sum_image hinj]
        refine sum_congr rfl fun j hj => ?_
        have hlt := (mem_filter.mp hj).2
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
          Nat.cast_sub hlt.le]
      have hsub : L_set.image (fun j => n - j) ⊆ Icc 1 K_fl := by
        intro d hd
        obtain ⟨j, hjL, rfl⟩ := mem_image.mp hd
        obtain ⟨hj, hlt⟩ := mem_filter.mp hjL
        have hrad := (nearRow_geometry_small_width hc0 hn hj hw).1
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
          ← Nat.cast_sub hlt.le] at hrad
        exact mem_Icc.mpr ⟨by omega, Nat.le_floor hrad⟩
      rw [hmap]
      exact (sum_le_sum_of_subset_of_nonneg (f := fun d : ℕ => 1 / (d : ℝ))
        hsub (fun _ _ _ => by positivity)).trans hhar_K
    have hU : (∑ j ∈ U_set, 1 / |(j : ℝ) - n|) ≤ 2 * (1 + Real.log R_c) := by
      have hinj : ∀ i ∈ U_set, ∀ j ∈ U_set, i - n = j - n → i = j := by
        intro i hi j hj hij
        have := (mem_filter.mp hi).2; have := (mem_filter.mp hj).2
        change i - n = j - n at hij; omega
      have hmap : (∑ j ∈ U_set, 1 / |(j : ℝ) - n|) =
          ∑ d ∈ U_set.image (fun j => j - n), 1 / (d : ℝ) := by
        rw [sum_image hinj]
        refine sum_congr rfl fun j hj => ?_
        have hlt := (mem_filter.mp hj).2
        rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)), Nat.cast_sub hlt.le]
      have hsub : U_set.image (fun j => j - n) ⊆ Icc 1 K_fl := by
        intro d hd
        obtain ⟨j, hjU, rfl⟩ := mem_image.mp hd
        obtain ⟨hj, hlt⟩ := mem_filter.mp hjU
        have hrad := (nearRow_geometry_small_width hc0 hn hj hw).1
        rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
          ← Nat.cast_sub hlt.le] at hrad
        exact mem_Icc.mpr ⟨by omega, Nat.le_floor hrad⟩
      rw [hmap]
      exact (sum_le_sum_of_subset_of_nonneg (f := fun d : ℕ => 1 / (d : ℝ))
        hsub (fun _ _ _ => by positivity)).trans hhar_K
    rw [hsplit]; linarith only [hL, hU]
  let row_nc : ℕ → ℝ := fun n => ∑ j ∈ nearRowIndices c N n,
    completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
      normalizedRamanujanMode m j / Real.sqrt j
  let B_nc := 4 * A_nc * Real.sqrt m * c * (1 + Real.log R_c)
  have hB0 : 0 ≤ B_nc := by
    dsimp only [B_nc]; have : 0 ≤ Real.log R_c := Real.log_nonneg hRc_ge1; positivity
  have hglobal : ∀ n ∈ Icc 1 N, |row_nc n| ≤ B_nc / Real.sqrt n := by
    intro n hn
    calc
      |row_nc n| ≤ ∑ j ∈ nearRowIndices c N n,
          |completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
            normalizedRamanujanMode m j / Real.sqrt j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ nearRowIndices c N n,
          (A_nc * Real.sqrt m * c / Real.sqrt n) * (1 / |(j : ℝ) - n|) :=
        sum_le_sum (hentry n hn)
      _ = (A_nc * Real.sqrt m * c / Real.sqrt n) *
          ∑ j ∈ nearRowIndices c N n, 1 / |(j : ℝ) - n| := (mul_sum _ _ _).symm
      _ ≤ (A_nc * Real.sqrt m * c / Real.sqrt n) * (4 * (1 + Real.log R_c)) :=
        mul_le_mul_of_nonneg_left (hsum_dist n hn) (by positivity)
      _ = B_nc / Real.sqrt n := by dsimp only [B_nc]; ring
  have hgood : ∀ n ∈ Icc 1 N, R_c + 1 ≤ (N : ℝ) / n → |row_nc n| ≤ 0 / Real.sqrt n := by
    intro n hn hquot
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hemp : nearRowIndices c N n = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      have hle := (nearRow_geometry_small_width hc0 hn hj hw).2.1
      have hq_le : (N : ℝ) / n ≤ R_c := (div_le_iff₀ hn0).mpr hle
      linarith only [hquot, hq_le]
    dsimp only [row_nc]; rw [hemp, sum_empty, abs_zero, zero_div]
  have htail := sum_abs_div_sqrt_le_harmonic_quotient_tail hN
    (show 1 ≤ R_c + 1 by linarith only [hRc_ge1]) le_rfl hB0 row_nc hglobal hgood
  have hlogRc : 1 + Real.log R_c ≤ C_R1 * (1 + Real.log c) := by
    have heq : R_c = (2 * Real.exp 2) * c := by unfold R_c linearNearRowRadius; ring
    rw [heq, Real.log_mul (by positivity) hc0.ne']
    have hlogc0 := Real.log_nonneg hc
    have hlog2e : 0 ≤ Real.log (2 * Real.exp 2) :=
      Real.log_nonneg (by have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2); linarith)
    dsimp only [C_R1]; nlinarith only [hlogc0, hlog2e]
  have hlog2T : 1 + Real.log (2 * (R_c + 1)) ≤ C_R2 * (1 + Real.log c) := by
    have h2T_le : 2 * (R_c + 1) ≤ (6 * Real.exp 2) * c := by
      unfold R_c linearNearRowRadius
      have he2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      nlinarith only [hc, he2]
    have hl1 := Real.log_le_log (by positivity) h2T_le
    rw [Real.log_mul (by positivity) hc0.ne'] at hl1
    have hlogc0 := Real.log_nonneg hc
    have hlog6e : 0 ≤ Real.log (6 * Real.exp 2) :=
      Real.log_nonneg (by have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2); linarith)
    dsimp only [C_R2]; nlinarith only [hl1, hlogc0, hlog6e]
  have hsum_nc : (∑ n ∈ Icc 1 N, |row_nc n| / Real.sqrt n) ≤
      (4 * A_nc * C_R1 * C_R2 + 1) * Real.sqrt m * c * (1 + Real.log c) ^ 2 := by
    have hB_le : B_nc ≤ 4 * A_nc * Real.sqrt m * c * (C_R1 * (1 + Real.log c)) :=
      mul_le_mul_of_nonneg_left hlogRc (by positivity)
    have hlogc0 := Real.log_nonneg hc
    calc
      _ ≤ 0 * (1 + Real.log N) + B_nc * (1 + Real.log (2 * (R_c + 1))) := htail
      _ = B_nc * (1 + Real.log (2 * (R_c + 1))) := by ring
      _ ≤ (4 * A_nc * Real.sqrt m * c * (C_R1 * (1 + Real.log c))) *
            (C_R2 * (1 + Real.log c)) :=
        mul_le_mul hB_le hlog2T
          (by linarith [Real.log_nonneg (show 1 ≤ 2 * (R_c + 1) by linarith)]) (by positivity)
      _ = (4 * A_nc * C_R1 * C_R2) * Real.sqrt m * c * (1 + Real.log c) ^ 2 := by ring
      _ ≤ (4 * A_nc * C_R1 * C_R2 + 1) * Real.sqrt m * c * (1 + Real.log c) ^ 2 := by
        have hnn : 0 ≤ Real.sqrt m * c * (1 + Real.log c) ^ 2 := by positivity
        linarith only [hnn]
  have hp := abs_inner_of_coord_eq_div_sqrt_log hl (nearCenterVector φ c N m) row_nc (fun _ => rfl)
  refine (hp.trans (mul_le_mul_of_nonneg_left hsum_nc (by positivity))).trans_eq ?_
  rw [Real.sqrt_mul (Nat.cast_nonneg m)]; ring



/-- Shifted reciprocal upward error paired in `L¹` via `sum_abs_div_sqrt_le_harmonic_quotient_tail`,
giving `O(φ(m) * c * (1 + log c) * (log N)^(1/k))`. -/
private theorem exists_shiftedReciprocal_l1_variable_rate
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → ∀ shift : ℕ → ℕ,
        (∑ n ∈ Icc 1 N, |shiftedReciprocalUpwardRowError φ c shift N m n| / Real.sqrt n) ≤
          K * (m.totient : ℝ) * c * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) := by
  obtain ⟨C, hC, hsource⟩ :=
    exists_conductor_uniform_affineShellCorrection_linear_log_rate hφ hsupp hM
  let D : ℝ := 4 * (Real.log 4 + 4)
  have hD : 0 ≤ D := by
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [D]; positivity
  let K := 2 * C + 5 * D + 1
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro A hA k hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hYlim : Tendsto (fun N : ℕ => Real.exp (Real.log N ^ (1 / (k : ℝ)))) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / (k : ℝ))).comp hloglim)
  filter_upwards [hYlim.eventually (hsource (A * k) (by positivity) k),
    hloglim.eventually_ge_atTop 1, eventually_ge_atTop 1] with N hsourceN hL hN
  intro m hm hmN c hc shift
  let L := Real.log (N : ℝ)
  let Y := Real.exp (L ^ (1 / (k : ℝ)))
  let T := 2 * c * Y
  let a := C * c / L
  let b := D * (m.totient : ℝ) * c
  have hL1 : 1 ≤ L := hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have h1c : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc]
  have htot : (1 : ℝ) ≤ m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hs1 : 1 ≤ L ^ (1 / (k : ℝ)) := Real.one_le_rpow hL1 (by positivity)
  have hs0 : 0 < L ^ (1 / (k : ℝ)) := Real.rpow_pos_of_pos hL0 _
  have hsPow : (L ^ (1 / (k : ℝ))) ^ k = L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, one_div_mul_cancel hkR.ne', Real.rpow_one]
  have hY1 : 1 ≤ Y := Real.one_le_exp_iff.mpr hs0.le
  have hT : 1 ≤ T := by dsimp only [T]; nlinarith only [hc, hY1]
  have hmY : (m : ℝ) ≤ Real.log Y ^ (A * k) := by
    dsimp only [Y]
    rw [Real.log_exp, ← Real.rpow_mul hL0.le]
    have heq : (1 / (k : ℝ)) * (A * k) = A := by field_simp [hkR.ne']
    rw [heq]; exact hmN
  have hglobal : ∀ n ∈ Icc 1 N,
      |shiftedReciprocalUpwardRowError φ c shift N m n| ≤ b / Real.sqrt n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    have hquot : 1 ≤ (N : ℝ) / n := (le_div_iff₀ hn0).mpr (by simpa only [one_mul] using hnN)
    rw [shiftedReciprocalUpwardRowError, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    exact div_le_div_of_nonneg_right
      (abs_affineShellCorrection_error_le_linear hm hφ hsupp hM n shift hc0 hquot)
      (Real.sqrt_nonneg _)
  have hgood : ∀ n ∈ Icc 1 N, T ≤ (N : ℝ) / n →
      |shiftedReciprocalUpwardRowError φ c shift N m n| ≤ a / Real.sqrt n := by
    intro n _ ht
    have hb := hsourceN.2 m hm hmY c ((N : ℝ) / n) hc ht shift n
    change |affinePrimeShellCorrectionOfShift m n shift φ c ((N : ℝ) / n) -
      ramanujanLagCoefficient m n * shellCorrectionOfShift φ c m shift| ≤
        C * c / Real.log Y ^ k at hb
    rw [show Real.log Y = L ^ (1 / (k : ℝ)) by exact Real.log_exp _, hsPow] at hb
    rw [shiftedReciprocalUpwardRowError, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
    exact div_le_div_of_nonneg_right hb (Real.sqrt_nonneg _)
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have hsum := sum_abs_div_sqrt_le_harmonic_quotient_tail hN hT ha0 hb0
    (shiftedReciprocalUpwardRowError φ c shift N m) hglobal hgood
  have hhead : a * (1 + L) ≤
      2 * C * (m.totient : ℝ) * c * (1 + Real.log c) * (L ^ (1 / (k : ℝ))) := by
    have hfrac : (1 + L) / L ≤ 2 := (div_le_iff₀ hL0).mpr (by linarith only [hL1])
    have hprod1 : (1 : ℝ) ≤ (m.totient : ℝ) * (1 + Real.log c) * (L ^ (1 / (k : ℝ))) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le htot h1c) hs1
    calc
      a * (1 + L) = C * c * ((1 + L) / L) := by dsimp only [a]; ring
      _ ≤ 2 * C * c := by
        have h := mul_le_mul_of_nonneg_left hfrac (show 0 ≤ C * c by positivity)
        nlinarith only [h]
      _ ≤ (2 * C * c) * ((m.totient : ℝ) * (1 + Real.log c) * (L ^ (1 / (k : ℝ)))) :=
        le_mul_of_one_le_right (by positivity) hprod1
      _ = _ := by ring
  have hlogT : 1 + Real.log (2 * T) ≤ 5 * (1 + Real.log c) * (L ^ (1 / (k : ℝ))) := by
    have hid : 2 * T = 4 * c * Real.exp (L ^ (1 / (k : ℝ))) := by dsimp only [T, Y]; ring
    rw [hid, Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_mul (by norm_num) hc0.ne', Real.log_exp]
    have hl4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
    have hlogc0 := Real.log_nonneg hc
    nlinarith only [hl4, hlogc0, h1c, hs1]
  have htail : b * (1 + Real.log (2 * T)) ≤
      5 * D * (m.totient : ℝ) * c * (1 + Real.log c) * (L ^ (1 / (k : ℝ))) := by
    calc
      b * (1 + Real.log (2 * T)) ≤ b * (5 * (1 + Real.log c) * (L ^ (1 / (k : ℝ)))) :=
        mul_le_mul_of_nonneg_left hlogT hb0
      _ = _ := by dsimp only [b]; ring
  have hraw := hsum.trans (add_le_add hhead htail)
  have hextra : 0 ≤ (m.totient : ℝ) * c * (1 + Real.log c) * (L ^ (1 / (k : ℝ))) := by positivity
  dsimp only [K]
  linarith only [hraw, hextra,
    (by ring : (2 * C + 5 * D + 1) * (m.totient : ℝ) * c *
      (1 + Real.log c) * (L ^ (1 / (k : ℝ))) =
      2 * C * (m.totient : ℝ) * c * (1 + Real.log c) * (L ^ (1 / (k : ℝ))) +
        5 * D * (m.totient : ℝ) * c * (1 + Real.log c) * (L ^ (1 / (k : ℝ))) +
        (m.totient : ℝ) * c * (1 + Real.log c) * (L ^ (1 / (k : ℝ))))]

/-- **Channel 8 (Upward prime source):** Splitting `actualUpwardRowError = a + b + r` into
logarithmic-minus-linearized (`L^2` Cauchy–Schwarz `O(c^5 log N / N)`), linearized-minus-reciprocal
(`L¹` split at `linearPrimeStrip c` giving `O(c / log N + c^3 / N)`), and reciprocal-minus-shell
(`L¹` quotient-harmonic bound `O(c * (1 + log c) * (log N)^(1/k) / log N)`) yields the linear-in-`c`
bilinear upward rate. -/
private theorem exists_upward_bilinear_variable_rate {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ l : ℕ, 0 < l →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        |⟪upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
            shellCorrection φ c m • normalizedRamanujanHorizonVector m N,
          normalizedRamanujanHorizonVector l N⟫| ≤
          K * Real.sqrt ((m : ℝ) * l) *
            (c * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
              c ^ 5 * Real.log N / (N : ℝ)) := by
  obtain ⟨Ca, hCa, ha⟩ := exists_logarithmicUpward_uniform_conductor_harmonic_bound hφ hsupp hM
  obtain ⟨Cs, hCs, hs⟩ := exists_shiftedReciprocal_l1_variable_rate hφ hsupp hM
  let d : ℝ := Real.exp 1 + 2
  let Ca' := 2 * Real.sqrt (Ca * d ^ 6)
  let Cb₁ := 48 * Real.sqrt 2 * d
  let Cb₂ := 64 * d ^ 3
  let K := Ca' + Cb₁ + Cb₂ + Cs + 1
  refine ⟨K, by dsimp only [K, Ca', Cb₁, Cb₂, d]; positivity, fun A hA k hk => ?_⟩
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hs A hA k hk, eventually_ge_atTop 1, hloglim.eventually_ge_atTop 1]
    with N hsource hN hlog
  intro m hm hmN l hl c hc hlarge
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have h1c : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc]
  have hs1 : 1 ≤ Real.log (N : ℝ) ^ (1 / (k : ℝ)) := Real.one_le_rpow hlog (by positivity)
  have htot_pos : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have htot_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  let B := linearPrimeStrip c
  have hBc : (B : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc
  have hB1 : (B : ℝ) + 1 ≤ d * c := by dsimp only [d]; nlinarith only [hBc, hc]
  have hBd : (B : ℝ) ≤ d * c := by linarith only [hB1]
  have hc2 : c ≤ c ^ 2 := by nlinarith only [hc]
  have hexp := Real.exp_pos 1
  have hwidth : c / N ≤ 1 := by
    apply (div_le_one hN0).mpr
    have hcoef : 1 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [hlarge, hc2, h]
  have hcN : c ≤ (N : ℝ) := (div_le_one hN0).mp hwidth
  have h2BN : 2 * B ≤ N := by
    have hcoef : 2 * (Real.exp 1 + 1) ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h1 := mul_le_mul_of_nonneg_left hc2 (show 0 ≤ 2 * (Real.exp 1 + 1) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    have h : 2 * (B : ℝ) ≤ N := by nlinarith only [hBc, h1, h2, hlarge]
    exact_mod_cast h
  have hBN : B ≤ N := by omega
  have hkernel : 2 * ((Real.exp 1 + 3) * c) * B ≤ (N : ℝ) := by
    have hcoef : 2 * (Real.exp 1 + 3) * (Real.exp 1 + 1) ≤
        4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h1 := mul_le_mul_of_nonneg_left hBc
      (show 0 ≤ 2 * ((Real.exp 1 + 3) * c) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [h1, h2, hlarge]
  have hB : ⌈c⌉₊ ≤ B := by
    apply Nat.ceil_le.mpr
    have h := mul_le_mul_of_nonneg_left
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)) hc0.le
    have hce : c ≤ c * Real.exp 1 := by simpa only [mul_one] using h
    exact hce.trans (Nat.le_ceil _)
  let rate_u := c * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
    c ^ 5 * Real.log N / (N : ℝ)
  have hru0 : 0 ≤ rate_u := by dsimp only [rate_u]; positivity
  have hru1 : c / Real.log N ≤ rate_u := by
    have hprod1 : 1 ≤ (1 + Real.log c) * Real.log (N : ℝ) ^ (1 / (k : ℝ)) :=
      one_le_mul_of_one_le_of_one_le h1c hs1
    have hle : c ≤ c * ((1 + Real.log c) * Real.log (N : ℝ) ^ (1 / (k : ℝ))) :=
      le_mul_of_one_le_right hc0.le hprod1
    exact ((div_le_div_of_nonneg_right hle hL0.le).trans_eq (by ring)).trans
      (le_add_of_nonneg_right (by positivity))
  have hru2 : c ^ 5 * Real.log N / (N : ℝ) ≤ rate_u := le_add_of_nonneg_left (by positivity)
  have hru3 : c * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) / Real.log N ≤ rate_u :=
    le_add_of_nonneg_right (by positivity)
  let a : ℕ → ℝ := fun n =>
    (logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) / Real.sqrt n
  let b : ℕ → ℝ := fun n =>
    (linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n
  let r : ℕ → ℝ := fun n =>
    (reciprocalUpwardCoefficient φ c B N m n -
      ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n
  let u_a : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    WithLp.toLp 2 (fun n => a n / Real.sqrt (Real.log N))
  let u_br : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    WithLp.toLp 2 (fun n => (b n + r n) / Real.sqrt (Real.log N))
  have hvec_split : normalizedUpwardPrimeResidual φ c N m = u_a + u_br := by
    ext n
    have hn : (n : ℕ) ∈ Icc 1 N := n.2
    have hsqrt : Real.sqrt (n : ℕ) ≠ 0 := (Real.sqrt_pos.mpr
      (by exact_mod_cast (mem_Icc.mp hn).1 : (0 : ℝ) < (n : ℕ))).ne'
    have hu : upwardPrimeRow (atomDilate φ (c / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
          (∫ u, atomDilate φ (c / N) u ^ 2) =
        logarithmicUpwardCoefficient φ c B N m n / Real.sqrt (n : ℕ) := by
      apply (eq_div_iff hsqrt).mpr
      simpa only [mul_comm] using sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient_small_width
        hsupp hc0 hn hwidth m
    change actualUpwardRowError φ c N m n / Real.sqrt (Real.log N) =
      a n / Real.sqrt (Real.log N) + (b n + r n) / Real.sqrt (Real.log N)
    rw [actualUpwardRowError, hu]
    dsimp only [a, b, r]; ring
  -- Part (a): Cauchy–Schwarz on `u_a`.
  have ha_bilin : |⟪u_a, normalizedRamanujanHorizonVector l N⟫| ≤
      Ca' * ((m.totient : ℝ) * Real.sqrt l) * rate_u := by
    have hnorm_ua : ‖u_a‖ ≤ Real.sqrt (Ca * d ^ 6) * (m.totient : ℝ) * c ^ 5 * (Real.log N / N) := by
      have hp := pow_le_pow_left₀ (show 0 ≤ (B : ℝ) + 1 by positivity) hB1 6
      have hb := (ha m N hN hlog c hc hwidth B hBN hkernel).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (show 0 ≤ Ca * (m.totient : ℝ) ^ 2 * c ^ 4 by positivity))
          (sq_nonneg (Real.log (N : ℝ) / N)))
      have hua_sq_eq : ‖u_a‖ ^ 2 = (∑ n ∈ Icc 1 N, a n ^ 2) / Real.log N := by
        rw [EuclideanSpace.real_norm_sq_eq]
        change (∑ n : PrimeHorizonIndex N, (a n / Real.sqrt (Real.log N)) ^ 2) = _
        simp only [div_pow, Real.sq_sqrt hL0.le]
        rw [← sum_div]
        congr 1
        exact sum_coe_sort (Icc 1 N) (fun n => a n ^ 2)
      have hsq : ‖u_a‖ ^ 2 ≤
          (Real.sqrt (Ca * d ^ 6) * (m.totient : ℝ) * c ^ 5 * (Real.log N / N)) ^ 2 := by
        rw [hua_sq_eq]
        refine hb.trans_eq ?_
        have hcd : (Real.sqrt (Ca * d ^ 6)) ^ 2 = Ca * d ^ 6 :=
          Real.sq_sqrt (by dsimp only [d]; positivity)
        calc
          Ca * (m.totient : ℝ) ^ 2 * c ^ 4 * (d * c) ^ 6 * (Real.log N / N) ^ 2 =
              (Ca * d ^ 6) * (m.totient : ℝ) ^ 2 * c ^ 10 * (Real.log N / N) ^ 2 := by ring
          _ = (Real.sqrt (Ca * d ^ 6)) ^ 2 * (m.totient : ℝ) ^ 2 * c ^ 10 *
                (Real.log N / N) ^ 2 := by rw [hcd]
          _ = (Real.sqrt (Ca * d ^ 6) * (m.totient : ℝ) * c ^ 5 * (Real.log N / N)) ^ 2 := by ring
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h
    have hnorm_vl : ‖normalizedRamanujanHorizonVector l N‖ ≤ 2 * Real.sqrt l := by
      have hsq : ‖normalizedRamanujanHorizonVector l N‖ ^ 2 ≤ (2 * Real.sqrt l) ^ 2 :=
        (norm_sq_normalizedRamanujanHorizonVector_le hl hlog).trans
          (by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg l)]; linarith [Nat.cast_nonneg (α := ℝ) l])
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h
    calc
      |⟪u_a, normalizedRamanujanHorizonVector l N⟫| ≤
          ‖u_a‖ * ‖normalizedRamanujanHorizonVector l N‖ := abs_real_inner_le_norm _ _
      _ ≤ (Real.sqrt (Ca * d ^ 6) * (m.totient : ℝ) * c ^ 5 * (Real.log N / N)) *
            (2 * Real.sqrt l) :=
        mul_le_mul hnorm_ua hnorm_vl (norm_nonneg _) (by positivity)
      _ = Ca' * ((m.totient : ℝ) * Real.sqrt l) * (c ^ 5 * Real.log N / (N : ℝ)) := by
        dsimp only [Ca']; ring
      _ ≤ Ca' * ((m.totient : ℝ) * Real.sqrt l) * rate_u :=
        mul_le_mul_of_nonneg_left hru2 (by dsimp only [Ca']; positivity)
  -- Part (b): `L¹` boundary split on `b`.
  have hb_l1 : (∑ n ∈ Icc 1 N, |b n| / Real.sqrt n) ≤
      Cb₁ * (m.totient : ℝ) * c + Cb₂ * (m.totient : ℝ) * c ^ 3 * Real.log N / (N : ℝ) := by
    let S_ex : ℕ → Finset ℕ := fun n =>
      (Icc 1 (N + B)).filter (fun k => N ≤ k * n + B ∧ k * n ≤ N + B)
    have hrow_ex : ∀ n ∈ Icc 1 N,
        |linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n| ≤
          4 * (B : ℝ) * m.totient * ∑ k ∈ S_ex n, (ArithmeticFunction.vonMangoldt k : ℝ) / k := by
      intro n hn
      have hn1 := (mem_Icc.mp hn).1
      let L_val := 4 * (B : ℝ) * (∫ u, φ u ^ 2) * m.totient
      have hpoint : ∀ k ∈ Icc 1 (N + B),
          |∑ h ∈ Icc 1 B, (linearizedUpwardOffset φ c N m n k h -
              reciprocalUpwardOffset φ c N m n k h)| ≤
            if N ≤ k * n + B ∧ k * n ≤ N + B then L_val else 0 := by
        intro k hk
        have hk1 := (mem_Icc.mp hk).1
        have hT : 1 ≤ k * n := Nat.mul_pos hk1 hn1
        by_cases hex : N ≤ k * n + B ∧ k * n ≤ N + B
        · rw [if_pos hex]
          have h := (abs_sum_le_sum_abs _ (Icc 1 B)).trans
            (sum_le_sum fun h _ => abs_linearizedUpwardOffset_sub_reciprocal_le hφ hsupp c N m n k h)
          refine h.trans_eq ?_
          simp only [L_val, sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
          ring
        · rw [if_neg hex]
          have hz : (∑ h ∈ Icc 1 B, (linearizedUpwardOffset φ c N m n k h -
              reciprocalUpwardOffset φ c N m n k h)) = 0 := by
            refine sum_eq_zero fun h hh => ?_
            have hhB := (mem_Icc.mp hh).2
            by_cases hhT : h < k * n
            · have hfar : k * n + B < N ∨ N + B < k * n := by omega
              rcases hfar with hfar | hfar
              · have hp : k * n + h ≤ N := by omega
                have hncut : h < k * n ∧ k * n - h ≤ N := ⟨hhT, by omega⟩
                have hkcut : k * n ≤ N := by omega
                simp only [linearizedUpwardOffset, reciprocalUpwardOffset, if_pos hp, if_pos hncut,
                  if_pos hkcut, ramanujanLagCoefficient_sub_eq_reflected hm hhT.le, sub_self]
              · have hp : ¬ k * n + h ≤ N := by omega
                have hncut : ¬ (h < k * n ∧ k * n - h ≤ N) := by omega
                have hkcut : ¬ k * n ≤ N := by omega
                simp only [linearizedUpwardOffset, reciprocalUpwardOffset, if_neg hp, if_neg hncut,
                  if_neg hkcut, add_zero, sub_self]
            · have hT0 : (0 : ℝ) < (k * n : ℕ) := by exact_mod_cast hT
              have hNc : (1 : ℝ) ≤ (N : ℝ) / c := (one_le_div hc0).mpr hcN
              have hhT' : (1 : ℝ) ≤ (h : ℝ) / (k * n : ℕ) :=
                (one_le_div hT0).mpr (by exact_mod_cast (show k * n ≤ h by omega))
              have hzero := shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
                ((one_le_mul_of_one_le_of_one_le hNc hhT').trans (le_abs_self _))
              simp only [linearizedUpwardOffset, reciprocalUpwardOffset, hzero, mul_zero, sub_self]
          rw [hz, abs_zero]
      unfold linearizedUpwardCoefficient reciprocalUpwardCoefficient
      rw [← mul_sub, ← sum_sub_distrib, abs_mul, abs_of_pos (one_div_pos.mpr hM)]
      calc
        1 / (∫ u, φ u ^ 2) * |∑ k ∈ Icc 1 (N + B),
            ((ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, linearizedUpwardOffset φ c N m n k h -
              (ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, reciprocalUpwardOffset φ c N m n k h)| ≤
          1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B),
            |(ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, linearizedUpwardOffset φ c N m n k h -
              (ArithmeticFunction.vonMangoldt k : ℝ) / k * ∑ h ∈ Icc 1 B, reciprocalUpwardOffset φ c N m n k h| :=
          mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
        _ ≤ 1 / (∫ u, φ u ^ 2) * ∑ k ∈ Icc 1 (N + B),
            if N ≤ k * n + B ∧ k * n ≤ N + B then
              (ArithmeticFunction.vonMangoldt k : ℝ) / k * L_val else 0 := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun k hk => ?_) (by positivity)
          rw [← mul_sub, ← sum_sub_distrib, abs_mul,
            abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))]
          have hpk := hpoint k hk
          split_ifs at hpk ⊢
          · exact mul_le_mul_of_nonneg_left hpk (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
          · simpa only [mul_zero] using mul_le_mul_of_nonneg_left hpk
              (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k))
        _ = 4 * (B : ℝ) * m.totient * ∑ k ∈ S_ex n, (ArithmeticFunction.vonMangoldt k : ℝ) / k := by
          dsimp only [S_ex, L_val]
          rw [← sum_filter, ← sum_mul]
          field_simp [hM.ne']
    have hS_sub : ∀ n : ℕ, 1 ≤ n → S_ex n ⊆ Icc ((N - B) / n) ((N + B) / n) := by
      intro n hn1 k hk
      obtain ⟨_, hlo, hhi⟩ := mem_filter.mp hk
      have ha' : (N - B) / n ≤ k :=
        (Nat.div_le_div_right (show N - B ≤ k * n by omega)).trans_eq
          (Nat.mul_div_cancel k (by omega))
      have hb' : k ≤ (N + B) / n :=
        (Nat.mul_div_cancel k (by omega)).symm.trans_le (Nat.div_le_div_right hhi)
      exact mem_Icc.mpr ⟨ha', hb'⟩
    have hcard_mul : ∀ n : ℕ, 1 ≤ n → ((S_ex n).card : ℝ) * n ≤ 2 * (B : ℝ) + 2 * n := by
      intro n hn1
      let a₀ := (N - B) / n
      let b₀ := (N + B) / n
      have hcard_le : (S_ex n).card ≤ (Icc a₀ b₀).card := card_le_card (hS_sub n hn1)
      by_cases hab : a₀ ≤ b₀
      · have hdiv_lo : N - B < (a₀ + 1) * n := by
          have h1 := Nat.div_add_mod (N - B) n
          have h2 := Nat.mod_lt (N - B) (show 0 < n by omega)
          dsimp only [a₀]
          nlinarith only [h1, h2, Nat.mul_comm n ((N - B) / n)]
        have hdiv_lo' : N - B < a₀ * n + n := by simpa only [Nat.add_mul, one_mul] using hdiv_lo
        have hdiv_hi : b₀ * n ≤ N + B := Nat.div_mul_le_self (N + B) n
        have hnat : (b₀ + 1 - a₀) * n ≤ 2 * B + 2 * n := by
          have hsub_mul : (b₀ + 1 - a₀) * n = b₀ * n + n - a₀ * n := by
            rw [Nat.sub_mul, Nat.add_mul, one_mul]
          omega
        have h1 : (S_ex n).card * n ≤ 2 * B + 2 * n := by
          have hc_eq : (Icc a₀ b₀).card = b₀ + 1 - a₀ := Nat.card_Icc a₀ b₀
          exact (Nat.mul_le_mul_right n (hcard_le.trans_eq hc_eq)).trans hnat
        exact_mod_cast h1
      · have hemp : Icc a₀ b₀ = ∅ := Icc_eq_empty hab
        rw [hemp, card_empty] at hcard_le
        have h0 : (S_ex n).card = 0 := Nat.eq_zero_of_le_zero hcard_le
        rw [h0, Nat.cast_zero, zero_mul]; positivity
    have hpart : Icc 1 N = Icc 1 B ∪ Ioc B N := by
      ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
    have hdisj : Disjoint (Icc 1 B) (Ioc B N) := by
      rw [Finset.disjoint_left]; intro n h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
    rw [hpart, sum_union hdisj]
    have hhigh : (∑ n ∈ Ioc B N, |b n| / Real.sqrt n) ≤ Cb₁ * (m.totient : ℝ) * c := by
      have hpt : ∀ n ∈ Ioc B N, |b n| ≤ 24 * Real.sqrt 2 * (m.totient : ℝ) * B / Real.sqrt N := by
        intro n hn
        obtain ⟨hBn, hnN⟩ := mem_Ioc.mp hn
        have hn1 : 1 ≤ n := by omega
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
        have hcard3 : ((S_ex n).card : ℝ) ≤ 3 := by
          have hm_c := hcard_mul n hn1
          have hBn_R : (B : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hBn)
          have hlt4 : ((S_ex n).card : ℝ) * n < 4 * (n : ℝ) := by nlinarith only [hm_c, hBn_R]
          have hnat4 : (S_ex n).card < 4 := by
            have : ((S_ex n).card : ℝ) < 4 := by nlinarith only [hlt4, hn0]
            exact_mod_cast this
          exact_mod_cast (show (S_ex n).card ≤ 3 by omega)
        have hterm_k : ∀ k ∈ S_ex n,
            (ArithmeticFunction.vonMangoldt k : ℝ) / k ≤ 2 * Real.sqrt (2 * (n : ℝ) / N) := by
          intro k hk
          obtain ⟨hkI, hlo, _⟩ := mem_filter.mp hk
          have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hkI).1
          have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1
          have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
          have hN_2kn : (N : ℝ) ≤ 2 * (k : ℝ) * n := by
            have hkn : N ≤ k * n + k * n := by omega
            have hknR : (N : ℝ) ≤ (k : ℝ) * n + (k : ℝ) * n := by exact_mod_cast hkn
            linarith only [hknR]
          have hinv_k : 1 / (k : ℝ) ≤ 2 * (n : ℝ) / N := by
            rw [div_le_div_iff₀ hk0 hN0, one_mul]; linarith only [hN_2kn]
          have hinv_sk : 1 / Real.sqrt k ≤ Real.sqrt (2 * (n : ℝ) / N) := by
            have h := Real.sqrt_le_sqrt hinv_k
            rwa [Real.sqrt_div zero_le_one, Real.sqrt_one] at h
          have hlog_sk : Real.log k ≤ 2 * Real.sqrt k := by
            have h1 := Real.log_le_sub_one_of_pos hsk
            have h2 : 2 * Real.log (Real.sqrt k) = Real.log k := by
              rw [show 2 * Real.log (Real.sqrt k) = Real.log (Real.sqrt k ^ 2) by
                rw [Real.log_pow]; ring, Real.sq_sqrt hk0.le]
            linarith only [h1, h2]
          have hvm : (ArithmeticFunction.vonMangoldt k : ℝ) / k ≤ 2 * (1 / Real.sqrt k) := by
            calc
              _ ≤ Real.log k / k :=
                div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log hk0.le
              _ ≤ (2 * Real.sqrt k) / k := div_le_div_of_nonneg_right hlog_sk hk0.le
              _ = 2 * (1 / Real.sqrt k) := by
                rw [div_eq_iff hk0.ne']
                calc
                  2 * Real.sqrt k = 2 * (1 / Real.sqrt k) * (Real.sqrt k * Real.sqrt k) := by
                    field_simp [hsk.ne']
                  _ = 2 * (1 / Real.sqrt k) * k := by rw [Real.mul_self_sqrt hk0.le]
          exact hvm.trans (mul_le_mul_of_nonneg_left hinv_sk zero_le_two)
        have hsum_k : (∑ k ∈ S_ex n, (ArithmeticFunction.vonMangoldt k : ℝ) / k) ≤
            6 * Real.sqrt 2 * Real.sqrt n / Real.sqrt N := by
          calc
            _ ≤ ∑ _k ∈ S_ex n, 2 * Real.sqrt (2 * (n : ℝ) / N) := sum_le_sum hterm_k
            _ = ((S_ex n).card : ℝ) * (2 * Real.sqrt (2 * (n : ℝ) / N)) := by
              rw [sum_const, nsmul_eq_mul]
            _ ≤ 3 * (2 * Real.sqrt (2 * (n : ℝ) / N)) :=
              mul_le_mul_of_nonneg_right hcard3 (by positivity)
            _ = 6 * Real.sqrt 2 * Real.sqrt n / Real.sqrt N := by
              rw [Real.sqrt_div (by positivity), Real.sqrt_mul zero_le_two]; ring
        dsimp only [b]
        rw [abs_div, abs_of_pos hsn]
        have hb0 := (div_le_div_of_nonneg_right (hrow_ex n (mem_Icc.mpr ⟨hn1, hnN⟩)) hsn.le).trans
          (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsum_k (by positivity)) hsn.le)
        refine hb0.trans_eq ?_
        field_simp [hsn.ne', (Real.sqrt_pos.mpr hN0).ne']; ring
      have hsub_hi : Ioc B N ⊆ Icc 1 N := fun n hn => by
        obtain ⟨h1, h2⟩ := mem_Ioc.mp hn; exact mem_Icc.mpr ⟨by omega, h2⟩
      have hsum_inv_hi : (∑ n ∈ Ioc B N, 1 / Real.sqrt (n : ℝ)) ≤ 2 * Real.sqrt N :=
        (sum_le_sum_of_subset_of_nonneg hsub_hi (fun _ _ _ => by positivity)).trans
          (sum_Icc_one_div_sqrt_le_two_sqrt N)
      calc
        (∑ n ∈ Ioc B N, |b n| / Real.sqrt n) ≤
            ∑ n ∈ Ioc B N, (24 * Real.sqrt 2 * (m.totient : ℝ) * B / Real.sqrt N) *
              (1 / Real.sqrt n) :=
          sum_le_sum fun n hn => by
            rw [div_eq_mul_one_div _ (Real.sqrt n)]
            exact mul_le_mul_of_nonneg_right (hpt n hn) (by positivity)
        _ = (24 * Real.sqrt 2 * (m.totient : ℝ) * B / Real.sqrt N) *
              ∑ n ∈ Ioc B N, 1 / Real.sqrt (n : ℝ) := (mul_sum _ _ _).symm
        _ ≤ (24 * Real.sqrt 2 * (m.totient : ℝ) * B / Real.sqrt N) * (2 * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left hsum_inv_hi (by positivity)
        _ = 48 * Real.sqrt 2 * (m.totient : ℝ) * B := by
          field_simp [(Real.sqrt_pos.mpr hN0).ne']; ring
        _ ≤ 48 * Real.sqrt 2 * (m.totient : ℝ) * (d * c) :=
          mul_le_mul_of_nonneg_left hBd (by positivity)
        _ = Cb₁ * (m.totient : ℝ) * c := by dsimp only [Cb₁]; ring
    have hlow : (∑ n ∈ Icc 1 B, |b n| / Real.sqrt n) ≤
        Cb₂ * (m.totient : ℝ) * c ^ 3 * Real.log N / (N : ℝ) := by
      have hpt : ∀ n ∈ Icc 1 B,
          |b n| / Real.sqrt n ≤ 64 * (m.totient : ℝ) * (B : ℝ) ^ 2 * Real.log N / (N : ℝ) := by
        intro n hn
        obtain ⟨hn1, hnB⟩ := mem_Icc.mp hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        have hsn1 : 1 ≤ Real.sqrt (n : ℝ) := by
          simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by exact_mod_cast hn1 : (1 : ℝ) ≤ n)
        have hnB_R : (n : ℝ) ≤ B := by exact_mod_cast hnB
        have hcard_4B : ((S_ex n).card : ℝ) ≤ 4 * (B : ℝ) / n := by
          rw [le_div_iff₀ hn0]; linarith only [hcard_mul n hn1, hnB_R]
        have hterm_k : ∀ k ∈ S_ex n,
            (ArithmeticFunction.vonMangoldt k : ℝ) / k ≤ 4 * (n : ℝ) * Real.log N / N := by
          intro k hk
          obtain ⟨hkI, _, _⟩ := mem_filter.mp hk
          have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hkI).1
          have hk_2N : (k : ℝ) ≤ 2 * (N : ℝ) := by
            exact_mod_cast (show k ≤ 2 * N from (mem_Icc.mp hkI).2.trans (by omega))
          have hlogk : Real.log k ≤ 2 * Real.log N := by
            have hl' := Real.log_le_log hk0 hk_2N
            rw [Real.log_mul (by norm_num) hN0.ne'] at hl'
            have hl2 : Real.log 2 ≤ 1 := by
              have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
            linarith only [hl', hl2, hlog]
          have hN_2kn : (N : ℝ) ≤ 2 * (k : ℝ) * n := by
            have hkn : N ≤ k * n + k * n := by omega
            have hknR : (N : ℝ) ≤ (k : ℝ) * n + (k : ℝ) * n := by exact_mod_cast hkn
            linarith only [hknR]
          have hinv_k : 1 / (k : ℝ) ≤ 2 * (n : ℝ) / N := by
            rw [div_le_div_iff₀ hk0 hN0, one_mul]; linarith only [hN_2kn]
          calc
            _ ≤ Real.log k / k :=
              div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log hk0.le
            _ ≤ (2 * Real.log N) * (1 / (k : ℝ)) := by
              rw [div_eq_mul_one_div]
              exact mul_le_mul_of_nonneg_right hlogk (by positivity)
            _ ≤ (2 * Real.log N) * (2 * (n : ℝ) / N) :=
              mul_le_mul_of_nonneg_left hinv_k (by positivity)
            _ = 4 * (n : ℝ) * Real.log N / N := by ring
        have hsum_k : (∑ k ∈ S_ex n, (ArithmeticFunction.vonMangoldt k : ℝ) / k) ≤
            16 * (B : ℝ) * Real.log N / N := by
          calc
            _ ≤ ∑ _k ∈ S_ex n, 4 * (n : ℝ) * Real.log N / N := sum_le_sum hterm_k
            _ = ((S_ex n).card : ℝ) * (4 * (n : ℝ) * Real.log N / N) := by
              rw [sum_const, nsmul_eq_mul]
            _ ≤ (4 * (B : ℝ) / n) * (4 * (n : ℝ) * Real.log N / N) :=
              mul_le_mul_of_nonneg_right hcard_4B (by positivity)
            _ = 16 * (B : ℝ) * Real.log N / N := by field_simp [hn0.ne', hN0.ne']; ring
        have hb_abs : |b n| ≤ 64 * (m.totient : ℝ) * (B : ℝ) ^ 2 * Real.log N / (N : ℝ) := by
          dsimp only [b]
          rw [abs_div, abs_of_pos (zero_lt_one.trans_le hsn1)]
          exact ((div_le_self (abs_nonneg _) hsn1).trans
            (hrow_ex n (mem_Icc.mpr ⟨hn1, hnB.trans hBN⟩))).trans
            ((mul_le_mul_of_nonneg_left hsum_k (by positivity)).trans_eq (by ring))
        exact (div_le_self (abs_nonneg _) hsn1).trans hb_abs
      have hp3 : (B : ℝ) ^ 3 ≤ d ^ 3 * c ^ 3 :=
        (pow_le_pow_left₀ (Nat.cast_nonneg B) hBd 3).trans_eq (by ring)
      calc
        (∑ n ∈ Icc 1 B, |b n| / Real.sqrt n) ≤
            ∑ _n ∈ Icc 1 B, 64 * (m.totient : ℝ) * (B : ℝ) ^ 2 * Real.log N / (N : ℝ) :=
          sum_le_sum hpt
        _ = 64 * (m.totient : ℝ) * (B : ℝ) ^ 3 * Real.log N / (N : ℝ) := by
          rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]; ring
        _ ≤ 64 * (m.totient : ℝ) * (d ^ 3 * c ^ 3) * Real.log N / (N : ℝ) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp3 (by positivity)) hL0.le)
            hN0.le
        _ = Cb₂ * (m.totient : ℝ) * c ^ 3 * Real.log N / (N : ℝ) := by dsimp only [Cb₂]; ring
    linarith only [hhigh, hlow]
  -- Part (c): `L¹` shifted-reciprocal average on `r`.
  have hr_l1 : (∑ n ∈ Icc 1 N, |r n| / Real.sqrt n) ≤
      Cs * (m.totient : ℝ) * c * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) := by
    have hpt : ∀ n ∈ Icc 1 N, |r n| / Real.sqrt n ≤
        (|shiftedReciprocalUpwardRowError φ c id N m n| / Real.sqrt n +
          |shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n| / Real.sqrt n) / 2 := by
      intro n hn
      have hrow : r n =
          (shiftedReciprocalUpwardRowError φ c id N m n +
            shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n) / 2 := by
        dsimp only [r]
        rw [reciprocalUpwardCoefficient_eq_shifted_corrections hφ hsupp hc0 hB N m n (mem_Icc.mp hn).1]
        dsimp only [shiftedReciprocalUpwardRowError]
        rw [shellCorrectionOfShift_reflected hm]
        change _ = ((affinePrimeShellCorrectionOfShift m n id φ c ((N : ℝ) / n) -
          ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n + _) / 2
        ring
      rw [hrow, abs_div, show |(2 : ℝ)| = 2 by norm_num, div_div, mul_comm (2 : ℝ)]
      have htri := div_le_div_of_nonneg_right (abs_add_le _ _) (Real.sqrt_nonneg n)
      rw [add_div] at htri
      exact (div_le_div_of_nonneg_right htri zero_le_two).trans_eq
        (by rw [div_div, div_div, add_div])
    have hs_id := hsource m hm hmN c hc id
    have hs_ref := hsource m hm hmN c hc (reflectedAffineShift m)
    calc
      (∑ n ∈ Icc 1 N, |r n| / Real.sqrt n) ≤
          ∑ n ∈ Icc 1 N,
            (|shiftedReciprocalUpwardRowError φ c id N m n| / Real.sqrt n +
              |shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n| / Real.sqrt n) / 2 :=
        sum_le_sum hpt
      _ = ((∑ n ∈ Icc 1 N, |shiftedReciprocalUpwardRowError φ c id N m n| / Real.sqrt n) +
            ∑ n ∈ Icc 1 N,
              |shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n| / Real.sqrt n) / 2 := by
        rw [← sum_div, sum_add_distrib]
      _ ≤ Cs * (m.totient : ℝ) * c * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) := by
        linarith only [hs_id, hs_ref]
  -- Pair `u_br` with `v_l` via `abs_inner_of_coord_eq_div_sqrt_log`.
  have hbr_bilin : |⟪u_br, normalizedRamanujanHorizonVector l N⟫| ≤
      (Cb₁ + Cb₂ + Cs) * ((m.totient : ℝ) * Real.sqrt l) * rate_u := by
    have hp := abs_inner_of_coord_eq_div_sqrt_log hl u_br (fun n => b n + r n) (fun _ => rfl)
    have hsum_br : (∑ n ∈ Icc 1 N, |b n + r n| / Real.sqrt n) ≤
        (∑ n ∈ Icc 1 N, |b n| / Real.sqrt n) + ∑ n ∈ Icc 1 N, |r n| / Real.sqrt n := by
      rw [← sum_add_distrib]
      exact sum_le_sum fun n _ => by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (abs_add_le (b n) (r n)) (Real.sqrt_nonneg n)
    have hc35 : c ^ 3 ≤ c ^ 5 * Real.log N :=
      (pow_le_pow_right₀ hc (by norm_num : 3 ≤ 5)).trans
        (le_mul_of_one_le_right (by positivity) hlog)
    have ht1 : Real.sqrt l / Real.log N * (Cb₁ * (m.totient : ℝ) * c) ≤
        Cb₁ * ((m.totient : ℝ) * Real.sqrt l) * rate_u := by
      have heq : Real.sqrt l / Real.log N * (Cb₁ * (m.totient : ℝ) * c) =
          Cb₁ * ((m.totient : ℝ) * Real.sqrt l) * (c / Real.log N) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hru1 (by dsimp only [Cb₁, d]; positivity)
    have ht2 : Real.sqrt l / Real.log N *
        (Cb₂ * (m.totient : ℝ) * c ^ 3 * Real.log N / (N : ℝ)) ≤
        Cb₂ * ((m.totient : ℝ) * Real.sqrt l) * rate_u := by
      have heq : Real.sqrt l / Real.log N *
          (Cb₂ * (m.totient : ℝ) * c ^ 3 * Real.log N / (N : ℝ)) =
          Cb₂ * ((m.totient : ℝ) * Real.sqrt l) * (c ^ 3 / (N : ℝ)) := by
        field_simp [hL0.ne', hN0.ne']
      rw [heq]
      have hdiv : c ^ 3 / (N : ℝ) ≤ rate_u :=
        (div_le_div_of_nonneg_right hc35 hN0.le).trans hru2
      exact mul_le_mul_of_nonneg_left hdiv (by dsimp only [Cb₂, d]; positivity)
    have ht3 : Real.sqrt l / Real.log N *
        (Cs * (m.totient : ℝ) * c * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ))) ≤
        Cs * ((m.totient : ℝ) * Real.sqrt l) * rate_u := by
      have heq : Real.sqrt l / Real.log N *
          (Cs * (m.totient : ℝ) * c * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ))) =
          Cs * ((m.totient : ℝ) * Real.sqrt l) *
            (c * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) / Real.log N) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hru3 (by positivity)
    have hcomb := hp.trans (mul_le_mul_of_nonneg_left
      (hsum_br.trans (add_le_add hb_l1 hr_l1)) (by positivity))
    rw [mul_add, mul_add] at hcomb
    exact hcomb.trans ((add_le_add (add_le_add ht1 ht2) ht3).trans_eq (by ring))
  -- Rescale by `(Real.sqrt m.totient)⁻¹`.
  rw [upwardPrimeVector_ramanujan_residual_eq φ c N hm, hvec_split, real_inner_smul_left,
    inner_add_left, abs_mul, abs_inv, abs_of_pos (Real.sqrt_pos.mpr htot_pos)]
  have htot_div : (Real.sqrt (m.totient : ℝ))⁻¹ * ((m.totient : ℝ) * Real.sqrt l) ≤
      Real.sqrt ((m : ℝ) * l) := by
    have hst : 0 < Real.sqrt (m.totient : ℝ) := Real.sqrt_pos.mpr htot_pos
    have hid : (Real.sqrt (m.totient : ℝ))⁻¹ * (m.totient : ℝ) = Real.sqrt (m.totient : ℝ) := by
      have hsq : Real.sqrt (m.totient : ℝ) * Real.sqrt (m.totient : ℝ) = (m.totient : ℝ) :=
        Real.mul_self_sqrt htot_pos.le
      calc
        (Real.sqrt (m.totient : ℝ))⁻¹ * (m.totient : ℝ) =
            (Real.sqrt (m.totient : ℝ))⁻¹ *
              (Real.sqrt (m.totient : ℝ) * Real.sqrt (m.totient : ℝ)) := by rw [hsq]
        _ = Real.sqrt (m.totient : ℝ) := inv_mul_cancel_left₀ hst.ne' _
    rw [← mul_assoc, hid, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right htot_le (Nat.cast_nonneg l))
  have hsum_ab := (abs_add_le _ _).trans (add_le_add ha_bilin hbr_bilin)
  calc
    (Real.sqrt (m.totient : ℝ))⁻¹ *
        |⟪u_a, normalizedRamanujanHorizonVector l N⟫ +
          ⟪u_br, normalizedRamanujanHorizonVector l N⟫| ≤
      (Real.sqrt (m.totient : ℝ))⁻¹ *
        ((Ca' + Cb₁ + Cb₂ + Cs) * ((m.totient : ℝ) * Real.sqrt l) * rate_u) :=
      mul_le_mul_of_nonneg_left (hsum_ab.trans_eq (by ring)) (by positivity)
    _ = (Ca' + Cb₁ + Cb₂ + Cs) *
          ((Real.sqrt (m.totient : ℝ))⁻¹ * ((m.totient : ℝ) * Real.sqrt l)) * rate_u := by ring
    _ ≤ K * Real.sqrt ((m : ℝ) * l) * rate_u := by
      refine mul_le_mul_of_nonneg_right ?_ hru0
      have hC0 : 0 ≤ Ca' + Cb₁ + Cb₂ + Cs := by dsimp only [Ca', Cb₁, Cb₂, d]; positivity
      have hm1 := mul_le_mul_of_nonneg_left htot_div hC0
      dsimp only [K]
      linarith only [hm1, Real.sqrt_nonneg ((m : ℝ) * l)]

/-! ## Section 3: Assembled Bilinear Residual, Relative Energy Sums, and Sub-One-Eighth Positivity -/

private theorem abs_inner_eight_signed_le {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p s c x q y z u v : E) :
    |⟪-p + s + c - x + q + (y + z) - u, v⟫| ≤
      |⟪p, v⟫| + |⟪s, v⟫| + |⟪c, v⟫| + |⟪x, v⟫| +
        |⟪q, v⟫| + |⟪y, v⟫| + |⟪z, v⟫| + |⟪u, v⟫| := by
  simp only [inner_add_left, inner_sub_left, inner_neg_left]
  have h1 := abs_sub (-⟪p, v⟫ + ⟪s, v⟫ + ⟪c, v⟫ - ⟪x, v⟫ + ⟪q, v⟫ + (⟪y, v⟫ + ⟪z, v⟫)) ⟪u, v⟫
  have h2 := abs_add_le (-⟪p, v⟫ + ⟪s, v⟫ + ⟪c, v⟫ - ⟪x, v⟫ + ⟪q, v⟫) (⟪y, v⟫ + ⟪z, v⟫)
  have h3 := abs_add_le ⟪y, v⟫ ⟪z, v⟫
  have h4 := abs_add_le (-⟪p, v⟫ + ⟪s, v⟫ + ⟪c, v⟫ - ⟪x, v⟫) ⟪q, v⟫
  have h5 := abs_sub (-⟪p, v⟫ + ⟪s, v⟫ + ⟪c, v⟫) ⟪x, v⟫
  have h6 := abs_add_le (-⟪p, v⟫ + ⟪s, v⟫) ⟪c, v⟫
  have h7 := abs_add_le (-⟪p, v⟫) ⟪s, v⟫
  rw [abs_neg] at h7
  linarith only [h1, h2, h3, h4, h5, h6, h7]

/-- **Eight-channel bilinear complete-Weil conductor residual bound.**
Across every logarithmic conductor range `m, l ≤ (log N)^A` (`A ≥ 0`), pairing the complete Weil
residual of mode `m` against mode `l` saves a full power of `c` relative to the `L^2` residual norm,
yielding `O(√(m l) * (1 + log m) * (c (1 + log c)^2 (log N)^(1/k) / log N + c^5 log N / N))`. -/
theorem exists_completeWeil_bilinear_conductor_residual_variable_rate {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N,
          normalizedRamanujanHorizonVector l N⟫| ≤
          K * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) *
            (c * (1 + Real.log c) ^ 2 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
              c ^ 5 * Real.log N / (N : ℝ)) := by
  obtain ⟨Cp, hCp, hp⟩ := exists_primeResidual_bilinear_bound
  obtain ⟨Cs, hCs, hs⟩ := exists_selfError_bilinear_bound hφ hsupp hM
  obtain ⟨Cx, hCx, hx⟩ := exists_crossError_bilinear_bound hφ hsupp hM
  obtain ⟨Cq, hCq, hq⟩ := exists_poleError_bilinear_bound hφ hsupp hM
  obtain ⟨Cd, hCd, hdown⟩ := exists_downward_bilinear_bound hφ hsupp hM
  obtain ⟨Cn, hCn, hnear⟩ := exists_nearCenter_bilinear_bound φ
  obtain ⟨Cu, hCu, hup⟩ := exists_upward_bilinear_variable_rate hφ hsupp hM
  let Cc := 9700 * |completeWeilPoleShift φ 1|
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  let K := Cp + Cs + Cc + Cx + Cq + 2 * Cd + Cn + Cu + 1
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro A hA k hk
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall_A : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / (8 * A + 8)) := by
    have hpos : 0 < 1 / (8 * A + 8) := by positivity
    have hsm := tendsto_natCast_atTop_atTop.eventually ((isLittleO_log_rpow_atTop hpos).bound zero_lt_one)
    filter_upwards [hsm, eventually_ge_atTop 1] with N hN _
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have habs : |Real.log (N : ℝ)| ≤ (N : ℝ) ^ (1 / (8 * A + 8)) := by
      simpa only [Function.comp_def, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hN0 _), one_mul] using hN
    exact (le_abs_self _).trans habs
  filter_upwards [hup A hA k hk, hsmall_A, eventually_ge_atTop 256,
    hloglim.eventually_ge_atTop ((72 * (A + 2)) ^ 2)] with N hupN hLA hN256 hL_big
  intro m hm hmL l hl hlL c hc hlarge
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL1 : 1 ≤ Real.log (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ (72 * (A + 2)) ^ 2 := by nlinarith only [hA]
    exact h1.trans hL_big
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have h1m : 1 ≤ 1 + Real.log (m : ℝ) := by linarith [Real.log_natCast_nonneg m]
  have h1c : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc]
  have hs1 : 1 ≤ Real.log (N : ℝ) ^ (1 / (k : ℝ)) := Real.one_le_rpow hL1 (by positivity)
  let M_ml := Real.sqrt ((m : ℝ) * l) * (1 + Real.log m)
  have hMml0 : 0 ≤ M_ml := by dsimp only [M_ml]; positivity
  have hsqrt_le_Mml : Real.sqrt ((m : ℝ) * l) ≤ M_ml :=
    le_mul_of_one_le_right (Real.sqrt_nonneg _) h1m
  -- Verify `M^4 ≤ N` and `18 * (1 + log M) ≤ log N` for `M = max 2 (max m l)`.
  let M := max 2 (max m l)
  have hM_le_2LA : (M : ℝ) ≤ 2 * Real.log (N : ℝ) ^ A := by
    have hLA1 : 1 ≤ Real.log (N : ℝ) ^ A := Real.one_le_rpow hL1 hA
    have h2 : (2 : ℝ) ≤ 2 * Real.log (N : ℝ) ^ A := by linarith only [hLA1]
    have hm' : (m : ℝ) ≤ 2 * Real.log (N : ℝ) ^ A := by linarith only [hmL, hLA1]
    have hl' : (l : ℝ) ≤ 2 * Real.log (N : ℝ) ^ A := by linarith only [hlL, hLA1]
    dsimp only [M]
    rw [Nat.cast_max, Nat.cast_max, Nat.cast_ofNat]
    exact max_le h2 (max_le hm' hl')
  have hMN4 : M ^ 4 ≤ N := by
    have hM4 : (M : ℝ) ^ 4 ≤ 16 * Real.log (N : ℝ) ^ (4 * A + 4) := by
      have hp := pow_le_pow_left₀ (Nat.cast_nonneg M) hM_le_2LA 4
      have he : (2 * Real.log (N : ℝ) ^ A) ^ (4 : ℕ) = 16 * Real.log (N : ℝ) ^ (4 * A) := by
        rw [mul_pow, show (2 : ℝ) ^ (4 : ℕ) = 16 by norm_num,
          ← Real.rpow_natCast (Real.log (N : ℝ) ^ A) 4, ← Real.rpow_mul hL0.le]
        congr 1; ring
      exact (hp.trans_eq he).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only : 4 * A ≤ 4 * A + 4)) (by norm_num))
    have hL_sqrtN : Real.log (N : ℝ) ^ (4 * A + 4) ≤ Real.sqrt N := by
      have hp := Real.rpow_le_rpow hL0.le hLA (by positivity : 0 ≤ 4 * A + 4)
      have he : ((N : ℝ) ^ (1 / (8 * A + 8))) ^ (4 * A + 4) = Real.sqrt N := by
        rw [← Real.rpow_mul hN0.le, Real.sqrt_eq_rpow]
        congr 1; field_simp [show (8 * A + 8 : ℝ) ≠ 0 by positivity]; ring
      exact hp.trans_eq he
    have h16_sqrtN : (16 : ℝ) ≤ Real.sqrt N := by
      have h256 : (16 : ℝ) ^ 2 ≤ N := by
        have : (256 : ℝ) ≤ N := by exact_mod_cast hN256
        linarith only [this]
      have h := Real.sqrt_le_sqrt h256
      rwa [Real.sqrt_sq (by norm_num)] at h
    have hM4_N : (M : ℝ) ^ 4 ≤ (N : ℝ) :=
      hM4.trans ((mul_le_mul h16_sqrtN hL_sqrtN (by positivity) (Real.sqrt_nonneg _)).trans_eq
        (Real.mul_self_sqrt hN0.le))
    exact_mod_cast hM4_N
  have hlog18 : 18 * (1 + Real.log (M : ℝ)) ≤ Real.log (N : ℝ) := by
    let L := Real.log (N : ℝ)
    have hsL_ge : 72 * (A + 2) ≤ Real.sqrt L := by
      have h := Real.sqrt_le_sqrt hL_big
      rwa [Real.sqrt_sq (by positivity)] at h
    have hsL1 : 1 ≤ Real.sqrt L := by linarith only [hsL_ge, hA]
    have hlogL_le : Real.log L ≤ 2 * Real.sqrt L := by
      have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hL0)
      have h2 : Real.log L = 2 * Real.log (Real.sqrt L) := by
        rw [Real.log_sqrt hL0.le]; ring
      linarith only [h1, h2]
    have hM0 : (0 : ℝ) < M := by positivity
    have hlogM_le : 1 + Real.log (M : ℝ) ≤ 2 * (A + 2) * Real.sqrt L := by
      have hl1 := Real.log_le_log hM0 hM_le_2LA
      rw [Real.log_mul zero_lt_two.ne' (Real.rpow_pos_of_pos hL0 A).ne', Real.log_rpow hL0] at hl1
      have hl2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos zero_lt_two; linarith
      have hA_mul := mul_le_mul_of_nonneg_left hlogL_le hA
      nlinarith only [hl1, hl2, hA_mul, hsL1, hA]
    have hsqL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
    nlinarith only [hlogM_le, hsL_ge, hsqL, hsL1, hA]
  -- Standard overlap comparison rates into `R`.
  let R := c * (1 + Real.log c) ^ 2 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
    c ^ 5 * Real.log N / (N : ℝ)
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hc2_N : c ^ 2 ≤ (N : ℝ) := by
    have he := Real.exp_pos 1
    have hcoef : 1 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [he]
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [h, hlarge]
  have h2Bc_N : 2 * (Real.exp 1 + 2) * c ≤ (N : ℝ) := by
    have he := Real.exp_pos 1
    have hcoef : 2 * (Real.exp 1 + 2) ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [he]
    have h1 : 2 * (Real.exp 1 + 2) * c ≤ 2 * (Real.exp 1 + 2) * c ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hc]) (by positivity)
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    linarith only [h1, h, hlarge]
  have htwo_c : 2 * c ≤ (N : ℝ) := by nlinarith only [h2Bc_N, Real.exp_pos 1, hc0]
  have hcN : c ≤ (N : ℝ) := by linarith only [htwo_c, hc0]
  have hrate_c1 : ∀ {a : ℕ}, a ≤ 2 → c * (1 + Real.log c) ^ a / Real.log N ≤ R :=
    fun {a} ha => by
      have ha2 : (1 + Real.log c) ^ a ≤ (1 + Real.log c) ^ 2 := pow_le_pow_right₀ h1c ha
      have hnum : c * (1 + Real.log c) ^ a ≤
          c * (1 + Real.log c) ^ 2 * Real.log N ^ (1 / (k : ℝ)) :=
        (mul_le_mul_of_nonneg_left ha2 hc0.le).trans
          (le_mul_of_one_le_right (by positivity) hs1)
      exact (div_le_div_of_nonneg_right hnum hL0.le).trans (le_add_of_nonneg_right (by positivity))
  have hrate_base : 1 / Real.log N ≤ R := by
    have h1 : (1 : ℝ) ≤ c * (1 + Real.log c) ^ 0 := by rw [pow_zero, mul_one]; exact hc
    exact (div_le_div_of_nonneg_right h1 hL0.le).trans (hrate_c1 (by norm_num))
  have hrate_sub : ∀ {b : ℕ}, 1 ≤ b → b ≤ 5 → c ^ b / (N : ℝ) ≤ R :=
    fun {b} hb1 hb5 => by
      have hcb5 : c ^ b ≤ c ^ 5 * Real.log N :=
        (pow_le_pow_right₀ hc hb5).trans (le_mul_of_one_le_right (by positivity) hL1)
      exact (div_le_div_of_nonneg_right hcb5 hN0.le).trans (le_add_of_nonneg_left (by positivity))
  -- Collect all eight channel bounds.
  let v_m := normalizedRamanujanHorizonVector m N
  let v_l := normalizedRamanujanHorizonVector l N
  have hp' : |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) v_m -
      (Real.log N - ramanujanAdjunctionEnergy m) • v_m, v_l⟫| ≤ Cp * M_ml * R := by
    refine (hp m l N hm hl).trans ?_
    rw [show Cp * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) / Real.log N =
      Cp * M_ml * (1 / Real.log N) by dsimp only [M_ml]; ring]
    exact mul_le_mul_of_nonneg_left hrate_base (by positivity)
  have hs' : |⟪completeWeilSelfError φ c N • v_m, v_l⟫| ≤ Cs * M_ml * R := by
    refine (hs m l hm hl N hN1 hL1 c hc0 hcN).trans ?_
    have hc1_div : c / (N : ℝ) ≤ R := by
      simpa only [pow_one] using hrate_sub (by norm_num : 1 ≤ 1) (by norm_num : 1 ≤ 5)
    rw [show Cs * Real.sqrt ((m : ℝ) * l) * c / (N : ℝ) =
      Cs * Real.sqrt ((m : ℝ) * l) * (c / (N : ℝ)) by ring]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt_le_Mml hCs.le) hc1_div
      (by positivity) (by positivity)
  have hc' : |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) v_m -
      (if m = 1 then completeWeilPoleShift φ c else 0) • v_m, v_l⟫| ≤ Cc * M_ml * R := by
    have hcen := fullWeilCenter_residual_bilinear_bound (completeWeilPoleShift φ c)
      hm hl hMN4 hlog18
    have hshift : |completeWeilPoleShift φ c| = |completeWeilPoleShift φ 1| * c := by
      have h1 : completeWeilPoleShift φ c = completeWeilPoleShift φ 1 * c := by
        unfold completeWeilPoleShift; ring
      rw [h1, abs_mul, abs_of_pos hc0]
    have heq : 9700 * |completeWeilPoleShift φ c| * Real.sqrt ((m : ℝ) * l) *
        (1 + Real.log m) / Real.log N =
        Cc * M_ml * (c * (1 + Real.log c) ^ 0 / Real.log N) := by
      dsimp only [Cc, M_ml]; rw [hshift, pow_zero]; ring
    exact hcen.trans (heq.trans_le
      (mul_le_mul_of_nonneg_left (hrate_c1 (by norm_num)) (by positivity)))
  have hx' : |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) v_m, v_l⟫| ≤
      Cx * M_ml * R := by
    refine (hx m l hm hl c hc N hN1 hc2_N).trans ?_
    rw [show Cx * Real.sqrt ((m : ℝ) * l) * c / Real.log N =
      Cx * Real.sqrt ((m : ℝ) * l) * (c * (1 + Real.log c) ^ 0 / Real.log N) by
        rw [pow_zero]; ring]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt_le_Mml hCx.le)
      (hrate_c1 (by norm_num)) (by positivity) (by positivity)
  have hq' : |⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) v_m, v_l⟫| ≤
      Cq * M_ml * R := by
    refine (hq m l hm hl c hc N hN1 hL1 hcN).trans ?_
    have hc25 : c ^ 2 * Real.log N / (N : ℝ) ≤ R :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc (by norm_num : 2 ≤ 5)) hL0.le)
        hN0.le).trans (le_add_of_nonneg_left (by positivity))
    rw [show Cq * Real.sqrt ((m : ℝ) * l) * c ^ 2 * Real.log N / (N : ℝ) =
      Cq * Real.sqrt ((m : ℝ) * l) * (c ^ 2 * Real.log N / (N : ℝ)) by ring]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt_le_Mml hCq.le) hc25
      (by positivity) (by positivity)
  have hd' : |⟪(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m,
      v_l⟫| ≤ (2 * Cd) * M_ml * R := by
    have hb := hdown m l hm hl c hc N hN1 hL1 h2Bc_N
    have hr_sum : c * (1 + Real.log c) / Real.log N + c ^ 2 / (N : ℝ) ≤ 2 * R := by
      have h1 : c * (1 + Real.log c) / Real.log N ≤ R := by
        simpa only [pow_one] using hrate_c1 (by norm_num : 1 ≤ 2)
      have h2 := hrate_sub (by norm_num : 1 ≤ 2) (by norm_num : 2 ≤ 5)
      linarith only [h1, h2]
    exact (hb.trans_eq (by dsimp only [M_ml]; ring)).trans
      ((mul_le_mul_of_nonneg_left hr_sum (by positivity)).trans_eq (by ring))
  have hn' : |⟪nearCenterVector φ c N m, v_l⟫| ≤ Cn * M_ml * R := by
    refine (hnear m l hm hl c hc N hN1 htwo_c).trans ?_
    rw [show Cn * Real.sqrt ((m : ℝ) * l) * c * (1 + Real.log c) ^ 2 / Real.log N =
      Cn * Real.sqrt ((m : ℝ) * l) * (c * (1 + Real.log c) ^ 2 / Real.log N) by ring]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt_le_Mml hCn.le)
      (hrate_c1 (by norm_num)) (by positivity) (by positivity)
  have hu' : |⟪upwardPrimeVector φ c N v_m - shellCorrection φ c m • v_m, v_l⟫| ≤
      Cu * M_ml * R := by
    refine (hupN m hm hmL l hl c hc hlarge).trans ?_
    have hup_R : c * (1 + Real.log c) * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
        c ^ 5 * Real.log N / (N : ℝ) ≤ R := by
      dsimp only [R]
      refine add_le_add ?_ le_rfl
      apply div_le_div_of_nonneg_right _ hL0.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (by simpa only [pow_one] using pow_le_pow_right₀ h1c (by norm_num : 1 ≤ 2)) hc0.le
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt_le_Mml hCu.le) hup_R
      (by positivity) (by positivity)
  rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM hc0 hN1 hm]
  have h8 := abs_inner_eight_signed_le
    (Matrix.toEuclideanLin (fullPrimeMatrix N) v_m -
      (Real.log N - ramanujanAdjunctionEnergy m) • v_m)
    (completeWeilSelfError φ c N • v_m)
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) v_m -
      (if m = 1 then completeWeilPoleShift φ c else 0) • v_m)
    (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) v_m)
    (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) v_m)
    ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m)
    (nearCenterVector φ c N m)
    (upwardPrimeVector φ c N v_m - shellCorrection φ c m • v_m)
    v_l
  have hb := h8.trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add hp' hs') hc') hx') hq') hd') hn') hu')
  calc
    _ ≤ Cp * M_ml * R + Cs * M_ml * R + Cc * M_ml * R + Cx * M_ml * R +
          Cq * M_ml * R + (2 * Cd) * M_ml * R + Cn * M_ml * R + Cu * M_ml * R := hb
    _ = (Cp + Cs + Cc + Cx + Cq + 2 * Cd + Cn + Cu) * M_ml * R := by ring
    _ ≤ K * M_ml * R :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith only) hMml0) hR0

/-- Specialization of `exists_completeWeil_bilinear_conductor_residual_variable_rate` to
`tiltedUnitSpline`. -/
theorem exists_tiltedUnitSpline_bilinear_conductor_residual_variable_rate :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.log (N : ℝ) ^ A →
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy tiltedUnitSpline c m •
              normalizedRamanujanHorizonVector m N,
          normalizedRamanujanHorizonVector l N⟫| ≤
          K * Real.sqrt ((m : ℝ) * l) * (1 + Real.log m) *
            (c * (1 + Real.log c) ^ 2 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
              c ^ 5 * Real.log N / (N : ℝ)) :=
  exists_completeWeil_bilinear_conductor_residual_variable_rate contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos

/-! ### First-Power Inverse-Energy Relative Weights -/

private theorem conductor_inv_energy_weight_le {c : ℝ} (hc : 1 ≤ c) {m : ℕ} (hm : 0 < m) :
    (m : ℝ) / completedConductorEnergy tiltedUnitSpline c m ≤
      (c ^ 7 / (m : ℝ) ^ 2 + (m : ℝ)) / tiltedSplineSpectralFloorConstant := by
  let κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := zero_lt_one.trans_le hm1
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hfloor := tiltedUnitSpline_completedConductorEnergy_ge_conductor_scale hc0 hm
  have htot_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hratio : 1 ≤ (m : ℝ) / m.totient := (one_le_div htot).mpr htot_le
  by_cases hmc : (m : ℝ) ≤ c
  · have hp : ((m : ℝ) / c) ^ 7 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (div_nonneg hm0.le hc0.le)
        ((div_le_one hc0).mpr hmc) 7
    rw [min_eq_right hp] at hfloor
    have henergy_lower : κ * ((m : ℝ) / c) ^ 7 ≤ completedConductorEnergy tiltedUnitSpline c m := by
      have h1 : κ ≤ (2 * tiltedSplineTailConstant / ∫ u, tiltedUnitSpline u ^ 2) *
          ((m : ℝ) / m.totient) := le_mul_of_one_le_right hκ.le hratio
      exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans hfloor
    have hm26 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 6 := pow_le_pow_right₀ hm1 (by norm_num : 2 ≤ 6)
    calc
      (m : ℝ) / completedConductorEnergy tiltedUnitSpline c m ≤
          (m : ℝ) / (κ * ((m : ℝ) / c) ^ 7) :=
        div_le_div_of_nonneg_left hm0.le (by positivity) henergy_lower
      _ = (c ^ 7 / (m : ℝ) ^ 6) / κ := by field_simp [hκ.ne', hm0.ne', hc0.ne']
      _ ≤ (c ^ 7 / (m : ℝ) ^ 2) / κ :=
        div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hm0) hm26) hκ.le
      _ ≤ (c ^ 7 / (m : ℝ) ^ 2 + (m : ℝ)) / κ :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_right hm0.le) hκ.le
  · have hcm : c ≤ (m : ℝ) := le_of_not_ge hmc
    have henergy_lower : κ ≤ completedConductorEnergy tiltedUnitSpline c m :=
      tiltedUnitSpline_completedConductorEnergy_ge_above_overlap hc0 hm hcm
    calc
      (m : ℝ) / completedConductorEnergy tiltedUnitSpline c m ≤ (m : ℝ) / κ :=
        div_le_div_of_nonneg_left hm0.le hκ henergy_lower
      _ ≤ (c ^ 7 / (m : ℝ) ^ 2 + (m : ℝ)) / κ :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hκ.le

private theorem conductor_log_sq_inv_energy_weight_le {c : ℝ} (hc : 1 ≤ c) {m : ℕ} (hm : 0 < m) :
    (m : ℝ) * (1 + Real.log m) ^ 2 / completedConductorEnergy tiltedUnitSpline c m ≤
      (4 * c ^ 7 / (m : ℝ) ^ 2 + (m : ℝ) * (1 + Real.log m) ^ 2) /
        tiltedSplineSpectralFloorConstant := by
  let κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := zero_lt_one.trans_le hm1
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hfloor := tiltedUnitSpline_completedConductorEnergy_ge_conductor_scale hc0 hm
  have htot_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hratio : 1 ≤ (m : ℝ) / m.totient := (one_le_div htot).mpr htot_le
  have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
  by_cases hmc : (m : ℝ) ≤ c
  · have hp : ((m : ℝ) / c) ^ 7 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (div_nonneg hm0.le hc0.le)
        ((div_le_one hc0).mpr hmc) 7
    rw [min_eq_right hp] at hfloor
    have henergy_lower : κ * ((m : ℝ) / c) ^ 7 ≤ completedConductorEnergy tiltedUnitSpline c m := by
      have h1 : κ ≤ (2 * tiltedSplineTailConstant / ∫ u, tiltedUnitSpline u ^ 2) *
          ((m : ℝ) / m.totient) := le_mul_of_one_le_right hκ.le hratio
      exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans hfloor
    have hlog_sq : (1 + Real.log (m : ℝ)) ^ 2 ≤ 4 * (m : ℝ) := by
      have h1 := one_add_log_le_two_sqrt hm
      have hsq := pow_le_pow_left₀ (by positivity) h1 2
      rwa [mul_pow, Real.sq_sqrt hm0.le, show (2 : ℝ) ^ 2 = 4 by norm_num] at hsq
    have hm25 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 5 := pow_le_pow_right₀ hm1 (by norm_num : 2 ≤ 5)
    calc
      (m : ℝ) * (1 + Real.log m) ^ 2 / completedConductorEnergy tiltedUnitSpline c m ≤
          ((m : ℝ) * (4 * (m : ℝ))) / (κ * ((m : ℝ) / c) ^ 7) :=
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_sq hm0.le)
          (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
            integral_tiltedUnitSpline_sq_pos hc0 m)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) henergy_lower)
      _ = (4 * c ^ 7 / (m : ℝ) ^ 5) / κ := by field_simp [hκ.ne', hm0.ne', hc0.ne']; ring
      _ ≤ (4 * c ^ 7 / (m : ℝ) ^ 2) / κ :=
        div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hm0) hm25) hκ.le
      _ ≤ (4 * c ^ 7 / (m : ℝ) ^ 2 + (m : ℝ) * (1 + Real.log m) ^ 2) / κ :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hκ.le
  · have hcm : c ≤ (m : ℝ) := le_of_not_ge hmc
    have henergy_lower : κ ≤ completedConductorEnergy tiltedUnitSpline c m :=
      tiltedUnitSpline_completedConductorEnergy_ge_above_overlap hc0 hm hcm
    calc
      (m : ℝ) * (1 + Real.log m) ^ 2 / completedConductorEnergy tiltedUnitSpline c m ≤
          ((m : ℝ) * (1 + Real.log m) ^ 2) / κ :=
        div_le_div_of_nonneg_left (by positivity) hκ henergy_lower
      _ ≤ (4 * c ^ 7 / (m : ℝ) ^ 2 + (m : ℝ) * (1 + Real.log m) ^ 2) / κ :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hκ.le

/-- First-power inverse-energy conductor sum: `∑_{m=1}^Q m / E_m(c) ≤ (2 c^7 + Q^2) / κ₀`. -/
theorem sum_conductor_inv_energy_le {c : ℝ} (hc : 1 ≤ c) (Q : ℕ) :
    (∑ m ∈ Icc 1 Q, (m : ℝ) / completedConductorEnergy tiltedUnitSpline c m) ≤
      (2 * c ^ 7 + (Q : ℝ) ^ 2) / tiltedSplineSpectralFloorConstant := by
  let κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 ≤ κ := tiltedSplineSpectralFloorConstant_pos.le
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hlin : (∑ m ∈ Icc 1 Q, (m : ℝ)) ≤ (Q : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _m ∈ Icc 1 Q, (Q : ℝ) := sum_le_sum fun m hm => by exact_mod_cast (mem_Icc.mp hm).2
      _ = (Q : ℝ) ^ 2 := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
  have hinv := RHTower.Sieve.sum_inv_sq_le_two Q
  calc
    _ ≤ ∑ m ∈ Icc 1 Q, (c ^ 7 / (m : ℝ) ^ 2 + (m : ℝ)) / κ :=
      sum_le_sum fun m hm => conductor_inv_energy_weight_le hc (mem_Icc.mp hm).1
    _ = (c ^ 7 * (∑ m ∈ Icc 1 Q, 1 / (m : ℝ) ^ 2) + ∑ m ∈ Icc 1 Q, (m : ℝ)) / κ := by
      rw [← sum_div, sum_add_distrib, mul_sum]
      congr 2
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ (2 * c ^ 7 + (Q : ℝ) ^ 2) / κ := by
      apply div_le_div_of_nonneg_right _ hκ
      have h := mul_le_mul_of_nonneg_left hinv (pow_nonneg hc0 7)
      linarith only [h, hlin]

/-- Log-weighted first-power inverse-energy conductor sum:
`∑_{m=1}^Q m (1 + log m)^2 / E_m(c) ≤ (8 c^7 + Q^2 (1 + log Q)^2) / κ₀`. -/
theorem sum_conductor_log_sq_inv_energy_le {c : ℝ} (hc : 1 ≤ c) (Q : ℕ) :
    (∑ m ∈ Icc 1 Q, (m : ℝ) * (1 + Real.log m) ^ 2 /
        completedConductorEnergy tiltedUnitSpline c m) ≤
      (8 * c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) / tiltedSplineSpectralFloorConstant := by
  let κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 ≤ κ := tiltedSplineSpectralFloorConstant_pos.le
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hlin : (∑ m ∈ Icc 1 Q, (m : ℝ) * (1 + Real.log m) ^ 2) ≤
      (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 := by
    calc
      _ ≤ ∑ _m ∈ Icc 1 Q, (Q : ℝ) * (1 + Real.log Q) ^ 2 := by
        refine sum_le_sum fun m hm => ?_
        obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
        have hmQ' : (m : ℝ) ≤ Q := by exact_mod_cast hmQ
        have hlog : Real.log m ≤ Real.log Q := Real.log_le_log hm0 hmQ'
        exact mul_le_mul hmQ'
          (pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg m]) (by linarith only [hlog]) 2)
          (sq_nonneg _) (Nat.cast_nonneg Q)
      _ = (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
  have hinv := RHTower.Sieve.sum_inv_sq_le_two Q
  calc
    _ ≤ ∑ m ∈ Icc 1 Q, (4 * c ^ 7 / (m : ℝ) ^ 2 + (m : ℝ) * (1 + Real.log m) ^ 2) / κ :=
      sum_le_sum fun m hm => conductor_log_sq_inv_energy_weight_le hc (mem_Icc.mp hm).1
    _ = (4 * c ^ 7 * (∑ m ∈ Icc 1 Q, 1 / (m : ℝ) ^ 2) +
          ∑ m ∈ Icc 1 Q, (m : ℝ) * (1 + Real.log m) ^ 2) / κ := by
      rw [← sum_div, sum_add_distrib, mul_sum]
      congr 2
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ (8 * c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) / κ := by
      apply div_le_div_of_nonneg_right _ hκ
      have h := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 4 * c ^ 7)
      linarith only [h, hlin]

/-- **First-power inverse-energy Schur cross budget.**
Weighting squared single-mode residuals by `1 / E_m(c)` (instead of `1 / E_m(c)^2`) yields total
cross mass `O((c^7 + Q^2 (1 + log Q)^2) * rate_quad)` with leading overlap exponent `7 + 2 = 9`. -/
theorem exists_tiltedUnitSpline_quadratic_inv_energy_residual_sum_le :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.log (N : ℝ) ^ A →
        (∑ m ∈ Icc 1 Q,
          ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
              (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy tiltedUnitSpline c m •
              normalizedRamanujanHorizonVector m N‖ ^ 2 /
            completedConductorEnergy tiltedUnitSpline c m) ≤
          K * (c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) *
            (c ^ 2 * (1 + Real.log c) ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
              c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
  obtain ⟨K₀, hK₀, hres⟩ := exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate
  let κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  refine ⟨8 * K₀ / κ, by positivity, ?_⟩
  intro A hA k hk
  filter_upwards [hres A hA k hk] with N hN
  intro c hc hwidth Q hQ
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  let r := c ^ 2 * (1 + Real.log c) ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
    c ^ 10 * (Real.log (N : ℝ) / N) ^ 2
  have hr : 0 ≤ r := by
    have := Real.log_natCast_nonneg N
    have : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc]
    dsimp only [r]; positivity
  calc
    _ ≤ ∑ m ∈ Icc 1 Q,
          (K₀ * ((m : ℝ) * (1 + Real.log m) ^ 2) * r) /
            completedConductorEnergy tiltedUnitSpline c m := by
      refine sum_le_sum fun m hm => ?_
      have hm1 := (mem_Icc.mp hm).1
      have hmQ : (m : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hm).2
      exact div_le_div_of_nonneg_right (hN m hm1 (hmQ.trans hQ) c hc hwidth)
        (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
          integral_tiltedUnitSpline_sq_pos hc0 m)
    _ = (K₀ * r) * ∑ m ∈ Icc 1 Q,
          (m : ℝ) * (1 + Real.log m) ^ 2 / completedConductorEnergy tiltedUnitSpline c m := by
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ (K₀ * r) * ((8 * c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) / κ) :=
      mul_le_mul_of_nonneg_left (sum_conductor_log_sq_inv_energy_le hc Q) (by positivity)
    _ ≤ (8 * K₀ / κ) * (c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) * r := by
      have hbase : 8 * c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 ≤
          8 * (c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) := by
        have := mul_nonneg (sq_nonneg (Q : ℝ)) (sq_nonneg (1 + Real.log Q))
        linarith only [this]
      exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hbase hκ.le)
        (by positivity : 0 ≤ K₀ * r)).trans_eq (by ring)

/-- **Factored double-sum bilinear relative residual bound.**
Symmetrically dividing each bilinear residual square `|⟪r_m, v_l⟫|^2` by `E_m(c) * E_l(c)` yields
`O((c^7 + Q^2 (1 + log Q)^2)^2 * rate_bilin^2)`, with root overlap exponent `7 + 1 = 8`. -/
theorem exists_tiltedUnitSpline_bilinear_relative_residual_sum_le :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.log (N : ℝ) ^ A →
        (∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
          |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
              (normalizedRamanujanHorizonVector m N) -
              completedConductorEnergy tiltedUnitSpline c m •
                normalizedRamanujanHorizonVector m N,
            normalizedRamanujanHorizonVector l N⟫| ^ 2 /
            (completedConductorEnergy tiltedUnitSpline c m *
              completedConductorEnergy tiltedUnitSpline c l)) ≤
          K * (c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) ^ 2 *
            (c * (1 + Real.log c) ^ 2 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
              c ^ 5 * Real.log N / (N : ℝ)) ^ 2 := by
  obtain ⟨K₀, hK₀, hres⟩ := exists_tiltedUnitSpline_bilinear_conductor_residual_variable_rate
  let κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  refine ⟨16 * K₀ ^ 2 / κ ^ 2, by positivity, ?_⟩
  intro A hA k hk
  filter_upwards [hres A hA k hk] with N hN
  intro c hc hwidth Q hQ
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  let r := c * (1 + Real.log c) ^ 2 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
    c ^ 5 * Real.log N / (N : ℝ)
  have hpt : ∀ m ∈ Icc 1 Q, ∀ l ∈ Icc 1 Q,
      |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m •
            normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector l N⟫| ^ 2 /
        (completedConductorEnergy tiltedUnitSpline c m *
          completedConductorEnergy tiltedUnitSpline c l) ≤
      (K₀ ^ 2 * r ^ 2) *
        (((m : ℝ) * (1 + Real.log m) ^ 2 / completedConductorEnergy tiltedUnitSpline c m) *
          ((l : ℝ) / completedConductorEnergy tiltedUnitSpline c l)) := by
    intro m hm l hl
    have hm1 := (mem_Icc.mp hm).1
    have hl1 := (mem_Icc.mp hl).1
    have hmQ : (m : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hm).2
    have hlQ : (l : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hl).2
    have hb := hN m hm1 (hmQ.trans hQ) l hl1 (hlQ.trans hQ) c hc hwidth
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hEm0 := completedConductorEnergy_nonneg contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 m
    have hEl0 := completedConductorEnergy_nonneg contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 l
    refine (div_le_div_of_nonneg_right hsq (mul_nonneg hEm0 hEl0)).trans_eq ?_
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hsum1 := sum_conductor_log_sq_inv_energy_le hc Q
  have hsum2 := sum_conductor_inv_energy_le hc Q
  let W := c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2
  have hW1 : (8 * c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) / κ ≤ (8 / κ) * W := by
    have hb : 8 * c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 ≤ 8 * W := by
      dsimp only [W]
      have := mul_nonneg (sq_nonneg (Q : ℝ)) (sq_nonneg (1 + Real.log Q))
      linarith only [this]
    exact (div_le_div_of_nonneg_right hb hκ.le).trans_eq (by ring)
  have hW2 : (2 * c ^ 7 + (Q : ℝ) ^ 2) / κ ≤ (2 / κ) * W := by
    have h1Q : 1 ≤ (1 + Real.log (Q : ℝ)) ^ 2 :=
      one_le_pow₀ (by linarith [Real.log_natCast_nonneg Q])
    have hQle : (Q : ℝ) ^ 2 ≤ (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 :=
      le_mul_of_one_le_right (sq_nonneg _) h1Q
    have hb : 2 * c ^ 7 + (Q : ℝ) ^ 2 ≤ 2 * W := by dsimp only [W]; linarith only [hQle]
    exact (div_le_div_of_nonneg_right hb hκ.le).trans_eq (by ring)
  calc
    _ ≤ ∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q, (K₀ ^ 2 * r ^ 2) *
          (((m : ℝ) * (1 + Real.log m) ^ 2 / completedConductorEnergy tiltedUnitSpline c m) *
            ((l : ℝ) / completedConductorEnergy tiltedUnitSpline c l)) :=
      sum_le_sum fun m hm => sum_le_sum fun l hl => hpt m hm l hl
    _ = (K₀ ^ 2 * r ^ 2) *
          ((∑ m ∈ Icc 1 Q, (m : ℝ) * (1 + Real.log m) ^ 2 /
              completedConductorEnergy tiltedUnitSpline c m) *
            (∑ l ∈ Icc 1 Q, (l : ℝ) / completedConductorEnergy tiltedUnitSpline c l)) := by
      rw [Finset.sum_mul_sum, mul_sum]
      exact sum_congr rfl fun m _ => by rw [mul_sum]
    _ ≤ (K₀ ^ 2 * r ^ 2) * (((8 / κ) * W) * ((2 / κ) * W)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (hsum1.trans hW1) (hsum2.trans hW2)
          (sum_nonneg fun l hl => div_nonneg (Nat.cast_nonneg l)
            (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
              integral_tiltedUnitSpline_sq_pos hc0 l))
          (by dsimp only [W]; positivity))
        (by positivity)
    _ = (16 * K₀ ^ 2 / κ ^ 2) * W ^ 2 * r ^ 2 := by ring

/-! ### Energy-Rescaled Subspace Floor and Sub-One-Eighth Positivity -/

/-- **Deterministic energy-rescaled subspace floor.**
Whenever the polarized Gram factor and the relative bilinear residual double sum on `Icc 1 Q` are
small, `spectralFloorWeilMatrix c N` retains at least one-quarter of the full completed conductor
energy sum `(1 / 4) * ∑_{m=1}^Q E_m(c) * a_m^2`. -/
theorem spectralFloorWeilMatrix_subspace_inner_ge_of_bilinear_budget
    {Q N : ℕ} {c : ℝ} (hQ1 : 1 ≤ Q) (hMN : max 2 Q * max 2 Q ≤ N)
    (hL0 : 0 < Real.log (N : ℝ)) (hc1 : 1 ≤ c)
    (hgram_small : 9 * (2 * (|completeWeilSelfFinitePart tiltedUnitSpline 1| + 5) /
        tiltedSplineSpectralFloorConstant + 1) *
        (1 + Real.log (max 2 Q : ℕ)) ^ 2 * c ^ 4 / Real.log N ≤ 1 / 4)
    (hbilin_small : (∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
        |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy tiltedUnitSpline c m •
              normalizedRamanujanHorizonVector m N,
          normalizedRamanujanHorizonVector l N⟫| ^ 2 /
          (completedConductorEnergy tiltedUnitSpline c m *
            completedConductorEnergy tiltedUnitSpline c l)) ≤ 1 / 64)
    (a : ℕ → ℝ) :
    (1 / 4 : ℝ) *
        (∑ m ∈ Icc 1 Q, completedConductorEnergy tiltedUnitSpline c m * a m ^ 2) ≤
      ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
          (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N),
        ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N⟫ := by
  let κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  let s := κ / (2 * c ^ 7)
  have hs_pos : 0 < s := by dsimp only [s]; positivity
  let E : ℕ → ℝ := fun m => completedConductorEnergy tiltedUnitSpline c m
  let Etil : ℕ → ℝ := fun m => E m - s
  have hEtil_ge_s : ∀ m ∈ Icc 1 Q, s ≤ Etil m := fun m hm =>
    spectralFloor_conductor_energy_ge hc1 (mem_Icc.mp hm).1
  have hEtil_pos : ∀ m ∈ Icc 1 Q, 0 < Etil m := fun m hm => hs_pos.trans_le (hEtil_ge_s m hm)
  have hE_le_2Etil : ∀ m ∈ Icc 1 Q, E m ≤ 2 * Etil m := fun m hm => by
    have h := hEtil_ge_s m hm; dsimp only [Etil] at h ⊢; linarith only [h]
  let S := ∑ m ∈ Icc 1 Q, Etil m * a m ^ 2
  have hS0 : 0 ≤ S := sum_nonneg fun m hm => mul_nonneg (hEtil_pos m hm).le (sq_nonneg _)
  have hS_ge_half : (1 / 2 : ℝ) * (∑ m ∈ Icc 1 Q, E m * a m ^ 2) ≤ S := by
    rw [mul_sum]
    refine sum_le_sum fun m hm => ?_
    have h := hE_le_2Etil m hm
    nlinarith only [h, sq_nonneg (a m)]
  -- Decompose `spectralFloorWeilMatrix` action into diagonal `Etil` part and residual part.
  let y := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
  let y_diag := ∑ m ∈ Icc 1 Q, (Etil m * a m) • normalizedRamanujanHorizonVector m N
  let r_vec : ℕ → EuclideanSpace ℝ (PrimeHorizonIndex N) := fun m =>
    Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (normalizedRamanujanHorizonVector m N) - E m • normalizedRamanujanHorizonVector m N
  have hexpand : ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) y, y⟫ =
      ⟪y_diag, y⟫ + ∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
        a m * a l * ⟪r_vec m, normalizedRamanujanHorizonVector l N⟫ := by
    have hact : Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) y =
        y_diag + ∑ m ∈ Icc 1 Q, a m • r_vec m := by
      dsimp only [y, y_diag]
      rw [map_sum, ← sum_add_distrib]
      refine sum_congr rfl fun m _ => ?_
      rw [map_smul, smul_smul, ← smul_add]
      congr 1
      have hres := spectralFloorWeilMatrix_residual_eq c m N
      dsimp only [r_vec, Etil, E, s, κ] at hres ⊢
      rw [← hres]; abel
    rw [hact, inner_add_left]
    congr 1
    dsimp only [y]
    rw [sum_inner]
    refine sum_congr rfl fun m _ => ?_
    rw [inner_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  -- Part 1: Polarized Gram discrepancy `|⟪y_diag, y⟫ - S| ≤ (1 / 4) * S`.
  let M_Q := max 2 Q
  have hMQ2 : 2 ≤ M_Q := le_max_left 2 Q
  have hQ_MQ : Q ≤ M_Q := le_max_right 2 Q
  let C_E := |completeWeilSelfFinitePart tiltedUnitSpline 1| + 5
  have hCE_pos : 0 < C_E := by dsimp only [C_E]; positivity
  have hEtil_ub : ∀ m ∈ Icc 1 Q, Etil m ≤ C_E * (1 + Real.log (M_Q : ℝ)) := by
    intro m hm
    obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hmM : (m : ℝ) ≤ M_Q := by exact_mod_cast (hmQ.trans hQ_MQ)
    have hlogm : Real.log m ≤ Real.log (M_Q : ℝ) := Real.log_le_log hm0 hmM
    have hlogM0 : 0 ≤ Real.log (M_Q : ℝ) := Real.log_natCast_nonneg M_Q
    have hE_anti := completedConductorEnergy_anti contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos zero_lt_one hc1 hm1
    have hE1_ub := completedConductorEnergy_le_of_one_le contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos le_rfl hm1
    have h1 : Etil m ≤ E m := by dsimp only [Etil]; linarith only [hs_pos]
    have habs0 := abs_nonneg (completeWeilSelfFinitePart tiltedUnitSpline 1)
    dsimp only [C_E, E] at h1 ⊢
    nlinarith only [h1, hE_anti, hE1_ub, hlogm, hlogM0, habs0]
  have hgram_bound : |⟪y_diag, y⟫ - S| ≤ (1 / 4 : ℝ) * S := by
    let a' : ℕ → ℝ := fun m => if m ≤ Q then a m else 0
    let d' : ℕ → ℝ := fun m => if m ≤ Q then Etil m * a m else 0
    have hy_eq : (∑ m ∈ Icc 1 M_Q, a' m • normalizedRamanujanHorizonVector m N) = y := by
      dsimp only [y, a']
      symm
      refine sum_subset (Icc_subset_Icc_right hQ_MQ) fun m hm hnot => ?_
      have hnQ : ¬ m ≤ Q := fun h => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, h⟩)
      simp only [if_neg hnQ, zero_smul]
    have hyd_eq : (∑ m ∈ Icc 1 M_Q, d' m • normalizedRamanujanHorizonVector m N) = y_diag := by
      dsimp only [y_diag, d']
      symm
      refine sum_subset (Icc_subset_Icc_right hQ_MQ) fun m hm hnot => ?_
      have hnQ : ¬ m ≤ Q := fun h => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, h⟩)
      simp only [if_neg hnQ, zero_smul]
    have hS_eq : (∑ m ∈ Icc 1 M_Q, d' m * a' m) = S := by
      dsimp only [S, d', a']
      symm
      refine (sum_congr rfl fun m hm => ?_).trans
        (sum_subset (Icc_subset_Icc_right hQ_MQ) fun m hm hnot => ?_).symm
      · rw [if_pos (mem_Icc.mp hm).2, if_pos (mem_Icc.mp hm).2]; ring
      · have hnQ : ¬ m ≤ Q := fun h => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, h⟩)
        simp only [if_neg hnQ, zero_mul]
    have hd_sq : (∑ m ∈ Icc 1 M_Q, d' m ^ 2) ≤ C_E * (1 + Real.log (M_Q : ℝ)) * S := by
      have heq : (∑ m ∈ Icc 1 M_Q, d' m ^ 2) = ∑ m ∈ Icc 1 Q, Etil m ^ 2 * a m ^ 2 := by
        dsimp only [d']
        symm
        refine (sum_congr rfl fun m hm => ?_).trans
          (sum_subset (Icc_subset_Icc_right hQ_MQ) fun m hm hnot => ?_).symm
        · rw [if_pos (mem_Icc.mp hm).2]; ring
        · have hnQ : ¬ m ≤ Q := fun h => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, h⟩)
          simp only [if_neg hnQ, zero_pow (by decide)]
      rw [heq, mul_sum]
      refine sum_le_sum fun m hm => ?_
      have hub := hEtil_ub m hm
      have hpos := hEtil_pos m hm
      have h1 : Etil m ^ 2 * a m ^ 2 = Etil m * (Etil m * a m ^ 2) := by ring
      rw [h1]
      exact (mul_le_mul_of_nonneg_right hub (by positivity)).trans_eq (by ring)
    have ha_sq : (∑ m ∈ Icc 1 M_Q, a' m ^ 2) ≤ (2 * c ^ 7 / κ) * S := by
      have heq : (∑ m ∈ Icc 1 M_Q, a' m ^ 2) = ∑ m ∈ Icc 1 Q, a m ^ 2 := by
        dsimp only [a']
        symm
        refine (sum_congr rfl fun m hm => by rw [if_pos (mem_Icc.mp hm).2]).trans
          (sum_subset (Icc_subset_Icc_right hQ_MQ) fun m hm hnot => ?_).symm
        have hnQ : ¬ m ≤ Q := fun h => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, h⟩)
        simp only [if_neg hnQ, zero_pow (by decide)]
      rw [heq, mul_sum]
      refine sum_le_sum fun m hm => ?_
      have hge := hEtil_ge_s m hm
      have h1 : a m ^ 2 ≤ (1 / s) * (Etil m * a m ^ 2) := by
        rw [one_div_mul_eq_div, le_div_iff₀ hs_pos, mul_comm]
        exact mul_le_mul_of_nonneg_right hge (sq_nonneg _)
      exact h1.trans_eq (by dsimp only [s]; field_simp [hκ.ne', hc0.ne']; ring)
    have hprod_sqrt : Real.sqrt (∑ m ∈ Icc 1 M_Q, d' m ^ 2) *
        Real.sqrt (∑ m ∈ Icc 1 M_Q, a' m ^ 2) ≤
        (2 * C_E / κ + 1) * (1 + Real.log (M_Q : ℝ)) * c ^ 4 * S := by
      let U := (2 * C_E / κ + 1) * (1 + Real.log (M_Q : ℝ)) * c ^ 4 * S
      have h1M : 1 ≤ 1 + Real.log (M_Q : ℝ) := by linarith [Real.log_natCast_nonneg M_Q]
      have hU0 : 0 ≤ U := by dsimp only [U]; positivity
      have hsq : (Real.sqrt (∑ m ∈ Icc 1 M_Q, d' m ^ 2) *
          Real.sqrt (∑ m ∈ Icc 1 M_Q, a' m ^ 2)) ^ 2 ≤ U ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _),
          Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
        have hm1 := mul_le_mul hd_sq ha_sq (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        have hc78 : c ^ 7 ≤ c ^ 8 := pow_le_pow_right₀ hc1 (by norm_num : 7 ≤ 8)
        have h1M_sq : 1 + Real.log (M_Q : ℝ) ≤ (1 + Real.log (M_Q : ℝ)) ^ 2 := by
          simpa only [pow_one] using pow_le_pow_right₀ h1M (by norm_num : 1 ≤ 2)
        have hC_sq : 2 * C_E / κ ≤ (2 * C_E / κ + 1) ^ 2 := by
          have : 0 ≤ 2 * C_E / κ := by positivity
          nlinarith only [this]
        have hfactor : (C_E * (1 + Real.log (M_Q : ℝ)) * S) * ((2 * c ^ 7 / κ) * S) =
            (2 * C_E / κ) * (1 + Real.log (M_Q : ℝ)) * c ^ 7 * S ^ 2 := by ring
        have hstep1 : (2 * C_E / κ) * (1 + Real.log (M_Q : ℝ)) * c ^ 7 ≤
            (2 * C_E / κ + 1) ^ 2 * (1 + Real.log (M_Q : ℝ)) ^ 2 * c ^ 8 :=
          mul_le_mul (mul_le_mul hC_sq h1M_sq (by positivity) (sq_nonneg _)) hc78
            (by positivity) (by positivity)
        have hstep2 := mul_le_mul_of_nonneg_right hstep1 (sq_nonneg S)
        have hU2 : (2 * C_E / κ + 1) ^ 2 * (1 + Real.log (M_Q : ℝ)) ^ 2 * c ^ 8 * S ^ 2 = U ^ 2 := by
          dsimp only [U]; ring
        exact hm1.trans (hfactor.trans_le (hstep2.trans_eq hU2))
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq hU0] at h
    have hp := CompletedArithmeticForms.abs_inner_sum_normalizedRamanujanHorizonVector_sub_le
      hMQ2 hMN d' a'
    rw [hyd_eq, hy_eq, hS_eq] at hp
    calc
      |⟪y_diag, y⟫ - S| ≤ 9 * (1 + Real.log (M_Q : ℝ)) / Real.log N *
            ((2 * C_E / κ + 1) * (1 + Real.log (M_Q : ℝ)) * c ^ 4 * S) :=
        hp.trans (by
          rw [mul_assoc (9 * (1 + Real.log (M_Q : ℝ)) / Real.log N)]
          exact mul_le_mul_of_nonneg_left hprod_sqrt
            (by have := Real.log_natCast_nonneg M_Q; positivity))
      _ = (9 * (2 * C_E / κ + 1) * (1 + Real.log (M_Q : ℝ)) ^ 2 * c ^ 4 / Real.log N) * S := by
        ring
      _ ≤ (1 / 4 : ℝ) * S := mul_le_mul_of_nonneg_right hgram_small hS0
  -- Part 2: Cauchy–Schwarz on the energy-rescaled bilinear residual double sum.
  have hbilin_bound : |∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
      a m * a l * ⟪r_vec m, normalizedRamanujanHorizonVector l N⟫| ≤ (1 / 4 : ℝ) * S := by
    let b : ℕ → ℝ := fun m => Real.sqrt (Etil m) * |a m|
    let u : ℕ × ℕ → ℝ := fun p =>
      |⟪r_vec p.1, normalizedRamanujanHorizonVector p.2 N⟫| / Real.sqrt (Etil p.1 * Etil p.2)
    have hb_sq_sum : (∑ p ∈ Icc 1 Q ×ˢ Icc 1 Q, (b p.1 * b p.2) ^ 2) = S ^ 2 := by
      have hb_m : ∀ m ∈ Icc 1 Q, b m ^ 2 = Etil m * a m ^ 2 := fun m hm => by
        dsimp only [b]; rw [mul_pow, Real.sq_sqrt (hEtil_pos m hm).le, sq_abs]
      rw [Finset.sum_product]
      have h1 : (∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q, (b m * b l) ^ 2) =
          (∑ m ∈ Icc 1 Q, b m ^ 2) * (∑ l ∈ Icc 1 Q, b l ^ 2) := by
        rw [Finset.sum_mul_sum]
        exact sum_congr rfl fun m _ => sum_congr rfl fun l _ => mul_pow _ _ 2
      rw [h1, sum_congr rfl hb_m, sq]
    have hu_sq_sum : (∑ p ∈ Icc 1 Q ×ˢ Icc 1 Q, u p ^ 2) ≤ 1 / 16 := by
      rw [Finset.sum_product]
      have hpt : ∀ m ∈ Icc 1 Q, ∀ l ∈ Icc 1 Q,
          u (m, l) ^ 2 ≤ 4 * (|⟪r_vec m, normalizedRamanujanHorizonVector l N⟫| ^ 2 /
            (E m * E l)) := by
        intro m hm l hl
        have hEm_pos : 0 < E m := (hEtil_pos m hm).trans_le (by dsimp only [Etil]; linarith [hs_pos])
        have hEl_pos : 0 < E l := (hEtil_pos l hl).trans_le (by dsimp only [Etil]; linarith [hs_pos])
        have hprod_pos : 0 < Etil m * Etil l := mul_pos (hEtil_pos m hm) (hEtil_pos l hl)
        dsimp only [u]
        rw [div_pow, Real.sq_sqrt hprod_pos.le]
        have hprod_le : E m * E l ≤ 4 * (Etil m * Etil l) := by
          have h := mul_le_mul (hE_le_2Etil m hm) (hE_le_2Etil l hl) hEl_pos.le (by positivity)
          linarith only [h]
        have hdiv : 1 / (Etil m * Etil l) ≤ 4 / (E m * E l) := by
          rw [div_le_div_iff₀ hprod_pos (mul_pos hEm_pos hEl_pos), one_mul]
          exact hprod_le
        calc
          |⟪r_vec m, normalizedRamanujanHorizonVector l N⟫| ^ 2 / (Etil m * Etil l) =
              |⟪r_vec m, normalizedRamanujanHorizonVector l N⟫| ^ 2 * (1 / (Etil m * Etil l)) :=
            div_eq_mul_one_div _ _
          _ ≤ |⟪r_vec m, normalizedRamanujanHorizonVector l N⟫| ^ 2 * (4 / (E m * E l)) :=
            mul_le_mul_of_nonneg_left hdiv (sq_nonneg _)
          _ = _ := by ring
      calc
        (∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q, u (m, l) ^ 2) ≤
            ∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q, 4 *
              (|⟪r_vec m, normalizedRamanujanHorizonVector l N⟫| ^ 2 / (E m * E l)) :=
          sum_le_sum fun m hm => sum_le_sum fun l hl => hpt m hm l hl
        _ = 4 * ∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
              |⟪r_vec m, normalizedRamanujanHorizonVector l N⟫| ^ 2 / (E m * E l) := by
          rw [mul_sum]; exact sum_congr rfl fun m _ => by rw [mul_sum]
        _ ≤ 4 * (1 / 64) := mul_le_mul_of_nonneg_left hbilin_small (by norm_num)
        _ = 1 / 16 := by norm_num
    have hdom : |∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q,
        a m * a l * ⟪r_vec m, normalizedRamanujanHorizonVector l N⟫| ≤
        ∑ p ∈ Icc 1 Q ×ˢ Icc 1 Q, (b p.1 * b p.2) * u p := by
      rw [Finset.sum_product]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l hl => ?_)
      have hsm : 0 < Real.sqrt (Etil m) := Real.sqrt_pos.mpr (hEtil_pos m hm)
      have hsl : 0 < Real.sqrt (Etil l) := Real.sqrt_pos.mpr (hEtil_pos l hl)
      rw [abs_mul, abs_mul]
      dsimp only [b, u]
      rw [Real.sqrt_mul (hEtil_pos m hm).le]
      exact le_of_eq (by field_simp [hsm.ne', hsl.ne'])
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 Q ×ˢ Icc 1 Q)
      (fun p => b p.1 * b p.2) u
    rw [hb_sq_sum] at hcs
    have hsq_le : (∑ p ∈ Icc 1 Q ×ˢ Icc 1 Q, (b p.1 * b p.2) * u p) ^ 2 ≤ ((1 / 4 : ℝ) * S) ^ 2 := by
      calc
        _ ≤ S ^ 2 * (∑ p ∈ Icc 1 Q ×ˢ Icc 1 Q, u p ^ 2) := hcs
        _ ≤ S ^ 2 * (1 / 16) := mul_le_mul_of_nonneg_left hu_sq_sum (sq_nonneg S)
        _ = ((1 / 4 : ℝ) * S) ^ 2 := by ring
    have hnonneg_sum : 0 ≤ ∑ p ∈ Icc 1 Q ×ˢ Icc 1 Q, (b p.1 * b p.2) * u p :=
      sum_nonneg fun p hp => by
        obtain ⟨hm, hl⟩ := mem_product.mp hp
        dsimp only [b, u]
        have := (hEtil_pos p.1 hm).le; have := (hEtil_pos p.2 hl).le
        positivity
    have h := Real.sqrt_le_sqrt hsq_le
    rw [Real.sqrt_sq hnonneg_sum, Real.sqrt_sq (by positivity)] at h
    exact hdom.trans h
  -- Combine diagonal floor and bilinear error.
  have hdiag_lb : (3 / 4 : ℝ) * S ≤ ⟪y_diag, y⟫ := by
    have h := (abs_le.mp hgram_bound).1
    linarith only [h]
  have hbilin_lb : -(1 / 4 : ℝ) * S ≤
      ∑ m ∈ Icc 1 Q, ∑ l ∈ Icc 1 Q, a m * a l * ⟪r_vec m, normalizedRamanujanHorizonVector l N⟫ := by
    have h := (abs_le.mp hbilin_bound).1
    linarith only [h]
  rw [hexpand]
  linarith only [hdiag_lb, hbilin_lb, hS_ge_half]

/-- **Polylogarithmic conductor subspace coercivity below `1 / 8`.**
For every `0 < α < 1 / 8` and `0 < q` with `α + 2 * q < 1`, eventually in `N`,
`spectralFloorWeilMatrix c N` dominates `(1 / 4) * ∑_{m=1}^{Q₁} E_m(c) * a_m^2` uniformly across
`1 ≤ c ≤ (log N)^α` at cutoff `Q₁ = ⌊(log N)^q⌋₊`. -/
theorem eventually_tiltedUnitSpline_polylog_conductorSubspace_energy_ge
    {α q : ℝ} (hα : 0 < α) (hα_lt : α < oneEighthPowerLogExponent)
    (hq : 0 < q) (hαq : α + 2 * q < 1) :
    ∀ᶠ N : ℕ in atTop,
      let Q₁ := ⌊Real.log (N : ℝ) ^ q⌋₊
      ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α → ∀ a : ℕ → ℝ,
        (1 / 4 : ℝ) *
            (∑ m ∈ Icc 1 Q₁, completedConductorEnergy tiltedUnitSpline c m * a m ^ 2) ≤
          ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
              (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N),
            ∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N⟫ := by
  have hα8 : α < 1 / 8 := hα_lt
  have hq_half : q < 1 / 2 := by linarith only [hα, hαq]
  let δ := min (1 - 8 * α) (1 - (α + 2 * q))
  have hδ : 0 < δ := lt_min (by linarith only [hα8]) (by linarith only [hαq])
  let ν := δ / 20
  have hν : 0 < ν := by dsimp only [ν]; positivity
  let k : ℕ := ⌈1 / (2 * ν)⌉₊ + 1
  have hk : 1 ≤ k := by dsimp only [k]; omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hrate_k : 1 / (k : ℝ) ≤ 2 * ν := by
    have hceil := Nat.le_ceil (1 / (2 * ν))
    have h2νk : 1 ≤ (2 * ν) * (k : ℝ) := by
      have h := (div_le_iff₀ (by positivity : 0 < 2 * ν)).mp hceil
      dsimp only [k]; push_cast; nlinarith only [h, hν]
    exact (div_le_iff₀ hk0).mpr h2νk
  have hexp1 : 8 * α + 2 * ν + 1 / (k : ℝ) - 1 ≤ -ν := by
    have h1 : δ ≤ 1 - 8 * α := min_le_left _ _
    dsimp only [ν] at hrate_k ⊢; linarith only [h1, hrate_k, hδ]
  have hexp2 : α + 2 * q + 4 * ν + 1 / (k : ℝ) - 1 ≤ -ν := by
    have h2 : δ ≤ 1 - (α + 2 * q) := min_le_right _ _
    dsimp only [ν] at hrate_k ⊢; linarith only [h2, hrate_k, hδ]
  obtain ⟨K_bilin, hK_bilin, hbilin⟩ := exists_tiltedUnitSpline_bilinear_relative_residual_sum_le
  let C_gram := 9 * (2 * (|completeWeilSelfFinitePart tiltedUnitSpline 1| + 5) /
    tiltedSplineSpectralFloorConstant + 1)
  have hCgram_pos : 0 < C_gram := by
    have := tiltedSplineSpectralFloorConstant_pos; dsimp only [C_gram]; positivity
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL_rpow8 : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by
    have hsm := tendsto_natCast_atTop_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).bound zero_lt_one)
    filter_upwards [hsm, eventually_ge_atTop 1] with N hN _
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact (le_abs_self _).trans (by
      simpa only [Function.comp_def, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hN0 _), one_mul] using hN)
  filter_upwards [hbilin q hq.le k hk, hL_rpow8,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1 hν 1),
    ((tendsto_rpow_atTop hq).comp hLlim).eventually_ge_atTop 2,
    ((tendsto_rpow_atTop hν).comp hLlim).eventually_ge_atTop (max (4 * C_gram) (1024 * K_bilin)),
    hLlim.eventually_ge_atTop 4, eventually_ge_atTop 256] with
      N hbilinN hL8 hpoly hQ_ge2 hν_big hL4 hN256
  dsimp only [Function.comp_def] at hpoly hQ_ge2 hν_big
  dsimp only
  let L := Real.log (N : ℝ)
  let Q₁ := ⌊L ^ q⌋₊
  intro c hc1 hcup a
  have hL1 : 1 ≤ L := by linarith only [hL4]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 1 ≤ N by omega)
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hQ2 : 2 ≤ Q₁ := Nat.le_floor hQ_ge2
  have hQ1 : 1 ≤ Q₁ := by omega
  have hMQ_eq : max 2 Q₁ = Q₁ := max_eq_right hQ2
  have hQ_le : (Q₁ : ℝ) ≤ L ^ q := Nat.floor_le (by positivity)
  have hL8_pow : L ^ (8 : ℕ) ≤ (N : ℝ) := by
    have hp := pow_le_pow_left₀ hL0.le hL8 8
    have he : ((N : ℝ) ^ (1 / 8 : ℝ)) ^ (8 : ℕ) = (N : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    exact hp.trans_eq he
  have hcpow : ∀ j : ℕ, c ^ j ≤ L ^ ((j : ℝ) * α) := fun j => by
    have hp := pow_le_pow_left₀ hc0.le hcup j
    have he : (L ^ α) ^ j = L ^ ((j : ℝ) * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hp.trans_eq he
  have hcL : c ≤ L := hcup.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα8] : α ≤ 1))
  have hwidth : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) := by
    have he1 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have h144 : 4 * (Real.exp 1 + 3) ^ 2 ≤ 144 := by nlinarith only [he1, Real.exp_pos 1]
    have hc2_L : c ^ 2 ≤ L := (hcpow 2).trans (by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num; linarith only [hα8]))
    have h144_L7 : (144 : ℝ) ≤ L ^ 7 :=
      (by norm_num : (144 : ℝ) ≤ 4 ^ 7).trans (pow_le_pow_left₀ (by norm_num) hL4 7)
    calc
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ 144 * L :=
        mul_le_mul h144 hc2_L (sq_nonneg _) (by norm_num)
      _ ≤ L ^ 7 * L := mul_le_mul_of_nonneg_right h144_L7 hL0.le
      _ = L ^ 8 := by ring
      _ ≤ (N : ℝ) := hL8_pow
  have hMN : max 2 Q₁ * max 2 Q₁ ≤ N := by
    rw [hMQ_eq]
    have hQ_sq : (Q₁ : ℝ) ^ 2 ≤ L := by
      have hp := pow_le_pow_left₀ (Nat.cast_nonneg Q₁) hQ_le 2
      have he : (L ^ q) ^ (2 : ℕ) = L ^ (2 * q) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
      exact (hp.trans_eq he).trans (by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hq_half]))
    have hLN : L ≤ (N : ℝ) := (by simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 8)).trans hL8_pow
    have hcast : ((Q₁ * Q₁ : ℕ) : ℝ) ≤ (N : ℝ) := by
      simpa only [sq, Nat.cast_mul] using hQ_sq.trans hLN
    exact_mod_cast hcast
  have hpoly1 : 1 + Real.log L ≤ L ^ ν := by simpa only [one_mul, pow_one] using hpoly
  have hQ0 : (0 : ℝ) < Q₁ := by exact_mod_cast hQ1
  have hHQ : 1 + Real.log (Q₁ : ℝ) ≤ L ^ ν := by
    have hh := Real.log_le_log hQ0 hQ_le
    rw [Real.log_rpow hL0] at hh
    have hm := mul_le_mul_of_nonneg_right (hq_half.le.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
      (Real.log_nonneg hL1)
    linarith only [hh, hm, hpoly1]
  have hHQsq : (1 + Real.log (Q₁ : ℝ)) ^ 2 ≤ L ^ (2 * ν) := by
    have hh := pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg Q₁]) hHQ 2
    have he : (L ^ ν) ^ (2 : ℕ) = L ^ (2 * ν) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hh.trans_eq he
  have hVc : 1 + Real.log c ≤ L ^ ν := by
    linarith only [Real.log_le_log hc0 hcL, hpoly1]
  have hVcsq : (1 + Real.log c) ^ 2 ≤ L ^ (2 * ν) := by
    have hh := pow_le_pow_left₀ (by linarith [Real.log_nonneg hc1]) hVc 2
    have he : (L ^ ν) ^ (2 : ℕ) = L ^ (2 * ν) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hh.trans_eq he
  have hmul_ν : L ^ ν * L ^ (-ν) = 1 := by
    rw [← Real.rpow_add hL0, show ν + (-ν) = 0 by ring, Real.rpow_zero]
  -- Bound the polarized Gram discrepancy factor.
  have hgram_small : C_gram * (1 + Real.log (max 2 Q₁ : ℕ)) ^ 2 * c ^ 4 / L ≤ 1 / 4 := by
    rw [hMQ_eq]
    have hexp_g : 2 * ν + 4 * α - 1 ≤ -ν := by
      have h1 : δ ≤ 1 - 8 * α := min_le_left _ _
      dsimp only [ν]; linarith only [h1, hα8, hδ]
    have hc4 := hcpow 4
    have h4C : 4 * C_gram ≤ L ^ ν := le_trans (le_max_left _ _) hν_big
    calc
      C_gram * (1 + Real.log (Q₁ : ℝ)) ^ 2 * c ^ 4 / L ≤
          C_gram * (L ^ (2 * ν) * L ^ ((4 : ℝ) * α) / L) := by
        rw [mul_assoc C_gram, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right
            (mul_le_mul hHQsq hc4 (by positivity) (by positivity)) hL0.le) hCgram_pos.le
      _ = C_gram * L ^ (2 * ν + 4 * α - 1) := by
        congr 1
        rw [← Real.rpow_add hL0, ← Real.rpow_sub hL0, Real.rpow_one]
        congr 1; ring
      _ ≤ C_gram * L ^ (-ν) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 hexp_g) hCgram_pos.le
      _ = (1 / 4 : ℝ) * ((4 * C_gram) * L ^ (-ν)) := by ring
      _ ≤ (1 / 4 : ℝ) * (L ^ ν * L ^ (-ν)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4C (by positivity)) (by norm_num)
      _ = 1 / 4 := by rw [hmul_ν, mul_one]
  -- Bound the double-sum relative bilinear residual budget.
  have hbilin_small : (∑ m ∈ Icc 1 Q₁, ∑ l ∈ Icc 1 Q₁,
      |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m •
            normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector l N⟫| ^ 2 /
        (completedConductorEnergy tiltedUnitSpline c m *
          completedConductorEnergy tiltedUnitSpline c l)) ≤ 1 / 64 := by
    have hraw := hbilinN c hc1 hwidth Q₁ hQ_le
    let r_lead := c * (1 + Real.log c) ^ 2 * L ^ (1 / (k : ℝ)) / L
    have hr_lead0 : 0 ≤ r_lead := by
      dsimp only [r_lead]
      have : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
      positivity
    have hr_sub : c ^ 5 * L / (N : ℝ) ≤ r_lead := by
      have hc5_invL : c ^ 5 * L / (N : ℝ) ≤ 1 / L := by
        rw [div_le_div_iff₀ hN0 hL0, one_mul]
        have hc5_L5 : c ^ 5 ≤ L ^ 5 := pow_le_pow_left₀ hc0.le hcL 5
        have hL78 : L ^ 7 ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num : 7 ≤ 8)
        calc
          c ^ 5 * L * L ≤ L ^ 5 * L * L :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc5_L5 hL0.le) hL0.le
          _ = L ^ 7 := by ring
          _ ≤ (N : ℝ) := hL78.trans hL8_pow
      have hinvL_lead : 1 / L ≤ r_lead := by
        dsimp only [r_lead]
        apply div_le_div_of_nonneg_right _ hL0.le
        have h1c_sq : 1 ≤ (1 + Real.log c) ^ 2 :=
          one_le_pow₀ (by linarith [Real.log_nonneg hc1])
        have hs1 : 1 ≤ L ^ (1 / (k : ℝ)) := Real.one_le_rpow hL1 (by positivity)
        exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hc1 h1c_sq) hs1
      exact hc5_invL.trans hinvL_lead
    have hr_lead_ub : r_lead ≤ L ^ (α + 2 * ν + 1 / (k : ℝ) - 1) := by
      dsimp only [r_lead]
      have hnum : c * (1 + Real.log c) ^ 2 * L ^ (1 / (k : ℝ)) ≤
          L ^ α * L ^ (2 * ν) * L ^ (1 / (k : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hcup hVcsq (sq_nonneg _) (by positivity)) (by positivity)
      calc
        c * (1 + Real.log c) ^ 2 * L ^ (1 / (k : ℝ)) / L ≤
            (L ^ α * L ^ (2 * ν) * L ^ (1 / (k : ℝ))) / L :=
          div_le_div_of_nonneg_right hnum hL0.le
        _ = L ^ (α + 2 * ν + 1 / (k : ℝ) - 1) := by
          rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_sub hL0, Real.rpow_one]
    have ht1 : c ^ 7 * r_lead ≤ L ^ (-ν) := by
      calc
        c ^ 7 * r_lead ≤ L ^ ((7 : ℝ) * α) * L ^ (α + 2 * ν + 1 / (k : ℝ) - 1) :=
          mul_le_mul (hcpow 7) hr_lead_ub hr_lead0 (by positivity)
        _ = L ^ (8 * α + 2 * ν + 1 / (k : ℝ) - 1) := by
          rw [← Real.rpow_add hL0]; congr 1; ring
        _ ≤ L ^ (-ν) := Real.rpow_le_rpow_of_exponent_le hL1 hexp1
    have ht2 : (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2 * r_lead ≤ L ^ (-ν) := by
      have hQ2_pow : (Q₁ : ℝ) ^ 2 ≤ L ^ (2 * q) := by
        have hp := pow_le_pow_left₀ (Nat.cast_nonneg Q₁) hQ_le 2
        have he : (L ^ q) ^ (2 : ℕ) = L ^ (2 * q) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
        exact hp.trans_eq he
      calc
        (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2 * r_lead ≤
            (L ^ (2 * q) * L ^ (2 * ν)) * L ^ (α + 2 * ν + 1 / (k : ℝ) - 1) :=
          mul_le_mul (mul_le_mul hQ2_pow hHQsq (sq_nonneg _) (by positivity))
            hr_lead_ub hr_lead0 (by positivity)
        _ = L ^ (α + 2 * q + 4 * ν + 1 / (k : ℝ) - 1) := by
          rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; congr 1; ring
        _ ≤ L ^ (-ν) := Real.rpow_le_rpow_of_exponent_le hL1 hexp2
    let W := c ^ 7 + (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2
    let r_full := r_lead + c ^ 5 * L / (N : ℝ)
    have hWr_le : W * r_full ≤ 4 * L ^ (-ν) := by
      have hr2 : r_full ≤ 2 * r_lead := by dsimp only [r_full]; linarith only [hr_sub]
      have hW0 : 0 ≤ W := by dsimp only [W]; positivity
      calc
        W * r_full ≤ W * (2 * r_lead) := mul_le_mul_of_nonneg_left hr2 hW0
        _ = 2 * (c ^ 7 * r_lead + (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2 * r_lead) := by
          dsimp only [W]; ring
        _ ≤ 4 * L ^ (-ν) := by linarith only [ht1, ht2]
    have hWr0 : 0 ≤ W * r_full := by dsimp only [W, r_full]; positivity
    have hLν_le1 : L ^ (-ν) ≤ 1 := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν])
    have hLν_sq : (L ^ (-ν)) ^ 2 ≤ L ^ (-ν) := by
      rw [sq]; exact mul_le_of_le_one_right (by positivity) hLν_le1
    have h1024 : 1024 * K_bilin ≤ L ^ ν := le_trans (le_max_right _ _) hν_big
    calc
      _ ≤ K_bilin * W ^ 2 * r_full ^ 2 := hraw
      _ = K_bilin * (W * r_full) ^ 2 := by ring
      _ ≤ K_bilin * (4 * L ^ (-ν)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hWr0 hWr_le 2) hK_bilin.le
      _ = 16 * K_bilin * (L ^ (-ν)) ^ 2 := by ring
      _ ≤ 16 * K_bilin * L ^ (-ν) :=
        mul_le_mul_of_nonneg_left hLν_sq (by positivity)
      _ = (1 / 64 : ℝ) * ((1024 * K_bilin) * L ^ (-ν)) := by ring
      _ ≤ (1 / 64 : ℝ) * (L ^ ν * L ^ (-ν)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1024 (by positivity)) (by norm_num)
      _ = 1 / 64 := by rw [hmul_ν, mul_one]
  exact spectralFloorWeilMatrix_subspace_inner_ge_of_bilinear_budget hQ1 hMN hL0 hc1
    hgram_small hbilin_small a

/-- **Sub-one-eighth spectral floor on every fixed finite conductor packet (`Σ-2` closed up to `1 / 8`).**
For every fixed conductor cutoff `M₀ : ℕ` and every `0 < α < 1 / 8`, eventually in `N`,
`completeWeilEnergy tiltedUnitSpline c N` dominates `(κ₀ / (2 c^7)) * ‖y‖^2` on the entire packet
subspace `conductorSubspace M₀ N` across `1 ≤ c ≤ (log N)^α`. -/
theorem eventually_tiltedUnitSpline_fixed_conductorSubspace_energy_ge_below_one_eighth
    (M₀ : ℕ) {α : ℝ} (hα : 0 < α) (hα_lt : α < oneEighthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      ∀ y ∈ conductorSubspace M₀ N,
        (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖y‖ ^ 2 ≤
          completeWeilEnergy tiltedUnitSpline c N y := by
  have hα8 : α < 1 / 8 := hα_lt
  have hq : (0 : ℝ) < 1 / 4 := by norm_num
  have hαq : α + 2 * (1 / 4 : ℝ) < 1 := by linarith only [hα8]
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_tiltedUnitSpline_polylog_conductorSubspace_energy_ge hα hα_lt hq hαq,
    ((tendsto_rpow_atTop hq).comp hLlim).eventually_ge_atTop (M₀ : ℝ)] with N hpolyN hM_le
  dsimp only [Function.comp_def] at hM_le
  let Q₁ := ⌊Real.log (N : ℝ) ^ (1 / 4 : ℝ)⌋₊
  have hMQ : M₀ ≤ Q₁ := Nat.le_floor hM_le
  intro c hc1 hcup y hy
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  obtain ⟨a, -, rfl⟩ := (mem_conductorSubspace_iff (M := M₀) (N := N) (x := y)).mp hy
  let a' : ℕ → ℝ := fun m => if m ≤ M₀ then a m else 0
  have hy_eq : (∑ m ∈ Icc 1 M₀, a m • normalizedRamanujanHorizonVector m N) =
      ∑ m ∈ Icc 1 Q₁, a' m • normalizedRamanujanHorizonVector m N := by
    dsimp only [a']
    refine (sum_congr rfl fun m hm => by rw [if_pos (mem_Icc.mp hm).2]).trans
      (sum_subset (Icc_subset_Icc_right hMQ) fun m hm hnot => ?_)
    have hnM : ¬ m ≤ M₀ := fun h => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, h⟩)
    simp only [if_neg hnM, zero_smul]
  have hfloor := hpolyN c hc1 hcup a'
  rw [← hy_eq, spectralFloorWeilMatrix_inner] at hfloor
  have hnonneg : 0 ≤ (1 / 4 : ℝ) *
      (∑ m ∈ Icc 1 Q₁, completedConductorEnergy tiltedUnitSpline c m * a' m ^ 2) :=
    mul_nonneg (by norm_num) (sum_nonneg fun m _ =>
      mul_nonneg (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline
        tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 m) (sq_nonneg _))
  linarith only [hfloor, hnonneg]

/-- **Strict positivity on every fixed finite conductor packet up to `1 / 8`.** -/
theorem eventually_tiltedUnitSpline_fixed_conductorSubspace_pos_below_one_eighth
    (M₀ : ℕ) {α : ℝ} (hα : 0 < α) (hα_lt : α < oneEighthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      ∀ y ∈ conductorSubspace M₀ N, y ≠ 0 →
        0 < completeWeilEnergy tiltedUnitSpline c N y := by
  filter_upwards [eventually_tiltedUnitSpline_fixed_conductorSubspace_energy_ge_below_one_eighth
    M₀ hα hα_lt] with N hN c hc1 hcup y hy hy0
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hpos : 0 < (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖y‖ ^ 2 :=
    mul_pos (div_pos tiltedSplineSpectralFloorConstant_pos (by positivity))
      (sq_pos_of_pos (norm_pos_iff.mpr hy0))
  exact hpos.trans_le (hN c hc1 hcup y hy)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_bilinear_conductor_residual_variable_rate
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_bilinear_conductor_residual_variable_rate
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_quadratic_inv_energy_residual_sum_le
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_bilinear_relative_residual_sum_le
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_polylog_conductorSubspace_energy_ge
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_fixed_conductorSubspace_energy_ge_below_one_eighth
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_fixed_conductorSubspace_pos_below_one_eighth

