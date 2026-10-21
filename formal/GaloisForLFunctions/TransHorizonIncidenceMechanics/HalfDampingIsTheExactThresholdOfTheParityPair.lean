import GaloisForLFunctions.TransHorizonIncidenceMechanics.RealCharacterParityPairsAndTheParityBarrier
import GaloisForLFunctions.RHTower.GaussSpikeMass
import GaloisForLFunctions.HTGeometry.RpowHarmonicTailAsymptotic

/-!
# Half damping is the exact threshold of the parity pair

Let `𝒞(K, ε)` be the weights with `|c(d)| ≤ K d^{-ε}`. Writing `⌊n/d⌋ = n/d − {n/d}` along the
counting step `k ↦ k + 1` and splitting the mean at the prefix,
`A_c(n) = Σ_{d≤n} c(d)(⌊n/d⌋ − n/d) − n Σ_{d>n} c(d)/d`,
so `|A_c(n)| ≤ K C_ε n^{1−ε}` with `C_ε = 1 + 1/(1−ε) + 1/ε` (integral comparison for the head,
`Σ_{d>n} d^{-1-ε} ≤ n^{-ε}/ε` for the tail), and the pronic cell `n` carries at most
`(K C_ε)² n^{-2ε}`.

* **Above half damping** the receiver energy is bounded on all of `𝒞(K, ε)` by one constant, so no
  parity pair exists and receiver boundedness is trivially a function of the amplitudes.
* **At and below half damping** the receiver grows at most like `Σ_{n≤T} n^{-2ε}` (`≍ T^{1−2ε}`, and
  `log T` at `ε = 1/2`), and the positive twin of every real character attains this rate: the parity
  pairs of real characters are extremal, bounded against maximal growth.
* Hence, for every `K > 0` and `ε > 0`, receiver boundedness on `𝒞(K, ε)` is a function of the
  Ramanujan amplitudes **if and only if** `ε > 1/2`.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The universal prefix bound -/

theorem summable_div_of_dampedClass {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ} (hc : DampedClass K ε c) :
    Summable (fun d : ℕ => c d / d) := by
  refine ((Real.summable_nat_rpow.mpr (by linarith : -1 - ε < -1)).mul_left K).of_norm_bounded
    fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [Real.zero_rpow (show -1 - ε ≠ 0 by linarith)]
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
    calc |c d| ≤ K * (d : ℝ) ^ (-ε) := hc d
      _ = K * (d : ℝ) ^ (-1 - ε) * d := by
        rw [mul_assoc, ← Real.rpow_add_one hd0.ne', show -1 - ε + 1 = -ε by ring]

theorem nonneg_of_dampedClass {K ε : ℝ} {c : ℕ → ℝ} (hc : DampedClass K ε c) : 0 ≤ K := by
  have h := hc 1
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at h
  exact (abs_nonneg _).trans h

/-- The class shrinks as the damping grows. -/
theorem dampedClass_mono {K ε ε' : ℝ} (hε' : 0 < ε') (hεε' : ε' ≤ ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) : DampedClass K ε' c := fun d => by
  have hK := nonneg_of_dampedClass hc
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h := hc 0
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero] at h
    exact h.trans (mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg 0) _))
  · have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    exact (hc d).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) hK)

theorem abs_natDiv_sub_div_le (n d : ℕ) (hd : 0 < d) : |((n / d : ℕ) : ℝ) - (n : ℝ) / d| ≤ 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hle : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le
  have hlt : (n : ℝ) / d < ((n / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hd0]
    have h := Nat.lt_mul_div_succ n hd
    have h' : (n : ℝ) < d * (((n / d : ℕ) : ℝ) + 1) := by exact_mod_cast h
    linarith
  rw [abs_le]; constructor <;> linarith

/-- **The exact split of the prefix.** `A_c(n) = Σ_{d≤n} c(d)(⌊n/d⌋ − n/d) − n Σ_{d>n} c(d)/d`. -/
theorem weightCenteredPrefix_eq_split (c : ℕ → ℝ) (hs : Summable (fun d : ℕ => c d / d)) (n : ℕ) :
    weightCenteredPrefix c (∑' d : ℕ, c d / d) n =
      ∑ d ∈ Icc 1 n, c d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d) -
        n * ∑' k : ℕ, c (k + (n + 1)) / ((k + (n + 1) : ℕ) : ℝ) := by
  have hr : range (n + 1) = insert 0 (Icc 1 n) := by
    ext d; simp only [mem_range, mem_insert, mem_Icc]; omega
  have hhead : ∑ d ∈ range (n + 1), c d / d = ∑ d ∈ Icc 1 n, c d / d := by
    rw [hr, sum_insert (by simp)]; simp
  rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor, ← hs.sum_add_tsum_nat_add (n + 1), hhead]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have h : ∀ d ∈ Icc 1 n, c d * ((n : ℝ) / d) = c d / d * n := fun d _ => by ring
  rw [Finset.sum_congr rfl h, ← Finset.sum_mul]
  ring

/-- **The universal prefix bound** `|A_c(n)| ≤ K C_ε n^{1−ε}` on `𝒞(K, ε)`, `0 < ε < 1`. -/
theorem abs_weightCenteredPrefix_le_of_dampedClass {K ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {c : ℕ → ℝ} (hc : DampedClass K ε c) {n : ℕ} (hn : 1 ≤ n) :
    |weightCenteredPrefix c (∑' d : ℕ, c d / d) n| ≤
      K * (1 + 1 / (1 - ε) + 1 / ε) * (n : ℝ) ^ (1 - ε) := by
  have hK := nonneg_of_dampedClass hc
  rw [weightCenteredPrefix_eq_split c (summable_div_of_dampedClass hε hc) n]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set P := (n : ℝ) ^ (1 - ε) with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
  have hhead : |∑ d ∈ Icc 1 n, c d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d)| ≤ K * (1 + P / (1 - ε)) := by
    calc _ ≤ ∑ d ∈ Icc 1 n, |c d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 n, K * (d : ℝ) ^ (-ε) := sum_le_sum fun d hd => by
          have hd : 0 < d := by have := (mem_Icc.mp hd).1; omega
          rw [abs_mul]
          calc |c d| * |((n / d : ℕ) : ℝ) - (n : ℝ) / d| ≤ |c d| * 1 :=
                mul_le_mul_of_nonneg_left (abs_natDiv_sub_div_le n d hd) (abs_nonneg _)
            _ ≤ _ := by rw [mul_one]; exact hc d
      _ = K * ∑ d ∈ Icc 1 n, (d : ℝ) ^ (-ε) := by rw [mul_sum]
      _ ≤ K * (1 + P / (1 - ε)) :=
          mul_le_mul_of_nonneg_left (RHTower.sum_rpow_neg_head_le hε hε1 n) hK
  have htail : |∑' k : ℕ, c (k + (n + 1)) / ((k + (n + 1) : ℕ) : ℝ)| ≤ K * ((n : ℝ) ^ (-ε) / ε) := by
    have hbound : ∀ k : ℕ, ‖c (k + (n + 1)) / ((k + (n + 1) : ℕ) : ℝ)‖ ≤
        K * ((n : ℝ) + 1 + k) ^ (-ε - 1) := by
      intro k
      have hcast : ((k + (n + 1) : ℕ) : ℝ) = (n : ℝ) + 1 + k := by push_cast; ring
      have hpos : (0 : ℝ) < (n : ℝ) + 1 + k := by positivity
      rw [Real.norm_eq_abs, abs_div, hcast, abs_of_pos hpos, div_le_iff₀ hpos]
      calc |c (k + (n + 1))| ≤ K * (((k + (n + 1) : ℕ) : ℝ)) ^ (-ε) := hc _
        _ = K * ((n : ℝ) + 1 + k) ^ (-ε - 1) * ((n : ℝ) + 1 + k) := by
          rw [hcast, mul_assoc, ← Real.rpow_add_one hpos.ne', show -ε - 1 + 1 = -ε by ring]
    have hsum := (HTGeometry.summable_shift_rpow (q := -ε) (by linarith) n).mul_left K
    calc _ ≤ ∑' k : ℕ, K * ((n : ℝ) + 1 + k) ^ (-ε - 1) := tsum_of_norm_bounded hsum.hasSum hbound
      _ = K * ∑' k : ℕ, ((n : ℝ) + 1 + k) ^ (-ε - 1) := tsum_mul_left
      _ ≤ K * ((n : ℝ) ^ (-ε) / ε) := by
          refine mul_le_mul_of_nonneg_left ?_ hK
          have h := HTGeometry.tsum_shift_rpow_le (q := -ε) (by linarith) hn
          rwa [neg_neg] at h
  have hnP : (n : ℝ) * (n : ℝ) ^ (-ε) = P := by
    rw [hP, show (1 : ℝ) - ε = 1 + -ε by ring, Real.rpow_add hn0, Real.rpow_one]
  calc _ ≤ |∑ d ∈ Icc 1 n, c d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d)| +
        |(n : ℝ) * ∑' k : ℕ, c (k + (n + 1)) / ((k + (n + 1) : ℕ) : ℝ)| := abs_sub _ _
    _ ≤ K * (1 + P / (1 - ε)) + n * (K * ((n : ℝ) ^ (-ε) / ε)) := by
        rw [abs_mul, abs_of_pos hn0]
        exact add_le_add hhead (mul_le_mul_of_nonneg_left htail hn0.le)
    _ = K * 1 + K * (1 / (1 - ε)) * P + K * (1 / ε) * P := by rw [← hnP]; ring
    _ ≤ K * P + K * (1 / (1 - ε)) * P + K * (1 / ε) * P := by
        gcongr
    _ = _ := by ring

/-- Every pronic cell carries at most `(K C_ε)² n^{-2ε}`. -/
theorem weightCell_le_of_dampedClass {K ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) {n : ℕ} (hn : 1 ≤ n) :
    weightCenteredPrefix c (∑' d : ℕ, c d / d) n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (K * (1 + 1 / (1 - ε) + 1 / ε)) ^ 2 * (n : ℝ) ^ (-2 * ε) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hK := nonneg_of_dampedClass hc
  have hA := abs_weightCenteredPrefix_le_of_dampedClass hε hε1 hc hn
  set A := weightCenteredPrefix c (∑' d : ℕ, c d / d) n
  set C := K * (1 + 1 / (1 - ε) + 1 / ε)
  have hsq : A ^ 2 ≤ (C * (n : ℝ) ^ (1 - ε)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
  have hpow : ((n : ℝ) ^ (1 - ε)) ^ 2 = (n : ℝ) ^ 2 * (n : ℝ) ^ (-2 * ε) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (1 - ε)) 2, ← Real.rpow_mul hn0.le,
      ← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hn0]
    congr 1; push_cast; ring
  have hQ : 0 ≤ C ^ 2 * (n : ℝ) ^ (-2 * ε) := by positivity
  rw [div_le_iff₀ (by positivity)]
  calc A ^ 2 ≤ (C * (n : ℝ) ^ (1 - ε)) ^ 2 := hsq
    _ = C ^ 2 * (n : ℝ) ^ (-2 * ε) * (n : ℝ) ^ 2 := by rw [mul_pow, hpow]; ring
    _ ≤ C ^ 2 * (n : ℝ) ^ (-2 * ε) * ((n : ℝ) * ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hQ

/-- **Maximal growth.** On `𝒞(K, ε)`, `0 < ε < 1`: `E_T(c) ≤ (K C_ε)² Σ_{n≤T} n^{-2ε}`. -/
theorem weightPronicEnergy_le_of_dampedClass {K ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) (T : ℕ) :
    weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤
      (K * (1 + 1 / (1 - ε) + 1 / ε)) ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-2 * ε) := by
  rw [weightPronicEnergy, mul_sum]
  exact sum_le_sum fun n hn => weightCell_le_of_dampedClass hε hε1 hc (mem_Icc.mp hn).1

/-- **Above half damping the receiver is bounded uniformly on the class.** -/
theorem exists_uniform_weightPronicEnergy_bound {K ε : ℝ} (hε : 1 / 2 < ε) :
    ∃ E : ℝ, ∀ c : ℕ → ℝ, DampedClass K ε c → ∀ T : ℕ,
      weightPronicEnergy c (∑' d : ℕ, c d / d) T ≤ E := by
  set ε' := min ε (3 / 4)
  have h1 : 1 / 2 < ε' := lt_min hε (by norm_num)
  have h2 : ε' < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * ε')) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine ⟨(K * (1 + 1 / (1 - ε') + 1 / ε')) ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (-2 * ε'),
    fun c hc T => ?_⟩
  refine (weightPronicEnergy_le_of_dampedClass (by linarith) h2
    (dampedClass_mono (by linarith) (min_le_left _ _) hc) T).trans ?_
  exact mul_le_mul_of_nonneg_left
    (hsum.sum_le_tsum _ fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) (sq_nonneg _)

/-! ### The twins grow at the maximal rate -/

/-- A drift of `K n (2n)^{-ε}` on `(n, 2n]`, `ε ≤ 1/2`, puts at least `(K²/4) n^{-2ε}` into the
pronic cell `n`. -/
theorem weightCell_ge_rpow_of_drift {c : ℕ → ℝ} {m K ε : ℝ} (hc : ∀ d, 0 ≤ c d)
    (hm : HasSum (fun d : ℕ => c d / d) m) (hK : 0 ≤ K) (hε2 : ε ≤ 1 / 2) {n : ℕ}
    (hn : 1 ≤ n)
    (hdrift : K * n * (2 * (n : ℝ)) ^ (-ε) ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), c d / d) :
    K ^ 2 / 4 * (n : ℝ) ^ (-2 * ε) ≤
      weightCenteredPrefix c m n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hA := weightCenteredPrefix_le_neg_drift hc hm n
  set A := weightCenteredPrefix c m n
  set Q := (n : ℝ) ^ (-2 * ε)
  have hQ : 0 ≤ Q := Real.rpow_nonneg hn0.le _
  -- `((2n)^{-ε})² = 2^{-2ε} n^{-2ε} ≥ n^{-2ε}/2`
  have h2 : ((2 * (n : ℝ)) ^ (-ε)) ^ 2 = (2 : ℝ) ^ (-2 * ε) * Q := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hn0.le]
    norm_num [Q]; ring_nf
  have h2' : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (-2 * ε) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hlow : K * n * (2 * (n : ℝ)) ^ (-ε) ≤ -A := by linarith
  have h0 : 0 ≤ K * n * (2 * (n : ℝ)) ^ (-ε) := by positivity
  have hsq : (K * n * (2 * (n : ℝ)) ^ (-ε)) ^ 2 ≤ A ^ 2 := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  have hexp : (K * n * (2 * (n : ℝ)) ^ (-ε)) ^ 2 = K ^ 2 * (n : ℝ) ^ 2 * ((2 : ℝ) ^ (-2 * ε) * Q) := by
    rw [mul_pow, h2]; ring
  have hKQ : 0 ≤ K ^ 2 * Q := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have s1 : K ^ 2 / 4 * Q * ((n : ℝ) * ((n : ℝ) + 1)) ≤ K ^ 2 * Q * ((n : ℝ) ^ 2 / 2) := by
    have : (n : ℝ) * ((n : ℝ) + 1) / 4 ≤ (n : ℝ) ^ 2 / 2 := by nlinarith
    calc K ^ 2 / 4 * Q * ((n : ℝ) * ((n : ℝ) + 1)) = K ^ 2 * Q * ((n : ℝ) * ((n : ℝ) + 1) / 4) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hKQ
  have s2 : K ^ 2 * Q * ((n : ℝ) ^ 2 / 2) ≤ K ^ 2 * (n : ℝ) ^ 2 * ((2 : ℝ) ^ (-2 * ε) * Q) := by
    have := mul_le_mul_of_nonneg_left h2' (mul_nonneg (sq_nonneg (n : ℝ)) hKQ)
    linarith
  linarith

variable {q : ℕ} [NeZero q]

theorem charTwinWeight_mem_dampedClass (χ : MulChar (ZMod q) ℤ) {ε : ℝ} (hε : 0 < ε) :
    DampedClass (|charDampedMass χ ε| / charUnitMass χ ε) ε (charTwinWeight χ ε) := fun d => by
  have hκ : 0 ≤ |charDampedMass χ ε| / charUnitMass χ ε :=
    div_nonneg (abs_nonneg _) (charUnitMass_pos χ hε).le
  have h1 : charUnit χ d ≤ 1 := by
    have h := abs_charSign_le χ d
    unfold charUnit; nlinarith [abs_nonneg (charSign χ d), sq_abs (charSign χ d)]
  rw [abs_of_nonneg (charTwinWeight_nonneg χ hε d), charTwinWeight, dampedSignWeight]
  refine mul_le_mul_of_nonneg_left ?_ hκ
  exact (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (Nat.cast_nonneg d) _)).trans_eq (one_mul _)

/-- **The real character pairs are extremal.** For every real non-principal character and every
`0 < ε ≤ 1/2`: the receiver of `χ(d)d^{-ε}` is bounded, while the receiver of its positive twin is
pinched between `a Σ_{8q≤n≤T} n^{-2ε}` and `b Σ_{n≤T} n^{-2ε}`, the maximal growth on its class. -/
theorem char_parityPair_extremal {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    (∃ E : ℝ, ∀ T : ℕ,
        weightPronicEnergy (dampedSignWeight (charSign χ) ε) (charDampedMass χ ε) T ≤ E) ∧
    ∃ a b : ℝ, 0 < a ∧ ∀ T : ℕ,
      a * ∑ n ∈ Icc (8 * q) T, (n : ℝ) ^ (-2 * ε) ≤
          weightPronicEnergy (charTwinWeight χ ε) |charDampedMass χ ε| T ∧
        weightPronicEnergy (charTwinWeight χ ε) |charDampedMass χ ε| T ≤
          b * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-2 * ε) := by
  have hL := charDampedMass_ne_zero (χ := χ) hε
  have hq0 : 0 < q := NeZero.pos q
  set κ := |charDampedMass χ ε| / charUnitMass χ ε
  have hκ : 0 < κ := div_pos (abs_pos.mpr hL) (charUnitMass_pos χ hε)
  set K := κ / (8 * q)
  have hK : 0 < K := div_pos hκ (by positivity)
  have hmean : ∑' d : ℕ, charTwinWeight χ ε d / d = |charDampedMass χ ε| :=
    (hasSum_charTwinWeight_div χ hε).tsum_eq
  refine ⟨(char_parityPair hχ hε hε2).2.2.1, K ^ 2 / 4,
    (κ * (1 + 1 / (1 - ε) + 1 / ε)) ^ 2, by positivity, fun T => ⟨?_, ?_⟩⟩
  · have hcell : ∀ n ∈ Icc (8 * q) T, K ^ 2 / 4 * (n : ℝ) ^ (-2 * ε) ≤
        weightCenteredPrefix (charTwinWeight χ ε) |charDampedMass χ ε| n ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1)) := fun n hn =>
      weightCell_ge_rpow_of_drift (charTwinWeight_nonneg χ hε) (hasSum_charTwinWeight_div χ hε)
        hK.le hε2 (by have := (mem_Icc.mp hn).1; omega)
        (charTwin_drift_ge χ hε hL (mem_Icc.mp hn).1)
    rw [mul_sum, weightPronicEnergy]
    refine (sum_le_sum hcell).trans (sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ =>
      div_nonneg (sq_nonneg _) (by positivity))
    intro n hn
    rw [mem_Icc] at hn ⊢
    omega
  · rw [← hmean]
    exact weightPronicEnergy_le_of_dampedClass hε (by linarith)
      (charTwinWeight_mem_dampedClass χ hε) T

/-! ### The threshold -/

/-- **Half damping is the exact threshold of the parity pair.** For every `K > 0` and `ε > 0`,
receiver boundedness on `𝒞(K, ε)` is a function of the Ramanujan amplitudes if and only if
`ε > 1/2`. -/
theorem receiverBounded_amplitudeInvariant_iff {K ε : ℝ} (hK : 0 < K) (hε : 0 < ε) :
    (∃ Φ : (ℕ → ℝ) → Prop, ∀ c : ℕ → ℝ, DampedClass K ε c →
      (ReceiverBounded c ↔ Φ (fun e => |weightRamanujanCoeff c e|))) ↔ 1 / 2 < ε := by
  constructor
  · intro h
    by_contra hle
    exact parity_barrier hK hε (not_lt.mp hle) h
  · intro hε2
    obtain ⟨E, hE⟩ := exists_uniform_weightPronicEnergy_bound (K := K) hε2
    exact ⟨fun _ => True, fun c hc => iff_true_intro ⟨E, hE c hc⟩⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
