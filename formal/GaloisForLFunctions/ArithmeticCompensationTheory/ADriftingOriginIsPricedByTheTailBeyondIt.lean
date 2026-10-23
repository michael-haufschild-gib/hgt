import GaloisForLFunctions.ArithmeticCompensationTheory.AChangeOfOriginCostsAQuadraticConstant
import GaloisForLFunctions.ArithmeticCompensationTheory.TheReceiverEnergyEscapesToTheHorizon
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass

/-!
# A drifting origin is priced by the tail beyond it

A finite change of origin costs at most the constant `(k+1)(k+2)/2` in the pronic norm, so it never
changes admission. This file prices an origin that **drifts with the horizon**, `k = k(T)`.

* **The exact two-sided price.** The pronic energy of the translate `a(· + k)` on `[1, T]` lies
  between the tail `E(T + k) − E(k)` of the original sequence beyond the origin and
  `(k+1)(k+2)/2` times that tail (`pronicTail_le_pronicEnergy_shift`,
  `pronicEnergy_shift_le_tail`). A translate sees only the cells beyond the origin, reweighted by
  at most the quadratic constant.
* **Drift tolerance is exactly a bounded drift.** Every admitted sequence stays admitted along a
  drift `k(T)` if and only if the drift is bounded (`forall_admitted_drift_admitted_iff`); one
  admitted sequence, `a(n) = n^{1/4}`, has drifted energy tending to infinity along every drift
  tending to infinity (`tendsto_pronicEnergy_quarterPower_drift`). So no norm-level argument
  controls a drifting origin: drift control must use the tail decay of the specific source.
* **The trivial drift budget of the receiver.** For `0 < ε < ½` the damped Möbius receiver
  translated by `k` cells has pronic energy at most `D (k+1)^{2−2ε} (1 + T^{1−2ε})`
  (`exists_dampedMobius_drift_le`), from the source bound `|A_ε(n)| ≤ C n^{1−ε}` and
  `n + k ≤ (k+1) n`.
-/

open Filter Topology Finset RHTower
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-- The pronic energy up to `T + k` splits at the origin `k`: the head `[1, k]` plus the cells
`k + 1, …, k + T` with their own weights. -/
theorem pronicEnergy_add_eq (a : ℕ → ℝ) (k T : ℕ) :
    pronicEnergy a (T + k) = pronicEnergy a k +
      ∑ n ∈ Icc 1 T, a (n + k) ^ 2 / (((n + k : ℕ) : ℝ) * (((n + k : ℕ) : ℝ) + 1)) := by
  have hsplit : Icc 1 (T + k) = Icc 1 k ∪ (Icc 1 T).image (fun n => n + k) := by
    ext m
    simp only [mem_union, mem_Icc, mem_image]
    constructor
    · intro hm
      by_cases hmk : m ≤ k
      · exact Or.inl ⟨hm.1, hmk⟩
      · exact Or.inr ⟨m - k, ⟨by omega, by omega⟩, by omega⟩
    · rintro (hm | ⟨n, hn, rfl⟩) <;> omega
  have hdisj : Disjoint (Icc 1 k) ((Icc 1 T).image (fun n => n + k)) := by
    rw [disjoint_left]
    intro m hm hm'
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm'
    have := (mem_Icc.mp hm).2
    have := (mem_Icc.mp hn).1
    omega
  rw [pronicEnergy, hsplit, sum_union hdisj, sum_image (fun x _ y _ h => by simpa using h)]
  rfl

/-- **The translate carries at least the tail beyond the origin.** -/
theorem pronicTail_le_pronicEnergy_shift (a : ℕ → ℝ) (k T : ℕ) :
    pronicEnergy a (T + k) - pronicEnergy a k ≤ pronicEnergy (fun n => a (n + k)) T := by
  have h := pronicEnergy_le_head_add_shift a k T
  linarith

/-- **The translate carries at most `(k+1)(k+2)/2` times the tail beyond the origin.** -/
theorem pronicEnergy_shift_le_tail (a : ℕ → ℝ) (k T : ℕ) :
    pronicEnergy (fun n => a (n + k)) T ≤
      ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * (pronicEnergy a (T + k) - pronicEnergy a k) := by
  set c : ℝ := ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2
  have hterm : ∀ n ∈ Icc 1 T, a (n + k) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      c * (a (n + k) ^ 2 / (((n + k : ℕ) : ℝ) * (((n + k : ℕ) : ℝ) + 1))) := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hw : ((n : ℝ) + k) * ((n : ℝ) + k + 1) ≤ c * ((n : ℝ) * ((n : ℝ) + 1)) :=
      pronicWeight_shift_le hn1 k
    push_cast
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hw (sq_nonneg (a (n + k)))]
  rw [pronicEnergy_add_eq a k T, add_sub_cancel_left, mul_sum]
  exact sum_le_sum hterm

/-! ## Drift tolerance is exactly a bounded drift -/

/-- The witness `a(n) = n^{1/4}`, written `√√n`. -/
def quarterPower (n : ℕ) : ℝ := Real.sqrt (Real.sqrt n)

theorem quarterPower_sq (n : ℕ) : quarterPower n ^ 2 = Real.sqrt n :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

/-- `n^{1/4}` is admitted: its pronic energy is at most `3`, since each cell is at most `n^{−3/2}`. -/
theorem pronicEnergy_quarterPower_le (T : ℕ) : pronicEnergy quarterPower T ≤ 3 := by
  have hcell : ∀ n ∈ Icc 1 T, quarterPower n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hs : Real.sqrt n = (n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ) ^ 2 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hn0]
      norm_num
    have hp : 0 < (n : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hn0 _
    rw [quarterPower_sq, hs, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : (n : ℝ) ^ 2 ≤ (n : ℝ) * ((n : ℝ) + 1))
      hp.le]
  calc pronicEnergy quarterPower T ≤ ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(3 / 2 : ℝ)) := sum_le_sum hcell
    _ ≤ 1 + 1 / (3 / 2 - 1) := sum_Icc_rpow_neg_le (by norm_num) T
    _ = 3 := by norm_num

/-- The first cell of a translate of `n^{1/4}` already carries `√(k+1)/2`. -/
theorem sqrt_le_pronicEnergy_quarterPower_shift (k : ℕ) {T : ℕ} (hT : 1 ≤ T) :
    Real.sqrt ((k : ℝ) + 1) / 2 ≤ pronicEnergy (fun n => quarterPower (n + k)) T := by
  have h := single_le_sum (f := fun n => quarterPower (n + k) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))
    (fun n _ => by positivity) (mem_Icc.mpr ⟨le_rfl, hT⟩)
  rw [pronicEnergy]
  refine le_trans (le_of_eq ?_) h
  simp only [quarterPower_sq]
  push_cast
  rw [add_comm (1 : ℝ) k]
  norm_num

/-- **One admitted sequence defeats every unbounded drift.** The translates of `n^{1/4}` along any
drift tending to infinity have pronic energy tending to infinity. -/
theorem tendsto_pronicEnergy_quarterPower_drift {k : ℕ → ℕ} (hk : Tendsto k atTop atTop) :
    Tendsto (fun T => pronicEnergy (fun n => quarterPower (n + k T)) T) atTop atTop := by
  have hs : Tendsto (fun T => Real.sqrt ((k T : ℝ) + 1) / 2) atTop atTop := by
    refine Tendsto.atTop_div_const (by norm_num) (Real.tendsto_sqrt_atTop.comp ?_)
    exact tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hk)
  refine tendsto_atTop_mono' atTop ?_ hs
  filter_upwards [eventually_ge_atTop 1] with T hT
  exact sqrt_le_pronicEnergy_quarterPower_shift (k T) hT

/-- **Drift tolerance is exactly a bounded drift.** Every admitted sequence has bounded pronic
energy along the translates `a(· + k(T))` if and only if the drift `k` is bounded. -/
theorem forall_admitted_drift_admitted_iff (k : ℕ → ℕ) :
    (∀ a : ℕ → ℝ, (∃ B, ∀ T, pronicEnergy a T ≤ B) →
      ∃ B, ∀ T, pronicEnergy (fun n => a (n + k T)) T ≤ B) ↔ ∃ K, ∀ T, k T ≤ K := by
  constructor
  · intro h
    obtain ⟨B, hB⟩ := h quarterPower ⟨3, pronicEnergy_quarterPower_le⟩
    refine ⟨max (k 0) ⌈4 * B ^ 2⌉₊, fun T => ?_⟩
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · exact le_max_left _ _
    refine le_max_of_le_right ?_
    have h1 := (sqrt_le_pronicEnergy_quarterPower_shift (k T) hT).trans (hB T)
    have hsq0 : 0 ≤ Real.sqrt ((k T : ℝ) + 1) := Real.sqrt_nonneg _
    have h2 : (k T : ℝ) + 1 ≤ 4 * B ^ 2 := by
      have h3 := pow_le_pow_left₀ hsq0 (by linarith : Real.sqrt ((k T : ℝ) + 1) ≤ 2 * B) 2
      rw [Real.sq_sqrt (by positivity)] at h3
      linarith
    exact_mod_cast (by linarith : (k T : ℝ) ≤ 4 * B ^ 2).trans (Nat.le_ceil _)
  · rintro ⟨K, hK⟩ a ⟨B, hB⟩
    have hB0 : 0 ≤ B := (pronicEnergy_nonneg a 0).trans (hB 0)
    refine ⟨((K : ℝ) + 1) * ((K : ℝ) + 2) / 2 * B, fun T => ?_⟩
    have hk : (k T : ℝ) ≤ K := by exact_mod_cast hK T
    calc pronicEnergy (fun n => a (n + k T)) T
        ≤ ((k T : ℝ) + 1) * ((k T : ℝ) + 2) / 2 * pronicEnergy a (T + k T) :=
          pronicEnergy_shift_le a (k T) T
      _ ≤ ((K : ℝ) + 1) * ((K : ℝ) + 2) / 2 * B :=
          mul_le_mul (by gcongr) (hB _) (pronicEnergy_nonneg _ _) (by positivity)

/-! ## The trivial drift budget of the receiver -/

/-- **The receiver's drift budget.** For `0 < ε < ½` the damped Möbius receiver translated by `k`
cells has pronic energy at most `D (k+1)^{2−2ε} (1 + T^{1−2ε})` on `[1, T]`. -/
theorem exists_dampedMobius_drift_le {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ k T : ℕ,
      pronicEnergy (fun n => pmPowerDampedCenteredDivisorPrefix ε (n + k)) T ≤
        D * ((k : ℝ) + 1) ^ (2 - 2 * ε) * (1 + (T : ℝ) ^ (1 - 2 * ε)) := by
  obtain ⟨C, hC, h⟩ := exists_abs_centredPrefix_le hε hεhalf
  have hd : 0 < 1 - 2 * ε := by linarith
  refine ⟨C ^ 2 * (1 + 1 / (1 - 2 * ε)), by positivity, fun k T => ?_⟩
  set K : ℝ := ((k : ℝ) + 1) ^ (2 - 2 * ε)
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  have hcell : ∀ n ∈ Icc 1 T, pmPowerDampedCenteredDivisorPrefix ε (n + k) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1)) ≤ C ^ 2 * K * (n : ℝ) ^ (-(2 * ε)) := by
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    -- `n + k ≤ (k+1) n` moves the drift out of the source bound
    have hmono : ((n + k : ℕ) : ℝ) ^ (1 - ε) ≤ ((k : ℝ) + 1) ^ (1 - ε) * (n : ℝ) ^ (1 - ε) := by
      rw [← Real.mul_rpow (by positivity) hn0.le]
      exact Real.rpow_le_rpow (by positivity) (by push_cast; nlinarith [mul_nonneg hk0 (by linarith : (0 : ℝ) ≤ n - 1)])
        (by linarith)
    have hb : |pmPowerDampedCenteredDivisorPrefix ε (n + k)| ≤
        C * (((k : ℝ) + 1) ^ (1 - ε) * (n : ℝ) ^ (1 - ε)) :=
      (h (n + k) (by omega)).trans (mul_le_mul_of_nonneg_left hmono hC)
    have hsq : pmPowerDampedCenteredDivisorPrefix ε (n + k) ^ 2 ≤
        C ^ 2 * K * ((n : ℝ) ^ (1 - ε)) ^ 2 := by
      have hKe : K = (((k : ℝ) + 1) ^ (1 - ε)) ^ 2 := by
        show ((k : ℝ) + 1) ^ (2 - 2 * ε) = _
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        ring
      rw [hKe, ← sq_abs]
      calc |pmPowerDampedCenteredDivisorPrefix ε (n + k)| ^ 2
          ≤ (C * (((k : ℝ) + 1) ^ (1 - ε) * (n : ℝ) ^ (1 - ε))) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hb 2
        _ = C ^ 2 * (((k : ℝ) + 1) ^ (1 - ε)) ^ 2 * ((n : ℝ) ^ (1 - ε)) ^ 2 := by ring
    have hw := rpow_sq_div_pronic_le (ε := ε) hn1
    calc pmPowerDampedCenteredDivisorPrefix ε (n + k) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ C ^ 2 * K * ((n : ℝ) ^ (1 - ε)) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
          div_le_div_of_nonneg_right hsq (by positivity)
      _ = C ^ 2 * K * (((n : ℝ) ^ (1 - ε)) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by ring
      _ ≤ C ^ 2 * K * (n : ℝ) ^ (-2 * ε) := mul_le_mul_of_nonneg_left hw (by positivity)
      _ = C ^ 2 * K * (n : ℝ) ^ (-(2 * ε)) := by rw [neg_mul]
  have hsum := sum_rpow_neg_head_le (by positivity : 0 < 2 * ε) (by linarith : 2 * ε < 1) T
  have hpow : 0 ≤ (T : ℝ) ^ (1 - 2 * ε) := Real.rpow_nonneg (Nat.cast_nonneg T) _
  have h2 : 0 ≤ 1 / (1 - 2 * ε) := by positivity
  calc pronicEnergy (fun n => pmPowerDampedCenteredDivisorPrefix ε (n + k)) T
      ≤ ∑ n ∈ Icc 1 T, C ^ 2 * K * (n : ℝ) ^ (-(2 * ε)) := sum_le_sum hcell
    _ = C ^ 2 * K * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 * ε)) := by rw [mul_sum]
    _ ≤ C ^ 2 * K * (1 + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ C ^ 2 * (1 + 1 / (1 - 2 * ε)) * K * (1 + (T : ℝ) ^ (1 - 2 * ε)) := by
        have h1 : (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) = 1 / (1 - 2 * ε) * (T : ℝ) ^ (1 - 2 * ε) :=
          by ring
        rw [h1]
        have hCK : 0 ≤ C ^ 2 * K := by positivity
        nlinarith [mul_nonneg hCK (mul_nonneg h2 hpow), mul_nonneg hCK h2, mul_nonneg hCK hpow]

end GaloisForLFunctions.ArithmeticCompensationTheory
