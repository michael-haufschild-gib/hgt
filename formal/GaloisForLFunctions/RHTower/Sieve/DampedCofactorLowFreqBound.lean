import GaloisForLFunctions.RHTower.Sieve.DampedTwistSharpRate
import GaloisForLFunctions.RHTower.Sieve.DampedCofactorTransfer
import GaloisForLFunctions.RHTower.Sieve.CofactorLowFreqBound

/-!
# The damped cofactor polynomial at low frequency

The damped analogue of `Sieve/CofactorLowFreqBound`.  The cofactor polynomial of the damped Möbius
coefficient `μ(m)t^{ω_P(m)}` is a twisted damped sum over an interval, so the twisted damped contour
bound gives it a saving better than any power of the logarithm, uniformly over a frequency range
that is itself larger than any power of the logarithm — and, decisively, uniformly in the damping
parameter `t ∈ [0,1]`, because the Euler correction factor depends only on the abscissa.

Averaging over `t` then transfers the saving to the exact Ramaré cofactor `μ(m)/(ω_P(m)+1)`, which
is the coefficient the Ramaré split actually produces.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- The explicit majorant for a sharp twisted damped sum. -/
def dampedSharpBound (P : Finset ℕ) (N : ℝ) : ℝ :=
  dampedCorrBound P (leftAbscissa (contourParam (N + smoothWidth N)))
      * (3 * N * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2)))
      / Real.pi
    + (smoothWidth N + 1)

/-- Above `3` the correction factor of the majorant is well defined and nonnegative. -/
theorem half_le_leftAbscissa_contourParam_add_smoothWidth {N : ℝ} (hN : 3 ≤ N) :
    1 / 2 ≤ leftAbscissa (contourParam (N + smoothWidth N)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have he : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hlogN : (1 : ℝ) ≤ Real.log N :=
    (Real.le_log_iff_exp_le hN0).2 (by linarith)
  have hW : (1 : ℝ) ≤ smoothWidth N := one_le_smoothWidth hN0 hlogN
  have hNW : (0 : ℝ) < N + smoothWidth N := by linarith
  have hlogNW : (1 : ℝ) ≤ Real.log (N + smoothWidth N) :=
    (Real.le_log_iff_exp_le hNW).2 (by linarith)
  have hrp : (1 : ℝ) ≤ (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 10) := (Real.one_rpow _).symm
      _ ≤ (Real.log (N + smoothWidth N)) ^ ((1 : ℝ) / 10) :=
          Real.rpow_le_rpow (by norm_num) hlogNW (by norm_num)
  have hL1 : (1 : ℝ) ≤ Real.log (contourParam (N + smoothWidth N)) :=
    le_trans hrp (le_log_contourParam _)
  have hL9 : (1 : ℝ) ≤ (Real.log (contourParam (N + smoothWidth N))) ^ 9 := one_le_pow₀ hL1
  have hA0 := zeroFreeConst_pos
  have hA1 := zeroFreeConst_le_one
  rw [leftAbscissa]
  have hsmall : zeroFreeConst
      / (16 * (Real.log (contourParam (N + smoothWidth N))) ^ 9) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL9, hA1, hA0]
  linarith

/-- The majorant is nonnegative above `3`. -/
theorem dampedSharpBound_nonneg {P : Finset ℕ} (hP : ∀ q ∈ P, 2 ≤ q) {N : ℝ} (hN : 3 ≤ N) :
    0 ≤ dampedSharpBound P N := by
  have hN0 : (0 : ℝ) < N := by linarith
  have he : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hlogN : (1 : ℝ) ≤ Real.log N := (Real.le_log_iff_exp_le hN0).2 (by linarith)
  have hW : (1 : ℝ) ≤ smoothWidth N := one_le_smoothWidth hN0 hlogN
  have hcorr : 0 ≤ dampedCorrBound P (leftAbscissa (contourParam (N + smoothWidth N))) :=
    dampedCorrBound_nonneg hP (half_le_leftAbscissa_contourParam_add_smoothWidth hN)
  rw [dampedSharpBound]
  have h1 : (0 : ℝ)
      ≤ dampedCorrBound P (leftAbscissa (contourParam (N + smoothWidth N)))
        * (3 * N * Real.exp (-(zeroFreeConst / 8192 * ((Real.log N) ^ ((1 : ℝ) / 20)) ^ 2 / 2)))
        / Real.pi := by positivity
  linarith

/-- The damped coefficient against the Gallagher phase is the twisted damped coefficient. -/
theorem dampedOmegaMoebius_mul_unitLogPhase_eq (P : Finset ℕ) (t : ℝ) (n : ℕ) (w : ℝ) :
    dampedOmegaMoebius P t n * unitLogPhase w n = dampedTwist P t (-(2 * Real.pi * w)) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [dampedTwist_zero, dampedOmegaMoebius_zero, zero_mul]
  · rw [dampedTwist, unitLogPhase_eq_cpow hn w]
    congr 2
    push_cast
    ring

/-- **The damped cofactor polynomial is a twisted damped sum.** -/
theorem logPoly_dampedOmegaMoebius_eq_sum_dampedTwist (P : Finset ℕ) (t : ℝ) (s : Finset ℕ)
    (w : ℝ) :
    logPoly (dampedOmegaMoebius P t) s w
      = ∑ n ∈ s, dampedTwist P t (-(2 * Real.pi * w)) n := by
  rw [logPoly]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← dampedOmegaMoebius_mul_unitLogPhase_eq P t n w, unitLogPhase]

/-- A twisted damped sum over an interval is a difference of initial sums. -/
theorem sum_dampedTwist_Icc_eq (P : Finset ℕ) (t τ : ℝ) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a ≤ b + 1) :
    ∑ n ∈ Finset.Icc a b, dampedTwist P t τ n
      = (∑ n ∈ Finset.range (b + 1), dampedTwist P t τ n)
        - ∑ n ∈ Finset.range ((a - 1) + 1), dampedTwist P t τ n := by
  classical
  have hsub : Finset.range ((a - 1) + 1) ⊆ Finset.range (b + 1) := by
    intro n hn
    rw [Finset.mem_range] at hn ⊢
    omega
  rw [eq_comm, sub_eq_iff_eq_add, ← Finset.sum_sdiff hsub]
  have hsd : Finset.range (b + 1) \ Finset.range ((a - 1) + 1) = Finset.Icc a b := by
    ext n
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [hsd, add_comm]

/-- **The damped cofactor polynomial over an interval, at low frequency.**  Uniformly in the
damping parameter. -/
theorem exists_norm_logPoly_dampedOmegaMoebius_Icc_le {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) :
    ∃ (K₀ : ℕ) (N₁ : ℝ), ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ (a b : ℕ) (w : ℝ), 1 ≤ a →
      N₁ ≤ ((a - 1 : ℕ) : ℝ) → N₁ ≤ (b : ℝ) →
      K₀ ≤ contourParam (((a - 1 : ℕ) : ℝ) + smoothWidth ((a - 1 : ℕ) : ℝ)) →
      K₀ ≤ contourParam ((b : ℝ) + smoothWidth (b : ℝ)) →
      5 + 4 * |(-(2 * Real.pi * w))|
        ≤ ((contourParam (((a - 1 : ℕ) : ℝ) + smoothWidth ((a - 1 : ℕ) : ℝ)) : ℕ) : ℝ) →
      5 + 4 * |(-(2 * Real.pi * w))| ≤ ((contourParam ((b : ℝ) + smoothWidth (b : ℝ)) : ℕ) : ℝ) →
      ‖logPoly (dampedOmegaMoebius P t) (Finset.Icc a b) w‖
        ≤ dampedSharpBound P ((a - 1 : ℕ) : ℝ) + dampedSharpBound P (b : ℝ) := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  obtain ⟨K₀, hev⟩ := exists_norm_sum_dampedTwist_rate hPprime
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hev
  refine ⟨K₀, max N₁ 3, ?_⟩
  intro t ht0 ht1 a b w ha hlo' hhi' hKlo hKhi hτlo hτhi
  have hlo : N₁ ≤ ((a - 1 : ℕ) : ℝ) := le_trans (le_max_left _ _) hlo'
  have hhi : N₁ ≤ (b : ℝ) := le_trans (le_max_left _ _) hhi'
  have hlo3 : (3 : ℝ) ≤ ((a - 1 : ℕ) : ℝ) := le_trans (le_max_right _ _) hlo'
  have hhi3 : (3 : ℝ) ≤ (b : ℝ) := le_trans (le_max_right _ _) hhi'
  set τ : ℝ := -(2 * Real.pi * w) with hτ
  have hbound : ∀ N : ℝ, N₁ ≤ N →
      K₀ ≤ contourParam (N + smoothWidth N) →
      5 + 4 * |τ| ≤ ((contourParam (N + smoothWidth N) : ℕ) : ℝ) →
      ‖∑ n ∈ Finset.range (⌊N⌋₊ + 1), dampedTwist P t τ n‖ ≤ dampedSharpBound P N := by
    intro N hN hK hτle
    exact hN₁ N hN t ht0 ht1 τ hK hτle
  have hlofl : ⌊((a - 1 : ℕ) : ℝ)⌋₊ = a - 1 := Nat.floor_natCast _
  have hhifl : ⌊((b : ℕ) : ℝ)⌋₊ = b := Nat.floor_natCast _
  have hA := hbound ((a - 1 : ℕ) : ℝ) hlo hKlo hτlo
  have hB := hbound ((b : ℕ) : ℝ) hhi hKhi hτhi
  rw [hlofl] at hA
  rw [hhifl] at hB
  by_cases hab : a ≤ b + 1
  · rw [logPoly_dampedOmegaMoebius_eq_sum_dampedTwist, ← hτ, sum_dampedTwist_Icc_eq P t τ ha hab]
    refine (norm_sub_le _ _).trans ?_
    linarith [hA, hB]
  · have hempty : Finset.Icc a b = ∅ := Finset.Icc_eq_empty (by omega)
    rw [logPoly, hempty, Finset.sum_empty, norm_zero]
    linarith [dampedSharpBound_nonneg hP2 hlo3, dampedSharpBound_nonneg hP2 hhi3]

/-- **The damped cofactor polynomial of an initial block, at low frequency.** -/
theorem exists_norm_logPoly_dampedOmegaMoebius_Icc_one_le {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) :
    ∃ (K₀ : ℕ) (N₁ : ℝ), ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ (b : ℕ) (w : ℝ), N₁ ≤ (b : ℝ) →
      K₀ ≤ contourParam ((b : ℝ) + smoothWidth (b : ℝ)) →
      5 + 4 * |(-(2 * Real.pi * w))|
        ≤ ((contourParam ((b : ℝ) + smoothWidth (b : ℝ)) : ℕ) : ℝ) →
      ‖logPoly (dampedOmegaMoebius P t) (Finset.Icc 1 b) w‖ ≤ dampedSharpBound P (b : ℝ) := by
  obtain ⟨K₀, hev⟩ := exists_norm_sum_dampedTwist_rate hPprime
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hev
  refine ⟨K₀, N₁, ?_⟩
  intro t ht0 ht1 b w hb hK hτ
  have hfl : ⌊((b : ℕ) : ℝ)⌋₊ = b := Nat.floor_natCast _
  have hbase := hN₁ ((b : ℕ) : ℝ) hb t ht0 ht1 (-(2 * Real.pi * w)) hK hτ
  rw [hfl] at hbase
  rw [logPoly_dampedOmegaMoebius_eq_sum_dampedTwist,
    ← sum_range_succ_eq_sum_Icc (dampedTwist_zero P t (-(2 * Real.pi * w))) b]
  exact hbase

/-- **The exact Ramaré cofactor polynomial of an initial block, at low frequency.**  Averaging the
uniform-in-`t` saving over `t ∈ [0,1]`. -/
theorem exists_norm_logPoly_ramareCofactorCoeff_Icc_one_le {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) :
    ∃ (K₀ : ℕ) (N₁ : ℝ), ∀ (b : ℕ) (w : ℝ), N₁ ≤ (b : ℝ) →
      K₀ ≤ contourParam ((b : ℝ) + smoothWidth (b : ℝ)) →
      5 + 4 * |(-(2 * Real.pi * w))|
        ≤ ((contourParam ((b : ℝ) + smoothWidth (b : ℝ)) : ℕ) : ℝ) →
      ‖logPoly (ramareCofactorCoeff P) (Finset.Icc 1 b) w‖ ≤ dampedSharpBound P (b : ℝ) := by
  obtain ⟨K₀, N₁, hmain⟩ := exists_norm_logPoly_dampedOmegaMoebius_Icc_one_le hPprime
  refine ⟨K₀, N₁, fun b w hb hK hτ => ?_⟩
  exact norm_logPoly_ramareCofactorCoeff_le_of_uniform P (Finset.Icc 1 b) w
    (fun t ht => hmain t ht.1 ht.2 b w hb hK hτ)

/-- **The exact Ramaré cofactor polynomial of a ladder step, at low frequency.** -/
theorem exists_norm_logPoly_ramareCofactorCoeff_geomCofactorBlockAt_le {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) :
    ∃ (K₀ : ℕ) (N₁ : ℝ), ∀ (B₀ j : ℕ) (Q η w : ℝ), 1 ≤ Q → 0 ≤ η →
      N₁ ≤ ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) →
      K₀ ≤ contourParam (((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
        + smoothWidth ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)) →
      5 + 4 * |(-(2 * Real.pi * w))|
        ≤ ((contourParam (((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)
            + smoothWidth ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ)) : ℕ) : ℝ) →
      ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlockAt 1 B₀ Q η j) w‖
        ≤ dampedSharpBound P ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) := by
  obtain ⟨K₀, N₁, hbound⟩ := exists_norm_logPoly_ramareCofactorCoeff_Icc_one_le hPprime
  refine ⟨K₀, N₁, ?_⟩
  intro B₀ j Q η w hQ hη hN hK hτ
  rw [geomCofactorBlockAt_one_eq hQ hη j]
  exact hbound ⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ w hN hK hτ

end

end RHTower.Sieve
