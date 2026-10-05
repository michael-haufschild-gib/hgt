import GaloisForLFunctions.RHTower.BeurlingCountedPrimeDeletion
import GaloisForLFunctions.RHTower.BeurlingDeletionRegion
import GaloisForLFunctions.RHTower.PrimeDeletionSquareRootFloor
import GaloisForLFunctions.RHTower.PrimeRpowLogSumAsymptotic
import GaloisForLFunctions.RHTower.Sieve.ChebyshevErrorPowerBound
import GaloisForLFunctions.RHTower.PrimeVacuumErrorTransfer
import GaloisForLFunctions.RHTower.Sieve.AbelIncreasingWeight

/-!
# The deletion exponent lies in `[α/2, β₀(α)]`

Assume RH and `1/2 < α < 4/5`.  The count-controlled deletion set `S` has square-root discrepancy
against `p^{α−1}` at every frequency, so it realizes the Perron region: the `S`-free integers obey
`N_S(x) = a x + O(x^β)` for every `β > β₀(α)`, and the deletion system is an `[α, β]`-system for
every `β₀(α) < β < 1/2`.  Its prime count also obeys `Σ_{p ≤ x} (1_S(p) − p^{α−1}) =
O(x^{α−1/2} log² x)`.

Abel summation against `log p` turns the count control into
`θ_S(y) = Σ_{p ≤ y} p^{α−1} log p + O(y^{α−1/2+ε})`, and Abel summation of `p^{α−1}` against
`θ(t) = t + O(t^{1/2+ε})` (RH) gives `Σ_{p ≤ y} p^{α−1} log p = y^α/α + O(y^{α−1/2+ε})`.  Splitting
the deleted Chebyshev function by prime-power exponent,
`ψ_S(x) = θ_S(x) + θ_S(x^{1/2}) + Σ_{k ≥ 3} θ_S(x^{1/k}) = (x^α + x^{α/2})/α + O(x^η)` with
`η < α/2`.  The discrete multiplicative uncertainty floor then forbids `N_S(x) − a x = O(x^θ)` for
every `θ < α/2`.
-/

open Filter Topology Asymptotics MeasureTheory Set intervalIntegral

noncomputable section

namespace RHTower.BeurlingDeletion

/-! ## Weighted prime sums under RH -/

/-- Under RH, `θ(t) = t + O(t^{1/2+ε})`. -/
theorem exists_abs_theta_sub_le (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → |Chebyshev.theta t - t| ≤ C * t ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hpsi⟩ :=
    Sieve.exists_chebyshevPsiReal_error_power_bound hRH (show 0 < ε / 2 by linarith)
  refine ⟨C + 4 / ε, by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have h1 : |Chebyshev.psi t - t| ≤ C * t ^ (1 / 2 + ε / 2) := by
    rw [← chebyshevPsiReal_eq_psi]; exact hpsi t ht
  have h2 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log ht
  have hlog := Real.log_le_rpow_div ht0.le (show 0 < ε / 2 by linarith)
  have h3 : 2 * Real.sqrt t * Real.log t ≤ 4 / ε * t ^ (1 / 2 + ε / 2) := by
    rw [Real.rpow_add ht0, ← Real.sqrt_eq_rpow]
    have hs : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
    calc 2 * Real.sqrt t * Real.log t ≤ 2 * Real.sqrt t * (t ^ (ε / 2) / (ε / 2)) := by gcongr
      _ = 4 / ε * (Real.sqrt t * t ^ (ε / 2)) := by field_simp; ring
  have h4 : t ^ (1 / 2 + ε / 2) ≤ t ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  have h5 : |Chebyshev.theta t - t| ≤
      |Chebyshev.psi t - t| + |Chebyshev.psi t - Chebyshev.theta t| := by
    calc |Chebyshev.theta t - t| =
        |(Chebyshev.psi t - t) - (Chebyshev.psi t - Chebyshev.theta t)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  calc |Chebyshev.theta t - t| ≤ C * t ^ (1 / 2 + ε / 2) + 4 / ε * t ^ (1 / 2 + ε / 2) := by
        linarith
    _ = (C + 4 / ε) * t ^ (1 / 2 + ε / 2) := by ring
    _ ≤ (C + 4 / ε) * t ^ (1 / 2 + ε) := mul_le_mul_of_nonneg_left h4 (by positivity)

/-- `Σ_{p ≤ y} p^{α−1} log p`. -/
def primeLogWeightSum (α y : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Iic ⌊y⌋₊).filter Nat.Prime, (p : ℝ) ^ (α - 1) * Real.log p

theorem primeLogWeightSum_eq (α : ℝ) {y : ℝ} (hy : 2 ≤ y) :
    primeLogWeightSum α y = (2 : ℝ) ^ (α - 1) * Real.log 2 + primeRpowLogSumIoc α y := by
  have hn : 2 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  unfold primeLogWeightSum primeRpowLogSumIoc
  rw [Finset.sum_filter]
  have hI : Finset.Iic ⌊y⌋₊ = Finset.range (⌊y⌋₊ + 1) := by
    ext; simp
  have hJ : Finset.Ioc 2 ⌊y⌋₊ = Finset.Ico 3 (⌊y⌋₊ + 1) := by
    ext; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hI, hJ, ← Finset.sum_range_add_sum_Ico _ (show 3 ≤ ⌊y⌋₊ + 1 by omega)]
  congr 1
  simp [Finset.sum_range_succ, Nat.prime_two]

/-- **Under RH, `Σ_{p ≤ y} p^{α−1} log p = y^α/α + O(y^{α−1/2+ε})`.** -/
theorem exists_abs_primeLogWeightSum_sub_le (hRH : RiemannHypothesis) {α : ℝ} (hα1 : 1 / 2 < α)
    (hα : α < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y →
      |primeLogWeightSum α y - y ^ α / α| ≤ C * y ^ (α - 1 / 2 + ε) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨Cθ, hCθ, hθ⟩ := exists_abs_theta_sub_le hRH hε
  set s := α - 1 / 2 + ε with hs
  have hs0 : 0 < s := by linarith
  set K₀ := |(2 : ℝ) ^ (α - 1) * Real.log 2 - (2 : ℝ) ^ (α - 1) * Chebyshev.theta 2 +
    (α - 1) * ((2 : ℝ) ^ α / α)| with hK₀
  have hM : 0 ≤ K₀ + Cθ + |α - 1| * (Cθ / s) := by positivity
  refine ⟨K₀ + Cθ + |α - 1| * (Cθ / s) + 2 / α, by positivity, fun y hy => ?_⟩
  have hys : 1 ≤ y ^ s := Real.one_le_rpow hy hs0.le
  have hy0 : 0 < y := by linarith
  rcases lt_or_ge y 2 with hy2 | hy2
  · have hzero : primeLogWeightSum α y = 0 := by
      unfold primeLogWeightSum
      refine Finset.sum_eq_zero fun p hp => ?_
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      have hfl : ⌊y⌋₊ < 2 := (Nat.floor_lt hy0.le).mpr (by exact_mod_cast hy2)
      have : p ≤ 1 := by have := Finset.mem_Iic.mp hp1; omega
      exact absurd hp2 (by interval_cases p <;> norm_num)
    rw [hzero, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    have hyα : y ^ α ≤ 2 := by
      calc y ^ α ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy hα.le
        _ = y := Real.rpow_one y
        _ ≤ 2 := hy2.le
    have h2 : y ^ α / α ≤ 2 / α := div_le_div_of_nonneg_right hyα hα0.le
    calc y ^ α / α ≤ (K₀ + Cθ + |α - 1| * (Cθ / s) + 2 / α) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hys (by positivity)
  · rw [primeLogWeightSum_eq α hy2, primeRpowLogSumIoc_eq hy2,
      integral_derivRpow_mul_theta_eq hα0 hy2]
    set I := ∫ t in (2 : ℝ)..y, thetaError t * t ^ (α - 1) with hI
    have hIb : |I| ≤ Cθ * (y ^ s / s) := by
      have hb : ∀ t ∈ Set.Ioc (2 : ℝ) y, ‖thetaError t * t ^ (α - 1)‖ ≤ Cθ * t ^ (s - 1) := by
        intro t ht
        have ht1 : 1 ≤ t := by linarith [ht.1]
        have ht0 : 0 < t := by linarith
        have he : thetaError t = (Chebyshev.theta t - t) / t := by
          unfold thetaError; field_simp
        rw [Real.norm_eq_abs, abs_mul, he, abs_div, abs_of_pos ht0,
          abs_of_pos (by positivity : 0 < t ^ (α - 1))]
        have h := hθ t ht1
        have hpow : t ^ (1 / 2 + ε) / t * t ^ (α - 1) = t ^ (s - 1) := by
          rw [div_mul_eq_mul_div, ← Real.rpow_add ht0, div_eq_iff ht0.ne',
            ← Real.rpow_add_one ht0.ne']
          congr 1; rw [hs]; ring
        calc |Chebyshev.theta t - t| / t * t ^ (α - 1) ≤
            Cθ * t ^ (1 / 2 + ε) / t * t ^ (α - 1) := by gcongr
          _ = Cθ * (t ^ (1 / 2 + ε) / t * t ^ (α - 1)) := by ring
          _ = Cθ * t ^ (s - 1) := by rw [hpow]
      have hint := intervalIntegral.norm_integral_le_of_norm_le hy2 (Filter.Eventually.of_forall hb)
        ((intervalIntegral.intervalIntegrable_rpow' (r := s - 1) (by linarith)).const_mul Cθ)
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
        show s - 1 + 1 = s by ring] at hint
      have h2s : 0 < (2 : ℝ) ^ s := by positivity
      have hdiv : (y ^ s - (2 : ℝ) ^ s) / s ≤ y ^ s / s :=
        div_le_div_of_nonneg_right (by linarith) hs0.le
      rw [← Real.norm_eq_abs]
      exact hint.trans (mul_le_mul_of_nonneg_left hdiv hCθ.le)
    have hboundary : |y ^ (α - 1) * (Chebyshev.theta y - y)| ≤ Cθ * y ^ s := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < y ^ (α - 1))]
      calc y ^ (α - 1) * |Chebyshev.theta y - y| ≤ y ^ (α - 1) * (Cθ * y ^ (1 / 2 + ε)) := by
            gcongr; exact hθ y hy
        _ = Cθ * (y ^ (α - 1) * y ^ (1 / 2 + ε)) := by ring
        _ = Cθ * y ^ s := by rw [← Real.rpow_add hy0, hs]; ring_nf
    have hyy : y ^ (α - 1) * y = y ^ α := by
      rw [Real.rpow_sub_one hy0.ne', div_mul_cancel₀ _ hy0.ne']
    have hθy : y ^ (α - 1) * Chebyshev.theta y =
        y ^ (α - 1) * (Chebyshev.theta y - y) + y ^ α := by
      rw [mul_sub, hyy]; ring
    have hexp : (2 : ℝ) ^ (α - 1) * Real.log 2 + (y ^ (α - 1) * Chebyshev.theta y -
        (2 : ℝ) ^ (α - 1) * Chebyshev.theta 2 - ((α - 1) * ((y ^ α - (2 : ℝ) ^ α) / α) +
          (α - 1) * I)) - y ^ α / α =
        ((2 : ℝ) ^ (α - 1) * Real.log 2 - (2 : ℝ) ^ (α - 1) * Chebyshev.theta 2 +
          (α - 1) * ((2 : ℝ) ^ α / α)) + y ^ (α - 1) * (Chebyshev.theta y - y) -
          (α - 1) * I := by
      rw [hθy]; field_simp; ring
    rw [hexp]
    have hK : |(2 : ℝ) ^ (α - 1) * Real.log 2 - (2 : ℝ) ^ (α - 1) * Chebyshev.theta 2 +
        (α - 1) * ((2 : ℝ) ^ α / α)| ≤ K₀ * y ^ s := by
      rw [← hK₀]; nlinarith [abs_nonneg ((2 : ℝ) ^ (α - 1) * Real.log 2 -
        (2 : ℝ) ^ (α - 1) * Chebyshev.theta 2 + (α - 1) * ((2 : ℝ) ^ α / α))]
    have hIα : |(α - 1) * I| ≤ |α - 1| * (Cθ / s) * y ^ s := by
      rw [abs_mul]
      calc |α - 1| * |I| ≤ |α - 1| * (Cθ * (y ^ s / s)) :=
            mul_le_mul_of_nonneg_left hIb (abs_nonneg _)
        _ = |α - 1| * (Cθ / s) * y ^ s := by ring
    calc _ ≤ |(2 : ℝ) ^ (α - 1) * Real.log 2 - (2 : ℝ) ^ (α - 1) * Chebyshev.theta 2 +
            (α - 1) * ((2 : ℝ) ^ α / α)| + |y ^ (α - 1) * (Chebyshev.theta y - y)| +
            |(α - 1) * I| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ K₀ * y ^ s + Cθ * y ^ s + |α - 1| * (Cθ / s) * y ^ s := by linarith
      _ ≤ (K₀ + Cθ + |α - 1| * (Cθ / s) + 2 / α) * y ^ s := by
          have : 0 ≤ 2 / α * y ^ s := by positivity
          nlinarith

/-! ## From the count of a deletion set to its Chebyshev function -/

/-- The Chebyshev function `θ_S(y) = Σ_{p ≤ y, p ∈ S} log p` of a set of primes. -/
def thetaDel (S : Set ℕ) (y : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Iic ⌊y⌋₊).filter Nat.Prime, S.indicator (fun _ => (1 : ℝ)) p * Real.log p

theorem thetaDel_nonneg (S : Set ℕ) (y : ℝ) : 0 ≤ thetaDel S y :=
  Finset.sum_nonneg fun p _ =>
    mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Real.log_natCast_nonneg p)

theorem sum_Iic_zero_filter_prime (f : ℕ → ℝ) :
    ∑ p ∈ (Finset.Iic 0).filter Nat.Prime, f p = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
  have : p = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp hp1)
  exact absurd (this ▸ hp2) Nat.not_prime_zero

/-- **Abel summation against `log p`.**  A bound `B` on every prefix count
`Σ_{p ≤ m} (1_S(p) − p^{α−1})`, `m ≤ y`, bounds the logarithmic deviation by `2 B log y`. -/
theorem abs_thetaDel_sub_le {S : Set ℕ} {α B y : ℝ} (hy : 1 ≤ y)
    (hB : ∀ m : ℕ, 1 ≤ m → m ≤ ⌊y⌋₊ →
      |∑ p ∈ (Finset.Iic m).filter Nat.Prime,
        (S.indicator (fun _ => (1 : ℝ)) p - (p : ℝ) ^ (α - 1))| ≤ B) :
    |thetaDel S y - primeLogWeightSum α y| ≤ 2 * B * Real.log y := by
  classical
  set n := ⌊y⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hy)
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 1 le_rfl hn1)
  set g : ℕ → ℂ := fun i => if i.Prime then
    ((S.indicator (fun _ => (1 : ℝ)) i - (i : ℝ) ^ (α - 1) : ℝ) : ℂ) else 0 with hg
  have hI : ∀ m : ℕ, Finset.Iic m = Finset.range (m + 1) := fun m => by
    ext; simp
  have hsum : thetaDel S y - primeLogWeightSum α y = ∑ p ∈ (Finset.Iic n).filter Nat.Prime,
      (S.indicator (fun _ => (1 : ℝ)) p - (p : ℝ) ^ (α - 1)) * Real.log p := by
    unfold thetaDel primeLogWeightSum
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hcast : ((∑ p ∈ (Finset.Iic n).filter Nat.Prime,
      (S.indicator (fun _ => (1 : ℝ)) p - (p : ℝ) ^ (α - 1)) * Real.log p : ℝ) : ℂ) =
      ∑ i ∈ Finset.range (n + 1), ((Real.log i : ℝ) : ℂ) * g i := by
    rw [Finset.sum_filter, hI, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hg]
    split_ifs <;> push_cast <;> ring
  have hpartial : ∀ k ≤ n + 1, ‖∑ i ∈ Finset.range k, g i‖ ≤ B := by
    intro k hk
    rcases k with _ | k
    · simpa using hB0
    · have hk' : k ≤ n := by omega
      have heq : ∑ i ∈ Finset.range (k + 1), g i = ((∑ p ∈ (Finset.Iic k).filter Nat.Prime,
          (S.indicator (fun _ => (1 : ℝ)) p - (p : ℝ) ^ (α - 1)) : ℝ) : ℂ) := by
        rw [Finset.sum_filter, hI, Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hg]
        split_ifs <;> simp
      rw [heq, Complex.norm_real, Real.norm_eq_abs]
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0; rw [sum_Iic_zero_filter_prime, abs_zero]; exact hB0
      · exact hB k hpos hk'
  have hmono : ∀ i : ℕ, (fun i : ℕ => Real.log i) i ≤ (fun i : ℕ => Real.log i) (i + 1) := by
    intro i
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; simp
    · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast Nat.le_succ i)
  have h := Sieve.norm_sum_mul_le_of_bounded_partial_mono (n + 1) (fun i : ℕ => Real.log i) g
    (by simp) hmono hpartial
  rw [← hcast, Complex.norm_real, Real.norm_eq_abs, ← hsum, Nat.add_sub_cancel] at h
  have hlog : Real.log n ≤ Real.log y :=
    Real.log_le_log (by exact_mod_cast hn1) (Nat.floor_le (by linarith))
  calc _ ≤ 2 * B * Real.log n := h
    _ ≤ 2 * B * Real.log y := mul_le_mul_of_nonneg_left hlog (by positivity)

/-- **The deleted Chebyshev function splits by prime-power exponent:**
`ψ_S(x) = Σ_{k ≥ 1} θ_S(x^{1/k})`. -/
theorem deletedChebyshev_eq_sum_thetaDel (S : Set ℕ) {x : ℝ} (hx : 0 ≤ x) :
    PrimeDeletion.deletedChebyshev S x =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, thetaDel S (x ^ ((1 : ℝ) / k)) := by
  classical
  unfold PrimeDeletion.deletedChebyshev
  have hIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hfilt : ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, PrimeDeletion.deletedVonMangoldt S n =
      ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter IsPrimePow, PrimeDeletion.deletedVonMangoldt S n := by
    refine (Finset.sum_filter_of_ne fun n _ hn => ?_).symm
    by_contra h
    apply hn
    unfold PrimeDeletion.deletedVonMangoldt
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h, zero_mul]
  rw [hIcc, hfilt, Chebyshev.sum_PrimePow_eq_sum_sum _ hx]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
  unfold thetaDel
  have hset : (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime =
      (Finset.Iic ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Iic]
    constructor
    · rintro ⟨⟨_, h⟩, hp⟩; exact ⟨h, hp⟩
    · rintro ⟨h, hp⟩; exact ⟨⟨hp.pos, h⟩, hp⟩
  rw [hset]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp := (Finset.mem_filter.mp hp).2
  unfold PrimeDeletion.deletedVonMangoldt PrimeDeletion.qFreeIndicator
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk0, ArithmeticFunction.vonMangoldt_apply_prime hpp,
    Nat.primeFactors_prime_pow hk0 hpp]
  by_cases hS : p ∈ S
  · rw [if_neg (fun h => h.2 p (Finset.mem_singleton_self p) hS)]
    simp [hS]
  · rw [if_pos ⟨pow_ne_zero _ hpp.ne_zero, fun q hq => by rw [Finset.mem_singleton.mp hq]; exact hS⟩]
    simp [hS]

namespace Counted

variable {α : ℝ}

/-- **The Chebyshev function of the counted deletion set:** under RH,
`θ_S(y) = y^α/α + O(y^γ)` for every `γ > α − 1/2`. -/
theorem exists_abs_thetaDel_sub_le (hRH : RiemannHypothesis) (hα1 : 1 / 2 < α) (hα : α < 1)
    {γ : ℝ} (hγ : α - 1 / 2 < γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ y → |thetaDel (deletedC hα) y - y ^ α / α| ≤ C * y ^ γ := by
  set δ := (γ - (α - 1 / 2)) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨C₁, hC₁, hW⟩ := exists_abs_primeLogWeightSum_sub_le hRH hα1 hα hδ0
  obtain ⟨C₂, hC₂, hcount⟩ := exists_count_bound hα1 hα
  set r := min (δ / 3) 1 with hr
  have hr0 : 0 < r := lt_min (by linarith) one_pos
  have hr1 : r ≤ 1 := min_le_right _ _
  have hr3 : 3 * r ≤ δ := by have := min_le_left (δ / 3) 1; linarith
  refine ⟨C₁ + 16 * C₂ / r ^ 3, by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  set B := C₂ * y ^ (α - 1 / 2) * (Real.log y + 1) ^ 2 with hB
  have hpref : ∀ m : ℕ, 1 ≤ m → m ≤ ⌊y⌋₊ →
      |∑ p ∈ (Finset.Iic m).filter Nat.Prime,
        ((deletedC hα).indicator (fun _ => (1 : ℝ)) p - (p : ℝ) ^ (α - 1))| ≤ B := by
    intro m hm1 hmy
    have hm : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hmy' : (m : ℝ) ≤ y := le_trans (by exact_mod_cast hmy) (Nat.floor_le hy0.le)
    have h := hcount m hm
    rw [Nat.floor_natCast] at h
    have h1 : (m : ℝ) ^ (α - 1 / 2) ≤ y ^ (α - 1 / 2) :=
      Real.rpow_le_rpow (by linarith) hmy' (by linarith)
    have h2 : Real.log m + 1 ≤ Real.log y + 1 := by
      linarith [Real.log_le_log (by linarith) hmy']
    have h3 : (Real.log m + 1) ^ 2 ≤ (Real.log y + 1) ^ 2 := by
      have : 0 ≤ Real.log m + 1 := by linarith [Real.log_nonneg hm]
      gcongr
    calc _ ≤ C₂ * (m : ℝ) ^ (α - 1 / 2) * (Real.log m + 1) ^ 2 := h
      _ ≤ B := by
          rw [hB]
          have : 0 ≤ C₂ * (m : ℝ) ^ (α - 1 / 2) := by positivity
          calc C₂ * (m : ℝ) ^ (α - 1 / 2) * (Real.log m + 1) ^ 2 ≤
              C₂ * (m : ℝ) ^ (α - 1 / 2) * (Real.log y + 1) ^ 2 :=
                mul_le_mul_of_nonneg_left h3 this
            _ ≤ C₂ * y ^ (α - 1 / 2) * (Real.log y + 1) ^ 2 := by
                gcongr
  have hA := abs_thetaDel_sub_le (S := deletedC hα) (α := α) hy hpref
  have hWy := hW y hy
  have hL : Real.log y + 1 ≤ 2 * (y ^ r / r) := (log_bounds hr0 hr1 hy).2
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have hcube : (Real.log y + 1) ^ 3 ≤ 8 * y ^ (3 * r) / r ^ 3 := by
    have h0 : 0 ≤ Real.log y + 1 := by linarith
    have hyr : (y ^ r) ^ 3 = y ^ (3 * r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; congr 1; push_cast; ring
    calc (Real.log y + 1) ^ 3 ≤ (2 * (y ^ r / r)) ^ 3 := by gcongr
      _ = 8 * (y ^ r) ^ 3 / r ^ 3 := by field_simp; ring
      _ = 8 * y ^ (3 * r) / r ^ 3 := by rw [hyr]
  have hexp1 : y ^ (α - 1 / 2) * y ^ (3 * r) ≤ y ^ γ := by
    rw [← Real.rpow_add hy0]; exact Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  have hexp2 : y ^ (α - 1 / 2 + δ) ≤ y ^ γ := Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  have hP : 0 ≤ C₂ * y ^ (α - 1 / 2) := by positivity
  have hT : 2 * B * Real.log y ≤ 16 * C₂ / r ^ 3 * y ^ γ := by
    have hsq : (Real.log y + 1) ^ 2 * Real.log y ≤ (Real.log y + 1) ^ 3 := by
      have := sq_nonneg (Real.log y + 1); nlinarith
    calc 2 * B * Real.log y =
        2 * (C₂ * y ^ (α - 1 / 2)) * ((Real.log y + 1) ^ 2 * Real.log y) := by rw [hB]; ring
      _ ≤ 2 * (C₂ * y ^ (α - 1 / 2)) * (Real.log y + 1) ^ 3 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ 2 * (C₂ * y ^ (α - 1 / 2)) * (8 * y ^ (3 * r) / r ^ 3) :=
          mul_le_mul_of_nonneg_left hcube (by positivity)
      _ = 16 * C₂ / r ^ 3 * (y ^ (α - 1 / 2) * y ^ (3 * r)) := by ring
      _ ≤ 16 * C₂ / r ^ 3 * y ^ γ := mul_le_mul_of_nonneg_left hexp1 (by positivity)
  have hW' : C₁ * y ^ (α - 1 / 2 + δ) ≤ C₁ * y ^ γ := mul_le_mul_of_nonneg_left hexp2 hC₁
  calc |thetaDel (deletedC hα) y - y ^ α / α| ≤
      |thetaDel (deletedC hα) y - primeLogWeightSum α y| +
        |primeLogWeightSum α y - y ^ α / α| := abs_sub_le _ _ _
    _ ≤ 16 * C₂ / r ^ 3 * y ^ γ + C₁ * y ^ γ := by linarith
    _ = (C₁ + 16 * C₂ / r ^ 3) * y ^ γ := by ring

/-- The exponent of the remainder in the deleted Chebyshev function. -/
def chebExponent (α : ℝ) : ℝ := max ((3 * α - 1) / 4) (5 * α / 12)

theorem chebExponent_nonneg (hα0 : 0 < α) : 0 ≤ chebExponent α :=
  le_max_of_le_right (by linarith)

theorem chebExponent_lt (hα0 : 0 < α) (hα : α < 1) : chebExponent α < α / 2 :=
  max_lt (by linarith) (by linarith)

/-- **The deleted Chebyshev function of the counted set:** under RH,
`ψ_S(x) = (x^α + x^{α/2})/α + O(x^η)` with `η = max((3α − 1)/4, 5α/12) < α/2`. -/
theorem isBigO_deletedChebyshev (hRH : RiemannHypothesis) (hα1 : 1 / 2 < α) (hα : α < 1) :
    (fun x : ℝ => PrimeDeletion.deletedChebyshev (deletedC hα) x - 1 / α * (x ^ α + x ^ (α / 2)))
      =O[atTop] fun x => x ^ chebExponent α := by
  have hα0 : 0 < α := by linarith
  set γ := (3 * α - 1) / 4 with hγ
  have hγ0 : 0 ≤ γ := by rw [hγ]; linarith
  obtain ⟨C, hC, hθ⟩ := exists_abs_thetaDel_sub_le hRH hα1 hα (γ := γ) (by rw [hγ]; linarith)
  set S := deletedC hα with hSdef
  refine IsBigO.of_bound (2 * C + 24 / α * (C + 1 / α)) ?_
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2 := Real.log_two_gt_d9
  set K := ⌊Real.log x / Real.log 2⌋₊ with hK
  have hK2 : 2 ≤ K := by
    apply Nat.le_floor
    rw [le_div_iff₀ hl2]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hx
    push_cast
    linarith
  have hKle : (K : ℝ) ≤ 2 * Real.log x := by
    have h := Nat.floor_le (div_nonneg (Real.log_nonneg hx1) hl2.le)
    have : Real.log x / Real.log 2 ≤ 2 * Real.log x := by
      rw [div_le_iff₀ hl2]; nlinarith [Real.log_nonneg hx1]
    rw [hK]; linarith
  rw [deletedChebyshev_eq_sum_thetaDel S hx0.le, ← hK,
    ← Finset.add_sum_Ioc_eq_sum_Icc (by omega : 1 ≤ K)]
  have hIoc : Finset.Ioc 1 K = Finset.Icc 2 K := by
    ext; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hIoc, ← Finset.add_sum_Ioc_eq_sum_Icc (by omega : 2 ≤ K)]
  have hIoc2 : Finset.Ioc 2 K = Finset.Icc 3 K := by
    ext; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hIoc2]
  simp only [Nat.cast_one, Nat.cast_ofNat, div_one, Real.rpow_one]
  have h1 := hθ x hx1
  have hsq1 : 1 ≤ x ^ ((1 : ℝ) / 2) := Real.one_le_rpow hx1 (by norm_num)
  have h2 := hθ (x ^ ((1 : ℝ) / 2)) hsq1
  have hpow2 : (x ^ ((1 : ℝ) / 2)) ^ α = x ^ (α / 2) := by
    rw [← Real.rpow_mul hx0.le]; congr 1; ring
  rw [hpow2] at h2
  have hsqx : x ^ ((1 : ℝ) / 2) ≤ x := by
    calc x ^ ((1 : ℝ) / 2) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one x
  have hpow2γ : (x ^ ((1 : ℝ) / 2)) ^ γ ≤ x ^ γ :=
    Real.rpow_le_rpow (by positivity) hsqx hγ0
  have hterm : ∀ k ∈ Finset.Icc 3 K, thetaDel S (x ^ ((1 : ℝ) / k)) ≤
      (C + 1 / α) * x ^ (α / 3) := by
    intro k hk
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hk0 : (0 : ℝ) < k := by linarith
    have hy1 : 1 ≤ x ^ ((1 : ℝ) / k) := Real.one_le_rpow hx1 (by positivity)
    have hyα : (x ^ ((1 : ℝ) / k)) ^ α ≤ x ^ (α / 3) := by
      rw [← Real.rpow_mul hx0.le]
      refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_left hα0.le (by norm_num) hk3
    have hyγ : (x ^ ((1 : ℝ) / k)) ^ γ ≤ (x ^ ((1 : ℝ) / k)) ^ α :=
      Real.rpow_le_rpow_of_exponent_le hy1 (by rw [hγ]; linarith)
    have h := (abs_le.mp (hθ _ hy1)).2
    have hdiv : (x ^ ((1 : ℝ) / k)) ^ α / α = 1 / α * (x ^ ((1 : ℝ) / k)) ^ α := by ring
    calc thetaDel S (x ^ ((1 : ℝ) / k)) ≤
        (x ^ ((1 : ℝ) / k)) ^ α / α + C * (x ^ ((1 : ℝ) / k)) ^ γ := by linarith
      _ ≤ 1 / α * (x ^ ((1 : ℝ) / k)) ^ α + C * (x ^ ((1 : ℝ) / k)) ^ α := by
          rw [hdiv]; gcongr
      _ = (C + 1 / α) * (x ^ ((1 : ℝ) / k)) ^ α := by ring
      _ ≤ (C + 1 / α) * x ^ (α / 3) := mul_le_mul_of_nonneg_left hyα (by positivity)
  have hcard : ((Finset.Icc 3 K).card : ℝ) ≤ K := by
    rw [Nat.card_Icc]; exact_mod_cast (by omega : K + 1 - 3 ≤ K)
  have htail0 : 0 ≤ ∑ k ∈ Finset.Icc 3 K, thetaDel S (x ^ ((1 : ℝ) / k)) :=
    Finset.sum_nonneg fun k _ => thetaDel_nonneg S _
  have hlogx : Real.log x ≤ x ^ (α / 12) / (α / 12) :=
    Real.log_le_rpow_div hx0.le (by positivity)
  have hx13 : x ^ (α / 12) * x ^ (α / 3) = x ^ (5 * α / 12) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have htail : ∑ k ∈ Finset.Icc 3 K, thetaDel S (x ^ ((1 : ℝ) / k)) ≤
      24 / α * (C + 1 / α) * x ^ (5 * α / 12) := by
    calc ∑ k ∈ Finset.Icc 3 K, thetaDel S (x ^ ((1 : ℝ) / k)) ≤
        ∑ k ∈ Finset.Icc 3 K, (C + 1 / α) * x ^ (α / 3) := Finset.sum_le_sum hterm
      _ = ((Finset.Icc 3 K).card : ℝ) * ((C + 1 / α) * x ^ (α / 3)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * Real.log x) * ((C + 1 / α) * x ^ (α / 3)) :=
          mul_le_mul_of_nonneg_right (hcard.trans hKle) (by positivity)
      _ ≤ (2 * (x ^ (α / 12) / (α / 12))) * ((C + 1 / α) * x ^ (α / 3)) := by
          gcongr
      _ = 24 / α * (C + 1 / α) * (x ^ (α / 12) * x ^ (α / 3)) := by field_simp; ring
      _ = 24 / α * (C + 1 / α) * x ^ (5 * α / 12) := by rw [hx13]
  have hη1 : x ^ γ ≤ x ^ chebExponent α :=
    Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)
  have hη2 : x ^ (5 * α / 12) ≤ x ^ chebExponent α :=
    Real.rpow_le_rpow_of_exponent_le hx1 (le_max_right _ _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ x ^ chebExponent α)]
  have heq : thetaDel S x + (thetaDel S (x ^ ((1 : ℝ) / 2)) +
      ∑ k ∈ Finset.Icc 3 K, thetaDel S (x ^ ((1 : ℝ) / k))) - 1 / α * (x ^ α + x ^ (α / 2)) =
      (thetaDel S x - x ^ α / α) + (thetaDel S (x ^ ((1 : ℝ) / 2)) - x ^ (α / 2) / α) +
        ∑ k ∈ Finset.Icc 3 K, thetaDel S (x ^ ((1 : ℝ) / k)) := by ring
  rw [heq]
  have hC24 : 0 ≤ 24 / α * (C + 1 / α) := by positivity
  calc _ ≤ |thetaDel S x - x ^ α / α| + |thetaDel S (x ^ ((1 : ℝ) / 2)) - x ^ (α / 2) / α| +
        |∑ k ∈ Finset.Icc 3 K, thetaDel S (x ^ ((1 : ℝ) / k))| := abs_add_three _ _ _
    _ ≤ C * x ^ γ + C * x ^ γ + 24 / α * (C + 1 / α) * x ^ (5 * α / 12) := by
        rw [abs_of_nonneg htail0]
        have : C * (x ^ ((1 : ℝ) / 2)) ^ γ ≤ C * x ^ γ := mul_le_mul_of_nonneg_left hpow2γ hC
        linarith
    _ ≤ C * x ^ chebExponent α + C * x ^ chebExponent α +
          24 / α * (C + 1 / α) * x ^ chebExponent α := by
        have := mul_le_mul_of_nonneg_left hη1 hC
        have := mul_le_mul_of_nonneg_left hη2 hC24
        linarith
    _ = (2 * C + 24 / α * (C + 1 / α)) * x ^ chebExponent α := by ring

/-- **The square-root floor for the counted deletion set:** under RH, `N_S(x) − a x ≠ O(x^θ)` for
every `a` and every `θ < α/2`. -/
theorem not_isBigO_qFreeCount (hRH : RiemannHypothesis) (hα1 : 1 / 2 < α) (hα : α < 1)
    {θ : ℝ} (hθ : θ < α / 2) (a : ℝ) :
    ¬ (fun x : ℝ => PrimeDeletion.qFreeCount (deletedC hα) x - a * x) =O[atTop]
      fun x => x ^ θ := by
  have hα0 : 0 < α := by linarith
  intro hO
  have hθθ : (fun x : ℝ => x ^ θ) =O[atTop] fun x => x ^ max θ 0 := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
  exact PrimeDeletion.not_isBigO_qFreeCount_of_multiplicity (deletedC hα) (l := 1) one_pos
    (le_max_right _ _) (max_lt hθ (by linarith)) (chebExponent_nonneg hα0)
    (chebExponent_lt hα0 hα) hα0 hα.le (isBigO_deletedChebyshev hRH hα1 hα) (hO.trans hθθ)

/-! ## The window -/

/-- The count-controlled deletion set as deletion data. -/
def countedData (hα0 : 0 < α) (hα : α < 1) : DeletionData α where
  S := deletedC hα
  prime := fun _ hp => prime_of_mem_deletedC hα hp
  C := Classical.choose (exists_twisted_bound hα0 hα)
  C_nonneg := (Classical.choose_spec (exists_twisted_bound hα0 hα)).1
  disc := (Classical.choose_spec (exists_twisted_bound hα0 hα)).2

end Counted

/-- `α/2 < β₀(α) < 1/2` on `(1/2, 4/5)`, and `β₀(α) > 0`. -/
theorem half_lt_betaZero {α : ℝ} (hα0 : 0 < α) (hα : α < 1) : α / 2 < betaZero α := by
  unfold betaZero
  split_ifs
  · rw [div_lt_div_iff₀ (by norm_num) (by linarith)]; nlinarith
  · rw [lt_div_iff₀ (by linarith)]; nlinarith

/-- Under RH, any deletion data has `N_S(x) = a x + O(x^β)` for every `β > β₀(α)`. -/
theorem DeletionData.exists_norm_count_sub_le_of_betaZero_lt {α : ℝ} (D : DeletionData α)
    (hRH : RiemannHypothesis) (hα1 : 1 / 2 < α) (hα : α < 1) {β : ℝ} (hβ : betaZero α < β) :
    ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X → ‖D.count X - D.density * X‖ ≤ C * X ^ β := by
  have hα0 : 0 < α := by linarith
  unfold betaZero at hβ
  split_ifs at hβ
  · obtain ⟨C, hC⟩ := D.exists_norm_count_sub_le_saw hRH hα1 hα (η := β - 3 * α / (α + 4))
      (by linarith)
    exact ⟨C, fun X hX => by simpa using hC X hX⟩
  · obtain ⟨C, hC⟩ := D.exists_norm_count_sub_le hRH hα0 hα (η := β - 1 / (3 - α)) (by linarith)
    exact ⟨C, fun X hX => by simpa using hC X hX⟩

theorem countFn_sFreeR_eq (S : Set ℕ) (x : ℝ) :
    GaloisForLFunctions.HTGeometry.PowerHyperbola.countFn (sFreeR S) x =
      PrimeDeletion.qFreeCount S x := by
  classical
  unfold GaloisForLFunctions.HTGeometry.PowerHyperbola.countFn PrimeDeletion.qFreeCount
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _), sFreeR_zero, zero_add]
  have hI : Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ := by
    ext; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hI]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold sFreeR PrimeDeletion.qFreeIndicator SFree
  congr 1

/-- **The deletion exponent lies in `[α/2, β₀(α)]`.**  Assume RH and `1/2 < α < 4/5`.  There is a
set `S` of primes whose deletion system is an `[α, β]`-system for every `β₀(α) < β < 1/2`, and
whose free integers have positive density `a` with `N_S(x) = a x + O(x^β)` for every `β > β₀(α)`,
while `N_S(x) − a' x ≠ O(x^θ)` for every `a'` and every `θ < α/2`. -/
theorem exists_deletion_exponent_window (hRH : RiemannHypothesis) {α : ℝ} (hα1 : 1 / 2 < α)
    (hα : α < 4 / 5) :
    ∃ S : Set ℕ, (∀ p ∈ S, p.Prime) ∧
      (∀ β (hβ : 0 < β), betaZero α < β → β < 1 / 2 →
        (deletionSystem S β hβ).IsAlphaBetaSystem α β) ∧
      ∃ a : ℝ, 0 < a ∧
        (∀ β, betaZero α < β →
          (fun x : ℝ => PrimeDeletion.qFreeCount S x - a * x) =O[atTop] fun x => x ^ β) ∧
        ∀ θ, θ < α / 2 → ∀ a' : ℝ,
          ¬ (fun x : ℝ => PrimeDeletion.qFreeCount S x - a' * x) =O[atTop] fun x => x ^ θ := by
  have hα' : α < 1 := by linarith
  have hα0 : 0 < α := by linarith
  set D := Counted.countedData hα0 hα' with hD
  have hb0 := half_lt_betaZero hα0 hα'
  -- a count exponent strictly between `β₀(α)` and `1`
  obtain ⟨C₀, hC₀⟩ := D.exists_norm_count_sub_le_of_betaZero_lt hRH hα1 hα'
    (β := (betaZero α + 1) / 2) (by
      have : betaZero α < 1 := by
        unfold betaZero; split_ifs
        · rw [div_lt_one (by linarith)]; linarith
        · rw [div_lt_one (by linarith)]; linarith
      linarith)
  have hbz1 : betaZero α < 1 := by
    unfold betaZero; split_ifs
    · rw [div_lt_one (by linarith)]; linarith
    · rw [div_lt_one (by linarith)]; linarith
  obtain ⟨hapos, -⟩ := D.density_re_pos hRH hα0 hα' (γ := (betaZero α + 1) / 2) (by linarith) hC₀
  refine ⟨D.S, D.prime, fun β hβ hβ0 hβ1 => ?_, D.density.re, hapos, fun β hβ => ?_,
    fun θ hθ a' => Counted.not_isBigO_qFreeCount hRH hα1 hα' hθ a'⟩
  · set γ := (betaZero α + β) / 2 with hγ
    obtain ⟨C, hC⟩ := D.exists_norm_count_sub_le_of_betaZero_lt hRH hα1 hα' (β := γ)
      (by rw [hγ]; linarith)
    exact isAlphaBetaSystem_of_count hRH hα1 hα' D hβ hβ1 (by linarith) (by linarith)
      (by rw [hγ]; linarith) ⟨C, hC⟩
  · obtain ⟨C, hC⟩ := D.exists_norm_count_sub_le_of_betaZero_lt hRH hα1 hα' hβ
    refine IsBigO.of_bound |C| ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have h := D.abs_countFn_sub_le hC x hx
    rw [countFn_sFreeR_eq] at h
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ x ^ β)]
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))

end RHTower.BeurlingDeletion
