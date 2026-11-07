import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheFirstReturnIsAnExtremeValue
import GaloisForLFunctions.PrimeTorusTheory.TheSavingAtEveryLength
import GaloisForLFunctions.PrimeTorusTheory.TheMassOfMisalignedPrimes
import GaloisForLFunctions.RHTower.ThetaChronologicalPacketResolution

/-!
# The precision law of the first return

Precision buys length. At a return to precision `η` on the primes below `y`, the critical defect
`D(t) = Σ_{p<y} (1 − cos(t log p))/√p` is at most `12 η √y` (`criticalDefect_le_of_isReturn`). Every absolute saving
`D(t) ≥ s(t)` of prime torus theory therefore excludes returns at precision `η < s(t)/(12√y)` at every height where it
holds. Since the first return tends to infinity with `y` (`tendsto_firstReturn_primesBelow`), small heights are excluded
as well, and the saving becomes a lower bound for `R(y, η)`.

* **Subexponential precision** (`eventually_exp_rpow_lt_firstReturn`). For `A > 1`, `δ > 0`: once `y` is large,
  `12 η √y < exp(−δ y^{1/A})` forces `R(y, η) > exp(y^{1/A})`. In logarithms, `log R ≥ (log(1/η))/δ` with `δ` arbitrary
  along `log(1/η) ≍ y^{1/A}`.
* **Polynomial precision gives the RH bracket** (`eventually_exp_sqrt_lt_firstReturn`). With `c = 4·48⁴/10^{10}`:
  `12 η √y · y⁴ < c` forces `R(y, η) > exp(√(y/(48 log y)))`. Under RH this lower bound holds at constant precision;
  unconditionally it holds at precision `≍ y^{−9/2}`.
* **The bracket** (`the_precision_law`). With the Dirichlet bound `R(y, η) ≤ Q^{π(y)}`, `2π² ≤ ηQ²`, and the pole's price
  `R(y, η) ≥ exp(c(log y)^{1−η})` of `TheFirstReturnIsAnExtremeValue`, the first return is bracketed at every precision.

What is missing is the constant-precision column: `log R(y, η)` at fixed `η` is known only between `(log y)^{1−η}` (here;
Vinogradov–Korobov gives `(log y)^{3/2−o(1)}`) and `y/log y`.
-/

open Real Finset Filter Topology

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

/-- `Σ_{p<N} 1/√p ≤ 12√N`. -/
theorem sum_primesBelow_inv_sqrt_le (N : ℕ) : ∑ p ∈ N.primesBelow, 1 / √(p : ℝ) ≤ 12 * √(N : ℝ) := by
  have h := RHTower.sum_primesLE_log_mul_rpow_neg_half_le N
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsub : N.primesBelow ⊆ Nat.primesLE N := by
    intro p hp
    rw [Nat.primesLE, Nat.mem_primesBelow] at *
    exact ⟨by omega, hp.2⟩
  have hterm : ∀ p ∈ Nat.primesLE N, 1 / √(p : ℝ) ≤ Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)) / Real.log 2 := by
    intro p hp
    rw [Nat.primesLE, Nat.mem_primesBelow] at hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
    have hlog : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    have hrpow : (p : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / √(p : ℝ) := by
      rw [Real.rpow_neg (by positivity), Real.sqrt_eq_rpow, inv_eq_one_div]
    rw [hrpow, le_div_iff₀ hl2]
    have h0 : 0 ≤ 1 / √(p : ℝ) := by positivity
    nlinarith
  calc ∑ p ∈ N.primesBelow, 1 / √(p : ℝ) ≤ ∑ p ∈ Nat.primesLE N, 1 / √(p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ p ∈ Nat.primesLE N, Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)) / Real.log 2 :=
        Finset.sum_le_sum hterm
    _ = (∑ p ∈ Nat.primesLE N, Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ))) / Real.log 2 := by
        rw [Finset.sum_div]
    _ ≤ 8 * √(N : ℝ) / Real.log 2 := div_le_div_of_nonneg_right h hl2.le
    _ ≤ 12 * √(N : ℝ) := by
        rw [div_le_iff₀ hl2]
        have := Real.log_two_gt_d9
        have : 0 ≤ √(N : ℝ) := Real.sqrt_nonneg _
        nlinarith

/-- **A return has a small critical defect.** -/
theorem criticalDefect_le_of_isReturn {N : ℕ} {η t : ℝ} (hη : 0 ≤ η)
    (h : IsReturn N.primesBelow logStep η t) :
    ∑ p ∈ N.primesBelow, (1 - cos (t * Real.log p)) / √(p : ℝ) ≤ η * (12 * √(N : ℝ)) := by
  calc ∑ p ∈ N.primesBelow, (1 - cos (t * Real.log p)) / √(p : ℝ)
      ≤ ∑ p ∈ N.primesBelow, η * (1 / √(p : ℝ)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (h p hp) (Real.sqrt_nonneg _)
    _ = η * ∑ p ∈ N.primesBelow, 1 / √(p : ℝ) := by rw [Finset.mul_sum]
    _ ≤ η * (12 * √(N : ℝ)) := mul_le_mul_of_nonneg_left (sum_primesBelow_inv_sqrt_le N) hη

/-- The first return on the primes below `N` tends to infinity. -/
theorem tendsto_firstReturn_primesBelow {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    Tendsto (fun N : ℕ => firstReturn N.primesBelow logStep η) atTop atTop := by
  have h := (tendsto_firstReturn_primes hη0 hη1).comp (tendsto_sub_atTop_nat 1)
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_ge_atTop 1] with N hN
  have e : Nat.primesLE (N - 1) = N.primesBelow := by
    rw [Nat.primesLE, Nat.sub_add_cancel hN]
  simp only [Function.comp_apply, e]
  exact le_rfl

/-- No return in `[a, b]` past a first return at least `a`: the first return exceeds `b`. -/
theorem lt_firstReturn_of_forall_not {ι : Type*} [DecidableEq ι] {s : Finset ι} {ℓ : ι → ℝ} {η a b : ℝ}
    (hη : 0 < η) (ha : a ≤ firstReturn s ℓ η) (h : ∀ t, a ≤ t → t ≤ b → ¬ IsReturn s ℓ η t) :
    b < firstReturn s ℓ η := by
  by_contra hle
  push Not at hle
  exact h _ ha hle (isReturn_firstReturn s ℓ hη)

/-- Small precision returns no earlier than precision `1/2`. -/
theorem eventually_le_firstReturn_of_small (T : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → T ≤ firstReturn N.primesBelow logStep η := by
  filter_upwards [(tendsto_firstReturn_primesBelow (η := 1 / 2) (by norm_num) (by norm_num)).eventually_ge_atTop T]
    with N hN η hη0 hη1
  exact hN.trans (firstReturn_anti_prec hη0 hη1)

/-- **Subexponential precision.** For `A > 1`, `δ > 0` and large `y`: `12 η √y < exp(−δ y^{1/A})` forces
`R(y, η) > exp(y^{1/A})`. -/
theorem eventually_exp_rpow_lt_firstReturn {A δ : ℝ} (hA : 1 < A) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ η : ℝ, 0 < η → η * (12 * √(N : ℝ)) < Real.exp (-(δ * (N : ℝ) ^ (1 / A))) →
      Real.exp ((N : ℝ) ^ (1 / A)) < firstReturn N.primesBelow logStep η := by
  obtain ⟨T₀, hT₀, hsave⟩ := PrimeTorusTheory.rpow_neg_le_sum_primes_critical hA hδ
  filter_upwards [eventually_le_firstReturn_of_small (max T₀ 1), eventually_ge_atTop 1] with N hN hN1 η hη0 hηs
  have hsq : 1 ≤ √(N : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hN1
  have hηhalf : η ≤ 1 / 2 := by
    have h1 : Real.exp (-(δ * (N : ℝ) ^ (1 / A))) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]
      positivity
    nlinarith
  refine lt_firstReturn_of_forall_not hη0 (hN η hη0 hηhalf) fun t ht1 ht2 hret => ?_
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ht1)
  have htabs : |t| = t := abs_of_pos ht0
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ((le_max_right _ _).trans ht1)
  have hlogt : Real.log t ≤ (N : ℝ) ^ (1 / A) := by
    rw [Real.log_le_iff_le_exp ht0]
    exact ht2
  have hA0 : 0 < A := by linarith
  have hlen : Real.log |t| ^ A ≤ (N : ℕ) := by
    rw [htabs]
    have h1 := Real.rpow_le_rpow hlogt0 hlogt hA0.le
    rw [← Real.rpow_mul (Nat.cast_nonneg N), one_div, inv_mul_cancel₀ hA0.ne', Real.rpow_one] at h1
    exact h1
  have hs := hsave t (by rw [htabs]; exact (le_max_left _ _).trans ht1) N hlen
  have hd := criticalDefect_le_of_isReturn hη0.le hret
  have hpow : Real.exp (-(δ * (N : ℝ) ^ (1 / A))) ≤ |t| ^ (-δ) := by
    rw [htabs, Real.rpow_def_of_pos ht0]
    exact Real.exp_le_exp.mpr (by nlinarith)
  linarith

/-- **Polynomial precision gives the RH bracket.** With `c = 4·48⁴/10^{10}` and large `y`: `12 η √y · y⁴ < c` forces
`R(y, η) > exp(√(y/(48 log y)))`. -/
theorem eventually_exp_sqrt_lt_firstReturn :
    ∀ᶠ N : ℕ in atTop, ∀ η : ℝ, 0 < η → η * (12 * √(N : ℝ)) * (N : ℝ) ^ 4 < 4 / 10 ^ 10 * 48 ^ 4 →
      Real.exp (√((N : ℝ) / (48 * Real.log N))) < firstReturn N.primesBelow logStep η := by
  obtain ⟨T₀, hT₀, hsave⟩ := PrimeTorusTheory.le_sum_primes_critical
  filter_upwards [eventually_le_firstReturn_of_small (max T₀ (Real.exp (Real.exp 1))), eventually_ge_atTop 3]
    with N hN hN3 η hη0 hηs
  have hN3' : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hlogN : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hsq : 1 ≤ √(N : ℝ) := by
    rw [Real.one_le_sqrt]
    linarith
  have hNpow : 1 ≤ (N : ℝ) ^ 4 := one_le_pow₀ (by linarith)
  have hηhalf : η ≤ 1 / 2 := by
    have h1 : η * (12 * √(N : ℝ)) * (N : ℝ) ^ 4 ≥ η * 12 := by
      have : 12 ≤ 12 * √(N : ℝ) * (N : ℝ) ^ 4 := by nlinarith
      nlinarith
    have : (4 : ℝ) / 10 ^ 10 * 48 ^ 4 < 6 := by norm_num
    linarith
  refine lt_firstReturn_of_forall_not hη0 (hN η hη0 hηhalf) fun t ht1 ht2 hret => ?_
  have hee : Real.exp (Real.exp 1) ≤ t := (le_max_right _ _).trans ht1
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) hee
  have htabs : |t| = t := abs_of_pos ht0
  set L := Real.log t with hL
  have hLe : Real.exp 1 ≤ L := by rw [hL, Real.le_log_iff_exp_le ht0]; exact hee
  have hL1 : 1 ≤ L := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hLe
  have hℓ1 : 1 ≤ Real.log L := by rw [Real.le_log_iff_exp_le (by linarith)]; exact hLe
  have hX : L ≤ √((N : ℝ) / (48 * Real.log N)) := by
    rw [hL, Real.log_le_iff_le_exp ht0]
    exact ht2
  have hL2 : L ^ 2 ≤ (N : ℝ) / (48 * Real.log N) := by
    have h0 : 0 ≤ L := by linarith
    have := pow_le_pow_left₀ h0 hX 2
    rwa [sq_sqrt (by positivity)] at this
  have hLN : L ≤ N := by
    have h1 : (N : ℝ) / (48 * Real.log N) ≤ N := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hℓN : Real.log L ≤ Real.log N := Real.log_le_log (by linarith) hLN
  have hprod : L ^ 2 * Real.log L ≤ (N : ℝ) / 48 := by
    have h1 : L ^ 2 * Real.log L ≤ (N : ℝ) / (48 * Real.log N) * Real.log N :=
      mul_le_mul hL2 hℓN (by linarith) (by positivity)
    have h2 : (N : ℝ) / (48 * Real.log N) * Real.log N = (N : ℝ) / 48 := by
      field_simp
    linarith
  have hlen : 48 * Real.log |t| ^ 2 * Real.log (Real.log |t|) ≤ (N : ℕ) := by
    rw [htabs, ← hL]
    linarith
  have hs := hsave t (by rw [htabs]; exact (le_max_left _ _).trans ht1) N hlen
  rw [htabs, ← hL] at hs
  have hd := criticalDefect_le_of_isReturn hη0.le hret
  -- The saving is at least `c/N⁴`.
  have hden : L ^ 8 * Real.log L ^ 4 ≤ ((N : ℝ) / 48) ^ 4 := by
    have e : L ^ 8 * Real.log L ^ 4 = (L ^ 2 * Real.log L) ^ 4 := by ring
    rw [e]
    exact pow_le_pow_left₀ (by positivity) hprod 4
  have hpos : 0 < L ^ 8 * Real.log L ^ 4 := by positivity
  have hsave' : 4 / 10 ^ 10 * 48 ^ 4 / (N : ℝ) ^ 4 ≤ 4 / 10 ^ 10 / (L ^ 8 * Real.log L ^ 4) := by
    have e : 4 / 10 ^ 10 * 48 ^ 4 / (N : ℝ) ^ 4 = 4 / 10 ^ 10 / (((N : ℝ) / 48) ^ 4) := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_left (by norm_num) hpos hden
  have hNp : 0 < (N : ℝ) ^ 4 := by positivity
  have hfin : η * (12 * √(N : ℝ)) < 4 / 10 ^ 10 * 48 ^ 4 / (N : ℝ) ^ 4 := by
    rw [lt_div_iff₀ hNp]
    exact hηs
  linarith

/-- **The precision law.** Dirichlet bounds the first return above at every precision; the saving at polynomial
precision bounds it below by the RH bracket; the pole bounds it below at constant precision. -/
theorem the_precision_law :
    (∀ (N Q : ℕ) (η : ℝ), 1 ≤ Q → 2 * π ^ 2 ≤ η * (Q : ℝ) ^ 2 →
      firstReturn N.primesBelow logStep η ≤ (Q : ℝ) ^ (N.primesBelow).card) ∧
    (∀ᶠ N : ℕ in atTop, ∀ η : ℝ, 0 < η → η * (12 * √(N : ℝ)) * (N : ℝ) ^ 4 < 4 / 10 ^ 10 * 48 ^ 4 →
      Real.exp (√((N : ℝ) / (48 * Real.log N))) < firstReturn N.primesBelow logStep η) ∧
    (∃ M : ℝ, 5 ≤ M ∧ ∀ N : ℕ, 3 ≤ N → ∀ η t : ℝ, 0 ≤ η → 1 ≤ t →
      IsReturn (Nat.primesLE N) logStep η t →
      (1 - η) * RHTower.Sieve.logLog N - η * |RHTower.Sieve.mertensSecondUpperConst| - harmonicConst ≤
        Real.log (M + Real.log (t + 1))) := by
  refine ⟨fun N Q η hQ hηQ => firstReturn_le_pow _ _ hQ hηQ, eventually_exp_sqrt_lt_firstReturn, ?_⟩
  obtain ⟨M, hM5, hM⟩ := exists_norm_zeta_le_log
  exact ⟨M, hM5, fun N hN η t hη ht h => firstReturn_lower hM5 hM hN hη ht h⟩

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
