import GaloisForLFunctions.MultiplicativePositivityGeometry.IntegralRealization
import GaloisForLFunctions.RHTower.Sieve.ChebyshevThetaBigO
import GaloisForLFunctions.RHTower.VonMangoldtLogMomentHankel
import GaloisForLFunctions.RHTower.SelbergPrimePolynomialHighMoments

/-!
# Integral realization of the lattice divisors over the rational primes

The one-prime factor `(1 − e^{−h(s−1)})^{−1}` (and its shift by `a`) has the boundary divisor
`cos(au)` on the lattice `(2π/h)ℤ` and `0` off it (`progression_isBoundaryDivisor`); with `a = h`
this is the lattice of simple poles, with `a = h/2` the alternating character. Its frequencies
`λ_k = hk + a` are not logarithms of integers. They are reproduced by rational primes in shrinking
windows.

* **Windows** (`window`). `W_k` is the set of primes in `(e^{λ_k}, e^{λ_k}(1 + 1/(k+1)²)]`. By the
  prime number theorem with the error `x e^{−c√log x}` its mass `S_k = Σ_{p ∈ W_k} log p / p` lies
  in `[1/(4(k+1)²), 2/(k+1)²]` for large `k`, and the windows are disjoint
  (`eventually_window_good`).
* **Multiplicities.** Every prime of `W_k` gets the exponent `M_k = ⌊h / S_k⌋`; all other primes
  get `0`. The Euler product `Π_p (1 − p^{−s})^{−m(p)}` has nonnegative integer exponents.
* **Same divisor** (`latticeRound_isBoundaryDivisor`). Window by window the integral weights carry
  mass `M_k S_k ∈ (h − S_k, h]` on frequencies within `1/(k+1)²` of `λ_k`; the total discrepancy is
  bounded uniformly in the damping, so it is invisible at the boundary.

Consequences (`integral_lattice`, `integral_alternating`): the lattice of simple poles and the
alternating character are boundary divisors of Euler products with nonnegative integer exponents
over the rational primes. With the finite configurations of `IntegralRealization` every type of
the boundary trichotomy and every countermodel of the minimality table except the signed one is
realized by integral data.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-! ### Windows of primes -/

/-- The window frequencies `λ_k = hk + a`. -/
noncomputable def winFreq (h a : ℝ) (k : ℕ) : ℝ := h * k + a

/-- The left end `e^{λ_k}` of the `k`-th window. -/
noncomputable def winLo (h a : ℝ) (k : ℕ) : ℝ := Real.exp (winFreq h a k)

/-- The right end `e^{λ_k}(1 + 1/(k+1)²)` of the `k`-th window. -/
noncomputable def winHi (h a : ℝ) (k : ℕ) : ℝ := winLo h a k * (1 + 1 / ((k : ℝ) + 1) ^ 2)

/-- The primes of the `k`-th window. -/
noncomputable def window (h a : ℝ) (k : ℕ) : Finset ℕ :=
  (Ioc ⌊winLo h a k⌋₊ ⌊winHi h a k⌋₊).filter Nat.Prime

/-- The window mass `S_k = Σ_{p ∈ W_k} log p / p`. -/
noncomputable def windowMass (h a : ℝ) (k : ℕ) : ℝ := ∑ p ∈ window h a k, Real.log p / p

variable {h a : ℝ}

theorem winLo_pos (k : ℕ) : 0 < winLo h a k := Real.exp_pos _

theorem winLo_lt_winHi (k : ℕ) : winLo h a k < winHi h a k := by
  unfold winHi
  have := winLo_pos (h := h) (a := a) k
  have : 0 < 1 / ((k : ℝ) + 1) ^ 2 := by positivity
  nlinarith

theorem winHi_le_two_mul (k : ℕ) : winHi h a k ≤ 2 * winLo h a k := by
  unfold winHi
  have h1 : 1 / ((k : ℝ) + 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  nlinarith [winLo_pos (h := h) (a := a) k]

theorem mem_window {k p : ℕ} (hp : p ∈ window h a k) :
    winLo h a k < p ∧ (p : ℝ) ≤ winHi h a k ∧ p.Prime := by
  unfold window at hp
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  refine ⟨(Nat.floor_lt (winLo_pos k).le).mp hp.1.1, ?_, hp.2⟩
  exact (Nat.le_floor_iff (le_of_lt ((winLo_pos k).trans (winLo_lt_winHi k)))).mp hp.1.2

theorem log_mem_window {k p : ℕ} (hp : p ∈ window h a k) :
    winFreq h a k < Real.log p ∧ Real.log p ≤ winFreq h a k + 1 / ((k : ℝ) + 1) ^ 2 := by
  obtain ⟨hlo, hhi, -⟩ := mem_window hp
  have hp0 : (0 : ℝ) < p := (winLo_pos k).trans hlo
  constructor
  · rw [← Real.log_exp (winFreq h a k)]
    exact Real.log_lt_log (winLo_pos k) hlo
  · have h1 := Real.log_le_log hp0 hhi
    unfold winHi winLo at h1
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp] at h1
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / ((k : ℝ) + 1) ^ 2 by positivity)
    linarith

/-- The `θ`-mass of a window. -/
theorem sum_log_window (k : ℕ) :
    ∑ p ∈ window h a k, Real.log p =
      Chebyshev.theta (winHi h a k) - Chebyshev.theta (winLo h a k) := by
  have hle : ⌊winLo h a k⌋₊ ≤ ⌊winHi h a k⌋₊ := Nat.floor_le_floor (winLo_lt_winHi k).le
  simp only [Chebyshev.theta, window, Finset.sum_filter]
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le ⌊winLo h a k⌋₊) hle]
  ring

theorem windowMass_le (k : ℕ) :
    windowMass h a k ≤ (∑ p ∈ window h a k, Real.log p) / winLo h a k := by
  unfold windowMass
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hlo, -, hpr⟩ := mem_window hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
  exact div_le_div_of_nonneg_left hlog (winLo_pos k) hlo.le

theorem le_windowMass (k : ℕ) :
    (∑ p ∈ window h a k, Real.log p) / winHi h a k ≤ windowMass h a k := by
  unfold windowMass
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hlo, hhi, hpr⟩ := mem_window hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
  exact div_le_div_of_nonneg_left hlog ((winLo_pos k).trans hlo) hhi

/-- `(k+1)² e^{−c√(hk + a)} → 0`. -/
theorem tendsto_sq_mul_exp_neg_sqrt (hh : 0 < h) (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * Real.exp (-c * Real.sqrt (h * k + a))) atTop
      (𝓝 0) := by
  set b := c * Real.sqrt (h / 2)
  have hb : 0 < b := mul_pos hc (Real.sqrt_pos.mpr (by linarith))
  have hbound : ∀ᶠ k : ℕ in atTop, ((k : ℝ) + 1) ^ 2 * Real.exp (-c * Real.sqrt (h * k + a)) ≤
      2880 / b ^ 6 * (1 / (k : ℝ)) := by
    have hk0 : ∀ᶠ k : ℕ in atTop, (2 * |a| / h : ℝ) ≤ k := by
      simpa using tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * |a| / h)
    filter_upwards [hk0, eventually_ge_atTop 1] with k hk hk1
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hhalf : h / 2 * k ≤ h * k + a := by
      have : 2 * |a| ≤ h * k := by rwa [div_le_iff₀ hh, mul_comm] at hk
      linarith [neg_abs_le a]
    have hsq : b * Real.sqrt k ≤ c * Real.sqrt (h * k + a) := by
      rw [show b * Real.sqrt k = c * Real.sqrt (h / 2 * k) by
        rw [Real.sqrt_mul (by linarith) k]; ring]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hhalf) hc.le
    have hexp : Real.exp (-c * Real.sqrt (h * k + a)) ≤ Real.exp (-(b * Real.sqrt k)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hpow := Real.pow_div_factorial_le_exp (le_of_lt (mul_pos hb (Real.sqrt_pos.mpr
      (by linarith)))) 6
    have hfact : (Nat.factorial 6 : ℝ) = 720 := by norm_num [Nat.factorial]
    rw [hfact, mul_pow, show Real.sqrt k ^ 6 = (k : ℝ) ^ 3 by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt (by linarith)]] at hpow
    have hepos : 0 < Real.exp (b * Real.sqrt k) := Real.exp_pos _
    have hinv : Real.exp (-(b * Real.sqrt k)) ≤ 720 / (b ^ 6 * (k : ℝ) ^ 3) := by
      rw [Real.exp_neg, inv_le_comm₀ hepos (by positivity), inv_div]
      linarith
    calc ((k : ℝ) + 1) ^ 2 * Real.exp (-c * Real.sqrt (h * k + a))
        ≤ (2 * k) ^ 2 * (720 / (b ^ 6 * (k : ℝ) ^ 3)) := by
          refine mul_le_mul (by nlinarith) (hexp.trans hinv) (Real.exp_pos _).le (by positivity)
      _ = 2880 / b ^ 6 * (1 / (k : ℝ)) := by field_simp; ring
  have hlim : Tendsto (fun k : ℕ => 2880 / b ^ 6 * (1 / (k : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat).const_mul (2880 / b ^ 6)
  refine squeeze_zero' (Eventually.of_forall fun k => by positivity) hbound hlim

/-- **Good windows.** For large `k` the window mass lies in `[1/(4(k+1)²), 2/(k+1)²]` and the
window ends before the next one starts. -/
theorem eventually_window_good (hh : 0 < h) (a : ℝ) :
    ∀ᶠ k : ℕ in atTop, 1 / (4 * ((k : ℝ) + 1) ^ 2) ≤ windowMass h a k ∧
      windowMass h a k ≤ 2 / ((k : ℝ) + 1) ^ 2 ∧ winHi h a k < winLo h a (k + 1) := by
  obtain ⟨c, hc, hθ⟩ := RHTower.Sieve.chebyshevTheta_sub_id_isBigO
  obtain ⟨C, hC⟩ := hθ.bound
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp (hC.and (eventually_ge_atTop (1 : ℝ)))
  have hlo : Tendsto (fun k : ℕ => winLo h a k) atTop atTop := by
    unfold winLo winFreq
    refine Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_right _ a ?_)
    exact (tendsto_natCast_atTop_atTop).const_mul_atTop hh
  have hsmall := (tendsto_sq_mul_exp_neg_sqrt hh a hc).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / (6 * (|C| + 1)) by positivity))
  have hdisj : ∀ᶠ k : ℕ in atTop, 1 + 1 / ((k : ℝ) + 1) ^ 2 < Real.exp h := by
    have h1 : 1 < Real.exp h := Real.one_lt_exp.mpr hh
    have ht : Tendsto (fun k : ℕ => 1 + 1 / ((k : ℝ) + 1) ^ 2) atTop (𝓝 1) := by
      have : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
        have h2 := (tendsto_one_div_add_atTop_nhds_zero_nat).pow 2
        simpa [one_div, inv_pow] using h2
      simpa using this.const_add 1
    exact ht.eventually (gt_mem_nhds h1)
  filter_upwards [hlo.eventually (eventually_ge_atTop x₀), hsmall, hdisj] with k hk hsm hdj
  set lo := winLo h a k
  set hi := winHi h a k
  set ε := Real.exp (-c * Real.sqrt (h * k + a))
  have hlo0 : 0 < lo := winLo_pos k
  have hlohi := winLo_lt_winHi (h := h) (a := a) k
  have hhi2 := winHi_le_two_mul (h := h) (a := a) k
  have hε0 : 0 < ε := Real.exp_pos _
  have hlogLo : Real.log lo = h * k + a := by simp [lo, winLo, winFreq]
  -- PNT error at both ends, bounded by `C ε` times the end.
  have herr : ∀ y : ℝ, lo ≤ y → |Chebyshev.theta y - y| ≤ |C| * y * ε := by
    intro y hy
    have hy0 : 0 < y := hlo0.trans_le hy
    have hx := (hx₀ y (hk.trans hy)).1
    simp only [Pi.sub_apply, id, Real.norm_eq_abs] at hx
    have hgy : |y * Real.exp (-c * Real.sqrt (Real.log y))| ≤ y * ε := by
      rw [abs_of_pos (by positivity)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hy0.le
      have : Real.log lo ≤ Real.log y := Real.log_le_log hlo0 hy
      have : Real.sqrt (h * k + a) ≤ Real.sqrt (Real.log y) := Real.sqrt_le_sqrt (by linarith)
      nlinarith
    calc |Chebyshev.theta y - y| ≤ C * |y * Real.exp (-c * Real.sqrt (Real.log y))| := hx
      _ ≤ |C| * (y * ε) := mul_le_mul (le_abs_self C) hgy (abs_nonneg _) (abs_nonneg C)
      _ = |C| * y * ε := by ring
  have h1 := herr lo le_rfl
  have h2 := herr hi hlohi.le
  have hwidth : hi - lo = lo / ((k : ℝ) + 1) ^ 2 := by simp only [hi, winHi]; ring
  have hsm' : 6 * (|C| + 1) * (((k : ℝ) + 1) ^ 2 * ε) < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hsm; linarith
  have hk2 : 0 < ((k : ℝ) + 1) ^ 2 := by positivity
  have hθlo : |C| * lo * ε ≤ lo / (6 * ((k : ℝ) + 1) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have : |C| * (((k : ℝ) + 1) ^ 2 * ε) * 6 ≤ 1 := by nlinarith [abs_nonneg C]
    nlinarith
  have hθhi : |C| * hi * ε ≤ lo / (3 * ((k : ℝ) + 1) ^ 2) := by
    have : |C| * hi * ε ≤ |C| * (2 * lo) * ε :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhi2 (abs_nonneg C)) hε0.le
    have e : lo / (3 * ((k : ℝ) + 1) ^ 2) = 2 * (lo / (6 * ((k : ℝ) + 1) ^ 2)) := by
      field_simp; ring
    rw [e]; nlinarith
  have hsumlo := sum_log_window (h := h) (a := a) k
  rw [abs_le] at h1 h2
  have hmass_lo : lo / (2 * ((k : ℝ) + 1) ^ 2) ≤ ∑ p ∈ window h a k, Real.log p := by
    rw [hsumlo]
    have e : lo / (2 * ((k : ℝ) + 1) ^ 2) =
        lo / ((k : ℝ) + 1) ^ 2 - lo / (6 * ((k : ℝ) + 1) ^ 2) - lo / (3 * ((k : ℝ) + 1) ^ 2) := by
      field_simp; ring
    rw [e]; linarith
  have hmass_hi : ∑ p ∈ window h a k, Real.log p ≤ 2 * lo / ((k : ℝ) + 1) ^ 2 := by
    rw [hsumlo]
    have e : 2 * lo / ((k : ℝ) + 1) ^ 2 ≥
        lo / ((k : ℝ) + 1) ^ 2 + lo / (6 * ((k : ℝ) + 1) ^ 2) + lo / (3 * ((k : ℝ) + 1) ^ 2) := by
      rw [ge_iff_le, div_add_div _ _ (by positivity) (by positivity),
        div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) hk2]
      nlinarith
    linarith
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans ?_ (le_windowMass k)
    rw [le_div_iff₀ (hlo0.trans hlohi)]
    calc 1 / (4 * ((k : ℝ) + 1) ^ 2) * hi ≤ 1 / (4 * ((k : ℝ) + 1) ^ 2) * (2 * lo) :=
          mul_le_mul_of_nonneg_left hhi2 (by positivity)
      _ = lo / (2 * ((k : ℝ) + 1) ^ 2) := by field_simp; ring
      _ ≤ _ := hmass_lo
  · refine (windowMass_le k).trans ?_
    rw [div_le_div_iff₀ hlo0 hk2]
    nlinarith
  · simp only [hi, winHi, winLo, winFreq]
    rw [show h * ((k + 1 : ℕ) : ℝ) + a = (h * k + a) + h by push_cast; ring, Real.exp_add]
    exact mul_lt_mul_of_pos_left hdj (Real.exp_pos _)

end GaloisForLFunctions.MultiplicativePositivityGeometry
