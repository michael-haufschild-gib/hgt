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
      have : 2 * |a| ≤ h * k := by have := (div_le_iff₀ hh).mp hk; linarith
      linarith [neg_abs_le a]
    have hsq : b * Real.sqrt k ≤ c * Real.sqrt (h * k + a) := by
      rw [show b * Real.sqrt k = c * Real.sqrt (h / 2 * k) by
        rw [Real.sqrt_mul (by linarith) k]; ring]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hhalf) hc.le
    have hexp : Real.exp (-c * Real.sqrt (h * k + a)) ≤ Real.exp (-(b * Real.sqrt k)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hpow := Real.pow_div_factorial_le_exp (b * Real.sqrt k) (by positivity) 6
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
    have := (tendsto_one_div_atTop_nhds_zero_nat).const_mul (2880 / b ^ 6)
    rwa [mul_zero] at this
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
    have h1 : 1 < Real.exp h := by have := Real.add_one_lt_exp (ne_of_gt hh); linarith
    have ht : Tendsto (fun k : ℕ => 1 + 1 / ((k : ℝ) + 1) ^ 2) atTop (𝓝 1) := by
      have : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
        have h2 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa [div_pow] using h2.pow 2
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
  have hsumlo : ∑ p ∈ window h a k, Real.log p = Chebyshev.theta hi - Chebyshev.theta lo :=
    sum_log_window k
  rw [abs_le] at h1 h2
  -- Everything in units of `q = lo/(k+1)²`, the window width.
  have hq : 0 < lo / ((k : ℝ) + 1) ^ 2 := div_pos hlo0 hk2
  have e6 : lo / (6 * ((k : ℝ) + 1) ^ 2) = lo / ((k : ℝ) + 1) ^ 2 / 6 := by
    rw [div_div, mul_comm]
  have e3 : lo / (3 * ((k : ℝ) + 1) ^ 2) = lo / ((k : ℝ) + 1) ^ 2 / 3 := by
    rw [div_div, mul_comm]
  rw [e6] at hθlo
  rw [e3] at hθhi
  have hmass_lo : lo / (2 * ((k : ℝ) + 1) ^ 2) ≤ ∑ p ∈ window h a k, Real.log p := by
    rw [hsumlo, show lo / (2 * ((k : ℝ) + 1) ^ 2) = lo / ((k : ℝ) + 1) ^ 2 / 2 by
      rw [div_div, mul_comm]]
    linarith
  have hmass_hi : ∑ p ∈ window h a k, Real.log p ≤ 2 * lo / ((k : ℝ) + 1) ^ 2 := by
    rw [hsumlo, mul_div_assoc]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans ?_ (le_windowMass k)
    rw [le_div_iff₀ (hlo0.trans hlohi)]
    calc 1 / (4 * ((k : ℝ) + 1) ^ 2) * hi ≤ 1 / (4 * ((k : ℝ) + 1) ^ 2) * (2 * lo) :=
          mul_le_mul_of_nonneg_left hhi2 (by positivity)
      _ = lo / (2 * ((k : ℝ) + 1) ^ 2) := by field_simp; ring
      _ ≤ _ := hmass_lo
  · refine (windowMass_le k).trans ?_
    rw [div_le_iff₀ hlo0]
    calc _ ≤ 2 * lo / ((k : ℝ) + 1) ^ 2 := hmass_hi
      _ = 2 / ((k : ℝ) + 1) ^ 2 * lo := by ring
  · simp only [hi, winHi, winLo, winFreq]
    rw [show h * ((k + 1 : ℕ) : ℝ) + a = (h * k + a) + h by push_cast; ring,
      Real.exp_add (h * k + a) h]
    exact mul_lt_mul_of_pos_left hdj (Real.exp_pos _)

/-! ### The integral exponents -/

/-- A start index past which every window is good. -/
noncomputable def goodStart (hh : 0 < h) (a : ℝ) : ℕ :=
  max 1 (Classical.choose (Filter.eventually_atTop.mp (eventually_window_good hh a)))

theorem good_of_le (hh : 0 < h) (a : ℝ) {k : ℕ} (hk : goodStart hh a ≤ k) :
    1 / (4 * ((k : ℝ) + 1) ^ 2) ≤ windowMass h a k ∧
      windowMass h a k ≤ 2 / ((k : ℝ) + 1) ^ 2 ∧ winHi h a k < winLo h a (k + 1) :=
  Classical.choose_spec (Filter.eventually_atTop.mp (eventually_window_good hh a)) k
    (le_trans (le_max_right _ _) hk)

theorem winLo_mono (hh : 0 < h) {k k' : ℕ} (hkk : k ≤ k') : winLo h a k ≤ winLo h a k' := by
  unfold winLo winFreq
  refine Real.exp_le_exp.mpr ?_
  have : (k : ℝ) ≤ k' := by exact_mod_cast hkk
  nlinarith

/-- Good windows are ordered: every prime of an earlier window is smaller. -/
theorem lt_of_mem_window (hh : 0 < h) {k k' p q : ℕ} (hk : goodStart hh a ≤ k) (hkk : k < k')
    (hp : p ∈ window h a k) (hq : q ∈ window h a k') : p < q := by
  have h1 := (mem_window hp).2.1
  have h2 := (good_of_le hh a hk).2.2
  have h3 := winLo_mono (a := a) hh (Nat.succ_le_of_lt hkk)
  have h4 := (mem_window hq).1
  exact_mod_cast (h1.trans_lt (h2.trans_le h3)).trans h4

theorem eq_of_mem_window (hh : 0 < h) {k k' p : ℕ} (hk : goodStart hh a ≤ k)
    (hk' : goodStart hh a ≤ k') (hp : p ∈ window h a k) (hp' : p ∈ window h a k') : k = k' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact lt_irrefl p (lt_of_mem_window hh hk hlt hp hp')
  · exact lt_irrefl p (lt_of_mem_window hh hk' hlt hp' hp)

open Classical in
/-- The window index of `n` (zero if `n` lies in no good window). -/
noncomputable def windowIndex (hh : 0 < h) (a : ℝ) (n : ℕ) : ℕ :=
  if hn : ∃ k, goodStart hh a ≤ k ∧ n ∈ window h a k then Nat.find hn else 0

/-- The integer exponent `⌊h/S_k⌋` of a prime of the `k`-th good window, `0` elsewhere. -/
noncomputable def latticeMult (hh : 0 < h) (a : ℝ) (n : ℕ) : ℕ :=
  if goodStart hh a ≤ windowIndex hh a n ∧ n ∈ window h a (windowIndex hh a n) then
    ⌊h / windowMass h a (windowIndex hh a n)⌋₊ else 0

theorem windowIndex_of_mem (hh : 0 < h) {k p : ℕ} (hk : goodStart hh a ≤ k)
    (hp : p ∈ window h a k) : windowIndex hh a p = k := by
  classical
  have hex : ∃ k, goodStart hh a ≤ k ∧ p ∈ window h a k := ⟨k, hk, hp⟩
  unfold windowIndex
  rw [dif_pos hex]
  have hs := Nat.find_spec hex
  exact eq_of_mem_window hh hs.1 hk hs.2 hp

theorem latticeMult_of_mem (hh : 0 < h) {k p : ℕ} (hk : goodStart hh a ≤ k)
    (hp : p ∈ window h a k) : latticeMult hh a p = ⌊h / windowMass h a k⌋₊ := by
  unfold latticeMult
  rw [windowIndex_of_mem hh hk hp, if_pos ⟨hk, hp⟩]

theorem latticeMult_eq_zero (hh : 0 < h) {n : ℕ}
    (hn : ∀ k, goodStart hh a ≤ k → n ∉ window h a k) : latticeMult hh a n = 0 := by
  unfold latticeMult
  rw [if_neg fun h' => hn _ h'.1 h'.2]

/-- The exponents grow at most like `(log p)²`. -/
theorem latticeMult_le (hh : 0 < h) (n : ℕ) :
    (latticeMult hh a n : ℝ) ≤ 4 / h * (Real.log n + |a| + h) ^ 2 := by
  by_cases hn : ∃ k, goodStart hh a ≤ k ∧ n ∈ window h a k
  · obtain ⟨k, hk, hp⟩ := hn
    rw [latticeMult_of_mem hh hk hp]
    obtain ⟨hS, -, -⟩ := good_of_le hh a hk
    have hk2 : 0 < ((k : ℝ) + 1) ^ 2 := by positivity
    have hS0 : 0 < windowMass h a k := lt_of_lt_of_le (by positivity) hS
    have h1 : (⌊h / windowMass h a k⌋₊ : ℝ) ≤ 4 * h * ((k : ℝ) + 1) ^ 2 := by
      refine (Nat.floor_le (div_nonneg hh.le hS0.le)).trans ?_
      rw [div_le_iff₀ hS0]
      have : 1 ≤ 4 * ((k : ℝ) + 1) ^ 2 * windowMass h a k := by
        rw [div_le_iff₀ (by positivity)] at hS; linarith
      nlinarith
    have hlog := (log_mem_window hp).1
    unfold winFreq at hlog
    have hk1 : (k : ℝ) + 1 ≤ (Real.log n + |a| + h) / h := by
      rw [le_div_iff₀ hh]
      nlinarith [neg_abs_le a]
    have hk0 : 0 ≤ (k : ℝ) + 1 := by positivity
    calc (⌊h / windowMass h a k⌋₊ : ℝ) ≤ 4 * h * ((k : ℝ) + 1) ^ 2 := h1
      _ ≤ 4 * h * ((Real.log n + |a| + h) / h) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk0 hk1 2) (by positivity)
      _ = 4 / h * (Real.log n + |a| + h) ^ 2 := by field_simp
  · push Not at hn
    rw [latticeMult_eq_zero hh fun k hk hp => hn k hk hp, Nat.cast_zero]
    positivity

/-! ### The integral datum has the lattice divisor -/

/-- Proper prime powers with a squared logarithm have finite total mass. -/
theorem summable_nonprime_logSq :
    Summable fun n : ℕ => if n.Prime then 0 else
      (1 + Real.log n) ^ 2 * (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
  set d : ℕ → ℝ := fun n => if n.Prime then 0 else
    (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 + 1 / 4 : ℝ))
  have hd0 : ∀ n, 0 ≤ d n := fun n => by
    simp only [d]; split_ifs
    · exact le_rfl
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hd : Summable d := by
    refine summable_of_sum_range_le hd0 (c := 36 / (1 / 4)) fun N => ?_
    have hsub : ∑ i ∈ range N, d i ≤ ∑ i ∈ Icc 0 N, d i :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => by
        simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega) fun i _ _ => hd0 i
    refine hsub.trans ?_
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le N)]
    have h0 : d 0 = 0 := by simp [d, Nat.not_prime_zero]
    rw [h0, zero_add, show Ioc 0 N = Icc 1 N by ext; simp; omega, ← Finset.sum_filter_add_sum_filter_not
      (Icc 1 N) Nat.Prime]
    have hpr : ∑ i ∈ (Icc 1 N).filter Nat.Prime, d i = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [d, (Finset.mem_filter.mp hi).2]
    rw [hpr, zero_add]
    have hnp : ∑ i ∈ (Icc 1 N).filter (fun n => ¬ n.Prime), d i =
        ∑ i ∈ (Icc 1 N).filter (fun n => ¬ n.Prime),
          (ArithmeticFunction.vonMangoldt i : ℝ) * (i : ℝ) ^ (-(1 / 2 + 1 / 4 : ℝ)) :=
      Finset.sum_congr rfl fun i hi => by simp [d, (Finset.mem_filter.mp hi).2]
    rw [hnp]
    exact RHTower.sum_nonprime_vonMangoldt_rpow_le (by norm_num) (by norm_num) N
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hd.mul_left 81)
  · split_ifs
    · exact le_rfl
    · exact div_nonneg (mul_nonneg (sq_nonneg _) ArithmeticFunction.vonMangoldt_nonneg)
        (Nat.cast_nonneg _)
  · simp only [d]
    split_ifs with hp
    · simp
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < n := by linarith
      have hlog := Real.log_le_rpow_div hn0.le (by norm_num : (0 : ℝ) < 1 / 8)
      have hr1 : 1 ≤ (n : ℝ) ^ (1 / 8 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
      have hsq : (1 + Real.log n) ^ 2 ≤ 81 * (n : ℝ) ^ (1 / 4 : ℝ) := by
        have h9 : 1 + Real.log n ≤ 9 * (n : ℝ) ^ (1 / 8 : ℝ) := by
          have : Real.log n ≤ 8 * (n : ℝ) ^ (1 / 8 : ℝ) := by
            rw [show (n : ℝ) ^ (1 / 8 : ℝ) / (1 / 8) = 8 * (n : ℝ) ^ (1 / 8 : ℝ) by ring] at hlog
            exact hlog
          linarith
        have hl0 : 0 ≤ 1 + Real.log n := by linarith [Real.log_nonneg hn1]
        calc (1 + Real.log n) ^ 2 ≤ (9 * (n : ℝ) ^ (1 / 8 : ℝ)) ^ 2 := pow_le_pow_left₀ hl0 h9 2
          _ = 81 * (n : ℝ) ^ (1 / 4 : ℝ) := by
            rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 8 : ℝ)) 2, ← Real.rpow_mul hn0.le]
            norm_num
      have hdiv : (n : ℝ) ^ (1 / 4 : ℝ) / n = (n : ℝ) ^ (-(1 / 2 + 1 / 4 : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hn0]
        norm_num
      have hΛ := (ArithmeticFunction.vonMangoldt_nonneg (n := n) : (0 : ℝ) ≤ _)
      calc (1 + Real.log n) ^ 2 * (ArithmeticFunction.vonMangoldt n : ℝ) / n
          ≤ 81 * (n : ℝ) ^ (1 / 4 : ℝ) * (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
            gcongr
        _ = 81 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 + 1 / 4 : ℝ))) := by
            rw [← hdiv]; ring

/-- The damped mode `e^{−tx} cos(tu)` moves by at most `e^{−λx}(t − λ)(x + |u|)` for `t ≥ λ`. -/
theorem abs_mode_sub_le {x u t l : ℝ} (hx : 0 ≤ x) (htl : l ≤ t) :
    |Real.exp (-(t * x)) * Real.cos (t * u) - Real.exp (-(l * x)) * Real.cos (l * u)| ≤
      Real.exp (-(l * x)) * ((t - l) * (x + |u|)) := by
  have hsplit : Real.exp (-(t * x)) * Real.cos (t * u) - Real.exp (-(l * x)) * Real.cos (l * u) =
      (Real.exp (-(t * x)) - Real.exp (-(l * x))) * Real.cos (t * u) +
        Real.exp (-(l * x)) * (Real.cos (t * u) - Real.cos (l * u)) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have he : |Real.exp (-(t * x)) - Real.exp (-(l * x))| ≤ Real.exp (-(l * x)) * ((t - l) * x) := by
    have hfac : Real.exp (-(t * x)) = Real.exp (-(l * x)) * Real.exp (-((t - l) * x)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hfac, show Real.exp (-(l * x)) * Real.exp (-((t - l) * x)) - Real.exp (-(l * x)) =
      -(Real.exp (-(l * x)) * (1 - Real.exp (-((t - l) * x)))) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (by
        linarith [Real.exp_le_one_iff.mpr (by nlinarith : -((t - l) * x) ≤ 0)]))]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (-((t - l) * x))])
      (Real.exp_pos _).le
  have hc : |Real.cos (t * u) - Real.cos (l * u)| ≤ (t - l) * |u| := by
    refine (Real.abs_cos_sub_cos_le _ _).trans ?_
    rw [← sub_mul, abs_mul, abs_of_nonneg (by linarith)]
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos (-(l * x)))]
  have := Real.abs_cos_le_one (t * u)
  have hE := (Real.exp_pos (-(l * x))).le
  nlinarith [abs_nonneg (Real.exp (-(t * x)) - Real.exp (-(l * x))),
    abs_nonneg (Real.cos (t * u) - Real.cos (l * u))]

theorem summable_inv_succ_sq : Summable fun c : ℕ => 1 / ((c : ℝ) + 1) ^ 2 := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa [Nat.cast_add, Nat.cast_one] using h

/-- One good window against one term of the progression datum. -/
theorem abs_window_sub_le (hh : 0 < h) {c : ℕ} (hc : goodStart hh a ≤ c) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x ≤ 1) (u : ℝ) :
    |∑ p ∈ window h a c, (latticeMult hh a p : ℝ) * zetaBoundaryWeight x p *
        Real.cos (logFrequency p * u) -
      h * Real.exp (-(winFreq h a c * x)) * Real.cos (winFreq h a c * u)| ≤
      Real.exp |a| * (2 + h * (1 + |u|)) * (1 / ((c : ℝ) + 1) ^ 2) := by
  obtain ⟨hS, hS2, -⟩ := good_of_le hh a hc
  set S := windowMass h a c
  set M := ⌊h / S⌋₊
  set l := winFreq h a c
  have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS
  have hM : (M : ℝ) * S ≤ h := by
    have := Nat.floor_le (div_nonneg hh.le hS0.le)
    rwa [le_div_iff₀ hS0] at this
  have hM' : h - S < (M : ℝ) * S := by
    have := Nat.lt_floor_add_one (h / S)
    rw [div_lt_iff₀ hS0] at this
    linarith
  have hE : Real.exp (-(l * x)) ≤ Real.exp |a| := by
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ h * (c : ℝ) * x := by positivity
    simp only [l, winFreq]
    nlinarith [neg_abs_le a, le_abs_self a]
  -- Rewrite each prime term as `M (log p / p) · φ(log p)`.
  have hterm : ∀ p ∈ window h a c, (latticeMult hh a p : ℝ) * zetaBoundaryWeight x p *
      Real.cos (logFrequency p * u) = M * (Real.log p / p) *
        (Real.exp (-(Real.log p * x)) * Real.cos (Real.log p * u)) := by
    intro p hp
    obtain ⟨hlo, -, hpr⟩ := mem_window hp
    have hp0 : (0 : ℝ) < p := (winLo_pos c).trans hlo
    rw [latticeMult_of_mem hh hc hp, zetaBoundaryWeight, ArithmeticFunction.vonMangoldt_apply_prime hpr,
      logFrequency, Real.rpow_def_of_pos hp0, show Real.log p * -(1 + x) = -Real.log p + -(Real.log p * x)
        by ring, Real.exp_add, Real.exp_neg (Real.log p), Real.exp_log hp0]
    field_simp
    simp only [M, S]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hsplit : ∑ p ∈ window h a c, (M : ℝ) * (Real.log p / p) *
        (Real.exp (-(Real.log p * x)) * Real.cos (Real.log p * u)) -
      h * Real.exp (-(l * x)) * Real.cos (l * u) =
      (M : ℝ) * ∑ p ∈ window h a c, Real.log p / p *
        (Real.exp (-(Real.log p * x)) * Real.cos (Real.log p * u) -
          Real.exp (-(l * x)) * Real.cos (l * u)) +
        ((M : ℝ) * S - h) * (Real.exp (-(l * x)) * Real.cos (l * u)) := by
    have hS' : S = ∑ p ∈ window h a c, Real.log p / p := rfl
    have e1 : ∑ p ∈ window h a c, (M : ℝ) * (Real.log p / p) *
        (Real.exp (-(Real.log p * x)) * Real.cos (Real.log p * u)) =
        M * ∑ p ∈ window h a c, Real.log p / p *
          (Real.exp (-(Real.log p * x)) * Real.cos (Real.log p * u)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
    have e2 : ∑ p ∈ window h a c, Real.log p / p *
        (Real.exp (-(Real.log p * x)) * Real.cos (Real.log p * u) -
          Real.exp (-(l * x)) * Real.cos (l * u)) =
        ∑ p ∈ window h a c, Real.log p / p *
          (Real.exp (-(Real.log p * x)) * Real.cos (Real.log p * u)) -
          S * (Real.exp (-(l * x)) * Real.cos (l * u)) := by
      rw [hS', Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [e1, e2]
    ring
  rw [hsplit]
  have hpart : |∑ p ∈ window h a c, Real.log p / p *
      (Real.exp (-(Real.log p * x)) * Real.cos (Real.log p * u) -
        Real.exp (-(l * x)) * Real.cos (l * u))| ≤
      S * (Real.exp (-(l * x)) * ((1 / ((c : ℝ) + 1) ^ 2) * (x + |u|))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp only [S, windowMass, Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hlo, -, hpr⟩ := mem_window hp
    have hlog := log_mem_window hp
    have hlp : 0 ≤ Real.log p / p := div_nonneg (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le))
      (Nat.cast_nonneg _)
    rw [abs_mul, abs_of_nonneg hlp]
    refine mul_le_mul_of_nonneg_left ((abs_mode_sub_le hx0.le hlog.1.le).trans ?_) hlp
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right (by linarith [hlog.2]) (by positivity)
  have hk2 : 0 < ((c : ℝ) + 1) ^ 2 := by positivity
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hφ : |Real.exp (-(l * x)) * Real.cos (l * u)| ≤ Real.exp (-(l * x)) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hM0, abs_mul]
  have h1 : (M : ℝ) * |∑ p ∈ window h a c, Real.log p / p *
      (Real.exp (-(Real.log p * x)) * Real.cos (Real.log p * u) -
        Real.exp (-(l * x)) * Real.cos (l * u))| ≤
      h * (Real.exp (-(l * x)) * ((1 / ((c : ℝ) + 1) ^ 2) * (x + |u|))) := by
    calc _ ≤ (M : ℝ) * (S * (Real.exp (-(l * x)) * ((1 / ((c : ℝ) + 1) ^ 2) * (x + |u|)))) :=
          mul_le_mul_of_nonneg_left hpart hM0
      _ = (M * S) * (Real.exp (-(l * x)) * ((1 / ((c : ℝ) + 1) ^ 2) * (x + |u|))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hM (by positivity)
  have h2 : |(M : ℝ) * S - h| * |Real.exp (-(l * x)) * Real.cos (l * u)| ≤
      (2 / ((c : ℝ) + 1) ^ 2) * Real.exp (-(l * x)) := by
    have habs : |(M : ℝ) * S - h| ≤ 2 / ((c : ℝ) + 1) ^ 2 := by
      rw [abs_le]; constructor <;> linarith
    exact mul_le_mul habs hφ (abs_nonneg _) (by positivity)
  have hu : x + |u| ≤ 1 + |u| := by linarith
  have hfin : h * (Real.exp (-(l * x)) * ((1 / ((c : ℝ) + 1) ^ 2) * (x + |u|))) +
      (2 / ((c : ℝ) + 1) ^ 2) * Real.exp (-(l * x)) ≤
      Real.exp |a| * (2 + h * (1 + |u|)) * (1 / ((c : ℝ) + 1) ^ 2) := by
    have e1 : h * (Real.exp (-(l * x)) * ((1 / ((c : ℝ) + 1) ^ 2) * (x + |u|))) +
        (2 / ((c : ℝ) + 1) ^ 2) * Real.exp (-(l * x)) =
        Real.exp (-(l * x)) * (2 + h * (x + |u|)) * (1 / ((c : ℝ) + 1) ^ 2) := by ring
    rw [e1]
    refine mul_le_mul_of_nonneg_right (mul_le_mul hE (by nlinarith) (by positivity)
      (Real.exp_pos _).le) (by positivity)
  linarith

/-- A sum over the fibre of the window index is the sum over the window. -/
theorem tsum_windowIndex_fiber (hh : 0 < h) (f : ℕ → ℝ)
    (hf : ∀ n, (∀ k, goodStart hh a ≤ k → n ∉ window h a k) → f n = 0) (c : ℕ) :
    ∑' b : (windowIndex hh a) ⁻¹' {c}, f b =
      if goodStart hh a ≤ c then ∑ p ∈ window h a c, f p else 0 := by
  classical
  have hstart : 1 ≤ goodStart hh a := le_max_left _ _
  rw [_root_.tsum_subtype]
  split_ifs with hc
  · have hset : (windowIndex hh a) ⁻¹' {c} = ↑(window h a c) := by
      ext n
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_coe]
      constructor
      · intro hn
        unfold windowIndex at hn
        split_ifs at hn with hex
        · have := Nat.find_spec hex
          rw [hn] at this
          exact this.2
        · omega
      · exact windowIndex_of_mem hh hc
    rw [hset, tsum_eq_sum (s := window h a c) fun n hn => Set.indicator_of_notMem hn _]
    exact Finset.sum_congr rfl fun n hn => Set.indicator_of_mem (Finset.mem_coe.mpr hn) _
  · refine (tsum_congr fun n => ?_).trans tsum_zero
    by_cases hn : n ∈ (windowIndex hh a) ⁻¹' {c}
    · rw [Set.indicator_of_mem hn]
      refine hf n fun k hk hnk => ?_
      have hidx := windowIndex_of_mem hh hk hnk
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hn
      omega
    · exact Set.indicator_of_notMem hn _

/-- **The integral datum has the progression divisor.** -/
theorem latticeRound_isBoundaryDivisor (hh : 0 < h) (a : ℝ) :
    IsBoundaryDivisor logFrequency (intWeight (latticeMult hh a)) (progressionDivisor h a) := by
  classical
  set m := latticeMult hh a
  set B := |a| + h
  have hB : 0 ≤ B := by positivity
  -- `m(minFac n) Λ(n) ≤ (4/h)(log n + B)² Λ(n)`.
  have hmin : ∀ x, ∀ n : ℕ, (m n.minFac : ℝ) * zetaBoundaryWeight x n ≤
      4 / h * (Real.log n + B) ^ 2 * zetaBoundaryWeight x n := by
    intro x n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [zetaBoundaryWeight]
    refine mul_le_mul_of_nonneg_right ((latticeMult_le hh _).trans ?_)
      (zetaBoundaryWeight_nonneg x n)
    have hf1 : (1 : ℝ) ≤ n.minFac := by exact_mod_cast (Nat.minFac_pos n)
    have hfn : (n.minFac : ℝ) ≤ n := by exact_mod_cast Nat.minFac_le hn
    have hl0 : 0 ≤ Real.log n.minFac := Real.log_nonneg hf1
    have hl : Real.log n.minFac ≤ Real.log n := Real.log_le_log (by linarith) hfn
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 2)
      (by positivity)
  have hdom : ∀ x, 0 < x → Summable fun n : ℕ => 4 / h * (Real.log n + B) ^ 2 *
      zetaBoundaryWeight x n := by
    intro x hx
    have h1 := RHTower.summable_vonMangoldt_logPow (σ := 1 + x) (by linarith) 2
    have h0 := summable_zetaBoundaryWeight hx
    refine Summable.of_nonneg_of_le (fun n => by
      have := zetaBoundaryWeight_nonneg x n; positivity) (fun n => ?_)
      ((h1.mul_left (8 / h)).add (h0.mul_left (8 / h * B ^ 2)))
    have hz := zetaBoundaryWeight_nonneg x n
    have hsq : (Real.log n + B) ^ 2 ≤ 2 * Real.log n ^ 2 + 2 * B ^ 2 := by
      nlinarith [sq_nonneg (Real.log n - B)]
    have e : zetaBoundaryWeight x n = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + x)) :=
      rfl
    calc 4 / h * (Real.log n + B) ^ 2 * zetaBoundaryWeight x n
        ≤ 4 / h * (2 * Real.log n ^ 2 + 2 * B ^ 2) * zetaBoundaryWeight x n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) hz
      _ = 8 / h * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + x)) *
            Real.log n ^ 2) + 8 / h * B ^ 2 * zetaBoundaryWeight x n := by rw [← e]; ring
  refine ⟨fun x _ n => mul_nonneg (Nat.cast_nonneg _) (zetaBoundaryWeight_nonneg x n),
    fun x hx => Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Nat.cast_nonneg _) (zetaBoundaryWeight_nonneg x n))
      (fun n => hmin x n) (hdom x hx), fun u => ?_⟩
  -- The bounds on the two defects.
  set BQ := 4 / h * (1 + B) ^ 2 * ∑' n : ℕ, (if n.Prime then 0 else
      (1 + Real.log n) ^ 2 * (ArithmeticFunction.vonMangoldt n : ℝ) / n)
  set bnd : ℕ → ℝ := fun c => (if c < goodStart hh a then h * Real.exp |a| else 0) +
      Real.exp |a| * (2 + h * (1 + |u|)) * (1 / ((c : ℝ) + 1) ^ 2)
  have hbnd : Summable bnd := by
    refine Summable.add ?_ (summable_inv_succ_sq.mul_left _)
    refine summable_of_ne_finset_zero (s := range (goodStart hh a)) fun c hc => ?_
    rw [Finset.mem_range] at hc
    rw [if_neg hc]
  set BP := ∑' c, bnd c
  have hdef : ∀ x, 0 < x → x ≤ 1 →
      |cosineTrace (intWeight m x) logFrequency u -
        cosineTrace (progressionWeight h a x) (progressionFrequency h a) u| ≤ BP + BQ := by
    intro x hx0 hx1
    set f : ℕ → ℝ := fun n => if n.Prime then
      (m n : ℝ) * zetaBoundaryWeight x n * Real.cos (logFrequency n * u) else 0
    set q : ℕ → ℝ := fun n => if n.Prime then 0 else
      (m n.minFac : ℝ) * zetaBoundaryWeight x n * Real.cos (logFrequency n * u)
    have hsplit : ∀ n, intWeight m x n * Real.cos (logFrequency n * u) = f n + q n := by
      intro n
      simp only [f, q, intWeight]
      split_ifs with hp
      · rw [hp.minFac_eq]; ring
      · ring
    have hcosB : ∀ n, |(m n.minFac : ℝ) * zetaBoundaryWeight x n * Real.cos (logFrequency n * u)| ≤
        4 / h * (Real.log n + B) ^ 2 * zetaBoundaryWeight x n := fun n => by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (zetaBoundaryWeight_nonneg x n))]
      exact (mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg _)
        (zetaBoundaryWeight_nonneg x n)) (Real.abs_cos_le_one _)).trans (hmin x n)
    have hfs : Summable f := Summable.of_norm_bounded (hdom x hx0) fun n => by
      simp only [f, Real.norm_eq_abs]
      split_ifs with hp
      · have := hcosB n; rwa [hp.minFac_eq] at this
      · simp only [abs_zero]; have := zetaBoundaryWeight_nonneg x n; positivity
    have hqs : Summable q := Summable.of_norm_bounded (hdom x hx0) fun n => by
      simp only [q, Real.norm_eq_abs]
      split_ifs with hp
      · simp only [abs_zero]; have := zetaBoundaryWeight_nonneg x n; positivity
      · exact hcosB n
    -- The prime-power defect.
    have hqB : |∑' n, q n| ≤ BQ := by
      have hQs := summable_nonprime_logSq
      have hle : ∀ n, |q n| ≤ 4 / h * (1 + B) ^ 2 * (if n.Prime then 0 else
          (1 + Real.log n) ^ 2 * (ArithmeticFunction.vonMangoldt n : ℝ) / n) := by
        intro n
        simp only [q]
        split_ifs with hp
        · simp
        · rcases Nat.eq_zero_or_pos n with rfl | hn
          · simp [zetaBoundaryWeight]
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn1
          refine (hcosB n).trans ?_
          have hz : zetaBoundaryWeight x n ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / n :=
            zetaBoundaryWeight_le_div hx0.le n
          have hsq : (Real.log n + B) ^ 2 ≤ (1 + B) ^ 2 * (1 + Real.log n) ^ 2 := by
            rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
          calc 4 / h * (Real.log n + B) ^ 2 * zetaBoundaryWeight x n
              ≤ 4 / h * ((1 + B) ^ 2 * (1 + Real.log n) ^ 2) *
                  ((ArithmeticFunction.vonMangoldt n : ℝ) / n) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hsq (by positivity)) hz
                  (zetaBoundaryWeight_nonneg x n) (by positivity)
            _ = 4 / h * (1 + B) ^ 2 * ((1 + Real.log n) ^ 2 *
                  (ArithmeticFunction.vonMangoldt n : ℝ) / n) := by ring
      have hqa : Summable fun n => |q n| :=
        Summable.of_nonneg_of_le (fun n => abs_nonneg _) hle (hQs.mul_left _)
      calc |∑' n, q n| = ‖∑' n, q n‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' n, ‖q n‖ := norm_tsum_le_tsum_norm (by simpa only [Real.norm_eq_abs] using hqa)
        _ = ∑' n, |q n| := by simp only [Real.norm_eq_abs]
        _ ≤ BQ := (Summable.tsum_le_tsum hle hqa (hQs.mul_left _)).trans_eq tsum_mul_left
    -- The prime part, window by window.
    have hfib := hfs.hasSum.tsum_fiberwise (windowIndex hh a)
    have hfvan : ∀ n, (∀ k, goodStart hh a ≤ k → n ∉ window h a k) → f n = 0 := by
      intro n hn
      simp only [f]
      split_ifs
      · rw [show (m n : ℝ) = 0 by simp [m, latticeMult_eq_zero hh hn]]; ring
      · rfl
    simp_rw [tsum_windowIndex_fiber hh f hfvan] at hfib
    set F : ℕ → ℝ := fun c => if goodStart hh a ≤ c then ∑ p ∈ window h a c, f p else 0
    set G : ℕ → ℝ := fun c => progressionWeight h a x c * Real.cos (progressionFrequency h a c * u)
    have hGs : Summable G := summable_cosineTrace_terms (progressionWeight_nonneg hh x)
      (hasSum_progressionWeight hh hx0).summable (progressionFrequency h a) u
    have hFG : ∀ c, |F c - G c| ≤ bnd c := by
      intro c
      simp only [F, G, bnd]
      have hb0 : 0 ≤ Real.exp |a| * (2 + h * (1 + |u|)) * (1 / ((c : ℝ) + 1) ^ 2) := by positivity
      split_ifs with hc hc'
      · omega
      · rw [zero_add]
        have hsum : ∑ p ∈ window h a c, f p = ∑ p ∈ window h a c, (m p : ℝ) *
            zetaBoundaryWeight x p * Real.cos (logFrequency p * u) :=
          Finset.sum_congr rfl fun p hp => by simp [f, (mem_window hp).2.2]
        rw [hsum]
        have := abs_window_sub_le hh hc hx0 hx1 u
        simpa [progressionWeight, progressionFrequency, winFreq] using this
      · rw [zero_sub, abs_neg]
        unfold progressionWeight
        rw [abs_mul, abs_mul, abs_of_pos hh, abs_of_pos (Real.exp_pos _)]
        have hE : Real.exp (-((h * c + a) * x)) ≤ Real.exp |a| := Real.exp_le_exp.mpr (by
          have : 0 ≤ h * (c : ℝ) * x := by positivity
          nlinarith [neg_abs_le a, le_abs_self a])
        have hcos := Real.abs_cos_le_one (progressionFrequency h a c * u)
        have : h * Real.exp (-((h * c + a) * x)) * |Real.cos (progressionFrequency h a c * u)| ≤
            h * Real.exp |a| :=
          calc _ ≤ h * Real.exp (-((h * c + a) * x)) * 1 :=
                mul_le_mul_of_nonneg_left hcos (by positivity)
            _ ≤ h * Real.exp |a| := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hE hh.le
        linarith
      · omega
    have hFs : Summable F := by
      refine Summable.of_norm_bounded (hbnd.add (hGs.abs)) fun c => ?_
      rw [Real.norm_eq_abs]
      have := hFG c
      have := abs_sub_abs_le_abs_sub (F c) (G c)
      linarith
    have hP : ∑' n, f n = ∑' c, F c := hfib.tsum_eq.symm
    have htrace : cosineTrace (intWeight m x) logFrequency u = ∑' n, f n + ∑' n, q n := by
      unfold cosineTrace
      rw [← Summable.tsum_add hfs hqs]
      exact tsum_congr hsplit
    have hfull : cosineTrace (progressionWeight h a x) (progressionFrequency h a) u = ∑' c, G c := rfl
    rw [htrace, hfull, hP]
    have hdiff : |∑' c, F c - ∑' c, G c| ≤ BP := by
      rw [← Summable.tsum_sub hFs hGs]
      have hfga : Summable fun c => |F c - G c| :=
        Summable.of_nonneg_of_le (fun c => abs_nonneg _) hFG hbnd
      calc |∑' c, (F c - G c)| = ‖∑' c, (F c - G c)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' c, ‖F c - G c‖ := norm_tsum_le_tsum_norm (by simpa only [Real.norm_eq_abs] using hfga)
        _ = ∑' c, |F c - G c| := by simp only [Real.norm_eq_abs]
        _ ≤ BP := Summable.tsum_le_tsum hFG hfga hbnd
    calc |∑' c, F c + ∑' n, q n - ∑' c, G c| ≤ |∑' c, F c - ∑' c, G c| + |∑' n, q n| := by
          rw [show ∑' c, F c + ∑' n, q n - ∑' c, G c = (∑' c, F c - ∑' c, G c) + ∑' n, q n by ring]
          exact abs_add_le _ _
      _ ≤ BP + BQ := add_le_add hdiff hqB
  -- Pass to the limit.
  have hprog := (progression_isBoundaryDivisor hh a).tendsto u
  have hzero : Tendsto (fun x : ℝ => x * (cosineTrace (intWeight m x) logFrequency u -
      cosineTrace (progressionWeight h a x) (progressionFrequency h a) u)) (𝓝[>] 0) (𝓝 0) := by
    have hlin : Tendsto (fun x : ℝ => x * (BP + BQ)) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (BP + BQ)).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlin
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hx.1]
    exact mul_le_mul_of_nonneg_left (hdef x hx.1 hx.2) hx.1.le
  have := hprog.add hzero
  rw [add_zero] at this
  refine this.congr' (Eventually.of_forall fun x => ?_)
  ring

open Classical in
/-- **The lattice of simple poles over the rational primes.** -/
theorem integral_lattice {h : ℝ} (hh : 0 < h) :
    ∃ mult : ℕ → ℕ, IsBoundaryDivisor logFrequency (intWeight mult)
      (fun u => if ∃ k : ℤ, u = k * (2 * Real.pi / h) then 1 else 0) := by
  classical
  refine ⟨latticeMult hh h, ?_⟩
  convert latticeRound_isBoundaryDivisor hh h using 1
  funext u
  unfold progressionDivisor
  split_ifs with hu
  · obtain ⟨k, rfl⟩ := hu
    have e : h * (k * (2 * Real.pi / h)) = 0 + (k : ℝ) * (2 * Real.pi) := by field_simp; ring
    rw [e, Real.cos_add_int_mul_two_pi, Real.cos_zero]
  · rfl

/-- **The alternating character over the rational primes.** A simple pole at `1`, zeros at
`1 + i(2k+1)π/h` and poles at `1 + 2ikπ/h`, from integer exponents at the rational primes. -/
theorem integral_alternating {h : ℝ} (hh : 0 < h) :
    ∃ mult : ℕ → ℕ, IsBoundaryDivisor logFrequency (intWeight mult) (progressionDivisor h (h / 2)) ∧
      (∀ k : ℤ, progressionDivisor h (h / 2) (k * (2 * Real.pi / h)) = (-1) ^ k.natAbs) :=
  ⟨latticeMult hh (h / 2), latticeRound_isBoundaryDivisor hh _, (alternating_isBoundaryDivisor hh).2.1⟩

end GaloisForLFunctions.MultiplicativePositivityGeometry
