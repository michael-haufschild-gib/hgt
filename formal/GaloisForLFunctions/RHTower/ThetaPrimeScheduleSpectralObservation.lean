import GaloisForLFunctions.RHTower.ThetaCofinalCurrentSignChanges
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# Prime schedules and the complex spectral observation of the cutoff commutator

For `s = σ + iτ` with `1/2 < σ < 1`, the spectral observation of the moving shell is
`M_{S,N}(s − 1) = (s−1) G(s−1) N^{s−1} [E_S(s) H_N(s) − 1]` whenever every prime `≤ N` lies in `S`.
By the prime number theorem (`θ(x) ~ x`) every multiplicative window `(x, Cx]` carries
`Σ p^{−σ} → ∞`; windows with `|τ| log p` within `π/3` of `2πk` (resp. `(2k+1)π`) make
`|1 − p^{−s}|² ≤ exp(−p^{−σ}/2)` (resp. `≥ 1 + p^{−σ}`).  Adding the primes of one late window to all
primes `≤ N` gives prime exhaustions with `M_{S_N^−,N}(s − 1) → 0` and `|M_{S_N^+,N}(s − 1)| → ∞`
when `τ ≠ 0`: cofinality alone fixes no complex spectral limit.  For the natural schedule the exact
renormalization `[M/((s−1)G N^{s−1}) + 1]/E_{S_N}(s) = H_N(s)` returns the zeta partial sum.
-/

open MeasureTheory Set Filter Topology Asymptotics

namespace RHTower

noncomputable section

/-! ## Prime supply in multiplicative windows -/

/-- The primes of the multiplicative window `(x, Cx]`. -/
def multiplicativePrimeWindow (x C : ℝ) : Finset ℕ := (Finset.Ioc ⌊x⌋₊ ⌊C * x⌋₊).filter Nat.Prime

theorem theta_sub_eq_sum_primeWindow {x C : ℝ} (hx : 0 ≤ x) (hC : 1 ≤ C) :
    Chebyshev.theta (C * x) - Chebyshev.theta x = ∑ p ∈ multiplicativePrimeWindow x C, Real.log p := by
  have hle : ⌊x⌋₊ ≤ ⌊C * x⌋₊ := Nat.floor_mono (by nlinarith)
  rw [Chebyshev.theta, Chebyshev.theta, multiplicativePrimeWindow, sub_eq_iff_eq_add, Finset.sum_filter,
    Finset.sum_filter, Finset.sum_filter, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hle, add_comm]

theorem mem_multiplicativePrimeWindow {x C : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) {p : ℕ} (hp : p ∈ multiplicativePrimeWindow x C) :
    p.Prime ∧ x < p ∧ (p : ℝ) ≤ C * x := by
  simp only [multiplicativePrimeWindow, Finset.mem_filter, Finset.mem_Ioc] at hp
  exact ⟨hp.2, (Nat.floor_lt hx).1 hp.1.1,
    (Nat.cast_le.2 hp.1.2).trans (Nat.floor_le (by positivity))⟩

theorem tendsto_rpow_div_log_atTop_of_pos {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ => x ^ r / Real.log x) atTop atTop := by
  have h := (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x / x ^ r := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact div_pos (Real.log_pos hx) (Real.rpow_pos_of_pos (by linarith) r)
  have h' : Tendsto (fun x : ℝ => Real.log x / x ^ r) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨h, hpos⟩
  refine (tendsto_inv_nhdsGT_zero.comp h').congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp [Function.comp]

/-- **Prime supply.**  For `0 < σ < 1` and `C > 1`, `Σ_{x < p ≤ Cx} p^{−σ} → ∞` as `x → ∞`. -/
theorem tendsto_sum_primeWindow_rpow_neg {σ C : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hC : 1 < C) :
    Tendsto (fun x : ℝ => ∑ p ∈ multiplicativePrimeWindow x C, (p : ℝ) ^ (-σ)) atTop atTop := by
  have hθ : Tendsto (fun y : ℝ => Chebyshev.theta y / y) atTop (𝓝 1) :=
    ((isEquivalent_iff_tendsto_one (by filter_upwards [eventually_gt_atTop 0] with y hy
      using hy.ne')).1 chebyshev_asymptotic).congr fun y => by simp
  have hθC : Tendsto (fun x : ℝ => (Chebyshev.theta (C * x) - Chebyshev.theta x) / x) atTop
      (𝓝 (C * 1 - 1)) := by
    have h1 := (hθ.comp (tendsto_id.const_mul_atTop (by linarith : (0:ℝ) < C))).const_mul C
    refine (h1.sub hθ).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp, id]
    field_simp
  have hev := hθC.eventually (lt_mem_nhds (show (C - 1) / 2 < C * 1 - 1 by linarith))
  have hmain := ((tendsto_rpow_div_log_atTop_of_pos (r := 1 - σ) (by linarith)).comp
    (tendsto_id.const_mul_atTop (by linarith : (0:ℝ) < C))).const_mul_atTop
      (show 0 < (C - 1) / (2 * C) by apply div_pos <;> linarith)
  refine tendsto_atTop_mono' atTop ?_ hmain
  filter_upwards [hev, eventually_ge_atTop 1] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hCx : 1 < C * x := by nlinarith
  have hlog : 0 < Real.log (C * x) := Real.log_pos hCx
  have hterm : ∀ p ∈ multiplicativePrimeWindow x C, (C * x) ^ (-σ) * (Real.log p / Real.log (C * x)) ≤
      (p : ℝ) ^ (-σ) := fun p hp => by
    obtain ⟨hpp, hxp, hpC⟩ := mem_multiplicativePrimeWindow hx0.le (by linarith) hp
    have hp0 : (0 : ℝ) < p := hx0.trans hxp
    have h1 : (C * x) ^ (-σ) ≤ (p : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos hp0 hpC (by linarith)
    have h2 : Real.log p / Real.log (C * x) ≤ 1 :=
      (div_le_one hlog).2 (Real.log_le_log hp0 hpC)
    have h3 : 0 ≤ Real.log p / Real.log (C * x) :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)) hlog.le
    calc (C * x) ^ (-σ) * (Real.log p / Real.log (C * x)) ≤ (C * x) ^ (-σ) * 1 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ _ := by rw [mul_one]; exact h1
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, ← Finset.sum_div, ← theta_sub_eq_sum_primeWindow hx0.le hC.le] at hsum
  refine le_trans ?_ hsum
  have hθx : (C - 1) / 2 * x ≤ Chebyshev.theta (C * x) - Chebyshev.theta x := by
    have := (le_div_iff₀ hx0).1 hx.le; linarith
  have hsplit : (C * x) ^ (1 - σ) = (C * x) * (C * x) ^ (-σ) := by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add (by positivity), Real.rpow_one]
  simp only [Function.comp, id]
  rw [hsplit]
  have hpow : 0 < (C * x) ^ (-σ) := Real.rpow_pos_of_pos (by positivity) _
  calc (C - 1) / (2 * C) * (C * x * (C * x) ^ (-σ) / Real.log (C * x))
      = (C * x) ^ (-σ) * ((C - 1) / 2 * x / Real.log (C * x)) := by field_simp
    _ ≤ (C * x) ^ (-σ) * ((Chebyshev.theta (C * x) - Chebyshev.theta x) / Real.log (C * x)) := by
      gcongr

/-! ## Euler factors in phase windows -/

theorem natCast_cpow_neg_eq_cexp {p : ℕ} (hp : 0 < p) (s : ℂ) :
    (p : ℂ) ^ (-s) = Complex.exp (-s * (Real.log p : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg _), mul_comm]

theorem normSq_one_sub_natCast_cpow {p : ℕ} (hp : 0 < p) (s : ℂ) :
    Complex.normSq (1 - (p : ℂ) ^ (-s)) =
      1 - 2 * ((p : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log p)) + ((p : ℝ) ^ (-s.re)) ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hre : ((p : ℂ) ^ (-s)).re = (p : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log p) := by
    rw [natCast_cpow_neg_eq_cexp hp, Complex.exp_re, Real.rpow_def_of_pos hpR]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, Complex.mul_im, Complex.neg_im]
    ring_nf
    rw [Real.cos_neg]
  have hns : Complex.normSq ((p : ℂ) ^ (-s)) = ((p : ℝ) ^ (-s.re)) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re]
  rw [Complex.normSq_sub, Complex.normSq_one, hns, one_mul, Complex.conj_re, hre]
  ring

theorem log_mem_of_mem_primeWindow {u w : ℝ} {p : ℕ}
    (hp : p ∈ multiplicativePrimeWindow (Real.exp u) (Real.exp w)) : u < Real.log p ∧ Real.log p ≤ u + w := by
  obtain ⟨-, h1, h2⟩ := mem_multiplicativePrimeWindow (Real.exp_pos u).le (Real.exp_pos w).le hp
  have hp0 : (0 : ℝ) < p := (Real.exp_pos u).trans h1
  refine ⟨by rw [← Real.log_exp u]; exact Real.log_lt_log (Real.exp_pos u) h1, ?_⟩
  have := Real.log_le_log hp0 h2
  rwa [← Real.exp_add, Real.log_exp, add_comm] at this

/-- In a window `|τ| log p ∈ (c − π/3, c + π/3]` with `c = 2πk`, `cos(τ log p) ≥ 1/2`; with
`c = (2k+1)π`, `cos(τ log p) ≤ −1/2`. -/
theorem cos_bounds_of_phase {θ : ℝ} (k : ℕ) (h1 : 2 * Real.pi * k - Real.pi / 3 < θ)
    (h2 : θ ≤ 2 * Real.pi * k + Real.pi / 3) : 1 / 2 ≤ Real.cos θ := by
  have hθ' : Real.cos θ = Real.cos |θ - k * (2 * Real.pi)| := by
    rw [Real.cos_abs, Real.cos_sub_nat_mul_two_pi]
  rw [hθ', ← Real.cos_pi_div_three]
  refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) ?_
  rw [abs_le]; constructor <;> linarith

theorem cos_bounds_of_antiphase {θ : ℝ} (k : ℕ)
    (h1 : (2 * k + 1) * Real.pi - Real.pi / 3 < θ) (h2 : θ ≤ (2 * k + 1) * Real.pi + Real.pi / 3) :
    Real.cos θ ≤ -(1 / 2) := by
  have h := cos_bounds_of_phase k (θ := θ - Real.pi) (by linarith) (by linarith)
  have : Real.cos θ = -Real.cos (θ - Real.pi) := by rw [Real.cos_sub_pi, neg_neg]
  linarith

theorem normSq_one_sub_le_exp {p : ℕ} (hp : 0 < p) {s : ℂ} (hcos : 1 / 2 ≤ Real.cos (s.im * Real.log p))
    (hsmall : (p : ℝ) ^ (-s.re) ≤ 1 / 2) :
    Complex.normSq (1 - (p : ℂ) ^ (-s)) ≤ Real.exp (-((p : ℝ) ^ (-s.re) / 2)) := by
  rw [normSq_one_sub_natCast_cpow hp]
  have ha : 0 ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := Real.add_one_le_exp (-((p : ℝ) ^ (-s.re) / 2))
  nlinarith

theorem one_add_le_normSq_one_sub {p : ℕ} (hp : 0 < p) {s : ℂ}
    (hcos : Real.cos (s.im * Real.log p) ≤ -(1 / 2)) :
    1 + (p : ℝ) ^ (-s.re) ≤ Complex.normSq (1 - (p : ℂ) ^ (-s)) := by
  rw [normSq_one_sub_natCast_cpow hp]
  have ha : 0 ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith [sq_nonneg ((p : ℝ) ^ (-s.re))]

/-- **Phase-selected prime supply.**  For `0 < σ < 1`, `τ ≠ 0` and all `M, L`, there is a finite set
of primes `p > M` with `p^{−σ} ≤ 1/2`, `Σ p^{−σ} ≥ L`, and `cos(τ log p) ≥ 1/2` (phase `0`) or
`cos(τ log p) ≤ −1/2` (phase `π`). -/
theorem exists_phase_prime_set {σ τ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hτ : τ ≠ 0) (b : Bool)
    (M L : ℝ) :
    ∃ F : Finset ℕ, (∀ p ∈ F, p.Prime ∧ M < p ∧ (p : ℝ) ^ (-σ) ≤ 1 / 2 ∧
      (if b then Real.cos (τ * Real.log p) ≤ -(1 / 2) else 1 / 2 ≤ Real.cos (τ * Real.log p))) ∧
      L ≤ ∑ p ∈ F, (p : ℝ) ^ (-σ) := by
  have hτa : 0 < |τ| := abs_pos.2 hτ
  set w : ℝ := 2 * Real.pi / (3 * |τ|)
  have hw : 0 < w := by positivity
  set c : ℕ → ℝ := fun k => 2 * Real.pi * k + (if b then Real.pi else 0)
  set u : ℕ → ℝ := fun k => (c k - Real.pi / 3) / |τ|
  have hu : Tendsto u atTop atTop := by
    refine Tendsto.atTop_div_const hτa (tendsto_atTop_add_const_right _ _ ?_)
    exact tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop
      (by positivity))
  have hx := Real.tendsto_exp_atTop.comp hu
  have hC1 : 1 < Real.exp w := by have := Real.add_one_lt_exp hw.ne'; linarith
  have hsum := (tendsto_sum_primeWindow_rpow_neg hσ0 hσ1 hC1).comp hx
  obtain ⟨k, hk1, hk2⟩ := ((hsum.eventually (eventually_ge_atTop L)).and
    (hx.eventually (eventually_ge_atTop (max M ((2 : ℝ) ^ (1 / σ)))))).exists
  simp only [Function.comp] at hk1 hk2
  refine ⟨multiplicativePrimeWindow (Real.exp (u k)) (Real.exp w), fun p hp => ?_, hk1⟩
  obtain ⟨hpp, hxp, -⟩ := mem_multiplicativePrimeWindow (Real.exp_pos _).le (Real.exp_pos _).le hp
  obtain ⟨hl1, hl2⟩ := log_mem_of_mem_primeWindow hp
  have hp0 : (0 : ℝ) < p := (Real.exp_pos _).trans hxp
  refine ⟨hpp, lt_of_le_of_lt ((le_max_left _ _).trans hk2) hxp, ?_, ?_⟩
  · have h2 : (0 : ℝ) < (2 : ℝ) ^ (1 / σ) := by positivity
    calc (p : ℝ) ^ (-σ) ≤ ((2 : ℝ) ^ (1 / σ)) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos h2 (((le_max_right _ _).trans hk2).trans hxp.le)
            (by linarith)
      _ = 1 / 2 := by
          rw [← Real.rpow_mul (by norm_num), show 1 / σ * -σ = -1 by field_simp, Real.rpow_neg_one]
          norm_num
  · have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hcos : Real.cos (τ * Real.log p) = Real.cos (|τ| * Real.log p) := by
      rw [← Real.cos_abs, abs_mul, abs_of_nonneg hlogp]
    have hθ1 : c k - Real.pi / 3 < |τ| * Real.log p := by
      have := mul_lt_mul_of_pos_left hl1 hτa
      simp only [u] at this; rwa [mul_div_cancel₀ _ hτa.ne'] at this
    have hθ2 : |τ| * Real.log p ≤ c k + Real.pi / 3 := by
      have := mul_le_mul_of_nonneg_left hl2 hτa.le
      simp only [u, w] at this
      rw [mul_add, mul_div_cancel₀ _ hτa.ne'] at this
      have e : |τ| * (2 * Real.pi / (3 * |τ|)) = 2 * Real.pi / 3 := by field_simp
      rw [e] at this; linarith
    rw [hcos]
    cases b with
    | false =>
      simp only [c, if_false, add_zero, Bool.false_eq_true] at hθ1 hθ2 ⊢
      exact cos_bounds_of_phase k hθ1 hθ2
    | true =>
      simp only [c, if_true] at hθ1 hθ2 ⊢
      exact cos_bounds_of_antiphase k (by linarith) (by linarith)

theorem normSq_finitePrimeEulerProduct_le_of_phase {F : Finset ℕ} {s : ℂ}
    (hF : ∀ p ∈ F, p.Prime ∧ (p : ℝ) ^ (-s.re) ≤ 1 / 2 ∧ 1 / 2 ≤ Real.cos (s.im * Real.log p)) :
    Complex.normSq (finitePrimeEulerProduct F s) ≤
      Real.exp (-(∑ p ∈ F, (p : ℝ) ^ (-s.re)) / 2) := by
  rw [finitePrimeEulerProduct, map_prod, show -(∑ p ∈ F, (p : ℝ) ^ (-s.re)) / 2 =
    ∑ p ∈ F, -((p : ℝ) ^ (-s.re) / 2) by
      rw [← Finset.sum_neg_distrib, Finset.sum_div]; exact Finset.sum_congr rfl fun p _ => by ring,
    Real.exp_sum]
  exact Finset.prod_le_prod (fun p _ => Complex.normSq_nonneg _) fun p hp =>
    normSq_one_sub_le_exp (hF p hp).1.pos (hF p hp).2.2 (hF p hp).2.1

theorem one_add_sum_le_normSq_finitePrimeEulerProduct {F : Finset ℕ} {s : ℂ}
    (hF : ∀ p ∈ F, p.Prime ∧ Real.cos (s.im * Real.log p) ≤ -(1 / 2)) :
    1 + ∑ p ∈ F, (p : ℝ) ^ (-s.re) ≤ Complex.normSq (finitePrimeEulerProduct F s) := by
  rw [finitePrimeEulerProduct, map_prod]
  refine (one_add_sum_le_prod_one_add F (fun p => (p : ℝ) ^ (-s.re))
    fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _).trans ?_
  exact Finset.prod_le_prod (fun p _ => by positivity) fun p hp =>
    one_add_le_normSq_one_sub (hF p hp).1.pos (hF p hp).2

theorem finitePrimeEulerProduct_ne_zero {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {s : ℂ}
    (hs : 0 < s.re) : finitePrimeEulerProduct S s ≠ 0 := by
  rw [finitePrimeEulerProduct, Finset.prod_ne_zero_iff]
  intro p hp h
  have h1 : (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have hn := congrArg norm h1
  rw [Complex.norm_natCast_cpow_of_pos (hS p hp).pos, norm_one, Complex.neg_re] at hn
  have := Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (hS p hp).one_lt : (1:ℝ) < p)
    (by linarith : -s.re < 0)
  linarith

/-- When every prime `≤ N` lies in `S`, the rough partial sum is `1`. -/
theorem roughHarmonicCutoff_eq_one {S : Finset ℕ} {N : ℕ} (hN : 1 ≤ N) (hSp : ∀ p ∈ S, p.Prime)
    (hS : ∀ p, p.Prime → p ≤ N → p ∈ S) (s : ℂ) : roughHarmonicCutoff S N s = 1 := by
  have hset : (Finset.Icc 1 N).filter (fun m => ∀ p ∈ S, ¬ p ∣ m) = {1} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_contra hm
      exact h3 m.minFac (hS _ (Nat.minFac_prime hm) ((Nat.minFac_le (by omega)).trans h2))
        (Nat.minFac_dvd m)
    · rintro rfl
      exact ⟨⟨le_rfl, hN⟩, fun p hp hdvd => (hSp p hp).one_lt.ne' (Nat.dvd_one.1 hdvd)⟩
  rw [roughHarmonicCutoff, hset, Finset.sum_singleton, Nat.cast_one, Complex.one_cpow]

/-! ## The spectral observation of prime schedules -/

theorem harmonicCutoff_sub_tendsto {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Tendsto (fun N : ℕ => harmonicCutoff N s - ((N : ℝ) : ℂ) ^ (1 - s) / (1 - s)) atTop
      (𝓝 (riemannZeta s)) := by
  have hne : s ≠ 1 := fun h => by rw [h] at hs1; simp at hs1
  refine (tendsto_sum_cpow_sub_pow hs0 hne).congr fun N => ?_
  simp [harmonicCutoff]

theorem tendsto_norm_harmonicCutoff {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Tendsto (fun N : ℕ => ‖harmonicCutoff N s‖) atTop atTop := by
  have hne : (1 : ℂ) - s ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hlead : Tendsto (fun N : ℕ => ‖((N : ℝ) : ℂ) ^ (1 - s) / (1 - s)‖) atTop atTop := by
    have h := (tendsto_rpow_atTop (by simp; linarith : 0 < (1 - s).re)).comp
      tendsto_natCast_atTop_atTop
    refine (h.atTop_div_const (norm_pos_iff.2 hne)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hN)]
    rfl
  have hrem := (harmonicCutoff_sub_tendsto hs0 hs1).norm
  refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right _ (-(‖riemannZeta s‖ + 1)) hlead)
  filter_upwards [hrem.eventually (gt_mem_nhds (lt_add_one ‖riemannZeta s‖))] with N hN
  have := norm_sub_norm_le (((N : ℝ) : ℂ) ^ (1 - s) / (1 - s)) (harmonicCutoff N s)
  rw [norm_sub_rev] at this
  linarith

/-- The complex spectral observation `M_{S,N}(z) = ∫ e^{zy} e^{(y−log N)/2} C_{S,N}(y − log N) dy`. -/
def commutatorSpectralObservation (S : Finset ℕ) (N : ℕ) (z : ℂ) : ℂ :=
  ∫ y : ℝ, Complex.exp (z * y) * (movingCommutatorDensity S N y : ℂ)

/-- **(3h), exact form.**  If every prime `≤ N` lies in `S`, then
`M_{S,N}(s − 1) = (s − 1) G(s − 1) N^{s−1} [E_S(s) H_N(s) − 1]`. -/
theorem commutatorSpectralObservation_eq {S : Finset ℕ} (hSp : ∀ p ∈ S, p.Prime) {N : ℕ}
    (hN : 1 ≤ N) (hS : ∀ p, p.Prime → p ≤ N → p ∈ S) {s : ℂ} (hs : -2 < s.re) :
    commutatorSpectralObservation S N (s - 1) =
      (s - 1) * commutatorGammaFactor (s - 1) * (N : ℂ) ^ (s - 1) *
        (finitePrimeEulerProduct S s * harmonicCutoff N s - 1) := by
  rw [commutatorSpectralObservation, integral_cexp_mul_movingCommutatorDensity S hSp hN
    (by simp; linarith), show 1 + (s - 1) = s by ring, roughHarmonicCutoff_eq_one hN hSp hS]

theorem primesLE_union_primeExhaustion (F : ℕ → Finset ℕ) (hF : ∀ N, ∀ p ∈ F N, p.Prime) :
    PrimeExhaustion fun N => (Nat.primesLE N) ∪ F N :=
  ⟨fun N p hp => by
    rcases Finset.mem_union.1 hp with h | h
    · exact Nat.prime_of_mem_primesLE h
    · exact hF N p h, fun p hp => by
    filter_upwards [eventually_ge_atTop p] with N hN
    exact Finset.mem_union_left _ (Nat.mem_primesLE.2 ⟨hN, hp⟩)⟩

theorem finitePrimeEulerProduct_union {S F : Finset ℕ} (h : Disjoint S F) (s : ℂ) :
    finitePrimeEulerProduct (S ∪ F) s = finitePrimeEulerProduct S s * finitePrimeEulerProduct F s := by
  rw [finitePrimeEulerProduct, Finset.prod_union h]; rfl

/-- **(3h) No schedule-independent spectral limit.**  Fix `s = σ + iτ` with `1/2 < σ < 1` and
`τ ≠ 0`.  There are prime exhaustions `S_N^−`, `S_N^+` (every prime `≤ N` together with finitely many
later primes of one phase class) with `M_{S_N^−,N}(s − 1) → 0` and `|M_{S_N^+,N}(s − 1)| → ∞`. -/
theorem exists_prime_schedules_spectral_observation {s : ℂ} (hσ1 : 1 / 2 < s.re) (hσ2 : s.re < 1)
    (hτ : s.im ≠ 0) :
    (∃ S : ℕ → Finset ℕ, PrimeExhaustion S ∧
      Tendsto (fun N => commutatorSpectralObservation (S N) N (s - 1)) atTop (𝓝 0)) ∧
    (∃ S : ℕ → Finset ℕ, PrimeExhaustion S ∧
      Tendsto (fun N => ‖commutatorSpectralObservation (S N) N (s - 1)‖) atTop atTop) := by
  have hσ0 : 0 < s.re := by linarith
  set E₀ : ℕ → ℂ := fun N => finitePrimeEulerProduct (Nat.primesLE N) s
  set B : ℕ → ℂ := fun N => harmonicCutoff N s
  set c : ℝ := ‖(s - 1) * commutatorGammaFactor (s - 1)‖
  have hs1 : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hc : 0 < c := norm_pos_iff.2 (mul_ne_zero hs1 (commutatorGammaFactor_ne_zero (by simp; linarith)))
  have hE₀ : ∀ N, E₀ N ≠ 0 := fun N =>
    finitePrimeEulerProduct_ne_zero (fun p hp => Nat.prime_of_mem_primesLE hp) hσ0
  have hdisj : ∀ N (F : Finset ℕ), (∀ p ∈ F, N < p) → Disjoint (Nat.primesLE N) F := fun N F hF =>
    Finset.disjoint_left.2 fun p hp hpF => by
      have := (Nat.mem_primesLE.1 hp).1; have := hF p hpF; omega
  have hnormN : ∀ N : ℕ, 1 ≤ N → ‖(N : ℂ) ^ (s - 1)‖ = (N : ℝ) ^ (s.re - 1) := fun N hN => by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.sub_re, Complex.one_re]
  constructor
  · -- the vanishing schedule
    have hF : ∀ N : ℕ, ∃ F : Finset ℕ, (∀ p ∈ F, p.Prime ∧ (N : ℝ) < p ∧ (p : ℝ) ^ (-s.re) ≤ 1 / 2 ∧
        1 / 2 ≤ Real.cos (s.im * Real.log p)) ∧
        4 * Real.log (N * (‖E₀ N‖ * ‖B N‖ + 1) + 1) ≤ ∑ p ∈ F, (p : ℝ) ^ (-s.re) := fun N => by
      obtain ⟨F, hF1, hF2⟩ := exists_phase_prime_set hσ0 hσ2 hτ false N
        (4 * Real.log (N * (‖E₀ N‖ * ‖B N‖ + 1) + 1))
      exact ⟨F, fun p hp => by simpa using hF1 p hp, hF2⟩
    choose F hFp hFs using hF
    refine ⟨fun N => Nat.primesLE N ∪ F N,
      primesLE_union_primeExhaustion F fun N p hp => (hFp N p hp).1, ?_⟩
    have hbound : ∀ N : ℕ, 1 ≤ N → ‖commutatorSpectralObservation (Nat.primesLE N ∪ F N) N (s - 1)‖ ≤
        c * (N : ℝ) ^ (s.re - 1) * (1 / N + 1) := fun N hN => by
      rw [commutatorSpectralObservation_eq (fun p hp => by
          rcases Finset.mem_union.1 hp with h | h
          · exact Nat.prime_of_mem_primesLE h
          · exact (hFp N p h).1) hN
        (fun p hp hpN => Finset.mem_union_left _ (Nat.mem_primesLE.2 ⟨hpN, hp⟩)) (by linarith),
        finitePrimeEulerProduct_union (hdisj N (F N) fun p hp => by exact_mod_cast (hFp N p hp).2.1)]
      rw [norm_mul, norm_mul, hnormN N hN]
      set K : ℝ := N * (‖E₀ N‖ * ‖B N‖ + 1) + 1
      have hK0 : (0:ℝ) ≤ N * (‖E₀ N‖ * ‖B N‖ + 1) := by positivity
      have hK : 1 ≤ K := by simp only [K]; linarith
      have hnorm := normSq_finitePrimeEulerProduct_le_of_phase (F := F N) (s := s)
        fun p hp => ⟨(hFp N p hp).1, (hFp N p hp).2.2.1, (hFp N p hp).2.2.2⟩
      have hexp : Real.exp (-(∑ p ∈ F N, (p : ℝ) ^ (-s.re)) / 2) ≤ (K ^ 2)⁻¹ := by
        rw [← Real.exp_log (by positivity : (0:ℝ) < (K ^ 2)⁻¹), Real.log_inv, Real.log_pow]
        apply Real.exp_le_exp.2
        have := hFs N; push_cast; linarith
      have hEF : ‖finitePrimeEulerProduct (F N) s‖ ≤ K⁻¹ := by
        rw [Complex.normSq_eq_norm_sq] at hnorm
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1
          (hnorm.trans (hexp.trans_eq (by rw [inv_pow])))
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      have hprod : ‖E₀ N * finitePrimeEulerProduct (F N) s * B N‖ ≤ 1 / N := by
        rw [norm_mul, norm_mul]
        have h1 : ‖E₀ N‖ * ‖finitePrimeEulerProduct (F N) s‖ * ‖B N‖ ≤ ‖E₀ N‖ * K⁻¹ * ‖B N‖ := by
          gcongr
        refine h1.trans ?_
        rw [show ‖E₀ N‖ * K⁻¹ * ‖B N‖ = ‖E₀ N‖ * ‖B N‖ / K by ring, div_le_div_iff₀ (by linarith) hNR]
        simp only [K]
        nlinarith [norm_nonneg (E₀ N), norm_nonneg (B N), mul_nonneg (norm_nonneg (E₀ N)) (norm_nonneg (B N))]
      have hsub : ‖E₀ N * finitePrimeEulerProduct (F N) s * B N - 1‖ ≤ 1 / N + 1 :=
        (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
      exact mul_le_mul_of_nonneg_left hsub (by positivity)
    have hlim : Tendsto (fun N : ℕ => c * (N : ℝ) ^ (s.re - 1) * (1 / N + 1)) atTop (𝓝 0) := by
      have h1 := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - s.re)).comp tendsto_natCast_atTop_atTop
      have h2 := (h1.const_mul c).mul (tendsto_one_div_atTop_nhds_zero_nat.add
        (tendsto_const_nhds (x := (1 : ℝ))))
      simp only [mul_zero, zero_mul] at h2
      refine h2.congr fun N => ?_
      simp only [Function.comp, neg_sub]
    have hev : ∀ᶠ N : ℕ in atTop, ‖commutatorSpectralObservation (Nat.primesLE N ∪ F N) N (s - 1)‖ ≤
        c * (N : ℝ) ^ (s.re - 1) * (1 / N + 1) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact hbound N hN
    exact squeeze_zero_norm' hev hlim
  · -- the diverging schedule
    set R : ℕ → ℝ := fun N => (N : ℝ) ^ (2 - s.re) / (‖E₀ N‖ * ‖B N‖ + (if ‖B N‖ = 0 then 1 else 0))
    have hF : ∀ N : ℕ, ∃ F : Finset ℕ, (∀ p ∈ F, p.Prime ∧ (N : ℝ) < p ∧
        Real.cos (s.im * Real.log p) ≤ -(1 / 2)) ∧ R N ^ 2 ≤ ∑ p ∈ F, (p : ℝ) ^ (-s.re) := fun N => by
      obtain ⟨F, hF1, hF2⟩ := exists_phase_prime_set hσ0 hσ2 hτ true N (R N ^ 2)
      refine ⟨F, fun p hp => ⟨(hF1 p hp).1, (hF1 p hp).2.1, ?_⟩, hF2⟩
      have := (hF1 p hp).2.2.2
      simpa using this
    choose F hFp hFs using hF
    refine ⟨fun N => Nat.primesLE N ∪ F N,
      primesLE_union_primeExhaustion F fun N p hp => (hFp N p hp).1, ?_⟩
    have hBpos : ∀ᶠ N : ℕ in atTop, 1 ≤ ‖B N‖ :=
      (tendsto_norm_harmonicCutoff hσ0 hσ2).eventually (eventually_ge_atTop 1)
    have hbound : ∀ N : ℕ, 1 ≤ N → 1 ≤ ‖B N‖ →
        c * ((N : ℝ) - (N : ℝ) ^ (s.re - 1)) ≤
          ‖commutatorSpectralObservation (Nat.primesLE N ∪ F N) N (s - 1)‖ := fun N hN hB => by
      rw [commutatorSpectralObservation_eq (fun p hp => by
          rcases Finset.mem_union.1 hp with h | h
          · exact Nat.prime_of_mem_primesLE h
          · exact (hFp N p h).1) hN
        (fun p hp hpN => Finset.mem_union_left _ (Nat.mem_primesLE.2 ⟨hpN, hp⟩)) (by linarith),
        finitePrimeEulerProduct_union (hdisj N (F N) fun p hp => by exact_mod_cast (hFp N p hp).2.1)]
      rw [norm_mul, norm_mul, hnormN N hN]
      have hNR : (0 : ℝ) < N := by exact_mod_cast hN
      have hE0 : 0 < ‖E₀ N‖ := norm_pos_iff.2 (hE₀ N)
      have hRN : R N = (N : ℝ) ^ (2 - s.re) / (‖E₀ N‖ * ‖B N‖) := by
        simp only [R, if_neg (show ¬ ‖B N‖ = 0 by linarith), add_zero]
      have hnorm := one_add_sum_le_normSq_finitePrimeEulerProduct (F := F N) (s := s)
        fun p hp => ⟨(hFp N p hp).1, (hFp N p hp).2.2⟩
      rw [Complex.normSq_eq_norm_sq] at hnorm
      have hEF : R N ≤ ‖finitePrimeEulerProduct (F N) s‖ := by
        have hR0 : 0 ≤ R N := by rw [hRN]; positivity
        exact (pow_le_pow_iff_left₀ hR0 (norm_nonneg _) two_ne_zero).1 (by linarith [hFs N])
      have hprod : (N : ℝ) ^ (2 - s.re) ≤ ‖E₀ N * finitePrimeEulerProduct (F N) s * B N‖ := by
        rw [norm_mul, norm_mul]
        calc (N : ℝ) ^ (2 - s.re) = ‖E₀ N‖ * R N * ‖B N‖ := by
              rw [hRN]; field_simp
          _ ≤ _ := by gcongr
      have hsub : (N : ℝ) ^ (2 - s.re) - 1 ≤ ‖E₀ N * finitePrimeEulerProduct (F N) s * B N - 1‖ := by
        have := norm_sub_norm_le (E₀ N * finitePrimeEulerProduct (F N) s * B N) 1
        rw [norm_one] at this; linarith
      have hsplit : (N : ℝ) ^ (s.re - 1) * ((N : ℝ) ^ (2 - s.re) - 1) = N - (N : ℝ) ^ (s.re - 1) := by
        rw [mul_sub, ← Real.rpow_add hNR, show s.re - 1 + (2 - s.re) = 1 by ring, Real.rpow_one, mul_one]
      rw [show c * ((N : ℝ) - (N : ℝ) ^ (s.re - 1)) =
        c * (N : ℝ) ^ (s.re - 1) * ((N : ℝ) ^ (2 - s.re) - 1) by rw [mul_assoc, hsplit]]
      exact mul_le_mul_of_nonneg_left hsub (by positivity)
    have hlim : Tendsto (fun N : ℕ => c * ((N : ℝ) - (N : ℝ) ^ (s.re - 1))) atTop atTop := by
      have h : Tendsto (fun N : ℕ => (N : ℝ) - 1) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      refine Tendsto.const_mul_atTop hc (tendsto_atTop_mono' atTop ?_ h)
      filter_upwards [eventually_ge_atTop 1] with N hN
      have : (N : ℝ) ^ (s.re - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by linarith)
      linarith
    refine tendsto_atTop_mono' atTop ?_ hlim
    filter_upwards [eventually_ge_atTop 1, hBpos] with N hN hB
    exact hbound N hN hB

/-- **(3k) The exact but nonproductive renormalization.**  For the natural schedule
`S_N = {p ≤ N}`, `[M/((s−1)G(s−1)N^{s−1}) + 1]/E_{S_N}(s) = H_N(s)`, and subtracting
`N^{1−s}/(1−s)` recovers `ζ(s)`. -/
theorem natural_schedule_renormalization {s : ℂ} (hσ0 : 0 < s.re) (hσ1 : s.re < 1) {N : ℕ}
    (hN : 1 ≤ N) :
    (commutatorSpectralObservation (Nat.primesLE N) N (s - 1) /
        ((s - 1) * commutatorGammaFactor (s - 1) * (N : ℂ) ^ (s - 1)) + 1) /
      finitePrimeEulerProduct (Nat.primesLE N) s = harmonicCutoff N s := by
  have hs1 : s - 1 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have hG := commutatorGammaFactor_ne_zero (z := s - 1) (by simp; linarith)
  have hNc : (N : ℂ) ^ (s - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => by
      have := h.1; norm_cast at this; omega
  have hE := finitePrimeEulerProduct_ne_zero (S := Nat.primesLE N)
    (fun p hp => Nat.prime_of_mem_primesLE hp) hσ0
  rw [commutatorSpectralObservation_eq (fun p hp => Nat.prime_of_mem_primesLE hp) hN
    (fun p hp hpN => Nat.mem_primesLE.2 ⟨hpN, hp⟩) (by linarith)]
  field_simp
  ring

theorem natural_schedule_zeta_limit {s : ℂ} (hσ0 : 0 < s.re) (hσ1 : s.re < 1) :
    Tendsto (fun N : ℕ => harmonicCutoff N s - ((N : ℝ) : ℂ) ^ (1 - s) / (1 - s)) atTop
      (𝓝 (riemannZeta s)) := harmonicCutoff_sub_tendsto hσ0 hσ1

end

end RHTower
