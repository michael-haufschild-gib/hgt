import GaloisForLFunctions.RHTower.Suzuki.SuzukiPacketCoefficientSeries
import GaloisForLFunctions.RHTower.MFreeLadder
import GaloisForLFunctions.RHTower.WoldEulerActivationHolonomy
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# The Euler activation square

Activating prime support by the weight `a_h(n) = ∏_{p ∣ n} (1 - p^{-h})` and truncating the
maximal prime exponent at `m` gives a two-parameter Dirichlet series whose Euler product is
`∏_p (1 + (1 - p^{-h}) ∑_{k ≤ m} p^{-ks})`.  Its four boundary faces are the constant `1` at zero
activation, the zeta ratio `ζ(s)/ζ(s+h)` at infinite depth, the power-free ratio
`ζ(s)/ζ((m+1)s)` at full activation, and `ζ(s)` at the corner, in either order.
-/

open Complex Filter Topology ArithmeticFunction
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The activation coefficient -/

/-- The activation coefficient `a_h(n) = ∏_{p ∣ n} (1 - p^{-h})` of `(1)`. -/
def activationFactor (h : ℝ) : ArithmeticFunction ℂ := suzukiRadicalFactor (h / 2)

theorem activationFactor_apply {h : ℝ} {n : ℕ} (hn : n ≠ 0) :
    activationFactor h n = ∏ p ∈ n.primeFactors, (1 - (p : ℂ) ^ (-(h : ℂ))) := by
  rw [activationFactor, suzukiRadicalFactor_apply _ hn]
  refine Finset.prod_congr rfl fun p _ => ?_
  congr 2
  push_cast
  ring

theorem isMultiplicative_activationFactor (h : ℝ) : (activationFactor h).IsMultiplicative := by
  rw [activationFactor, suzukiRadicalFactor, doubleShiftedMoebius]
  exact (isMultiplicative_zeta.natCast).mul
    (isMultiplicative_dirichletShift (isMultiplicative_moebius.intCast))

theorem activationFactor_prime_pow {h : ℝ} {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    activationFactor h (p ^ k) = 1 - (p : ℂ) ^ (-(h : ℂ)) := by
  rw [activationFactor_apply (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_prime_pow hk hp,
    Finset.prod_singleton]

/-- For a nonnegative activation parameter the local factors are real and lie in `[0, 1]`. -/
theorem primeCpow_neg_ofReal_mem {h : ℝ} (hh : 0 ≤ h) {p : ℕ} (hp : p.Prime) :
    (p : ℂ) ^ (-(h : ℂ)) = (((p : ℝ) ^ (-h) : ℝ) : ℂ) ∧ 0 < (p : ℝ) ^ (-h) ∧
      (p : ℝ) ^ (-h) ≤ 1 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  refine ⟨?_, Real.rpow_pos_of_pos hp0 _, ?_⟩
  · rw [Complex.ofReal_cpow hp0.le]
    push_cast
    ring
  · exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)

theorem norm_one_sub_primeCpow_neg_le_one {h : ℝ} (hh : 0 ≤ h) {p : ℕ} (hp : p.Prime) :
    ‖1 - (p : ℂ) ^ (-(h : ℂ))‖ ≤ 1 := by
  obtain ⟨hcast, hpos, hle⟩ := primeCpow_neg_ofReal_mem hh hp
  rw [hcast, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_le]
  constructor <;> linarith

theorem norm_activationFactor_le_one {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    ‖activationFactor h n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [activationFactor_apply hn, norm_prod]
    refine Finset.prod_le_one (fun p _ => norm_nonneg _) fun p hp => ?_
    exact norm_one_sub_primeCpow_neg_le_one hh (Nat.prime_of_mem_primeFactors hp)

/-! ## The depth-truncated activation stream -/

/-- The depth-`m` activation coefficient of `(3)`: activation restricted to integers whose maximal
prime exponent is at most `m`. -/
def activationDepthFactor (h : ℝ) (m : ℕ) : ArithmeticFunction ℂ :=
  pmul (((mFreeIndicator (m + 1) : ArithmeticFunction ℤ) : ArithmeticFunction ℂ))
    (activationFactor h)

theorem isMultiplicative_activationDepthFactor (h : ℝ) (m : ℕ) :
    (activationDepthFactor h m).IsMultiplicative :=
  ((isMultiplicative_mFreeIndicator (Nat.succ_ne_zero m)).intCast).pmul
    (isMultiplicative_activationFactor h)

open scoped Classical in
theorem activationDepthFactor_apply (h : ℝ) (m : ℕ) (n : ℕ) :
    activationDepthFactor h m n =
      if MFree (m + 1) n then activationFactor h n else 0 := by
  rw [activationDepthFactor, pmul_apply, intCoe_apply, mFreeIndicator_apply]
  split_ifs <;> simp

theorem norm_activationDepthFactor_le_one {h : ℝ} (hh : 0 ≤ h) (m n : ℕ) :
    ‖activationDepthFactor h m n‖ ≤ 1 := by
  classical
  rw [activationDepthFactor_apply]
  split_ifs with hfree
  · exact norm_activationFactor_le_one hh n
  · simp

/-- The `n^{-s}`-weighted depth-`m` activation stream. -/
def activationCpow (h : ℝ) (m : ℕ) (s : ℂ) : ArithmeticFunction ℂ :=
  GaloisForLFunctions.HTGeometry.dirichletShift s (activationDepthFactor h m)

/-- The depth-`m` activation series `𝒵_m(h,s)` of `(3)`. -/
def activationSeries (h : ℝ) (m : ℕ) (s : ℂ) : ℂ :=
  LSeries (fun n => activationDepthFactor h m n) s

theorem tsum_activationCpow (h : ℝ) (m : ℕ) (s : ℂ) :
    ∑' n : ℕ, activationCpow h m s n = activationSeries h m s := by
  rw [activationSeries, LSeries]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [activationCpow, LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, activationCpow,
      GaloisForLFunctions.HTGeometry.dirichletShift_apply,
      GaloisForLFunctions.HTGeometry.cpowWeight]
    rw [div_eq_mul_inv, mul_comm]
    congr 1
    rw [← Complex.cpow_neg]

theorem isMultiplicative_activationCpow (h : ℝ) (m : ℕ) (s : ℂ) :
    (activationCpow h m s).IsMultiplicative :=
  isMultiplicative_dirichletShift (isMultiplicative_activationDepthFactor h m)

theorem summable_norm_activationCpow {h : ℝ} (hh : 0 ≤ h) (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => ‖activationCpow h m s n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (Real.summable_one_div_nat_rpow.mpr hs)
  have hnn : (0 : ℝ) ≤ 1 / ((n : ℝ)) ^ s.re :=
    div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [activationCpow] using hnn
  · rw [activationCpow, GaloisForLFunctions.HTGeometry.dirichletShift_apply,
      GaloisForLFunctions.HTGeometry.cpowWeight, norm_mul,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), neg_re,
      Real.rpow_neg (Nat.cast_nonneg n), one_div]
    have hle := norm_activationDepthFactor_le_one hh m n
    have hpos : (0 : ℝ) ≤ ((n : ℝ) ^ s.re)⁻¹ := by positivity
    nlinarith [norm_nonneg (activationDepthFactor h m n)]

/-! ## The Euler activation square -/

theorem range_succ_eq_insert_Icc (m : ℕ) : Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
  ext k
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
  omega

theorem activationCpow_prime_pow {h : ℝ} (m : ℕ) (s : ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    activationCpow h m s (p ^ k) =
      if k = 0 then 1
      else if k ≤ m then ((p : ℂ) ^ (-s)) ^ k * (1 - (p : ℂ) ^ (-(h : ℂ))) else 0 := by
  classical
  rw [activationCpow, GaloisForLFunctions.HTGeometry.dirichletShift_apply,
    GaloisForLFunctions.HTGeometry.cpowWeight, activationDepthFactor_apply]
  have hweight : ((p ^ k : ℕ) : ℂ) ^ (-s) = ((p : ℂ) ^ (-s)) ^ k := natCast_pow_cpow p k (-s)
  rcases eq_or_ne k 0 with rfl | hk
  · rw [if_pos rfl]
    simp only [pow_zero, Nat.cast_one, Complex.one_cpow, one_mul,
      if_pos (mFree_one (Nat.succ_ne_zero m))]
    exact (isMultiplicative_activationFactor h).map_one
  · rw [if_neg hk, hweight]
    by_cases hkm : k ≤ m
    · rw [if_pos hkm, if_pos, activationFactor_prime_pow hp hk]
      intro q hq hdvd
      have hqp : q = p := by
        have := (Nat.prime_dvd_prime_iff_eq hq hp).mp
          (hq.dvd_of_dvd_pow (dvd_trans (dvd_pow_self q (Nat.succ_ne_zero m)) hdvd))
        exact this
      subst hqp
      have hle := (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp hdvd
      omega
    · rw [if_neg hkm, if_neg, mul_zero]
      intro hfree
      exact hkm (by
        by_contra hcon
        exact hfree p hp (pow_dvd_pow p (by omega)))

theorem tsum_activationCpow_prime_pow (h : ℝ) (m : ℕ) (s : ℂ) (p : Nat.Primes) :
    ∑' k : ℕ, activationCpow h m s ((p : ℕ) ^ k)
      = 1 + (1 - ((p : ℕ) : ℂ) ^ (-(h : ℂ))) *
          ∑ k ∈ Finset.Icc 1 m, (((p : ℕ) : ℂ) ^ (-s)) ^ k := by
  classical
  have hzero : ∀ k ∉ Finset.range (m + 1), activationCpow h m s ((p : ℕ) ^ k) = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [activationCpow_prime_pow m s p.prop k, if_neg (by omega), if_neg (by omega)]
  rw [tsum_eq_sum hzero, range_succ_eq_insert_Icc, Finset.sum_insert (by simp)]
  rw [activationCpow_prime_pow m s p.prop 0, if_pos rfl]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  rw [activationCpow_prime_pow m s p.prop k, if_neg (by omega), if_pos hk.2]
  ring

/-- **The Euler activation square `(4)`.**  On the Euler half-plane the depth-`m` activation series
is the Euler product of its local activation factors. -/
theorem activationSeries_eq_tprod {h : ℝ} (hh : 0 ≤ h) (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    activationSeries h m s
      = ∏' p : Nat.Primes,
          (1 + (1 - ((p : ℕ) : ℂ) ^ (-(h : ℂ))) *
            ∑ k ∈ Finset.Icc 1 m, (((p : ℕ) : ℂ) ^ (-s)) ^ k) := by
  rw [← tsum_activationCpow h m s,
    ← (isMultiplicative_activationCpow h m s).eulerProduct_tprod
      (summable_norm_activationCpow hh m hs)]
  exact tprod_congr fun p => tsum_activationCpow_prime_pow h m s p

/-! ## The zero-activation face -/

theorem activationFactor_zero_eq_zero {n : ℕ} (hn : 1 < n) : activationFactor 0 n = 0 := by
  have hn0 : n ≠ 0 := by omega
  rw [activationFactor_apply hn0]
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hn
  refine Finset.prod_eq_zero hp ?_
  norm_num

/-- **The zero-activation face of `(5)`.**  Without activation only the empty prime support
survives, so the depth-`m` activation series is the constant one. -/
theorem activationSeries_zero_activation (m : ℕ) (s : ℂ) : activationSeries 0 m s = 1 := by
  classical
  rw [activationSeries, LSeries, tsum_eq_single 1]
  · rw [LSeries.term_of_ne_zero one_ne_zero, activationDepthFactor_apply,
      if_pos (mFree_one (Nat.succ_ne_zero m))]
    simpa using (isMultiplicative_activationFactor 0).map_one
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · rw [LSeries.term_of_ne_zero hn0, activationDepthFactor_apply]
      have hlt : 1 < n := by
        rcases Nat.lt_or_ge n 2 with h | h
        · interval_cases n <;> simp_all
        · omega
      rw [activationFactor_zero_eq_zero hlt]
      simp

/-! ## The infinite-depth face -/

theorem LSeries_activationFactor {h : ℝ} (hh : 0 ≤ h) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => activationFactor h n) s = riemannZeta s / riemannZeta (s + (h : ℂ)) := by
  have hα : ((h / 2 : ℝ) : ℂ) + ((h / 2 : ℝ) : ℂ) = (h : ℂ) := by
    push_cast
    ring
  have hsre : 1 < (s + ((h / 2 : ℝ) : ℂ) - ((h / 2 : ℝ) : ℂ)).re := by
    simpa using hs
  have hsre2 : 1 < (s + ((h / 2 : ℝ) : ℂ) + ((h / 2 : ℝ) : ℂ)).re := by
    have : (s + ((h / 2 : ℝ) : ℂ) + ((h / 2 : ℝ) : ℂ)).re = s.re + h := by
      simp only [Complex.add_re, Complex.ofReal_re]
      ring
    rw [this]
    linarith
  have hmain := LSeries_suzukiShiftedCoefficient (h / 2) hsre hsre2
  have hcoeff : LSeries (fun n => ((suzukiShiftedCoefficient (h / 2) n : ℝ) : ℂ))
      (s + ((h / 2 : ℝ) : ℂ))
      = LSeries (fun n => suzukiCoeffAF (h / 2) n) (s + ((h / 2 : ℝ) : ℂ)) :=
    LSeries_congr (fun {n} hn => (suzukiCoeffAF_apply (h / 2) hn).symm) _
  have hshift : LSeries (fun n => suzukiCoeffAF (h / 2) n) (s + ((h / 2 : ℝ) : ℂ))
      = LSeries (fun n => activationFactor h n) s := by
    rw [suzukiCoeffAF, GaloisForLFunctions.HTGeometry.LSeries_dirichletShift]
    have harg : s + ((h / 2 : ℝ) : ℂ) + -((h / 2 : ℝ) : ℂ) = s := by ring
    rw [harg, activationFactor]
  have h1 : s + ((h / 2 : ℝ) : ℂ) - ((h / 2 : ℝ) : ℂ) = s := by ring
  have h2 : s + ((h / 2 : ℝ) : ℂ) + ((h / 2 : ℝ) : ℂ) = s + (h : ℂ) := by
    push_cast
    ring
  rw [← hshift, ← hcoeff, hmain, h1, h2]

theorem mFree_succ_of_le_self {m n : ℕ} (hn : n ≠ 0) (hnm : n ≤ m) : MFree (m + 1) n := by
  intro p hp hdvd
  have h1 : p ^ (m + 1) ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have h2 : 2 ^ (m + 1) ≤ p ^ (m + 1) := Nat.pow_le_pow_left hp.two_le _
  have h3 : n < 2 ^ n := Nat.lt_two_pow_self
  have h4 : (2 : ℕ) ^ n ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem norm_term_activationDepthFactor_le {h : ℝ} (hh : 0 ≤ h) (m : ℕ) (s : ℂ) (n : ℕ) :
    ‖LSeries.term (fun k => activationDepthFactor h m k) s n‖ ≤ 1 / (n : ℝ) ^ s.re := by
  have hnn : (0 : ℝ) ≤ 1 / ((n : ℝ)) ^ s.re :=
    div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using hnn
  · have hpos : (0 : ℝ) < (n : ℝ) ^ s.re :=
      Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
    rw [LSeries.term_of_ne_zero hn, norm_div,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    gcongr
    exact norm_activationDepthFactor_le_one hh m n

/-- **The infinite-depth face of `(5)`.**  For every fixed activation the depth-truncated series
converges to the zeta ratio. -/
theorem tendsto_activationSeries_depth {h : ℝ} (hh : 0 ≤ h) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun m : ℕ => activationSeries h m s) atTop
      (𝓝 (riemannZeta s / riemannZeta (s + (h : ℂ)))) := by
  classical
  have hlim : ∀ n : ℕ,
      Tendsto (fun m : ℕ => LSeries.term (fun k => activationDepthFactor h m k) s n) atTop
        (𝓝 (LSeries.term (fun k => activationFactor h k) s n)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_ge_atTop n] with m hm
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, activationDepthFactor_apply,
        if_pos (mFree_succ_of_le_self hn hm)]
  have hbound : ∀ᶠ m : ℕ in atTop, ∀ n : ℕ,
      ‖LSeries.term (fun k => activationDepthFactor h m k) s n‖ ≤ 1 / (n : ℝ) ^ s.re :=
    Filter.Eventually.of_forall fun m n => norm_term_activationDepthFactor_le hh m s n
  have hmain :=
    tendsto_tsum_of_dominated_convergence (Real.summable_one_div_nat_rpow.mpr hs) hlim hbound
  rw [← LSeries_activationFactor hh hs]
  exact hmain

/-! ## The full-activation face -/

theorem tendsto_primeCpow_neg_atTop {p : ℕ} (hp : 1 < p) :
    Tendsto (fun h : ℝ => (p : ℂ) ^ (-(h : ℂ))) atTop (𝓝 0) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hcast : ∀ h : ℝ, (p : ℂ) ^ (-(h : ℂ)) = (((p : ℝ) ^ (-h) : ℝ) : ℂ) := by
    intro h
    rw [Complex.ofReal_cpow hp0.le]
    push_cast
    ring
  have hlogpos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hreal : Tendsto (fun h : ℝ => ((p : ℝ) ^ (-h))) atTop (𝓝 0) := by
    have hrw : ∀ h : ℝ, (p : ℝ) ^ (-h) = Real.exp (Real.log p * (-h)) := fun h =>
      Real.rpow_def_of_pos hp0 _
    rw [tendsto_congr hrw]
    refine Real.tendsto_exp_atBot.comp ?_
    exact Filter.Tendsto.const_mul_atBot hlogpos tendsto_neg_atTop_atBot
  have hcomp : Tendsto (fun h : ℝ => (((p : ℝ) ^ (-h) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp hreal
  rw [tendsto_congr hcast]
  simpa using hcomp

theorem tendsto_activationFactor_atTop {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun h : ℝ => activationFactor h n) atTop (𝓝 1) := by
  have hrw : ∀ h : ℝ, activationFactor h n
      = ∏ p ∈ n.primeFactors, (1 - (p : ℂ) ^ (-(h : ℂ))) := fun h => activationFactor_apply hn
  rw [tendsto_congr hrw]
  have hfac : ∀ p ∈ n.primeFactors,
      Tendsto (fun h : ℝ => 1 - (p : ℂ) ^ (-(h : ℂ))) atTop (𝓝 1) := by
    intro p hp
    have := tendsto_primeCpow_neg_atTop (Nat.prime_of_mem_primeFactors hp).one_lt
    simpa using tendsto_const_nhds.sub this
  simpa using tendsto_finsetProd n.primeFactors hfac

/-- **The full-activation face of `(5)`.**  At infinite activation the depth-`m` series is the
power-free zeta ratio. -/
theorem tendsto_activationSeries_activation (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun h : ℝ => activationSeries h m s) atTop
      (𝓝 (riemannZeta s / riemannZeta (((m : ℂ) + 1) * s))) := by
  classical
  have hlim : ∀ n : ℕ,
      Tendsto (fun h : ℝ => LSeries.term (fun k => activationDepthFactor h m k) s n) atTop
        (𝓝 (LSeries.term (fun k => ((mFreeIndicator (m + 1) k : ℤ) : ℂ)) s n)) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    by_cases hfree : MFree (m + 1) n
    · have hterm : ∀ h : ℝ, LSeries.term (fun k => activationDepthFactor h m k) s n
          = activationFactor h n / (n : ℂ) ^ s := by
        intro h
        rw [LSeries.term_of_ne_zero hn, activationDepthFactor_apply, if_pos hfree]
      rw [tendsto_congr hterm, LSeries.term_of_ne_zero hn, mFreeIndicator_apply, if_pos hfree]
      simp only [Int.cast_one]
      simpa using (tendsto_activationFactor_atTop hn).div_const ((n : ℂ) ^ s)
    · have hterm : ∀ h : ℝ, LSeries.term (fun k => activationDepthFactor h m k) s n = 0 := by
        intro h
        rw [LSeries.term_of_ne_zero hn, activationDepthFactor_apply, if_neg hfree, zero_div]
      rw [tendsto_congr hterm, LSeries.term_of_ne_zero hn, mFreeIndicator_apply, if_neg hfree]
      simp
  have hbound : ∀ᶠ h : ℝ in atTop, ∀ n : ℕ,
      ‖LSeries.term (fun k => activationDepthFactor h m k) s n‖ ≤ 1 / (n : ℝ) ^ s.re := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with h hh n
    exact norm_term_activationDepthFactor_le hh m s n
  have hmain :=
    tendsto_tsum_of_dominated_convergence (Real.summable_one_div_nat_rpow.mpr hs) hlim hbound
  have hcast : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  have hzeta : LSeries (fun n => ((mFreeIndicator (m + 1) n : ℤ) : ℂ)) s
      = riemannZeta s / riemannZeta (((m : ℂ) + 1) * s) := by
    rw [← hcast]
    exact LSeries_mFree_eq_riemannZeta_div (Nat.succ_ne_zero m) hs
  rw [← hzeta]
  exact hmain

/-! ## The corner -/

/-- Zeta tends to one along every family escaping through the open right half-plane.  This is the
arbitrary-filter form of the sequential corpus statement. -/
theorem tendsto_riemannZeta_of_re_atTop_filter {α : Type*} {l : Filter α} {w : α → ℂ}
    (hw : Tendsto (fun a => (w a).re) l atTop) :
    Tendsto (fun a => riemannZeta (w a)) l (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  filter_upwards [hw.eventually_gt_atTop (1 + 1 / eps)] with a ha
  have hwin : 1 < (w a).re := by
    have : 0 < 1 / eps := one_div_pos.mpr heps
    linarith
  have hbound := norm_riemannZeta_sub_one_le hwin
  rw [dist_eq]
  refine hbound.trans_lt ?_
  have hden : 1 / eps < (w a).re - 1 := by linarith
  have hdenpos : 0 < (w a).re - 1 := by linarith
  exact (one_div_lt hdenpos heps).2 hden

/-- **The corner of `(5)` in the depth direction.** -/
theorem tendsto_zetaRatio_depth (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun m : ℕ => riemannZeta s / riemannZeta (((m : ℂ) + 1) * s)) atTop
      (𝓝 (riemannZeta s)) := by
  have hre : Tendsto (fun m : ℕ => ((((m : ℂ) + 1) * s)).re) atTop atTop := by
    have hfun : ∀ m : ℕ, ((((m : ℂ) + 1) * s)).re = ((m : ℝ) + 1) * s.re := by
      intro m
      simp [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.natCast_re,
        Complex.natCast_im]
    simp only [hfun]
    exact Filter.Tendsto.atTop_mul_const hs
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hden := (tendsto_riemannZeta_of_re_atTop_filter hre).inv₀ one_ne_zero
  have hmul := (tendsto_const_nhds (x := riemannZeta s) (f := atTop (α := ℕ))).mul hden
  simpa [div_eq_mul_inv] using hmul

/-- **The corner of `(5)` in the activation direction.** -/
theorem tendsto_zetaRatio_activation (s : ℂ) :
    Tendsto (fun h : ℝ => riemannZeta s / riemannZeta (s + (h : ℂ))) atTop
      (𝓝 (riemannZeta s)) := by
  have hre : Tendsto (fun h : ℝ => ((s + (h : ℂ))).re) atTop atTop := by
    simp only [Complex.add_re, Complex.ofReal_re]
    exact tendsto_atTop_add_const_left atTop s.re tendsto_id
  have hden := (tendsto_riemannZeta_of_re_atTop_filter hre).inv₀ one_ne_zero
  have hmul := (tendsto_const_nhds (x := riemannZeta s) (f := atTop (α := ℝ))).mul hden
  simpa [div_eq_mul_inv] using hmul

end

end RHTower
