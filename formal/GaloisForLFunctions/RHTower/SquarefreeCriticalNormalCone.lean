import GaloisForLFunctions.RHTower.PrimeProfileWindowLimit
import GaloisForLFunctions.HTGeometry.GeometricHellingerExpansion

/-!
# The squarefree parity digit carries the whole critical Hellinger normal cone

`prime-valuation-dyadic-fermion-normal-cone-law`, equations `(11)`–`(13b)`.

At the critical scaling `c_x = u / log x` the local geometric law of the prime `p` has radial nome
`p^{-(1-2c)}`.  Its parity digit is a Bernoulli law, and the Hellinger affinity of two such digits
is `1 - ½ (√a - √b)² + O(a² + b²)` in logarithm, where the quadratic displacement is exactly
`(e^{u t_p} - e^{v t_p})² / p`.  Summing over the primes below the cutoff turns the displacement
into the Mertens prime window of the profile `(e^{ut} - e^{vt})² / t` and the remainder into a
Tannery-dominated family, so the parity-digit affinity converges to the coherent kernel

`K(u,v) = exp(-½ ∫₀¹ (e^{ut} - e^{vt})² dt/t)`.
-/

open Filter Topology Set
open GaloisForLFunctions.HTGeometry

open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The radial prime nome -/

/-- The radial prime nome `q_{p,c} = p^{-(1-2c)}`. -/
def radialNome (c : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 - 2 * c))

theorem radialNome_pos {c : ℝ} {n : ℕ} (hn : 2 ≤ n) : 0 < radialNome c n := by
  have : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact Real.rpow_pos_of_pos this _

theorem radialNome_zero {n : ℕ} (hn : 2 ≤ n) : radialNome 0 n = ((n : ℝ))⁻¹ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [radialNome]
  norm_num
  rw [Real.rpow_neg_one]

theorem radialNome_eq_exp {c : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    radialNome c n = Real.exp (-(1 - 2 * c) * Real.log n) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [radialNome, Real.rpow_def_of_pos hn0]
  ring_nf

/-- Square root of an exponential. -/
theorem sqrt_exp (y : ℝ) : Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
  have hsq : Real.exp (y / 2) ^ 2 = Real.exp y := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [← hsq, Real.sqrt_sq (Real.exp_pos _).le]

/-- The square root of the radial nome splits off the drift character. -/
theorem sqrt_radialNome {c : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt (radialNome c n) =
      Real.exp (-(Real.log n) / 2) * Real.exp (c * Real.log n) := by
  rw [radialNome_eq_exp hn, sqrt_exp, ← Real.exp_add]
  congr 1
  ring
/-- **The quadratic Hellinger displacement of the parity digit.** -/
theorem sq_sqrt_radialNome_sub {c d : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    (Real.sqrt (radialNome c n) - Real.sqrt (radialNome d n)) ^ 2
      = (Real.exp (c * Real.log n) - Real.exp (d * Real.log n)) ^ 2 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hinv : Real.exp (-(Real.log n) / 2) ^ 2 = ((n : ℝ))⁻¹ := by
    rw [sq, ← Real.exp_add]
    rw [show -(Real.log n) / 2 + -(Real.log n) / 2 = -Real.log n by ring, Real.exp_neg,
      Real.exp_log hn0]
  rw [sqrt_radialNome hn, sqrt_radialNome hn, ← mul_sub, mul_pow, hinv]
  rw [div_eq_inv_mul]

/-- On the strip the radial nome stays inside the Taylor window `[0, 3/4]`. -/
theorem radialNome_le {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (hc : |c| ≤ 1 / 8) :
    radialNome c n ≤ 3 / 4 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  have hlog0 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc1 : -(1 / 8 : ℝ) ≤ c := neg_le_of_abs_le hc
  have hc2 : c ≤ 1 / 8 := le_of_abs_le hc
  have hexp : -(1 - 2 * c) * Real.log n ≤ -(3 / 4) * Real.log 2 := by
    have h1 : (3 : ℝ) / 4 ≤ 1 - 2 * c := by linarith
    nlinarith [hlog, hlog0]
  rw [radialNome_eq_exp hn]
  refine le_trans (Real.exp_le_exp.mpr hexp) ?_
  set y := Real.exp (-(3 / 4 : ℝ) * Real.log 2) with hy
  have hy0 : (0 : ℝ) < y := Real.exp_pos _
  have hy4 : y ^ 4 = 1 / 8 := by
    rw [hy, ← Real.exp_nat_mul]
    rw [show ((4 : ℕ) : ℝ) * (-(3 / 4 : ℝ) * Real.log 2) = -(3 * Real.log 2) by push_cast; ring]
    rw [show (3 : ℝ) * Real.log 2 = Real.log 8 by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring]
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  nlinarith [hy0, hy4, sq_nonneg (y - 3 / 4), sq_nonneg (y + 3 / 4), sq_nonneg (y * y - 9 / 16)]

/-- On the strip the square of the radial nome is dominated by `n^{-3/2}`. -/
theorem sq_radialNome_le {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (hc : |c| ≤ 1 / 8) :
    radialNome c n ^ 2 ≤ ((n : ℝ)) ^ (-(3 / 2 : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hc1 : -(1 / 8 : ℝ) ≤ c := neg_le_of_abs_le hc
  have hc2 : c ≤ 1 / 8 := le_of_abs_le hc
  have hpow : radialNome c n ^ 2 = ((n : ℝ)) ^ (-(2 * (1 - 2 * c))) := by
    rw [radialNome, ← Real.rpow_natCast (((n : ℝ)) ^ (-(1 - 2 * c))) 2, ← Real.rpow_mul hn0.le]
    congr 1
    push_cast
    ring
  rw [hpow]
  refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
  linarith

/-! ## The parity digit and its remainder -/

/-- The parity-digit Hellinger affinity of the prime `n` between radial drifts `c` and `d`;
extended by `1` off the primes. -/
def parityDigitAffinity (c d : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then bitHellingerAffinity (radialNome c n) (radialNome d n) 0 else 1

theorem parityDigitAffinity_pos {c d : ℝ} (n : ℕ) : 0 < parityDigitAffinity c d n := by
  rw [parityDigitAffinity]
  split_ifs with hp
  · have hn : 2 ≤ n := hp.two_le
    have ha : 0 < radialNome c n := radialNome_pos hn
    have hb : 0 < radialNome d n := radialNome_pos hn
    rw [bitHellingerAffinity]
    have hnum : (0 : ℝ) < 1 + Real.sqrt (radialNome c n * radialNome d n) ^ 2 ^ 0 := by
      have := Real.sqrt_nonneg (radialNome c n * radialNome d n)
      simp only [pow_zero, pow_one]
      linarith
    have hden : (0 : ℝ) <
        Real.sqrt ((1 + radialNome c n ^ 2 ^ 0) * (1 + radialNome d n ^ 2 ^ 0)) := by
      refine Real.sqrt_pos.mpr ?_
      simp only [pow_zero, pow_one]
      nlinarith
    exact div_pos hnum hden
  · exact zero_lt_one

/-- The per-prime remainder of the parity-digit expansion. -/
def parityRemainder (c d : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then
    Real.log (bitHellingerAffinity (radialNome c n) (radialNome d n) 0)
      + (Real.exp (c * Real.log n) - Real.exp (d * Real.log n)) ^ 2 / (n : ℝ) / 2
  else 0

/-- **The per-prime remainder is dominated by `8 n^{-3/2}`.** -/
theorem abs_parityRemainder_le {c d : ℝ} (hc : |c| ≤ 1 / 8) (hd : |d| ≤ 1 / 8) (n : ℕ) :
    |parityRemainder c d n| ≤ 8 * ((n : ℝ)) ^ (-(3 / 2 : ℝ)) := by
  rw [parityRemainder]
  split_ifs with hp
  · have hn : 2 ≤ n := hp.two_le
    have ha0 : 0 ≤ radialNome c n := (radialNome_pos hn).le
    have hb0 : 0 ≤ radialNome d n := (radialNome_pos hn).le
    have hkey := abs_log_bitHellingerAffinity_zero_add_le ha0 hb0
      (radialNome_le hn hc) (radialNome_le hn hd)
    have hdisp := sq_sqrt_radialNome_sub (c := c) (d := d) hn
    rw [hdisp] at hkey
    refine le_trans hkey ?_
    have h1 := sq_radialNome_le hn hc
    have h2 := sq_radialNome_le hn hd
    linarith
  · have : (0 : ℝ) ≤ ((n : ℝ)) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    simpa using by linarith

theorem summable_parityRemainderBound :
    Summable (fun n : ℕ => 8 * ((n : ℝ)) ^ (-(3 / 2 : ℝ))) := by
  have h : Summable (fun n : ℕ => (((n : ℝ)) ^ (3 / 2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  refine (h.mul_left 8).congr (fun n => ?_)
  rw [← Real.rpow_neg (Nat.cast_nonneg n)]

/-! ## Termwise vanishing of the remainder -/

theorem bitHellingerAffinity_zero_eq (a b : ℝ) :
    bitHellingerAffinity a b 0 = (1 + Real.sqrt (a * b)) / Real.sqrt ((1 + a) * (1 + b)) := by
  rw [bitHellingerAffinity]
  norm_num

theorem bitHellingerAffinity_self {a : ℝ} (ha : 0 ≤ a) : bitHellingerAffinity a a 0 = 1 := by
  have h1 : Real.sqrt (a * a) = a := by
    rw [← sq, Real.sqrt_sq ha]
  have h2 : Real.sqrt ((1 + a) * (1 + a)) = 1 + a := by
    rw [← sq, Real.sqrt_sq (by linarith)]
  rw [bitHellingerAffinity_zero_eq, h1, h2]
  field_simp

theorem tendsto_bitHellingerAffinity_zero_one {A B : ℕ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hA : Tendsto A atTop (nhds a)) (hB : Tendsto B atTop (nhds a)) :
    Tendsto (fun N => bitHellingerAffinity (A N) (B N) 0) atTop (nhds 1) := by
  have hnum : Tendsto (fun N => 1 + Real.sqrt (A N * B N)) atTop (nhds (1 + a)) := by
    have hprod : Tendsto (fun N => A N * B N) atTop (nhds (a * a)) := hA.mul hB
    have hsqrt := (Real.continuous_sqrt.tendsto (a * a)).comp hprod
    have hval : Real.sqrt (a * a) = a := by rw [← sq, Real.sqrt_sq ha]
    rw [hval] at hsqrt
    exact tendsto_const_nhds.add hsqrt
  have hden : Tendsto (fun N => Real.sqrt ((1 + A N) * (1 + B N))) atTop (nhds (1 + a)) := by
    have hprod : Tendsto (fun N => (1 + A N) * (1 + B N)) atTop (nhds ((1 + a) * (1 + a))) :=
      (tendsto_const_nhds.add hA).mul (tendsto_const_nhds.add hB)
    have hsqrt := (Real.continuous_sqrt.tendsto ((1 + a) * (1 + a))).comp hprod
    have hval : Real.sqrt ((1 + a) * (1 + a)) = 1 + a := by
      rw [← sq, Real.sqrt_sq (by linarith)]
    rw [hval] at hsqrt
    exact hsqrt
  have hne : (1 : ℝ) + a ≠ 0 := by linarith
  have hdiv := hnum.div hden hne
  rw [div_self hne] at hdiv
  exact hdiv.congr fun N => (bitHellingerAffinity_zero_eq (A N) (B N)).symm

theorem tendsto_radialNome {C : ℕ → ℝ} (hC : Tendsto C atTop (nhds 0)) {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun N => radialNome (C N) n) atTop (nhds ((n : ℝ))⁻¹) := by
  have hcont : Tendsto (fun N => Real.exp (-(1 - 2 * C N) * Real.log n)) atTop
      (nhds (Real.exp (-(1 - 2 * 0) * Real.log n))) := by
    refine (Real.continuous_exp.tendsto _).comp ?_
    exact ((tendsto_const_nhds.sub (hC.const_mul 2)).neg.mul_const (Real.log n))
  have hval : Real.exp (-(1 - 2 * 0) * Real.log n) = ((n : ℝ))⁻¹ := by
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [show -(1 - 2 * (0 : ℝ)) * Real.log n = -Real.log n by ring, Real.exp_neg,
      Real.exp_log hn0]
  rw [hval] at hcont
  exact hcont.congr fun N => (radialNome_eq_exp hn).symm

/-- **Each prime's remainder vanishes as the drift vanishes.** -/
theorem tendsto_parityRemainder_zero (n : ℕ) {C D : ℕ → ℝ}
    (hC : Tendsto C atTop (nhds 0)) (hD : Tendsto D atTop (nhds 0)) :
    Tendsto (fun N => parityRemainder (C N) (D N) n) atTop (nhds 0) := by
  by_cases hp : n.Prime
  · have hn : 2 ≤ n := hp.two_le
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hinv : (0 : ℝ) ≤ ((n : ℝ))⁻¹ := by positivity
    have haff := tendsto_bitHellingerAffinity_zero_one hinv
      (tendsto_radialNome hC hn) (tendsto_radialNome hD hn)
    have hlog : Tendsto
        (fun N => Real.log (bitHellingerAffinity (radialNome (C N) n) (radialNome (D N) n) 0))
        atTop (nhds 0) := by
      have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp haff
      simpa [Function.comp_def] using this
    have hchar : Tendsto
        (fun N => (Real.exp (C N * Real.log n) - Real.exp (D N * Real.log n)) ^ 2 / (n : ℝ) / 2)
        atTop (nhds 0) := by
      have h1 : Tendsto (fun N => Real.exp (C N * Real.log n)) atTop (nhds 1) := by
        have := (Real.continuous_exp.tendsto (0 * Real.log n)).comp (hC.mul_const (Real.log n))
        simpa [Function.comp_def] using this
      have h2 : Tendsto (fun N => Real.exp (D N * Real.log n)) atTop (nhds 1) := by
        have := (Real.continuous_exp.tendsto (0 * Real.log n)).comp (hD.mul_const (Real.log n))
        simpa [Function.comp_def] using this
      have := (((h1.sub h2).pow 2).div_const (n : ℝ)).div_const 2
      simpa using this
    have := hlog.add hchar
    rw [add_zero] at this
    refine this.congr fun N => ?_
    rw [parityRemainder, if_pos hp]
  · simp only [parityRemainder, if_neg hp]
    exact tendsto_const_nhds

/-! ## The coherent kernel -/

/-- The two-parameter critical profile `t ↦ (e^{ut} - e^{vt})²`. -/
def coherentProfile (u v t : ℝ) : ℝ := (Real.exp (u * t) - Real.exp (v * t)) ^ 2

theorem divProfile_coherentProfile (u v : ℝ) :
    divProfile (coherentProfile u v) = fun t => Real.exp (2 * v * t) * critProfile (u - v) t := by
  funext t
  rw [divProfile, critProfile, coherentProfile]
  by_cases ht : t = 0
  · simp [ht]
  · rw [if_neg ht, if_neg ht]
    have hfac : Real.exp (u * t) - Real.exp (v * t)
        = Real.exp (v * t) * (Real.exp ((u - v) * t) - 1) := by
      rw [mul_sub, ← Real.exp_add, mul_one]
      congr 2
      ring
    rw [hfac, mul_pow, ← Real.exp_nat_mul]
    push_cast
    rw [show (2 : ℝ) * (v * t) = 2 * v * t by ring]
    ring

theorem continuousOn_divProfile_coherentProfile (u v : ℝ) :
    ContinuousOn (divProfile (coherentProfile u v)) (Set.Icc 0 1) := by
  rw [divProfile_coherentProfile]
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
    (continuousOn_critProfile (u - v))

/-- The critical coherent exponent `½ ∫₀¹ (e^{ut} - e^{vt})² dt/t`. -/
def coherentExponent (u v : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1, divProfile (coherentProfile u v) t) / 2

/-- The critical coherent kernel `K(u,v) = exp(-½ ∫₀¹ (e^{ut} - e^{vt})² dt/t)`. -/
def coherentKernel (u v : ℝ) : ℝ := Real.exp (-coherentExponent u v)

/-- `Φ(u)` of the card is the diagonal coherent exponent against the critical parameter. -/
theorem coherentExponent_zero (u : ℝ) :
    coherentExponent u 0 = (∫ t in (0 : ℝ)..1, critProfile u t) / 2 := by
  rw [coherentExponent]
  congr 2
  funext t
  rw [divProfile_coherentProfile]
  simp

/-! ## The exact log decomposition of the parity digit -/

theorem log_parityDigitAffinity_eq (u v : ℝ) (N : ℕ) (n : ℕ) :
    Real.log (parityDigitAffinity (u / Real.log N) (v / Real.log N) n)
      = -((if n.Prime then
            coherentProfile u v (Real.log n / Real.log N) / (n : ℝ) else 0) / 2)
        + parityRemainder (u / Real.log N) (v / Real.log N) n := by
  by_cases hp : n.Prime
  · have hn : 2 ≤ n := hp.two_le
    have hdisp := sq_sqrt_radialNome_sub (c := u / Real.log N) (d := v / Real.log N) hn
    have hchar : ∀ w : ℝ, Real.exp (w / Real.log N * Real.log n)
        = Real.exp (w * (Real.log n / Real.log N)) := by
      intro w
      congr 1
      ring
    rw [parityDigitAffinity, if_pos hp, parityRemainder, if_pos hp, if_pos hp,
      coherentProfile, hchar u, hchar v]
    ring
  · rw [parityDigitAffinity, if_neg hp, parityRemainder, if_neg hp, if_neg hp, Real.log_one]
    ring

/-! ## The critical limit -/

theorem tendsto_drift_zero (u : ℝ) :
    Tendsto (fun N : ℕ => u / Real.log N) atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem eventually_abs_drift_le (u : ℝ) :
    ∀ᶠ N : ℕ in atTop, |u / Real.log N| ≤ 1 / 8 := by
  have h := (tendsto_drift_zero u).abs
  rw [abs_zero] at h
  exact h.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8))

/-- **The total remainder vanishes.**  `(14)` summed over the critical prime window. -/
theorem tendsto_sum_parityRemainder (u v : ℝ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N,
        parityRemainder (u / Real.log N) (v / Real.log N) n) atTop (nhds 0) := by
  refine tendsto_finsetSum_Icc_zero summable_parityRemainderBound
    (fun n => by positivity) ?_ ?_
  · filter_upwards [eventually_abs_drift_le u, eventually_abs_drift_le v] with N hu hv n _
    exact abs_parityRemainder_le hu hv n
  · intro n
    exact tendsto_parityRemainder_zero n (tendsto_drift_zero u) (tendsto_drift_zero v)

/-- **`(11)` and `(13b)`.**  The all-prime parity-digit Hellinger affinity at the critical scaling
converges to the coherent kernel `K(u,v)`. -/
theorem tendsto_criticalParityAffinity (u v : ℝ) :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 0 N,
        parityDigitAffinity (u / Real.log N) (v / Real.log N) n)
      atTop (nhds (coherentKernel u v)) := by
  have hdisp := tendsto_sum_divProfile (coherentProfile u v)
    (continuousOn_divProfile_coherentProfile u v)
  have hrem := tendsto_sum_parityRemainder u v
  have hsplit : ∀ N : ℕ,
      ∑ n ∈ Finset.Icc 0 N,
          Real.log (parityDigitAffinity (u / Real.log N) (v / Real.log N) n)
        = -((∑ n ∈ Finset.Icc 0 N,
              (if n.Prime then
                coherentProfile u v (Real.log n / Real.log N) / (n : ℝ) else 0)) / 2)
          + ∑ n ∈ Finset.Icc 0 N,
              parityRemainder (u / Real.log N) (v / Real.log N) n := by
    intro N
    rw [Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => log_parityDigitAffinity_eq u v N n
  have hlim : Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.Icc 0 N,
        Real.log (parityDigitAffinity (u / Real.log N) (v / Real.log N) n))
      atTop (nhds (-coherentExponent u v)) := by
    have hcomb := ((hdisp.div_const 2).neg).add hrem
    rw [add_zero] at hcomb
    refine hcomb.congr fun N => (hsplit N).symm |>.trans ?_
    rfl
  have hprod := tendsto_prod_Icc_of_tendsto_sum_log
    (A := fun N n => parityDigitAffinity (u / Real.log N) (v / Real.log N) n)
    (Filter.Eventually.of_forall fun N n _ => parityDigitAffinity_pos n) hlim
  exact hprod

/-! ## The full geometric affinity has the same critical limit -/

/-- The geometric Hellinger affinity of the prime `n` between radial drifts `c` and `d`;
extended by `1` off the primes. -/
def geometricPrimeAffinity (c d : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then geometricHellingerAffinity (radialNome c n) (radialNome d n) else 1

theorem geometricHellingerAffinity_pos {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b)
    (hb1 : b < 1) : 0 < geometricHellingerAffinity a b := by
  have hab : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hablt : a * b < 1 := by nlinarith
  have hs1 : Real.sqrt (a * b) < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hab hablt
  rw [geometricHellingerAffinity]
  refine div_pos (Real.sqrt_pos.mpr (by nlinarith)) (by linarith)

theorem geometricHellingerAffinity_self {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    geometricHellingerAffinity a a = 1 := by
  have h1 : Real.sqrt ((1 - a) * (1 - a)) = 1 - a := by
    rw [← sq, Real.sqrt_sq (by linarith)]
  have h2 : Real.sqrt (a * a) = a := by rw [← sq, Real.sqrt_sq ha0]
  rw [geometricHellingerAffinity, h1, h2]
  exact div_self (by linarith)

theorem geometricPrimeAffinity_pos {c d : ℝ} (hc : |c| ≤ 1 / 8) (hd : |d| ≤ 1 / 8) (n : ℕ) :
    0 < geometricPrimeAffinity c d n := by
  rw [geometricPrimeAffinity]
  split_ifs with hp
  · have hn : 2 ≤ n := hp.two_le
    exact geometricHellingerAffinity_pos (radialNome_pos hn).le
      (lt_of_le_of_lt (radialNome_le hn hc) (by norm_num))
      (radialNome_pos hn).le (lt_of_le_of_lt (radialNome_le hn hd) (by norm_num))
  · exact zero_lt_one

/-- The per-prime remainder of the geometric expansion. -/
def geometricRemainder (c d : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then
    Real.log (geometricHellingerAffinity (radialNome c n) (radialNome d n))
      + (Real.exp (c * Real.log n) - Real.exp (d * Real.log n)) ^ 2 / (n : ℝ) / 2
  else 0

theorem abs_geometricRemainder_le {c d : ℝ} (hc : |c| ≤ 1 / 8) (hd : |d| ≤ 1 / 8) (n : ℕ) :
    |geometricRemainder c d n| ≤ 8 * ((n : ℝ)) ^ (-(3 / 2 : ℝ)) := by
  rw [geometricRemainder]
  split_ifs with hp
  · have hn : 2 ≤ n := hp.two_le
    have ha0 : 0 ≤ radialNome c n := (radialNome_pos hn).le
    have hb0 : 0 ≤ radialNome d n := (radialNome_pos hn).le
    have hkey := abs_log_geometricHellingerAffinity_add_le ha0 hb0
      (radialNome_le hn hc) (radialNome_le hn hd)
    have hdisp := sq_sqrt_radialNome_sub (c := c) (d := d) hn
    rw [hdisp] at hkey
    refine le_trans hkey ?_
    have h1 := sq_radialNome_le hn hc
    have h2 := sq_radialNome_le hn hd
    linarith
  · have : (0 : ℝ) ≤ ((n : ℝ)) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    simpa using by linarith

theorem tendsto_geometricHellingerAffinity_one {A B : ℕ → ℝ} {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hA : Tendsto A atTop (nhds a)) (hB : Tendsto B atTop (nhds a)) :
    Tendsto (fun N => geometricHellingerAffinity (A N) (B N)) atTop (nhds 1) := by
  have hnum : Tendsto (fun N => Real.sqrt ((1 - A N) * (1 - B N))) atTop (nhds (1 - a)) := by
    have hprod : Tendsto (fun N => (1 - A N) * (1 - B N)) atTop (nhds ((1 - a) * (1 - a))) :=
      (tendsto_const_nhds.sub hA).mul (tendsto_const_nhds.sub hB)
    have hsqrt := (Real.continuous_sqrt.tendsto ((1 - a) * (1 - a))).comp hprod
    have hval : Real.sqrt ((1 - a) * (1 - a)) = 1 - a := by
      rw [← sq, Real.sqrt_sq (by linarith)]
    rw [hval] at hsqrt
    exact hsqrt
  have hden : Tendsto (fun N => 1 - Real.sqrt (A N * B N)) atTop (nhds (1 - a)) := by
    have hprod : Tendsto (fun N => A N * B N) atTop (nhds (a * a)) := hA.mul hB
    have hsqrt := (Real.continuous_sqrt.tendsto (a * a)).comp hprod
    have hval : Real.sqrt (a * a) = a := by rw [← sq, Real.sqrt_sq ha0]
    rw [hval] at hsqrt
    exact tendsto_const_nhds.sub hsqrt
  have hne : (1 : ℝ) - a ≠ 0 := by linarith
  have hdiv := hnum.div hden hne
  rw [div_self hne] at hdiv
  exact hdiv.congr fun N => rfl

theorem tendsto_geometricRemainder_zero (n : ℕ) {C D : ℕ → ℝ}
    (hC : Tendsto C atTop (nhds 0)) (hD : Tendsto D atTop (nhds 0)) :
    Tendsto (fun N => geometricRemainder (C N) (D N) n) atTop (nhds 0) := by
  by_cases hp : n.Prime
  · have hn : 2 ≤ n := hp.two_le
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hinv0 : (0 : ℝ) ≤ ((n : ℝ))⁻¹ := by positivity
    have hinv1 : ((n : ℝ))⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      right; linarith
    have haff := tendsto_geometricHellingerAffinity_one hinv0 hinv1
      (tendsto_radialNome hC hn) (tendsto_radialNome hD hn)
    have hlog : Tendsto
        (fun N => Real.log (geometricHellingerAffinity (radialNome (C N) n) (radialNome (D N) n)))
        atTop (nhds 0) := by
      have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp haff
      simpa [Function.comp_def] using this
    have hchar : Tendsto
        (fun N => (Real.exp (C N * Real.log n) - Real.exp (D N * Real.log n)) ^ 2 / (n : ℝ) / 2)
        atTop (nhds 0) := by
      have h1 : Tendsto (fun N => Real.exp (C N * Real.log n)) atTop (nhds 1) := by
        have := (Real.continuous_exp.tendsto (0 * Real.log n)).comp (hC.mul_const (Real.log n))
        simpa [Function.comp_def] using this
      have h2 : Tendsto (fun N => Real.exp (D N * Real.log n)) atTop (nhds 1) := by
        have := (Real.continuous_exp.tendsto (0 * Real.log n)).comp (hD.mul_const (Real.log n))
        simpa [Function.comp_def] using this
      have := (((h1.sub h2).pow 2).div_const (n : ℝ)).div_const 2
      simpa using this
    have := hlog.add hchar
    rw [add_zero] at this
    refine this.congr fun N => ?_
    rw [geometricRemainder, if_pos hp]
  · simp only [geometricRemainder, if_neg hp]
    exact tendsto_const_nhds

theorem log_geometricPrimeAffinity_eq (u v : ℝ) (N : ℕ) (n : ℕ) :
    Real.log (geometricPrimeAffinity (u / Real.log N) (v / Real.log N) n)
      = -((if n.Prime then
            coherentProfile u v (Real.log n / Real.log N) / (n : ℝ) else 0) / 2)
        + geometricRemainder (u / Real.log N) (v / Real.log N) n := by
  by_cases hp : n.Prime
  · have hn : 2 ≤ n := hp.two_le
    have hdisp := sq_sqrt_radialNome_sub (c := u / Real.log N) (d := v / Real.log N) hn
    have hchar : ∀ w : ℝ, Real.exp (w / Real.log N * Real.log n)
        = Real.exp (w * (Real.log n / Real.log N)) := by
      intro w
      congr 1
      ring
    rw [geometricPrimeAffinity, if_pos hp, geometricRemainder, if_pos hp, if_pos hp,
      coherentProfile, hchar u, hchar v]
    ring
  · rw [geometricPrimeAffinity, if_neg hp, geometricRemainder, if_neg hp, if_neg hp, Real.log_one]
    ring

theorem tendsto_sum_geometricRemainder (u v : ℝ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N,
        geometricRemainder (u / Real.log N) (v / Real.log N) n) atTop (nhds 0) := by
  refine tendsto_finsetSum_Icc_zero summable_parityRemainderBound
    (fun n => by positivity) ?_ ?_
  · filter_upwards [eventually_abs_drift_le u, eventually_abs_drift_le v] with N hu hv n _
    exact abs_geometricRemainder_le hu hv n
  · intro n
    exact tendsto_geometricRemainder_zero n (tendsto_drift_zero u) (tendsto_drift_zero v)

/-- **`(13)`.**  The full geometric prime-valuation Hellinger affinity at the critical scaling has
the same limit as its parity digit: the coherent kernel `K(u,v)`. -/
theorem tendsto_criticalGeometricAffinity (u v : ℝ) :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 0 N,
        geometricPrimeAffinity (u / Real.log N) (v / Real.log N) n)
      atTop (nhds (coherentKernel u v)) := by
  have hdisp := tendsto_sum_divProfile (coherentProfile u v)
    (continuousOn_divProfile_coherentProfile u v)
  have hrem := tendsto_sum_geometricRemainder u v
  have hsplit : ∀ N : ℕ,
      ∑ n ∈ Finset.Icc 0 N,
          Real.log (geometricPrimeAffinity (u / Real.log N) (v / Real.log N) n)
        = -((∑ n ∈ Finset.Icc 0 N,
              (if n.Prime then
                coherentProfile u v (Real.log n / Real.log N) / (n : ℝ) else 0)) / 2)
          + ∑ n ∈ Finset.Icc 0 N,
              geometricRemainder (u / Real.log N) (v / Real.log N) n := by
    intro N
    rw [Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => log_geometricPrimeAffinity_eq u v N n
  have hlim : Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.Icc 0 N,
        Real.log (geometricPrimeAffinity (u / Real.log N) (v / Real.log N) n))
      atTop (nhds (-coherentExponent u v)) := by
    have hcomb := ((hdisp.div_const 2).neg).add hrem
    rw [add_zero] at hcomb
    refine hcomb.congr fun N => (hsplit N).symm |>.trans ?_
    rfl
  refine tendsto_prod_Icc_of_tendsto_sum_log ?_ hlim
  filter_upwards [eventually_abs_drift_le u, eventually_abs_drift_le v] with N hu hv n _
  exact geometricPrimeAffinity_pos hu hv n

/-- **`(12)`.**  The whole higher dyadic tower is asymptotically invisible: the ratio of the full
geometric affinity to its parity digit tends to one. -/
theorem tendsto_higherDigitTail_one (u v : ℝ) :
    Tendsto (fun N : ℕ =>
        (∏ n ∈ Finset.Icc 0 N, geometricPrimeAffinity (u / Real.log N) (v / Real.log N) n) /
          ∏ n ∈ Finset.Icc 0 N, parityDigitAffinity (u / Real.log N) (v / Real.log N) n)
      atTop (nhds 1) := by
  have hg := tendsto_criticalGeometricAffinity u v
  have hp := tendsto_criticalParityAffinity u v
  have hne : coherentKernel u v ≠ 0 := by
    rw [coherentKernel]
    exact (Real.exp_pos _).ne'
  have := hg.div hp hne
  rwa [div_self hne] at this

/-! ## `(22)`: the critical Fisher capacity -/

theorem divProfile_sq : divProfile (fun t : ℝ => t ^ 2) = fun t : ℝ => t := by
  funext t
  rw [divProfile]
  by_cases ht : t = 0
  · simp [ht]
  · rw [if_neg ht, sq, mul_div_assoc, div_self ht, mul_one]

theorem fisherFactor_bounds {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ x⁻¹ / (1 - x⁻¹) ^ 2 - x⁻¹ ∧ x⁻¹ / (1 - x⁻¹) ^ 2 - x⁻¹ ≤ 8 / x ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hxm : (0 : ℝ) < x - 1 := by linarith
  have hne : (1 : ℝ) - x⁻¹ ≠ 0 := by
    have : (1 : ℝ) - x⁻¹ = (x - 1) / x := by field_simp
    rw [this]
    positivity
  have hval : x⁻¹ / (1 - x⁻¹) ^ 2 - x⁻¹ = (2 * x - 1) / (x * (x - 1) ^ 2) := by
    field_simp
    ring
  rw [hval]
  refine ⟨div_nonneg (by linarith) (by positivity), ?_⟩
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hx, hxm, hx0]

/-- The correction between the geometric Fisher capacity and its leading prime term. -/
def fisherCorrection (N n : ℕ) : ℝ :=
  if n.Prime then
    (Real.log n / Real.log N) ^ 2 * (((n : ℝ))⁻¹ / (1 - ((n : ℝ))⁻¹) ^ 2 - ((n : ℝ))⁻¹)
  else 0

theorem tendsto_sum_fisherCorrection :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N, fisherCorrection N n) atTop (nhds 0) := by
  refine tendsto_finsetSum_Icc_zero (bound := fun n : ℕ => 8 / ((n : ℝ)) ^ 2) ?_
    (fun n => by positivity) ?_ ?_
  · have h : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    refine (h.mul_left 8).congr (fun n => ?_)
    rw [mul_one_div]
  · filter_upwards [eventually_ge_atTop 2] with N hN n hn
    rw [fisherCorrection]
    split_ifs with hp
    · have hn2 : 2 ≤ n := hp.two_le
      have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
      have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
      have hle : Real.log (n : ℝ) ≤ Real.log (N : ℝ) := by
        refine Real.log_le_log (by linarith) ?_
        exact_mod_cast hn
      have ht0 : 0 ≤ Real.log (n : ℝ) / Real.log (N : ℝ) := by positivity
      have ht1 : Real.log (n : ℝ) / Real.log (N : ℝ) ≤ 1 := by
        rw [div_le_one hlogN]; exact hle
      obtain ⟨hf0, hf1⟩ := fisherFactor_bounds hnr
      have ht2 : (Real.log (n : ℝ) / Real.log (N : ℝ)) ^ 2 ≤ 1 := by nlinarith
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hf0)]
      calc (Real.log (n : ℝ) / Real.log (N : ℝ)) ^ 2
              * (((n : ℝ))⁻¹ / (1 - ((n : ℝ))⁻¹) ^ 2 - ((n : ℝ))⁻¹)
          ≤ 1 * (((n : ℝ))⁻¹ / (1 - ((n : ℝ))⁻¹) ^ 2 - ((n : ℝ))⁻¹) :=
            mul_le_mul_of_nonneg_right ht2 hf0
        _ = ((n : ℝ))⁻¹ / (1 - ((n : ℝ))⁻¹) ^ 2 - ((n : ℝ))⁻¹ := one_mul _
        _ ≤ 8 / ((n : ℝ)) ^ 2 := hf1
    · have : (0 : ℝ) ≤ 8 / ((n : ℝ)) ^ 2 := by positivity
      simpa using this
  · intro n
    simp only [fisherCorrection]
    by_cases hp : n.Prime
    · simp only [if_pos hp]
      have hlim : Tendsto (fun N : ℕ => Real.log (n : ℝ) / Real.log (N : ℝ)) atTop (nhds 0) :=
        tendsto_drift_zero (Real.log n)
      have := ((hlim.pow 2).mul_const
        (((n : ℝ))⁻¹ / (1 - ((n : ℝ))⁻¹) ^ 2 - ((n : ℝ))⁻¹))
      simpa using this
    · simp only [if_neg hp]
      exact tendsto_const_nhds

/-- **`(22)`.**  The critical normal-cone Fisher metric of the geometric prime-valuation sector is
`1/2`: the `(log x)^{-2}`-normalized capacity of the primes below the cutoff converges. -/
theorem tendsto_criticalFisherCapacity :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 0 N,
        (if n.Prime then
          (Real.log n) ^ 2 * (((n : ℝ))⁻¹ / (1 - ((n : ℝ))⁻¹) ^ 2) / (Real.log N) ^ 2
        else 0))
      atTop (nhds (1 / 2)) := by
  have hmain := tendsto_sum_divProfile (fun t : ℝ => t ^ 2) (by
    rw [divProfile_sq]; exact continuous_id.continuousOn)
  have hint : (∫ t in (0 : ℝ)..1, divProfile (fun t : ℝ => t ^ 2) t) = 1 / 2 := by
    rw [divProfile_sq, integral_id]
    norm_num
  rw [hint] at hmain
  have hcorr := tendsto_sum_fisherCorrection
  have hcomb := hmain.add hcorr
  rw [add_zero] at hcomb
  refine hcomb.congr fun N => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [fisherCorrection]
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp, if_pos hp, div_pow]
    ring
  · rw [if_neg hp, if_neg hp, if_neg hp]
    ring

end

end RHTower
