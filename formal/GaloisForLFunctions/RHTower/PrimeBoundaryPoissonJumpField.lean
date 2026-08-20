import GaloisForLFunctions.RHTower.PrimeBoundaryDickmanWick
import GaloisForLFunctions.RHTower.PrimeSuperspaceDecompactification
import GaloisForLFunctions.RHTower.Sieve.MoebiusSmoothLimit
import Mathlib

/-!
# The finite prime-boundary Poisson jump field and its symmetric Dickman limit

This module builds the probability space behind the finite prime-boundary Wick cumulant.  For
every prime `p ≤ N` two independent Poisson channels `K_p^±` of rate `1/p` are constructed as a
product measure, and the finite symmetric prime-jump field is

`X_N = ∑_{p ≤ N} (log p / log N) (K_p^+ - K_p^-)`.

Its exponential moment at any complex argument is computed exactly:

`E[exp (z X_N)] = exp (K_N (z / log N))`,

where `K_N` is the corpus finite prime cumulant `primeBoundaryWickCumulant`.  Specializing to real
and imaginary arguments gives the moment generating function `R_N (c / log N)` and the
characteristic function `exp (-V_N (c / log N))` of the card, so the previously formula-level
`primeBoundaryCharacteristic` is identified with a genuine expectation.

The finite Lévy measure `ν_N = ∑_{p ≤ N} (1/p)(δ_{u_p} + δ_{-u_p})` is constructed, its total
mass is shown to diverge, and its normalized windows are shown to converge to the scale-invariant
Lévy measure `1_{(0,1]} du/u`; in particular every even Lévy moment converges to `1/m`, which is
both the convergent quadratic mass and the cumulant tower of the symmetric Dickman law.  Finally
the characteristic functions converge to the strictly positive limit `exp (-Φ_T(c))`, so neither
the finite prime boundary field nor its thermodynamic limit has a real interference node.
-/

noncomputable section

namespace RHTower

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

private theorem tsum_pow_div_factorial_real (x : ℝ) :
    ∑' n : ℕ, x ^ n / (n.factorial : ℝ) = Real.exp x := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

private theorem tsum_pow_div_factorial_complex (x : ℂ) :
    ∑' n : ℕ, x ^ n / (n.factorial : ℂ) = Complex.exp x := by
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

/-- **The Poisson moment generating function.** -/
theorem integral_exp_mul_poissonMeasure (r : ℝ≥0) (a t : ℝ) :
    ∫ n : ℕ, Real.exp (t * (a * n)) ∂(poissonMeasure r)
      = Real.exp ((r : ℝ) * (Real.exp (t * a) - 1)) := by
  rw [integral_poissonMeasure]
  have hterm : ∀ n : ℕ,
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) • Real.exp (t * (a * n))
        = Real.exp (-(r : ℝ)) * (((r : ℝ) * Real.exp (t * a)) ^ n / (n.factorial : ℝ)) := by
    intro n
    have hexp : Real.exp (t * (a * n)) = (Real.exp (t * a)) ^ n := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hexp, smul_eq_mul, mul_pow]
    field_simp
  rw [tsum_congr hterm, tsum_mul_left, tsum_pow_div_factorial_real, ← Real.exp_add]
  congr 1
  ring

/-- **The Poisson exponential moment at a complex argument.** -/
theorem integral_cexp_mul_poissonMeasure (r : ℝ≥0) (a : ℝ) (z : ℂ) :
    ∫ n : ℕ, Complex.exp (z * (a * n)) ∂(poissonMeasure r)
      = Complex.exp ((r : ℂ) * (Complex.exp (z * a) - 1)) := by
  rw [integral_poissonMeasure]
  have hterm : ∀ n : ℕ,
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) • Complex.exp (z * (a * n))
        = (Real.exp (-(r : ℝ)) : ℂ) * (((r : ℂ) * Complex.exp (z * a)) ^ n / (n.factorial : ℂ)) := by
    intro n
    have hexp : Complex.exp (z * (a * n)) = (Complex.exp (z * a)) ^ n := by
      rw [← Complex.exp_nat_mul]; congr 1; ring
    rw [hexp, mul_pow, Complex.real_smul]
    push_cast
    field_simp
  rw [tsum_congr hterm, tsum_mul_left, tsum_pow_div_factorial_complex, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## The finite symmetric prime-jump field -/

/-- The index set of the finite prime-jump field: for every prime `p ≤ N` a positive (`true`) and
a negative (`false`) Poisson channel. -/
abbrev PrimeJumpIndex (N : ℕ) : Type := Bool × {p : ℕ // p ∈ Nat.primesLE N}

/-- The Poisson rate `1/p` carried by each channel of the prime `p`. -/
def primeJumpRate {N : ℕ} (i : PrimeJumpIndex N) : ℝ≥0 := ((i.2 : ℕ) : ℝ≥0)⁻¹

/-- The normalized signed jump size `± log p / log N`. -/
def primeJumpSize {N : ℕ} (i : PrimeJumpIndex N) : ℝ :=
  (if i.1 then (1 : ℝ) else -1) * (Real.log i.2 / Real.log N)

/-- The law of the finite prime-jump field: independent Poisson channels, one per index. -/
def primeJumpMeasure (N : ℕ) : Measure (PrimeJumpIndex N → ℕ) :=
  Measure.pi fun i => poissonMeasure (primeJumpRate i)

instance (N : ℕ) : IsProbabilityMeasure (primeJumpMeasure N) := by
  unfold primeJumpMeasure; infer_instance

/-- `X_N = ∑_{p ≤ N} (log p / log N) (K_p⁺ - K_p⁻)`, the finite symmetric prime-jump field `(1)`. -/
def primeJumpField (N : ℕ) (ω : PrimeJumpIndex N → ℕ) : ℝ :=
  ∑ i : PrimeJumpIndex N, primeJumpSize i * ω i

/-! ## The exact finite Wick–Lévy theorem -/

private theorem primeJumpRate_coe {N : ℕ} (i : PrimeJumpIndex N) :
    ((primeJumpRate i : ℝ≥0) : ℂ) = ((i.2 : ℕ) : ℂ)⁻¹ := by
  simp [primeJumpRate]

/-- **The exact finite complex Wick–Lévy identity.**  The exponential moment of the finite
symmetric prime-jump field at any complex argument is the exponential of the finite prime
cumulant evaluated at the boundary-layer scale `1/log N`. -/
theorem integral_cexp_primeJumpField (N : ℕ) (z : ℂ) :
    ∫ ω, Complex.exp (z * primeJumpField N ω) ∂(primeJumpMeasure N)
      = Complex.exp (primeBoundaryWickCumulant N (z / (Real.log N : ℂ))) := by
  have hprod : ∀ ω : PrimeJumpIndex N → ℕ,
      Complex.exp (z * primeJumpField N ω)
        = ∏ i : PrimeJumpIndex N, Complex.exp (z * (primeJumpSize i * (ω i : ℂ))) := by
    intro ω
    rw [← Complex.exp_sum, primeJumpField]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  simp only [hprod, primeJumpMeasure]
  rw [integral_fintype_prod_eq_prod
    (fun (i : PrimeJumpIndex N) (n : ℕ) => Complex.exp (z * ((primeJumpSize i : ℝ) * (n : ℂ))))]
  have hchannel : ∀ i : PrimeJumpIndex N,
      ∫ n : ℕ, Complex.exp (z * ((primeJumpSize i : ℝ) * (n : ℂ)))
          ∂(poissonMeasure (primeJumpRate i))
        = Complex.exp (((i.2 : ℕ) : ℂ)⁻¹ * (Complex.exp (z * (primeJumpSize i : ℝ)) - 1)) := by
    intro i
    rw [integral_cexp_mul_poissonMeasure (primeJumpRate i) (primeJumpSize i) z, primeJumpRate_coe]
  simp only [hchannel]
  rw [← Complex.exp_sum]
  congr 1
  rw [primeBoundaryWickCumulant, Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib, ← Finset.sum_coe_sort (Nat.primesLE N)]
  refine Finset.sum_congr rfl fun i _ => ?_
  set a : ℂ := z / (Real.log N : ℂ) * (Real.log (i : ℕ) : ℂ) with ha
  have htrue : z * ((primeJumpSize ((true, i) : PrimeJumpIndex N) : ℝ) : ℂ) = a := by
    simp only [primeJumpSize, ha, if_pos]
    push_cast
    ring
  have hfalse : z * ((primeJumpSize ((false, i) : PrimeJumpIndex N) : ℝ) : ℂ) = -a := by
    simp only [primeJumpSize, ha]
    push_cast
    ring
  have hcosh : Complex.cosh a = (Complex.exp a + Complex.exp (-a)) / 2 := by
    simp [Complex.cosh]
  rw [htrue, hfalse, hcosh]
  dsimp only
  ring

/-- The radial reflected energy is the cutoff energy at half scale. -/
theorem primeClockRadialEnergy_eq_cutoff (N : ℕ) (r : ℝ) :
    primeClockRadialEnergy N r = primeClockCutoffEnergy N (r / 2) := by
  rw [primeClockRadialEnergy, primeClockCutoffEnergy_half_eq_cosh]

/-- **`(5)`: the log moment generating function of the finite prime-jump field.**
`log E[exp (c X_N)] = R_N (c / log N)`. -/
theorem integral_exp_primeJumpField (N : ℕ) (c : ℝ) :
    ∫ ω, Real.exp (c * primeJumpField N ω) ∂(primeJumpMeasure N)
      = Real.exp (primeClockRadialEnergy N (c / Real.log N)) := by
  have hc : ((∫ ω, Real.exp (c * primeJumpField N ω) ∂(primeJumpMeasure N) : ℝ) : ℂ)
      = ((Real.exp (primeClockRadialEnergy N (c / Real.log N)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    have hpt : ∀ ω : PrimeJumpIndex N → ℕ,
        ((Real.exp (c * primeJumpField N ω) : ℝ) : ℂ)
          = Complex.exp ((c : ℂ) * ((primeJumpField N ω : ℝ) : ℂ)) := by
      intro ω
      rw [Complex.ofReal_exp]
      push_cast
      ring_nf
    simp only [hpt]
    rw [integral_cexp_primeJumpField,
      show ((c : ℂ) / (Real.log N : ℂ)) = ((c / Real.log N : ℝ) : ℂ) by push_cast; ring,
      primeBoundaryWickCumulant_ofReal, ← primeClockRadialEnergy_eq_cutoff,
      ← Complex.ofReal_exp]
  exact_mod_cast hc

/-- **`(6)`: the characteristic function of the finite prime-jump field** is the finite
prime-boundary characteristic function at boundary-layer scale. -/
theorem integral_cexp_I_primeJumpField (N : ℕ) (c : ℝ) :
    ∫ ω, Complex.exp ((c : ℂ) * Complex.I * ((primeJumpField N ω : ℝ) : ℂ))
        ∂(primeJumpMeasure N)
      = primeBoundaryCharacteristic N (c / Real.log N) := by
  rw [integral_cexp_primeJumpField, primeBoundaryCharacteristic]
  congr 2
  push_cast
  ring

/-- **`(19)`: the finite prime-jump characteristic function is a strictly positive real.**  The
universal prime-clock boundary layer has no real interference node. -/
theorem integral_cexp_I_primeJumpField_eq_ofReal_exp (N : ℕ) (c : ℝ) :
    ∫ ω, Complex.exp ((c : ℂ) * Complex.I * ((primeJumpField N ω : ℝ) : ℂ))
        ∂(primeJumpMeasure N)
      = ((Real.exp (-primeClockVerticalEnergy N (c / Real.log N)) : ℝ) : ℂ) := by
  rw [integral_cexp_I_primeJumpField, primeBoundaryCharacteristic_eq_ofReal_exp]

theorem integral_cexp_I_primeJumpField_ne_zero (N : ℕ) (c : ℝ) :
    ∫ ω, Complex.exp ((c : ℂ) * Complex.I * ((primeJumpField N ω : ℝ) : ℂ))
        ∂(primeJumpMeasure N) ≠ 0 := by
  rw [integral_cexp_I_primeJumpField]
  exact primeBoundaryCharacteristic_ne_zero N _

/-! ## The finite Lévy measure and its scale-invariant limit -/

/-- The finite symmetric Lévy measure `ν_N = ∑_{p ≤ N} (1/p)(δ_{u_p} + δ_{-u_p})` of `(2)`. -/
def primeJumpLevyMeasure (N : ℕ) : Measure ℝ :=
  ∑ i : PrimeJumpIndex N,
    ENNReal.ofReal (((i.2 : ℕ) : ℝ))⁻¹ • Measure.dirac (primeJumpSize i)

private theorem integrable_dirac_real (f : ℝ → ℝ) (hf : Measurable f) (a : ℝ) :
    Integrable f (Measure.dirac a) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_dirac a (fun x => ‖f x‖ₑ)]
  exact ENNReal.coe_lt_top

/-- Testing the finite Lévy measure against a measurable function. -/
theorem integral_primeJumpLevyMeasure (N : ℕ) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ u, f u ∂(primeJumpLevyMeasure N)
      = ∑ p ∈ Nat.primesLE N,
          (f (Real.log p / Real.log N) + f (-(Real.log p / Real.log N))) / p := by
  classical
  rw [primeJumpLevyMeasure, integral_finsetSum_measure]
  · have hterm : ∀ i : PrimeJumpIndex N,
        ∫ u, f u ∂(ENNReal.ofReal (((i.2 : ℕ) : ℝ))⁻¹ • Measure.dirac (primeJumpSize i))
          = f (primeJumpSize i) / ((i.2 : ℕ) : ℝ) := by
      intro i
      have hpprime : Nat.Prime (i.2 : ℕ) := (Nat.mem_primesLE.mp i.2.2).2
      have hppos : (0 : ℝ) < ((i.2 : ℕ) : ℝ) := by exact_mod_cast hpprime.pos
      rw [integral_smul_measure, integral_dirac,
        ENNReal.toReal_ofReal (by positivity), smul_eq_mul, div_eq_inv_mul]
    simp only [hterm]
    rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib,
      ← Finset.sum_coe_sort (Nat.primesLE N)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have htrue : primeJumpSize ((true, i) : PrimeJumpIndex N)
        = Real.log (i : ℕ) / Real.log N := by
      simp only [primeJumpSize]; norm_num
    have hfalse : primeJumpSize ((false, i) : PrimeJumpIndex N)
        = -(Real.log (i : ℕ) / Real.log N) := by
      simp only [primeJumpSize]; norm_num
    rw [htrue, hfalse]
    dsimp only
    ring
  · intro i _
    exact (integrable_dirac_real f hf _).smul_measure ENNReal.ofReal_ne_top

/-- The prime Lévy test quotient `f(u)/u`, extended by zero at the origin. -/
def levyTestQuotient (f : ℝ → ℝ) (u : ℝ) : ℝ := if u = 0 then 0 else f u / u

theorem primeLevyWindow_eq (f : ℝ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ p ∈ Nat.primesLE N, f (Real.log p / Real.log N) / p
      = mertensPrimeWindow (levyTestQuotient f) N / Real.log N := by
  classical
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  rw [sum_primesLE_eq_filter, mertensPrimeWindow, Finset.sum_div, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hp : n.Prime
  · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hu : Real.log (n : ℝ) / Real.log (N : ℝ) ≠ 0 := by positivity
    rw [if_pos hp, mertensPrimeWeight, if_pos hp, levyTestQuotient, if_neg hu]
    field_simp
  · rw [if_neg hp, mertensPrimeWeight, if_neg hp, mul_zero, zero_div]

/-- **`(10)`--`(11)`: the scale-invariant Lévy limit.**  For every test function whose Lévy
quotient `f(u)/u` extends continuously to `[0,1]`, the positive half of the finite prime Lévy
measure converges to `1_{(0,1]}(u) du/u`. -/
theorem tendsto_primeLevyWindow {f : ℝ → ℝ}
    (hf : ContinuousOn (levyTestQuotient f) (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesLE N, f (Real.log p / Real.log N) / p) atTop
      (𝓝 (∫ u in (0 : ℝ)..1, levyTestQuotient f u)) := by
  refine (tendsto_mertensPrimeWindow_div_log hf).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  exact (primeLevyWindow_eq f hN).symm

/-- **`(2)`: the total mass of the finite Lévy measure** is `2 ∑_{p ≤ N} 1/p`. -/
theorem integral_one_primeJumpLevyMeasure (N : ℕ) :
    ∫ _u : ℝ, (1 : ℝ) ∂(primeJumpLevyMeasure N) = ∑ p ∈ Nat.primesLE N, 2 / (p : ℝ) := by
  rw [integral_primeJumpLevyMeasure N (fun _ => (1 : ℝ)) measurable_const]
  refine Finset.sum_congr rfl fun p _ => by norm_num

/-- The total Lévy mass of the prime boundary layer diverges, while its quadratic mass `(3)`
converges. -/
theorem tendsto_integral_one_primeJumpLevyMeasure_atTop :
    Tendsto (fun N : ℕ => ∫ _u : ℝ, (1 : ℝ) ∂(primeJumpLevyMeasure N)) atTop atTop := by
  have hset : ∀ N : ℕ, Nat.primesLE N = Nat.primesBelow (N + 1) := by
    intro N
    ext p
    simp [Nat.mem_primesLE, Nat.mem_primesBelow]
  have hbase : Tendsto (fun N : ℕ => ∑ p ∈ Nat.primesBelow (N + 1), 1 / (p : ℝ)) atTop atTop :=
    RHTower.Sieve.tendsto_sum_primesBelow_inv_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hmul : Tendsto (fun N : ℕ => 2 * ∑ p ∈ Nat.primesBelow (N + 1), 1 / (p : ℝ))
      atTop atTop := hbase.const_mul_atTop (by norm_num)
  refine hmul.congr fun N => ?_
  rw [integral_one_primeJumpLevyMeasure, hset, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => by ring

/-- **`(21)`: the squared normalized coherent overlap in the critical window is exactly the
finite prime-jump characteristic function.** -/
theorem sq_exp_neg_half_primeClockVerticalEnergy (N : ℕ) (c : ℝ) :
    Real.exp (-(primeClockVerticalEnergy N (c / Real.log N)) / 2) ^ 2
      = Real.exp (-primeClockVerticalEnergy N (c / Real.log N)) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-! ## The symmetric Dickman limit -/

/-- **`(3)` and `(17)`: the even Lévy moments of the prime boundary layer.**  For every `m ≥ 1`
the `2m`-th moment of the finite prime Lévy measure converges to `1/m`; the case `m = 1` is the
convergent quadratic mass `(3)` and the general case is the cumulant tower of the symmetric
Dickman law. -/
theorem tendsto_primeJumpLevyMoment {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N : ℕ =>
        ∑ p ∈ Nat.primesLE N, 2 * (Real.log p / Real.log N) ^ (2 * m) / p)
      atTop (𝓝 (1 / (m : ℝ))) := by
  have hquot : levyTestQuotient (fun u : ℝ => 2 * u ^ (2 * m))
      = fun u : ℝ => 2 * u ^ (2 * m - 1) := by
    funext u
    rw [levyTestQuotient]
    by_cases hu : u = 0
    · have hpos : 0 < 2 * m - 1 := by omega
      rw [if_pos hu, hu, zero_pow (by omega), mul_zero]
    · rw [if_neg hu]
      rw [show 2 * m = (2 * m - 1) + 1 by omega, pow_succ]
      field_simp
      congr 1
  have hcont : ContinuousOn (levyTestQuotient (fun u : ℝ => 2 * u ^ (2 * m)))
      (Set.Icc (0 : ℝ) 1) := by
    rw [hquot]
    exact (continuous_const.mul (continuous_pow _)).continuousOn
  have hlimit : (∫ u in (0 : ℝ)..1, levyTestQuotient (fun u : ℝ => 2 * u ^ (2 * m)) u)
      = 1 / (m : ℝ) := by
    rw [hquot, intervalIntegral.integral_const_mul, integral_pow]
    have hm' : ((2 * m - 1 : ℕ) : ℝ) + 1 = 2 * (m : ℝ) := by
      have : (2 * m - 1 : ℕ) + 1 = 2 * m := by omega
      have := congrArg (fun k : ℕ => (k : ℝ)) this
      push_cast at this
      linarith
    rw [hm']
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hone : (1 : ℝ) ^ (2 * m - 1 + 1) = 1 := one_pow _
    have hzero : (0 : ℝ) ^ (2 * m - 1 + 1) = 0 := zero_pow (by omega)
    rw [hone, hzero]
    field_simp
    ring
  have := tendsto_primeLevyWindow hcont
  rw [hlimit] at this
  exact this

/-- **`(14)`: the limiting log moment generating function** of the prime boundary layer is the
Wick profile on the real axis. -/
theorem tendsto_integral_exp_primeJumpField (c : ℝ) :
    Tendsto (fun N : ℕ => ∫ ω, Real.exp (c * primeJumpField N ω) ∂(primeJumpMeasure N)) atTop
      (𝓝 (Real.exp (∫ u in (0 : ℝ)..1, radialProfileTest c u))) := by
  have h := (Real.continuous_exp.tendsto _).comp (tendsto_primeClockRadialEnergy_scaled c)
  refine h.congr fun N => ?_
  exact (integral_exp_primeJumpField N c).symm

/-- **`(16)` and `(20)`: convergence in distribution to the symmetric Dickman law.**  The
characteristic functions of the finite prime-jump fields converge to the strictly positive
exponential of the limiting vertical profile. -/
theorem tendsto_integral_cexp_I_primeJumpField (c : ℝ) :
    Tendsto (fun N : ℕ => ∫ ω, Complex.exp ((c : ℂ) * Complex.I * ((primeJumpField N ω : ℝ) : ℂ))
        ∂(primeJumpMeasure N)) atTop
      (𝓝 (((Real.exp (-(∫ u in (0 : ℝ)..1, verticalProfileTest c u)) : ℝ) : ℂ))) := by
  have hreal : Tendsto
      (fun N : ℕ => Real.exp (-primeClockVerticalEnergy N (c / Real.log N))) atTop
      (𝓝 (Real.exp (-(∫ u in (0 : ℝ)..1, verticalProfileTest c u)))) :=
    (Real.continuous_exp.tendsto _).comp
      ((tendsto_primeClockVerticalEnergy_scaled c).neg)
  have hcomplex := (Complex.continuous_ofReal.tendsto _).comp hreal
  refine hcomplex.congr fun N => ?_
  exact (integral_cexp_I_primeJumpField_eq_ofReal_exp N c).symm

/-- The limiting characteristic function is strictly positive: the symmetric Dickman law has no
real interference node `(20)`. -/
theorem exp_neg_verticalProfile_pos (c : ℝ) :
    0 < Real.exp (-(∫ u in (0 : ℝ)..1, verticalProfileTest c u)) := Real.exp_pos _

/-- The limiting cumulant of the prime boundary layer is the Wick profile `(15)`. -/
theorem wickProfile_eq_neg_verticalProfile (c : ℝ) :
    wickProfile (((c : ℝ) : ℂ) * Complex.I)
      = -((∫ u in (0 : ℝ)..1, verticalProfileTest c u : ℝ) : ℂ) :=
  wickProfile_mul_I c

end RHTower

namespace RHTower

open MeasureTheory Filter
open scoped Topology

/-- **`(23)`: the unscaled signed Lévy defect vanishes.**  The difference between the finite
prime Lévy window and the scale-invariant limit tends to zero for every admissible test function;
the successor card determines its algebraic asymptotics. -/
theorem tendsto_primeJumpLevyDefect {f : ℝ → ℝ}
    (hf : ContinuousOn (levyTestQuotient f) (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesLE N, f (Real.log p / Real.log N) / p)
        - ∫ u in (0 : ℝ)..1, levyTestQuotient f u) atTop (𝓝 0) := by
  have h := (tendsto_primeLevyWindow hf).sub_const (∫ u in (0 : ℝ)..1, levyTestQuotient f u)
  simpa using h

end RHTower
