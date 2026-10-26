import GaloisForLFunctions.ArithmeticEffectivityTheory.TheEffectivityCalculus
import GaloisForLFunctions.BiarithmeticGeometry.PrimePowerTransitionGroups
import GaloisForLFunctions.RHTower.VonKochChebyshevBound

/-!
# The horizon torsion: which integer the sign is about

Over `ℤ` the integers of the explicit formula are orders of finite groups. The horizon `{1, …, N}`
has period `lcm(1, …, N)`, and its **log-torsion** is `log |ℤ / lcm(1, …, N) ℤ| = ψ(N)`
(`logTorsion_eq_psi`); passing from `N` to `N + 1` adds exactly the log-order of a cyclic kernel,
`Λ(N + 1)` (`logTorsion_succ_sub`).

* **Bézout of `Spec ℤ`** (`log_eq_logTorsion`, `log_eq_sum_factorization_logs`). For `n ≥ 1` the
  archimedean degree `log n` equals the finite log-torsion `log |ℤ/nℤ| = Σ_p v_p(n) log p ≥ 0`: the
  product formula, read as the nonnegativity of an effective divisor's intersection with the
  ample class. It is the only integrality inequality the base supplies.
* **The box class** (`eulerChar_boxClass`). On every polar surface the class `√N · A` has Euler
  characteristic `χ = N` (canonical class `0`): the degrees of freedom of the polar box of length
  `N`.
* **The integer the sign is about** (`riemannHypothesis_iff_logTorsion_sub_eulerChar`). RH holds iff
  the log-torsion of the horizon equals the Euler characteristic of the box class up to
  `O(√N log² N)`: `log |ℤ / lcm(1, …, N) ℤ| = N + O(√N log² N)` (von Koch). The two computations of
  one Euler characteristic are the degree of the box and the torsion of its period; RH is that they
  agree at square-root precision.
-/

noncomputable section

open Filter Asymptotics Real

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

open ArithmeticCastelnuovoSeveri BiarithmeticGeometry

/-- The **log-torsion** of the horizon `{1, …, N}`: `log |ℤ / lcm(1, …, N) ℤ|`. -/
def logTorsion (N : ℕ) : ℝ := Real.log (Nat.card (ZMod (Nat.lcmUpto N)))

theorem logTorsion_eq_log_lcmUpto (N : ℕ) : logTorsion N = Real.log (Nat.lcmUpto N) := by
  rw [logTorsion, Nat.card_zmod]

/-- The log-torsion of the horizon is Chebyshev's `ψ`. -/
theorem logTorsion_eq_psi (N : ℕ) : logTorsion N = Chebyshev.psi N := by
  rw [logTorsion_eq_log_lcmUpto, Chebyshev.psi_eq_log_lcmUpto]

/-- **Each new horizon point adds the log-order of a cyclic kernel**: `Λ(N + 1)`. -/
theorem logTorsion_succ_sub (N : ℕ) :
    logTorsion (N + 1) - logTorsion N = ArithmeticFunction.vonMangoldt (N + 1) := by
  rw [logTorsion_eq_log_lcmUpto, logTorsion_eq_log_lcmUpto, ← log_horizonPeriodJump,
    ← horizonPeriodJump_mul N, Nat.cast_mul, Real.log_mul
      (by exact_mod_cast (horizonPeriodJump_pos N).ne') (by exact_mod_cast Nat.lcmUpto_ne_zero N)]
  ring

/-- **Bézout of `Spec ℤ`**: the archimedean degree of a positive integer is the log-order of the
finite group it cuts out. -/
theorem log_eq_logTorsion (n : ℕ) : Real.log n = Real.log (Nat.card (ZMod n)) := by
  rw [Nat.card_zmod]

/-- The product formula: `log n = Σ_p v_p(n) log p`, a sum of nonnegative log-orders. -/
theorem log_eq_sum_factorization_logs (n : ℕ) :
    Real.log n = n.factorization.sum fun p t => t * Real.log p :=
  Real.log_nat_eq_sum_factorization n

/-- The **box class** `√N · A` of a polar surface. -/
def boxClass {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E) (N : ℕ) : E :=
  Real.sqrt N • S.ample

/-- The box class has Euler characteristic `N`. -/
theorem eulerChar_boxClass {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E) (N : ℕ) :
    eulerChar S 0 0 (boxClass S N) = N := by
  rw [boxClass, eulerChar_smul, S.pair_ample_ample, Real.sq_sqrt (Nat.cast_nonneg N)]
  simp

/-- Von Koch at integer horizons: RH iff `ψ(N) − N = O(√N log² N)` along `ℕ`. -/
theorem riemannHypothesis_iff_logTorsion_sub_isBigO :
    RiemannHypothesis ↔ (fun N : ℕ => logTorsion N - N) =O[atTop]
      (fun N : ℕ => Real.sqrt N * Real.log N ^ 2) := by
  rw [RHTower.riemannHypothesis_iff_chebyshevPsi_sub_isBigO]
  constructor
  · intro h
    simpa only [Function.comp_def, logTorsion_eq_psi] using
      h.comp_tendsto tendsto_natCast_atTop_atTop
  · intro h
    have h1 := h.comp_tendsto (tendsto_nat_floor_atTop (α := ℝ))
    have hfl : (fun x : ℝ => Real.sqrt ⌊x⌋₊ * Real.log ⌊x⌋₊ ^ 2) =O[atTop]
        fun x : ℝ => Real.sqrt x * Real.log x ^ 2 := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hf1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.one_le_floor_iff x |>.mpr hx
      have hfx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
      have hl0 : 0 ≤ Real.log ⌊x⌋₊ := Real.log_nonneg hf1
      have hl : Real.log ⌊x⌋₊ ≤ Real.log x := Real.log_le_log (by linarith) hfx
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by
        have := Real.log_nonneg hx; positivity), one_mul]
      exact mul_le_mul (Real.sqrt_le_sqrt hfx) (pow_le_pow_left₀ hl0 hl 2) (by positivity)
        (Real.sqrt_nonneg _)
    have h2 : (fun x : ℝ => (⌊x⌋₊ : ℝ) - x) =O[atTop] fun x : ℝ => Real.sqrt x * Real.log x ^ 2 := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
      have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
      have hlog : 1 ≤ Real.log x := (Real.le_log_iff_exp_le (by linarith)).mpr hx
      have hs : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity), one_mul,
        abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le (by linarith)))]
      have := Nat.lt_floor_add_one x
      nlinarith [one_le_pow₀ (n := 2) hlog]
    refine ((h1.trans hfl).add h2).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_def, logTorsion_eq_psi, ← Chebyshev.psi_eq_psi_coe_floor]
    ring

/-- **The integer the sign is about.** On every polar surface, RH holds iff the log-torsion of the
horizon `{1, …, N}` equals the Euler characteristic of the box class `√N · A` up to
`O(√N log² N)`. -/
theorem riemannHypothesis_iff_logTorsion_sub_eulerChar {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : PolarSurface E) :
    RiemannHypothesis ↔ (fun N : ℕ => logTorsion N - eulerChar S 0 0 (boxClass S N)) =O[atTop]
      (fun N : ℕ => Real.sqrt N * Real.log N ^ 2) := by
  simp only [eulerChar_boxClass]
  exact riemannHypothesis_iff_logTorsion_sub_isBigO

end GaloisForLFunctions.ArithmeticEffectivityTheory
