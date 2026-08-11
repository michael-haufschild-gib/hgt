import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PortRecurrenceJets
import GaloisForLFunctions.HTGeometry.ZetaVerticalAlmostPeriodic
import GaloisForLFunctions.RHTower.GammaDampedPrimeLogCauchyDomain

/-!
# The weighted prime port and its capacity hierarchy

A weighted prime chart with weights `w p > 0` and coefficients `a p` is turned into the flat source
chart by `c p = a p / √(w p)`, so the jet capacities of the port are

`C_n = ∑_p ‖a p‖² (log p)^{2n} / w p`.

With `a p = 1` and `w p = p (log p)²` the zeroth capacity is the convergent series `∑ 1/(p (log p)²)`
while the first is the divergent prime harmonic series `∑ 1/p`.  The global port orbit is therefore
norm-continuous, totally bounded and recurrent, while its infinitesimal prime-log time generator is
not a continuous port in the same chart.

The unweighted augmentation, the Euler half-density port, and the shifted density port record the
three other capacity phases.
-/

namespace HTGeometry.ConstraintMotiveRelativity

section PrimeChart

/-- The prime-log phase family. -/
noncomputable def primeLog (p : Nat.Primes) : ℝ := Real.log p

theorem log_two_le_primeLog (p : Nat.Primes) : Real.log 2 ≤ primeLog p := by
  rw [primeLog]
  exact Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)

theorem primeLog_pos (p : Nat.Primes) : 0 < primeLog p :=
  lt_of_lt_of_le (Real.log_pos (by norm_num)) (log_two_le_primeLog p)

theorem primeLog_ne_zero (p : Nat.Primes) : primeLog p ≠ 0 := (primeLog_pos p).ne'

/-- The flat chart coefficient of a weighted prime port. -/
noncomputable def chartCoef (a : Nat.Primes → ℂ) (w : Nat.Primes → ℝ) (p : Nat.Primes) : ℂ :=
  a p / (Real.sqrt (w p) : ℂ)

/-- **`(CA.3)` at `n = 0`.**  The chart mass of a weighted port term is `‖a p‖² / w p`. -/
theorem norm_chartCoef_sq (a : Nat.Primes → ℂ) {w : Nat.Primes → ℝ} {p : Nat.Primes}
    (hw : 0 < w p) : ‖chartCoef a w p‖ ^ 2 = ‖a p‖ ^ 2 / w p := by
  have hs : 0 < Real.sqrt (w p) := Real.sqrt_pos.2 hw
  rw [chartCoef, norm_div, div_pow]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, Real.sq_sqrt hw.le]

/-- **`(CA.3)`.**  The `n`-th jet capacity term of a weighted prime port. -/
theorem norm_jetCoef_chartCoef_sq (a : Nat.Primes → ℂ) {w : Nat.Primes → ℝ} {p : Nat.Primes}
    (hw : 0 < w p) (n : ℕ) :
    ‖jetCoef primeLog (chartCoef a w) n p‖ ^ 2
      = ‖a p‖ ^ 2 * Real.log p ^ (2 * n) / w p := by
  rw [norm_jetCoef_sq, norm_chartCoef_sq a hw, primeLog]
  ring

/-! ### The singular-time port -/

/-- The singular-time weight `(CA.10)`, `w p = p (log p)²`. -/
noncomputable def singularWeight (p : Nat.Primes) : ℝ := (p : ℝ) * Real.log p ^ 2

theorem singularWeight_pos (p : Nat.Primes) : 0 < singularWeight p := by
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  have hl : 0 < Real.log p := primeLog_pos p
  rw [singularWeight]
  positivity

/-- Its flat chart coefficient family. -/
noncomputable def singularCoef : Nat.Primes → ℂ := chartCoef (fun _ => 1) singularWeight

theorem norm_singularCoef_sq (p : Nat.Primes) :
    ‖singularCoef p‖ ^ 2 = 1 / ((p : ℝ) * Real.log p ^ 2) := by
  rw [singularCoef, norm_chartCoef_sq _ (singularWeight_pos p), singularWeight]
  simp

/-- **`(CA.11)`, first half.**  The zeroth capacity converges. -/
theorem summable_singularCapacity : Summable fun p : Nat.Primes => ‖singularCoef p‖ ^ 2 := by
  refine RHTower.summable_prime_invNatLogSq.congr fun p => ?_
  rw [RHTower.invNatLogSq, norm_singularCoef_sq]

/-- **`(CA.11)`, second half.**  The first jet capacity is the divergent prime harmonic series. -/
theorem not_summable_singularJetOne :
    ¬ Summable fun p : Nat.Primes => ‖jetCoef primeLog singularCoef 1 p‖ ^ 2 := by
  intro hcon
  refine Nat.Primes.not_summable_one_div (hcon.congr fun p => ?_)
  have hl : Real.log p ≠ 0 := primeLog_ne_zero p
  have hp : (p : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    exact this.ne'
  rw [norm_jetCoef_sq, norm_singularCoef_sq, primeLog]
  field_simp

/-- **Corollary 3.1.**  The singular-time port orbit is norm-continuous, totally bounded with
compact closure and recurrent, while it is not even once continuously differentiable: the
infinitesimal prime-log time generator is not a continuous port in the same chart. -/
theorem singular_time_law :
    Continuous (portOrbit primeLog singularCoef summable_singularCapacity) ∧
    TotallyBounded (Set.range (portOrbit primeLog singularCoef summable_singularCapacity)) ∧
    IsCompact (closure (Set.range (portOrbit primeLog singularCoef summable_singularCapacity))) ∧
    (∀ ε > 0, ∀ T : ℝ, ∃ t : ℝ, T < t ∧
      ‖portOrbit primeLog singularCoef summable_singularCapacity t
        - portOrbit primeLog singularCoef summable_singularCapacity 0‖ < ε) ∧
    ¬ ContDiff ℝ 1 (portOrbit primeLog singularCoef summable_singularCapacity) := by
  refine ⟨continuous_portOrbit, totallyBounded_range_portOrbit, isCompact_closure_range_portOrbit,
    fun ε hε T => portOrbit_recurrent hε T, ?_⟩
  intro hcon
  have h1 : ((1 : ℕ) : WithTop ℕ∞) = 1 := by norm_num
  rw [← h1] at hcon
  exact not_summable_singularJetOne
    ((contDiff_portOrbit_iff primeLog 1 singularCoef summable_singularCapacity).1 hcon 1 le_rfl)

/-! ### The other capacity phases -/

/-- **§5.1, unweighted augmentation.**  `a = w = 1` has divergent capacity, so the constraint is
dense and the Hausdorff port vanishes. -/
theorem not_summable_unweightedCapacity :
    ¬ Summable fun p : Nat.Primes => ‖chartCoef (fun _ => 1) (fun _ => 1) p‖ ^ 2 := by
  have hval : ∀ p : Nat.Primes, ‖chartCoef (fun _ => (1 : ℂ)) (fun _ => (1 : ℝ)) p‖ ^ 2 = 1 := by
    intro p
    rw [norm_chartCoef_sq _ (by norm_num : (0:ℝ) < 1)]
    simp
  intro hcon
  have : Summable fun _ : Nat.Primes => (1 : ℝ) := hcon.congr hval
  rw [summable_const_iff] at this
  exact one_ne_zero this

/-- **§5.2, the Euler half-density port.**  `a p = (log p)/√p`, `w = 1` has divergent capacity: the
capacity dominates a constant multiple of the prime harmonic series. -/
theorem not_summable_eulerHalfDensityCapacity :
    ¬ Summable fun p : Nat.Primes => Real.log p ^ 2 / (p : ℝ) := by
  intro hcon
  refine Nat.Primes.not_summable_one_div ?_
  have hle : ∀ p : Nat.Primes,
      Real.log 2 ^ 2 * (1 / (p : ℝ)) ≤ Real.log p ^ 2 / (p : ℝ) := by
    intro p
    have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlp : Real.log 2 ≤ Real.log p := log_two_le_primeLog p
    rw [mul_one_div, div_le_div_iff_of_pos_right hp]
    nlinarith
  have hnn : ∀ p : Nat.Primes, 0 ≤ Real.log 2 ^ 2 * (1 / (p : ℝ)) := by
    intro p
    have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    positivity
  have hs : Summable fun p : Nat.Primes => Real.log 2 ^ 2 * (1 / (p : ℝ)) :=
    hcon.of_nonneg_of_le hnn hle
  have hl2 : Real.log 2 ^ 2 ≠ 0 := by
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  exact (hs.mul_left (Real.log 2 ^ 2)⁻¹).congr fun p => by field_simp

/-- **§5.3, right of half density.**  `a p = (log p) p^{-σ}`, `w = 1` has finite capacity exactly
for `σ > 1/2`. -/
theorem summable_shiftedDensityCapacity_iff {σ : ℝ} :
    (Summable fun p : Nat.Primes => Real.log p ^ 2 * (p : ℝ) ^ (-(2 * σ))) ↔ 1 / 2 < σ := by
  constructor
  · intro hcon
    by_contra hσ
    push Not at hσ
    refine not_summable_eulerHalfDensityCapacity (hcon.of_nonneg_of_le ?_ ?_)
    · intro p
      have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
      have : 0 ≤ Real.log p := (primeLog_pos p).le
      positivity
    · intro p
      have hp : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.one_lt.le
      have hpp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
      have hexp : ((p : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ ((p : ℕ) : ℝ) ^ (-(2 * σ)) :=
        Real.rpow_le_rpow_of_exponent_le hp (by linarith)
      have hdiv : Real.log p ^ 2 / (p : ℝ) = Real.log p ^ 2 * ((p : ℝ) ^ (-(1 : ℝ))) := by
        rw [Real.rpow_neg_one, div_eq_mul_inv]
      rw [hdiv]
      have hlog : 0 ≤ Real.log p ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_left hexp hlog
  · intro hσ
    have hbase : Summable fun n : ℕ => Real.log n ^ 2 / (n : ℝ) ^ (2 * σ) :=
      GaloisForLFunctions.HTGeometry.summable_log_pow_div_nat_rpow 2 (by linarith)
    refine (hbase.subtype (fun n : ℕ => n.Prime)).congr fun p => ?_
    have hpp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    rw [Real.rpow_neg hpp.le, div_eq_mul_inv]

end PrimeChart

end HTGeometry.ConstraintMotiveRelativity
