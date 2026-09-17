import GaloisForLFunctions.RHTower.PrimeLogThetaLowerClosedGraphLanding

/-!
# Four-level lower-half closed-graph landing for the prime-log theta clock

The literal prime-log theta clock has source symbols

```text
Q_n,l(-i t) = sum_p l_p (2 log(p)^(n+2) / sqrt(p)) exp(-t log(p)).
```

For every positive `t`, including each of the four levels `n = 0,1,2,3`, this is an honest
source-`ℓ²` reporter.  Composing those reporters with the source projection of
`Graph(cl primeLogCriticalLaplaceSynthesis)` gives one four-level closed-graph map.  On every
literal core vector it carries the full denominator-free Wronskian ladder and each labelled
mixed cross term, retaining the exact left and right Xi powers.

This is a lower-half-strip relative landing, not a real-axis boundary quotient: the latter still
needs the genuinely new PHCCED boundary mechanism because literal real-axis reporters are not
source-`ℓ²`.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal InnerProduct LinearPMap

namespace RHTower

noncomputable section

/-- Literal source coefficient at clock degree `n` on the lower imaginary theta ray. -/
def primeLogThetaLowerClockCoefficient
    (n : ℕ) (t : ℝ) (p : Nat.Primes) : ℂ :=
  ((2 * Real.log (p : ℝ) ^ (n + 2) / Real.sqrt (p : ℝ) *
    Real.exp (-(Real.log (p : ℝ) * t)) : ℝ) : ℂ)

/-- Exact source mass of the lower-half clock coefficient. -/
theorem norm_sq_primeLogThetaLowerClockCoefficient
    (n : ℕ) (t : ℝ) (p : Nat.Primes) :
    ‖primeLogThetaLowerClockCoefficient n t p‖ ^ 2 =
      4 * Real.log (p : ℝ) ^ (2 * n + 4) /
        (p : ℝ) ^ (1 + 2 * t) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hcoeff : 0 < 2 * Real.log (p : ℝ) ^ (n + 2) / Real.sqrt (p : ℝ) *
      Real.exp (-(Real.log (p : ℝ) * t)) := by
    positivity
  have hsqrt : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  unfold primeLogThetaLowerClockCoefficient
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcoeff]
  have hexp : Real.exp (-(Real.log (p : ℝ) * t)) ^ 2 =
      (p : ℝ) ^ (-(2 * t)) := by
    rw [pow_two, ← Real.exp_add, Real.rpow_def_of_pos hp]
    congr 1
    ring
  field_simp [hsqrt]
  rw [Real.sq_sqrt hp.le, hexp, Real.rpow_add hp,
    Real.rpow_one, Real.rpow_neg hp.le]
  have hpow : (p : ℝ) ^ (t * 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hp _).ne'
  field_simp [hpow]
  rw [← pow_mul, show (n + 2) * 2 = 2 * n + 4 by omega]
  ring

/-- Every lower-half clock degree is represented by an actual source Hilbert vector. -/
theorem memℓp_primeLogThetaLowerClockCoefficient
    (n : ℕ) (t : ℝ) (ht : 0 < t) :
    Memℓp (primeLogThetaLowerClockCoefficient n t) 2 := by
  have hnat := HTGeometry.summable_log_pow_div_nat_rpow (2 * n + 4)
    (show (1 : ℝ) < 1 + 2 * t by linarith)
  have hprime : Summable (fun p : Nat.Primes =>
      Real.log ((p : ℕ) : ℝ) ^ (2 * n + 4) /
        (((p : ℕ) : ℝ) ^ (1 + 2 * t))) :=
    Summable.subtype hnat Nat.Prime
  apply memℓp_gen
  refine (hprime.mul_left (4 : ℝ)).congr fun p => ?_
  norm_num
  simpa only [mul_div_assoc, Nat.cast_ofNat] using
    (norm_sq_primeLogThetaLowerClockCoefficient n t p).symm

/-- Source-Hilbert reporter for one lower-half clock degree. -/
def primeLogThetaLowerClockReporter
    (n : ℕ) (t : ℝ) (ht : 0 < t) : primeLogCriticalSourceL2 :=
  ⟨primeLogThetaLowerClockCoefficient n t,
    memℓp_primeLogThetaLowerClockCoefficient n t ht⟩

private theorem star_primeLogThetaLowerClockCoefficient
    (n : ℕ) (t : ℝ) (p : Nat.Primes) :
    star (primeLogThetaLowerClockCoefficient n t p) =
      primeLogThetaLowerClockCoefficient n t p := by
  change star ((2 * Real.log (p : ℝ) ^ (n + 2) / Real.sqrt (p : ℝ) *
    Real.exp (-(Real.log (p : ℝ) * t)) : ℝ) : ℂ) =
      ((2 * Real.log (p : ℝ) ^ (n + 2) / Real.sqrt (p : ℝ) *
        Real.exp (-(Real.log (p : ℝ) * t)) : ℝ) : ℂ)
  exact Complex.conj_ofReal _

/-- The lower-half coefficient is exactly the literal strip clock coefficient at `-i t`. -/
theorem primeLogThetaLowerClockCoefficient_eq_strip
    (n : ℕ) (t : ℝ) (p : Nat.Primes) :
    primeLogThetaLowerClockCoefficient n t p =
      primeLogThetaStripCoefficient p * (Real.log (p : ℝ) : ℂ) ^ n *
        Complex.exp (-I * (-I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ)) := by
  unfold primeLogThetaLowerClockCoefficient primeLogThetaStripCoefficient
  have harg : -I * (-I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ) =
      (-(Real.log (p : ℝ) * t) : ℝ) := by
    push_cast
    calc
      -I * (-I * (t : ℂ)) * Complex.log (p : ℂ) =
          ((-I) * (-I)) * (t : ℂ) * Complex.log (p : ℂ) := by ring
      _ = (-1 : ℂ) * (t : ℂ) * Complex.log (p : ℂ) := by
        rw [show (-I : ℂ) * (-I) = -1 by norm_num]
      _ = -(Complex.log (p : ℂ) * (t : ℂ)) := by ring
  rw [harg, show Complex.exp ((-(Real.log (p : ℝ) * t) : ℝ) : ℂ) =
      (Real.exp (-(Real.log (p : ℝ) * t)) : ℂ) by rw [Complex.ofReal_exp]]
  push_cast
  ring

/-- Literal finite source symbols are source inner products against their degree reporter. -/
theorem primeLogThetaLowerClockReporter_inner_srcEmb
    (n : ℕ) (t : ℝ) (ht : 0 < t) (l : Nat.Primes →₀ ℂ) :
    inner ℂ (primeLogThetaLowerClockReporter n t ht)
      (HTGeometry.ConstraintMotiveRelativity.srcEmb l) =
      ∑ p ∈ l.support, l p * primeLogThetaLowerClockCoefficient n t p := by
  rw [lp.inner_eq_tsum]
  have hsum : (∑' p : Nat.Primes,
      inner ℂ ((primeLogThetaLowerClockReporter n t ht :
        primeLogCriticalSourceL2) p)
        ((HTGeometry.ConstraintMotiveRelativity.srcEmb l :
          primeLogCriticalSourceL2) p)) =
      ∑ p ∈ l.support,
        inner ℂ ((primeLogThetaLowerClockReporter n t ht :
          primeLogCriticalSourceL2) p)
          ((HTGeometry.ConstraintMotiveRelativity.srcEmb l :
            primeLogCriticalSourceL2) p) := by
    apply tsum_eq_sum
    intro p hp
    rw [RCLike.inner_apply,
      HTGeometry.ConstraintMotiveRelativity.srcEmb_apply]
    simp only [Finsupp.notMem_support_iff.mp hp, zero_mul]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [RCLike.inner_apply,
    HTGeometry.ConstraintMotiveRelativity.srcEmb_apply]
  change l p * star (primeLogThetaLowerClockCoefficient n t p) =
    l p * primeLogThetaLowerClockCoefficient n t p
  rw [star_primeLogThetaLowerClockCoefficient]

/-- The literal degree-`n` strip symbol on the lower ray is the corresponding source report. -/
theorem primeLogThetaStripSymbol_lower_eq_inner
    (n : ℕ) (t : ℝ) (ht : 0 < t) (l : Nat.Primes →₀ ℂ) :
    primeLogThetaStripSymbol n l (-I * (t : ℂ)) =
      inner ℂ (primeLogThetaLowerClockReporter n t ht)
        (HTGeometry.ConstraintMotiveRelativity.srcEmb l) := by
  rw [primeLogThetaLowerClockReporter_inner_srcEmb]
  unfold primeLogThetaStripSymbol
  apply Finset.sum_congr rfl
  intro p hp
  calc
    l p * primeLogThetaStripCoefficient p * (Real.log (p : ℝ) : ℂ) ^ n *
          Complex.exp (-I * (-I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ)) =
        l p * (primeLogThetaStripCoefficient p * (Real.log (p : ℝ) : ℂ) ^ n *
          Complex.exp (-I * (-I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ))) := by ring
    _ = l p * primeLogThetaLowerClockCoefficient n t p := by
      rw [← primeLogThetaLowerClockCoefficient_eq_strip n t p]

/-- Degree-`n` lower-half source report on the full closed critical-Laplace graph. -/
def primeLogThetaLowerClockClosedGraphEvaluation
    (n : ℕ) (t : ℝ) (ht : 0 < t) :
    primeLogCriticalLaplaceSynthesis.closure.graph →ₗ[ℂ] ℂ where
  toFun z := inner ℂ (primeLogThetaLowerClockReporter n t ht) z.1.1
  map_add' x y := by simp
  map_smul' c x := by simp

/-- The closed-graph report restricts to its literal finite source core. -/
theorem primeLogThetaLowerClockClosedGraphEvaluation_core
    (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : primeLogCriticalLaplaceSynthesis.domain) :
    primeLogThetaLowerClockClosedGraphEvaluation n t ht
      (primeLogCriticalLaplaceClosureCorePoint x) =
      inner ℂ (primeLogThetaLowerClockReporter n t ht)
        (x : primeLogCriticalSourceL2) := by
  rfl

/-- One simultaneous four-level source morphism on the complete closed graph. -/
def primeLogThetaLowerFourLevelClosedGraphEvaluation
    (t : ℝ) (ht : 0 < t) :
    primeLogCriticalLaplaceSynthesis.closure.graph →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun z := fun i => primeLogThetaLowerClockClosedGraphEvaluation i.1 t ht z
  map_add' x y := by
    ext i
    simp [primeLogThetaLowerClockClosedGraphEvaluation]
  map_smul' c x := by
    ext i
    simp [primeLogThetaLowerClockClosedGraphEvaluation]

/-- Coordinate formula for the four-level closed-graph morphism. -/
theorem primeLogThetaLowerFourLevelClosedGraphEvaluation_apply
    (t : ℝ) (ht : 0 < t)
    (z : primeLogCriticalLaplaceSynthesis.closure.graph) (i : Fin 4) :
    primeLogThetaLowerFourLevelClosedGraphEvaluation t ht z i =
      primeLogThetaLowerClockClosedGraphEvaluation i.1 t ht z := rfl

/-- Every lower-half Wronskian level is represented by the corresponding closed-graph source
coordinate, retaining its full Xi power. -/
theorem primeLogThetaStripWronskianIterate_lowerClosedGraphCore
    (n : ℕ) (t : ℝ) (ht : 0 < t) (htstrip : t < 1)
    (x : primeLogCriticalLaplaceSynthesis.domain) :
    primeLogThetaStripWronskianIterate 1 n
      (primeLogThetaFourierLaplace (primeLogCriticalLaplaceCore x)) (-I * (t : ℂ)) =
      XiC (-I * (t : ℂ)) ^ (1 + n) *
        primeLogThetaLowerClockClosedGraphEvaluation n t ht
          (primeLogCriticalLaplaceClosureCorePoint x) := by
  have hw : |(-I * (t : ℂ)).im| < 1 := by
    rw [Complex.mul_im]
    norm_num
    rw [abs_of_nonneg ht.le]
    exact htstrip
  rw [primeLogThetaStripWronskianIterate_thetaFourierLaplace n
    (primeLogCriticalLaplaceCore x) hw,
    primeLogThetaStripSymbol_lower_eq_inner]
  rw [primeLogThetaLowerClockClosedGraphEvaluation_core,
    srcEmb_primeLogCriticalLaplaceCore]

/-- The four-level morphism preserves each Xi level `1` through `4` on literal graph-core
vectors. -/
theorem primeLogThetaStripWronskianIterate_lowerFourLevelClosedGraphCore
    (i : Fin 4) (t : ℝ) (ht : 0 < t) (htstrip : t < 1)
    (x : primeLogCriticalLaplaceSynthesis.domain) :
    primeLogThetaStripWronskianIterate 1 i.1
      (primeLogThetaFourierLaplace (primeLogCriticalLaplaceCore x)) (-I * (t : ℂ)) =
      XiC (-I * (t : ℂ)) ^ (1 + i.1) *
        primeLogThetaLowerFourLevelClosedGraphEvaluation t ht
          (primeLogCriticalLaplaceClosureCorePoint x) i := by
  rw [primeLogThetaLowerFourLevelClosedGraphEvaluation_apply]
  exact primeLogThetaStripWronskianIterate_lowerClosedGraphCore
    i.1 t ht htstrip x

/-- Labelled mixed source term for two retained Wronskian levels. -/
def primeLogThetaLowerFourLevelMixed
    (t : ℝ) (ht : 0 < t)
    (z : primeLogCriticalLaplaceSynthesis.closure.graph) (i j : Fin 4) : ℂ :=
  primeLogThetaLowerFourLevelClosedGraphEvaluation t ht z i *
    star (primeLogThetaLowerFourLevelClosedGraphEvaluation t ht z j)

/-- Every labelled mixed Wronskian term retains the distinct left and right Xi filtration powers
and its exact source cross term. -/
theorem primeLogThetaStripWronskianIterate_lowerFourLevelMixedCore
    (i j : Fin 4) (t : ℝ) (ht : 0 < t) (htstrip : t < 1)
    (x : primeLogCriticalLaplaceSynthesis.domain) :
    primeLogThetaStripWronskianIterate 1 i.1
      (primeLogThetaFourierLaplace (primeLogCriticalLaplaceCore x)) (-I * (t : ℂ)) *
      star (primeLogThetaStripWronskianIterate 1 j.1
        (primeLogThetaFourierLaplace (primeLogCriticalLaplaceCore x)) (-I * (t : ℂ))) =
      (XiC (-I * (t : ℂ)) ^ (1 + i.1) *
        star (XiC (-I * (t : ℂ)) ^ (1 + j.1))) *
        primeLogThetaLowerFourLevelMixed t ht
          (primeLogCriticalLaplaceClosureCorePoint x) i j := by
  rw [primeLogThetaStripWronskianIterate_lowerFourLevelClosedGraphCore
      i t ht htstrip x,
    primeLogThetaStripWronskianIterate_lowerFourLevelClosedGraphCore
      j t ht htstrip x]
  unfold primeLogThetaLowerFourLevelMixed
  rw [star_mul]
  ring

end

end RHTower
