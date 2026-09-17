import GaloisForLFunctions.RHTower.PrimeLogThetaFourLevelLowerClosedGraphLanding

/-!
# Prime-log theta precompletion weighted boundary

The literal real theta axis is outside the dual of the existing critical source
`ℓ²`: its level-`n` coefficient has squared size asymptotic to
`log(p)^(2n+4) / p`.  Route P therefore cannot obtain its boundary by a
continuous scalar reader on the old completed graph.

This module makes the topology-changing alternative precise before that
completion.  Finite source coefficient `l p` is represented by
`sqrt(p) * l p`; equivalently, the precompletion source norm weights the
square of coefficient `p`.  The corresponding level-`n` real-axis dual
coefficient is `2 log(p)^(n+2) / p`, whose squared mass is summable.  The
resulting non-scalar four-level map recovers every literal finite theta symbol,
every labelled mixed term, and the full Xi-filtered Wronskian ladder.

This does not extend through the old Hilbert graph, and does not yet connect
the reweighted precompletion to the escape multiplicity or nuclear budget.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal InnerProduct LinearPMap

namespace RHTower

noncomputable section

/-- The `sqrt(p)` reweighted representative of a finite prime source. -/
def primeLogThetaPrecompletionWeightedCore
    (l : Nat.Primes →₀ ℂ) : primeLogCriticalSourceL2 :=
  ⟨fun p => (Real.sqrt (p : ℝ) : ℂ) * l p, by
    apply memℓp_gen
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (Finset.finite_toSet l.support)
    intro p hp
    by_contra hnot
    have hzero : l p = 0 := Finsupp.notMem_support_iff.mp hnot
    simp [hzero] at hp⟩

/-- Linearity of the precompletion reweighting on literal finite source symbols. -/
def primeLogThetaPrecompletionWeightedCoreLinear :
    (Nat.Primes →₀ ℂ) →ₗ[ℂ] primeLogCriticalSourceL2 where
  toFun := primeLogThetaPrecompletionWeightedCore
  map_add' l m := by
    apply Subtype.ext
    funext p
    change (Real.sqrt (p : ℝ) : ℂ) * (l + m) p =
      (Real.sqrt (p : ℝ) : ℂ) * l p + (Real.sqrt (p : ℝ) : ℂ) * m p
    rw [Finsupp.add_apply]
    ring
  map_smul' c l := by
    apply Subtype.ext
    funext p
    change (Real.sqrt (p : ℝ) : ℂ) * (c • l) p =
      c • ((Real.sqrt (p : ℝ) : ℂ) * l p)
    rw [Finsupp.smul_apply]
    simp only [smul_eq_mul]
    ring

/-- Level-`n` real-axis coefficient dual to the precompletion weighted source. -/
def primeLogThetaPrecompletionWeightedBoundaryCoefficient
    (n : ℕ) (x : ℝ) (p : Nat.Primes) : ℂ :=
  ((2 * Real.log (p : ℝ) ^ (n + 2) / (p : ℝ) : ℝ) : ℂ) *
    Complex.exp (-I * (x : ℂ) * (Real.log (p : ℝ) : ℂ))

/-- Exact square mass of the weighted real-axis boundary coefficient. -/
theorem norm_sq_primeLogThetaPrecompletionWeightedBoundaryCoefficient
    (n : ℕ) (x : ℝ) (p : Nat.Primes) :
    ‖primeLogThetaPrecompletionWeightedBoundaryCoefficient n x p‖ ^ 2 =
      4 * Real.log (p : ℝ) ^ (2 * n + 4) / (p : ℝ) ^ 2 := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hcoeff : 0 < 2 * Real.log (p : ℝ) ^ (n + 2) / (p : ℝ) := by
    positivity
  unfold primeLogThetaPrecompletionWeightedBoundaryCoefficient
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcoeff,
    Complex.norm_exp]
  have hre : (-I * (x : ℂ) * (Real.log (p : ℝ) : ℂ)).re = 0 := by
    have hleft : (-I * (x : ℂ)).re = 0 := by
      rw [Complex.mul_re]
      norm_num
    have hright : (Real.log (p : ℝ) : ℂ).im = 0 := by rfl
    rw [Complex.mul_re, hleft, hright]
    ring
  rw [hre, Real.exp_zero, mul_one]
  field_simp [hp.ne']
  rw [← pow_mul]
  ring_nf

/-- Every real-axis clock degree is an honest dual vector after precompletion weighting. -/
theorem memℓp_primeLogThetaPrecompletionWeightedBoundaryCoefficient
    (n : ℕ) (x : ℝ) :
    Memℓp (primeLogThetaPrecompletionWeightedBoundaryCoefficient n x) 2 := by
  have hnat := HTGeometry.summable_log_pow_div_nat_rpow (2 * n + 4)
    (show (1 : ℝ) < 2 by norm_num)
  have hprime : Summable (fun p : Nat.Primes =>
      Real.log ((p : ℕ) : ℝ) ^ (2 * n + 4) / ((p : ℕ) : ℝ) ^ (2 : ℝ)) :=
    Summable.subtype hnat Nat.Prime
  apply memℓp_gen
  refine (hprime.mul_left (4 : ℝ)).congr fun p => ?_
  norm_num
  rw [norm_sq_primeLogThetaPrecompletionWeightedBoundaryCoefficient]
  rw [← Real.rpow_two]
  ring

/-- Hilbert dual vector realizing a weighted real-axis theta coefficient. -/
def primeLogThetaPrecompletionWeightedBoundaryReporter
    (n : ℕ) (x : ℝ) : primeLogCriticalSourceL2 :=
  ⟨fun p => star (primeLogThetaPrecompletionWeightedBoundaryCoefficient n x p), by
    apply memℓp_gen
    have hsum := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp
      (memℓp_primeLogThetaPrecompletionWeightedBoundaryCoefficient n x)
    simpa only [norm_star] using hsum⟩

/-- Weighted real-axis pairing equals the literal theta symbol, with no reweighting of its value. -/
theorem primeLogThetaPrecompletionWeightedBoundaryReporter_inner_core
    (n : ℕ) (x : ℝ) (l : Nat.Primes →₀ ℂ) :
    inner ℂ (primeLogThetaPrecompletionWeightedBoundaryReporter n x)
      (primeLogThetaPrecompletionWeightedCore l) =
      primeLogThetaStripSymbol n l x := by
  rw [lp.inner_eq_tsum]
  have hsum : (∑' p : Nat.Primes,
      inner ℂ
        ((primeLogThetaPrecompletionWeightedBoundaryReporter n x :
          primeLogCriticalSourceL2) p)
        ((primeLogThetaPrecompletionWeightedCore l : primeLogCriticalSourceL2) p)) =
      ∑ p ∈ l.support,
        inner ℂ
          ((primeLogThetaPrecompletionWeightedBoundaryReporter n x :
            primeLogCriticalSourceL2) p)
          ((primeLogThetaPrecompletionWeightedCore l : primeLogCriticalSourceL2) p) := by
    apply tsum_eq_sum
    intro p hp
    rw [RCLike.inner_apply]
    change (Real.sqrt (p : ℝ) : ℂ) * l p *
      star (primeLogThetaPrecompletionWeightedBoundaryReporter n x p) = 0
    rw [Finsupp.notMem_support_iff.mp hp]
    ring
  rw [hsum, primeLogThetaStripSymbol]
  apply Finset.sum_congr rfl
  intro p hp
  rw [RCLike.inner_apply]
  change (Real.sqrt (p : ℝ) : ℂ) * l p *
      star (star (primeLogThetaPrecompletionWeightedBoundaryCoefficient n x p)) = _
  rw [star_star]
  unfold primeLogThetaPrecompletionWeightedBoundaryCoefficient primeLogThetaStripCoefficient
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hsqrt : Real.sqrt (p : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast p.2.pos)).ne'
  push_cast
  rw [show Complex.log (p : ℂ) ^ (n + 2) =
      Complex.log (p : ℂ) ^ 2 * Complex.log (p : ℂ) ^ n by
    rw [show n + 2 = 2 + n by omega, pow_add]]
  field_simp [hsqrt, hp0]
  have hsquare : (Real.sqrt (p : ℝ) : ℂ) ^ 2 = (p : ℂ) := by
    have hpos' : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
    have hpos : 0 ≤ (p : ℝ) := hpos'.le
    have hreal : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt hpos
    exact_mod_cast hreal
  rw [hsquare]
  field_simp [hpc]

/-- The simultaneous non-scalar boundary reader retaining theta degrees `0` through `3`. -/
def primeLogThetaPrecompletionWeightedBoundaryFourLevel (x : ℝ) :
    primeLogCriticalSourceL2 →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun z := fun i =>
    inner ℂ (primeLogThetaPrecompletionWeightedBoundaryReporter i.1 x) z
  map_add' z w := by
    ext i
    simp
  map_smul' c z := by
    ext i
    simp

/-- Each retained boundary coordinate equals its literal finite theta clock. -/
theorem primeLogThetaPrecompletionWeightedBoundaryFourLevel_apply_core
    (x : ℝ) (l : Nat.Primes →₀ ℂ) (i : Fin 4) :
    primeLogThetaPrecompletionWeightedBoundaryFourLevel x
      (primeLogThetaPrecompletionWeightedCore l) i =
      primeLogThetaStripSymbol i.1 l x := by
  exact primeLogThetaPrecompletionWeightedBoundaryReporter_inner_core i.1 x l

/-- Labelled mixed terms of the four-level boundary preserve both clock labels. -/
def primeLogThetaPrecompletionWeightedBoundaryFourLevelMixed
    (x : ℝ) (l : Nat.Primes →₀ ℂ) (i j : Fin 4) : ℂ :=
  primeLogThetaPrecompletionWeightedBoundaryFourLevel x
      (primeLogThetaPrecompletionWeightedCore l) i *
    star (primeLogThetaPrecompletionWeightedBoundaryFourLevel x
      (primeLogThetaPrecompletionWeightedCore l) j)

theorem primeLogThetaPrecompletionWeightedBoundaryFourLevelMixed_eq_literal
    (x : ℝ) (l : Nat.Primes →₀ ℂ) (i j : Fin 4) :
    primeLogThetaPrecompletionWeightedBoundaryFourLevelMixed x l i j =
      primeLogThetaStripSymbol i.1 l x *
        star (primeLogThetaStripSymbol j.1 l x) := by
  unfold primeLogThetaPrecompletionWeightedBoundaryFourLevelMixed
  rw [primeLogThetaPrecompletionWeightedBoundaryFourLevel_apply_core,
    primeLogThetaPrecompletionWeightedBoundaryFourLevel_apply_core]

/-- The precompletion boundary retains every Xi-filtered Wronskian level on the real axis. -/
theorem primeLogThetaStripWronskianIterate_precompletionWeightedBoundaryFourLevel
    (i : Fin 4) (x : ℝ) (l : Nat.Primes →₀ ℂ) :
    primeLogThetaStripWronskianIterate 1 i.1
      (primeLogThetaFourierLaplace l) x =
      XiC x ^ (1 + i.1) *
        primeLogThetaPrecompletionWeightedBoundaryFourLevel x
          (primeLogThetaPrecompletionWeightedCore l) i := by
  have hx : |(x : ℂ).im| < 1 := by norm_num
  rw [primeLogThetaStripWronskianIterate_thetaFourierLaplace i.1 l hx,
    primeLogThetaPrecompletionWeightedBoundaryFourLevel_apply_core]

end

end RHTower
