import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.TangentPowerSaving
import GaloisForLFunctions.ArithmeticGaugeTheory.TheGaugeExponentIsATailInvariant

/-!
# Absolute tangent summability and linear gauge flows

Joint regularity of an actual gauge family forces its prime velocities to be
absolutely summable at an exponent below one. The proof applies the quadratic
power saving and a weighted Cauchy–Schwarz estimate.

The linear phase flow with these velocities has actual gauge fibres of the
form `ζ exp(H)`, with `H` holomorphic on a fixed half-plane extending left of
one. This statement concerns the linear flow, not arbitrary nonlinear fibres
with the same tangent.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- A quadratic power saving implies absolute prime summability at a smaller saving. -/
theorem summable_absolute_prime_of_energy {a : Nat.Primes → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hs : Summable (fun p : Nat.Primes => a p ^ 2 * (p : ℝ) ^ (-(1 - δ)))) :
    Summable (fun p : Nat.Primes => |a p| * (p : ℝ) ^ (-(1 - δ / 4))) := by
  have hpow (p : Nat.Primes) (b : ℝ) : ((p : ℝ) ^ b) ^ 2 = (p : ℝ) ^ (b * 2) := by
    simpa using (Real.rpow_mul (by positivity : 0 ≤ (p : ℝ)) b (2 : ℝ)).symm
  let f : Nat.Primes → ℝ := fun p => |a p| * (p : ℝ) ^ (-(1 - δ) / 2)
  let g : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-(1 + δ / 2) / 2)
  have hf (p : Nat.Primes) : f p ^ 2 = a p ^ 2 * (p : ℝ) ^ (-(1 - δ)) := by
    dsimp [f]
    rw [mul_pow, sq_abs, hpow]
    congr 2
    ring
  have hg (p : Nat.Primes) : g p ^ 2 = (p : ℝ) ^ (-(1 + δ / 2)) := by
    dsimp [g]
    rw [hpow]
    congr 1
    ring
  have hfs : Summable (fun p => f p ^ 2) := by simpa only [hf] using hs
  have hgs : Summable (fun p => g p ^ 2) := by
    have hh := summable_primeDamping (show 1 < 1 + δ / 2 by linarith only [hδ])
    change Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(1 + δ / 2))) at hh
    simpa only [hg] using hh
  have hp : Summable (fun p => f p * g p) := by
    refine ((hfs.add hgs).div_const 2).of_nonneg_of_le (fun p => by dsimp [f, g]; positivity) ?_
    intro p
    nlinarith only [sq_nonneg (f p - g p)]
  have he (p : Nat.Primes) : f p * g p = |a p| * (p : ℝ) ^ (-(1 - δ / 4)) := by
    dsimp [f, g]
    rw [mul_assoc, ← Real.rpow_add (by exact_mod_cast p.2.pos : (0 : ℝ) < (p : ℝ))]
    congr 2
    ring
  simpa only [he] using hp

/-- Every tangent to an actual jointly regularized family is absolutely prime summable below one. -/
theorem gauge_tangent_absolute_power_saving {x : ℝ → GaugeTorus}
    {u : Nat.Primes → ℂ → ℂ} {U : ℂ × ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hx0 : x 0 = 0)
    (hu : ∀ p, DifferentiableOn ℂ (u p) (ball 0 R))
    (hbd : ∀ p z, z ∈ ball 0 R → ‖u p z‖ ≤ M)
    (hphase : ∀ t : ℝ, |t| < R → ∀ p, u p (t : ℂ) = twist (x t) p)
    (hU : AnalyticAt ℂ U (0, 1))
    (hagree : ∀ σ : ℝ, 1 < σ → σ < 1 + R → ∀ t : ℝ, |t| < R →
      U ((t : ℂ), (σ : ℂ)) = ((σ : ℂ) - 1) * gaugeFibre (x t) (σ : ℂ)) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧
      Summable (fun p : Nat.Primes => |(deriv (u p) 0).im| * (p : ℝ) ^ (-σ)) := by
  obtain ⟨δ, hδ, hδ2, hs⟩ := gauge_tangent_power_saving hR hx0 hu hbd hphase hU hagree
  refine ⟨1 - δ / 4, by linarith only [hδ2], by linarith only [hδ], ?_⟩
  exact summable_absolute_prime_of_energy hδ hs


/-- The real gauge flow with prescribed prime angular velocities. -/
def linearPhaseGauge (a : Nat.Primes → ℝ) (t : ℝ) : GaugeTorus :=
  fun n => if h : n.Prime then
    ((t * a ⟨n, h⟩ / (2 * Real.pi) : ℝ) : UnitAddCircle) else 0

/-- Entire complexification of one prime coordinate of the linear gauge flow. -/
def linearPrimePhase (a : Nat.Primes → ℝ) (p : Nat.Primes) (z : ℂ) : ℂ :=
  Complex.exp ((a p : ℂ) * Complex.I * z)

theorem linearPhaseGauge_zero (a : Nat.Primes → ℝ) : linearPhaseGauge a 0 = 0 := by
  funext n
  simp only [linearPhaseGauge, zero_mul, zero_div, AddCircle.coe_zero, dite_eq_ite,
    ite_self, Pi.zero_apply]

theorem twist_linearPhaseGauge_prime (a : Nat.Primes → ℝ) (t : ℝ) (p : Nat.Primes) :
    twist (linearPhaseGauge a t) p = linearPrimePhase a p (t : ℂ) := by
  rcases p with ⟨p, hp⟩
  rw [ArithmeticGaugeTheory.twist_prime_apply _ hp]
  simp only [linearPhaseGauge, dif_pos hp, fourier_coe_apply, linearPrimePhase]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

theorem differentiable_linearPrimePhase (a : Nat.Primes → ℝ) (p : Nat.Primes) :
    Differentiable ℂ (linearPrimePhase a p) :=
  ((differentiable_const ((a p : ℂ) * Complex.I)).mul differentiable_id).cexp

theorem deriv_linearPrimePhase_zero (a : Nat.Primes → ℝ) (p : Nat.Primes) :
    deriv (linearPrimePhase a p) 0 = (a p : ℂ) * Complex.I := by
  change deriv (fun z : ℂ => Complex.exp ((a p : ℂ) * Complex.I * z)) 0 = _
  have h := ((hasDerivAt_id (0 : ℂ)).const_mul ((a p : ℂ) * Complex.I)).cexp
  simpa only [linearPrimePhase, id_eq, mul_zero, Complex.exp_zero, mul_one, one_mul] using h.deriv

theorem linearPrimePhase_bound {a : Nat.Primes → ℝ} {K R : ℝ}
    (ha : ∀ p, |a p| ≤ K) (p : Nat.Primes) {z : ℂ} (hz : z ∈ ball 0 R) :
    ‖linearPrimePhase a p z‖ ≤ Real.exp (K * R) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (ha p)
  have hzn : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  exact mul_le_mul (ha p) hzn.le (norm_nonneg _) hK

/-- Every real fibre of an absolutely summable linear phase flow is an isozeric Euler deformation. -/
theorem linearPhaseGauge_mem_isozericClass {a : Nat.Primes → ℝ} {K σ : ℝ}
    (ha : ∀ p, |a p| ≤ K)
    (hs : Summable (fun p : Nat.Primes => |a p| * (p : ℝ) ^ (-σ))) (t : ℝ) :
    linearPhaseGauge a t ∈ isozericClass σ := by
  have hb (p : Nat.Primes) : ‖twist (linearPhaseGauge a t) p - 1‖ ≤
      (|t| * Real.exp (K * |t|)) * |a p| := by
    rw [twist_linearPhaseGauge_prime, linearPrimePhase]
    have hTaylor := Complex.norm_exp_sub_sum_le_norm_mul_exp ((a p : ℂ) * I * (t : ℂ)) 1
    have ht : ‖Complex.exp ((a p : ℂ) * I * (t : ℂ)) - 1‖ ≤
        ‖(a p : ℂ) * I * (t : ℂ)‖ * Real.exp ‖(a p : ℂ) * I * (t : ℂ)‖ := by
      simpa [Finset.sum_range_succ, Nat.factorial] using hTaylor
    have hn : ‖(a p : ℂ) * I * (t : ℂ)‖ = |a p| * |t| := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    rw [hn] at ht
    calc _ ≤ (|a p| * |t|) * Real.exp (|a p| * |t|) := ht
         _ ≤ (|a p| * |t|) * Real.exp (K * |t|) :=
           mul_le_mul_of_nonneg_left
             (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (ha p) (abs_nonneg t)))
             (mul_nonneg (abs_nonneg _) (abs_nonneg _))
         _ = _ := by ring
  change Summable (fun p : Nat.Primes =>
    ‖twist (linearPhaseGauge a t) p - 1‖ * (p : ℝ) ^ (-σ))
  refine (hs.mul_left (|t| * Real.exp (K * |t|))).of_nonneg_of_le
    (fun p => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)) ?_
  intro p
  calc _ ≤ ((|t| * Real.exp (K * |t|)) * |a p|) * (p : ℝ) ^ (-σ) :=
         mul_le_mul_of_nonneg_right (hb p) (Real.rpow_nonneg (by positivity) _)
       _ = _ := by ring

theorem linearPhaseGauge_isozeric {a : Nat.Primes → ℝ} {K σ : ℝ}
    (ha : ∀ p, |a p| ≤ K) (hσ : 1 / 2 ≤ σ)
    (hs : Summable (fun p : Nat.Primes => |a p| * (p : ℝ) ^ (-σ))) (t : ℝ) :
    AnalyticOnNhd ℂ (deformationExponent (linearPhaseGauge a t)) {s | σ < s.re} ∧
      ∀ s : ℂ, 1 < s.re → gaugeFibre (linearPhaseGauge a t) s =
        riemannZeta s * Complex.exp (deformationExponent (linearPhaseGauge a t) s) :=
  exists_isozeric hσ (linearPhaseGauge_mem_isozericClass ha hs t)


#print axioms summable_absolute_prime_of_energy
#print axioms gauge_tangent_absolute_power_saving
#print axioms twist_linearPhaseGauge_prime
#print axioms deriv_linearPrimePhase_zero
#print axioms linearPhaseGauge_isozeric
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
