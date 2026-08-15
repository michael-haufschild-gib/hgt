import GaloisForLFunctions.RHTower.RoutePPrimitiveBaseBalancedReflectionCodiagonal
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability

/-!
# Route P primitive base joint-damping wall

P-G184 proves that cubic regularization makes the balanced primitive source/co-source codiagonal
summable. This module determines its exact absolute-convergence chamber. If `s` is the total real
damping of the two biorthogonal legs, the regularized source coefficient is the P-G181 base weight
times `n^(-s)`. The complete prime-depth family is summable exactly when `0 ≤ s`.

Thus the cubic regularizer reaches the functional-equation reflection wall, including its boundary,
but cannot cross into any negative-damping neighborhood by ordinary absolute convergence. The
remaining completed-Xi conormal transport must therefore be a boundary-value, closed-graph, or
other genuinely completed continuation theorem; an ordinary source-series contour crossing is
impossible.
-/

open Complex Matrix Real Filter Topology
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Real regularized primitive weight at total joint damping `s`. -/
def routePPrimitiveBaseJointDampingWeight
    (s : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  routePPrimitiveBaseCauchyCubicWeight pe *
    (xiGammaEulerValuationNat pe : ℝ) ^ (-s)

/-- Literal two-leg source codiagonal: source damping `a+s` and co-source damping `-a` have total
damping `s`; the base Cauchy self-kernel is inserted before summation. -/
def routePPrimitiveBaseJointDampingCodiagonal
    (a s : ℝ) (pe : Nat.Primes × ℕ) : ℂ :=
  routePBaseCauchyCubicKernel 1
      (xiGammaEulerPrimitiveLogFrequency pe)
      (xiGammaEulerPrimitiveLogFrequency pe) 0 *
    (xiGammaEulerPrimitiveCommonTestSourceCoeff ((a + s : ℝ) : ℂ) pe *
      star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff (-a : ℂ) pe))

/-- The actual biorthogonal source codiagonal is the real joint-damping weight. It depends only on
the total damping `s`, not on how damping is distributed between the two legs. -/
theorem routePPrimitiveBaseJointDampingCodiagonal_eq_weight
    (a s : ℝ) (pe : Nat.Primes × ℕ) :
    routePPrimitiveBaseJointDampingCodiagonal a s pe =
      (routePPrimitiveBaseJointDampingWeight s pe : ℂ) := by
  have hn : xiGammaEulerValuationNat pe ≠ 0 := by
    unfold xiGammaEulerValuationNat
    exact pow_ne_zero _ pe.1.property.ne_zero
  have hn0 : (0 : ℝ) ≤ (xiGammaEulerValuationNat pe : ℝ) := by positivity
  have hparam :
      (((a + s : ℝ) : ℂ) + star (-((a : ℝ) : ℂ)) + 1) = ((s + 1 : ℝ) : ℂ) := by
    push_cast
    simp
  have hterm :
      LSeries.term
          (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
          ((s + 1 : ℝ) : ℂ) (xiGammaEulerValuationNat pe) =
        LSeries.term
            (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
            1 (xiGammaEulerValuationNat pe) *
          (((xiGammaEulerValuationNat pe : ℂ) ^ (s : ℂ))⁻¹) := by
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [show ((s + 1 : ℝ) : ℂ) = (s : ℂ) + 1 by push_cast; rfl]
    rw [Complex.cpow_add (s : ℂ) 1 (Nat.cast_ne_zero.mpr hn)]
    rw [Complex.cpow_one]
    field_simp
  have hcpow :
      (((xiGammaEulerValuationNat pe : ℂ) ^ (s : ℂ))⁻¹) =
        (((xiGammaEulerValuationNat pe : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [show (xiGammaEulerValuationNat pe : ℂ) =
      (((xiGammaEulerValuationNat pe : ℝ) : ℂ)) by norm_num,
      ← Complex.ofReal_cpow hn0, ← Complex.ofReal_inv, ← Real.rpow_neg]
    exact hn0
  rw [routePPrimitiveBaseJointDampingCodiagonal,
    xiGammaEulerPrimitiveCommonTestSourceCoeff_mul_star_coSourceCoeff_eq_term,
    hparam, hterm, hcpow]
  have hzero := routePPrimitiveBaseBalancedReflectionCodiagonal_eq_weight 0 pe
  rw [routePPrimitiveBaseBalancedReflectionCodiagonal,
    xiGammaEulerPrimitiveCommonTestSourceCoeff_mul_star_coSourceCoeff_eq_term] at hzero
  simp only [ofReal_zero, neg_zero, star_zero, zero_add] at hzero
  rw [routePPrimitiveBaseJointDampingWeight]
  push_cast
  rw [← hzero]
  ring

theorem routePPrimitiveBaseJointDampingWeight_nonneg
    (s : ℝ) (pe : Nat.Primes × ℕ) :
    0 ≤ routePPrimitiveBaseJointDampingWeight s pe := by
  exact mul_nonneg (routePPrimitiveBaseCauchyCubicWeight_nonneg pe)
    (Real.rpow_nonneg (by positivity) _)

/-- The whole joint-damping source is summable throughout the closed nonnegative chamber. -/
theorem summable_routePPrimitiveBaseJointDampingWeight_of_nonneg
    {s : ℝ} (hs : 0 ≤ s) :
    Summable (routePPrimitiveBaseJointDampingWeight s) := by
  refine Summable.of_nonneg_of_le
    (routePPrimitiveBaseJointDampingWeight_nonneg s) ?_
    summable_routePPrimitiveBaseCauchyCubicWeight
  intro pe
  rw [routePPrimitiveBaseJointDampingWeight]
  have hn1 : (1 : ℝ) ≤ (xiGammaEulerValuationNat pe : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      unfold xiGammaEulerValuationNat
      exact pow_ne_zero _ pe.1.property.ne_zero)
  have hr : (xiGammaEulerValuationNat pe : ℝ) ^ (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  exact mul_le_of_le_one_right (routePPrimitiveBaseCauchyCubicWeight_nonneg pe) hr

/-- Exact depth-zero prime slice of the joint-damping weight. -/
theorem routePPrimitiveBaseJointDampingWeight_prime_zero
    (s : ℝ) (p : Nat.Primes) :
    routePPrimitiveBaseJointDampingWeight s (p, 0) =
      (1 / (4 * (p : ℝ) * Real.log (p : ℝ) ^ 2)) * (p : ℝ) ^ (-s) := by
  rw [routePPrimitiveBaseJointDampingWeight,
    routePPrimitiveBaseCauchyCubicWeight,
    xiGammaEulerPrimitiveCubicLogMomentWeight, invNatLogSq]
  simp only [xiGammaEulerValuationNat, pow_one, Nat.cast_zero, zero_add,
    one_pow, inv_one]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'
  field_simp [hp.ne', hlog]
  ring

/-- Every negative joint damping diverges already on the depth-zero prime face. -/
theorem not_summable_routePPrimitiveBaseJointDampingWeight_of_neg
    {s : ℝ} (hs : s < 0) :
    ¬ Summable (routePPrimitiveBaseJointDampingWeight s) := by
  intro hsum
  have hprime : Summable (fun p : Nat.Primes =>
      routePPrimitiveBaseJointDampingWeight s (p, 0)) :=
    hsum.comp_injective (fun p q h => by exact congrArg Prod.fst h)
  have hδ : 0 < -s := neg_pos.mpr hs
  obtain ⟨N₀, hN₀⟩ :=
    (burnolEventually_log_pow_le_rpow hδ 2).exists_forall_of_atTop
  let N : ℕ := max 3 ⌈N₀⌉₊
  set t : Set Nat.Primes := {p : Nat.Primes | (p : ℕ) < N} with ht
  have htfin : t.Finite :=
    Set.Finite.preimage (Subtype.val_injective.injOn) (Set.finite_Iio N)
  have hsub : Summable (fun x : ↥tᶜ =>
      routePPrimitiveBaseJointDampingWeight s ((x : Nat.Primes), 0)) :=
    hprime.subtype _
  have hcomp : Summable (fun x : ↥tᶜ => (1 / 4 : ℝ) *
      (1 / (((x : Nat.Primes) : ℕ) : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) ?_ hsub
    rintro ⟨p, hp⟩
    have hpN : N ≤ (p : ℕ) := by
      have : ¬ ((p : ℕ) < N) := hp
      omega
    have hpN₀ : N₀ ≤ ((p : ℕ) : ℝ) := by
      refine le_trans (Nat.le_ceil N₀) ?_
      exact_mod_cast le_trans (le_max_right 3 ⌈N₀⌉₊) hpN
    have hlog := hN₀ ((p : ℕ) : ℝ) hpN₀
    change (1 / 4 : ℝ) * (1 / (p : ℝ)) ≤
      routePPrimitiveBaseJointDampingWeight s (p, 0)
    rw [routePPrimitiveBaseJointDampingWeight_prime_zero]
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
    have hlogpos : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.property.one_lt)
    have hmul : Real.log (p : ℝ) ^ 2 ≤ (p : ℝ) ^ (-s) := hlog
    calc
      (1 / 4 : ℝ) * (1 / (p : ℝ)) =
          (1 / (4 * (p : ℝ) * Real.log (p : ℝ) ^ 2)) *
            Real.log (p : ℝ) ^ 2 := by field_simp
      _ ≤ (1 / (4 * (p : ℝ) * Real.log (p : ℝ) ^ 2)) *
            (p : ℝ) ^ (-s) := by
        exact mul_le_mul_of_nonneg_left hmul (by positivity)
  have hone : Summable (fun x : ↥tᶜ =>
      1 / (((x : Nat.Primes) : ℕ) : ℝ)) := by
    have h := hcomp.mul_left 4
    refine h.congr fun x => ?_
    ring
  exact burnolNotSummable_prime_one_div ((Set.Finite.summable_compl_iff htfin).mp hone)

/-- **P-G185, real form.** Cubic regularization has the exact closed joint-damping chamber
`s ≥ 0`. -/
theorem summable_routePPrimitiveBaseJointDampingWeight_iff
    (s : ℝ) :
    Summable (routePPrimitiveBaseJointDampingWeight s) ↔ 0 ≤ s := by
  constructor
  · intro h
    by_contra hs
    exact not_summable_routePPrimitiveBaseJointDampingWeight_of_neg
      (lt_of_not_ge hs) h
  · exact summable_routePPrimitiveBaseJointDampingWeight_of_nonneg

/-- **P-G185, source form.** The literal regularized biorthogonal codiagonal is absolutely
summable exactly on the same closed chamber, independently of damping split `a`. -/
theorem summable_routePPrimitiveBaseJointDampingCodiagonal_iff
    (a s : ℝ) :
    Summable (routePPrimitiveBaseJointDampingCodiagonal a s) ↔ 0 ≤ s := by
  rw [← summable_routePPrimitiveBaseJointDampingWeight_iff s]
  constructor
  · intro h
    exact h.norm.congr fun pe => by
      rw [routePPrimitiveBaseJointDampingCodiagonal_eq_weight,
        norm_real, Real.norm_eq_abs,
        abs_of_nonneg (routePPrimitiveBaseJointDampingWeight_nonneg s pe)]
  · intro h
    have hc : Summable (fun pe : Nat.Primes × ℕ =>
        (routePPrimitiveBaseJointDampingWeight s pe : ℂ)) :=
      h.map Complex.ofRealCLM Complex.ofRealCLM.continuous
    exact hc.congr fun pe =>
      (routePPrimitiveBaseJointDampingCodiagonal_eq_weight a s pe).symm

end

end RHTower
