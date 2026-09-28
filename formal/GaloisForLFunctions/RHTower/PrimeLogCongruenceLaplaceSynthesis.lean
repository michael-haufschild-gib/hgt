import GaloisForLFunctions.RHTower.PrimeLogCubicLaplaceGraphFormation
import GaloisForLFunctions.RHTower.PrimeLogCongruenceIdealExit
import GaloisForLFunctions.RHTower.PrimeLogCriticalCubicKernelNoBoundedOperator
import GaloisForLFunctions.RHTower.PolynomialFockAdaptedTangentPacketSynthesis
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator
import GaloisForLFunctions.HTGeometry.CompactFourierEntire
import GaloisForLFunctions.Hurwitz.ExpIndependence

/-!
# Prime-log congruence Laplace synthesis: Gram law, Hilbert--Schmidt wall, and critical endpoint

Companion to `PrimeLogCubicLaplaceGraphFormation` (ULF-PCLGF-001).  For `d > 0`, `0 ≤ u ≤ d`,
primes `p` and `t > 0` the congruence features are

`ψ_{d,u,p}(t) = 2 t √(w_{d,u}(p)) (log p)^{3/2} p^{-t}`,
`w_{d,u}(p) = 8 d log p · p^{-(1 + 2(d-u))}`.

This module proves

* (PCLGF.2) the exact prime-mixed cubic Gram law
  `⟨ψ_{d,u,p}, ψ_{d,u,q}⟩ = √(w_p w_q) (2√(log p log q)/(log p + log q))³`;
* (PCLGF.3) `‖ψ_{d,u,p}‖² = w_{d,u}(p)`;
* the synthesis `c ↦ ∑ c_p ψ_{d,u,p}` extends to a Hilbert--Schmidt operator on `ℓ²(Primes)`
  exactly when `u < d`;
* (PCLGF.4) at `u = d` the features are `√(8d)` times the literal critical columns, whose Gram is
  the raw critical cubic kernel of ULF-PLCCKU-001; hence the critical synthesis `A_*` has no
  bounded extension to `ℓ²(Primes)`;
* the critical synthesis is injective on its finite-prime source core.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal InnerProductSpace

namespace RHTower

noncomputable section

/-! ## Scalar identities -/

theorem primeLogCriticalWeight_pos (p : Nat.Primes) : 0 < primeLogCriticalWeight p :=
  div_pos (Real.log_pos (by exact_mod_cast p.property.one_lt))
    (by exact_mod_cast p.property.pos)

/-- `w_{d,u}(p) = 8 d · (p^{u-d})² · (log p / p)`. -/
theorem primeLogCongruenceWeight_eq_critical {d : ℝ} (hd : 0 < d) (u : ℝ) (p : Nat.Primes) :
    primeLogCongruenceWeight d u p =
      8 * d * ((p : ℝ) ^ (u - d)) ^ 2 * primeLogCriticalWeight p := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hpow : (p : ℝ) ^ (-(1 + 2 * (d - u))) = ((p : ℝ) ^ (u - d)) ^ 2 * (p : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_neg_one, ← Real.rpow_add hp]
    congr 1
    push_cast
    ring
  rw [primeLogCongruenceWeight_eq hd, hpow, primeLogCriticalWeight]
  field_simp

/-- `√(w_{d,u}(p)) = √(8d) · p^{u-d} · √(log p / p)`. -/
theorem sqrt_primeLogCongruenceWeight {d : ℝ} (hd : 0 < d) (u : ℝ) (p : Nat.Primes) :
    Real.sqrt (primeLogCongruenceWeight d u p) =
      Real.sqrt (8 * d) * (p : ℝ) ^ (u - d) * Real.sqrt (primeLogCriticalWeight p) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hpow : 0 ≤ (p : ℝ) ^ (u - d) := Real.rpow_nonneg hp.le _
  rw [primeLogCongruenceWeight_eq_critical hd, Real.sqrt_mul
      (mul_nonneg (by positivity) (sq_nonneg _)),
    Real.sqrt_mul (by positivity), Real.sqrt_sq hpow]

/-- The raw critical kernel written in closed form. -/
theorem primeLogCriticalCubicKernel_eq (p q : Nat.Primes) :
    primeLogCriticalCubicKernel p q =
      8 * Real.log (p : ℝ) ^ 2 * Real.log (q : ℝ) ^ 2 /
        (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          (Real.log (p : ℝ) + Real.log (q : ℝ)) ^ 3) := by
  have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hlq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast q.property.one_lt)
  have hsp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast p.property.pos)
  have hsq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast q.property.pos)
  unfold primeLogCriticalCubicKernel primeLogCriticalWeight primeLogCriticalCubicCorrelation
  rw [Real.sqrt_mul (div_nonneg hlp.le (Nat.cast_nonneg _)),
    Real.sqrt_div hlp.le, Real.sqrt_div hlq.le, Real.sqrt_mul hlp.le]
  set a := Real.sqrt (Real.log (p : ℝ)) with ha
  set b := Real.sqrt (Real.log (q : ℝ)) with hb
  have ha2 : a ^ 2 = Real.log (p : ℝ) := Real.sq_sqrt hlp.le
  have hb2 : b ^ 2 = Real.log (q : ℝ) := Real.sq_sqrt hlq.le
  rw [← ha2, ← hb2]
  have hsum : 0 < a ^ 2 + b ^ 2 := by rw [ha2, hb2]; exact add_pos hlp hlq
  field_simp
  ring

/-- The critical Laplace Gram is the raw critical cubic kernel. -/
theorem integral_primeLogCriticalLaplaceFeature_mul_eq_kernel (p q : Nat.Primes) :
    (∫ t : ℝ in Ioi 0,
      primeLogCriticalLaplaceFeature p t * primeLogCriticalLaplaceFeature q t) =
      primeLogCriticalCubicKernel p q := by
  rw [integral_primeLogCriticalLaplaceFeature_mul, primeLogCriticalCubicKernel_eq]

theorem primeLogCriticalCubicCorrelation_self (p : Nat.Primes) :
    primeLogCriticalCubicCorrelation p p = 1 := by
  have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  unfold primeLogCriticalCubicCorrelation
  rw [Real.sqrt_mul_self hlp.le]
  field_simp
  norm_num

theorem primeLogCriticalCubicKernel_self (p : Nat.Primes) :
    primeLogCriticalCubicKernel p p = primeLogCriticalWeight p := by
  rw [primeLogCriticalCubicKernel, primeLogCriticalCubicCorrelation_self, mul_one,
    Real.sqrt_mul_self (primeLogCriticalWeight_nonneg p)]

/-! ## The congruence features -/

/-- The congruence Laplace feature `ψ_{d,u,p}(t) = 2 t √w_{d,u}(p) (log p)^{3/2} p^{-t}`. -/
def primeLogCongruenceLaplaceFeature (d u : ℝ) (p : Nat.Primes) (t : ℝ) : ℝ :=
  2 * t * Real.sqrt (primeLogCongruenceWeight d u p) * Real.sqrt (Real.log (p : ℝ)) ^ 3 *
    Real.exp (-(Real.log (p : ℝ) * t))

/-- The congruence feature is the critical feature scaled by `√(8d) p^{u-d}`. -/
theorem primeLogCongruenceLaplaceFeature_eq {d : ℝ} (hd : 0 < d) (u : ℝ) (p : Nat.Primes)
    (t : ℝ) :
    primeLogCongruenceLaplaceFeature d u p t =
      Real.sqrt (8 * d) * (p : ℝ) ^ (u - d) * primeLogCriticalLaplaceFeature p t := by
  have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  unfold primeLogCongruenceLaplaceFeature primeLogCriticalLaplaceFeature
  rw [sqrt_primeLogCongruenceWeight hd, primeLogCriticalWeight,
    Real.sqrt_div hlp.le]
  have ha2 : Real.sqrt (Real.log (p : ℝ)) ^ 2 = Real.log (p : ℝ) := Real.sq_sqrt hlp.le
  have h4 : Real.log (p : ℝ) ^ 2 = Real.sqrt (Real.log (p : ℝ)) ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, ha2]
  have hsp : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast p.property.pos)
  rw [h4]
  field_simp

/-- **(PCLGF.2)** Exact prime-mixed cubic Gram law of the congruence features. -/
theorem integral_primeLogCongruenceLaplaceFeature_mul {d : ℝ} (hd : 0 < d) (u : ℝ)
    (p q : Nat.Primes) :
    (∫ t : ℝ in Ioi 0,
      primeLogCongruenceLaplaceFeature d u p t * primeLogCongruenceLaplaceFeature d u q t) =
      Real.sqrt (primeLogCongruenceWeight d u p * primeLogCongruenceWeight d u q) *
        (2 * Real.sqrt (Real.log (p : ℝ) * Real.log (q : ℝ)) /
          (Real.log (p : ℝ) + Real.log (q : ℝ))) ^ 3 := by
  simp_rw [primeLogCongruenceLaplaceFeature_eq hd]
  rw [show (fun t => Real.sqrt (8 * d) * (p : ℝ) ^ (u - d) * primeLogCriticalLaplaceFeature p t *
        (Real.sqrt (8 * d) * (q : ℝ) ^ (u - d) * primeLogCriticalLaplaceFeature q t)) =
      fun t => (Real.sqrt (8 * d) * (p : ℝ) ^ (u - d) *
        (Real.sqrt (8 * d) * (q : ℝ) ^ (u - d))) *
        (primeLogCriticalLaplaceFeature p t * primeLogCriticalLaplaceFeature q t) by
      funext t; ring,
    integral_const_mul, integral_primeLogCriticalLaplaceFeature_mul_eq_kernel,
    Real.sqrt_mul (primeLogCongruenceWeight_nonneg hd p), sqrt_primeLogCongruenceWeight hd,
    sqrt_primeLogCongruenceWeight hd, primeLogCriticalCubicKernel,
    Real.sqrt_mul (primeLogCriticalWeight_nonneg p), primeLogCriticalCubicCorrelation]
  ring

/-- **(PCLGF.3)** `‖ψ_{d,u,p}‖² = w_{d,u}(p)`. -/
theorem integral_primeLogCongruenceLaplaceFeature_sq {d : ℝ} (hd : 0 < d) (u : ℝ)
    (p : Nat.Primes) :
    (∫ t : ℝ in Ioi 0, primeLogCongruenceLaplaceFeature d u p t ^ 2) =
      primeLogCongruenceWeight d u p := by
  simp_rw [sq]
  rw [integral_primeLogCongruenceLaplaceFeature_mul hd,
    Real.sqrt_mul_self (primeLogCongruenceWeight_nonneg hd p)]
  have := primeLogCriticalCubicCorrelation_self p
  unfold primeLogCriticalCubicCorrelation at this
  rw [this, mul_one]

/-- **(PCLGF.4)** At the wall `u = d` the congruence feature is `√(8d)` times the literal
critical column `2 t (log p)² p^{-t-1/2}`. -/
theorem primeLogCongruenceLaplaceFeature_critical {d : ℝ} (hd : 0 < d) (p : Nat.Primes)
    (t : ℝ) :
    primeLogCongruenceLaplaceFeature d d p t =
      Real.sqrt (8 * d) * primeLogCriticalLaplaceFeature p t := by
  rw [primeLogCongruenceLaplaceFeature_eq hd, sub_self, Real.rpow_zero, mul_one]

/-- The squared column norms of the congruence synthesis are summable exactly below the wall. -/
theorem summable_integral_primeLogCongruenceLaplaceFeature_sq_iff {d u : ℝ} (hd : 0 < d)
    (hu : 0 ≤ u) :
    Summable (fun p : Nat.Primes =>
      ∫ t : ℝ in Ioi 0, primeLogCongruenceLaplaceFeature d u p t ^ 2) ↔ u < d := by
  simp_rw [integral_primeLogCongruenceLaplaceFeature_sq hd]
  exact summable_primeLogCongruenceWeight_iff hd hu

/-! ## `L²` columns -/

/-- `L²` column of the congruence synthesis. -/
def primeLogCongruenceLaplaceColumn (d u : ℝ) (p : Nat.Primes) : primeLogCriticalHalfLineL2 :=
  ((Real.sqrt (8 * d) * (p : ℝ) ^ (u - d) : ℝ) : ℂ) • primeLogCriticalLaplaceFeatureL2 p

theorem primeLogCongruenceLaplaceColumn_ae {d : ℝ} (hd : 0 < d) (u : ℝ) (p : Nat.Primes) :
    (primeLogCongruenceLaplaceColumn d u p : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t => (primeLogCongruenceLaplaceFeature d u p t : ℂ) := by
  filter_upwards [Lp.coeFn_smul ((Real.sqrt (8 * d) * (p : ℝ) ^ (u - d) : ℝ) : ℂ)
      (primeLogCriticalLaplaceFeatureL2 p),
    primeLogCriticalLaplaceFeatureL2_ae p] with t h1 h2
  rw [primeLogCongruenceLaplaceColumn, h1, Pi.smul_apply, h2, smul_eq_mul,
    primeLogCongruenceLaplaceFeature_eq hd, primeLogCriticalLaplaceFeatureC]
  push_cast
  ring

/-- `L²` inner products of critical columns are the raw critical cubic kernel. -/
theorem inner_primeLogCriticalLaplaceFeatureL2 (p q : Nat.Primes) :
    ⟪primeLogCriticalLaplaceFeatureL2 p, primeLogCriticalLaplaceFeatureL2 q⟫_ℂ =
      (primeLogCriticalCubicKernel p q : ℂ) := by
  rw [MeasureTheory.L2.inner_def, ← integral_primeLogCriticalLaplaceFeature_mul_eq_kernel,
    ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [primeLogCriticalLaplaceFeatureL2_ae p,
    primeLogCriticalLaplaceFeatureL2_ae q] with t hp hq
  rw [hp, hq, primeLogCriticalLaplaceFeatureC, primeLogCriticalLaplaceFeatureC,
    RCLike.inner_apply, Complex.conj_ofReal]
  push_cast
  ring

/-- `L²` inner products of congruence columns: the Gram law (PCLGF.2) in `L²`. -/
theorem inner_primeLogCongruenceLaplaceColumn {d : ℝ} (hd : 0 < d) (u : ℝ)
    (p q : Nat.Primes) :
    ⟪primeLogCongruenceLaplaceColumn d u p, primeLogCongruenceLaplaceColumn d u q⟫_ℂ =
      ((Real.sqrt (primeLogCongruenceWeight d u p * primeLogCongruenceWeight d u q) *
        primeLogCriticalCubicCorrelation p q : ℝ) : ℂ) := by
  rw [primeLogCongruenceLaplaceColumn, primeLogCongruenceLaplaceColumn, inner_smul_left,
    inner_smul_right, inner_primeLogCriticalLaplaceFeatureL2, Complex.conj_ofReal,
    Real.sqrt_mul (primeLogCongruenceWeight_nonneg hd p), sqrt_primeLogCongruenceWeight hd,
    sqrt_primeLogCongruenceWeight hd, primeLogCriticalCubicKernel,
    Real.sqrt_mul (primeLogCriticalWeight_nonneg p)]
  push_cast
  ring

theorem norm_sq_primeLogCongruenceLaplaceColumn {d : ℝ} (hd : 0 < d) (u : ℝ)
    (p : Nat.Primes) :
    ‖primeLogCongruenceLaplaceColumn d u p‖ ^ 2 = primeLogCongruenceWeight d u p := by
  have h := inner_primeLogCongruenceLaplaceColumn hd u p p
  rw [inner_self_eq_norm_sq_to_K, primeLogCriticalCubicCorrelation_self, mul_one,
    Real.sqrt_mul_self (primeLogCongruenceWeight_nonneg hd p)] at h
  have h' : ((‖primeLogCongruenceLaplaceColumn d u p‖ ^ 2 : ℝ) : ℂ) =
      ((primeLogCongruenceWeight d u p : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow]; exact h
  exact Complex.ofReal_injective h'

/-! ## Hilbert--Schmidt wall -/

theorem summable_norm_inner_primeLogCongruenceLaplaceColumn_sq {d u : ℝ} (hd : 0 < d)
    (hsum : Summable (primeLogCongruenceWeight d u)) (x : primeLogCriticalHalfLineL2) :
    Summable fun p : Nat.Primes =>
      ‖⟪primeLogCongruenceLaplaceColumn d u p, x⟫_ℂ‖ ^ (2 : ℝ) := by
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_)
    (hsum.mul_right (‖x‖ ^ 2))
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← norm_sq_primeLogCongruenceLaplaceColumn hd, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

theorem primeLogCongruenceLaplaceColumn_bessel {d u : ℝ} (hd : 0 < d)
    (hsum : Summable (primeLogCongruenceWeight d u)) (x : primeLogCriticalHalfLineL2) :
    (∑' p : Nat.Primes, ‖⟪primeLogCongruenceLaplaceColumn d u p, x⟫_ℂ‖ ^ (2 : ℝ)) ≤
      (Real.sqrt (∑' p, primeLogCongruenceWeight d u p) * ‖x‖) ^ (2 : ℝ) := by
  have hterm (p : Nat.Primes) :
      ‖⟪primeLogCongruenceLaplaceColumn d u p, x⟫_ℂ‖ ^ (2 : ℝ) ≤
        primeLogCongruenceWeight d u p * ‖x‖ ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ← norm_sq_primeLogCongruenceLaplaceColumn hd, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  have htsum_nonneg : 0 ≤ ∑' p, primeLogCongruenceWeight d u p :=
    tsum_nonneg fun p => primeLogCongruenceWeight_nonneg hd p
  calc (∑' p : Nat.Primes, ‖⟪primeLogCongruenceLaplaceColumn d u p, x⟫_ℂ‖ ^ (2 : ℝ))
      ≤ ∑' p, primeLogCongruenceWeight d u p * ‖x‖ ^ 2 :=
        (summable_norm_inner_primeLogCongruenceLaplaceColumn_sq hd hsum x).tsum_le_tsum hterm
          (hsum.mul_right _)
    _ = (∑' p, primeLogCongruenceWeight d u p) * ‖x‖ ^ 2 := tsum_mul_right
    _ = (Real.sqrt (∑' p, primeLogCongruenceWeight d u p) * ‖x‖) ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_pow,
          Real.sq_sqrt htsum_nonneg]

/-- Below the wall, the congruence synthesis as a bounded operator on `ℓ²(Primes)`. -/
def primeLogCongruenceLaplaceSynthesisOp {d u : ℝ} (hd : 0 < d)
    (hsum : Summable (primeLogCongruenceWeight d u)) :
    lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] primeLogCriticalHalfLineL2 :=
  besselFamilySynthesisOperator (primeLogCongruenceLaplaceColumn d u)
    (summable_norm_inner_primeLogCongruenceLaplaceColumn_sq hd hsum) (Real.sqrt_nonneg _)
    (primeLogCongruenceLaplaceColumn_bessel hd hsum)

theorem primeLogCongruenceLaplaceSynthesisOp_single {d u : ℝ} (hd : 0 < d)
    (hsum : Summable (primeLogCongruenceWeight d u)) (p : Nat.Primes) :
    primeLogCongruenceLaplaceSynthesisOp hd hsum (lp.single 2 p 1) =
      primeLogCongruenceLaplaceColumn d u p := by
  rw [← HTGeometry.ellTwoCoordinateBasis_apply]
  exact besselFamilySynthesisOperator_coordinateBasis _ _ _ _ p

/-- **Hilbert--Schmidt wall.**  The congruence synthesis extends to a Hilbert--Schmidt operator on
`ℓ²(Primes)` exactly when `u < d`. -/
theorem exists_hilbertSchmidt_primeLogCongruenceLaplaceSynthesis_iff {d u : ℝ} (hd : 0 < d)
    (hu : 0 ≤ u) :
    (∃ A : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] primeLogCriticalHalfLineL2,
        (∀ p, A (lp.single 2 p 1) = primeLogCongruenceLaplaceColumn d u p) ∧
          ContinuousLinearMap.IsHilbertSchmidt A) ↔ u < d := by
  constructor
  · rintro ⟨A, hA, hHS⟩
    rw [← summable_primeLogCongruenceWeight_iff hd hu]
    have h := hHS.summable (HilbertSchmidt.lpBasis Nat.Primes)
    simp_rw [HilbertSchmidt.lpBasis_apply, hA, norm_sq_primeLogCongruenceLaplaceColumn hd] at h
    exact h
  · intro hud
    have hsum := (summable_primeLogCongruenceWeight_iff hd hu).2 hud
    refine ⟨primeLogCongruenceLaplaceSynthesisOp hd hsum,
      primeLogCongruenceLaplaceSynthesisOp_single hd hsum, ?_⟩
    apply ContinuousLinearMap.isHilbertSchmidt_of_summable (HilbertSchmidt.lpBasis Nat.Primes)
    simp_rw [HilbertSchmidt.lpBasis_apply, primeLogCongruenceLaplaceSynthesisOp_single,
      norm_sq_primeLogCongruenceLaplaceColumn hd]
    exact hsum

/-! ## The critical endpoint has no bounded extension -/

/-- No bounded operator on `ℓ²(Primes)` sends `e_p` to the critical columns: its Gram would be a
bounded operator with the raw critical cubic kernel as matrix. -/
theorem not_exists_bounded_primeLogCriticalLaplaceColumns :
    ¬ ∃ A : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] primeLogCriticalHalfLineL2,
      ∀ p, A (lp.single 2 p 1) = primeLogCriticalLaplaceFeatureL2 p := by
  rintro ⟨A, hA⟩
  apply not_exists_bounded_operator_primeLogCriticalCubicKernel (𝕜 := ℂ)
  refine ⟨ContinuousLinearMap.adjoint A ∘L A, fun p q => ?_⟩
  have hcoord : ∀ x : lp (fun _ : Nat.Primes => ℂ) 2,
      x p = ⟪(lp.single 2 p (1 : ℂ) : lp (fun _ : Nat.Primes => ℂ) 2), x⟫_ℂ := by
    intro x
    simp [lp.inner_single_left]
  rw [hcoord, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, hA, hA,
    inner_primeLogCriticalLaplaceFeatureL2]
  rfl

/-- **(PCLGF.4)** The critical synthesis `A_*` has no bounded extension. -/
theorem primeLogCriticalLaplaceSynthesis_no_bounded_extension :
    ¬ ∃ B : primeLogCriticalSourceL2 →L[ℂ] primeLogCriticalHalfLineL2,
      ∀ x : primeLogCriticalLaplaceSynthesis.domain,
        B x = primeLogCriticalLaplaceSynthesis x := by
  rintro ⟨B, hB⟩
  apply not_exists_bounded_primeLogCriticalLaplaceColumns
  refine ⟨B, fun p => ?_⟩
  have hmem : HTGeometry.ConstraintMotiveRelativity.srcEmb (Finsupp.single p (1 : ℂ)) ∈
      LinearMap.range (HTGeometry.ConstraintMotiveRelativity.srcEmb (P := Nat.Primes)) :=
    ⟨_, rfl⟩
  have h := hB ⟨_, hmem⟩
  rw [primeLogCriticalLaplaceSynthesis_apply, primeLogCriticalLaplaceMass] at h
  simp only [HTGeometry.ConstraintMotiveRelativity.srcEmb_single, one_smul,
    Finsupp.linearCombination_single] at h
  exact h

/-- The same wall for the congruence columns at `u = d`: no bounded extension. -/
theorem not_exists_bounded_primeLogCongruenceLaplaceColumn_critical {d : ℝ} (hd : 0 < d) :
    ¬ ∃ A : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] primeLogCriticalHalfLineL2,
      ∀ p, A (lp.single 2 p 1) = primeLogCongruenceLaplaceColumn d d p := by
  rintro ⟨A, hA⟩
  have hc : (Real.sqrt (8 * d) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by linarith)).ne'
  apply not_exists_bounded_primeLogCriticalLaplaceColumns
  refine ⟨(Real.sqrt (8 * d) : ℂ)⁻¹ • A, fun p => ?_⟩
  rw [smul_apply, hA, primeLogCongruenceLaplaceColumn, sub_self,
    Real.rpow_zero, mul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-! ## Source faithfulness -/

/-- **Source faithfulness.**  The literal critical synthesis is injective on its finite-prime
source core. -/
theorem primeLogCriticalLaplaceMass_injective :
    Function.Injective primeLogCriticalLaplaceMass := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro l hl
  -- transport the finite support to `Fin n`
  set s := l.support
  let e := s.equivFin
  let n := s.card
  let prm : Fin n → Nat.Primes := fun i => (e.symm i : Nat.Primes)
  have hprm : Function.Injective prm := fun i j hij => e.symm.injective (Subtype.ext hij)
  have hzeroAE :
      (fun t : ℝ => ∑ p ∈ s, l p * primeLogCriticalLaplaceFeatureC p t)
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun _ => 0 := by
    have h := primeLogCriticalLaplaceMass_ae l
    rw [hl] at h
    exact h.symm.trans (Lp.coeFn_zero ℂ 2 _)
  let beta : Fin n → ℂ := fun i => -(Real.log ((prm i : ℕ) : ℝ) : ℂ)
  let coeff : Fin n → ℂ := fun i =>
    l (prm i) * (2 * Real.log ((prm i : ℕ) : ℝ) ^ 2 / Real.sqrt ((prm i : ℕ) : ℝ) : ℝ)
  let G : ℂ → ℂ := fun z => ∑ i, coeff i * z * Complex.exp (beta i * z)
  have hGdiff : Differentiable ℂ G := by
    dsimp [G]
    fun_prop
  have hsumFin : ∀ t : ℝ, (∑ p ∈ s, l p * primeLogCriticalLaplaceFeatureC p t) = G (t : ℂ) := by
    intro t
    rw [← Finset.sum_coe_sort s, ← e.symm.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [G, coeff, beta, prm]
    rw [primeLogCriticalLaplaceFeatureC, primeLogCriticalLaplaceFeature]
    push_cast
    simp only [neg_mul]
    ring
  have hGae : (fun t : ℝ => G (t : ℂ)) =ᵐ[volume.restrict (Ioo (2 : ℝ) 4)] fun _ => 0 := by
    have hsub : Ioo (2 : ℝ) 4 ⊆ Ioi (0 : ℝ) := fun t ht => lt_trans (by norm_num) ht.1
    have h := hzeroAE.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [h] with t ht
    rw [← hsumFin]
    exact ht
  have hGall : ∀ z : ℂ, G z = 0 := by
    intro z
    exact GaloisForLFunctions.HTGeometry.entire_eq_zero_of_ae_vanishing_on_real_interval
      (t₀ := (3 : ℝ)) (r := (1 : ℝ)) hGdiff (by norm_num)
      (by
        norm_num
        rw [Filter.eventually_inf_principal]
        apply (ae_restrict_iff' measurableSet_Ioo).mp
        simpa only [Filter.EventuallyEq] using hGae) z
  have hbeta : Function.Injective beta := by
    intro i j hij
    apply hprm
    have hlog : Real.log ((prm i : ℕ) : ℝ) = Real.log ((prm j : ℕ) : ℝ) := by
      have h1 : ((Real.log ((prm i : ℕ) : ℝ) : ℝ) : ℂ) = ((Real.log ((prm j : ℕ) : ℝ) : ℝ) : ℂ) :=
        neg_injective hij
      exact_mod_cast h1
    have hpi : (0 : ℝ) < ((prm i : ℕ) : ℝ) := by exact_mod_cast (prm i).property.pos
    have hpj : (0 : ℝ) < ((prm j : ℕ) : ℝ) := by exact_mod_cast (prm j).property.pos
    have := Real.log_injOn_pos hpi hpj hlog
    exact Subtype.ext (by exact_mod_cast this)
  have hcoeff : coeff = 0 := by
    apply HurwitzExp.expLin_eq_zero_on_open hbeta isOpen_compl_singleton
      (Set.nonempty_compl.mpr (Set.singleton_ne_univ 0))
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    have hfactor : G z = z * ∑ i, coeff i * Complex.exp (beta i * z) := by
      dsimp [G]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hprod : z * ∑ i, coeff i * Complex.exp (beta i * z) = 0 := by
      rw [← hfactor]; exact hGall z
    exact (mul_eq_zero.mp hprod).resolve_left hz0
  ext p
  by_cases hp : p ∈ s
  · have hi := congrFun hcoeff (e ⟨p, hp⟩)
    dsimp [coeff, prm] at hi
    rw [Equiv.symm_apply_apply] at hi
    have hlp : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
    have hsp : 0 < Real.sqrt ((p : ℕ) : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast p.property.pos)
    have hne : ((2 * Real.log ((p : ℕ) : ℝ) ^ 2 / Real.sqrt ((p : ℕ) : ℝ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.log ((p : ℕ) : ℝ) ^ 2 /
        Real.sqrt ((p : ℕ) : ℝ)).ne'
    simpa using (mul_eq_zero.mp hi).resolve_right hne
  · simpa [s] using hp

theorem primeLogCriticalLaplaceSynthesis_injective :
    Function.Injective primeLogCriticalLaplaceSynthesis := by
  intro x y hxy
  rw [primeLogCriticalLaplaceSynthesis_apply_core, primeLogCriticalLaplaceSynthesis_apply_core]
    at hxy
  have h := primeLogCriticalLaplaceMass_injective hxy
  apply Subtype.ext
  rw [← srcEmb_primeLogCriticalLaplaceCore x, ← srcEmb_primeLogCriticalLaplaceCore y, h]

end

end RHTower
