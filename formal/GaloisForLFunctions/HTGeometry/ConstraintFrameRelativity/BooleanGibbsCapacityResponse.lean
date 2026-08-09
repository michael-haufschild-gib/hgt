import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.FiniteTiltResponse
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellCapacityDepth

/-!
# The Boolean Gibbs law, its Schur capacity, and their exact responses

The divisor Gibbs law of a squarefree modulus is the product Bernoulli law of the fugacities:

`Z⁻¹ ∏_{p ∈ S} x_p = ∏_{p ∈ S} q_p ∏_{p ∉ S} (1 - q_p)`,   `q_p = x_p/(1+x_p)`.

Its parity and energy statistics have the exact diagonal covariance Gram
`A = ∑ w_p`, `B = ∑ w_p λ_p`, `C = ∑ w_p λ_p²` with `w_p = q_p(1-q_p)`, so the parity--energy
Schur capacity is `π²(A - B²/C)` and equals the ordered clock-gap ratio.

Two exact responses follow: a general coefficient tilt differentiates the optimised capacity to
`π² Cov(r, R²)` for the regression residual `R`, and a factorwise fugacity change gives the closed
formula `π² ∑ w_p(1 - 2q_p) s_p (1 - β λ_p)²`.
-/

namespace HTGeometry.ConstraintFrameRelativity

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The divisor Gibbs law is a product Bernoulli law -/

/-- **Gibbs--Bernoulli bridge.** -/
theorem bernoulliWeight_occProb (x : ι → ℝ) (hx : ∀ p, 0 < x p) (S : Finset ι) :
    bernoulliWeight (fun p => occProb (x p)) S
      = (∏ p ∈ S, x p) / ∏ p, (1 + x p) := by
  have h1 : ∀ p : ι, (0 : ℝ) < 1 + x p := fun p => by linarith [hx p]
  have hA : ∏ p ∈ S, occProb (x p) = (∏ p ∈ S, x p) / ∏ p ∈ S, (1 + x p) := by
    simp only [occProb]
    rw [Finset.prod_div_distrib]
  have hB : ∏ p ∈ Sᶜ, (1 - occProb (x p)) = (∏ p ∈ Sᶜ, (1 + x p))⁻¹ := by
    have hpt : ∀ p : ι, 1 - occProb (x p) = ((1 + x p))⁻¹ := by
      intro p
      have hp := (h1 p).ne'
      rw [occProb]
      field_simp
      ring
    rw [Finset.prod_congr rfl fun p _ => hpt p, ← Finset.prod_inv_distrib]
  have hkey : (∏ p ∈ S, (1 + x p)) * ∏ p ∈ Sᶜ, (1 + x p) = ∏ p, (1 + x p) :=
    Finset.prod_mul_prod_compl S _
  have hSpos : (0 : ℝ) < ∏ p ∈ S, (1 + x p) := Finset.prod_pos fun p _ => h1 p
  have hCpos : (0 : ℝ) < ∏ p ∈ Sᶜ, (1 + x p) := Finset.prod_pos fun p _ => h1 p
  rw [bernoulliWeight, hA, hB, ← hkey]
  field_simp

theorem sum_bernoulliWeight (q : ι → ℝ) : ∑ S : Finset ι, bernoulliWeight q S = 1 := by
  have h := bernoulliExp_one q
  simpa [bernoulliExp] using h

/-! ## The covariance Gram of parity and energy -/

/-- The Bernoulli variance vector. -/
def bernoulliVar (q : ι → ℝ) (p : ι) : ℝ := q p * (1 - q p)

theorem wcov_bernoulliWeight (q : ι → ℝ) (f g : Finset ι → ℝ) :
    wcov (bernoulliWeight q) f g = bernoulliCov q f g := rfl

theorem bernoulliCov_one_one (q : ι → ℝ) :
    bernoulliCov q (linearStat fun _ => 1) (linearStat fun _ => 1) = capA (bernoulliVar q) := by
  rw [bernoulliCov_linearStat, capA]
  exact Finset.sum_congr rfl fun p _ => by simp [bernoulliVar]

theorem bernoulliCov_one_lam (q lam : ι → ℝ) :
    bernoulliCov q (linearStat fun _ => 1) (linearStat lam) = capB (bernoulliVar q) lam := by
  rw [bernoulliCov_linearStat, capB]
  exact Finset.sum_congr rfl fun p _ => by simp [bernoulliVar]; ring

theorem bernoulliCov_lam_lam (q lam : ι → ℝ) :
    bernoulliCov q (linearStat lam) (linearStat lam) = capC (bernoulliVar q) lam := by
  rw [bernoulliCov_linearStat, capC]
  exact Finset.sum_congr rfl fun p _ => by simp [bernoulliVar]; ring

/-! ## The ordered capacity ratio -/

/-- **The capacity as an ordered clock-gap ratio.** -/
theorem schurCapacity_eq_ordered_ratio [LinearOrder ι] {w lam : ι → ℝ} (hC : 0 < capC w lam) :
    schurCapacity w lam
      = Real.pi ^ 2 *
        ((∑ p, ∑ r ∈ Finset.univ.filter (fun r => p < r), w p * w r * (lam p - lam r) ^ 2)
          / capC w lam) := by
  rw [schurCapacity_eq_ratio hC, capA_mul_capC_sub_capB_sq_lt]

/-! ## Exact response to a coefficient intervention -/

/-- **Exact intervention response of the Boolean capacity.**  Tilting the Gibbs law by a score
`r` moves the optimised parity--energy capacity by `π² Cov(r, R²)`. -/
theorem hasDerivAt_booleanTiltCapacity (q lam : ι → ℝ) (r : Finset ι → ℝ)
    (hC : capC (bernoulliVar q) lam ≠ 0) :
    HasDerivAt
      (fun e => Real.pi ^ 2 *
        (tiltCov (bernoulliWeight q) r e (linearStat fun _ => 1) (linearStat fun _ => 1)
          - tiltCov (bernoulliWeight q) r e (linearStat fun _ => 1) (linearStat lam) ^ 2
            / tiltCov (bernoulliWeight q) r e (linearStat lam) (linearStat lam)))
      (Real.pi ^ 2 * wcov (bernoulliWeight q) r (fun S =>
        ((linearStat (fun _ => 1) S - wexp (bernoulliWeight q) (linearStat fun _ => 1))
          - (capB (bernoulliVar q) lam / capC (bernoulliVar q) lam)
            * (linearStat lam S - wexp (bernoulliWeight q) (linearStat lam))) ^ 2)) 0 := by
  have hμ : ∑ S : Finset ι, bernoulliWeight q S = 1 := sum_bernoulliWeight q
  have hgg : wcov (bernoulliWeight q) (linearStat lam) (linearStat lam)
      = capC (bernoulliVar q) lam := by
    rw [wcov_bernoulliWeight, bernoulliCov_lam_lam]
  have hfg : wcov (bernoulliWeight q) (linearStat fun _ => 1) (linearStat lam)
      = capB (bernoulliVar q) lam := by
    rw [wcov_bernoulliWeight, bernoulliCov_one_lam]
  have h := hasDerivAt_tiltSchurCapacity hμ r (linearStat fun _ => 1) (linearStat lam)
    (by rw [hgg]; exact hC)
  rw [hgg, hfg] at h
  exact h

/-! ## Exact response to a factorwise fugacity change -/

omit [DecidableEq ι] in
/-- **Fugacity response.**  A factorwise change of fugacities moves the capacity by
`π² ∑ w_p (1 - 2 q_p) s_p (1 - β λ_p)²`. -/
theorem hasDerivAt_fugacitySchurCapacity (x s lam : ι → ℝ) (hx : ∀ p, 0 < x p)
    (hC : capC (fun p => fugacityVar (x p) (s p) 0) lam ≠ 0) :
    HasDerivAt (fun e => schurCapacity (fun p => fugacityVar (x p) (s p) e) lam)
      (Real.pi ^ 2 * ∑ p, (fugacityVar (x p) (s p) 0 * (1 - 2 * fugacityProb (x p) (s p) 0) * s p)
        * (1 - (capB (fun p => fugacityVar (x p) (s p) 0) lam
            / capC (fun p => fugacityVar (x p) (s p) 0) lam) * lam p) ^ 2) 0 := by
  set w' : ι → ℝ :=
    fun p => fugacityVar (x p) (s p) 0 * (1 - 2 * fugacityProb (x p) (s p) 0) * s p with hw'
  have hderiv : ∀ p : ι, HasDerivAt (fun e => fugacityVar (x p) (s p) e) (w' p) 0 :=
    fun p => hasDerivAt_fugacityVar (hx p) (s p)
  have hA : HasDerivAt (fun e => capA (fun p => fugacityVar (x p) (s p) e)) (∑ p, w' p) 0 :=
    HasDerivAt.fun_sum fun p _ => hderiv p
  have hB : HasDerivAt (fun e => capB (fun p => fugacityVar (x p) (s p) e) lam)
      (∑ p, w' p * lam p) 0 :=
    HasDerivAt.fun_sum fun p _ => (hderiv p).mul_const (lam p)
  have hC' : HasDerivAt (fun e => capC (fun p => fugacityVar (x p) (s p) e) lam)
      (∑ p, w' p * lam p ^ 2) 0 :=
    HasDerivAt.fun_sum fun p _ => (hderiv p).mul_const (lam p ^ 2)
  have h := hasDerivAt_capacityOfMoments hA hB hC' hC
  simp only [schurCapacity]
  refine h.congr_deriv ?_
  set β := capB (fun p => fugacityVar (x p) (s p) 0) lam
    / capC (fun p => fugacityVar (x p) (s p) 0) lam with hβ
  have hexpand : ∑ p, w' p * (1 - β * lam p) ^ 2
      = (∑ p, w' p) - 2 * β * (∑ p, w' p * lam p) + β ^ 2 * ∑ p, w' p * lam p ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hexpand]

end HTGeometry.ConstraintFrameRelativity
