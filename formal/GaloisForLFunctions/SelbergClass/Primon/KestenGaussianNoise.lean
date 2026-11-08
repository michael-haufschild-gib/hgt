import GaloisForLFunctions.SelbergClass.Primon.KestenGreenConditioning
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Independent Gaussian innovations for the prime Green kernel

A countable product of real Gaussian measures realizes the Green
innovation variances: `q/(1+q)` at the initial site and `q` thereafter.
The coordinate variables are jointly Gaussian, independent, centered,
and square integrable. Their covariance is exactly diagonal.
-/

open _root_.RHTower MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The initial innovation has the boundary variance; all later innovations have variance `q`. -/
def kestenGaussianNoiseVariance (p : Nat.Primes) (n : ℕ) : ℝ≥0 :=
  ⟨if n = 0 then primeReciprocal p / (1 + primeReciprocal p) else primeReciprocal p, by
    split_ifs
    · exact (div_pos (primeReciprocal_pos p) (by have := primeReciprocal_pos p; positivity)).le
    · exact (primeReciprocal_pos p).le⟩

theorem kestenGaussianNoiseVariance_zero (p : Nat.Primes) :
    (kestenGaussianNoiseVariance p 0 : ℝ) = primeReciprocal p / (1 + primeReciprocal p) := rfl

theorem kestenGaussianNoiseVariance_succ (p : Nat.Primes) (n : ℕ) :
    (kestenGaussianNoiseVariance p (n + 1) : ℝ) = primeReciprocal p := by
  change (if n + 1 = 0 then primeReciprocal p / (1 + primeReciprocal p) else primeReciprocal p) = _
  rw [if_neg (Nat.succ_ne_zero n)]

theorem kestenGaussianNoiseVariance_pos (p : Nat.Primes) (n : ℕ) :
    0 < (kestenGaussianNoiseVariance p n : ℝ) := by
  change 0 < (if n = 0 then primeReciprocal p / (1 + primeReciprocal p) else primeReciprocal p)
  split_ifs
  · exact div_pos (primeReciprocal_pos p) (by have := primeReciprocal_pos p; positivity)
  · exact primeReciprocal_pos p

/-- The actual probability law of the countable family of independent innovations. -/
def kestenGaussianNoiseMeasure (p : Nat.Primes) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun n => gaussianReal 0 (kestenGaussianNoiseVariance p n))

instance isProbabilityMeasure_kestenGaussianNoiseMeasure (p : Nat.Primes) :
    IsProbabilityMeasure (kestenGaussianNoiseMeasure p) := by
  unfold kestenGaussianNoiseMeasure
  infer_instance

/-- Each coordinate has the prescribed centered Gaussian law. -/
theorem hasLaw_kestenGaussianNoise (p : Nat.Primes) (n : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => ω n) (gaussianReal 0 (kestenGaussianNoiseVariance p n))
      (kestenGaussianNoiseMeasure p) :=
  (measurePreserving_eval_infinitePi (fun n => gaussianReal 0 (kestenGaussianNoiseVariance p n)) n).hasLaw

/-- Independence holds for the entire countable family, not just for pairs. -/
theorem iIndepFun_kestenGaussianNoise (p : Nat.Primes) :
    iIndepFun (fun n (ω : ℕ → ℝ) => ω n) (kestenGaussianNoiseMeasure p) :=
  iIndepFun_infinitePi (P := fun n => gaussianReal 0 (kestenGaussianNoiseVariance p n))
    (X := fun (_ : ℕ) (x : ℝ) => x) (fun _ => measurable_id)

/-- Every finite coordinate vector is jointly Gaussian. -/
theorem isGaussianProcess_kestenGaussianNoise (p : Nat.Primes) :
    IsGaussianProcess (fun n (ω : ℕ → ℝ) => ω n) (kestenGaussianNoiseMeasure p) := by
  constructor
  intro I
  exact iIndepFun.hasGaussianLaw (fun i : I => (hasLaw_kestenGaussianNoise p i).hasGaussianLaw)
    (iIndepFun.precomp Subtype.val_injective (iIndepFun_kestenGaussianNoise p))

theorem memLp_kestenGaussianNoise (p : Nat.Primes) (n : ℕ) :
    MemLp (fun ω : ℕ → ℝ => ω n) 2 (kestenGaussianNoiseMeasure p) :=
  (hasLaw_kestenGaussianNoise p n).hasGaussianLaw.memLp_two

theorem integral_kestenGaussianNoise (p : Nat.Primes) (n : ℕ) :
    (∫ ω, ω n ∂kestenGaussianNoiseMeasure p) = 0 := by
  rw [(hasLaw_kestenGaussianNoise p n).integral_eq, integral_id_gaussianReal]

theorem variance_kestenGaussianNoise (p : Nat.Primes) (n : ℕ) :
    Var[fun ω => ω n; kestenGaussianNoiseMeasure p] = (kestenGaussianNoiseVariance p n : ℝ) := by
  rw [(hasLaw_kestenGaussianNoise p n).variance_eq, variance_id_gaussianReal]

/-- The product probability measure realizes precisely the diagonal innovation covariance. -/
theorem covariance_kestenGaussianNoise (p : Nat.Primes) (n m : ℕ) :
    cov[fun ω => ω n, fun ω => ω m; kestenGaussianNoiseMeasure p] =
      if n = m then (kestenGaussianNoiseVariance p n : ℝ) else 0 := by
  by_cases h : n = m
  · subst m
    rw [covariance_self (measurable_pi_apply n).aemeasurable, variance_kestenGaussianNoise, if_pos rfl]
  · rw [if_neg h]
    exact ((iIndepFun_kestenGaussianNoise p).indepFun h).covariance_eq_zero
      (memLp_kestenGaussianNoise p n) (memLp_kestenGaussianNoise p m)

end
end GaloisForLFunctions.SelbergClass.Primon
