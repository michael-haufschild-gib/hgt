import GaloisForLFunctions.ArithmeticCorrelationGeometry.AlmostEveryGaugePointCancelsToTheSquareRoot
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Maximal critical moments averaged over prime twists

Vertical translation multiplies every Dirichlet coefficient by a unit phase.
Consequently every finite height measure gives the same Haar mean square
per unit mass. Dyadic decomposition also controls every shorter cutoff
by a single integrable function, at the cost of two powers of the depth.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimeTwistedMoments
open Finset MeasureTheory Complex
open GaloisForLFunctions.ArithmeticCorrelationGeometry
noncomputable section

/-- Vertical translation of an arbitrary finite Dirichlet section. -/
def verticalCoeff (a : ℕ → ℂ) (t : ℝ) (n : ℕ) := a n * Complex.exp (((-t*Real.log n : ℝ):ℂ)*Complex.I)

private theorem norm_verticalCoeff (a : ℕ → ℂ) (t : ℝ) (n : ℕ) :
    ‖verticalCoeff a t n‖ = ‖a n‖ := by
  rw [verticalCoeff,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one]

/-- Squared modulus at a single time and prime twist. -/
def power (a : ℕ → ℂ) (s : Finset ℕ) (x : GaugeTorus) (t : ℝ) :=
  ‖orthoSum (fun n y => twist y n) (verticalCoeff a t) s x‖^2

private theorem power_continuous (a : ℕ → ℂ) (s : Finset ℕ) :
    Continuous (fun p : GaugeTorus × ℝ => power a s p.1 p.2) := by
  unfold power orthoSum
  apply Continuous.pow
  apply Continuous.norm
  apply continuous_finsetSum
  intro n _
  exact (continuous_const.mul (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_snd.neg.mul continuous_const)).mul continuous_const))).mul
      ((continuous_twist n).comp continuous_fst)

private theorem power_le (a : ℕ → ℂ) (s : Finset ℕ) (x : GaugeTorus) (t : ℝ) :
    power a s x t ≤ (∑ n ∈ s, ‖a n‖)^2 := by
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  apply (norm_sum_le _ _).trans
  exact sum_le_sum fun n _ => by rw [norm_mul,norm_verticalCoeff,norm_twist,mul_one]

variable (ν : Measure ℝ) [IsFiniteMeasure ν]

private theorem integrable_power (a : ℕ → ℂ) (s : Finset ℕ) :
    Integrable (fun p : GaugeTorus × ℝ => power a s p.1 p.2) (gaugeHaar.prod ν) :=
  Integrable.of_bound (power_continuous a s).aestronglyMeasurable _
    (.of_forall fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact power_le a s p.1 p.2)

theorem integrable_power_at (a : ℕ → ℂ) (s : Finset ℕ) (x : GaugeTorus) :
    Integrable (power a s x) ν := by
  apply Integrable.of_bound ((power_continuous a s).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    ((∑ n ∈ s, ‖a n‖)^2)
  exact .of_forall fun t => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact power_le a s x t

/-- The prime-twisted moment against a finite measure on heights. -/
def moment (a : ℕ → ℂ) (s : Finset ℕ) (x : GaugeTorus) := ∫ t, power a s x t ∂ν

theorem integrable_moment (a : ℕ → ℂ) (s : Finset ℕ) :
    Integrable (moment ν a s) gaugeHaar := (integrable_power ν a s).integral_prod_left

omit [IsFiniteMeasure ν] in
theorem moment_nonneg (a : ℕ → ℂ) (s : Finset ℕ) (x : GaugeTorus) :
    0 ≤ moment ν a s x := integral_nonneg fun _ => sq_nonneg _

/-- Every finite height measure returns exactly its mass times the diagonal. -/
theorem integral_prime_twisted_moment (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) :
    ∫ x, moment ν a s x ∂gaugeHaar = ν.real Set.univ * ∑ n ∈ s, ‖a n‖^2 := by
  have ht (t : ℝ) : ∫ x, power a s x t ∂gaugeHaar = ∑ n ∈ s, ‖a n‖^2 := by
    calc
      _ = ∑ n ∈ s, ‖verticalCoeff a t n‖^2 :=
        integral_sq_norm_orthoSum (fun n => (continuous_twist n).measurable)
          (fun n x => (norm_twist x n).le) (fun _ _ hm hn => integral_twist_mul_conj hm hn) _ hs
      _ = _ := by simp only [norm_verticalCoeff]
  calc
    _ = ∫ t, ∫ x, power a s x t ∂gaugeHaar ∂ν :=
      integral_integral_swap (integrable_power ν a s)
    _ = _ := by simp only [ht,integral_const,smul_eq_mul]

/-- One positive time-integrated dyadic sum for every cutoff below 2^(K+1). -/
def maximalEnvelope (a : ℕ → ℂ) (K : ℕ) (x : GaugeTorus) :=
  ((K:ℝ)+1)*∑ j ∈ range (K+1), ∑ i ∈ range (2^(K+1-j)),
    moment ν a (Ioc (2^j*i) (2^j*(i+1))) x

/-- Every partial section, with the same twist and height measure, is bounded
by the common dyadic envelope. -/
theorem moment_le_maximalEnvelope (a : ℕ → ℂ) {N K : ℕ} (hN : N < 2^(K+1)) (x : GaugeTorus) :
    moment ν a (Ioc 0 N) x ≤ maximalEnvelope ν a K x := by
  let block (j i : ℕ) := Ioc (2^j*i) (2^j*(i+1))
  have hblocks (j : ℕ) := integrable_finsetSum (range (2^(K+1-j))) (fun i _ => integrable_power_at ν a (block j i) x)
  have h := integral_mono (integrable_power_at ν a (Ioc 0 N) x)
    ((integrable_finsetSum (range (K+1)) (fun j _ => hblocks j)).const_mul ((K:ℝ)+1))
    (fun t => sq_norm_orthoSum_le (fun n y => twist y n) (verticalCoeff a t) hN x)
  change _ ≤ ∫ t, ((K:ℝ)+1)*(∑ j ∈ range (K+1), ∑ i ∈ range (2^(K+1-j)), power a (block j i) x t) ∂ν at h
  rw [integral_const_mul,integral_finsetSum _ (fun j _ => hblocks j)] at h
  have inner (j : ℕ) : (∫ t, ∑ i ∈ range (2^(K+1-j)), power a (block j i) x t ∂ν) =
      ∑ i ∈ range (2^(K+1-j)), moment ν a (block j i) x :=
    integral_finsetSum _ (fun i _ => integrable_power_at ν a (block j i) x)
  simp_rw [inner] at h
  exact h

theorem integrable_maximalEnvelope (a : ℕ → ℂ) (K : ℕ) :
    Integrable (maximalEnvelope ν a K) gaugeHaar :=
  (integrable_finsetSum _ (fun _ _ => integrable_finsetSum _ (fun _ _ =>
    integrable_moment ν a _))).const_mul _

/-- The exact Haar cost of the common maximal envelope is independent of
the location and shape of the height measure. -/
theorem integral_maximalEnvelope (a : ℕ → ℂ) (K : ℕ) :
    ∫ x, maximalEnvelope ν a K x ∂gaugeHaar =
      ((K:ℝ)+1)^2 * ν.real Set.univ * ∑ n ∈ Ioc 0 (2^(K+1)), ‖a n‖^2 := by
  let block (j i : ℕ) := Ioc (2^j*i) (2^j*(i+1))
  have he (j i : ℕ) := integral_prime_twisted_moment ν a (s:=block j i)
    (fun n hn => by have := (mem_Ioc.mp hn).1; omega)
  have level (j : ℕ) (hj : j ∈ range (K+1)) :
      ∑ i ∈ range (2^(K+1-j)), (∑ n ∈ block j i, ‖a n‖^2) = ∑ n ∈ Ioc 0 (2^(K+1)), ‖a n‖^2 := by
    have hle : j ≤ K+1 := (mem_range.mp hj).le
    rw [show (∑ i ∈ range (2^(K+1-j)), ∑ n ∈ block j i, ‖a n‖^2) =
      ∑ n ∈ Ioc (2^j*0) (2^j*2^(K+1-j)), ‖a n‖^2 from sum_Ioc_tile_mono _ (e:=fun i => 2^j*i)
        (fun _ _ h => Nat.mul_le_mul_left _ h) _,mul_zero,←pow_add,Nat.add_sub_cancel' hle]
  unfold maximalEnvelope
  rw [integral_const_mul,integral_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun i _ => integrable_moment ν a (block j i)))]
  have per (j : ℕ) (hj : j ∈ range (K+1)) :
      (∫ x, ∑ i ∈ range (2^(K+1-j)), moment ν a (block j i) x ∂gaugeHaar) =
      ν.real Set.univ * ∑ n ∈ Ioc 0 (2^(K+1)), ‖a n‖^2 := by
    rw [integral_finsetSum _ (fun i _ => integrable_moment ν a (block j i))]
    simp only [he,←mul_sum,level j hj]
  rw [sum_congr rfl per,sum_const,card_range,nsmul_eq_mul,Nat.cast_succ]
  ring

#print axioms integral_prime_twisted_moment
#print axioms moment_le_maximalEnvelope
#print axioms integral_maximalEnvelope
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimeTwistedMoments
