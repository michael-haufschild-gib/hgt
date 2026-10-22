import GaloisForLFunctions.RHTower.ThetaMovingShellFourierJet
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFiniteShellSeamCancellation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Frequency derivatives of literal finite theta prefixes

The positive-half-line complex moments are genuine frequency derivatives.
Their real zeroth jet is the existing canonical prefix cosine transform.
-/

open Real Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower
noncomputable section

def thetaShellPrefixFrequencyJet (N k : ℕ) (b : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, thetaShellFrequencyJet n k b

def thetaShellPrefixCosine (N : ℕ) (b : ℝ) : ℝ :=
  (thetaShellPrefixFrequencyJet N 0 b).re

theorem hasDerivAt_thetaShellFrequencyJet (n k : ℕ) (b : ℝ) :
    HasDerivAt (thetaShellFrequencyJet n k) (thetaShellFrequencyJet n (k+1) b) b := by
  let F : ℝ → ℝ → ℂ := fun t x => (thetaCuspSourceTerm x (n+1) : ℂ) *
    (Complex.I * (x : ℂ))^k * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))
  let F' : ℝ → ℝ → ℂ := fun t x => (thetaCuspSourceTerm x (n+1) : ℂ) *
    (Complex.I * (x : ℂ))^(k+1) * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))
  have hcont (j : ℕ) (t : ℝ) : Continuous (fun x : ℝ =>
      (thetaCuspSourceTerm x (n+1) : ℂ) * (Complex.I * (x : ℂ))^j *
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) := by
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  have hint := integrableOn_thetaShellFrequencyJetIntegrand n (k+1) 0
  have hnorm : (fun x => ‖F' 0 x‖) =
      (fun x : ℝ => |thetaCuspSourceTerm x (n+1)| * |x|^(k+1)) := by
    ext x
    simp [F', norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hmajor : IntegrableOn (fun x : ℝ =>
      |thetaCuspSourceTerm x (n+1)| * |x|^(k+1)) (Ioi 0) := by
    rw [← hnorm]
    exact hint.norm
  have hdiff (t x : ℝ) : HasDerivAt (fun t => F t x) (F' t x) t := by
    have hphase : HasDerivAt (fun z : ℂ => Complex.I * z * (x : ℂ))
        (Complex.I * (x : ℂ)) (t : ℂ) := by
      simpa only [mul_one, id_eq] using!
        ((hasDerivAt_id (t : ℂ)).const_mul Complex.I).mul_const (x : ℂ)
    have he := (((Complex.hasDerivAt_exp _).comp (t : ℂ) hphase).comp_ofReal).const_mul
      ((thetaCuspSourceTerm x (n+1) : ℂ) * (Complex.I * (x : ℂ))^k)
    simpa only [F, F', Function.comp_def, pow_succ, mul_assoc, mul_left_comm, mul_comm] using! he
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := F) (F' := F')
    (bound := fun x => |thetaCuspSourceTerm x (n+1)| * |x|^(k+1))
    (s := univ) (x₀ := b) (Filter.univ_mem)
    (Eventually.of_forall fun t => (hcont k t).aestronglyMeasurable.restrict)
    (integrableOn_thetaShellFrequencyJetIntegrand n k b)
    ((hcont (k+1) b).aestronglyMeasurable.restrict)
    (Eventually.of_forall fun x t _ => by
      simp [F', norm_pow, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs])
    hmajor (Eventually.of_forall fun x t _ => hdiff t x)
  exact h.2

theorem hasDerivAt_thetaShellPrefixFrequencyJet (N k : ℕ) (b : ℝ) :
    HasDerivAt (thetaShellPrefixFrequencyJet N k)
      (thetaShellPrefixFrequencyJet N (k+1) b) b := by
  convert HasDerivAt.sum (u := Finset.range N)
    (fun n _ => hasDerivAt_thetaShellFrequencyJet n k b) using 1
  all_goals first | rfl | (ext t; simp [thetaShellPrefixFrequencyJet])

theorem hasDerivAt_thetaShellPrefixRealJet (N k : ℕ) (b : ℝ) :
    HasDerivAt (fun t => (thetaShellPrefixFrequencyJet N k t).re)
      (thetaShellPrefixFrequencyJet N (k+1) b).re b := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt b
    (hasDerivAt_thetaShellPrefixFrequencyJet N k b)

theorem iteratedDeriv_thetaShellPrefixCosine (N k : ℕ) :
    iteratedDeriv k (thetaShellPrefixCosine N) =
      fun b => (thetaShellPrefixFrequencyJet N k b).re := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext b
    exact (hasDerivAt_thetaShellPrefixRealJet N k b).deriv

theorem thetaShellPrefixCosine_eq_literal (N : ℕ) (b : ℝ) :
    thetaShellPrefixCosine N b = ∫ x : ℝ in Ioi 0,
      thetaCuspFiniteShellPrefix N x * Real.cos (b*x) := by
  unfold thetaShellPrefixCosine thetaShellPrefixFrequencyJet
  rw [Complex.re_sum]
  have hterm (n : ℕ) : (thetaShellFrequencyJet n 0 b).re =
      ∫ x : ℝ in Ioi 0, thetaCuspSourceTerm x (n+1) * Real.cos (b*x) := by
    unfold thetaShellFrequencyJet
    have hr := integral_re (𝕜 := ℂ) (integrableOn_thetaShellFrequencyJetIntegrand n 0 b)
    change (∫ x : ℝ in Ioi 0,
      ((thetaCuspSourceTerm x (n+1) : ℂ) * (Complex.I * (x : ℂ))^0 *
        Complex.exp (Complex.I * (b : ℂ) * (x : ℂ))).re) =
      (∫ x : ℝ in Ioi 0, (thetaCuspSourceTerm x (n+1) : ℂ) * (Complex.I * (x : ℂ))^0 *
        Complex.exp (Complex.I * (b : ℂ) * (x : ℂ))).re at hr
    rw [← hr]
    apply integral_congr_ae
    filter_upwards with x
    simp only [pow_zero, mul_one, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [Complex.exp_re]
    simp
  simp_rw [hterm]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards with x
    rw [thetaCuspFiniteShellPrefix, Finset.sum_range_succ']
    simp only [thetaCuspSourceTerm, thetaCuspSeed, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0),
      zero_pow (by decide : 4 ≠ 0), zero_mul, sub_zero, mul_zero, add_zero, Finset.sum_mul]
  · intro n hn
    exact (integrableOn_thetaShellFrequencyJetIntegrand n 0 b).re.congr
      (Eventually.of_forall fun x => by
        simp [Complex.mul_re, Complex.exp_re, mul_assoc])

end
end RHTower
