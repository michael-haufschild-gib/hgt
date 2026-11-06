import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomAllRankCenterTail
import GaloisForLFunctions.RHTower.PrimeArchThetaAtomLikelihoodRatio
import GaloisForLFunctions.HTGeometry.IteratedDerivTranslate

/-!
# Holomorphic normalization of ordered theta pairs

The product of two ordinary theta atoms is a translated first-atom
radial kernel. The identity preserves every real source derivative.
-/

set_option autoImplicit false

open Complex Set MeasureTheory
namespace GaloisForLFunctions.CompletedArithmeticForms
open HTGeometry _root_.RHTower
noncomputable section

/-- Entire difference-coordinate continuation of one ordered theta pair. -/
def thetaAtomPairComplex (n m : ℕ) (s : ℝ) (z : ℂ) : ℂ :=
  (Real.exp (-(Real.log n + Real.log m) / 2) : ℂ) *
    firstAtomComplexPair ((s + Real.log n + Real.log m) / 2)
      (z + ((Real.log n - Real.log m) / 2 : ℝ))

theorem thetaAtomPairComplex_entire (n m : ℕ) (s : ℝ) :
    Differentiable ℂ (thetaAtomPairComplex n m s) := by
  unfold thetaAtomPairComplex
  exact (differentiable_const _).mul
    ((firstAtomComplexPair_entire _).comp (differentiable_id.add_const _))

/-- The entire pair restricts to the literal two source atoms. -/
theorem thetaAtomPairComplex_ofReal {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (s t : ℝ) :
    thetaAtomPairComplex n m s (t : ℂ) =
      (thetaCuspSourceTerm (s / 2 + t) n * thetaCuspSourceTerm (s / 2 - t) m : ℝ) := by
  unfold thetaAtomPairComplex
  rw [← Complex.ofReal_add, firstAtomComplexPair_ofReal, ← Complex.ofReal_mul]
  congr 1
  rw [show (s + Real.log n + Real.log m) / 2 +
      (t + (Real.log n - Real.log m) / 2) = s / 2 + t + Real.log n by ring,
    show (s + Real.log n + Real.log m) / 2 -
      (t + (Real.log n - Real.log m) / 2) = s / 2 - t + Real.log m by ring,
    thetaCuspSourceTerm_shift_one hn, thetaCuspSourceTerm_shift_one hm]
  have hc : Real.exp (-(Real.log n + Real.log m) / 2) *
      Real.exp (Real.log n / 2) * Real.exp (Real.log m / 2) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  calc
    _ = (Real.exp (-(Real.log n + Real.log m) / 2) *
      Real.exp (Real.log n / 2) * Real.exp (Real.log m / 2)) *
        (thetaCuspSourceTerm (s / 2 + t) n * thetaCuspSourceTerm (s / 2 - t) m) := by ring
    _ = _ := by rw [hc, one_mul]

/-- Complex pair jets agree with the actual real source derivatives. -/
theorem thetaAtomPairComplex_jet {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (s : ℝ) (k : ℕ) :
    iteratedDeriv k (thetaAtomPairComplex n m s) 0 =
      (iteratedDeriv k (fun t : ℝ =>
        thetaCuspSourceTerm (s / 2 + t) n * thetaCuspSourceTerm (s / 2 - t) m) 0 : ℝ) := by
  have h := congrFun (_root_.HTGeometry.iteratedDeriv_comp_ofReal k
    (thetaAtomPairComplex_entire n m s)) 0
  have he : (fun t : ℝ => thetaAtomPairComplex n m s (t : ℂ)) =
      fun t : ℝ => ((thetaCuspSourceTerm (s / 2 + t) n *
        thetaCuspSourceTerm (s / 2 - t) m : ℝ) : ℂ) := funext (thetaAtomPairComplex_ofReal hn hm s)
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ =>
      thetaCuspSourceTerm (s / 2 + t) n * thetaCuspSourceTerm (s / 2 - t) m) := by
    unfold thetaCuspSourceTerm thetaCuspSeed
    fun_prop
  rw [he, GaloisForLFunctions.iteratedDeriv_ofReal_comp hs k] at h
  exact h.symm

/-- Product scale sets the radial cutoff; label ratio translates the difference coordinate. -/
theorem thetaAtomPairComplex_eq_radialKernel {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (s : ℝ) (z : ℂ) :
    thetaAtomPairComplex n m s z =
      ((4 * (Real.pi * n * m) ^ (-(1 / 2 : ℝ)) * (Real.pi * n * m * Real.exp s) : ℝ) : ℂ) *
        firstAtomRadialKernel (Real.pi * n * m * Real.exp s)
          (z + ((Real.log n - Real.log m) / 2 : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hscale : Real.pi * Real.exp (s + Real.log n + Real.log m) =
      Real.pi * n * m * Real.exp s := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hnR, Real.exp_log hmR]
    ring
  have hcoef : Real.exp (-(Real.log n + Real.log m) / 2) * Real.pi ^ (-(1 / 2 : ℝ)) =
      (Real.pi * n * m) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos Real.pi_pos,
      Real.rpow_def_of_pos (mul_pos (mul_pos Real.pi_pos hnR) hmR),
      ← Real.exp_add, Real.log_mul (mul_pos Real.pi_pos hnR).ne' hmR.ne',
      Real.log_mul Real.pi_pos.ne' hnR.ne']
    congr 1
    ring
  rw [thetaAtomPairComplex, firstAtomComplexPair_eq_radialKernel, hscale,
    firstAtomCenterTailFactor]
  have hc : Real.exp (-(Real.log n + Real.log m) / 2) *
      (4 * Real.pi ^ (-(1 / 2 : ℝ)) * (Real.pi * n * m * Real.exp s)) =
      4 * (Real.pi * n * m) ^ (-(1 / 2 : ℝ)) * (Real.pi * n * m * Real.exp s) := by
    calc
      _ = 4 * (Real.exp (-(Real.log n + Real.log m) / 2) *
        Real.pi ^ (-(1 / 2 : ℝ))) * (Real.pi * n * m * Real.exp s) := by ring
      _ = _ := by rw [hcoef]
  rw [← mul_assoc, ← Complex.ofReal_mul, hc]

/-- Every literal ordered-pair jet has the same radial normalization. -/
theorem thetaAtomPairComplex_jet_eq_radial {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (s : ℝ) (k : ℕ) :
    iteratedDeriv k (thetaAtomPairComplex n m s) 0 =
      ((4 * (Real.pi * n * m) ^ (-(1 / 2 : ℝ)) * (Real.pi * n * m * Real.exp s) : ℝ) : ℂ) *
        iteratedDeriv k (firstAtomRadialKernel (Real.pi * n * m * Real.exp s))
          (((Real.log n - Real.log m) / 2 : ℝ) : ℂ) := by
  have he := congrArg (fun f : ℂ → ℂ => iteratedDeriv k f 0)
    (funext (thetaAtomPairComplex_eq_radialKernel hn hm s))
  rw [iteratedDeriv_const_mul_field] at he
  dsimp only at he
  rw [HTGeometry.iteratedDeriv_comp_add_right, zero_add] at he
  exact he

#print axioms thetaAtomPairComplex_jet
#print axioms thetaAtomPairComplex_jet_eq_radial

end
end GaloisForLFunctions.CompletedArithmeticForms
