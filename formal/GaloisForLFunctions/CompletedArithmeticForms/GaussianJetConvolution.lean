import GaloisForLFunctions.CompletedArithmeticForms.WickCauchyPayment
import GaloisForLFunctions.RHTower.XiSliceMixedClassDetection

/-!
# Exact Gaussian jet convolution

Multiplication of the Gaussian kernel by one entire function of the sum has
an exact finite coefficient formula. Its common Gaussian contraction index
retains the factorial cancellations needed for bounds on the complete form.
-/

noncomputable section

open Finset Metric
open scoped ContDiff

namespace GaloisForLFunctions.CompletedArithmeticForms

open _root_.RHTower

/-- One-variable multiplier of the complete Gaussian polynomial kernel. -/
def gaussianMultiplierKernel (h : ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  Complex.exp (8 * p.1 * p.2) * h (p.1 + p.2)

theorem gaussianMultiplierKernel_contDiff {h : ℂ → ℂ} (hh : Differentiable ℂ h) :
    ContDiff ℂ ∞ (gaussianMultiplierKernel h) := by
  have hc : ContDiff ℂ ∞ h := hh.contDiff
  unfold gaussianMultiplierKernel
  fun_prop

/-- The first variable exposes the common Gaussian contraction degree. -/
theorem firstComplexJet_gaussianMultiplier {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (i : ℕ) (w : ℂ) :
    firstComplexJet (gaussianMultiplierKernel h) i (0, w) =
      ∑ r ∈ range (i + 1), (i.choose r : ℂ) * (8 : ℂ) ^ r *
        (w ^ r * iteratedDeriv (i - r) h w) := by
  rw [firstComplexJet_eq_iteratedDeriv]
  have he : (fun z : ℂ => gaussianMultiplierKernel h (z, w)) =
      fun z : ℂ => Complex.exp ((8 * w) * z) * h (z + w) := by
    funext z
    unfold gaussianMultiplierKernel
    congr 2
    ring
  have hg : Differentiable ℂ (fun z : ℂ => Complex.exp ((8 * w) * z)) := by fun_prop
  have hhw : Differentiable ℂ (fun z : ℂ => h (z + w)) := hh.comp (by fun_prop)
  rw [he, iteratedDeriv_fun_mul hg.contDiff.contDiffAt hhw.contDiff.contDiffAt]
  apply Finset.sum_congr rfl
  intro r hr
  have ht := congrFun (iteratedDeriv_comp_add_const (i - r) h w) 0
  simp only [zero_add] at ht
  rw [iteratedDeriv_cexp_const_mul, ht]
  simp only [mul_zero, Complex.exp_zero, mul_one, mul_pow]
  ring

private theorem iteratedDeriv_iterated_zero (h : ℂ → ℂ) (a b : ℕ) :
    iteratedDeriv b (iteratedDeriv a h) 0 = iteratedDeriv (a + b) h 0 := by
  simp only [iteratedDeriv_eq_iterate]
  rw [Nat.add_comm a b, Function.iterate_add_apply]

/-- Every mixed coefficient is a finite Gaussian contraction sum. -/
theorem mixedKernelJet_gaussianMultiplier_sum {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (i j : ℕ) :
    mixedKernelJet (gaussianMultiplierKernel h) i j =
      ∑ r ∈ range (i + 1),
        (i.choose r : ℂ) * (j.choose r : ℂ) * (8 : ℂ) ^ r * (r.factorial : ℂ) *
          iteratedDeriv ((i - r) + (j - r)) h 0 := by
  have hd (a : ℕ) : Differentiable ℂ (iteratedDeriv a h) :=
    ContDiff.differentiable_iteratedDeriv' a hh.contDiff
  have he : (fun w : ℂ => firstComplexJet (gaussianMultiplierKernel h) i (0, w)) =
      fun w : ℂ => ∑ r ∈ range (i + 1), (i.choose r : ℂ) * (8 : ℂ) ^ r *
        (w ^ r * iteratedDeriv (i - r) h w) :=
    funext (firstComplexJet_gaussianMultiplier hh i)
  have hterm (r : ℕ) : ContDiffAt ℂ j
      (fun w : ℂ => (i.choose r : ℂ) * (8 : ℂ) ^ r *
        (w ^ r * iteratedDeriv (i - r) h w)) 0 := by
    have hr := hd (i - r)
    have ht : Differentiable ℂ (fun w : ℂ => (i.choose r : ℂ) * (8 : ℂ) ^ r *
      (w ^ r * iteratedDeriv (i - r) h w)) := by fun_prop
    exact ht.contDiff.contDiffAt
  rw [mixedKernelJet, he,
    iteratedDeriv_fun_sum (f := fun r w => (i.choose r : ℂ) * (8 : ℂ) ^ r *
      (w ^ r * iteratedDeriv (i - r) h w)) (fun r _ => hterm r)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [_root_.iteratedDeriv_const_mul_field,
    _root_.RHTower.iteratedDeriv_pow_mul_zero (hd (i - r))]
  by_cases hrj : r ≤ j
  · rw [if_pos hrj, iteratedDeriv_iterated_zero]
    push_cast
    ring
  · simp only [if_neg hrj, Nat.choose_eq_zero_of_lt (by omega : j < r),
      Nat.cast_zero, mul_zero, zero_mul]

/-- Only contraction degrees present in both source directions contribute. -/
theorem mixedKernelJet_gaussianMultiplier {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (i j : ℕ) :
    mixedKernelJet (gaussianMultiplierKernel h) i j =
      ∑ r ∈ range (min i j + 1),
        (i.choose r : ℂ) * (j.choose r : ℂ) * (8 : ℂ) ^ r * (r.factorial : ℂ) *
          iteratedDeriv ((i - r) + (j - r)) h 0 := by
  rw [mixedKernelJet_gaussianMultiplier_sum hh]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : min i j + 1 ≤ i + 1))
  intro r hri hrmin
  have hir : r ≤ i := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hri
  have hmin : min i j < r := by
    have := Finset.mem_range.not.mp hrmin
    omega
  have hjr : j < r := by omega
  simp only [Nat.choose_eq_zero_of_lt hjr, Nat.cast_zero, mul_zero, zero_mul]

/-- Literal source error after the exact Gaussian factor is removed. -/
def gaussianProfileError (q : ℝ) (z : ℂ) : ℂ := gaussianRelativeProfile q z - 1

theorem gaussianProfileError_entire (q : ℝ) : Differentiable ℂ (gaussianProfileError q) := by
  unfold gaussianProfileError gaussianRelativeProfile firstAtomGaussianKernel
    gaussianReflectionCoordinate
  fun_prop

/-- The physical mixed error has precisely the one-variable Gaussian multiplier form. -/
theorem firstAtomWickError_eq_gaussianMultiplier {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    firstAtomWickError x =
      gaussianMultiplierKernel (gaussianProfileError (thetaCuspSingleAtomReflectionScale 1 x)) := by
  funext p
  rw [firstAtomWickError, firstAtomWickKernel_eq_relativeProfile hq]
  unfold gaussianMultiplierKernel gaussianProfileError
  ring

/-- One Cauchy radius controls every source-relative coefficient before Gaussian contraction. -/
theorem gaussianProfileError_jet_le {q R : ℝ} (hq : 3 ≤ q) (hR : 1 ≤ R)
    (hRq : 4 * R ^ 2 ≤ q) (hR4q : R ^ 4 ≤ q) (k : ℕ) :
    ‖iteratedDeriv k (gaussianProfileError q) 0‖ ≤
      (k.factorial : ℝ) * (gaussianRelativeErrorConstant * R ^ 4 / q) / R ^ k := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
    (by linarith only [hR] : 0 < R) (gaussianProfileError_entire q).diffContOnCl
  intro z hz
  have hzn : ‖z‖ = R := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
  exact gaussianRelativeProfile_error_le hq hR hRq hR4q hzn.le

#print axioms mixedKernelJet_gaussianMultiplier
#print axioms firstAtomWickError_eq_gaussianMultiplier
#print axioms gaussianProfileError_jet_le

end GaloisForLFunctions.CompletedArithmeticForms
