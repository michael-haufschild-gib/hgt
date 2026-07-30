import Mathlib.Analysis.Complex.Poisson
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeBoundary

/-!
# Finite Blaschke all-pass group delay

For a disk parameter `a`, the boundary phase rate of the all-pass section

`bₐ(z) = (z - a) / (1 - conj(a) z)`

is the disk Poisson kernel.  This is the standard group-delay law from lossless discrete-time
all-pass filtering.  Products add their group delays, so every nonempty finite Blaschke product
has strictly positive boundary phase rate.

The final theorem applies the value law to the existing paraorthogonal terminal equation.  The
existing root-location theorem supplies `‖z‖ = 1`; Poisson positivity then discharges derivative
nonvanishing at the root.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exact complex derivative of one disk Blaschke factor away from its denominator pole. -/
theorem hasDerivAt_blaschkeFactor {a z : ℂ}
    (hden : 1 - star a * z ≠ 0) :
    HasDerivAt (fun w : ℂ => (w - a) / (1 - star a * w))
      ((1 - star a * a) / (1 - star a * z) ^ 2) z := by
  have hnum : HasDerivAt (fun w : ℂ => w - a) 1 z :=
    (hasDerivAt_id z).sub_const a
  have hden' : HasDerivAt (fun w : ℂ => 1 - star a * w) (-star a) z := by
    convert! (hasDerivAt_const z (1 : ℂ)).sub
      ((hasDerivAt_const z (star a)).mul (hasDerivAt_id z)) using 1
    all_goals ring
  convert! hnum.div hden' hden using 1
  all_goals ring

/-- On the unit circle, the Poisson kernel is the squared-modulus ratio used by the all-pass
group-delay formula. -/
theorem poissonKernel_zero_eq_normSq_ratio {a z : ℂ} (hz : ‖z‖ = 1) :
    poissonKernel 0 a z =
      (1 - Complex.normSq a) / Complex.normSq (z - a) := by
  rw [poissonKernel_def]
  simp [Complex.normSq_eq_norm_sq, hz]

/-- A disk point and a unit-circle point are distinct. -/
private theorem unitCircle_sub_diskPoint_ne_zero {a z : ℂ}
    (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    z - a ≠ 0 := by
  rw [sub_ne_zero]
  intro hza
  have hnorm := congrArg norm hza
  rw [hz] at hnorm
  linarith

/-- **Single-section all-pass group delay.**  The angular logarithmic derivative of a stable
Blaschke section is exactly its disk Poisson kernel on the unit circle. -/
theorem mul_logDeriv_blaschkeFactor_eq_poissonKernel {a z : ℂ}
    (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    z * logDeriv (fun w : ℂ => (w - a) / (1 - star a * w)) z =
      (poissonKernel 0 a z : ℂ) := by
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hz
    norm_num at hz
  have hza : z - a ≠ 0 := unitCircle_sub_diskPoint_ne_zero ha hz
  have hstarza : star (z - a) ≠ 0 := star_ne_zero.mpr hza
  have hden : 1 - star a * z ≠ 0 :=
    blaschkeFactor_den_ne_zero ha hz.le
  have hunit : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hden_eq : 1 - star a * z = z * star (z - a) := by
    rw [star_sub]
    calc
      1 - star a * z = z * star z - star a * z := by rw [hunit]
      _ = z * (star z - star a) := by ring
  rw [logDeriv_apply, (hasDerivAt_blaschkeFactor hden).deriv,
    poissonKernel_zero_eq_normSq_ratio hz]
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self]
  rw [hden_eq]
  rw [Complex.star_def] at hstarza ⊢
  field_simp [hz0, hza, hstarza]

/-- Every stable all-pass section has strictly positive boundary group delay. -/
theorem poissonKernel_zero_pos_of_norm_lt_one {a z : ℂ}
    (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    0 < poissonKernel 0 a z := by
  have hza : z - a ≠ 0 := unitCircle_sub_diskPoint_ne_zero ha hz
  rw [poissonKernel_zero_eq_normSq_ratio hz]
  apply div_pos
  · rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  · exact Complex.normSq_pos.mpr hza

/-- **Cascade group-delay law.**  Boundary group delays add across a finite all-pass cascade. -/
theorem mul_logDeriv_finsetBlaschke_eq_sum_poissonKernel
    {ι : Type*} (s : Finset ι) {a : ι → ℂ}
    (ha : ∀ i ∈ s, ‖a i‖ < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    z * logDeriv
        (fun w : ℂ => ∏ i ∈ s, ((w - a i) / (1 - star (a i) * w))) z =
      ((∑ i ∈ s, poissonKernel 0 (a i) z : ℝ) : ℂ) := by
  have hfac : ∀ i ∈ s, (z - a i) / (1 - star (a i) * z) ≠ 0 := by
    intro i hi
    apply norm_ne_zero_iff.mp
    rw [norm_blaschkeFactor_eq_one (ha i hi) hz]
    norm_num
  have hdiff : ∀ i ∈ s,
      DifferentiableAt ℂ (fun w : ℂ => (w - a i) / (1 - star (a i) * w)) z := by
    intro i hi
    exact (hasDerivAt_blaschkeFactor
      (blaschkeFactor_den_ne_zero (ha i hi) hz.le)).differentiableAt
  have hprod := logDeriv_prod (x := z)
    (f := fun i (w : ℂ) => (w - a i) / (1 - star (a i) * w)) hfac hdiff
  calc
    z * logDeriv
        (fun w : ℂ => ∏ i ∈ s, ((w - a i) / (1 - star (a i) * w))) z =
        ∑ i ∈ s,
          z * logDeriv (fun w : ℂ => (w - a i) / (1 - star (a i) * w)) z := by
            rw [hprod, Finset.mul_sum]
    _ = ∑ i ∈ s, (poissonKernel 0 (a i) z : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_logDeriv_blaschkeFactor_eq_poissonKernel (ha i hi) hz
    _ = ((∑ i ∈ s, poissonKernel 0 (a i) z : ℝ) : ℂ) := by
      push_cast
      rfl

/-- A nonempty stable all-pass cascade has strictly positive boundary phase rate. -/
theorem re_mul_logDeriv_finsetBlaschke_pos
    {ι : Type*} (s : Finset ι) {a : ι → ℂ}
    (ha : ∀ i ∈ s, ‖a i‖ < 1) (hs : s.Nonempty)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 < (z * logDeriv
      (fun w : ℂ => ∏ i ∈ s, ((w - a i) / (1 - star (a i) * w))) z).re := by
  rw [mul_logDeriv_finsetBlaschke_eq_sum_poissonKernel s ha hz]
  simp only [ofReal_re]
  apply Finset.sum_pos'
  · intro i hi
    exact (poissonKernel_zero_pos_of_norm_lt_one (ha i hi) hz).le
  · obtain ⟨i, hi⟩ := hs
    exact ⟨i, hi, poissonKernel_zero_pos_of_norm_lt_one (ha i hi) hz⟩

/-- A nonempty finite Blaschke product has no boundary logarithmic critical point. -/
theorem logDeriv_finsetBlaschke_ne_zero
    {ι : Type*} (s : Finset ι) {a : ι → ℂ}
    (ha : ∀ i ∈ s, ‖a i‖ < 1) (hs : s.Nonempty)
    {z : ℂ} (hz : ‖z‖ = 1) :
    logDeriv
      (fun w : ℂ => ∏ i ∈ s, ((w - a i) / (1 - star (a i) * w))) z ≠ 0 := by
  intro hzero
  have hpos := re_mul_logDeriv_finsetBlaschke_pos s ha hs hz
  rw [hzero, mul_zero, zero_re] at hpos
  exact (lt_irrefl 0 hpos).elim

/-- The terminal all-pass map `z ↦ z B(z) - τ` is noncritical everywhere on the unit circle.  The
extra identity factor contributes one unit of group delay, so this remains true even for the empty
Blaschke product. -/
theorem deriv_finsetBlaschke_terminal_ne_zero
    {ι : Type*} (s : Finset ι) {a : ι → ℂ}
    (ha : ∀ i ∈ s, ‖a i‖ < 1) {z : ℂ} (hz : ‖z‖ = 1) (τ : ℂ) :
    deriv
      (fun w : ℂ =>
        w * (∏ i ∈ s, ((w - a i) / (1 - star (a i) * w))) - τ) z ≠ 0 := by
  let B : ℂ → ℂ :=
    fun w => ∏ i ∈ s, ((w - a i) / (1 - star (a i) * w))
  have hBnorm : ‖B z‖ = 1 := by
    simpa [B] using norm_finsetBlaschke_eq_one s ha hz
  have hB : B z ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hBnorm]
    norm_num
  have hBdiff : DifferentiableAt ℂ B z := by
    dsimp only [B]
    apply DifferentiableAt.fun_finsetProd
    intro i hi
    exact (hasDerivAt_blaschkeFactor
      (blaschkeFactor_den_ne_zero (ha i hi) hz.le)).differentiableAt
  have hphase_nonneg :
      0 ≤ (z * logDeriv B z).re := by
    rw [show z * logDeriv B z =
      ((∑ i ∈ s, poissonKernel 0 (a i) z : ℝ) : ℂ) by
        simpa [B] using mul_logDeriv_finsetBlaschke_eq_sum_poissonKernel s ha hz]
    simp only [ofReal_re]
    exact Finset.sum_nonneg fun i hi =>
      (poissonKernel_zero_pos_of_norm_lt_one (ha i hi) hz).le
  have hshift : 1 + z * logDeriv B z ≠ 0 := by
    intro hzero
    have hre : (1 : ℝ) + (z * logDeriv B z).re = 0 := by
      simpa using congrArg Complex.re hzero
    linarith
  have hmul : HasDerivAt (fun w : ℂ => w * B w)
      (B z + z * deriv B z) z := by
    simpa only [id_eq, one_mul] using!
      (hasDerivAt_id z).mul hBdiff.hasDerivAt
  have hrewrite :
      B z + z * deriv B z = B z * (1 + z * logDeriv B z) := by
    rw [logDeriv_apply]
    field_simp [hB]
  change deriv (fun w : ℂ => w * B w - τ) z ≠ 0
  rw [deriv_sub_const, hmul.deriv, hrewrite]
  exact mul_ne_zero hB hshift

/-- **Direct paraorthogonal consumer.**  Every solution of the existing finite Blaschke terminal
equation is a noncritical (hence simple analytic) root of its terminal function.  Root location
discharges the unit-circle premise; no derivative hypothesis remains. -/
theorem finiteBlaschke_paraorthogonal_root_deriv_ne_zero
    {n : ℕ} (a : Fin n → ℂ) (τ z : ℂ)
    (ha : ∀ i, ‖a i‖ < 1) (hτ : ‖τ‖ = 1)
    (hroot : z * ∏ i, ((z - a i) / (1 - star (a i) * z)) = τ) :
    deriv
      (fun w : ℂ =>
        w * ∏ i, ((w - a i) / (1 - star (a i) * w)) - τ) z ≠ 0 := by
  have hz : ‖z‖ = 1 :=
    finiteBlaschke_paraorthogonal_root_norm_eq_one a τ z ha hτ hroot
  exact deriv_finsetBlaschke_terminal_ne_zero Finset.univ
    (fun i _ => ha i) hz τ

end

end GaloisForLFunctions.HTGeometry
