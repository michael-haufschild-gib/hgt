import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.UniformGaussianLatticeTail
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Scale-uniform Schwartz bounds on the Gaussian lattice

One finite Schwartz seminorm controls the absolute mass of the nonzero Gaussian
samples after multiplication by the squared sampling scale. Arbitrary additive
phases do not change this bound. The full sum differs from its zero-frequency
value by the same uniformly controlled tail.
-/

noncomputable section
open scoped Classical
open Complex

namespace GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson

/-- A finite seminorm controlling fourth-order pointwise decay. -/
def fourthDecayConstant (f : SchwartzMap ℂ ℂ) : ℝ :=
  2 ^ 4 * ((Finset.Iic (4, 0)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) f

/-- Fourth-order decay is supplied by the Schwartz test itself. -/
theorem fourthDecayConstant_bound (f : SchwartzMap ℂ ℂ) (z : ℂ) :
    (1 + ‖z‖) ^ 4 * ‖f z‖ ≤ fourthDecayConstant f := by
  simpa only [fourthDecayConstant, norm_iteratedFDeriv_zero] using
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
      (m := (4, 0)) (k := 4) (n := 0) le_rfl le_rfl f z

/-- The finite decay constant is nonnegative. -/
theorem fourthDecayConstant_nonneg (f : SchwartzMap ℂ ℂ) : 0 ≤ fourthDecayConstant f := by
  have h := fourthDecayConstant_bound f 0
  simp only [norm_zero, add_zero, one_pow, one_mul] at h
  exact (norm_nonneg (f 0)).trans h

/-- An arbitrary additive phase on the Gaussian lattice. -/
def gaussianPhase (a : ℂ) (z : GaussianInt) : ℂ :=
  Complex.exp ((2 * Real.pi * (a * (z : ℂ)).re : ℝ) * I)

/-- Additive phases have unit modulus at every lattice point. -/
theorem norm_gaussianPhase (a : ℂ) (z : GaussianInt) : ‖gaussianPhase a z‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The phase-modulated Schwartz samples with the origin removed. -/
def schwartzLatticeTail (f : SchwartzMap ℂ ℂ) (s : PositiveScale) (a : ℂ)
    (z : GaussianInt) : ℂ :=
  if z = 0 then 0 else gaussianPhase a z * f ((s.val : ℂ) * (z : ℂ))

/-- The Gaussian envelope controls every phase-modulated sample pointwise. -/
theorem norm_schwartzLatticeTail_le (f : SchwartzMap ℂ ℂ) (s : PositiveScale)
    (a : ℂ) (z : GaussianInt) :
    ‖schwartzLatticeTail f s a z‖ ≤ fourthDecayConstant f * gaussianTail s z := by
  by_cases hz : z = 0
  · simp [schwartzLatticeTail, gaussianTail, hz]
  · rw [schwartzLatticeTail, if_neg hz, norm_mul, norm_gaussianPhase, one_mul,
      gaussianTail, if_neg hz]
    have h := fourthDecayConstant_bound f ((s.val : ℂ) * (z : ℂ))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg s.property.le] at h
    have hd : 0 < (1 + s.val * ‖(z : ℂ)‖) ^ 4 := by
      have hs : 0 < s.val := s.property
      positivity
    rw [mul_one_div, le_div_iff₀ hd]
    simpa only [mul_comm] using h

/-- Absolute convergence is proved for every scale and phase. -/
theorem summable_norm_schwartzLatticeTail (f : SchwartzMap ℂ ℂ) (s : PositiveScale) (a : ℂ) :
    Summable (fun z : GaussianInt => ‖schwartzLatticeTail f s a z‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_schwartzLatticeTail_le f s a)
    ((summable_gaussianTail s).mul_left (fourthDecayConstant f))

/-- Complex convergence follows from the established absolute convergence. -/
theorem summable_schwartzLatticeTail (f : SchwartzMap ℂ ℂ) (s : PositiveScale) (a : ℂ) :
    Summable (schwartzLatticeTail f s a) :=
  summable_norm_iff.mp (summable_norm_schwartzLatticeTail f s a)

/-- Absolute tail mass is bounded uniformly in both scale and additive phase. -/
theorem scaled_schwartzLatticeTail_mass_le (f : SchwartzMap ℂ ℂ) (s : PositiveScale) (a : ℂ) :
    s.val ^ 2 * (∑' z : GaussianInt, ‖schwartzLatticeTail f s a z‖) ≤
      12 * fourthDecayConstant f := by
  have hs := summable_norm_schwartzLatticeTail f s a
  have hm := (summable_gaussianTail s).mul_left (fourthDecayConstant f)
  have hsum := Summable.tsum_le_tsum (norm_schwartzLatticeTail_le f s a) hs hm
  rw [tsum_mul_left] at hsum
  calc
    _ ≤ s.val ^ 2 * (fourthDecayConstant f * ∑' z : GaussianInt, gaussianTail s z) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg s.val)
    _ = fourthDecayConstant f * (s.val ^ 2 * ∑' z : GaussianInt, gaussianTail s z) := by ring
    _ ≤ fourthDecayConstant f * 12 :=
      mul_le_mul_of_nonneg_left (scaled_gaussianTail_le s) (fourthDecayConstant_nonneg f)
    _ = _ := mul_comm _ _

/-- The complex tail inherits the same scale-uniform estimate. -/
theorem scaled_norm_schwartzLatticeTail_le (f : SchwartzMap ℂ ℂ) (s : PositiveScale) (a : ℂ) :
    s.val ^ 2 * ‖∑' z : GaussianInt, schwartzLatticeTail f s a z‖ ≤
      12 * fourthDecayConstant f :=
  (mul_le_mul_of_nonneg_left
    (norm_tsum_le_tsum_norm (summable_norm_schwartzLatticeTail f s a)) (sq_nonneg s.val)).trans
      (scaled_schwartzLatticeTail_mass_le f s a)

/-- The complete phase-modulated Gaussian lattice sum. -/
def schwartzLatticeSum (f : SchwartzMap ℂ ℂ) (s : PositiveScale) (a : ℂ) : ℂ :=
  ∑' z : GaussianInt, gaussianPhase a z * f ((s.val : ℂ) * (z : ℂ))

private theorem latticeTerm_eq (f : SchwartzMap ℂ ℂ) (s : PositiveScale) (a : ℂ) :
    (fun z : GaussianInt => gaussianPhase a z * f ((s.val : ℂ) * (z : ℂ))) =
      fun z => (if z = 0 then f 0 else 0) + schwartzLatticeTail f s a z := by
  funext z
  by_cases hz : z = 0 <;> simp [schwartzLatticeTail, gaussianPhase, hz]

/-- The full lattice series is summable, including its zero term. -/
theorem summable_schwartzLattice (f : SchwartzMap ℂ ℂ) (s : PositiveScale) (a : ℂ) :
    Summable (fun z : GaussianInt => gaussianPhase a z * f ((s.val : ℂ) * (z : ℂ))) := by
  rw [latticeTerm_eq]
  exact (hasSum_ite_eq (0 : GaussianInt) (f 0)).summable.add
    (summable_schwartzLatticeTail f s a)

/-- The absolute mass also splits exactly into the origin and the punctured tail. -/
theorem schwartzLattice_mass_eq (f : SchwartzMap ℂ ℂ) (s : PositiveScale) (a : ℂ) :
    (∑' z : GaussianInt, ‖gaussianPhase a z * f ((s.val : ℂ) * (z : ℂ))‖) =
      ‖f 0‖ + ∑' z : GaussianInt, ‖schwartzLatticeTail f s a z‖ := by
  have hd := hasSum_ite_eq (0 : GaussianInt) ‖f 0‖
  have he : (fun z : GaussianInt =>
      ‖gaussianPhase a z * f ((s.val : ℂ) * (z : ℂ))‖) =
      fun z => (if z = 0 then ‖f 0‖ else 0) + ‖schwartzLatticeTail f s a z‖ := by
    funext z
    by_cases hz : z = 0 <;> simp [schwartzLatticeTail, gaussianPhase, hz]
  rw [he, hd.summable.tsum_add (summable_norm_schwartzLatticeTail f s a), hd.tsum_eq]

/-- After removing the absolute mass at zero, all phases share the same bound. -/
theorem scaled_schwartz_mass_sub_zero_le (f : SchwartzMap ℂ ℂ) (s : PositiveScale) (a : ℂ) :
    s.val ^ 2 * ((∑' z : GaussianInt,
      ‖gaussianPhase a z * f ((s.val : ℂ) * (z : ℂ))‖) - ‖f 0‖) ≤
      12 * fourthDecayConstant f := by
  rw [schwartzLattice_mass_eq, add_sub_cancel_left]
  exact scaled_schwartzLatticeTail_mass_le f s a

/-- Removing the origin subtracts exactly the value of the test at zero. -/
theorem schwartzLatticeSum_eq (f : SchwartzMap ℂ ℂ) (s : PositiveScale) (a : ℂ) :
    schwartzLatticeSum f s a = f 0 + ∑' z : GaussianInt, schwartzLatticeTail f s a z := by
  have hd := hasSum_ite_eq (0 : GaussianInt) (f 0)
  rw [schwartzLatticeSum, latticeTerm_eq,
    hd.summable.tsum_add (summable_schwartzLatticeTail f s a), hd.tsum_eq]

/-- The zero term is the only part excluded from the uniform scaled estimate. -/
theorem scaled_schwartz_sum_sub_zero_le (f : SchwartzMap ℂ ℂ) (s : PositiveScale) (a : ℂ) :
    s.val ^ 2 * ‖schwartzLatticeSum f s a - f 0‖ ≤ 12 * fourthDecayConstant f := by
  rw [schwartzLatticeSum_eq, add_sub_cancel_left]
  exact scaled_norm_schwartzLatticeTail_le f s a

end GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson
