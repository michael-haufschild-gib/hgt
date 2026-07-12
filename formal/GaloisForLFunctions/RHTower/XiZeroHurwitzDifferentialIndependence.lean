import GaloisForLFunctions.Hurwitz.IntegerTranslationDifferentialMatroid
import GaloisForLFunctions.RHTower.XiCanonicalProduct

/-!
# Hurwitz differential independence indexed by Xi zeros

The intrinsic `ℂ/ℤ` differential-matroid law for the continued Hurwitz family becomes
hypothesis-free on every finite injective family of actual Xi-divisor support points.  The reason
is purely value-theoretic: every Xi zero has real part strictly between zero and one, so it is
nonintegral, and two such strip points can differ by an integer only when they are equal.

This is the direct interface between the Xi divisor and Hurwitz shift hypertranscendence.  It does
not locate the Xi zeros.  It says that once distinct divisor values are selected, the corresponding
Hurwitz functions admit no joint algebraic differential relation over `ℂ(a)`.
-/

open Complex
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential

namespace RHTower

noncomputable section

open HurwitzJointLadder HurwitzOrbit
open GaloisForLFunctions.HTGeometry

/-- A point in the open critical strip is not an integer. -/
theorem openCriticalStrip_point_ne_int {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) (m : ℤ) :
    s ≠ (m : ℂ) := by
  intro h
  have hre : s.re = (m : ℝ) := by
    have := congrArg Complex.re h
    simpa using this
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have hmle : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
    linarith
  · subst m
    norm_num at hre
    linarith
  · have hmge : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
    linarith

/-- Two open-critical-strip points in the same residue class modulo `ℤ` are equal. -/
theorem openCriticalStrip_eq_of_sub_eq_int {s t : ℂ}
    (hs : 0 < s.re ∧ s.re < 1) (ht : 0 < t.re ∧ t.re < 1)
    (m : ℤ) (h : s - t = (m : ℂ)) : s = t := by
  have hre : s.re - t.re = (m : ℝ) := by
    have := congrArg Complex.re h
    simpa using this
  have hm0 : m = 0 := by
    rcases lt_trichotomy m 0 with hm | hm | hm
    · have hmle : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
      linarith
    · exact hm
    · have hmge : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
      linarith
  subst m
  have hzero : s - t = 0 := by simpa using h
  exact sub_eq_zero.mp hzero

/-- **Xi-zero Hurwitz differential-independence law.**  Every finite injective family of actual
Xi-divisor support points indexes a jointly differentially independent family of analytically
continued Hurwitz functions in the shift variable. -/
theorem xi_zero_hurwitz_differentialIndependent
    {I : Type*} [Fintype I] [DecidableEq I]
    (ρ : I → XiDivisorSupport) (hρ : Function.Injective ρ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun i => continuedHzetaUpperEndMero ((ρ i : XiDivisorSupport) : ℂ)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let s : I → ℂ := fun i => (ρ i : XiDivisorSupport)
  have hstrip : ∀ i, 0 < (s i).re ∧ (s i).re < 1 := by
    intro i
    exact xi_divisor_support_re_mem_open_unit (ρ i)
  have hnon : ∀ i, ∀ m : ℤ, s i ≠ (m : ℂ) := by
    intro i m
    exact openCriticalStrip_point_ne_int (hstrip i) m
  rw [continued_hurwitz_intrinsic_residue_differentialMatroid_law s hnon]
  intro i j hmono
  apply hρ
  apply Subtype.ext
  obtain ⟨m, hm⟩ :=
    (monoScalar_eq_monoScalar_iff_integerDifference (s i) (s j)).mp hmono
  exact openCriticalStrip_eq_of_sub_eq_int (hstrip i) (hstrip j) m hm

end

end RHTower
