import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.CoreCauchyAnalyticContinuation
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.HeckeScatteringBoundaryCorrection
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Corrected Hecke transport of the actual physical core

Two physical evaluations recover the zeta-axis and scattering coefficients. Their
nonvanishing determinant follows from the strict exponential chord inequality.
Retaining both boundary corrections gives the arithmetic eigenvalue for every
prime on the literal Cauchy core, with a single surviving channel at resonances.
-/

set_option autoImplicit false
noncomputable section
open Complex Set
open GaloisForLFunctions RenormalizedIntersectionTheory MayerScatteringCore
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

private theorem dyadic_strict_chord {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) :
    (2 : ℝ) ^ σ < 1 + σ := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := strictConvexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (Real.log 2))
    (ne_of_lt hlog) (sub_pos.mpr hσ1) hσ
    (show (1 - σ) + σ = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero,
    Real.exp_log (by norm_num : (0 : ℝ) < 2), mul_one] at h
  rw [Real.rpow_def_of_pos (by norm_num)]
  calc
    Real.exp (Real.log 2 * σ) = Real.exp (σ * Real.log 2) := by congr 1; ring
    _ < (1 - σ) + σ * 2 := h
    _ = 1 + σ := by ring

/-- Two physical evaluations recover the boundary coefficients throughout the open strip. -/
theorem coreBoundaryDeterminant_ne_zero {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1) :
    1 - (w + 1) * (2 : ℂ) ^ (-w) ≠ 0 := by
  intro hz
  have he : (w + 1) * (2 : ℂ) ^ (-w) = 1 := (sub_eq_zero.mp hz).symm
  have hp : (2 : ℂ) ^ (-w) * (2 : ℂ) ^ w = 1 := by
    rw [← Complex.cpow_add (-w) w (by norm_num : (2 : ℂ) ≠ 0), neg_add_cancel, Complex.cpow_zero]
  have heq : w + 1 = (2 : ℂ) ^ w := by
    have h := congrArg (fun z : ℂ => z * (2 : ℂ) ^ w) he
    rwa [mul_assoc, hp, mul_one, one_mul] at h
  have hn := Complex.re_le_norm (w + 1)
  simp only [Complex.add_re, Complex.one_re] at hn
  rw [heq, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)] at hn
  exact (not_le_of_gt (dyadic_strict_chord hw hw1)) (by linarith only [hn])

#print axioms coreBoundaryDeterminant_ne_zero

/-- The scattering coordinate determined by the values at `1` and `2`. -/
def mayerCoreScatteringCoordinate (s : ℂ) (f : ℝ → ℂ) : ℂ :=
  (2 * f 2 - (1 + (2 : ℂ) ^ (-(2 * s))) * f 1) /
    (1 - (2 * s + 1) * (2 : ℂ) ^ (-(2 * s)))

/-- The zeta-axis coordinate determined by the same two evaluations. -/
def mayerCoreZetaCoordinate (s : ℂ) (f : ℝ → ℂ) : ℂ :=
  ((2 * s - 3) * mayerCoreScatteringCoordinate s f - f 1) / 2

private theorem core_one_all_parameters {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) :
    mayerPeriodCore s 1 = (2 * riemannZeta (2 * s - 1) / (2 * s - 1)) * (2 * s - 3) -
      2 * riemannZeta (2 * s) := by
  have hden : 2 * s - 1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith only [hi, him]
  rw [mayerPeriodCore_eq_eisenstein_sub_boundary hs hs1 him (by norm_num), Complex.ofReal_one,
    eisensteinLewisPeriod_one_eq hs hs1]
  simp only [scatteringPowers, Complex.ofReal_one, Complex.one_cpow]
  field_simp [hden]
  ring

private theorem core_two_all_parameters {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) :
    2 * mayerPeriodCore s 2 =
      (2 * riemannZeta (2 * s - 1) / (2 * s - 1)) *
        (2 * s - 2 - 4 * (2 : ℂ) ^ (-(2 * s))) -
      2 * riemannZeta (2 * s) * (1 + (2 : ℂ) ^ (-(2 * s))) := by
  have hinv := lewisModularInversion_mayerPeriodCore hs him (a := 2) (by norm_num)
  change (2 : ℂ) ^ (-(2 * s)) * mayerPeriodCore s (2 : ℝ)⁻¹ =
    mayerPeriodCore s 2 at hinv
  have hh := hecke_mayerPeriodCore_at_one hs him
  rw [lewisHeckeT2] at hh
  norm_num only [mul_one, div_self (by norm_num : (2 : ℝ) ≠ 0),
    Complex.ofReal_ofNat, one_div] at hh
  simp only [one_div] at hh
  rw [hinv] at hh
  have hc := core_one_all_parameters hs hs1 him
  linear_combination hh + hc

/-- The physical evaluation coordinate recovers the exact scattering coefficient. -/
theorem mayerCoreScatteringCoordinate_core {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) :
    mayerCoreScatteringCoordinate s (mayerPeriodCore s) =
      2 * riemannZeta (2 * s - 1) / (2 * s - 1) := by
  have hw : 0 < (2 * s).re := by simp; linarith only [hs]
  have hw1 : (2 * s).re < 1 := by simp; linarith only [hs1]
  have hd := coreBoundaryDeterminant_ne_zero hw hw1
  rw [mayerCoreScatteringCoordinate, core_two_all_parameters hs hs1 him,
    core_one_all_parameters hs hs1 him]
  apply (div_eq_iff hd).mpr
  ring

/-- The second physical coordinate recovers the zeta-axis coefficient, including off resonance. -/
theorem mayerCoreZetaCoordinate_core {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) :
    mayerCoreZetaCoordinate s (mayerPeriodCore s) = riemannZeta (2 * s) := by
  rw [mayerCoreZetaCoordinate, mayerCoreScatteringCoordinate_core hs hs1 him,
    core_one_all_parameters hs hs1 him]
  ring

/-- The actual Hecke operator with its two boundary channels recovered from the input.
The correction has rank at most two on the space of physical functions. -/
def mayerCorrectedHeckeT2 (s : ℂ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  lewisHeckeT2 s f a +
    mayerCoreZetaCoordinate s f *
      (lewisHeckeT2 s (fun x : ℝ => 1 + (x : ℂ) ^ (-(2 * s))) a -
        (1 + 2 * (2 : ℂ) ^ (-(2 * s))) * (1 + (a : ℂ) ^ (-(2 * s)))) +
    mayerCoreScatteringCoordinate s f *
      (lewisHeckeT2 s (scatteringPowers (2 * s)) a -
        (1 + 2 * (2 : ℂ) ^ (-(2 * s))) * scatteringPowers (2 * s) a)

/-- The corrected source Hecke action has the completed eigenvalue on the actual PM core,
throughout the upper open strip and at every positive coordinate. -/
theorem mayerCorrectedHeckeT2_core {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) {a : ℝ} (ha : 0 < a) :
    mayerCorrectedHeckeT2 s (mayerPeriodCore s) a =
      (1 + 2 * (2 : ℂ) ^ (-(2 * s))) * mayerPeriodCore s a := by
  have hE := eisensteinLewisPeriod_hecke hs hs1 ha
  rw [lewisHeckeT2] at hE
  rw [mayerCorrectedHeckeT2, mayerCoreZetaCoordinate_core hs hs1 him,
    mayerCoreScatteringCoordinate_core hs hs1 him]
  simp only [lewisHeckeT2]
  rw [mayerPeriodCore_eq_eisenstein_sub_boundary hs hs1 him (by positivity : 0 < 2 * a),
    mayerPeriodCore_eq_eisenstein_sub_boundary hs hs1 him (by positivity : 0 < a / 2),
    mayerPeriodCore_eq_eisenstein_sub_boundary hs hs1 him (by positivity : 0 < (a + 1) / 2),
    mayerPeriodCore_eq_eisenstein_sub_boundary hs hs1 him (by positivity : 0 < 2 * a / (a + 1)),
    mayerPeriodCore_eq_eisenstein_sub_boundary hs hs1 him ha]
  linear_combination hE

#print axioms mayerCoreScatteringCoordinate_core
#print axioms mayerCoreZetaCoordinate_core
#print axioms mayerCorrectedHeckeT2_core

/-- The same two physical coordinates correct every actual prime Hecke correspondence. -/
def mayerCorrectedHeckeOperator (p : ℕ) (s : ℂ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  lewisHeckeOperator p s f a +
    mayerCoreZetaCoordinate s f *
      (lewisHeckeOperator p s (fun x : ℝ => 1 + (x : ℂ) ^ (-(2 * s))) a -
        (1 + (p : ℂ) ^ (1 - 2 * s)) * (1 + (a : ℂ) ^ (-(2 * s)))) +
    mayerCoreScatteringCoordinate s f *
      (lewisHeckeOperator p s (scatteringPowers (2 * s)) a -
        (1 + (p : ℂ) ^ (1 - 2 * s)) * scatteringPowers (2 * s) a)

/-- Every corrected source prime correspondence acts on the actual core with its
arithmetic eigenvalue. Boundary coordinates are recovered from physical evaluations. -/
theorem mayerCorrectedHeckeOperator_core {p : ℕ} [Fact p.Prime] {s : ℂ}
    (hs : 0 < s.re) (hs1 : s.re < 1 / 2) (him : 0 < s.im) {a : ℝ} (ha : 0 < a) :
    mayerCorrectedHeckeOperator p s (mayerPeriodCore s) a =
      (1 + (p : ℂ) ^ (1 - 2 * s)) * mayerPeriodCore s a := by
  have hraw : lewisHeckeOperator p s (mayerPeriodCore s) a =
      lewisHeckeOperator p s (fun x : ℝ => eisensteinLewisPeriod s x) a -
        riemannZeta (2 * s) *
          lewisHeckeOperator p s (fun x : ℝ => 1 + (x : ℂ) ^ (-(2 * s))) a -
        (2 * riemannZeta (2 * s - 1) / (2 * s - 1)) *
          lewisHeckeOperator p s (scatteringPowers (2 * s)) a := by
    simp only [lewisHeckeOperator, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro M hM
    obtain ⟨hc, hx⟩ := heckeBranch_pos hM ha
    rw [mayerPeriodCore_eq_eisenstein_sub_boundary hs hs1 him (div_pos hx hc)]
    ring
  rw [mayerCorrectedHeckeOperator, mayerCoreZetaCoordinate_core hs hs1 him,
    mayerCoreScatteringCoordinate_core hs hs1 him, hraw,
    eisensteinLewisPeriod_lewisHecke hs hs1 ha,
    mayerPeriodCore_eq_eisenstein_sub_boundary hs hs1 him ha]
  ring

/-- At every upper resonance the zeta-axis channel vanishes, leaving one exact
scattering correction for every prime. -/
theorem mayerPeriodCore_prime_hecke_rank_one {p : ℕ} [Fact p.Prime] {s : ℂ}
    (hs : s ∈ upperMayerResonances) {a : ℝ} (ha : 0 < a) :
    lewisHeckeOperator p s (mayerPeriodCore s) a +
      (mayerPeriodCore s 1 / (2 * s - 3)) *
        (lewisHeckeOperator p s (scatteringPowers (2 * s)) a -
          (1 + (p : ℂ) ^ (1 - 2 * s)) * scatteringPowers (2 * s) a) =
      (1 + (p : ℂ) ^ (1 - 2 * s)) * mayerPeriodCore s a := by
  have hz : riemannZeta (2 * s) = 0 :=
    (isMayerScatteringResonance_iff_zeta_zero hs.2.1 hs.2.2.1).mp hs.2
  have hden : 2 * s - 3 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith only [hi, hs.1]
  have hcoord : mayerPeriodCore s 1 / (2 * s - 3) =
      2 * riemannZeta (2 * s - 1) / (2 * s - 1) := by
    rw [core_one_all_parameters hs.2.1 hs.2.2.1 hs.1, hz, mul_zero, sub_zero]
    exact mul_div_cancel_right₀ _ hden
  have h := mayerCorrectedHeckeOperator_core (p := p) hs.2.1 hs.2.2.1 hs.1 ha
  rw [mayerCorrectedHeckeOperator, mayerCoreZetaCoordinate_core hs.2.1 hs.2.2.1 hs.1,
    mayerCoreScatteringCoordinate_core hs.2.1 hs.2.2.1 hs.1, hz, zero_mul, add_zero] at h
  rwa [hcoord]

#print axioms mayerCorrectedHeckeOperator_core
#print axioms mayerPeriodCore_prime_hecke_rank_one

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
