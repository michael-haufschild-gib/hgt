import GaloisForLFunctions.RHTower.WeldOrderFiltration
import GaloisForLFunctions.RHTower.L2FourierReflection
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Bounded spectral gauges are forced to have order zero

`WeldOrderFiltration` identifies the weld as a nonzero class modulo order-zero gauge, but that
restriction is useful only if the fixed representation forces it.  This file proves that it does on
the project's critical-line spectral space `L²(ℝ)`.

Coordinate multiplication is the spectral realization of the derivation direction.  Normalized
indicators of the unit intervals `[N,N+1]` have norm one, whereas their coordinate multiples have
norm at least `N`.  Hence coordinate multiplication has no bounded extension.  More generally, a
bounded operator agreeing with `aD+bI` on these explicit domain vectors forces `a=0`.

Consequently every concretely bounded affine weld cochain is automatically order zero, and no such
cochain can trivialize a nonzero prime weld.  The interval index is only an unboundedness witness; it
does not transport the datum or construct a carrier.
-/

open MeasureTheory Set
open GaloisForLFunctions
open scoped ENNReal

noncomputable section
namespace GaloisForLFunctions.RHTower

/-- The fixed critical-line spectral Hilbert space `L²(ℝ)`. -/
abbrev WeldSpectralL2 := _root_.RHTower.FourierRealL2

/-- Unit intervals escaping to high spectral frequency. -/
def weldSpectralInterval (N : ℕ) : Set ℝ := Set.Icc (N : ℝ) (N + 1 : ℝ)

theorem volume_weldSpectralInterval (N : ℕ) :
    volume (weldSpectralInterval N) = 1 := by
  rw [weldSpectralInterval, Real.volume_Icc]
  norm_num

theorem volume_weldSpectralInterval_ne_top (N : ℕ) :
    volume (weldSpectralInterval N) ≠ ∞ := by
  rw [volume_weldSpectralInterval]
  exact ENNReal.one_ne_top

/-- The normalized constant vector on `[N,N+1]`. -/
def weldSpectralUnitVector (N : ℕ) : WeldSpectralL2 :=
  indicatorConstLp 2 measurableSet_Icc (volume_weldSpectralInterval_ne_top N) (1 : ℂ)

theorem norm_weldSpectralUnitVector (N : ℕ) : ‖weldSpectralUnitVector N‖ = 1 := by
  rw [weldSpectralUnitVector,
    norm_indicatorConstLp (p := 2) (μ := volume) (by norm_num) (by norm_num)]
  simp [measureReal_def, Real.volume_Icc]

/-- Coordinate multiplication of a compactly supported unit-interval vector belongs to `L²`. -/
theorem memLp_weldSpectralCoordinate (N : ℕ) :
    MemLp ((weldSpectralInterval N).indicator fun x : ℝ => (x : ℂ)) 2 volume := by
  unfold weldSpectralInterval
  rw [memLp_indicator_iff_restrict measurableSet_Icc]
  apply MemLp.of_bound
  · exact Complex.continuous_ofReal.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · exact hx.2
    · exact le_trans (Nat.cast_nonneg N) hx.1

/-- The coordinate multiple `x 1_[N,N+1]`, viewed in `L²(ℝ)`. -/
def weldSpectralCoordinateVector (N : ℕ) : WeldSpectralL2 :=
  (memLp_weldSpectralCoordinate N).toLp _

theorem weldSpectralCoordinateVector_ae (N : ℕ) :
    weldSpectralCoordinateVector N =ᵐ[volume]
      (weldSpectralInterval N).indicator fun x : ℝ => (x : ℂ) :=
  (memLp_weldSpectralCoordinate N).coeFn_toLp

theorem weldSpectralUnitVector_ae (N : ℕ) :
    weldSpectralUnitVector N =ᵐ[volume]
      (weldSpectralInterval N).indicator fun _ : ℝ => (1 : ℂ) :=
  indicatorConstLp_coeFn

/-- Coordinate multiplication sends the norm-one `N`th packet to a vector of norm at least `N`. -/
theorem nat_le_norm_weldSpectralCoordinateVector (N : ℕ) :
    (N : ℝ) ≤ ‖weldSpectralCoordinateVector N‖ := by
  have hpoint : ∀ᵐ x : ℝ ∂volume,
      ‖(((N : ℂ) • weldSpectralUnitVector N : WeldSpectralL2) : ℝ → ℂ) x‖ ≤
        ‖weldSpectralCoordinateVector N x‖ := by
    filter_upwards [Lp.coeFn_smul (N : ℂ) (weldSpectralUnitVector N),
      weldSpectralUnitVector_ae N, weldSpectralCoordinateVector_ae N]
      with x hsmul hunit hcoord
    rw [hsmul, hcoord]
    change ‖(N : ℂ) * weldSpectralUnitVector N x‖ ≤
      ‖(weldSpectralInterval N).indicator (fun x : ℝ => (x : ℂ)) x‖
    rw [hunit]
    by_cases hx : x ∈ weldSpectralInterval N
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      simp only [mul_one, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs]
      rw [abs_of_nonneg (le_trans (Nat.cast_nonneg N) hx.1)]
      exact hx.1
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  have hnorm := Lp.norm_le_norm_of_ae_le hpoint
  rw [norm_smul, norm_weldSpectralUnitVector, mul_one, Complex.norm_natCast] at hnorm
  exact hnorm

/-- Coordinate multiplication on its explicit unit-interval domain has no bounded extension. -/
theorem no_bounded_weldSpectralCoordinate :
    ¬ ∃ T : WeldSpectralL2 →L[ℂ] WeldSpectralL2,
      ∀ N, T (weldSpectralUnitVector N) = weldSpectralCoordinateVector N := by
  rintro ⟨T, hT⟩
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ‖T‖
  have hlower := nat_le_norm_weldSpectralCoordinateVector N
  have hupper : ‖weldSpectralCoordinateVector N‖ ≤ ‖T‖ := by
    rw [← hT N]
    simpa [norm_weldSpectralUnitVector] using T.le_opNorm (weldSpectralUnitVector N)
  exact (not_lt_of_ge (hlower.trans hupper)) hN

/-- **Boundedness forces order zero.**  If a bounded operator agrees with `aD+bI` on the explicit
spectral domain vectors, then its derivation coefficient `a` vanishes. -/
theorem bounded_weldSpectralAffine_forces_orderZero
    (T : WeldSpectralL2 →L[ℂ] WeldSpectralL2) (a b : ℂ)
    (hT : ∀ N, T (weldSpectralUnitVector N) =
      a • weldSpectralCoordinateVector N + b • weldSpectralUnitVector N) :
    a = 0 := by
  by_contra ha
  let S : WeldSpectralL2 →L[ℂ] WeldSpectralL2 :=
    (a⁻¹ • T) - ((a⁻¹ * b) • ContinuousLinearMap.id ℂ WeldSpectralL2)
  apply no_bounded_weldSpectralCoordinate
  refine ⟨S, ?_⟩
  intro N
  change a⁻¹ • T (weldSpectralUnitVector N) -
      (a⁻¹ * b) • weldSpectralUnitVector N = weldSpectralCoordinateVector N
  rw [hT N, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ha, one_smul]
  module

/-- Data realizing every affine cochain value as a bounded operator on the fixed spectral `L²`
space.  The action equation is required only on vectors in the coordinate-multiplier domain. -/
structure BoundedWeldSpectralCochain (θ : ℝ)
    (b : WeldGroup → WeldAffineCoeff θ) where
  operator : WeldGroup → (WeldSpectralL2 →L[ℂ] WeldSpectralL2)
  realizes : ∀ g N, operator g (weldSpectralUnitVector N) =
    ((b g).1 : ℂ) • weldSpectralCoordinateVector N +
      ((b g).2 : ℂ) • weldSpectralUnitVector N

/-- Every concretely bounded spectral affine cochain is order zero; no admissibility Prop is needed. -/
theorem BoundedWeldSpectralCochain.isOrderZero {θ : ℝ}
    {b : WeldGroup → WeldAffineCoeff θ} (B : BoundedWeldSpectralCochain θ b) :
    IsOrderZeroAffineCochain θ b := by
  intro g
  change (b g).1 = 0
  have hcomplex : ((b g).1 : ℂ) = 0 :=
    bounded_weldSpectralAffine_forces_orderZero (B.operator g)
      ((b g).1 : ℂ) ((b g).2 : ℂ) (B.realizes g)
  exact_mod_cast hcomplex

/-- A nonzero weld cocycle has no primitive realized by bounded affine operators on spectral `L²`. -/
theorem no_boundedWeldSpectralPrimitive {θ : ℝ} (hθ : θ ≠ 0) :
    ¬ ∃ b : WeldGroup → WeldAffineCoeff θ,
      Nonempty (BoundedWeldSpectralCochain θ b) ∧
        twoCoboundary b = weldAffineCocycle θ := by
  rintro ⟨b, ⟨B⟩, hb⟩
  exact no_orderZeroAffinePrimitive hθ ⟨b, B.isOrderZero, hb⟩

/-- Every prime weld has no bounded affine spectral primitive. -/
theorem prime_no_boundedWeldSpectralPrimitive {p : ℕ} (hp : p.Prime) :
    ¬ ∃ b : WeldGroup → WeldAffineCoeff (Real.log p),
      Nonempty (BoundedWeldSpectralCochain (Real.log p) b) ∧
        twoCoboundary b = weldAffineCocycle (Real.log p) :=
  no_boundedWeldSpectralPrimitive
    (ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt)))

end GaloisForLFunctions.RHTower
