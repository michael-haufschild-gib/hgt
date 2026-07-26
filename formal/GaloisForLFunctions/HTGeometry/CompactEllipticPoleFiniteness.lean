import GaloisForLFunctions.HTGeometry.JacobiThetaDifferentialOrbitObstruction
import Mathlib.Analysis.Meromorphic.Divisor
import GaloisForLFunctions.HTGeometry.EllipticFundamentalPoles

/-!
# Compact elliptic pole finiteness and the unconditional theta orbit obstruction

An elliptic meromorphic function has only finitely many poles on a nontorsion translation orbit.
The proof reduces the orbit to fractional coordinates in a compact fundamental parallelogram,
uses local finiteness of the meromorphic divisor on that compact set, and uses nontorsion to make
the reduction injective.  This discharges the finiteness hypothesis in the differential theta
orbit obstruction for genuine elliptic coboundary primitives.
-/

open Complex Set Filter Function Metric
open scoped Topology

namespace GaloisForLFunctions

noncomputable section

/-- Reduction of a point to fractional coordinates in the basis `(1, τ)`. -/
def ellipticReduce (τ z : ℂ) : ℂ :=
  ((Int.fract (tauCoordX τ z) : ℝ) : ℂ) +
    ((Int.fract (tauCoordY τ z) : ℝ) : ℂ) * τ

theorem ellipticReduce_norm_le (τ z : ℂ) :
    ‖ellipticReduce τ z‖ ≤ 1 + ‖τ‖ := by
  calc
    ‖ellipticReduce τ z‖ ≤
        ‖((Int.fract (tauCoordX τ z) : ℝ) : ℂ)‖ +
          ‖((Int.fract (tauCoordY τ z) : ℝ) : ℂ) * τ‖ := by
      exact norm_add_le _ _
    _ = Int.fract (tauCoordX τ z) +
        Int.fract (tauCoordY τ z) * ‖τ‖ := by
      rw [norm_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg
          (Int.fract_nonneg (tauCoordX τ z) : 0 ≤ (Int.fract (tauCoordX τ z) : ℝ)),
        abs_of_nonneg
          (Int.fract_nonneg (tauCoordY τ z) : 0 ≤ (Int.fract (tauCoordY τ z) : ℝ))]
    _ ≤ 1 + ‖τ‖ := by
      have hx0 := Int.fract_nonneg (tauCoordX τ z)
      have hx1 := Int.fract_lt_one (tauCoordX τ z)
      have hy0 := Int.fract_nonneg (tauCoordY τ z)
      have hy1 := Int.fract_lt_one (tauCoordY τ z)
      have hn := norm_nonneg τ
      nlinarith

theorem ellipticReduce_lattice_decomposition {τ z : ℂ} (hτ : τ.im ≠ 0) :
    z = ellipticReduce τ z + (⌊tauCoordX τ z⌋ : ℂ) +
      (⌊tauCoordY τ z⌋ : ℂ) * τ := by
  have hx : (tauCoordX τ z : ℂ) =
      ((Int.fract (tauCoordX τ z) : ℝ) : ℂ) + (⌊tauCoordX τ z⌋ : ℂ) := by
    exact_mod_cast (Int.fract_add_floor (tauCoordX τ z)).symm
  have hy : (tauCoordY τ z : ℂ) =
      ((Int.fract (tauCoordY τ z) : ℝ) : ℂ) + (⌊tauCoordY τ z⌋ : ℂ) := by
    exact_mod_cast (Int.fract_add_floor (tauCoordY τ z)).symm
  calc
    z = (tauCoordX τ z : ℂ) + (tauCoordY τ z : ℂ) * τ :=
      tauCoord_decomposition (τ := τ) (z := z) hτ
    _ = (((Int.fract (tauCoordX τ z) : ℝ) : ℂ) +
          (⌊tauCoordX τ z⌋ : ℂ)) +
        (((Int.fract (tauCoordY τ z) : ℝ) : ℂ) +
          (⌊tauCoordY τ z⌋ : ℂ)) * τ := by rw [hx, hy]
    _ = ellipticReduce τ z + (⌊tauCoordX τ z⌋ : ℂ) +
        (⌊tauCoordY τ z⌋ : ℂ) * τ := by
      simp only [ellipticReduce]
      ring

theorem ellipticReduce_injective_on_nontorsion_orbit
    {τ p q : ℂ} (hτ : τ.im ≠ 0) (hq : ThetaTranslationNontorsion τ q) :
    Set.InjOn (fun n : ℤ => ellipticReduce τ (additiveOrbitPoint p q n)) Set.univ := by
  intro n _ m _ hred
  have hn := ellipticReduce_lattice_decomposition
    (z := additiveOrbitPoint p q n) hτ
  have hm := ellipticReduce_lattice_decomposition
    (z := additiveOrbitPoint p q m) hτ
  have hnm : (n - m) * q =
      (⌊tauCoordX τ (additiveOrbitPoint p q n)⌋ -
        ⌊tauCoordX τ (additiveOrbitPoint p q m)⌋ : ℤ) +
      (⌊tauCoordY τ (additiveOrbitPoint p q n)⌋ -
        ⌊tauCoordY τ (additiveOrbitPoint p q m)⌋ : ℤ) * τ := by
    simp only [additiveOrbitPoint] at hred
    simp only [additiveOrbitPoint] at hn hm ⊢
    rw [hred] at hn
    push_cast
    linear_combination hn - hm
  have hzero := hq
    (⌊tauCoordX τ (additiveOrbitPoint p q n)⌋ -
      ⌊tauCoordX τ (additiveOrbitPoint p q m)⌋)
    (⌊tauCoordY τ (additiveOrbitPoint p q n)⌋ -
      ⌊tauCoordY τ (additiveOrbitPoint p q m)⌋)
    (n - m) (by simpa only [Int.cast_sub] using hnm)
  omega

/-- The poles of a globally meromorphic function in any closed disc form a finite set: the
closed-ball case of `HTGeometry.finite_poles_of_isCompact`. -/
theorem meromorphic_poles_closedBall_finite
    {g : ℂ → ℂ} (hg : MeromorphicOn g Set.univ) (R : ℝ) :
    {z ∈ closedBall (0 : ℂ) R | meromorphicOrderAt g z < 0}.Finite :=
  HTGeometry.finite_poles_of_isCompact hg (isCompact_closedBall 0 R)

/-- An elliptic meromorphic function has finitely many poles on every nontorsion translation
orbit. -/
theorem poleIndexSet_finite_of_elliptic
    {g : ℂ → ℂ} {τ p q : ℂ} (hτ : 0 < τ.im)
    (hg : MeromorphicOn g Set.univ)
    (hperiodOne : Function.Periodic g 1)
    (hperiodTau : Function.Periodic g τ)
    (hq : ThetaTranslationNontorsion τ q) :
    (poleIndexSet g p q).Finite := by
  let r : ℤ → ℂ := fun n => ellipticReduce τ (additiveOrbitPoint p q n)
  let T : Set ℂ :=
    {z ∈ closedBall (0 : ℂ) (1 + ‖τ‖) | meromorphicOrderAt g z < 0}
  have hT : T.Finite := meromorphic_poles_closedBall_finite hg (1 + ‖τ‖)
  have hmap : Set.MapsTo r (poleIndexSet g p q) T := by
    intro n hn
    rw [poleIndexSet, Set.mem_setOf_eq] at hn
    change r n ∈ closedBall (0 : ℂ) (1 + ‖τ‖) ∧ meromorphicOrderAt g (r n) < 0
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff]
      exact ellipticReduce_norm_le τ (additiveOrbitPoint p q n)
    · let a : ℤ := ⌊tauCoordX τ (additiveOrbitPoint p q n)⌋
      let b : ℤ := ⌊tauCoordY τ (additiveOrbitPoint p q n)⌋
      have hperA : Function.Periodic g (a : ℂ) := by
        simpa [a] using hperiodOne.int_mul a
      have hperB : Function.Periodic g ((b : ℂ) * τ) := by
        simpa [b] using hperiodTau.int_mul b
      have hper : Function.Periodic g ((a : ℂ) + (b : ℂ) * τ) :=
        hperA.add_period hperB
      have hord := meromorphicOrderAt_add_period g
        ((a : ℂ) + (b : ℂ) * τ) (r n) hper
      have hdecomp := ellipticReduce_lattice_decomposition
        (z := additiveOrbitPoint p q n) hτ.ne'
      change meromorphicOrderAt g (r n) < 0
      rw [← hord]
      convert hn using 2
      simpa only [r, a, b, add_assoc] using hdecomp.symm
  have himage : (r '' poleIndexSet g p q).Finite :=
    hT.subset (Set.image_subset_iff.mpr hmap)
  apply himage.of_finite_image
  exact (ellipticReduce_injective_on_nontorsion_orbit hτ.ne' hq).mono (Set.subset_univ _)

/-- **Unconditional local elliptic obstruction.** A nonzero constant-coefficient differential
operator applied to a nonresonant theta defect is not a shift coboundary of any globally
meromorphic function elliptic for `(1, τ)`. -/
theorem thetaDifferentialOperator_ne_ellipticShiftCoboundary
    {L : Polynomial ℂ} (hL : L ≠ 0) {τ q h : ℂ} (hτ : 0 < τ.im)
    (hq : ThetaTranslationNontorsion τ q)
    (hnonres : ThetaTranslationNonresonant τ q h)
    (g : ℂ → ℂ) (hg : MeromorphicOn g Set.univ)
    (hperiodOne : Function.Periodic g 1)
    (hperiodTau : Function.Periodic g τ) :
    ¬ ∀ z : ℂ,
      constantCoeffDifferentialOperator L (thetaLogDerivDefect h · τ) z =
        g (z + q) - g z := by
  apply thetaDifferentialOperator_ne_shiftCoboundary_of_finitePoleOrbit
    hL hτ hq hnonres g
  · intro n
    exact hg (additiveOrbitPoint (thetaHalfPeriod τ - h) q n) (Set.mem_univ _)
  · exact poleIndexSet_finite_of_elliptic hτ hg hperiodOne hperiodTau hq

end

end GaloisForLFunctions
