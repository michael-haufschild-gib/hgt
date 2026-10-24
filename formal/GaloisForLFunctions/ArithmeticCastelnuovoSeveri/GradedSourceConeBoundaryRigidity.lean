import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceConeBoundaryRigidity

/-!
# Signed reserves cannot repair source Bézout

A graded source cone allows either fibre degree to be negative. Bézout rules this out:
if a source has negative reserve, lift it to opposite fibre degrees and intersect it with
a sufficiently large pure-fibre class. Their intersection is negative. Thus Bézout itself
forces the reserve to be nonnegative, and the exact source-boundary classification applies.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- A negative source reserve gives two graded-effective classes with negative intersection. -/
theorem exists_gradedSourceCone_negative_pair {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x)
    (x : C) (hneg : Φ x < 0) :
    ∃ y ∈ S.gradedSourceCone Φ, ∃ z ∈ S.gradedSourceCone Φ, S.pair y z < 0 := by
  let p := Real.sqrt (-Φ x / 2)
  have hp : 0 ≤ p := Real.sqrt_nonneg _
  have hp2 : p ^ 2 = -Φ x / 2 := Real.sq_sqrt (by positivity)
  have hp0 : 0 < p := by nlinarith only [hp, hp2, hneg]
  let c := 2 + max (Φ 0) 0
  have hc : 2 ≤ c := by dsimp [c]; linarith only [le_max_right (Φ 0) 0]
  have hΦc : Φ 0 ≤ 2 * c := by
    dsimp [c]
    linarith only [le_max_left (Φ 0) 0, le_max_right (Φ 0) 0]
  refine ⟨S.withFibreDegrees x p (-p), ?_, S.withFibreDegrees 0 c 1, ?_, ?_⟩
  · rw [S.mem_gradedSourceCone_iff, S.pair_ample, S.withFibreDegrees_pair_H,
      S.withFibreDegrees_pair_V, S.source_withFibreDegrees hfib, S.polar_self,
      S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V]
    constructor <;> nlinarith only [hp2]
  · rw [S.mem_gradedSourceCone_iff, S.pair_ample, S.withFibreDegrees_pair_H,
      S.withFibreDegrees_pair_V, S.source_withFibreDegrees hfib, S.polar_self,
      S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V]
    constructor <;> linarith only [hc, hΦc]
  · rw [S.pair_withFibreDegrees]
    have hzero : S.defect x 0 = 0 := by
      simp only [defect, polar, map_zero, LinearMap.zero_apply, mul_zero, zero_mul,
        add_zero, sub_zero]
    rw [hzero]
    have hprod : 0 < p * (c - 1) := mul_pos hp0 (by linarith only [hc])
    nlinarith only [hprod]

/-- Nonnegativity of the source is necessary for Bézout even when only ample degree is tested. -/
theorem source_nonneg_of_gradedSourceCone_bezout {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x)
    (hB : S.BezoutAxiom (S.gradedSourceCone Φ)) : ∀ x : C, 0 ≤ Φ x := by
  intro x
  by_contra h
  obtain ⟨y, hy, z, hz, hyz⟩ := S.exists_gradedSourceCone_negative_pair hfib x (lt_of_not_ge h)
  exact (not_lt_of_ge (hB y hy z hz)) hyz

/-- Graded Bézout is equivalent to nonnegativity and the full mixed source contraction law. -/
theorem gradedSourceCone_bezout_iff {Φ : C → ℝ}
    (heven : ∀ x : C, Φ (-x) = Φ x)
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    S.BezoutAxiom (S.gradedSourceCone Φ) ↔
      (∀ x : C, 0 ≤ Φ x) ∧ ∀ x y : C, S.defect x y ^ 2 ≤ Φ x * Φ y := by
  constructor
  · intro hB
    have hnn := S.source_nonneg_of_gradedSourceCone_bezout hfib hB
    refine ⟨hnn, (S.sourceCone_bezout_iff_defect_sq_le hnn heven hfib).mp ?_⟩
    rwa [S.sourceCone_eq_gradedSourceCone_of_nonneg hnn]
  · rintro ⟨hnn, hcs⟩
    rw [← S.sourceCone_eq_gradedSourceCone_of_nonneg hnn]
    exact (S.sourceCone_bezout_iff_defect_sq_le hnn heven hfib).mpr hcs

/-- Signed source reserves have both axioms precisely when they represent the nonnegative defect. -/
theorem gradedSourceCone_riemannRoch_and_bezout_iff {Φ : C → ℝ}
    (heven : ∀ x : C, Φ (-x) = Φ x)
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    (S.RiemannRochAxiom (S.gradedSourceCone Φ) ∧
      S.BezoutAxiom (S.gradedSourceCone Φ)) ↔
      (∀ x : C, 0 ≤ Φ x) ∧ ∀ x : C, Φ x = S.defect x x := by
  constructor
  · rintro ⟨hRR, hB⟩
    have hnn := S.source_nonneg_of_gradedSourceCone_bezout hfib hB
    refine ⟨hnn, (S.sourceCone_riemannRoch_and_bezout_iff hnn heven hfib).mp ?_⟩
    rw [S.sourceCone_eq_gradedSourceCone_of_nonneg hnn]
    exact ⟨hRR, hB⟩
  · rintro ⟨hnn, heq⟩
    rw [← S.sourceCone_eq_gradedSourceCone_of_nonneg hnn]
    exact (S.sourceCone_riemannRoch_and_bezout_iff hnn heven hfib).mpr heq

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurface
