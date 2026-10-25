import GaloisForLFunctions.ArithmeticOrientationTheory.AnEffectivityFromSectionsThatDoesNotReadTheForm
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceRiemannRochWithoutSymmetry
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceConePrimitiveFaithfulness
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.NumericalEquivalenceOnTheScalingSurface

/-!
# Boundary rigidity for section readings

The source obstruction matrix encodes membership in the determinantal source cone. Its rank
does not remove the exact representation obligation: RR and Bézout require the source reserve
to equal the Weil defect. Finite scalar mass reserves and finite Fourier readings fail Bézout
at every positive aperture. The Boolean section count is also bounded by one, so it cannot
satisfy a dimension-growth estimate along the pure-fibre classes.
-/

noncomputable section

open GaloisForLFunctions.ArithmeticCastelnuovoSeveri Zeta23

namespace GaloisForLFunctions.ArithmeticOrientationTheory

variable {C : Type*} [AddCommGroup C] [Module ℝ C]

/-- The section encoding has exactly the same mixed Bézout obligation as its source cone. -/
theorem sourceSectionCone_bezout_iff_defect_sq_le (S : PolarSurface C) {Φ : C → ℝ}
    (hnn : ∀ x : C, 0 ≤ Φ x) (heven : ∀ x : C, Φ (-x) = Φ x)
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    S.BezoutAxiom (sourceSectionCone S Φ) ↔
      ∀ x y : C, S.defect x y ^ 2 ≤ Φ x * Φ y := by
  rw [sourceSectionCone_eq_sourceCone]
  exact S.sourceCone_bezout_iff_defect_sq_le hnn heven hfib

/-- Source section RR and Bézout together force exact representation of the defect. -/
theorem sourceSectionCone_riemannRoch_and_bezout_iff (S : PolarSurface C) {Φ : C → ℝ}
    (hnn : ∀ x : C, 0 ≤ Φ x) (heven : ∀ x : C, Φ (-x) = Φ x)
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    (S.RiemannRochAxiom (sourceSectionCone S Φ) ∧
      S.BezoutAxiom (sourceSectionCone S Φ)) ↔ ∀ x : C, Φ x = S.defect x x := by
  rw [sourceSectionCone_eq_sourceCone]
  exact S.sourceCone_riemannRoch_and_bezout_iff hnn heven hfib

/-- Signed or asymmetric section reserves have RR exactly when their positive part lies below the defect. -/
theorem sourceSectionCone_riemannRoch_iff_positivePart_le_defect (S : PolarSurface C)
    {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    S.RiemannRochAxiom (sourceSectionCone S Φ) ↔
      ∀ x : C, max (Φ x) 0 ≤ S.defect x x := by
  rw [sourceSectionCone_eq_sourceCone]
  exact S.sourceCone_riemannRoch_iff_positivePart_le_defect hfib

/-- The full section boundary classification imposes no initial source sign or symmetry. -/
theorem sourceSectionCone_riemannRoch_and_bezout_iff_positivePart_eq_defect
    (S : PolarSurface C) {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    (S.RiemannRochAxiom (sourceSectionCone S Φ) ∧
      S.BezoutAxiom (sourceSectionCone S Φ)) ↔
      ∀ x : C, max (Φ x) 0 = S.defect x x := by
  rw [sourceSectionCone_eq_sourceCone]
  exact S.sourceCone_riemannRoch_and_bezout_iff_positivePart_eq_defect hfib

theorem sourceSectionCone_bezout_iff_positiveParts (S : PolarSurface C) {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) :
    S.BezoutAxiom (sourceSectionCone S Φ) ↔
      ∀ x y : C, max (S.defect x y) 0 ^ 2 ≤ max (Φ x) 0 * max (Φ y) 0 := by
  rw [sourceSectionCone_eq_sourceCone]
  exact S.sourceCone_bezout_iff_positiveParts hfib

/-- On the full compact scaling surface, ampleness requires a strictly positive reading of every nonzero source. -/
theorem scalingSourceSectionCone_ample_iff_source_pos {Φ : ScalingCycle → ℝ}
    (hfib : ∀ (x : ScalingCycle) (a b : ℝ),
      Φ (x + a • scalingSurface.H + b • scalingSurface.V) = Φ x) :
    scalingSurface.AmpleAxiom (sourceSectionCone scalingSurface Φ) ↔
      ∀ x : ScalingCycle, x.2.2 ≠ 0 → 0 < Φ x := by
  rw [sourceSectionCone_eq_sourceCone,
    scalingSurface.sourceCone_ample_iff_defect_radical hfib]
  constructor
  · intro h x hx
    by_contra hpos
    exact hx ((scalingSurface_defect_radical_iff_source_eq_zero x).mp
      (h x (le_of_not_gt hpos)))
  · intro h x hx
    apply (scalingSurface_defect_radical_iff_source_eq_zero x).mpr
    by_contra hf
    exact (not_lt_of_ge hx) (h x hf)

/-- The rank of the Boolean obstruction matrix counts membership and is at most one. -/
theorem sourceH0_le_one (S : PolarSurface C) (Φ : C → ℝ) (x : C) :
    sourceH0 S Φ x ≤ 1 := by
  rw [sourceH0_eq_ite]
  split_ifs <;> omega

/-- A Boolean section count cannot satisfy the dimension form of RR for any canonical class or Euler constant. -/
theorem exists_sourceH0_riemannRoch_dimension_failure (S : PolarSurface C)
    (Φ : C → ℝ) (K : C) (χ : ℝ) :
    ∃ x : C, (sourceH0 S Φ x : ℝ) + (sourceH0 S Φ (K - x) : ℝ) <
      S.pair x (x - K) / 2 + χ := by
  let k := S.pair S.ample K
  let t := |k| + |χ| + 4
  have ht : 4 ≤ t := by dsimp only [t]; linarith only [abs_nonneg k, abs_nonneg χ]
  have hk : k ≤ t - 4 := by dsimp only [t]; linarith only [le_abs_self k, abs_nonneg χ]
  have hχ : -t + 4 ≤ χ := by dsimp only [t]; linarith only [neg_abs_le χ, abs_nonneg k]
  have hmul := mul_le_mul_of_nonneg_left hk (show 0 ≤ t by linarith only [ht])
  let x := t • S.ample
  have hAA : S.pair S.ample S.ample = 2 := by
    simp only [PolarSurface.ample, map_add, LinearMap.add_apply, S.pair_H_H,
      S.pair_V_H, S.pair_H_V, S.pair_V_V]
    norm_num
  have hxx : S.pair x (x - K) = 2 * t ^ 2 - t * k := by
    dsimp only [x, k]
    simp only [map_sub, map_smul, LinearMap.smul_apply, smul_eq_mul, hAA]
    ring
  have hx : (sourceH0 S Φ x : ℝ) ≤ 1 := by exact_mod_cast sourceH0_le_one S Φ x
  have hKx : (sourceH0 S Φ (K - x) : ℝ) ≤ 1 := by
    exact_mod_cast sourceH0_le_one S Φ (K - x)
  refine ⟨x, ?_⟩
  rw [hxx]
  nlinarith only [hx, hKx, ht, hχ, hmul, sq_nonneg t]

/-- Boolean section counts cannot pay unbounded self-intersection, even along pure fibres. -/
theorem exists_sourceSectionCone_self_pair_gt_count_add (S : PolarSurface C) {Φ : C → ℝ}
    (hfib : ∀ (x : C) (a b : ℝ), Φ (x + a • S.H + b • S.V) = Φ x) (M : ℝ) :
    ∃ x ∈ sourceSectionCone S Φ, (sourceH0 S Φ x : ℝ) + M < S.pair x x := by
  let c := 2 + max (Φ 0) 0 + max M 0
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpay : Φ 0 ≤ 2 * c := by
    dsimp [c]
    linarith only [le_max_left (Φ 0) 0, le_max_right (Φ 0) 0, le_max_right M 0]
  have hlarge : 1 + M < 2 * c := by
    dsimp [c]
    linarith only [le_max_right (Φ 0) 0, le_max_left M 0, le_max_right M 0]
  let x := S.withFibreDegrees 0 c 1
  have hx : x ∈ sourceSectionCone S Φ := by
    rw [sourceSectionCone_eq_sourceCone, S.mem_sourceCone_iff]
    dsimp [x]
    rw [S.withFibreDegrees_pair_H, S.withFibreDegrees_pair_V,
      S.source_withFibreDegrees hfib, S.polar_self, S.withFibreDegrees_pair_H,
      S.withFibreDegrees_pair_V]
    exact ⟨hc, zero_le_one, by simpa only [mul_one] using hpay⟩
  refine ⟨x, hx, ?_⟩
  have hcount : (sourceH0 S Φ x : ℝ) ≤ 1 := by exact_mod_cast sourceH0_le_one S Φ x
  have hxx : S.pair x x = 2 * c := by
    rw [show x = S.withFibreDegrees 0 c 1 from rfl, S.pair_withFibreDegrees]
    simp only [PolarSurface.defect, PolarSurface.polar, map_zero, LinearMap.zero_apply,
      mul_zero, zero_mul, add_zero, sub_zero, mul_one, one_mul]
    ring
  rw [hxx]
  linarith only [hcount, hlarge]

/-- The scalar mass inequality is not Bézout for the original scaling pairing. -/
theorem realTestsAt_l2MassSectionCone_not_bezout {r : ℝ} (hr : 0 < r) (c : ℝ) :
    ¬ (scalingSubsurface (realTestsAt r)).BezoutAxiom (l2MassSectionCone c (realTestsAt r)) := by
  rw [l2MassSectionCone_eq_l2SourceCone]
  exact (realTestsAt_l2SourceCones_not_bezout hr c).1

/-- Turning finitely many linear readings into a section rank does not restore Bézout. -/
theorem finiteLinearReadingSourceSectionCone_not_bezout {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) (F : V → ℝ) :
    ¬ (scalingSubsurface (realTestsAt r)).BezoutAxiom
      (sourceSectionCone (scalingSubsurface (realTestsAt r)) (fun x => F (L x.2.2))) := by
  rw [sourceSectionCone_eq_sourceCone]
  exact finiteLinearReadingSourceCone_not_bezout hr L F

/-- Normalized finite linear section readings also miss the ampleness condition. -/
theorem normalizedFiniteLinearReadingSourceSectionCone_not_ample {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) (F : V → ℝ) :
    ¬ (scalingSubsurface (realTestsAt r)).AmpleAxiom
      (sourceSectionCone (scalingSubsurface (realTestsAt r)) (fun x => F (L x.2.2) - F 0)) := by
  rw [sourceSectionCone_eq_sourceCone]
  exact normalizedFiniteLinearReadingSourceCone_not_ample hr L F

/-- Finite Fourier postprocessing is a special case of the linear-reading obstruction. -/
theorem finiteFourierReadingSourceSectionCone_not_bezout {r : ℝ} (hr : 0 < r)
    {ι : Type*} [Fintype ι] (z : ι → ℂ) (F : (ι → ℂ) → ℝ) :
    ¬ (scalingSubsurface (realTestsAt r)).BezoutAxiom
      (sourceSectionCone (scalingSubsurface (realTestsAt r))
        (fun x => F (fun i => paperFT (cx x.2.2.1.1) (z i)) - F 0)) := by
  rw [sourceSectionCone_eq_sourceCone]
  exact finiteFourierReadingSourceCone_not_bezout hr z F

end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.sourceSectionCone_bezout_iff_defect_sq_le
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.sourceSectionCone_riemannRoch_and_bezout_iff_positivePart_eq_defect
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.sourceSectionCone_bezout_iff_positiveParts
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.scalingSourceSectionCone_ample_iff_source_pos
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.exists_sourceH0_riemannRoch_dimension_failure
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.exists_sourceSectionCone_self_pair_gt_count_add
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.finiteLinearReadingSourceSectionCone_not_bezout
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.normalizedFiniteLinearReadingSourceSectionCone_not_ample
