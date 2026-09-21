import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalFriedrichsSource

import GaloisForLFunctions.RHTower.MaassFiniteDeckCoreWitness
import GaloisForLFunctions.RHTower.SelbergMaassCharacterGradient
import GaloisForLFunctions.RHTower.SelbergMaassCharacterDynamics
import GaloisForLFunctions.HTGeometry.PeriodicStripGreen

/-!
# Periodic Green identity for finite-deck Maass coordinates

The source-to-Friedrichs bridge needs an exact Green identity on finite strips.
This file derives its periodic side cancellation directly from finite-deck
translation covariance, without unfolding the source during derivative proofs.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory
open scoped ContDiff

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open MaassCongruenceL2 SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage
  SelbergMaassMean GaloisForLFunctions.HTGeometry
noncomputable section

theorem retractedDeckComponent_contDiff_two {N : ℕ} (F : formPreDomain N) (q : Deck N)
    (hF : ContDiffOn ℝ 2 (fun z => (chartFun (F : ℍ → DeckSpace N) z) q)
      {z : ℂ | 0 < z.im}) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (retractedDeckComponent ε F q) := by
  change ContDiff ℝ 2 (fun p => (chartFun (F : ℍ → DeckSpace N) (retractedPoint ε p)) q)
  exact contDiff_retractedField_of (by exact (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top (2 : ℕ))).le) hε hF

theorem chartDeriv_componentX_level_periodic {N : ℕ} (F : formPreDomain N) (q : Deck N) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    (chartDeriv (F : ℍ → DeckSpace N) 1
      (ofComplex (point (x + (N + 1 : ℕ)) y))) q =
      (chartDeriv (F : ℍ → DeckSpace N) 1 (ofComplex (point x y))) q := by
  have hperiodic : ∀ t : ℝ,
      GaloisForLFunctions.HTGeometry.chartFun (component (F : ℍ → DeckSpace N) q)
        (point (t + (N + 1 : ℝ)) y) =
      GaloisForLFunctions.HTGeometry.chartFun (component (F : ℍ → DeckSpace N) q)
        (point t y) := by
    intro t
    change component (F : ℍ → DeckSpace N) q
      (ofComplex (point (t + (N + 1 : ℝ)) y)) =
      component (F : ℍ → DeckSpace N) q (ofComplex (point t y))
    simpa only [Nat.cast_add, Nat.cast_one] using component_level_periodic F q hy t
  have hp := directional_periodic (component_c1 F q) hy (N + 1 : ℝ) hperiodic x
  have hleft := hasDerivAt_standardDeckComponentX F q (x + (N + 1 : ℝ)) hy
  have hright := hasDerivAt_standardDeckComponentX F q x hy
  change HasDerivAt
    (fun t => GaloisForLFunctions.HTGeometry.chartFun (component (F : ℍ → DeckSpace N) q)
      (point t y))
    ((chartDeriv (F : ℍ → DeckSpace N) 1
      (ofComplex (point (x + (N + 1 : ℝ)) y))) q) (x + (N + 1 : ℝ)) at hleft
  change HasDerivAt
    (fun t => GaloisForLFunctions.HTGeometry.chartFun (component (F : ℍ → DeckSpace N) q)
      (point t y))
    ((chartDeriv (F : ℍ → DeckSpace N) 1 (ofComplex (point x y))) q) x at hright
  calc
    (chartDeriv (F : ℍ → DeckSpace N) 1
      (ofComplex (point (x + (N + 1 : ℕ)) y))) q =
        directional 1 (GaloisForLFunctions.HTGeometry.chartFun
          (component (F : ℍ → DeckSpace N) q)) (point (x + (N + 1 : ℝ)) y) :=
      by
        simpa only [Nat.cast_add, Nat.cast_one] using
          hleft.unique (slice_horizontal (component_c1 F q) hy (x + (N + 1 : ℝ)))
    _ = directional 1 (GaloisForLFunctions.HTGeometry.chartFun
          (component (F : ℍ → DeckSpace N) q)) (point x y) := hp
    _ = (chartDeriv (F : ℍ → DeckSpace N) 1 (ofComplex (point x y))) q :=
      (hright.unique (slice_horizontal (component_c1 F q) hy x)).symm


theorem retractedDeckComponentX_level_periodic {N : ℕ} (F : formPreDomain N)
    (q : Deck N) {ε x y : ℝ} (hε : 0 < ε) (hy : ε < y) :
    retractedDeckComponentX ε F q (x + (N + 1 : ℝ), y) =
      retractedDeckComponentX ε F q (x, y) := by
  rw [retractedDeckComponentX_eq_chartDeriv hε hy F q,
    retractedDeckComponentX_eq_chartDeriv hε hy F q]
  simpa [SelbergMaassMean.point, Nat.cast_add, Nat.cast_one] using
    chartDeriv_componentX_level_periodic F q (hε.trans hy) x


/-- Above the cutoff, a retracted finite-deck coordinate retains its level period. -/
theorem retractedDeckComponent_level_periodic {N : ℕ} (F : formPreDomain N)
    (q : Deck N) {ε x y : ℝ} (hε : 0 < ε) (hy : ε < y) :
    retractedDeckComponent ε F q (x + (N + 1 : ℝ), y) =
      retractedDeckComponent ε F q (x, y) := by
  unfold retractedDeckComponent
  rw [retractedPoint_eq_of_le hε hy.le, retractedPoint_eq_of_le hε hy.le]
  change component (F : ℍ → DeckSpace N) q
    (ofComplex (point (x + (N + 1 : ℝ)) y)) =
    component (F : ℍ → DeckSpace N) q (ofComplex (point x y))
  simpa only [Nat.cast_add, Nat.cast_one] using component_level_periodic F q (hε.trans hy) x

/-- The periodic finite-deck side flux cancels on every strip above the cutoff. -/
theorem retractedDeckComponent_horizontal_flux_level_periodic {N : ℕ}
    (U V : formPreDomain N) (q : Deck N) {ε x y : ℝ}
    (hε : 0 < ε) (hy : ε < y) :
    stripDeriv (1, 0) (retractedDeckComponent ε U q) (x + (N + 1 : ℝ), y) *
        star (retractedDeckComponent ε V q (x + (N + 1 : ℝ), y)) =
      stripDeriv (1, 0) (retractedDeckComponent ε U q) (x, y) *
        star (retractedDeckComponent ε V q (x, y)) := by
  change retractedDeckComponentX ε U q (x + (N + 1 : ℝ), y) *
      star (retractedDeckComponent ε V q (x + (N + 1 : ℝ), y)) =
    retractedDeckComponentX ε U q (x, y) * star (retractedDeckComponent ε V q (x, y))
  rw [retractedDeckComponentX_level_periodic U q hε hy,
    retractedDeckComponent_level_periodic V q hε hy]

/-- The literal exceptional source has a globally retracted `C²` deck coordinate. -/
theorem retractedSourceDeckComponent_contDiff_two
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    {ε : ℝ} (hε : 0 < ε) (q : Deck N) :
    ContDiff ℝ 2 (retractedDeckComponent ε (sourceInFormPreDomain N lam f) q) := by
  apply retractedDeckComponent_contDiff_two (sourceInFormPreDomain N lam f) q _ hε
  change ContDiffOn ℝ 2 (fun z => sourceVector N f (ofComplex z) q) {z : ℂ | 0 < z.im}
  exact ((EuclideanSpace.proj q).restrictScalars ℝ).contDiff.comp_contDiffOn
    (SelbergMaassCharacterGradient.sourceVector_contDiffOn N f)

/-- Mixed periodic Green formula for one actual source coordinate and an arbitrary
finite-deck test coordinate on a strip whose every height lies above the cutoff. -/
theorem retractedSource_test_periodic_strip_green
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (F : formPreDomain N) (q : Deck N) {ε c d : ℝ} (hε : 0 < ε)
    (hhigh : ∀ y ∈ uIcc c d, ε < y) :
    (∫ x in (0 : ℝ)..(N + 1 : ℝ), ∫ y in c..d,
      (stripDeriv (1, 0)
          (stripDeriv (1, 0) (retractedDeckComponent ε (sourceInFormPreDomain N lam f) q))
          (x, y) * star (retractedDeckComponent ε F q (x, y)) +
        stripDeriv (1, 0) (retractedDeckComponent ε (sourceInFormPreDomain N lam f) q)
          (x, y) * star (stripDeriv (1, 0) (retractedDeckComponent ε F q) (x, y))) +
      (stripDeriv (0, 1)
          (stripDeriv (0, 1) (retractedDeckComponent ε (sourceInFormPreDomain N lam f) q))
          (x, y) * star (retractedDeckComponent ε F q (x, y)) +
        stripDeriv (0, 1) (retractedDeckComponent ε (sourceInFormPreDomain N lam f) q)
          (x, y) * star (stripDeriv (0, 1) (retractedDeckComponent ε F q) (x, y)))) =
      (∫ x in (0 : ℝ)..(N + 1 : ℝ),
        stripDeriv (0, 1) (retractedDeckComponent ε (sourceInFormPreDomain N lam f) q)
          (x, d) * star (retractedDeckComponent ε F q (x, d))) -
        ∫ x in (0 : ℝ)..(N + 1 : ℝ),
          stripDeriv (0, 1) (retractedDeckComponent ε (sourceInFormPreDomain N lam f) q)
            (x, c) * star (retractedDeckComponent ε F q (x, c)) := by
  apply complex_periodic_strip_green
    (retractedDeckComponent ε (sourceInFormPreDomain N lam f) q)
    (retractedDeckComponent ε F q)
  · exact retractedSourceDeckComponent_contDiff_two N lam f hε q
  · exact contDiff_retractedDeckComponent hε F q
  · intro y hy
    simpa only [zero_add, Nat.cast_add, Nat.cast_one] using
      retractedDeckComponent_horizontal_flux_level_periodic
        (sourceInFormPreDomain N lam f) F q hε (hhigh y hy) (x := 0)


theorem retractedSourceDeckComponentXX_eq_source_directional
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (q : Deck N) {ε x y : ℝ} (hε : 0 < ε) (hy : ε < y) :
    stripDeriv (1, 0)
      (stripDeriv (1, 0)
        (retractedDeckComponent ε (sourceInFormPreDomain N lam f) q)) (x, y) =
      directional 1 (directional 1
        (GaloisForLFunctions.HTGeometry.chartFun
          (component (sourceInFormPreDomain N lam f : ℍ → DeckSpace N) q)))
        (point x y) := by
  let U := retractedDeckComponent ε (sourceInFormPreDomain N lam f) q
  let S := GaloisForLFunctions.HTGeometry.chartFun
    (component (sourceInFormPreDomain N lam f : ℍ → DeckSpace N) q)
  have hU : ContDiff ℝ 2 U := retractedSourceDeckComponent_contDiff_two N lam f hε q
  have hS : ContDiffOn ℝ 2 S {z : ℂ | 0 < z.im} := by
    change ContDiffOn ℝ 2 (fun z => sourceVector N f (ofComplex z) q) {z : ℂ | 0 < z.im}
    exact ((EuclideanSpace.proj q).restrictScalars ℝ).contDiff.comp_contDiffOn
      (SelbergMaassCharacterGradient.sourceVector_contDiffOn N f)
  have hline : HasDerivAt (fun t : ℝ => stripDeriv (1, 0) U (t, y))
      (stripDeriv (1, 0) (stripDeriv (1, 0) U) (x, y)) x := by
    have hcoord : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x := by
      simpa using (hasFDerivAt_prodMk_left (𝕜 := ℝ) (E := ℝ) (F := ℝ) x y).hasDerivAt
    exact ((contDiff_stripDeriv (1, 0) U hU).differentiable one_ne_zero (x, y)).hasFDerivAt
      |>.comp_hasDerivAt x hcoord
  have hS1 : ContDiffOn ℝ 1 S {z : ℂ | 0 < z.im} := hS.of_le (by norm_num)
  have hSline : HasDerivAt (fun t : ℝ => directional 1 S (point t y))
      (directional 1 (directional 1 S) (point x y)) x := by
    apply slice_horizontal
    exact directional_contDiffOn hS (m := 1)
      (by exact (WithTop.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by norm_num)))) 1
    exact hε.trans hy
  have heq : (fun t : ℝ => stripDeriv (1, 0) U (t, y)) =ᶠ[𝓝 x]
      fun t => directional 1 S (point t y) := by
    filter_upwards with t
    change retractedDeckComponentX ε (sourceInFormPreDomain N lam f) q (t, y) = _
    rw [retractedDeckComponentX_eq_chartDeriv hε hy]
    have hstandard := hasDerivAt_standardDeckComponentX
      (sourceInFormPreDomain N lam f) q t (hε.trans hy)
    change HasDerivAt (fun u => S (point u y)) _ t at hstandard
    exact hstandard.unique (slice_horizontal hS1 (hε.trans hy) t)
  exact hline.unique (hSline.congr_of_eventuallyEq heq)

theorem retractedSourceDeckComponentYY_eq_source_directional
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (q : Deck N) {ε x y : ℝ} (hε : 0 < ε) (hy : ε < y) :
    stripDeriv (0, 1)
      (stripDeriv (0, 1)
        (retractedDeckComponent ε (sourceInFormPreDomain N lam f) q)) (x, y) =
      directional Complex.I (directional Complex.I
        (GaloisForLFunctions.HTGeometry.chartFun
          (component (sourceInFormPreDomain N lam f : ℍ → DeckSpace N) q)))
        (point x y) := by
  let U := retractedDeckComponent ε (sourceInFormPreDomain N lam f) q
  let S := GaloisForLFunctions.HTGeometry.chartFun
    (component (sourceInFormPreDomain N lam f : ℍ → DeckSpace N) q)
  have hU : ContDiff ℝ 2 U := retractedSourceDeckComponent_contDiff_two N lam f hε q
  have hS : ContDiffOn ℝ 2 S {z : ℂ | 0 < z.im} := by
    change ContDiffOn ℝ 2 (fun z => sourceVector N f (ofComplex z) q) {z : ℂ | 0 < z.im}
    exact ((EuclideanSpace.proj q).restrictScalars ℝ).contDiff.comp_contDiffOn
      (SelbergMaassCharacterGradient.sourceVector_contDiffOn N f)
  have hline : HasDerivAt (fun t : ℝ => stripDeriv (0, 1) U (x, t))
      (stripDeriv (0, 1) (stripDeriv (0, 1) U) (x, y)) y := by
    have hcoord : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y := by
      simpa using (hasFDerivAt_prodMk_right (𝕜 := ℝ) (E := ℝ) (F := ℝ) x y).hasDerivAt
    exact ((contDiff_stripDeriv (0, 1) U hU).differentiable one_ne_zero (x, y)).hasFDerivAt
      |>.comp_hasDerivAt y hcoord
  have hS1 : ContDiffOn ℝ 1 S {z : ℂ | 0 < z.im} := hS.of_le (by norm_num)
  have hSline : HasDerivAt (fun t : ℝ => directional Complex.I S (point x t))
      (directional Complex.I (directional Complex.I S) (point x y)) y := by
    apply slice_vertical
    exact directional_contDiffOn hS (m := 1)
      (by exact (WithTop.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by norm_num)))) Complex.I
    exact hε.trans hy
  have heq : (fun t : ℝ => stripDeriv (0, 1) U (x, t)) =ᶠ[𝓝 y]
      fun t => directional Complex.I S (point x t) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    change retractedDeckComponentY ε (sourceInFormPreDomain N lam f) q (x, t) = _
    rw [retractedDeckComponentY_eq_chartDeriv hε ht]
    have hstandard := hasDerivAt_standardDeckComponentY
      (sourceInFormPreDomain N lam f) q x (hε.trans ht)
    change HasDerivAt (fun u => S (point x u)) _ t at hstandard
    exact hstandard.unique (slice_vertical hS1 x (hε.trans ht))
  exact hline.unique (hSline.congr_of_eventuallyEq heq)

/-- Above the cutoff, the retracted source coordinate satisfies its literal
Euclidean Maass equation. -/
theorem retractedSourceDeckComponent_laplacian
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (q : Deck N) {ε x y : ℝ} (hε : 0 < ε) (hy : ε < y) :
    stripDeriv (1, 0)
        (stripDeriv (1, 0) (retractedDeckComponent ε (sourceInFormPreDomain N lam f) q))
        (x, y) +
      stripDeriv (0, 1)
        (stripDeriv (0, 1) (retractedDeckComponent ε (sourceInFormPreDomain N lam f) q))
        (x, y) =
      ((-(lam.1 / y ^ 2) : ℝ) : ℂ) *
        retractedDeckComponent ε (sourceInFormPreDomain N lam f) q (x, y) := by
  rw [retractedSourceDeckComponentXX_eq_source_directional N lam f q hε hy,
    retractedSourceDeckComponentYY_eq_source_directional N lam f q hε hy]
  let S := GaloisForLFunctions.HTGeometry.chartFun
    (component (sourceInFormPreDomain N lam f : ℍ → DeckSpace N) q)
  have hsource := SelbergMaassCharacterDynamics.source_readout_laplacian N f
    (EuclideanSpace.proj q) (ofComplex (point x y))
  have hS_eq : S = fun w => (EuclideanSpace.proj q) (sourceVector N f (ofComplex w)) := rfl
  have hvalue : retractedDeckComponent ε (sourceInFormPreDomain N lam f) q (x, y) =
      S (point x y) := by
    unfold retractedDeckComponent S
    rw [retractedPoint_eq_of_le hε hy.le]
    rfl
  change directional 1 (directional 1 S) (point x y) +
      directional Complex.I (directional Complex.I S) (point x y) = _
  rw [hvalue, hS_eq]
  rw [ofComplex_apply_of_im_pos (by simpa [point] using hε.trans hy)] at hsource
  change directional 1 (directional 1 (fun w =>
      (EuclideanSpace.proj q) (sourceVector N f (ofComplex w)))) (point x y) +
      directional Complex.I (directional Complex.I (fun w =>
        (EuclideanSpace.proj q) (sourceVector N f (ofComplex w)))) (point x y) = _ at hsource
  convert hsource using 1 <;> simp [point]

end
end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
