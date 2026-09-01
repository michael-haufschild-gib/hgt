import GaloisForLFunctions.HTGeometry.RatFuncTranslationFixedField
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixAlgebraicUntwistingNoGo

/-!
# Rational-localization dichotomy for source Γ₆ untwisting

The Laurent source algebra detects nontrivial holonomy because `t + c` ceases to be a unit when
`c ≠ 0`.  This file tests whether localization can repair that obstruction without merely erasing
the detector.

There are two sharp outcomes.  A principal finite-denominator localization admits translation of
the inverse generator by `q` exactly when its denominator vanishes at `-q`; hence no nonzero finite
denominator admits every real source grade.  At the other extreme, the total rational function
field has a unique untwisting for every holonomy: additive translation `X ↦ X + (u-1)`.  Thus finite
localization cannot carry the grade-universal gauge, while total localization makes it automatic
and nonselective.  Neither closes the shared HB/FZZ-P/PW-B/RBH Ward chain.
-/

open Polynomial

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

private theorem sourceGammaSixRatFuncAlgEquiv_ext_X {K : Type*} [Field K]
    {f g : RatFunc K ≃ₐ[K] RatFunc K}
    (hX : f RatFunc.X = g RatFunc.X) : f = g := by
  apply AlgEquiv.ext
  intro z
  have hring : f.toRingEquiv.toRingHom = g.toRingEquiv.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := K[X])
    intro p
    have hpoly :
        f.toRingEquiv.toRingHom.comp (algebraMap K[X] (RatFunc K)) =
          g.toRingEquiv.toRingHom.comp (algebraMap K[X] (RatFunc K)) := by
      apply Polynomial.ringHom_ext
      · intro c
        change f (algebraMap K (RatFunc K) c) =
          g (algebraMap K (RatFunc K) c)
        rw [f.commutes, g.commutes]
      · simpa [RatFunc.algebraMap_X] using hX
    exact DFunLike.congr_fun hpoly p
  exact DFunLike.congr_fun hring z

/-- Multiplication by the rational-source local-system differential `X-u`. -/
def sourceHorizontalGammaSixRationalHolonomyBoundary {K : Type*} [Field K]
    (u : K) (f : RatFunc K) : RatFunc K :=
  (RatFunc.X - algebraMap K (RatFunc K) u) * f

/-- A rational untwisting is a coefficient-fixing automorphism intertwining `X-u` with `X-1`. -/
def SourceHorizontalGammaSixRationalUntwisting {K : Type*} [Field K]
    (u : K) (φ : RatFunc K ≃ₐ[K] RatFunc K) : Prop :=
  ∀ f : RatFunc K,
    φ (sourceHorizontalGammaSixRationalHolonomyBoundary u f) =
      sourceHorizontalGammaSixRationalHolonomyBoundary 1 (φ f)

/-- **Unique rational gauge.**  Intertwining forces, and is forced by, translation through
`u-1`. -/
theorem sourceHorizontalGammaSixRationalUntwisting_iff {K : Type*} [Field K]
    (u : K) (φ : RatFunc K ≃ₐ[K] RatFunc K) :
    SourceHorizontalGammaSixRationalUntwisting u φ ↔
      φ = ratFuncTranslationEquiv (u - 1) := by
  constructor
  · intro hφ
    apply sourceGammaSixRatFuncAlgEquiv_ext_X
    have hone := hφ 1
    rw [sourceHorizontalGammaSixRationalHolonomyBoundary,
      sourceHorizontalGammaSixRationalHolonomyBoundary,
      map_mul, map_sub, φ.commutes, map_one, mul_one, mul_one] at hone
    rw [ratFuncTranslationEquiv_X, map_sub, map_one]
    have hone' :
        φ RatFunc.X - algebraMap K (RatFunc K) u = RatFunc.X - 1 := by
      simpa using hone
    linear_combination hone'
  · rintro rfl
    intro f
    rw [sourceHorizontalGammaSixRationalHolonomyBoundary,
      sourceHorizontalGammaSixRationalHolonomyBoundary,
      map_mul, map_sub, ratFuncTranslationEquiv_X,
      AlgEquiv.commutes, map_sub, map_one]
    congr 1
    ring

/-- Every scalar holonomy has exactly one untwisting after total fraction-field localization. -/
theorem existsUnique_sourceHorizontalGammaSixRationalUntwisting
    {K : Type*} [Field K] (u : K) :
    ∃! φ : RatFunc K ≃ₐ[K] RatFunc K,
      SourceHorizontalGammaSixRationalUntwisting u φ := by
  refine ⟨ratFuncTranslationEquiv (u - 1),
    (sourceHorizontalGammaSixRationalUntwisting_iff u _).2 rfl, ?_⟩
  intro φ hφ
  exact (sourceHorizontalGammaSixRationalUntwisting_iff u φ).1 hφ

/-- A principal localization at powers of `D` admits translation by `q` precisely when the
translated inverse generator can be formed, equivalently when some `D^n` contains `X+q`. -/
def SourceHorizontalGammaSixFiniteDenominatorAdmitsTranslation
    (D : ℝ[X]) (q : ℝ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ X + C q ∣ D ^ n

/-- **Finite-denominator admission law.**  Translation by `q` is admitted exactly at the closed
fibre `D(-q)=0`. -/
theorem sourceHorizontalGammaSixFiniteDenominatorAdmitsTranslation_iff
    (D : ℝ[X]) (q : ℝ) :
    SourceHorizontalGammaSixFiniteDenominatorAdmitsTranslation D q ↔
      D.IsRoot (-q) := by
  constructor
  · rintro ⟨n, _, hdiv⟩
    have hlinear : (X - C (-q) : ℝ[X]) = X + C q := by
      simp
    have hrootLinear : (X + C q : ℝ[X]).IsRoot (-q) := by
      rw [← hlinear]
      exact Polynomial.dvd_iff_isRoot.mp (dvd_refl _)
    obtain ⟨E, hE⟩ := hdiv
    have hpow : (D.eval (-q)) ^ n = 0 := by
      have := congrArg (fun p : ℝ[X] => p.eval (-q)) hE
      simpa [hrootLinear] using this
    by_contra hD
    exact (pow_ne_zero n hD) hpow
  · intro hroot
    refine ⟨1, by omega, ?_⟩
    rw [pow_one]
    have hdiv : (X - C (-q) : ℝ[X]) ∣ D :=
      Polynomial.dvd_iff_isRoot.mpr hroot
    simpa using hdiv

/-- A finite denominator admits every real translation only in the degenerate zero case. -/
theorem everySourceHorizontalGammaSixFiniteDenominatorAdmitsTranslation_iff
    (D : ℝ[X]) :
    (∀ q : ℝ, SourceHorizontalGammaSixFiniteDenominatorAdmitsTranslation D q) ↔
      D = 0 := by
  constructor
  · intro hall
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hrange : (Set.range fun q : ℝ => -q).Infinite :=
      Set.infinite_range_of_injective neg_injective
    refine hrange.mono ?_
    rintro x ⟨q, rfl⟩
    exact
      (sourceHorizontalGammaSixFiniteDenominatorAdmitsTranslation_iff D q).1 (hall q)
  · rintro rfl
    intro q
    refine ⟨1, by omega, ?_⟩
    simp

/-- Total rational localization of one literal Xi-selected physical holonomy. -/
def SourceHorizontalGammaSixPhysicalRationalUntwisting (q : XiZeroCopy)
    (φ : RatFunc ℝ ≃ₐ[ℝ] RatFunc ℝ) : Prop :=
  SourceHorizontalGammaSixRationalUntwisting
    (sourceHorizontalGammaSixPhysicalHolonomy q) φ

/-- Every physical holonomy has a unique rational gauge, without any critical-line condition. -/
theorem sourceHorizontalGammaSixPhysicalRationalUntwisting_existsUnique
    (q : XiZeroCopy) :
    ∃! φ : RatFunc ℝ ≃ₐ[ℝ] RatFunc ℝ,
      SourceHorizontalGammaSixPhysicalRationalUntwisting q φ := by
  exact existsUnique_sourceHorizontalGammaSixRationalUntwisting _

/-- **Pointwise localization phase transition.**  The original cyclic source untwists only at
trivial holonomy, but its total fraction field untwists uniquely at every holonomy. -/
theorem sourceHorizontalGammaSixLocalizationPhaseTransition (u : ℝ) :
    (SourceHorizontalGammaSixAlgebraicUntwisting u ↔ u = 1) ∧
      ∃! φ : RatFunc ℝ ≃ₐ[ℝ] RatFunc ℝ,
        SourceHorizontalGammaSixRationalUntwisting u φ := by
  exact ⟨sourceHorizontalGammaSixAlgebraicUntwisting_iff u,
    existsUnique_sourceHorizontalGammaSixRationalUntwisting u⟩

/-- **[SHARED-WARD RATIONAL-LOCALIZATION ROUTE-CLASS KILL].**  Finite principal
localization cannot support all source grades, whereas the total rational field uniquely untwists
every scalar and every physical Γ₆ holonomy.  These two canonical localization classes therefore
either fail grade-universality or erase the holonomy discriminator; neither manufactures the shared
Ward law. -/
theorem sourceHorizontalGammaSixRationalLocalizationRouteKilled :
    (∀ u : ℝ, ∃! φ : RatFunc ℝ ≃ₐ[ℝ] RatFunc ℝ,
      SourceHorizontalGammaSixRationalUntwisting u φ) ∧
      (∀ q : XiZeroCopy, ∃! φ : RatFunc ℝ ≃ₐ[ℝ] RatFunc ℝ,
        SourceHorizontalGammaSixPhysicalRationalUntwisting q φ) ∧
      ¬ ∃ D : ℝ[X], D ≠ 0 ∧
        ∀ q : ℝ,
          SourceHorizontalGammaSixFiniteDenominatorAdmitsTranslation D q := by
  refine ⟨existsUnique_sourceHorizontalGammaSixRationalUntwisting,
    sourceHorizontalGammaSixPhysicalRationalUntwisting_existsUnique, ?_⟩
  rintro ⟨D, hD, hall⟩
  exact hD
    ((everySourceHorizontalGammaSixFiniteDenominatorAdmitsTranslation_iff D).1 hall)

end

end RHTower
