import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixRationalLocalizationNoGo

/-!
# Closed-fibre obstruction to Gamma-six algebraic untwisting

The preceding localization dichotomy left one apparent algebraic survivor: an infinite, non-field
source algebra retaining a closed fibre while admitting enough translations to remove every
holonomy.  This file closes that survivor without any finiteness, reducedness, domain, or
localization hypothesis.

For a distinguished coordinate `x` in an arbitrary commutative algebra, intertwining `x-u` with
`x-1` forces `x` to translate by `u-1`.  A proper fibre ideal containing `x-a` cannot be preserved
by that translation unless `u=1`, because it would otherwise contain a nonzero base-field unit.
Thus grade-universal algebraic untwisting and retention of a fixed closed source fibre are
incompatible.  Any surviving shared HB/FZZ-P/PW-B/RBH Ward producer must therefore leave
fibre-preserving commutative algebraic gauge transport.
-/

namespace RHTower

noncomputable section

open Polynomial

/-- Multiplication by the affine source boundary `x-u`. -/
def sourceHorizontalGammaSixAffineBoundary
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (x : A) (u : K) (f : A) : A :=
  (x - algebraMap K A u) * f

/-- An algebraic gauge intertwines the holonomy boundary `x-u` with the fixed boundary `x-1`. -/
def SourceHorizontalGammaSixAffineUntwisting
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (x : A) (u : K) (φ : A ≃ₐ[K] A) : Prop :=
  ∀ f : A,
    φ (sourceHorizontalGammaSixAffineBoundary x u f) =
      sourceHorizontalGammaSixAffineBoundary x (1 : K) (φ f)

/-- Intertwining is exactly translation of the distinguished source coordinate. -/
theorem sourceHorizontalGammaSixAffineUntwisting_iff_coordinateTranslation
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (x : A) (u : K) (φ : A ≃ₐ[K] A) :
    SourceHorizontalGammaSixAffineUntwisting x u φ ↔
      φ x = x + algebraMap K A (u - 1) := by
  constructor
  · intro hφ
    have hone := hφ 1
    simp only [sourceHorizontalGammaSixAffineBoundary, mul_one, map_sub,
      φ.commutes, map_one] at hone
    calc
      φ x = (φ x - algebraMap K A u) + algebraMap K A u := by ring
      _ = (x - 1) + algebraMap K A u := by rw [hone]
      _ = x + algebraMap K A (u - 1) := by rw [map_sub, map_one]; ring
  · intro hx f
    rw [sourceHorizontalGammaSixAffineBoundary,
      sourceHorizontalGammaSixAffineBoundary, map_mul, map_sub, φ.commutes,
      hx, map_sub, map_one]
    congr 1
    ring

/-- A proper closed fibre of the distinguished affine coordinate. -/
structure SourceHorizontalGammaSixClosedFibre
    (K A : Type*) [Field K] [CommRing A] [Algebra K A] where
  coordinate : A
  center : K
  ideal : Ideal A
  coordinate_sub_center_mem :
    coordinate - algebraMap K A center ∈ ideal
  proper : ideal ≠ ⊤

/-- The gauge preserves the closed fibre forward. -/
def SourceHorizontalGammaSixClosedFibre.Preserves
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (F : SourceHorizontalGammaSixClosedFibre K A)
    (φ : A ≃ₐ[K] A) : Prop :=
  ∀ y : A, y ∈ F.ideal → φ y ∈ F.ideal

/-- **Closed-fibre trilemma.** A fibre-preserving affine untwisting exists exactly at trivial
holonomy.  Only forward ideal invariance is required. -/
theorem sourceHorizontalGammaSixClosedFibre_preservedUntwisting_iff
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (F : SourceHorizontalGammaSixClosedFibre K A) (u : K) :
    (∃ φ : A ≃ₐ[K] A,
      SourceHorizontalGammaSixAffineUntwisting F.coordinate u φ ∧
        F.Preserves φ) ↔ u = 1 := by
  constructor
  · rintro ⟨φ, hφ, hpres⟩
    have hx :=
      (sourceHorizontalGammaSixAffineUntwisting_iff_coordinateTranslation
        F.coordinate u φ).1 hφ
    have himage := hpres
      (F.coordinate - algebraMap K A F.center)
      F.coordinate_sub_center_mem
    have himage' :
        (F.coordinate - algebraMap K A F.center) +
            algebraMap K A (u - 1) ∈ F.ideal := by
      rw [map_sub, φ.commutes, hx] at himage
      convert himage using 1
      ring
    have hscalar : algebraMap K A (u - 1) ∈ F.ideal := by
      have hsub := F.ideal.sub_mem himage' F.coordinate_sub_center_mem
      simpa using hsub
    by_contra hu
    have hu0 : u - 1 ≠ 0 := sub_ne_zero.mpr hu
    have hunit : IsUnit (algebraMap K A (u - 1)) :=
      IsUnit.map (algebraMap K A) (isUnit_iff_ne_zero.mpr hu0)
    exact F.proper (F.ideal.eq_top_of_isUnit_mem hscalar hunit)
  · rintro rfl
    refine ⟨AlgEquiv.refl, ?_, ?_⟩
    · exact
        (sourceHorizontalGammaSixAffineUntwisting_iff_coordinateTranslation
          F.coordinate 1 (AlgEquiv.refl : A ≃ₐ[K] A)).2 (by simp)
    · intro y hy
      exact hy

/-- No proper closed fibre admits an algebraic untwisting at every holonomy grade. -/
theorem sourceHorizontalGammaSixClosedFibre_no_gradeUniversalUntwisting
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (F : SourceHorizontalGammaSixClosedFibre K A) :
    ¬ ∀ u : K, ∃ φ : A ≃ₐ[K] A,
      SourceHorizontalGammaSixAffineUntwisting F.coordinate u φ ∧
        F.Preserves φ := by
  intro hall
  have hzero :=
    (sourceHorizontalGammaSixClosedFibre_preservedUntwisting_iff F 0).1
      (hall 0)
  exact zero_ne_one hzero

/-- The literal origin fibre of the polynomial affine source. -/
def sourceHorizontalGammaSixPolynomialOriginFibre :
    SourceHorizontalGammaSixClosedFibre ℝ ℝ[X] where
  coordinate := Polynomial.X
  center := 0
  ideal := Ideal.span {Polynomial.X}
  coordinate_sub_center_mem := by
    simp only [map_zero, sub_zero]
    exact Ideal.subset_span (Set.mem_singleton Polynomial.X)
  proper := by
    intro htop
    have h1 : (1 : ℝ[X]) ∈ Ideal.span {(Polynomial.X : ℝ[X])} := by
      rw [htop]
      simp
    rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff] at h1
    norm_num at h1

/-- **[SHARED-WARD CLOSED-FIBRE ALGEBRAIC ROUTE-CLASS KILL].** Even the universal
polynomial affine enlargement cannot preserve its origin fibre while untwisting every grade. -/
theorem sourceHorizontalGammaSixClosedFibreAlgebraicUntwistingRouteKilled :
    (∀ u : ℝ,
      (∃ φ : ℝ[X] ≃ₐ[ℝ] ℝ[X],
        SourceHorizontalGammaSixAffineUntwisting Polynomial.X u φ ∧
          sourceHorizontalGammaSixPolynomialOriginFibre.Preserves φ) ↔
        u = 1) ∧
      ¬ ∀ u : ℝ, ∃ φ : ℝ[X] ≃ₐ[ℝ] ℝ[X],
        SourceHorizontalGammaSixAffineUntwisting Polynomial.X u φ ∧
          sourceHorizontalGammaSixPolynomialOriginFibre.Preserves φ := by
  exact ⟨sourceHorizontalGammaSixClosedFibre_preservedUntwisting_iff
      sourceHorizontalGammaSixPolynomialOriginFibre,
    sourceHorizontalGammaSixClosedFibre_no_gradeUniversalUntwisting
      sourceHorizontalGammaSixPolynomialOriginFibre⟩

end

end RHTower
