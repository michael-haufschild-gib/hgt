import GaloisForLFunctions.HTGeometry.MultipleSineCanonicalFaceOrbit
import GaloisForLFunctions.HTGeometry.EllipticGammaRationalBaseMatroid

/-!
# Off-face directions are differentially neutral

A maximal face `J` has complementary pair `{i, j}`, and its face coordinate is the double-sine
source of that pair.  In the two directions outside `J` the structural difference equation makes
the one-step defect a cotangent, which is differentially algebraic.  Telescoping over `ℤ` turns
that into: every integer translate of a face coordinate differs from it by a differentially
algebraic element.

This is the concrete analytic content behind rank-neutrality of an off-face direction, the second
interface of the face-gluing engine.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-! ### Telescoping a one-step defect over the integers -/

/-- **Integer telescoping of a translation defect.**  If one step of a translation moves an element
by a differentially algebraic amount, then so does every integer multiple of that step. -/
theorem differentialAlgebraicOver_zpow_translation_sub {q : ℂ}
    {Y : meroField (Set.univ : Set ℂ)}
    (h1 : DifferentialAlgebraicOver (RatFunc ℂ) (addTranslationMeroEquiv q Y - Y)) (n : ℤ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (addTranslationMeroEquiv ((n : ℂ) * q) Y - Y) := by
  have hneg : DifferentialAlgebraicOver (RatFunc ℂ)
      (addTranslationMeroEquiv (-q) Y - Y) := by
    have hmap : DifferentialAlgebraicOver (RatFunc ℂ)
        (addTranslationMeroEquiv (-q) (addTranslationMeroEquiv q Y - Y)) :=
      differentialAlgebraicOver_addTranslationMeroEquiv (-q) h1
    rw [(addTranslationMeroEquiv (-q)).map_sub, addTranslationMeroEquiv_add] at hmap
    have hz : -q + q = 0 := by ring
    rw [hz, addTranslationMeroEquiv_zero_apply] at hmap
    have hres := differentialAlgebraicOver_neg hmap
    have hrw : -(Y - addTranslationMeroEquiv (-q) Y)
        = addTranslationMeroEquiv (-q) Y - Y := by ring
    rwa [hrw] at hres
  have hstepGen : ∀ (p : ℂ) (m : ℤ),
      DifferentialAlgebraicOver (RatFunc ℂ) (addTranslationMeroEquiv p Y - Y) →
      DifferentialAlgebraicOver (RatFunc ℂ) (addTranslationMeroEquiv ((m : ℂ) * q) Y - Y) →
      DifferentialAlgebraicOver (RatFunc ℂ)
        (addTranslationMeroEquiv (p + (m : ℂ) * q) Y - Y) := by
    intro p m hp hm
    have hsum := differentialAlgebraicOver_add
      (differentialAlgebraicOver_addTranslationMeroEquiv p hm) hp
    rw [(addTranslationMeroEquiv p).map_sub, addTranslationMeroEquiv_add] at hsum
    have hcollapse :
        addTranslationMeroEquiv (p + (m : ℂ) * q) Y - addTranslationMeroEquiv p Y
          + (addTranslationMeroEquiv p Y - Y)
        = addTranslationMeroEquiv (p + (m : ℂ) * q) Y - Y := by ring
    rwa [hcollapse] at hsum
  induction n using Int.induction_on with
  | zero =>
      have hz : ((0 : ℤ) : ℂ) * q = 0 := by simp
      rw [hz, addTranslationMeroEquiv_zero_apply, sub_self]
      exact differentialAlgebraicOver_zero_mero
  | succ k ih =>
      have hres := hstepGen q k h1 ih
      have harg : q + ((k : ℤ) : ℂ) * q = (((k : ℤ) + 1 : ℤ) : ℂ) * q := by
        push_cast
        ring
      rwa [harg] at hres
  | pred k ih =>
      have hres := hstepGen (-q) (-(k : ℤ)) hneg ih
      have harg : -q + ((-(k : ℤ) : ℤ) : ℂ) * q = ((-(k : ℤ) - 1 : ℤ) : ℂ) * q := by
        push_cast
        ring
      rwa [harg] at hres

/-! ### The face coordinate in its two off-face directions -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The one-step defect of the canonical face coordinate in either off-face direction is
differentially algebraic: it is a cotangent up to a rational function. -/
theorem differentialAlgebraicOver_canonicalFace_step (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {i j : ι} (hij : i ≠ j) (hS : ({i, j} : Finset ι).Nonempty) {q : ι} (hq : q = i ∨ q = j) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (addTranslationMeroEquiv (ω q) (frameSourceMero ω hω ({i, j} : Finset ι) hS)
        - frameSourceMero ω hω ({i, j} : Finset ι) hS) := by
  classical
  have hcard : ({i, j} : Finset ι).card = 2 := Finset.card_pair hij
  have himem : i ∈ ({i, j} : Finset ι) := by simp
  have hjmem : j ∈ ({i, j} : Finset ι) := by simp
  obtain ⟨t, cst, hd0, hd1⟩ :=
    exists_exact_doubleSine_source ω hω ({i, j} : Finset ι) i j himem hjmem hij hcard hS
  set Mcan : meroField (Set.univ : Set ℂ) :=
    frameSourceMero ω hω ({i, j} : Finset ι) hS with hMcan
  have hrat : ∀ p : ℂ, DifferentialAlgebraicOver (RatFunc ℂ)
      (addTranslationMeroEquiv p (ratMero t) - ratMero t) := by
    intro p
    refine differentialAlgebraicOver_sub ?_ ?_
    · exact differentialAlgebraicOver_addTranslationMeroEquiv p
        (differentialAlgebraicOver_algebraMap (E := meroField (Set.univ : Set ℂ)) t)
    · exact differentialAlgebraicOver_algebraMap (E := meroField (Set.univ : Set ℂ)) t
  have hsplit : ∀ p : ℂ,
      addTranslationMeroEquiv p (Mcan + ratMero t) - (Mcan + ratMero t)
        = (addTranslationMeroEquiv p Mcan - Mcan)
          + (addTranslationMeroEquiv p (ratMero t) - ratMero t) := by
    intro p
    rw [(addTranslationMeroEquiv p).map_add]
    ring
  rcases hq with rfl | rfl
  · have hcot : DifferentialAlgebraicOver (RatFunc ℂ)
        (addTranslationMeroEquiv (ω q) (Mcan + ratMero t) - (Mcan + ratMero t)) := by
      rw [hd0]
      exact differentialAlgebraicOver_neg (differentialAlgebraicOver_periodCotMero (ω j))
    rw [hsplit (ω q)] at hcot
    have := differentialAlgebraicOver_sub hcot (hrat (ω q))
    have hrw : addTranslationMeroEquiv (ω q) Mcan - Mcan
          + (addTranslationMeroEquiv (ω q) (ratMero t) - ratMero t)
        - (addTranslationMeroEquiv (ω q) (ratMero t) - ratMero t)
        = addTranslationMeroEquiv (ω q) Mcan - Mcan := by ring
    rwa [hrw] at this
  · have hcot : DifferentialAlgebraicOver (RatFunc ℂ)
        (addTranslationMeroEquiv (ω q) (Mcan + ratMero t) - (Mcan + ratMero t)) := by
      rw [hd1]
      refine differentialAlgebraicOver_add
        (differentialAlgebraicOver_neg (differentialAlgebraicOver_periodCotMero (ω i))) ?_
      exact differentialAlgebraicOver_algebraMap (E := meroField (Set.univ : Set ℂ))
        (RatFunc.C cst)
    rw [hsplit (ω q)] at hcot
    have := differentialAlgebraicOver_sub hcot (hrat (ω q))
    have hrw : addTranslationMeroEquiv (ω q) Mcan - Mcan
          + (addTranslationMeroEquiv (ω q) (ratMero t) - ratMero t)
        - (addTranslationMeroEquiv (ω q) (ratMero t) - ratMero t)
        = addTranslationMeroEquiv (ω q) Mcan - Mcan := by ring
    rwa [hrw] at this

/-- **Off-face rank neutrality, in analytic form.**  Every integer translate, in an off-face
direction, of any external translate of the canonical face coordinate differs from it by a
differentially algebraic element — over the complex constants. -/
theorem differentialAlgebraicOver_translate_canonicalFace (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {i j : ι} (hij : i ≠ j) (hS : ({i, j} : Finset ι).Nonempty) {q : ι} (hq : q = i ∨ q = j)
    (s : ℂ) (n : ℤ) :
    DifferentialAlgebraicOver ℂ
      (addTranslationMeroEquiv ((n : ℂ) * ω q)
          (addTranslationMeroEquiv s (frameSourceMero ω hω ({i, j} : Finset ι) hS))
        - addTranslationMeroEquiv s (frameSourceMero ω hω ({i, j} : Finset ι) hS)) := by
  classical
  set Mcan : meroField (Set.univ : Set ℂ) :=
    frameSourceMero ω hω ({i, j} : Finset ι) hS with hMcan
  have hbase := differentialAlgebraicOver_zpow_translation_sub
    (differentialAlgebraicOver_canonicalFace_step ω hω hij hS hq) n
  have htrans := differentialAlgebraicOver_addTranslationMeroEquiv s hbase
  rw [(addTranslationMeroEquiv s).map_sub, addTranslationMeroEquiv_add] at htrans
  have hcomm : addTranslationMeroEquiv (s + (n : ℂ) * ω q) Mcan
      = addTranslationMeroEquiv ((n : ℂ) * ω q) (addTranslationMeroEquiv s Mcan) := by
    rw [addTranslationMeroEquiv_add]
    have harg : (n : ℂ) * ω q + s = s + (n : ℂ) * ω q := by ring
    rw [harg]
  rw [hcomm] at htrans
  exact differentialAlgebraicOver_complex_of_ratFunc htrans

end

end GaloisForLFunctions.HTGeometry
