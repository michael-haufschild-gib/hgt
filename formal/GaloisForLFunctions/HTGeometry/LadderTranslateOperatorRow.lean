import GaloisForLFunctions.HTGeometry.ScaledDigammaTranslateIndependence
import GaloisForLFunctions.HTGeometry.DifferentialOperatorRowHypertranscendence
import GaloisForLFunctions.HTGeometry.EllipticCompositumRationalBase
import GaloisForLFunctions.HTGeometry.EllipticGammaFlatNonvanishing

/-!
# A nonzero differential-linear form in ladder translates is hypertranscendental

The atomic theorem makes the translates of a solution of the order-one ladder differentially
independent over the coordinate field.  Restricting the coefficient field to the constants keeps them
independent, and a nonzero row of constant-coefficient differential operators applied to a
differentially independent family is hypertranscendental over the constants — the triangular
substitution that reads off the highest jet.  Differential algebraicity over the coordinate field
descends to the constants, so hypertranscendence over the constants is the stronger statement, and
the form is hypertranscendental over the coordinate field as well.

This is the step the reverse inclusion of the Barnes annihilator theorem uses: after the ladder has
reduced the source to one period, a nonzero operator of the remaining ring becomes a nonzero
constant-coefficient differential-linear form in translates on distinct orbits, hence not
differentially algebraic.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic zeroNomeScalarTower

/-- **A nonzero constant-coefficient differential-linear form in ladder translates is
hypertranscendental over the coordinate field.**  Here `φ` solves the order-one ladder equation
`φ(z + ω) - φ(z) = 1/z` and the shifts are pairwise distinct modulo `ωℤ`. -/
theorem hypertranscendentalOver_ladderTranslateOperatorRow {ω : ℂ} (hω : ω ≠ 0) (b : ℂ)
    (φ : meroField (Set.univ : Set ℂ))
    (hφ : addTranslationMeroEquiv ω φ
      = φ + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
        (1 / (RatFunc.X + RatFunc.C b)))
    {r : ℕ} (h : Fin r → ℂ)
    (hincong : ∀ i i' : Fin r, i ≠ i' → ∀ n : ℤ, h i - h i' ≠ (n : ℂ) * ω)
    (L : Fin r → Polynomial ℂ) (hL : L ≠ 0) :
    HypertranscendentalOver (RatFunc ℂ)
      (∑ i, differentialOperatorApply (L i) (addTranslationMeroEquiv (h i) φ)) := by
  intro hDA
  have hind := differentialIndependent_ladderTranslate hω b φ hφ h hincong
  have hindC : DifferentialIndependent ℂ fun i => addTranslationMeroEquiv (h i) φ :=
    hind.restrictScalars (algebraMap ℂ (RatFunc ℂ)).injective
  exact hypertranscendentalOver_differentialOperatorRow_of_ne_zero
    deriv_algebraMap_complex L hL _ hindC
    (differentialAlgebraicOver_complex_of_ratFunc hDA)

end

end GaloisForLFunctions.HTGeometry

/-! ## An arbitrary finite index -/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic zeroNomeScalarTower

/-- **A nonzero operator row on ladder translates indexed by an arbitrary finite type.** -/
theorem hypertranscendentalOver_ladderTranslateOperatorRow_fintype {ω : ℂ} (hω : ω ≠ 0) (b : ℂ)
    (φ : meroField (Set.univ : Set ℂ))
    (hφ : addTranslationMeroEquiv ω φ
      = φ + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
        (1 / (RatFunc.X + RatFunc.C b)))
    {κ : Type*} [Fintype κ] [DecidableEq κ] (h : κ → ℂ)
    (hincong : ∀ i i' : κ, i ≠ i' → ∀ n : ℤ, h i - h i' ≠ (n : ℂ) * ω)
    (L : κ → Polynomial ℂ) (hL : L ≠ 0) :
    HypertranscendentalOver (RatFunc ℂ)
      (∑ i, differentialOperatorApply (L i) (addTranslationMeroEquiv (h i) φ)) := by
  intro hDA
  have hind := differentialIndependent_ladderTranslate_fintype hω b φ hφ h hincong
  have hindC : DifferentialIndependent ℂ fun i => addTranslationMeroEquiv (h i) φ :=
    hind.restrictScalars (algebraMap ℂ (RatFunc ℂ)).injective
  exact hypertranscendentalOver_differentialOperatorRow_of_ne_zero
    deriv_algebraMap_complex L hL _ hindC
    (differentialAlgebraicOver_complex_of_ratFunc hDA)

/-! ## The monomial shift dictionary -/

/-- The shift that a translation monomial applies. -/
def monomialShift {N : ℕ} (ω : Fin N → ℂ) (n : Fin N →₀ ℕ) : ℂ := ∑ k, (n k : ℂ) * ω k

/-- **Rationally independent periods separate the monomial shifts.**  Two distinct exponent vectors
avoiding the direction `j` give shifts in different classes modulo `ω j ℤ`: an equality of classes is
a nontrivial integral relation among the periods. -/
theorem monomialShift_incongruent {N : ℕ} (ω : Fin N → ℂ)
    (hQ : ∀ n : Fin N → ℤ, ∑ k, (n k : ℂ) * ω k = 0 → ∀ k, n k = 0)
    (j : Fin N) {a b : Fin N →₀ ℕ} (ha : a j = 0) (hb : b j = 0) (hab : a ≠ b) (m : ℤ) :
    monomialShift ω a - monomialShift ω b ≠ (m : ℂ) * ω j := by
  classical
  intro hcon
  set n : Fin N → ℤ := fun k => if k = j then -m else (a k : ℤ) - (b k : ℤ) with hn
  have hterm : ∀ k : Fin N, ((n k : ℤ) : ℂ) * ω k
      = ((a k : ℂ) - (b k : ℂ)) * ω k - (if k = j then (m : ℂ) * ω j else 0) := by
    intro k
    by_cases hk : k = j
    · subst hk
      rw [hn]
      simp only [ha, hb]
      push_cast
      ring
    · rw [hn]
      simp only [if_neg hk]
      push_cast
      ring
  have hdiff : monomialShift ω a - monomialShift ω b
      = ∑ k, ((a k : ℂ) - (b k : ℂ)) * ω k := by
    rw [monomialShift, monomialShift, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hrel : ∑ k, ((n k : ℤ) : ℂ) * ω k = 0 := by
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib, ← hdiff, hcon,
      Finset.sum_ite_eq' Finset.univ j fun _ => (m : ℂ) * ω j]
    simp
  have hzero := hQ n hrel
  obtain ⟨k₀, hk₀⟩ := Finsupp.ne_iff.mp hab
  have hkj : k₀ ≠ j := by
    intro hcj
    rw [hcj, ha, hb] at hk₀
    exact hk₀ rfl
  have := hzero k₀
  rw [hn] at this
  simp only [if_neg hkj, sub_eq_zero] at this
  exact hk₀ (by exact_mod_cast this)

/-! ## A nonzero translation-differential operator on one ladder solution -/

/-- **The reverse-inclusion step of the Barnes annihilator theorem.**  Let the periods be
rationally independent, let `φ` solve the ladder equation for the period `ω j`, and let a
constant-coefficient differential-translation operator avoid the direction `j`.  If the operator is
nonzero, its value on `φ` is hypertranscendental over the coordinate field. -/
theorem hypertranscendentalOver_ladderMonomialOperatorSum {N : ℕ} (ω : Fin N → ℂ)
    (hQ : ∀ n : Fin N → ℤ, ∑ k, (n k : ℂ) * ω k = 0 → ∀ k, n k = 0)
    (j : Fin N) (b : ℂ) (φ : meroField (Set.univ : Set ℂ))
    (hφ : addTranslationMeroEquiv (ω j) φ
      = φ + algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
        (1 / (RatFunc.X + RatFunc.C b)))
    (s : Finset (Fin N →₀ ℕ)) (hs : ∀ n ∈ s, n j = 0)
    (L : (Fin N →₀ ℕ) → Polynomial ℂ) {n₀ : Fin N →₀ ℕ} (hn₀ : n₀ ∈ s) (hL : L n₀ ≠ 0) :
    HypertranscendentalOver (RatFunc ℂ)
      (∑ n ∈ s, differentialOperatorApply (L n)
        (addTranslationMeroEquiv (monomialShift ω n) φ)) := by
  classical
  have hωj : ω j ≠ 0 := by
    intro h0
    have hrel : ∑ k, (((if k = j then (1 : ℤ) else 0) : ℤ) : ℂ) * ω k = 0 := by
      rw [Finset.sum_eq_single j]
      · simp [h0]
      · intro k _ hk
        simp [hk]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have := hQ _ hrel j
    simp at this
  have hsum : (∑ n ∈ s, differentialOperatorApply (L n)
        (addTranslationMeroEquiv (monomialShift ω n) φ))
      = ∑ x : {x // x ∈ s}, differentialOperatorApply (L x.1)
        (addTranslationMeroEquiv (monomialShift ω x.1) φ) :=
    (Finset.sum_coe_sort s _).symm
  rw [hsum]
  refine hypertranscendentalOver_ladderTranslateOperatorRow_fintype hωj b φ hφ
    (fun x : {x // x ∈ s} => monomialShift ω x.1) ?_ (fun x => L x.1) ?_
  · intro x x' hxx m
    exact monomialShift_incongruent ω hQ j (hs _ x.2) (hs _ x'.2)
      (fun hc => hxx (Subtype.ext hc)) m
  · intro hzero
    exact hL (congrFun hzero ⟨n₀, hn₀⟩)

end

end GaloisForLFunctions.HTGeometry
