import GaloisForLFunctions.MeromorphicSimplePoleDifferentialOperator

/-!
# The analytic theta differential-orbit obstruction

For a translation nontorsion modulo the theta lattice and a shift outside the enlarged lattice,
the differentiated theta defect has exactly one pole on its distinguished translation orbit.  The
pole-support boundary theorem then excludes it from every meromorphic shift coboundary whose pole
indices on that orbit are finite.
-/

open Complex Set Filter
open scoped Topology

namespace GaloisForLFunctions

noncomputable section

/-- Translation by `q` is nontorsion modulo `ℤ + ℤτ`. -/
def ThetaTranslationNontorsion (τ q : ℂ) : Prop :=
  ∀ a b n : ℤ, n * q = a + b * τ → n = 0

/-- The shift `h` lies outside the enlarged lattice `ℤ + ℤτ + ℤq`. -/
def ThetaTranslationNonresonant (τ q h : ℂ) : Prop :=
  ¬ ∃ a b n : ℤ, h = a + b * τ + n * q

theorem thetaNonlatticeShift_of_translationNonresonant
    {τ q h : ℂ} (hnonres : ThetaTranslationNonresonant τ q h) :
    ThetaNonlatticeShift τ h := by
  intro hh
  obtain ⟨a, b, hab⟩ := hh
  apply hnonres
  exact ⟨a, b, 0, by simpa using hab⟩

/-- **Differential theta orbit obstruction.** A nonzero constant-coefficient differential
operator applied to a nonresonant theta defect cannot be a shift coboundary of a meromorphic
function with finitely many pole indices on the distinguished orbit. -/
theorem thetaDifferentialOperator_ne_shiftCoboundary_of_finitePoleOrbit
    {L : Polynomial ℂ} (hL : L ≠ 0) {τ q h : ℂ} (hτ : 0 < τ.im)
    (hq : ThetaTranslationNontorsion τ q)
    (hnonres : ThetaTranslationNonresonant τ q h)
    (g : ℂ → ℂ)
    (hg : ∀ n : ℤ, MeromorphicAt g
      (additiveOrbitPoint (thetaHalfPeriod τ - h) q n))
    (hfinite : (poleIndexSet g (thetaHalfPeriod τ - h) q).Finite) :
    ¬ ∀ z : ℂ,
      constantCoeffDifferentialOperator L (thetaLogDerivDefect h · τ) z =
        g (z + q) - g z := by
  intro heq
  let p := thetaHalfPeriod τ - h
  let f := constantCoeffDifferentialOperator L (thetaLogDerivDefect h · τ)
  have hh := thetaNonlatticeShift_of_translationNonresonant hnonres
  apply shiftCoboundary_not_singleton_poleOrbit g f p q hg
    (fun z => heq z) hfinite
  · apply (constantCoeffDifferentialOperator_thetaLogDerivDefect_pole_iff hL hτ hh).2
    right
    exact ⟨0, 0, by simp [p]⟩
  · intro n hnPole
    obtain hbase | hshift :=
      (constantCoeffDifferentialOperator_thetaLogDerivDefect_pole_iff hL hτ hh).1 hnPole
    · obtain ⟨a, b, hab⟩ := hbase
      exfalso
      apply hnonres
      refine ⟨-a, -b, n, ?_⟩
      dsimp [additiveOrbitPoint, p] at hab
      push_cast
      linear_combination -hab
    · obtain ⟨a, b, hab⟩ := hshift
      apply hq a b n
      dsimp [additiveOrbitPoint, p] at hab
      linear_combination hab

end

end GaloisForLFunctions
