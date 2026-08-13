import GaloisForLFunctions.RHTower.FieldOneFiniteStageSUnitClosed

/-!
# Explicit compact fundamental domain for the module-one idele classes

For every finite set `S` of rational finite places, the module-one part of the
finite-stage idele class group is canonically isomorphic and homeomorphic to
the product of the selected local unit groups.  This strengthens the previous
surjectivity/compactness result to an exact topological-group identification.

The key rigidity is archimedean: two norm-one representatives with real
coordinate `1` can differ by a diagonal rational `S`-unit only when that
rational unit is `1`.  Closedness of the diagonal `S`-unit image supplies the
Hausdorff quotient needed for the compact-to-Hausdorff argument.
-/

open scoped NNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain

/-- The canonical map from the product of selected local unit groups to the
module-one class group is injective. -/
theorem fieldOneFiniteStageNormOneTorusToModuleOne_injective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Function.Injective (fieldOneFiniteStageNormOneTorusToModuleOne S) := by
  intro k l hkl
  have hclass := congrArg Subtype.val hkl
  change
    (QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S))
        (fieldOneFiniteStageNormOneTorusIdele S k) =
      (QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S))
        (fieldOneFiniteStageNormOneTorusIdele S l) at hclass
  rw [QuotientGroup.mk'_eq_mk'] at hclass
  rcases hclass with ⟨z, hzN, hzEq⟩
  change z ∈ Subgroup.map
    (fieldOneFiniteStageDiagonalUnit S) (fieldOneSUnitSubgroup S) at hzN
  rw [Subgroup.mem_map] at hzN
  rcases hzN with ⟨q, hqS, hqz⟩
  have hzReal : ((z.1 : ℝˣ) : ℝ) = 1 := by
    have h := congrArg (fun u : FieldOneFiniteStageIdele S => (u.1 : ℝ)) hzEq
    simpa [fieldOneFiniteStageNormOneTorusIdele] using h
  have hqReal : (((q : ℚˣ) : ℚ) : ℝ) = 1 := by
    calc
      (((q : ℚˣ) : ℚ) : ℝ) = ((z.1 : ℝˣ) : ℝ) := by
        exact congrArg (fun a : FieldOneFiniteStageIdele S => (a.1 : ℝ)) hqz
      _ = 1 := hzReal
  have hqVal : ((q : ℚˣ) : ℚ) = 1 := by
    exact_mod_cast hqReal
  have hqOne : q = 1 := by
    apply Units.ext
    exact hqVal
  have hzOne : z = 1 := by
    rw [← hqz, hqOne, map_one]
  rw [hzOne, mul_one] at hzEq
  apply funext
  intro v
  apply Subtype.ext
  apply Units.ext
  have h := congrArg
    (fun u : FieldOneFiniteStageIdele S =>
      ((u.2 v : (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ)) hzEq
  exact h

/-- Canonical multiplicative equivalence between the selected local unit torus
and the module-one finite-stage idele class group. -/
def fieldOneFiniteStageNormOneTorusMulEquiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageNormOneTorus S ≃*
      FieldOneFiniteStageModuleOneClass S :=
  MulEquiv.ofBijective (fieldOneFiniteStageNormOneTorusToModuleOne S)
    ⟨fieldOneFiniteStageNormOneTorusToModuleOne_injective S,
      fieldOneFiniteStageNormOneTorusToModuleOne_surjective S⟩

set_option synthInstance.maxHeartbeats 200000

/-- Canonical homeomorphism from the selected local unit torus onto the
module-one finite-stage idele class group. -/
def fieldOneFiniteStageNormOneTorusHomeomorph
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageNormOneTorus S ≃ₜ
      FieldOneFiniteStageModuleOneClass S :=
  (fieldOneFiniteStageNormOneTorusMulEquiv S).toEquiv.toHomeomorphOfContinuousClosed
    (fieldOneFiniteStageNormOneTorusToModuleOne_continuous S)
    (fieldOneFiniteStageNormOneTorusToModuleOne_continuous S).isClosedMap

/-- The preceding homeomorphism respects multiplication in both directions. -/
def fieldOneFiniteStageNormOneTorusContinuousMulEquiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageNormOneTorus S ≃ₜ*
      FieldOneFiniteStageModuleOneClass S :=
  ContinuousMulEquiv.mk
    (fieldOneFiniteStageNormOneTorusMulEquiv S)
    (fieldOneFiniteStageNormOneTorusToModuleOne_continuous S)
    (fieldOneFiniteStageNormOneTorusHomeomorph S).symm.continuous

end

end GaloisForLFunctions.RHTower
