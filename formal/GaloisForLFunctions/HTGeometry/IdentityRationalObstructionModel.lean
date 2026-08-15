import GaloisForLFunctions.HTGeometry.TateFractureObstructionBianchiAmplitudeLaw

/-!
# The identity bigraded rational model has cofinal typed obstructions

The constant bigraded module whose every bidegree is the rational line carries the identity in every
twisted weight, because a constant bigraded family makes every degree shift the same object.  The
transported composite of two identities is again the identity, so the typed obstruction of weight
`n` is the number of positive decompositions of `n`, acting as a scalar on the rational line.

That number is nonzero for every weight at least two, so nonzero typed obstructions occur cofinally.
The model has unbounded vertical amplitude, as it must: finite amplitude forbids exactly this
behaviour.
-/

open CategoryTheory

namespace GaloisForLFunctions.HTGeometry

section IdentityModel

/-- The constant bigraded rational model. -/
noncomputable def identityRationalModel : ℤ → ℤ → ModuleCat ℚ := fun _ _ => ModuleCat.of ℚ ℚ

/-- Every twisted component of the constant model is the identity. -/
noncomputable def identityTwistedComponent (r : ℕ) :
    BundledTwistedComponent identityRationalModel r := fun _ _ => 𝟙 _

theorem composeAtWeight_identityTwistedComponent {n r s : ℕ} (h : r + s = n) (p q : ℤ) :
    bundledComposeTwistedComponentsAtWeight identityRationalModel n r s
        (identityTwistedComponent r) (identityTwistedComponent s) p q = 𝟙 _ := by
  rw [bundledComposeTwistedComponentsAtWeight, dif_pos h]
  simp only [identityTwistedComponent]
  rfl

/-- The typed obstruction of the identity model counts the positive decompositions of the
weight. -/
theorem bundledTypedTwistedObstruction_identityRational (n : ℕ) (p q : ℤ) :
    bundledTypedTwistedObstruction identityRationalModel identityTwistedComponent n p q =
      (((Finset.antidiagonal n).filter (fun x => 1 ≤ x.1 ∧ 1 ≤ x.2)).card) •
        𝟙 (ModuleCat.of ℚ ℚ) := by
  classical
  rw [bundledTypedTwistedObstruction, Finset.sum_apply, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun x hx =>
    composeAtWeight_identityTwistedComponent
      (Finset.mem_antidiagonal.mp (Finset.mem_filter.mp hx).1) p q]
  rw [Finset.sum_const]
  rfl

theorem nsmul_id_ne_zero {c : ℕ} (hc : c ≠ 0) :
    (c • 𝟙 (ModuleCat.of ℚ ℚ)) ≠ 0 := by
  intro h
  have hval := congrArg
    (fun f : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ => f.hom (1 : ℚ)) h
  simp at hval
  exact hc hval

/-- **Cofinal typed obstructions in the identity model.**  The constant bigraded rational module
with identity twisted components has nonzero typed obstructions at arbitrarily high weights. -/
theorem hasCofinalNonzeroBundledTypedObstructions_identityRational :
    HasCofinalNonzeroBundledTypedObstructions identityRationalModel identityTwistedComponent := by
  classical
  intro c
  refine ⟨c + 2, by omega, fun hzero => ?_⟩
  have hval : bundledTypedTwistedObstruction identityRationalModel identityTwistedComponent
      (c + 2) 0 0 = 0 := by
    rw [hzero]
    rfl
  rw [bundledTypedTwistedObstruction_identityRational] at hval
  have hcard : (((Finset.antidiagonal (c + 2)).filter
      (fun x => 1 ≤ x.1 ∧ 1 ≤ x.2)).card) ≠ 0 := by
    refine Finset.card_ne_zero_of_mem (a := (1, c + 1)) ?_
    exact Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr (by omega), by omega, by omega⟩
  exact nsmul_id_ne_zero hcard hval

/-- The identity model has unbounded vertical amplitude. -/
theorem not_bundledHasVerticalAmplitude_identityRational (a b : ℤ) :
    ¬ BundledHasVerticalAmplitude identityRationalModel a b :=
  cofinalNonzeroBundledTypedObstructions_not_verticalAmplitude identityRationalModel
    identityTwistedComponent hasCofinalNonzeroBundledTypedObstructions_identityRational

end IdentityModel

end GaloisForLFunctions.HTGeometry
