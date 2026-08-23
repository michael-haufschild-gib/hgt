import GaloisForLFunctions.HTGeometry.OrbitChargeSuperselection

/-!
# Hasse principles for finite orbit-charge data

The global gauge class of finitely supported data on disjoint integer orbits is detected by the
charge on every orbit.  Vanishing and equality of all local charges are respectively equivalent to
global boundary triviality and global gauge equivalence.  Every finitely supported local charge
profile has a global realization.
-/

namespace GaloisForLFunctions

noncomputable section

/-- A finite multi-orbit datum is a global gauge boundary exactly when every local orbit charge
vanishes. -/
theorem orbitwiseBoundary_hasse_iff
    {ι A : Type*} [AddCommGroup A] (D : ι →₀ (ℤ →₀ A)) :
    (∃ E, D = orbitwiseBoundary E) ↔
      ∀ i, additiveOrbitSum (D i) = 0 := by
  rw [← orbitwiseCharge_eq_zero_iff_exists_boundary D]
  constructor
  · intro h i
    have hi := congrArg (fun q : ι →₀ A => q i) h
    simpa [orbitwiseCharge] using hi
  · intro h
    ext i
    simpa [orbitwiseCharge] using h i

/-- Two finite multi-orbit data are globally gauge equivalent exactly when all their local orbit
charges agree. -/
theorem orbitwiseGauge_hasse_iff
    {ι A : Type*} [AddCommGroup A] (D F : ι →₀ (ℤ →₀ A)) :
    (∃ E, D - F = orbitwiseBoundary E) ↔
      ∀ i, additiveOrbitSum (D i) = additiveOrbitSum (F i) := by
  rw [← orbitwiseData_sameCharge_iff_boundary D F]
  constructor
  · intro h i
    have hi := congrArg (fun q : ι →₀ A => q i) h
    simpa [orbitwiseCharge] using hi
  · intro h
    ext i
    simpa [orbitwiseCharge] using h i

/-- Every finitely supported collection of local orbit charges has a global finite datum. -/
theorem orbitwiseCharge_hasse_surjective
    {ι A : Type*} [AddCommGroup A] (q : ι →₀ A) :
    ∃ D : ι →₀ (ℤ →₀ A),
      ∀ i, additiveOrbitSum (D i) = q i := by
  obtain ⟨D, hD⟩ := orbitwiseChargeHom_surjective (ι := ι) (A := A) q
  refine ⟨D, fun i => ?_⟩
  have hi := congrArg (fun r : ι →₀ A => r i) hD
  simpa [orbitwiseChargeHom_apply, orbitwiseCharge] using hi

end


end GaloisForLFunctions
