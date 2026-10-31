import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentCoefficientStream

/-!
# Naturality of completed unipotent coefficient streams

A coefficient-ring map restricts to the actual unipotent matrix group.
The unrestricted stream bijection commutes with this map, allowing the
same coordinates to be evaluated in every local completion.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Entrywise coefficient mapping on actual completed unipotent matrices. -/
def unipotentCoefficientMap (f : R →+* S) : unipotentCoefficientGroup R →* unipotentCoefficientGroup S where
  toFun g := ⟨Matrix.SpecialLinearGroup.map (PowerSeries.map f) g.1, by
    apply (mem_unipotentCoefficientGroup S _).mpr
    change f (PowerSeries.constantCoeff (g.1 0 0)) = 1 ∧
      f (PowerSeries.constantCoeff (g.1 1 0)) = 0 ∧ f (PowerSeries.constantCoeff (g.1 1 1)) = 1
    obtain ⟨ha, hc, hd⟩ := (mem_unipotentCoefficientGroup R g).mp g.property
    rw [ha, hc, hd, map_one, map_zero]
    exact ⟨rfl, rfl, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.1 h.1)

@[simp] theorem unipotentCoefficientMap_apply (f : R →+* S)
    (g : unipotentCoefficientGroup R) (i j : Fin 2) :
    (unipotentCoefficientMap f g).1 i j = PowerSeries.map f (g.1 i j) := rfl

/-- Faithful ring maps remain faithful on the completed unipotent group. -/
theorem unipotentCoefficientMap_injective (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (unipotentCoefficientMap f) := by
  intro g h he
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  exact PowerSeries.map_injective f hf (congrArg (fun q : unipotentCoefficientGroup S => q.1 i j) he)

/-- The actual matrix map acts coefficientwise in the unrestricted stream. -/
theorem unipotentStream_map (f : R →+* S) (g : unipotentCoefficientGroup R) (N : ℕ) :
    unipotentCoefficientStreamEquiv S (unipotentCoefficientMap f g) N =
      f (unipotentCoefficientStreamEquiv R g N) := by
  change unipotentCoordinatesToStream S (unipotentCoefficientToCoordinates S (unipotentCoefficientMap f g)) N =
    f (unipotentCoordinatesToStream R (unipotentCoefficientToCoordinates R g) N)
  unfold unipotentCoordinatesToStream
  split_ifs <;> exact PowerSeries.coeff_map f _ _

/-- Decoding a mapped stream equals mapping the actual decoded matrix. -/
theorem unipotentCoefficientMap_stream_symm (f : R →+* S) (x : ℕ → R) :
    unipotentCoefficientMap f ((unipotentCoefficientStreamEquiv R).symm x) =
      (unipotentCoefficientStreamEquiv S).symm (fun n => f (x n)) := by
  apply (unipotentCoefficientStreamEquiv S).injective
  funext n
  rw [unipotentStream_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentCoefficientMap_injective
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentStream_map
