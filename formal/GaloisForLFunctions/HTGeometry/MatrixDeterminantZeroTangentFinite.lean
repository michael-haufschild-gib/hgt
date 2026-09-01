import GaloisForLFunctions.HTGeometry.DifferentialMatrixGroupInfiniteTangent
import GaloisForLFunctions.HTGeometry.MatrixDeterminantKernelFinite

/-!
# Zero determinant-one tangent forces finiteness

Combines nonvanishing of the tangent of an infinite differential matrix group with the
index-at-most-two determinant decomposition.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- A determinant-square-one matrix group with zero determinant-one tangent is finite. -/
theorem finite_matrixSet_of_detOne_tangent_eq_bot
    {C : Type u} [Field C] [Algebra ℚ C] [CharZero C] [Differential C]
    [IsDifferentiallyClosed C]
    (G : Set (Matrix (Fin 2) (Fin 2) C))
    (gone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ G)
    (gmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G)
    (ginv : ∀ a ∈ G, ∃ b ∈ G, a * b = 1)
    (gdetSq : ∀ a ∈ G, a.det ^ 2 = 1)
    (hzero : matrixTangentM
        (matrixVanishingIdeal {a ∈ G | a.det = 1})
        (subset_matrixZeroSet_vanishingIdeal {a ∈ G | a.det = 1}
          ⟨gone, Matrix.det_one⟩) = ⊥) :
    G.Finite := by
  classical
  let H : Set (Matrix (Fin 2) (Fin 2) C) := {a ∈ G | a.det = 1}
  have hHone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ H := ⟨gone, Matrix.det_one⟩
  have hHmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H := by
    intro a ha b hb
    exact ⟨gmul a ha.1 b hb.1, by
      rw [Matrix.det_mul, ha.2, hb.2, one_mul]⟩
  have hHinv : ∀ a ∈ H, ∃ b ∈ H, a * b = 1 := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := ginv a ha.1
    refine ⟨b, ⟨hb, ?_⟩, hab⟩
    have hdetab : a.det * b.det = 1 := by
      rw [← Matrix.det_mul, hab]
      exact Matrix.det_one
    simpa [ha.2] using hdetab
  have hHfinite : H.Finite := by
    by_contra hnot
    have hInfinite : H.Infinite := Set.not_finite.mp hnot
    have hne := matrixTangentM_ne_bot_of_infinite_matrixSet H hHone hHmul
      (fun _ h => h.2) hHinv hInfinite
    apply hne
    simpa only [H] using hzero
  let S : Submonoid (Matrix (Fin 2) (Fin 2) C) :=
    { carrier := G
      one_mem' := gone
      mul_mem' := fun ha hb => gmul _ ha _ hb }
  have hright : ∀ x : S, ∃ y : S, x * y = 1 := by
    intro x
    obtain ⟨y, hy, hxy⟩ := ginv x x.property
    exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
  have hdetOneSubtype : ({x : S | x.1.det = 1} : Set S).Finite := by
    have hpre := hHfinite.preimage
      (f := fun x : S => (x : Matrix (Fin 2) (Fin 2) C))
      (fun _ _ _ _ h => Subtype.ext h)
    simpa [H, S] using hpre
  letI : Finite S := finite_submonoid_of_finite_detOne S hright
    (fun x => gdetSq x x.property) hdetOneSubtype
  have hSfinite : (S : Set (Matrix (Fin 2) (Fin 2) C)).Finite :=
    Set.toFinite (S : Set (Matrix (Fin 2) (Fin 2) C))
  simpa [S] using hSfinite

end

end GaloisForLFunctions.HTGeometry
