import GaloisForLFunctions.RHTower.ConnectedSymmetryBarrier

/-!
# Hasse classification of nonvanishing-loop homotopy classes

The winding number is promoted from a conserved quantity to an exact quotient classifier.
Nonvanishing loops with fixed endpoints are quotiented by equality of their winding packet; the
corpus homotopy theorem identifies this relation exactly with deformation through nonvanishing
loops.  The quotient is equivalent to its realized integer profiles, giving existence and
uniqueness for every realizable local invariant.
-/

namespace RHTower

noncomputable section

/-- A nonvanishing loop bundled with all continuity, endpoint, and nonvanishing obligations. -/
structure WindingLoop (a b : ℝ) where
  curve : ℝ → ℂ
  isLoop : IsLoop curve a b

/-- Integer Hasse packet of a bundled nonvanishing loop. -/
def windingLoopHassePacket {a b : ℝ} (L : WindingLoop a b) : ℤ :=
  windingNumber L.curve a b

/-- Deformation relation through nonvanishing loops with the same endpoints. -/
def WindingLoopJoined {a b : ℝ} (L M : WindingLoop a b) : Prop :=
  ∃ H : ℝ → ℝ → ℂ,
    Continuous (fun p : ℝ × ℝ => H p.1 p.2) ∧
    (∀ σ t, H σ t ≠ 0) ∧ (∀ σ, H σ a = H σ b) ∧
    (∀ t, H 0 t = L.curve t) ∧ (∀ t, H 1 t = M.curve t)

/-- Winding packets agree exactly when the two global loops are joined through nonvanishing
loops. -/
theorem windingLoopHassePacket_eq_iff_joined
    {a b : ℝ} (L M : WindingLoop a b) :
    windingLoopHassePacket L = windingLoopHassePacket M ↔
      WindingLoopJoined L M :=
  windingNumber_eq_iff_joined L.isLoop M.isLoop

/-- Setoid of nonvanishing loops classified by their complete winding packet. -/
def windingLoopHasseSetoid (a b : ℝ) : Setoid (WindingLoop a b) where
  r L M := windingLoopHassePacket L = windingLoopHassePacket M
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Global deformation classes of nonvanishing loops. -/
def WindingLoopHasseClass (a b : ℝ) :=
  Quotient (windingLoopHasseSetoid a b)

/-- Integer winding profiles actually realized by nonvanishing loops with endpoints `a,b`. -/
def WindingLoopHasseProfile (a b : ℝ) :=
  {z : ℤ // ∃ L : WindingLoop a b, windingLoopHassePacket L = z}

/-- Hasse map from global deformation classes to realized integer profiles. -/
def windingLoopClassHasseMap (a b : ℝ) :
    WindingLoopHasseClass a b → WindingLoopHasseProfile a b :=
  Quotient.lift
    (fun L => ⟨windingLoopHassePacket L, ⟨L, rfl⟩⟩)
    (by
      intro L M h
      apply Subtype.ext
      exact h)

/-- Winding profiles separate global nonvanishing-loop deformation classes. -/
theorem windingLoopClassHasseMap_injective (a b : ℝ) :
    Function.Injective (windingLoopClassHasseMap a b) := by
  intro q r h
  induction q using Quotient.inductionOn with
  | _ L =>
      induction r using Quotient.inductionOn with
      | _ M =>
          apply Quotient.sound
          change windingLoopHassePacket L = windingLoopHassePacket M
          exact congrArg Subtype.val h

/-- Every realized integer profile comes from a global loop class. -/
theorem windingLoopClassHasseMap_surjective (a b : ℝ) :
    Function.Surjective (windingLoopClassHasseMap a b) := by
  intro z
  obtain ⟨L, hL⟩ := z.2
  refine ⟨Quotient.mk (windingLoopHasseSetoid a b) L, ?_⟩
  apply Subtype.ext
  exact hL

/-- Global nonvanishing-loop deformation classes are exactly their realized winding profiles. -/
noncomputable def windingLoopClassHasseEquiv (a b : ℝ) :
    WindingLoopHasseClass a b ≃ WindingLoopHasseProfile a b :=
  Equiv.ofBijective (windingLoopClassHasseMap a b)
    ⟨windingLoopClassHasseMap_injective a b,
      windingLoopClassHasseMap_surjective a b⟩

/-- Every realizable winding profile has one unique global deformation class. -/
theorem windingLoopClass_existsUnique_of_profile
    {a b : ℝ} (z : WindingLoopHasseProfile a b) :
    ∃! q : WindingLoopHasseClass a b,
      windingLoopClassHasseMap a b q = z := by
  refine ⟨(windingLoopClassHasseEquiv a b).symm z, ?_, ?_⟩
  · exact (windingLoopClassHasseEquiv a b).apply_symm_apply z
  · intro q hq
    apply (windingLoopClassHasseEquiv a b).injective
    change windingLoopClassHasseMap a b q =
      windingLoopClassHasseMap a b ((windingLoopClassHasseEquiv a b).symm z)
    rw [hq]
    exact ((windingLoopClassHasseEquiv a b).apply_symm_apply z).symm

end


end RHTower
