import GaloisForLFunctions.HTGeometry.ABHN.LocalInvariants
import GaloisForLFunctions.HTGeometry.ABHN.RestrictedBrauerGroup

/-!
# Archimedean localization in the restricted Brauer target

The unrestricted global-to-local Brauer map is already available at every number-field place.
Finite ramification is still needed to show that this full family is restricted.  Its
archimedean component is restricted unconditionally because a number field has only finitely many
infinite places.  Complex components are split, leaving only real places in this closed fragment.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The global-to-local Brauer map restricted to infinite places, with every finite place set to
the split class. -/
noncomputable def numberFieldArchimedeanLocalBrauerMap :
    BrauerGroup.{u, u} K → RestrictedLocalBrauerClasses K := fun x ↦
  { toLocalBrauerClasses := fun w ↦ by
      cases w with
      | infinite v => exact numberFieldLocalBrauerMap K x (.infinite v)
      | finite v => exact brauerSplitClass (completion K (.finite v))
    finite_nonSplit_support := by
      apply (Set.finite_range (fun v : NumberField.InfinitePlace K =>
        NumberFieldPlace.infinite v)).subset
      rintro (_ | v) h
      · change brauerSplitClass (completion K (.finite _)) ≠
          brauerSplitClass (completion K (.finite _)) at h
        exact False.elim (h rfl)
      · exact ⟨v, rfl⟩ }

/-- At an infinite place, archimedean localization is ordinary scalar-extension localization. -/
theorem numberFieldArchimedeanLocalBrauerMap_infinite
    (x : BrauerGroup.{u, u} K) (v : NumberField.InfinitePlace K) :
    (numberFieldArchimedeanLocalBrauerMap K x).toLocalBrauerClasses (.infinite v) =
      numberFieldLocalBrauerMap K x (.infinite v) := rfl

/-- At a finite place, archimedean localization deliberately has split value. -/
theorem numberFieldArchimedeanLocalBrauerMap_finite
    (x : BrauerGroup.{u, u} K) (v : NumberField.FinitePlace K) :
    (numberFieldArchimedeanLocalBrauerMap K x).toLocalBrauerClasses (.finite v) =
      brauerSplitClass (completion K (.finite v)) := rfl

/-- Archimedean localization is additive for tensor-product addition on Brauer classes. -/
noncomputable def numberFieldArchimedeanLocalBrauerAddHom :
    BrauerGroup.{u, u} K →+ RestrictedLocalBrauerClasses K where
  toFun := numberFieldArchimedeanLocalBrauerMap K
  map_zero' := by
    apply RestrictedLocalBrauerClasses.ext
    funext w
    cases w with
    | finite v => rfl
    | infinite v =>
      change numberFieldLocalBrauerMap K (brauerSplitClass K) (.infinite v) =
        brauerSplitClass (completion K (.infinite v))
      exact congrFun (numberFieldLocalBrauerMap_split K) (.infinite v)
  map_add' x y := by
    apply RestrictedLocalBrauerClasses.ext
    funext w
    cases w with
    | finite v =>
      change brauerSplitClass (completion K (.finite v)) =
        brauerSplitClass (completion K (.finite v)) +
          brauerSplitClass (completion K (.finite v))
      change (0 : BrauerGroup (completion K (.finite v))) = 0 + 0
      exact (zero_add 0).symm
    | infinite v =>
      change numberFieldLocalBrauerMap K (x + y) (.infinite v) =
        numberFieldLocalBrauerMap K x (.infinite v) +
          numberFieldLocalBrauerMap K y (.infinite v)
      exact congrFun (numberFieldLocalBrauerMap_tensorAdd K x y) (.infinite v)

/-- Complex infinite places make no contribution to the archimedean restricted family. -/
theorem numberFieldArchimedeanLocalBrauerMap_complex_eq_split
    (x : BrauerGroup.{u, u} K) (v : NumberField.InfinitePlace K) (hv : v.IsComplex) :
    (numberFieldArchimedeanLocalBrauerMap K x).toLocalBrauerClasses (.infinite v) =
      brauerSplitClass v.Completion := by
  exact complexInfiniteLocalBrauerMap_eq_split K v hv x

/-- The only possible nonsplit archimedean components are at real infinite places. -/
theorem numberFieldArchimedeanLocalBrauerMap_nonSplitSupport_subset_realInfinite
    (x : BrauerGroup.{u, u} K) :
    {w | (numberFieldArchimedeanLocalBrauerMap K x).toLocalBrauerClasses w ≠
      brauerSplitClass (completion K w)} ⊆
      {w | ∃ v : NumberField.InfinitePlace K, ¬v.IsComplex ∧ w = .infinite v} := by
  rintro (_ | v) h
  · change brauerSplitClass (completion K (.finite _)) ≠
      brauerSplitClass (completion K (.finite _)) at h
    exact False.elim (h rfl)
  · by_cases hv : v.IsComplex
    · exact False.elim (h (numberFieldArchimedeanLocalBrauerMap_complex_eq_split K x v hv))
    · exact ⟨v, hv, rfl⟩

end GaloisForLFunctions.HTGeometry.ABHN
