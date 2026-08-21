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

/-- The real-place coordinates of archimedean localization.  Finite coordinates are discarded
and complex coordinates are canonically split. -/
noncomputable def numberFieldRealLocalBrauerCoordinates :
    BrauerGroup.{u, u} K →
      ((v : {v : NumberField.InfinitePlace K // ¬ v.IsComplex}) →
        BrauerGroup.{u, u} v.1.Completion) := fun x v ↦
  numberFieldLocalBrauerMap K x (.infinite v.1)

/-- The real-place coordinate map is additive.  This is the archimedean component of the
global-to-local Brauer map after discarding the provably split finite and complex components. -/
noncomputable def numberFieldRealLocalBrauerCoordinatesAddHom :
    BrauerGroup.{u, u} K →+
      ((v : {v : NumberField.InfinitePlace K // ¬ v.IsComplex}) →
        BrauerGroup.{u, u} v.1.Completion) where
  toFun := numberFieldRealLocalBrauerCoordinates K
  map_zero' := by
    funext v
    change numberFieldLocalBrauerMap K (brauerSplitClass K) (.infinite v.1) =
      brauerSplitClass v.1.Completion
    exact congrFun (numberFieldLocalBrauerMap_split K) (.infinite v.1)
  map_add' := by
    intro x y
    funext v
    change numberFieldLocalBrauerMap K (x + y) (.infinite v.1) =
      numberFieldLocalBrauerMap K x (.infinite v.1) +
        numberFieldLocalBrauerMap K y (.infinite v.1)
    exact congrFun (numberFieldLocalBrauerMap_tensorAdd K x y) (.infinite v.1)

/-- Two archimedean restricted Brauer families agree exactly when their real-place coordinates
agree.  Thus complex places impose no independent archimedean coordinate in ABHN. -/
theorem numberFieldArchimedeanLocalBrauerMap_eq_iff_realCoordinates
    (x y : BrauerGroup.{u, u} K) :
    numberFieldArchimedeanLocalBrauerMap K x = numberFieldArchimedeanLocalBrauerMap K y ↔
      numberFieldRealLocalBrauerCoordinates K x = numberFieldRealLocalBrauerCoordinates K y := by
  constructor
  · intro h
    funext v
    exact congrFun (congrArg RestrictedLocalBrauerClasses.toLocalBrauerClasses h) (.infinite v.1)
  · intro h
    apply RestrictedLocalBrauerClasses.ext
    funext w
    cases w with
    | finite v => rfl
    | infinite v =>
      by_cases hv : v.IsComplex
      · change numberFieldLocalBrauerMap K x (.infinite v) =
          numberFieldLocalBrauerMap K y (.infinite v)
        calc
          numberFieldLocalBrauerMap K x (.infinite v) =
              brauerSplitClass (completion K (.infinite v)) :=
            complexInfiniteLocalBrauerMap_eq_split K v hv x
          _ = numberFieldLocalBrauerMap K y (.infinite v) :=
            (complexInfiniteLocalBrauerMap_eq_split K v hv y).symm
      · let rv : {v : NumberField.InfinitePlace K // ¬ v.IsComplex} := ⟨v, hv⟩
        change numberFieldLocalBrauerMap K x (.infinite v) =
          numberFieldLocalBrauerMap K y (.infinite v)
        exact congrFun h rv

/-- The global classes with trivial archimedean localization are exactly those with all real
coordinates trivial.  This is a kernel identity, not an assertion that either kernel is zero. -/
theorem numberFieldArchimedeanLocalBrauerAddHom_ker_eq_realCoordinates_ker :
    (numberFieldArchimedeanLocalBrauerAddHom K).ker =
      (numberFieldRealLocalBrauerCoordinatesAddHom K).ker := by
  ext x
  change numberFieldArchimedeanLocalBrauerMap K x = 0 ↔
    numberFieldRealLocalBrauerCoordinates K x = 0
  rw [← (numberFieldArchimedeanLocalBrauerAddHom K).map_zero,
    ← (numberFieldRealLocalBrauerCoordinatesAddHom K).map_zero]
  exact numberFieldArchimedeanLocalBrauerMap_eq_iff_realCoordinates K x 0

end GaloisForLFunctions.HTGeometry.ABHN
