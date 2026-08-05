import GaloisForLFunctions.HTGeometry.TailQuotientSeparationLaw

/-!
# Saturated supports and determined reporters exist

The separation laws of the tail quotient run on two families of hypotheses: that completion erases
every modification supported in a given set, and that a reporter is determined by a given
observation.  Neither was ever exhibited.

Both extremes realize them.  The empty support is saturated for *every* setoid, because a record
that is unmodified outside it is unmodified; and the all-identifying setoid is saturated on every
support.  Dually, constant reporters are determined by every observation, and a reporter is
determined by the total observation whenever the observation determines the record.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ## Saturated supports -/

/-- **The empty support is saturated for every completion.**  A modification supported in it is no
modification at all. -/
theorem modificationSaturatedOn_empty {I A : Type*} (r : Setoid (I → A)) :
    ModificationSaturatedOn r (∅ : Set I) := by
  intro u v h
  have huv : u = v := by
    funext i
    by_contra hne
    exact (h hne).elim
  subst huv
  exact r.refl u

/-- The all-identifying completion is saturated on every support. -/
theorem modificationSaturatedOn_top {I A : Type*} (E : Set I) :
    ModificationSaturatedOn (⊤ : Setoid (I → A)) E := fun _ _ _ => trivial

/-- Saturation is monotone downward in the support. -/
theorem ModificationSaturatedOn.mono {I A : Type*} {r : Setoid (I → A)} {E F : Set I}
    (h : ModificationSaturatedOn r F) (hEF : E ⊆ F) :
    ModificationSaturatedOn r E := fun _ _ hsub => h (hsub.trans hEF)

/-! ## Saturated support families -/

/-- The empty family is saturated for every completion. -/
theorem observationSupportFamilySaturated_empty {I A : Type*} (r : Setoid (I → A)) :
    ObservationSupportFamilySaturated r (∅ : Set (Set I)) := by
  intro E hE
  exact hE.elim

/-- The family of the empty support is saturated for every completion. -/
theorem observationSupportFamilySaturated_singleton_empty {I A : Type*} (r : Setoid (I → A)) :
    ObservationSupportFamilySaturated r ({(∅ : Set I)} : Set (Set I)) := by
  intro E hE
  rw [Set.mem_singleton_iff] at hE
  subst hE
  exact modificationSaturatedOn_empty r

/-- The all-identifying completion saturates every support family, including the full power set. -/
theorem observationSupportFamilySaturated_top {I A : Type*} (𝒩 : Set (Set I)) :
    ObservationSupportFamilySaturated (⊤ : Setoid (I → A)) 𝒩 :=
  fun E _ => modificationSaturatedOn_top E

/-! ## Determined reporters -/

/-- Constant reporters are determined by every observation support. -/
theorem coordinateQuotientReporterDeterminedOn_const {I A Y : Type*} (r : Setoid (I → A))
    (E : Set I) (y : Y) :
    CoordinateQuotientReporterDeterminedOn r E (fun _ => y) := fun _ _ _ => rfl

/-- Every reporter is determined by the total observation support. -/
theorem coordinateQuotientReporterDeterminedOn_univ {I A Y : Type*} (r : Setoid (I → A))
    (F : Quotient r → Y) :
    CoordinateQuotientReporterDeterminedOn r (Set.univ : Set I) F := by
  intro u v h
  have huv : u = v := funext fun i => h i (Set.mem_univ i)
  rw [huv]

/-- Constant reporters are determined by every finite observation. -/
theorem finiteCoordinateQuotientReporterDeterminedBy_const {I A Y : Type*} (r : Setoid (I → A))
    (s : Finset I) (y : Y) :
    FiniteCoordinateQuotientReporterDeterminedBy r s (fun _ => y) := fun _ _ _ => rfl

/-- On a finite index set, every reporter is determined by the total finite observation. -/
theorem finiteCoordinateQuotientReporterDeterminedBy_univ {I A Y : Type*} [Fintype I]
    [DecidableEq I] (r : Setoid (I → A)) (F : Quotient r → Y) :
    FiniteCoordinateQuotientReporterDeterminedBy r (Finset.univ : Finset I) F := by
  intro u v h
  have huv : u = v := funext fun i => h i (Finset.mem_univ i)
  rw [huv]

/-- Constant reporters are determined by every finite horizon. -/
theorem tailQuotientReporterDeterminedBy_const {A Y : Type*} (r : Setoid (ℕ → A))
    (N : ℕ) (y : Y) :
    TailQuotientReporterDeterminedBy r N (fun _ => y) := fun _ _ _ => rfl

/-- A reporter determined by one horizon is determined by every longer horizon. -/
theorem TailQuotientReporterDeterminedBy.mono {A Y : Type*} {r : Setoid (ℕ → A)}
    {N M : ℕ} {F : Quotient r → Y} (h : TailQuotientReporterDeterminedBy r N F) (hNM : N ≤ M) :
    TailQuotientReporterDeterminedBy r M F :=
  fun u v hagree => h u v fun n hn => hagree n (hn.trans hNM)

end GaloisForLFunctions.HTGeometry
