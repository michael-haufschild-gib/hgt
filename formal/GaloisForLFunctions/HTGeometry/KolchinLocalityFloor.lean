import GaloisForLFunctions.HTGeometry.KolchinSlopeDichotomy

/-!
# The operator-independent Kolchin locality floor

The one-reporter Kolchin slope takes only the values `0` and `1`, so it is a genuine two-valued
invariant of a reporter.  Taking the infimum of that invariant over a nonempty family of reporters
removes the arbitrary choice of local operator, and a forcing theorem — every member of the family
is hypertranscendental whenever the exchange law is — makes the floor at least the slope of the
exchange law itself.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]

open scoped Classical in
/-- The two-valued one-reporter Kolchin slope. -/
def kolchinSlopeValue (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential E] (x : E) : ℝ :=
  if HypertranscendentalOver F x then 1 else 0

theorem kolchinSlopeValue_nonneg (x : E) : 0 ≤ kolchinSlopeValue F x := by
  classical
  rw [kolchinSlopeValue]
  split <;> norm_num

theorem kolchinSlopeValue_le_one (x : E) : kolchinSlopeValue F x ≤ 1 := by
  classical
  rw [kolchinSlopeValue]
  split <;> norm_num

theorem kolchinSlopeValue_eq_one_of_hypertranscendentalOver {x : E}
    (hx : HypertranscendentalOver F x) : kolchinSlopeValue F x = 1 := by
  classical
  rw [kolchinSlopeValue, if_pos hx]

theorem kolchinSlopeValue_eq_zero_of_differentialAlgebraicOver {x : E}
    (hx : DifferentialAlgebraicOver F x) : kolchinSlopeValue F x = 0 := by
  classical
  rw [kolchinSlopeValue, if_neg (fun h => h hx)]

/-- **The slope value is the actual limit of the normalized jet rank.** -/
theorem tendsto_kolchinSlope_kolchinSlopeValue [Differential F] [DifferentialAlgebra F E]
    [CharZero E] (x : E) :
    Tendsto (normalizedRankSequence (kolchinJetRank F x)) atTop
      (nhds (kolchinSlopeValue F x)) := by
  classical
  by_cases hx : HypertranscendentalOver F x
  · rw [kolchinSlopeValue_eq_one_of_hypertranscendentalOver hx]
    exact tendsto_kolchinSlope_one_of_hypertranscendentalOver hx
  · have hda : DifferentialAlgebraicOver F x := not_not.mp hx
    rw [kolchinSlopeValue_eq_zero_of_differentialAlgebraicOver hda]
    exact tendsto_kolchinSlope_zero_of_differentialAlgebraicOver hda

/-- The operator-independent local floor of a nonempty family of reporters. -/
def kolchinLocalFloor (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential E] (fam : Set E) : ℝ :=
  ⨅ x : fam, kolchinSlopeValue F (x : E)

theorem bddBelow_kolchinSlopeValue_range (fam : Set E) :
    BddBelow (Set.range fun x : fam => kolchinSlopeValue F (x : E)) :=
  ⟨0, by rintro _ ⟨x, rfl⟩; exact kolchinSlopeValue_nonneg _⟩

theorem kolchinLocalFloor_nonneg {fam : Set E} (hne : fam.Nonempty) :
    0 ≤ kolchinLocalFloor F fam := by
  haveI := hne.to_subtype
  exact le_ciInf fun x => kolchinSlopeValue_nonneg _

/-- **The Kolchin locality inequality.**  If hypertranscendence of the exchange reporter forces
every member of a nonempty local family onto the hypertranscendental branch, then the local floor is
at least the slope of the exchange reporter. -/
theorem kolchinSlopeValue_le_kolchinLocalFloor {S : E} {fam : Set E} (hne : fam.Nonempty)
    (hforce : HypertranscendentalOver F S → ∀ A ∈ fam, HypertranscendentalOver F A) :
    kolchinSlopeValue F S ≤ kolchinLocalFloor F fam := by
  classical
  haveI := hne.to_subtype
  by_cases hS : HypertranscendentalOver F S
  · rw [kolchinSlopeValue_eq_one_of_hypertranscendentalOver hS]
    refine le_ciInf fun x => ?_
    rw [kolchinSlopeValue_eq_one_of_hypertranscendentalOver (hforce hS x x.2)]
  · have hda : DifferentialAlgebraicOver F S := not_not.mp hS
    rw [kolchinSlopeValue_eq_zero_of_differentialAlgebraicOver hda]
    exact kolchinLocalFloor_nonneg hne

/-- **Saturation on the hypertranscendental branch.**  If the exchange reporter is HT and forces the
family, the local floor is exactly `1`. -/
theorem kolchinLocalFloor_eq_one {S : E} {fam : Set E} (hne : fam.Nonempty)
    (hS : HypertranscendentalOver F S)
    (hforce : ∀ A ∈ fam, HypertranscendentalOver F A) :
    kolchinLocalFloor F fam = 1 := by
  classical
  haveI := hne.to_subtype
  refine le_antisymm ?_ ?_
  · obtain ⟨A, hA⟩ := hne
    refine le_trans (ciInf_le (bddBelow_kolchinSlopeValue_range fam) (⟨A, hA⟩ : fam)) ?_
    exact kolchinSlopeValue_le_one _
  · have := kolchinSlopeValue_le_kolchinLocalFloor (S := S) hne (fun _ => hforce)
    rwa [kolchinSlopeValue_eq_one_of_hypertranscendentalOver hS] at this

end

end GaloisForLFunctions.HTGeometry
