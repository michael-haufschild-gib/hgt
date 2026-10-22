import GaloisForLFunctions.RHTower.Schanuel.SchanuelWeldApex
import GaloisForLFunctions.RHTower.ExpAlgebraicTranscendental
import GaloisForLFunctions.HTGeometry.TranscendenceSubfamilyExtraction
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Stagewise form of the Schanuel interface, and its first two stages

Schanuel's conjecture is carried in the corpus as one `Prop` interface quantified over the family
size.  Splitting it stagewise isolates exactly which stages are open: the empty and one-element
stages hold unconditionally.  The latter is Hermite–Lindemann: for every nonzero complex number,
either it or its exponential is transcendental.  Thus stage two is the first genuinely open stage.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Extraction of an algebraically independent `n`-tuple from one fixed exponential family. -/
def SchanuelExtractionFor {n : ℕ} (x : Fin n → ℂ) : Prop :=
  ∃ t : Fin n → ℂ, Function.Injective t ∧
    (∀ i, t i ∈ Set.range x ∪ Set.range (fun j => Complex.exp (x j))) ∧
    AlgebraicIndependent ℚ t

/-- The extraction form of Schanuel's conjecture at one fixed family size. -/
def SchanuelExtractionAt (n : ℕ) : Prop :=
  ∀ x : Fin n → ℂ, LinearIndependent ℚ x → SchanuelExtractionFor x

/-- The additive and exponential coordinates of one Schanuel family, with separate indices. -/
def schanuelExponentialGenerator {n : ℕ} (x : Fin n → ℂ) : Fin n ⊕ Fin n → ℂ
  | Sum.inl i => x i
  | Sum.inr i => Complex.exp (x i)

theorem range_schanuelExponentialGenerator {n : ℕ} (x : Fin n → ℂ) :
    Set.range (schanuelExponentialGenerator x) =
      Set.range x ∪ Set.range (fun i => Complex.exp (x i)) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | inl i => exact Or.inl ⟨i, rfl⟩
    | inr i => exact Or.inr ⟨i, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr i, rfl⟩

/-- Field generated over the algebraic numbers by one finite exponential family. -/
def schanuelExponentialValueField {n : ℕ} (x : Fin n → ℂ) :
    IntermediateField (algebraicClosure ℚ ℂ) ℂ :=
  IntermediateField.adjoin (algebraicClosure ℚ ℂ)
    (Set.range (schanuelExponentialGenerator x))

/-- Extraction from one exponential family is exactly the corresponding transcendence-degree
lower bound. -/
theorem schanuelExtractionFor_iff_cardinal_le_trdeg {n : ℕ} (x : Fin n → ℂ) :
    SchanuelExtractionFor x ↔
      (n : Cardinal) ≤
        Algebra.trdeg (algebraicClosure ℚ ℂ) (schanuelExponentialValueField x) := by
  classical
  constructor
  · rintro ⟨t, _, htmem, htind⟩
    let K := schanuelExponentialValueField x
    have htK : ∀ i, t i ∈ K := by
      intro i
      apply IntermediateField.subset_adjoin (algebraicClosure ℚ ℂ)
      rw [range_schanuelExponentialGenerator]
      exact htmem i
    let tK : Fin n → K := fun i => ⟨t i, htK i⟩
    letI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) :=
      algebraicClosure.isAlgebraic ℚ ℂ
    have htindBase : AlgebraicIndependent (algebraicClosure ℚ ℂ) t :=
      htind.extendScalars (algebraicClosure ℚ ℂ)
    have htindK : AlgebraicIndependent (algebraicClosure ℚ ℂ) tK := by
      apply AlgebraicIndependent.of_comp K.val
      simpa [tK, Function.comp_def] using htindBase
    simpa [Cardinal.mk_fin] using htindK.cardinalMk_le_trdeg
  · intro htrdeg
    obtain ⟨σ, hσ⟩ :=
      GaloisForLFunctions.HTGeometry.exists_algebraicIndependent_subfamily
        (schanuelExponentialGenerator x) htrdeg
    let t : Fin n → ℂ := fun i => schanuelExponentialGenerator x (σ i)
    have htind : AlgebraicIndependent ℚ t :=
      hσ.restrictScalars (algebraMap ℚ (algebraicClosure ℚ ℂ)).injective
    refine ⟨t, htind.injective, ?_, htind⟩
    intro i
    rw [← range_schanuelExponentialGenerator]
    exact Set.mem_range_self (σ i)

/-- Failure of extraction from one exponential family is exactly transcendence degree below the
family size. -/
theorem not_schanuelExtractionFor_iff_trdeg_lt {n : ℕ} (x : Fin n → ℂ) :
    (¬ SchanuelExtractionFor x) ↔
      Algebra.trdeg (algebraicClosure ℚ ℂ) (schanuelExponentialValueField x) <
        (n : Cardinal) := by
  simpa only [not_le] using
    not_congr (schanuelExtractionFor_iff_cardinal_le_trdeg x)

/-- The stagewise Schanuel interface is the universal transcendence-degree lower bound. -/
theorem schanuelExtractionAt_iff_forall_trdeg_ge (n : ℕ) :
    SchanuelExtractionAt n ↔
      ∀ x : Fin n → ℂ, LinearIndependent ℚ x →
        (n : Cardinal) ≤
          Algebra.trdeg (algebraicClosure ℚ ℂ) (schanuelExponentialValueField x) := by
  constructor
  · intro h x hx
    exact (schanuelExtractionFor_iff_cardinal_le_trdeg x).mp (h x hx)
  · intro h x hx
    exact (schanuelExtractionFor_iff_cardinal_le_trdeg x).mpr (h x hx)

/-- Failure of the stagewise Schanuel interface is witnessed by one rationally independent family
whose exponential value field has transcendence degree below the family size. -/
theorem not_schanuelExtractionAt_iff_exists_trdeg_lt (n : ℕ) :
    (¬ SchanuelExtractionAt n) ↔
      ∃ x : Fin n → ℂ, LinearIndependent ℚ x ∧
        Algebra.trdeg (algebraicClosure ℚ ℂ) (schanuelExponentialValueField x) <
          (n : Cardinal) := by
  classical
  constructor
  · intro h
    simp only [SchanuelExtractionAt, not_forall] at h
    obtain ⟨x, hx, hfail⟩ := h
    exact ⟨x, hx, (not_schanuelExtractionFor_iff_trdeg_lt x).mp hfail⟩
  · rintro ⟨x, hx, hlt⟩ hstage
    exact (not_schanuelExtractionFor_iff_trdeg_lt x).mpr hlt (hstage x hx)

/-- The interface is exactly the conjunction of its stages. -/
theorem schanuelConjecture_iff_forall_stage :
    SchanuelConjecture ↔ ∀ n, SchanuelExtractionAt n := by
  constructor
  · intro h n x hx
    exact h n x hx
  · intro h n x hx
    exact h n x hx

/-- Stage zero holds unconditionally. -/
theorem schanuelExtractionAt_zero : SchanuelExtractionAt 0 := by
  intro x _
  refine ⟨x, ?_, ?_, algebraicIndependent_empty_type⟩
  · intro a b _
    exact a.elim0
  · intro i
    exact i.elim0

/-- **Stage one is Hermite–Lindemann.**  The one-element stage of the extraction form holds exactly
when for every nonzero complex number either it or its exponential is transcendental over `ℚ`. -/
theorem schanuelExtractionAt_one_iff :
    SchanuelExtractionAt 1 ↔
      ∀ z : ℂ, z ≠ 0 → Transcendental ℚ z ∨ Transcendental ℚ (Complex.exp z) := by
  constructor
  · intro h z hz
    have hli : LinearIndependent ℚ (fun _ : Fin 1 => z) := by
      rw [linearIndependent_unique_iff]
      exact hz
    obtain ⟨t, _, hmem, hind⟩ := h _ hli
    have htrans : Transcendental ℚ (t 0) :=
      algebraicIndependent_unique_type_iff.mp hind
    rcases hmem 0 with hcase | hcase
    · obtain ⟨j, hj⟩ := hcase
      rw [← hj] at htrans
      exact Or.inl htrans
    · obtain ⟨j, hj⟩ := hcase
      rw [← hj] at htrans
      exact Or.inr htrans
  · intro h x hx
    have hx0 : x 0 ≠ 0 := by
      have := linearIndependent_unique_iff.mp hx
      simpa using this
    rcases h (x 0) hx0 with htrans | htrans
    · refine ⟨fun _ => x 0, ?_, ?_, ?_⟩
      · intro a b _
        exact Subsingleton.elim a b
      · intro i
        exact Or.inl ⟨0, rfl⟩
      · exact algebraicIndependent_unique_type_iff.mpr htrans
    · refine ⟨fun _ => Complex.exp (x 0), ?_, ?_, ?_⟩
      · intro a b _
        exact Subsingleton.elim a b
      · intro i
        exact Or.inr ⟨0, rfl⟩
      · exact algebraicIndependent_unique_type_iff.mpr htrans

/-- **Stage one holds unconditionally.**  This is Hermite–Lindemann, with the algebraic case
discharged by `exp_algebraic_transcendental`. -/
theorem schanuelExtractionAt_one : SchanuelExtractionAt 1 := by
  rw [schanuelExtractionAt_one_iff]
  intro z hz
  by_cases hzalg : IsAlgebraic ℤ z
  · exact Or.inr (exp_algebraic_transcendental hzalg hz)
  · left
    intro hzalgQ
    exact hzalg ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hzalgQ)

end

end GaloisForLFunctions.RHTower
