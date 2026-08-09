import GaloisForLFunctions.HTGeometry.EscapeSubgroup
import GaloisForLFunctions.HTGeometry.EllipticMeroFieldDifferentialAlgebraicity

/-!
# The period quotient of a hypertranscendental meromorphic germ

The period group of a global meromorphic germ is
`Per(x) = {h : ℂ | x(· + h) = x}`.  In one complex variable a compact period quotient forces two
`ℝ`-independent periods, hence double periodicity, hence differential algebraicity.  Contrapositive:

* **`not_compactSpace_quotient_meroPeriodSubgroup`** — a hypertranscendental global meromorphic
  germ has noncompact period quotient.

The supporting subgroup fact is independent of the analysis:

* **`exists_rIndependent_of_compactSpace_quotient`** — a subgroup of `ℂ` with compact quotient
  contains two `ℝ`-independent elements, because otherwise it lies on one real line and the
  transverse coordinate descends to a continuous surjection onto `ℝ`.
-/

open Set Topology

namespace GaloisForLFunctions

/-! ## Subgroups of `ℂ` with compact quotient -/

/-- Two complex numbers that are not `ℝ`-independent, the first nonzero, are real multiples. -/
theorem exists_real_mul_of_not_linearIndependent {v p : ℂ} (hv : v ≠ 0)
    (h : ¬ LinearIndependent ℝ ![v, p]) : ∃ t : ℝ, p = (t : ℂ) * v := by
  by_contra hcon
  refine h (LinearIndependent.pair_iff.mpr ?_)
  intro s t hst
  rcases eq_or_ne t 0 with rfl | ht
  · refine ⟨?_, rfl⟩
    simp only [zero_smul, add_zero, Complex.real_smul] at hst
    rcases mul_eq_zero.mp hst with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 hv
  · exfalso
    refine hcon ⟨-s / t, ?_⟩
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    simp only [Complex.real_smul] at hst
    have hcast : ((-s / t : ℝ) : ℂ) = -(s : ℂ) / (t : ℂ) := by push_cast; ring
    rw [hcast]
    field_simp
    linear_combination hst

/-- **A subgroup of `ℂ` with compact quotient contains two `ℝ`-independent elements.** -/
theorem exists_rIndependent_of_compactSpace_quotient {P : AddSubgroup ℂ}
    (h : CompactSpace (ℂ ⧸ P)) :
    ∃ α β : ℂ, α ∈ P ∧ β ∈ P ∧ LinearIndependent ℝ ![α, β] := by
  by_contra hcon
  have hnone : ∀ α ∈ P, ∀ β ∈ P, ¬ LinearIndependent ℝ ![α, β] := by
    intro α hα β hβ hind
    exact hcon ⟨α, β, hα, hβ, hind⟩
  -- choose a direction containing the whole subgroup
  obtain ⟨v, hv, hline⟩ : ∃ v : ℂ, v ≠ 0 ∧ ∀ p ∈ P, ∃ t : ℝ, p = (t : ℂ) * v := by
    by_cases hex : ∃ p ∈ P, p ≠ 0
    · obtain ⟨w, hw, hw0⟩ := hex
      exact ⟨w, hw0, fun p hp => exists_real_mul_of_not_linearIndependent hw0 (hnone w hw p hp)⟩
    · refine ⟨1, one_ne_zero, fun p hp => ⟨0, ?_⟩⟩
      have : p = 0 := by
        by_contra hp0
        exact hex ⟨p, hp, hp0⟩
      simp [this]
  refine not_compactSpace_quotient_of_realSurjection
    (AddMonoidHom.mk' (fun z : ℂ => (z / v).im) ?_) ?_ ?_ ?_ h
  · intro a b
    rw [add_div, Complex.add_im]
  · exact Complex.continuous_im.comp (continuous_id.div_const v)
  · intro p hp
    obtain ⟨t, rfl⟩ := hline p hp
    show (((t : ℂ) * v) / v).im = 0
    rw [mul_div_assoc, div_self hv, mul_one]
    simp
  · intro r
    refine ⟨(r : ℂ) * Complex.I * v, ?_⟩
    show (((r : ℂ) * Complex.I * v) / v).im = r
    rw [mul_div_assoc, div_self hv, mul_one]
    simp

/-! ## The period group of a meromorphic germ -/

namespace HTGeometry

open Bottcher

noncomputable section

local instance meroPeriodDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance meroPeriodDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance meroPeriodRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

/-- The zero translation is the identity, since translations compose additively and each is
injective. -/
theorem addTranslationMeroEquiv_zero_self (x : meroField (Set.univ : Set ℂ)) :
    addTranslationMeroEquiv (0 : ℂ) x = x := by
  have h := addTranslationMeroEquiv_add (0 : ℂ) (0 : ℂ) x
  rw [add_zero] at h
  exact (addTranslationMeroEquiv (0 : ℂ)).injective h

/-- The period group of a global meromorphic germ. -/
def meroPeriodSubgroup (x : meroField (Set.univ : Set ℂ)) : AddSubgroup ℂ where
  carrier := {h : ℂ | addTranslationMeroEquiv h x = x}
  zero_mem' := addTranslationMeroEquiv_zero_self x
  add_mem' := by
    intro a b ha hb
    show addTranslationMeroEquiv (a + b) x = x
    rw [← addTranslationMeroEquiv_add]
    rw [show addTranslationMeroEquiv b x = x from hb]
    exact ha
  neg_mem' := by
    intro a ha
    show addTranslationMeroEquiv (-a) x = x
    have hax : addTranslationMeroEquiv a x = x := ha
    have hstep := congrArg (addTranslationMeroEquiv (-a)) hax
    rw [addTranslationMeroEquiv_add, neg_add_cancel, addTranslationMeroEquiv_zero_self] at hstep
    exact hstep.symm

theorem mem_meroPeriodSubgroup {x : meroField (Set.univ : Set ℂ)} {h : ℂ} :
    h ∈ meroPeriodSubgroup x ↔ addTranslationMeroEquiv h x = x := Iff.rfl

/-- **Noncompact period-quotient law in one complex variable.**  A hypertranscendental global
meromorphic germ has noncompact period quotient: a compact quotient would supply two
`ℝ`-independent periods, and a doubly periodic germ is differentially algebraic. -/
theorem not_compactSpace_quotient_meroPeriodSubgroup
    {x : meroField (Set.univ : Set ℂ)}
    (hx : HypertranscendentalOver (RatFunc ℂ) x) :
    ¬ CompactSpace (ℂ ⧸ meroPeriodSubgroup x) := by
  intro hcompact
  obtain ⟨α, β, hα, hβ, hindep⟩ := exists_rIndependent_of_compactSpace_quotient hcompact
  exact hx (differentialAlgebraicOver_of_translation_fixed hindep hα hβ)

end

end HTGeometry

end GaloisForLFunctions
