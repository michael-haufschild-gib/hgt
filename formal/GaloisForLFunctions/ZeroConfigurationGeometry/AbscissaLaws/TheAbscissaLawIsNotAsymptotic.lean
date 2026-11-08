import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheAbscissaLawsOfAZeroConfiguration

/-!
# The abscissa law is not asymptotic

Call a property of zero configurations **asymptotic** (`IsAsymptotic`) when it depends only on the
zeros above some height: two configurations that agree, with multiplicities, at all heights
`|Im z| > T` for some `T` have it or not together. ZAL is asymptotic.

**Theorem** (`exists_not_abscissaLawAt_zero_of_isAsymptotic`). If an asymptotic property holds for
some pure configuration, it holds for a configuration that approaches the line and violates the
finite case of AAL (`h = 0`): add one reflection pair `{ρ, 1 − ρ̄}` off the line (`addPair`).

So no statement about the distribution of zeros at large height — densities, pair statistics, gaps,
growth of counts — decides the finite stratum (B13) or AAL: an input for them must see the zeros at
bounded height, i.e. the function itself.
-/

open Complex Set
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

open ArithmeticCastelnuovoSeveri

/-- **Asymptotic properties** depend only on the zeros above some height, with multiplicities. -/
def IsAsymptotic (P : ZeroConfig → Prop) : Prop :=
  ∀ Z Z' : ZeroConfig, (∃ T : ℝ, ∀ z : ℂ, T < |z.im| →
      (z ∈ Z.carrier ↔ z ∈ Z'.carrier) ∧ (z ∈ Z.carrier → Z.mult z = Z'.mult z)) → (P Z ↔ P Z')

theorem approachesLine_isAsymptotic : IsAsymptotic ApproachesLine := by
  -- symmetric, so one direction suffices
  suffices H : ∀ Z Z' : ZeroConfig, (∃ T : ℝ, ∀ z : ℂ, T < |z.im| →
      (z ∈ Z.carrier ↔ z ∈ Z'.carrier)) → ApproachesLine Z → ApproachesLine Z' by
    intro Z Z' hT
    obtain ⟨T, hT⟩ := hT
    exact ⟨H Z Z' ⟨T, fun z hz => (hT z hz).1⟩, H Z' Z ⟨T, fun z hz => (hT z hz).1.symm⟩⟩
  rintro Z Z' ⟨T, hT⟩ hZ h hh
  refine ((hZ h hh).union (finite_of_abs_im_le Z' T)).subset fun z ⟨hz, hre⟩ => ?_
  by_cases hzT : T < |z.im|
  · exact Or.inl ⟨(hT z hzT).mpr hz, hre⟩
  · exact Or.inr ⟨hz, not_lt.mp hzT⟩

open scoped Classical in
/-- Adding one reflection pair `{ρ, 1 − ρ̄}` absent from `Z`, with multiplicity one. -/
def addPair (Z : ZeroConfig) (ρ : ℂ) (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) (hρ : ρ ∉ Z.carrier)
    (hρ' : reflect ρ ∉ Z.carrier) : ZeroConfig where
  carrier := Z.carrier ∪ {ρ, reflect ρ}
  mult z := if z ∈ Z.carrier then Z.mult z else 1
  one_le_mult z _ := by
    split_ifs with h
    · exact Z.one_le_mult z h
    · exact le_rfl
  strip := by
    rintro z (hz | rfl | rfl)
    · exact Z.strip z hz
    · exact ⟨h0, h1⟩
    · rw [ArithmeticCastelnuovoSeveri.re_reflect]; exact ⟨by linarith, by linarith⟩
  reflect_mem := by
    rintro z (hz | rfl | rfl)
    · exact Or.inl (Z.reflect_mem z hz)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl (by simp [reflect]))
  mult_reflect := by
    rintro z (hz | rfl | rfl)
    · simp [hz, Z.reflect_mem z hz, Z.mult_reflect z hz]
    · simp [hρ, hρ']
    · have hrr : reflect (reflect ρ) = ρ := by simp [reflect]
      simp [hrr, hρ, hρ']
  finite_window T₁ T₂ := ((Z.finite_window T₁ T₂).union
    ((finite_singleton _).insert _)).subset fun z ⟨hz, hw⟩ => by
      rcases hz with hz | hz
      · exact Or.inl ⟨hz, hw⟩
      · exact Or.inr hz

/-- **One pair added to a pure configuration**: ZAL holds and the finite case of AAL fails. -/
theorem addPair_not_abscissaLawAt_zero {Z : ZeroConfig} (hP : Pure Z) {ρ : ℂ} (h0 : 0 ≤ ρ.re)
    (h12 : 1 / 2 < ρ.re) (h1 : ρ.re ≤ 1) :
    ∃ (hρ : ρ ∉ Z.carrier) (hρ' : reflect ρ ∉ Z.carrier),
      ApproachesLine (addPair Z ρ h0 h1 hρ hρ') ∧ ¬ AbscissaLawAt (addPair Z ρ h0 h1 hρ hρ') 0 := by
  have hρ : ρ ∉ Z.carrier := fun h => by have := hP ρ h; linarith
  have hρ' : reflect ρ ∉ Z.carrier := fun h => by
    have := hP _ h
    rw [ArithmeticCastelnuovoSeveri.re_reflect] at this
    linarith
  refine ⟨hρ, hρ', ?_⟩
  have hfin : ∀ h : ℝ, 0 ≤ h → (rightOf (addPair Z ρ h0 h1 hρ hρ') h).Finite := by
    intro h hh
    refine ((finite_singleton (reflect ρ)).insert ρ).subset fun z ⟨hz, hre⟩ => ?_
    rcases hz with hz | hz
    · have := hP z hz; linarith
    · exact hz
  refine ⟨fun h hh => hfin h hh.le, fun hA => ?_⟩
  have := hA (hfin 0 le_rfl) ρ (Or.inr (Or.inl rfl))
  linarith

/-- Adding a pair changes a configuration only at one height. -/
theorem addPair_agrees_above (Z : ZeroConfig) (ρ : ℂ) (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1)
    (hρ : ρ ∉ Z.carrier) (hρ' : reflect ρ ∉ Z.carrier) :
    ∀ z : ℂ, |ρ.im| < |z.im| →
      (z ∈ Z.carrier ↔ z ∈ (addPair Z ρ h0 h1 hρ hρ').carrier) ∧
        (z ∈ Z.carrier → Z.mult z = (addPair Z ρ h0 h1 hρ hρ').mult z) := by
  intro z hz
  have hne : z ≠ ρ := fun h => by rw [h] at hz; exact lt_irrefl _ hz
  have hne' : z ≠ reflect ρ := fun h => by
    rw [h] at hz
    have him : (reflect ρ).im = ρ.im := by simp [reflect]
    rw [him] at hz
    exact lt_irrefl _ hz
  constructor
  · constructor
    · exact fun h => Or.inl h
    · rintro (h | h | h)
      · exact h
      · exact absurd h hne
      · exact absurd h hne'
  · intro h
    simp [addPair, h]

/-- **No asymptotic property decides the finite stratum.** -/
theorem exists_not_abscissaLawAt_zero_of_isAsymptotic {P : ZeroConfig → Prop}
    (hP : IsAsymptotic P) {Z : ZeroConfig} (hZ : Pure Z) (hPZ : P Z) :
    ∃ Z' : ZeroConfig, P Z' ∧ ApproachesLine Z' ∧ ¬ AbscissaLawAt Z' 0 := by
  obtain ⟨hρ, hρ', hZAL, hnot⟩ := addPair_not_abscissaLawAt_zero hZ
    (ρ := (3 / 4 : ℂ)) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨_, (hP _ _ ⟨|(3 / 4 : ℂ).im|, addPair_agrees_above Z _ _ _ hρ hρ'⟩).mp hPZ, hZAL, hnot⟩

end GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
