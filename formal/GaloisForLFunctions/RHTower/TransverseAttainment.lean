import GaloisForLFunctions.RHTower.TransverseMaximumPrinciple

/-!
# Attainment: what is provable, and what the obstruction is

The maximum principle reduced the transverse-equilibrium chain to two inputs: the marginality
identity, and **attainment** of the supremum of the real part over the divisor.  This module records
exactly how far attainment can be pushed.

* On every **bounded** band of ordinates the supremum is attained, because the divisor is locally
  finite.  So failure of attainment is purely an escape-to-infinity phenomenon: a sequence of zeros
  whose real parts increase to the supremum while their ordinates diverge.
* If the **off-line set is finite**, attainment holds — and then the marginality identity gives the
  hypothesis outright.  Equivalently, the identity forces the hypothesis *or* infinitely many
  off-line zeros.

Attainment itself is **not proved here and is not provable by these means**.  Nothing in the zero-free
region or in the density theorems excludes a supremum approached only at infinity: the zero-free
bound tends to one as the ordinate grows, and the density bounds still permit infinitely many zeros
to the right of any fixed abscissa below the supremum.  This is the same attained/non-attained
dichotomy the ledger reached from single-base lag sampling and from window averaging; the present
chain arrives at it from a third direction.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- **Attainment holds on every bounded band of ordinates**, by local finiteness of the divisor. -/
theorem exists_max_re_in_band (t : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hne : {ρ : XiDivisorSupport | |(ρ : ℂ).im - t| ≤ r}.Nonempty) :
    ∃ ρ₀ ∈ {ρ : XiDivisorSupport | |(ρ : ℂ).im - t| ≤ r},
      ∀ ρ ∈ {ρ : XiDivisorSupport | |(ρ : ℂ).im - t| ≤ r}, (ρ : ℂ).re ≤ (ρ₀ : ℂ).re :=
  Set.exists_max_image _ _ (finite_xiDivisorSupport_band t hr) hne

/-- The off-line part of the divisor. -/
def offLineSupport : Set XiDivisorSupport := {ρ : XiDivisorSupport | (ρ : ℂ).re ≠ 1 / 2}

/-- If the off-line set is empty the hypothesis holds. -/
theorem riemannHypothesis_of_offLineSupport_empty (h : offLineSupport = ∅) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_re_eq (c := 1 / 2) fun ρ => ?_
  have hmem := Set.eq_empty_iff_forall_notMem.mp h ρ
  simpa only [offLineSupport, Set.mem_setOf_eq, not_not] using hmem

/-- **A finite off-line set forces attainment.**  The maximum over the off-line set lies strictly
right of the critical line, because the reflection keeps that set stable, so it dominates the
on-line points as well. -/
theorem exists_max_re_of_offLineSupport_finite
    (hfin : offLineSupport.Finite) (hne : offLineSupport.Nonempty) :
    ∃ ρ₀ : XiDivisorSupport, ∀ ρ : XiDivisorSupport, (ρ : ℂ).re ≤ (ρ₀ : ℂ).re := by
  obtain ⟨ρ₀, hρ₀mem, hρ₀max⟩ :=
    Set.exists_max_image _ (fun ρ : XiDivisorSupport => (ρ : ℂ).re) hfin hne
  refine ⟨ρ₀, ?_⟩
  have hgt : 1 / 2 < (ρ₀ : ℂ).re := by
    obtain ⟨ρ₁, hρ₁⟩ := hne
    have h1 : (ρ₁ : ℂ).re ≠ 1 / 2 := hρ₁
    rcases lt_or_gt_of_ne h1 with hlt | hgt1
    · have hp : supportPartner ρ₁ ∈ offLineSupport := by
        simp only [offLineSupport, Set.mem_setOf_eq, supportPartner_re]
        intro hc; linarith
      have hle := hρ₀max _ hp
      rw [supportPartner_re] at hle
      linarith
    · have hle := hρ₀max _ hρ₁
      linarith
  intro ρ
  by_cases hoff : (ρ : ℂ).re = 1 / 2
  · rw [hoff]; linarith
  · exact hρ₀max ρ hoff

/-- **The identity plus a finite off-line set gives the hypothesis.** -/
theorem riemannHypothesis_of_harmonic_of_offLineSupport_finite
    (hH : ∀ j : XiDivisorSupport, transverseForce j = 0)
    (hfin : offLineSupport.Finite) :
    RiemannHypothesis := by
  rcases Set.eq_empty_or_nonempty offLineSupport with hempty | hne
  · exact riemannHypothesis_of_offLineSupport_empty hempty
  · exact riemannHypothesis_of_transverseForce_zero_of_attained hH
      (exists_max_re_of_offLineSupport_finite hfin hne)

/-- **The dichotomy.**  The marginality identity forces either the hypothesis or infinitely many
off-line zeros.  Attainment is therefore only at issue when the off-line set is infinite. -/
theorem riemannHypothesis_or_offLineSupport_infinite_of_harmonic
    (hH : ∀ j : XiDivisorSupport, transverseForce j = 0) :
    RiemannHypothesis ∨ offLineSupport.Infinite := by
  by_cases hfin : offLineSupport.Finite
  · exact Or.inl (riemannHypothesis_of_harmonic_of_offLineSupport_finite hH hfin)
  · exact Or.inr hfin

end

end RHTower
