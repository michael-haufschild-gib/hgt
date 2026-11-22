import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.SingleReading
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.Divisor
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Topology.Compactness.Lindelof

/-!
# Single readings at complex inverse temperature

Different spectra have distinct analytic germs at one. Their meromorphic
continuations can agree only on a locally finite subset of the plane.
Countability of the clock times gives one exceptional set for all pairs.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open Set Filter DyadicAperture.Binary ZeroForcingCalculus

private theorem finite_order {t u : ExceptionalTime} (h : response t ≠ response u) (s : ℂ) :
    meromorphicOrderAt (response t-response u) s ≠ ⊤ := by
  have ha (v : ExceptionalTime) : AnalyticAt ℂ (response v) 1 :=
    response_regular v ⟨1,by norm_num⟩ (by norm_num)
  have hn : (response t-response u) 1 ≠ 0 := sub_ne_zero.mpr (fun he => h ((response_eq_iff_unit t u).mpr he))
  have hz : meromorphicOrderAt (response t-response u) 1 = 0 :=
    meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero ((ha t).sub (ha u)) hn
  have hm : MeromorphicOn (response t-response u) univ := fun z _ => (response_meromorphic t z).sub (response_meromorphic u z)
  exact hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 1) (mem_univ s) (hz ▸ WithTop.zero_ne_top)

private theorem separated {t u : ExceptionalTime} (h : response t ≠ response u) (K : Set ℂ) :
    {z | response t z ≠ response u z} ∈ codiscreteWithin K := by
  have hm : MeromorphicOn (response t-response u) K := fun z _ => (response_meromorphic t z).sub (response_meromorphic u z)
  have he := MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero hm (fun z _ => finite_order h z)
  exact he.mono fun z hz eq => hz (sub_eq_zero.mpr eq)

/-- Any two different spectra agree only finitely often on each compact set. -/
theorem coincidences_finite {t u : ExceptionalTime} (h : response t ≠ response u) (K : Set ℂ) (hK : IsCompact K) :
    {s ∈ K | response t s = response u s}.Finite := by
  change (K ∩ {s | response t s = response u s}).Finite
  simpa only [Set.sdiff_eq,Set.compl_setOf,not_not] using hK.finite_sdiff_of_mem_codiscreteWithin (separated h K)

private theorem coincidence_countable (t u : ExceptionalTime) :
    {s | response t ≠ response u ∧ response t s = response u s}.Countable := by
  by_cases h : response t = response u
  · simp [h]
  · have hcomp : {s | response t s = response u s}ᶜ ∈ codiscreteWithin univ := separated h univ
    have hd := isDiscrete_of_codiscreteWithin hcomp
    rw [inter_univ] at hd
    have hc := (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hd
    exact hc.mono fun _ hs => hs.2

def collisions : Set ℂ := {s | ∃ t u : ExceptionalTime, response t ≠ response u ∧ response t s = response u s}

theorem collisions_countable : collisions.Countable := by
  letI : Countable ExceptionalTime := exceptional_countable.to_subtype
  have hc := Set.countable_iUnion (fun t : ExceptionalTime => Set.countable_iUnion (coincidence_countable t))
  apply hc.mono
  rintro s ⟨t,u,hn,he⟩
  exact mem_iUnion.mpr ⟨t,mem_iUnion.mpr ⟨u,hn,he⟩⟩

theorem outside_collisions (s : {s : ℂ // s ∉ collisions}) (t u : ExceptionalTime) :
    response t s.val = response u s.val ↔ block t = block u ∧ windingOrder t = windingOrder u := by
  rw [← unit_trace_eq_iff,← response_eq_iff_unit]
  refine ⟨fun he => Classical.byContradiction fun hn => s.property ⟨t,u,hn,he⟩,fun h => congrFun h _⟩

#print axioms coincidences_finite
#print axioms collisions_countable
#print axioms outside_collisions

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
