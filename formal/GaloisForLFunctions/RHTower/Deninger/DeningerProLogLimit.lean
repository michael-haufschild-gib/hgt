import GaloisForLFunctions.RHTower.Deninger.DeningerLogGroupSequence
import GaloisForLFunctions.RHTower.Deninger.DeningerRationalDivisorSequence

/-!
# The pro-log limit of the finite stages

The finite divisorial log structures increase with the set of primes, and every rational unit lies
in one of them, because its divisor has finite support.  So the filtered union of the finite stages
is the whole group of rational units, which is what makes the colimit of the finite Kummer sequences
the divisor sequence of the rationals.

* `deningerLogGpSub_mono` : the finite stages increase with `P`.
* `deningerLogGpSub_exhaust` : every rational unit lies in a finite stage.
* `deningerClosedPt_disjoint` : distinct primes cut out disjoint divisors.
-/

namespace RHTower

open TopologicalSpace

/-- **Distinct primes cut out disjoint divisors on the arithmetic curve.** -/
theorem deningerClosedPt_disjoint {p q : Nat.Primes} (hpq : p ≠ q) :
    ({deningerClosedPt p} : Set deningerArithBase) ∩ {deningerClosedPt q} = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
    not_and]
  rintro rfl h
  exact hpq (deningerClosedPt_injective h)

/-- **The finite stages of the divisorial log structure increase with the set of primes.** -/
theorem deningerLogSub_mono {P P' : Finset Nat.Primes} (h : P ⊆ P')
    (U : Opens deningerArithBase) : deningerLogSub P U ≤ deningerLogSub P' U := by
  intro q hq p hp
  exact ⟨(hq p hp).1, fun hP' => (hq p hp).2 (fun hP => hP' (h hP))⟩

/-- **The finite stages of the groupified log structure increase with the set of primes.** -/
theorem deningerLogGpSub_mono {P P' : Finset Nat.Primes} (h : P ⊆ P')
    (U : Opens deningerArithBase) :
    (deningerLogGpAddCond P).sub U ≤ (deningerLogGpAddCond P').sub U := by
  rintro f ⟨hconst, hcond⟩
  exact ⟨hconst, fun x p hxp hP' => hcond x p hxp (fun hP => hP' (h hP))⟩

/-- **Every rational unit lies in a finite stage**: its divisor has finite support. -/
theorem deningerLogGpSub_exhaust (q : ℚˣ) (U : Opens deningerArithBase) :
    ∃ P : Finset Nat.Primes,
      (fun _ : ↥U => Additive.ofMul q) ∈ (deningerLogGpAddCond P).sub U := by
  classical
  refine ⟨(deningerDivisor q).support, ⟨fun _ _ => rfl, fun x p _ hP => ?_⟩⟩
  have h : deningerDivisor q p = 0 := by
    by_contra hne
    exact hP (Finsupp.mem_support_iff.2 hne)
  exact h

/-- **Every element of the divisorial log structure lies in a finite stage** as soon as it is
regular on the open set. -/
theorem deningerLogSub_exhaust (q : ℚˣ) (U : Opens deningerArithBase)
    (hreg : ∀ p : Nat.Primes, deningerClosedPt p ∈ U → 0 ≤ padicValRat ((p : ℕ)) ((q : ℚ))) :
    ∃ P : Finset Nat.Primes, q ∈ deningerLogSub P U := by
  classical
  refine ⟨(deningerDivisor q).support, fun p hp => ⟨hreg p hp, fun hP => ?_⟩⟩
  have h : deningerDivisor q p = 0 := by
    by_contra hne
    exact hP (Finsupp.mem_support_iff.2 hne)
  exact h

end RHTower
