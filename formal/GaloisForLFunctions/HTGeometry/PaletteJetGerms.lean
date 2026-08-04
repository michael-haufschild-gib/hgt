import GaloisForLFunctions.HTGeometry.PaletteJetRelation
import GaloisForLFunctions.HTGeometry.HypertranscendentalJetGerms
import GaloisForLFunctions.HTGeometry.FamilyJetRelationPropagation

/-!
# A palette of exponential carriers has algebraically independent jet germs

The capacity theorems consume a palette: a finite family of germs whose jets are algebraically
independent over the constants.  Splitting one rationally independent frequency sequence into finitely
many infinite blocks produces such a palette, and the log-primes give it explicitly for every size.

A relation among the jet germs on a nonempty open set is a relation among the jets of the carriers
there; the carriers are entire, so the relation propagates to the whole plane, and along the real line
frequency separation kills it.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {ι : Type*} [DecidableEq ι] {n : ℕ} {a : ι → ℂ} {omega : ι → ℝ} {bidx : ι → Fin n}

omit [DecidableEq ι] in
/-- **A block of a normally summable family is normally summable.** -/
theorem expSeriesNormallySummable_blockAmp (ha : ExpSeriesNormallySummable a omega) (k : Fin n) :
    ExpSeriesNormallySummable (blockAmp a bidx k) omega := by
  intro R
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (ha R)
  · positivity
  · refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
    rw [blockAmp]
    by_cases h : bidx i = k
    · rw [if_pos h]
    · rw [if_neg h, norm_zero]
      positivity

/-- The germ of a block carrier on an open set. -/
def blockCarrierGerm (V : Set ℂ) {ι : Type*} {n : ℕ} {a : ι → ℂ} {bidx : ι → Fin n} {omega : ι → ℝ}
    (hb : ∀ k, ExpSeriesNormallySummable (blockAmp a bidx k) omega) (k : Fin n) :
    analyticGermSubringOn V :=
  ⟨((blockCarrier a bidx omega k : ℂ → ℂ) : Germ (𝓟 V) ℂ),
    ⟨blockCarrier a bidx omega k, fun z _ => analyticAt_cexpSeriesCarrier (hb k) z, rfl⟩⟩

/-- **The jet germs of a palette are algebraically independent over the constants.**  A relation among
them evaluates to a relation among the jets of the carriers on the open set, propagates to the whole
plane because the carriers are entire, and is killed on the real line by frequency separation. -/
theorem algebraicIndependent_paletteJetGerm {V : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty)
    (hom : RationallyIndependentSequence omega)
    (hb : ∀ k : Fin n, ExpSeriesNormallySummable (blockAmp a bidx k) omega)
    (hinf : ∀ k : Fin n, {y : ι | bidx y = k ∧ a y ≠ 0}.Infinite) :
    letI : Algebra ℂ (analyticGermSubringOn V) := (constGermHom V).toAlgebra
    AlgebraicIndependent ℂ fun q : Fin n × ℕ =>
      (dirSubringDeriv hVo (1 : ℂ))^[q.2] (blockCarrierGerm V hb q.1) := by
  letI : Algebra ℂ (analyticGermSubringOn V) := (constGermHom V).toAlgebra
  rw [algebraicIndependent_iff]
  intro Q hQ
  refine eq_zero_of_paletteJetRelation_vanishing hom hb hinf Q fun t => ?_
  have hA : ∀ (k : Fin n) (w : ℂ), AnalyticAt ℂ (blockCarrier a bidx omega k) w :=
    fun k w => analyticAt_cexpSeriesCarrier (hb k) w
  refine familyJetRelation_eq_zero_of_isOpen hA hVo hVne (fun z hz => ?_) (t : ℂ)
  have hQz := congrArg (analyticGermEval hz) hQ
  rw [map_zero, analyticGermEval_aeval hz] at hQz
  have hjet : (fun q : Fin n × ℕ =>
      analyticGermEval hz ((dirSubringDeriv hVo (1 : ℂ))^[q.2] (blockCarrierGerm V hb q.1)))
      = fun q : Fin n × ℕ => iteratedDeriv q.2 (blockCarrier a bidx omega q.1) z := by
    funext q
    exact analyticGermEval_iterate hVo hz rfl q.2
  rw [hjet] at hQz
  exact hQz

/-! ### An explicit palette of every size -/

/-- The block of a prime index in a palette of `n + 1` blocks. -/
def primeBlockIndex (n : ℕ) (j : ℕ) : Fin (n + 1) := ⟨j % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

theorem infinite_primeBlock (n : ℕ) (k : Fin (n + 1)) :
    {y : ℕ | primeBlockIndex n y = k ∧ logPrimeAmplitude y ≠ 0}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : ℕ => (k : ℕ) + t * (n + 1)) ?_ ?_
  · intro s t hst
    have hn : 0 < n + 1 := Nat.succ_pos n
    simp only [add_right_inj] at hst
    exact Nat.eq_of_mul_eq_mul_right hn hst
  · intro t
    refine ⟨Fin.ext ?_, logPrimeAmplitude_ne_zero _⟩
    show ((k : ℕ) + t * (n + 1)) % (n + 1) = (k : ℕ)
    rw [Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt k.isLt

theorem expSeriesNormallySummable_logPrimeBlock (n : ℕ) (k : Fin (n + 1)) :
    ExpSeriesNormallySummable
      (blockAmp logPrimeAmplitude (primeBlockIndex n) k) logPrimeFrequency :=
  expSeriesNormallySummable_blockAmp expSeriesNormallySummable_logPrime k

/-- **An explicit palette of every size: the jet germs of the `n + 1` log-prime block carriers are
algebraically independent over the constants, on every nonempty open set.** -/
theorem algebraicIndependent_jetGerm_logPrimePalette {V : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty)
    (n : ℕ) :
    letI : Algebra ℂ (analyticGermSubringOn V) := (constGermHom V).toAlgebra
    AlgebraicIndependent ℂ fun q : Fin (n + 1) × ℕ =>
      (dirSubringDeriv hVo (1 : ℂ))^[q.2]
        (blockCarrierGerm V (expSeriesNormallySummable_logPrimeBlock n) q.1) :=
  algebraicIndependent_paletteJetGerm hVo hVne rationallyIndependentSequence_logPrimeFrequency
    (expSeriesNormallySummable_logPrimeBlock n) (infinite_primeBlock n)

end

end GaloisForLFunctions.HTGeometry
