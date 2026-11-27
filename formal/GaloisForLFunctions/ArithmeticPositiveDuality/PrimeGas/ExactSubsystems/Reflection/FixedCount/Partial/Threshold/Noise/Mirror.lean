import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Partial.Threshold.Noise.Optimal
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Partial.Threshold.Minimum

/-! # The noise denominator vanishes exactly on reflecting prime spectra -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold.Noise

open Finset GaloisForLFunctions.HTGeometry _root_.HTGeometry

variable {X : Type*} [Fintype X]

/-- A reflected sorted shape is equivalent to an actual permutation pairing all level energies. -/
theorem separation_zero_iff_pairing (E : X → ℝ) : separation E = 0 ↔
    ∃ R : Equiv.Perm X, ∃ d : ℝ, ∀ x, E x+E (R x)=d := by
  rw [zero_separation]
  constructor
  · intro equality
    let μ := (∑ i, coordinates E i)/(Fintype.card X : ℝ)
    let a := (Tuple.sort (centered (coordinates E))).trans (Fintype.equivFin X).symm
    let R := (a.symm.trans Fin.revPerm).trans a
    have val (i) : lowVector E i = E (a i)-μ := rfl
    refine ⟨R,2*μ,?_⟩
    intro x
    obtain ⟨i,rfl⟩ := a.surjective x
    have h := congrFun equality i
    change lowVector E i = -lowVector E i.rev at h
    rw [val,val] at h
    change E (a i)+E (a (Fin.rev (a.symm (a i)))) = 2*μ
    rw [a.symm_apply_apply]
    linarith only [h]
  · rintro ⟨R,d,h⟩
    have eqp : finiteGibbsStateWeight 1 E = finiteGibbsStateWeight (-1) E ∘ R :=
      funext ((permuted_gibbs_iff E R 1).mpr (Or.inr ⟨d,h⟩))
    have hh := congrArg rankedLog eqp
    rw [rankedLog_perm] at hh
    simpa only [ranked_positive E zero_le_one,ranked_negative E (show (-1:ℝ) ≤ 0 by norm_num),neg_neg,one_mul] using hh

variable {S : Finset Nat.Primes} (c : S → ℕ) (m : ℕ)

private theorem all_pairs (g u : State c m) (h : ∀ x : State c m, Inside g u x) :
    ∃ R : Equiv.Perm (State c m), ∀ x, energy (level x)+energy (level (R x)) = energy (level g)+energy (level u) := by
  let a : State c m ≃ Mirror g u := ⟨fun x => ⟨x,h x⟩,Subtype.val,fun _ => rfl,fun _ => rfl⟩
  exact ⟨(a.trans (reflection g u)).trans a.symm,fun x => reflected_energy g u (a x)⟩

/-- The explicit greedy list decides whether the optimal stable inverse exists. -/
theorem separation_zero_iff_empty :
    separation (fun x : State c m => energy (level x)) = 0 ↔ candidates c m = ∅ := by
  rw [separation_zero_iff_pairing,no_candidates_iff]
  by_cases hn : Nonempty (State c m)
  · obtain ⟨w⟩ := hn
    obtain ⟨g,u,_,_,lo,hi,ext⟩ := anchors w
    constructor
    · rintro ⟨R,d,h⟩
      have key : energy (level g)+energy (level u) = d := by
        linarith only [h g,h u,(ext (R g)).2,(ext (R u)).1]
      ext z
      constructor
      · rintro ⟨x,rfl⟩
        refine ⟨R x,?_⟩
        change -energy (level (R x))-baseline reversePrice c m = energy (level x)-baseline price c m
        linarith only [lo,hi,h x,key]
      · rintro ⟨x,rfl⟩
        refine ⟨R x,?_⟩
        change energy (level (R x))-baseline price c m = -energy (level x)-baseline reversePrice c m
        linarith only [lo,hi,h x,key]
    · intro he
      have allin (x : State c m) : Inside g u x := by
        have hmem : energy (level x)-baseline price c m ∈ lowerEdge c m := ⟨x,rfl⟩
        rw [he] at hmem
        obtain ⟨y,hy⟩ := hmem
        change -energy (level y)-baseline reversePrice c m = energy (level x)-baseline price c m at hy
        have hx : energy (level x)+energy (level y) = energy (level g)+energy (level u) := by linarith only [lo,hi,hy]
        intro i
        have hpair := (energy_pair_iff g u x y).mp hx i
        have hc := count_cap y i
        omega
      obtain ⟨R,hr⟩ := all_pairs c m g u allin
      exact ⟨R,_,hr⟩
  · constructor
    · intro _
      ext z
      constructor <;> rintro ⟨x,_⟩ <;> exact (hn ⟨x⟩).elim
    · intro _
      exact ⟨Equiv.refl _,0,fun x => (hn ⟨x⟩).elim⟩

theorem outgoing_estimate (h : (candidates c m).Nonempty) (s : ℂ) :
    estimate (fun x : State c m => energy (level x)) (rankedLog (fun x => outgoingShare s x)) = 2*s.re-1 := by
  have hn := fun he => h.ne_empty ((separation_zero_iff_empty c m).mp he)
  have hp : 0 < separation (fun x : State c m => energy (level x)) :=
    lt_of_le_of_ne (separation_nonneg _) (Ne.symm hn)
  simp_rw [outgoing_gibbs]
  exact exact_estimate _ hp _

/-- An exact estimator on all complex inputs with squared Lipschitz bound `K` exists
precisely when the greedy list is nonempty and the bound reaches the sharp threshold. -/
theorem outgoing_stability_iff (K : ℝ) :
    (∃ F : (Fin (Fintype.card (State c m)) → ℝ) → ℝ,
      (∀ s : ℂ, F (rankedLog (fun x : State c m => outgoingShare s x)) = 2*s.re-1) ∧
      ∀ v w, (F v-F w)^2 ≤ K*sqDistance v w) ↔
      (candidates c m).Nonempty ∧ 4 ≤ K*separation (fun x : State c m => energy (level x)) := by
  let E := fun x : State c m => energy (level x)
  have hp : 0 < separation E ↔ (candidates c m).Nonempty := by
    have hn := separation_nonneg E
    constructor
    · intro h
      exact Finset.nonempty_iff_ne_empty.mpr fun hempty => h.ne' ((separation_zero_iff_empty c m).mpr hempty)
    · intro h
      exact lt_of_le_of_ne hn (fun eq => h.ne_empty ((separation_zero_iff_empty c m).mp eq.symm))
  rw [← hp, ← stability_iff E K]
  constructor
  · rintro ⟨F,he,hb⟩
    refine ⟨F,fun t => ?_,hb⟩
    have h := he (((t+1)/2 : ℝ) : ℂ)
    simp_rw [outgoing_gibbs,Complex.ofReal_re] at h
    rwa [show 2*((t+1)/2)-1 = t by ring] at h
  · rintro ⟨F,he,hb⟩
    refine ⟨F,fun s => ?_,hb⟩
    simp_rw [outgoing_gibbs]
    exact he _

#print axioms outgoing_stability_iff
#print axioms separation_zero_iff_pairing
#print axioms separation_zero_iff_empty
#print axioms outgoing_estimate

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold.Noise
