import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Universal.Ratios

/-! # Universal two-order test on a single particle–hole probability law -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Universal

open Finset Real
open _root_.HTGeometry (finiteGibbsPartition finiteGibbsPartition_pos finiteGibbsStateWeight)

/-- Opposite real orders of the centered negative log probabilities of one outgoing law. -/
def passes (S : Finset Nat.Primes) (C : ℝ) (k l : ℕ) (s : ℂ) (u : ℝ) : Prop :=
  let E := labelEnergy (elementary (S := S))
  let Y := centered (Observation.information (finiteGibbsStateWeight (2*s.re-1) (Mixed.mixedEnergy E C k l)))
  finiteGibbsPartition u Y=finiteGibbsPartition (-u) Y

private theorem log_iff {I : Type*} [Fintype I] [Nonempty I] (E : I → ℝ) (u : ℝ) :
    finiteGibbsPartition u E=finiteGibbsPartition (-u) E ↔ Mixed.contrast E 0 u=0 := by
  simp only [Mixed.contrast,zero_sub,partition_negative E,sub_eq_zero]
  refine ⟨congrArg log,fun h => ?_⟩
  simpa only [exp_log (finiteGibbsPartition_pos _ _)] using congrArg exp h

theorem passes_iff (S : Finset Nat.Primes) (hs : 2<S.card) (C : ℝ) (k l : ℕ) (s : ℂ) (u : ℝ) :
    passes S C k l s u ↔ k=l ∨ Coincides (elementary (S := S)) (u*(2*s.re-1)) := by
  letI : Nonempty S := Finset.nonempty_coe_sort.mpr (Finset.card_pos.mp (by omega))
  let A := fun i => (2*s.re-1)*centered (labelEnergy (elementary (S := S))) i
  have mixed : Mixed.contrast (Mixed.mixedEnergy A 0 k l) 0 u=((k : ℝ)-l)*Mixed.contrast A 0 u := by
    simpa only [Mixed.pairedSum,mul_zero,sub_zero,add_zero] using Mixed.mixed_contrast A 0 k l 0 u
  dsimp only [passes]
  rw [Observation.centered_joint_information,log_iff,mixed,mul_eq_zero,sub_eq_zero,Nat.cast_inj,← log_iff]
  apply or_congr_right
  simp only [A,Coincides,finiteGibbsPartition,neg_neg,neg_mul,mul_assoc]

/-- A positive ratio works on every elementary packet and every ordered replication
exactly outside the exceptional set. Equal particle and hole counts cancel at every order. -/
theorem universal_law_iff {r : ℝ} (hr : 0<r) :
    (∀ (S : Finset Nat.Primes), 2<S.card → ∀ (C : ℝ) (k l : ℕ) (s : ℂ),
      (passes S C k l s 1 ∧ passes S C k l s r ↔
        k=l ∨ ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x)) ↔ r∉exceptional := by
  rw [← detects_iff hr]
  constructor
  · intro all S hs d
    let s : ℂ := ⟨(1+d)/2,0⟩
    have re : s.re=(1+d)/2 := rfl
    have damp : 2*s.re-1=d := by rw [re]; ring
    have line : s.re=1/2 ↔ d=0 := by rw [re]; constructor <;> intro h <;> linarith only [h]
    have h := all S hs 0 1 0 s
    simpa only [passes_iff S hs,one_mul,damp,one_ne_zero,false_or,split_isometric_iff,line] using h
  · intro all S hs C k l s
    rw [passes_iff S hs,passes_iff S hs,one_mul,← or_and_left,all S hs,split_isometric_iff]
    apply or_congr_right
    constructor <;> intro h <;> linarith only [h]

#print axioms passes_iff
#print axioms universal_law_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Universal
