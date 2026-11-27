import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Observation.Center
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Mixed.Observation

/-! # A critical-line test from one unlabeled mixed-sector probability law -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Observation

open Finset Real _root_.HTGeometry
open FixedCount (State capacity pairCount)

variable {I J : Type*} [Fintype I] [Fintype J]

theorem heat_congr {E : I → ℝ} {F : J → ℝ} (h : Matches E F) (r : ℕ) :
    HeatTests E r ↔ HeatTests F r := by
  unfold HeatTests
  simp only [partition_congr h]

private theorem zero_contrast_iff (E : I → ℝ) (t : ℝ) :
    Mixed.contrast E 0 t=0 ↔ finiteGibbsPartition t E=finiteGibbsPartition (-t) E := by
  simp only [Mixed.contrast,zero_sub,partition_negative E,sub_eq_zero]
  rcases isEmpty_or_nonempty I with he | hn
  · letI := he
    simp only [finiteGibbsPartition,univ_eq_empty,sum_empty]
  · letI := hn
    constructor
    · intro h
      have eq := congrArg exp h
      simpa only [exp_log (finiteGibbsPartition_pos _ _)] using eq
    · exact congrArg log

theorem mixed_tests (A : I → ℝ) (k l r : ℕ) :
    HeatTests (Mixed.mixedEnergy A 0 k l) r ↔ k=l ∨ HeatTests A r := by
  have id (t : ℝ) : Mixed.contrast (Mixed.mixedEnergy A 0 k l) 0 t =
      ((k : ℝ)-l)*Mixed.contrast A 0 t := by
    simpa only [Mixed.pairedSum,mul_zero,sub_zero,add_zero] using Mixed.mixed_contrast A 0 k l 0 t
  constructor
  · intro h
    by_cases eq : k=l
    · exact Or.inl eq
    have hn : (k : ℝ)-(l : ℝ) ≠ 0 := sub_ne_zero.mpr fun he => eq (Nat.cast_injective (R := ℝ) he)
    refine Or.inr (fun j hj hjr => (zero_contrast_iff A _).mp ?_)
    have hz := (zero_contrast_iff _ _).mpr (h j hj hjr)
    rw [id] at hz
    exact (mul_eq_zero.mp hz).resolve_left hn
  · intro h j hj hjr
    apply (zero_contrast_iff _ _).mp
    rw [id]
    rcases h with rfl | ht
    · rw [sub_self,zero_mul]
    · rw [(zero_contrast_iff _ _).mpr (ht j hj hjr),mul_zero]

private theorem scaled_tests (E : I → ℝ) (t : ℝ) :
    HeatTests (fun i => t*centered E i) (cutoff (Fintype.card I)) ↔ t=0 ∨ Reflects E := by
  let A := fun i => t*centered E i
  have cz : centered A=A := centered_eq_of_sum_zero (by simp only [A,← mul_sum,sum_centered,mul_zero])
  change HeatTests A _ ↔ _
  rw [← cz,centered_heat_iff_reflects,reflects_iff_centered_pair A,cz,reflects_iff_centered_pair E]
  constructor
  · rintro ⟨R,h⟩
    by_cases hz : t=0
    · exact Or.inl hz
    refine Or.inr ⟨R,fun x => ?_⟩
    have hh := h x
    change t*centered E x + t*centered E (R x)=0 at hh
    rw [← mul_add] at hh
    exact (mul_eq_zero.mp hh).resolve_left hz
  · rintro (rfl | ⟨R,h⟩)
    · exact ⟨Equiv.refl _,fun x => by simp only [A,zero_mul,add_zero]⟩
    · refine ⟨R,fun x => ?_⟩
      change t*centered E x + t*centered E (R x)=0
      rw [← mul_add,h,mul_zero]

/-- At most four levels need only one opposite-temperature comparison. Away from
zero temperature, rescaling cannot introduce a reflection. -/
theorem small_single_test (E : I → ℝ) (t : ℝ) (size : Fintype.card I ≤ 4) :
    finiteGibbsPartition t (centered E)=finiteGibbsPartition (-t) (centered E) ↔ t=0 ∨ Reflects E := by
  constructor
  · intro eq
    apply (scaled_tests E t).mp
    intro j lo hi
    unfold cutoff at hi
    obtain rfl : j=1 := by omega
    simpa only [finiteGibbsPartition,Nat.cast_one,neg_neg,neg_one_mul,one_mul,neg_mul] using eq
  · rintro (rfl | symmetric)
    · rw [neg_zero]
    · have pair := (pairs_iff_matches _ _).mp ((reflects_iff_centered_pair E).mp symmetric)
      rw [partition_negative]
      simpa only [zero_sub] using partition_congr pair t

/-- The needed aperture is determined by one input sector even when the observed
spectrum consists of an exponentially larger collection of particles and holes. -/
theorem joint_half_test (E : I → ℝ) (C : ℝ) (k l : ℕ) (t : ℝ) :
    HeatTests (centered (information (finiteGibbsStateWeight t (Mixed.mixedEnergy E C k l))))
        (cutoff (Fintype.card I)) ↔ k=l ∨ t=0 ∨ Reflects E := by
  rw [centered_joint_information,mixed_tests,scaled_tests]

/-- Exact criterion using the centered negative logarithms of one physical output
distribution. All comparisons use positive and negative *integer* powers. -/
theorem single_law_iff {S : Finset Nat.Primes} (c : S → ℕ) (m k l : ℕ) (s : ℂ) :
    HeatTests (centered (information (Mixed.fillingShare c m (capacity c-m) k l s)))
        (cutoff (Fintype.card (State c m))) ↔
      k=l ∨ (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x) ∨
        capacity c < m ∨ (∑ i, pairCount c m i)=2*m := by
  by_cases hm : m ≤ capacity c
  · have hh := Mixed.filling_matches c (Nat.add_sub_of_le hm) k l
    have law : Mixed.fillingShare c m (capacity c-m) k l s =
        finiteGibbsStateWeight (2*s.re-1) (Mixed.fillingEnergy c m (capacity c-m) k l) :=
      funext (Mixed.filling_gibbs c m (capacity c-m) k l s)
    rw [law,← heat_congr (information_matches hh (2*s.re-1)),joint_half_test,split_isometric_iff,sector_reflection_iff]
    have mid : 2*s.re-1=0 ↔ s.re=1/2 := by constructor <;> intro h <;> linarith only [h]
    rw [mid]
  · have absent : IsEmpty (State c m) := ⟨fun x => hm ((FixedCount.feasible_iff c m).mp ⟨x⟩)⟩
    letI := absent
    refine ⟨fun _ => Or.inr (Or.inr (Or.inl (lt_of_not_ge hm))),fun _ j hj hr => ?_⟩
    simp only [Fintype.card_of_isEmpty,cutoff,Nat.zero_sub,Nat.zero_div] at hr
    omega

/-- With three or four one-copy states the whole critical-line test reduces to
one comparison on the observed composite law, at orders one and minus one. -/
theorem single_comparison {S : Finset Nat.Primes} (c : S → ℕ) (m k l : ℕ) (s : ℂ)
    (size : Fintype.card (State c m)=3 ∨ Fintype.card (State c m)=4) :
    let Y := centered (information (Mixed.fillingShare c m (capacity c-m) k l s))
    finiteGibbsPartition 1 Y = finiteGibbsPartition (-1) Y ↔
      k=l ∨ (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x) ∨
        capacity c < m ∨ (∑ i, pairCount c m i)=2*m := by
  dsimp only
  rw [← single_law_iff]
  have cut : cutoff (Fintype.card (State c m))=1 := by unfold cutoff; omega
  rw [cut]
  constructor
  · intro h j lo hi
    obtain rfl : j=1 := le_antisymm hi lo
    simpa only [Nat.cast_one] using h
  · intro h
    simpa only [Nat.cast_one] using h 1 le_rfl le_rfl

#print axioms small_single_test
#print axioms single_comparison
#print axioms mixed_tests
#print axioms joint_half_test
#print axioms single_law_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Observation
