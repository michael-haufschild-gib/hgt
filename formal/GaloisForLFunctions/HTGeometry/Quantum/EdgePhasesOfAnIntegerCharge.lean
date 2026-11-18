import GaloisForLFunctions.HTGeometry.Quantum.AllCopyChargeGauge

/-!
# Recognizing a common circle character on an integer charge column

A Bézout combination gives the unique reference phase for a primitive
column. For a general column, a root of this reference restores its
content. Relations involving two entries suffice, with a uniform bound
on the absolute sum of their coefficients.
-/

noncomputable section
open Finset Matrix
open scoped Classical
namespace GaloisForLFunctions.HTGeometry.Quantum.TensorObservation
open CollectiveDiophantineGeometry.Simplex

variable {E : Type*} [Fintype E]

/-- Pairwise power identities characterize a single reference phase when
the charges have a Bézout dual. This holds for any number of entries. -/
theorem primitive_reference (v c : E → ℤ) (hc : c ⬝ᵥ v=1) (φ : E → Circle) :
    (∀ i j, (φ i)^(v j)=(φ j)^(v i)) ↔ ∃! T : Circle, ∀ i, φ i=T^(v i) := by
  constructor
  · intro h
    let T := ∏ j, (φ j)^(c j)
    have product (t : Circle) : (∏ j, (t^(v j))^(c j))=t := by
      rw [← product_character]
      change t^(c ⬝ᵥ v)=t
      rw [hc,zpow_one]
    refine ⟨T,fun i => ?_,fun t ht => ?_⟩
    · calc
        φ i = ∏ j, (((φ i)^(v j))^(c j)) := (product _).symm
        _ = ∏ j, ((φ j)^(c j))^(v i) := by
          apply prod_congr rfl
          intro j _
          rw [h i j,← zpow_mul,← zpow_mul,mul_comm]
        _ = T^(v i) := prod_zpow ..
    · change t=∏ j, (φ j)^(c j)
      simpa only [ht] using (product t).symm
  · rintro ⟨T,hT,_⟩ i j
    rw [hT,hT,← zpow_mul,← zpow_mul,mul_comm]

/-- Tests of balanced signed pairs whose total number of entries is at most N. -/
def pairTests (q : E → ℤ) (φ : E → Circle) (N : ℕ) : Prop :=
  ∀ i j a b, a*q i+b*q j=0 → a.natAbs+b.natAbs≤N → (φ i)^a*(φ j)^b=1

/-- Unequal normalized magnitudes add to at most 2Q−1. Equal magnitudes
give the primitive relation (1,1) or (1,−1). -/
private theorem tested_powers (v : E → ℤ) (φ : E → Circle) (Q : ℕ)
    (hQ : ∀ i, (v i).natAbs≤Q) (tests : pairTests v φ (max 2 (2*Q-1))) (i j : E) :
    (φ i)^(v j)=(φ j)^(v i) := by
  by_cases h : (v i).natAbs=(v j).natAbs
  · have he : |v i|=|v j| := by simpa using congrArg (fun n : ℕ => (n : ℤ)) h
    rcases abs_eq_abs.mp he with he | he
    · have hg := tests i j 1 (-1) (by rw [he]; ring)
        (by simpa using le_max_left 2 (2*Q-1))
      have hs : φ i=φ j := by
        simpa only [zpow_one,zpow_neg_one,← div_eq_mul_inv,div_eq_one] using hg
      rw [he,hs]
    · have hg := tests i j 1 1 (by rw [he]; ring)
        (by simpa using le_max_left 2 (2*Q-1))
      have hm : φ i*φ j=1 := by simpa only [zpow_one] using hg
      have hs : φ i=(φ j)⁻¹ := by
        calc φ i = φ i*(φ j*(φ j)⁻¹) := by simp
             _ = (φ j)⁻¹ := by rw [← mul_assoc,hm,one_mul]
      rw [he,hs,inv_zpow,zpow_neg]
  · have bound : (v j).natAbs+(-(v i)).natAbs≤max 2 (2*Q-1) := by
      rw [Int.natAbs_neg]
      have := hQ i
      have := hQ j
      omega
    have hv := tests i j (v j) (-(v i)) (by ring) bound
    simpa only [zpow_neg,← div_eq_mul_inv,div_eq_one] using hv

/-- Bounded two-entry relations characterize arbitrary compatible edge
phases. The zero column requires the identity at every entry. -/
theorem finite_pair_iff (q : E → ℤ) (φ : E → Circle) (Q : ℕ)
    (hQ : ∀ i, (q i/content q).natAbs≤Q) :
    pairTests q φ (max 2 (2*Q-1)) ↔ ∃ t : Circle, ∀ i, φ i=t^(q i) := by
  classical
  constructor
  · intro test
    by_cases hz : q=0
    · refine ⟨1,fun i => ?_⟩
      have hg := test i i 1 0 (by simp [hz]) (by change 1≤max (2 : ℕ) (2*Q-1); omega)
      simpa only [zpow_one,zpow_zero,mul_one,one_zpow] using hg
    obtain ⟨v,c,hv,hc⟩ := primitive_direction q hz
    have g₀ : content q≠0 := fun he => hz (by simpa only [he,zero_smul] using hv)
    have eqn (i : E) : q i=content q*v i := congrFun hv i
    have hQ' (i : E) : (v i).natAbs≤Q := by
      have h := hQ i
      rw [eqn i,mul_comm (content q),Int.mul_ediv_cancel _ g₀] at h
      exact h
    have test' : pairTests v φ (max 2 (2*Q-1)) := by
      intro i j a b he hn
      exact test i j a b (by rw [eqn,eqn]; linear_combination (content q)*he) hn
    obtain ⟨T,hT,_⟩ := (primitive_reference v c hc φ).1 (tested_powers v φ Q hQ' test')
    obtain ⟨t,ht⟩ := circle_root _ g₀ T
    exact ⟨t,fun i => by rw [hT,eqn,zpow_mul,ht]⟩
  · rintro ⟨t,ht⟩ i j a b he _
    rw [ht,ht,← zpow_mul,← zpow_mul,← zpow_add,mul_comm (q i),mul_comm (q j),he,zpow_zero]

end GaloisForLFunctions.HTGeometry.Quantum.TensorObservation

#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.primitive_reference
#print axioms GaloisForLFunctions.HTGeometry.Quantum.TensorObservation.finite_pair_iff
