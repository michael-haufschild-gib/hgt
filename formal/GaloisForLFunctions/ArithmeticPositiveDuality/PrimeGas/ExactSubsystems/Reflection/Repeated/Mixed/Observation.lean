import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Mixed.Holes

/-! # Reflected outgoing probabilities for mixed particle and hole ensembles -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Mixed

open Finset _root_.HTGeometry
open FixedCount (State capacity pairCount)
open scoped ComplexConjugate

variable {X : Type*} [Fintype X]

theorem copy_gibbs (E : X → ℝ) (k : ℕ) (t : ℝ) (x : Fin k → X) :
    finiteGibbsStateWeight t (copyEnergy E k) x = copyWeight (finiteGibbsStateWeight t E) k x := by
  simp only [finiteGibbsStateWeight,partition_copies,copyEnergy,copyWeight,mul_sum,Real.exp_sum,
    prod_div_distrib,prod_const,card_univ,Fintype.card_fin]

variable {S : Finset Nat.Primes} (c : S → ℕ)

private theorem contrast_congr {I J : Type*} [Fintype I] [Fintype J] {E : I → ℝ} {F : J → ℝ}
    (h : Matches E F) (d t : ℝ) : contrast E d t = contrast F d t := by
  obtain ⟨e,he⟩ := h
  have flip : Matches (fun x => d-E x) (fun y => d-F y) := ⟨e,fun x => congrArg (d-·) (he x)⟩
  rw [contrast,contrast,partition_congr (show Matches E F from ⟨e,he⟩) t,partition_congr flip t]

/-- The measured log heat-trace contrast on complementary fillings is proportional to
the signed excess of particle copies, at every real inverse temperature. -/
theorem filling_log_imbalance {m n : ℕ} (h : m+n=capacity c) (k l : ℕ) (d t : ℝ) :
    contrast (fillingEnergy c m n k l) (pairedSum (fullEnergy c) k l d) t =
      ((k : ℝ)-l)*contrast (sectorEnergy c m) d t := by
  rw [← contrast_congr (filling_matches c h k l),mixed_contrast]

def fillingShare (m n k l : ℕ) (s : ℂ) (z : (Fin k → State c m) × (Fin l → State c n)) :=
  copyWeight (share c m s) k z.1 * copyWeight (share c n s) l z.2

theorem filling_gibbs (m n k l : ℕ) (s : ℂ) (z : (Fin k → State c m) × (Fin l → State c n)) :
    fillingShare c m n k l s z = finiteGibbsStateWeight (2*s.re-1) (fillingEnergy c m n k l) z := by
  letI : Nonempty (Fin k → State c m) := ⟨z.1⟩
  letI : Nonempty (Fin l → State c n) := ⟨z.2⟩
  unfold fillingShare fillingEnergy
  rw [finiteGibbsStateWeight_tensor,copy_gibbs,copy_gibbs]
  have law (a : ℕ) : share c a s = finiteGibbsStateWeight (2*s.re-1) (sectorEnergy c a) :=
    funext (FixedCount.outgoing_gibbs s)
  rw [law m,law n]

/-- For the physical product probabilities at reflected complex parameters, balance
is exactly the extra ambiguity introduced by mixing particles with their vacancies. -/
theorem filling_outgoing_iff (m k l : ℕ) (s : ℂ) :
    Matches (fillingShare c m (capacity c-m) k l s) (fillingShare c m (capacity c-m) k l (1-conj s)) ↔
      (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ∨ k=l ∨ capacity c < m ∨
        (∑ i, pairCount c m i)=2*m := by
  rw [split_isometric_iff,← filling_reflection_iff]
  let E := fillingEnergy c m (capacity c-m) k l
  have flip : 2*(1-conj s).re-1 = -(2*s.re-1) := by
    rw [Complex.sub_re,Complex.one_re,Complex.conj_re]; ring
  have mid : 2*s.re-1=0 ↔ s.re=1/2 := by constructor <;> intro h <;> linarith only [h]
  have fixed (R : Equiv.Perm ((Fin k → State c m) × (Fin l → State c (capacity c-m)))) :
      (∀ x, fillingShare c m (capacity c-m) k l s x = fillingShare c m (capacity c-m) k l (1-conj s) (R x)) ↔
      s.re=1/2 ∨ ∃ L, ∀ x, E x+E (R x)=L := by
    simp only [filling_gibbs,flip,FixedCount.permuted_gibbs_iff,mid,E]
  constructor
  · rintro ⟨R,hh⟩
    rcases (fixed R).mp hh with line | ⟨d,hd⟩
    · exact Or.inl line
    · exact Or.inr ⟨d,R,hd⟩
  · rintro (line | ⟨d,R,hd⟩)
    · exact ⟨Equiv.refl _,(fixed _).mpr (Or.inl line)⟩
    · exact ⟨R,(fixed _).mpr (Or.inr ⟨d,hd⟩)⟩

#print axioms filling_log_imbalance
#print axioms copy_gibbs
#print axioms filling_gibbs
#print axioms filling_outgoing_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Mixed
