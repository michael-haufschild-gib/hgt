import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Moments

/-! # Recovery of a finite spectrum from an identical tensor power -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated

open Finset
open _root_.HTGeometry (finiteGibbsPartition)

variable {X Y : Type*} [Fintype X] [Fintype Y]

def copyEnergy {I : Type*} (E : I → ℝ) (k : ℕ) (x : Fin k → I) := ∑ i, E (x i)

def copyWeight {I : Type*} (P : I → ℝ) (k : ℕ) (x : Fin k → I) := ∏ i, P (x i)

/-- Every moment counts ordered tuples separately, even when their weights coincide. -/
theorem moment_copies (P : X → ℝ) (k j : ℕ) : moment (copyWeight P k) j = (moment P j)^k := by
  simp only [moment,copyWeight,← prod_pow]
  rw [← Fintype.prod_sum (fun (_ : Fin k) (x : X) => P x^j),prod_const,card_univ,Fintype.card_fin]

theorem partition_copies (E : X → ℝ) (k : ℕ) (t : ℝ) :
    finiteGibbsPartition t (copyEnergy E k) = (finiteGibbsPartition t E)^k := by
  simp only [finiteGibbsPartition,copyEnergy,mul_sum,Real.exp_sum]
  rw [← Fintype.prod_sum (fun (_ : Fin k) (x : X) => Real.exp (-t * E x)),prod_const,card_univ,Fintype.card_fin]

theorem partition_congr {E : X → ℝ} {F : Y → ℝ} (h : Matches E F) (t : ℝ) :
    finiteGibbsPartition t E = finiteGibbsPartition t F := by
  obtain ⟨e,he⟩ := h
  exact Fintype.sum_equiv e _ _ fun x => congrArg (fun u => Real.exp (-t*u)) (he x)

theorem partition_nonneg (E : X → ℝ) (t : ℝ) : 0 ≤ finiteGibbsPartition t E :=
  sum_nonneg fun _ _ => (Real.exp_pos _).le

/-- Every positive tensor power determines its single-copy spectrum with multiplicities. -/
theorem copy_matches_iff (E : X → ℝ) (F : Y → ℝ) (k : ℕ) :
    Matches (copyEnergy E k) (copyEnergy F k) ↔ k=0 ∨ Matches E F := by
  constructor
  · intro h
    by_cases hk : k=0
    · exact Or.inl hk
    right
    apply (matches_iff_partitions E F).mpr
    intro j _
    have eq := partition_congr h (j : ℝ)
    rw [partition_copies,partition_copies] at eq
    exact (pow_left_inj₀ (partition_nonneg _ _) (partition_nonneg _ _) hk).mp eq
  · intro h
    apply (matches_iff_partitions _ _).mpr
    intro j _
    rw [partition_copies,partition_copies]
    rcases h with rfl | h
    · rw [pow_zero,pow_zero]
    · rw [partition_congr h]

def PairsAt {I : Type*} (E : I → ℝ) (L : ℝ) := ∃ R : Equiv.Perm I, ∀ x, E x+E (R x)=L

def Reflects {I : Type*} (E : I → ℝ) := ∃ L, PairsAt E L

omit [Fintype X] in
theorem pairs_iff_matches (E : X → ℝ) (L : ℝ) :
    PairsAt E L ↔ Matches E (fun x => L-E x) := by
  constructor <;> rintro ⟨e,he⟩ <;> exact ⟨e,fun x => by linarith only [he x]⟩

omit [Fintype X] in
theorem copy_sub (E : X → ℝ) (k : ℕ) (d : ℝ) :
    copyEnergy (fun x => d-E x) k = fun x => (k : ℝ)*d-copyEnergy E k x := by
  funext x
  simp only [copyEnergy,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem pairs_copies_iff (E : X → ℝ) (k : ℕ) (d : ℝ) :
    PairsAt (copyEnergy E k) ((k : ℝ)*d) ↔ k=0 ∨ PairsAt E d := by
  rw [pairs_iff_matches,← copy_sub,copy_matches_iff,pairs_iff_matches]

/-- A reflection of a composite can permute all tuples arbitrarily. Its existence still
implies a one-copy reflection whenever at least one copy is present. -/
theorem reflects_copies_iff (E : X → ℝ) (k : ℕ) :
    Reflects (copyEnergy E k) ↔ k=0 ∨ Reflects E := by
  constructor
  · rintro ⟨L,h⟩
    by_cases hk : k=0
    · exact Or.inl hk
    have hn : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have hs : (k : ℝ)*(L/k)=L := by field_simp
    rw [← hs] at h
    exact Or.inr ⟨_,((pairs_copies_iff E k _).mp h).resolve_left hk⟩
  · rintro (hk | ⟨d,h⟩)
    · exact ⟨_,(pairs_copies_iff E k 0).mpr (Or.inl hk)⟩
    · exact ⟨_,(pairs_copies_iff E k d).mpr (Or.inr h)⟩

#print axioms moment_copies
#print axioms partition_copies
#print axioms copy_matches_iff
#print axioms pairs_copies_iff
#print axioms reflects_copies_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated
