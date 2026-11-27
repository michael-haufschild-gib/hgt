import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Powers
import GaloisForLFunctions.HTGeometry.FiniteKMSPurityNormalization

/-! # Exact cancellation between an energy list and its particle–hole reflection -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Mixed

open Finset _root_.HTGeometry

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Difference of log heat traces at energies `E` and `d-E`. -/
def contrast (E : X → ℝ) (d t : ℝ) :=
  Real.log (finiteGibbsPartition t E) - Real.log (finiteGibbsPartition t (fun x => d-E x))

theorem zero_of_pair {E : X → ℝ} {d : ℝ} (h : PairsAt E d) (t : ℝ) : contrast E d t=0 := by
  rw [contrast,partition_congr ((pairs_iff_matches E d).mp h) t,sub_self]

theorem pair_iff_zero (E : X → ℝ) (d : ℝ) :
    PairsAt E d ↔ ∀ j ≤ Fintype.card X, contrast E d (j : ℝ)=0 := by
  refine ⟨fun h j _ => zero_of_pair h _,?_⟩
  intro h
  rcases isEmpty_or_nonempty X with he | hn
  · exact ⟨Equiv.refl _,fun x => (he.false x).elim⟩
  · letI := hn
    apply (pairs_iff_matches _ _).mpr
    apply (matches_iff_partitions _ _).mpr
    intro j hj
    have eq := congrArg Real.exp (sub_eq_zero.mp (h j hj))
    simpa only [Real.exp_log (finiteGibbsPartition_pos _ _)] using eq

omit [Fintype X] [Fintype Y] in
theorem tensor_pair {E : X → ℝ} {F : Y → ℝ} {a b : ℝ} (ha : PairsAt E a) (hb : PairsAt F b) :
    PairsAt (finiteTensorEnergy E F) (a+b) := by
  obtain ⟨e,he⟩ := ha
  obtain ⟨f,hf⟩ := hb
  refine ⟨e.prodCongr f,fun z => ?_⟩
  change (E z.1+F z.2)+(E (e z.1)+F (f z.2))=a+b
  linarith only [he z.1,hf z.2]

private theorem tensor_contrast [Nonempty X] [Nonempty Y] (E : X → ℝ) (F : Y → ℝ) (a b t : ℝ) :
    contrast (finiteTensorEnergy E F) (a+b) t = contrast E a t + contrast F b t := by
  have flip : (fun z => a+b-finiteTensorEnergy E F z) = finiteTensorEnergy (fun x => a-E x) (fun y => b-F y) := by
    funext z
    unfold finiteTensorEnergy
    ring
  simp only [contrast,flip,finiteGibbsPartition_tensor,Real.log_mul (finiteGibbsPartition_pos _ _).ne' (finiteGibbsPartition_pos _ _).ne']
  ring

private theorem shift_partition (E : X → ℝ) (a t : ℝ) :
    finiteGibbsPartition t (fun x => a+E x) = Real.exp (-t*a)*finiteGibbsPartition t E := by
  unfold finiteGibbsPartition
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [← Real.exp_add]
  congr 1
  ring

private theorem complement_contrast [Nonempty X] (E : X → ℝ) (C d t : ℝ) :
    contrast (fun x => C-E x) (2*C-d) t = -contrast E d t := by
  have h₁ : (fun x => C-E x) = fun x => (C-d)+(d-E x) := by funext x; ring
  have h₂ : (fun x => (2*C-d)-(C-E x)) = fun x => (C-d)+E x := by funext x; ring
  rw [contrast,contrast,h₂,h₁,shift_partition,shift_partition,
    Real.log_mul (Real.exp_pos _).ne' (finiteGibbsPartition_pos _ _).ne',
    Real.log_mul (Real.exp_pos _).ne' (finiteGibbsPartition_pos _ _).ne']
  ring

private theorem copy_contrast (E : X → ℝ) (k : ℕ) (d t : ℝ) :
    contrast (copyEnergy E k) ((k : ℝ)*d) t = (k : ℝ)*contrast E d t := by
  rw [contrast,← copy_sub,partition_copies,partition_copies,Real.log_pow,Real.log_pow,contrast,mul_sub]

def mixedEnergy {I : Type*} (E : I → ℝ) (C : ℝ) (k l : ℕ) :=
  finiteTensorEnergy (copyEnergy E k) (copyEnergy (fun x => C-E x) l)

def pairedSum (C : ℝ) (k l : ℕ) (d : ℝ) := (k : ℝ)*d+(l : ℝ)*(2*C-d)

/-- Particle copies contribute one unit and hole copies minus one unit to the log difference. -/
theorem mixed_contrast (E : X → ℝ) (C : ℝ) (k l : ℕ) (d t : ℝ) :
    contrast (mixedEnergy E C k l) (pairedSum C k l d) t = ((k : ℝ)-l)*contrast E d t := by
  rcases isEmpty_or_nonempty X with he | hn
  · have vac (F : X → ℝ) (r : ℝ) : PairsAt F r := ⟨Equiv.refl _,fun x => (he.false x).elim⟩
    have left := (pairs_copies_iff E k d).mpr (Or.inr (vac _ _))
    have right := (pairs_copies_iff (fun x => C-E x) l (2*C-d)).mpr (Or.inr (vac _ _))
    rw [mixedEnergy,pairedSum,zero_of_pair (tensor_pair left right),zero_of_pair (vac E d),mul_zero]
  · letI := hn
    rw [mixedEnergy,pairedSum,tensor_contrast,copy_contrast,copy_contrast,complement_contrast]
    ring

/-- At the indicated center, balanced replication cancels all spectral discrepancies.
Unequal replication preserves the single-copy pairing condition. -/
theorem mixed_pairs_iff (E : X → ℝ) (C : ℝ) (k l : ℕ) (d : ℝ) :
    PairsAt (mixedEnergy E C k l) (pairedSum C k l d) ↔ k=l ∨ PairsAt E d := by
  constructor
  · intro h
    by_cases eq : k=l
    · exact Or.inl eq
    have hn : (k : ℝ)-(l : ℝ) ≠ 0 := sub_ne_zero.mpr (fun h => eq (Nat.cast_injective (R := ℝ) h))
    refine Or.inr ((pair_iff_zero E d).mpr fun j _ => ?_)
    have hz := zero_of_pair h (j : ℝ)
    rw [mixed_contrast] at hz
    exact (mul_eq_zero.mp hz).resolve_left hn
  · intro h
    apply (pair_iff_zero _ _).mpr
    intro j _
    rw [mixed_contrast]
    rcases h with rfl | h
    · rw [sub_self,zero_mul]
    · rw [zero_of_pair h,mul_zero]

theorem mixed_reflects_iff (E : X → ℝ) (C : ℝ) (k l : ℕ) :
    Reflects (mixedEnergy E C k l) ↔ k=l ∨ Reflects E := by
  constructor
  · rintro ⟨L,h⟩
    by_cases eq : k=l
    · exact Or.inl eq
    have hn : (k : ℝ)-(l : ℝ) ≠ 0 := sub_ne_zero.mpr (fun h => eq (Nat.cast_injective (R := ℝ) h))
    let d := (L-2*(l : ℝ)*C)/((k : ℝ)-l)
    have center : pairedSum C k l d = L := by
      unfold pairedSum
      calc _ = ((k : ℝ)-l)*d+2*(l : ℝ)*C := by ring
           _ = L := by unfold d; field_simp [hn]; ring
    rw [← center] at h
    exact Or.inr ⟨d,((mixed_pairs_iff E C k l d).mp h).resolve_left eq⟩
  · rintro (eq | ⟨d,h⟩)
    · exact ⟨_,(mixed_pairs_iff E C k l 0).mpr (Or.inl eq)⟩
    · exact ⟨_,(mixed_pairs_iff E C k l d).mpr (Or.inr h)⟩

#print axioms pair_iff_zero
#print axioms mixed_contrast
#print axioms mixed_pairs_iff
#print axioms mixed_reflects_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Mixed
