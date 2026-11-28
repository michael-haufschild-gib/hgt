import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.Partition
import Mathlib.Algebra.Order.Floor.Ring

/-! # Dense near-resonances at a specified frequency resolution -/

open Finset Set
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A bounded band needs at most one more bin than its scaled width.
Two frequencies in the same bin have scaled detuning at most one. -/
theorem frequency_bins {α : Type*} (F : Finset α) (x : α → ℝ)
    (a b w : ℝ) (hw : 0≤w) (hx : ∀ S∈F, x S∈Icc a b) :
    ∃ j : α → Fin (⌊w*(b-a)⌋₊+1), ∀ S∈F, ∀ T∈F, j S=j T → |w*(x S-x T)|≤1 := by
  let m := ⌊w*(b-a)⌋₊
  let y (S : α) := w*(x S-a)
  let j (S : α) : Fin (m+1) := ⟨min ⌊y S⌋₊ m,(min_le_right ..).trans_lt (Nat.lt_succ_self m)⟩
  have hval (S) (hS : S∈F) : (j S).val=⌊y S⌋₊ := by
    exact min_eq_left (Nat.floor_mono (mul_le_mul_of_nonneg_left (sub_le_sub_right (hx S hS).2 a) hw))
  have hbin (S T : α) (hS : S∈F) (hT : T∈F) (hh : j S=j T) :
      |w*(x S-x T)|≤1 := by
    have hsame := congrArg Fin.val hh
    rw [hval S hS,hval T hT] at hsame
    have hfloor (U) (hU : U∈F) : (⌊y U⌋₊:ℝ)≤y U :=
      Nat.floor_le (mul_nonneg hw (sub_nonneg.mpr (hx U hU).1))
    have hlo := hfloor S hS
    have hhi := Nat.lt_floor_add_one (y S)
    rw [hsame] at hlo hhi
    rw [show w*(x S-x T)=y S-y T by dsimp only [y]; ring,abs_le]
    constructor <;> linarith only [hlo,hhi,hfloor T hT,Nat.lt_floor_add_one (y T)]
  exact ⟨j,fun S hS T hT => hbin S T hS hT⟩

/-- Count broad-support differences of size at most the inverse time
resolution. No arithmetic separation of the spectrum is assumed. -/
theorem detuning_count (F : Finset (Finset I)) (r : ℕ) (x : Finset I → ℝ)
    (a b w : ℝ) (hw : 0≤w) (hx : ∀ S∈F, x S∈Icc a b) :
    (F.card:ℝ)^2 ≤ ((⌊w*(b-a)⌋₊+1:ℕ):ℝ)*(
      (pairCount F r (fun S T => |w*(x S-x T)|≤1):ℝ)+F.card*(2^r*(3/2)^Fintype.card I)) := by
  obtain ⟨j,hj⟩ := frequency_bins F x a b w hw hx
  simpa only [Fintype.card_fin] using partition_floor F r j (fun S T => |w*(x S-x T)|≤1) hj

/-- The sum of $q$ levels in a symmetric band lies in its $q$-fold dilation. -/
theorem subset_mem_band (E : I → ℝ) {A : ℝ} (hE : ∀ i, |E i|≤A)
    {q : ℕ} {S : Finset I} (hS : S∈(univ : Finset I).powersetCard q) :
    (∑ i ∈ S, E i) ∈ Icc (-((q:ℝ)*A)) ((q:ℝ)*A) := by
  have hc := (mem_powersetCard.mp hS).2
  have hl := sum_le_sum (s:=S) (fun i _ => (abs_le.mp (hE i)).1)
  have hu := sum_le_sum (s:=S) (fun i _ => (abs_le.mp (hE i)).2)
  simpa only [Set.mem_Icc,sum_const,nsmul_eq_mul,hc,mul_neg] using And.intro hl hu

/-- Count close broad-support pairs of fixed-cardinality energy sums. -/
theorem subset_sum_count (E : I → ℝ) (A : ℝ) (r q : ℕ) (w : ℝ) (hw : 0≤w)
    (hE : ∀ i, |E i|≤A) :
    let F := (univ : Finset I).powersetCard q
    let x (S : Finset I) := ∑ i ∈ S, E i
    ((Fintype.card I).choose q:ℝ)^2 ≤ ((⌊w*(2*q*A)⌋₊+1:ℕ):ℝ)*(
      (pairCount F r (fun S T => |w*(x S-x T)|≤1):ℝ)+
      ((Fintype.card I).choose q:ℝ)*(2^r*(3/2)^Fintype.card I)) := by
  intro F x
  simpa only [F,card_powersetCard,card_univ,show (q:ℝ)*A- -(q*A)=2*q*A by ring] using
    detuning_count F r x (-(q*A)) (q*A) w hw (fun _ hs => subset_mem_band E hE hs)

#print axioms subset_sum_count
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances
