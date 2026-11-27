import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Spectrum

/-! # The maximal reflected part of a bounded prime occupation sector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial

open Finset

variable {S : Finset Nat.Primes} {c : S → ℕ} {m : ℕ}

private theorem energy_inj : Function.Injective energy := by
  intro a b h
  apply PNat.coe_injective
  have he := congrArg Real.exp h
  simp only [energy,Real.exp_log (Nat.cast_pos.mpr a.pos),Real.exp_log (Nat.cast_pos.mpr b.pos)] at he
  exact_mod_cast he

/-- A common sum of energies determines every paired occupation number. -/
theorem energy_pair_iff (g u x y : State c m) :
    energy (level x)+energy (level y) = energy (level g)+energy (level u) ↔
    ∀ i, count x i+count y i = count g i+count u i := by
  rw [← energy_mul,← energy_mul,energy_inj.eq_iff]
  change integerLabel S (count x)*integerLabel S (count y) = integerLabel S (count g)*integerLabel S (count u) ↔ _
  rw [← integerLabel_add,← integerLabel_add,(integerLabel_injective S).eq_iff]
  exact funext_iff

/-- The partner with the required coordinate sums respects all occupation caps. -/
def Inside (g u x : State c m) : Prop := ∀ i,
  count x i ≤ count g i+count u i ∧ count g i+count u i ≤ count x i+c i

theorem inside_intervals (g u x : State c m) : Inside g u x ↔ ∀ i,
    count g i+count u i-c i ≤ count x i ∧ count x i ≤ min (c i) (count g i+count u i) := by
  constructor
  · intro h i
    obtain ⟨hl,hu⟩ := h i
    exact ⟨by omega,le_min (count_cap x i) hl⟩
  · intro h i
    obtain ⟨lo,hi⟩ := h i
    exact ⟨hi.trans (min_le_right _ _),by omega⟩

abbrev Mirror (g u : State c m) := {x : State c m // Inside g u x}

private def partner (g u : State c m) (x : Mirror g u) : State c m :=
  ⟨fun i => ⟨count g i+count u i-count x.val i,by
    have h := x.property i
    omega⟩,by
    change (∑ i, (count g i+count u i-count x.val i)) = m
    rw [sum_tsub_distrib _ (fun i _ => (x.property i).1),sum_add_distrib,count_sum,count_sum,count_sum]
    omega⟩

private theorem partner_counts (g u : State c m) (x : Mirror g u) (i : S) :
    count x.val i + count (partner g u x) i = count g i+count u i := by
  change count x.val i+(count g i+count u i-count x.val i)=_
  have h := x.property i
  omega

private def image (g u : State c m) (x : Mirror g u) : Mirror g u :=
  ⟨partner g u x, fun i => by
    have h := partner_counts g u x i
    have hc := count_cap x.val i
    omega⟩

/-- The energy mirror restricts to an involutive permutation of the feasible intersection. -/
def reflection (g u : State c m) : Equiv.Perm (Mirror g u) :=
  let inv : Function.Involutive (image g u) := fun x => by
    apply Subtype.ext
    apply state_ext
    intro i
    have h := partner_counts g u x i
    have h' := partner_counts g u (image g u x) i
    change count x.val i+count (image g u x).val i = _ at h
    change count (image g u x).val i+count (image g u (image g u x)).val i = _ at h'
    omega
  ⟨image g u,image g u,inv,inv⟩

theorem reflected_energy (g u : State c m) (x : Mirror g u) :
    energy (level x.val)+energy (level (reflection g u x).val) = energy (level g)+energy (level u) :=
  (energy_pair_iff _ _ _ _).mpr (partner_counts g u x)

private theorem inside_of_pair (g u x y : State c m) (h : energy (level x)+energy (level y) =
    energy (level g)+energy (level u)) : Inside g u x := by
  intro i
  have hp := (energy_pair_iff g u x y).mp h i
  have hc := count_cap y i
  omega

/-- An occupation in the box has exactly one energy partner in the entire original sector. -/
theorem unique_partner_iff (g u x : State c m) :
    (∃! y : State c m, energy (level x)+energy (level y) = energy (level g)+energy (level u)) ↔ Inside g u x := by
  constructor
  · rintro ⟨y,hy,_⟩
    exact inside_of_pair g u x y hy
  · intro hx
    let z : Mirror g u := ⟨x,hx⟩
    refine ⟨(reflection g u z).val,reflected_energy g u z,?_⟩
    intro y hy
    exact state_ext fun i => Nat.add_left_cancel (((energy_pair_iff g u x y).mp hy i).trans
      (partner_counts g u z i).symm)

/-- Every family carrying a reflection with the same energy sum lies in this mirror. -/
theorem maximal (g u : State c m) (A : Set (State c m))
    (closed : ∀ x ∈ A, ∃ y ∈ A, energy (level x)+energy (level y) = energy (level g)+energy (level u)) :
    A ⊆ {x | Inside g u x} := by
  intro x hx
  obtain ⟨y,_,hy⟩ := closed x hx
  exact inside_of_pair g u x y hy

/-- Exact shared energy offsets for any two anchors, including the lower and upper extremes. -/
theorem shared_offsets (g u : State c m) :
    Set.range (fun x : State c m => energy (level x)-energy (level g)) ∩
      Set.range (fun y : State c m => energy (level u)-energy (level y)) =
    Set.range (fun x : Mirror g u => energy (level x.val)-energy (level g)) := by
  ext z
  constructor
  · rintro ⟨⟨x,rfl⟩,⟨y,hy⟩⟩
    change energy (level u)-energy (level y) = energy (level x)-energy (level g) at hy
    exact ⟨⟨x,inside_of_pair g u x y (by linarith only [hy])⟩,rfl⟩
  · rintro ⟨x,rfl⟩
    refine ⟨⟨x.val,rfl⟩,⟨(reflection g u x).val,?_⟩⟩
    linarith only [reflected_energy g u x]

#print axioms energy_pair_iff
#print axioms inside_intervals
#print axioms reflected_energy
#print axioms unique_partner_iff
#print axioms maximal
#print axioms shared_offsets

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial
