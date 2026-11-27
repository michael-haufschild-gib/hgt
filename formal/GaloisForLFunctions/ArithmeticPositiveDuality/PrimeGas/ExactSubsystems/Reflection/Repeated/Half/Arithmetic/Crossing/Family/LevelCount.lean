import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Spectrum

/-! # Counting positive reflection ties by distinct energies, with arbitrary degeneracies -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family

open Finset
open GaloisForLFunctions.HTGeometry (signChanges_add_one_le)

variable {I : Type*} [Fintype I]

/-- Opposite frequencies contribute at most twice the number of distinct levels. -/
private theorem active_levels (E : I → ℝ) : (Zeros.active E).card≤2*(univ.image E).card := by
  classical
  let S := univ.image E
  have mirror : univ.image (fun i => -E i)=S.image Neg.neg := by rw [image_image]; rfl
  have count : (Zeros.active E).card≤(S ∪ univ.image (fun i => -E i)).card :=
    card_filter_le _ _
  rw [mirror] at count
  exact count.trans ((card_union_le _ _).trans (by rw [two_mul]; exact Nat.add_le_add_left card_image_le _))

/-- The number of distinct positive ties, increased by two, is bounded by
the physical number of distinct energies before centering. -/
theorem blind_distinct_levels (E : I → ℝ) (asym : ¬Reflects E) :
    (blind E).ncard+2≤(univ.image E).card := by
  classical
  obtain ⟨v,detected⟩ : ∃ v, oddTrace (centered E) v ≠ 0 := by
    by_contra! all
    exact asym ((centered_heat_iff_reflects E).mp fun j _ _ => (agrees_odd E j).mpr (all j))
  let fin := finite_blind E
  let Z := fin.toFinset
  have zeros (t : ℝ) (hit : t ∈ Z) : 0<t ∧ oddTrace (centered E) t=0 := by
    have h : t ∈ blind E := fin.mem_toFinset.mp hit
    exact ⟨h.1,(agrees_odd E t).mp h.2.1⟩
  have bound := Zeros.sign_bound (sum_centered E) detected Z zeros
  have changes := signChanges_add_one_le (Zeros.active_pos detected)
    (fun i => Zeros.imbalance (centered E) (Zeros.radius (centered E) i))
  have count := active_levels (centered E)
  have translation : univ.image (centered E)=(univ.image E).image (fun x => x-meanEnergy E) := by
    rw [image_image]; rfl
  rw [translation] at count
  have sub : ((univ.image E).image (fun x => x-meanEnergy E)).card≤(univ.image E).card := card_image_le
  have card : (blind E).ncard=Z.card := Set.ncard_eq_toFinset_card _ fin
  omega

#print axioms blind_distinct_levels

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family
